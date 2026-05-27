"""
Rocq MCP -> LLM -> Lean demo pipeline.

  1. Extract a theorem statement from a .v file via the rocq-mcp server.
  2. Ask Gemini to translate it to Lean 4.
  3. Write the translation to Scratch.lean.
  4. Verify with `lake env lean`.
  5. Print result.

Run from anywhere:
    GEMINI_API_KEY=... .venv/bin/python orchestrator/pipeline.py
"""

from __future__ import annotations

import asyncio
import json
import os
import re
import subprocess
import sys
from pathlib import Path

from google import genai
from mcp import ClientSession, StdioServerParameters
from mcp.client.stdio import stdio_client

REPO_ROOT = Path(__file__).resolve().parent.parent
LEAN_PROJECT = REPO_ROOT / "lean" / "geocoq_translate"
SCRATCH_LEAN = LEAN_PROJECT / "GeocoqTranslate" / "Scratch.lean"
ROCQ_MCP_BIN = REPO_ROOT / ".venv" / "bin" / "rocq-mcp"

MODEL = "gemini-2.5-flash"

ROCQ_FILE = "theories/Axioms/playground.v"
ROCQ_THEOREM_NAME = "neq_sym"


PROMPT_TEMPLATE = """You are translating a Rocq (Coq) theorem to Lean 4.

Output ONLY a complete, self-contained Lean 4 file. Do not include any prose
explanation. Wrap the Lean code in a single ```lean fenced code block.

Requirements:
- The file must compile under stock Lean 4 (no Mathlib imports).
- Declare any required types as `axiom` if they have no obvious Lean primitive.
- Use Lean 4 syntax: `theorem`, `by`, `intro`, `exact`, `Ne.symm`, etc.
- Keep it minimal.

Rocq theorem (name: {name}):

```coq
{statement}
```
"""


async def extract_rocq_theorem(file: str, theorem: str) -> str:
    """Spawn rocq-mcp, open the theorem, return the statement string."""
    params = StdioServerParameters(
        command=str(ROCQ_MCP_BIN),
        args=[],
        env={**os.environ, "ROCQ_WORKSPACE": str(REPO_ROOT)},
    )
    async with stdio_client(params) as (read, write):
        async with ClientSession(read, write) as session:
            await session.initialize()
            result = await session.call_tool(
                "rocq_start",
                {"file": file, "theorem": theorem, "force_restart": True},
            )

    payload = json.loads(result.content[0].text)
    if not payload.get("success"):
        sys.exit(f"error: rocq-mcp could not open {theorem}: {payload}")

    # The 'goals' field looks like: "\n|-forall A : Type, ..."
    goals = payload["goals"]
    match = re.search(r"\|-\s*(.+)", goals, re.DOTALL)
    if not match:
        sys.exit(f"error: could not parse goal from {goals!r}")
    return match.group(1).strip()


def extract_lean_code(reply: str) -> str:
    """Pull the Lean code out of a fenced block. Fall back to raw reply."""
    match = re.search(r"```lean\s*\n(.*?)```", reply, re.DOTALL)
    if match:
        return match.group(1).rstrip() + "\n"
    return reply.strip() + "\n"


def call_gemini(theorem_name: str, statement: str) -> str:
    api_key = os.environ.get("GEMINI_API_KEY") or os.environ.get("GOOGLE_API_KEY")
    if not api_key:
        sys.exit("error: set GEMINI_API_KEY (or GOOGLE_API_KEY) in env")

    client = genai.Client(api_key=api_key)
    response = client.models.generate_content(
        model=MODEL,
        contents=PROMPT_TEMPLATE.format(name=theorem_name, statement=statement),
    )
    return response.text


def verify_lean() -> tuple[bool, str, str]:
    result = subprocess.run(
        ["lake", "env", "lean", "GeocoqTranslate/Scratch.lean"],
        capture_output=True,
        text=True,
        cwd=LEAN_PROJECT,
    )
    return result.returncode == 0, result.stdout, result.stderr


async def amain() -> int:
    print(f"[ROCQ] extracting `{ROCQ_THEOREM_NAME}` from {ROCQ_FILE} via rocq-mcp...")
    statement = await extract_rocq_theorem(ROCQ_FILE, ROCQ_THEOREM_NAME)
    print("[ROCQ] extracted statement:\n")
    print(f"  {statement}\n")

    print(f"[LLM] asking {MODEL}...")
    reply = call_gemini(ROCQ_THEOREM_NAME, statement)
    lean_code = extract_lean_code(reply)
    print("[LLM] generated Lean:\n")
    print(lean_code)

    SCRATCH_LEAN.write_text(lean_code)
    print(f"[LLM] wrote {SCRATCH_LEAN.relative_to(REPO_ROOT)}\n")

    print("[LEAN] running `lake env lean`...")
    ok, out, err = verify_lean()
    if out:
        print("--- stdout ---")
        print(out)
    if err:
        print("--- stderr ---")
        print(err)

    if ok:
        print("[LEAN] verification succeeded")
        return 0
    print("[LEAN] verification failed")
    return 1


if __name__ == "__main__":
    sys.exit(asyncio.run(amain()))
