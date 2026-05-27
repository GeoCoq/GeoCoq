"""
End-to-end demo: rocq-mcp + LLM + lean-mcp.

Pipeline:
  1. [rocq-mcp]   open neq_sym in playground.v, read the goal as the theorem
  2. [LLM]        ask Gemini to translate it to Lean 4
  3. [filesystem] write to GeocoqTranslate/Scratch.lean
  4. [lean-mcp]   query lean_diagnostic_messages for that file -> pass/fail

Run:
    GEMINI_API_KEY=... .venv/bin/python orchestrator/demo.py
"""

from __future__ import annotations

import asyncio
import json
import os
import re
import shutil
import sys
from pathlib import Path

from google import genai
from mcp import ClientSession, StdioServerParameters
from mcp.client.stdio import stdio_client

REPO_ROOT = Path(__file__).resolve().parent.parent
LEAN_PROJECT = REPO_ROOT / "lean" / "geocoq_translate"
SCRATCH_LEAN = LEAN_PROJECT / "GeocoqTranslate" / "Scratch.lean"

# Resolve rocq-mcp: same venv as this script, then PATH.
ROCQ_MCP_BIN = (
    os.environ.get("ROCQ_MCP_BIN")
    or shutil.which("rocq-mcp", path=str(Path(sys.executable).parent))
    or shutil.which("rocq-mcp")
    or "rocq-mcp"
)
# Resolve lean-lsp-mcp: PATH, then ~/.local/bin (typical uv tool install).
LEAN_MCP_BIN = (
    os.environ.get("LEAN_MCP_BIN")
    or shutil.which("lean-lsp-mcp")
    or str(Path.home() / ".local" / "bin" / "lean-lsp-mcp")
)

MODEL = "gemini-2.5-flash"

# Simple Rocq theorem source -- standalone, no GeoCoq context needed.
ROCQ_FILE = "theories/Axioms/playground.v"
ROCQ_THEOREM = "neq_sym"


PROMPT_TEMPLATE = """Translate this Rocq theorem to Lean 4. Output ONLY a complete,
self-contained Lean 4 file in a single ```lean fenced block. No prose.

Requirements:
- Stock Lean 4, no Mathlib imports.
- Use Lean syntax: `theorem`, `by`, `intro`, `exact`, `Ne.symm`, etc.
- Provide a complete proof.

Rocq theorem (name: {name}):

```coq
{statement}
```
"""


# ---------- rocq-mcp ----------

async def extract_from_rocq(file: str, theorem: str) -> str:
    """Use rocq-mcp to open a theorem and return its goal as the statement."""
    params = StdioServerParameters(
        command=str(ROCQ_MCP_BIN), args=[],
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
        sys.exit(f"rocq-mcp could not open {theorem}: {payload}")
    m = re.search(r"\|-\s*(.+)", payload["goals"], re.DOTALL)
    if not m:
        sys.exit(f"could not parse goal from: {payload['goals']!r}")
    return m.group(1).strip()


# ---------- LLM ----------

def call_gemini(name: str, statement: str) -> str:
    api_key = os.environ.get("GEMINI_API_KEY") or os.environ.get("GOOGLE_API_KEY")
    if not api_key:
        sys.exit("error: set GEMINI_API_KEY in env")
    client = genai.Client(api_key=api_key)
    resp = client.models.generate_content(
        model=MODEL,
        contents=PROMPT_TEMPLATE.format(name=name, statement=statement),
    )
    return resp.text


def extract_lean_code(reply: str) -> str:
    m = re.search(r"```lean\s*\n(.*?)```", reply, re.DOTALL)
    return (m.group(1) if m else reply).rstrip() + "\n"


# ---------- lean-mcp ----------

async def verify_with_lean_mcp(lean_file_rel: str) -> tuple[bool, list[dict]]:
    """Use lean-mcp to fetch diagnostics for the file. Returns (no_errors, diag_list)."""
    params = StdioServerParameters(
        command=str(LEAN_MCP_BIN),
        args=["--lean-project-path", str(LEAN_PROJECT)],
        env={**os.environ},
    )
    async with stdio_client(params) as (read, write):
        async with ClientSession(read, write) as session:
            await session.initialize()
            result = await session.call_tool(
                "lean_diagnostic_messages",
                {"file_path": lean_file_rel},
            )
    # The MCP tool returns the diagnostics as text content; parse it.
    text = result.content[0].text if result.content else ""
    # Errors typically include lines like "error:" or severity 1.
    has_error = bool(re.search(r"error", text, re.IGNORECASE))
    return not has_error, text


# ---------- driver ----------

async def amain() -> int:
    print(f"[1/4] rocq-mcp: extracting {ROCQ_THEOREM} from {ROCQ_FILE}")
    statement = await extract_from_rocq(ROCQ_FILE, ROCQ_THEOREM)
    print(f"      -> {statement}\n")

    print(f"[2/4] gemini ({MODEL}): translating to Lean 4")
    reply = call_gemini(ROCQ_THEOREM, statement)
    lean_code = extract_lean_code(reply)
    print("      generated:\n")
    for line in lean_code.splitlines():
        print(f"        {line}")
    print()

    print(f"[3/4] writing {SCRATCH_LEAN.relative_to(REPO_ROOT)}")
    SCRATCH_LEAN.write_text(lean_code)
    print()

    print("[4/4] lean-mcp: fetching diagnostics for Scratch.lean")
    ok, diagnostics = await verify_with_lean_mcp("GeocoqTranslate/Scratch.lean")
    print("      diagnostics:")
    for line in (diagnostics or "(none)").splitlines():
        print(f"        {line}")
    print()

    if ok:
        print("RESULT: all parts worked -- rocq-mcp + LLM + lean-mcp -- and the Lean translation type-checks.")
        return 0
    print("RESULT: pipeline ran end-to-end, but the Lean translation has errors.")
    return 1


if __name__ == "__main__":
    sys.exit(asyncio.run(amain()))
