"""
Demo progression: run the rocq-mcp + Gemini + lean-mcp pipeline on a
sequence of progressively harder Rocq theorems.

For each test case:
  1. [rocq-mcp]   extract theorem statement
  2. [LLM]        Gemini translates to Lean 4
  3. [filesystem] write to Scratch.lean
  4. [lean-mcp]   fetch diagnostics for the file

Prints per-case status and a final summary.

Run:
    GEMINI_API_KEY=... .venv/bin/python orchestrator/demo_progression.py
"""

from __future__ import annotations

import asyncio
import sys
from dataclasses import dataclass
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from demo import (
    REPO_ROOT,
    SCRATCH_LEAN,
    call_gemini,
    extract_from_rocq,
    extract_lean_code,
    verify_with_lean_mcp,
)


@dataclass
class Case:
    name: str
    description: str


ROCQ_FILE = "theories/Axioms/rocq_demo.v"
CASES = [
    Case("add_0_r", "nat identity, single induction"),
    Case("add_comm", "nat addition commutativity, nested induction"),
    Case("length_app", "list length distributes over append"),
    Case("de_morgan", "De Morgan, pure propositional logic"),
    Case("exists_not_all", "mixes exists, forall, and negation"),
]


@dataclass
class Result:
    case: Case
    statement: str | None = None
    lean_code: str | None = None
    verified: bool = False
    diag: str = ""
    error: str | None = None


async def run_one(case: Case) -> Result:
    r = Result(case=case)
    try:
        r.statement = await extract_from_rocq(ROCQ_FILE, case.name)
    except SystemExit as e:
        r.error = f"extract: {e}"
        return r
    try:
        reply = call_gemini(case.name, r.statement)
        r.lean_code = extract_lean_code(reply)
    except SystemExit as e:
        r.error = f"llm: {e}"
        return r
    SCRATCH_LEAN.write_text(r.lean_code)
    r.verified, r.diag = await verify_with_lean_mcp(
        "GeocoqTranslate/Scratch.lean"
    )
    return r


def print_case(idx: int, total: int, r: Result) -> None:
    status = "PASS" if r.verified else ("FAIL" if r.error is None else "ERROR")
    print(f"\n[{idx}/{total}] {r.case.name} -- {status}")
    print(f"  desc:      {r.case.description}")
    if r.statement:
        print(f"  rocq:      {r.statement}")
    if r.error:
        print(f"  error:     {r.error}")
        return
    if r.lean_code:
        first_lines = "\n             ".join(r.lean_code.strip().splitlines()[:6])
        print(f"  lean[1:6]: {first_lines}")
    diag_snip = (r.diag or "").replace("\n", " ")[:300]
    print(f"  diag:      {diag_snip}")


def print_summary(results: list[Result]) -> None:
    print("\n" + "=" * 78)
    print(f"{'name':<22} {'status':<6} description")
    print("-" * 78)
    for r in results:
        status = "PASS" if r.verified else ("ERROR" if r.error else "FAIL")
        print(f"{r.case.name:<22} {status:<6} {r.case.description}")
    passed = sum(1 for r in results if r.verified)
    print(f"\n{passed}/{len(results)} cases verified by lean-mcp")

    out_dir = REPO_ROOT / "orchestrator" / "experiment_outputs"
    out_dir.mkdir(exist_ok=True)
    for r in results:
        if r.lean_code:
            (out_dir / f"{r.case.name}.lean").write_text(r.lean_code)
    print(f"\nLean outputs saved to {out_dir.relative_to(REPO_ROOT)}/")


async def amain() -> int:
    print(f"running {len(CASES)} case(s) on {ROCQ_FILE}...")
    results: list[Result] = []
    for i, case in enumerate(CASES, 1):
        print(f"\n=== [{i}/{len(CASES)}] {case.name} ===")
        r = await run_one(case)
        results.append(r)
        print_case(i, len(CASES), r)
    print_summary(results)
    return 0 if all(r.verified for r in results) else 1


if __name__ == "__main__":
    sys.exit(asyncio.run(amain()))
