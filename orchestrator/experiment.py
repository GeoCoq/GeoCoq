"""
Toy GeoCoq -> Lean translation experiment.

For each theorem in TEST_CASES, runs:
  extract statement  ->  Gemini translate  ->  lean type-check

and reports pass/fail. Prints a summary table at the end.

Extraction note: rocq-mcp's `find_thm` doesn't pre-process file imports,
so it works only for theorems whose statements use stdlib primitives.
For GeoCoq theorems (which need the Tarski context), we fall back to a
simple regex on the .v source. This is a known rocq-mcp limitation.

Run:
    GEMINI_API_KEY=... .venv/bin/python orchestrator/experiment.py
"""

from __future__ import annotations

import asyncio
import re
import sys
from dataclasses import dataclass
from pathlib import Path

# Reuse pipeline helpers
sys.path.insert(0, str(Path(__file__).resolve().parent))
from pipeline import (
    LEAN_PROJECT,
    REPO_ROOT,
    SCRATCH_LEAN,
    call_gemini,
    extract_lean_code,
    extract_rocq_theorem,
    verify_lean,
)


def extract_from_source(rocq_file: str, theorem: str) -> str:
    """Pull `Lemma <theorem> : <stmt>.` directly from the .v file text.

    Used when rocq-mcp can't process the theorem's surrounding context.
    """
    text = (REPO_ROOT / rocq_file).read_text()
    # Match `Lemma <name> [optional binders] : <stmt>.` allowing multi-line.
    pattern = (
        rf"\b(?:Lemma|Theorem|Definition)\s+{re.escape(theorem)}\b"
        rf"([^.]*?):\s*([^.]*?)\."
    )
    m = re.search(pattern, text, re.DOTALL)
    if not m:
        raise SystemExit(f"text extraction: {theorem} not found in {rocq_file}")
    binders = m.group(1).strip()
    stmt = m.group(2).strip()
    return f"{binders} : {stmt}".strip().lstrip(":").strip()


async def extract_theorem(rocq_file: str, theorem: str) -> tuple[str, str]:
    """Try rocq-mcp first; fall back to text extraction. Returns (statement, source)."""
    try:
        stmt = await extract_rocq_theorem(rocq_file, theorem)
        return stmt, "rocq-mcp"
    except SystemExit:
        stmt = extract_from_source(rocq_file, theorem)
        return stmt, "text"


@dataclass
class TestCase:
    name: str
    rocq_file: str
    theorem: str
    description: str


TEST_CASES = [
    TestCase(
        name="L0_pure_logic",
        rocq_file="theories/Axioms/playground.v",
        theorem="neq_sym",
        description="Pure logic, no GeoCoq context",
    ),
    TestCase(
        name="L1_tpoint_type",
        rocq_file="theories/Axioms/playground.v",
        theorem="point_eq_sym",
        description="Introduces primitive type Tpoint",
    ),
    TestCase(
        name="L2_cong_relation",
        rocq_file="theories/Axioms/playground.v",
        theorem="cong_sym_stmt",
        description="Uses primitive Cong relation",
    ),
    TestCase(
        name="L3_bet_and_cong",
        rocq_file="theories/Axioms/playground.v",
        theorem="bet_cong_stmt",
        description="Combines Bet and Cong primitives",
    ),
]


@dataclass
class Result:
    case: TestCase
    statement: str | None
    lean_code: str | None
    verified: bool
    stdout: str
    stderr: str
    error: str | None = None


async def run_case(case: TestCase) -> Result:
    try:
        statement = await extract_rocq_theorem(case.rocq_file, case.theorem)
    except SystemExit as e:
        return Result(case, None, None, False, "", "", error=f"extract: {e}")

    try:
        reply = call_gemini(case.theorem, statement)
        lean_code = extract_lean_code(reply)
    except SystemExit as e:
        return Result(case, statement, None, False, "", "", error=f"llm: {e}")

    SCRATCH_LEAN.write_text(lean_code)
    ok, out, err = verify_lean()
    return Result(case, statement, lean_code, ok, out, err)


def print_result(idx: int, total: int, r: Result) -> None:
    status = "PASS" if r.verified else "FAIL"
    print(f"\n[{idx}/{total}] {r.case.name} -- {status}")
    print(f"  desc: {r.case.description}")
    if r.statement:
        print(f"  rocq stmt: {r.statement}")
    if r.error:
        print(f"  error: {r.error}")
        return
    if not r.verified:
        # Show only first 8 lines of stderr to keep output tight
        snippet = "\n    ".join((r.stderr or r.stdout).strip().splitlines()[:8])
        if snippet:
            print(f"  diag:\n    {snippet}")


def print_summary(results: list[Result]) -> None:
    print("\n" + "=" * 70)
    print(f"{'name':<25} {'status':<7} {'description'}")
    print("-" * 70)
    for r in results:
        status = "PASS" if r.verified else "FAIL"
        print(f"{r.case.name:<25} {status:<7} {r.case.description}")
    passed = sum(1 for r in results if r.verified)
    print(f"\n{passed}/{len(results)} passed")

    # Save the last Lean file from each run for inspection
    out_dir = REPO_ROOT / "orchestrator" / "experiment_outputs"
    out_dir.mkdir(exist_ok=True)
    for r in results:
        if r.lean_code:
            (out_dir / f"{r.case.name}.lean").write_text(r.lean_code)
    print(f"\nLean outputs saved to {out_dir.relative_to(REPO_ROOT)}")


async def amain() -> int:
    print(f"running {len(TEST_CASES)} test case(s)...\n")
    results = []
    for i, case in enumerate(TEST_CASES, 1):
        print(f"=== [{i}/{len(TEST_CASES)}] {case.name} ===")
        r = await run_case(case)
        results.append(r)
        print_result(i, len(TEST_CASES), r)

    print_summary(results)
    return 0 if all(r.verified for r in results) else 1


if __name__ == "__main__":
    sys.exit(asyncio.run(amain()))
