# End-to-End Demo: Rocq MCP + LLM + Lean MCP

A minimal but real cross-prover translation pipeline. Proves all three
components work together, end-to-end, with no mocks.

## What this experiment is

```
.v file (Rocq)
   |
   |  (1) rocq-mcp: extract theorem statement
   v
plain-text statement
   |
   |  (2) Gemini 2.5 Flash: translate to Lean 4
   v
.lean file
   |
   |  (3) lean-mcp: fetch diagnostics
   v
pass / fail
```

Each arrow is a real protocol call. The two prover sides talk via MCP
(stdio JSON-RPC); the LLM hop in the middle is HTTPS to Google.

## Scope

This is a **demo**, not a translation system. It deliberately uses a
trivial, GeoCoq-independent lemma (`neq_sym : forall A a b, a <> b -> b <> a`)
to isolate the integration question (do the pieces work?) from the much
harder translation-quality question (can the LLM translate non-trivial
GeoCoq theorems?).

The deliberate non-features in v1:

- No interactive tactic steering
- No goal polling
- No retry loop on Lean failure
- No multi-file translation
- No autonomous proof search
- No GeoCoq context (Tarski axioms, `Bet`, `Cong`, etc.) — these expose
  a separate `rocq-mcp` `find_thm` limitation; see "Known limitations."

## Files

| Path | Role |
|---|---|
| `theories/Axioms/playground.v` | Source of the Rocq theorem (`Lemma neq_sym`) |
| `orchestrator/demo.py` | The orchestrator script (one file, ~140 lines) |
| `lean/geocoq_translate/GeocoqTranslate/Scratch.lean` | Output sink for the Lean translation |
| `lean/geocoq_translate/lakefile.lean` | Lake project that hosts the Lean side |

## The four steps

### Step 1: rocq-mcp extracts the statement

The orchestrator spawns the `rocq-mcp` server as a stdio subprocess via
the `mcp` Python SDK:

```python
params = StdioServerParameters(
    command=".venv/bin/rocq-mcp", args=[],
    env={**os.environ, "ROCQ_WORKSPACE": str(REPO_ROOT)},
)
async with stdio_client(params) as (read, write):
    async with ClientSession(read, write) as session:
        await session.initialize()
        result = await session.call_tool(
            "rocq_start",
            {"file": "theories/Axioms/playground.v",
             "theorem": "neq_sym",
             "force_restart": True},
        )
```

`rocq_start` opens the proof of `neq_sym` and returns the current goal,
which (since we're at the very start of the proof) is the theorem
statement itself. The JSON looks like:

```json
{"success": true, "state_id": 1,
 "goals": "\n|-forall (A : Type) (a b : A), a <> b -> b <> a",
 "theorem": "neq_sym",
 "proof_finished": false}
```

We strip the `\n|-` prefix and get the bare statement string:
`forall (A : Type) (a b : A), a <> b -> b <> a`.

### Step 2: Gemini translates to Lean 4

A single non-streaming call to `gemini-2.5-flash` via the
`google-genai` SDK with a tight prompt:

```
Translate this Rocq theorem to Lean 4. Output ONLY a complete,
self-contained Lean 4 file in a single ```lean fenced block. No prose.

Requirements:
- Stock Lean 4, no Mathlib imports.
- Use Lean syntax: `theorem`, `by`, `intro`, `exact`, `Ne.symm`, etc.
- Provide a complete proof.

Rocq theorem (name: neq_sym):

```coq
forall (A : Type) (a b : A) : a <> b -> b <> a
```
```

The reply gets parsed for a `lean ...` fenced block. Example output:

```lean
theorem neq_sym (A : Type) (a b : A) : a ≠ b → b ≠ a := by
  intro h h_ba
  exact h h_ba.symm
```

### Step 3: write Scratch.lean

Plain `Path.write_text` — no Lean tooling involved here.

### Step 4: lean-mcp checks the file

The orchestrator spawns the second MCP server, `lean-lsp-mcp`, also
over stdio:

```python
params = StdioServerParameters(
    command="~/.local/bin/lean-lsp-mcp",
    args=["--lean-project-path", str(LEAN_PROJECT)],
    env={**os.environ},
)
```

…and calls the `lean_diagnostic_messages` tool. The reply is a JSON
blob (text content) like:

```json
{
  "success": true,
  "timed_out": false,
  "items": [
    {"severity": "warning",
     "message": "unused variable `B` ...",
     "line": 1, "column": 20}
  ],
  "failed_dependencies": []
}
```

We scan it for the substring `error` (case-insensitive). If absent, the
Lean translation type-checked.

## How to run

Prerequisites (already set up in this repo):

- Opam switch `play_rocq` active (Coq 8.18, mathcomp 1.18, dune, coq-lsp)
- Python venv at `.venv/` with `mcp`, `fastmcp`, `google-genai`, `rocq_mcp`
- `~/.local/bin/lean-lsp-mcp` installed via `uv tool install lean-lsp-mcp`
- Lean toolchain reachable from `lake env lean`

To run the demo:

```bash
# 1. (One-time) build the Rocq playground so rocq-mcp can resolve imports
dune build theories/Axioms/playground.vo

# 2. Export your Gemini key
export GEMINI_API_KEY=<your-key>

# 3. Run
.venv/bin/python orchestrator/demo.py
```

Expected console output:

```
[1/4] rocq-mcp: extracting neq_sym from theories/Axioms/playground.v
      -> forall (A : Type) (a b : A), a <> b -> b <> a

[2/4] gemini (gemini-2.5-flash): translating to Lean 4
      generated:
        theorem neq_sym (A : Type) (a b : A) : a ≠ b → b ≠ a := by
          intro h h_ba
          exact h h_ba.symm

[3/4] writing lean/geocoq_translate/GeocoqTranslate/Scratch.lean

[4/4] lean-mcp: fetching diagnostics for Scratch.lean
      diagnostics:
        {"success": true, "timed_out": false, "items": [...], ...}

RESULT: all parts worked -- rocq-mcp + LLM + lean-mcp -- and the Lean translation type-checks.
```

## Smoke-testing the MCP servers in isolation

You can verify each MCP server independently of the LLM (useful for
diagnosing where a failure originates):

```python
# orchestrator/demo_smoke.py would look like:
import asyncio, sys
sys.path.insert(0, "orchestrator")
from demo import extract_from_rocq, verify_with_lean_mcp

async def main():
    stmt = await extract_from_rocq(
        "theories/Axioms/playground.v", "neq_sym")
    print("rocq extracted:", stmt)

    ok, diags = await verify_with_lean_mcp(
        "GeocoqTranslate/Scratch.lean")
    print("lean clean compile:", ok)

asyncio.run(main())
```

This was used during development to confirm both ends worked before
plugging in Gemini.

## Known limitations

### rocq-mcp's `find_thm` doesn't pre-process imports

When extracting a theorem whose statement requires identifiers from
`Require Import …` lines earlier in the file, `rocq_start(file, theorem=name)`
fails with `Tarski_neutral_dimensionless was not found`. It works only
for theorems whose types use stdlib primitives (`Type`, `=`, `<>`).

This is why the demo uses `neq_sym` and not, e.g., `cong_sym`. A real
translation pipeline targeting GeoCoq would need either:

- a workaround using position-based `rocq_start` followed by
  `rocq_query` against a fully-loaded state, or
- text-based statement extraction (regex on the `.v` file), or
- a fix in the upstream rocq-mcp.

### `rocq_query` with `file=` mode is flaky

In our environment, `rocq_query` with the `file=` parameter
intermittently crashes with `JLang.Point.t.offset` — likely a state
corruption issue. `rocq_query` with `from_state=` against a session
that was started via `rocq_start` is more reliable.

### `lake env lean` would also work for step 4

Strictly, you don't need `lean-mcp` for v1 — `subprocess.run(["lake",
"env", "lean", file])` gives you compile pass/fail and a stderr string.
We use `lean-mcp` here because:

1. The exercise was to make both MCP servers part of the loop.
2. `lean-mcp`'s JSON-structured diagnostics are easier to programmatically
   inspect (severity, line, column) than parsing stderr.
3. `lean-mcp` exposes much richer tools (`lean_goal`, `lean_run_code`,
   `lean_multi_attempt`, premise search, …) that become useful in v2.

## What v2 would look like

Natural extensions, in increasing complexity:

1. **Replace the hardcoded theorem name with a CLI arg.** One-line change.
2. **Retry loop on Lean failure.** If `lean_diagnostic_messages` reports
   errors, feed them back to Gemini with the original Rocq statement and
   ask for a fix. Cap at one or two retries.
3. **Use `lean_goal` after a partial proof.** When Gemini's translation
   leaves a `sorry`, query the goal at that position and ask Gemini to
   continue. This is real interactive proof construction.
4. **Try a non-trivial Rocq theorem.** Once the rocq-mcp limitation
   above is resolved, pick a GeoCoq lemma that actually uses `Bet` /
   `Cong`. Translation quality becomes the headline metric, not
   plumbing.
5. **Translation-quality benchmark.** A list of N theorems × M prompts
   × K models, measuring pass-rate. The current code is close to this —
   `orchestrator/experiment.py` started in this direction.

## Why this matters

This is the minimum viable evidence that the architecture works:

- The same Python process talks to two MCP servers simultaneously,
  passing the output of one through an LLM to the other.
- All three pieces (Rocq tooling, LLM, Lean tooling) are real — none of
  them are mocked or stubbed.
- A translation went from a real `.v` file through a real LLM into a
  real `.lean` file that a real Lean checker accepted.

From here, every additional capability is incremental — you're refining
quality and robustness within an architecture that already works,
rather than discovering whether the integration is possible at all.
