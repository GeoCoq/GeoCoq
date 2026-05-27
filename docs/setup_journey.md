# GeoCoq + Rocq MCP + Lean MCP Setup Journey

A chronological log of every problem we hit while getting this development
environment working, what we tried, what failed, and what stuck.

## Final state (what works now)

| Piece | Version / location |
|---|---|
| Opam switch | `play_rocq` (only switch besides `default`) |
| Coq | 8.18.0 |
| coq-lsp server | 0.2.3+8.18 at `~/.opam/play_rocq/bin/coq-lsp` |
| Cursor extension | `ejgallego.coq-lsp@0.2.3-universal` |
| mathcomp | 1.18.0 (ssreflect, fingroup, algebra, solvable, field) |
| dune | 3.23.0 |
| GeoCoq build | `dune build` → 459/460 `.vo` files (only the upstream `gelertner_inspired_axioms.v` cross-namespace bug fails) |
| Editor type-checking | Works on every file we tried |
| `pipeline.py` | Rocq MCP → Gemini → Lean verifier loop, end-to-end |

---

## Problem 1: `dune build` on master failed under Rocq 9.1.1

### Symptoms
```
theories/Coinc/Utils/arity.v: Unable to locate library Arith
theories/Main/Utils/all_equiv.v: Unable to locate library List
theories/Elements/.../euclidean_tactics.v: Unable to locate library Classical
theories/Main/Meta_theory/Continuity/first_order.v: Cannot find a physical path bound to Logic.ChoiceFacts
theories/Algebraic/dune: Theory "mathcomp" has not been found
theories/Axioms/gelertner_inspired_axioms.v:152: Cannot find a physical path bound to GeoCoq.Main.Tarski_dev.Ch12_parallel_inter_dec
```

### What I tried first — adding `Stdlib` to dune files

Hypothesis: under Rocq 9.x + dune-coq 0.8, the Stdlib is no longer
implicitly added as a `(theories …)` dependency in each `coq.theory` stanza.

I edited every `theories/*/dune` to add `Stdlib`:
```
- (theories GeoCoq.Coinc)
+ (theories GeoCoq.Coinc Stdlib)
```
Verified `theories/Coinc/Utils/arity.v` compiled afterwards (only
deprecation warnings, no error).

**Reverted on user request** — they didn't want source modifications,
only diagnosis. `git checkout --` on the five dune files brought them
back to upstream state.

### What actually worked — Pierre's suggestion (Coq 8.18.0)

Pierre Boutry recommended:
```
opam switch create switch_name --packages coq.8.18.0,coq-mathcomp-field.1.18.0
```

The GeoCoq `master` branch was reverted from a Rocq 9.0 upgrade attempt
(`git log` shows commit `77d1c66` "Revert 'upgrading to rocq9.0.0 and
mathcomp2.4.0'"), so it's still 8.x code. Coq 8.x makes Stdlib implicit
in dune-coq 0.8, so the build "just works."

### Verification (proper test under fresh switch)

Created a `rocq-9.1.1` opam switch alongside the existing one (with
`--no-switch` so my default stayed put):
```
opam switch create rocq-9.1.1 ocaml-base-compiler.5.2.0 --no-switch -y
opam install --switch=rocq-9.1.1 -y dune rocq-core.9.1.1 rocq-stdlib \
    coq-mathcomp-ssreflect coq-mathcomp-fingroup \
    coq-mathcomp-algebra coq-mathcomp-field
```

Cloned a fresh tree to `/tmp/geocoq-rocq91-test`, ran
`dune build` under it: **25 of 460 `.vo` files built, then errored**.
Same Stdlib/mathcomp/gelertner issues as before — plus an additional
"HB not in loadpath" issue because mathcomp 2.5 uses Hierarchy Builder.

Conclusion: GeoCoq master legitimately doesn't build on Rocq 9.1.1
as-is. Needed Coq 8.x.

### The one remaining failure on every toolchain

`theories/Axioms/gelertner_inspired_axioms.v:152` does
`Require Import GeoCoq.Main.Tarski_dev.…` from inside the **Axioms**
theory — but Axioms' dune config only declares `GeoCoq.Coinc` as a
dependency, so Main isn't on the loadpath. This is a genuine upstream
bug; the file itself flags it on line 149 ("Should be in a separate
file/directory."). Reproduces on Coq 8.18.0, Coq 8.20.1, and Rocq 9.1.1.
Not blocking my own work.

---

## Problem 2: Switch hygiene

We ended up with three switches: `default`, `rocq` (the original 8.20.1
install), `rocq-9.1.1` (test sandbox), `play_rocq` (Pierre's recipe).

### Cleanup order (the careful version)

1. Created `play_rocq` with `--no-switch` so it sat alongside.
2. Verified `dune build` worked on the real tree under `play_rocq`
   (`opam exec --switch=play_rocq -- dune build`).
3. Installed `coq-lsp` in `play_rocq` — this is where things got tricky
   (see Problem 4).
4. After coq-lsp was confirmed working, removed both old switches:
   ```
   opam switch remove rocq -y
   opam switch remove rocq-9.1.1 -y
   ```
5. Activated `play_rocq` as the default for this user:
   ```
   opam switch play_rocq
   eval $(opam env)
   ```

Final disk: `~2 GB` saved by removing the two old switches.

---

## Problem 3: `coq-lsp` install failure

Tried:
```
opam install --switch=play_rocq coq-lsp -y
```

Failed silently — opam picked `coq-lsp.0.2.5` (the latest) but **0.2.5
has no `+8.18` variant**. The newest coq-lsp for Coq 8.18 is
`0.2.3+8.18`.

Fix: pin explicitly:
```
opam install --switch=play_rocq coq-lsp.0.2.3+8.18 -y
```

Installed cleanly. Lesson: coq-lsp versions are tightly tied to specific
Coq versions via the `+8.xx` / `+9.x` suffix — always pin when on older
Coq.

---

## Problem 4: Editor showing red squiggles on `Require Import GeoCoq.Axioms.*`

This was the longest debugging arc. Three distinct issues, fixed one at
a time.

### Issue 4a: Cursor extension version mismatch

Cursor had auto-updated `ejgallego.coq-lsp` to `0.2.4`. Our server was
`0.2.3+8.18` (only 8.18-compatible version). The LSP wire protocol
diverges across minor versions — extension couldn't drive the server
properly.

Fix:
```
/Applications/Cursor.app/Contents/Resources/app/bin/cursor \
    --install-extension ejgallego.coq-lsp@0.2.3 --force
```

Restart of the LSP server didn't clear the errors — symptoms were the
same as before.

### Issue 4b: `.vo` files were in `_build/`, not `theories/`

The repo's `_CoqProject` declares:
```
-Q theories GeoCoq
```
But dune builds put compiled artifacts at:
```
_build/default/theories/Axioms/tarski_axioms.vo
```
…**not** at `theories/Axioms/tarski_axioms.vo` (no `.vo` files live next
to `.v` sources at all). So coq-lsp, obeying `_CoqProject`, looked under
`theories/` and found nothing.

Verified by running plain `coqc`:
```
$ echo 'Require Import GeoCoq.Axioms.tarski_axioms.' > /tmp/smoke.v
$ coqc -Q theories GeoCoq /tmp/smoke.v
Error: Cannot find a physical path bound to logical path GeoCoq.Axioms.tarski_axioms.

$ coqc -Q _build/default/theories GeoCoq /tmp/smoke.v
(success)
```

Fix: tell coq-lsp (and only coq-lsp — not dune) to add `_build/default/theories`
as a search path via `.vscode/settings.json`:
```json
"coq-lsp.args": [
    "-Q", "_build/default/theories,GeoCoq"
]
```

`_CoqProject` left untouched so `dune build` keeps working with the
plain `theories/` path.

### Issue 4c: I used the wrong `-Q` syntax (caused coq-lsp to fail to start)

Initial attempt used **coqc syntax** for the `-Q` flag:
```json
"coq-lsp.args": [
    "-Q", "_build/default/theories", "GeoCoq",
    "-w", "-ambiguous-paths",
    "-w", "-notation-overridden"
]
```

This is wrong on two counts:
1. **coq-lsp's `-Q` takes a single `DIR,LP` argument** (comma-separated),
   not three space-separated args like `coqc`. Reference:
   `coq-lsp --help` shows `-Q DIR,LP, --load-path=DIR,LP`.
2. **`-w` is a Coq compiler flag, not a coq-lsp flag.** coq-lsp's
   arg parser rejects unknown options.

Running it from a shell to verify:
```
$ coq-lsp -Q _build/default/theories GeoCoq -w -ambiguous-paths
Usage: coq-lsp [--help] [OPTION]…
coq-lsp: unknown option '-w' unknown option '-a' unknown option '-w' unknown
         option '-n'
```

Server bailed at startup, hence "coq-lsp failing to start" in the editor.

Final, working args:
```json
"coq-lsp.args": [
    "-Q", "_build/default/theories,GeoCoq"
]
```

Warning suppression isn't needed at the coq-lsp arg level — coq-lsp
reads `_CoqProject` itself and picks up `-arg -w -arg -ambiguous-paths`
from there.

---

## Problem 5: `rocq_query` in rocq-mcp keeps crashing

Symptom:
```
{"success":false,"error":"JLang.Point.t.offset","reason":"crashed"}
```
…on any `rocq_query` call. But `rocq_start` works fine.

Workaround (not a fix): use `rocq_start` for the orchestrator extraction
step instead of `rocq_query`. `rocq_start` returns the goal as
`"|-<statement>"`, which we parse back into a string.

`pipeline.py`'s `extract_rocq_theorem()` uses this approach.

---

## Pipeline.py — the actual demo

Final architecture:

```
pipeline.py
    ├── rocq-mcp (stdio subprocess via mcp Python SDK)
    │       └── rocq_start(file=playground.v, theorem=neq_sym)
    │           → goal "|-forall (A : Type) (a b : A), a <> b -> b <> a"
    │
    ├── Gemini 2.5 Flash (google-genai SDK)
    │       └── translate Coq theorem → Lean 4 file
    │
    ├── Write lean/geocoq_translate/GeocoqTranslate/Scratch.lean
    │
    └── subprocess: `lake env lean GeocoqTranslate/Scratch.lean`
            → exit 0 / 1
```

Source of truth for the Rocq theorem: `theories/Axioms/playground.v`.
Edit the `Lemma neq_sym` there, re-run `pipeline.py`, it picks up the
new statement automatically.

Verified working end-to-end with `neq_sym` — Gemini Flash produced a
clean Lean 4 proof, `lake env lean` exited 0.

### Run it

```
opam exec --switch=play_rocq -- dune build theories/Axioms/playground.vo   # if you edited playground.v
export GEMINI_API_KEY=<your-key>
.venv/bin/python orchestrator/pipeline.py
```

---

## Files changed during the session

| File | Change |
|---|---|
| `test.v` | New — sum-of-squares proof, then expanded as MCP scratchpad |
| `theories/Axioms/playground.v` | Added standalone `Lemma neq_sym` for pipeline extraction |
| `theories/Axioms/adg_definitions.v` | (Pre-existing user work, untouched by me) |
| `theories/Axioms/Definitions.v` | (Pre-existing user work — only the trailing-newline change) |
| `orchestrator/pipeline.py` | New — the end-to-end demo orchestrator |
| `.vscode/settings.json` | Added `coq-lsp.args` for the `_build/default/theories` search path |
| `docs/setup_journey.md` | This file |

Reverted before commit:
- The `Stdlib`-addition edits to `theories/*/dune` (5 files) — only
  needed if upgrading to Rocq 9.x.

---

## Things to remember for next time

1. **GeoCoq master is Coq 8.x territory** — don't burn time on Rocq 9.x
   unless you're explicitly porting it.
2. **coq-lsp version must match the Cursor/VS Code extension version**,
   and both must match the Coq version (`coq-lsp.X.Y.Z+8.NN`).
   Newest extension ≠ best — pin to what your switch supports.
3. **dune builds `.vo` into `_build/default/theories/`**, not next to
   the `.v` files. Editor needs to be told this via `coq-lsp.args`
   (workspace setting), not `_CoqProject` (which dune reads).
4. **coq-lsp's CLI syntax is not coqc's.** `-Q DIR,LP` (one arg, comma),
   no `-w` warning flags.
5. When `rocq_query` crashes, use `rocq_start` and parse the goal —
   same information, different code path.
