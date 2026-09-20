# RESULT_FINAL_20260919_1554Z.tgz — read me first

Lean 4 formalization: corner state sum wall laws and soft theorem (source frame SM15).
Completed 2026-09-19 15:55 UTC. The tarball is self-contained: frozen sources, Lean code,
checker tools, every review record and receipt, and a `setup.sh` that installs the Lean
toolchain and rebuilds from scratch (no build artifacts are shipped; about 5 minutes on a
fast machine, up to an hour on a slow network).

```
sha256  40c1be0b6f709aa80d2b79026d3c10764a21a9bb132009eac63bab0a06b4baae
RESULT_FINAL_20260919_1554Z.tgz  (142 MB)
```

## Final state

| item | result |
|---|---|
| claims verified | 132/132 |
| checklist rows accepted | 192/192 |
| final targets | 8/8 |
| `check_lean.py --all` | PASS (stage 1: 191 mapped, 49,207 audited; development: 192 / 49,212) |
| `verify_bundle.py` | PASS ("FOCUSED BUNDLE VERIFIED: 191 files") |
| sorry | none under `work/lean` |
| axioms | exactly the nine registered ones (five are admitted literature interfaces) |

Final theorem: `SM.corner_laws_and_soft` in `work/lean/SM/CornerLawsAndSoft.lean`.

## Where to start

1. `FINAL_REVIEW.md` (top level): the completed fidelity review. §4.3 lists the admitted
   literature axioms, §5 is the honest gap list, §7 the inconsistencies noticed.
2. `work/AUTHOR_NOTES.md`: the dated decision log (every local decision, deferral, and audit).
3. `work/STATUS.md`: the executor's running status; the top entry is the closing state.

## To rebuild and re-check

```sh
tar xzf RESULT_FINAL_20260919_1554Z.tgz
cd CORNER_LAWS_FOCUSED_20260912
bash setup.sh
export PATH="$HOME/.elan/bin:$PATH"
python3 tools/check_lean.py work/lean --all
python3 verify_bundle.py
```

## Stale documents inside the bundle

`README.md`, `START_HERE.md`, and `work/HANDOVER_README.md` are the instructions the
executing agent was given at the start of the run (or at the 2026-09-16 checkpoint). They
still describe an unfinished state ("20 of 132 claims verified", "124/132") and tell the
reader to prove the rest. Ignore those counts; the current state is in `FINAL_REVIEW.md`
and `work/STATUS.md`.

## Disclosures worth knowing (all detailed in FINAL_REVIEW.md)

- The final theorem rests on nine registered axioms; five are literature interfaces that
  were admitted, not proved (`blueprint/AXIOM_REGISTRY.md`), including the descent axiom
  `SM.lit_homfly_descent` added on the author's 2026-09-15 decision.
- One registry edit (G-07) was applied and then reverted because it broke a frozen-source
  hash check; the disclosure lives in the policy label and the review instead.
- Row 57's internal skeleton had four sub-lemmas that were false as stated and were replaced
  by corrected, proved forms; row 110's wave-5 boxes were restated with radius hypotheses.
  No row statement was changed.
- One review record had stored the hash of the wrong frozen file and was corrected with a
  recorded note (D-DOC-4); it was the only mismatch among 192 rows.
