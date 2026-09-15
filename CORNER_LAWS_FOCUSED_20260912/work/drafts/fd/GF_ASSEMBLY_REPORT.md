# GF_ASSEMBLY_REPORT.md — assembly of row 87 fd:generic-front

Date: 2026-09-14.  Output: `work/drafts/fd/GF_Assembled.lean` (5411 lines, md5
`c8915f2a08c5268f3f7a7b46d37400d1`).  Inputs: `GF_Skeleton.lean` (625 lines) and `GF_U_P{0,…,6}.lean`
with their `GF_U_P*_REPORT.md`.  Scripts: `GF_assemble.py` (assembly + repair + de-duplication, every
step asserted; re-runnable), `GF_clash_scan.py` (namespace-aware name-clash scan, adapted from
`TN_clash_scan.py`).  Nothing under `work/lean` was written or built; the only compile command used was
`cd work/lean && lake env lean ../drafts/fd/GF_Assembled.lean` (and the same command on `/tmp` copies for
`#print axioms` and the pass-1 control).  Scratch: `/tmp/gf_assembly/`.

## Result in one line

**0 `sorry` (`grep -c sorry` = 0, also case-insensitive), 0 errors, 0 unproved leaves, 0 name clashes.**
`#print axioms SM.fd_generic_front` = `[propext, Classical.choice, Quot.sound]` — no `sorryAx`.
The statement block (§1–§4, assembled lines 36-212) is byte-identical to `GenericFront_Statement.lean`
lines 79-255 (and to skeleton lines 26-202).  One deliberate deviation from the skeleton: its leaf P2.2
(`stage1_stable`) was **false as stated** and was replaced by the repair unit P2 had prepared and tested
(§3); the statement of every other declaration is unchanged.  Two linter warnings remain (unused binders
in FROZEN statements, §8).

## 1. Statement-freeze verification (task item 1)

`diff GF_Skeleton.lean GF_U_<u>.lean` (normal format) was parsed hunk by hunk.  Rule: a `c` hunk must
replace exactly one `  sorry` line (the replacement may carry the helpers that follow the leaf up to the
next skeleton line); an `a` hunk is a pure insertion; any `d` hunk is a violation.  Hunks of different
units may not touch the same skeleton line.

| unit | hunks | `sorry` lines replaced | removed non-`sorry` lines | helpers added | verdict |
|---|---|---|---|---|---|
| P0 | 4 (`221a`, `227c`, `234c`, `240c`) | 3 (P0.1–P0.3) | none | 7 (`gp0_*`) | clean |
| P1 | 5 (`292a`, `299c`, `307c`, `311c`, `316c`) | 4 (P1.1–P1.4) | none | 17 (`gp1_*`) | clean |
| P2 | 3 (`331a`, `337c`, `345a`) | 1 (P2.1) | none | 24 (`gp2_*`) | clean; P2.2 left `sorry` (false, §3); `345a` = a 3-line pointer comment inside the still-`sorry` body of P2.2 |
| P3 | 5 (`368a`, `376c`, `386c`, `395c`, `403c`) | 4 (P3.1–P3.4) | none | 70 (`gp3_*`, incl. 3 `def`s) | clean |
| P4 | 3 (`450a`, `456c`, `463c`) | 2 (P4.1–P4.2) | none | 7 (`gp4_*`, incl. 1 `def`) | clean |
| P5 | 9 (`4a5`, `478a`, `483c`, `490c`, `501c`, `514c`, `521c`, `534c`, `544c`) | 7 (P5.1–P5.7) | none | 74 (`gp5_*`) | clean; `4a5` = one extra import (§8) |
| P6 | 5 (`568a`, `573c`, `580c`, `587c`, `592c`) | 4 (P6.1–P6.4) | none | 14 (`gp6_*`) | clean |

No violation; nothing was rejected.  Independently of the hunk parse: all 77 skeleton declaration headers
(multi-line, byte-exact) and all 26 `LEAF` docstrings occur verbatim in the pass-1 result; in the final file
76 headers and 25 docstrings do — the missing ones are exactly those of the removed false leaf P2.2.
Every surviving skeleton line occurs in the assembled file in skeleton order.

## 2. Assembly (task item 2)

`GF_assemble.py`, pass 1: all 34 hunks applied in one pass over the skeleton (replacements at `c`,
insertions after `a`), then checked:
* every inserted block occurs in the result **exactly once, contiguously** (34/34);
* **213 distinct helper names**, none duplicated across units and none re-declaring a skeleton name (each
  unit uses its own `gpN_` prefix, verified for all 213), so **no renaming** was needed;
* pass-1 result (`/tmp/gf_assembly/GF_Assembled_pass1.lean`, 5434 lines) compiles: 0 errors, exactly one
  `declaration uses sorry` (line 1394, leaf P2.2 `stage1_stable`) — the faithful control.

Pass 4 (de-duplication, task item 2): four helpers of later units restate a helper of an earlier unit with a
**byte-identical statement** (binders included); the later copy was dropped (with its docstring) and its
uses renamed, after asserting that the kept declaration precedes the removed block:

| removed | kept | uses renamed |
|---|---|---|
| `gp5_front_periodic` | `gp2_periodic_front` | 3 |
| `gp5_circDist_le_abs` | `gp2_circDist_le_abs` | 1 |
| `gp5_hamVF_eq_zero_of_notMem` | `gp3_hamVF_eq_zero_of_notMem` | 2 |
| `gp4_sameParam_symm` | `gp3_sameParam_symm` | 1 |

Final file: 285 top-level declarations = 76 skeleton declarations + 209 helpers (P0 7, P1 17, P2 24,
P3 70, P4 6, P5 71, P6 14).  Helpers with merely similar (not identical) statements — e.g.
`gp1_periodic_deriv`/`gp2_periodic_deriv`/`gp5_periodic_deriv`, `gp2_deriv_coordZ`/`gp4_deriv_z`,
`gp3_hamVF_congr`/`gp5_hamVF_congr`, the `gp6_*_stage` lemmas duplicating inline work of P0.2 — were
left alone (different hypotheses/forms; merging them is a porting-time cleanup, not an assembly step).

## 3. Unproved leaves (task item 3) — none; the false leaf P2.2 and its repair

After pass 1 the single remaining `sorry` was LEAF P2.2

```
theorem stage1_stable {L : ℝ → ℝ³} (h : Stage1 L) {δc : ℝ} (hδ : LocallyInjectiveFront L δc)
    (m : ℕ) (Hs : Fin m → ℝ³ → ℝ) (hHs : ∀ i, ContactMotionsHyp (Hs i)) :
    ∃ r > 0, ∀ a : ℝ^m, ‖a‖ < r →
      Stage1 (composeFlows m Hs (par a) ∘ L) ∧ LocallyInjectiveFront (composeFlows m Hs (par a) ∘ L) δc
```

which is **false as stated** (`GF_U_P2_REPORT.md` §2, numerically checked in `GF_U_P2_probe.py`): it
quantifies over every collar width `δc`, and for `L(θ) = (sin 2θ, sin θ, cos θ − ⅓cos 3θ)` — `Stage1`,
one transverse double point at circular distance exactly `π`, so `LocallyInjectiveFront L π` — the
`H^x`-bump perturbation at `L(3π/2)` moves the double point to circular distance `π − |a|/2 < π` for every
`a ≠ 0`, so the conclusion fails for all `‖a‖ < r`, whatever `r`.  I did not attempt to prove it (it cannot
be proved); the 45-minute budget was not needed for anything else since every other leaf came proved.

Repair (pass 2 of `GF_assemble.py`, exact-match replacements asserted to occur once):
* the leaf (docstring, statement, the unit's pointer comment, `sorry`) is removed and replaced by a
  `/-! … -/` note (final line 1400) recording the counterexample and the true form;
* `step2` (the only consumer; final line 2354) is re-proved with the half collar width, exactly the patch
  unit P2 tested in `/tmp/fd/p2/P2_step2test.lean`: `hδ' := gp2_locallyInjectiveFront_mono hδ …`
  (`δc/2`), `exists_CR_avoidance h hδ' 1 one_pos`, `gp2_stage1_stable_of_lt h hδ (half_pos hδ.1)
  (half_lt_self hδ.1) m Hs hHs` in place of `stage1_stable h hδ m Hs hHs`, `K2 (δc / 2)`/`K3 (δc / 2)` in
  `hU`/`hav`, `collar := ⟨δc / 2, hδa⟩`.  The statement of `step2` is unchanged (asserted); the rest of its
  body is the skeleton's.  `Stage2.collar` is existential, so nothing downstream sees the width.
* `gp2_stage1_stable_of_lt` (final line 1343) is the true form (`δ' < δc`), proved by unit P2 with axioms
  `[propext, Classical.choice, Quot.sound]` in the assembled file.

`unproved_leaves` = [] in the sense of the task: no leaf of the file is `sorry`; the one leaf not proved
as stated was removed as false, per the P2 report's instruction ("can be deleted from the skeleton or kept
as a dead `sorry`; nothing else references it") and the TN precedent (`TN_ASSEMBLY_REPORT.md` §3).

## 4. Compile, `sorry` count, axioms (task item 4)

* `cd work/lean && lake env lean ../drafts/fd/GF_Assembled.lean`: **0 errors**, ~21 s wall; warnings: two
  `linter.unusedVariables` on frozen statements (§8), nothing else (no `declaration uses sorry`).
* `grep -c sorry GF_Assembled.lean` = **0**; `grep -ci sorry` = 0.
* `/tmp/gf_assembly/GF_axioms.lean` (= the file + `#print axioms`):
  `SM.fd_generic_front` → `[propext, Classical.choice, Quot.sound]`; same for `SM.GenericFront.step1`,
  `step2`, `step3`, `exists_germ_isotopy`, `exists_collar`, `gp2_stage1_stable_of_lt`, and the four P6
  leaves.  `#check SM.fd_generic_front : SM.GenericFrontData`.

## 5. Statement byte-identity (task item 5)

`cmp <(sed -n 79,255p GenericFront_Statement.lean) <(sed -n 36,212p GF_Assembled.lean)` → identical
(177 lines, `namespace SM` … `def GenericFrontData … GenericFrontConclusion L Φ`).  The offset (skeleton
26 → assembled 36) is the rewritten module docstring (+9 lines) and the P5 import (+1).

## 6. Name-clash scan (task item 6)

`GF_clash_scan.py` indexes every non-private top-level declaration of the 657 `.lean` files under
`work/lean` (14,281 declarations), tracking `namespace`/`section`/`end` (block comments skipped), and
compares with the 285 fully-qualified names of `GF_Assembled.lean` (281 in `SM.GenericFront`;
`SM.GenericFrontHyp`, `SM.GenericFrontConclusion`, `SM.GenericFrontData`, `SM.fd_generic_front` directly in
`SM`):
* exact fully-qualified clashes: **0**;
* pre-existing `SM.GenericFront*` declarations in `work/lean`: **0** (namespace new);
* duplicate names inside the assembled file: **0**;
* short-name shadow in an enclosing namespace: **1**, `SM.GenericFront.SameParam` vs `SM.SameParam`
  (`SM/FrontSmooth.lean:246`, `SameParam {c : ℕ} (p q : Param c) : Prop`, a different type).
  `SM.FrontSmooth` is NOT in the import closure of this file (`#check @SM.SameParam` fails on a probe
  importing `SM.ContactMotions` + `SM.ParameterAvoidance`), so there is no ambiguity today — the clean
  compile confirms.  If a future module imports both, unqualified `SameParam` inside `namespace
  SM.GenericFront` becomes an overload resolved by elaboration (the arguments here are `ℝ`, so it still
  resolves), but the porter may prefer to keep `SM.GenericFront` and `SM.FrontSmooth` apart or qualify.
* informational (unrelated namespaces, no ambiguity; the file opens `ContactMotions` only for
  `hamFlow hamVF composeFlows ContactMotionsHyp`): the §1 notions `alpha`, `IsEmbeddedCircle`,
  `IsPositiveTransverse`, `IsLegendrian`, `IsCircleReparam`, `IsPushoffAnnulus`, `IsPositivePushoff`,
  `TransverselyIsotopic`, `IsCompactlySupportedAmbientIsotopy` ~ the same names in
  `SM.TransverseNeighborhood` (row 84 is already in `work/lean/SM/TransverseNeighborhood.lean`; the
  skeleton's §1 says these copies are "to be deduplicated at porting time by importing that module"),
  `alpha` ~ `SM.ContactMotions.alpha`, `front` ~ `SM.TransverseKnot.front`, `cuspSet` ~
  `SM.SpatialLink.cuspSet`/`SM.SmoothFront.cuspSet`, `doublePoints` ~ `SM.SmoothRegularLoop.doublePoints`,
  `par` ~ `SM.FrontRealize.Shape.par`, `IsPushoffAnnulus.circle` ~ `SM.CeRoundingNonVacuity.circle`.
* sanity: the `work/lean` names the file relies on (`SM.ContactMotions.{hamFlow, hamVF, composeFlows,
  ContactMotionsHyp, globalFlow}`, `SM.ParameterAvoidanceHyp`, `SM.ParameterAvoidance.zeroParams`,
  `SM.exists_param_avoiding`, `SM.fd_contact_motions`) are all found in the index.

## 7. Module docstring / directives (task item 7)

Since the `sorry` count is 0 the header docstring was rewritten (assembly provenance, layout, the units,
the P2.2 deviation, the extra import, the axioms line); the word does not occur anywhere in the file (any
case).  There were no `#print`/`#eval`/`#check` lines to remove (the units had none; asserted).

## 8. Notes for the integrator

* **Header**: one import beyond the skeleton's, `Mathlib.Analysis.Calculus.ContDiff.Bounds` (5th line;
  unit P5 needs the Leibniz rule `norm_iteratedFDeriv_mul_le` etc. for P5.4).  Kept as the P5 report asks.
* **Two linter warnings** (`linter.unusedVariables`) on FROZEN statements, left untouched by the freeze
  rule: `hHs` in P1.2 `noDoubleZero_of_notMem` (assembled line 883) and `hf'` in P5.3
  `exactGerm_of_cuspFlow` (line 2785).  At porting time rename them `_hHs`, `_hf'` (or drop the
  hypotheses — neither is needed) or add `set_option linter.unusedVariables false in`.
* **Docstring/proof mismatch inherited from unit P1** (statement unaffected): the frozen docstring of
  P1.1 `exists_cusp_avoidance` describes the printed per-cusp family `H₂, H₃`; the proof uses the family
  `χ·cos y, χ·sin y` with `n = 2` (`GF_U_P1_REPORT.md` §2).  Adjust the docstring when porting if wanted.
* **To move into `work/lean`**: the file is self-contained over `SM.ContactMotions`,
  `SM.ParameterAvoidance` and five Mathlib imports; `SM.GenericFront` is a new namespace.  The §1 copies of
  the row-84 notions could then be replaced by `SM.TransverseNeighborhood`'s (same text; the statement
  file's own plan) — a separate, statement-touching step that was out of scope here.
* Compile time ~21 s wall (8 threads) with a warm `.lake` cache.
