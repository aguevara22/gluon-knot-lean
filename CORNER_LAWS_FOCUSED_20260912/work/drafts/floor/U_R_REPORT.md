# U_R_REPORT — unit U-R (clause (R) of cf:thm-carrierfloor), 2026-09-15

File: `work/drafts/floor/U_R.lean` (byte-identical copy of `Statements_FINAL.lean` + the U-R proof; no statement,
definition, name or docstring changed — `diff Statements_FINAL.lean U_R.lean` shows only the inserted helpers and the
replaced leaf body).

Compile: `cd work/lean && lake env lean ../drafts/floor/U_R.lean` — exit 0, **0 errors**, 22 warnings
`declaration uses sorry`, all at the other units' leaves (lines 189, 328, 439-737: `CarrierFloorAData.junction_local`,
`CarrierFloorCData.floor_support`, `ua_*`, `ub_*`, `usw_*`, `ui_*`, `urot_*`, `ucurl_*`, `ul_*`, `ulift_*`,
`cf_thm_carrierfloor_C_of_bound`, `uf_*`); none in §8.1. `grep -c sorry`: Statements_FINAL.lean 25 → U_R.lean 24
(textual hits; two are prose mentions in the header docstring and the §8 header — declarations with `sorry` 23 → 22).

## Leaves proved (1 of 1)

- `ur_P_reverse_all (X : Diagram) : P X.reverse = P X` — exactly PLAN_FINAL §3 (R):
  `congrFun (coefficient_transport (fun D => P D.reverse) P ur_reverse_rcompetitor P_rcompetitor) X`.
  Consequently `cf_thm_carrierfloor_R : CarrierFloorRData` (frozen assembly) is now sorry-free.

## Leaves left

None in this unit.

## Helpers added (both in §8.1, immediately before the leaf's docstring, `ur_` prefix)

- `ur_isCrossingFreeCircle_reverse (D : Diagram) (h : D.IsCrossingFreeCircle) : D.reverse.IsCrossingFreeCircle`
  (4 lines). `IsCrossingFreeCircle = (Γ.c = 1 ∧ IsEmpty Γ.Crossing)` (LinkDiagram.lean:587); `D.reverse.Γ` is
  definitionally `D.Γ.reverseShadow` (reverse = `pullback … reverseMap`, 1213; `Shadow.reverseShadow` is an `abbrev`
  with the same `c`, 1113), so the first conjunct is the given `hc` and the second is
  `D.Γ.reverseCrossingEquiv.isEmpty` (`Equiv.isEmpty`, with `reverseCrossingEquiv : Γ.reverseShadow.Crossing ≃
  Γ.Crossing`, LinkDiagram.lean:1199). The plan estimated 15 lines; the equiv makes it one term.
- `ur_reverse_rcompetitor : RCompetitor (fun D : Diagram => P D.reverse)` (7 lines): `planar` from
  `reverseCarries_planarIsotopic` (LinkMoves.lean:2459) + `P_planar` (PolynomialBlock.lean:604); `reidemeister_I/II/III`
  from `reverseCarries_RI/RII/RIII` (3071/3117/3231) + `P_reidemeister_I/II/III` (605-607); `circle` from the helper
  above + `P_circle` (609); `skein` from `IsSkeinTriple.reverse` (3318, sides kept) + `P_skein` (638).

Total added: ~30 lines including docstrings (the plan budgeted 250; every ingredient was already accepted).

## Axioms (`#print axioms`, run on a scratchpad copy — nothing appended to the unit file)

- `ur_isCrossingFreeCircle_reverse`: [propext, Classical.choice, Quot.sound]
- `ur_reverse_rcompetitor`: [propext, Classical.choice, Quot.sound, SM.lp_lm]
- `ur_P_reverse_all`: [propext, Classical.choice, Quot.sound, SM.lp_lm, **SM.lp_lm_uniqueness**]
- `cf_thm_carrierfloor_R`: [propext, Classical.choice, Quot.sound, **SM.lit_homfly**, SM.lp_lm, SM.lp_lm_uniqueness]

**For the assembler (PLAN_FINAL §4 says "expected [propext, Classical.choice, Quot.sound, SM.lp_lm] for the (R)(A)(B)
theorems" — that is not attainable for (R) and should be corrected in the plan/AUTHOR_NOTES):**
1. `SM.lp_lm_uniqueness` is unavoidable for the leaf: `coefficient_transport` itself depends on it (its header,
   CoefficientTransport.lean:3, and `#print axioms SM.coefficient_transport` = [.., SM.lp_lm, SM.lp_lm_uniqueness]).
   Any proof of `P X.reverse = P X` via lp:coefficient-transport — the printed route — carries it.
2. `SM.lit_homfly` enters through the FROZEN assembly, not through U-R: the `knot_reverse` field of
   `cf_thm_carrierfloor_R` is proved with `P_eq_homfly` + `homfly_descent` (Statements_FINAL.lean §8.1), and
   `P_eq_homfly` = [.., SM.lit_homfly, SM.lp_lm, SM.lp_lm_uniqueness]. A `lit_homfly`-free alternative exists
   (`LinkEquiv X X'` is `Relation.EqvGen` of the four generators, LinkMoves.lean:760, and `P_rcompetitor` gives `P` invariance
   generator by generator — `Relation.EqvGen.rec`/`eqvGen_carries`-style induction, ~15 lines), but the assembly is
   frozen so I did not touch it; the assembler can decide whether that is wanted.
   Both axioms are policy axioms (work/lean/axiom-policy.json: `lp:lm-uniqueness → SM.lp_lm_uniqueness`,
   `lit:homfly → SM.lit_homfly`).

## Mathlib / library pitfalls met

- None serious. Two small notes: (i) the `sorry`-warning text uses backticks (``declaration uses `sorry` ``), so a
  `grep 'sorry'` count is the reliable check, not `'sorry'` with ASCII quotes; (ii) the `Q` in `coefficient_transport`
  must be written with the explicit binder type `fun D : Diagram => P D.reverse` for the `RCompetitor` instance to elaborate
  against `RCompetitor (fun D => P D.reverse)` without a type ascription (elaboration is otherwise fine).

## Correctness / fidelity notes

- The leaf is TRUE as stated and needs no extra hypothesis: the argument is on all oriented link diagrams (the printed
  proof's generality, sm-3:4340ff); the row field `P_reverse` restricts to `componentCount = 1` (FR-FL-R1) and is derived
  from the leaf by discarding the hypothesis, as in the frozen assembly.
- Nothing numerical to probe: the proof is a direct transport of accepted invariance lemmas through
  `coefficient_transport`.
- No file under work/lean was written; scratch files live in the session scratchpad only.
