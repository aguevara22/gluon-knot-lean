# Wave 2 — unit C report (leaf `cf_thm_carrierfloor_C_of_bound`), 2026-09-15

File: `work/drafts/floor/W2_C.lean` (= `Wave2_Skeleton.lean` + this unit; 3176 lines).
Compile: `cd work/lean && lake env lean ../drafts/floor/W2_C.lean` — **exit 0, 0 errors**, 15 s warm
(log: scratchpad `W2_C_compile.log`).  Nothing under `work/lean` touched; no statement changed.

## 1. Result

| leaf | status |
|---|---|
| `cf_thm_carrierfloor_C_of_bound (hbound : TransverseFrontBound) : CarrierFloorCData` (l.3040) | **PROVED** (body only; header `:= by` kept) |

`grep -c sorry`: skeleton **6** → W2_C.lean **5** (= 2 docstring mentions l.30/l.418 + the three other-unit
leaves `ub_tangencyCount_of_admissible` l.967, `usw_P_switchAll` l.1718, `ulift_exists_transverse_lift` l.2931).
`diff Wave2_Skeleton.lean W2_C.lean | grep '^<'` = exactly one line, the leaf's `  sorry`.
Statement identity (`tools/wave1_stmt_check.py` parametrised on skeleton vs W2_C): **242 declarations checked,
242 byte-identical, 0 mismatches**.  Added lines scanned for `sorry|admit|native_decide|axiom|set_option|@[simp]|attribute`: none.

## 2. Helpers added (prefix `uc_`, all immediately before the leaf in §8.8, same section; whole-word grep over
`work/lean/SM/**`: 0 hits for each name)

| helper | line | content |
|---|---|---|
| `uc_mindegAZ_le_zZeroPart (f) (hf : f ≠ 0) (hz : zZeroPart f ≠ 0) : mindegAZ f ≤ mindegAZ (zZeroPart f)` | 2938 | `mindegAZ_spec hz` gives an attained `(mindegAZ (zZeroPart f), k)`; `k = 0` (else `coeffAt_zZeroPart_of_ne`), `coeffAt_zZeroPart_zero`, `(mindegAZ_spec hf).2` |
| `uc_floor_of_allPos (hbound) C X (h : CarrierFloorCHyp C X) (hpos : AllPosOrOneNeg C.P) (Db : PolygonDiagram C) (hD : Db.toDiagram = X.switchAll) : ((1 - X.writhe : ℤ) : ℝ) - \|rot\| ≤ mindegAZ (P X)` | 2954 | PLAN §3 (C) steps 2-7 on the normalised orientation: `ub_exists_admissibleDirection` (`h.turn_exists`, `h.turn_ne`, `hpos`); `ε := clearance C / 2`, `Admissible` from `h.turn_ne`, `clearance_pos h.generic`; `(ub_tangencyCount_of_admissible …).1`; `R : ℕ` with `(R : ℝ) = \|rot\|` from `rotationNumber_integer` (`Nat.cast_natAbs`, `Int.cast_abs`); `Db` all-negative via `hD`, `usw_switchAll_sign`, `isPositive_iff_sign_eq_one`; `ucurl_exists_curled` → `F', X', c, hnou, hP, hw, hneg'`; `urot_exists_rotated` → `G, c', hiff`; `hdown` from `hnou`/`hiff`; `ulift_exists_transverse_lift` → `K, hread, hwr`; `hbound K X' hread`; `P X' = ι (P X)` (`hP`, `hD`, `usw_P_switchAll`), `degAZ (ι (P X)) = −mindegAZ (P X)` (`ui_mirrorSubstitution.degAZ_eq`, `P_ne_zero`), `X'.writhe = −w − R` (`hw`, `hD`, `usw_switchAll_writhe`); `linarith` in ℤ, `exact_mod_cast`, `rw [hR]` |
| `uc_carrierFloorCHyp_reverse C X (h) (hpos : AllPosOrOneNeg (reversal C.P)) : CarrierFloorCHyp C.reverse X.reverse` | 3001 | step 1 transport via `CarrierFloorCHyp.of_diagram`: shadow `X.Γ.reverseShadow = single C.reverse` (`show` + `rw [h.shadow]`), positivity by `reverse_sign` + `isPositive_iff_sign_eq_one`, `turn_ne` by `principalTurn_reversal h.turn_exists`, alternative `Or.inl hpos` |
| `uc_floor (hbound) C X (h : CarrierFloorCHyp C X) : ((1 - X.writhe : ℤ) : ℝ) - \|rot\| ≤ mindegAZ (P X)` | 3020 | `rcases h.alternative`: normalised case with `Db := PolygonDiagram.ofDiagram X.switchAll h.shadow`, `hD := toDiagram_ofDiagram`; reversed case on `(C.reverse, X.reverse)` then `ur_P_reverse_all`, `reverse_writhe`, `rotationNumber_reversal h.turn_exists`, `abs_neg` |

Leaf body (l.3040): `refine ⟨fun C X h => uc_floor hbound C X h, fun C X h hz => ?_⟩`; `floor_zZero` from `uc_floor` and
`uc_mindegAZ_le_zZeroPart (P X) (P_ne_zero X) hz` cast to ℝ, `linarith`.  Total added: 4 helpers + leaf body, ≈ 105 lines
(the plan's ≈ 550 was for the pre-wave-1 accounting; every geometric step was already a proved or black-box leaf).

## 3. Black boxes consumed (hypothesis-free theorems, statements frozen)

`ub_tangencyCount_of_admissible` (B3), `usw_P_switchAll` (EQ), `ulift_exists_transverse_lift` (LIFT-3) — the three
remaining wave-2 sorries.  Everything else used is proved in the file: `ur_P_reverse_all`, `ub_exists_admissibleDirection`,
`usw_switchAll_sign`, `usw_switchAll_writhe`, `ui_mirrorSubstitution` (repaired `natAbs` form; only `degAZ_eq` consumed),
`ucurl_exists_curled`, `urot_exists_rotated`; accepted: `PolygonDiagram.ofDiagram/toDiagram_ofDiagram`,
`CornerRounding.Admissible/clearance_pos`, `rotationNumber_integer`, `rotationNumber_reversal`, `principalTurn_reversal`,
`Diagram.reverse_sign/reverse_writhe/isPositive_iff_sign_eq_one`, `mindegAZ_spec`, `P_ne_zero`, `coeffAt_zZeroPart_*`.

## 4. `#print axioms` (scratch copy `W2_C_axioms.lean` = W2_C.lean + print lines; log `W2_C_axioms.log`)

- `SM.cf_thm_carrierfloor_C_of_bound`: `[propext, sorryAx, Classical.choice, Quot.sound, SM.lp_lm, SM.lp_lm_uniqueness]`
  — `sorryAx` enters ONLY through the three black boxes of §3; `lp_lm*` through `P` (registered interfaces).
- `SM.uc_floor`: same list; `SM.uc_floor_of_allPos`: `[propext, sorryAx, Classical.choice, Quot.sound, SM.lp_lm]`.
- `SM.uc_carrierFloorCHyp_reverse`, `SM.uc_mindegAZ_le_zZeroPart`: `[propext, Classical.choice, Quot.sound]`.
- `SM.thm_floor_of_bound`: adds `SM.lit_homfly` (through `uf_a_floor_of_C`), as in wave 1.
Once B3/EQ/LIFT-3 land, `sorryAx` disappears from all of the above with no change here.

## 5. Notes for the assembler / reviewer

- The leaf is FALSE-free as stated: no statement change needed; no missing hypothesis found.  The reversed branch
  needs only `h.turn_exists` (`Regular C.P`) for `principalTurn_reversal`/`rotationNumber_reversal` — present in
  `CarrierFloorCHyp` (FR-FL-C1's redundant field earns its keep here, otherwise `(h.shadow ▸ X.generic).regular` would do).
- `ε := clearance C / 2` is one fixed admissible value (the printed proof's "ε ∈ (0, ε₁)"); `BClaim`'s quantifier is not needed.
- `R` is taken as a fresh `ℕ` witness (`obtain ⟨R, hR⟩ : ∃ R : ℕ, (R : ℝ) = |rot|`) rather than `k.natAbs` so that
  `norm_cast` does not rewrite `↑k.natAbs` to `|↑k|` midway (it did on the first attempt).
- Dependent-type rewrites (`x : X.switchAll.Γ.Crossing`, `x : X.reverse.Γ.Crossing`) are done through a type-ascribed
  `have e : … := lemma X x` then `rw [e]`; a bare `rw [lemma]` fails to find the pattern.
- Unused-variable warnings on FROZEN binders (`hturn` l.608, `hu` l.2211) are inherited from wave 1, left as is.
