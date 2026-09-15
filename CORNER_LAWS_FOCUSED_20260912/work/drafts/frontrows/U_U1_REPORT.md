# U_U1_REPORT — unit U1 (counts + degrees), 2026-09-14

File: `work/drafts/frontrows/U_U1.lean` (copy of `Skeleton_FINAL.lean` with the 12 U1 leaves proved).
Checked with `cd work/lean && lake env lean ../drafts/frontrows/U_U1.lean` (Lean v4.34.0-rc2, project Mathlib pin):
**0 errors**; the only warnings are the 14 `declaration uses 'sorry'` of the other units' leaves.
`grep -c sorry`: 26 before (Skeleton_FINAL.lean) → **14 after**.  `diff Skeleton_FINAL.lean U_U1.lean` removes only
the 12 `sorry` bodies; every definition, statement, name and docstring is verbatim.  File length 667 → 1609 lines
(+942; estimate was 1.1-1.4k).

## 1. Leaves proved (12/12)

`#print axioms` on each: `[propext, Classical.choice, Quot.sound]` — no `sorryAx`, no `SM.lp_lm`, no
`SM.ng_finite_word`.

**L-deg (4).**
- `delta_ne_zero` — `δ = (a − a⁻¹) z⁻¹`; `a − a⁻¹ ≠ 0` because `[a¹z⁰](a − a⁻¹) = 1` (`coeffAt_sub`, `coeffAt_a`,
  `coeffAt_single`); `z⁻¹` is the value of the unit `R.zUnit⁻¹`; `mul_ne_zero` in the domain `R`.
- `degAZ_delta = 1` — `degAZ_mul` (both factors nonzero) with `degAZ (a − a⁻¹) = 1` (`degAZ_eq_of_spec`: attained
  at `(1,0)`, every support exponent is `±1 ≤ 1`) and `degAZ z⁻¹ = 0` (`degA_single`).
- `degAZ_le_of_eq_pos` / `degAZ_le_of_eq_neg` — `degA_add_le` / `degA_sub_le` on the two summands, each summand's
  degree by `degAZ_mul` and `degAZ a = 1`, `degAZ a⁻¹ = −1`, `degAZ z = 0` (from `degA_a/aInv/z` through
  `degA_eq_degAZ`), then back to `ℤ` with `WithBot.coe_le_coe` (`u1_degAZ_le_max_of_degA_le`).

**L-cnt (8).**  Uniform route (PLAN_FINAL §4 L-cnt): `realize_downCount`/`realize_writhe` (words nonempty) turn
`D`, `w` into `downCountFrom [] / writheFrom []` of the letters; `u1_downCountFrom_append₃`/`u1_writheFrom_append₃`
split `X ++ P ++ Y` at the cut `c₀ = run X []` before the factor (`Closed.exists_run`); the exterior terms
`X.·[]`, `Y.·c₁` are literally the same on both sides because the two factors have the same typing effect
(β1's `run_*` lemmas), so each leaf reduces to the factor's own value on the symbolic cut, proved by one local
lemma per printed pattern (`u1_*_local`): the cut is decomposed exactly as in the corresponding `run_*` proof
(`step_eq_some_iff`, `exists_split_last`, `exists_cons_of_σ_succ`), the typing constraint on the bits is read off
the `r` step (`a = d`, `b = !d`, `p ≠ q`), each `step` is recorded by `step_of_prefix`, and the bits are evaluated
by `u1_downBit_l/σ`, `u1_signBit_l/r` (constants) and `u1_downBit_r_drop`, `u1_signBit_σ_drop` (the window at
the letter's position, via `List.drop_left'` / `u1_drop_eq₁`).  Values obtained:
- `typeI_counts`: curl `l_m σ_{m∓1} r_m` has `D = 1`, `w = 1` (both variants; the typing forces the through-strand
  bit, the crossing is positive, exactly one cusp is downward); the target `X ++ Y` is nonempty
  (`u1_typeI_target_ne_nil`: a curl cannot be typed from the empty cut).
- `typeII_counts`: the two crossings have opposite signs (`s(!d,b) + s(d,b) = 0` etc.), cusp bit unchanged; all
  four variants including the right-cusp ones (`r`'s down bit reads the same upper strand in both words).
- `typeIII_counts`: no cusp; the three crossing signs are the same multiset `{s(p,q), s(p,r), s(q,r)}` in both
  braid words (`ring`), either direction.
- `zigzag_counts`: `w = 0` locally, `D_local = if d then 0 else 2` (both cusps downward or both upward).
- `crossedCusp_counts`: the crossing has sign `−1` (arms oppositely directed), so `w' = w + 1`; `D` changes by
  `±1` with the flipped bit (`l_i d ↦ l_i (!d)`; `σ_i r_i ↦ r_i` reads the other arm).
- `circleDeletion_counts`: `l_m r_m` has `D = 1`, `w = 0`.
- `skein_counts`: `A`, `A'`, `C` each carry the single cusp letter with bit `d` (`D_local = if d then 0 else 1`
  in all three), and `s(a,d) + s(!d,a) = 0` (the printed (t,u) table), so `w_A + w_{A'} = 2 w_C`.
- `comm_counts`: the general disjoint-gadget argument of `run_comm_above/below` redone with the bits:
  `u1_downBit_window`/`u1_signBit_window` say a letter's bit reads only its `arity` window at its position,
  so the exchanged letters see the same windows (the reindexed letter at the shifted prefix), and the same holds
  after `reindex` (`act_reindex`, `idx_reindex`).  Both directions of `IsComm` via `IsCommStep` on `W`/`W'`.

## 2. Helpers added (51, all `u1_`-prefixed, in `SM.FrontRows`)

Before `delta_ne_zero`: `u1_aInv_ne_zero`, `u1_zInv_ne_zero`, `u1_coeffAt_aInv`, `u1_coeffAt_a_sub_aInv_one`,
`u1_a_sub_aInv_ne_zero`.  Before `degAZ_delta`: `u1_degAZ_of_degA`, `u1_degAZ_a`, `u1_degAZ_aInv`, `u1_degAZ_z`,
`u1_degAZ_zInv`, `u1_degAZ_a_sub_aInv`.  Before `degAZ_le_of_eq_pos`: `u1_degAZ_le_max_of_degA_le`.

Section `/-! ### U1 infrastructure -/` (`section U1Infra … end U1Infra`, placed before `comm_counts`, with a local
`open SM.FrontWord.Letter SM.FrontWord.Word`): `u1_downCountFrom_nil`, `u1_writheFrom_nil`,
`u1_downCountFrom_cons`, `u1_writheFrom_cons`, `u1_downCountFrom_append`, `u1_writheFrom_append`,
`u1_run_append_some`, `u1_downCountFrom_append₃`, `u1_writheFrom_append₃`, `u1_downBit_l`, `u1_downBit_σ`,
`u1_signBit_l`, `u1_signBit_r`, `u1_downBit_r`, `u1_signBit_σ`, `u1_downBit_window`, `u1_signBit_window`,
`u1_drop_eq₁`, `u1_downBit_r_drop`, `u1_signBit_σ_drop`, `u1_downBit_window'`, `u1_signBit_window'`,
`u1_typeI_left_local`, `u1_typeI_right_local`, `u1_zigzag_below_local`, `u1_zigzag_above_local`, `u1_circle_local`,
`u1_crossedCusp_l_local`, `u1_crossedCusp_r_local`, `u1_typeII_l_left_local`, `u1_typeII_l_right_local`,
`u1_typeII_r_left_local`, `u1_typeII_r_right_local`, `u1_typeIII_local`, `u1_skein_local`, `u1_comm_above_local`,
`u1_comm_below_local`, `u1_commStep_counts`, `u1_typeI_target_ne_nil`.

`u1_downCountFrom_append` / `u1_writheFrom_append` (`(V ++ W).downCountFrom c = V.downCountFrom c + W.downCountFrom c'`
when `run V c = some c'`) and the window lemmas are general enough for U2/U3 if they need word-layer counts.

## 3. Findings

- No leaf is false and none needs a stronger hypothesis.  The one subtlety: `typeI_counts` would be FALSE if the
  target `X ++ Y` could be empty (`realize ⟨[], _⟩` is the standard circle with `D = 1`, `w = 0`, while the curl
  gives `D = w = 1`), but a curl is never typable from the empty cut (`u1_typeI_target_ne_nil`), so the case does not
  arise; the other patterns' targets are nonempty syntactically or by the accepted `IsZigzagDeletion.ne_nil` /
  the built-in `X ++ Y ≠ []` of `IsCircleDeletion`.
- Rows closed by U1 alone: fields `comm_D/comm_w` (76), `typeII_D/typeII_w` (78), `typeIII_D/typeIII_w` (79).
  `#print axioms SM.ng_front_II/III` still shows `sorryAx` through the `d`/`B` fields (U5/U6 leaves), as planned.
- Compile time of the whole file ~8 s wall on this pod; scratch iterations were done on `/tmp/u1/*.lean`
  importing `SM.LinkLaurentRing` / `SM.FrontRealizeCorrespondence` only.
