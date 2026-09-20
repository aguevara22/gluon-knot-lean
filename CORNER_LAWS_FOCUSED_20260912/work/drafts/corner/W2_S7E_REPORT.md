# W2_S7E_REPORT — unit S7E (leaf unit U110-E `s7_sliding_law_at`, prefix `s7e_`), 2026-09-15 20:40 UTC / 4:40pm ET

File: `work/drafts/corner/W2_S7E.lean` = `W2_S7A2.lean` (which compiles: 0 errors, verified first) + ONE inserted
block (lines 6257-8477, 2221 lines, **175 declarations**: 17 `def`/`noncomputable def`, 158 theorems), placed inside
`section VertexEdge` immediately BEFORE the docstring of the leaf `s7_sliding_law_at` (now line 8482), i.e. right after
U110-A2's `end S7A2Assembly` (line 6255).  `diff W2_S7A2.lean W2_S7E.lean` = `6256a6257,8477`: a pure insertion,
**0 deleted lines**; no definition, structure, statement, name or docstring of the frozen file touched; no import added;
no `open` added; the leaf's `sorry` body is UNCHANGED (see §2: the contact sector is not closed).
Check (official): `cd work/lean && lake env lean ../drafts/corner/W2_S7E.lean` — **0 errors**, exit 0, ~40 s warm;
**9 `declaration uses sorry`** = exactly the 5 open leaves (`sg_daughters_products` 679, `s7_sliding_law_at` 8482,
`s7_bigon_law_at` 9647, `sft_same_sign` 11378, `sft_loop` 11531) + the 4 §6 row theorems (11626-11641); every other
warning is pre-existing in `Wave1_Assembled.lean` (the `sfta_` cosmetics of WAVE1_ASSEMBLY_REPORT §9, lines > 10000);
**0 warnings inside the block** (all unused-instance linter hits silenced with `omit [NeZero n] in`).
`grep -c sorry`: 11 before → 11 after (no `sorry` in the block).  `python3 tools/stmt_check.py W2_S7E.lean`: **49/49 PASS**.
Clash scan: `grep -rln s7e_ work/lean/{SM,CV,Bridge,RProof}` empty; no other `U_*.lean`/`W2_*.lean` uses the prefix.
Axioms (`#print axioms` on a scratch copy, 23 queries): the algebra `s7e_law_of_sectors` and all mark/key/order/owner
geometry (`s7e_nextMark_inr`, `s7e_owner_vl_eq_vertex`, `s7e_nextMark_wa`, `s7e_xm_mem_iff`, `s7e_hmem`,
`s7e_sign_const`, `s7e_isRotated`, `s7e_hbit`, `s7e_wind_eq`, `s7e_crossEquiv`, `s7e_isRotated_of_top_to_bottom`) =
`[propext, Classical.choice, Quot.sound]`; `s7e_cornerStateSum_eq_sum_term`, `s7e_law_at_of_sectors`,
`s7e_sliding_law_at_of_sectors`, `s7e_contactSector_of_pivotSplit` add `SM.lit_homfly` (through `C_X1.selector_form`);
`s7e_coef_eq`, `s7e_term_eq`, `s7e_spectatorSector_of`, `s7e_exists_spectatorSector`, `s7e_sliding_law_at_of_contact` =
`[propext, Classical.choice, Quot.sound, SM.lit_homfly, SM.lp_lm, SM.lp_lm_uniqueness]` (through U110-D's record route,
exactly as `s7d_cornerCoefficient_eq_of_cut`).  Nothing depends on `sorryAx`.
Uses from the file: U110-A (`s7a_visit`, `s7a_markMap`, `s7a_cross`, `s7a_sideComponentEquiv(_owner)`,
`s7a_side_hs/_hpar/_turn/_sgn`, `s7a_side_isDecomposition_iff`, `s7a_side_mem_carrierCrossings`,
`s7a_turn_ccpCornerPolygon`, `s7a_ccpCornerCount_eq`, `s7a_sliding_relocation_sign`, `s7a_between_or`), U110-A2
(`s7a2_IntervalLocal`, `s7a2_exists_intervalLocal`, `s7a2_sideLocal`, `s7a2_crossing_iff`,
`s7a2_continuousAt_edgeParameter`, `s7a2_pos_of_ne_zero`, `s7a2_carrierRotation_eq`), U110-C (`s7c_carrierWeight_eq_sel`,
`s7c_map_univ_eq_of_equiv`), U110-D (`s7d_gaussList_eq_of_strictMono`, `s7d_gaussList_isRotated_of_cut`,
`s7d_cornerCoefficient_eq_of_gaussList_rotated`, `s7d_cornerProduct_eq_of_equiv`, `s7d_positiveOverBit_eq_of_crossingSign`),
U110-B (only in the REPACKAGING §1.K: `s7b_PivotSplit`, `s7b_firstCrossingQ`, `s7b_secondCrossingQ`,
`s7b_slidingDecompositionEquiv`); accepted: `vertex_sides`, `VertexLocalData`, `ContactParameterWindows`,
`unaffected_visit_outside_window`, `vertexEdge_contact_tests`, `C_X1.selector_form`, `nextMark_no_mark_between`,
`markSuccessor_ne_self`, `owner_eq_iff`, `mem_carrierCrossings`, `pairVisit(_parameter)`, `visitTwin_unique`,
`visit_eq_or_twin`, `crossing_support_partner`, `visitParameter_eq_of_support_pair`, `traversalKey_lt_iff`,
`zmod_val_next_of_ne_last`, `last_index_val_succ`.

## 0. What this unit provides, in one paragraph

PLAN §3.3 sliding (1) and (4) are PROVED, (2)-(3) are REDUCED to two explicit hypotheses.  **(4) The algebra**:
`s7e_law_of_sectors` — two state sums indexed by the supports of `P₋`, `P₊` compared through a SPECTATOR sector
(supports avoiding the contact crossing, matched term by term) and a CONTACT sector (decompositions through the
contact crossing, both sides in bijection with `Ind(λ₁) × Ind(λ₂)`, termwise difference `s · g₁ · g₂`) give
`Σ f' − Σ f = s (Σ g₁)(Σ g₂)`; read on `C_X1.selector_form` completed by zeros (`s7e_term`, CS3's `stateTerm`
re-declared) this is `s7e_law_at_of_sectors` / `s7e_sliding_law_at_of_sectors` (the leaf statement from the two sectors,
each below a radius).  **(1) The spectator sector is PROVED** (`s7e_exists_spectatorSector : ∃ δ > 0, ∀ t < δ,
s7e_SpectatorSector hn h t`): the crossing bijection `x₋ ↦ x₊`, persistent crossings by support (`s7e_crossEquiv`,
`s7e_supportEquiv`, `s7e_spectatorEquiv`); for a support `S ∌ x₋` the decompositions correspond (U110-A), the selector
weights agree corner by corner (U110-A turns + U110-C's multiset selector, `s7e_wind_eq`), and the corner coefficients
agree (`s7e_coef_eq`) by U110-D's record route with the **relocated visit map** `s7e_visitMap` (persistent visits by
`s7a_visit`, the two visits of `x₋` to the two visits of `x₊`), whose `hmem` needs the new fact **`x₋` is a
self-crossing of `q` iff `x₊` is one of `e q`** (`s7e_xm_mem_iff`: the leg visit is adjacent to the vertex `μ_M`, the
`a`-visit's successor is the same persistent mark on both sides — `s7e_owner_vl_eq_vertex`, `s7e_nextMark_wa`, via a
small **`nextMark` calculus** `s7e_nextMark_inr/_inl` and sign constancy of the persistent `a`-visits through the wall,
`s7e_sign_const`), whose rotated Gauss lists come from key monotonicity up to the ONE relocated leg visit
(`s7e_isRotated`: no wrap for `M ≠ 0`; for `M = 0` the leg visit wraps from the top of the key order to the bottom or
back, two specialisations of U110-D's cut form, `s7e_isRotated_of_top_to_bottom/_bottom_to_top`), whose over bits come
from `s7a_side_sgn` and `s7a_sliding_relocation_sign` (`s7e_hbit`), and whose rotation equality is U110-A2's
`s7a2_carrierRotation_eq`.  **(2)-(3) the contact sector** is stated as `s7e_ContactSector hn h h₁ h₂ t` (exactly the
shape the algebra consumes) and REPACKAGED on U110-B's support bijections (`s7e_contactSector_of_pivotSplit`: two
`s7b_PivotSplit` instances + the termwise identity along `s7b_slidingDecompositionEquiv`); the leaf follows from it
(`s7e_sliding_law_at_of_contact`).  The leaf itself is left `sorry` (§2).

## 1. Proved (all `s7e_`; `{n} [NeZero n]` from `section VertexEdge`)

### 1.A Algebra (section `S7EAlgebra`)
* `s7e_term hn hP S := if h : IsDecomposition hn hP S then wind hn hP S * cornerProduct hn hP S h else 0`;
  `s7e_term_of_not`, `s7e_term_of_decomposition`; **`s7e_cornerStateSum_eq_sum_term : cornerStateSum hn hP = ∑ S,
  s7e_term hn hP S`** (`C_X1.selector_form` + `Finset.sum_attach` + completion by zeros).
* `s7e_sum_split` (a sum split into the `¬P`/`P` subtype sums), `s7e_sum_full_eq_of_zero`, `s7e_sum_subtype_eq_of_zero`
  (restriction to the decompositions inside a sector; `Equiv.subtypeSubtypeEquivSubtypeInter`).
* **`s7e_law_of_sectors`** (pure; `f f' g₁ g₂ : ℤ`-valued on `Fintype`s, predicates `p p' D D' D₁ D₂`, `e₀ : {S // ¬p S} ≃
  {S // ¬p' S}` with `f' (e₀ S) = f S`, zero off `D`/`D'`/`D₁`/`D₂`, `e : {S // D S ∧ p S} ≃ {S₁ // D₁ S₁} × {S₂ // D₂
  S₂}`, `e'` likewise, `hc : ∀ q, f' (e'.symm q) − f (e.symm q) = s * (g₁ q.1 * g₂ q.2)`) : `∑ f' − ∑ f = s * ((∑ g₁) *
  (∑ g₂))` (`Fintype.sum_equiv`, `Fintype.sum_prod_type`, `Finset.sum_mul_sum`).

### 1.B The sliding pattern and the two sectors (section `S7ESliding`)
* `s7e_leg g M a : Bool := decide (IsCrossing (g.sideTuple false g.sideBase).val {a, M})` — the leg of `x₋`;
  **`s7e_pattern (hn h t)`**: `P₋(t)` has exactly `{a, contactLeg (s7e_leg) M}`, `P₊(t)` exactly `{a, contactLeg (!s7e_leg) M}`,
  at EVERY `t` (`vertex_sides … .2.2.2.1 t t` and `… t g.sideBase`, `SlidingCrossingPattern`, `h.2`).
* `s7e_xm hn h t : Crossing P₋(t)`, `s7e_xp hn h t : Crossing P₊(t)` (+ `_val`, `_affected`);
  **`s7e_eq_xm_of_affected` / `s7e_eq_xp_of_affected`** (the ONLY contact-affected crossing of each side).
* **`s7e_ContactSector hn h h₁ h₂ t : Prop`** := `∃ e e', ∀ q, s7e_term hn hP₊ (e'.symm q).1 − s7e_term hn hP₋ (e.symm q).1 =
  (g.contactSign M a : ℤ) * (s7e_term hn₁ h₁ q.1.1 * s7e_term hn₂ h₂ q.2.1)` with `e : {S // IsDecomposition hn hP₋ S ∧ x₋ ∈ S}
  ≃ {S₁ // IsDecomposition hn₁ h₁ S₁} × {S₂ // …}`, `e'` on `P₊` at `x₊` (`hnᵢ := (contactHalfSizes_bounds hn h.1.1).i.1`,
  the frozen statement's own size proofs); **`s7e_SpectatorSector hn h t : Prop`** := `∃ e₀ : {S // x₋ ∉ S} ≃ {S // x₊ ∉ S}, ∀ S,
  s7e_term hn hP₊ (e₀ S).1 = s7e_term hn hP₋ S.1`.
* **`s7e_law_at_of_sectors`** (the law at one `t` from both sectors), **`s7e_sliding_law_at_of_sectors`** (the leaf
  statement from both sectors each below a radius; `δ := min`).

### 1.C The `nextMark` calculus (section `S7EMarks`; any generic `P`)
* `s7e_mEdge`, `s7e_mParam : Mark P → _` (edge label / parameter of a mark), `s7e_markKey_eq (markKey m = edge.val + param)`,
  **`s7e_markKey_lt_iff`** (edge label first, then parameter), `s7e_between_iff` (`traversalBetween` on keys, `Iff.rfl`),
  `s7e_markKey_bounds/_nonneg/_lt_n`, `s7e_edge_eq_of_key_sandwich`, `s7e_val_succ` (`(i+1).val` in the two cases),
  `s7e_visitParameter_pos/_lt_one`, `s7e_visit_eq_of_param` (same edge, same parameter ⇒ same visit).
* **`s7e_nextMark_inr`** (`nextMark (inr v) = inl (v.edge + 1) ∨ ∃ w, = inr w ∧ same edge ∧ param v < param w`),
  **`s7e_nextMark_inl`** (`nextMark (inl i) = inl (i+1) ∨ ∃ w on edge i, = inr w`) — from `nextMark_no_mark_between` +
  `s7a_between_or`, with the wrap `i = −1` handled; `s7e_nextMark_eq_of_no_between` (uniqueness); the betweenness
  templates `s7e_between_same_edge`, `s7e_between_inl_mark_inl`, `s7e_between_mark_mark_inl`; the characterisations
  **`s7e_nextMark_inr_eq_inl`** (no later visit on the edge), **`s7e_nextMark_inl_eq_inr`** (first visit on the edge),
  **`s7e_nextMark_inr_eq_inr`** (first later visit on the edge); `s7e_owner_inr_eq_next` (unselected visit and its
  successor share their owner), `s7e_owner_inl_eq_next`.

### 1.D Rotated Gauss lists (section `S7ERotated`; U110-D's cut form specialised)
* `s7e_isRotated_of_strictMono`; **`s7e_isRotated_of_top_to_bottom`** (the relocated visit `z` is the LAST of `X` in `P`'s key
  order, its image the FIRST in `Q`'s; everything else key-monotone); **`s7e_isRotated_of_bottom_to_top`** (`z` below a cut
  `c`, all others at or above `c`, its image the LAST).

### 1.E The two visits of a crossing (section `S7EContactVisits`)
* `s7e_va hc := pairVisit hc` (edge `a`), `s7e_vl hc` (edge `ℓ`) for `hc : IsCrossing Q {a, ℓ}`; `_fst_val`, `_edge`, `s7e_vl_fst`
  (same crossing), `s7e_va_param/_vl_param` (Cramer parameters), `s7e_vl_ne_va`, **`s7e_twin_va`, `s7e_twin_vl`**,
  **`s7e_visit_of_fst`** (exhaustion), `s7e_visit_eq_va/_vl` (by edge), `s7e_edge_of_fst`.

### 1.F The crossing and support bijections (section `S7ECrossEquiv`; generic `P Q`, `hs`, `x₋ x₊` unique affected)
* `s7e_crossMap` (`x ↦ if affected then x₊ else s7a_cross hs x _`), injective/surjective, **`s7e_crossEquiv : Crossing P ≃
  Crossing Q`** (`_xm`, `_symm_xp`, `_of_not`), **`s7e_supportEquiv : Finset (Crossing P) ≃ Finset (Crossing Q)`**
  (`Finset.map`; `s7e_mem_supportEquiv`, **`s7e_xp_mem_supportEquiv : x₊ ∈ E S ↔ x₋ ∈ S`**, `s7e_persistent_of_not_mem`,
  `s7e_supportEquiv_persistent`, **`s7e_supportEquiv_hSS'`** = U110-A's `hSS'`), **`s7e_spectatorEquiv : {S // x₋ ∉ S} ≃ {S // x₊ ∉ S}`**.

### 1.G A side polygon with its windows (section `S7ESidePolygon`; generic `Q`, leg `f`, `hw : ContactParameterWindows`)
* `s7e_a_ne_leg`, `s7e_a_ne_M`, `s7e_a_ne_M_sub_one`, `s7e_a_add_one_ne_M`, `s7e_M_ne_a_add_one` (from `ContactSeparated`).
* Window bounds: `s7e_persist_a` (persistent `a`-visit: `3η < |param − r|`), `s7e_persist_leg`, **`s7e_persist_M_sub_one`**
  (`param < 1 − 3η`), **`s7e_persist_M`** (`3η < param`), `s7e_va_param_near` (`|param v_a − r| < η`), `s7e_vl_param_near`,
  `s7e_vl_param_false` (`1 − η < param v_ℓ`), `s7e_vl_param_true` (`param v_ℓ < η`).
* `s7e_visit_cases` (every visit is `v_a`, `v_ℓ` or persistent), `s7e_persistent_of_edge_a/_leg/_ne`.
* **`s7e_owner_vl_eq_vertex`**: `owner S (inr v_ℓ) = owner S (inl M)` for every `S ∌ x` (`f = false`: `nextMark v_ℓ = μ_M`,
  the leg visit is the last mark on edge `M−1`; `f = true`: `nextMark μ_M = v_ℓ`, the first mark on edge `M`).
* **`s7e_nextMark_va_persistent`**, `s7e_no_later_of_nextMark_inl`, `s7e_min_of_nextMark_inr` (the successor of the
  `a`-visit and its minimality, read off `nextMark_no_mark_between`).

### 1.H The spectator sector at the wall, owners (section `S7ESpectator`; `(h : g.SlidingAt M a) (hloc : s7a2_IntervalLocal …) (t) (ht : t.val < δ) (hη : 0 < η)`)
* Abbreviations `s7e_hL`, `s7e_hs`, `s7e_hw b`, `s7e_hpar`, `s7e_hPm/_hPp` (the side genericities), `s7e_hxm/_hxp`
  (the contact crossings as `IsCrossing`), `s7e_hm/_hp` (uniqueness), `s7e_huniq_m/_p`, `s7e_va_fst_xm` etc.
* **`s7e_sign_const`** (sign constancy through the wall: `edgeParameter P₋ a j < r ↔ edgeParameter P₊ a j < r` for a
  persistent crossing `{a, j}` — `s7a2_continuousAt_edgeParameter` + the window at every `|u| < δ` + `s7a2_pos_of_ne_zero`),
  **`s7e_side_a`** (the visit form).
* **`s7e_visitMap`** (the relocated visit map), `_of_not`, `_va`, `_vl`, `_affected`; **`s7e_E`** (the support bijection of
  the wall), `s7e_E_hSS'`, `s7e_E_hSp`, `s7e_E_hSp'`, `s7e_xp_mem_E`, `s7e_xp_notMem_E`; **`s7e_e S hS`** (= U110-A's
  `s7a_sideComponentEquiv` on the persistent support), `s7e_e_owner`.
* `s7e_owner_vl_m`, `s7e_owner_vl_p`; **`s7e_nextMark_wa`** (`nextMark P₊ (inr w_a) = s7a_markMap hs (nextMark P₋ (inr v_a))`,
  by the two cases of `s7e_nextMark_inr`, sign constancy, `hpar`); **`s7e_xm_mem_iff`** (`x₋ ∈ cc q ↔ x₊ ∈ cc (e q)`);
  **`s7e_hmem`** (U110-D's `hmem` for `s7e_visitMap`).

### 1.I The key order relative to the contact visits (section `S7EKeys`; generic side polygon)
* `s7e_gkey` (`geometricVisitKey (CB.cg hn hQ) v = markKey hn hQ.1 (inr v)`, `rfl`), `s7e_param_lt_va_iff`,
  `s7e_va_lt_param_iff` (a persistent `a`-visit is before/after `v_a` iff its parameter is below/above `r`),
  `s7e_key_lt_vl_false` (`key u < key v_ℓ ↔ u.edge.val ≤ (M−1).val`), `s7e_vl_lt_key_false`, `s7e_key_lt_vl_true`
  (`↔ u.edge.val < M.val`), `s7e_vl_lt_key_true`, `s7e_key_vl_lt_eta` (`M = 0`, leg `M`: `key v_ℓ < η`), `s7e_eta_le_key`.

### 1.J The spectator sector, closed (section `S7ESpectatorKeys`, `S7EAssembly`)
* `s7e_side_a_gt`, `s7e_visitMap_edge` (edges preserved off the leg), `s7e_visitMap_ne_wl`; **`s7e_key_nonleg`** (key
  monotone on the visits other than the leg visit), **`s7e_key_leg_ne`** (`M ≠ 0`: the leg relocates without wrap),
  **`s7e_key_leg_zero_false`** (`M = 0`, leg `−1 ↦ 0`: last ↦ first), `s7e_key_vl_lt_eta_wall`, **`s7e_key_leg_zero_true`**
  (`M = 0`, leg `0 ↦ −1`: first ↦ last); **`s7e_isRotated`** (the rotated Gauss lists of corresponding spectator carriers).
* **`s7e_htwin`**, `s7e_sgn_contact` (`crossingSign P₊ a ℓ₊ = crossingSign P₋ a ℓ₋`, both directions of
  `s7a_sliding_relocation_sign` with the contact tests), **`s7e_hbit`**; `s7e_isDecomposition_E`; **`s7e_coef_eq`**
  (`cornerCoefficient hn hP₋ S q hS = cornerCoefficient hn hP₊ (E S) (e q) hS'`); **`s7e_wind_eq`**; **`s7e_term_eq`**
  (`s7e_term hn hP₊ (E S) = s7e_term hn hP₋ S` for `x₋ ∉ S`); **`s7e_spectatorSector_of`**;
  **`s7e_exists_spectatorSector (h) : ∃ δ > 0, ∀ t < δ, s7e_SpectatorSector hn h t`** (`δ := min` of A2's interval radius
  and `vertexEdge_contact_tests`' radius); **`s7e_sliding_law_at_of_contact`** (the leaf statement from
  `∃ δ > 0, ∀ t < δ, s7e_ContactSector hn h h₁ h₂ t`).

### 1.K The contact sector repackaged on U110-B (section `S7EContactRepack`)
* `s7e_hQC hn g h t b` (persistent crossings of a side agree with the centre's, `VertexCrossingData`'s last clause);
  **`s7e_contactSector_of_pivotSplit`**: from `hsplitm : s7b_PivotSplit (Interlaces hn hP₋) (Interlaces hn₁ h₁) (Interlaces
  hn₂ h₂) (s7b_firstCrossingQ hn h.1.1 h.1.2.2.2.1 (s7e_hQC … false)) (s7b_secondCrossingQ …) (s7e_xm hn h t)`, `hsplitp`
  (the same on `P₊` at `x₊`) and `hterm : ∀ q, s7e_term hn hP₊ ((s7b_slidingDecompositionEquiv … hsplitp).symm q).1 −
  s7e_term hn hP₋ ((s7b_slidingDecompositionEquiv … hsplitm).symm q).1 = s * (term₁ q.1.1 * term₂ q.2.1)` conclude
  `s7e_ContactSector hn h h₁ h₂ t`.

## 2. Not proved — the leaf and what closes it (read before the wave-3 assembly)

**The leaf `s7_sliding_law_at` is NOT closed; its `sorry` is untouched.**  Its body, once the contact sector is available,
is one line:
```
  exact s7e_sliding_law_at_of_contact hn g h h₁ h₂ ⟨δc, hδc, fun t ht =>
    s7e_contactSector_of_pivotSplit hn g h t h₁ h₂ (hsplitm t ht) (hsplitp t ht) (hterm t ht)⟩
```
What remains is exactly PLAN §3.3 sliding (2)-(3) at the level of U110-B's hypotheses — none of it is provided by any
wave-1/2 unit (U_S7B_REPORT §2 lists it as U110-B's unproved content):

1. **The interlacement transfer** `s7b_PivotSplit (Interlaces hn hQ) (Interlaces hn₁ h₁) (Interlaces hn₂ h₂)
   (s7b_firstCrossingQ …) (s7b_secondCrossingQ …) x` on BOTH sides (`Q = P₋(t)`, `x = x₋` and `Q = P₊(t)`, `x = x₊`; U_S7B
   §2.2, est. 500-800 lines).  Fields `split.inj₁/inj₂/disjoint`, `x_not₁/₂` are proved in U_S7B; open are `rel₁ rel₂`
   (the cyclic order of the images of a half's visits on `Q` is the half's — the edge maps `firstHalfIndex`/`secondHalfEdgeIndex`
   are cyclic-range embeddings, the same-edge parameter order is preserved off the cut and rescaled monotonically on it,
   and on the side polygon the side of `r` of a cut-edge visit is the centre's: `s7e_sign_const` applies at the centre too,
   since `s7a2_pos_of_ne_zero` covers `|u| ≤ t` including `u = 0`), `cross cross'` (no interlacing between the two halves'
   images: the visits of each lie in one of the two arcs cut by `x`'s two visits — the arc through `μ_M … μ_a` and the arc
   through `μ_{a+1} … μ_{M−1}`), `x_free₁/₂` (a half crossing does not interlace `x`), `x_split` (a crossing `y ≠ x` of `Q`
   not interlacing `x` is the image of a half crossing — needs the CONVERSE of `s7b_isCrossing_firstHalf_image`: a
   crossing of the centre with both labels in the range `M..a` and, on the cut edge `a`, parameter `< r`, is a crossing of
   `λ₁`; not in U_S7B).
2. **The termwise identity** `hterm` along `s7b_slidingDecompositionEquiv`: for `S₋ := insert x₋ (join S₁ S₂)` and `S₊ :=
   insert x₊ (join S₁ S₂)` (both decompositions by the equivs), `wind(S₊) cornerProduct(S₊) − wind(S₋) cornerProduct(S₋) =
   s · wind(S₁) cornerProduct(S₁) · wind(S₂) cornerProduct(S₂)`.  Its inputs, per PLAN §3.3 and U_S7B §3:
   * **`s7b_SlidingTransport.ret`** on both sides (U_S7B §2.1, est. 600-900 lines): the first-return law of the smoothing
     successor on the marks of `λ₁ ⊕ λ₂` under `s7b_slidingMark`.  §1.C's `nextMark` calculus (`s7e_nextMark_inr/_inl` and
     the `_eq_` characterisations) is the tool U_S7B §2.1(i) asked for; (ii) is `s7e_hpar`-type order transfer plus the
     half parameter laws `s7b_visitParameter_*`; (iii) is exactly `s7e_owner_vl_eq_vertex`'s adjacency
     (`nextMark v_ℓ = μ_M`, resp. `nextMark μ_M = v_ℓ`) and `s7e_nextMark_wa`'s side-of-`r` classification through
     `s7e_sign_const` — so the "approach clause" U_S7B feared is NOT needed: sign constancy on the interval replaces it.
     From `ret`: `componentEquiv : Component hn hQ S ≃ Component hn₁ h₁ S₁ ⊕ Component hn₂ h₂ S₂`,
     `carrierCrossings_eq_img_first/_second`, `carrierCrossingCount_eq_*` (all proved in U_S7B from `ret` + the split).
   * **Coefficients** (eq. s7c:sliding-coefficients): for each carrier of `S₋` the coefficient equals that of the
     corresponding half carrier — `s7d_cornerCoefficient_eq_of_cut` with `φ := s7b_firstVisitQ⁻¹`/`s7b_secondVisitQ⁻¹` on
     the carrier's visits, `hmem` from `carrierCrossings_eq_img_*`, `hmono/hcut` from the key decoding of the half labelling
     (cut at the contact, `c := M.val + …`), `htwin` from `s7b_*VisitQ_visitTwin`, `hbit` from `s7d_positiveOverBit_eq_of_smul`
     with `HalvesData.cut_segments` (cut edges `r • edge P a`, `(1−r) • edge P a`) — and **`hr`**, the rotation equality,
     which for the two carriers through the contact (`λ₁`'s carrier through its vertex `0` vs `Q`'s carrier through `μ_M`;
     `λ₂`'s through its vertex `0` vs `Q`'s through the pivot) is the printed **principal-angle addition** in one open
     half-plane (eq. s7c:turn-short-a/b, sm-4:343-357): the side carrier has ONE extra corner (`v_a` on `P₋` with leg `M−1`;
     the leg visit on `P₊`) whose two adjacent turns add to the half's single contact turn — NOT in the library (U110-A2
     explicitly excludes it; the ingredients are `principalAngle_smul`, `s7i_principalTurn_eq_of_pos_smul`,
     `rotationNumber = Σ principalTurn / 2π`); for the other carriers it is a family through the wall / U110-I's ledger.
   * **Selectors** (eq. s7c:short-selector, eq. s7c:sliding-selector-difference): `wind(S₋) = Q_sp · wt(L)` with the one
     changed carrier via `s7c_carrierWeight_refine` (needs the ORDERED corner bijection `{i // i ≠ j} ≃ ZMod k₁`,
     turn-preserving — U_S7B §2.3, est. 400-600 lines) and `s7c_sliding_selector_difference` with `s := contactSign`
     (`vertex_contact_signs`) and `τ := turn at μ_M`.
   * **Bookkeeping**: `cornerProduct(S₋) = cornerProduct(S₁) · cornerProduct(S₂)` (`Fintype.prod_sum_type` along
     `componentEquiv`), `wind` likewise with the refinement, then `s7c_sliding_selector_difference`.

**Estimated remaining size**: 2,500-4,000 lines (B's three items 1,500-2,300 + the relocated rotation equality 300-500 +
coefficient/selector/bookkeeping assembly 600-900).  **Nothing believed false.**  No missing hypothesis found in the
frozen statement.  The one implicit hypothesis the spectator sector needed beyond A2's interval data is the contact
TEST radius (`vertexEdge_contact_tests`, for `s7a_sliding_relocation_sign`'s `htest`), intersected into `δ`.

Two truth-relevant observations from the proof: (a) the spectator sector is NOT a plain `s7a_visit` transport — a spectator
carrier may have `x₋` as a self-crossing (e.g. `S = ∅`), and then its Gauss list on `P₊` is a ROTATION of the mapped list
when `M = 0` (`s7e_isRotated_of_top_to_bottom/_bottom_to_top`), not equal to it; the equality of coefficients still holds
through `RecordIso` (U110-D's `hrot` form).  (b) the leg visit and `μ_M` are adjacent marks on each side, so the
relocation `x₋ ↦ x₊` never changes any owner — this is what makes `s7e_xm_mem_iff` hold for EVERY persistent support.

## 3. How to consume

* Wave-3 assembler / the U110-B follow-up: the leaf body is the one-liner of §2 once `hsplitm t ht`, `hsplitp t ht`, `hterm t
  ht` exist below a radius `δc`; the shapes are printed in `s7e_contactSector_of_pivotSplit`'s statement (line 8452) —
  `hQ := s7a_sideGeneric g b`, `hsep := h.1.1`, `hm := h.1.2.2.2.1`, `hQC := s7e_hQC hn g h t b`, `x := s7e_xm hn h t` /
  `s7e_xp hn h t`.
* Anyone proving `ret`: `s7e_nextMark_inr_eq_inl/_inl_eq_inr/_inr_eq_inr` give `nextMark` from parameter minimality;
  `s7e_owner_vl_eq_vertex` and `s7e_nextMark_wa` are the contact-adjacent steps of the first-return law already done;
  `s7e_sign_const`/`s7e_side_a`/`s7e_side_a_gt` classify persistent `a`-visits by their side of `r` on either side (and,
  through `s7a2_pos_of_ne_zero` at `u = 0`, on the centre, i.e. relative to the halves' cut).
* The bigon branch (U110-F/K): §1.C-1.F are branch-independent (generic polygons; the crossing bijection needs only
  "unique affected crossing on each side", which fails for the bigon — there the persistent transport `s7a_cross` alone is
  the spectator map, and `s7e_isRotated_of_strictMono` + `s7a_side_mem_carrierCrossings` suffice for ineligible `T`).

## 4. Mathlib / Lean pitfalls hit (v4.34.0-rc2 pin)

* Section variables used only in a PROOF are not included, for `def`s as well as theorems (a `def` whose body mentions
  `hn` got no `hn` argument): `include … in` before the docstring, or explicit binders.  `include … in` and
  `omit [NeZero n] in` both go BEFORE the docstring (after it: "expected 'lemma'").
* `x₋`, `x₊` are not identifiers (`₊`, `₋` are not subscript letters/digits): use `xm`, `xp`.
* `rw [s7e_between_iff] at hb` / `rw [s7e_markKey_eq]` / `rw [s7e_gkey]` without explicit `hn hP` leave `?hP` unassigned
  (only `?hP.1` appears in the pattern), which then poisons every later `linarith` with "resulting expression contains
  metavariables": always pass `hn hP` explicitly.
* `cases hf : f` fails ("generalize: result is not type correct") when `f` occurs in dependent hypotheses (`hc : IsCrossing
  Q {a, contactLeg f M}`); `cases f` (no naming) works on a variable, and for a CONSTANT like `s7e_leg g M a` use
  `rcases Bool.eq_false_or_eq_true (s7e_leg g M a) with hf | hf` and pass `hf` to lemmas stated with a Bool VARIABLE.
* `rintro rfl` for `w ≠ z` erases `z` from the context; later references to `z` fail — use `intro h; rw [h] at …`.
* `rw [hM]` with `hM : M = 0` fails (motive) when `M` occurs in dependent hypotheses; rewrite the derived ℕ fact
  (`have : M.val = 0 := by rw [hM, ZMod.val_zero]`) instead.  `ZMod.val_neg_one` is stated on `ZMod (n+1)`; on `ZMod n`
  use `last_index_val_succ : (-1 : ZMod n).val + 1 = n`; `zmod_val_next_of_ne_last` gives `(i+1).val = i.val + 1` for `i ≠ -1`.
* `abs_of_neg` needs STRICT negativity: from `¬ r < p` and `3η < |p − r|` first get `p ≠ r`, or use `abs_of_nonpos`.
* `rw [s7a_visit_support, s7a_visit_edge]` on `(s7a_visit hs u hu).1.val = {(s7a_visit hs u hu).2.val, j}` breaks the
  dependent `.2`; both sides are `rfl`-equal to the `u`-form, so `exact hj` directly.
* `dite_eq_left (h : p)` needs `h` stated with the SYNTACTIC condition of the `if` (`show ContactAffected M a (s7e_va hc).1.val
  from …`), not a defeq one; `ite_eq_left/right` replace the deprecated `if_pos/if_neg`.
* `omit [NeZero n] in` cascades: once a lemma no longer needs the instance, its users may not either (the linter reports
  them one round later).

## 5. Left

The leaf `s7_sliding_law_at` (its `sorry` untouched; closed conditionally by `s7e_sliding_law_at_of_contact` +
`s7e_contactSector_of_pivotSplit`, §2).  Not touched (other units): `sg_daughters_products`, `s7_bigon_law_at`,
`sft_same_sign`, `sft_loop`, the four §6 row theorems.
