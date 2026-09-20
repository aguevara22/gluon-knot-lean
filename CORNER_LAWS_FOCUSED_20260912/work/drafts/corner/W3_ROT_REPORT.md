# W3_ROT_REPORT — wave 3, unit ROT (prefix `s7q_`, serving the leaf `s7_sliding_law_at`), 2026-09-15 ~21:50 UTC / 5:50pm ET

File: `work/drafts/corner/W3_ROT.lean` = `W3_Skeleton.lean` + ONE inserted block (lines 23-1277, 1255 lines, **58 declarations**:
48 theorems, 7 defs, 3 structures), placed inside `section VertexEdge` immediately BEFORE the docstring of the leaf
`s7_sliding_law_at` (now line 1278).  `diff W3_Skeleton.lean W3_ROT.lean` = `22a23,1277`: a pure insertion, **0 deleted
lines**; the statements, names and docstrings of `s7_sliding_law_at`, `s7_bigon_law_at`, `thm_C_S7_of`, `thm_C_S7_of_floor`,
`thm_C_S7` are untouched; the leaf's `sorry` body is UNCHANGED (the leaf is NOT closed, §4).
Check (official): `cd work/lean && lake env lean ../drafts/corner/W3_ROT.lean` — **0 errors**, exit 0, ~15 s warm;
**6 `declaration uses sorry`** = the 4 black boxes of this unit (`s7q_box_split` 966, `s7q_box_ret` 1035, `s7q_box_order` 1067,
`s7q_box_carriers` 1109) + the 2 leaves (`s7_sliding_law_at` 1281, `s7_bigon_law_at` 1300); no other warning.
`grep -c sorry`: 2 (skeleton) → 8 (6 declarations + 2 prose mentions).  `python3 tools/stmt_check.py`: 4/49 on both
`W3_Skeleton.lean` and `W3_ROT.lean` (the same 4: the checker expects the assembled file; unchanged by this unit).
Clash scan: `grep -rln s7q_ work/lean/{SM,CV,Bridge,RProof}` empty; no other draft uses the prefix.
Axioms (`#print axioms` on a scratch copy): all pure lemmas of §S7QAngles/§S7QMerge/§S7QAlgebra and the key decoding
(`s7q_principalAngle_add_of_side`, `s7q_two_turn_perturb`, `s7q_principal_delete`, `s7q_CornerMerge.rotationNumber_eq`,
`s7q_principal_three_a`, `s7q_term_difference`, `s7q_key_decoding`, `s7q_keys_first`, `s7q_pre_of_symm`) =
`[propext, Classical.choice, Quot.sound]`; `s7q_term_eq_of_rowData` adds `lit_homfly` (through `cornerCoefficient`);
`s7q_coef_first`, `s7q_rowData_of_transport` add `lp_lm, lp_lm_uniqueness` (U110-D's record route, as
`s7d_cornerCoefficient_eq_of_cut`); `s7q_box_rows`, `s7q_sliding_law_at_of_boxes` add `sorryAx` (through the boxes only).

## 0. What this unit provides, in one paragraph

PLAN §3.3 sliding (2)-(3) at the level of U110-E's contact sector is REDUCED to four explicit geometric black boxes, and
everything between them and the leaf is PROVED: (c) the per-row bookkeeping — products over the carriers along U110-B's
`componentEquiv`, the ONE refined selector per side and `s7c_sliding_selector_difference` — gives the termwise identity
`hterm` (`s7q_term_difference`, `s7q_term_eq_of_rowData`); the coefficient clause of a row is `s7d_cornerCoefficient_eq_of_cut`
carrier by carrier with `hmem` (from `carrierCrossings_eq_img_*`) and `htwin` PROVED (`s7q_coef_first/_second`) and the
key decoding `hmono`/`hcut` PROVED from the same-edge order agreement alone (`s7q_key_decoding`, `s7q_keys_first/_second`,
`s7q_cutFirst_of`); (a) the exact angle identities — half-plane additivity (eqs. s7c:turn-short-a/b), the two-turn
perturbation, the three-turn ↔ two-turn merge and the exact vertex deletion — with their polygon-level sum bookkeeping
(`s7q_CornerMerge`, `s7q_CornerPerturb` ⇒ `rotationNumber` equal, turn multiset refined by one turn).  The leaf statement
follows from the boxes (`s7q_sliding_law_at_of_boxes`, the one-liner of W2_S7E_REPORT §2 with the boxes explicit).  Two
DEFECTS in the specification of (a) were found and corrected (§3): the printed two-turn form is a three-turn form on the
side polygon, and — more importantly — the germ moves EVERY vertex (`WallGerm.curve` is an arbitrary continuous family), so
the rotation/over-bit/turn-sign equalities between a side carrier and a half carrier are continuity statements, not exact
positive-multiple identifications; the exact lemmas here are the algebraic core of the corrected route (§3.2).

## 1. Proved (all `s7q_`; `{n} [NeZero n]` from `section VertexEdge`)

### 1.A Principal-angle addition (section `S7QAngles`, lines 33-203; pure plane geometry)
* `s7q_det_swap`; **`s7q_principalAngle_add_of_side (hτ : τ ≠ 0) (h1 : sign (det r u) = τ) (h2 : sign (det r w) = τ) :
  ∠(r,u) + ∠(u,w) = ∠(r,w)`** — eq. s7c:turn-short-a ("no hidden multiple of `2π`": the three angles agree mod `2π` by
  `principalAngle_coe_angle`, `∠(r,u), ∠(r,w) ∈ (0,π)` or `(−π,0)` by `principalAngle_sign`/`_bounds`, `∠(u,w) ∈ (−π,π]`,
  so the integer is `0`); `s7q_principalAngle_swap (RegularPair u v) : ∠(v,u) = −∠(u,v)` (the library's
  `principalAngle_swap` lives in `SM.ZeroRotationSeed`, not imported); **`s7q_principalAngle_add_of_side'`** — eq.
  s7c:turn-short-b `∠(u,w) + ∠(w,r) = ∠(u,r)`; **`s7q_two_turn_perturb`**: `sign det(w,u) = sign det(w,u')`, `sign det(r,u) =
  sign det(r,u')` ⇒ `∠(w,u) + ∠(u,r) = ∠(w,u') + ∠(u',r)` (replacing a direction by a perturbed one on the same side of both
  neighbours keeps the sum of the two adjacent turns); **`s7q_principal_delete`**: `d = α r + β u` (`α, β > 0`), `u`, `w` on one
  side of `r` resp. `d`, and `r`, `d` on one side of `e` ⇒ `∠(e,r) + ∠(r,u) + ∠(u,w) = ∠(e,d) + ∠(d,w)` (exact deletion of the
  corner between `r` and `u`).

### 1.B Corner correspondences at the polygon level (section `S7QMerge`, 205-453)
* `s7q_sum_eq_of_merge` (`Σ f = Σ g` for `e : {i // i ≠ j} ≃ ZMod k₁`, `g ∘ e = f` off a finite set `T`, and on `T` the sums
  differ by `f j`), `s7q_sum_eq_of_perturb` (`e : ZMod k ≃ ZMod k₁`, `g ∘ e = f` off `T`, equal sums on `T`).
* **`structure s7q_CornerMerge Q Q₁ j`** (`ne₁ ne₂ ne₃`, `e : {i // i ≠ j} ≃ ZMod k₁`, `turn_eq` at every `i ≠ j`,
  `principal_eq` off `{j−1, j+1}`, `principal_three : pt₁(e(j−1)) + pt₁(e(j+1)) = pt(j−1) + pt(j) + pt(j+1)`);
  **`.rotationNumber_eq`**, **`.turns_eq : s7c_turns Q = s7c_turns Q₁ + {turn Q j}`**.
* **`s7q_principal_three_a`** (`P₋`, leg `M−1`: `r → u_in → u_out → w` vs `r → u_out' → w`) and **`s7q_principal_three_b`**
  (`P₊`, leg `M`: `w → u_in → u_out → r` vs `w → u_in' → r`): the `principal_three` field from edge data (positive multiples via
  `s7i_principalTurn_eq_of_pos_smul`) and the sign data `sign det(r,u_in) = sign det(r,u_out) = sign det(r,u_out') = η`,
  `sign det(w,u_out) = sign det(w,u_out') = σ` (turn-short + two-turn perturbation).
* **`structure s7q_CornerPerturb Q Q₁ p`** (`e : ZMod k ≃ ZMod k₁`, `turn_eq`, `principal_eq` off `{p−1, p}`,
  `principal_two`); `.rotationNumber_eq`, `.turns_eq : s7c_turns Q = s7c_turns Q₁`; **`s7q_principal_two`** (the
  `principal_two` field from edge data + `s7q_two_turn_perturb`).
* On carriers: `s7q_carrierRotation_eq_of_merge`, **`s7q_carrierWeight_eq_of_merge : wt(q) = sel(turns(q₁) + {turn j})`**
  (eq. s7c:short-selector in the multiset form `s7c_sliding_selector_difference` consumes), `s7q_carrierRotation_eq_of_perturb`,
  `s7q_carrierWeight_eq_of_perturb : wt(q) = wt(q₁)`.

### 1.C The row algebra (section `S7QAlgebra`, 455-566)
* `s7q_prod_eq_of_except` (a product through `e : B ≃ D` with one exceptional value).
* **`s7q_term_difference`** (abstract, `D = Component S₁ ⊕ Component S₂`): coefficients transported, weights transported
  except at `a₀` (`P₋`) / `a₀'` (`P₊`), `a₀ ≠ a₀'`, `w a₀ = sel m₀ ∋ s`, `w a₀' = sel m₀' ∋ −s`, refined weights `sel(m₀ + {τ})`,
  `sel(m₀' + {τ})` ⇒ `W₊C₊ − W₋C₋ = s (Π w)(Π c)`; `Q_sp := Π_{D ∖ {a₀,a₀'}} w` "without assuming it nonzero" (eqs.
  s7c:sliding-selector-factors/-difference via `s7c_sliding_selector_difference`).
* **`structure s7q_RowData hn hQ hn₁ hn₂ hP₁ hP₂ hS hS₁ hS₂ a₀ m₀ τ : Prop`** — `∃ e : Component S ≃ Component S₁ ⊕ Component S₂`,
  coefficients `= Sum.elim c₁ c₂ (e q)`, weights `= Sum.elim w₁ w₂ (e q)` for `e q ≠ a₀`, `wt(e.symm a₀) = sel(m₀ + {τ})`.
* **`s7q_term_eq_of_rowData`**: two row data (`P₋` at `a₀`, `P₊` at `a₀'`) ⇒ `s7e_term hQp Sp − s7e_term hQm Sm = s (term₁ S₁ · term₂ S₂)`.

### 1.D Row data from RET + SPLIT (section `S7QTransport`, 568-946)
* `s7q_CutFirst/_Second` (the cut-form inputs of `s7d_cornerCoefficient_eq_of_cut` for one carrier: `∃ c, hmono ∧ hcut ∧ hbit ∧ hr`).
* **Key decoding**: `s7q_key_eq` (`geometricVisitKey = edge.val + parameter`), `s7q_firstHalfIndex_val : (M + i).val = (M.val + i.val) % n`,
  `s7q_secondHalfEdgeIndex_val`, `s7q_mod_cases`, **`s7q_key_decoding`** (abstract: half keys `i + p`, image keys
  `((m + i) % n) + p'`, same-edge order of `p'` = that of `p` ⇒ image order = half order cut at `c = n − m`),
  **`s7q_keys_first/_second`** (the `hmono`/`hcut` clauses for `s7b_firstVisitQ`/`s7b_secondVisitQ` from the ONE hypothesis
  `hord` = same-edge parameter order agreement, cut `c = n − M.val` resp. `n − a.val`), **`s7q_cutFirst_of/_cutSecond_of`**
  (`s7q_CutFirst` from `hord`, `hbit`, `hr`).
* **`s7q_coef_first/_second`**: `cornerCoefficient hQ S q hS = cornerCoefficient λᵢ Sᵢ qᵢ hSᵢ` for `hT.componentEquiv q = inl q₁`
  (resp. `inr q₂`) from `s7q_CutFirst` — `hmem` from `carrierCrossings_eq_img_first` + `s7b_visit_of_firstCrossingQ`,
  `htwin` from `s7b_firstVisitQ_visitTwin`.
* **`s7q_rowData_of_transport`**: `s7q_RowData` with `e := hT.componentEquiv` from a transport instance, the pivot split, the
  cut data of every carrier and the weight clauses.

### 1.E Boxes and assembly (section `S7QBoxes`, 948-1276; the boxes themselves are §2)
* `s7q_Split t b h₁ h₂ x` (= the `s7b_PivotSplit` of `s7e_contactSector_of_pivotSplit`), `s7q_contactPoint first`
  (`inl (owner S₁ (inl 0))` / `inr (owner S₂ (inl 0))` — the two half contact carriers, `componentEquiv_owner_vertexM/_pivot`),
  `s7q_contactTurns`, `s7q_contactPoint_ne`, `s7q_contactPoint_weight` (`Sum.elim … (contactPoint) = sel (contactTurns)`).
* **`s7q_pre_of_symm`** (for RET): `q.1.1 = s7b_pre ι₁ ((E).symm q).1 ∧ q.2.1 = s7b_pre ι₂ …` — the `first_pre`/`second_pre`
  fields of `s7b_SlidingTransport` on a row (`rfl` through `slidingEquiv_apply`).
* `s7q_OrderAgrees t b` (same-edge order agreement for both halves), `s7q_CarrierData hT a₀ m₀ τ` (per carrier: `hbit`, `hr`;
  weights off `a₀`; refined weight), **`s7q_rowData_of_carrierData`**, **`s7q_box_rows`** (PROVED from the three boxes RET,
  ORDER, CARRIERS), **`s7q_hterm_of_rows`** (the exact `hterm` shape of `s7e_contactSector_of_pivotSplit`),
  **`s7q_exists_contactSector`** (`∃ δ > 0, ∀ t < δ, s7e_ContactSector hn h h₁ h₂ t` from SPLIT + rows),
  **`s7q_sliding_law_at_of_boxes`** (the leaf's exact statement, from `s7e_sliding_law_at_of_contact`).

## 2. Black boxes (stated with `sorry`; consumed as listed)

1. **`s7q_box_split hn g h h₁ h₂ : ∃ δ > 0, ∀ t < δ, s7q_Split hn g h t false h₁ h₂ (s7e_xm hn h t) ∧ s7q_Split … true … (s7e_xp hn h t)`**
   — unit SPLIT (U_S7B_REPORT §2.2; est. 500-800 lines; a `s7p_`-prefixed draft was seen in progress in this wave).
2. **`s7q_box_ret hn g h h₁ h₂ : ∃ δ > 0, ∀ t < δ, ∀ hsplitm hsplitp q, (∃ vm, vm.1 = s7e_xm hn h t ∧ s7b_SlidingTransport … false … ((Em).symm q).1 q.1.1 q.2.1 vm) ∧ (the same on `true` at `s7e_xp`)`**
   — unit RET (U_S7B_REPORT §2.1 `ret`; est. 600-900).  `vm` is the leg visit; `first_pre`/`second_pre` are `s7q_pre_of_symm`.
3. **`s7q_box_order hn g h : ∃ δ > 0, ∀ t < δ, ∀ b, s7q_OrderAgrees hn g h t b`** — for both halves and both sides: `v.2.val = w.2.val →
   (param v < param w ↔ param (s7b_*VisitQ v) < param (s7b_*VisitQ w))`.  Content: lem:wall-sides (V) `ContactOrderAgrees` /
   `VertexLocalData.visit_order` on the side composed with U110-B's parameter laws at the centre (equal off the cut,
   `r·t` / `r + (1−r)t` on it — monotone).  Est. 150-300 lines.  (In the SPLIT draft this is `s7p_SideData.hord`.)
4. **`s7q_box_carriers hn g h h₁ h₂ : ∃ first τ δ, τ ≠ 0 ∧ 0 < δ ∧ ∀ t < δ, ∀ hsplitm hsplitp q, s ∈ contactTurns first ∧ −s ∈ contactTurns (!first) ∧ (∀ vm hT, vm.1 = x₋ → s7q_CarrierData (false side) hT (contactPoint first) (contactTurns first) τ) ∧ (∀ vm hT, vm.1 = x₊ → s7q_CarrierData (true side) hT (contactPoint (!first)) (contactTurns (!first)) τ)`**
   — the geometric content of THIS unit's (a) and of (c)'s `hbit`, plus the turn signs (U_S7B §2.3's ordered correspondence),
   see §3.2 for the corrected route and §6 for estimates.  `first` = the half whose contact carrier carries the extra corner on
   `P₋` (`λ₁` iff the leg of `x₋` is `M−1`, i.e. `s7e_leg g M a = false`); `s = χ(P₋) = g.contactSign M a`
   (`vertex_contact_signs`) is the contact sign of that half; `τ = sgn det(u_in,u_out)` = the turn at `μ_M`, nonzero
   (`ccpCornerPolygon_turn_ne_zero`), the same on both sides.

## 3. Defects found (rule 4) and the corrected forms

### 3.1 The two-turn form of eqs. s7c:turn-short-a/b is a THREE-turn form on the side polygon
The brief / W2_S7E_REPORT §2 state "the side carrier has ONE extra corner whose two adjacent turns add to the half's single
contact turn".  With the directions at the wall (`m = μ_M` of the centre) this is eq. s7c:turn-short-a/b verbatim.  But the
compared polygons are `Q(t)`'s carrier (corner polygon with edges `∝ r, u_in^Q, u_out^Q, w^Q`) and the half's carrier (edges
`∝ r, u_out^c, w^c`), and `u_out^Q ≠ u_out^c` (`μ_M` is displaced on the side): the corner AFTER `μ_M` also changes its
principal turn.  Corrected exact form (`s7q_CornerMerge.principal_three`, `s7q_principal_three_a/_b`):
`ϑ(r,u_in^Q) + ϑ(u_in^Q,u_out^Q) + ϑ(u_out^Q,w) = ϑ(r,u_out^c) + ϑ(u_out^c,w)` under `sign det(r,·)` equal on
`u_in^Q, u_out^Q, u_out^c` and `sign det(w,·)` equal on `u_out^Q, u_out^c`.  Likewise the OTHER contact carrier (the pivot
carrier on `P₋`, the `v_a`-carrier on `P₊`) has the same corners with TWO perturbed turns of equal sum (`s7q_CornerPerturb`).
The sign-level statement (turn multiset refined by exactly `{τ}`) is unaffected.

### 3.2 The germ moves EVERY vertex: the exact identifications are between polygons on the SAME side only
`WallGerm.curve : Ioo (−radius) radius → LabelledTuple n` is an arbitrary continuous family (`SM/WallGerm.lean:13-19`); the
contact windows (`ContactParameterWindows`, `s7e_sign_const`) already treat the persistent crossings as MOVING with `t`.  Hence
`edge Q(t) j` is NOT a positive multiple of `edge center j` for any `j`, and none of `hr`, `hbit`, the turn-sign equalities
between a carrier of `Q(t)` and a carrier of `λᵢ` (which lives on the CENTRE) is an exact positive-multiple identification —
even for the carriers away from the contact.  They are continuity statements for small `t` (the spectator sector's precedent:
U110-A2's `s7a2_carrierRotation_eq` via the regular family `s7a2_cornerFamily` and `rotationNumber_family_constant`;
`s7e_sign_const`/`s7e_sgn_contact` for signs).  So `s7q_CornerMerge`/`s7q_CornerPerturb` as stated (exact principal turns off
the affected corners) are NOT directly instantiable with `Q := ccpCornerPolygon Q(t) …`, `Q₁ := ccpCornerPolygon λ₁ …`; the
`principal_eq` fields would be false.  **Corrected route for `hr` of the extra-corner carrier** (the (a) content):
(i) EXACT step inside `Q(t)`: delete the extra corner `v_a` from `Q(t)`'s carrier polygon; the merged direction is
`d = μ_M(Q) − prev = α r^Q + β u_in^Q` (`α, β > 0`: `prev → v_a` runs along edge `a`, `v_a → μ_M` along edge `M−1` of `Q`), and
`s7q_principal_delete` gives `ϑ(e,r) + ϑ(r,u_in) + ϑ(u_in,u_out) = ϑ(e,d) + ϑ(d,u_out)` exactly under eq. s7c:sliding-signs
plus the two smallness sign conditions `sign det(e,d) = sign det(e,r)`, `sign det(d,u_out) = sign det(r,u_in)` (both hold for
`β` small, i.e. `t` small); with `s7q_sum_eq_of_merge` (`T = {prev, μ_M}`) this is `rotationNumber (Q(t) carrier) =
rotationNumber Q̂(t)` for the `(k−1)`-gon `Q̂(t)` through the same marks as `λ₁`'s carrier but at `Q(t)`'s positions.
(ii) PERTURBATION step: `Q̂(t) → ccpCornerPolygon λ₁ S₁ q₁` as `t → 0⁺` (corner by corner, the marks correspond by
`s7b_slidingMark`, positions continuous in the germ parameter, `μ_M(Q(t)) → μ_M(c)`), so `rotationNumber_locally_constant
(ccpCornerPolygon_regular …)` (SM/RegularPerturbation.lean:46, an `∀ᶠ` statement in the `LabelledTuple` topology) gives the
equality below some radius; alternatively A2's family device `s7a2_cornerFamily` from the side time to the wall, whose limit
polygon is exactly `Q̂(0)` = the half's carrier polygon.  For the other contact carrier and all remaining carriers only step
(ii) is needed (same corner count).  The turn-SIGN equalities (weights) and the over bits are the same kind of statement
(`turn` is locally constant on regular polygons: `regular_persists` + the sign of a continuous `det`).
**Nothing in the frozen statement is affected**; the exact lemmas of §1.A-B remain the algebraic core of step (i) (and apply
verbatim if a future germ model moves only the vertex `M`).

### 3.3 Two truth checks on the stated boxes
* `s7q_box_carriers` asserts coefficient/weight transport for ALL carriers, including the two contact carriers (eq.
  s7c:sliding-coefficients "`C₋(S) = C₊(φS) = C₁(S₁)C₂(S₂)`": every carrier's `d_Q` reads `m_Q` (`carrierCrossingCount_eq_*`) and
  `r_Q` (`hr`)); the contact crossing `x₋` is a crossing of NO carrier (its two visits have different owners), consistent with
  `carrierCrossings_eq_img_*`.
* `hord` (`s7q_box_order`) is true for every edge: off the cut and away from the moving vertices the parameters agree with the
  centre's; on edges `M−1`, `M` (and, for a general germ, everywhere) the same-edge ORDER is `VertexLocalData.visit_order`;
  on the cut edge `a` the half parameter `t ↦ r·t` (resp. `r + (1−r)t`) is monotone and the contact-affected crossings
  `{a,M−1}`, `{a,M}` are not images (`s7b_firstCrossingQ_not_affected`).

## 4. The leaf

`s7_sliding_law_at` is NOT closed; its `sorry` is untouched (rule 2: (a)-(c) did not all land).  Its body, once the four boxes
are theorems, is
```
  exact s7q_sliding_law_at_of_boxes hn g h h₁ h₂
```
(`s7q_sliding_law_at_of_boxes` has the leaf's exact statement and is PROVED from `s7q_box_split`, `s7q_box_ret`,
`s7q_box_order`, `s7q_box_carriers`; W2_S7E_REPORT §2's one-liner is `s7q_exists_contactSector`).

## 5. How to consume (wave 4)

* **SPLIT**: prove `s7q_box_split` (or `s7q_Split hn g h t b h₁ h₂ x` at each side below a radius; the definition unfolds to the
  `s7b_PivotSplit` of `s7e_contactSector_of_pivotSplit`, and `s7q_Split` is accepted wherever that is expected, by `rfl`).
* **RET**: prove `s7q_box_ret`; `vm` = the leg visit (`s7e_vl`); `first_pre`/`second_pre` are `s7q_pre_of_symm … q`; `pivot_mem`
  is `((E).symm q).2.2`; `affected` is `s7e_xm_affected`/`s7e_xp_affected` after `vm.1 = x`.
* **ORDER**: prove `s7q_box_order`; then `s7q_keys_first/_second` give the whole `hmono`/`hcut` content — no key arithmetic left.
* **CARRIERS** (`s7q_box_carriers`): per side and row, given `hT`: for each carrier `q` with `hT.componentEquiv q = inl q₁`
  (`inr q₂`): `hbit` (over bits along `s7b_firstVisitQ`: `s7d_positiveOverBit_eq_of_crossingSign` + sign constancy, cf.
  `s7e_hbit`), `hr` (§3.2 route; `s7q_carrierRotation_eq_of_merge/_of_perturb` if the exact structures can be instantiated,
  else `s7q_principal_delete` + `rotationNumber_locally_constant`); the weights: `s7c_carrierWeight_eq_sel` + the turn multiset
  identities (`s7q_CornerMerge.turns_eq` needs only `e` and `turn_eq` — the sign-level ordered correspondence of U_S7B §2.3,
  which IS instantiable across the wall since it is sign-level); the refined weight at `hT.componentEquiv.symm (contactPoint
  first)` is `s7q_carrierWeight_eq_of_merge`-shaped: `sel(contactTurns first + {τ})`; the contact-sign memberships: the half
  contact corner `μ_M` of `λ₁` has turn `sgn det(r,u_out^c) = η₁`, of `λ₂` `sgn det(u_in^c, r) = η₂ = −η₁`, and `χ(P₋) = s` is
  the one of the refined half (sm-4:359-362).
* The assembler: the leaf body of §4 once the boxes are theorems; nothing else changes.

## 6. Estimated remaining size (for the leaf, beyond wave 3's SPLIT/RET units)

ORDER 150-300; CARRIERS: sign-level ordered corner correspondence (U_S7B §2.3) 400-600, `hbit` 150-250, `hr` exact step
(edge identification of the corner polygon near the contact: `ccpCornerPolygon_turn_det`-type edge lemmas + `s7q_principal_delete`)
150-250, `hr` perturbation step (convergence of the corner polygons + `rotationNumber_locally_constant`, or the A2 family
device adapted to the relocated marks) 300-500, turn-sign constancy for all corners 200-300, contact-sign memberships and `τ`
100-150.  Total ≈ 1,450-2,350 lines (plus SPLIT 500-800 and RET 600-900 from their units).  Nothing believed false in the
frozen statement; the boxes are stated in the shapes the proved assembly consumes.

## 7. Mathlib / Lean pitfalls hit (v4.34.0-rc2 pin)

* `principalAngle_swap`, `principalAngle_neg_neg` are in `SM.ZeroRotationSeed`, not reachable from the frozen imports:
  re-proved as `s7q_principalAngle_swap` (mod-`2π` agreement + bounds, the `sftc_principalAngle_add` pattern).
* `Finset.sum_ite_eq'`, `ite_true` (`if_pos/if_neg/if_true` are deprecated → `ite_eq_left/right`, `ite_true`); the Finset
  `{a, a} = {a}` is `Finset.insert_eq_of_mem (Finset.mem_singleton_self a)`; `Finset.sum_pair (h : a ≠ b)`;
  `Finset.sum_add_sum_compl`; `Finset.erase_right_comm`.
* `Fintype.prod_sum_type` leaves `Sum.elim f g (inl a)` syntactically — `simp only [Sum.elim_inl, Sum.elim_inr]` before `rw`.
* Keys: `s7e_gkey hn hQ v` then `s7e_markKey_eq hn hQ (Sum.inr v)` and `rfl` gives `geometricVisitKey = edge.val + parameter`
  (pass `hn hQ` explicitly, W2_S7E_REPORT §4); `ZMod.val_add`, `ZMod.val_natCast_of_lt`, `Nat.mod_eq_sub_mod` for the wrap.
* `rw [hp] at h2` with `hp : p − 1 = p` works on a hypothesis; on the goal's Finset literal rewrite first, then
  `insert_eq_of_mem`.
* In the multi-goal `rw [lemma … ?_ ?_]` the side goals come in an unexpected order; state them as `have`s first.
