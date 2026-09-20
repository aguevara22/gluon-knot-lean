# R176_LEDGER_REPORT — row 176 (R:extreme_transport), the LEDGER unit: items (14), (13), (12) of `s176_PortDataRest`

LEDGER prover (subagent), 2026-09-15.  Inputs: Site_176_REPORT.md (§3, §5, §6), U_R176_REPORT.md §5 items 2–5,
RProof/RALedgers.lean `est_PortData` (:872) and the `est_` wall data (`est_wall`, `est_retained_affected`,
`est_not_retained_H`, `est_retained_u_iff`, `est_mem_U_L`, `est_S'_ind`, `est_liftCrossing`,
`est_groupedWrithe_affected`), RProof/X1Rows3.lean (`GT_Wall`, `GT_carrierEquiv`, `GT_cornerPolygon_eq`, `GT_turn_tcp`,
`GT_carrierR_eq`, `GT_wind_eq`), SM/GeoCarrierCount.lean (the geometric insertion calculus:
`geoSmoothingSuccessor_insert*`, `geoSmoothingSuccessor_insert_child_data`, `geoOwner_insert_iff_of_unaffected`,
`geoIndependent_remaining_pair_owners`, `geo_selected_visits_separated`, `geoOwner_eq_of_subset`,
`geoInheritsMarkOrder_of_independent`), SM/FlatCarriers.lean + SM/GeoCornerPolygon.lean (`geoOutSlot`, `geoInEdge`,
`geoCornerPolygon_edge_smul`, `geoCornerPolygon_edge_pred_smul`, `geoCornerPolygon_turn_eq_sign_of_independent`,
`geoCornerMark_*`), CV/UniformRot.lean (`one_le_rot_of_one_dissent`, `uniformrot.pos_three/neg_three`),
CV/Rotation.lean (`two_pi_mul_rot`, `rot_reversal`, `regular_reversal'`), CV/X1.lean (`groupedWrithe_eq_card_geoCarrierCrossings`,
`carrierR_cast`, `carrierPolygon_cvRegular`), CV/Carriers.lean (`wind_ne_zero_imp`, `CarrierUniform`),
CV/HomflyRows.lean (`IsLinkingNumber`, `exists_linkingNumber`), SM/ZeroLink.lean (`mixedSignSum`), the Site_176 §C
labelled-corner lemmas (`s176_cyclic`, `s176_nb_a/b/c`, `s176_visitTwin_eq`, `s176_ne_of_supports`, `s176_event_site_core`).

## 0. Deliverables and checks

| item | result |
|---|---|
| `work/drafts/moves/R176_LEDGER.lean` | 6245 lines = `Site_176.lean` (4143 lines, **byte-identical**, checked with `cmp` on the prefix) + an APPENDIX of 2102 lines (module comment + §L0–§L5, 148 declarations, all names `r176l_`, namespace `RProof`) |
| compile `cd work/lean && lake env lean ../drafts/moves/R176_LEDGER.lean` | exit 0, **0 errors**, 20–40 s (2 min under load); warnings: exactly the skeleton's **33** `declaration uses sorry` + the skeleton's own `<;>` style warning + one harmless linter note (`r176l_selectedPart_eq`: "section variable `b` unused" — it is the label inside the included `hv`) |
| `grep -c sorry` | **34 before / 34 after** (Site_176.lean 34 = skeleton; the appendix adds NO `sorry` — the black boxes are hypotheses / Props, never `sorry`ed) |
| `#print axioms` | every geometric/ledger theorem (`r176l_uniformOrOneDissent_of_shape`, `r176l_one_le_sign_mul_rot_of_shape`, `r176l_abs_ledger`, `r176l_mixedSignSum_eq_card`, `r176l_card_retained`, `r176l_rot_ledger`, `r176l_children_case1`, `r176l_local_signs`, `r176l_shape_L1/L2`, `r176l_rot_add_case1`, `r176l_lt_c_of_indep`, `r176l_ledgerData_case1`, `r176l_Sf_indep_event`, `r176l_uniform_transport`): `[propext, Classical.choice, Quot.sound]`; the assemblies `r176l_portDataRest_of`, `r176l_portDataRest_case1`, `r176l_portDataRest_of_uniform`: additionally `SM.lit_homfly` (through `groupedPoly`/`homfly` in the field types — the accepted `est_ledger` footprint); `r176l_est_port_relation_weak_uniform_of`: additionally `sorryAx` THROUGH the frozen leaf `exists_bigonData_of_triangle` via `s176_port_weak_of_event'` only (as `s176_est_port_relation_weak_of'`) |
| written under `work/lean` | nothing; RALedgers/Site_176 material untouched (rule 1) |

## 1. What is PROVED (exact statements in the file)

### §L0 Abstract ledgers on labelled tuples (no geometry)
* `r176l_OneDissentShape L σ := ∃ k₀, turn L k₀ = -σ ∧ ∀ k ≠ k₀, turn L k = σ` — the RA (12) corner-sign shape.
* **`r176l_uniformOrOneDissent_of_shape (hL : Regular L) (hσ : σ ≠ 0) : OneDissentShape L σ → UniformOrOneDissentCV L`**
  — (12): `σ = 1` directly, `σ = -1` after reversal (`principalTurn_reversal`, `principalTurn_sign`).
* **`r176l_one_le_sign_mul_rot_of_shape : 1 ≤ (σ : ℤ) * rot L`** (lem:uniformrot (ii) after a possible reversal, `rot_reversal`).
* `r176l_rot_uniform_three : c = 3 → (∀ k, turn L k = σ) → rot L = σ` (uniform triangle, `uniformrot.pos_three/neg_three`).
* **`r176l_abs_ledger : r = r₁ + r₂ + σ → 1 ≤ σ r₁ → 1 ≤ σ r₂ → |r| = |r₁| + |r₂| + 1`** — the `|·|`-arithmetic of (13).

### §L1 `2ℓ` as a count
* `r176l_IsMixed D i j x` (a crossing between the components `i, j`); `r176l_mixedSignSum_eq` (copy of the accepted
  `SM.s7h_mixedSignSum_eq`, whose module is not imported) and **`r176l_mixedSignSum_eq_card : (∀ x, D.sign x = 1) →
  mixedSignSum D i j = #{mixed crossings}`** — "since every mixed retained crossing is positive … exactly `2ℓ`
  complementary-mask crossings occur".

### §L2 The interface and the assembly
* `r176l_Children hP S' Sf q' Λ₁ Λ₂` (Prop): `Λ₁, Λ₂ ⊆ q'`, `Λ₁ ≠ Λ₂`, every `Sf`-unselected visit owned by `q'` is
  owned by `Λ₁` or `Λ₂`.  `r176l_mixedSet` (the mask-`uv` survivors: retained by `q'`, unselected in `Sf`, visits on
  different children), `r176l_selectedPart` (retained by `q'`, selected in `Sf`).
* **`r176l_retained_decomp`, `r176l_card_retained : (retained q').card = (retained Λ₁).card + (retained Λ₂).card +
  #mixedSet + #selectedPart`** — the L-side decomposition of (14), four pairwise disjoint parts.
* **`r176l_SmoothData`** — the SMOOTH black box (§2 below); `r176l_ell`, `r176l_ell_spec : IsLinkingNumber DA i j ℓ`
  (`CV.exists_linkingNumber`), `r176l_two_mul_ell : 2ℓ = #mixedSet`.
* **`r176l_portDataRest_of : SmoothData → (14 in the form w₀ = w₁ + w₂ + #mixedSet) → (13) → alt₁ → alt₂ →
  s176_PortDataRest`** — the constructor of the target structure.
* `r176l_alt_of_shape` ((12) for both children from their shapes), **`r176l_rot_ledger : R(D₊) = R(D₀) →
  rot q' = rot Λ₁ + rot Λ₂ + σ → shapes → (carrierR q : ℤ) = carrierR Λ₁ + carrierR Λ₂ + 1`** ((13), via `carrierR_cast`).

### §L3 The geometric realisation on the labelled corner (carrier level, case 1)
Setting (Site_176 §C): `hP : CrossingGeometry P`, `T` independent, `q` a carrier, labels `a b c`, `j = {a,b} ∈ T`,
`u = {a,c}`, `v = {b,c}` retained by `q`, the successor facts `ρ (u,a) = (j,a)`, `ρ (j,b) = (v,b)` (case 1) and
`hSf : GeoIndependent (Sf := insert v (insert u T))`.
* L3.1–3: the six local visits, `Sf`, `S₁ = insert u T`; `ρ_T`, `ρ_{S₁}`, `ρ_{Sf}` at the local marks;
  **`r176l_succSf_cycle`**: the central triangle `(u,c) → (j,a) → (v,b) → (u,c)` is a `ρ_{Sf}`-3-cycle.
* L3.4 **the two-step split**: `r176l_sameCycle_three` (membership in a 3-cycle), `r176l_owner_insert_or` (the exact
  two-child split of `geoSmoothingSuccessor_insert_child_data` as a disjunction), `r176l_owner_Sf_L2_iff` (the `(u,a)`
  child is unaffected by the second insertion), `r176l_Z_eq`, `r176l_mem_Z` (`Z` owns exactly its three marks),
  `r176l_L1_ne_L2`, `r176l_L1_ne_Z`, `r176l_L2_ne_Z`, `r176l_owner_Sf_cases` (every mark of `q` lies on `Λ₁`, `Λ₂` or `Z`),
  **`r176l_children_case1 : r176l_Children hP T Sf q (Λ₁ := owner_{Sf} (v,c)) (Λ₂ := owner_{Sf} (u,a))`**.
* L3.5 corner sets: `r176l_cornerSet`, **`r176l_sum_cornerMark`** (sum over `ZMod c(r)` = sum over the corner marks,
  `geoCornerMark` bijective), `r176l_cornerCount_eq_card`, `r176l_tau S m := principalAngle (e_{inEdge m}) (e_{outSlot S m})`,
  **`r176l_principalTurn_eq_tau`** (the principal turn at `k` is the angle at its corner mark: `edge_pred_smul`,
  `edge_smul`, `principalAngle_smul`), `r176l_principalAngle_swap`, `r176l_outSlot_eq_of_iff` / `r176l_tau_eq_of_iff`
  (inherited corners keep their out-slot and angle).
* L3.6 **`r176l_vector_identity`**: `γ e_c = -α e_a - β e_b`, `α, β, γ > 0` (the three crossing points from the
  visit parameters, `edgePoint_sub_edgePoint`); **`r176l_local_signs`**: `sgn det(e_a,e_c) = sgn det(e_c,e_b) = -σ`,
  `sgn det(e_c,e_a) = sgn det(e_b,e_c) = σ` with `σ = sgn det(e_a,e_b)` — RA (3)/(6)/(12).
* L3.7 **the corner sets of the three children**: `r176l_mem_cornerSet_L1/L2` (inherited corners of `q` owned by the
  child + the one new corner `(v,c)` / `(u,a)`), `r176l_mem_cornerSet_Z`, `r176l_cornerCount_Z = 3`,
  `r176l_mem_cornerSet_q` (the corners of `q` = inherited-on-`Λ₁` ⊔ inherited-on-`Λ₂` ⊔ `{(j,a)}`),
  `r176l_sigma_eq` (`σ = sgn det(e_a,e_b)` from uniformity at the corner `(j,a)`), `r176l_turn_inherited`,
  **`r176l_shape_L1`, `r176l_shape_L2 : OneDissentShape (geoCornerPolygon Sf Λᵢ) σ`** — (12), and
  **`r176l_turn_Z`** (the central triangle is uniform with sign `σ`).
* L3.8 **`r176l_sum_principalTurn_add`**: `Σ τ(Λ₁) + Σ τ(Λ₂) + Σ τ(Z) = Σ τ(q)` (the two new turns at each smoothing
  site are opposite — `principalAngle` antisymmetry on the transverse pairs — every inherited turn unchanged), and
  **`r176l_rot_add_case1 : rot q = rot Λ₁ + rot Λ₂ + σ`** (turnlift (ii) `two_pi_mul_rot` on the four polygons, `rot Z = σ`).
* L3.9 **`r176l_lt_c_of_indep`**: the orientation of `c` is FORCED by the independence of `S_full` (with `u <_a j`,
  `j <_b v`, the order `u <_c v` would put the two visits of `v` on different `S₁`-children, against
  `geoIndependent_remaining_pair_owners`); `r176l_selectedPart_eq = {u, v}`; the bundle **`r176l_LedgerData`** (subset,
  children, card, shape₁, shape₂, rot_add) and **`r176l_ledgerData_case1`**.

### §L4 The event level
* **`r176l_Sf_indep_event`**: `S_full = Q' ∪ {j', u', v'}` is independent on `L` (`est_mem_U_L`, `complement_on_triangle`).
* **`r176l_uniform_transport`**: uniformity (with its sign) is carried across the wall (`GT_cornerPolygon_eq`, `GT_turn_tcp`).
* **`r176l_portDataRest_case1`**, **`r176l_portDataRest_labelled`** (either orientation, case 2 = case 1 on
  `(b, a, c), (j, v, u)` with `s176_cyclic` forcing `v' <_b j'`), **`r176l_portDataRest_of_uniform`** (six relabellings):
  for the binders of `est_port_relation` + the retained `u'` + **`hwind : wind(Q ∪ {j}) ≠ 0`** + the SMOOTH black box,
  `Nonempty (s176_PortDataRest … (est_liftCrossing … hu'))` — the `hrest` obligation of `s176_est_port_relation_weak_of'`.

### §L5 The corrected interface (rule 4, see §3)
* `r176l_est_port_relation_uniform`, `r176l_est_port_relation_weak_uniform` (the two interface Props with the extra
  hypothesis `wind ≠ 0`), `r176l_est_port_relation_weak_uniform_of_weak`, and
  **`r176l_est_port_relation_weak_uniform_of (hsmooth) (hrec : ∀ …, s176_hrec_wall …) : r176l_est_port_relation_weak_uniform`**.

## 2. Black boxes (consumed, not constructed)

1. **`r176l_SmoothData hn hG' hS' q' y Sf hSf Λ₁ Λ₂`** (structure, Type) — the SMOOTH unit's deliverable at a full support
   `Sf` with two carriers `Λ₁ Λ₂` (both PARAMETERS, defined geometrically by this unit): `DA : Diagram`,
   `smooth : IsOrientedSmoothing (carrierDiagram q') y DA`, `two : DA.componentCount = 2`, `i j : Fin DA.Γ.c`, `ij`,
   `poly₁ : homfly (DA.knotRestrict i) = groupedPoly hn hG' hSf Λ₁`, `poly₂` (the record isos of the component restrictions
   with the lifts of the outer carriers + lc:single-crossing for the kink — SMOOTH's), and the (14)-bridge
   **`mixed : mixedSignSum DA i j = #(r176l_mixedSet hG'.cg S' Sf q' Λ₁ Λ₂)`** ("the mixed crossings of `D_A` are exactly the
   mask-`uv` survivors, all positive").  `r176l_mixedSignSum_eq_card` reduces `mixed` to a bijection between the mixed
   crossings of `D_A` and `r176l_mixedSet` once `∀ x, DA.sign x = 1` is known (the smoothing keeps the other crossings of the
   positive lift and creates none).  I could not prove `mixed` here: it needs the component structure of `D_A`, which
   `IsOrientedSmoothing` (a disc-local geometric relation, no component bijection) does not expose — it is available to
   SMOOTH through the record iso `RecordIso DA.record (D₊.record.smooth v)` of `exists_smoothing_record_visit`.
2. **`r176l_smooth_black_box : Prop`** — the event-level form: for every labelled case-1 configuration
   (`a b c`, `j' = {a,b}`, `u' = {a,c}`, `v' = {b,c}` retained, `u' <_a j'`) and `y ∈ {lift u', lift v'}`,
   `Nonempty (r176l_SmoothData … y (r176l_Sf S' u' v') hSf (Λ₁ := owner_{Sf} (v',c)) (Λ₂ := owner_{Sf} (u',a)))`.
   Taken as a HYPOTHESIS of `r176l_portDataRest_of_uniform` / `r176l_est_port_relation_weak_uniform_of` (no `sorry`).
   The pair `{Λ₁, Λ₂}` is canonical (the two children of `q'` other than the central triangle, whichever local crossing
   is smoothed), so SMOOTH may realise it in either orientation.
3. **`hrec` (`s176_hrec_wall`)** — the record identification of the Site unit (its open clause `hsucc`), consumed as the
   hypothesis `hrec` of `r176l_est_port_relation_weak_uniform_of` exactly as in `s176_est_port_relation_weak_of'`.
4. The frozen leaf `exists_bigonData_of_triangle` enters only through `s176_port_weak_of_event'` (as before).

## 3. DEFECT of the interface as stated (rule 4): `est_PortData.rot` / `.alt₁` / `.alt₂` need `wind(S) ≠ 0`

`est_PortData` (RALedgers:872), hence `s176_PortDataRest` and `est_port_relation`, demand (13) `R = R₁ + R₂ + 1` and
(12) `UniformOrOneDissentCV (geoCornerPolygon Sf Λᵢ)` for EVERY affected carrier.  The printed proof (RA §3) derives both
from the UNIFORMITY of the affected carrier, which it has only when the common singleton selector is nonzero:
"If the common singleton selector is zero, the matched selector ledger already makes both terms in (2) zero.  Assume
it is nonzero.  Then the affected singleton carrier is uniform; by (6), all its corners have sign `σ`."  For a MIXED
affected carrier the inherited corners of an outer carrier carry both signs (e.g. two left and two right turns on the
`seg₁` arc): `UniformOrOneDissentCV` fails, and `rot Λ₁ + rot Λ₂ + σ` can have `|·|` smaller than `|rot Λ₁| + |rot Λ₂| + 1`
(e.g. `rot Λ₁ = 2, rot Λ₂ = -1, σ = 1`), so (13) fails as stated.  Nothing in the event data excludes a mixed affected carrier.

Corrected forms stated in the file (not asserted, never mapped): `r176l_est_port_relation_uniform` and
`r176l_est_port_relation_weak_uniform` = the two interface Props with the extra hypothesis
`CV.wind (geomAt E t ht.1) (Q ∪ {j}) ≠ 0`.  Under it the whole non-move part is PROVED here from the SMOOTH black box
(`r176l_portDataRest_of_uniform`).  **Consumer change needed (RALedgers, not made):** `est_row_H` (and
`s176_est_row_H_weak`) must split on `wind(S) = 0`: there both row terms `wind(S) · ∏ Ω₁` vanish (`wind` is carried
across the wall, `GT_wind_eq`), so `est_omega1_eq_of_port` is only invoked for `wind(S) ≠ 0`, where the corrected Prop
supplies the port data.  The fields `DA … poly₂, ℓ, link, writhe` do NOT need uniformity ((14) is proved here without it:
`r176l_card_retained` + `est_groupedWrithe_affected`), so an alternative correction is to move `rot`, `alt₁`, `alt₂` under
a `wind ≠ 0` guard inside `est_PortData`.

## 4. Pitfalls met

1. **`insert` and `DecidableEq (Crossing P)`.** The accepted insertion lemmas of SM/GeoCarrierCount.lean state
   `insert v.1 S` with `fun a b => Classical.propDecidable (a = b)` (their `attribute [local instance]`), while a file in
   namespace `RProof` resolves `DecidableEq (Crossing P)` to the global `RProof.instDecidableEqCrossing`; the two
   `Finset.instInsert`s are NOT definitionally equal, so `exact`/`Eq.trans` against those lemmas fail with a type
   mismatch, and `attribute [local instance] Classical.propDecidable` does not change the resolution (the global
   instance still wins).  `attribute [local instance 2000] Classical.propDecidable` does, but also changes the instance
   of `{a, c} : Finset (ZMod n)` and breaks every `s176_` lemma.  Fix used: a reducible NAMED instance for `Crossing P`
   only — `abbrev r176l_decEq (P) : DecidableEq (Crossing P) := fun a b => Classical.propDecidable (a = b)` +
   `attribute [local instance 2000] r176l_decEq` inside the section; `insert` then unfolds to the library's form.
   Writing `@insert _ _ (@Finset.instInsert _ (fun a b => …)) x S` explicitly instead triggers "synthesized type class
   instance is not definitionally equal to expression inferred by typing rules" (the elaborator re-synthesises).
2. `visitOn x ℓ _`, `r176l_ua hu` etc. are definitional unfoldings; a lemma stated for `visitParameter (visitOn u a _)`
   instantiates at `crossingTransport hs u` with the H-side proof `huac : u.val = {a, c}` (the transported crossing has
   the same `val` by `rfl`), but the elaborator needs `(u := crossingTransport hs u)` named explicitly whenever the
   crossing only occurs inside such a proof argument.
3. `s176_visitTwin_eq hj hab _ _` in `rw` leaves the two membership proofs as side goals (`b ∈ ↑j`); pass them
   (`(s176_mem_left hj) (s176_mem_right hj)`).
4. `sign_neg` in Mathlib is `a < 0 → sign a = -1`; the negation law is `Left.sign_neg : sign (-a) = -sign a`.
   `SignType` is not an additive group: `neg_eq_zero` does not apply to `0 = -σ`; `cases σ <;> decide`.
5. `push_cast` turns `((σ : ℤ) : ℝ)` into `(σ : ℝ)` in the goal but not in a hypothesis where it appears as
   `↑↑σ`; `linarith` then sees different atoms.  Keep the casts as `Int.cast` and finish with `Int.cast_injective`.
6. After `obtain ⟨k, rfl⟩ := h.exists_nat_pow_eq` the hypothesis `h` still mentions `k`, so `induction k` generalises
   it and the inductive hypothesis becomes an implication; `rw [← hk]; clear hk h` first.
7. `set W := est_wall … with hW` inside a proof whose hypotheses `hu' hv' y hy` mention the wall creates shadowed
   copies and a fresh `y`; the black box then fails to unify.  Write `est_wall …` out in full instead.
8. In a `fun` against a `∀ {a b c} … {v} …` type, implicit lambdas are inserted only for LEADING implicit binders and
   not at all once the `fun` carries any `{}` binder: write `fun {a b c} … {v} … =>`.
9. `rintro (rfl | rfl)` on `x = u ∨ x = v` with `u` a section variable eliminates `u` itself (later `u` is unbound);
   use `rintro (h | h)` + `rw [h]`.
10. Section variables used only in a proof are not included automatically (`include … in`), and `omit [NeZero n]` is
    refused on any statement mentioning `GeoComponent` (which needs `NeZero n`); the linter also flags an included label
    variable as "unused" when only the included equation `hv : v.val = {b, c}` mentions it.

## 5. What remains (not proved here)

| obligation | where it enters | note |
|---|---|---|
| `r176l_SmoothData` (`DA`, `two`, `i j`, `poly₁ poly₂`, `mixed`) — the oriented smoothing with two components, the exact owner map (9)/(9a) with lc:single-crossing for the kink, and the (14)-bridge `2ℓ = #mixedSet` | `r176l_portDataRest_of`, hypothesis `hsmooth : r176l_smooth_black_box` | SMOOTH unit; `r176l_mixedSignSum_eq_card` reduces `mixed` to a bijection of the mixed crossings of `D_A` with `r176l_mixedSet` once `∀ x, DA.sign x = 1` |
| `hsucc` / `s176_hrec_wall` | hypothesis `hrec` of `r176l_est_port_relation_weak_uniform_of` | Site unit (≈ 500–700 lines per Site_176_REPORT §3) |
| the `wind(S) = 0` case of the consumer (`est_row_H` split) | RALedgers | ≈ 20 lines; both row terms vanish by `GT_wind_eq` |
| F-176-1 acceptance (the weak `port` field) | RALedgers | as in Site_176_REPORT §4 |

Everything of (14), (13), (12) that is geometric — the children of the affected carrier under `S_full`, the retained-set
decomposition, the corner-sign ledger (3)/(6)/(12), the one-dissent shapes, the signed rotation additivity, the forced
orientation of the third strand, independence of `S_full` on `L`, the transport of uniformity — is PROVED, with standard
axioms only, at the carrier level for the labelled case 1 and assembled at the event level in both orientations and all
six labellings.
