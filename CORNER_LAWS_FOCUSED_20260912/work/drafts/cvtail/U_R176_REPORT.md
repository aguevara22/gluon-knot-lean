# U-176 report — R:extreme_transport (`RProof.extreme_transport`), prefix `est_`

Prover: U-176 unit, 2026-09-15.  File: `work/drafts/cvtail/U_R176.lean` (copy of `Statements_FINAL.lean`
+ pure insertions; `diff Statements_FINAL.lean U_R176.lean | grep '^<'` prints nothing).
Check: `cd work/lean && lake env lean ../drafts/cvtail/U_R176.lean` → **0 errors, 0 warnings other than the
10 `declaration uses sorry`** that the FINAL already had (the 4 placeholders, the 3 lane leaves, the 3 RA rows);
`grep -c sorry`: 11 before / 11 after (one occurrence is the FINAL's docstring at line 35).  Compile ≈ 19 s.

## 1. Leaf status

* **Leaf `RProof.extreme_transport` (row 176): LEFT as `sorry`** — by design (D-F11): the row is PROVED as the
  conditional theorem `est_extreme_transport_of (hF : CV.CarrierSlotFloor) (hport : est_port_relation)` /
  `est_ledger hF hport : RowShape @ExtremeTransportData`, and the interface Prop `est_port_relation` (the RII
  port relation with its diagram identifications, G10-scale) is stated but NOT realised.  The interface is never
  mapped.  Plug-in line for the assembler once the interface is realised:
  ```
  theorem extreme_transport … :=
    est_extreme_transport_of (CV.carrier_slot_floor_of_C SM.cf_thm_carrierfloor.clauseC)
      <proof of est_port_relation> hn E e f g h3 h4e h4f h4g hE
  ```
  (`CV.carrier_slot_floor_of_C` is the U-SLOT leaf; `SM.cf_thm_carrierfloor` the floor lane's row 99 placeholder.)
* **Everything else in the unit is PROVED**, sorry-free, no new axiom: `#print axioms RProof.est_ledger` =
  `propext, Classical.choice, Quot.sound, SM.lit_homfly, SM.lp_lm, SM.lp_lm_uniqueness` (the accepted rows'
  footprint; `lit_homfly` through `homfly`, `lp_lm*` through cor:groupedknot/`P_eq_homfly` inside
  `GT_groupedPoly_eq_homfly`).  The purely combinatorial part (`est_retained_affected`, the wall, the retained
  sets) uses only `propext, Classical.choice, Quot.sound`.

## 2. Two `import` lines added (NOT a statement change — flag for the assembler)

`import CV.FullTwist` and `import CV.HomflyRows` (accepted modules, PLAN_FINAL §4 176 names both: lem:fulltwist,
lem:homflyrows (ii)) were added after `import CV.Axioms`.  The FINAL did not import them; nothing else in the header
or in any frozen declaration was touched.

## 3. The interface Props (never mapped)

### `est_PortData` (structure, Type — data-carrying; consumed through `Nonempty`)
`est_PortData hn hG hG' hS hS' q q' y`, for `q` the affected carrier of `S = Q ∪ {j}` on the `K3` side `H`
(`D_0 = carrierDiagram q`, clean), `q'` its copy on the empty side `L` (`D_+ = carrierDiagram q'`, retaining the two
other triangle crossings as "the positive self-crossings `q, r`") and `y : D_+.Γ.Crossing` the lift crossing of the
one to be switched.  Fields = the geometric steps of R_EXTREME_SINGLETON_TRANSPORT_PROOF.md §1–§3:

| field | RA text | Lean |
|---|---|---|
| `port` | (T2) "Switching `q` … `q, r` an empty opposite-sign oriented RII pair. Deleting it leaves exactly `D_0`" | `Relation.ReflTransGen RII (D_+.switch y) D_0` (the shape `CV.fulltwist_coefficient` consumes) |
| `DA`, `smooth` | (T1) `D_A = smooth_q(D_+)` | `IsOrientedSmoothing D_+ y DA` |
| `two`, `i`, `j`, `ij` | "Smoothing `q` splits `D_+` into two components" | `DA.componentCount = 2`, two distinct component tags |
| `Sf`, `hSf`, `Λ₁`, `Λ₂` | `S_full = Q ∪ {x,y,z}` independent on `L`, its clean outer carriers `L_G` | `Sf ∈ Ind`, `Λ₁ Λ₂ : GeoComponent … Sf` |
| `poly₁`, `poly₂` | (9a)/(10) "polynomials `(Q_C, Q_B)`" — the exact owner map + lc:single-crossing for the kink `r` | `homfly (DA.knotRestrict i) = groupedPoly Λ₁`, same for `j`, `Λ₂` |
| `ℓ`, `link` | "`ell` the linking number of the two components" | `CV.IsLinkingNumber DA i j ℓ` |
| `writhe` | (14) `w_0 = w_1 + w_2 + 2ℓ` | `groupedWrithe q = groupedWrithe Λ₁ + groupedWrithe Λ₂ + 2ℓ` |
| `rot` | (13) `R_1 + R_2 + 1 = R` (turnlift (ii) + corner ledger (12)) | `(carrierR q : ℤ) = carrierR Λ₁ + carrierR Λ₂ + 1` |
| `alt₁`, `alt₂` | (12) "exactly one-dissent, never uniform with the wrong sign" (after a possible reversal) | `CV.UniformOrOneDissentCV (geoCornerPolygon … Λᵢ)` |

Deliberately NOT in the interface (proved instead): `y` positive (`geoPositiveLift_isPositive`), `w_+ = w_0 + 2`
(`est_groupedWrithe_affected`), `R(D_+) = R(D_0)` (`GT_carrierR_eq`), `d_+ = d_0 − 2`, the identification
`d(D(W)) = slot`, `Ω(D(W)) = Ω₁` (§B below), the floor consumption, all Laurent algebra.

### `est_port_relation : Prop` (the event-level interface)
For every `n`, `hn`, simple-RIII event data `hL : LocalizationData`, `hR : AV_EventRadius`, `e ≠ f ≠ g`, `K3` side `t`
(`CompleteLocal`), opposite `t'`, `hs`, outside `Q` with `FullAvail`, selected `j ∈ T`, and carrier `q` of `Q ∪ {j}`
whose copy `GT_carrierEquiv (est_wall …) q` retains some unselected `u' ∈ T'` ("affected"): there EXISTS a choice
`u` (with `u' ` retained) such that `Nonempty (est_PortData … q (GT_carrierEquiv (est_wall …) q) (est_liftCrossing … hu'))`.
The `∃ u` conclusion (rather than `∀ u`) is the weakest form the ledger needs: the printed proof fixes one `q` per
row ((5): `j=x: q=y`, `j=y: q=x`, `j=z: q=y`); a realiser may take that one.

## 4. Helpers added (all PROVED; section `EST` inside `namespace RProof`, immediately before the leaf)

A. Laurent algebra: `est_coeff_sub`, `est_coeffAt_of_zRow` ((16) extraction of the two monomials of `a − a⁻¹`
from the `[z⁻¹]` row (11)), `est_coeffAt_mul_eq_zero` (coefficient below the sum of two floors vanishes,
`mindegAZ_mul`).
B. def:X1 data on the grouped diagram: `est_carrierDiagram_writhe` (`w(D(W)) = w_{S,L}`), `est_carrierDiagram_d`
(`d = slot`; `absRot = carrierR` is `rfl`), `est_carrierDiagram_Omega` (`Ω = Ω₁`).
C. Interface: `est_PortData`, `est_liftCrossing`, `est_port_relation`.
D. Affected-carrier ledger: `est_omega1_eq_of_port` — (7) `d_+ = d_0 − 2` ⇒ `CV.fulltwist_coefficient` ⇒ (8);
`CV.homflyrows.two_component_row` ⇒ (11); (15) `slot Λ₁ + slot Λ₂ = slot q + 2 + 2ℓ` by `omega` from (13),(14);
`CarrierSlotFloor` at `Λ₁, Λ₂` + `cvt_groupedPoly_ne_zero` ⇒ both extracted coefficients vanish (16) ⇒ `Ω₁ q' = Ω₁ q`.
E. Event configuration: `est_tri_exhaust`, `est_interlaces_of_complete`, `est_eq_j_of_mem_S_T`, `est_S_ind`,
`est_S'_ind`, `est_wall : GT_Wall … (Q ∪ {j})`, `est_not_mem_U_H` (dominated on `H`), `est_mem_U_L` (survive on `L`).
F. Retained sets across the wall: `est_shared_not_mem_third`, `est_good_of_edge`, `est_not_mem_S`,
`est_owner_shared_eq` (the shared-edge visits of `u, v` lie on ONE carrier `q₀`), `est_not_retained_H`,
`est_retained_outside_iff`, `est_retained_u_iff` (`u'` retained by the copy of `q` iff `q = q₀`),
`est_retained_eq_of_ne` (unaffected: retained set carried), `est_retained_affected`
(retained(`q₀'`) = carried set ∪ `{u', v'}`).
G. Carriers: `est_groupedPoly_eq_of_ne` (`EXT_homfly_wall`), `est_omega1_eq_of_ne`, `est_groupedWrithe_affected` (7).
H. Assembly: `est_rowTerm_eq_of_omega` (the `Ω₁`-only form of `AV_rowTerm_eq_of_summandTransport` — needed because
`P_{S,L}`, `w_{S,L}` of the affected carrier are NOT carried), `est_others`, `est_row_H` (`K3` side), `est_row`
(either side, by `graphs_complementary` + the `(t', t)` symmetry as in `GT_endpoint_transport_edge`),
`est_extremeTransportData` (the six fields; PRE fields = the accepted `PRE_176_*`), `est_ledger`
(`RowShape @ExtremeTransportData`, radius = min of rows 164/172 + sign radius, as `generic_transport`),
`est_extreme_transport_of` (the row statement).
I. Sanity: `est_switch_writhe` (`(D_+.switch y).writhe = w_+ − 2`, consistent with (T2) since RII preserves writhe).

≈ 850 lines inserted.

## 5. What remains to realise `est_port_relation` (G10-scale; precise list)

Given the event data and the affected carrier `q₀` (owner of the `u, v` visits on their shared edge — proved
unique and characterised by `est_retained_u_iff`), construct for the chosen switch crossing:
1. **(T2) the RII port relation** `ReflTransGen RII ((carrierDiagram q₀').switch y) (carrierDiagram q₀)`: an actual
   `SM.Link.RIIData U (carrierDiagram q₀) ((carrierDiagram q₀').switch y)` (SM/LinkMoves.lean:596) — disc `U`
   containing the empty bigon between the two triangle-strand arcs ("choose the RIII disc small enough to contain the
   whole resulting bigon and no outside strand, crossing, or vertex"), `LocalFrame`, `MoveMatch` outside,
   `ArcCover`, `Separates`, `same_over`; the two diagrams live on DIFFERENT polygons (`E.curve t'` vs `E.curve t`), so
   the outside match is the wall transport of the carried marks (`GT_carrierEquiv`, `GT_cornerPolygon_eq`), i.e. an
   isotopy through the wall, not an identity — this is the G11-type cost (RProof/GenericTransport.lean did the RIII
   analogue in ≈11k lines via `G11_Config`; no `RIIData` is constructed anywhere in work/lean yet).
2. **(T1) the oriented smoothing** `D_A` of `carrierDiagram q₀'` at `y` as an actual `Diagram` with
   `IsOrientedSmoothing` (SM/LinkMoves.lean:743, `OrientedSmoothingData`) and `componentCount = 2`.  No existence
   theorem for oriented smoothings of a polygonal diagram exists in the library (the skein axiom is relational).
3. **The exact owner map (9)/(9a)**: `S_full = Q' ∪ {j', u', v'}` independent on `L` (easy: full availability +
   `EmptyLocal`), its outer carriers `Λ₁, Λ₂` (`GeoComponent`), and `homfly (D_A.knotRestrict i) = groupedPoly Λ₁`
   etc. — record isomorphism of the component restriction with the outer carrier's lift, after removing the kink
   `r` (lc:single-crossing, `SM/SingleCrossing.lean`) — the "skeleton ↔ carrier identification" (rlane2 NOTES_FINAL §12
   risk 8) on the successor structure `geoSmoothingSuccessor` of `S_full`.
4. **(14)** `w_0 = w_1 + w_2 + 2ℓ` with `ℓ` the linking number (`CV.exists_linkingNumber`): the retained set of
   `q₀` on `H` = self-crossings of `Λ₁` ∪ of `Λ₂` ∪ the mask-`uv` survivors (R-PAR `interlaced_pair`), the latter
   being exactly the mixed crossings of `D_A`, all positive.
5. **(13)** `R = R_1 + R_2 + 1` and **(12)** `UniformOrOneDissentCV` for `Λ₁, Λ₂`: turnlift (ii)
   (`CV.turnlift_full.polygon_two_pi_rot`) on the two oriented smoothings with the opposite new turns; the corner-sign
   ledger (6)/(12) from `sign_branch` (`s_x = σ, s_y = −σ, s_z = σ`) and `CV.selector_A` (≥ 2 inherited corners);
   `uniformrot` for the central triangle (`rot = ±1`).
Nothing of 1–5 is on the path of any other unit; U-174's RII deletion and U-177's RII-after-smoothing share 1–2.

## 6. Library / Mathlib pitfalls met

* `geomAt E t ht` is a `theorem` (a proof of the Prop `CrossingGeometry`), so `ht : t.val ≠ 0` can NEVER be inferred
  from a hypothesis mentioning `geomAt E t ht` — make it an explicit binder (the `⋯` in error messages is exactly this).
  Conversely `geomAt E t ht.1` and `(genericAt E t ht.1).crossingGeometry` are interchangeable by proof irrelevance.
* `LaurentPolynomial ℤ` coefficient of a difference: no `LaurentPolynomial.coeff_sub`; `by simp` proves
  `(p − q).coeff d = p.coeff d − q.coeff d` (`est_coeff_sub`).  `SM.Link.coeff_T_mul'` gives `(T n * p).coeff d = p.coeff (d − n)`;
  `aPow` is `abbrev` for `LaurentPolynomial.T`; `coeff_zRow` bridges `zRow k f` and `coeffAt d k f`.
* `CV.fulltwist_coefficient` needs `hL hH : componentCount = 1` — `rfl` for `carrierDiagram`
  (`geoPositiveLift_componentCount` is `rfl`); `absRot (carrierDiagram …) rfl = carrierR` is `rfl` after
  `unfold CV.absRot CV.carrierR` (the component polygon IS `geoCornerPolygon`, `geoPositiveLift_comp`).
* `EXT_homfly_wall` must be applied after `rw [GT_groupedPoly_eq_homfly]; unfold CV.carrierDiagram` (it is stated on
  `geoPositiveLift` with `CarrierGeometry` binders; unification fills `ofDiagrammatic …`), exactly as in
  `G11_empty_groupedPoly_eq`.
* `Finset.card_union_of_disjoint` still works under this Mathlib pin; `Finset.card_pair` needs the inequality of the
  transported crossings (`(crossingTransport hs).injective.ne`).
* `GT_tri_cases` + a 27-case `rcases … <;> first | …` is the cheapest way to exhaust the triangle; the label bash in
  `est_shared_not_mem_third` needs `hef heg hfg` explicitly (the labels are in `ZMod n`, no `omega`).
* `est_port_relation` mentions `est_wall`, `est_S_ind`, `est_S'_ind` inside its statement; they are Props, so any
  proof of them matches by proof irrelevance when the realiser instantiates it.

## 7. Notes for the executor / assembler

* The unit does NOT consume 155 (C) directly, only `CV.CarrierSlotFloor` (D-CVT-2, FR-CV-155-9) — as an explicit
  hypothesis `hF` of `est_ledger`; the instantiation `carrier_slot_floor_of_C SM.cf_thm_carrierfloor.clauseC` is the
  assembler's, when row 99 (C) lands.
* Sides: the fields quantify `ExtremeLocal` at `t`; `est_row` handles `t` = `K3` directly and `t` = empty by symmetry
  (`PRE_176_graphs_complementary` read backwards), so no coorientation enters (FR-R-174..177).
* Row-176 helper naming: all `est_`; nothing outside section `EST` (lines ≈ 790–1640) was changed.
