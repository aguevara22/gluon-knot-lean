import SM.FlatCarriers
import SM.CX1
import SM.CChamber

/-! # thm:C-S3 (the flat law) — SKELETON B

Design route B (work/drafts/cs3/PLAN_B.md), written 2026-09-13 by a Claude Code proof-architect
subagent. Target: `SM.thm_C_S3 : CS3Data` with the FIXED statement of work/drafts/CS3_statement.lean
(reference/SM/sm-4-knotlaws.tex:153-229). Checked with `cd work/lean && lake env lean
../drafts/cs3/Skeleton_B.lean`: no errors, `sorry` only inside the chain.

Organisation ("transport of the def:C data along a carrier correspondence", stated once, instantiated
three times):

* §0 Diagram layer (`SM.Link`): planar isotopy of one-component positive diagrams under (a) cyclic
  re-indexing (`Reindexed`, from the accepted `reparam_positiveDiagram_single_shift`), (b) a continuous
  family of generic one-component shadows (`Deform.of_family`, as in SM/CChamber.lean), (c) the
  subdivision of an edge at a point lying on no other edge (`appendVertex`; NEW geometry).
* §1 The geo ↔ accepted bridge on a generic polygon, and the flat configurations: the carrier
  correspondences of cor:flat-carriers as `Equiv`s onto the accepted `Carrier.Component`s of the two
  generic sides and of the deletion (`sideEquiv`, `delEquiv`).
* §2 The abstract transport lemma: for a generic configuration with a carrier bijection `e : ι ≃
  Component`, equal crossing counts, rotations and HOMFLY values give
  `cornerProduct = ∏ refCoefficient`, and equal weights away from one carrier give `wind = w(q₀) * U`.
* §3 The three instantiations (right, left, deletion) of the hypotheses of §2 from the fields of
  `FlatCarriersData`, the HOMFLY equality coming from §0 via the corner family across the wall.
* §4 The sums: reindexing both side sums and the deletion sum over the centre's independent
  supports, the standalone selector algebra, the one-parameter law, chamber constancy along a side
  (prop:C-chamber) and the assembly `thm_C_S3`.

Every lemma of the chain is stated; `sorry` only inside the chain, never in `thm_C_S3` itself. -/

set_option linter.unusedSectionVars false

namespace SM

open Link Carrier GeoCarrier

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## §0. Diagram layer: planar isotopies of one-component positive diagrams -/

namespace Link

/-- (L0.1) A cyclic shift of the labels preserves genericity of a one-component shadow
(`StrandMap.generic_pullback` along the accepted `shiftStrandMap`, regularity by `regular_shift`). -/
theorem single_generic_shift {k : ℕ} [NeZero k] (hk : 3 ≤ k) (Q : LabelledTuple k) (r : ZMod k)
    (hΓ : (Shadow.single ⟨k, hk, Q⟩).Generic) : (Shadow.single ⟨k, hk, shift r Q⟩).Generic :=
  (shiftStrandMap ⟨k, hk, Q⟩ r).generic_pullback hΓ
    (fun _ => (regular_shift r Q).mpr (hΓ.regular 0))

/-- (L0.2) Cyclic shift: the positive diagrams are planar isotopic (a `Reparam`,
`reparam_positiveDiagram_single_shift`). -/
theorem planarIsotopic_positiveDiagram_single_shift {k : ℕ} [NeZero k] (hk : 3 ≤ k) (Q : LabelledTuple k)
    (r : ZMod k) (hΓ : (Shadow.single ⟨k, hk, Q⟩).Generic)
    (hΓ' : (Shadow.single ⟨k, hk, shift r Q⟩).Generic) :
    PlanarIsotopic ((Shadow.single ⟨k, hk, Q⟩).positiveDiagram hΓ)
      ((Shadow.single ⟨k, hk, shift r Q⟩).positiveDiagram hΓ') :=
  PlanarIsotopic.of_reparam (reparam_positiveDiagram_single_shift ⟨k, hk, Q⟩ r hΓ hΓ')

/-- (L0.3) Genericity of a one-component shadow is invariant under `Reindexed` (an equality of sizes
and a cyclic shift). -/
theorem single_generic_of_reindexed {m m' : ℕ} [NeZero m] [NeZero m'] (hm : 3 ≤ m) (hm' : 3 ≤ m')
    {Q : LabelledTuple m} {Q' : LabelledTuple m'} (h : Reindexed Q Q')
    (hΓ : (Shadow.single ⟨m, hm, Q⟩).Generic) : (Shadow.single ⟨m', hm', Q'⟩).Generic := by
  obtain ⟨hmm, -⟩ := id h
  subst hmm
  obtain ⟨r, rfl⟩ := reindexed_eq_shift h
  exact single_generic_shift hm Q r hΓ

/-- (L0.4) The positive diagrams of `Reindexed` polygons are planar isotopic. -/
theorem planarIsotopic_positiveDiagram_single_of_reindexed {m m' : ℕ} [NeZero m] [NeZero m']
    (hm : 3 ≤ m) (hm' : 3 ≤ m') {Q : LabelledTuple m} {Q' : LabelledTuple m'} (h : Reindexed Q Q')
    (hΓ : (Shadow.single ⟨m, hm, Q⟩).Generic) (hΓ' : (Shadow.single ⟨m', hm', Q'⟩).Generic) :
    PlanarIsotopic ((Shadow.single ⟨m, hm, Q⟩).positiveDiagram hΓ)
      ((Shadow.single ⟨m', hm', Q'⟩).positiveDiagram hΓ') := by
  obtain ⟨hmm, -⟩ := id h
  subst hmm
  obtain ⟨r, rfl⟩ := reindexed_eq_shift h
  exact planarIsotopic_positiveDiagram_single_shift hm Q r hΓ hΓ'

/-- (L0.5) Along a continuous family of polygons whose one-component shadows are all generic, the
crossing pairs are constant: locally constant by the accepted `crossing_support_persists_of_geometry`
(through `crossingGeometry_of_single_generic`), hence constant on the connected `unitInterval`
(as `Carrier.isCrossing_transportedCornerPolygon_path`, SM/CChamber.lean). -/
theorem isCrossing_single_family_constant {k : ℕ} [NeZero k] (hk : 3 ≤ k)
    {Φ : unitInterval → LabelledTuple k} (hΦ : Continuous Φ)
    (hgen : ∀ s, (Shadow.single ⟨k, hk, Φ s⟩).Generic) (s : unitInterval)
    (x : Finset (ZMod k)) : IsCrossing (Φ s) x ↔ IsCrossing (Φ 0) x := by
  have hg : IsLocallyConstant fun s : unitInterval => {x | IsCrossing (Φ s) x} := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro t₀
    have hev := crossing_support_persists_of_geometry (crossingGeometry_of_single_generic hk (hgen t₀))
    filter_upwards [hΦ.continuousAt.eventually hev] with t' ht'
    exact Set.ext ht'
  exact Set.ext_iff.mp (IsLocallyConstant.apply_eq_of_preconnectedSpace hg s 0) x

/-- (L0.6) A continuous family of generic one-component shadows gives a generic deformation of the
positive diagrams (`Deform.of_family`, positivity persists by `Diagram.isPositive_deform_of_family`,
identification of the endpoint by `Shadow.eq_positiveDiagram_of_isPositive`; as
`Carrier.deform_positiveLift_path`). -/
theorem planarIsotopic_positiveDiagram_single_family {k : ℕ} [NeZero k] (hk : 3 ≤ k)
    {Φ : unitInterval → LabelledTuple k} (hΦ : Continuous Φ)
    (hgen : ∀ s, (Shadow.single ⟨k, hk, Φ s⟩).Generic) :
    PlanarIsotopic ((Shadow.single ⟨k, hk, Φ 0⟩).positiveDiagram (hgen 0))
      ((Shadow.single ⟨k, hk, Φ 1⟩).positiveDiagram (hgen 1)) := by
  let D : Diagram := (Shadow.single ⟨k, hk, Φ 0⟩).positiveDiagram (hgen 0)
  let V : unitInterval → D.Γ.Vertices := fun u _ => Φ u
  have hV : ∀ (i : Fin D.Γ.c) (j : ZMod (D.Γ.comp i).k), Continuous fun u => V u i j :=
    fun _ j => (continuous_apply j).comp hΦ
  have hgen' : ∀ u, (D.Γ.withVertices (V u)).Generic := fun u => hgen u
  have hcross : ∀ u (x : Finset D.Γ.Strand),
      (D.Γ.withVertices (V u)).IsCrossing x ↔ D.Γ.IsCrossing x :=
    fun u x => single_isCrossing_iff_of_forall hk
      (fun s => isCrossing_single_family_constant hk hΦ hgen u s) x
  have h0 : V 0 = D.Γ.vertices := rfl
  have hd : Deform D (D.deform (V 1) (hgen' 1) (hcross 1)) := Deform.of_family D hV hgen' hcross h0
  have heq : D.deform (V 1) (hgen' 1) (hcross 1) = (Shadow.single ⟨k, hk, Φ 1⟩).positiveDiagram (hgen 1) :=
    Shadow.eq_positiveDiagram_of_isPositive _ (hgen 1) _ rfl
      (D.isPositive_deform_of_family hV hgen' hcross h0
        (fun x => Shadow.positiveDiagram_isPositive _ _ x))
  rw [← heq]
  exact PlanarIsotopic.of_deform hd

/-- (L0.7a) Consecutive edges of a regular polygon meet only at their common vertex (independent
directions: `intersection_parameters_unique`; collinear same direction: parameter comparison). -/
theorem regular_adjacent_meet {k : ℕ} [NeZero k] {Q : LabelledTuple k} (hQ : Regular Q)
    (i : ZMod k) {x : Plane} (hx : x ∈ edgeSegment Q i) (hx' : x ∈ edgeSegment Q (i + 1)) :
    x = Q (i + 1) := by
  sorry

/-- (L0.7) Subdividing the closing edge `E_{-1}` of a generic one-component polygon at an interior
point lying on no other closed edge keeps the one-component shadow generic (`single_generic_of` with
the label case analysis `insertion_indices_exhaust`; regularity `regular_appendVertex`; the pieces
`[Q_{k-1}, p]`, `[p, Q_0]` are sub-segments of `E_{-1}` with directions `t₀ • E_{-1}`,
`(1 - t₀) • E_{-1}`; the new non-adjacent pairs `(k-1, 0)`, `(k, k-2)` do not meet by
`regular_adjacent_meet`). NEW GEOMETRY (risk 1). -/
theorem single_generic_appendVertex {k : ℕ} [NeZero k] (hk : 3 ≤ k) (Q : LabelledTuple k)
    {t₀ : ℝ} (h0 : 0 < t₀) (h1 : t₀ < 1) (hΓ : (Shadow.single ⟨k, hk, Q⟩).Generic)
    (hoff : ∀ i : ZMod k, i ≠ -1 → edgePoint Q (-1) t₀ ∉ edgeSegment Q i) :
    (Shadow.single ⟨k + 1, Nat.le_succ_of_le hk, appendVertex Q t₀⟩).Generic := by
  sorry

/-- (L0.8) The subdivision is a reparametrization of the positive diagram: `ReparamData` with
`e = id`, `φ` the piecewise-linear circle map sending `(i, u) ↦ (insertIndex i, u)` for `i ≠ -1` and
`(-1, u) ↦ (insertIndex (-1), u / t₀)` for `u < t₀`, `(insertedIndex k, (u - t₀) / (1 - t₀))` for
`u ≥ t₀` (strictly increasing on keys, so `traversalBetween` is preserved; `eval_eq` by the two
scalings; over occurrences correspond crossing by crossing since every crossing of the subdivision
comes from one of `Q` — the extra non-adjacent pairs do not meet — with positive rescaled directions).
NEW GEOMETRY (risk 1). -/
theorem reparam_positiveDiagram_single_appendVertex {k : ℕ} [NeZero k] (hk : 3 ≤ k)
    (Q : LabelledTuple k) {t₀ : ℝ} (h0 : 0 < t₀) (h1 : t₀ < 1)
    (hΓ : (Shadow.single ⟨k, hk, Q⟩).Generic)
    (hoff : ∀ i : ZMod k, i ≠ -1 → edgePoint Q (-1) t₀ ∉ edgeSegment Q i)
    (hΓ' : (Shadow.single ⟨k + 1, Nat.le_succ_of_le hk, appendVertex Q t₀⟩).Generic) :
    Reparam ((Shadow.single ⟨k, hk, Q⟩).positiveDiagram hΓ)
      ((Shadow.single ⟨k + 1, Nat.le_succ_of_le hk, appendVertex Q t₀⟩).positiveDiagram hΓ') := by
  sorry

end Link

/-! ## §1a. The geo ↔ accepted bridge on a generic polygon

Stated for an arbitrary proof `hP' : CrossingGeometry P` (all such proofs are equal, so the
`GeoComponent`s coincide by proof irrelevance): the four flat configurations use the proofs
`flatSideCG` / `flatDeletionCG`, which `rw` cannot unify with `generic_crossingGeometry`. -/

section GenericBridge

variable {m : ℕ} [NeZero m] (hm : 3 ≤ m) {P : LabelledTuple m} (hP : Generic P)
  (hP' : CrossingGeometry P) (S' : Finset (Crossing P))

/-- (F2.1) The retained crossings of a geo-carrier of a generic polygon are those of the accepted
carrier (`geoComponentEquivGeneric_owner`, injectivity of the equivalence). -/
theorem geoCarrierCrossings_eq_generic (q : GeoComponent hP' S') :
    geoCarrierCrossings hP' S' q =
      carrierCrossings hm hP S' (geoComponentEquivGeneric hm hP S' q) := by
  sorry

/-- (F2.2) Corner counts agree (`geoComponentCornerList_eq_generic`). -/
theorem geoCornerCount_eq_generic (q : GeoComponent hP' S') :
    geoCornerCount hP' S' q = ccpCornerCount hm hP S' (geoComponentEquivGeneric hm hP S' q) :=
  congrArg List.length (geoComponentCornerList_eq_generic hm hP S' q)

/-- (F2.3) The accepted corner polygon and the geo corner polygon of a generic polygon are the same
polygon up to `Reindexed` (in fact literally equal through the cast; `geoMarkPosition_eq_generic`,
`geoComponentCornerList_eq_generic`, `reindexed_of_cast`). -/
theorem reindexed_ccpCornerPolygon_geoCornerPolygon (q : GeoComponent hP' S') :
    Reindexed (ccpCornerPolygon hm hP S' (geoComponentEquivGeneric hm hP S' q))
      (geoCornerPolygon hP' S' q) := by
  sorry

/-- (F2.4) The selector depends only on the `Reindexed` class (`cornerSelector_congr`, `turn_shift`). -/
theorem cornerSelector_of_reindexed {m m' : ℕ} [NeZero m] [NeZero m'] {Q : LabelledTuple m}
    {Q' : LabelledTuple m'} (h : Reindexed Q Q') : cornerSelector Q' = cornerSelector Q := by
  obtain ⟨hmm, -⟩ := id h
  subst hmm
  obtain ⟨r, rfl⟩ := reindexed_eq_shift h
  apply cornerSelector_congr _ _ rfl
  · intro i
    exact ⟨i + r, by rw [turn_shift]⟩
  · intro i
    exact ⟨i - r, by rw [turn_shift, sub_add_cancel]⟩

/-- (F2.5) lem:C-X1's weight is the selector of the corner polygon (by the three clauses
`C_X1.weight_right/left/mixed` and `cornerSelector_of_all_right/left/mixed`). -/
theorem carrierWeight_eq_cornerSelector (q : Component hm hP S') :
    carrierWeight hm hP S' q = cornerSelector (ccpCornerPolygon hm hP S' q) := by
  by_cases hR : ∀ i, turn (ccpCornerPolygon hm hP S' q) i = -1
  · rw [C_X1.weight_right m hm P hP S' q hR, cornerSelector_of_all_right _ hR]
  · by_cases hL : ∀ i, turn (ccpCornerPolygon hm hP S' q) i = 1
    · rw [C_X1.weight_left m hm P hP S' q hL, cornerSelector_of_all_left _ hL]
    · rw [C_X1.weight_mixed m hm P hP S' q hR hL, cornerSelector_of_mixed _ hR hL]

/-- (F2.6) The geo selector of a carrier of a generic polygon is lem:C-X1's weight of the accepted
carrier. -/
theorem geoCarrierSelector_eq_carrierWeight (q : GeoComponent hP' S') :
    geoCarrierSelector hP' S' q =
      carrierWeight hm hP S' (geoComponentEquivGeneric hm hP S' q) := by
  rw [geoCarrierSelector_eq_cornerSelector, carrierWeight_eq_cornerSelector,
    cornerSelector_of_reindexed (reindexed_ccpCornerPolygon_geoCornerPolygon hm hP hP' S' q)]

end GenericBridge

/-! ## §2. The abstract transport of the def:C data along a carrier correspondence -/

section AbstractTransport

variable {m : ℕ} [NeZero m] (hm : 3 ≤ m) {P : LabelledTuple m} (hP : Generic P)
  {S' : Finset (Crossing P)} (hS' : IsDecomposition hm hP S') {ι : Type*} [Fintype ι]
  (e : ι ≃ Component hm hP S')

/-- The corner coefficient computed from reference data `(m_Q, r_Q, H⁺_Q)`:
`[a^{1 - m_Q - |r_Q|} z^0] H⁺_Q`. -/
def refCoefficient (mC : ℕ) (rC : ℝ) (HC : R) : ℤ :=
  coeffAt (1 - (mC : ℤ) - |round rC|) 0 HC

/-- (T1) A carrier whose crossing count, rotation and HOMFLY value are the reference data has the
reference coefficient (unfolding def:C). -/
theorem cornerCoefficient_eq_ref (q : ι) (mC : ℕ) (rC : ℝ) (HC : R)
    (hcount : carrierCrossingCount hm hP S' (e q) = mC)
    (hrot : carrierRotation hm hP S' (e q) = rC)
    (hH : homfly (positiveLift hm hP S' (e q) hS') = HC) :
    cornerCoefficient hm hP S' (e q) hS' = refCoefficient mC rC HC := by
  unfold cornerCoefficient cornerCoefficientWith cornerSlot carrierRotationInt refCoefficient
  rw [hcount, hrot, hH]

/-- (T2) **Transport of the coefficient product.** Along a carrier bijection `e` with equal
crossing counts, rotations and HOMFLY values, `∏_Q c(Q)` is the product of the reference
coefficients (`Fintype.prod_equiv`). -/
theorem cornerProduct_eq_of_carrier_data (mC : ι → ℕ) (rC : ι → ℝ) (HC : ι → R)
    (hcount : ∀ q, carrierCrossingCount hm hP S' (e q) = mC q)
    (hrot : ∀ q, carrierRotation hm hP S' (e q) = rC q)
    (hH : ∀ q, homfly (positiveLift hm hP S' (e q) hS') = HC q) :
    cornerProduct hm hP S' hS' = ∏ q : ι, refCoefficient (mC q) (rC q) (HC q) := by
  unfold cornerProduct
  exact (Fintype.prod_equiv e _ _
    (fun q => (cornerCoefficient_eq_ref hm hP hS' e q _ _ _ (hcount q) (hrot q) (hH q)).symm)).symm

/-- (T3) **Transport of the selector product up to one carrier.** If the weights agree with reference
weights away from `q₀`, `wind = wt(e q₀) * ∏_{q ≠ q₀} w(q)` (`Finset.mul_prod_erase`). -/
theorem wind_eq_of_weights (q₀ : ι) (wC : ι → ℤ)
    (hw : ∀ q, q ≠ q₀ → carrierWeight hm hP S' (e q) = wC q) :
    wind hm hP S' = carrierWeight hm hP S' (e q₀) * ∏ q ∈ Finset.univ.erase q₀, wC q := by
  unfold wind
  rw [← Fintype.prod_equiv e (fun q => carrierWeight hm hP S' (e q))
      (fun q' => carrierWeight hm hP S' q') (fun _ => rfl),
    ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ q₀)]
  congr 1
  exact Finset.prod_congr rfl fun q hq => hw q (Finset.ne_of_mem_erase hq)

end AbstractTransport

/-- (T4) **The selector algebra**, standalone: `(W_R − W_L) · U · B = W_D · U · B`. -/
theorem flat_term_identity (aR aL aD U B : ℤ) (h : aR - aL = aD) :
    aR * U * B - aL * U * B = aD * U * B := by
  rw [← h]
  ring

/-! ## §1b. The flat configurations: carrier correspondences as equivalences -/

section Flat

variable {n : ℕ} [NeZero n] (hn : 3 ≤ n) (g : WallGerm (n + 1)) (j : ZMod (n + 1))
    (hz : g.pointZeros = {turnSupport j})
    (hb : StrictBetween (g.center (j - 1)) (g.center j) (g.center (j + 1)))
    (hc : g.concurrences = ∅)

/-- The centre's independent supports `Ind(G_{P(0)})`, the common index set of the three sums. -/
def centreSupports : Finset (Finset (Crossing g.center)) :=
  Finset.univ.filter (GeoIndependent (flatCentreCG hn g j hz hb hc))

theorem mem_centreSupports (S : Finset (Crossing g.center)) :
    S ∈ centreSupports hn g j hz hb hc ↔ GeoIndependent (flatCentreCG hn g j hz hb hc) S := by
  simp [centreSupports]

variable (t : g.SideParameter) (hs : CommonSupports g t) (S : Finset (Crossing g.center))

/-- (F1.1) cor (i), sides: the side copy of a centre carrier, as an equivalence of geo-carriers
(`Quotient.congr (markTransport (hs b))`, well defined and injective by `correspond_sides.2`). -/
def sideCarrierEquiv (hF : FlatCarriersData hn g j hz hb hc t hs S) (b : Bool) :
    GeoComponent (flatCentreCG hn g j hz hb hc) S ≃
      GeoComponent (flatSideCG hn g b t) (transportSupport (hs b) S) :=
  Quotient.congr (markTransport (hs b)) (fun a a' => by
    have h := (hF.correspond_sides b).2 a a'
    rw [geoOwner_eq_iff, geoOwner_eq_iff] at h
    exact h)

theorem sideCarrierEquiv_owner (hF : FlatCarriersData hn g j hz hb hc t hs S) (b : Bool)
    (a : Mark g.center) :
    sideCarrierEquiv hn g j hz hb hc t hs S hF b (geoOwner (flatCentreCG hn g j hz hb hc) S a) =
      geoOwner (flatSideCG hn g b t) (transportSupport (hs b) S) (markTransport (hs b) a) := rfl

/-- (F1.2) cor (i), deletion: the centre copy of a deletion carrier (`Quotient.lift` of
`geoOwner ∘ fusionMark`, well defined by `correspond_deletion.2.1`). -/
def delToCentre (hF : FlatCarriersData hn g j hz hb hc t hs S) :
    GeoComponent (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S) →
      GeoComponent (flatCentreCG hn g j hz hb hc) S :=
  Quotient.lift (fun b => geoOwner (flatCentreCG hn g j hz hb hc) S (fusionMark hn g j hz hb hc b))
    (fun b b' hbb' => (hF.correspond_deletion.2.1 b b').mp ((geoOwner_eq_iff _ _ _ _).mpr hbb'))

/-- The assignment is a bijection: injective by `correspond_deletion.2.1`, surjective by
`correspond_deletion.2.2`. -/
theorem delToCentre_bijective (hF : FlatCarriersData hn g j hz hb hc t hs S) :
    Function.Bijective (delToCentre hn g j hz hb hc t hs S hF) := by
  constructor
  · intro x y hxy
    induction x using Quotient.inductionOn with
    | h b =>
      induction y using Quotient.inductionOn with
      | h b' =>
        show geoOwner (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S) b =
          geoOwner (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S) b'
        exact (hF.correspond_deletion.2.1 b b').mpr hxy
  · intro q
    obtain ⟨b, hb'⟩ := hF.correspond_deletion.2.2 q
    exact ⟨geoOwner (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S) b, hb'⟩

/-- The deletion copy of a centre carrier. -/
def delCarrierEquiv (hF : FlatCarriersData hn g j hz hb hc t hs S) :
    GeoComponent (flatCentreCG hn g j hz hb hc) S ≃
      GeoComponent (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S) :=
  (Equiv.ofBijective _ (delToCentre_bijective hn g j hz hb hc t hs S hF)).symm

theorem delCarrierEquiv_owner (hF : FlatCarriersData hn g j hz hb hc t hs S)
    (b : Mark (deleteVertex g.center j)) :
    delCarrierEquiv hn g j hz hb hc t hs S hF
        (geoOwner (flatCentreCG hn g j hz hb hc) S (fusionMark hn g j hz hb hc b)) =
      geoOwner (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S) b := by
  unfold delCarrierEquiv
  rw [Equiv.symm_apply_eq]
  rfl

/-- The side copy read as an accepted carrier of the generic side polygon
(`geoComponentEquivGeneric`; `flatSideCG` is `generic_crossingGeometry` by proof irrelevance). -/
def sideEquiv (hF : FlatCarriersData hn g j hz hb hc t hs S) (b : Bool) :
    GeoComponent (flatCentreCG hn g j hz hb hc) S ≃
      Component (flat_hn1 hn) (g.sideTuple b t).property (transportSupport (hs b) S) :=
  (sideCarrierEquiv hn g j hz hb hc t hs S hF b).trans
    (geoComponentEquivGeneric (flat_hn1 hn) (g.sideTuple b t).property (transportSupport (hs b) S))

/-- The deletion copy read as an accepted carrier of the generic deletion. -/
def delEquiv (hF : FlatCarriersData hn g j hz hb hc t hs S) :
    GeoComponent (flatCentreCG hn g j hz hb hc) S ≃
      Component hn (generic_deleteVertex hn hz hb hc) (deletionSupport hn g j hz hb hc S) :=
  (delCarrierEquiv hn g j hz hb hc t hs S hF).trans
    (geoComponentEquivGeneric hn (generic_deleteVertex hn hz hb hc) (deletionSupport hn g j hz hb hc S))

theorem sideEquiv_owner (hF : FlatCarriersData hn g j hz hb hc t hs S) (b : Bool)
    (a : Mark g.center) :
    sideEquiv hn g j hz hb hc t hs S hF b (geoOwner (flatCentreCG hn g j hz hb hc) S a) =
      owner (flat_hn1 hn) (g.sideTuple b t).property (transportSupport (hs b) S)
        (markTransport (hs b) a) := rfl

theorem delEquiv_owner (hF : FlatCarriersData hn g j hz hb hc t hs S)
    (b : Mark (deleteVertex g.center j)) :
    delEquiv hn g j hz hb hc t hs S hF
        (geoOwner (flatCentreCG hn g j hz hb hc) S (fusionMark hn g j hz hb hc b)) =
      owner hn (generic_deleteVertex hn hz hb hc) (deletionSupport hn g j hz hb hc S) b := by
  unfold delEquiv
  rw [Equiv.trans_apply, delCarrierEquiv_owner]
  rfl

/-- The distinguished carrier `Q_*` on the sides is the side carrier of the vertex mark `j`
(`markTransport` fixes vertices). -/
theorem sideEquiv_central (hF : FlatCarriersData hn g j hz hb hc t hs S) (b : Bool) :
    sideEquiv hn g j hz hb hc t hs S hF b (centralCarrierThroughJ hn g j hz hb hc S) =
      owner (flat_hn1 hn) (g.sideTuple b t).property (transportSupport (hs b) S) (Sum.inl j) := rfl

/-- The deletion copy of `Q_*` is `deletionCopyThroughJ` (`central_vs_deletion_through_mu_j.1`,
`fusionMark_delMark`, `geoOwner_successor`). -/
theorem delEquiv_central (hF : FlatCarriersData hn g j hz hb hc t hs S) :
    delEquiv hn g j hz hb hc t hs S hF (centralCarrierThroughJ hn g j hz hb hc S) =
      geoComponentEquivGeneric hn (generic_deleteVertex hn hz hb hc) (deletionSupport hn g j hz hb hc S)
        (deletionCopyThroughJ hn g j hz hb hc S) := by
  have h1 := hF.central_vs_deletion_through_mu_j.1
  have h2 : centralCarrierThroughJ hn g j hz hb hc S =
      geoOwner (flatCentreCG hn g j hz hb hc) S
        (fusionMark hn g j hz hb hc (delMark hn g j hz hb hc
          (geoSmoothingSuccessor (flatCentreCG hn g j hz hb hc) S (Sum.inl j)))) := by
    rw [fusionMark_delMark hn g j hz hb hc _ h1, geoOwner_successor]
    rfl
  rw [h2]
  unfold delEquiv
  rw [Equiv.trans_apply, delCarrierEquiv_owner]
  rfl

/-- Decomposition hypotheses on the sides and on the deletion (def:flat-carriers,
`independent_supports`). -/
theorem side_isDecomposition (hD : FlatCarriersDefinitionData hn g j hz hb hc t hs S)
    (hS : GeoIndependent (flatCentreCG hn g j hz hb hc) S) (b : Bool) :
    IsDecomposition (flat_hn1 hn) (g.sideTuple b t).property (transportSupport (hs b) S) :=
  (hD.independent_supports.1 b).mp hS

theorem del_isDecomposition (hD : FlatCarriersDefinitionData hn g j hz hb hc t hs S)
    (hS : GeoIndependent (flatCentreCG hn g j hz hb hc) S) :
    IsDecomposition hn (generic_deleteVertex hn hz hb hc) (deletionSupport hn g j hz hb hc S) :=
  hD.independent_supports.2.mp hS

/-- Every centre carrier has at least three corners (its side copy is an accepted carrier of a
decomposition: `geoCornerCount_markTransport`, `geoCornerCount_eq_generic`,
`ccpCornerCount_ge_three`). -/
theorem three_le_geoCornerCount_centre (hD : FlatCarriersDefinitionData hn g j hz hb hc t hs S)
    (hS : GeoIndependent (flatCentreCG hn g j hz hb hc) S)
    (q : GeoComponent (flatCentreCG hn g j hz hb hc) S) :
    3 ≤ geoCornerCount (flatCentreCG hn g j hz hb hc) S q := by
  obtain ⟨a, rfl⟩ := geoOwner_surjective (flatCentreCG hn g j hz hb hc) S q
  rw [geoCornerCount_markTransport (flatCentreCG hn g j hz hb hc) (flatSideCG hn g true t) (hs true)
      (hD.identify_sides_marks true) S a,
    geoCornerCount_eq_generic (flat_hn1 hn) (g.sideTuple true t).property (flatSideCG hn g true t)]
  exact ccpCornerCount_ge_three (flat_hn1 hn) (g.sideTuple true t).property
    (side_isDecomposition hn g j hz hb hc t hs S hD hS true) _

/-! ## §3a. The slot data: crossing counts and rotations (cor (ii)) -/

/-- (F3.1) `m_Q` of the side copy is the centre carrier's retained-crossing count
(`same_retained_crossings.1`, `geoCarrierCrossings_eq_generic`, `Finset.card_map`). -/
theorem carrierCrossingCount_side (hF : FlatCarriersData hn g j hz hb hc t hs S) (b : Bool)
    (q : GeoComponent (flatCentreCG hn g j hz hb hc) S) :
    carrierCrossingCount (flat_hn1 hn) (g.sideTuple b t).property (transportSupport (hs b) S)
        (sideEquiv hn g j hz hb hc t hs S hF b q) =
      (geoCarrierCrossings (flatCentreCG hn g j hz hb hc) S q).card := by
  obtain ⟨a, rfl⟩ := geoOwner_surjective (flatCentreCG hn g j hz hb hc) S q
  have h1 : carrierCrossings (flat_hn1 hn) (g.sideTuple b t).property (transportSupport (hs b) S)
      (sideEquiv hn g j hz hb hc t hs S hF b (geoOwner (flatCentreCG hn g j hz hb hc) S a)) =
      geoCarrierCrossings (flatSideCG hn g b t) (transportSupport (hs b) S)
        (geoOwner (flatSideCG hn g b t) (transportSupport (hs b) S) (markTransport (hs b) a)) :=
    (geoCarrierCrossings_eq_generic (flat_hn1 hn) (g.sideTuple b t).property (flatSideCG hn g b t)
      (transportSupport (hs b) S)
      (geoOwner (flatSideCG hn g b t) (transportSupport (hs b) S) (markTransport (hs b) a))).symm
  have h2 : geoCarrierCrossings (flatSideCG hn g b t) (transportSupport (hs b) S)
      (geoOwner (flatSideCG hn g b t) (transportSupport (hs b) S) (markTransport (hs b) a)) =
      (geoCarrierCrossings (flatCentreCG hn g j hz hb hc) S
        (geoOwner (flatCentreCG hn g j hz hb hc) S a)).map (crossingTransport (hs b)).toEmbedding := by
    ext x'
    obtain ⟨x, rfl⟩ := (crossingTransport (hs b)).surjective x'
    rw [Finset.mem_map_equiv, Equiv.symm_apply_apply]
    exact (hF.same_retained_crossings.1 b a x).symm
  rw [carrierCrossingCount_eq_card, h1, h2, Finset.card_map]

/-- (F3.2) `m_Q` of the deletion copy (`same_retained_crossings.2`). -/
theorem carrierCrossingCount_del (hF : FlatCarriersData hn g j hz hb hc t hs S)
    (q : GeoComponent (flatCentreCG hn g j hz hb hc) S) :
    carrierCrossingCount hn (generic_deleteVertex hn hz hb hc) (deletionSupport hn g j hz hb hc S)
        (delEquiv hn g j hz hb hc t hs S hF q) =
      (geoCarrierCrossings (flatCentreCG hn g j hz hb hc) S q).card := by
  obtain ⟨b', hb'⟩ := hF.correspond_deletion.2.2 q
  subst hb'
  have h1 : carrierCrossings hn (generic_deleteVertex hn hz hb hc) (deletionSupport hn g j hz hb hc S)
      (owner hn (generic_deleteVertex hn hz hb hc) (deletionSupport hn g j hz hb hc S) b') =
      geoCarrierCrossings (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S)
        (geoOwner (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S) b') :=
    (geoCarrierCrossings_eq_generic hn (generic_deleteVertex hn hz hb hc) (flatDeletionCG hn g j hz hb hc)
      (deletionSupport hn g j hz hb hc S)
      (geoOwner (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S) b')).symm
  have h2 : geoCarrierCrossings (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S)
      (geoOwner (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S) b') =
      (geoCarrierCrossings (flatCentreCG hn g j hz hb hc) S
        (geoOwner (flatCentreCG hn g j hz hb hc) S (fusionMark hn g j hz hb hc b'))).map
          (fusionCrossingEquiv hn hz hb hc).toEmbedding := by
    ext x'
    obtain ⟨x, rfl⟩ := (fusionCrossingEquiv hn hz hb hc).surjective x'
    rw [Finset.mem_map_equiv, Equiv.symm_apply_apply]
    exact (hF.same_retained_crossings.2 b' x).symm
  rw [carrierCrossingCount_eq_card, delEquiv_owner, h1, h2, Finset.card_map]

/-- (F4.1) `r_Q` of the side copy is the centre carrier's rotation (`same_rotation.1`,
`rotationNumber_of_reindexed` with `reindexed_ccpCornerPolygon_geoCornerPolygon`). -/
theorem carrierRotation_side (hF : FlatCarriersData hn g j hz hb hc t hs S) (b : Bool)
    (q : GeoComponent (flatCentreCG hn g j hz hb hc) S) :
    carrierRotation (flat_hn1 hn) (g.sideTuple b t).property (transportSupport (hs b) S)
        (sideEquiv hn g j hz hb hc t hs S hF b q) =
      rotationNumber (geoCornerPolygon (flatCentreCG hn g j hz hb hc) S q) := by
  obtain ⟨a, rfl⟩ := geoOwner_surjective (flatCentreCG hn g j hz hb hc) S q
  have h1 : carrierRotation (flat_hn1 hn) (g.sideTuple b t).property (transportSupport (hs b) S)
      (sideEquiv hn g j hz hb hc t hs S hF b (geoOwner (flatCentreCG hn g j hz hb hc) S a)) =
      rotationNumber (geoCornerPolygon (flatSideCG hn g b t) (transportSupport (hs b) S)
        (geoOwner (flatSideCG hn g b t) (transportSupport (hs b) S) (markTransport (hs b) a))) :=
    (rotationNumber_of_reindexed (reindexed_ccpCornerPolygon_geoCornerPolygon (flat_hn1 hn)
      (g.sideTuple b t).property (flatSideCG hn g b t) (transportSupport (hs b) S)
      (geoOwner (flatSideCG hn g b t) (transportSupport (hs b) S) (markTransport (hs b) a)))).symm
  rw [h1]
  exact (hF.same_rotation.1 b a).1

/-- (F4.2) `r_Q` of the deletion copy (`same_rotation.2`). -/
theorem carrierRotation_del (hF : FlatCarriersData hn g j hz hb hc t hs S)
    (q : GeoComponent (flatCentreCG hn g j hz hb hc) S) :
    carrierRotation hn (generic_deleteVertex hn hz hb hc) (deletionSupport hn g j hz hb hc S)
        (delEquiv hn g j hz hb hc t hs S hF q) =
      rotationNumber (geoCornerPolygon (flatCentreCG hn g j hz hb hc) S q) := by
  obtain ⟨b', hb'⟩ := hF.correspond_deletion.2.2 q
  subst hb'
  have h1 : carrierRotation hn (generic_deleteVertex hn hz hb hc) (deletionSupport hn g j hz hb hc S)
      (owner hn (generic_deleteVertex hn hz hb hc) (deletionSupport hn g j hz hb hc S) b') =
      rotationNumber (geoCornerPolygon (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S)
        (geoOwner (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S) b')) :=
    (rotationNumber_of_reindexed (reindexed_ccpCornerPolygon_geoCornerPolygon hn
      (generic_deleteVertex hn hz hb hc) (flatDeletionCG hn g j hz hb hc)
      (deletionSupport hn g j hz hb hc S)
      (geoOwner (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S) b'))).symm
  rw [delEquiv_owner, h1]
  exact (hF.same_rotation.2 b').1

/-! ## §3b. The selectors (cor (iii)) -/

/-- (F5.1) Away from `Q_*` the side weight is the deletion weight (`other_selectors_agree`,
`geoCarrierSelector_eq_carrierWeight`, surjectivity `correspond_deletion.2.2`). -/
theorem carrierWeight_side_eq_del (hF : FlatCarriersData hn g j hz hb hc t hs S) (b : Bool)
    (q : GeoComponent (flatCentreCG hn g j hz hb hc) S)
    (hq : q ≠ centralCarrierThroughJ hn g j hz hb hc S) :
    carrierWeight (flat_hn1 hn) (g.sideTuple b t).property (transportSupport (hs b) S)
        (sideEquiv hn g j hz hb hc t hs S hF b q) =
      carrierWeight hn (generic_deleteVertex hn hz hb hc) (deletionSupport hn g j hz hb hc S)
        (delEquiv hn g j hz hb hc t hs S hF q) := by
  obtain ⟨b', hb'⟩ := hF.correspond_deletion.2.2 q
  subst hb'
  have h1 : carrierWeight (flat_hn1 hn) (g.sideTuple b t).property (transportSupport (hs b) S)
      (sideEquiv hn g j hz hb hc t hs S hF b
        (geoOwner (flatCentreCG hn g j hz hb hc) S (fusionMark hn g j hz hb hc b'))) =
      geoCarrierSelector (flatSideCG hn g b t) (transportSupport (hs b) S)
        (geoOwner (flatSideCG hn g b t) (transportSupport (hs b) S)
          (markTransport (hs b) (fusionMark hn g j hz hb hc b'))) :=
    (geoCarrierSelector_eq_carrierWeight (flat_hn1 hn) (g.sideTuple b t).property (flatSideCG hn g b t)
      (transportSupport (hs b) S)
      (geoOwner (flatSideCG hn g b t) (transportSupport (hs b) S)
        (markTransport (hs b) (fusionMark hn g j hz hb hc b')))).symm
  have h2 : carrierWeight hn (generic_deleteVertex hn hz hb hc) (deletionSupport hn g j hz hb hc S)
      (owner hn (generic_deleteVertex hn hz hb hc) (deletionSupport hn g j hz hb hc S) b') =
      geoCarrierSelector (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S)
        (geoOwner (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S) b') :=
    (geoCarrierSelector_eq_carrierWeight hn (generic_deleteVertex hn hz hb hc) (flatDeletionCG hn g j hz hb hc)
      (deletionSupport hn g j hz hb hc S)
      (geoOwner (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S) b')).symm
  rw [h1, delEquiv_owner, h2]
  exact hF.other_selectors_agree b b' hq

/-- (F5.2) eq. ccf:distinguished-selector: `W(Q_*^right) − W(Q_*^left) = W(Q_*^D)`
(`selector_identity`, `sideEquiv_central`, `delEquiv_central`). -/
theorem carrierWeight_central (hF : FlatCarriersData hn g j hz hb hc t hs S) (bR bL : Bool)
    (hR : IsRightSide g j bR t) (hL : IsLeftSide g j bL t) :
    carrierWeight (flat_hn1 hn) (g.sideTuple bR t).property (transportSupport (hs bR) S)
        (sideEquiv hn g j hz hb hc t hs S hF bR (centralCarrierThroughJ hn g j hz hb hc S)) -
      carrierWeight (flat_hn1 hn) (g.sideTuple bL t).property (transportSupport (hs bL) S)
        (sideEquiv hn g j hz hb hc t hs S hF bL (centralCarrierThroughJ hn g j hz hb hc S)) =
    carrierWeight hn (generic_deleteVertex hn hz hb hc) (deletionSupport hn g j hz hb hc S)
      (delEquiv hn g j hz hb hc t hs S hF (centralCarrierThroughJ hn g j hz hb hc S)) := by
  have key := hF.selector_identity bR bL hR hL
  rw [geoCarrierSelector_eq_carrierWeight (flat_hn1 hn) (g.sideTuple bR t).property
      (flatSideCG hn g bR t) (transportSupport (hs bR) S),
    geoCarrierSelector_eq_carrierWeight (flat_hn1 hn) (g.sideTuple bL t).property
      (flatSideCG hn g bL t) (transportSupport (hs bL) S),
    geoCarrierSelector_eq_carrierWeight hn (generic_deleteVertex hn hz hb hc)
      (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S)] at key
  rw [delEquiv_central]
  exact key

/-! ## §3c. The HOMFLY values: the corner family across the wall -/

/-- The definition data along the whole side interval `(0, t]` (from `flat_carriers_definition`,
whose radius covers every `s < δ`): needed to certify genericity of the corner polygons of the
positive lifts at every intermediate side parameter of the deformation. -/
def SidePathData (t : g.SideParameter) : Prop :=
  ∀ s : g.SideParameter, s.val ≤ t.val → ∃ hs : CommonSupports g s,
    ∀ S : Finset (Crossing g.center), GeoIndependent (flatCentreCG hn g j hz hb hc) S →
      FlatCarriersDefinitionData hn g j hz hb hc s hs S

/-- (F6a) Continuity of the mark points at ANY parameter on the geometric record domain
(`continuousAt_markPointOn` generalised from the centre: vertices by `g.continuous_curve`, visits by
`continuousAt_edgeParameter_of_geometry` at `g.curve s`, the centre's crossing pairs persisting). -/
theorem continuousAt_markPointOn_of_geometry (s : g.Parameter) (hC : CrossingGeometry (g.curve s))
    (hcr : ∀ c : Finset (ZMod (n + 1)), IsCrossing g.center c → IsCrossing (g.curve s) c)
    (a : Mark g.center) : ContinuousAt (fun s => markPointOn g s a) s := by
  cases a with
  | inl i => exact ((continuous_apply i).comp g.continuous_curve).continuousAt
  | inr v =>
    have hcross : IsCrossing (g.curve s) {v.2.val, (visitTwin v).2.val} := by
      apply hcr
      rw [← visit_crossing_val_eq_pair v]
      exact v.1.property
    have hF : ContinuousAt (fun Q : LabelledTuple (n + 1) =>
        edgePoint Q v.2.val (edgeParameter Q v.2.val (visitTwin v).2.val)) (g.curve s) :=
      (continuous_vertex v.2.val).continuousAt.add
        ((continuousAt_edgeParameter_of_geometry hC hcross).smul
          (continuous_edge v.2.val).continuousAt)
    exact ContinuousAt.comp (f := g.curve) (x := s) hF g.continuous_curve.continuousAt

/-- The parameter `u ↦ ±(u · t)` of the family from the centre (`u = 0`) to the side `b` at `t`
(`u = 1`). -/
def famParam (b : Bool) (u : unitInterval) : g.Parameter :=
  ⟨if b then u.val * t.val else -(u.val * t.val), by
    have h0 := u.property.1
    have h1 := u.property.2
    have ht0 := t.property.1
    have ht1 := t.property.2
    have hr := g.radius_pos
    have hut : u.val * t.val ≤ t.val := by nlinarith
    have hut0 : 0 ≤ u.val * t.val := by positivity
    split_ifs <;> constructor <;> linarith⟩

theorem famParam_zero (b : Bool) : famParam g t b 0 = g.zeroParameter := by
  apply Subtype.ext
  simp [famParam, WallGerm.zeroParameter]

theorem famParam_one (b : Bool) : famParam g t b 1 = g.sideTime b t := by
  apply Subtype.ext
  cases b <;> simp [famParam, WallGerm.sideTime]

/-- At a positive family parameter the polygon is a side polygon (`famParam g t b u = sideTime b s`
with `s = u · t`). -/
theorem famParam_pos (b : Bool) (u : unitInterval) (hu : 0 < u.val) :
    famParam g t b u = g.sideTime b ⟨u.val * t.val, mul_pos hu t.property.1,
      lt_of_le_of_lt (mul_le_of_le_one_left t.property.1.le u.property.2) t.property.2⟩ := by
  apply Subtype.ext
  cases b <;> simp [famParam, WallGerm.sideTime]

theorem continuous_famParam (b : Bool) : Continuous (famParam g t b) := by
  apply Continuous.subtype_mk
  cases b
  · exact (continuous_subtype_val.mul continuous_const).neg
  · exact continuous_subtype_val.mul continuous_const

/-- Along the family the centre's crossing pairs persist (trivial at `u = 0`; `CommonSupports` of
`SidePathData` at `u > 0`). -/
theorem famParam_crossings (hpath : SidePathData hn g j hz hb hc t) (b : Bool) (u : unitInterval)
    (c : Finset (ZMod (n + 1))) (hcen : IsCrossing g.center c) :
    IsCrossing (g.curve (famParam g t b u)) c := by
  sorry

/-- The corner polygon of the centre carrier `q` read along the family towards the side `b`. -/
def sideFamily (q : GeoComponent (flatCentreCG hn g j hz hb hc) S) (b : Bool) :
    unitInterval → LabelledTuple (geoCornerCount (flatCentreCG hn g j hz hb hc) S q) :=
  fun u => cornerFamily hn g j hz hb hc S q (famParam g t b u)

theorem sideFamily_zero (q : GeoComponent (flatCentreCG hn g j hz hb hc) S) (b : Bool) :
    sideFamily hn g j hz hb hc t S q b 0 = geoCornerPolygon (flatCentreCG hn g j hz hb hc) S q := by
  unfold sideFamily
  rw [famParam_zero, cornerFamily_zero]

theorem sideFamily_one (q : GeoComponent (flatCentreCG hn g j hz hb hc) S) (b : Bool) :
    sideFamily hn g j hz hb hc t S q b 1 = cornerFamily hn g j hz hb hc S q (g.sideTime b t) := by
  unfold sideFamily
  rw [famParam_one]

/-- (F6a') The family is continuous (`continuousAt_markPointOn_of_geometry` at every `famParam u`,
whose polygon has crossing geometry by `flat_germ_spatial_data` and carries the centre's crossing
pairs by `famParam_crossings`; `continuous_pi`). -/
theorem continuous_sideFamily (hpath : SidePathData hn g j hz hb hc t)
    (q : GeoComponent (flatCentreCG hn g j hz hb hc) S) (b : Bool) :
    Continuous (sideFamily hn g j hz hb hc t S q b) := by
  have hcont : ∀ a : Mark g.center,
      Continuous fun u : unitInterval => markPointOn g (famParam g t b u) a := by
    intro a
    rw [continuous_iff_continuousAt]
    intro u
    have hC : CrossingGeometry (g.curve (famParam g t b u)) :=
      (flat_germ_spatial_data (by omega) g hz hb hc (famParam g t b u)).1
    exact (continuousAt_markPointOn_of_geometry g (famParam g t b u) hC
      (famParam_crossings hn g j hz hb hc t hpath b u) a).comp
        (continuous_famParam g t b).continuousAt
  unfold sideFamily cornerFamily
  exact continuous_pi fun k => hcont _

/-- (F6b) At a side parameter `s` (with its definition data) the family is a re-indexing of the
accepted corner polygon of the side copy (`geoComponentCornerList_markTransport` with
`identify_sides_marks`, `markPointOn_side`, `reindexed_ccpCornerPolygon_geoCornerPolygon`; the
device of `rotationNumber_cornerFamily_side`). -/
theorem reindexed_cornerFamily_side (s : g.SideParameter) (hs' : CommonSupports g s)
    (hD' : FlatCarriersDefinitionData hn g j hz hb hc s hs' S) (b : Bool) (a : Mark g.center) :
    Reindexed
      (ccpCornerPolygon (flat_hn1 hn) (g.sideTuple b s).property (transportSupport (hs' b) S)
        (geoComponentEquivGeneric (flat_hn1 hn) (g.sideTuple b s).property (transportSupport (hs' b) S)
          (geoOwner (flatSideCG hn g b s) (transportSupport (hs' b) S) (markTransport (hs' b) a))))
      (cornerFamily hn g j hz hb hc S (geoOwner (flatCentreCG hn g j hz hb hc) S a)
        (g.sideTime b s)) := by
  sorry

/-- (F6b') Hence the family's one-component shadow is generic at every side parameter
(`carrierShadow_generic`, `single_generic_of_reindexed`). -/
theorem single_generic_cornerFamily_side (s : g.SideParameter) (hs' : CommonSupports g s)
    (hD' : FlatCarriersDefinitionData hn g j hz hb hc s hs' S)
    (hS : GeoIndependent (flatCentreCG hn g j hz hb hc) S) (b : Bool)
    (q : GeoComponent (flatCentreCG hn g j hz hb hc) S)
    (hk : 3 ≤ geoCornerCount (flatCentreCG hn g j hz hb hc) S q) :
    (Shadow.single ⟨_, hk, cornerFamily hn g j hz hb hc S q (g.sideTime b s)⟩).Generic := by
  obtain ⟨a, rfl⟩ := geoOwner_surjective (flatCentreCG hn g j hz hb hc) S q
  exact Link.single_generic_of_reindexed
    (ccpCornerCount_ge_three (flat_hn1 hn) (g.sideTuple b s).property
      (side_isDecomposition hn g j hz hb hc s hs' S hD' hS b) _) hk
    (reindexed_cornerFamily_side hn g j hz hb hc S s hs' hD' b a)
    (carrierShadow_generic (flat_hn1 hn) (g.sideTuple b s).property (transportSupport (hs' b) S) _
      (side_isDecomposition hn g j hz hb hc s hs' S hD' hS b))

/-- (F6c) cor (i) "every other central carrier is unchanged by deletion": for `q ≠ Q_*` the centre
corner polygon is a re-indexing of the deletion copy's accepted corner polygon
(`others_unchanged.2.1`, `fusion_mark_point`, `reindexed_markPolygon_of_isRotated`,
`reindexed_markPolygon_map`, `markPolygon_congr`; the device of `rotationNumber_others_unchanged`). -/
theorem reindexed_del_centre_of_ne (hF : FlatCarriersData hn g j hz hb hc t hs S)
    (q : GeoComponent (flatCentreCG hn g j hz hb hc) S)
    (hq : q ≠ centralCarrierThroughJ hn g j hz hb hc S) :
    Reindexed
      (ccpCornerPolygon hn (generic_deleteVertex hn hz hb hc) (deletionSupport hn g j hz hb hc S)
        (delEquiv hn g j hz hb hc t hs S hF q))
      (geoCornerPolygon (flatCentreCG hn g j hz hb hc) S q) := by
  sorry

/-- (F6d) cor (i) "differs from its deletion copy only by the positive-flat subdivision at `μ_j`":
the centre corner polygon of `Q_*` is a re-indexing of `appendVertex` of a cyclic shift of the
deletion copy's corner polygon, the new vertex `μ_j` lying strictly inside the closing edge and on no
other closed edge of the deletion polygon (`central_vs_deletion_through_mu_j.3`, `turns_nonzero.1`
with `flat_of_turn_eq_zero`, the list surgery of `rotationNumber_erase_flat`,
`reindexed_appendVertex_markPolygon`; the off-edge clause from `Link.consecutive_meet`,
`Link.nonadjacent_meet_crossing` on the deletion, `crossingPoint_fusion`, the centre's
`crossingPoint ≠ vertex` of `flat_germ_spatial_data`, and injectivity of `g.center`). RISK 2. -/
theorem flat_vertex_subdivision (hF : FlatCarriersData hn g j hz hb hc t hs S) :
    ∃ (r : ZMod (ccpCornerCount hn (generic_deleteVertex hn hz hb hc)
        (deletionSupport hn g j hz hb hc S)
        (delEquiv hn g j hz hb hc t hs S hF (centralCarrierThroughJ hn g j hz hb hc S))))
      (t₀ : ℝ), 0 < t₀ ∧ t₀ < 1 ∧
      (∀ i, i ≠ -1 →
        edgePoint (shift r (ccpCornerPolygon hn (generic_deleteVertex hn hz hb hc)
          (deletionSupport hn g j hz hb hc S)
          (delEquiv hn g j hz hb hc t hs S hF (centralCarrierThroughJ hn g j hz hb hc S)))) (-1) t₀ ∉
        edgeSegment (shift r (ccpCornerPolygon hn (generic_deleteVertex hn hz hb hc)
          (deletionSupport hn g j hz hb hc S)
          (delEquiv hn g j hz hb hc t hs S hF (centralCarrierThroughJ hn g j hz hb hc S)))) i) ∧
      Reindexed
        (appendVertex (shift r (ccpCornerPolygon hn (generic_deleteVertex hn hz hb hc)
          (deletionSupport hn g j hz hb hc S)
          (delEquiv hn g j hz hb hc t hs S hF (centralCarrierThroughJ hn g j hz hb hc S)))) t₀)
        (geoCornerPolygon (flatCentreCG hn g j hz hb hc) S
          (centralCarrierThroughJ hn g j hz hb hc S)) := by
  sorry

/-- (F6e) The centre corner polygon of every carrier is a generic one-component shadow: away from
`Q_*` a re-indexing of a generic deletion carrier polygon (F6c), for `Q_*` a subdivision of one
(F6d, `single_generic_appendVertex`, `single_generic_shift`). -/
theorem single_generic_centre (hD : FlatCarriersDefinitionData hn g j hz hb hc t hs S)
    (hF : FlatCarriersData hn g j hz hb hc t hs S)
    (hS : GeoIndependent (flatCentreCG hn g j hz hb hc) S)
    (q : GeoComponent (flatCentreCG hn g j hz hb hc) S) :
    (Shadow.single ⟨_, three_le_geoCornerCount_centre hn g j hz hb hc t hs S hD hS q,
      geoCornerPolygon (flatCentreCG hn g j hz hb hc) S q⟩).Generic := by
  have hSD := del_isDecomposition hn g j hz hb hc t hs S hD hS
  have hkD := ccpCornerCount_ge_three hn (generic_deleteVertex hn hz hb hc) hSD
    (delEquiv hn g j hz hb hc t hs S hF q)
  have hgenD := carrierShadow_generic hn (generic_deleteVertex hn hz hb hc)
    (deletionSupport hn g j hz hb hc S) (delEquiv hn g j hz hb hc t hs S hF q) hSD
  by_cases hq : q = centralCarrierThroughJ hn g j hz hb hc S
  · subst hq
    obtain ⟨r, t₀, h0, h1, hoff, hre⟩ := flat_vertex_subdivision hn g j hz hb hc t hs S hF
    exact Link.single_generic_of_reindexed (Nat.le_succ_of_le hkD) _ hre
      (Link.single_generic_appendVertex hkD _ h0 h1 (Link.single_generic_shift hkD _ r hgenD) hoff)
  · exact Link.single_generic_of_reindexed hkD _
      (reindexed_del_centre_of_ne hn g j hz hb hc t hs S hF q hq) hgenD

/-- (F6e') Genericity along the whole family (`u = 0`: F6e; `u > 0`: F6b' at `s = u·t` with
`SidePathData`). -/
theorem single_generic_sideFamily (hD : FlatCarriersDefinitionData hn g j hz hb hc t hs S)
    (hF : FlatCarriersData hn g j hz hb hc t hs S)
    (hS : GeoIndependent (flatCentreCG hn g j hz hb hc) S)
    (hpath : SidePathData hn g j hz hb hc t)
    (q : GeoComponent (flatCentreCG hn g j hz hb hc) S) (b : Bool) (u : unitInterval) :
    (Shadow.single ⟨_, three_le_geoCornerCount_centre hn g j hz hb hc t hs S hD hS q,
      sideFamily hn g j hz hb hc t S q b u⟩).Generic := by
  by_cases hu : u.val = 0
  · have hu0 : u = 0 := Subtype.ext hu
    subst hu0
    rw [sideFamily_zero]
    exact single_generic_centre hn g j hz hb hc t hs S hD hF hS q
  · have hu0 : 0 < u.val := lt_of_le_of_ne u.property.1 (Ne.symm hu)
    have hle : u.val * t.val ≤ t.val := mul_le_of_le_one_left t.property.1.le u.property.2
    obtain ⟨hs', hD'⟩ := hpath ⟨u.val * t.val, mul_pos hu0 t.property.1,
      lt_of_le_of_lt hle t.property.2⟩ hle
    unfold sideFamily
    rw [famParam_pos g t b u hu0]
    exact single_generic_cornerFamily_side hn g j hz hb hc S _ hs' (hD' S hS) hS b q _

/-- (F6f) The side positive lift is planar isotopic to the positive diagram of the centre corner
polygon: re-indexing to `sideFamily 1` (L0.4 with F6b at `s = t`), then the deformation `1 → 0`
(L0.6, `PlanarIsotopic.symm`). -/
theorem planarIsotopic_side_centre (hD : FlatCarriersDefinitionData hn g j hz hb hc t hs S)
    (hF : FlatCarriersData hn g j hz hb hc t hs S)
    (hS : GeoIndependent (flatCentreCG hn g j hz hb hc) S)
    (hpath : SidePathData hn g j hz hb hc t)
    (q : GeoComponent (flatCentreCG hn g j hz hb hc) S) (b : Bool) :
    PlanarIsotopic
      (positiveLift (flat_hn1 hn) (g.sideTuple b t).property (transportSupport (hs b) S)
        (sideEquiv hn g j hz hb hc t hs S hF b q) (side_isDecomposition hn g j hz hb hc t hs S hD hS b))
      ((Shadow.single ⟨_, three_le_geoCornerCount_centre hn g j hz hb hc t hs S hD hS q,
        geoCornerPolygon (flatCentreCG hn g j hz hb hc) S q⟩).positiveDiagram
          (single_generic_centre hn g j hz hb hc t hs S hD hF hS q)) := by
  obtain ⟨a, rfl⟩ := geoOwner_surjective (flatCentreCG hn g j hz hb hc) S q
  have hk := three_le_geoCornerCount_centre hn g j hz hb hc t hs S hD hS
    (geoOwner (flatCentreCG hn g j hz hb hc) S a)
  have hgen := single_generic_sideFamily hn g j hz hb hc t hs S hD hF hS hpath
    (geoOwner (flatCentreCG hn g j hz hb hc) S a) b
  have hre : Reindexed
      (ccpCornerPolygon (flat_hn1 hn) (g.sideTuple b t).property (transportSupport (hs b) S)
        (sideEquiv hn g j hz hb hc t hs S hF b (geoOwner (flatCentreCG hn g j hz hb hc) S a)))
      (sideFamily hn g j hz hb hc t S (geoOwner (flatCentreCG hn g j hz hb hc) S a) b 1) := by
    rw [sideFamily_one]
    exact reindexed_cornerFamily_side hn g j hz hb hc S t hs hD b a
  have h1 : PlanarIsotopic
      (positiveLift (flat_hn1 hn) (g.sideTuple b t).property (transportSupport (hs b) S)
        (sideEquiv hn g j hz hb hc t hs S hF b (geoOwner (flatCentreCG hn g j hz hb hc) S a))
        (side_isDecomposition hn g j hz hb hc t hs S hD hS b))
      ((Shadow.single ⟨_, hk, sideFamily hn g j hz hb hc t S
        (geoOwner (flatCentreCG hn g j hz hb hc) S a) b 1⟩).positiveDiagram (hgen 1)) :=
    Link.planarIsotopic_positiveDiagram_single_of_reindexed
      (ccpCornerCount_ge_three (flat_hn1 hn) (g.sideTuple b t).property
        (side_isDecomposition hn g j hz hb hc t hs S hD hS b) _) hk hre
      (carrierShadow_generic (flat_hn1 hn) (g.sideTuple b t).property (transportSupport (hs b) S) _
        (side_isDecomposition hn g j hz hb hc t hs S hD hS b)) (hgen 1)
  have h2 := Link.planarIsotopic_positiveDiagram_single_family hk
    (continuous_sideFamily hn g j hz hb hc t S hpath _ b) hgen
  have h3 : (Shadow.single ⟨_, hk, sideFamily hn g j hz hb hc t S
        (geoOwner (flatCentreCG hn g j hz hb hc) S a) b 0⟩).positiveDiagram (hgen 0) =
      (Shadow.single ⟨_, hk, geoCornerPolygon (flatCentreCG hn g j hz hb hc) S
        (geoOwner (flatCentreCG hn g j hz hb hc) S a)⟩).positiveDiagram
        (single_generic_centre hn g j hz hb hc t hs S hD hF hS _) :=
    positiveDiagram_congr (by rw [sideFamily_zero]) _ _
  rw [← h3]
  exact h1.trans h2.symm

/-- (F6g) The positive diagram of the centre corner polygon is planar isotopic to the deletion
positive lift: for `q ≠ Q_*` by re-indexing (L0.4, F6c); for `Q_*` by re-indexing to the
subdivision (F6d), the subdivision `Reparam` (L0.8) and the shift (L0.2). -/
theorem planarIsotopic_centre_del (hD : FlatCarriersDefinitionData hn g j hz hb hc t hs S)
    (hF : FlatCarriersData hn g j hz hb hc t hs S)
    (hS : GeoIndependent (flatCentreCG hn g j hz hb hc) S)
    (q : GeoComponent (flatCentreCG hn g j hz hb hc) S) :
    PlanarIsotopic
      ((Shadow.single ⟨_, three_le_geoCornerCount_centre hn g j hz hb hc t hs S hD hS q,
        geoCornerPolygon (flatCentreCG hn g j hz hb hc) S q⟩).positiveDiagram
          (single_generic_centre hn g j hz hb hc t hs S hD hF hS q))
      (positiveLift hn (generic_deleteVertex hn hz hb hc) (deletionSupport hn g j hz hb hc S)
        (delEquiv hn g j hz hb hc t hs S hF q) (del_isDecomposition hn g j hz hb hc t hs S hD hS)) := by
  have hSD := del_isDecomposition hn g j hz hb hc t hs S hD hS
  have hkD := ccpCornerCount_ge_three hn (generic_deleteVertex hn hz hb hc) hSD
    (delEquiv hn g j hz hb hc t hs S hF q)
  have hgenD := carrierShadow_generic hn (generic_deleteVertex hn hz hb hc)
    (deletionSupport hn g j hz hb hc S) (delEquiv hn g j hz hb hc t hs S hF q) hSD
  by_cases hq : q = centralCarrierThroughJ hn g j hz hb hc S
  · subst hq
    obtain ⟨r, t₀, h0, h1, hoff, hre⟩ := flat_vertex_subdivision hn g j hz hb hc t hs S hF
    have hgS := Link.single_generic_shift hkD _ r hgenD
    have hgA := Link.single_generic_appendVertex hkD _ h0 h1 hgS hoff
    refine (Link.planarIsotopic_positiveDiagram_single_of_reindexed (Nat.le_succ_of_le hkD) _ hre
      hgA (single_generic_centre hn g j hz hb hc t hs S hD hF hS _)).symm.trans ?_
    refine (PlanarIsotopic.of_reparam
      (Link.reparam_positiveDiagram_single_appendVertex hkD _ h0 h1 hgS hoff hgA)).symm.trans ?_
    exact (Link.planarIsotopic_positiveDiagram_single_shift hkD _ r hgenD hgS).symm
  · exact (Link.planarIsotopic_positiveDiagram_single_of_reindexed hkD _
      (reindexed_del_centre_of_ne hn g j hz hb hc t hs S hF q hq) hgenD
      (single_generic_centre hn g j hz hb hc t hs S hD hF hS q)).symm

/-- (F6) **The HOMFLY values of corresponding positive lifts agree** (lit:homfly, `homfly_planar`). -/
theorem homfly_side_eq_del (hD : FlatCarriersDefinitionData hn g j hz hb hc t hs S)
    (hF : FlatCarriersData hn g j hz hb hc t hs S)
    (hS : GeoIndependent (flatCentreCG hn g j hz hb hc) S)
    (hpath : SidePathData hn g j hz hb hc t)
    (q : GeoComponent (flatCentreCG hn g j hz hb hc) S) (b : Bool) :
    homfly (positiveLift (flat_hn1 hn) (g.sideTuple b t).property (transportSupport (hs b) S)
        (sideEquiv hn g j hz hb hc t hs S hF b q) (side_isDecomposition hn g j hz hb hc t hs S hD hS b)) =
      homfly (positiveLift hn (generic_deleteVertex hn hz hb hc) (deletionSupport hn g j hz hb hc S)
        (delEquiv hn g j hz hb hc t hs S hF q) (del_isDecomposition hn g j hz hb hc t hs S hD hS)) :=
  homfly_planar ((planarIsotopic_side_centre hn g j hz hb hc t hs S hD hF hS hpath q b).trans
    (planarIsotopic_centre_del hn g j hz hb hc t hs S hD hF hS q))

/-! ## §3d. The three instantiations -/

/-- (I1) The coefficient product of a side equals that of the deletion (T2 twice, with the reference
data `m_Q`, `r_Q` read at the centre and `H⁺_Q` read on the deletion copy). -/
theorem cornerProduct_side_eq_del (hD : FlatCarriersDefinitionData hn g j hz hb hc t hs S)
    (hF : FlatCarriersData hn g j hz hb hc t hs S)
    (hS : GeoIndependent (flatCentreCG hn g j hz hb hc) S)
    (hpath : SidePathData hn g j hz hb hc t) (b : Bool) :
    cornerProduct (flat_hn1 hn) (g.sideTuple b t).property (transportSupport (hs b) S)
        (side_isDecomposition hn g j hz hb hc t hs S hD hS b) =
      cornerProduct hn (generic_deleteVertex hn hz hb hc) (deletionSupport hn g j hz hb hc S)
        (del_isDecomposition hn g j hz hb hc t hs S hD hS) := by
  rw [cornerProduct_eq_of_carrier_data (flat_hn1 hn) (g.sideTuple b t).property
      (side_isDecomposition hn g j hz hb hc t hs S hD hS b) (sideEquiv hn g j hz hb hc t hs S hF b)
      (fun q => (geoCarrierCrossings (flatCentreCG hn g j hz hb hc) S q).card)
      (fun q => rotationNumber (geoCornerPolygon (flatCentreCG hn g j hz hb hc) S q))
      (fun q => homfly (positiveLift hn (generic_deleteVertex hn hz hb hc)
        (deletionSupport hn g j hz hb hc S) (delEquiv hn g j hz hb hc t hs S hF q)
        (del_isDecomposition hn g j hz hb hc t hs S hD hS)))
      (carrierCrossingCount_side hn g j hz hb hc t hs S hF b)
      (carrierRotation_side hn g j hz hb hc t hs S hF b)
      (fun q => homfly_side_eq_del hn g j hz hb hc t hs S hD hF hS hpath q b),
    cornerProduct_eq_of_carrier_data hn (generic_deleteVertex hn hz hb hc)
      (del_isDecomposition hn g j hz hb hc t hs S hD hS) (delEquiv hn g j hz hb hc t hs S hF)
      (fun q => (geoCarrierCrossings (flatCentreCG hn g j hz hb hc) S q).card)
      (fun q => rotationNumber (geoCornerPolygon (flatCentreCG hn g j hz hb hc) S q))
      (fun q => homfly (positiveLift hn (generic_deleteVertex hn hz hb hc)
        (deletionSupport hn g j hz hb hc S) (delEquiv hn g j hz hb hc t hs S hF q)
        (del_isDecomposition hn g j hz hb hc t hs S hD hS)))
      (carrierCrossingCount_del hn g j hz hb hc t hs S hF)
      (carrierRotation_del hn g j hz hb hc t hs S hF) (fun _ => rfl)]

/-- (I2) The selector identity per support: `wind_R − wind_L = wind_D` (T3 three times with the
reference weights read on the deletion, `carrierWeight_side_eq_del`, `carrierWeight_central`, and the
selector algebra). -/
theorem wind_side_sub_side_eq_del (hF : FlatCarriersData hn g j hz hb hc t hs S) (bR bL : Bool)
    (hR : IsRightSide g j bR t) (hL : IsLeftSide g j bL t) :
    wind (flat_hn1 hn) (g.sideTuple bR t).property (transportSupport (hs bR) S) -
        wind (flat_hn1 hn) (g.sideTuple bL t).property (transportSupport (hs bL) S) =
      wind hn (generic_deleteVertex hn hz hb hc) (deletionSupport hn g j hz hb hc S) := by
  have hwR := wind_eq_of_weights (flat_hn1 hn) (g.sideTuple bR t).property
    (S' := transportSupport (hs bR) S) (sideEquiv hn g j hz hb hc t hs S hF bR)
    (centralCarrierThroughJ hn g j hz hb hc S)
    (fun q => carrierWeight hn (generic_deleteVertex hn hz hb hc) (deletionSupport hn g j hz hb hc S)
      (delEquiv hn g j hz hb hc t hs S hF q))
    (fun q hq => carrierWeight_side_eq_del hn g j hz hb hc t hs S hF bR q hq)
  have hwL := wind_eq_of_weights (flat_hn1 hn) (g.sideTuple bL t).property
    (S' := transportSupport (hs bL) S) (sideEquiv hn g j hz hb hc t hs S hF bL)
    (centralCarrierThroughJ hn g j hz hb hc S)
    (fun q => carrierWeight hn (generic_deleteVertex hn hz hb hc) (deletionSupport hn g j hz hb hc S)
      (delEquiv hn g j hz hb hc t hs S hF q))
    (fun q hq => carrierWeight_side_eq_del hn g j hz hb hc t hs S hF bL q hq)
  have hwD := wind_eq_of_weights hn (generic_deleteVertex hn hz hb hc)
    (S' := deletionSupport hn g j hz hb hc S) (delEquiv hn g j hz hb hc t hs S hF)
    (centralCarrierThroughJ hn g j hz hb hc S)
    (fun q => carrierWeight hn (generic_deleteVertex hn hz hb hc) (deletionSupport hn g j hz hb hc S)
      (delEquiv hn g j hz hb hc t hs S hF q))
    (fun _ _ => rfl)
  rw [hwR, hwL, hwD, ← sub_mul, carrierWeight_central hn g j hz hb hc t hs S hF bR bL hR hL]

/-! ## §4. The sums -/

/-- (F7.1) lem:C-X1 for a side, reindexed over the centre's independent supports through
`transportSupport (hs b)` (a bijection `centreSupports ≃ Ind(G_side)` by `independent_supports.1`
and `crossingTransport`; `Finset.sum_nbij` on the total-function form, the device of
`cornerStateSum_transport`). -/
theorem cornerStateSum_side_eq
    (hD : ∀ S, GeoIndependent (flatCentreCG hn g j hz hb hc) S →
      FlatCarriersDefinitionData hn g j hz hb hc t hs S) (b : Bool) :
    cornerStateSum (flat_hn1 hn) (g.sideTuple b t).property =
      ∑ S ∈ (centreSupports hn g j hz hb hc).attach,
        wind (flat_hn1 hn) (g.sideTuple b t).property (transportSupport (hs b) S.1) *
          cornerProduct (flat_hn1 hn) (g.sideTuple b t).property (transportSupport (hs b) S.1)
            (side_isDecomposition hn g j hz hb hc t hs S.1
              (hD S.1 ((mem_centreSupports hn g j hz hb hc S.1).mp S.2))
              ((mem_centreSupports hn g j hz hb hc S.1).mp S.2) b) := by
  sorry

/-- (F7.2) lem:C-X1 for the deletion, reindexed over the centre's independent supports through
`deletionSupport` (`independent_supports.2`, `fusionCrossingEquiv`). -/
theorem cornerStateSum_del_eq
    (hD : ∀ S, GeoIndependent (flatCentreCG hn g j hz hb hc) S →
      FlatCarriersDefinitionData hn g j hz hb hc t hs S) :
    cornerStateSum hn (generic_deleteVertex hn hz hb hc) =
      ∑ S ∈ (centreSupports hn g j hz hb hc).attach,
        wind hn (generic_deleteVertex hn hz hb hc) (deletionSupport hn g j hz hb hc S.1) *
          cornerProduct hn (generic_deleteVertex hn hz hb hc) (deletionSupport hn g j hz hb hc S.1)
            (del_isDecomposition hn g j hz hb hc t hs S.1
              (hD S.1 ((mem_centreSupports hn g j hz hb hc S.1).mp S.2))
              ((mem_centreSupports hn g j hz hb hc S.1).mp S.2)) := by
  sorry

/-- (F10) **The flat law at one side parameter** `t`, for a right side `bR` and a left side `bL`
at that `t`: term by term over the centre's supports, `(wind_R − wind_L) · B_S = wind_D · B_S`. -/
theorem flat_law_at
    (hD : ∀ S, GeoIndependent (flatCentreCG hn g j hz hb hc) S →
      FlatCarriersDefinitionData hn g j hz hb hc t hs S)
    (hF : ∀ S, GeoIndependent (flatCentreCG hn g j hz hb hc) S →
      FlatCarriersData hn g j hz hb hc t hs S)
    (hpath : SidePathData hn g j hz hb hc t) (bR bL : Bool)
    (hR : IsRightSide g j bR t) (hL : IsLeftSide g j bL t) :
    cornerStateSum (flat_hn1 hn) (g.sideTuple bR t).property -
        cornerStateSum (flat_hn1 hn) (g.sideTuple bL t).property =
      cornerStateSum hn (generic_deleteVertex hn hz hb hc) := by
  rw [cornerStateSum_side_eq hn g j hz hb hc t hs hD bR, cornerStateSum_side_eq hn g j hz hb hc t hs hD bL,
    cornerStateSum_del_eq hn g j hz hb hc t hs hD, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun S _ => ?_
  have hS := (mem_centreSupports hn g j hz hb hc S.1).mp S.2
  rw [cornerProduct_side_eq_del hn g j hz hb hc t hs S.1 (hD S.1 hS) (hF S.1 hS) hS hpath bR,
    cornerProduct_side_eq_del hn g j hz hb hc t hs S.1 (hD S.1 hS) (hF S.1 hS) hS hpath bL,
    ← sub_mul, wind_side_sub_side_eq_del hn g j hz hb hc t hs S.1 (hF S.1 hS) bR bL hR hL]

end Flat

/-! ## §4b. Chamber constancy along one side (prop:C-chamber) -/

section SideChamber

variable {n : ℕ} [NeZero n] (g : WallGerm (n + 1))

instance : PreconnectedSpace g.SideParameter := Subtype.preconnectedSpace isPreconnected_Ioo

/-- Turn signs are constant along a side (`Carrier.generic_family_turn_constant` for the continuous
family `g.sideTuple b` on the connected `SideParameter`). -/
theorem turn_sideTuple_eq (b : Bool) (t t' : g.SideParameter) (i : ZMod (n + 1)) :
    turn (g.sideTuple b t).val i = turn (g.sideTuple b t').val i :=
  Carrier.generic_family_turn_constant (g.continuous_sideTuple b) t t' i

/-- Two polygons of one side lie in one labelled chamber (the connected image of `SideParameter`
under `g.sideTuple b` lies in the connected component, `IsPreconnected.subset_connectedComponent`). -/
theorem sideTuple_mem_labelledChamber (b : Bool) (t t' : g.SideParameter) :
    g.sideTuple b t' ∈ labelledChamber (g.sideTuple b t) :=
  (isPreconnected_range (g.continuous_sideTuple b)).subset_connectedComponent ⟨t, rfl⟩ ⟨t', rfl⟩

/-- (F11) prop:C-chamber along a side: `C` does not depend on the side parameter
(`cornerStateSum_eq_of_mem_labelledChamber`). -/
theorem cornerStateSum_sideTuple_eq (hn : 3 ≤ n) (b : Bool) (t t' : g.SideParameter) :
    cornerStateSum (flat_hn1 hn) (g.sideTuple b t).property =
      cornerStateSum (flat_hn1 hn) (g.sideTuple b t').property :=
  cornerStateSum_eq_of_mem_labelledChamber (flat_hn1 hn) (sideTuple_mem_labelledChamber g b t t')

end SideChamber

end

/-! ## §5. thm:C-S3 -/

/-- thm:C-S3 as printed (statement of work/drafts/CS3_statement.lean). -/
structure CS3Data : Prop where
  /-- eq. ccf:flat-law: `C(P_right) − C(P_left) = C(P(0) ∖ j)` at a simple flat wall, for the polygons of the two
  sides at all sufficiently small side parameters. -/
  flat_law : ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (g : WallGerm (n + 1)) (j : ZMod (n + 1))
    (hz : g.pointZeros = {turnSupport j})
    (hb : StrictBetween (g.center (j - 1)) (g.center j) (g.center (j + 1)))
    (hc : g.concurrences = ∅) (_hsc : g.SignChanges (fun P => (turn P j : ℝ))),
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ g.radius ∧
      ∀ (bR bL : Bool) (tR tL : g.SideParameter), tR.val < δ → tL.val < δ →
        IsRightSide g j bR tR → IsLeftSide g j bL tL →
        cornerStateSum (flat_hn1 hn) (g.sideTuple bR tR).property -
            cornerStateSum (flat_hn1 hn) (g.sideTuple bL tL).property =
          cornerStateSum hn (generic_deleteVertex hn hz hb hc)

/-- **thm:C-S3.** The radius is the smaller of the radii of `flat_carriers_definition` and
`flat_carriers`; the two side parameters are brought to the common parameter `t = tR` by chamber
constancy along the left side (`cornerStateSum_sideTuple_eq`) and turn constancy
(`turn_sideTuple_eq`, so `bL` is still the left side at `tR`); then `flat_law_at`. -/
theorem thm_C_S3 : CS3Data where
  flat_law := by
    intro n _ hn g j hz hb hc hsc
    obtain ⟨δ₁, hδ₁, hδ₁r, hdef⟩ := flat_carriers_definition hn g hz hb hc hsc
    obtain ⟨δ₂, hδ₂, -, hcor⟩ := flat_carriers hn g hz hb hc hsc
    refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, (min_le_left _ _).trans hδ₁r, ?_⟩
    intro bR bL tR tL htR htL hR hL
    have htR1 : tR.val < δ₁ := lt_of_lt_of_le htR (min_le_left _ _)
    have htR2 : tR.val < δ₂ := lt_of_lt_of_le htR (min_le_right _ _)
    obtain ⟨hs, hF⟩ := hcor tR htR2
    have hD : ∀ S, GeoIndependent (flatCentreCG hn g j hz hb hc) S →
        FlatCarriersDefinitionData hn g j hz hb hc tR hs S := by
      intro S hS
      obtain ⟨_, hD'⟩ := hdef tR htR1
      exact hD' S hS
    have hpath : SidePathData hn g j hz hb hc tR := fun s hst =>
      hdef s (lt_of_le_of_lt hst htR1)
    have hL' : IsLeftSide g j bL tR := by
      unfold IsLeftSide at hL ⊢
      rw [turn_sideTuple_eq g bL tR tL]
      exact hL
    rw [cornerStateSum_sideTuple_eq g hn bL tL tR]
    exact flat_law_at hn g j hz hb hc tR hs hD hF hpath bR bL hR hL'

end SM
