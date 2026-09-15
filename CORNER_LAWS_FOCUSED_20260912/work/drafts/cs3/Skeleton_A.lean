import SM.FlatCarriers
import SM.CX1
import SM.CChamber
import SM.GermSides

/-! # thm:C-S3 (the flat law) — SKELETON A

Target: `SM.thm_C_S3 : CS3Data` (work/drafts/CS3_statement.lean, copied verbatim at the end).
Source: reference/SM/sm-4-knotlaws.tex:153-229. Plan: work/drafts/cs3/PLAN_A.md.

Every lemma of the chain is STATED (the open ones with `sorry`) and `thm_C_S3` is PROVED from the
chain; the bookkeeping lemmas are proved outright. Route (plan §1): reduce to one side parameter
`t` (chamber constancy along a side, accepted `GermSides` + `prop_C_chamber`); rewrite `C` through
lem:C-X1 as `Σ_S wind(S) ∏ c(Q)`; reindex the three sums over the centre's supports; for each
independent `S`, carriers correspond through `sideCarrierEquiv` / `deletionCarrierEquiv` (fields
`correspond_sides`, `correspond_deletion` of the accepted `FlatCarriersData`); the coefficients
agree because the slots agree (`same_retained_crossings`, `same_rotation`) and the positive lifts
are planar-isotopic to the positive diagram of the centre corner polygon — a `Deform` along the
accepted `cornerFamily` through the flat centre (side) and a `Reparam` (flat subdivision at
`μ_j`) or a cyclic re-indexing (deletion); the selector identity closes the sum
(`selector_identity`, `other_selectors_agree`). -/

namespace SM

open Link Carrier GeoCarrier

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## A. Link-layer lemmas on one-component shadows (new, general) -/

section LinkLayer

/-- `Reindexed` is transitive (compose the two shifts through `ℕ`-casts). -/
theorem Reindexed.trans {m₁ m₂ m₃ : ℕ} [NeZero m₁] [NeZero m₂] [NeZero m₃]
    {Q₁ : LabelledTuple m₁} {Q₂ : LabelledTuple m₂} {Q₃ : LabelledTuple m₃}
    (h₁ : Reindexed Q₁ Q₂) (h₂ : Reindexed Q₂ Q₃) : Reindexed Q₁ Q₃ := by
  obtain ⟨hm, r, hr⟩ := h₁
  obtain ⟨hm', r', hr'⟩ := h₂
  subst hm hm'
  refine ⟨rfl, r' + r, fun k => ?_⟩
  rw [hr' k, hr]
  congr 1
  push_cast
  rw [ZMod.natCast_zmod_val, add_assoc]

/-- `Reindexed` is symmetric (shift back by `(-r).val`). -/
theorem Reindexed.symm {m₁ m₂ : ℕ} [NeZero m₁] [NeZero m₂]
    {Q₁ : LabelledTuple m₁} {Q₂ : LabelledTuple m₂} (h : Reindexed Q₁ Q₂) : Reindexed Q₂ Q₁ := by
  obtain ⟨hm, r, hr⟩ := h
  subst hm
  refine ⟨rfl, (-(r : ZMod m₁)).val, fun k => ?_⟩
  rw [hr]
  congr 1
  rw [Nat.cast_add, Nat.cast_add, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val,
    ZMod.natCast_zmod_val]
  ring

/-- A recast is a re-indexing without shift. -/
theorem reindexed_recastTuple {k k' : ℕ} [NeZero k] [NeZero k'] (hk : k' = k)
    (f : LabelledTuple k) : Reindexed f (recastTuple hk f) := by
  subst hk
  exact reindexed_refl f

theorem edgeSegment_recastTuple {k k' : ℕ} (hk : k' = k) (f : LabelledTuple k) (e : ZMod k') :
    edgeSegment (recastTuple hk f) e = edgeSegment f (Equiv.cast (congrArg ZMod hk) e) := by
  subst hk; rfl

theorem getElem_congr_lists {α : Type*} (L L' : List α) (h : L = L') (i i' : ℕ)
    (hi : i < L.length) (hi' : i' < L'.length) (hii : i = i') : L[i]'hi = L'[i']'hi' := by
  subst h; subst hii; rfl

namespace Link

/-- A cyclic shift of the labels keeps a one-component shadow generic
(`StrandMap.generic_pullback` along the accepted `shiftStrandMap`). -/
theorem single_generic_shift {k : ℕ} (hk : 3 ≤ k) (X : LabelledTuple k) (r : ZMod k)
    (h : (Shadow.single ⟨k, hk, X⟩).Generic) : (Shadow.single ⟨k, hk, shift r X⟩).Generic := by
  have : NeZero k := ⟨by omega⟩
  exact StrandMap.generic_pullback (shiftStrandMap ⟨k, hk, X⟩ r) h
    (fun _ => (regular_shift r X).mpr (h.regular 0))

/-- Genericity of a one-component shadow is invariant under re-indexing. -/
theorem single_generic_of_reindexed {m m' : ℕ} [NeZero m] [NeZero m'] {X : LabelledTuple m}
    {Y : LabelledTuple m'} (h : Reindexed X Y) (hm : 3 ≤ m) (hm' : 3 ≤ m')
    (hX : (Shadow.single ⟨m, hm, X⟩).Generic) : (Shadow.single ⟨m', hm', Y⟩).Generic := by
  obtain ⟨hmm, -⟩ := id h
  subst hmm
  obtain ⟨r, rfl⟩ := reindexed_eq_shift h
  exact single_generic_shift hm X r hX

/-- Re-indexed one-component positive diagrams have the same HOMFLY polynomial
(`reparam_positiveDiagram_single_shift`, `homfly_planar`). -/
theorem homfly_positiveDiagram_single_of_reindexed {m m' : ℕ} [NeZero m] [NeZero m']
    {X : LabelledTuple m} {Y : LabelledTuple m'} (h : Reindexed X Y) (hm : 3 ≤ m) (hm' : 3 ≤ m')
    (hX : (Shadow.single ⟨m, hm, X⟩).Generic) (hY : (Shadow.single ⟨m', hm', Y⟩).Generic) :
    homfly ((Shadow.single ⟨m, hm, X⟩).positiveDiagram hX) =
      homfly ((Shadow.single ⟨m', hm', Y⟩).positiveDiagram hY) := by
  obtain ⟨hmm, -⟩ := id h
  subst hmm
  obtain ⟨r, rfl⟩ := reindexed_eq_shift h
  exact homfly_planar (PlanarIsotopic.of_reparam
    (reparam_positiveDiagram_single_shift ⟨m, hm, X⟩ r hX hY))

/-- **Deform along a continuous family of generic one-component shadows** (the general form of
`deform_positiveLift_path`): the crossing pairs are constant (`crossing_support_persists_of_geometry`
+ `crossingGeometry_of_single_generic`, locally constant on the connected `unitInterval`),
`Deform.of_family`, positivity persists (`isPositive_deform_of_family`), and the deformed diagram
is the positive diagram (`eq_positiveDiagram_of_isPositive`). -/
theorem deform_positiveDiagram_single_of_family {k : ℕ} (hk : 3 ≤ k)
    (Φ : unitInterval → LabelledTuple k) (hΦ : Continuous Φ)
    (hgen : ∀ u, (Shadow.single ⟨k, hk, Φ u⟩).Generic) :
    Deform ((Shadow.single ⟨k, hk, Φ 0⟩).positiveDiagram (hgen 0))
      ((Shadow.single ⟨k, hk, Φ 1⟩).positiveDiagram (hgen 1)) := by
  have : NeZero k := ⟨by omega⟩
  let D : Diagram := (Shadow.single ⟨k, hk, Φ 0⟩).positiveDiagram (hgen 0)
  let V : unitInterval → D.Γ.Vertices := fun u _ => Φ u
  have hV : ∀ (i : Fin D.Γ.c) (j : ZMod (D.Γ.comp i).k), Continuous fun u => V u i j :=
    fun _ j => (continuous_apply j).comp hΦ
  have hgen' : ∀ u, (D.Γ.withVertices (V u)).Generic := fun u => hgen u
  have hcross : ∀ u (x : Finset D.Γ.Strand),
      (D.Γ.withVertices (V u)).IsCrossing x ↔ D.Γ.IsCrossing x := by
    intro u x
    have hg : IsLocallyConstant fun u : unitInterval => {s : Finset (ZMod k) | IsCrossing (Φ u) s} := by
      rw [IsLocallyConstant.iff_eventually_eq]
      intro u₀
      have hev := crossing_support_persists_of_geometry
        (crossingGeometry_of_single_generic hk (hgen u₀))
      filter_upwards [hΦ.continuousAt.eventually hev] with u' hu'
      exact Set.ext hu'
    have hconst := Set.ext_iff.mp (IsLocallyConstant.apply_eq_of_preconnectedSpace hg u 0)
    exact single_isCrossing_iff_of_forall hk (fun s => hconst s) x
  have h0 : V 0 = D.Γ.vertices := rfl
  have hd : Deform D (D.deform (V 1) (hgen' 1) (hcross 1)) := Deform.of_family D hV hgen' hcross h0
  have heq : D.deform (V 1) (hgen' 1) (hcross 1) =
      (Shadow.single ⟨k, hk, Φ 1⟩).positiveDiagram (hgen 1) :=
    Shadow.eq_positiveDiagram_of_isPositive _ (hgen 1) _ rfl
      (D.isPositive_deform_of_family hV hgen' hcross h0
        (fun x => Shadow.positiveDiagram_isPositive _ _ x))
  rw [← heq]
  exact hd

theorem homfly_positiveDiagram_single_of_family {k : ℕ} (hk : 3 ≤ k)
    (Φ : unitInterval → LabelledTuple k) (hΦ : Continuous Φ)
    (hgen : ∀ u, (Shadow.single ⟨k, hk, Φ u⟩).Generic) :
    homfly ((Shadow.single ⟨k, hk, Φ 0⟩).positiveDiagram (hgen 0)) =
      homfly ((Shadow.single ⟨k, hk, Φ 1⟩).positiveDiagram (hgen 1)) :=
  homfly_planar (PlanarIsotopic.of_deform (deform_positiveDiagram_single_of_family hk Φ hΦ hgen))

/-- **Flat subdivision keeps genericity.** Appending the vertex `edgePoint X (-1) u`, `0 < u < 1`, on
the closing edge of a generic one-component shadow keeps it generic provided the new vertex lies on
no other closed edge (regularity: `regular_appendVertex`; the two half-edges have the direction of
the old closing edge, `edge_appendVertex_last/new`; a point interior to a half-edge is interior to
the old edge). -/
theorem single_generic_appendVertex {m : ℕ} [NeZero m] (hm : 3 ≤ m) (X : LabelledTuple m)
    {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) (hX : (Shadow.single ⟨m, hm, X⟩).Generic)
    (hnew : ∀ e : ZMod m, e ≠ -1 → edgePoint X (-1) u ∉ edgeSegment X e) :
    (Shadow.single ⟨m + 1, Nat.le_succ_of_le hm, appendVertex X u⟩).Generic := by
  sorry

/-- **The flat subdivision is a reparametrization** (`ReparamData`: `e = id`, `φ` the monotone
re-parametrization of the circle sending the closing edge `[0,1)` of `X` to the two half-edges
`[0,u) ∪ [u,1)`, order-preserving, tracing the same points; crossings correspond through their
crossing points since both diagrams are positive). -/
theorem reparam_positiveDiagram_single_appendVertex {m : ℕ} [NeZero m] (hm : 3 ≤ m)
    (X : LabelledTuple m) {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1)
    (hX : (Shadow.single ⟨m, hm, X⟩).Generic)
    (hX' : (Shadow.single ⟨m + 1, Nat.le_succ_of_le hm, appendVertex X u⟩).Generic) :
    Reparam ((Shadow.single ⟨m, hm, X⟩).positiveDiagram hX)
      ((Shadow.single ⟨m + 1, Nat.le_succ_of_le hm, appendVertex X u⟩).positiveDiagram hX') := by
  sorry

theorem homfly_positiveDiagram_single_appendVertex {m : ℕ} [NeZero m] (hm : 3 ≤ m)
    (X : LabelledTuple m) {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1)
    (hX : (Shadow.single ⟨m, hm, X⟩).Generic)
    (hX' : (Shadow.single ⟨m + 1, Nat.le_succ_of_le hm, appendVertex X u⟩).Generic) :
    homfly ((Shadow.single ⟨m, hm, X⟩).positiveDiagram hX) =
      homfly ((Shadow.single ⟨m + 1, Nat.le_succ_of_le hm, appendVertex X u⟩).positiveDiagram hX') :=
  homfly_planar (PlanarIsotopic.of_reparam
    (reparam_positiveDiagram_single_appendVertex hm X hu0 hu1 hX hX'))

end Link

/-- The list form of the flat-vertex erasure (the structure of the accepted
`rotationNumber_erase_flat`, exported): the polygon of `L` is, up to re-indexing, the polygon of
`L'` (read back on `L'.length` vertices) with one vertex appended at the parameter `u ∈ (0,1)` of
its closing edge, that vertex being the point `f x`. -/
theorem exists_appendVertex_of_erase_flat {α β : Type*} [BEq α] [LawfulBEq α]
    (f : α → Plane) (L : List α) [NeZero L.length] (hnd : L.Nodup) {x : α} (hx : x ∈ L)
    (hflat : ∀ k : ZMod L.length, L[k.val]'(ZMod.val_lt k) = x →
      ∃ s : ℝ, 0 < s ∧ edge (markPolygon f L) k = s • edge (markPolygon f L) (k - 1))
    (g : α → β) (f' : β → Plane) (hf' : ∀ a ∈ L, a ≠ x → f' (g a) = f a)
    (L' : List β) [NeZero L'.length] (hL' : (L.erase x).map g ~r L') :
    ∃ (Q : LabelledTuple L'.length) (u : ℝ), 0 < u ∧ u < 1 ∧
      Reindexed (markPolygon f' L') Q ∧ Reindexed (appendVertex Q u) (markPolygon f L) ∧
      edgePoint Q (-1) u = f x := by
  sorry

end LinkLayer

/-! ## B. On a generic polygon the geo data are the accepted data (recast) -/

section GenericIdentification

variable {n : ℕ} [NeZero n] (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
  (S : Finset (Crossing P))

theorem geoCornerCount_eq_generic (q : GeoComponent (generic_crossingGeometry hn hP) S) :
    geoCornerCount (generic_crossingGeometry hn hP) S q =
      ccpCornerCount hn hP S (geoComponentEquivGeneric hn hP S q) := by
  unfold geoCornerCount ccpCornerCount
  rw [geoComponentCornerList_eq_generic]

/-- The geo corner polygon is the accepted one, recast along the equal corner counts. -/
theorem geoCornerPolygon_eq_generic (q : GeoComponent (generic_crossingGeometry hn hP) S) :
    geoCornerPolygon (generic_crossingGeometry hn hP) S q =
      recastTuple (geoCornerCount_eq_generic hn hP S q)
        (ccpCornerPolygon hn hP S (geoComponentEquivGeneric hn hP S q)) := by
  funext k
  unfold geoCornerPolygon recastTuple
  rw [ccpCornerPolygon_apply, geoMarkPosition_eq_generic hn hP]
  congr 2
  exact getElem_congr_lists _ _ (geoComponentCornerList_eq_generic hn hP S q) _ _ _ _
    (zmod_val_cast (geoCornerCount_eq_generic hn hP S q) k).symm

theorem geoCornerCount_ge_three_generic {S : Finset (Crossing P)} (hS : IsDecomposition hn hP S)
    (q : GeoComponent (generic_crossingGeometry hn hP) S) :
    3 ≤ geoCornerCount (generic_crossingGeometry hn hP) S q := by
  rw [geoCornerCount_eq_generic]
  exact ccpCornerCount_ge_three hn hP hS _

/-- The carrier shadow of the accepted carrier is the one-component shadow of the geo corner
polygon (`polyComp_recastTuple`). -/
theorem carrierShadow_eq_single_geo {S : Finset (Crossing P)} (hS : IsDecomposition hn hP S)
    (q : GeoComponent (generic_crossingGeometry hn hP) S) :
    carrierShadow hn hP S (geoComponentEquivGeneric hn hP S q) hS =
      Shadow.single ⟨geoCornerCount (generic_crossingGeometry hn hP) S q,
        geoCornerCount_ge_three_generic hn hP hS q,
        geoCornerPolygon (generic_crossingGeometry hn hP) S q⟩ := by
  unfold carrierShadow carrierPolyComp
  rw [geoCornerPolygon_eq_generic hn hP]
  exact congrArg Shadow.single (polyComp_recastTuple _ _ _ _).symm

theorem single_geo_generic {S : Finset (Crossing P)} (hS : IsDecomposition hn hP S)
    (q : GeoComponent (generic_crossingGeometry hn hP) S) :
    (Shadow.single ⟨geoCornerCount (generic_crossingGeometry hn hP) S q,
      geoCornerCount_ge_three_generic hn hP hS q,
      geoCornerPolygon (generic_crossingGeometry hn hP) S q⟩).Generic := by
  rw [← carrierShadow_eq_single_geo hn hP hS q]
  exact carrierShadow_generic hn hP S _ hS

/-- The positive lift of the accepted carrier is the positive diagram of the geo corner polygon. -/
theorem positiveLift_eq_geo {S : Finset (Crossing P)} (hS : IsDecomposition hn hP S)
    (q : GeoComponent (generic_crossingGeometry hn hP) S) :
    positiveLift hn hP S (geoComponentEquivGeneric hn hP S q) hS =
      (Shadow.single ⟨geoCornerCount (generic_crossingGeometry hn hP) S q,
        geoCornerCount_ge_three_generic hn hP hS q,
        geoCornerPolygon (generic_crossingGeometry hn hP) S q⟩).positiveDiagram
        (single_geo_generic hn hP hS q) := by
  unfold positiveLift
  exact positiveDiagram_congr (carrierShadow_eq_single_geo hn hP hS q) _ _

theorem cornerSelector_recastTuple {k k' : ℕ} [NeZero k] [NeZero k'] (hk : k' = k)
    (f : LabelledTuple k) : cornerSelector (recastTuple hk f) = cornerSelector f := by
  subst hk; rfl

/-- The selector weight of lem:C-X1 is the selector of the corner polygon. -/
theorem carrierWeight_eq_cornerSelector (q : Component hn hP S) :
    carrierWeight hn hP S q = cornerSelector (ccpCornerPolygon hn hP S q) := by
  unfold carrierWeight cornerSelector
  split_ifs <;> rfl

/-- The selector weight of lem:C-X1 is the selector of cor:flat-carriers (iii). -/
theorem carrierWeight_eq_geoCarrierSelector (q : GeoComponent (generic_crossingGeometry hn hP) S) :
    carrierWeight hn hP S (geoComponentEquivGeneric hn hP S q) =
      geoCarrierSelector (generic_crossingGeometry hn hP) S q := by
  rw [geoCarrierSelector_eq_cornerSelector, geoCornerPolygon_eq_generic hn hP,
    cornerSelector_recastTuple, carrierWeight_eq_cornerSelector]

theorem wind_eq_prod_geoCarrierSelector :
    wind hn hP S = ∏ q : GeoComponent (generic_crossingGeometry hn hP) S,
      geoCarrierSelector (generic_crossingGeometry hn hP) S q := by
  unfold wind
  exact (Fintype.prod_equiv (geoComponentEquivGeneric hn hP S) _ _
    fun q => (carrierWeight_eq_geoCarrierSelector hn hP S q).symm).symm

theorem carrierCrossings_eq_geo (q : GeoComponent (generic_crossingGeometry hn hP) S) :
    carrierCrossings hn hP S (geoComponentEquivGeneric hn hP S q) =
      geoCarrierCrossings (generic_crossingGeometry hn hP) S q := by
  ext x
  rw [mem_carrierCrossings]
  simp only [geoCarrierCrossings, Finset.mem_filter, Finset.mem_univ, true_and]
  refine and_congr Iff.rfl (forall_congr' fun v => forall_congr' fun _ => ?_)
  rw [← geoComponentEquivGeneric_owner]
  exact (geoComponentEquivGeneric hn hP S).injective.eq_iff

theorem carrierCrossingCount_eq_geo (q : GeoComponent (generic_crossingGeometry hn hP) S) :
    carrierCrossingCount hn hP S (geoComponentEquivGeneric hn hP S q) =
      (geoCarrierCrossings (generic_crossingGeometry hn hP) S q).card := by
  rw [carrierCrossingCount_eq_card, carrierCrossings_eq_geo]

theorem carrierRotation_eq_geo (q : GeoComponent (generic_crossingGeometry hn hP) S) :
    carrierRotation hn hP S (geoComponentEquivGeneric hn hP S q) =
      rotationNumber (geoCornerPolygon (generic_crossingGeometry hn hP) S q) := by
  unfold carrierRotation
  rw [geoCornerPolygon_eq_generic, rotationNumber_recastTuple]

/-- `c(Q)` read on the geo data of the carrier. -/
theorem cornerCoefficient_eq_geo {S : Finset (Crossing P)} (hS : IsDecomposition hn hP S)
    (q : GeoComponent (generic_crossingGeometry hn hP) S) :
    cornerCoefficient hn hP S (geoComponentEquivGeneric hn hP S q) hS =
      coeffAt (1 - ((geoCarrierCrossings (generic_crossingGeometry hn hP) S q).card : ℤ) -
          |round (rotationNumber (geoCornerPolygon (generic_crossingGeometry hn hP) S q))|) 0
        (homfly ((Shadow.single ⟨geoCornerCount (generic_crossingGeometry hn hP) S q,
          geoCornerCount_ge_three_generic hn hP hS q,
          geoCornerPolygon (generic_crossingGeometry hn hP) S q⟩).positiveDiagram
          (single_geo_generic hn hP hS q))) := by
  rw [cornerCoefficient_eq_coeffAt]
  unfold cornerHomfly cornerSlot carrierRotationInt
  rw [carrierCrossingCount_eq_geo, carrierRotation_eq_geo, positiveLift_eq_geo]

end GenericIdentification

/-! ## C. The carrier bijections at one side parameter -/

section Carriers

variable {n : ℕ} [NeZero n] (hn : 3 ≤ n) (g : WallGerm (n + 1)) (j : ZMod (n + 1))
  (hz : g.pointZeros = {turnSupport j})
  (hb : StrictBetween (g.center (j - 1)) (g.center j) (g.center (j + 1)))
  (hc : g.concurrences = ∅) (t : g.SideParameter) (hs : CommonSupports g t)
  (S : Finset (Crossing g.center))

/-- Centre carriers ↔ side carriers (field `correspond_sides`): the carrier of `a` goes to the
carrier of `markTransport (hs b) a`. -/
def sideCarrierEquiv (hF : FlatCarriersData hn g j hz hb hc t hs S) (b : Bool) :
    GeoComponent (flatCentreCG hn g j hz hb hc) S ≃
      GeoComponent (flatSideCG hn g b t) (transportSupport (hs b) S) :=
  Quotient.congr (markTransport (hs b)) fun a a' => by
    have h := (hF.correspond_sides b).2 a a'
    rw [geoOwner_eq_iff, geoOwner_eq_iff] at h
    exact h

theorem sideCarrierEquiv_owner (hF : FlatCarriersData hn g j hz hb hc t hs S) (b : Bool)
    (a : Mark g.center) :
    sideCarrierEquiv hn g j hz hb hc t hs S hF b (geoOwner (flatCentreCG hn g j hz hb hc) S a) =
      geoOwner (flatSideCG hn g b t) (transportSupport (hs b) S) (markTransport (hs b) a) := rfl

theorem sideCarrierEquiv_central (hF : FlatCarriersData hn g j hz hb hc t hs S) (b : Bool) :
    sideCarrierEquiv hn g j hz hb hc t hs S hF b (centralCarrierThroughJ hn g j hz hb hc S) =
      geoOwner (flatSideCG hn g b t) (transportSupport (hs b) S) (Sum.inl j) := rfl

/-- The centre copy of a deletion carrier (field `correspond_deletion`): the carrier of `b` goes
to the carrier of `fusionMark b`; a bijection by `correspond_deletion.2`. -/
def deletionCarrierEquiv (hF : FlatCarriersData hn g j hz hb hc t hs S) :
    GeoComponent (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S) ≃
      GeoComponent (flatCentreCG hn g j hz hb hc) S :=
  Equiv.ofBijective
    (Quotient.lift (fun b => geoOwner (flatCentreCG hn g j hz hb hc) S (fusionMark hn g j hz hb hc b))
      fun b b' hbb' => (hF.correspond_deletion.2.1 b b').mp (Quotient.sound hbb'))
    (by
      constructor
      · intro x y hxy
        induction x using Quotient.inductionOn with
        | h b =>
          induction y using Quotient.inductionOn with
          | h b' => exact (hF.correspond_deletion.2.1 b b').mpr hxy
      · intro q
        obtain ⟨b, hb⟩ := hF.correspond_deletion.2.2 q
        exact ⟨Quotient.mk _ b, hb⟩)

theorem deletionCarrierEquiv_owner (hF : FlatCarriersData hn g j hz hb hc t hs S)
    (b : Mark (deleteVertex g.center j)) :
    deletionCarrierEquiv hn g j hz hb hc t hs S hF
        (geoOwner (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S) b) =
      geoOwner (flatCentreCG hn g j hz hb hc) S (fusionMark hn g j hz hb hc b) := rfl

/-- The deletion copy of the carrier through `μ_j` is `deletionCopyThroughJ`
(`fusionMark_delMark` with `central_vs_deletion_through_mu_j.1`, `geoOwner_successor`). -/
theorem deletionCarrierEquiv_deletionCopy (hF : FlatCarriersData hn g j hz hb hc t hs S) :
    deletionCarrierEquiv hn g j hz hb hc t hs S hF (deletionCopyThroughJ hn g j hz hb hc S) =
      centralCarrierThroughJ hn g j hz hb hc S := by
  show deletionCarrierEquiv hn g j hz hb hc t hs S hF
      (geoOwner (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S)
        (delMark hn g j hz hb hc
          (geoSmoothingSuccessor (flatCentreCG hn g j hz hb hc) S (Sum.inl j)))) =
    geoOwner (flatCentreCG hn g j hz hb hc) S (Sum.inl j)
  rw [deletionCarrierEquiv_owner,
    fusionMark_delMark hn g j hz hb hc _ hF.central_vs_deletion_through_mu_j.1, geoOwner_successor]

theorem deletionCarrierEquiv_symm_central (hF : FlatCarriersData hn g j hz hb hc t hs S) :
    (deletionCarrierEquiv hn g j hz hb hc t hs S hF).symm (centralCarrierThroughJ hn g j hz hb hc S) =
      deletionCopyThroughJ hn g j hz hb hc S := by
  rw [Equiv.symm_apply_eq]
  exact (deletionCarrierEquiv_deletionCopy hn g j hz hb hc t hs S hF).symm

/-! ### Slots: retained crossings and rotations agree (cor (ii)) -/

theorem card_geoCarrierCrossings_side (hF : FlatCarriersData hn g j hz hb hc t hs S) (b : Bool)
    (q : GeoComponent (flatCentreCG hn g j hz hb hc) S) :
    (geoCarrierCrossings (flatSideCG hn g b t) (transportSupport (hs b) S)
        (sideCarrierEquiv hn g j hz hb hc t hs S hF b q)).card =
      (geoCarrierCrossings (flatCentreCG hn g j hz hb hc) S q).card := by
  obtain ⟨a, rfl⟩ := geoOwner_surjective (flatCentreCG hn g j hz hb hc) S q
  rw [sideCarrierEquiv_owner]
  have h : geoCarrierCrossings (flatSideCG hn g b t) (transportSupport (hs b) S)
      (geoOwner (flatSideCG hn g b t) (transportSupport (hs b) S) (markTransport (hs b) a)) =
      (geoCarrierCrossings (flatCentreCG hn g j hz hb hc) S
        (geoOwner (flatCentreCG hn g j hz hb hc) S a)).map (crossingTransport (hs b)).toEmbedding := by
    ext x'
    obtain ⟨x, rfl⟩ := (crossingTransport (hs b)).surjective x'
    rw [Finset.mem_map_equiv, Equiv.symm_apply_apply]
    exact (hF.same_retained_crossings.1 b a x).symm
  rw [h, Finset.card_map]

theorem card_geoCarrierCrossings_deletion (hF : FlatCarriersData hn g j hz hb hc t hs S)
    (q : GeoComponent (flatCentreCG hn g j hz hb hc) S) :
    (geoCarrierCrossings (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S)
        ((deletionCarrierEquiv hn g j hz hb hc t hs S hF).symm q)).card =
      (geoCarrierCrossings (flatCentreCG hn g j hz hb hc) S q).card := by
  obtain ⟨q', rfl⟩ := (deletionCarrierEquiv hn g j hz hb hc t hs S hF).surjective q
  obtain ⟨b, rfl⟩ := geoOwner_surjective (flatDeletionCG hn g j hz hb hc) _ q'
  rw [Equiv.symm_apply_apply, deletionCarrierEquiv_owner]
  have h : geoCarrierCrossings (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S)
      (geoOwner (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S) b) =
      (geoCarrierCrossings (flatCentreCG hn g j hz hb hc) S
        (geoOwner (flatCentreCG hn g j hz hb hc) S (fusionMark hn g j hz hb hc b))).map
          (fusionCrossingEquiv hn hz hb hc).toEmbedding := by
    ext x'
    obtain ⟨x, rfl⟩ := (fusionCrossingEquiv hn hz hb hc).surjective x'
    rw [Finset.mem_map_equiv, Equiv.symm_apply_apply]
    exact (hF.same_retained_crossings.2 b x).symm
  rw [h, Finset.card_map]

theorem rotationNumber_side (hF : FlatCarriersData hn g j hz hb hc t hs S) (b : Bool)
    (q : GeoComponent (flatCentreCG hn g j hz hb hc) S) :
    rotationNumber (geoCornerPolygon (flatSideCG hn g b t) (transportSupport (hs b) S)
        (sideCarrierEquiv hn g j hz hb hc t hs S hF b q)) =
      rotationNumber (geoCornerPolygon (flatCentreCG hn g j hz hb hc) S q) := by
  obtain ⟨a, rfl⟩ := geoOwner_surjective (flatCentreCG hn g j hz hb hc) S q
  exact (hF.same_rotation.1 b a).1

theorem rotationNumber_deletion (hF : FlatCarriersData hn g j hz hb hc t hs S)
    (q : GeoComponent (flatCentreCG hn g j hz hb hc) S) :
    rotationNumber (geoCornerPolygon (flatDeletionCG hn g j hz hb hc)
        (deletionSupport hn g j hz hb hc S) ((deletionCarrierEquiv hn g j hz hb hc t hs S hF).symm q)) =
      rotationNumber (geoCornerPolygon (flatCentreCG hn g j hz hb hc) S q) := by
  obtain ⟨q', rfl⟩ := (deletionCarrierEquiv hn g j hz hb hc t hs S hF).surjective q
  obtain ⟨b, rfl⟩ := geoOwner_surjective (flatDeletionCG hn g j hz hb hc) _ q'
  rw [Equiv.symm_apply_apply, deletionCarrierEquiv_owner]
  exact (hF.same_rotation.2 b).1

end Carriers

/-! ## D. The centre corner polygons: re-indexed deletion copies, and the flat subdivision -/

section CentreGeometry

variable {n : ℕ} [NeZero n] (hn : 3 ≤ n) (g : WallGerm (n + 1)) (j : ZMod (n + 1))
  (hz : g.pointZeros = {turnSupport j})
  (hb : StrictBetween (g.center (j - 1)) (g.center j) (g.center (j + 1)))
  (hc : g.concurrences = ∅) (t : g.SideParameter) (hs : CommonSupports g t)
  (S : Finset (Crossing g.center))

/-- Corner counts agree between a centre carrier and its side copy
(`geoCornerCount_markTransport` with `identify_sides_marks_of`). -/
theorem geoCornerCount_side (hsd : SideRecordData hn g j hz hb hc t)
    (hF : FlatCarriersData hn g j hz hb hc t hs S) (b : Bool)
    (q : GeoComponent (flatCentreCG hn g j hz hb hc) S) :
    geoCornerCount (flatSideCG hn g b t) (transportSupport (hs b) S)
        (sideCarrierEquiv hn g j hz hb hc t hs S hF b q) =
      geoCornerCount (flatCentreCG hn g j hz hb hc) S q := by
  obtain ⟨a, rfl⟩ := geoOwner_surjective (flatCentreCG hn g j hz hb hc) S q
  exact (geoCornerCount_markTransport _ _ (hs b) (identify_sides_marks_of hn g j hz hb hc t hsd hs b)
    S a).symm

/-- Every centre carrier of an independent support has at least three corners (its side copy is
an accepted carrier). -/
theorem geoCornerCount_ge_three_centre (hsd : SideRecordData hn g j hz hb hc t)
    (hS : GeoIndependent (flatCentreCG hn g j hz hb hc) S)
    (hF : FlatCarriersData hn g j hz hb hc t hs S)
    (q : GeoComponent (flatCentreCG hn g j hz hb hc) S) :
    3 ≤ geoCornerCount (flatCentreCG hn g j hz hb hc) S q := by
  rw [← geoCornerCount_side hn g j hz hb hc t hs S hsd hF true q]
  exact geoCornerCount_ge_three_generic (flat_hn1 hn) (g.sideTuple true t).property
    (((independent_supports_of hn g j hz hb hc t hsd hs S).1 true).mp hS) _

/-- "Every other central carrier is unchanged by deletion": its corner polygon is a re-indexing of
its deletion copy's (`others_unchanged.2` through `reindexed_markPolygon_of_isRotated`,
`reindexed_markPolygon_map`, `markPolygon_congr` with `fusion_mark_point` — the three steps of
`rotationNumber_others_unchanged`). -/
theorem reindexed_deletion_other (hF : FlatCarriersData hn g j hz hb hc t hs S)
    (q : GeoComponent (flatCentreCG hn g j hz hb hc) S)
    (hq : q ≠ centralCarrierThroughJ hn g j hz hb hc S) :
    Reindexed (geoCornerPolygon (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S)
        ((deletionCarrierEquiv hn g j hz hb hc t hs S hF).symm q))
      (geoCornerPolygon (flatCentreCG hn g j hz hb hc) S q) := by
  obtain ⟨q', rfl⟩ := (deletionCarrierEquiv hn g j hz hb hc t hs S hF).surjective q
  obtain ⟨b, rfl⟩ := geoOwner_surjective (flatDeletionCG hn g j hz hb hc) _ q'
  rw [Equiv.symm_apply_apply, deletionCarrierEquiv_owner]
  rw [deletionCarrierEquiv_owner] at hq
  have hrot := Cycle.coe_eq_coe.mp (hF.others_unchanged b hq).2.1
  have : NeZero ((geoComponentCornerList (flatDeletionCG hn g j hz hb hc)
      (deletionSupport hn g j hz hb hc S)
      (geoOwner (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S) b)).map
        (fusionMark hn g j hz hb hc)).length := ⟨by rw [List.length_map]; exact NeZero.ne _⟩
  have h1 := reindexed_markPolygon_of_isRotated
    (fun m => traversalEvaluation g.center (geoMarkPosition (flatCentreCG hn g j hz hb hc) m)) hrot
  have h2 := reindexed_markPolygon_map
    (fun m => traversalEvaluation g.center (geoMarkPosition (flatCentreCG hn g j hz hb hc) m))
    (fusionMark hn g j hz hb hc)
    (geoComponentCornerList (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S)
      (geoOwner (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S) b))
  have h3 := markPolygon_congr
    (f := (fun m => traversalEvaluation g.center (geoMarkPosition (flatCentreCG hn g j hz hb hc) m))
      ∘ fusionMark hn g j hz hb hc)
    (f' := fun m => traversalEvaluation (deleteVertex g.center j)
      (geoMarkPosition (flatDeletionCG hn g j hz hb hc) m))
    (geoComponentCornerList (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S)
      (geoOwner (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S) b))
    (fun a _ => fusion_mark_point hn g j hz hb hc a)
  exact (h3 ▸ h2).trans h1

/-- "The central copy of that carrier differs from its deletion copy only by the positive-flat
subdivision at `μ_j`": the centre corner polygon of the carrier through `μ_j` is, up to re-indexing,
the deletion copy's corner polygon with the vertex `μ_j` appended on its closing edge at an interior
parameter (`exists_appendVertex_of_erase_flat` on `central_vs_deletion_through_mu_j.3`, with
`flat_of_turn_eq_zero` from `turns_nonzero.1` and regularity, and `deletion_mark_point`). -/
theorem exists_appendVertex_central (hF : FlatCarriersData hn g j hz hb hc t hs S) :
    ∃ (Q : LabelledTuple (geoCornerCount (flatDeletionCG hn g j hz hb hc)
        (deletionSupport hn g j hz hb hc S) (deletionCopyThroughJ hn g j hz hb hc S))) (u : ℝ),
      0 < u ∧ u < 1 ∧
      Reindexed (geoCornerPolygon (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S)
        (deletionCopyThroughJ hn g j hz hb hc S)) Q ∧
      Reindexed (appendVertex Q u)
        (geoCornerPolygon (flatCentreCG hn g j hz hb hc) S (centralCarrierThroughJ hn g j hz hb hc S)) ∧
      edgePoint Q (-1) u = g.center j := by
  sorry

/-- `μ_j` lies on at most one closed edge of the deletion copy of the carrier through `μ_j`: two
non-adjacent edges meet only at a crossing point of the deletion (`nonadjacent_meet_crossing`),
which is a centre crossing point (`crossingPoint_fusion`) and so not the vertex `μ_j`
(`flat_germ_spatial_data` at the centre); consecutive edges meet only at their common corner
(`consecutive_meet`), a deletion corner point, which is the point of a centre mark other than
`μ_j` (`deletion_mark_point`, `central_vs_deletion_through_mu_j.3`), hence not `μ_j`
(injectivity of the centre vertices, no vertex is a crossing point). -/
theorem mu_j_unique_edge (hF : FlatCarriersData hn g j hz hb hc t hs S)
    (hS_D : IsDecomposition hn (generic_deleteVertex hn hz hb hc) (deletionSupport hn g j hz hb hc S))
    (e e' : ZMod (geoCornerCount (flatDeletionCG hn g j hz hb hc)
      (deletionSupport hn g j hz hb hc S) (deletionCopyThroughJ hn g j hz hb hc S)))
    (he : g.center j ∈ edgeSegment (geoCornerPolygon (flatDeletionCG hn g j hz hb hc)
      (deletionSupport hn g j hz hb hc S) (deletionCopyThroughJ hn g j hz hb hc S)) e)
    (he' : g.center j ∈ edgeSegment (geoCornerPolygon (flatDeletionCG hn g j hz hb hc)
      (deletionSupport hn g j hz hb hc S) (deletionCopyThroughJ hn g j hz hb hc S)) e') :
    e = e' := by
  sorry

/-- The one-component shadow of every centre corner polygon is generic: for the carrier through
`μ_j` by `single_generic_appendVertex` (the new vertex `μ_j` is on no other edge by
`mu_j_unique_edge`, transported along the re-indexing), for every other carrier by
`single_generic_of_reindexed` from the deletion copy (`single_geo_generic`). -/
theorem centre_shadow_generic (hsd : SideRecordData hn g j hz hb hc t)
    (hS : GeoIndependent (flatCentreCG hn g j hz hb hc) S)
    (hF : FlatCarriersData hn g j hz hb hc t hs S)
    (q : GeoComponent (flatCentreCG hn g j hz hb hc) S) :
    (Shadow.single ⟨geoCornerCount (flatCentreCG hn g j hz hb hc) S q,
      geoCornerCount_ge_three_centre hn g j hz hb hc t hs S hsd hS hF q,
      geoCornerPolygon (flatCentreCG hn g j hz hb hc) S q⟩).Generic := by
  sorry

/-- The HOMFLY polynomial of the positive lift of the deletion copy of a centre carrier (read as the
positive diagram of its geo corner polygon, `positiveLift_eq_geo`) is that of the positive diagram
of the centre corner polygon: through `μ_j` by `homfly_positiveDiagram_single_appendVertex` and two
re-indexings (`homfly_positiveDiagram_single_of_reindexed`, `exists_appendVertex_central`,
`deletionCarrierEquiv_symm_central`), elsewhere by one re-indexing (`reindexed_deletion_other`). -/
theorem homfly_deletion_eq_centre (hsd : SideRecordData hn g j hz hb hc t)
    (hS : GeoIndependent (flatCentreCG hn g j hz hb hc) S)
    (hF : FlatCarriersData hn g j hz hb hc t hs S)
    (q : GeoComponent (flatCentreCG hn g j hz hb hc) S)
    (hS_D : IsDecomposition hn (generic_deleteVertex hn hz hb hc) (deletionSupport hn g j hz hb hc S)) :
    homfly ((Shadow.single ⟨geoCornerCount (flatDeletionCG hn g j hz hb hc)
          (deletionSupport hn g j hz hb hc S) ((deletionCarrierEquiv hn g j hz hb hc t hs S hF).symm q),
        geoCornerCount_ge_three_generic hn (generic_deleteVertex hn hz hb hc) hS_D _,
        geoCornerPolygon (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S)
          ((deletionCarrierEquiv hn g j hz hb hc t hs S hF).symm q)⟩).positiveDiagram
        (single_geo_generic hn (generic_deleteVertex hn hz hb hc) hS_D _)) =
      homfly ((Shadow.single ⟨geoCornerCount (flatCentreCG hn g j hz hb hc) S q,
        geoCornerCount_ge_three_centre hn g j hz hb hc t hs S hsd hS hF q,
        geoCornerPolygon (flatCentreCG hn g j hz hb hc) S q⟩).positiveDiagram
        (centre_shadow_generic hn g j hz hb hc t hs S hsd hS hF q)) := by
  sorry

end CentreGeometry

/-! ## E. The deformation through the flat centre -/

section DeformThroughCentre

variable {n : ℕ} [NeZero n] (hn : 3 ≤ n) (g : WallGerm (n + 1)) (j : ZMod (n + 1))
  (hz : g.pointZeros = {turnSupport j})
  (hb : StrictBetween (g.center (j - 1)) (g.center j) (g.center (j + 1)))
  (hc : g.concurrences = ∅)

/-- The radius facts of lem:flat-sides used along the family: below `δ`, every `g.curve s` is on
the geometric record domain with the centre's crossing supports (`FlatSidesData`, last conjunct,
through `GeometricRecordsAgree`), and the side records hold at every side parameter. -/
def FlatFamilyData (δ : ℝ) : Prop :=
  0 < δ ∧ δ ≤ g.radius ∧
  (∀ s : g.Parameter, |s.val| < δ →
    CrossingGeometry (g.curve s) ∧
      ∀ c : Finset (ZMod (n + 1)), IsCrossing g.center c ↔ IsCrossing (g.curve s) c) ∧
  ∀ t : g.SideParameter, t.val < δ → SideRecordData hn g j hz hb hc t

theorem exists_flatFamilyData (hsc : g.SignChanges (fun P => (turn P j : ℝ))) :
    ∃ δ : ℝ, FlatFamilyData hn g j hz hb hc δ := by
  obtain ⟨δS, hδS, hδSr, hloc⟩ := flat_side_records hn g j hz hb hc (flat_sides hn g hz hb hc hsc)
  obtain ⟨_, _, _, _, _, _, δF, hδF, -, -, hF⟩ := flat_sides hn g hz hb hc hsc
  refine ⟨min δS δF, lt_min hδS hδF, (min_le_left _ _).trans hδSr, ?_, ?_⟩
  · intro s hs
    have h := hF s (lt_of_lt_of_le hs (min_le_right _ _))
    obtain ⟨hsupp, -⟩ := h.2.2.2.2.2.1
    exact ⟨h.2.1, hsupp⟩
  · intro t ht
    exact (hloc t (lt_of_lt_of_le ht (min_le_left _ _))).2

omit [NeZero n] in
/-- `markPointOn` is continuous at every parameter on the geometric record domain with the
centre's supports (the proof of the accepted `continuousAt_markPointOn`, at `s₀` in place of `0`:
vertices by `g.continuous_curve`, visits by `continuousAt_edgeParameter_of_geometry`). -/
theorem continuousAt_markPointOn_of (s₀ : g.Parameter) (hC : CrossingGeometry (g.curve s₀))
    (hcs : ∀ c : Finset (ZMod (n + 1)), IsCrossing g.center c ↔ IsCrossing (g.curve s₀) c)
    (a : Mark g.center) : ContinuousAt (fun s => markPointOn g s a) s₀ := by
  cases a with
  | inl i => exact ((continuous_apply i).comp g.continuous_curve).continuousAt
  | inr v =>
    have hcross0 : IsCrossing g.center {v.2.val, (visitTwin v).2.val} := by
      rw [← visit_crossing_val_eq_pair v]
      exact v.1.property
    have hcross := (hcs _).mp hcross0
    have hF : ContinuousAt (fun Q : LabelledTuple (n + 1) =>
        edgePoint Q v.2.val (edgeParameter Q v.2.val (visitTwin v).2.val)) (g.curve s₀) :=
      (continuous_vertex v.2.val).continuousAt.add
        ((continuousAt_edgeParameter_of_geometry hC hcross).smul
          (continuous_edge v.2.val).continuousAt)
    exact ContinuousAt.comp (f := g.curve) (x := s₀) hF g.continuous_curve.continuousAt

/-- The affine path `u ↦ u · (±t)` from the centre to the side time `sideTime b t`. -/
def sideParamPath (b : Bool) (t : g.SideParameter) (u : unitInterval) : g.Parameter :=
  ⟨u.val * (g.sideTime b t).val, by
    have h1 := (g.sideTime b t).property
    have h2 := u.property
    simp only [Set.mem_Ioo, Set.mem_Icc] at h1 h2 ⊢
    constructor <;> nlinarith [abs_nonneg (g.sideTime b t).val, g.radius_pos]⟩

omit [NeZero n] in
theorem sideParamPath_zero (b : Bool) (t : g.SideParameter) :
    sideParamPath g b t 0 = g.zeroParameter := by
  apply Subtype.ext
  simp [sideParamPath, WallGerm.zeroParameter]

omit [NeZero n] in
theorem sideParamPath_one (b : Bool) (t : g.SideParameter) :
    sideParamPath g b t 1 = g.sideTime b t := by
  apply Subtype.ext
  simp [sideParamPath]

omit [NeZero n] in
theorem continuous_sideParamPath (b : Bool) (t : g.SideParameter) :
    Continuous (sideParamPath g b t) :=
  (continuous_subtype_val.mul continuous_const).subtype_mk _

omit [NeZero n] in
theorem abs_sideParamPath_lt (b : Bool) (t : g.SideParameter) {δ : ℝ} (ht : t.val < δ)
    (u : unitInterval) : |(sideParamPath g b t u).val| < δ := by
  show |u.val * (g.sideTime b t).val| < δ
  rw [abs_mul, g.sideTime_val_abs, abs_of_nonneg u.property.1]
  exact lt_of_le_of_lt (mul_le_of_le_one_left t.property.1.le u.property.2) ht

omit [NeZero n] in
/-- For `0 < u`, the path parameter is the side time of the side parameter `u · t`. -/
theorem sideParamPath_eq_sideTime (b : Bool) (t : g.SideParameter) (u : unitInterval)
    (hu : 0 < u.val) :
    sideParamPath g b t u =
      g.sideTime b ⟨u.val * t.val, by
        have h1 := t.property; have h2 := u.property
        simp only [Set.mem_Ioo, Set.mem_Icc] at h1 h2 ⊢
        constructor <;> nlinarith⟩ := by
  apply Subtype.ext
  show u.val * (g.sideTime b t).val = (g.sideTime b ⟨u.val * t.val, _⟩).val
  cases b <;> simp only [WallGerm.sideTime, Bool.false_eq_true, ↓reduceIte, mul_neg]

variable (S : Finset (Crossing g.center))

/-- The side copy's corner polygon is the accepted `cornerFamily` at the side time, recast along
the equal corner counts (the corner list is carried literally by `markTransport`:
`geoComponentCornerList_markTransport` with `identify_sides_marks_of`; points by
`markPointOn_side`). -/
theorem geoCornerPolygon_side_eq_cornerFamily (t : g.SideParameter)
    (hsd : SideRecordData hn g j hz hb hc t) (hs : CommonSupports g t) (b : Bool)
    (a : Mark g.center) :
    geoCornerPolygon (flatSideCG hn g b t) (transportSupport (hs b) S)
        (geoOwner (flatSideCG hn g b t) (transportSupport (hs b) S) (markTransport (hs b) a)) =
      recastTuple (geoCornerCount_markTransport _ _ (hs b)
          (identify_sides_marks_of hn g j hz hb hc t hsd hs b) S a).symm
        (cornerFamily hn g j hz hb hc S (geoOwner (flatCentreCG hn g j hz hb hc) S a)
          (g.sideTime b t)) := by
  sorry

/-- At a side time the family's one-component shadow is generic (it is the recast carrier shadow
of the side copy, `single_geo_generic`). -/
theorem cornerFamily_side_generic (t : g.SideParameter) (hsd : SideRecordData hn g j hz hb hc t)
    (hS : GeoIndependent (flatCentreCG hn g j hz hb hc) S) (b : Bool)
    (q : GeoComponent (flatCentreCG hn g j hz hb hc) S)
    (hk : 3 ≤ geoCornerCount (flatCentreCG hn g j hz hb hc) S q) :
    (Shadow.single ⟨geoCornerCount (flatCentreCG hn g j hz hb hc) S q, hk,
      cornerFamily hn g j hz hb hc S q (g.sideTime b t)⟩).Generic := by
  sorry

/-- The positive diagram of the side copy's corner polygon (= the positive lift of the accepted
side carrier, `positiveLift_eq_geo`) is the positive diagram of the family at the side time
(`geoCornerPolygon_side_eq_cornerFamily`, `polyComp_recastTuple`, `positiveDiagram_congr`). -/
theorem geoDiagram_side_eq_cornerFamily (t : g.SideParameter)
    (hsd : SideRecordData hn g j hz hb hc t) (hs : CommonSupports g t)
    (hS : GeoIndependent (flatCentreCG hn g j hz hb hc) S)
    (hF : FlatCarriersData hn g j hz hb hc t hs S) (b : Bool)
    (q : GeoComponent (flatCentreCG hn g j hz hb hc) S)
    (hS_T : IsDecomposition (flat_hn1 hn) (g.sideTuple b t).property (transportSupport (hs b) S)) :
    (Shadow.single ⟨geoCornerCount (flatSideCG hn g b t) (transportSupport (hs b) S)
          (sideCarrierEquiv hn g j hz hb hc t hs S hF b q),
        geoCornerCount_ge_three_generic (flat_hn1 hn) (g.sideTuple b t).property hS_T _,
        geoCornerPolygon (flatSideCG hn g b t) (transportSupport (hs b) S)
          (sideCarrierEquiv hn g j hz hb hc t hs S hF b q)⟩).positiveDiagram
        (single_geo_generic (flat_hn1 hn) (g.sideTuple b t).property hS_T _) =
      (Shadow.single ⟨geoCornerCount (flatCentreCG hn g j hz hb hc) S q,
        geoCornerCount_ge_three_centre hn g j hz hb hc t hs S hsd hS hF q,
        cornerFamily hn g j hz hb hc S q (g.sideTime b t)⟩).positiveDiagram
        (cornerFamily_side_generic hn g j hz hb hc S t hsd hS b q _) := by
  sorry

/-- **The Deform through the flat centre.** Along `u ↦ cornerFamily S q (sideParamPath b t u)` the
corner polygon of the centre carrier moves continuously (`continuousAt_markPointOn_of` on the
family radius) from the centre corner polygon (`cornerFamily_zero`) to the side copy's; every
intermediate shadow is generic (`u = 0`: `centre_shadow_generic`; `u > 0`:
`cornerFamily_side_generic` at the side parameter `u · t`, `sideParamPath_eq_sideTime`); so
`homfly_positiveDiagram_single_of_family` identifies the HOMFLY polynomials (endpoints:
`cornerFamily_zero`, `geoDiagram_side_eq_cornerFamily`). Stated on the geo positive diagram of the
side copy (= the positive lift, `positiveLift_eq_geo`), as `cornerCoefficient_eq_geo` reads it. -/
theorem homfly_side_eq_centre {δ : ℝ} (hδ : FlatFamilyData hn g j hz hb hc δ)
    (t : g.SideParameter) (ht : t.val < δ) (hs : CommonSupports g t)
    (hS : GeoIndependent (flatCentreCG hn g j hz hb hc) S)
    (hF : FlatCarriersData hn g j hz hb hc t hs S) (b : Bool)
    (q : GeoComponent (flatCentreCG hn g j hz hb hc) S)
    (hS_T : IsDecomposition (flat_hn1 hn) (g.sideTuple b t).property (transportSupport (hs b) S)) :
    homfly ((Shadow.single ⟨geoCornerCount (flatSideCG hn g b t) (transportSupport (hs b) S)
          (sideCarrierEquiv hn g j hz hb hc t hs S hF b q),
        geoCornerCount_ge_three_generic (flat_hn1 hn) (g.sideTuple b t).property hS_T _,
        geoCornerPolygon (flatSideCG hn g b t) (transportSupport (hs b) S)
          (sideCarrierEquiv hn g j hz hb hc t hs S hF b q)⟩).positiveDiagram
        (single_geo_generic (flat_hn1 hn) (g.sideTuple b t).property hS_T _)) =
      homfly ((Shadow.single ⟨geoCornerCount (flatCentreCG hn g j hz hb hc) S q,
        geoCornerCount_ge_three_centre hn g j hz hb hc t hs S (hδ.2.2.2 t ht) hS hF q,
        geoCornerPolygon (flatCentreCG hn g j hz hb hc) S q⟩).positiveDiagram
        (centre_shadow_generic hn g j hz hb hc t hs S (hδ.2.2.2 t ht) hS hF q)) := by
  sorry

end DeformThroughCentre

/-! ## F. Corresponding carrier coefficients agree -/

section Coefficients

variable {n : ℕ} [NeZero n] (hn : 3 ≤ n) (g : WallGerm (n + 1)) (j : ZMod (n + 1))
  (hz : g.pointZeros = {turnSupport j})
  (hb : StrictBetween (g.center (j - 1)) (g.center j) (g.center (j + 1)))
  (hc : g.concurrences = ∅) (S : Finset (Crossing g.center))

/-- `c(Q)` of a side copy equals `c(Q)` of the deletion copy: equal slots (`card_geoCarrierCrossings_*`,
`rotationNumber_*`) and equal HOMFLY values (both equal the centre diagram's:
`homfly_side_eq_centre`, `homfly_deletion_eq_centre`), through `cornerCoefficient_eq_geo`. -/
theorem cornerCoefficient_side_eq_deletion {δ : ℝ} (hδ : FlatFamilyData hn g j hz hb hc δ)
    (t : g.SideParameter) (ht : t.val < δ) (hs : CommonSupports g t)
    (hS : GeoIndependent (flatCentreCG hn g j hz hb hc) S)
    (hF : FlatCarriersData hn g j hz hb hc t hs S) (b : Bool)
    (q : GeoComponent (flatCentreCG hn g j hz hb hc) S)
    (hS_T : IsDecomposition (flat_hn1 hn) (g.sideTuple b t).property (transportSupport (hs b) S))
    (hS_D : IsDecomposition hn (generic_deleteVertex hn hz hb hc) (deletionSupport hn g j hz hb hc S)) :
    cornerCoefficient (flat_hn1 hn) (g.sideTuple b t).property (transportSupport (hs b) S)
        (geoComponentEquivGeneric (flat_hn1 hn) (g.sideTuple b t).property _
          (sideCarrierEquiv hn g j hz hb hc t hs S hF b q)) hS_T =
      cornerCoefficient hn (generic_deleteVertex hn hz hb hc) (deletionSupport hn g j hz hb hc S)
        (geoComponentEquivGeneric hn (generic_deleteVertex hn hz hb hc) _
          ((deletionCarrierEquiv hn g j hz hb hc t hs S hF).symm q)) hS_D := by
  rw [cornerCoefficient_eq_geo, cornerCoefficient_eq_geo]
  rw [card_geoCarrierCrossings_side hn g j hz hb hc t hs S hF b q]
  rw [card_geoCarrierCrossings_deletion hn g j hz hb hc t hs S hF q]
  rw [rotationNumber_side hn g j hz hb hc t hs S hF b q]
  rw [rotationNumber_deletion hn g j hz hb hc t hs S hF q]
  rw [homfly_side_eq_centre hn g j hz hb hc S hδ t ht hs hS hF b q hS_T]
  rw [homfly_deletion_eq_centre hn g j hz hb hc t hs S (hδ.2.2.2 t ht) hS hF q hS_D]

/-- The products of the carrier coefficients agree (`Fintype.prod_equiv` along
`geoEq_T ∘ sideCarrierEquiv ∘ deletionCarrierEquiv ∘ geoEq_D⁻¹`). -/
theorem cornerProduct_side_eq_deletion {δ : ℝ} (hδ : FlatFamilyData hn g j hz hb hc δ)
    (t : g.SideParameter) (ht : t.val < δ) (hs : CommonSupports g t)
    (hS : GeoIndependent (flatCentreCG hn g j hz hb hc) S)
    (hF : FlatCarriersData hn g j hz hb hc t hs S) (b : Bool)
    (hS_T : IsDecomposition (flat_hn1 hn) (g.sideTuple b t).property (transportSupport (hs b) S))
    (hS_D : IsDecomposition hn (generic_deleteVertex hn hz hb hc) (deletionSupport hn g j hz hb hc S)) :
    cornerProduct (flat_hn1 hn) (g.sideTuple b t).property (transportSupport (hs b) S) hS_T =
      cornerProduct hn (generic_deleteVertex hn hz hb hc) (deletionSupport hn g j hz hb hc S) hS_D := by
  unfold cornerProduct
  let e := ((geoComponentEquivGeneric hn (generic_deleteVertex hn hz hb hc) _).symm.trans
    ((deletionCarrierEquiv hn g j hz hb hc t hs S hF).trans
      ((sideCarrierEquiv hn g j hz hb hc t hs S hF b).trans
        (geoComponentEquivGeneric (flat_hn1 hn) (g.sideTuple b t).property _))))
  refine (Fintype.prod_equiv e _ _ fun qD => ?_).symm
  have h := cornerCoefficient_side_eq_deletion hn g j hz hb hc S hδ t ht hs hS hF b
    (deletionCarrierEquiv hn g j hz hb hc t hs S hF
      ((geoComponentEquivGeneric hn (generic_deleteVertex hn hz hb hc) _).symm qD)) hS_T hS_D
  rw [Equiv.symm_apply_apply, Equiv.apply_symm_apply] at h
  exact h.symm

end Coefficients

/-! ## G. The selector algebra: `wind_R − wind_L = wind_D` -/

section SelectorAlgebra

variable {n : ℕ} [NeZero n] (hn : 3 ≤ n) (g : WallGerm (n + 1)) (j : ZMod (n + 1))
  (hz : g.pointZeros = {turnSupport j})
  (hb : StrictBetween (g.center (j - 1)) (g.center j) (g.center (j + 1)))
  (hc : g.concurrences = ∅) (t : g.SideParameter) (hs : CommonSupports g t)
  (S : Finset (Crossing g.center))

/-- `wind` of a side, indexed by the centre carriers. -/
theorem wind_side_eq_prod (hF : FlatCarriersData hn g j hz hb hc t hs S) (b : Bool) :
    wind (flat_hn1 hn) (g.sideTuple b t).property (transportSupport (hs b) S) =
      ∏ q : GeoComponent (flatCentreCG hn g j hz hb hc) S,
        geoCarrierSelector (flatSideCG hn g b t) (transportSupport (hs b) S)
          (sideCarrierEquiv hn g j hz hb hc t hs S hF b q) := by
  rw [wind_eq_prod_geoCarrierSelector]
  exact (Fintype.prod_equiv (sideCarrierEquiv hn g j hz hb hc t hs S hF b) _ _ fun _ => rfl).symm

/-- `wind` of the deletion, indexed by the centre carriers. -/
theorem wind_deletion_eq_prod (hF : FlatCarriersData hn g j hz hb hc t hs S) :
    wind hn (generic_deleteVertex hn hz hb hc) (deletionSupport hn g j hz hb hc S) =
      ∏ q : GeoComponent (flatCentreCG hn g j hz hb hc) S,
        geoCarrierSelector (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S)
          ((deletionCarrierEquiv hn g j hz hb hc t hs S hF).symm q) := by
  rw [wind_eq_prod_geoCarrierSelector]
  exact (Fintype.prod_equiv (deletionCarrierEquiv hn g j hz hb hc t hs S hF).symm _ _
    fun _ => rfl).symm

/-- "All other corresponding carrier selectors agree" (field `other_selectors_agree`), read on the
centre carriers: away from the carrier through `μ_j`, the side copy's selector is the deletion
copy's. -/
theorem selector_other (hF : FlatCarriersData hn g j hz hb hc t hs S) (b : Bool)
    (q : GeoComponent (flatCentreCG hn g j hz hb hc) S)
    (hq : q ≠ centralCarrierThroughJ hn g j hz hb hc S) :
    geoCarrierSelector (flatSideCG hn g b t) (transportSupport (hs b) S)
        (sideCarrierEquiv hn g j hz hb hc t hs S hF b q) =
      geoCarrierSelector (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S)
        ((deletionCarrierEquiv hn g j hz hb hc t hs S hF).symm q) := by
  obtain ⟨q', rfl⟩ := (deletionCarrierEquiv hn g j hz hb hc t hs S hF).surjective q
  obtain ⟨b', rfl⟩ := geoOwner_surjective (flatDeletionCG hn g j hz hb hc) _ q'
  rw [Equiv.symm_apply_apply, deletionCarrierEquiv_owner, sideCarrierEquiv_owner]
  rw [deletionCarrierEquiv_owner] at hq
  exact hF.other_selectors_agree b b' hq

/-- eq. ccf:distinguished-selector, read on the centre carriers (field `selector_identity` with
`sideCarrierEquiv_central`, `deletionCarrierEquiv_symm_central`). -/
theorem selector_central (hF : FlatCarriersData hn g j hz hb hc t hs S) (bR bL : Bool)
    (hR : IsRightSide g j bR t) (hL : IsLeftSide g j bL t) :
    geoCarrierSelector (flatSideCG hn g bR t) (transportSupport (hs bR) S)
        (sideCarrierEquiv hn g j hz hb hc t hs S hF bR (centralCarrierThroughJ hn g j hz hb hc S)) -
      geoCarrierSelector (flatSideCG hn g bL t) (transportSupport (hs bL) S)
        (sideCarrierEquiv hn g j hz hb hc t hs S hF bL (centralCarrierThroughJ hn g j hz hb hc S)) =
      geoCarrierSelector (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S)
        ((deletionCarrierEquiv hn g j hz hb hc t hs S hF).symm
          (centralCarrierThroughJ hn g j hz hb hc S)) := by
  rw [deletionCarrierEquiv_symm_central, sideCarrierEquiv_central, sideCarrierEquiv_central]
  exact hF.selector_identity bR bL hR hL

/-- eq. ccf:term-difference for the selectors: `wind_R − wind_L = wind_D`
(`Fintype.prod_eq_mul_prod_compl` at `q_*`, `selector_other` on the complement, `selector_central`;
`sub_mul`). -/
theorem wind_law (hF : FlatCarriersData hn g j hz hb hc t hs S) (bR bL : Bool)
    (hR : IsRightSide g j bR t) (hL : IsLeftSide g j bL t) :
    wind (flat_hn1 hn) (g.sideTuple bR t).property (transportSupport (hs bR) S) -
        wind (flat_hn1 hn) (g.sideTuple bL t).property (transportSupport (hs bL) S) =
      wind hn (generic_deleteVertex hn hz hb hc) (deletionSupport hn g j hz hb hc S) := by
  rw [wind_side_eq_prod hn g j hz hb hc t hs S hF bR, wind_side_eq_prod hn g j hz hb hc t hs S hF bL,
    wind_deletion_eq_prod hn g j hz hb hc t hs S hF,
    Fintype.prod_eq_mul_prod_compl (centralCarrierThroughJ hn g j hz hb hc S),
    Fintype.prod_eq_mul_prod_compl (centralCarrierThroughJ hn g j hz hb hc S),
    Fintype.prod_eq_mul_prod_compl (centralCarrierThroughJ hn g j hz hb hc S)]
  have hU : ∀ b : Bool, ∏ q ∈ ({centralCarrierThroughJ hn g j hz hb hc S} : Finset _)ᶜ,
      geoCarrierSelector (flatSideCG hn g b t) (transportSupport (hs b) S)
        (sideCarrierEquiv hn g j hz hb hc t hs S hF b q) =
      ∏ q ∈ ({centralCarrierThroughJ hn g j hz hb hc S} : Finset _)ᶜ,
        geoCarrierSelector (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S)
          ((deletionCarrierEquiv hn g j hz hb hc t hs S hF).symm q) := by
    intro b
    refine Finset.prod_congr rfl fun q hq => ?_
    rw [Finset.mem_compl, Finset.mem_singleton] at hq
    exact selector_other hn g j hz hb hc t hs S hF b q hq
  rw [hU bR, hU bL, ← sub_mul, selector_central hn g j hz hb hc t hs S hF bR bL hR hL]

end SelectorAlgebra

/-! ## H. The state sums: reindexing over the centre's supports and the flat law at one `t` -/

section StateSum

variable {n : ℕ} [NeZero n]

/-- The summand of lem:C-X1 as a total function of the support (`0` off `Ind(G_P)`). -/
def stateTerm (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P) (S : Finset (Crossing P)) : ℤ :=
  if h : IsDecomposition hn hP S then wind hn hP S * cornerProduct hn hP S h else 0

theorem stateTerm_of_not (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    {S : Finset (Crossing P)} (h : ¬ IsDecomposition hn hP S) : stateTerm hn hP S = 0 :=
  dite_eq_right h

theorem stateTerm_of_decomposition (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    {S : Finset (Crossing P)} (h : IsDecomposition hn hP S) :
    stateTerm hn hP S = wind hn hP S * cornerProduct hn hP S h :=
  dite_eq_left h

/-- lem:C-X1 as a sum over all supports (`C_X1.selector_form`, `Finset.sum_attach`,
completion by zeros). -/
theorem cornerStateSum_eq_sum_stateTerm (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P) :
    cornerStateSum hn hP = ∑ S : Finset (Crossing P), stateTerm hn hP S := by
  rw [C_X1.selector_form]
  have h1 : (∑ S ∈ (independentSupports hn hP).attach, wind hn hP S.1 * cornerProduct hn hP S.1 S.2) =
      ∑ S ∈ (independentSupports hn hP).attach, stateTerm hn hP S.1 :=
    Finset.sum_congr rfl fun S _ => (stateTerm_of_decomposition hn hP S.2).symm
  rw [h1, Finset.sum_attach]
  exact Finset.sum_subset (Finset.subset_univ _) fun S _ hS => stateTerm_of_not hn hP hS

/-- `Finset.map` along an equivalence, as an equivalence of finsets. -/
def finsetMapEquiv {α β : Type*} (e : α ≃ β) : Finset α ≃ Finset β where
  toFun S := S.map e.toEmbedding
  invFun S := S.map e.symm.toEmbedding
  left_inv S := by simp [Finset.map_map]
  right_inv S := by simp [Finset.map_map]

theorem sum_finsetMapEquiv {α β : Type*} [Fintype α] [Fintype β] (e : α ≃ β) (f : Finset β → ℤ) :
    ∑ S' : Finset β, f S' = ∑ S : Finset α, f (S.map e.toEmbedding) :=
  (Fintype.sum_equiv (finsetMapEquiv e) _ _ fun _ => rfl).symm

variable (hn : 3 ≤ n) (g : WallGerm (n + 1)) (j : ZMod (n + 1))
  (hz : g.pointZeros = {turnSupport j})
  (hb : StrictBetween (g.center (j - 1)) (g.center j) (g.center (j + 1)))
  (hc : g.concurrences = ∅)

/-- The term-wise flat law: for every centre support `S`, the right term minus the left term is the
deletion term (off `GeoIndependent` all three vanish by `independent_supports_of`; on it,
`stateTerm_of_decomposition`, `cornerProduct_side_eq_deletion` twice, `wind_law`, `sub_mul`). -/
theorem stateTerm_law {δ : ℝ} (hδ : FlatFamilyData hn g j hz hb hc δ)
    (t : g.SideParameter) (ht : t.val < δ) (hs : CommonSupports g t)
    (hF : ∀ S : Finset (Crossing g.center), GeoIndependent (flatCentreCG hn g j hz hb hc) S →
      FlatCarriersData hn g j hz hb hc t hs S)
    (bR bL : Bool) (hR : IsRightSide g j bR t) (hL : IsLeftSide g j bL t)
    (S : Finset (Crossing g.center)) :
    stateTerm (flat_hn1 hn) (g.sideTuple bR t).property (transportSupport (hs bR) S) -
        stateTerm (flat_hn1 hn) (g.sideTuple bL t).property (transportSupport (hs bL) S) =
      stateTerm hn (generic_deleteVertex hn hz hb hc) (deletionSupport hn g j hz hb hc S) := by
  have hind := independent_supports_of hn g j hz hb hc t (hδ.2.2.2 t ht) hs S
  by_cases hS : GeoIndependent (flatCentreCG hn g j hz hb hc) S
  · have hR' := (hind.1 bR).mp hS
    have hL' := (hind.1 bL).mp hS
    have hD' := hind.2.mp hS
    rw [stateTerm_of_decomposition _ _ hR', stateTerm_of_decomposition _ _ hL',
      stateTerm_of_decomposition _ _ hD',
      cornerProduct_side_eq_deletion hn g j hz hb hc S hδ t ht hs hS (hF S hS) bR hR' hD',
      cornerProduct_side_eq_deletion hn g j hz hb hc S hδ t ht hs hS (hF S hS) bL hL' hD',
      ← sub_mul, wind_law hn g j hz hb hc t hs S (hF S hS) bR bL hR hL]
  · rw [stateTerm_of_not _ _ (fun h => hS ((hind.1 bR).mpr h)),
      stateTerm_of_not _ _ (fun h => hS ((hind.1 bL).mpr h)),
      stateTerm_of_not _ _ (fun h => hS (hind.2.mpr h))]
    simp

/-- The flat law at one side parameter `t` below the radii of cor:flat-carriers and of the family
data: `C(P(bR, t)) − C(P(bL, t)) = C(P(0) ∖ j)`. -/
theorem flat_law_at {δ : ℝ} (hδ : FlatFamilyData hn g j hz hb hc δ)
    (t : g.SideParameter) (ht : t.val < δ) (hs : CommonSupports g t)
    (hF : ∀ S : Finset (Crossing g.center), GeoIndependent (flatCentreCG hn g j hz hb hc) S →
      FlatCarriersData hn g j hz hb hc t hs S)
    (bR bL : Bool) (hR : IsRightSide g j bR t) (hL : IsLeftSide g j bL t) :
    cornerStateSum (flat_hn1 hn) (g.sideTuple bR t).property -
        cornerStateSum (flat_hn1 hn) (g.sideTuple bL t).property =
      cornerStateSum hn (generic_deleteVertex hn hz hb hc) := by
  rw [cornerStateSum_eq_sum_stateTerm, cornerStateSum_eq_sum_stateTerm, cornerStateSum_eq_sum_stateTerm,
    sum_finsetMapEquiv (crossingTransport (hs bR)), sum_finsetMapEquiv (crossingTransport (hs bL)),
    sum_finsetMapEquiv (fusionCrossingEquiv hn hz hb hc), ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun S _ => stateTerm_law hn g j hz hb hc hδ t ht hs hF bR bL hR hL S

end StateSum

/-! ## I. Reduction to one side parameter, and the theorem -/

section Reduction

variable {n : ℕ} [NeZero n] (hn : 3 ≤ n) (g : WallGerm (n + 1)) (j : ZMod (n + 1))

omit [NeZero n] in
/-- "Proposition prop:C-chamber supplies the well-defined side values": along one side the state
sum is constant (`GermSides.sideTuple_mem_labelledSide`, `labelledSide_eq_at`,
`cornerStateSum_eq_of_mem_labelledChamber`). -/
theorem cornerStateSum_side_const (b : Bool) (t t' : g.SideParameter) :
    cornerStateSum (flat_hn1 hn) (g.sideTuple b t).property =
      cornerStateSum (flat_hn1 hn) (g.sideTuple b t').property := by
  have h : g.sideTuple b t' ∈ labelledChamber (g.sideTuple b t) := by
    rw [← g.labelledSide_eq_at b t]
    exact g.sideTuple_mem_labelledSide b t'
  exact cornerStateSum_eq_of_mem_labelledChamber (flat_hn1 hn) h

omit [NeZero n] in
/-- The turn at `j` is constant along one side (`generic_family_turn_constant` on the connected
side-parameter interval). -/
theorem side_turn_const (b : Bool) (t t' : g.SideParameter) :
    turn (g.sideTuple b t).val j = turn (g.sideTuple b t').val j :=
  Carrier.generic_family_turn_constant (g.continuous_sideTuple b) t t' j

omit [NeZero n] in
theorem isLeftSide_of_side (b : Bool) (t t' : g.SideParameter) (h : IsLeftSide g j b t) :
    IsLeftSide g j b t' := by
  unfold IsLeftSide at *
  rw [← side_turn_const g j b t t']
  exact h

end Reduction

/-- thm:C-S3 as printed (statement verbatim from work/drafts/CS3_statement.lean). -/
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

/-- **thm:C-S3.** The radius is the minimum of cor:flat-carriers' radius (`flat_carriers`) and the
family radius (`exists_flatFamilyData`); the left side is moved to the right side's parameter
(`cornerStateSum_side_const`, `isLeftSide_of_side`) and `flat_law_at` closes. -/
theorem thm_C_S3 : CS3Data where
  flat_law := by
    intro n _ hn g j hz hb hc hsc
    obtain ⟨δC, hδC, hδCr, hFC⟩ := flat_carriers hn g hz hb hc hsc
    obtain ⟨δF, hδF⟩ := exists_flatFamilyData hn g j hz hb hc hsc
    refine ⟨min δC δF, lt_min hδC hδF.1, (min_le_left _ _).trans hδCr, ?_⟩
    intro bR bL tR tL htR htL hR hL
    have htRC : tR.val < δC := lt_of_lt_of_le htR (min_le_left _ _)
    have htRF : tR.val < δF := lt_of_lt_of_le htR (min_le_right _ _)
    obtain ⟨hs, hF⟩ := hFC tR htRC
    rw [cornerStateSum_side_const hn g bL tL tR]
    exact flat_law_at hn g j hz hb hc hδF tR htRF hs hF bR bL hR
      (isLeftSide_of_side g j bL tL tR hL)

end

end SM
