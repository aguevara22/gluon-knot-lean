import SM.Chambers

/-! The preimage, finite-component bound and cyclic permutation clauses of
source def:chamber. This uses a saturated clopen union, without assuming a
path-lifting theorem for the cyclic quotient. -/

namespace SM

open Set Topology

variable {n : ℕ}

def genericShift (a : ZMod n) (P : GenericTuple n) : GenericTuple n :=
  ⟨shift a P.val, (generic_shift a P.val).mpr P.property⟩

@[simp] theorem genericShift_zero (P : GenericTuple n) : genericShift 0 P = P := by
  apply Subtype.ext
  exact shift_zero P.val

theorem genericShift_add (a b : ZMod n) (P : GenericTuple n) :
    genericShift a (genericShift b P) = genericShift (a + b) P := by
  apply Subtype.ext
  exact shift_add a b P.val

theorem continuous_genericShift (a : ZMod n) : Continuous (genericShift a : GenericTuple n → _) := by
  apply Continuous.subtype_mk
  exact continuous_pi fun i => (continuous_apply (i + a)).comp continuous_subtype_val

def genericShiftHomeomorph (a : ZMod n) : GenericTuple n ≃ₜ GenericTuple n where
  toFun := genericShift a
  invFun := genericShift (-a)
  left_inv := by intro P; simp [genericShift_add]
  right_inv := by intro P; simp [genericShift_add]
  continuous_toFun := continuous_genericShift a
  continuous_invFun := continuous_genericShift (-a)

theorem projection_eq_iff (P Q : GenericTuple n) :
    polygonProjection P = polygonProjection Q ↔ ∃ a : ZMod n, Q = genericShift a P := by
  constructor
  · intro h
    obtain ⟨a, ha⟩ := Quotient.exact h
    exact ⟨a, Subtype.ext ha⟩
  · rintro ⟨a, rfl⟩
    exact Quotient.sound ⟨a, rfl⟩

@[simp] theorem projection_genericShift (a : ZMod n) (P : GenericTuple n) :
    polygonProjection (genericShift a P) = polygonProjection P :=
  ((projection_eq_iff P _).mpr ⟨a, rfl⟩).symm

theorem continuous_polygonProjection :
    Continuous (polygonProjection : GenericTuple n → GenericPolygon n) :=
  continuous_quotient_mk'

theorem genericShift_labelledChamber (a : ZMod n) (P : GenericTuple n) :
    genericShift a '' labelledChamber P = labelledChamber (genericShift a P) := by
  let e := genericShiftHomeomorph a
  change e '' connectedComponent P = connectedComponent (e P)
  apply Set.Subset.antisymm (e.continuous.image_connectedComponent_subset P)
  intro Q hQ
  refine ⟨e.symm Q, ?_, e.apply_symm_apply Q⟩
  have h := e.symm.continuous.image_connectedComponent_subset (e P) ⟨Q, hQ, rfl⟩
  simpa using h

theorem preimage_projection_image (A : Set (GenericTuple n)) :
    polygonProjection ⁻¹' (polygonProjection '' A) = ⋃ a : ZMod n, genericShift a '' A := by
  ext Q
  constructor
  · rintro ⟨P, hP, hPQ⟩
    obtain ⟨a, rfl⟩ := (projection_eq_iff P Q).mp hPQ
    exact mem_iUnion.mpr ⟨a, P, hP, rfl⟩
  · intro hQ
    obtain ⟨a, P, hP, rfl⟩ := mem_iUnion.mp hQ
    exact ⟨P, hP, (projection_genericShift a P).symm⟩

/-- The actual cyclic saturation of one labelled connected component. -/
def cyclicChamberUnion (P : GenericTuple n) : Set (GenericTuple n) :=
  ⋃ a : ZMod n, labelledChamber (genericShift a P)

theorem preimage_projection_labelledChamber (P : GenericTuple n) :
    polygonProjection ⁻¹' (polygonProjection '' labelledChamber P) = cyclicChamberUnion P := by
  rw [preimage_projection_image]
  simp only [genericShift_labelledChamber, cyclicChamberUnion]

theorem isClopen_cyclicChamberUnion (hn : 3 ≤ n) (P : GenericTuple n) :
    IsClopen (cyclicChamberUnion P) := by
  haveI : NeZero n := ⟨by omega⟩
  letI := genericTuple_locallyPathConnected hn
  exact ⟨isClosed_iUnion_of_finite (fun _ => isClosed_connectedComponent),
    isOpen_iUnion (fun _ => isOpen_connectedComponent)⟩

theorem projection_labelledChamber_eq_chamber (hn : 3 ≤ n) (P : GenericTuple n) :
    polygonProjection '' labelledChamber P = chamber (polygonProjection P) := by
  have hq : IsQuotientMap (polygonProjection : GenericTuple n → GenericPolygon n) :=
    isQuotientMap_quotient_mk'
  have hc := isClopen_cyclicChamberUnion hn P
  have hcl : IsClopen (polygonProjection '' labelledChamber P) := by
    refine ⟨hq.isClosed_preimage.mp ?_, hq.isOpen_preimage.mp ?_⟩
    · simpa only [preimage_projection_labelledChamber] using hc.1
    · simpa only [preimage_projection_labelledChamber] using hc.2
  apply Set.Subset.antisymm (continuous_polygonProjection.image_connectedComponent_subset P)
  exact hcl.connectedComponent_subset ⟨P, mem_connectedComponent, rfl⟩

theorem chamber_preimage_eq_cyclic_union (hn : 3 ≤ n) (P : GenericTuple n) :
    polygonProjection ⁻¹' chamber (polygonProjection P) =
      ⋃ a : ZMod n, labelledChamber (genericShift a P) := by
  rw [← projection_labelledChamber_eq_chamber hn P, preimage_projection_labelledChamber]
  rfl

noncomputable def labelledChambersOver [NeZero n] (P : GenericTuple n) :
    Finset (Set (GenericTuple n)) := by
  classical
  exact Finset.univ.image (fun a : ZMod n => labelledChamber (genericShift a P))

theorem labelledChambersOver_card_le [NeZero n] (P : GenericTuple n) :
    (labelledChambersOver P).card ≤ n := by
  classical
  simpa only [labelledChambersOver, Finset.card_univ, ZMod.card] using
    (Finset.card_image_le (s := Finset.univ) (f := fun a : ZMod n => labelledChamber (genericShift a P)))

theorem labelledChambersOver_union [NeZero n] (P : GenericTuple n) :
    ⋃ C ∈ labelledChambersOver P, C = cyclicChamberUnion P := by
  classical
  ext Q
  simp [labelledChambersOver, cyclicChamberUnion]

theorem sigma_permutes_labelledChambers (P : GenericTuple n) (a : ZMod n) :
    genericShift 1 '' labelledChamber (genericShift a P) =
      labelledChamber (genericShift (a + 1) P) := by
  rw [genericShift_labelledChamber, genericShift_add, add_comm 1 a]

/-- Full definition aggregate, including the source's mathematical assertions
about the finite family above a quotient chamber and its cyclic permutation. -/
theorem chamber_definition (hn : 3 ≤ n) (P : GenericTuple n) :
    chamber (polygonProjection P) = connectedComponent (polygonProjection P) ∧
    (∀ Q : GenericTuple n, labelledChamber Q = connectedComponent Q) ∧
    polygonProjection ⁻¹' chamber (polygonProjection P) =
      (⋃ a : ZMod n, labelledChamber (genericShift a P)) ∧
    (∃ S : Finset (Set (GenericTuple n)), S.card ≤ n ∧
      (∀ C ∈ S, ∃ Q : GenericTuple n, C = labelledChamber Q) ∧
      polygonProjection ⁻¹' chamber (polygonProjection P) = ⋃ C ∈ S, C) ∧
    (∀ a : ZMod n, genericShift 1 '' labelledChamber (genericShift a P) =
      labelledChamber (genericShift (a + 1) P)) := by
  haveI : NeZero n := ⟨by omega⟩
  classical
  refine ⟨rfl, fun _ => rfl, chamber_preimage_eq_cyclic_union hn P, ?_,
    sigma_permutes_labelledChambers P⟩
  refine ⟨labelledChambersOver P, labelledChambersOver_card_le P, ?_, ?_⟩
  · intro C hC
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hC
    exact ⟨genericShift a P, rfl⟩
  · rw [labelledChambersOver_union, chamber_preimage_eq_cyclic_union hn P]
    rfl

end SM
