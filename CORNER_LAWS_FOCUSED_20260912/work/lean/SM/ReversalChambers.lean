import SM.GenericReversal
import SM.CyclicChambers

/-! Actual homeomorphisms of the generic locus and its cyclic quotient.
Their images of connected components are proved equal to full components. -/

namespace SM

open Set Topology

variable {n : ℕ}

def genericReversal (P : GenericTuple n) : GenericTuple n :=
  ⟨reversal P.val, (generic_reversal P.val).mpr P.property⟩

theorem genericReversal_involutive : Function.Involutive (genericReversal (n := n)) := by
  intro P
  apply Subtype.ext
  exact reversal_involutive P.val

theorem genericReversal_shift (a : ZMod n) (P : GenericTuple n) :
    genericReversal (genericShift a P) = genericShift (-a) (genericReversal P) := by
  apply Subtype.ext
  exact reversal_shift a P.val

theorem continuous_genericReversal : Continuous (genericReversal (n := n)) := by
  apply Continuous.subtype_mk
  exact continuous_pi fun i => (continuous_apply (2 - i)).comp continuous_subtype_val

def genericReversalHomeomorph : GenericTuple n ≃ₜ GenericTuple n where
  toFun := genericReversal
  invFun := genericReversal
  left_inv := genericReversal_involutive
  right_inv := genericReversal_involutive
  continuous_toFun := continuous_genericReversal
  continuous_invFun := continuous_genericReversal

theorem genericReversal_labelledChamber (P : GenericTuple n) :
    genericReversal '' labelledChamber P = labelledChamber (genericReversal P) := by
  let e := genericReversalHomeomorph (n := n)
  change e '' connectedComponent P = connectedComponent (e P)
  apply Set.Subset.antisymm (e.continuous.image_connectedComponent_subset P)
  intro Q hQ
  refine ⟨e.symm Q, ?_, e.apply_symm_apply Q⟩
  have h := e.symm.continuous.image_connectedComponent_subset (e P) ⟨Q, hQ, rfl⟩
  simpa using h

def genericPolygonReversal : GenericPolygon n → GenericPolygon n :=
  Quotient.map genericReversal (fun _ _ h => reversal_respects_cyclic h)

theorem genericPolygonReversal_projection (P : GenericTuple n) :
    genericPolygonReversal (polygonProjection P) = polygonProjection (genericReversal P) := rfl

theorem genericPolygonReversal_involutive :
    Function.Involutive (genericPolygonReversal (n := n)) := by
  intro P
  refine Quotient.inductionOn P (fun Q => ?_)
  change polygonProjection (genericReversal (genericReversal Q)) = polygonProjection Q
  rw [genericReversal_involutive Q]

theorem continuous_genericPolygonReversal : Continuous (genericPolygonReversal (n := n)) := by
  exact (continuous_polygonProjection.comp continuous_genericReversal).quotient_lift _

def genericPolygonReversalHomeomorph : GenericPolygon n ≃ₜ GenericPolygon n where
  toFun := genericPolygonReversal
  invFun := genericPolygonReversal
  left_inv := genericPolygonReversal_involutive
  right_inv := genericPolygonReversal_involutive
  continuous_toFun := continuous_genericPolygonReversal
  continuous_invFun := continuous_genericPolygonReversal

theorem genericPolygonReversal_chamber (P : GenericPolygon n) :
    genericPolygonReversal '' chamber P = chamber (genericPolygonReversal P) := by
  let e := genericPolygonReversalHomeomorph (n := n)
  change e '' connectedComponent P = connectedComponent (e P)
  apply Set.Subset.antisymm (e.continuous.image_connectedComponent_subset P)
  intro Q hQ
  refine ⟨e.symm Q, ?_, e.apply_symm_apply Q⟩
  have h := e.symm.continuous.image_connectedComponent_subset (e P) ⟨Q, hQ, rfl⟩
  simpa using h

end SM
