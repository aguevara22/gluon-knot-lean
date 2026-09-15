import SM.FusionIndices

namespace SM

variable {n : ℕ} [NeZero n]

/-- Exactly the two incident parent roots map to the fused child root. -/
theorem fusionIndex_eq_last_iff_incident (j g : ZMod (n + 1)) :
    fusionIndex j g = (-1 : ZMod n) ↔ incident j g := by
  rw [fusionIndex_eq_iff_lift]
  simp only [DeletionEdgeLift, ite_true, incident]

/-- Every child root is represented by an actual parent root. -/
theorem fusionIndex_surjective (j : ZMod (n + 1)) : Function.Surjective (fusionIndex (n := n) j) := by
  intro i
  exact ⟨deletionIndex j i, fusionIndex_deletionIndex j i⟩

/-- The nonincident image root has both original endpoint labels, in order. -/
theorem fusionIndex_nonincident_labels (j g : ZMod (n + 1)) (h : ¬ incident j g) :
    deletionIndex j (fusionIndex j g) = g ∧
      deletionIndex j (fusionIndex j g + 1) = g + 1 := by
  have hp : g ≠ j - 1 := fun he => h (Or.inl he)
  have hj : g ≠ j := fun he => h (Or.inr he)
  refine ⟨deletionIndex_fusionIndex hj hp, ?_⟩
  rw [deletionIndex_next j (fusionIndex_ne_last hj hp), deletionIndex_fusionIndex hj hp]

/-- The fused image root runs from the predecessor to the successor, not
from either old incident edge's former endpoint pair. -/
theorem fusionIndex_incident_labels (j g : ZMod (n + 1)) (h : incident j g) :
    deletionIndex j (fusionIndex j g) = j - 1 ∧
      deletionIndex j (fusionIndex j g + 1) = j + 1 := by
  rw [(fusionIndex_eq_last_iff_incident j g).mpr h, neg_add_cancel]
  exact ⟨deletionIndex_last j, deletionIndex_zero j⟩

/-- Uniqueness is proved at label level, so it does not depend on accidental
equalities of geometric vertex coordinates. -/
theorem fusionIndex_unique_nonincident_root (j g : ZMod (n + 1)) (h : ¬ incident j g) :
    ∃! i : ZMod n, i ≠ -1 ∧ deletionIndex j i = g ∧ deletionIndex j (i + 1) = g + 1 := by
  have hp : g ≠ j - 1 := fun he => h (Or.inl he)
  have hj : g ≠ j := fun he => h (Or.inr he)
  have he := fusionIndex_nonincident_labels j g h
  refine ⟨fusionIndex j g, ⟨fusionIndex_ne_last hj hp, he⟩, ?_⟩
  intro i hi
  exact deletionIndex_injective j (hi.2.1.trans he.1.symm)

/-- The deletion part of the printed physical induced-root map: all ordered
endpoint pairs are explicit. This is not the separate half-map definition. -/
theorem fusionIndex_physical_deletion_root (P : LabelledTuple (n + 1)) (j g : ZMod (n + 1)) :
    (incident j g →
      deleteVertex P j (fusionIndex j g) = P (j - 1) ∧
        deleteVertex P j (fusionIndex j g + 1) = P (j + 1)) ∧
    (¬ incident j g →
      deleteVertex P j (fusionIndex j g) = P g ∧
        deleteVertex P j (fusionIndex j g + 1) = P (g + 1)) := by
  constructor
  · intro h
    have he := fusionIndex_incident_labels j g h
    simp only [deleteVertex_apply, he.1, he.2, and_self]
  · intro h
    have he := fusionIndex_nonincident_labels j g h
    simp only [deleteVertex_apply, he.1, he.2, and_self]

/-- At a retained root the whole parametrized physical edge is identical. -/
theorem fusionIndex_nonincident_edgePoint (P : LabelledTuple (n + 1)) (j g : ZMod (n + 1))
    (h : ¬ incident j g) (s : ℝ) :
    edgePoint (deleteVertex P j) (fusionIndex j g) s = edgePoint P g s := by
  have he := (fusionIndex_physical_deletion_root P j g).2 h
  simp only [edgePoint, edge, he.1, he.2]

end SM

#check SM.fusionIndex_eq_last_iff_incident
#print axioms SM.fusionIndex_eq_last_iff_incident

#check SM.fusionIndex_surjective
#print axioms SM.fusionIndex_surjective

#check SM.fusionIndex_nonincident_labels
#print axioms SM.fusionIndex_nonincident_labels

#check SM.fusionIndex_incident_labels
#print axioms SM.fusionIndex_incident_labels

#check SM.fusionIndex_unique_nonincident_root
#print axioms SM.fusionIndex_unique_nonincident_root

#check SM.fusionIndex_physical_deletion_root
#print axioms SM.fusionIndex_physical_deletion_root

#check SM.fusionIndex_nonincident_edgePoint
#print axioms SM.fusionIndex_nonincident_edgePoint
