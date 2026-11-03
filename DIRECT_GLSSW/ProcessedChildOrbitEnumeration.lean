import ProcessedChildUniqueConnector
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.HOMFLY
open PermutationOrbits LowestRowContract
attribute [local instance] Classical.propDecidable
variable (t : MarkedParentState) (c : Fin t.1.nCrossing)
    (R : ComponentRestriction (smoothCrossing t.1 c)
      (rootSelfCutComponents t.1 c (t.2.2.connected _ _)
        (firstVisitedBranch t.2.1 c) (Sum.inl true)))

/-- The actual rooted orbit length, before any deletion or polygon reduction. -/
def detachedOrbitSize : ℕ :=
  Fintype.card (Fibre R.diagram.continuation
    (componentOf R.diagram.continuation (detachedConnector t c R)))

theorem detachedOrbitSize_pos : 0 < detachedOrbitSize t c R := by
  apply Fintype.card_pos_iff.mpr
  exact ⟨⟨detachedConnector t c R,rfl⟩⟩

/-- Actual continuation enumeration, bijective onto every arc of the exact
component restriction. Connectedness is derived from the restriction. -/
def detachedOrbitEquiv : Fin (detachedOrbitSize t c R) ≃ Fin R.diagram.nArc :=
  Equiv.ofBijective (fun j => (orbitEnumeration R.diagram.continuation (detachedConnector t c R) j).val) (by
    constructor
    · exact Subtype.val_injective.comp (orbitEnumeration _ _).injective
    · intro e
      have he : componentOf R.diagram.continuation e =
          componentOf R.diagram.continuation (detachedConnector t c R) :=
        (componentOf_eq_iff _ _ _).mpr (R.continuation_sameCycle e _)
      obtain ⟨j,hj⟩ := (orbitEnumeration R.diagram.continuation (detachedConnector t c R)).surjective ⟨e,he⟩
      exact ⟨j,congrArg Subtype.val hj⟩)

theorem detachedOrbitEquiv_apply (j : Fin (detachedOrbitSize t c R)) :
    detachedOrbitEquiv t c R j = (R.diagram.continuation ^ j.val) (detachedConnector t c R) := by
  exact orbitEnumeration_apply_val _ _ j

theorem detachedOrbitEquiv_zero :
    detachedOrbitEquiv t c R ⟨0,detachedOrbitSize_pos t c R⟩ = detachedConnector t c R := by
  rw [detachedOrbitEquiv_apply]
  rfl

theorem detachedOrbitEquiv_successor (i j : Fin (detachedOrbitSize t c R))
    (hij : j.val = i.val+1) :
    R.diagram.continuation (detachedOrbitEquiv t c R i) = detachedOrbitEquiv t c R j := by
  rw [detachedOrbitEquiv_apply,detachedOrbitEquiv_apply,hij,pow_succ',Equiv.Perm.mul_apply]

theorem detachedOrbitEquiv_old_code (i : Fin (detachedOrbitSize t c R)) (hi : 0 < i.val) :
    ∃ a : Fin t.1.nArc,
      (smoothArcEquiv t.1).symm (R.arcEquiv (detachedOrbitEquiv t c R i)).val = Sum.inl a := by
  apply (detached_old_code_iff t c R _).mpr
  intro he
  rw [← detachedOrbitEquiv_zero t c R] at he
  have hh := (detachedOrbitEquiv t c R).injective he
  have hv := congrArg Fin.val hh
  exact (Nat.ne_of_gt hi) hv

/-- The orbit size counts all genuine arcs of the component restriction. -/
theorem detachedOrbitSize_eq_nArc : detachedOrbitSize t c R = R.diagram.nArc := by
  simpa only [Fintype.card_fin] using Fintype.card_congr (detachedOrbitEquiv t c R)

end DirectGLSSW.HOMFLY
