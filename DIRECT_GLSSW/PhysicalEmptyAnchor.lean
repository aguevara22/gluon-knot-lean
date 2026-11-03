import PhysicalCursorG1
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.TraversalClosure
open DirectGLSSW ActiveArc RetainedWords Primitive PermutationOrbits
attribute [local instance] Classical.propDecidable

/-- The actual empty smoothing follows the one physical linear event cycle. -/
lemma empty_incoming_isCycle {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ) (hR : Regular q) :
    (incoming q hR.noTriple ∅).IsCycleOn Set.univ := by
  have he : incoming q hR.noTriple ∅ = successor q hR.noTriple := by
    ext x
    cases x with
    | inl i => rfl
    | inr v => simp [incoming,pairing,pairingMap]
  rw [he]
  letI := eventOrder q hR.noTriple
  exact orderedCyclicSuccessor_isCycleOn (Event q)

/-- Every original anchor has an actual retained open-word index under the
empty support. No count or enumeration equality is assumed. -/
def emptyAnchorIndex {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ) (hR : Regular q)
    (j : Fin (n+2)) : Fin (openCount q hR ∅) := by
  let P := incoming q hR.noTriple ∅
  let z : Fibre P (componentOf P (start q)) := ⟨Sum.inl j,
    (componentOf_eq_iff P _ _).mpr ((empty_incoming_isCycle q hR).2 (Set.mem_univ _) (Set.mem_univ _))⟩
  let c : Corner q hR ∅ (start q) := ⟨(orbitEnumeration P (start q)).symm z,by
    have hh := congrArg Subtype.val ((orbitEnumeration P (start q)).apply_symm_apply z)
    change retained q ∅ (eventAt q hR ∅ (start q) ((orbitEnumeration P (start q)).symm z))
    change retained q ∅ _
    rw [show eventAt q hR ∅ (start q) ((orbitEnumeration P (start q)).symm z)=Sum.inl j from hh]
    trivial⟩
  exact (enumeration q hR ∅ (start q)).symm c

lemma emptyAnchorIndex_event {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ) (hR : Regular q)
    (j : Fin (n+2)) : cornerEvent q hR ∅ (start q) (emptyAnchorIndex q hR j)=Sum.inl j := by
  unfold emptyAnchorIndex cornerEvent
  dsimp only
  rw [OrderIso.apply_symm_apply]
  exact congrArg Subtype.val ((orbitEnumeration _ _).apply_symm_apply _)

lemma emptyAnchorIndex_vertex {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ) (hR : Regular q)
    (j : Fin (n+2)) : vertex q hR ∅ (start q) (emptyAnchorIndex q hR j)=q j := by
  rw [RetainedWords.vertex,emptyAnchorIndex_event]
  rfl

lemma emptyAnchorIndex_injective {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ) (hR : Regular q) :
    Function.Injective (emptyAnchorIndex q hR) := by
  intro i j hij
  have hh := congrArg (cornerEvent q hR ∅ (start q)) hij
  rw [emptyAnchorIndex_event,emptyAnchorIndex_event] at hh
  exact Sum.inl.inj hh

lemma emptyAnchorIndex_ne_zero {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ) (hR : Regular q)
    (j : Fin (n+2)) (hj : j≠0) : (emptyAnchorIndex q hR j).val≠0 := by
  intro hh
  have he : emptyAnchorIndex q hR j=openFirst q hR ∅ := Fin.ext hh
  have hx := congrArg (cornerEvent q hR ∅ (start q)) he
  rw [emptyAnchorIndex_event,open_cornerEvent_first] at hx
  exact hj (Sum.inl.inj hx)
end DirectGLSSW.ActiveArc.TraversalClosure
