import ActiveArcParentReducedCarriers

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.CompatibleWords
open PermutationOrbits FiniteCycleOrder SingletonWords Split Cursor RetainedWords
attribute [local instance] Classical.propDecidable

/-- The literal physical crossing pairing restricted to its retained events. -/
def physicalRetainedPairing {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ)
    (S : Finset (Crossing q)) : Equiv.Perm {x : Event q // retained q S x} :=
  (pairing q S).subtypeEquiv (by
    intro x
    cases x with
    | inl i => rfl
    | inr v =>
      by_cases hv : v.1∈S <;> simp [pairing,pairingMap,retained,hv])

variable {a b : ℕ} (q : Fin (a+b+2) → PlanarPoint ℝ) (hR : Regular q)
variable (c : Crossing q) (hc : FirstCrossing q c) (hcut : c.val.2.val=a)
variable (S : Finset (PolygonCrossing (child q hR c hc.1 hcut)))
variable (T : Finset (Crossing (parent q c hcut)))

/-- Actual piece-support swaps preserve the retained singleton complement. -/
def complementRetainedPairing : Equiv.Perm (ComplementRetained q hR c hc hcut S T) :=
  (pairing q (pieceSelections q hR c hc hcut S T)).subtypeEquiv (by
    have hf (x : Event q)
        (hx : retained q (insert c (pieceSelections q hR c hc hcut S T)) x ∧
          (Nonalternation.eventEnumeration q hR).symm x∈complementSide (leftRank q hR c) (rightRank q hR c)) :
        retained q (insert c (pieceSelections q hR c hc hcut S T))
            (pairing q (pieceSelections q hR c hc hcut S T) x) ∧
          (Nonalternation.eventEnumeration q hR).symm (pairing q (pieceSelections q hR c hc hcut S T) x)∈
            complementSide (leftRank q hR c) (rightRank q hR c) := by
      rcases (retained_complement_range q hR c hc hcut S T x).mp hx with rfl|⟨y,hy,rfl⟩
      · exact (retained_complement_range q hR c hc hcut S T (start q)).mpr (Or.inl rfl)
      · rw [pieceSelections_parent_pairing]
        exact (retained_complement_range q hR c hc hcut S T _).mpr (Or.inr
          ⟨(physicalRetainedPairing (parent q c hcut) T ⟨y,hy⟩).val,
            (physicalRetainedPairing (parent q c hcut) T ⟨y,hy⟩).property,rfl⟩)
    intro x
    constructor
    · exact hf x
    · intro hx
      have hh := hf _ hx
      have he : pairing q (pieceSelections q hR c hc hcut S T)
          (pairing q (pieceSelections q hR c hc hcut S T) x)=x :=
        (pairing q (pieceSelections q hR c hc hcut S T)).left_inv x
      rwa [he] at hh)

theorem complementRetainedPairing_start :
    complementRetainedPairing q hR c hc hcut S T (complementRetainedStart q hR c hc hcut S T)=
      complementRetainedStart q hR c hc hcut S T := by
  apply Subtype.ext
  rfl

theorem complementRetainedPairing_image (x : ParentRetained q c hcut T) :
    complementRetainedPairing q hR c hc hcut S T (parentRetainedOrderIso q hR c hc hcut S T x).val=
      (parentRetainedOrderIso q hR c hc hcut S T (physicalRetainedPairing (parent q c hcut) T x)).val := by
  apply Subtype.ext
  exact pieceSelections_parent_pairing q hR c hc hcut S T x.val

/-- Exact orbit prefix for the concrete reduced retained carrier permutations.
The subsequent deletion theorem is still needed to identify these with the
literal filtered incoming orbit words. -/
theorem reduced_parent_orbitWord :
    letI := eventOrder q hR.noTriple
    letI := eventOrder (parent q c hcut) (regular_parent q hR c hcut).noTriple
    orbitWord (orderedCyclicSuccessor (ComplementRetained q hR c hc hcut S T) *
      complementRetainedPairing q hR c hc hcut S T) (complementRetainedStart q hR c hc hcut S T)=
      complementRetainedStart q hR c hc hcut S T ::
        (orbitWord (orderedCyclicSuccessor (ParentRetained q c hcut T) *
          physicalRetainedPairing (parent q c hcut) T) (parentRetainedStart q c hcut T)).map
            (fun x => (parentRetainedOrderIso q hR c hc hcut S T x).val) := by
  letI := eventOrder q hR.noTriple
  letI := eventOrder (parent q c hcut) (regular_parent q hR c hcut).noTriple
  exact OrderedInsertion.paired_orbitWord (parentRetainedStart q c hcut T)
    (complementRetainedStart q hR c hc hcut S T) (parentRetainedOrderIso q hR c hc hcut S T)
    (parentRetainedStart_le q hR c hcut T) (complementRetainedStart_le q hR c hc hcut S T)
    (physicalRetainedPairing (parent q c hcut) T) (complementRetainedPairing q hR c hc hcut S T)
    (complementRetainedPairing_start q hR c hc hcut S T)
    (complementRetainedPairing_image q hR c hc hcut S T)

end DirectGLSSW.ActiveArc.CompatibleWords
