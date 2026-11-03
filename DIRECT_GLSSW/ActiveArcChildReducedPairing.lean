import ActiveArcChildEventOrder

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.CompatibleWords
open PermutationOrbits FiniteCycleOrder SingletonWords Split Cursor RetainedWords
attribute [local instance] Classical.propDecidable

/-- Actual polygon smoothing pairing restricted to its retained corners. -/
def polygonRetainedPairing {n : ℕ} (q : Fin n → PlanarPoint ℝ)
    (S : Finset (PolygonCrossing q)) :
    Equiv.Perm {x : PolygonEvent q // DaughterFirstReturn.retainedCorner q S x} :=
  (smoothingPairing q S).subtypeEquiv (fun x => (DaughterFirstReturn.pairing_preserves_retained q S x).symm)

variable {a b : ℕ} (q : Fin (a+b+2) → PlanarPoint ℝ) (hR : Regular q)
variable (c : Crossing q) (hc : FirstCrossing q c) (hcut : c.val.2.val=a)
variable (S : Finset (PolygonCrossing (child q hR c hc.1 hcut)))
variable (T : Finset (Crossing (parent q c hcut)))

theorem pieceSelections_child_pairing (x : PolygonEvent (child q hR c hc.1 hcut)) :
    pairing q (pieceSelections q hR c hc hcut S T) (childEventMap q hR c hc hcut x)=
      childEventMap q hR c hc hcut (smoothingPairing (child q hR c hc.1 hcut) S x) := by
  have hn : c∉pieceSelections q hR c hc hcut S T := by
    intro hh
    exact ((pieceSelections_range q hR c hc hcut _).mp ⟨S,T,rfl⟩ c hh).1 rfl
  cases x with
  | inl i =>
    by_cases hi : i=0
    · simp [childEventMap,hi,pairing,pairingMap,smoothingPairing_apply,smoothingPairingMap,
        hn]
    · simp [childEventMap,hi,pairing,pairingMap,smoothingPairing_apply,smoothingPairingMap]
  | inr v =>
    change (if childCrossingToOriginal q hR c hc.1 hcut v.1∈pieceSelections q hR c hc hcut S T
      then (Sum.inr (childCrossingToOriginal q hR c hc.1 hcut v.1,!v.2) : Event q)
      else Sum.inr (childVisitMap q hR c hc.1 hcut v))=_
    simp only [pieceSelections_child_mem]
    by_cases hv : v.1∈S <;>
      simp [hv,smoothingPairing_apply,smoothingPairingMap,childEventMap,childVisitMap,crossingVisitFlip]

/-- Actual piece-support swaps preserve the retained singleton child interval. -/
def intervalRetainedPairing : Equiv.Perm (IntervalRetained q hR c hc hcut S T) :=
  (pairing q (pieceSelections q hR c hc hcut S T)).subtypeEquiv (by
    have hf (x : Event q)
        (hx : retained q (insert c (pieceSelections q hR c hc hcut S T)) x ∧
          (Nonalternation.eventEnumeration q hR).symm x∈intervalSide (leftRank q hR c) (rightRank q hR c)) :
        retained q (insert c (pieceSelections q hR c hc hcut S T))
            (pairing q (pieceSelections q hR c hc hcut S T) x) ∧
          (Nonalternation.eventEnumeration q hR).symm (pairing q (pieceSelections q hR c hc hcut S T) x)∈
            intervalSide (leftRank q hR c) (rightRank q hR c) := by
      obtain ⟨y,hy,rfl⟩ := (retained_interval_range q hR c hc hcut S T x).mp hx
      rw [pieceSelections_child_pairing]
      exact (retained_interval_range q hR c hc hcut S T _).mpr
        ⟨(polygonRetainedPairing (child q hR c hc.1 hcut) S ⟨y,hy⟩).val,
          (polygonRetainedPairing (child q hR c hc.1 hcut) S ⟨y,hy⟩).property,rfl⟩
    intro x
    constructor
    · exact hf x
    · intro hx
      have hh := hf _ hx
      have he : pairing q (pieceSelections q hR c hc hcut S T)
          (pairing q (pieceSelections q hR c hc hcut S T) x)=x :=
        (pairing q (pieceSelections q hR c hc hcut S T)).left_inv x
      rwa [he] at hh)

theorem childRetainedEquiv_pairing (x : ChildRetained q hR c hc hcut S) :
    intervalRetainedPairing q hR c hc hcut S T (childRetainedEquiv q hR c hc hcut S T x)=
      childRetainedEquiv q hR c hc hcut S T (polygonRetainedPairing (child q hR c hc.1 hcut) S x) := by
  apply Subtype.ext
  exact pieceSelections_child_pairing q hR c hc hcut S T x.val

end DirectGLSSW.ActiveArc.CompatibleWords
