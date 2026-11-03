import ActiveArcIntervalRootWords
import ActiveArcPolygonRetainedWords
import DirectGLSSW.OrderedCyclicSeamRotation

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.CompatibleWords
open PermutationOrbits FiniteCycleOrder SingletonWords Split Cursor RetainedWords
attribute [local instance] Classical.propDecidable
variable {a b : ℕ} (q : Fin (a+b+2) → PlanarPoint ℝ) (hR : Regular q)
variable (c : Crossing q) (hc : FirstCrossing q c) (hcut : c.val.2.val=a)
variable (S : Finset (PolygonCrossing (child q hR c hc.1 hcut)))
variable (T : Finset (Crossing (parent q c hcut)))

def childRetainedZero : ChildRetained q hR c hc hcut S := ⟨Sum.inl 0,True.intro⟩
def intervalRetainedRight : IntervalRetained q hR c hc hcut S T :=
  ⟨Sum.inr (c,true),Finset.mem_insert_self _ _,right_in_interval q hR c⟩

theorem childRetainedZero_le (x : ChildRetained q hR c hc hcut S) :
    letI := polygonEventOrder (child q hR c hc.1 hcut) (child_noTriple q hR c hc.1 hcut)
    childRetainedZero q hR c hc hcut S ≤ x := child_zero_le q hR c hc hcut x.val

theorem intervalRetainedRight_ge (x : IntervalRetained q hR c hc hcut S T) :
    letI := eventOrder q hR.noTriple
    x ≤ intervalRetainedRight q hR c hc hcut S T :=
  ((rank_interval_iff q hR c x.val).mp x.property.2).2

theorem childRetainedEquiv_zero :
    childRetainedEquiv q hR c hc hcut S T (childRetainedZero q hR c hc hcut S)=
      intervalRetainedRight q hR c hc hcut S T := by
  apply Subtype.ext
  exact childEventMap_zero q hR c hc hcut

theorem childRetainedEquiv_lt_nonzero (x y : ChildRetained q hR c hc hcut S)
    (hx : x≠childRetainedZero q hR c hc hcut S) (hy : y≠childRetainedZero q hR c hc hcut S) :
    letI := eventOrder q hR.noTriple
    letI := polygonEventOrder (child q hR c hc.1 hcut) (child_noTriple q hR c hc.1 hcut)
    childRetainedEquiv q hR c hc hcut S T x < childRetainedEquiv q hR c hc hcut S T y ↔ x < y := by
  letI := eventOrder q hR.noTriple
  letI := polygonEventOrder (child q hR c hc.1 hcut) (child_noTriple q hR c hc.1 hcut)
  exact childEventMap_lt_nonzero q hR c hc hcut x.val y.val
    (fun he => hx (Subtype.ext he)) (fun he => hy (Subtype.ext he))

/-- The actual retained child carrier has the exact singleton-interval cyclic
successor, including the physical c-right to first-child-event wrap. -/
theorem childRetainedEquiv_successor (x : ChildRetained q hR c hc hcut S) :
    letI := eventOrder q hR.noTriple
    letI := polygonEventOrder (child q hR c hc.1 hcut) (child_noTriple q hR c hc.1 hcut)
    childRetainedEquiv q hR c hc hcut S T (orderedCyclicSuccessor (ChildRetained q hR c hc hcut S) x)=
      orderedCyclicSuccessor (IntervalRetained q hR c hc hcut S T) (childRetainedEquiv q hR c hc hcut S T x) := by
  letI := eventOrder q hR.noTriple
  letI := polygonEventOrder (child q hR c hc.1 hcut) (child_noTriple q hR c hc.1 hcut)
  exact orderedCyclicSuccessor_naturality_of_cut (childRetainedEquiv q hR c hc hcut S T)
    (childRetainedZero q hR c hc hcut S) (intervalRetainedRight q hR c hc hcut S T)
    (childRetainedZero_le q hR c hc hcut S) (intervalRetainedRight_ge q hR c hc hcut S T)
    (childRetainedEquiv_zero q hR c hc hcut S T) (childRetainedEquiv_lt_nonzero q hR c hc hcut S T) x

theorem childRetainedEquiv_incoming (x : ChildRetained q hR c hc hcut S) :
    letI := eventOrder q hR.noTriple
    letI := polygonEventOrder (child q hR c hc.1 hcut) (child_noTriple q hR c hc.1 hcut)
    (orderedCyclicSuccessor (IntervalRetained q hR c hc hcut S T)*intervalRetainedPairing q hR c hc hcut S T)
        (childRetainedEquiv q hR c hc hcut S T x)=
      childRetainedEquiv q hR c hc hcut S T
        ((orderedCyclicSuccessor (ChildRetained q hR c hc hcut S)*polygonRetainedPairing (child q hR c hc.1 hcut) S) x) := by
  letI := eventOrder q hR.noTriple
  letI := polygonEventOrder (child q hR c hc.1 hcut) (child_noTriple q hR c hc.1 hcut)
  rw [Equiv.Perm.mul_apply,Equiv.Perm.mul_apply,childRetainedEquiv_pairing]
  exact (childRetainedEquiv_successor q hR c hc hcut S T _).symm

theorem childRetainedEquiv_orbitWord (x : ChildRetained q hR c hc hcut S) :
    letI := eventOrder q hR.noTriple
    letI := polygonEventOrder (child q hR c hc.1 hcut) (child_noTriple q hR c hc.1 hcut)
    orbitWord (orderedCyclicSuccessor (IntervalRetained q hR c hc hcut S T)*intervalRetainedPairing q hR c hc hcut S T)
        (childRetainedEquiv q hR c hc hcut S T x)=
      (orbitWord (orderedCyclicSuccessor (ChildRetained q hR c hc hcut S)*polygonRetainedPairing (child q hR c hc.1 hcut) S) x).map
        (childRetainedEquiv q hR c hc hcut S T) := by
  letI := eventOrder q hR.noTriple
  letI := polygonEventOrder (child q hR c hc.1 hcut) (child_noTriple q hR c hc.1 hcut)
  exact orbitWord_map_injective _ _ (childRetainedEquiv q hR c hc hcut S T)
    (childRetainedEquiv q hR c hc hcut S T).injective (childRetainedEquiv_incoming q hR c hc hcut S T) x

end DirectGLSSW.ActiveArc.CompatibleWords
