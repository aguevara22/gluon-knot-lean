import DaughterEventCoverage
import DaughterLocalCrossing

set_option autoImplicit false
namespace DirectGLSSW.DaughterLocalCrossingEquiv
open DaughterFirstReturn DaughterParentCrossing DaughterEventCoverage DaughterLocalCrossing
open PolygonNonalternation PermutationOrbits ActualLocalSupports
noncomputable section

variable {n : ℕ} (P : Fin n → PlanarPoint ℝ) (hP : CyclicGeneric P)
variable (S : Finset (PolygonCrossing P)) (hS : polygonNonalternating P hP.g2 S)
variable (root : PolygonEvent P) (hroot : retainedCorner P S root)

/-- Both original visits of an eligible local crossing are covered by actual
daughter open edges. Ordering their daughter labels constructs the inverse crossing. -/
theorem localCrossingEmbedding_surjective :
    Function.Surjective (localCrossingEmbedding P hP S hS root hroot) := by
  intro c
  have hnc (b : Bool) : ¬ retainedCorner P S (Sum.inr (c.val,b)) := c.property.1
  obtain ⟨i,hei,hi⟩ := nonretained_event_in_daughter_edge P hP S root hroot
    (Sum.inr (c.val,false)) (hnc false) c.property.2.1
  obtain ⟨j,hej,hj⟩ := nonretained_event_in_daughter_edge P hP S root hroot
    (Sum.inr (c.val,true)) (hnc true) c.property.2.2
  have hci : daughterCarrier P hP.g2 S root i = c.val.val.1 := by
    simpa only [polygonEventEdge,crossingVisitEdge,Bool.false_eq_true,ite_false] using hei.symm
  have hcj : daughterCarrier P hP.g2 S root j = c.val.val.2 := by
    simpa only [polygonEventEdge,crossingVisitEdge,ite_true] using hej.symm
  change edgeInterior (daughterVertex P hP.g2 S root) i (crossingPoint P c.val) at hi
  change edgeInterior (daughterVertex P hP.g2 S root) j (crossingPoint P c.val) at hj
  have hij : i ≠ j := by
    intro h
    have hbad : c.val.val.1 = c.val.val.2 := hci.symm.trans (h ▸ hcj)
    exact (ne_of_lt c.val.property.1) hbad
  by_cases hlt : i < j
  · let d : PolygonCrossing (daughterVertex P hP.g2 S root) :=
      ⟨(i,j),hlt,⟨crossingPoint P c.val,hi,hj⟩⟩
    refine ⟨d,Subtype.ext (Subtype.ext ?_)⟩
    change (parentCrossing P hP S hS root hroot d).val = c.val.val
    rw [parentCrossing_labels]
    change (if daughterCarrier P hP.g2 S root i < daughterCarrier P hP.g2 S root j
      then (daughterCarrier P hP.g2 S root i,daughterCarrier P hP.g2 S root j)
      else (daughterCarrier P hP.g2 S root j,daughterCarrier P hP.g2 S root i)) = c.val.val
    rw [hci,hcj,if_pos c.val.property.1]
  · have hji : j < i := lt_of_le_of_ne (le_of_not_gt hlt) hij.symm
    let d : PolygonCrossing (daughterVertex P hP.g2 S root) :=
      ⟨(j,i),hji,⟨crossingPoint P c.val,hj,hi⟩⟩
    refine ⟨d,Subtype.ext (Subtype.ext ?_)⟩
    change (parentCrossing P hP S hS root hroot d).val = c.val.val
    rw [parentCrossing_labels]
    change (if daughterCarrier P hP.g2 S root j < daughterCarrier P hP.g2 S root i
      then (daughterCarrier P hP.g2 S root j,daughterCarrier P hP.g2 S root i)
      else (daughterCarrier P hP.g2 S root i,daughterCarrier P hP.g2 S root j)) = c.val.val
    rw [hci,hcj,if_neg (not_lt_of_gt c.val.property.1)]

/-- Exact crossing bijection, with the previously proved actual parentCrossing map. -/
def localCrossingEquiv : PolygonCrossing (daughterVertex P hP.g2 S root) ≃
    LocalCrossing P (smoothingDartPermutation P hP.g2 S) S
      (componentOf (smoothingDartPermutation P hP.g2 S) root) :=
  Equiv.ofBijective (localCrossingEmbedding P hP S hS root hroot)
    ⟨(localCrossingEmbedding P hP S hS root hroot).injective,
      localCrossingEmbedding_surjective P hP S hS root hroot⟩

theorem localCrossingEquiv_apply (c : PolygonCrossing (daughterVertex P hP.g2 S root)) :
    (localCrossingEquiv P hP S hS root hroot c).val =
      parentCrossing P hP S hS root hroot c := rfl




end
end DirectGLSSW.DaughterLocalCrossingEquiv
