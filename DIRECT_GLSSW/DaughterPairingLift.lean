import DaughterKeptSuccessor

set_option autoImplicit false
namespace DirectGLSSW.DaughterPairingLift
open DaughterFirstReturn DaughterParentCrossing DaughterCrossingAvoidance
  DaughterVisitLift DaughterEventLift PolygonNonalternation
noncomputable section
attribute [local instance] Classical.propDecidable

variable {n : ℕ} (P : Fin n → PlanarPoint ℝ) (hP : CyclicGeneric P)
variable (S : Finset (PolygonCrossing P)) (hS : polygonNonalternating P hP.g2 S)
variable (root : PolygonEvent P) (hroot : retainedCorner P S root)

def liftedSupport (T : Finset (PolygonCrossing (daughterVertex P hP.g2 S root))) :
    Finset (PolygonCrossing P) :=
  T.map ⟨parentCrossing P hP S hS root hroot,parentCrossing_injective P hP S hS root hroot⟩

theorem mem_liftedSupport_iff (T : Finset (PolygonCrossing (daughterVertex P hP.g2 S root)))
    (c : PolygonCrossing (daughterVertex P hP.g2 S root)) :
    parentCrossing P hP S hS root hroot c ∈ liftedSupport P hP S hS root hroot T ↔ c ∈ T := by
  constructor
  · intro h
    obtain ⟨d,hd,he⟩ := Finset.mem_map.mp h
    have hdc : d = c := parentCrossing_injective P hP S hS root hroot he
    simpa only [hdc] using hd
  · intro h
    exact Finset.mem_map.mpr ⟨c,h,rfl⟩

theorem liftedSupport_card (T : Finset (PolygonCrossing (daughterVertex P hP.g2 S root))) :
    (liftedSupport P hP S hS root hroot T).card = T.card := Finset.card_map _

theorem liftedSupport_disjoint (T : Finset (PolygonCrossing (daughterVertex P hP.g2 S root))) :
    Disjoint S (liftedSupport P hP S hS root hroot T) := by
  apply Finset.disjoint_left.mpr
  intro c hc hd
  obtain ⟨d,_,he⟩ := Finset.mem_map.mp hd
  have he' : parentCrossing P hP S hS root hroot d = c := he
  rw [← he'] at hc
  exact parentCrossing_not_mem P hP S hS root hroot d hc

theorem liftedPairing_fixes_old_retained
    (T : Finset (PolygonCrossing (daughterVertex P hP.g2 S root)))
    (y : PolygonEvent P) (hy : retainedCorner P S y) :
    smoothingPairing P (liftedSupport P hP S hS root hroot T) y = y := by
  cases y with
  | inl e => rfl
  | inr v =>
    apply (smoothingPairing_visit_fixed_iff P _ v).mpr
    exact fun h => Finset.disjoint_left.mp (liftedSupport_disjoint P hP S hS root hroot T) hy h

theorem eventLift_pairing
    (T : Finset (PolygonCrossing (daughterVertex P hP.g2 S root)))
    (x : PolygonEvent (daughterVertex P hP.g2 S root)) :
    eventLift P hP S hS root hroot (smoothingPairing (daughterVertex P hP.g2 S root) T x) =
      smoothingPairing P (liftedSupport P hP S hS root hroot T) (eventLift P hP S hS root hroot x) := by
  cases x with
  | inl i =>
    exact (liftedPairing_fixes_old_retained P hP S hS root hroot T _
      (cornerEnumeration P hP.g2 S root i).property).symm
  | inr v =>
    have hm : (visitLift P hP S hS root hroot v).1 ∈ liftedSupport P hP S hS root hroot T ↔ v.1 ∈ T :=
      mem_liftedSupport_iff P hP S hS root hroot T v.1
    change eventLift P hP S hS root hroot
      (if v.1 ∈ T then Sum.inr (crossingVisitFlip (daughterVertex P hP.g2 S root) v) else Sum.inr v) =
      if (visitLift P hP S hS root hroot v).1 ∈ liftedSupport P hP S hS root hroot T
      then Sum.inr (crossingVisitFlip P (visitLift P hP S hS root hroot v))
      else Sum.inr (visitLift P hP S hS root hroot v)
    by_cases h : v.1 ∈ T
    · rw [if_pos h,if_pos (hm.mpr h)]
      exact congrArg Sum.inr (visitLift_flip P hP S hS root hroot v)
    · rw [if_neg h,if_neg (fun hh => h (hm.mp hh))]
      rfl

theorem eventLift_retained_union_iff
    (T : Finset (PolygonCrossing (daughterVertex P hP.g2 S root)))
    (x : PolygonEvent (daughterVertex P hP.g2 S root)) :
    retainedCorner (daughterVertex P hP.g2 S root) T x ↔
      retainedCorner P (S ∪ liftedSupport P hP S hS root hroot T) (eventLift P hP S hS root hroot x) := by
  cases x with
  | inl i =>
    have hr : retainedCorner P S (eventLift P hP S hS root hroot (Sum.inl i)) :=
      (cornerEnumeration P hP.g2 S root i).property
    have hr' : retainedCorner P (S ∪ liftedSupport P hP S hS root hroot T)
        (eventLift P hP S hS root hroot (Sum.inl i)) := by
      cases hy : eventLift P hP S hS root hroot (Sum.inl i) with
      | inl e => trivial
      | inr v =>
        rw [hy] at hr
        exact Finset.mem_union_left _ hr
    exact ⟨fun _ => hr',fun _ => True.intro⟩
  | inr v =>
    change v.1 ∈ T ↔ (visitLift P hP S hS root hroot v).1 ∈ S ∪ liftedSupport P hP S hS root hroot T
    rw [Finset.mem_union]
    have hn : (visitLift P hP S hS root hroot v).1 ∉ S :=
      parentCrossing_not_mem P hP S hS root hroot v.1
    simp only [hn,false_or]
    exact (mem_liftedSupport_iff P hP S hS root hroot T v.1).symm








end
end DirectGLSSW.DaughterPairingLift
