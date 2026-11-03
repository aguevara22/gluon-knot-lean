import ActiveArcParentClosedAuxiliary

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.CompatibleWords
open PermutationOrbits FiniteCycleOrder SingletonWords Split Cursor
attribute [local instance] Classical.propDecidable
variable {a b : ℕ} (q : Fin (a+b+2) → PlanarPoint ℝ) (hR : Regular q)
variable (c : Crossing q) (hc : FirstCrossing q c) (hcut : c.val.2.val=a)

/-- Actual cyclic child labels. The anchor at c is the original RIGHT cut
visit, at the last event of the singleton interval. Its cyclic closing edge
is the actual prefix of the original crossed edge. -/
def childEventMap : PolygonEvent (child q hR c hc.1 hcut) → Event q
  | Sum.inl i => if i=0 then Sum.inr (c,true) else Sum.inl (childVertex i)
  | Sum.inr v => Sum.inr (childVisitMap q hR c hc.1 hcut v)

@[simp] theorem childEventMap_zero :
    childEventMap q hR c hc hcut (Sum.inl 0)=Sum.inr (c,true) := by
  simp [childEventMap]

@[simp] theorem childEventMap_anchor (i : Fin (a+1)) (hi : i≠0) :
    childEventMap q hR c hc hcut (Sum.inl i)=Sum.inl (childVertex i) := by
  simp [childEventMap,hi]

@[simp] theorem childEventMap_visit (v : CrossingVisit (child q hR c hc.1 hcut)) :
    childEventMap q hR c hc hcut (Sum.inr v)=Sum.inr (childVisitMap q hR c hc.1 hcut v) := rfl

theorem childEventMap_point (x : PolygonEvent (child q hR c hc.1 hcut)) :
    eventPoint q (childEventMap q hR c hc hcut x)=
      polygonEventPoint (child q hR c hc.1 hcut) x := by
  cases x with
  | inl i =>
    by_cases hi : i=0
    · subst i;simp [childEventMap,eventPoint,polygonEventPoint,child_zero]
    · rw [childEventMap_anchor q hR c hc hcut i hi]
      exact (child_nonzero q hR c hc.1 hcut i hi).symm
  | inr v => exact childCrossingToOriginal_point q hR c hc.1 hcut v.1

theorem childCrossing_ne_cut (d : PolygonCrossing (child q hR c hc.1 hcut)) :
    childCrossingToOriginal q hR c hc.1 hcut d≠c := by
  intro he
  have hm := childCrossingToOriginal_inChild q hR c hc.1 hcut d
  rw [he] at hm
  exact crossing_not_inChild q c hc.1 hm

theorem childEventMap_injective : Function.Injective (childEventMap q hR c hc hcut) := by
  intro x y he
  cases x with
  | inl i =>
    cases y with
    | inl j =>
      by_cases hi : i=0 <;> by_cases hj : j=0
      · exact congrArg Sum.inl (hi.trans hj.symm)
      · simp [childEventMap,hi,hj] at he
      · simp [childEventMap,hi,hj] at he
      · have hh : childVertex (b:=b) i=childVertex j := by
          exact Sum.inl.inj (by simpa only [childEventMap,if_neg hi,if_neg hj] using he)
        have hv : i.val=j.val := congrArg (fun z : Fin (a+b+2) => z.val) hh
        exact congrArg Sum.inl (Fin.ext hv)
    | inr v =>
      by_cases hi : i=0
      · have hh : c=childCrossingToOriginal q hR c hc.1 hcut v.1 := by
          have he' : (Sum.inr (c,true) : Event q)=Sum.inr (childVisitMap q hR c hc.1 hcut v) := by
            simpa only [childEventMap,if_pos hi] using he
          exact congrArg Prod.fst (Sum.inr.inj he')
        exact False.elim (childCrossing_ne_cut q hR c hc hcut v.1 hh.symm)
      · simp [childEventMap,hi] at he
  | inr v =>
    cases y with
    | inl j =>
      by_cases hj : j=0
      · have hh : childCrossingToOriginal q hR c hc.1 hcut v.1=c := by
          have he' : (Sum.inr (childVisitMap q hR c hc.1 hcut v) : Event q)=Sum.inr (c,true) := by
            simpa only [childEventMap,if_pos hj] using he
          exact congrArg Prod.fst (Sum.inr.inj he')
        exact False.elim (childCrossing_ne_cut q hR c hc hcut v.1 hh)
      · simp [childEventMap,hj] at he
    | inr w =>
      have hh := Sum.inr.inj he
      have hd := childCrossingToOriginal_injective q hR c hc.1 hcut (congrArg Prod.fst hh)
      have hb : v.2=w.2 := congrArg (fun z : Visit q => z.2) hh
      exact congrArg Sum.inr (Prod.ext hd hb)

theorem childEventMap_in_interval (x : PolygonEvent (child q hR c hc.1 hcut)) :
    (Nonalternation.eventEnumeration q hR).symm (childEventMap q hR c hc hcut x) ∈
      intervalSide (leftRank q hR c) (rightRank q hR c) := by
  cases x with
  | inl i =>
    by_cases hi : i=0
    · simpa only [childEventMap,if_pos hi] using right_in_interval q hR c
    · rw [childEventMap_anchor q hR c hc hcut i hi]
      apply (anchor_interval_iff q hR c hc.1 hcut (childVertex i)).mpr
      change (0 : ℕ) < i.val ∧ i.val ≤ a
      exact ⟨Fin.pos_iff_ne_zero.mpr hi,Nat.le_of_lt_succ i.isLt⟩
  | inr v => exact child_visit_in_interval q hR c hc hcut v.1 v.2

end DirectGLSSW.ActiveArc.CompatibleWords
