import ActiveArcChildSupportSpectator
import ActiveArcParentVisitOrder

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.CompatibleWords
open PermutationOrbits FiniteCycleOrder SingletonWords Split Cursor
attribute [local instance] Classical.propDecidable
variable {a b : ℕ} (q : Fin (a+b+2) → PlanarPoint ℝ)

/-- Actual parent events inside the cut-open complement. Its initial anchor
maps to the retained LEFT cut visit. The original initial anchor is separate. -/
def parentEventMap (_hR : Regular q) (c : Crossing q) (_hc : FirstCrossing q c)
    (hcut : c.val.2.val=a) : Event (parent q c hcut) → Event q
  | Sum.inl i => if i=0 then Sum.inr (c,false) else Sum.inl (Split.vertex i)
  | Sum.inr v => Sum.inr (parentVisitMap q c hcut v)

variable (hR : Regular q) (c : Crossing q) (hc : FirstCrossing q c) (hcut : c.val.2.val=a)

@[simp] theorem parentEventMap_start :
    parentEventMap q hR c hc hcut (start (parent q c hcut))=Sum.inr (c,false) := by
  simp [parentEventMap,start]

@[simp] theorem parentEventMap_anchor_succ (i : Fin (b+1)) :
    parentEventMap q hR c hc hcut (Sum.inl i.succ)=Sum.inl (Split.vertex i.succ) := by
  simp [parentEventMap]

@[simp] theorem parentEventMap_visit (v : Visit (parent q c hcut)) :
    parentEventMap q hR c hc hcut (Sum.inr v)=Sum.inr (parentVisitMap q c hcut v) := rfl

theorem parentEventMap_point (x : Event (parent q c hcut)) :
    eventPoint q (parentEventMap q hR c hc hcut x)=eventPoint (parent q c hcut) x := by
  cases x with
  | inl i =>
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [parentEventMap,eventPoint,parent_zero]
    · rw [parentEventMap_anchor_succ]
      exact (parent_succ q c hcut j).symm
  | inr v => exact parentCrossingToOriginal_point q hR c hcut v.1

include hR in
theorem parentCrossing_ne_cut (d : Crossing (parent q c hcut)) :
    parentCrossingToOriginal q c hcut d≠c := by
  intro he
  have hm := parentCrossingToOriginal_inParent q hR c hcut d
  rw [he] at hm
  exact crossing_not_inParent q c hcut hm

theorem parentEventMap_ne_start (x : Event (parent q c hcut)) :
    parentEventMap q hR c hc hcut x≠start q := by
  cases x with
  | inl i =>
    by_cases hi : i=0
    · simp [parentEventMap,hi,start]
    · intro he
      simp only [parentEventMap,if_neg hi,start,Sum.inl.injEq] at he
      have hv := congrArg Fin.val (Sum.inl.inj he)
      have hip := Fin.pos_iff_ne_zero.mpr hi
      simp only [Split.vertex,Fin.val_zero] at hv
      omega
  | inr v => intro he;cases he

theorem parentEventMap_injective : Function.Injective (parentEventMap q hR c hc hcut) := by
  intro x y he
  cases x with
  | inl i =>
    cases y with
    | inl j =>
      by_cases hi : i=0 <;> by_cases hj : j=0
      · exact congrArg Sum.inl (hi.trans hj.symm)
      · simp [parentEventMap,hi,hj] at he
      · simp [parentEventMap,hi,hj] at he
      · simp only [parentEventMap,if_neg hi,if_neg hj,Sum.inl.injEq] at he
        exact congrArg Sum.inl (vertex_injective (Sum.inl.inj he))
    | inr v =>
      by_cases hi : i=0
      · have hh : c=parentCrossingToOriginal q c hcut v.1 := by
          have he' : (Sum.inr (c,false) : Event q)=Sum.inr (parentVisitMap q c hcut v) := by
            simpa only [parentEventMap,if_pos hi] using he
          exact congrArg Prod.fst (Sum.inr.inj he')
        exact False.elim (parentCrossing_ne_cut q hR c hcut v.1 hh.symm)
      · simp [parentEventMap,hi] at he
  | inr v =>
    cases y with
    | inl j =>
      by_cases hj : j=0
      · have hh : parentCrossingToOriginal q c hcut v.1=c := by
          have he' : (Sum.inr (parentVisitMap q c hcut v) : Event q)=Sum.inr (c,false) := by
            simpa only [parentEventMap,if_pos hj] using he
          exact congrArg Prod.fst (Sum.inr.inj he')
        exact False.elim (parentCrossing_ne_cut q hR c hcut v.1 hh)
      · simp [parentEventMap,hj] at he
    | inr w =>
      have hh := Sum.inr.inj he
      have hd := parentCrossingToOriginal_injective q c hcut (congrArg Prod.fst hh)
      have hb := congrArg Prod.snd hh
      exact congrArg Sum.inr (Prod.ext hd hb)

end DirectGLSSW.ActiveArc.CompatibleWords
