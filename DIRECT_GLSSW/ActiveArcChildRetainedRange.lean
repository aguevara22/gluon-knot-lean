import ActiveArcChildEventMap

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.CompatibleWords
open PermutationOrbits FiniteCycleOrder SingletonWords Split Cursor
attribute [local instance] Classical.propDecidable
variable {a b : ℕ} (q : Fin (a+b+2) → PlanarPoint ℝ) (hR : Regular q)
variable (c : Crossing q) (hc : FirstCrossing q c) (hcut : c.val.2.val=a)
variable (S : Finset (PolygonCrossing (child q hR c hc.1 hcut)))
variable (T : Finset (Crossing (parent q c hcut)))

theorem pieceSelections_child_mem (d : PolygonCrossing (child q hR c hc.1 hcut)) :
    childCrossingToOriginal q hR c hc.1 hcut d∈pieceSelections q hR c hc hcut S T ↔ d∈S := by
  constructor
  · intro hd
    obtain ⟨z,hz,he⟩ := Finset.mem_map.mp hd
    have hez : z=Sum.inl d := pieceCrossingToOriginal_injective q hR c hc hcut he
    rw [hez] at hz
    exact Finset.inl_mem_disjSum.mp hz
  · intro hd
    exact Finset.mem_map.mpr ⟨Sum.inl d,Finset.inl_mem_disjSum.mpr hd,rfl⟩

theorem childEventMap_retained (x : PolygonEvent (child q hR c hc.1 hcut)) :
    retained q (insert c (pieceSelections q hR c hc hcut S T)) (childEventMap q hR c hc hcut x) ↔
      DaughterFirstReturn.retainedCorner (child q hR c hc.1 hcut) S x := by
  cases x with
  | inl i =>
    by_cases hi : i=0
    · simp [childEventMap,hi,retained,DaughterFirstReturn.retainedCorner]
    · simp [childEventMap,hi,retained,DaughterFirstReturn.retainedCorner]
  | inr v =>
    change (childCrossingToOriginal q hR c hc.1 hcut v.1∈insert c (pieceSelections q hR c hc hcut S T)) ↔ v.1∈S
    rw [Finset.mem_insert]
    simp only [childCrossing_ne_cut q hR c hc hcut v.1,false_or,pieceSelections_child_mem]

/-- The actual child retained events exhaust exactly the actual retained
singleton interval, including its right cut visit and no extra closure site. -/
theorem retained_interval_range (x : Event q) :
    (retained q (insert c (pieceSelections q hR c hc hcut S T)) x ∧
      (Nonalternation.eventEnumeration q hR).symm x ∈ intervalSide (leftRank q hR c) (rightRank q hR c)) ↔
    ∃ y : PolygonEvent (child q hR c hc.1 hcut),
      DaughterFirstReturn.retainedCorner (child q hR c hc.1 hcut) S y ∧
      childEventMap q hR c hc hcut y=x := by
  constructor
  · rintro ⟨hr,hint⟩
    cases x with
    | inl i =>
      have hb := (anchor_interval_iff q hR c hc.1 hcut i).mp hint
      let j : Fin (a+1) := ⟨i.val,by omega⟩
      have hj : j≠0 := by
        intro he;have hv:=congrArg Fin.val he
        change i.val=0 at hv;omega
      refine ⟨Sum.inl j,True.intro,?_⟩
      rw [childEventMap_anchor q hR c hc hcut j hj]
      exact congrArg Sum.inl (Fin.ext rfl)
    | inr v =>
      change v.1∈insert c (pieceSelections q hR c hc hcut S T) at hr
      rcases Finset.mem_insert.mp hr with hcutv|hsel
      · have hv1 : v.2=true := by
          cases hv : v.2
          · exfalso
            have hn := left_not_interval q hR c
            apply hn
            have he : v=(c,false) := Prod.ext hcutv hv
            simpa only [he] using hint
          · rfl
        refine ⟨Sum.inl 0,True.intro,?_⟩
        rw [childEventMap_zero]
        exact congrArg Sum.inr (Prod.ext hcutv.symm hv1.symm)
      · obtain ⟨z,hz,he⟩ := Finset.mem_map.mp hsel
        cases z with
        | inl z =>
          refine ⟨Sum.inr (z,v.2),Finset.inl_mem_disjSum.mp hz,?_⟩
          exact congrArg Sum.inr (Prod.ext he rfl)
        | inr z =>
          exfalso
          have hn := parentEventMap_in_complement q hR c hc hcut (Sum.inr (z,v.2))
          apply hn
          change (Nonalternation.eventEnumeration q hR).symm
            (Sum.inr (parentCrossingToOriginal q c hcut z,v.2))∈_
          change parentCrossingToOriginal q c hcut z=v.1 at he
          rw [he]
          exact hint
  · rintro ⟨y,hy,rfl⟩
    exact ⟨(childEventMap_retained q hR c hc hcut S T y).mpr hy,
      childEventMap_in_interval q hR c hc hcut y⟩

abbrev ChildRetained := {x : PolygonEvent (child q hR c hc.1 hcut) //
  DaughterFirstReturn.retainedCorner (child q hR c hc.1 hcut) S x}
abbrev IntervalRetained := {x : Event q //
  retained q (insert c (pieceSelections q hR c hc hcut S T)) x ∧
    (Nonalternation.eventEnumeration q hR).symm x∈intervalSide (leftRank q hR c) (rightRank q hR c)}

/-- This actual event equivalence is not an increasing linear order map:
child anchor zero maps to the interval maximum, so cyclic order is required. -/
def childRetainedEquiv : ChildRetained q hR c hc hcut S ≃ IntervalRetained q hR c hc hcut S T :=
  Equiv.ofBijective (fun x => ⟨childEventMap q hR c hc hcut x.val,
    (childEventMap_retained q hR c hc hcut S T x.val).mpr x.property,
    childEventMap_in_interval q hR c hc hcut x.val⟩) ⟨by
      intro x y he
      apply Subtype.ext
      exact childEventMap_injective q hR c hc hcut (congrArg Subtype.val he),by
      intro y
      obtain ⟨x,hx,he⟩ := (retained_interval_range q hR c hc hcut S T y.val).mp y.property
      exact ⟨⟨x,hx⟩,Subtype.ext he⟩⟩

@[simp] theorem childRetainedEquiv_val (x : ChildRetained q hR c hc hcut S) :
    (childRetainedEquiv q hR c hc hcut S T x).val=childEventMap q hR c hc hcut x.val := rfl

end DirectGLSSW.ActiveArc.CompatibleWords
