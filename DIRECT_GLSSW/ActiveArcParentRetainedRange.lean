import ActiveArcParentEventMap

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.CompatibleWords
open PermutationOrbits FiniteCycleOrder SingletonWords Split Cursor
attribute [local instance] Classical.propDecidable
variable {a b : ℕ} (q : Fin (a+b+2) → PlanarPoint ℝ) (hR : Regular q)
variable (c : Crossing q) (hc : FirstCrossing q c) (hcut : c.val.2.val=a)

theorem parentEventMap_in_complement (x : Event (parent q c hcut)) :
    (Nonalternation.eventEnumeration q hR).symm (parentEventMap q hR c hc hcut x) ∈
      complementSide (leftRank q hR c) (rightRank q hR c) := by
  letI := eventOrder q hR.noTriple
  cases x with
  | inl i =>
    by_cases hi : i=0
    · simpa only [parentEventMap,if_pos hi] using left_not_interval q hR c
    · simp only [parentEventMap,if_neg hi]
      change (Nonalternation.eventEnumeration q hR).symm (Sum.inl (Split.vertex i)) ∉
        intervalSide (leftRank q hR c) (rightRank q hR c)
      intro hm
      have hb := (anchor_interval_iff q hR c hc.1 hcut (Split.vertex i)).mp hm
      have hp := Fin.pos_iff_ne_zero.mpr hi
      change 0<a+i.val ∧ a+i.val≤a at hb
      omega
  | inr v =>
    have hm := parentCrossingToOriginal_inParent q hR c hcut v.1
    have h0 := (cut_before_left_visit_iff q hR c hcut _).mpr hm
    have h1 := left_visit_lt_right q hR (parentCrossingToOriginal q c hcut v.1)
    have hv : (eventOrder q hR.noTriple).lt (Sum.inr (c,true))
        (Sum.inr (parentVisitMap q c hcut v)) := by
      rcases v with ⟨d,z⟩;cases z
      · exact h0
      · exact lt_trans h0 h1
    intro hh
    have hle := ((rank_interval_iff q hR c _).mp hh).2
    exact (not_lt_of_ge hle) hv

variable (S : Finset (PolygonCrossing (child q hR c hc.1 hcut)))
variable (T : Finset (Crossing (parent q c hcut)))

theorem pieceSelections_parent_mem (d : Crossing (parent q c hcut)) :
    parentCrossingToOriginal q c hcut d∈pieceSelections q hR c hc hcut S T ↔ d∈T := by
  constructor
  · intro hd
    obtain ⟨z,hz,he⟩ := Finset.mem_map.mp hd
    have hez : z=Sum.inr d := pieceCrossingToOriginal_injective q hR c hc hcut he
    rw [hez] at hz
    exact Finset.inr_mem_disjSum.mp hz
  · intro hd
    exact Finset.mem_map.mpr ⟨Sum.inr d,Finset.inr_mem_disjSum.mpr hd,rfl⟩

theorem parentEventMap_retained (x : Event (parent q c hcut)) :
    retained q (insert c (pieceSelections q hR c hc hcut S T)) (parentEventMap q hR c hc hcut x) ↔
      retained (parent q c hcut) T x := by
  cases x with
  | inl i =>
    by_cases hi : i=0
    · simp [parentEventMap,hi,retained]
    · simp [parentEventMap,hi,retained]
  | inr v =>
    change (parentCrossingToOriginal q c hcut v.1∈insert c (pieceSelections q hR c hc hcut S T)) ↔ v.1∈T
    rw [Finset.mem_insert]
    simp only [parentCrossing_ne_cut q hR c hcut v.1,false_or,pieceSelections_parent_mem]

/-- Exact retained-event range in the singleton open complement: the original
start anchor plus the actual parent retained events. Erased visits are excluded. -/
theorem retained_complement_range (x : Event q) :
    (retained q (insert c (pieceSelections q hR c hc hcut S T)) x ∧
      (Nonalternation.eventEnumeration q hR).symm x ∈ complementSide (leftRank q hR c) (rightRank q hR c)) ↔
    x=start q ∨ ∃ y : Event (parent q c hcut), retained (parent q c hcut) T y ∧
      parentEventMap q hR c hc hcut y=x := by
  constructor
  · rintro ⟨hr,hcomp⟩
    cases x with
    | inl i =>
      by_cases hi : i=0
      · left;exact congrArg Sum.inl hi
      · right
        have hip : 0 < i.val := Fin.pos_iff_ne_zero.mpr hi
        have hia : a < i.val := by
          by_contra hh
          exact hcomp ((anchor_interval_iff q hR c hc.1 hcut i).mpr ⟨hip,le_of_not_gt hh⟩)
        let j : Fin (b+2) := ⟨i.val-a,by have := i.isLt;omega⟩
        have hj : j≠0 := by intro he;have hv:=congrArg Fin.val he;simp only [j,Fin.val_zero] at hv;omega
        refine ⟨Sum.inl j,True.intro,?_⟩
        simp only [parentEventMap,if_neg hj,Sum.inl.injEq]
        apply congrArg Sum.inl
        apply Fin.ext
        change a+(i.val-a)=i.val
        omega
    | inr v =>
      right
      change v.1∈insert c (pieceSelections q hR c hc hcut S T) at hr
      rcases Finset.mem_insert.mp hr with hcutv|hsel
      · have hv0 : v.2=false := by
          cases hv : v.2
          · rfl
          · exfalso
            have hm := right_in_interval q hR c
            apply hcomp
            have he : v=(c,true) := Prod.ext hcutv hv
            rw [he]
            exact hm
        refine ⟨start (parent q c hcut),(endpoints_retained _ T).1,?_⟩
        rw [parentEventMap_start]
        exact congrArg Sum.inr (Prod.ext hcutv.symm hv0.symm)
      · obtain ⟨z,hz,he⟩ := Finset.mem_map.mp hsel
        cases z with
        | inl z =>
          exfalso
          have hm := child_visit_in_interval q hR c hc hcut z v.2
          apply hcomp
          change (Nonalternation.eventEnumeration q hR).symm (Sum.inr (v.1,v.2))∈_
          rw [← he]
          exact hm
        | inr z =>
          refine ⟨Sum.inr (z,v.2),Finset.inr_mem_disjSum.mp hz,?_⟩
          exact congrArg Sum.inr (Prod.ext he rfl)
  · rintro (rfl|⟨y,hy,rfl⟩)
    · refine ⟨(endpoints_retained q _).1,?_⟩
      rw [← eventEnumeration_zero q hR]
      change (Nonalternation.eventEnumeration q hR).symm (Nonalternation.eventEnumeration q hR (eventZero q))∉_
      rw [Equiv.symm_apply_apply]
      intro hh
      exact (Nat.not_lt_zero _) hh.1
    · exact ⟨(parentEventMap_retained q hR c hc hcut S T y).mpr hy,parentEventMap_in_complement q hR c hc hcut y⟩

end DirectGLSSW.ActiveArc.CompatibleWords
