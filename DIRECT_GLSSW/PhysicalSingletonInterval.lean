import ActiveArcSingletonWords
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.PhysicalKnotSplit
open PermutationOrbits FiniteCycleOrder SingletonWords Nonalternation
attribute [local instance] Classical.propDecidable
variable {a b : ℕ} (q : Fin (a+b+2) → PlanarPoint ℝ) (hR : Regular q) (c : Crossing q)

def intervalCorners (i : Fin (c.val.2.val-c.val.1.val+1)) : Event q :=
  if hi : i.val<c.val.2.val-c.val.1.val then
    Sum.inl ⟨c.val.1.val+i.val+1,by have := c.val.2.isLt;omega⟩
  else Sum.inr (c,true)

theorem anchor_in_interval (i : Fin (a+b+2)) :
    (eventEnumeration q hR).symm (Sum.inl i) ∈
      intervalSide (leftRank q hR c) (rightRank q hR c) ↔
        c.val.1.val < i.val ∧ i.val ≤ c.val.2.val := by
  letI := eventOrder q hR.noTriple
  rw [rank_interval_iff]
  simp only [← not_lt]
  rw [event_lt_iff,event_lt_iff]
  have hl := (leftParameter_spec q c).1
  have hr := (rightParameter_spec q c).1
  change ((c.val.1.val < i.val ∨ c.val.1.val=i.val ∧ leftParameter q c < (0:ℝ)) ∧
    ¬ (c.val.2.val < i.val ∨ c.val.2.val=i.val ∧ rightParameter q c < (0:ℝ))) ↔ _
  simp [not_lt_of_ge (le_of_lt hl),not_lt_of_ge (le_of_lt hr)]

theorem intervalCorners_sorted : letI := eventOrder q hR.noTriple;
    (List.ofFn (intervalCorners q c)).Sorted (· < ·) := by
  letI := eventOrder q hR.noTriple
  apply List.sorted_lt_ofFn_iff.mpr
  intro i j hij
  have hi := i.isLt
  have hj := j.isLt
  have hij' : i.val<j.val := hij
  have hlr : c.val.1.val<c.val.2.val := c.property.1
  unfold intervalCorners
  split_ifs with hiA hjA
  · exact (event_lt_iff q hR.noTriple _ _).mpr (Or.inl (by simpa [edgeTag] using (show c.val.1.val+i.val+1<c.val.1.val+j.val+1 by omega)))
  · apply (event_lt_iff q hR.noTriple _ _).mpr
    have hr := (rightParameter_spec q c).1
    change c.val.1.val+i.val+1<c.val.2.val ∨ c.val.1.val+i.val+1=c.val.2.val ∧ (0:ℝ)<rightParameter q c
    rcases lt_or_eq_of_le (show c.val.1.val+i.val+1≤c.val.2.val by omega) with hh|hh
    · exact Or.inl hh
    · exact Or.inr ⟨hh,hr⟩
  · omega
  · omega

theorem intervalCorners_mem (x : Event q) :
    x ∈ List.ofFn (intervalCorners q c) ↔
      (eventEnumeration q hR).symm x ∈ intervalSide (leftRank q hR c) (rightRank q hR c) ∧ retained q {c} x := by
  have hlr : c.val.1.val<c.val.2.val := c.property.1
  cases x with
  | inl k =>
    rw [anchor_in_interval q hR c]
    simp only [retained,true_and,and_true]
    constructor
    · intro hx
      obtain ⟨i,hi⟩:=List.mem_ofFn.mp hx
      by_cases hia : i.val<c.val.2.val-c.val.1.val
      · simp only [intervalCorners,dif_pos hia] at hi
        have hk := congrArg Fin.val (Sum.inl.inj hi)
        dsimp at hk
        omega
      · simp only [intervalCorners,dif_neg hia] at hi
        cases hi
    · intro hk
      let i : Fin (c.val.2.val-c.val.1.val+1) := ⟨k.val-c.val.1.val-1,by omega⟩
      refine List.mem_ofFn.mpr ⟨i,?_⟩
      have hia : i.val<c.val.2.val-c.val.1.val := by dsimp [i];omega
      simp only [intervalCorners,dif_pos hia]
      congr 1
      apply Fin.ext
      dsimp [i]
      omega
  | inr v =>
    rcases v with ⟨d,z⟩
    constructor
    · intro hx
      obtain ⟨i,hi⟩:=List.mem_ofFn.mp hx
      by_cases hia : i.val<c.val.2.val-c.val.1.val
      · simp only [intervalCorners,dif_pos hia] at hi
        cases hi
      · simp only [intervalCorners,dif_neg hia] at hi
        have hv:=Sum.inr.inj hi
        cases hv
        exact ⟨right_in_interval q hR c,by simp [retained]⟩
    · intro hx
      have hd : d=c := by simpa [retained] using hx.2
      subst d
      cases z with
      | false => exact (left_not_interval q hR c hx.1).elim
      | true => exact List.mem_ofFn.mpr ⟨⟨c.val.2.val-c.val.1.val,by omega⟩,by simp [intervalCorners]⟩

theorem interval_filtered_corners :
    (List.ofFn (intervalEvents q hR c)).filter (fun z => decide (retained q {c} z)) =
      List.ofFn (intervalCorners q c) := by
  letI := eventOrder q hR.noTriple
  apply List.Sorted.eq_of_mem_iff ((intervalEvents_sorted q hR c).filter _) (intervalCorners_sorted q hR c)
  intro x
  rw [List.mem_filter,intervalEvents_mem,intervalCorners_mem q hR c]
  simp

/-- Every actual singleton closed word is the crossing followed by the literal
original anchors strictly after its left carrier and through its right carrier. -/
theorem singleton_closed_word_offset :
    List.ofFn (RetainedWords.vertex q hR {c} (Sum.inr (c,true))) =
      crossingPoint q c :: List.ofFn (fun i : Fin (c.val.2.val-c.val.1.val) =>
        q ⟨c.val.1.val+i.val+1,by have := c.val.2.isLt;omega⟩) := by
  let r := intervalEvents q hR c ⟨0,(daughterLengths_pos _ _ (rank_lt q hR c)).1⟩
  have hcycle : (incoming q hR.noTriple {c}).SameCycle r (Sum.inr (c,true)) := by
    apply (mem_orbitWord_iff _ _ _).mp
    rw [interval_orbitWord]
    exact (intervalEvents_mem q hR c _).mpr (right_in_interval q hR c)
  have hrot := DaughterRootRotation.orbitWord_isRotated_of_sameCycle
    (incoming q hR.noTriple {c}) (Sum.inr (c,true)) r hcycle.symm
  have hf := DaughterRootRotation.listIsRotated_filter hrot (fun z => decide (retained q {c} z))
  rw [interval_orbitWord,interval_filtered_corners q hR c] at hf
  let anchors := List.ofFn (fun i : Fin (c.val.2.val-c.val.1.val) =>
    (Sum.inl ⟨c.val.1.val+i.val+1,by have := c.val.2.isLt;omega⟩ : Event q))
  have hc : List.ofFn (intervalCorners q c) = anchors.concat (Sum.inr (c,true)) := by
    rw [List.ofFn_succ']
    have hlast : intervalCorners q c (Fin.last (c.val.2.val-c.val.1.val))=Sum.inr (c,true) := by simp [intervalCorners]
    rw [hlast]
    congr 1
    apply congrArg List.ofFn
    funext i
    simp [intervalCorners,i.isLt,anchors]
  rw [hc] at hf
  have hr : anchors.concat (Sum.inr (c,true)) ~r Sum.inr (c,true)::anchors :=
    by simpa only [List.concat_eq_append] using (List.isRotated_concat (Sum.inr (c,true) : Event q) anchors)
  have he : (orbitWord (incoming q hR.noTriple {c}) (Sum.inr (c,true))).filter
      (fun z => decide (retained q {c} z)) = Sum.inr (c,true)::anchors := by
    apply nodup_rotated_eq_of_head ((orbitWord_nodup _ _).filter _) (hf.trans hr)
    rw [filtered_head q hR {c} (Sum.inr (c,true)) (by simp [retained])]
    rfl
  rw [retainedWord_eq_filtered,he,List.map_cons,List.map_ofFn]
  rfl
end DirectGLSSW.ActiveArc.PhysicalKnotSplit
