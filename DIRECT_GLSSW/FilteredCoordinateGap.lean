import ActiveArcRetainedEventFilter

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.FiniteFirstReturn
attribute [local instance] Classical.propDecidable

/-- Counting retained coordinates before an omitted coordinate identifies
its exact two bracketing retained indices. No order/bracket is assumed. -/
theorem filtered_coordinate_bracket {N M : ℕ} (P : Fin N → Prop)
    (e : Fin M → Fin N)
    (he : List.ofFn e = (List.ofFn (fun i : Fin N => i)).filter (fun i => decide (P i)))
    (j : Fin N) (hj : ¬P j) (m : ℕ)
    (hm : ((List.ofFn (fun i : Fin N => i)).take j.val |>.filter (fun i => decide (P i))).length=m)
    (hm0 : 0<m) (hmM : m<M) :
    (e ⟨m-1,by omega⟩).val < j.val ∧ j.val < (e ⟨m,hmM⟩).val := by
  let L := List.ofFn (fun i : Fin N => i)
  let A := (L.take j.val).filter (fun i => decide (P i))
  let B := (L.drop j.val).filter (fun i => decide (P i))
  have hAB : List.ofFn e = A ++ B := by
    rw [he]
    change L.filter _ = _
    conv_lhs => rw [← List.take_append_drop j.val L]
    exact List.filter_append _ _
  have hAm : A.length=m := hm
  have htake : (List.ofFn e).take m=A := by
    rw [hAB,← hAm,List.take_left]
  have hdrop : (List.ofFn e).drop m=B := by
    rw [hAB,← hAm,List.drop_left]
  have hleft : e ⟨m-1,by omega⟩ ∈ A := by
    rw [← htake]
    apply List.mem_take_iff_getElem.mpr
    refine ⟨m-1,?_,?_⟩
    · simp only [List.length_ofFn];omega
    · simp only [List.getElem_ofFn]
  have hright : e ⟨m,hmM⟩ ∈ B := by
    rw [← hdrop]
    apply List.mem_drop_iff_getElem.mpr
    refine ⟨0,?_,?_⟩
    · simpa using hmM
    · simp only [Nat.add_zero,List.getElem_ofFn]
  have hleft' := (List.mem_filter.mp hleft).1
  have hright' := (List.mem_filter.mp hright).1
  have hrightP : P (e ⟨m,hmM⟩) := by simpa using (List.mem_filter.mp hright).2
  obtain ⟨i,hi,hie⟩ := List.mem_take_iff_getElem.mp hleft'
  obtain ⟨k,hk,hke⟩ := List.mem_drop_iff_getElem.mp hright'
  have hie' : i=(e ⟨m-1,by omega⟩).val := by
    have hh := congrArg Fin.val hie
    simpa only [L,List.getElem_ofFn] using hh
  have hke' : j.val+k=(e ⟨m,hmM⟩).val := by
    have hh := congrArg Fin.val hke
    simpa only [L,List.getElem_ofFn] using hh
  constructor
  · omega
  · have hne : (e ⟨m,hmM⟩).val≠j.val := by
      intro h
      exact hj ((Fin.ext h) ▸ hrightP)
    omega

end DirectGLSSW.FiniteFirstReturn
