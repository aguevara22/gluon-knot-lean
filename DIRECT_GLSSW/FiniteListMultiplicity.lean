import Mathlib.Data.Finset.Dedup
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.List.Count

set_option autoImplicit false
namespace DirectGLSSW.HOMFLY.ArcSubdivision

private theorem count_flatMap_replicate_of_nodup {ι : Type*} [DecidableEq ι]
    (f : ι → ℕ) (l : List ι) (hnodup : l.Nodup) (i : ι) :
    (l.flatMap (fun j => List.replicate (f j) j)).count i =
      if i ∈ l then f i else 0 := by
  induction l with
  | nil => simp
  | cons a tail ih =>
      have hnot : a ∉ tail := List.nodup_cons.mp hnodup |>.1
      have htail := ih (List.nodup_cons.mp hnodup).2
      simp only [List.flatMap_cons, List.count_append, List.count_replicate]
      by_cases hia : i = a
      · subst i
        simpa [hnot] using htail
      · have hai : a ≠ i := Ne.symm hia
        simp [hia, hai, htail]

/-- A finite list whose exact multiplicity of each label is prescribed by `f`. -/
theorem exists_list_count {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : ι → ℕ) : ∃ l : List ι, ∀ i, l.count i = f i := by
  classical
  let l : List ι := Finset.univ.toList.flatMap (fun j => List.replicate (f j) j)
  refine ⟨l, ?_⟩
  intro i
  have hc := count_flatMap_replicate_of_nodup f Finset.univ.toList
    (Finset.nodup_toList _) i
  have hi : i ∈ Finset.univ.toList := by simp
  simpa [l, hi] using hc

end DirectGLSSW.HOMFLY.ArcSubdivision
