import DirectGLSSW.OrbitWordPrerequisite
import Mathlib.Data.List.Chain
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.OfFn

set_option autoImplicit false

namespace DirectGLSSW

/-- A nodup closed successor chain lists exactly the orbit based at its first element. -/
theorem orbitWord_eq_list_of_closed_chain
    {α : Type*} [Fintype α] (p : Equiv.Perm α) (root : α) (tail : List α)
    (hnodup : (root :: tail).Nodup)
    (hchain : List.Chain' (fun a b => p a = b) ((root :: tail) ++ [root])) :
    PermutationOrbits.orbitWord p root = root :: tail := by
  let xs := root :: tail
  have hpos : 0 < xs.length := by simp [xs]
  have hinj : Function.Injective xs.get := List.nodup_iff_injective_get.mp hnodup
  have hstep (i : Fin xs.length) : p (xs.get i) = xs.get (cyclicSuccessor i) := by
    have hi := i.isLt
    have hbound : i.val < (xs ++ [root]).length - 1 := by simpa using hi
    have hc := (List.chain'_iff_get.mp hchain) i.val hbound
    change p ((xs ++ [root]).get ⟨i.val, _⟩) =
      (xs ++ [root]).get ⟨i.val+1, _⟩ at hc
    have hs : (cyclicSuccessor i).val =
        if i.val+1 < xs.length then i.val+1 else 0 := by
      unfold cyclicSuccessor
      rw [cyclicVertexIndex_val i (k := 0) hpos]
      simp only [Nat.add_zero]
      split_ifs <;> omega
    by_cases hnext : i.val+1 < xs.length
    · have heq : cyclicSuccessor i = ⟨i.val+1,hnext⟩ := by
        apply Fin.ext
        simp only [hs, if_pos hnext, Fin.val_mk]
      rw [heq]
      simpa only [List.get_eq_getElem, List.getElem_append_left hi,
        List.getElem_append_left hnext] using hc
    · have hend : i.val+1 = xs.length := by omega
      have heq : cyclicSuccessor i = ⟨0,hpos⟩ := by
        apply Fin.ext
        simp only [hs, if_neg hnext, Fin.val_mk]
      rw [heq]
      change p (xs.get i) = root
      simpa [List.get_eq_getElem, List.getElem_append, hi, hnext, hend] using hc
  have hword := orbitWord_eq_of_injective_cyclicSuccessor p hpos xs.get hinj hstep
  simpa only [List.ofFn_get] using hword


end DirectGLSSW
