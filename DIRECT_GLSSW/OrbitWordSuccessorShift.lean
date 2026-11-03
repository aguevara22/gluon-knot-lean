import ActiveArcUnsmoothingSwap
import DirectGLSSW.OrbitWordPrerequisite
import Mathlib.Data.List.Rotate

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace DirectGLSSW.PermutationOrbits
open DirectGLSSW
variable {A : Type*} [Fintype A]

/-- The actual finite orbit list begins with its specified root. -/
theorem orbitWord_head_eq (p : Equiv.Perm A) (s : A) : (orbitWord p s).head? = some s := by
  have hp : 0 < Fintype.card (Fibre p (componentOf p s)) :=
    Fintype.card_pos_iff.mpr ⟨⟨s,rfl⟩⟩
  simp [orbitWord,List.head?_eq_getElem?,hp,orbitEnumeration_zero]

theorem orbitWord_cons_tail (p : Equiv.Perm A) (s : A) :
    orbitWord p s = s :: (orbitWord p s).tail := by
  have hn := orbitWord_nonempty p s
  have hh : (orbitWord p s).head hn = s := by
    rw [List.head_eq_getElem_zero]
    simp [orbitWord,orbitEnumeration_zero]
  calc
    orbitWord p s = (orbitWord p s).head hn :: (orbitWord p s).tail :=
      (List.head_cons_tail _ hn).symm
    _ = s :: (orbitWord p s).tail := by rw [hh]

/-- Advancing the root by its actual successor rotates its entire finite
orbit word by exactly one position, including singleton cycles. -/
theorem orbitWord_successor_rotate (p : Equiv.Perm A) (s : A) :
    orbitWord p (p s) = (orbitWord p s).rotate 1 := by
  let N := Fintype.card (Fibre p (componentOf p s))
  have hN : 0 < N := Fintype.card_pos_iff.mpr ⟨⟨s,rfl⟩⟩
  let g : Fin N → A := fun i => (orbitEnumeration p s (cyclicSuccessorPerm N i)).val
  have hg : Function.Injective g :=
    Subtype.val_injective.comp ((orbitEnumeration p s).injective.comp (cyclicSuccessorPerm N).injective)
  have hs (i : Fin N) : p (g i) = g (cyclicSuccessor i) := by
    simpa only [g,cyclicSuccessorPerm_apply,fibrePerm_apply_val] using
      (congrArg Subtype.val (orbitEnumeration_successor p s (cyclicSuccessorPerm N i))).symm
  have hzero : g ⟨0,hN⟩ = p s := by
    dsimp only [g]
    rw [orbitEnumeration_successor]
    simp only [fibrePerm_apply_val]
    congr 1
  have hw := orbitWord_eq_of_injective_cyclicSuccessor p hN g hg hs
  rw [hzero] at hw
  rw [hw]
  apply List.ext_getElem
  · simp [orbitWord,N]
  · intro i hi hj
    rw [List.getElem_ofFn,List.getElem_rotate]
    simp only [g,orbitWord,List.getElem_ofFn,List.length_ofFn,cyclicSuccessorPerm_apply,cyclicSuccessor,N]
    congr 2

theorem orbitWord_successor_tail (p : Equiv.Perm A) (s : A) :
    orbitWord p (p s) = (orbitWord p s).tail ++ [s] := by
  rw [orbitWord_successor_rotate,orbitWord_cons_tail p s,List.rotate_cons_succ,List.rotate_zero]
  rfl

theorem orbitWord_first_two (p : Equiv.Perm A) (s a : A) (hsa : s ≠ a) (hs : p s=a) :
    orbitWord p s = s :: a :: (orbitWord p s).drop 2 := by
  have hc := orbitWord_cons_tail p s
  have ht := orbitWord_successor_tail p s
  rw [hs] at ht
  cases he : (orbitWord p s).tail with
  | nil =>
    have hh := congrArg List.head? ht
    simp only [he,List.nil_append,orbitWord_head_eq,List.head?_cons,Option.some.injEq] at hh
    exact False.elim (hsa hh.symm)
  | cons x xs =>
    have hh := congrArg List.head? ht
    simp only [he,List.cons_append,orbitWord_head_eq,List.head?_cons,Option.some.injEq] at hh
    subst x
    rw [hc,he]
    rfl

end DirectGLSSW.PermutationOrbits
