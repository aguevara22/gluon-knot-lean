import DirectGLSSW.OrderedEventSuccessor
import DirectGLSSW.PermutationInsertionWords

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.OrderedInsertion
open PermutationOrbits
variable {A B : Type*} [LinearOrder A] [Fintype A] [LinearOrder B] [Fintype B]
variable (a : A) (b : B) (E : A ≃o {y : B // y≠b})
variable (ha : ∀ x : A, a≤x) (hb : ∀ y : B, b≤y)
include ha hb

omit [Fintype A] in
theorem successor_extra : orderedCyclicSuccessor B b=(E a).val := by
  apply orderedCyclicSuccessor_eq_of_order_spec
  left
  refine ⟨lt_of_le_of_ne (hb _) (Ne.symm (E a).property),?_⟩
  intro z hz
  have hzb : z≠b := ne_of_gt hz
  have hh := E.monotone (ha (E.symm ⟨z,hzb⟩))
  simpa only [OrderIso.apply_symm_apply] using hh

theorem successor_image (x : A) :
    orderedCyclicSuccessor B (E x).val=
      if orderedCyclicSuccessor A x=a then b else (E (orderedCyclicSuccessor A x)).val := by
  by_cases he : orderedCyclicSuccessor A x=a
  · rw [if_pos he]
    apply orderedCyclicSuccessor_eq_of_order_spec
    right
    refine ⟨?_,hb⟩
    have hmax : ∀ z : A, z≤x := by
      rcases orderedCyclicSuccessor_order_spec A x with ⟨hlt,_⟩|⟨hm,_⟩
      · rw [he] at hlt
        exact False.elim ((not_lt_of_ge (ha x)) hlt)
      · exact hm
    intro z
    by_cases hz : z=b
    · subst z;exact hb _
    · have hh := E.monotone (hmax (E.symm ⟨z,hz⟩))
      simpa only [OrderIso.apply_symm_apply] using hh
  · rw [if_neg he]
    apply orderedCyclicSuccessor_eq_of_order_spec
    left
    have hspec : x<orderedCyclicSuccessor A x ∧
        ∀ z : A, x<z → orderedCyclicSuccessor A x≤z := by
      rcases orderedCyclicSuccessor_order_spec A x with hs|⟨_,hm⟩
      · exact hs
      · exact False.elim (he (le_antisymm (hm a) (ha _)))
    refine ⟨E.strictMono hspec.1,?_⟩
    intro z hz
    have hzb : z≠b := by
      intro hh;subst z
      exact (not_lt_of_ge (hb _)) hz
    have hlt : x<E.symm ⟨z,hzb⟩ := by
      have hh : E x < (⟨z,hzb⟩ : {y : B // y≠b}) := hz
      simpa only [OrderIso.symm_apply_apply] using E.symm.strictMono hh
    have hh := E.monotone (hspec.2 _ hlt)
    simpa only [OrderIso.apply_symm_apply] using hh

/-- A least extra anchor inserts one literal orbit letter after composing with
pairings that fix that anchor and agree on the retained physical carrier. -/
theorem paired_orbitWord (t : Equiv.Perm A) (u : Equiv.Perm B)
    (hfix : u b=b) (hpair : ∀ x : A, u (E x).val=(E (t x)).val) :
    orbitWord (orderedCyclicSuccessor B*u) b=
      b :: (orbitWord (orderedCyclicSuccessor A*t) a).map (fun x => (E x).val) := by
  apply PermutationInsertion.inserted_orbitWord _ _ a b E.toEquiv
  · change orderedCyclicSuccessor B (u b)=(E a).val
    rw [hfix]
    exact successor_extra a b E ha hb
  · intro x
    change orderedCyclicSuccessor B (u (E x).val)=_
    rw [hpair]
    simpa only [Equiv.Perm.mul_apply] using successor_image a b E ha hb (t x)

end DirectGLSSW.OrderedInsertion
