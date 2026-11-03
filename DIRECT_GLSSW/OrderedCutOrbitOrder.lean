import OrderedCutInterval

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace DirectGLSSW.PermutationOrbits
open Equiv
attribute [local instance] Classical.propDecidable
variable {α : Type*} [LinearOrder α] [Fintype α]

/-- Away from the root b, the actual orbit coordinates of the middle cut
component agree strictly with the original linear order. -/
theorem orderedCut_orbitPosition_lt_iff (a b : α) (hab : a < b)
    (x y : Fibre (orderedCyclicSuccessor α * swap a b)
      (componentOf (orderedCyclicSuccessor α * swap a b) b))
    (hx : x.val ≠ b) (hy : y.val ≠ b) :
    ((orbitEnumeration (orderedCyclicSuccessor α * swap a b) b).symm x).val <
      ((orbitEnumeration (orderedCyclicSuccessor α * swap a b) b).symm y).val ↔
    x.val < y.val := by
  let p := orderedCyclicSuccessor α * swap a b
  let N := Fintype.card (Fibre p (componentOf p b))
  let e := orbitEnumeration p b
  have hN : 0 < N := Fintype.card_pos_iff.mpr ⟨⟨b,rfl⟩⟩
  let z : Fin N := ⟨0,hN⟩
  have hz : (e z).val = b := by simp [e,z,orbitEnumeration_apply_val]
  have hrange (v : Fibre p (componentOf p b)) : a < v.val ∧ v.val ≤ b :=
    (orderedCut_sameCycle_right_iff a b v.val hab).mp
      (((componentOf_eq_iff p v.val b).mp v.property).symm)
  have hstep (n : ℕ) (hn : 0 < n) (hnN : n+1 < N) :
      (e ⟨n,by omega⟩).val < (e ⟨n+1,hnN⟩).val := by
    let i : Fin N := ⟨n,by omega⟩
    have hi : (e i).val ≠ b := by
      intro h
      have hif : e i = e z := Subtype.ext (h.trans hz.symm)
      have hv := congrArg Fin.val (e.injective hif)
      change n = 0 at hv
      omega
    have hr := hrange (e i)
    have hneq : (e i).val ≠ a := ne_of_gt hr.1
    have hp : (e i).val < orderedCyclicSuccessor α (e i).val := by
      rcases orderedCyclicSuccessor_order_spec α (e i).val with hh | hh
      · exact hh.1
      · exact False.elim (hi (le_antisymm hr.2 (hh.1 b)))
    have hnext : (e ⟨n+1,hnN⟩).val = p (e i).val := by
      simp only [e,orbitEnumeration_apply_val,pow_succ',Perm.mul_apply]
      rfl
    rw [hnext]
    change (e i).val < (orderedCyclicSuccessor α * swap a b) (e i).val
    rw [mul_swap_apply_of_ne _ hneq hi]
    exact hp
  have hmono : ∀ (n : ℕ) (hnN : n < N) (i : Fin N),
      0 < i.val → i.val < n → (e i).val < (e ⟨n,hnN⟩).val := by
    intro n
    induction n with
    | zero => intro hnN i hi hil; omega
    | succ n ih =>
      intro hnN i hi hil
      have hn : n < N := by omega
      by_cases he : i.val = n
      · have hie : i = (⟨n,hn⟩ : Fin N) := Fin.ext he
        rw [hie]
        exact hstep n (by omega) hnN
      · exact (ih hn i hi (by omega)).trans (hstep n (by omega) hnN)
  let ix := e.symm x
  let iy := e.symm y
  have hix : (e ix).val = x.val := congrArg Subtype.val (e.apply_symm_apply x)
  have hiy : (e iy).val = y.val := congrArg Subtype.val (e.apply_symm_apply y)
  have hpos (v : Fibre p (componentOf p b)) (hv : v.val ≠ b) :
      0 < (e.symm v).val := by
    by_contra hn
    have hh : e.symm v = z := Fin.ext (by change _ = 0; omega)
    have he := congrArg Subtype.val (e.apply_symm_apply v)
    rw [hh,hz] at he
    exact hv he.symm
  have hpx := hpos x hx
  have hpy := hpos y hy
  change ix.val < iy.val ↔ x.val < y.val
  constructor
  · intro h
    have hh := hmono iy.val iy.isLt ix hpx h
    simpa only [hix,hiy] using hh
  · intro h
    by_contra hn
    rcases lt_or_eq_of_le (le_of_not_gt hn) with hlt | heq
    · have hh := hmono ix.val ix.isLt iy hpy hlt
      have hyx : y.val < x.val := by simpa only [hix,hiy] using hh
      exact (not_lt_of_gt h) hyx
    · have hh := congrArg (fun j => (e j).val) (Fin.ext heq : iy = ix)
      change (e iy).val = (e ix).val at hh
      rw [hix,hiy] at hh
      exact (ne_of_lt h) hh.symm

end DirectGLSSW.PermutationOrbits
