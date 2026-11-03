import PolygonRebaseGeometry

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.PolygonRebase
variable {n : ℕ} (ρ : Fin n ≃ Fin n)
    (hρ : ∀ e, ρ (cyclicSuccessor e) = cyclicSuccessor (ρ e))

include hρ in
theorem label_formula (hn : 0 < n) (e : Fin n) :
    (ρ e).val = ((ρ ⟨0,hn⟩).val + e.val) % n := by
  let root : Fin n := ⟨n-1,by omega⟩
  have hi : cyclicVertexIndex root e.val = e := by
    apply Fin.ext
    change (n-1+1+e.val)%n = e.val
    rw [Nat.sub_add_cancel hn,Nat.add_mod,Nat.mod_self,zero_add,Nat.mod_mod,
      Nat.mod_eq_of_lt e.isLt]
  have h0 : cyclicVertexIndex root 0 = ⟨0,hn⟩ := by
    apply Fin.ext
    change (n-1+1+0)%n = 0
    simp only [Nat.sub_add_cancel hn,Nat.add_zero,Nat.mod_self]
  have he := cyclicVertexIndex_relabel ρ hρ root e.val
  have hz := cyclicVertexIndex_relabel ρ hρ root 0
  rw [hi] at he
  rw [h0] at hz
  have hev := congrArg Fin.val he
  have hzv := congrArg Fin.val hz
  change (ρ e).val = ((ρ root).val+1+e.val)%n at hev
  change (ρ ⟨0,hn⟩).val = ((ρ root).val+1+0)%n at hzv
  rw [Nat.add_zero] at hzv
  rw [hev,hzv,Nat.mod_add_mod]

include hρ in
theorem label_order_cut (hn : 0 < n) (x y : Fin n) :
    ρ x < ρ y ↔
      ((ρ.symm ⟨0,hn⟩) ≤ x ∧ y < (ρ.symm ⟨0,hn⟩)) ∨
        ((x < (ρ.symm ⟨0,hn⟩) ↔ y < (ρ.symm ⟨0,hn⟩)) ∧ x < y) := by
  let z : Fin n := ⟨0,hn⟩
  let cut := ρ.symm z
  let r := (ρ z).val
  have hc : (r+cut.val)%n=0 := by
    have h := label_formula ρ hρ hn cut
    simpa only [cut,z,Equiv.apply_symm_apply] using h.symm
  have hr : r < n := (ρ z).isLt
  have hcut := cut.isLt
  by_cases hzero : r = 0
  · have hcv : cut.val = 0 := by simpa only [hzero,zero_add,Nat.mod_eq_of_lt hcut] using hc
    have hx := label_formula ρ hρ hn x
    have hy := label_formula ρ hρ hn y
    change (ρ x).val = (r+x.val)%n at hx
    change (ρ y).val = (r+y.val)%n at hy
    rw [hzero,zero_add,Nat.mod_eq_of_lt x.isLt] at hx
    rw [hzero,zero_add,Nat.mod_eq_of_lt y.isLt] at hy
    change (ρ x).val < (ρ y).val ↔
      (cut.val ≤ x.val ∧ y.val < cut.val) ∨
        ((x.val < cut.val ↔ y.val < cut.val) ∧ x.val < y.val)
    rw [hx,hy,hcv]
    simp
  · have hsum : r+cut.val=n := by
      by_cases hh : r+cut.val<n
      · rw [Nat.mod_eq_of_lt hh] at hc
        omega
      · rw [Nat.mod_eq_sub_mod (by omega),Nat.mod_eq_of_lt (by omega)] at hc
        omega
    have hv : ∀ e : Fin n, (ρ e).val =
        if e.val < cut.val then r+e.val else r+e.val-n := by
      intro e
      rw [label_formula ρ hρ hn]
      change (r+e.val)%n = _
      by_cases he : e.val < cut.val
      · rw [if_pos he,Nat.mod_eq_of_lt (by omega)]
      · rw [if_neg he,Nat.mod_eq_sub_mod (by omega),Nat.mod_eq_of_lt (by have := e.isLt;omega)]
    change (ρ x).val < (ρ y).val ↔
      (cut.val ≤ x.val ∧ y.val < cut.val) ∨
        ((x.val < cut.val ↔ y.val < cut.val) ∧ x.val < y.val)
    rw [hv x,hv y]
    split_ifs <;> omega

end DirectGLSSW.PolygonRebase
