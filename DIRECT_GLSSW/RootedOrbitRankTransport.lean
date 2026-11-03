import DirectGLSSW.LocalCoordinates

set_option autoImplicit false
namespace DirectGLSSW.RootedOrbitRankTransport
open PermutationOrbits
noncomputable section

variable {α β : Type*} [Fintype α] [Fintype β]
variable (E : α ≃ β) (p : Equiv.Perm α) (q : Equiv.Perm β)
variable (he : ∀ x, E (p x) = q (E x))

def fibreEquiv (root : α) : Fibre p (componentOf p root) ≃ Fibre q (componentOf q (E root)) where
  toFun x := ⟨E x.val,(componentOf_eq_iff _ _ _).mpr
    ((sameCycle_iff_of_intertwining E p q he x.val root).mp
      ((componentOf_eq_iff _ _ _).mp x.property))⟩
  invFun y := ⟨E.symm y.val,(componentOf_eq_iff _ _ _).mpr
    ((sameCycle_iff_of_intertwining E p q he (E.symm y.val) root).mpr
      (by simpa only [Equiv.apply_symm_apply] using (componentOf_eq_iff _ _ _).mp y.property))⟩
  left_inv x := Subtype.ext (E.symm_apply_apply x.val)
  right_inv y := Subtype.ext (E.apply_symm_apply y.val)

/-- Exact numerical orbit rank is unchanged by an actual rooted successor intertwining. -/
theorem orbitRank_map_val (root : α) (x : Fibre p (componentOf p root)) :
    ((orbitEnumeration q (E root)).symm (fibreEquiv E p q he root x)).val =
      ((orbitEnumeration p root).symm x).val := by
  have hpow : ∀ k : ℕ, ∀ z : α, E ((p^k) z) = (q^k) (E z) := by
    intro k
    induction k with
    | zero => intro z; rfl
    | succ k ih => intro z; rw [pow_succ',Equiv.Perm.mul_apply,he,ih,pow_succ',Equiv.Perm.mul_apply]
  have hcard := Fintype.card_congr (fibreEquiv E p q he root)
  let i := (orbitEnumeration p root).symm x
  let j : Fin (Fintype.card (Fibre q (componentOf q (E root)))) :=
    ⟨i.val,by rw [← hcard]; exact i.isLt⟩
  have hx : (orbitEnumeration p root i).val = x.val :=
    congrArg Subtype.val ((orbitEnumeration p root).apply_symm_apply x)
  have hj : orbitEnumeration q (E root) j = fibreEquiv E p q he root x := by
    apply Subtype.ext
    change (orbitEnumeration q (E root) j).val = E x.val
    rw [orbitEnumeration_apply_val]
    change (q ^ i.val) (E root) = E x.val
    rw [← hpow,← orbitEnumeration_apply_val,hx]
  have hjrank : (orbitEnumeration q (E root)).symm (fibreEquiv E p q he root x) = j := by
    rw [← hj,Equiv.symm_apply_apply]
  exact congrArg Fin.val hjrank



end
end DirectGLSSW.RootedOrbitRankTransport
