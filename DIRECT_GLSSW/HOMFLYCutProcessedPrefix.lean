import HOMFLYParentRootRetention

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.PermutationOrbits
open Equiv
variable {α : Type} [Fintype α] [DecidableEq α]

/-- The cut successor agrees with the old successor through the first cut visit. -/
theorem cut_pow_eq_of_le_earlier_position (p : Perm α) (r a b : α)
    (ha : componentOf p a = componentOf p r)
    (hb : componentOf p b = componentOf p r)
    (hlt : ((orbitEnumeration p r).symm ⟨a, ha⟩).val <
      ((orbitEnumeration p r).symm ⟨b, hb⟩).val)
    (n : ℕ) (hn : n ≤ ((orbitEnumeration p r).symm ⟨a, ha⟩).val) :
    ((p * swap a b) ^ n) r = (p ^ n) r := by
  let e := orbitEnumeration p r
  let ia := e.symm ⟨a, ha⟩
  let ib := e.symm ⟨b, hb⟩
  have hea : (e ia).val = a := congrArg Subtype.val (e.apply_symm_apply ⟨a, ha⟩)
  have heb : (e ib).val = b := congrArg Subtype.val (e.apply_symm_apply ⟨b, hb⟩)
  have hab : ia.val < ib.val := hlt
  have hne : ∀ t : ℕ, t < ia.val → (p ^ t) r ≠ a ∧ (p ^ t) r ≠ b := by
    intro t ht
    let j : Fin (Fintype.card (Fibre p (componentOf p r))) := ⟨t, by omega⟩
    have hj : (e j).val = (p ^ t) r := orbitEnumeration_apply_val p r j
    constructor
    · intro h
      have he : e j = e ia := Subtype.ext (hj.trans (h.trans hea.symm))
      have hv := congrArg Fin.val (e.injective he)
      change t = ia.val at hv
      omega
    · intro h
      have he : e j = e ib := Subtype.ext (hj.trans (h.trans heb.symm))
      have hv := congrArg Fin.val (e.injective he)
      change t = ib.val at hv
      omega
  induction n with
  | zero => rfl
  | succ n ih =>
    rcases hne n (by change n+1 ≤ ia.val at hn; omega) with ⟨hna,hnb⟩
    rw [pow_succ', Perm.mul_apply, ih (by omega),
      mul_swap_apply_of_ne p hna hnb, pow_succ', Perm.mul_apply]

/-- Every old visit at or before the first cut visit stays with the old root. -/
theorem root_sameCycle_cut_of_position_le (p : Perm α) (r a b x : α)
    (ha : componentOf p a = componentOf p r)
    (hb : componentOf p b = componentOf p r)
    (hx : componentOf p x = componentOf p r)
    (hlt : ((orbitEnumeration p r).symm ⟨a, ha⟩).val <
      ((orbitEnumeration p r).symm ⟨b, hb⟩).val)
    (hle : ((orbitEnumeration p r).symm ⟨x, hx⟩).val ≤
      ((orbitEnumeration p r).symm ⟨a, ha⟩).val) :
    (p * swap a b).SameCycle r x := by
  let j := (orbitEnumeration p r).symm ⟨x,hx⟩
  refine ⟨(j.val : ℤ), ?_⟩
  rw [zpow_natCast,cut_pow_eq_of_le_earlier_position p r a b ha hb hlt j.val hle]
  exact (orbitEnumeration_apply_val p r j).symm.trans
    (congrArg Subtype.val ((orbitEnumeration p r).apply_symm_apply ⟨x,hx⟩))

end DirectGLSSW.PermutationOrbits
