import DirectGLSSW.PermutationSplitJoin
import DirectGLSSW.HOMFLY.BasedTraversal

set_option autoImplicit false

namespace DirectGLSSW.PermutationOrbits
open Equiv
universe u
variable {α : Type u} [Fintype α] [DecidableEq α]

/-- An old component disjoint from both cut ports keeps its exact traversal. -/
theorem cutUnaffected_pow (p : Perm α) (a b root : α)
    (ha : ¬ p.SameCycle root a) (hb : ¬ p.SameCycle root b) (n : ℕ) :
    ((p * swap a b) ^ n) root = (p ^ n) root := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hna : (p ^ n) root ≠ a := by
      intro h
      exact ha ⟨(n : ℤ), by simpa only [zpow_natCast] using h⟩
    have hnb : (p ^ n) root ≠ b := by
      intro h
      exact hb ⟨(n : ℤ), by simpa only [zpow_natCast] using h⟩
    rw [pow_succ', Perm.mul_apply, ih, mul_swap_apply_of_ne p hna hnb,
      pow_succ', Perm.mul_apply]

theorem cutUnaffected_sameCycle (p : Perm α) (a b root x : α)
    (ha : ¬ p.SameCycle root a) (hb : ¬ p.SameCycle root b) :
    (p * swap a b).SameCycle root x ↔ p.SameCycle root x := by
  constructor
  · intro h
    obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
    refine ⟨(n : ℤ), ?_⟩
    rw [zpow_natCast, ← cutUnaffected_pow p a b root ha hb, hn]
  · intro h
    obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
    refine ⟨(n : ℤ), ?_⟩
    rw [zpow_natCast, cutUnaffected_pow p a b root ha hb, hn]

noncomputable def cutUnaffectedFibreEquiv (p : Perm α) (a b root : α)
    (ha : ¬ p.SameCycle root a) (hb : ¬ p.SameCycle root b) :
    Fibre p (componentOf p root) ≃
      Fibre (p * swap a b) (componentOf (p * swap a b) root) where
  toFun x := ⟨x.val, ((componentOf_eq_iff _ _ _).2
    ((cutUnaffected_sameCycle p a b root x.val ha hb).2
      ((componentOf_eq_iff _ _ _).1 x.property.symm))).symm⟩
  invFun x := ⟨x.val, ((componentOf_eq_iff _ _ _).2
    ((cutUnaffected_sameCycle p a b root x.val ha hb).1
      ((componentOf_eq_iff _ _ _).1 x.property.symm))).symm⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Actual orbit-enumeration positions on every unaffected old component
remain unchanged under the branch cut. -/
theorem cutUnaffected_orbitPosition (p : Perm α) (a b root : α)
    (ha : ¬ p.SameCycle root a) (hb : ¬ p.SameCycle root b)
    (x : Fibre p (componentOf p root)) :
    ((orbitEnumeration (p * swap a b) root).symm
      (cutUnaffectedFibreEquiv p a b root ha hb x)).val =
      ((orbitEnumeration p root).symm x).val := by
  let t := (orbitEnumeration p root).symm x
  have hc := Fintype.card_congr (cutUnaffectedFibreEquiv p a b root ha hb)
  let s : Fin (Fintype.card (Fibre (p * swap a b)
      (componentOf (p * swap a b) root))) := Fin.cast hc t
  have hp : (p ^ t.val) root = x.val := by
    have h := congrArg Subtype.val ((orbitEnumeration p root).apply_symm_apply x)
    simpa only [orbitEnumeration_apply_val] using h
  have he : orbitEnumeration (p * swap a b) root s =
      cutUnaffectedFibreEquiv p a b root ha hb x := by
    apply Subtype.ext
    rw [orbitEnumeration_apply_val]
    change ((p * swap a b) ^ t.val) root = x.val
    rw [cutUnaffected_pow p a b root ha hb, hp]
  rw [← he, Equiv.symm_apply_apply]
  rfl

end DirectGLSSW.PermutationOrbits

namespace DirectGLSSW.HOMFLY

/-- Expose the exact orbit coordinate used by a based traversal when its
chosen root on the component is already known. -/
theorem visitPosition_eq_orbitPosition_of_baseArc {D : PLLinkDiagram}
    (T : BasedTraversal D) (e root : Fin D.nArc)
    (hbase : (T.baseArc (PermutationOrbits.componentOf D.continuation e)).val = root)
    (he : PermutationOrbits.componentOf D.continuation e =
      PermutationOrbits.componentOf D.continuation root) :
    visitPosition T e =
      ((PermutationOrbits.orbitEnumeration D.continuation root).symm ⟨e, he⟩).val := by
  subst root
  rfl

end DirectGLSSW.HOMFLY






