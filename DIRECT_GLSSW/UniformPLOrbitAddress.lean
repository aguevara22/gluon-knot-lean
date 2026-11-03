import UniformPLComponent

set_option autoImplicit false
namespace DirectGLSSW.HOMFLY.PrincipalTurning
open Equiv PermutationOrbits

theorem continuation_pow_small_injective (D : PLLinkDiagram) (e : Fin D.nArc)
    (k l : ℕ) (hk : k < componentArcLength D e) (hl : l < componentArcLength D e)
    (he : (D.continuation ^ k) e = (D.continuation ^ l) e) : k=l := by
  have h : orbitEnumeration D.continuation e ⟨k,hk⟩ =
      orbitEnumeration D.continuation e ⟨l,hl⟩ := by
    apply Subtype.ext
    simpa only [orbitEnumeration_apply_val] using he
  exact congrArg Fin.val ((orbitEnumeration D.continuation e).injective h)

theorem continuation_pow_closed_period_iff (D : PLLinkDiagram) (e : Fin D.nArc)
    (k l : ℕ) (hk : k ≤ componentArcLength D e) (hl : l ≤ componentArcLength D e) :
    (D.continuation ^ k) e = (D.continuation ^ l) e ↔
      k=l ∨ (k=0 ∧ l=componentArcLength D e) ∨ (k=componentArcLength D e ∧ l=0) := by
  have hm := componentArcLength_pos D e
  have hp := continuation_pow_componentArcLength D e
  constructor
  · intro he
    by_cases hkm : k=componentArcLength D e
    · by_cases hlm : l=componentArcLength D e
      · exact Or.inl (hkm.trans hlm.symm)
      · have hl' : l < componentArcLength D e := lt_of_le_of_ne hl hlm
        have he0 : (D.continuation ^ 0) e = (D.continuation ^ l) e := by simpa only [hkm,hp,pow_zero,Perm.one_apply] using he
        have h0l := continuation_pow_small_injective D e 0 l hm hl' he0
        exact Or.inr (Or.inr ⟨hkm,h0l.symm⟩)
    · have hk' : k < componentArcLength D e := lt_of_le_of_ne hk hkm
      by_cases hlm : l=componentArcLength D e
      · have hek0 : (D.continuation ^ k) e = (D.continuation ^ 0) e := by simpa only [hlm,hp,pow_zero,Perm.one_apply] using he
        exact Or.inr (Or.inl ⟨continuation_pow_small_injective D e k 0 hk' hm hek0,hlm⟩)
      · exact Or.inl (continuation_pow_small_injective D e k l hk' (lt_of_le_of_ne hl hlm) he)
  · rintro (he | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩)
    · rw [he]
    · simpa only [pow_zero,Perm.one_apply] using hp.symm
    · simpa only [pow_zero,Perm.one_apply] using hp

theorem basedUniform_floor_bounds (m : ℕ) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) m) :
    0 ≤ Int.floor (t+1/2) ∧ Int.floor (t+1/2) ≤ (m : ℤ) := by
  constructor
  · exact Int.floor_nonneg.mpr (by linarith [ht.1])
  · apply Int.floor_le_iff.mpr
    push_cast
    linarith [ht.2]

theorem basedUniform_address_bounds (m : ℕ) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) m) :
    (((Int.floor (t+1/2)).toNat : ℕ) : ℤ) = Int.floor (t+1/2) ∧
      (Int.floor (t+1/2)).toNat ≤ m := by
  have h := basedUniform_floor_bounds m t ht
  have hc := Int.toNat_of_nonneg h.1
  refine ⟨hc,?_⟩
  rw [← hc] at h
  exact_mod_cast h.2

end DirectGLSSW.HOMFLY.PrincipalTurning




