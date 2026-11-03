import NoncornerOrbitGap

set_option autoImplicit false
namespace DirectGLSSW.FiniteRetainedPrefix
open FiniteFirstReturn
noncomputable section
attribute [local instance] Classical.propDecidable

/-- A retained zero coordinate means the first-return interval never wraps:
its last block ends at N, and all other blocks end at their next retained label. -/
theorem prefix_no_wrap {N : ℕ} (hN : 0 < N) (P : Fin N → Prop)
    (hzero : P ⟨0,hN⟩) (c : {i : Fin N // P i}) (k : ℕ)
    (hk : k < forwardGap c.val (orderedCyclicSuccessor {i : Fin N // P i} c).val) :
    c.val.val+k < N ∧ ∀ b : {i : Fin N // P i}, c < b → c.val.val+k < b.val.val := by
  let next := orderedCyclicSuccessor {i : Fin N // P i} c
  change k < forwardGap c.val next.val at hk
  have hspec := orderedCyclicSuccessor_order_spec {i : Fin N // P i} c
  rcases hspec with ⟨hinc,hmin⟩ | ⟨hmax,hmin⟩
  · have hcn : c.val.val < next.val.val := hinc
    have hkn : k < next.val.val-c.val.val := by
      simpa only [forwardGap,if_pos hcn] using hk
    have hn := next.val.isLt
    refine ⟨by omega,?_⟩
    intro b hcb
    have hnb : next.val.val ≤ b.val.val := hmin b hcb
    omega
  · have hn0 : next.val.val ≤ 0 := hmin ⟨⟨0,hN⟩,hzero⟩
    have hcn : ¬ c.val.val < next.val.val := by omega
    have hkn : k < N-c.val.val+next.val.val := by
      simpa only [forwardGap,if_neg hcn] using hk
    have hc := c.val.isLt
    refine ⟨by omega,?_⟩
    intro b hcb
    exact ((not_le_of_gt hcb) (hmax b)).elim

/-- Every coordinate has an actual retained predecessor and a nonwrapping
first-return offset, including offset zero at retained coordinates. -/
theorem exists_prefix {N : ℕ} (hN : 0 < N) (P : Fin N → Prop)
    (hzero : P ⟨0,hN⟩) (r : Fin N) :
    ∃ c : {i : Fin N // P i}, ∃ k : ℕ,
      k < forwardGap c.val (orderedCyclicSuccessor {i : Fin N // P i} c).val ∧
      (cyclicSuccessorPerm N ^ k) c.val = r ∧ r.val = c.val.val+k ∧
      ∀ b : {i : Fin N // P i}, c < b → r.val < b.val.val := by
  have hpre : ∃ c : {i : Fin N // P i}, ∃ k : ℕ,
      k < forwardGap c.val (orderedCyclicSuccessor {i : Fin N // P i} c).val ∧
      (cyclicSuccessorPerm N ^ k) c.val = r := by
    by_cases hr : P r
    · exact ⟨⟨r,hr⟩,0,forwardGap_pos _ _,by simp⟩
    · obtain ⟨c,k,_,hk,hreach⟩ := NoncornerOrbitGap.exists_preceding_retained hN P hzero r hr
      exact ⟨c,k,hk,hreach⟩
  obtain ⟨c,k,hk,hreach⟩ := hpre
  obtain ⟨hnowrap,hbefore⟩ := prefix_no_wrap hN P hzero c k hk
  have hkN : k < N := by omega
  have hr : r.val = c.val.val+k := by
    rw [← hreach,cyclicSuccessorPerm_pow_val_of_lt c.val hkN,if_pos hnowrap]
  exact ⟨c,k,hk,hreach,hr,fun b hcb => hr ▸ hbefore b hcb⟩



end
end DirectGLSSW.FiniteRetainedPrefix
