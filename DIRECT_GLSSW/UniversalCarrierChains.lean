import UniversalCarrierTransverse
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.UniversalCarrierDomain
open AuxiliaryCarrierChart
private theorem consecutive_pairs_ne {m : ℕ} (i j : Fin m) (hij : i.val<j.val) :
    ({i.castSucc,i.succ} : Finset (Fin (m+1)))≠{j.castSucc,j.succ} := by
  intro he
  have hm : i.castSucc∈({j.castSucc,j.succ} : Finset (Fin (m+1))) := by
    rw [←he];simp
  simp only [Finset.mem_insert,Finset.mem_singleton] at hm
  rcases hm with hm | hm
  all_goals
    have hh := congrArg Fin.val hm
    simp only [Fin.coe_castSucc,Fin.val_succ] at hh
    omega

theorem properPairs_consecutive {α : Type*} [DecidableEq α] {m : ℕ}
    (f : Fin (m+1) → α) (hf : Function.Injective f) (i j k : Fin m)
    (hij : i.val<j.val) (hjk : j.val<k.val) :
    ProperPairs (f i.castSucc,f i.succ) (f j.castSucc,f j.succ) (f k.castSucc,f k.succ) := by
  have h : ProperPairs (i.castSucc,i.succ) (j.castSucc,j.succ) (k.castSucc,k.succ) := by
    have hn (v : Fin m) : v.castSucc≠v.succ := by
      intro he;have hh:=congrArg Fin.val he;simp at hh
    refine ⟨hn i,hn j,hn k,consecutive_pairs_ne i j hij,consecutive_pairs_ne j k hjk,
      consecutive_pairs_ne i k (lt_trans hij hjk),?_⟩
    rintro ⟨x,hi,hj,hk⟩
    simp only [Finset.mem_insert,Finset.mem_singleton] at hi hj hk
    rcases hi with hi|hi <;> rcases hj with hj|hj <;> rcases hk with hk|hk
    all_goals
      have hi' := congrArg Fin.val hi
      have hj' := congrArg Fin.val hj
      have hk' := congrArg Fin.val hk
      simp only [Fin.coe_castSucc,Fin.val_succ] at hi' hj' hk'
      omega
  exact properPairs_map f hf _ _ _ h


/-- Isolate finite carrier-chain algebra from large dependent physical words. -/
theorem universal_chain_far {α : Type*} [DecidableEq α] {m : ℕ}
    (L : α → CarrierLine) (hL : UniversalLocus L)
    (f : Fin (m+1) → α) (hf : Function.Injective f)
    (z i j : Fin m) (hz : z.val = 0) (hi : 0 < i.val) (hij : i.val < j.val) :
    carrierTripleNumerator (L (f z.castSucc)) (L (f z.succ))
      (L (f i.castSucc)) (L (f i.succ)) (L (f j.castSucc)) (L (f j.succ))≠0 := by
  exact hL _ _ _ (properPairs_consecutive f hf z i j (by omega) hij)
end DirectGLSSW.UniversalCarrierDomain

