import FiniteSupportCuts
import DirectGLSSW.CutEventAdapterV3

set_option autoImplicit false

namespace DirectGLSSW.SupportCutMembership
open OrderedCapEvents MixedEdgeChainsV3 FiniteSupportCuts

theorem pairwise_iff_ordered_pairs {α : Type*} [LinearOrder α]
    (L : List α) (hL : L.Pairwise (· < ·)) (R : α → α → Prop) :
    L.Pairwise R ↔ ∀ a ∈ L, ∀ b ∈ L, a < b → R a b := by
  constructor
  · intro h a ha b hb hab
    obtain ⟨i,hi⟩ := List.mem_iff_get.mp ha
    obtain ⟨j,hj⟩ := List.mem_iff_get.mp hb
    have hij : i < j := by
      rcases lt_trichotomy i j with hlt | heq | hgt
      · exact hlt
      · subst j; rw [hi] at hj; exact (lt_irrefl a (hj ▸ hab)).elim
      · have hback := List.pairwise_iff_get.mp hL j i hgt
        rw [hj,hi] at hback
        exact (lt_asymm hab hback).elim
    simpa only [hi,hj] using List.pairwise_iff_get.mp h i j hij
  · intro h
    exact hL.imp_of_mem (fun ha hb hab => h _ ha _ hb hab)

theorem mem_cutEventChain {Q : ℕ → PlanarPoint ℝ} {n : ℕ}
    (u v : EventIndex Q n) (huv : u.val < v.val)
    (S : IntervalCutSet u.val v.val) (c : EventIndex Q n) :
    c ∈ cutEventChain u v huv S ↔ c = u ∨ c = v ∨ c.val ∈ S.val := by
  classical
  have hm : c ∈ cutEventChain u v huv S ↔
      c.val ∈ (cutEventChain u v huv S).map Fin.val := by
    constructor
    · exact fun h => List.mem_map.mpr ⟨c,h,rfl⟩
    · intro h
      obtain ⟨d,hd,heq⟩ := List.mem_map.mp h
      exact Fin.ext heq ▸ hd
  rw [hm]
  change c.val ∈ eventIndexValues (cutEventChain u v huv S) ↔ _
  rw [cutEventChain_values_eq_cutVertices]
  simp only [cutVertices,List.mem_cons,List.mem_append,List.mem_singleton,
    Finset.mem_sort,Fin.val_inj]
  tauto

theorem mem_support_cut_chain {α : Type*} {Q : ℕ → PlanarPoint ℝ} {n : ℕ}
    (u v : EventIndex Q n) (huv : u.val < v.val)
    (E : α ≃ ↥(Finset.Ioo u.val v.val)) (F : α → EventIndex Q n)
    (hF : ∀ z, (E z).val = (F z).val) (T : Finset α) (c : EventIndex Q n) :
    c ∈ cutEventChain u v huv (supportCutMap E T) ↔
      c = u ∨ c = v ∨ ∃ z ∈ T, F z = c := by
  rw [mem_cutEventChain]
  have hs : c.val ∈ (supportCutMap E T).val ↔ ∃ z ∈ T, F z = c := by
    change c.val ∈ T.map (indexEmbedding E) ↔ _
    rw [Finset.mem_map]
    constructor
    · rintro ⟨z,hz,heq⟩
      refine ⟨z,hz,Fin.ext ?_⟩
      exact (hF z).symm.trans heq
    · rintro ⟨z,hz,rfl⟩
      exact ⟨z,hz,hF z⟩
  rw [hs]




end DirectGLSSW.SupportCutMembership
