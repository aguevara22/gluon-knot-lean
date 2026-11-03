import SupportCutMembership
import SelectedCellClippedWord

set_option autoImplicit false

namespace DirectGLSSW.CellChainProduct
open OrderedCapEvents MixedEdgeChainsV3 FiniteSupportCuts SelectedCellClippedWord
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem support_cut_chain_eq_list {α : Type*} {Q : ℕ → PlanarPoint ℝ} {n : ℕ}
    (u v : EventIndex Q n) (huv : u.val < v.val)
    (E : α ≃ ↥(Finset.Ioo u.val v.val)) (F : α → EventIndex Q n)
    (hF : ∀ z, (E z).val = (F z).val) (L : List α)
    (hL : (L.map F).Pairwise (· < ·)) :
    cutEventChain u v huv (supportCutMap E L.toFinset) = u :: L.map F ++ [v] := by
  classical
  let g := fun z => (F z).val
  have hsort : (L.map g).Pairwise (· < ·) := by
    simpa only [List.pairwise_map] using hL
  have hs : (supportCutMap E L.toFinset).val = (L.map g).toFinset := by
    ext k
    simp only [supportCutMap,Finset.mem_map,List.mem_toFinset,List.mem_map]
    constructor
    · rintro ⟨z,hz,heq⟩
      exact ⟨z,hz,(hF z).symm.trans heq⟩
    · rintro ⟨z,hz,heq⟩
      exact ⟨z,hz,(hF z).trans heq⟩
  have hsorted : (L.map g).toFinset.sort (· ≤ ·) = L.map g :=
    (List.toFinset_sort (· ≤ ·) (hsort.imp (fun h => ne_of_lt h))).mpr
      (hsort.imp (fun h => le_of_lt h))
  apply (List.map_injective_iff.mpr Fin.val_injective)
  change eventIndexValues (cutEventChain u v huv (supportCutMap E L.toFinset)) = _
  rw [cutEventChain_values_eq_cutVertices]
  simp only [cutVertices,hs,hsorted,List.map_cons,List.map_append,List.map_map,
    List.map_singleton]
  rfl

theorem zip_chain_eq_cell_pairs {α β : Type*} (u v : β) (F : α → β) (L : List α) :
    (u :: L.map F ++ [v]).zip (u :: L.map F ++ [v]).tail =
      List.ofFn (fun i : Fin (L.length+1) =>
        (leftBoundary u F L i, rightBoundary v F L i)) := by
  apply List.ext_getElem
  · simp
  · intro j hj hk
    have hj' : j < L.length+1 := by simpa using hk
    simp only [List.getElem_zip,List.getElem_ofFn,List.tail_cons]
    apply Prod.ext
    · by_cases hj0 : j=0
      · subst j
        simp [leftBoundary]
      · have hpred : j-1 < L.length := by omega
        simp only [leftBoundary,dif_neg hj0,List.get_eq_getElem]
        simp [List.getElem_cons,hj0,List.getElem_append,hpred]
    · by_cases hjL : j<L.length
      · simp [rightBoundary,hjL,List.getElem_append]
      · have heq : j=L.length := by omega
        subst j
        simp [rightBoundary,List.getElem_append]

theorem chain_product_eq_cell_product {α β M : Type*} [CommMonoid M]
    (u v : β) (F : α → β) (L : List α) (B : β → β → M) :
    (((u :: L.map F ++ [v]).zip (u :: L.map F ++ [v]).tail).map
      (fun p => B p.1 p.2)).prod =
    ∏ i : Fin (L.length+1), B (leftBoundary u F L i) (rightBoundary v F L i) := by
  rw [zip_chain_eq_cell_pairs,List.map_ofFn]
  simp [Finset.prod_eq_multiset_prod]

theorem event_branchProduct_eq_cellProduct {α : Type*}
    (Q : ℕ → PlanarPoint ℝ) (n : ℕ) (u v : EventIndex Q n)
    (F : α → EventIndex Q n) (L : List α) :
    branchProduct (eventIntervalArray Q n) (eventIndexValues (u :: L.map F ++ [v])) =
    ∏ i : Fin (L.length+1),
      eventMatrix Q n (leftBoundary u F L i) (rightBoundary v F L i) := by
  have hentry (c d : EventIndex Q n) : eventIntervalArray Q n c.val d.val =
      eventMatrix Q n c d := by
    simp [eventIntervalArray,finiteMatrixIntervalArray,c.isLt,d.isLt]
  rw [branchProduct,eventIndexValues,← List.map_tail,List.zip_map,List.map_map]
  simp only [Function.comp_def,Prod.map,hentry]
  exact chain_product_eq_cell_product u v F L (eventMatrix Q n)


theorem cell_pairs_ordered {α β : Type*} (u v : β) (F : α → β) (L : List α)
    (R : β → β → Prop) (hR : (u :: L.map F ++ [v]).Pairwise R)
    (i : Fin (L.length+1)) :
    R (leftBoundary u F L i) (rightBoundary v F L i) := by
  let C := u :: L.map F ++ [v]
  have hi : i.val < (C.zip C.tail).length := by simpa [C] using i.isLt
  have hi0 : i.val < C.length := by
    have := i.isLt
    simp only [C,List.length_cons,List.length_append,List.length_map,List.length_singleton]
    omega
  have hi1 : i.val+1 < C.length := by
    have := i.isLt
    simp only [C,List.length_cons,List.length_append,List.length_map,List.length_singleton]
    omega
  have hpair : (C.zip C.tail)[i.val] = (leftBoundary u F L i,rightBoundary v F L i) := by
    simp only [C,zip_chain_eq_cell_pairs,List.getElem_ofFn,Fin.eta]
  simp only [List.getElem_zip,List.getElem_tail] at hpair
  have hrel := List.pairwise_iff_get.mp hR
    (⟨i.val,hi0⟩ : Fin C.length)
    (⟨i.val+1,hi1⟩ : Fin C.length) (by change i.val < i.val+1; omega)
  simp only [List.get_eq_getElem] at hrel
  change R (C[i.val]'hi0) (C[i.val+1]'hi1) at hrel
  rw [(Prod.mk.inj hpair).1,(Prod.mk.inj hpair).2] at hrel
  exact hrel

theorem support_cut_branchProduct_eq_cellProduct {α : Type*}
    (Q : ℕ → PlanarPoint ℝ) (n : ℕ) (u v : EventIndex Q n) (huv : u.val < v.val)
    (E : α ≃ ↥(Finset.Ioo u.val v.val)) (F : α → EventIndex Q n)
    (hF : ∀ z, (E z).val = (F z).val) (L : List α)
    (hL : (L.map F).Pairwise (· < ·)) :
    branchProduct (eventIntervalArray Q n)
      (cutVertices u.val v.val (supportCutMap E L.toFinset).val) =
    ∏ i : Fin (L.length+1),
      eventMatrix Q n (leftBoundary u F L i) (rightBoundary v F L i) := by
  rw [← cutEventChain_values_eq_cutVertices u v huv (supportCutMap E L.toFinset),
    support_cut_chain_eq_list u v huv E F hF L hL]
  exact event_branchProduct_eq_cellProduct Q n u v F L






end DirectGLSSW.CellChainProduct
