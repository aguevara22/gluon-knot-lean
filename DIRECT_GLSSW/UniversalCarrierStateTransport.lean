import UniversalCarrierTransverse
import ActiveArcParentLineGeometry
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.UniversalCarrierDomain
open AuxiliaryCarrierChart ActiveArc ActiveArc.Cursor ActiveArc.Split ActiveArc.OpenCarrier

private theorem supplied_affine (K : CarrierLine) (x y : PlanarPoint ℝ) (t : ℝ)
    (hx : lineValue K x=0) (hy : lineValue K y=0) :
    lineValue K (affinePoint x y t)=0 := by
  have hh : lineValue K (affinePoint x y t)=(1-t)*lineValue K x+t*lineValue K y := by
    simp only [lineValue,planarDet,affinePoint];ring
  rw [hh,hx,hy];ring

/-- The same supplied lines remain incident under literal head motion. -/
theorem supplied_moveStart_incidence {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ)
    (L : Fin (n+1) ⊕ Unit → CarrierLine)
    (hinc : ∀ e : Fin (n+1), lineValue (L (Sum.inl e)) (q e.castSucc)=0 ∧
      lineValue (L (Sum.inl e)) (q e.succ)=0)
    (hterminal : lineValue (L (Sum.inr ())) (q ⟨n+1,by omega⟩)=0) (t : ℝ) :
    (∀ e : Fin (n+1), lineValue (L (Sum.inl e)) (moveStart q t e.castSucc)=0 ∧
      lineValue (L (Sum.inl e)) (moveStart q t e.succ)=0) ∧
      lineValue (L (Sum.inr ())) (moveStart q t ⟨n+1,by omega⟩)=0 := by
  constructor
  · intro e
    by_cases he : e=0
    · subst e
      constructor
      · change lineValue (L (Sum.inl 0)) (moveStart q t 0)=0
        rw [moveStart_zero]
        exact supplied_affine _ _ _ _ (hinc 0).1 (hinc 0).2
      · rw [moveStart_succ]
        exact (hinc 0).2
    · rw [moveStart_eq q t e.castSucc (castSucc_ne_zero he),moveStart_succ]
      exact hinc e
  · rw [moveStart_eq q t _ (by intro he;have hh:=congrArg Fin.val he;simp at hh)]
    exact hterminal

def suffixCarrierMap {a b : ℕ} : Fin (b+1) ⊕ Unit → Fin (a+b+1) ⊕ Unit :=
  Sum.map (edge (a:=a)) id

theorem suffixCarrierMap_injective {a b : ℕ} :
    Function.Injective (suffixCarrierMap (a:=a) (b:=b)) := by
  intro x y he
  cases x <;> cases y
  · simp only [suffixCarrierMap,Sum.map_inl,Sum.inl.injEq] at he ⊢
    exact edge_injective he
  · exact Sum.noConfusion he
  · exact Sum.noConfusion he
  · exact congrArg Sum.inr (Subsingleton.elim _ _)

theorem supplied_suffix_incidence {a b : ℕ} (q : Fin (a+b+2) → PlanarPoint ℝ)
    (L : Fin (a+b+1) ⊕ Unit → CarrierLine)
    (hinc : ∀ e : Fin (a+b+1), lineValue (L (Sum.inl e)) (q e.castSucc)=0 ∧
      lineValue (L (Sum.inl e)) (q e.succ)=0)
    (hterminal : lineValue (L (Sum.inr ())) (q ⟨a+b+1,by omega⟩)=0) :
    let M := L ∘ suffixCarrierMap (a:=a) (b:=b)
    (∀ e : Fin (b+1), lineValue (M (Sum.inl e)) (suffix q e.castSucc)=0 ∧
      lineValue (M (Sum.inl e)) (suffix q e.succ)=0) ∧
      lineValue (M (Sum.inr ())) (suffix q ⟨b+1,by omega⟩)=0 := by
  intro M
  constructor
  · intro e
    change lineValue (L (Sum.inl (edge e))) (q (vertex e.castSucc))=0 ∧
      lineValue (L (Sum.inl (edge e))) (q (vertex e.succ))=0
    rw [vertex_castSucc,vertex_succ]
    exact hinc (edge e)
  · change lineValue (L (Sum.inr ())) (q (vertex ⟨b+1,by omega⟩))=0
    have hi : vertex (a:=a) (⟨b+1,by omega⟩ : Fin (b+2))=(⟨a+b+1,by omega⟩ : Fin (a+b+2)) := by
      apply Fin.ext
      simp [vertex,Nat.add_assoc]
    rw [hi]
    exact hterminal

/-- Full supplied-family propagation to an actual cut parent. The same global
family is restricted injectively; there is no new density or avoidance premise. -/
theorem universal_supplied_parent {a b : ℕ} (q : Fin (a+b+2) → PlanarPoint ℝ)
    (c : Crossing q) (hcut : c.val.2.val=a)
    (L : Fin (a+b+1) ⊕ Unit → CarrierLine)
    (hL : UniversalLocus L) (hT : PairTransverse L)
    (hinc : ∀ e : Fin (a+b+1), lineValue (L (Sum.inl e)) (q e.castSucc)=0 ∧
      lineValue (L (Sum.inl e)) (q e.succ)=0)
    (hterminal : lineValue (L (Sum.inr ())) (q ⟨a+b+1,by omega⟩)=0) :
    let M := L ∘ suffixCarrierMap (a:=a) (b:=b)
    UniversalLocus M ∧ PairTransverse M ∧
      (∀ e : Fin (b+1), lineValue (M (Sum.inl e)) (parent q c hcut e.castSucc)=0 ∧
        lineValue (M (Sum.inl e)) (parent q c hcut e.succ)=0) ∧
      lineValue (M (Sum.inr ())) (parent q c hcut ⟨b+1,by omega⟩)=0 := by
  intro M
  have hf := suffixCarrierMap_injective (a:=a) (b:=b)
  have hs := supplied_suffix_incidence q L hinc hterminal
  exact ⟨universalLocus_comap L hL _ hf,pairTransverse_comap L hT _ hf,
    supplied_moveStart_incidence (suffix q) M hs.1 hs.2 (rightParameter q c)⟩
end DirectGLSSW.UniversalCarrierDomain


