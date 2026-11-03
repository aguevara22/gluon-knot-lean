import CanonicalDaughterInventory
import DirectGLSSW.TruncationEdgeLift
import DirectGLSSW.TruncationPointGeometry

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.CyclicCarrierClearing
open AuxiliaryCarrierChart UniversalCarrierDomain TruncationDirection TruncationEdgeLift
open ShortEdgeCyclicAdapter

def truncatedCarrierLabel {n : ℕ} (a : Fin n) (i : Fin (n+1)) : Fin (n+1) :=
  if i = a.castSucc then Fin.last n else (collapseFin a i).castSucc

theorem truncatedCarrierLabel_eq {n : ℕ} (a : Fin n) (i : Fin (n+1)) :
    truncatedCarrierLabel a i =
      if i = a.castSucc then Fin.last n else (collapseFin a i).castSucc := rfl

theorem truncatedCarrierLabel_short {n : ℕ} (a : Fin n) :
    truncatedCarrierLabel a a.castSucc = Fin.last n := by simp [truncatedCarrierLabel]

theorem truncatedCarrierLabel_old {n : ℕ} (a e : Fin n) :
    truncatedCarrierLabel a (edgeLift a e) = e.castSucc := by
  simp [truncatedCarrierLabel,edgeLift_ne_short,collapseFin_edgeLift]

theorem truncatedCarrierLabel_injective {n : ℕ} (a : Fin n) :
    Function.Injective (truncatedCarrierLabel a) := by
  intro i j h
  by_cases hi : i = a.castSucc <;> by_cases hj : j = a.castSucc
  · exact hi.trans hj.symm
  · simp only [truncatedCarrierLabel,if_pos hi,if_neg hj] at h
    have hh := congrArg Fin.val h
    have hlt := (collapseFin a j).isLt
    simp only [Fin.val_last,Fin.coe_castSucc] at hh
    omega
  · simp only [truncatedCarrierLabel,if_neg hi,if_pos hj] at h
    have hh := congrArg Fin.val h
    have hlt := (collapseFin a i).isLt
    simp only [Fin.val_last,Fin.coe_castSucc] at hh
    omega
  · simp only [truncatedCarrierLabel,if_neg hi,if_neg hj] at h
    have hc := (Fin.castSucc_injective n) h
    have he := congrArg (edgeLift a) hc
    simpa only [edgeLift_collapseFin a i hi,edgeLift_collapseFin a j hj] using he

private theorem lineValue_segment (L : CarrierLine) (a b : PlanarPoint ℝ) (t : ℝ)
    (ha : lineValue L a = 0) (hb : lineValue L b = 0) :
    lineValue L (a+t • (b-a)) = 0 := by
  simp only [lineValue,planarDet,Prod.fst_add,Prod.snd_add,Prod.smul_fst,Prod.smul_snd,
    Prod.fst_sub,Prod.snd_sub,smul_eq_mul] at ha hb ⊢
  linear_combination (1-t)*ha+t*hb

/-- Literal original-edge incidence, with no size/genericity/positivity premise. -/
theorem truncated_old_carrier_incidence {n : ℕ} (q : Fin n → PlanarPoint ℝ)
    (a p : Fin n) (hp : cyclicSuccessor p = a) (scale ε : ℝ)
    (i : Fin (n+1)) (hi : i ≠ a.castSucc) :
    lineValue (polygonCarrierCoordinates q (collapseFin a i))
      (truncateCyclicCorner q a p scale ε i) = 0 ∧
    lineValue (polygonCarrierCoordinates q (collapseFin a i))
      (truncateCyclicCorner q a p scale ε (cyclicSuccessor i)) = 0 := by
  rw [truncateCyclicCorner_off_short q a p scale ε i hi,
    truncateCyclicCorner_successor_off_short q a p scale ε i hi]
  constructor
  · split_ifs with he
    · rw [he]
      exact lineValue_segment _ _ _ _ (polygonCarrierCoordinates_value_start q a)
        (polygonCarrierCoordinates_value_successor q a)
    · exact polygonCarrierCoordinates_value_start q _
  · split_ifs with he
    · have heq : collapseFin a i = p :=
        (cyclicSuccessor_bijective (n := n)).injective (he.trans hp.symm)
      rw [heq]
      exact lineValue_segment _ _ _ _ (by simpa only [hp] using polygonCarrierCoordinates_value_successor q p)
        (polygonCarrierCoordinates_value_start q p)
    · exact polygonCarrierCoordinates_value_successor q _

theorem truncated_augmented_carrier_incidence {n : ℕ} (q : Fin n → PlanarPoint ℝ)
    (a p : Fin n) (hp : cyclicSuccessor p = a) (scale ε : ℝ) (K : CarrierLine)
    (hleft : lineValue K (q a+ε • (q p-q a)) = 0)
    (hright : lineValue K (q a+(ε*scale) • (q (cyclicSuccessor a)-q a)) = 0) :
    ∀ i, lineValue (canonicalAugmentedCarrier q K (truncatedCarrierLabel a i))
        (truncateCyclicCorner q a p scale ε i) = 0 ∧
      lineValue (canonicalAugmentedCarrier q K (truncatedCarrierLabel a i))
        (truncateCyclicCorner q a p scale ε (cyclicSuccessor i)) = 0 := by
  intro i
  by_cases hi : i = a.castSucc
  · subst i
    have hK : canonicalAugmentedCarrier q K (Fin.last n) = K := by simp [canonicalAugmentedCarrier]
    rw [truncatedCarrierLabel_short,hK]
    have ha : truncateCyclicCorner q a p scale ε a.castSucc = q a+ε • (q p-q a) :=
      truncateCyclicCorner_anchor q a p scale ε
    rw [ha,cyclicSuccessor_shortEdge,truncateCyclicCorner_new]
    exact ⟨hleft,hright⟩
  · simpa only [truncatedCarrierLabel,if_neg hi,canonicalAugmentedCarrier,Fin.coe_castSucc,
      dif_pos (collapseFin a i).isLt] using truncated_old_carrier_incidence q a p hp scale ε i hi

end DirectGLSSW.CyclicCarrierClearing






