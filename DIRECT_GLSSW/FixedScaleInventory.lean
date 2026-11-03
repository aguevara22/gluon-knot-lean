import NormalizedSupportingLine

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.CyclicCarrierClearing
open AuxiliaryCarrierChart UniversalCarrierDomain

/-- One actual good truncation line witnesses a nonzero polynomial in the
short-edge parameter. The scale/direction remains fixed throughout the limit. -/
theorem fixed_direction_inventory_punctured {n : ℕ}
    (q : Fin n → PlanarPoint ℝ) (a U v : PlanarPoint ℝ) (ε₀ : ℝ)
    (hU : UniversalLocus (canonicalAugmentedCarrier q
      (v,-planarDet v (a+ε₀ • U))))
    (hT : PairTransverse (canonicalAugmentedCarrier q
      (v,-planarDet v (a+ε₀ • U))))
    (hC : allCycleSecantExclusions (canonicalAugmentedCarrier q
      (v,-planarDet v (a+ε₀ • U)))) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε < δ →
      UniversalLocus (canonicalAugmentedCarrier q (v,-planarDet v (a+ε • U))) ∧
      PairTransverse (canonicalAugmentedCarrier q (v,-planarDet v (a+ε • U))) ∧
      allCycleSecantExclusions (canonicalAugmentedCarrier q (v,-planarDet v (a+ε • U))) := by
  obtain ⟨P,hP⟩ := exists_canonical_inventory_polynomial n
  let x : ℝ → JointCoordinates n → ℝ := fun t => Sum.elim
    (fun p => if p.2 = 0 then (q p.1).1 else (q p.1).2)
    (fun i => if i = 0 then v.1 else if i = 1 then v.2 else -planarDet v (a+t • U))
  have hxv (t : ℝ) : jointVertices (x t) = q := by
    funext i
    simp [jointVertices,x]
  have hxL (t : ℝ) : jointLine (x t) = (v,-planarDet v (a+t • U)) := by
    apply Prod.ext
    · apply Prod.ext <;> simp [jointLine,x]
    · simp [jointLine,x]
  have ha (t : ℝ) : (fun i => x 0 i+t*(x 1 i-x 0 i)) = x t := by
    funext i
    rcases i with p|i
    · simp [x]
    · fin_cases i <;> simp [x,planarDet,smul_eq_mul] <;> ring
  have hw : MvPolynomial.eval (x ε₀) P ≠ 0 := by
    apply (hP (x ε₀)).mpr
    rw [hxv,hxL]
    exact ⟨hT,hU,hC⟩
  have hw' : MvPolynomial.eval (fun i => x 0 i+ε₀*(x 1 i-x 0 i)) P ≠ 0 := by
    rw [ha]
    exact hw
  obtain ⟨δ,hδ,hδP⟩ := affine_inventory_punctured P (x 0) (fun i => x 1 i-x 0 i) ε₀ hw'
  refine ⟨δ,hδ,?_⟩
  intro ε hε hεδ
  have he := hδP ε hε hεδ
  rw [ha] at he
  have hh := (hP (x ε)).mp he
  rw [hxv,hxL] at hh
  exact ⟨hh.2.1,hh.1,hh.2.2⟩

end DirectGLSSW.CyclicCarrierClearing

