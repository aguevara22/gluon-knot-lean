import ActiveArcOpenReconstruction

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.OpenCarrier
open DirectGLSSW ActiveArc AuxiliaryCarrierChart Filter Topology
variable {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ)

/-- The denominator-valid locus of the endpoint-coordinate chart. -/
def OpenChartNondegenerate (L : Fin (n+1) ⊕ Unit → CarrierLine) : Prop :=
  lineDenominator (initialLine q) (L (Sum.inl 0))≠0 ∧
  lineDenominator (L (Sum.inl ⟨n,by omega⟩)) (L (Sum.inr ()))≠0 ∧
  ∀ (i : Fin (n+2)) (h0 : i.val≠0) (ht : i.val≠n+1),
    lineDenominator (L (Sum.inl ⟨i.val-1,by have := i.isLt; omega⟩))
      (L (Sum.inl ⟨i.val,by have := i.isLt; omega⟩))≠0

theorem openChartLines_nondegenerate (hR : Regular q) (hG1 : cyclicNoncollinear q) :
    OpenChartNondegenerate q (openChartLines q) :=
  ⟨initialLine_denominator_ne q hR, terminalLine_denominator_ne q hR,
    adjacent_denominator_ne q hG1⟩

/-- On the valid chart every reconstructed physical edge belongs to its assigned line. -/
theorem reconstructOpen_incidence
    (L : Fin (n+1) ⊕ Unit → CarrierLine) (hL : OpenChartNondegenerate q L)
    (e : Fin (n+1)) :
    lineValue (L (Sum.inl e)) (reconstructOpen q L e.castSucc)=0 ∧
    lineValue (L (Sum.inl e)) (reconstructOpen q L e.succ)=0 := by
  constructor
  · by_cases h0 : e.val=0
    · have he : e=0 := Fin.ext h0
      subst e
      simpa only [reconstructOpen,Fin.coe_castSucc,Fin.val_zero,dif_pos rfl] using
        lineValue_intersection_right (initialLine q) (L (Sum.inl 0)) hL.1
    · have ht : e.castSucc.val≠n+1 := by have := e.isLt; simp only [Fin.coe_castSucc]; omega
      have hz : e.castSucc.val≠0 := h0
      rw [reconstructOpen,dif_neg hz,dif_neg ht]
      exact lineValue_intersection_right _ _ (hL.2.2 e.castSucc h0 ht)
  · have h0 : e.succ.val≠0 := by simp only [Fin.val_succ]; omega
    by_cases ht : e.succ.val=n+1
    · have he : e=⟨n,by omega⟩ := by
        apply Fin.ext
        change e.val=n
        change e.val+1=n+1 at ht
        omega
      rw [reconstructOpen,dif_neg h0,dif_pos ht,he]
      exact lineValue_intersection_left _ _ hL.2.1
    · rw [reconstructOpen,dif_neg h0,dif_neg ht]
      have he : (⟨e.succ.val-1,by have := e.succ.isLt; omega⟩ : Fin (n+1))=e :=
        Fin.ext (by simp only [Fin.val_succ]; omega)
      have h := lineValue_intersection_left _ _ (hL.2.2 e.succ h0 ht)
      simpa only [he] using h

/-- Both coordinate-only lines remain incident with their designated endpoints. -/
theorem reconstructOpen_endpoint_incidence
    (L : Fin (n+1) ⊕ Unit → CarrierLine) (hL : OpenChartNondegenerate q L) :
    lineValue (initialLine q) (reconstructOpen q L 0)=0 ∧
    lineValue (L (Sum.inr ())) (reconstructOpen q L ⟨n+1,by omega⟩)=0 := by
  constructor
  · simpa only [reconstructOpen,Fin.val_zero,dif_pos rfl] using
      lineValue_intersection_left (initialLine q) (L (Sum.inl 0)) hL.1
  · simpa only [reconstructOpen,show n+1≠0 by omega,dif_neg,dif_pos rfl] using
      lineValue_intersection_right (L (Sum.inl ⟨n,by omega⟩)) (L (Sum.inr ())) hL.2.1

theorem eventually_openChartNondegenerate (hR : Regular q) (hG1 : cyclicNoncollinear q) :
    ∀ᶠ L in 𝓝 (openChartLines q), OpenChartNondegenerate q L := by
  have hz : ∀ᶠ L in 𝓝 (openChartLines q), lineDenominator (initialLine q) (L (Sum.inl 0))≠0 := by
    have hc : Continuous (fun L : Fin (n+1) ⊕ Unit → CarrierLine =>
        lineDenominator (initialLine q) (L (Sum.inl 0))) := by
      unfold lineDenominator planarDet
      fun_prop
    exact hc.continuousAt.eventually_ne (initialLine_denominator_ne q hR)
  have ht : ∀ᶠ L in 𝓝 (openChartLines q),
      lineDenominator (L (Sum.inl ⟨n,by omega⟩)) (L (Sum.inr ()))≠0 := by
    have hc : Continuous (fun L : Fin (n+1) ⊕ Unit → CarrierLine =>
        lineDenominator (L (Sum.inl ⟨n,by omega⟩)) (L (Sum.inr ()))) := by
      unfold lineDenominator planarDet
      fun_prop
    exact hc.continuousAt.eventually_ne (terminalLine_denominator_ne q hR)
  have hm : ∀ᶠ L in 𝓝 (openChartLines q),
      ∀ (i : Fin (n+2)) (h0 : i.val≠0) (ht : i.val≠n+1),
        lineDenominator (L (Sum.inl ⟨i.val-1,by have := i.isLt; omega⟩))
          (L (Sum.inl ⟨i.val,by have := i.isLt; omega⟩))≠0 := by
    apply Filter.eventually_all.mpr
    intro i
    by_cases h0 : i.val=0
    · exact Filter.Eventually.of_forall (fun _ h => False.elim (h h0))
    · by_cases hi : i.val=n+1
      · exact Filter.Eventually.of_forall (fun _ _ h => False.elim (h hi))
      · have hc : Continuous (fun L : Fin (n+1) ⊕ Unit → CarrierLine =>
            lineDenominator (L (Sum.inl ⟨i.val-1,by have := i.isLt; omega⟩))
              (L (Sum.inl ⟨i.val,by have := i.isLt; omega⟩))) := by
          unfold lineDenominator planarDet
          fun_prop
        exact (hc.continuousAt.eventually_ne (adjacent_denominator_ne q hG1 i h0 hi)).mono
          (fun _ h _ _ => h)
  exact hz.and (ht.and hm)

/-- Every arc neighborhood pulls back to a valid neighborhood in independent carrier coordinates. -/
theorem eventually_reconstructOpen_valid_mem
    (hR : Regular q) (hG1 : cyclicNoncollinear q)
    (U : Set (Fin (n+2) → PlanarPoint ℝ)) (hU : U ∈ 𝓝 q) :
    ∀ᶠ L in 𝓝 (openChartLines q),
      OpenChartNondegenerate q L ∧ reconstructOpen q L ∈ U ∧
      ∀ e : Fin (n+1),
        lineValue (L (Sum.inl e)) (reconstructOpen q L e.castSucc)=0 ∧
        lineValue (L (Sum.inl e)) (reconstructOpen q L e.succ)=0 := by
  have hnear : ∀ᶠ L in 𝓝 (openChartLines q), reconstructOpen q L ∈ U := by
    apply (reconstructOpen_continuousAt q hR hG1).eventually
    simpa only [reconstructOpen_recovery q hR hG1] using hU
  filter_upwards [eventually_openChartNondegenerate q hR hG1,hnear] with L hL hLU
  exact ⟨hL,hLU,reconstructOpen_incidence q L hL⟩





end DirectGLSSW.ActiveArc.OpenCarrier
