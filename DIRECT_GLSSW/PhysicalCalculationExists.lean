import PhysicalCalculationData
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
noncomputable section
namespace DirectGLSSW.ActiveArc.FiniteCalculation
open Cursor Split Primitive RetainedWords OpenCarrier AuxiliaryCarrierChart UniversalCarrierDomain
open CompatibleWords SingletonWords ChildRestartRecursion

/-- Every actual working-domain state admits a finite literal geometric
calculation. All child states and current equations are constructed from the
physical step theorems; the only induction is the accepted actual ActiveStep. -/
theorem calculation_exists (hRI : GLSSWRootIndependence) {n : ℕ}
    (q : Fin (n+2) → PlanarPoint ℝ) (D : Domain q) : Calculation q D := by
  apply activeStep_induction (P := fun s => ∀ D : Domain s.2, Calculation s.2 D) ⟨n,q⟩ ?_ D
  intro s ih
  rcases s with ⟨n,q⟩
  intro D
  rcases TraversalClosure.actual_first_edge_selection q D.hleft with hn|hfirst|hfree
  · subst n
    apply Calculation.terminal q D
    rw [singleEdge_GammaM_one]
    norm_num [List.length_ofFn]
  · obtain ⟨c,hc⟩ := hfirst
    generalize hcut : c.val.2.val=a at *
    have ha : a≤n := by have := c.val.2.isLt;omega
    obtain ⟨b,rfl⟩ := Nat.exists_eq_add_of_le ha
    by_cases ho : crossingOver q (polygonCrossingOfArc q c)=(polygonCrossingOfArc q c).val.1
    · obtain ⟨ε,hε,hm0,hmc,hcp,hpb,hvalue,hG,hAux,hleft,hcore,hinc,hterminal⟩ :=
        exists_complete_first_over_step q D.hR D.hG D.hAux D.hleft hRI c hc hcut D.hcore
          D.L D.hL D.hT D.hinc D.hterminal ho
      let ht0 : 0≤leftParameter q c+ε := (lt_trans (leftParameter_spec q c).1 hcp).le
      let hA := (regular_first_window_iff q D.hR c hc _ ht0 hpb).mpr (ne_of_gt hcp)
      let A : Domain (moveStart q (leftParameter q c+ε)) :=
        ⟨hA,hG,hAux,hleft,hcore,D.L,D.hL,D.hT,hinc,hterminal⟩
      exact Calculation.over q D c hc ho ε hε hcp hpb A hvalue
        (ih _ (ActiveStep.afterFirst q D.hR c hc _ hcp hpb) A)
    · have hu : crossingUnder q (polygonCrossingOfArc q c)=(polygonCrossingOfArc q c).val.1 := by
        unfold crossingOver at ho
        unfold crossingUnder
        split_ifs with hsign
        · exact False.elim (ho (if_pos hsign))
        · rfl
      obtain ⟨ε,hε,hm0,hmc,hcp,hpb,hvalue,hpost,hPR,hPG,hPA,hPL,hPC,hML,hMT,hMI,hME⟩ :=
        exists_complete_first_under_step q D.hR D.hG D.hAux D.hleft hRI c hc hcut D.hcore
          D.L D.hL D.hT D.hinc D.hterminal hu
      obtain ⟨hG,hAux,hleft,hcore,hinc,hterminal⟩ := hpost
      let ht0 : 0≤leftParameter q c+ε := (lt_trans (leftParameter_spec q c).1 hcp).le
      let hA := (regular_first_window_iff q D.hR c hc _ ht0 hpb).mpr (ne_of_gt hcp)
      let A : Domain (moveStart q (leftParameter q c+ε)) :=
        ⟨hA,hG,hAux,hleft,hcore,D.L,D.hL,D.hT,hinc,hterminal⟩
      let P : Domain (parent q c hcut) :=
        ⟨hPR,hPG,hPA,hPL,hPC,D.L ∘ suffixCarrierMap (a:=a) (b:=b),hML,hMT,hMI,hME⟩
      exact Calculation.under q D c hc hcut hu ε hε hcp hpb A P hvalue
        (ih _ (ActiveStep.afterFirst q D.hR c hc _ hcp hpb) A)
        (ih _ (ActiveStep.parent q D.hR c hc hcut) P)
  · obtain ⟨hn,hfree,hfirst⟩ := hfree
    obtain ⟨b,rfl⟩ := Nat.exists_eq_add_of_le hn
    obtain ⟨hvalue,hSR,hSA,hSL,hSC,hML,hMT,hMI,hME⟩ :=
      CornerProjector.firstEdgeFree_left_corner_step q D.hR hfree D.hAux hRI D.hleft D.hcore
        D.L D.hL D.hT D.hinc D.hterminal
    let S : Domain (suffix q) :=
      ⟨hSR,TraversalClosure.suffix_G1 q D.hG,hSA,hSL,hSC,
        D.L ∘ suffixCarrierMap (a:=1) (b:=b),hML,hMT,hMI,hME⟩
    have hfirst' : 0<planarDet (q 1-q 0) (q 2-q 1) := by
      have he : (⟨2,by omega⟩ : Fin (1+b+2))=2 := by
        apply Fin.ext
        exact (Nat.mod_eq_of_lt (by omega : 2<1+b+2)).symm
      simpa only [he] using hfirst
    exact Calculation.corner q D hfree S hvalue
      (ih _ (ActiveStep.cornerSuffix q D.hR hfirst' hfree) S)
end DirectGLSSW.ActiveArc.FiniteCalculation
