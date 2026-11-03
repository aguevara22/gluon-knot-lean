import HistoricalChildSupportLift
import HistoricalChildEndpointOrder

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.HOMFLY.ProcessedExposedChild

open DirectGLSSW PolygonDrawingBridge LowestRowContract PermutationOrbits
open ActualLocalSupports SmoothingCornerGeometry

variable {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ) (hq : CyclicGeneric q)
    {t : MarkedParentState}
    (h : MarkedParentTrace (positivePolygonMarkedState q hq (initialAnchorTraversal q hq)) t)
    (c : Fin t.1.nCrossing) (hc : badAt t.2.1 c)
    (R : ComponentRestriction (smoothCrossing t.1 c)
      (rootSelfCutComponents t.1 c (t.2.2.connected _ _)
        (firstVisitedBranch t.2.1 c) (Sum.inl true)))
    (he : ExposedOpenPrimitive.LeftExposed q 0)
    (hAux : ActiveArc.Primitive.ClosedAuxiliary (ActiveArc.ExposedChart.cutArc q 0)
      (ActiveArc.ExposedChart.cutArc_regular q 0 hq))

private theorem perm_bool_flip (p : Equiv.Perm Bool) (b : Bool) :
    p (!b) = !(p b) := by
  have hne : p false ≠ p true := by
    intro h
    exact (by decide : (false : Bool) ≠ true) (p.injective h)
  cases b <;> cases h0 : p false <;> cases h1 : p true <;> simp_all

private theorem historicalChildLift_crossing_mem_iff
    (he : ExposedOpenPrimitive.LeftExposed q 0)
    (hAux : ActiveArc.Primitive.ClosedAuxiliary (ActiveArc.ExposedChart.cutArc q 0)
      (ActiveArc.ExposedChart.cutArc_regular q 0 hq))
    (S : Finset (PolygonCrossing (historicalSharpPolygon q hq h c hc R)))
    (d : PolygonCrossing (historicalSharpPolygon q hq h c hc R)) :
    historicalSharpPolygonCrossingMap q hq h c hc R d ∈
        historicalChildLift q hq h c hc R S ↔
      d ∈ S := by
  classical
  unfold historicalChildLift
  rw [Finset.mem_image]
  constructor
  · rintro ⟨d',hd',heq⟩
    have hinj := historicalSharpPolygonCrossingMap_injective q hq h c hc R he hAux
    have hEq : d' = d := hinj heq
    simpa [hEq] using hd'
  · intro hd
    exact ⟨d,hd,rfl⟩

private theorem historicalChildVisit_maps
    (d : PolygonCrossing (historicalSharpPolygon q hq h c hc R)) (b : Bool) :
    retainedEventMap q hq h c hc R
      (PolygonDrawing.visit (historicalSharpPolygon q hq h c hc R) d
        (if b then 1 else 0)) =
    PolygonDrawing.visit q (historicalSharpPolygonCrossingMap q hq h c hc R d)
      (if historicalChildBranchBool q hq h c hc R d b then 1 else 0) := by
  have hh := retainedEventMap_matched_visit q hq h c hc R d
    (if historicalChildBranchBool q hq h c hc R d b then 1 else 0)
  simpa only [historicalChildBranchBool_fin] using hh

private theorem fin2_code_eq_zero (b : Bool) :
    decide ((if b then 1 else 0 : Fin 2) = 0) = !b := by
  cases b <;> rfl

private theorem historicalChildBranchFin_symm
    (d : PolygonCrossing (historicalSharpPolygon q hq h c hc R)) (b : Bool) :
    (historicalSharpBranchPermutation q hq h c hc R d).symm (if b then 1 else 0) =
      (if historicalChildBranchBool q hq h c hc R d b then 1 else 0) := by
  apply (historicalSharpBranchPermutation q hq h c hc R d).injective
  rw [Equiv.apply_symm_apply]
  exact (historicalChildBranchBool_fin q hq h c hc R d b).symm

private theorem retainedEventMap_visit_bool
    (d : PolygonCrossing (historicalSharpPolygon q hq h c hc R)) (b : Bool) :
    retainedEventMap q hq h c hc R (Sum.inr (d,b)) =
      Sum.inr (historicalSharpPolygonCrossingMap q hq h c hc R d,
        historicalChildBranchBool q hq h c hc R d b) := by
  have hh := retainedEventMap_visit q hq h c hc R d (if b then 1 else 0)
  rw [historicalChildBranchFin_symm q hq h c hc R d b] at hh
  simpa [PolygonDrawing.visit] using hh

/-- Pairing selected child visits commutes exactly with the retained-event map. -/
theorem retainedEventMap_pairing
    (he : ExposedOpenPrimitive.LeftExposed q 0)
    (hAux : ActiveArc.Primitive.ClosedAuxiliary (ActiveArc.ExposedChart.cutArc q 0)
      (ActiveArc.ExposedChart.cutArc_regular q 0 hq))
    (S : Finset (PolygonCrossing (historicalSharpPolygon q hq h c hc R)))
    (x : PolygonEvent (historicalSharpPolygon q hq h c hc R)) :
    smoothingPairing q (historicalChildLift q hq h c hc R S)
      (retainedEventMap q hq h c hc R x) =
    retainedEventMap q hq h c hc R
      (smoothingPairing (historicalSharpPolygon q hq h c hc R) S x) := by
  classical
  let Q := historicalSharpPolygon q hq h c hc R
  let M := historicalSharpPolygonCrossingMap q hq h c hc R
  let F := retainedEventMap q hq h c hc R
  let lift := historicalChildLift q hq h c hc R S
  rcases x with i | ⟨d,b⟩
  · let z := retainedEventMap q hq h c hc R (Sum.inl i)
    have hz : DaughterFirstReturn.retainedCorner q (sharpSupport q hq h c) z := by
      simpa [z, retainedEventMap, DaughterFirstReturn.retainedCorner] using
        (DaughterFirstReturn.cornerEnumeration q hq.g2 (sharpSupport q hq h c)
          (sharpIntervalEvent q hq h c hc R ⟨0,detachedOldOrbitSize_pos c R⟩) i).property
    have hfixed : smoothingPairingMap q lift z = z := by
      cases hzEvent : z with
      | inl a => simp [smoothingPairingMap, hzEvent]
      | inr v =>
          have hv : v.1 ∈ sharpSupport q hq h c := by
            simpa [hzEvent, DaughterFirstReturn.retainedCorner] using hz
          have hdis := historicalChildLift_disjoint q hq h c hc R he hAux S
          have hvnot : v.1 ∉ lift := (Finset.disjoint_left.mp hdis) hv
          simp [smoothingPairingMap, hzEvent, hvnot]
    change smoothingPairingMap q lift z = z
    exact hfixed
  · have hmem : M d ∈ lift ↔ d ∈ S := by
      simpa [M,lift] using historicalChildLift_crossing_mem_iff q hq h c hc R he hAux S d
    have hflip := perm_bool_flip (historicalChildBranchBool q hq h c hc R d) b
    by_cases hd : d ∈ S
    · have hm : M d ∈ lift := hmem.mpr hd
      change historicalSharpPolygonCrossingMap q hq h c hc R d ∈
        historicalChildLift q hq h c hc R S at hm
      have hbase := retainedEventMap_visit_bool q hq h c hc R d b
      have hswap := retainedEventMap_visit_bool q hq h c hc R d (!b)
      change smoothingPairingMap q (historicalChildLift q hq h c hc R S)
          (retainedEventMap q hq h c hc R (Sum.inr (d,b))) =
        retainedEventMap q hq h c hc R
          (smoothingPairingMap Q S (Sum.inr (d,b)))
      rw [hbase, smoothingPairingMap_visit, if_pos hm]
      have hchild : smoothingPairingMap Q S (Sum.inr (d,b)) = Sum.inr (d,!b) := by
        change smoothingPairingMap (historicalSharpPolygon q hq h c hc R) S
          (Sum.inr (d,b)) = Sum.inr (d,!b)
        simp [smoothingPairingMap, crossingVisitFlip, hd]
      rw [hchild, hswap]
      exact (congrArg (fun b' => Sum.inr (M d,b')) hflip).symm
    · have hm : M d ∉ lift := fun h => hd (hmem.mp h)
      change historicalSharpPolygonCrossingMap q hq h c hc R d ∉
        historicalChildLift q hq h c hc R S at hm
      have hbase := retainedEventMap_visit_bool q hq h c hc R d b
      change smoothingPairingMap q (historicalChildLift q hq h c hc R S)
          (retainedEventMap q hq h c hc R (Sum.inr (d,b))) =
        retainedEventMap q hq h c hc R
          (smoothingPairingMap Q S (Sum.inr (d,b)))
      rw [hbase, smoothingPairingMap_visit, if_neg hm]
      have hchild : smoothingPairingMap Q S (Sum.inr (d,b)) = Sum.inr (d,b) := by
        change smoothingPairingMap (historicalSharpPolygon q hq h c hc R) S
          (Sum.inr (d,b)) = Sum.inr (d,b)
        simp [smoothingPairingMap, hd]
      rw [hchild]
      exact hbase.symm

/-- Every event outside the retained-event image is fixed by the lifted
smoothing pairing. -/
theorem historicalChildLift_pairing_fixed_of_not_range
    (he : ExposedOpenPrimitive.LeftExposed q 0)
    (hAux : ActiveArc.Primitive.ClosedAuxiliary (ActiveArc.ExposedChart.cutArc q 0)
      (ActiveArc.ExposedChart.cutArc_regular q 0 hq))
    (S : Finset (PolygonCrossing (historicalSharpPolygon q hq h c hc R)))
    (y : PolygonEvent q)
    (hy : y ∉ Set.range (retainedEventMap q hq h c hc R)) :
    smoothingPairing q (historicalChildLift q hq h c hc R S) y = y := by
  classical
  rcases y with i | ⟨d,b⟩
  · simp [smoothingPairing_apply,smoothingPairingMap]
  · have hnot : d ∉ historicalChildLift q hq h c hc R S := by
      intro hd
      change d ∈ Finset.image (historicalSharpPolygonCrossingMap q hq h c hc R) S at hd
      obtain ⟨d',hd',heq⟩ := Finset.mem_image.mp hd
      let childBool := (historicalChildBranchBool q hq h c hc R d').symm b
      have hbranch : historicalChildBranchBool q hq h c hc R d' childBool = b := by
        simp [childBool]
      have himage :
          retainedEventMap q hq h c hc R
            (PolygonDrawing.visit (historicalSharpPolygon q hq h c hc R) d'
              (if childBool then 1 else 0)) = Sum.inr (d,b) := by
        have hvisit := historicalChildVisit_maps q hq h c hc R d' childBool
        rw [hvisit, hbranch, heq]
        simp [PolygonDrawing.visit]
      apply hy
      exact ⟨PolygonDrawing.visit (historicalSharpPolygon q hq h c hc R) d'
        (if childBool then 1 else 0), himage⟩
    change smoothingPairing q (historicalChildLift q hq h c hc R S) (Sum.inr (d,b)) = Sum.inr (d,b)
    exact (smoothingPairing_visit_fixed_iff q
      (historicalChildLift q hq h c hc R S) (d,b)).mpr hnot

#check @retainedEventMap_pairing

#check @historicalChildLift_pairing_fixed_of_not_range


end DirectGLSSW.HOMFLY.ProcessedExposedChild
