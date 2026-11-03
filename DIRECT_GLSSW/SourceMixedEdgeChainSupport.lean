import SupportCellSums
import DirectGLSSW.MixedCellOrbitWord

set_option autoImplicit false
namespace DirectGLSSW.SourceMixedEdgeChainSupport
open MixedConsecutiveCapWord MixedEdgeSupportOrder MixedEdgeComponentRoots
open SelectedCellClippedWord ExtendedReturnArcGeometry CrossingCapPairing
open DaughterFirstReturn PermutationOrbits PolygonNonalternation
open OrderedCapEvents MixedEdgeChainsV3 MixedCapChainRestriction
noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

theorem exists_actual_support_cut_equiv
    {n : ℕ} (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q) (e : Fin n)
    (hU : (q (cyclicSuccessor e)).2 = 0) (hV : (q e).2 = 0)
    (hleft : (q (cyclicSuccessor e)).1 < (q e).1) (ε : ℝ) (hε : 0 < ε) :
    let Q := extendedArc hq.size_ge_three (q ∘ cyclicVertexEquiv e) ε
    ∃ u v : EventIndex Q n,
      eventTime Q n u = 0 ∧
      eventTime Q n v = (q e).1-(q (cyclicSuccessor e)).1 ∧
      ∃ huv : u < v,
      ∃ Φ : EdgeSeparatingSupport q hq.g2 e (hV.trans hU.symm) hleft ≃
        ArcIncreasingEventCuts Q n u v huv,
      ∀ T, (Φ T).val.val.card = T.val.card := by
  exact SeparatingSupportEventCuts.exists_actual_support_cut_equiv q hq e hU hV hleft ε hε

theorem clipped_cell_is_actual_daughter (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (e : Fin n) (hU : (q (cyclicSuccessor e)).2 = 0) (hV : (q e).2 = 0)
    (hleft : (q (cyclicSuccessor e)).1 < (q e).1) (ε : ℝ)
    (L : List (DirectGLSSW.EdgeChord q e)) (hL : OrderedEdgeSupport q hq e L)
    (i : Fin (L.length+1)) :
    let A := polygonEventPoint q (cellLeftEvent q e L i)
    let B := polygonEventPoint q (cellRootEvent q e L i)
    let k := leftBoundary 1 (fun z => returnRank q e z+1) L i
    let l := rightBoundary (n-1) (fun z => returnRank q e z+1) L i
    List.ofFn (crossingClippedCapWord (extendedArc hq.size_ge_three (q ∘ cyclicVertexEquiv e) ε)
      (A.1-(q (cyclicSuccessor e)).1) (B.1-(q (cyclicSuccessor e)).1) k l) =
      (daughterPointList q hq.g2 (supportOfList q e L) (cellRootEvent q e L i)).rotate 1 := by
  rw [MixedCellOrbitWord.daughterPointList_eq_cellEventWord q hq e
    (hV.trans hU.symm) hleft L hL i]
  exact clipped_cell_word q hq e hU hV hleft ε L hL i

/-- Every cell root labels exactly one actual oriented smoothing component. -/
theorem cells_biject_actual_components
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q) (e : Fin n)
    (L : List (EdgeChord q e)) (hL : L.Nodup)
    (hNA : polygonNonalternating q hq.g2 (supportOfList q e L)) :
    Function.Bijective (fun i : Fin (L.length+1) =>
      componentOf (smoothingDartPermutation q hq.g2 (supportOfList q e L))
        (cellRootEvent q e L i)) := by
  classical
  have h := (rootComponent_bijective q hq.g2 hq.size_ge_three e L.toFinset hNA).comp
    (cellRootEquiv q e L hL).bijective
  simpa only [Function.comp_def, rootComponent, ← cellRootEvent_eq_rootEvent,
    supportOfList] using h

/-- The inverse-expansion sign counts the actual r+1 cells. -/
theorem support_sign_is_cell_sign
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q) (e : Fin n)
    (hflat : (q e).2 = (q (cyclicSuccessor e)).2)
    (hleft : (q (cyclicSuccessor e)).1 < (q e).1)
    (T : EdgeSeparatingSupport q hq.g2 e hflat hleft) :
    let L := (edgeSupportOrderEquiv q hq.g2 hq.size_ge_three e hflat hleft T).val
    (-1 : ℚ)^(T.val.card+1) = (-1 : ℚ)^(L.length+1) := by
  classical
  dsimp only
  have h := SupportCellSums.ordered_support_toFinset q hq e hflat hleft T
  rw [← h, List.toFinset_card_of_nodup
    (edgeSupportOrderEquiv q hq.g2 hq.size_ge_three e hflat hleft T).property.2.1]

/-- On the actual separating-support domain, all cell and component side
conditions are discharged by the canonical increasing-chain equivalence. -/
theorem separating_support_cells_are_all_components
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q) (e : Fin n)
    (hflat : (q e).2 = (q (cyclicSuccessor e)).2)
    (hleft : (q (cyclicSuccessor e)).1 < (q e).1)
    (T : EdgeSeparatingSupport q hq.g2 e hflat hleft) :
    let L := (edgeSupportOrderEquiv q hq.g2 hq.size_ge_three e hflat hleft T).val
    OrderedEdgeSupport q hq e L ∧
    supportOfList q e L = T.val.image Subtype.val ∧
    Function.Bijective (fun i : Fin (L.length+1) =>
      componentOf (smoothingDartPermutation q hq.g2 (T.val.image Subtype.val))
        (cellRootEvent q e L i)) := by
  classical
  dsimp only
  let L := (edgeSupportOrderEquiv q hq.g2 hq.size_ge_three e hflat hleft T).val
  have hL : OrderedEdgeSupport q hq e L :=
    (edgeSupportOrderEquiv q hq.g2 hq.size_ge_three e hflat hleft T).property.2
  have hs : supportOfList q e L = T.val.image Subtype.val := by
    unfold supportOfList
    rw [SupportCellSums.ordered_support_toFinset q hq e hflat hleft T]
  refine ⟨hL, hs, ?_⟩
  have hb := cells_biject_actual_components q hq e L hL.1
    (by rw [hs]; exact T.property.2)
  rw [← hs]
  exact hb







end
end DirectGLSSW.SourceMixedEdgeChainSupport
