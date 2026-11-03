import SeparatingSupportEventCuts
import CellChainProduct

set_option autoImplicit false

namespace DirectGLSSW.SupportCellSums
open OrderedCapEvents MixedEdgeChainsV3 FiniteSupportCuts MixedEdgeSupportOrder
open MixedEventOrder MixedCapChainRestriction SeparatingSupportEventCuts
open SelectedCellClippedWord CellChainProduct
open scoped BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable

instance edgeSeparatingSupportFintype {n : ℕ} (q : Fin n → PlanarPoint ℝ)
    (hq : cyclicNoTripleIntersections q) (e : Fin n)
    (hflat : (q e).2 = (q (cyclicSuccessor e)).2)
    (hleft : (q (cyclicSuccessor e)).1 < (q e).1) :
    Fintype (EdgeSeparatingSupport q hq e hflat hleft) := by
  classical
  unfold EdgeSeparatingSupport
  infer_instance

theorem ordered_support_toFinset {n : ℕ} (q : Fin n → PlanarPoint ℝ)
    (hq : CyclicGeneric q) (e : Fin n)
    (hflat : (q e).2 = (q (cyclicSuccessor e)).2)
    (hleft : (q (cyclicSuccessor e)).1 < (q e).1)
    (T : EdgeSeparatingSupport q hq.g2 e hflat hleft) :
    (edgeSupportOrderEquiv q hq.g2 hq.size_ge_three e hflat hleft T).val.toFinset = T.val := by
  exact congrArg Subtype.val
    ((edgeSupportOrderEquiv q hq.g2 hq.size_ge_three e hflat hleft).symm_apply_apply T)

variable {n m : ℕ} (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q) (e : Fin n)
    (hflat : (q e).2 = (q (cyclicSuccessor e)).2)
    (hleft : (q (cyclicSuccessor e)).1 < (q e).1)
    (Q : ℕ → PlanarPoint ℝ) (u v : EventIndex Q m) (huv : u < v)
    (E : DirectGLSSW.EdgeChord q e ≃ ↥(Finset.Ioo u.val v.val))
    (F : DirectGLSSW.EdgeChord q e → EventIndex Q m)
    (hF : ∀ z, (E z).val = (F z).val)
    (offset : ℝ) (htime : ∀ z, eventTime Q m (F z) = (crossingPoint q z.val).1-offset)
    (hpU : eventPair Q m u = (1,2)) (hpV : eventPair Q m v = (n-1,n))
    (hpairs : ∀ z, eventPair Q m (F z) =
      (complementaryEventRank e
        (crossingVisitEdge q (DirectGLSSW.returnVisit q e z))+1,
       complementaryEventRank e
        (crossingVisitEdge q (DirectGLSSW.returnVisit q e z))+2))

theorem separating_support_term_product
    (T : EdgeSeparatingSupport q hq.g2 e hflat hleft) :
    let Φ := edgeSupportEventCutEquiv q hq e hflat hleft Q u v huv E F hF
      offset htime hpU hpV hpairs
    let L := (edgeSupportOrderEquiv q hq.g2 hq.size_ge_three e hflat hleft T).val
    branchProduct (eventIntervalArray Q m) (cutVertices u.val v.val (Φ T).val.val) =
      ∏ i : Fin (L.length+1),
        eventMatrix Q m (leftBoundary u F L i) (rightBoundary v F L i) := by
  dsimp only
  let L := (edgeSupportOrderEquiv q hq.g2 hq.size_ge_three e hflat hleft T).val
  have hT : L.toFinset = T.val := ordered_support_toFinset q hq e hflat hleft T
  have hL : (L.map F).Pairwise (· < ·) := by
    apply List.pairwise_map.mpr
    have hpair := (edgeSupportOrderEquiv q hq.g2 hq.size_ge_three e hflat hleft T).property.2.2
    exact hpair.imp (fun {c d} h =>
      (event_lt_iff_abscissa_lt q e Q F offset htime c d).mpr h.1)
  change branchProduct (eventIntervalArray Q m)
    (cutVertices u.val v.val (supportCutMap E T.val).val) = _
  calc
    _ = branchProduct (eventIntervalArray Q m)
        (cutVertices u.val v.val (supportCutMap E L.toFinset).val) := by rw [hT]
    _ = _ := by
      convert support_cut_branchProduct_eq_cellProduct Q m u v huv E F hF L hL using 1
      congr 3
      ext z
      simp [supportCutMap]

include E hF offset htime hpU hpV hpairs in
/-- Reindex the signed event expansion by actual separating supports, retaining
the actual event-matrix factor at each consecutive cell. -/
theorem event_cut_sum_eq_support_cell_sum :
    (∑ S : ArcIncreasingEventCuts Q m u v huv,
      (-1 : ℚ)^(S.val.val.card+1) *
        branchProduct (eventIntervalArray Q m) (cutVertices u.val v.val S.val.val)) =
    ∑ T : EdgeSeparatingSupport q hq.g2 e hflat hleft,
      let L := (edgeSupportOrderEquiv q hq.g2 hq.size_ge_three e hflat hleft T).val
      (-1 : ℚ)^(T.val.card+1) * ∏ i : Fin (L.length+1),
        eventMatrix Q m (leftBoundary u F L i) (rightBoundary v F L i) := by
  let Φ := edgeSupportEventCutEquiv q hq e hflat hleft Q u v huv E F hF
    offset htime hpU hpV hpairs
  rw [← Φ.sum_comp (fun S => (-1 : ℚ)^(S.val.val.card+1) *
    branchProduct (eventIntervalArray Q m) (cutVertices u.val v.val S.val.val))]
  apply Finset.sum_congr rfl
  intro T _
  have hcard := edgeSupportEventCutEquiv_card q hq e hflat hleft Q u v huv E F hF
    offset htime hpU hpV hpairs T
  have hprod := separating_support_term_product q hq e hflat hleft Q u v huv E F hF
    offset htime hpU hpV hpairs T
  change (-1 : ℚ)^((Φ T).val.val.card+1) * _ = _
  change (Φ T).val.val.card = T.val.card at hcard
  rw [hcard]
  exact congrArg (fun x : ℚ => (-1 : ℚ)^(T.val.card+1)*x) hprod




end
end DirectGLSSW.SupportCellSums
