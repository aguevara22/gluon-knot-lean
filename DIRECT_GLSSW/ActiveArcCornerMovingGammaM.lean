import ActiveArcCornerGammaMReindex
import ActiveArcFirstEdgeFreeMotion
import ActiveArcCornerWeightedProjector

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace DirectGLSSW.ActiveArc.CornerProjector
open Cursor Split Primitive RetainedWords CompatibleWords OpenFirstEdgeGeometry
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- The entire suffix-weighted prefix expression, with its actual dependent
support family bundled so pointwise equality transports all indices together. -/
def weightedPrefixValue {n : ℕ} (p : Fin (n+2) → PlanarPoint ℝ) (hp : Regular p)
    (hAux : ClosedAuxiliary p hp) (x : PlanarPoint ℝ) : ℚ :=
  ∑ T : Support p hp, (-1:ℚ)^T.val.card *
    (OpenMarkedCurrent.entry (polygonSignArray (fun k => if k=0 then x else
      rootedPolygonWord (OpenVertex p hp T) (openLast p hp T.val) (k-1)))
      0 (openCount p hp T.val) *
      ∏ C∈Finset.univ.erase (openComponent p hp.noTriple T.val),closedWeight p hp hAux T C)

private theorem weightedPrefixValue_congr {n : ℕ}
    (p r : Fin (n+2) → PlanarPoint ℝ) (hp : Regular p) (hr : Regular r)
    (hAp : ClosedAuxiliary p hp) (hAr : ClosedAuxiliary r hr)
    (x y : PlanarPoint ℝ) (he : p=r) (hxy : x=y) :
    weightedPrefixValue p hp hAp x=weightedPrefixValue r hr hAr y := by
  subst r
  subst y
  rfl

/-- Actual closed auxiliary genericity along a crossing-free first edge is
transported through its unchanged physical suffix. -/
theorem firstEdgeFree_closedAuxiliary_moveStart
    {b : ℕ} (q : Fin (1+b+2) → PlanarPoint ℝ) (hR : Regular q)
    (hfree : ∀ c : Crossing q, c.val.1≠0) (hAux : ClosedAuxiliary q hR)
    (t : ℝ) (ht0 : 0≤t) (ht1 : t<1) :
    ClosedAuxiliary (moveStart q t) (firstEdgeFree_regular_moveStart q hR hfree t ht0 ht1) := by
  apply corner_closedAuxiliary_from_suffix _ _ (firstEdgeFree_moveStart q hfree t ht0 ht1)
  have hs := corner_closedAuxiliary_suffix q hR hfree hAux
  simpa only [corner_suffix_moveStart] using hs

/-- The moving physical current is exactly the short-first weighted suffix
family. Every diagrammatic support and closed factor is transported internally. -/
theorem firstEdgeFree_moving_GammaM_eq_weighted_approach
    {b : ℕ} (q : Fin (1+b+2) → PlanarPoint ℝ) (hR : Regular q)
    (hfree : ∀ c : Crossing q, c.val.1≠0) (hAux : ClosedAuxiliary q hR)
    (hRI : GLSSWRootIndependence) (η : ℝ) (hη : 0<η) (hη1 : η<1) :
    let ht0 : 0≤1-η := le_of_lt (sub_pos.mpr hη1)
    let ht1 : 1-η<1 := sub_lt_self 1 hη
    GammaM (moveStart q (1-η))
      (firstEdgeFree_regular_moveStart q hR hfree (1-η) ht0 ht1)
      (firstEdgeFree_closedAuxiliary_moveStart q hR hfree hAux (1-η) ht0 ht1) =
    ∑ T : Support (suffix q) (regular_suffix q hR), (-1:ℚ)^T.val.card *
      (OpenMarkedCurrent.entry (polygonSignArray
        (approach (fun k => if k=0 then q 0 else
          rootedPolygonWord (OpenVertex (suffix q) (regular_suffix q hR) T)
            (openLast (suffix q) (regular_suffix q hR) T.val) (k-1)) η))
          0 (openCount (suffix q) (regular_suffix q hR) T.val) *
        ∏ C∈Finset.univ.erase (openComponent (suffix q) (regular_suffix q hR).noTriple T.val),
          closedWeight (suffix q) (regular_suffix q hR)
            (corner_closedAuxiliary_suffix q hR hfree hAux) T C) := by
  dsimp only
  let r := moveStart q (1-η)
  let hr := firstEdgeFree_regular_moveStart q hR hfree (1-η)
    (le_of_lt (sub_pos.mpr hη1)) (sub_lt_self 1 hη)
  let hfr := firstEdgeFree_moveStart q hfree (1-η)
    (le_of_lt (sub_pos.mpr hη1)) (sub_lt_self 1 hη)
  let hAr := firstEdgeFree_closedAuxiliary_moveStart q hR hfree hAux (1-η)
    (le_of_lt (sub_pos.mpr hη1)) (sub_lt_self 1 hη)
  have hv : GammaM r hr hAr=weightedPrefixValue (suffix r) (regular_suffix r hr)
      (corner_closedAuxiliary_suffix r hr hfr hAr) (r 0) :=
    firstEdgeFree_GammaM_eq_weighted_suffix r hr hfr hRI hAr
  have he := weightedPrefixValue_congr (suffix r) (suffix q)
    (regular_suffix r hr) (regular_suffix q hR)
    (corner_closedAuxiliary_suffix r hr hfr hAr) (corner_closedAuxiliary_suffix q hR hfree hAux)
    (r 0) (affinePoint (q 1) (q 0) η)
    (corner_suffix_moveStart q (1-η)) (corner_moveStart_approach_endpoint q η)
  rw [hv,he]
  unfold weightedPrefixValue
  apply Finset.sum_congr rfl
  intro T _
  congr 2
  apply openMarkedCurrent_entry_congr_of_word_eq
    (N:=openCount (suffix q) (regular_suffix q hR) T.val) _ _
    (lt_of_lt_of_le (by decide : 0<2) (open_count_ge_two _ _ T.val))
  intro k hk
  by_cases hz : k=0
  · subst k
    rw [approach_zero]
    simp only [ite_true,show (1:ℕ)≠0 by decide,ite_false,Nat.sub_self]
    have hw := openCurrent_word (suffix q) (regular_suffix q hR) T 0
      (lt_of_lt_of_le (by decide : 0<2) (open_count_ge_two _ _ T.val))
    rw [openVertex_zero] at hw
    have hs : suffix q 0=q 1 := by simp [suffix,Split.vertex]
    rw [hw,hs]
  · rw [approach_pos _ η (Nat.pos_of_ne_zero hz)]
    simp only [if_neg hz]



end DirectGLSSW.ActiveArc.CornerProjector
