import ActiveArcCornerClosedWeights
import OpenCurrentWordCongruence

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace DirectGLSSW.ActiveArc.Split
open Primitive RetainedWords PermutationOrbits
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {b : ℕ} (q : Fin (1+b+2) → PlanarPoint ℝ) (hR : Regular q)
variable (hfree : ∀ d : Crossing q, d.val.1 ≠ 0)

/-- Exact prefix identity on the finite range used by the current. -/
theorem corner_rootedWord_prefix (T : Support (suffix q) (regular_suffix q hR))
    (k : ℕ) (hk : k<openCount q hR (firstEdgeFreeSupportEquiv q hfree hR T).val) :
    rootedPolygonWord (OpenVertex q hR (firstEdgeFreeSupportEquiv q hfree hR T))
      (openLast q hR (firstEdgeFreeSupportEquiv q hfree hR T).val) k =
    if k=0 then q 0 else rootedPolygonWord
      (OpenVertex (suffix q) (regular_suffix q hR) T)
      (openLast (suffix q) (regular_suffix q hR) T.val) (k-1) := by
  by_cases hz : k=0
  · subst k
    simpa only [ite_true] using corner_rootedWord_zero q hR hfree T
  · have hcount := corner_openCount q hR hfree T
    have hp : k-1<openCount (suffix q) (regular_suffix q hR) T.val := by omega
    have he := corner_rootedWord_shift q hR hfree T (k-1) hp
    have hsucc : k-1+1=k := by omega
    simpa only [hsucc,if_neg hz] using he

theorem corner_openCurrent_eq_prefix (T : Support (suffix q) (regular_suffix q hR)) :
    openCurrent q hR (firstEdgeFreeSupportEquiv q hfree hR T) =
    OpenMarkedCurrent.entry (polygonSignArray (fun k => if k=0 then q 0 else
      rootedPolygonWord (OpenVertex (suffix q) (regular_suffix q hR) T)
        (openLast (suffix q) (regular_suffix q hR) T.val) (k-1)))
      0 (openCount (suffix q) (regular_suffix q hR) T.val) := by
  rw [openCurrent_eq_entry_of_word_eq q hR (firstEdgeFreeSupportEquiv q hfree hR T)
    (fun k => if k=0 then q 0 else
      rootedPolygonWord (OpenVertex (suffix q) (regular_suffix q hR) T)
        (openLast (suffix q) (regular_suffix q hR) T.val) (k-1)) ?_]
  · rw [corner_openCount q hR hfree T]
    simp only [Nat.add_sub_cancel]
  · intro k hk
    exact (corner_rootedWord_prefix q hR hfree T k hk).symm.trans
      (openCurrent_word q hR (firstEdgeFreeSupportEquiv q hfree hR T) k hk)

/-- Actual ΓM, reindexed by actual suffix supports with original auxiliary input only. -/
theorem firstEdgeFree_GammaM_eq_weighted_suffix (hRI : GLSSWRootIndependence)
    (hAux : ClosedAuxiliary q hR) :
    GammaM q hR hAux =
    ∑ T : Support (suffix q) (regular_suffix q hR), (-1 : ℚ)^T.val.card *
      (OpenMarkedCurrent.entry (polygonSignArray (fun k => if k=0 then q 0 else
        rootedPolygonWord (OpenVertex (suffix q) (regular_suffix q hR) T)
          (openLast (suffix q) (regular_suffix q hR) T.val) (k-1)))
        0 (openCount (suffix q) (regular_suffix q hR) T.val) *
      ∏ D ∈ Finset.univ.erase (openComponent (suffix q) (regular_suffix q hR).noTriple T.val),
        closedWeight (suffix q) (regular_suffix q hR)
          (corner_closedAuxiliary_suffix q hR hfree hAux) T D) := by
  unfold GammaM
  symm
  apply Fintype.sum_equiv (firstEdgeFreeSupportEquiv q hfree hR)
  intro T
  rw [firstEdgeFreeSupportEquiv_card q hfree hR T,
    corner_openCurrent_eq_prefix q hR hfree T,
    ← corner_closedWeight_product_eq q hR hfree hRI hAux T]

end DirectGLSSW.ActiveArc.Split
