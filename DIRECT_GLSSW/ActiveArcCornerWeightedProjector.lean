import ActiveArcCornerPrefixSign
import ActiveArcParentConditionalProjector
import OpenCurrentFarRadius

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.CornerProjector
open Cursor Split Primitive RetainedWords CompatibleWords OpenFirstEdgeGeometry ShortEdgeSignStability
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- Weighted short-edge formula on the actual suffix supports. The suffix
closed auxiliary condition is explicit here and will be supplied by transport
from the original arc in the physical GammaM consumer. -/
theorem exists_weighted_left_corner_projector
    {b : ℕ} (q : Fin (1+b+2) → PlanarPoint ℝ) (hR : Regular q)
    (hAux : ClosedAuxiliary (suffix q) (regular_suffix q hR))
    (hleft : 0<planarDet (q 1-q 0) (q 2-q 1))
    (hfar : ∀ T : Primitive.Support (suffix q) (regular_suffix q hR),
      ∀ k j, 1<k → k<j → j≤openCount (suffix q) (regular_suffix q hR) T.val →
        polygonHDet (fun k => if k=0 then q 0 else
          rootedPolygonWord (OpenVertex (suffix q) (regular_suffix q hR) T)
            (openLast (suffix q) (regular_suffix q hR) T.val) (k-1)) 1 k j≠0) :
    let p := suffix q
    let hp := regular_suffix q hR
    let P := fun T : Primitive.Support p hp => fun k => if k=0 then q 0 else
      rootedPolygonWord (OpenVertex p hp T) (openLast p hp T.val) (k-1)
    ∃ ρ : ℝ, 0<ρ ∧ ρ≤1 ∧ ∀ η : ℝ, 0<η → η<ρ →
      (∑ T : Primitive.Support p hp, (-1:ℚ)^T.val.card *
        (OpenMarkedCurrent.entry (polygonSignArray (approach (P T) η))
          0 (openCount p hp T.val) *
          ∏ C∈Finset.univ.erase (openComponent p hp.noTriple T.val),
            closedWeight p hp hAux T C)) = -GammaM p hp hAux := by
  let p := suffix q
  let hp := regular_suffix q hR
  let P := fun T : Primitive.Support p hp => fun k => if k=0 then q 0 else
    rootedPolygonWord (OpenVertex p hp T) (openLast p hp T.val) (k-1)
  let N := fun T : Primitive.Support p hp => openCount p hp T.val
  let R : Primitive.Support p hp → ℝ → Prop := fun T η =>
    OpenMarkedCurrent.entry (polygonSignArray (approach (P T) η)) 0 (N T) =
      -openCurrent p hp T
  have hlocal : ∀ T, T∈(Finset.univ : Finset (Primitive.Support p hp)) →
      ∃ δ : ℝ, 0<δ ∧ ∀ η : ℝ, 0<η → η<δ → R T η := by
    intro T _
    obtain ⟨δ,hδ,_,hgood⟩ := OpenCurrentFarRadius.exists_far_radius_entry_short_first
      (P T) (N T) (hfar T)
    refine ⟨δ,hδ,?_⟩
    intro η hη hηδ
    have hN : 1<N T := lt_of_lt_of_le (by decide : 1<2) (open_count_ge_two p hp T.val)
    have hv := (hgood η hη hηδ).2 (N T) hN le_rfl
    have hs : polygonSignArray (P T) 0 1 2 = -1 :=
      suffix_retained_prefix_sign012_eq_neg_one q hR T hleft
    have ht : OpenMarkedCurrent.entry (polygonSignArray (P T)) 1 (N T)=openCurrent p hp T :=
      TinyParentConditional.prefixed_tail_entry p hp T (q 0)
    rw [hs,ht] at hv
    norm_num at hv
    exact hv
  obtain ⟨δ,hδ,hgood⟩ := exists_finset_common_radius
    (Finset.univ : Finset (Primitive.Support p hp)) R hlocal
  refine ⟨min δ 1,lt_min hδ (by norm_num),min_le_right _ _,?_⟩
  intro η hη hηδ
  have hentry : ∀ T : Primitive.Support p hp,
      OpenMarkedCurrent.entry (polygonSignArray (approach (P T) η)) 0 (N T)=
        -openCurrent p hp T := by
    intro T
    exact hgood η hη (lt_of_lt_of_le hηδ (min_le_left _ _)) T (Finset.mem_univ T)
  change (∑ T : Primitive.Support p hp, (-1:ℚ)^T.val.card *
    (OpenMarkedCurrent.entry (polygonSignArray (approach (P T) η)) 0 (N T) *
      ∏ C∈Finset.univ.erase (openComponent p hp.noTriple T.val),
        closedWeight p hp hAux T C)) = -GammaM p hp hAux
  unfold GammaM
  rw [←Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro T _
  rw [hentry T]
  ring


end DirectGLSSW.ActiveArc.CornerProjector
