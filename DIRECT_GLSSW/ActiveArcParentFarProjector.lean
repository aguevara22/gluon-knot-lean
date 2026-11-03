import ActiveArcParentConditionalProjector
import OpenCurrentFarRadius

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.TinyParentFarProjector
open Primitive Cursor Split CompatibleWords ShortEdgeSignStability OpenFirstEdgeGeometry
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- The actual weighted parent projector from far-row nonvanishing alone.
The missing physical far-nonzero domain remains an explicit premise. -/
theorem exists_weighted_parent_projector
    {a b : ℕ} (q : Fin (a+b+2) → PlanarPoint ℝ) (hR : Regular q)
    (c : Crossing q) (hc : FirstCrossing q c) (hcut : c.val.2.val=a)
    (hAux : Primitive.ClosedAuxiliary q hR)
    (hfar : ∀ T : Primitive.Support (parent q c hcut) (regular_parent q hR c hcut),
      ∀ k j, 1<k → k<j → j≤RetainedWords.openCount (parent q c hcut)
        (regular_parent q hR c hcut) T.val →
        polygonHDet (fun k => if k=0 then q 0 else
          rootedPolygonWord (Primitive.OpenVertex (parent q c hcut)
            (regular_parent q hR c hcut) T)
            (RetainedWords.openLast (parent q c hcut) (regular_parent q hR c hcut) T.val)
            (k-1)) 1 k j ≠ 0) :
    let p := parent q c hcut
    let hp := regular_parent q hR c hcut
    let hA := parent_closedAuxiliary q hR c hc hcut hAux
    let P := fun T : Primitive.Support p hp => fun k => if k=0 then q 0 else
      rootedPolygonWord (Primitive.OpenVertex p hp T) (RetainedWords.openLast p hp T.val) (k-1)
    let N := fun T : Primitive.Support p hp => RetainedWords.openCount p hp T.val
    ∃ r : ℝ, 0<r ∧ r≤1 ∧ ∀ ε : ℝ, 0<ε → ε<r →
      (∑ T : Primitive.Support p hp, (-1 : ℚ)^T.val.card *
        (OpenMarkedCurrent.entry (polygonSignArray (approach (P T) ε)) 0 (N T) *
          ∏ C ∈ Finset.univ.erase (openComponent p hp.noTriple T.val),
            Primitive.closedWeight p hp hA T C)) =
      -((1+scalarSignValue (planarDet (q 1-q 0)
        (q c.val.2.succ-q c.val.2.castSucc)))/2) * Primitive.GammaM p hp hA := by
  classical
  let p := parent q c hcut
  let hp := regular_parent q hR c hcut
  let hA := parent_closedAuxiliary q hR c hc hcut hAux
  let P := fun T : Primitive.Support p hp => fun k => if k=0 then q 0 else
    rootedPolygonWord (Primitive.OpenVertex p hp T) (RetainedWords.openLast p hp T.val) (k-1)
  let N := fun T : Primitive.Support p hp => RetainedWords.openCount p hp T.val
  let W := fun T : Primitive.Support p hp => (-1 : ℚ)^T.val.card *
    ∏ C ∈ Finset.univ.erase (openComponent p hp.noTriple T.val),
      Primitive.closedWeight p hp hA T C
  let d := scalarSignValue (planarDet (q 1-q 0)
    (q c.val.2.succ-q c.val.2.castSucc))
  have hN : ∀ T, 1<N T := by
    intro T
    have h := RetainedWords.open_count_ge_two p hp T.val
    dsimp [N]
    omega
  let R : Primitive.Support p hp → ℝ → Prop := fun T ε =>
    OpenMarkedCurrent.entry (polygonSignArray (approach (P T) ε)) 0 (N T) =
      (((1+polygonSignArray (P T) 0 1 2)/2)-1) *
        OpenMarkedCurrent.entry (polygonSignArray (P T)) 1 (N T)
  have hlocal : ∀ T, T∈(Finset.univ : Finset (Primitive.Support p hp)) →
      ∃ δ : ℝ, 0<δ ∧ ∀ ε : ℝ, 0<ε → ε<δ → R T ε := by
    intro T _
    obtain ⟨δ,hδ,_,hgood⟩ := DirectGLSSW.OpenCurrentFarRadius.exists_far_radius_entry_short_first
      (P T) (N T) (hfar T)
    refine ⟨δ,hδ,?_⟩
    intro ε hε hεδ
    exact (hgood ε hε hεδ).2 (N T) (hN T) le_rfl
  obtain ⟨δ,hδ,hgood⟩ := exists_finset_common_radius
    (Finset.univ : Finset (Primitive.Support p hp)) R hlocal
  refine ⟨min δ 1,lt_min hδ (by norm_num),min_le_right _ _,?_⟩
  intro ε hε hεδ
  have hsmall : ε<δ := lt_of_lt_of_le hεδ (min_le_left _ _)
  have hentry : ∀ T : Primitive.Support p hp,
      OpenMarkedCurrent.entry (polygonSignArray (approach (P T) ε)) 0 (N T) =
        (((1+polygonSignArray (P T) 0 1 2)/2)-1) *
          OpenMarkedCurrent.entry (polygonSignArray (P T)) 1 (N T) := by
    intro T
    exact hgood ε hε hsmall T (Finset.mem_univ T)
  change (∑ T : Primitive.Support p hp, (-1 : ℚ)^T.val.card *
      (OpenMarkedCurrent.entry (polygonSignArray (approach (P T) ε)) 0 (N T) *
        ∏ C ∈ Finset.univ.erase (openComponent p hp.noTriple T.val),
          Primitive.closedWeight p hp hA T C)) = -((1+d)/2) * Primitive.GammaM p hp hA
  calc
    _ = ∑ T, W T * OpenMarkedCurrent.entry (polygonSignArray (approach (P T) ε)) 0 (N T) := by
      apply Finset.sum_congr rfl
      intro T hT
      dsimp [W]
      ring
    _ = ∑ T, W T * (((1+polygonSignArray (P T) 0 1 2)/2)-1) *
        OpenMarkedCurrent.entry (polygonSignArray (P T)) 1 (N T) := by
      apply Finset.sum_congr rfl
      intro T hT
      rw [hentry T]
      ring
    _ = ∑ T : Primitive.Support p hp, -((1+d)/2) *
        ((-1 : ℚ)^T.val.card * (Primitive.openCurrent p hp T *
          ∏ C ∈ Finset.univ.erase (openComponent p hp.noTriple T.val),
            Primitive.closedWeight p hp hA T C)) := by
      apply Finset.sum_congr rfl
      intro T hT
      have hs : polygonSignArray (P T) 0 1 2 = -d :=
        DirectGLSSW.ActiveArc.Split.parent_prefixed_sign012 q hR c hc hcut T
      have ht : OpenMarkedCurrent.entry (polygonSignArray (P T)) 1 (N T) =
          Primitive.openCurrent p hp T :=
        DirectGLSSW.ActiveArc.TinyParentConditional.prefixed_tail_entry p hp T (q 0)
      rw [hs,ht]
      dsimp [W]
      ring
    _ = _ := by rw [← Finset.mul_sum]; rfl

end DirectGLSSW.ActiveArc.TinyParentFarProjector
