import OpenMarkedCurrentTranslation
import OpenCurrentFiniteFamily
import ActiveArcParentPrefixSign
import ActiveArcParentClosedAuxiliary

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.TinyParentConditional
open Primitive Cursor Split CompatibleWords ShortEdgeSignStability OpenFirstEdgeGeometry
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- Literal index shift from the prefixed word's tail to the actual parent M. -/
theorem prefixed_tail_entry {n : ℕ} (p : Fin (n+2) → PlanarPoint ℝ)
    (hp : Regular p) (T : Primitive.Support p hp) (x : PlanarPoint ℝ) :
    OpenMarkedCurrent.entry
      (polygonSignArray (fun k => if k=0 then x else
        rootedPolygonWord (Primitive.OpenVertex p hp T)
          (RetainedWords.openLast p hp T.val) (k-1)))
      1 (RetainedWords.openCount p hp T.val) = Primitive.openCurrent p hp T := by
  let m := RetainedWords.openCount p hp T.val
  let w := rootedPolygonWord (Primitive.OpenVertex p hp T) (RetainedWords.openLast p hp T.val)
  let P : ℕ → PlanarPoint ℝ := fun k => if k=0 then x else w (k-1)
  have hm : 2 ≤ m := RetainedWords.open_count_ge_two p hp T.val
  have ht := OpenMarkedCurrent.entry_tail_word P (n:=m-1) (by omega)
  have hw : (fun k => P (k+1))=w := by
    funext k
    simp [P]
  rw [hw,show m-1+1=m by omega] at ht
  exact ht.symm

/-- Conditional physical-word composition. The explicit open-prefix core
premise is not a consequence of ClosedAuxiliary. This theorem supplies no
source-node credit until that auxiliary-domain premise is discharged. -/
theorem exists_weighted_parent_projector
    {a b : ℕ} (q : Fin (a+b+2) → PlanarPoint ℝ) (hR : Regular q)
    (c : Crossing q) (hc : FirstCrossing q c) (hcut : c.val.2.val=a)
    (hAux : Primitive.ClosedAuxiliary q hR)
    (hcore : ∀ T : Primitive.Support (parent q c hcut) (regular_parent q hR c hcut),
      CoreHGeneric (fun k => if k=0 then q 0 else
        rootedPolygonWord (Primitive.OpenVertex (parent q c hcut)
          (regular_parent q hR c hcut) T)
          (RetainedWords.openLast (parent q c hcut)
            (regular_parent q hR c hcut) T.val) (k-1))
        (RetainedWords.openCount (parent q c hcut) (regular_parent q hR c hcut) T.val)) :
    let p := parent q c hcut
    let hp := regular_parent q hR c hcut
    let hA := parent_closedAuxiliary q hR c hc hcut hAux
    let P := fun T : Primitive.Support p hp => fun k => if k=0 then q 0 else
      rootedPolygonWord (Primitive.OpenVertex p hp T) (RetainedWords.openLast p hp T.val) (k-1)
    ∃ r : ℝ, 0<r ∧ r≤1 ∧ ∀ ε : ℝ, 0<ε → ε<r →
      (∑ T : Primitive.Support p hp, (-1 : ℚ)^T.val.card *
        (OpenMarkedCurrent.entry (polygonSignArray (approach (P T) ε))
          0 (RetainedWords.openCount p hp T.val) *
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
    ∏ C ∈ Finset.univ.erase (openComponent p hp.noTriple T.val), Primitive.closedWeight p hp hA T C
  let d := scalarSignValue (planarDet (q 1-q 0) (q c.val.2.succ-q c.val.2.castSucc))
  have hN : ∀ T, 1<N T := by
    intro T
    have h := RetainedWords.open_count_ge_two p hp T.val
    dsimp [N]
    omega
  obtain ⟨r,hr,hr1,hgood⟩ := OpenCurrentFiniteFamily.exists_weighted_short_first P N hN hcore W
  refine ⟨r,hr,hr1,?_⟩
  intro ε hε hεr
  have hsum := (hgood ε hε hεr).2
  change (∑ T : Primitive.Support p hp, (-1 : ℚ)^T.val.card *
      (OpenMarkedCurrent.entry (polygonSignArray (approach (P T) ε)) 0 (N T) *
        ∏ C ∈ Finset.univ.erase (openComponent p hp.noTriple T.val),
          Primitive.closedWeight p hp hA T C)) = -( (1+d)/2) * Primitive.GammaM p hp hA
  calc
    _ = ∑ T, W T * OpenMarkedCurrent.entry (polygonSignArray (approach (P T) ε)) 0 (N T) := by
      apply Finset.sum_congr rfl
      intro T hT
      dsimp [W]
      ring
    _ = ∑ T, W T * (((1+polygonSignArray (P T) 0 1 2)/2)-1) *
        OpenMarkedCurrent.entry (polygonSignArray (P T)) 1 (N T) := hsum
    _ = ∑ T : Primitive.Support p hp, -((1+d)/2) *
        ((-1 : ℚ)^T.val.card * (Primitive.openCurrent p hp T *
          ∏ C ∈ Finset.univ.erase (openComponent p hp.noTriple T.val),
            Primitive.closedWeight p hp hA T C)) := by
      apply Finset.sum_congr rfl
      intro T hT
      have hs : polygonSignArray (P T) 0 1 2 = -d := parent_prefixed_sign012 q hR c hc hcut T
      have ht : OpenMarkedCurrent.entry (polygonSignArray (P T)) 1 (N T) =
          Primitive.openCurrent p hp T := prefixed_tail_entry p hp T (q 0)
      rw [hs,ht]
      dsimp [W]
      ring
    _ = _ := by rw [← Finset.mul_sum]; rfl

end DirectGLSSW.ActiveArc.TinyParentConditional
