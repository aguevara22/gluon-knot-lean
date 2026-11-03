import ActiveArcTinyParentEndpoint
import ActiveArcParentFarProjector

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.LiteralTinyParent
open Cursor Split Primitive OpenFirstEdgeGeometry

variable {a b : ℕ} (q : Fin (a+b+2) → PlanarPoint ℝ)
variable (c : Crossing q) (hcut : c.val.2.val=a)

/-- Actual finite arc (p_eta,c,q_(a+1),...,q_N), with a physical initial
edge and the entire literal open parent as its tail. -/
def tinyParent (η : ℝ) : Fin (b+3) → PlanarPoint ℝ :=
  Fin.cons (affinePoint (crossingPoint q c) (q 0) η) (parent q c hcut)

@[simp] theorem tinyParent_zero (η : ℝ) :
    tinyParent q c hcut η 0=affinePoint (crossingPoint q c) (q 0) η := rfl

@[simp] theorem tinyParent_succ (η : ℝ) (i : Fin (b+2)) :
    tinyParent q c hcut η i.succ=parent q c hcut i := by
  simp only [tinyParent,Fin.cons_succ]

@[simp] theorem tinyParent_one (η : ℝ) :
    tinyParent q c hcut η 1=crossingPoint q c := by
  simpa only [tinyParent_succ] using parent_zero q c hcut

@[simp] theorem tinyParent_succ_succ (η : ℝ) (i : Fin (b+1)) :
    tinyParent q c hcut η i.succ.succ=q (vertex i.succ) := by
  rw [tinyParent_succ,parent_succ]

theorem tinyParent_pointList (η : ℝ) :
    List.ofFn (tinyParent q c hcut η)=
      affinePoint (crossingPoint q c) (q 0) η :: List.ofFn (parent q c hcut) := by
  simp only [tinyParent,List.ofFn_succ,Fin.cons_zero,Fin.cons_succ]

theorem tinyParent_eq_physical (hc : FirstCrossing q c) (η : ℝ) :
    tinyParent q c hcut η =
      Fin.cons (moveStart q (leftParameter q c*(1-η)) 0) (parent q c hcut) := by
  unfold tinyParent
  rw [moveStart_approach_endpoint q c hc η]

/-- Exact point-function equality to the already-proved projector path.
This does not assert a smoothing-support identification for tinyParent. -/
theorem tinyParent_prefixed_parent_word (hR : Regular q) (hc : FirstCrossing q c)
    (T : Support (parent q c hcut) (regular_parent q hR c hcut)) (η : ℝ) :
    (fun k : ℕ => if k=0 then tinyParent q c hcut η 0 else
      rootedPolygonWord (OpenVertex (parent q c hcut) (regular_parent q hR c hcut) T)
        (RetainedWords.openLast (parent q c hcut) (regular_parent q hR c hcut) T.val) (k-1)) =
    approach (fun k => if k=0 then q 0 else
      rootedPolygonWord (OpenVertex (parent q c hcut) (regular_parent q hR c hcut) T)
        (RetainedWords.openLast (parent q c hcut) (regular_parent q hR c hcut) T.val) (k-1)) η := by
  rw [parent_prefix_approach_endpoint q hR c hc hcut T η]
  funext k
  by_cases hk : k=0
  · simp only [hk,if_pos rfl,tinyParent_zero]
    exact (moveStart_approach_endpoint q c hc η).symm
  · simp only [if_neg hk]

end DirectGLSSW.ActiveArc.LiteralTinyParent
