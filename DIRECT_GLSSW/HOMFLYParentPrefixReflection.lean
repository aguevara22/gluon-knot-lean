import HOMFLYParentConnectorPosition

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.HOMFLY
open Equiv PermutationOrbits
attribute [local instance] Classical.propDecidable
local instance (D : PLLinkDiagram) : DecidableEq (diagramComponent D) := Classical.decEq _

/-- In the actual continuing component, a parent-root old-arc visit no later
than the connector boundary reflects to the same original visit. -/
theorem parentRoot_prefix_visitPosition_reflect (D : PLLinkDiagram) (T : BasedTraversal D)
    (c : Fin D.nCrossing)
    (hself : D.continuation.SameCycle (D.incoming c 0) (D.incoming c 1))
    (x : Fin D.nArc)
    (hx : componentOf (smoothCrossing D c).continuation
      (smoothArcEquiv D (Sum.inl x)) =
      componentOf (smoothCrossing D c).continuation
        (smoothArcEquiv D (Sum.inr (firstVisitedBranch T c))))
    (hle : visitPosition (parentRootSelfSmoothingTraversal D T c hself)
        (smoothArcEquiv D (Sum.inl x)) ≤
      visitPosition T (D.incoming c (firstVisitedBranch T c))) :
    visitPosition T x =
        visitPosition (parentRootSelfSmoothingTraversal D T c hself)
          (smoothArcEquiv D (Sum.inl x)) ∧
      componentOf D.continuation x =
        componentOf D.continuation (D.incoming c (firstVisitedBranch T c)) := by
  let i := firstVisitedBranch T c
  let a := D.incoming c i
  let U := parentRootSelfSmoothingTraversal D T c hself
  let f : Fin D.nArc → Fin (smoothCrossing D c).nArc :=
    fun e => smoothArcEquiv D (Sum.inl e)
  let r := (T.baseArc (componentOf D.continuation a)).val
  let n := visitPosition U (f x)
  have hroot : (U.baseArc (componentOf (smoothCrossing D c).continuation
      (smoothArcEquiv D (Sum.inr i)))).val = f r := by
    simpa [U, f, i, r, a] using parentRootSelfSmoothingTraversal_continuing_root D T c hself
  have hrootx : (U.baseArc (componentOf (smoothCrossing D c).continuation (f x))).val = f r := by
    rw [hx]
    exact hroot
  have hnewpow : ((smoothCrossing D c).continuation ^ n) (f r) = f x := by
    have hrec := visitPosition_reconstruct U (f x)
    dsimp only [n]
    rw [← hrootx]
    exact hrec
  have hp := parentRoot_prefix_pow D T c hself n hle
  dsimp only [i, a, r, f] at hp
  have hf : Function.Injective f := (smoothArcEquiv D).injective.comp Sum.inl_injective
  have hxp : x = (D.continuation ^ n) r := hf (hnewpow.symm.trans hp)
  have hcompR : componentOf D.continuation x = componentOf D.continuation r := by
    rw [hxp]
    simp
  have hcompA : componentOf D.continuation r = componentOf D.continuation a :=
    (T.baseArc (componentOf D.continuation a)).property
  have hcomp : componentOf D.continuation x = componentOf D.continuation a := hcompR.trans hcompA
  have hn : n < Fintype.card (Fibre D.continuation (componentOf D.continuation r)) := by
    have hle' : n ≤ visitPosition T a := by
      simpa [n, U, f] using hle
    have hposA := visitPosition_eq_orbitPosition_of_baseArc T a r rfl hcompA.symm
    have hcut : visitPosition T a <
        Fintype.card (Fibre D.continuation (componentOf D.continuation r)) := by
      rw [hposA]
      exact ((orbitEnumeration D.continuation r).symm ⟨a, hcompA.symm⟩).isLt
    omega
  let j : Fin (Fintype.card (Fibre D.continuation (componentOf D.continuation r))) := ⟨n, hn⟩
  have hj : (orbitEnumeration D.continuation r j).val = x := by
    rw [orbitEnumeration_apply_val]
    rw [hxp]
  have hrootold : (T.baseArc (componentOf D.continuation r)).val = r := by
    rw [hcompA]
  have hpos : visitPosition T x = n := by
    have hvisit := visitPosition_orbitEnumeration T r hrootold j
    rw [hj] at hvisit
    exact hvisit
  constructor
  · exact hpos.trans (by rfl)
  · exact hcomp

end DirectGLSSW.HOMFLY


