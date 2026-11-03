import ComponentRestrictionParentTraversal
import HOMFLYParentGoodPrefix
import HOMFLYParentConnectorExclusion
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.HOMFLY
open PermutationOrbits LowestRowContract
attribute [local instance] Classical.propDecidable

/-- Literal processed state of one actual rooted parent. The finite marks are
physical arcs; every mark has already been traversed before any remaining bad crossing. -/
structure ProcessedParentMarks (D : PLLinkDiagram) (T : BasedTraversal D) where
  marks : Finset (Fin D.nArc)
  connected : ∀ x y : Fin D.nArc, D.continuation.SameCycle x y
  beforeBad : ∀ x ∈ marks, ∀ d : Fin D.nCrossing, badAt T d →
    rankBefore (visitRank T x) (visitRank T (D.incoming d (firstVisitedBranch T d)))

namespace ProcessedParentMarks
variable {D : PLLinkDiagram} {T : BasedTraversal D}

/-- No marked history has yet been processed at the initial rooted diagram. -/
def initial (D : PLLinkDiagram) (T : BasedTraversal D)
    (hconn : ∀ x y : Fin D.nArc, D.continuation.SameCycle x y) :
    ProcessedParentMarks D T where
  marks := ∅
  connected := hconn
  beforeBad := by intro x hx; exact (Finset.not_mem_empty x hx).elim

/-- Every processed mark belongs to the preserved prefix at a genuine bad cut. -/
theorem mark_before_cut (S : ProcessedParentMarks D T) (c : Fin D.nCrossing)
    (hc : badAt T c) (x : {x : Fin D.nArc // x ∈ S.marks}) :
    visitPosition T x.val < visitPosition T (D.incoming c (firstVisitedBranch T c)) := by
  have h := S.beforeBad x.val x.property c hc
  have hx : componentOf D.continuation x.val =
      componentOf D.continuation (D.incoming c (firstVisitedBranch T c)) :=
    (componentOf_eq_iff _ _ _).2 (S.connected _ _)
  simpa only [rankBefore,visitRank,hx,lt_self_iff_false,true_and,false_or] using h

theorem mark_continuing_component (S : ProcessedParentMarks D T) (c : Fin D.nCrossing)
    (hc : badAt T c) (x : {x : Fin D.nArc // x ∈ S.marks}) :
    componentOf (smoothCrossing D c).continuation (smoothArcEquiv D (Sum.inl x.val)) =
      componentOf (smoothCrossing D c).continuation
        (smoothArcEquiv D (Sum.inr (firstVisitedBranch T c))) := by
  have h := prefix_visit_continuing_component D T c (S.connected _ _) x.val
    ((componentOf_eq_iff _ _ _).2 (S.connected _ _))
    (le_of_lt (S.mark_before_cut c hc x))
  rw [rootSelfCutComponents_false] at h
  exact h

theorem mark_before_connector (S : ProcessedParentMarks D T) (c : Fin D.nCrossing)
    (hc : badAt T c) (x : {x : Fin D.nArc // x ∈ S.marks}) :
    rankBefore
      (visitRank (parentRootSelfSmoothingTraversal D T c (S.connected _ _))
        (smoothArcEquiv D (Sum.inl x.val)))
      (visitRank (parentRootSelfSmoothingTraversal D T c (S.connected _ _))
        (smoothArcEquiv D (Sum.inr (firstVisitedBranch T c)))) :=
  parentRoot_prefix_before_connector D T c (S.connected _ _) x.val
    ((componentOf_eq_iff _ _ _).2 (S.connected _ _)) (le_of_lt (S.mark_before_cut c hc x))

/-- This excludes the actual arc tag; corner-vertex exclusion is a separate geometric fact. -/
theorem mark_not_detached (S : ProcessedParentMarks D T) (c : Fin D.nCrossing)
    (hc : badAt T c) (x : {x : Fin D.nArc // x ∈ S.marks}) :
    componentOf (smoothCrossing D c).continuation (smoothArcEquiv D (Sum.inl x.val)) ≠
      rootSelfCutComponents D c (S.connected _ _) (firstVisitedBranch T c) (Sum.inl true) :=
  before_first_visit_not_detached D T c (S.connected _ _) x.val
    (S.beforeBad x.val x.property c hc)

end ProcessedParentMarks
end DirectGLSSW.HOMFLY
