import ProcessedParentSmoothing
import ProcessedParentSwitching
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.HOMFLY
open PermutationOrbits LowestRowContract ProcessedParentMarks
attribute [local instance] Classical.propDecidable

/-- Actual diagram, original-root traversal, and finite processed marks. -/
abbrev MarkedParentState := Σ D : PLLinkDiagram, Σ T : BasedTraversal D, ProcessedParentMarks D T
abbrev StateMarks (s : MarkedParentState) := {a : Fin s.1.nArc // a ∈ s.2.2.marks}

inductive ProcessedMarkKind where
  | switched
  | connector
  deriving DecidableEq

/-- Only the two actual first-under operations are allowed. Restriction
existence remains an explicit external construction; no transport law is supplied. -/
inductive MarkedParentStep : MarkedParentState → MarkedParentState → Type where
  | switched {D : PLLinkDiagram} {T : BasedTraversal D} (S : ProcessedParentMarks D T)
      (c : Fin D.nCrossing) (hc : badAt T c)
      (hgood : ∀ d : Fin D.nCrossing,
        rankBefore (visitRank T (D.incoming d (firstVisitedBranch T d)))
          (visitRank T (D.incoming c (firstVisitedBranch T c))) → ¬ badAt T d) :
      MarkedParentStep ⟨D,T,S⟩
        ⟨switchCrossing D c,switchTraversal T c,S.switchStep c hc hgood⟩
  | smoothed {D : PLLinkDiagram} {T : BasedTraversal D} (S : ProcessedParentMarks D T)
      (c : Fin D.nCrossing) (hc : badAt T c)
      (hgood : ∀ d : Fin D.nCrossing,
        rankBefore (visitRank T (D.incoming d (firstVisitedBranch T d)))
          (visitRank T (D.incoming c (firstVisitedBranch T c))) → ¬ badAt T d)
      (R : ComponentRestriction (smoothCrossing D c)
        (componentOf (smoothCrossing D c).continuation
          (smoothArcEquiv D (Sum.inr (firstVisitedBranch T c))))) :
      MarkedParentStep ⟨D,T,S⟩
        ⟨R.diagram,R.basedTraversal (parentRootSelfSmoothingTraversal D T c (S.connected _ _)),
          S.smoothStep c hc hgood R⟩

namespace MarkedParentStep

/-- Literal old-tag maps, derived for each actual operation. -/
def markEmbedding {s t : MarkedParentState} (h : MarkedParentStep s t) :
    StateMarks s ↪ StateMarks t := by
  cases h with
  | switched S c hc hgood =>
    exact ⟨fun x => ⟨x.val,S.oldMark_mem_switchStep c hc hgood x⟩,
      fun x y h => Subtype.ext
        (congrArg (fun z : {a // a ∈ (S.switchStep c hc hgood).marks} => z.val) h)⟩
  | smoothed S c hc hgood R =>
    exact ⟨fun x => ⟨S.liftOldMark c hc R x,S.liftOldMark_mem_smoothStep c hc hgood R x⟩,
      fun x y h => S.liftOldMark_injective c hc R (congrArg Subtype.val h)⟩

/-- The kind of a new tag is retained: switched ports are not asserted regular. -/
def freshTag {s t : MarkedParentState} (h : MarkedParentStep s t) :
    ProcessedMarkKind × StateMarks t := by
  cases h with
  | @switched D T S c hc hgood =>
    exact ⟨.switched,⟨D.incoming c (firstVisitedBranch T c),Finset.mem_insert_self _ _⟩⟩
  | @smoothed D T S c hc hgood R =>
    exact ⟨.connector,⟨liftConnector D T c R,Finset.mem_insert_self _ _⟩⟩

end MarkedParentStep

/-- A finite literal history, with no abstract transition or rank hypotheses. -/
inductive MarkedParentTrace : MarkedParentState → MarkedParentState → Type where
  | nil (s : MarkedParentState) : MarkedParentTrace s s
  | cons {s t u : MarkedParentState} :
      MarkedParentStep s t → MarkedParentTrace t u → MarkedParentTrace s u

namespace MarkedParentTrace

/-- Finite induction composes the actual injective tag maps. -/
def markEmbedding {s t : MarkedParentState} (h : MarkedParentTrace s t) :
    StateMarks s ↪ StateMarks t :=
  match h with
  | .nil _ => Function.Embedding.refl _
  | .cons step tail => step.markEmbedding.trans tail.markEmbedding

@[simp] theorem markEmbedding_nil (s : MarkedParentState) (x : StateMarks s) :
    (MarkedParentTrace.nil s).markEmbedding x = x := rfl

@[simp] theorem markEmbedding_cons {s t u : MarkedParentState}
    (step : MarkedParentStep s t) (tail : MarkedParentTrace t u) (x : StateMarks s) :
    (MarkedParentTrace.cons step tail).markEmbedding x =
      tail.markEmbedding (step.markEmbedding x) := rfl

/-- Every birth carries its operation kind and its actual arc after the whole suffix. -/
def bornTags {s t : MarkedParentState} (h : MarkedParentTrace s t) :
    List (ProcessedMarkKind × StateMarks t) :=
  match h with
  | .nil _ => []
  | .cons step tail =>
      (step.freshTag.1,tail.markEmbedding step.freshTag.2) :: tail.bornTags

/-- Every earlier marked arc survives a finite actual history and is excluded
from the next detached child at a genuine bad crossing. -/
theorem historical_mark_not_detached {s t : MarkedParentState}
    (h : MarkedParentTrace s t) (c : Fin t.1.nCrossing) (hc : badAt t.2.1 c)
    (x : StateMarks s) :
    componentOf (smoothCrossing t.1 c).continuation
      (smoothArcEquiv t.1 (Sum.inl (h.markEmbedding x).val)) ≠
      rootSelfCutComponents t.1 c (t.2.2.connected _ _)
        (firstVisitedBranch t.2.1 c) (Sum.inl true) :=
  t.2.2.mark_not_detached c hc (h.markEmbedding x)

end MarkedParentTrace
end DirectGLSSW.HOMFLY
