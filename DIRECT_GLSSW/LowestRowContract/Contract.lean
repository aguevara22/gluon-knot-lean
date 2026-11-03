import Gemini.Solution

/-! Fixed geometric and coefficient definitions for the lowest-row assignment.
No lowest-row theorem is asserted or assumed in this module. -/
set_option autoImplicit false
noncomputable section

namespace DirectGLSSW.HOMFLY.LowestRowContract
open DirectGLSSW PermutationOrbits Coefficients
open scoped BigOperators

/-- The actual coefficient row, embedded in the z-degree-zero subring.
This retains every a coefficient, including all negative a exponents. -/
def zRow (P : HOMFLYCoeff) (n : ℤ) : HOMFLYCoeff :=
  P.sum fun ij v => if ij.2 = n then Finsupp.single (ij.1, 0) v else 0

def aPower (n : ℤ) : HOMFLYCoeff := Finsupp.single (n, 0) 1

/-- Standard crossing sign for the skein convention: positive means +1.
Do not substitute Gemini.crossingSignInt, which has the opposite convention. -/
def writheSign (D : PLLinkDiagram) (c : Fin D.nCrossing) : ℤ :=
  match crossingSign D c with
  | .pos => 1
  | .neg => -1

def IsMixed (D : PLLinkDiagram) (c : Fin D.nCrossing) : Prop :=
  componentOf D.continuation (D.incoming c 0) ≠
    componentOf D.continuation (D.incoming c 1)

/-- Sum of signs at all mixed crossings, exactly 2 times total linking number.
No integer division or parity premise is used to define the exponent. -/
def mixedWrithe (D : PLLinkDiagram) : ℤ := by
  classical
  exact ∑ c : Fin D.nCrossing, if IsMixed D c then writheSign D c else 0

/-- Full signed crossing sum for one unordered pair of DISTINCT components.
The diagonal is zero. Integer half-sums must be proved to exist by the worker. -/
def pairWrithe (D : PLLinkDiagram) (C E : diagramComponent D) : ℤ := by
  classical
  exact ∑ c : Fin D.nCrossing,
    if C ≠ E ∧
      ((componentOf D.continuation (D.incoming c 0) = C ∧
        componentOf D.continuation (D.incoming c 1) = E) ∨
       (componentOf D.continuation (D.incoming c 0) = E ∧
        componentOf D.continuation (D.incoming c 1) = C))
    then writheSign D c else 0

/-- Ordered double sum; for symmetric zero-diagonal linking this is twice the
source's unordered pair sum. Symmetry and zero diagonal follow from the target's
pairwise characterization, rather than being unproved data assumptions. -/
def totalOrderedPairSum (D : PLLinkDiagram)
    (linking : diagramComponent D → diagramComponent D → ℤ) : ℤ := by
  classical
  letI : Fintype (diagramComponent D) := componentFintype D.continuation
  exact ∑ C : diagramComponent D, ∑ E : diagramComponent D, linking C E

def ComponentArc (D : PLLinkDiagram) (C : diagramComponent D) :=
  {a : Fin D.nArc // componentOf D.continuation a = C}

def ComponentVertex (D : PLLinkDiagram) (C : diagramComponent D) :=
  {v : Fin D.nVertex // ∃ a : ComponentArc D C, D.arcSource a.val = v}

def ComponentCrossing (D : PLLinkDiagram) (C : diagramComponent D) :=
  {c : Fin D.nCrossing // ∀ i : Fin 2,
    componentOf D.continuation (D.incoming c i) = C}

/-- An exact component subdiagram. Every component arc and incident vertex is
retained; exactly its self crossings are crossings in the child. Mixed vertices
remain ordinary bivalent subdivision vertices. These are geometric typing data,
not polynomial, row, linking, or invariance assumptions. -/
structure ComponentRestriction (D : PLLinkDiagram) (C : diagramComponent D) where
  diagram : PLLinkDiagram
  nonempty : 0 < diagram.nArc
  arcEquiv : Fin diagram.nArc ≃ ComponentArc D C
  vertexEquiv : Fin diagram.nVertex ≃ ComponentVertex D C
  crossingEquiv : Fin diagram.nCrossing ≃ ComponentCrossing D C
  vertexPoint_eq : ∀ v,
    diagram.vertexPoint v = D.vertexPoint (vertexEquiv v).val
  source_eq : ∀ a,
    (vertexEquiv (diagram.arcSource a)).val = D.arcSource (arcEquiv a).val
  target_eq : ∀ a,
    (vertexEquiv (diagram.arcTarget a)).val = D.arcTarget (arcEquiv a).val
  crossingVertex_eq : ∀ c,
    (vertexEquiv (diagram.crossingVertex c)).val =
      D.crossingVertex (crossingEquiv c).val
  incoming_eq : ∀ c i,
    (arcEquiv (diagram.incoming c i)).val = D.incoming (crossingEquiv c).val i
  outgoing_eq : ∀ c i,
    (arcEquiv (diagram.outgoing c i)).val = D.outgoing (crossingEquiv c).val i
  continuation_eq : ∀ a,
    (arcEquiv (diagram.continuation a)).val = D.continuation (arcEquiv a).val
  through_eq : ∀ c, diagram.through c = D.through (crossingEquiv c).val
  overBranch_eq : ∀ c, diagram.overBranch c = D.overBranch (crossingEquiv c).val

abbrev Evaluator := (D : PLLinkDiagram) → 0 < D.nArc → HOMFLYCoeff

def componentRowProduct (H : Evaluator) (D : PLLinkDiagram)
    (R : ∀ C : diagramComponent D, ComponentRestriction D C) : HOMFLYCoeff := by
  classical
  letI : Fintype (diagramComponent D) := componentFintype D.continuation
  exact ∏ C : diagramComponent D, zRow (H (R C).diagram (R C).nonempty) 0

end DirectGLSSW.HOMFLY.LowestRowContract
