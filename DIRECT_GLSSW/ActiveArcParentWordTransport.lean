import ActiveArcRetainedDeletion

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.CompatibleWords
open PermutationOrbits FiniteCycleOrder SingletonWords Split Cursor RetainedWords
attribute [local instance] Classical.propDecidable
variable {a b : ℕ} (q : Fin (a+b+2) → PlanarPoint ℝ) (hR : Regular q)
variable (c : Crossing q) (hc : FirstCrossing q c) (hcut : c.val.2.val=a)
variable (S : Finset (PolygonCrossing (child q hR c hc.1 hcut)))
variable (T : Finset (Crossing (parent q c hcut)))

/-- Exact literal open retained point word for arbitrary compatible daughter
selections. The extra original anchor q[0] is retained, so the tiny initial
edge q[0]→c is present. No daughter genericity or word identity is assumed. -/
theorem parent_open_word :
    List.ofFn (RetainedWords.vertex q hR (insert c (pieceSelections q hR c hc hcut S T)) (start q))=
      q ⟨0,by omega⟩ :: List.ofFn
        (RetainedWords.vertex (parent q c hcut) (regular_parent q hR c hcut) T (start (parent q c hcut))) := by
  letI := eventOrder q hR.noTriple
  letI := eventOrder (parent q c hcut) (regular_parent q hR c hcut).noTriple
  rw [sourceWord_eq_complementReduced,reduced_parent_pointWord]
  congr 1
  exact (retainedWord_eq_reduced (parent q c hcut) (regular_parent q hR c hcut) T
    (start (parent q c hcut)) (endpoints_retained _ T).1).symm

end DirectGLSSW.ActiveArc.CompatibleWords
