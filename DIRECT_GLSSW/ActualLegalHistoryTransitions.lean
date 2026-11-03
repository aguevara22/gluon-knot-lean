import LiteralCarrierHistory
import LegalRestartChart
import ActiveArcSingletonWords

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.CyclicCarrierClearing
open ActiveArc ActiveArc.Cursor ActiveArc.Split ActiveArc.ExposedChart TruncationDirection

theorem literalCarrierPath_trans {s u t : LiteralCarrierState}
    (h : LiteralCarrierPath s u) (k : LiteralCarrierPath u t) :
    LiteralCarrierPath s t := by
  induction h with
  | nil => exact k
  | cons step tail ih => exact .cons step (ih k)

theorem literalCarrierPath_snoc {s u t : LiteralCarrierState}
    (h : LiteralCarrierPath s u) (step : LiteralCarrierStep u t) :
    LiteralCarrierPath s t :=
  literalCarrierPath_trans h (.cons step (.nil t))

/-- The actual source child has genericity from the closed smoothing domain
and is the literal next closed endpoint; no provenance hypothesis is added. -/
theorem actual_detached_child_generic_history
    {s : LiteralCarrierState} {a b : ℕ}
    (v : Fin (a+b+2) → PlanarPoint ℝ) (hR : Regular v)
    (c : Crossing v) (hc : FirstCrossing v c) (hcut : c.val.2.val=a)
    (hAux : Primitive.ClosedAuxiliary v hR)
    (hpath : LiteralCarrierPath s (.inr ⟨a+b,v⟩)) :
    CyclicGeneric (child v hR c hc.1 hcut) ∧
      LiteralCarrierPath s (.inl ⟨a+1,child v hR c hc.1 hcut⟩) :=
  ⟨SingletonWords.child_cyclicGeneric_of_closedAuxiliary v hR c hc.1 hcut hAux,
    literalCarrierPath_snoc hpath (.detach v hR c hc hcut)⟩

/-- The exposed rebasing changes labels only. Cutting the explicitly chosen
rebased truncation is exactly the raw truncation-cut history step. -/
theorem actual_rebased_truncation_cut_history
    {s : LiteralCarrierState} {n : ℕ}
    (d : Fin (n+1) → PlanarPoint ℝ) (hd : CyclicGeneric d)
    (a p : Fin (n+1)) (hp : cyclicSuccessor p=a)
    (scale ε : ℝ) (hs : 0 < scale) (hε : 0 < ε)
    (Q : Fin (n+2) → PlanarPoint ℝ)
    (hQ : Q = truncateCyclicCorner d a p scale ε ∘
      PolygonRebase.atEdge a.castSucc)
    (hpath : LiteralCarrierPath s (.inl ⟨n+1,d⟩)) :
    LiteralCarrierPath s (.inr ⟨n,cutArc Q 0⟩) := by
  subst Q
  rw [SourceLegalHistoryGenericity.cutArc_atEdge_eq]
  exact literalCarrierPath_snoc hpath (.truncateCut d hd a p hp scale ε hs hε)

end DirectGLSSW.CyclicCarrierClearing

