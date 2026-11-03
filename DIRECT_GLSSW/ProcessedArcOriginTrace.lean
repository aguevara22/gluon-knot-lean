import ProcessedArcOriginStep
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.HOMFLY
open PermutationOrbits LowestRowContract
attribute [local instance] Classical.propDecidable
namespace MarkedParentTrace

/-- The actual backward partial origin map along a finite literal history.
None records a connector born during this history, not a fallback arc label. -/
def arcOrigin {s t : MarkedParentState} (h : MarkedParentTrace s t) :
    Fin t.1.nArc → Option (Fin s.1.nArc) :=
  match h with
  | .nil _ => fun e => some e
  | .cons step tail => fun e => (tail.arcOrigin e).bind step.arcOrigin

theorem arcOrigin_some_injective {s t : MarkedParentState} (h : MarkedParentTrace s t) :
    ∀ (e f : Fin t.1.nArc) (a : Fin s.1.nArc),
      h.arcOrigin e = some a → h.arcOrigin f = some a → e=f := by
  induction h with
  | nil s =>
    intro e f a he hf
    exact Option.some.inj (he.trans hf.symm)
  | cons step tail ih =>
    intro e f a he hf
    cases hte : tail.arcOrigin e with
    | none => simp [arcOrigin,hte] at he
    | some b =>
      cases htf : tail.arcOrigin f with
      | none => simp [arcOrigin,htf] at hf
      | some d =>
        have hb : step.arcOrigin b = some a := by simpa only [arcOrigin,hte,Option.some_bind] using he
        have hd : step.arcOrigin d = some a := by simpa only [arcOrigin,htf,Option.some_bind] using hf
        have hbd := step.arcOrigin_some_injective b d a hb hd
        subst d
        exact ih e f b hte htf

theorem arcOrigin_markEmbedding {s t : MarkedParentState} (h : MarkedParentTrace s t) :
    ∀ x : StateMarks s, h.arcOrigin (h.markEmbedding x).val = some x.val := by
  induction h with
  | nil s => intro x; rfl
  | cons step tail ih =>
    intro x
    change (tail.arcOrigin (tail.markEmbedding (step.markEmbedding x)).val).bind step.arcOrigin = some x.val
    rw [ih,Option.some_bind,step.arcOrigin_markEmbedding]

theorem arcOrigin_none_marked {s t : MarkedParentState} (h : MarkedParentTrace s t) :
    ∀ e : Fin t.1.nArc, h.arcOrigin e = none → e ∈ t.2.2.marks := by
  induction h with
  | nil s => intro e he; cases he
  | @cons s t u step tail ih =>
    intro e he
    cases hte : tail.arcOrigin e with
    | none => exact ih e hte
    | some a =>
      have ha : step.arcOrigin a = none := by simpa only [arcOrigin,hte,Option.some_bind] using he
      let x : StateMarks t := ⟨a,step.arcOrigin_none_marked a ha⟩
      have hx : tail.arcOrigin (tail.markEmbedding x).val = some a := tail.arcOrigin_markEmbedding x
      have heq : e=(tail.markEmbedding x).val :=
        tail.arcOrigin_some_injective e (tail.markEmbedding x).val a hte hx
      rw [heq]
      exact (tail.markEmbedding x).property

/-- A later actual detached child contains no old arc born as an earlier
connector: every old-code arc has an actual ancestor in the starting diagram. -/
theorem detached_old_arc_has_origin {s t : MarkedParentState}
    (h : MarkedParentTrace s t) (c : Fin t.1.nCrossing) (hc : badAt t.2.1 c)
    (R : ComponentRestriction (smoothCrossing t.1 c)
      (rootSelfCutComponents t.1 c (t.2.2.connected _ _)
        (firstVisitedBranch t.2.1 c) (Sum.inl true)))
    (e : Fin R.diagram.nArc) (a : Fin t.1.nArc)
    (hea : (smoothArcEquiv t.1).symm (R.arcEquiv e).val = Sum.inl a) :
    ∃ a₀ : Fin s.1.nArc, h.arcOrigin a = some a₀ := by
  cases horigin : h.arcOrigin a with
  | some a₀ => exact ⟨a₀,rfl⟩
  | none =>
    have ham : a ∈ t.2.2.marks := h.arcOrigin_none_marked a horigin
    have hnot := t.2.2.mark_not_detached c hc ⟨a,ham⟩
    have hmap : (R.arcEquiv e).val = smoothArcEquiv t.1 (Sum.inl a) := by
      simpa only [Equiv.apply_symm_apply] using congrArg (smoothArcEquiv t.1) hea
    have hmem := (R.arcEquiv e).property
    rw [hmap] at hmem
    exact (hnot hmem).elim

end MarkedParentTrace
end DirectGLSSW.HOMFLY
