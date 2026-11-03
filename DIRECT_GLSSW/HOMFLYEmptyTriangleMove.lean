import HOMFLYCircuitSlabCuts
import HOMFLYDiskAttachmentBoundary

set_option autoImplicit false
namespace DirectGLSSW.HOMFLY
noncomputable section

def plArcTrace (D : PLLinkDiagram) (e : Fin D.nArc) : Set (PlanarPoint ℝ) :=
  segment ℝ (D.vertexPoint (D.arcSource e)) (D.vertexPoint (D.arcTarget e))

def plDrawingTrace (D : PLLinkDiagram) : Set (PlanarPoint ℝ) :=
  {z | ∃ e, z ∈ plArcTrace D e}

/-- Actual regular two-edge subarc bounding an empty triangle. Regular endpoints
ensure contraction changes no tangent at a crossing. No target or equality of
polynomials is supplied by this source-site data. -/
structure EmptyTriangleSite (D : PLLinkDiagram) where
  left : Fin D.nArc
  right : Fin D.nArc
  distinct : left ≠ right
  consecutive : D.continuation left = right
  joint : D.arcTarget left = D.arcSource right
  regular_start : ∀ c, D.crossingVertex c ≠ D.arcSource left
  regular_middle : ∀ c, D.crossingVertex c ≠ D.arcTarget left
  regular_end : ∀ c, D.crossingVertex c ≠ D.arcTarget right
  patch : TrianglePatch
  start_eq : D.vertexPoint (D.arcSource left) = patch.a
  middle_eq : D.vertexPoint (D.arcTarget left) = patch.b
  end_eq : D.vertexPoint (D.arcTarget right) = patch.c
  empty_support : plDrawingTrace D ∩ patch.fill = plArcTrace D left ∪ plArcTrace D right

/-- Concrete oriented PL contraction, indexed by its actual source and target.
Exactly the two selected arcs merge; all other oriented segments, crossing
ports, through pairings, overbranches and continuation steps are retained.
This record contains no isotopy assertion or evaluator-invariance field. -/
structure EmptyTriangleContraction (D E : PLLinkDiagram) where
  site : EmptyTriangleSite D
  arcMap : Fin D.nArc → Fin E.nArc
  arcMap_surjective : Function.Surjective arcMap
  arcMap_fibers : ∀ e f, arcMap e = arcMap f ↔
    e = f ∨ (e = site.left ∧ f = site.right) ∨ (e = site.right ∧ f = site.left)
  chord_start : E.vertexPoint (E.arcSource (arcMap site.left)) = site.patch.a
  chord_end : E.vertexPoint (E.arcTarget (arcMap site.left)) = site.patch.c
  retained_start : ∀ e, e ≠ site.left → e ≠ site.right →
    E.vertexPoint (E.arcSource (arcMap e)) = D.vertexPoint (D.arcSource e)
  retained_end : ∀ e, e ≠ site.left → e ≠ site.right →
    E.vertexPoint (E.arcTarget (arcMap e)) = D.vertexPoint (D.arcTarget e)
  continuation_map : ∀ e, e ≠ site.left →
    arcMap (D.continuation e) = E.continuation (arcMap e)
  crossingEquiv : Fin D.nCrossing ≃ Fin E.nCrossing
  crossing_point : ∀ c,
    E.vertexPoint (E.crossingVertex (crossingEquiv c)) = D.vertexPoint (D.crossingVertex c)
  incoming_map : ∀ c i, E.incoming (crossingEquiv c) i = arcMap (D.incoming c i)
  outgoing_map : ∀ c i, E.outgoing (crossingEquiv c) i = arcMap (D.outgoing c i)
  through_map : ∀ c, E.through (crossingEquiv c) = D.through c
  overBranch_map : ∀ c, E.overBranch (crossingEquiv c) = D.overBranch c

namespace EmptyTriangleSite

theorem left_subset_fill {D : PLLinkDiagram} (S : EmptyTriangleSite D) :
    plArcTrace D S.left ⊆ S.patch.fill := by
  intro z hz
  apply S.patch.boundary_subset_fill
  apply Or.inl; apply Or.inl
  simpa only [plArcTrace, S.start_eq, S.middle_eq] using hz

theorem right_subset_fill {D : PLLinkDiagram} (S : EmptyTriangleSite D) :
    plArcTrace D S.right ⊆ S.patch.fill := by
  intro z hz
  apply S.patch.boundary_subset_fill
  apply Or.inl; apply Or.inr
  simpa only [plArcTrace, ← S.joint, S.middle_eq, S.end_eq] using hz

end EmptyTriangleSite
namespace EmptyTriangleContraction

theorem crossing_count {D E : PLLinkDiagram} (M : EmptyTriangleContraction D E) :
    D.nCrossing = E.nCrossing := by
  simpa only [Fintype.card_fin] using Fintype.card_congr M.crossingEquiv

theorem chord_subset_fill {D E : PLLinkDiagram} (M : EmptyTriangleContraction D E) :
    plArcTrace E (M.arcMap M.site.left) ⊆ M.site.patch.fill := by
  intro z hz
  apply M.site.patch.boundary_subset_fill
  apply Or.inr
  simpa only [plArcTrace, M.chord_start, M.chord_end, segment_symm ℝ M.site.patch.a M.site.patch.c] using hz

theorem retained_trace {D E : PLLinkDiagram} (M : EmptyTriangleContraction D E)
    (e : Fin D.nArc) (hl : e ≠ M.site.left) (hr : e ≠ M.site.right) :
    plArcTrace E (M.arcMap e) = plArcTrace D e := by
  simp only [plArcTrace, M.retained_start e hl hr, M.retained_end e hl hr]

/-- Support characterization on actual geometric traces, not an isotopy claim. -/
theorem trace_outside {D E : PLLinkDiagram} (M : EmptyTriangleContraction D E) :
    plDrawingTrace D \ M.site.patch.fill = plDrawingTrace E \ M.site.patch.fill := by
  ext z
  constructor
  · rintro ⟨⟨e, he⟩, hz⟩
    have hl : e ≠ M.site.left := by
      intro h; subst e; exact hz (M.site.left_subset_fill he)
    have hr : e ≠ M.site.right := by
      intro h; subst e; exact hz (M.site.right_subset_fill he)
    exact ⟨⟨M.arcMap e, (M.retained_trace e hl hr).symm ▸ he⟩, hz⟩
  · rintro ⟨⟨f, hf⟩, hz⟩
    obtain ⟨e, rfl⟩ := M.arcMap_surjective f
    have hl : e ≠ M.site.left := by
      intro h; subst e; exact hz (M.chord_subset_fill hf)
    have hr : e ≠ M.site.right := by
      intro h; subst e
      have hm : M.arcMap M.site.right = M.arcMap M.site.left :=
        (M.arcMap_fibers _ _).mpr (Or.inr (Or.inr ⟨rfl, rfl⟩))
      rw [hm] at hf
      exact hz (M.chord_subset_fill hf)
    exact ⟨⟨e, M.retained_trace e hl hr ▸ hf⟩, hz⟩

end EmptyTriangleContraction
end
end DirectGLSSW.HOMFLY







