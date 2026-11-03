import HOMFLYEmptyTriangleCodes

set_option autoImplicit false
namespace DirectGLSSW.HOMFLY
noncomputable section

theorem affinePoint_mem_plArcTrace (D : PLLinkDiagram) (e : Fin D.nArc)
    (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    affinePoint (D.vertexPoint (D.arcSource e)) (D.vertexPoint (D.arcTarget e)) t ∈
      plArcTrace D e := by
  refine ⟨1-t, t, by linarith, h0, by ring, ?_⟩
  ext <;> dsimp [affinePoint] <;> ring

theorem vertexPoint_mem_plDrawingTrace (D : PLLinkDiagram) (v : Fin D.nVertex) :
    D.vertexPoint v ∈ plDrawingTrace D := by
  classical
  by_cases h : ∃ c, D.crossingVertex c = v
  · obtain ⟨c, rfl⟩ := h
    refine ⟨D.incoming c 0, ?_⟩
    change _ ∈ segment ℝ _ _
    rw [← D.incoming_target c 0]
    exact right_mem_segment ℝ _ _
  · have hr : ∀ c, D.crossingVertex c ≠ v := by simpa only [not_exists] using h
    have hp := Finset.card_pos.mp (by rw [(D.regular_degree_one v hr).1]; omega :
      0 < (incomingArcs D.arcTarget v).card)
    obtain ⟨e, he⟩ := hp
    have hv := (Finset.mem_filter.mp he).2
    refine ⟨e, ?_⟩
    change _ ∈ segment ℝ _ _
    rw [← hv]
    exact right_mem_segment ℝ _ _

namespace EmptyTriangleSite
variable {D : PLLinkDiagram} (S : EmptyTriangleSite D)

theorem chord_endpoints_ne : S.patch.a ≠ S.patch.c := by
  intro h
  apply S.patch.nondegenerate
  rw [h]
  simp [planarDet]

/-- The open chord is disjoint from the *entire* original drawing, derived
from the actual site emptiness equality. -/
theorem open_chord_avoids_source (t : ℝ) (h0 : 0 < t) (h1 : t < 1) :
    affinePoint S.patch.a S.patch.c t ∉ plDrawingTrace D := by
  let z := affinePoint S.patch.a S.patch.c t
  have hzseg : z ∈ segment ℝ S.patch.a S.patch.c := by
    refine ⟨1-t, t, by linarith, le_of_lt h0, by ring, ?_⟩
    ext <;> dsimp [z, affinePoint] <;> ring
  have hza : z ≠ S.patch.a := by
    intro h
    have he : t = 0 := affinePoint_injective _ _ S.chord_endpoints_ne
      (h.trans (affinePoint_zero _ _).symm)
    linarith
  have hzc : z ≠ S.patch.c := by
    intro h
    have he : t = 1 := affinePoint_injective _ _ S.chord_endpoints_ne
      (h.trans (affinePoint_one _ _).symm)
    linarith
  have hzfill : z ∈ S.patch.fill := S.patch.boundary_subset_fill
    (Or.inr (by simpa only [segment_symm ℝ S.patch.c S.patch.a] using hzseg))
  intro hz
  have hs := S.empty_support ▸ (show z ∈ plDrawingTrace D ∩ S.patch.fill from ⟨hz, hzfill⟩)
  have hdet : planarDet (S.patch.c-S.patch.a) (S.patch.b-S.patch.a) ≠ 0 := by
    rw [planarDet_swap]
    exact neg_ne_zero.mpr S.patch.nondegenerate
  let R : TrianglePatch := ⟨S.patch.a, S.patch.c, S.patch.b, hdet⟩
  apply R.edge_other_sides_disjoint_away_endpoints z hza hzc hzseg
  rcases hs with hl | hr
  · apply Or.inr
    simpa only [plArcTrace, S.start_eq, S.middle_eq, segment_symm ℝ S.patch.a S.patch.b]
      using hl
  · apply Or.inl
    simpa only [plArcTrace, ← S.joint, S.middle_eq, S.end_eq,
      segment_symm ℝ S.patch.b S.patch.c] using hr

end EmptyTriangleSite
end
end DirectGLSSW.HOMFLY



