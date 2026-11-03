import HOMFLYEmptyTriangleCodeLaws

set_option autoImplicit false
namespace DirectGLSSW.HOMFLY
noncomputable section
namespace EmptyTriangleSite
variable {D : PLLinkDiagram} (S : EmptyTriangleSite D)

theorem contract_vertices_avoid (v : S.ContractVertex) (e : S.ContractArc)
    (t : ℝ) (h0 : 0 < t) (h1 : t < 1) :
    D.vertexPoint v.val ≠ affinePoint
      (D.vertexPoint (S.contractSource e).val) (D.vertexPoint (S.contractTarget e).val) t := by
  intro h
  by_cases he : e.val = S.right
  · have hh : D.vertexPoint v.val = affinePoint S.patch.a S.patch.c t := by
      simpa only [contractSource, contractTarget, he, ite_true, ite_false, S.start_eq, S.end_eq] using h
    apply S.open_chord_avoids_source t h0 h1
    rw [← hh]
    exact vertexPoint_mem_plDrawingTrace D v.val
  · apply D.vertices_avoid_arc_interiors v.val e.val t h0 h1
    simpa only [contractSource, contractTarget, if_neg he] using h

theorem contract_interiors_disjoint (e f : S.ContractArc) (hef : e ≠ f)
    (s t : ℝ) (hs0 : 0 < s) (hs1 : s < 1) (ht0 : 0 < t) (ht1 : t < 1) :
    affinePoint (D.vertexPoint (S.contractSource e).val) (D.vertexPoint (S.contractTarget e).val) s ≠
      affinePoint (D.vertexPoint (S.contractSource f).val) (D.vertexPoint (S.contractTarget f).val) t := by
  intro h
  by_cases he : e.val = S.right <;> by_cases hf : f.val = S.right
  · exact hef (Subtype.ext (he.trans hf.symm))
  · have hh : affinePoint S.patch.a S.patch.c s =
        affinePoint (D.vertexPoint (D.arcSource f.val)) (D.vertexPoint (D.arcTarget f.val)) t := by
      simpa only [contractSource, contractTarget, he, ite_true, ite_false, if_neg hf, S.start_eq, S.end_eq] using h
    apply S.open_chord_avoids_source s hs0 hs1
    refine ⟨f.val, ?_⟩
    rw [hh]
    exact affinePoint_mem_plArcTrace D f.val t (le_of_lt ht0) (le_of_lt ht1)
  · have hh : affinePoint (D.vertexPoint (D.arcSource e.val)) (D.vertexPoint (D.arcTarget e.val)) s =
        affinePoint S.patch.a S.patch.c t := by
      simpa only [contractSource, contractTarget, hf, ite_true, ite_false, if_neg he, S.start_eq, S.end_eq] using h
    apply S.open_chord_avoids_source t ht0 ht1
    refine ⟨e.val, ?_⟩
    rw [← hh]
    exact affinePoint_mem_plArcTrace D e.val s (le_of_lt hs0) (le_of_lt hs1)
  · apply D.arc_interiors_disjoint e.val f.val (fun h => hef (Subtype.ext h)) s t hs0 hs1 ht0 ht1
    simpa only [contractSource, contractTarget, if_neg he, if_neg hf] using h

/-- Actual target diagram: the middle vertex and left arc are deleted; the
right arc is the chord. All validity fields are proved from the source site. -/
def contractDiagram : PLLinkDiagram where
  nVertex := Fintype.card S.ContractVertex
  nArc := Fintype.card S.ContractArc
  nCrossing := D.nCrossing
  vertexPoint v := D.vertexPoint (S.contractVertexEquiv.symm v).val
  arcSource e := S.contractVertexEquiv (S.contractSource (S.contractArcEquiv.symm e))
  arcTarget e := S.contractVertexEquiv (S.contractTarget (S.contractArcEquiv.symm e))
  crossingVertex c := S.contractVertexEquiv (S.contractCrossing c)
  crossingVertex_injective := by
    intro c d h
    exact D.crossingVertex_injective (congrArg Subtype.val (S.contractVertexEquiv.injective h))
  incoming c i := S.contractArcEquiv (S.contractIncoming c i)
  outgoing c i := S.contractArcEquiv (S.contractOutgoing c i)
  incoming_target := by
    intro c i
    simp only [Equiv.symm_apply_apply, S.contract_incoming_target]
  outgoing_source := by
    intro c i
    simp only [Equiv.symm_apply_apply, S.contract_outgoing_source]
  four_ports_distinct := by
    intro c
    refine ⟨?_, ?_, ?_⟩
    · intro h
      exact (D.four_ports_distinct c).1 (congrArg Subtype.val (S.contractArcEquiv.injective h))
    · intro h
      exact (D.four_ports_distinct c).2.1 (congrArg Subtype.val (S.contractArcEquiv.injective h))
    · intro i j h
      exact (D.four_ports_distinct c).2.2 i j (congrArg Subtype.val (S.contractArcEquiv.injective h))
  crossing_incidence_complete := by
    intro c e
    simpa only [Equiv.apply_eq_iff_eq, ← Equiv.symm_apply_eq, Equiv.symm_apply_apply] using
      S.contract_crossing_incidence c (S.contractArcEquiv.symm e)
  regular_degree_one := by
    classical
    intro v hv
    have hreg := S.contract_regular_unique (S.contractVertexEquiv.symm v) (by
      intro c h
      apply hv c
      exact (congrArg S.contractVertexEquiv h).trans (S.contractVertexEquiv.apply_symm_apply v))
    constructor
    · apply (filter_card_one_iff_unique _).mpr
      obtain ⟨e, he, hu⟩ := hreg.1
      refine ⟨S.contractArcEquiv e, ?_, ?_⟩
      · simp only [Equiv.symm_apply_apply, he, Equiv.apply_symm_apply]
      · intro f hf
        apply S.contractArcEquiv.symm.injective
        simp only [Equiv.symm_apply_apply]
        apply hu
        exact S.contractVertexEquiv.injective (hf.trans (S.contractVertexEquiv.apply_symm_apply v).symm)
    · apply (filter_card_one_iff_unique _).mpr
      obtain ⟨e, he, hu⟩ := hreg.2
      refine ⟨S.contractArcEquiv e, ?_, ?_⟩
      · simp only [Equiv.symm_apply_apply, he, Equiv.apply_symm_apply]
      · intro f hf
        apply S.contractArcEquiv.symm.injective
        simp only [Equiv.symm_apply_apply]
        apply hu
        exact S.contractVertexEquiv.injective (hf.trans (S.contractVertexEquiv.apply_symm_apply v).symm)
  through := D.through
  continuation := (S.contractArcEquiv.symm.trans S.contractPerm).trans S.contractArcEquiv
  continuation_incidence := by
    intro e
    simp only [Equiv.trans_apply, Equiv.symm_apply_apply]
    exact congrArg S.contractVertexEquiv (S.contract_continuation_incidence _)
  continuation_crossing := by
    intro c i
    simp only [Equiv.trans_apply, Equiv.symm_apply_apply, S.contract_continuation_crossing]
  overBranch := D.overBranch
  vertexPoint_injective := by
    intro v w h
    exact S.contractVertexEquiv.symm.injective (Subtype.ext (D.vertexPoint_injective h))
  arc_endpoints_distinct := by
    intro e h
    exact S.contract_endpoints_distinct _ (S.contractVertexEquiv.injective h)
  arc_interiors_disjoint := by
    intro e f hef s t hs0 hs1 ht0 ht1
    simpa only [Equiv.symm_apply_apply] using
      S.contract_interiors_disjoint (S.contractArcEquiv.symm e) (S.contractArcEquiv.symm f)
        (fun h => hef (S.contractArcEquiv.symm.injective h)) s t hs0 hs1 ht0 ht1
  vertices_avoid_arc_interiors := by
    intro v e t h0 h1
    simpa only [Equiv.symm_apply_apply] using
      S.contract_vertices_avoid (S.contractVertexEquiv.symm v) (S.contractArcEquiv.symm e) t h0 h1
  through_tangents_positive_collinear := by
    intro c i
    simpa only [Equiv.symm_apply_apply, contractCrossing, contractSource, contractTarget,
      contractIncoming, contractOutgoing, if_neg (S.incoming_ne_right c i)] using
      D.through_tangents_positive_collinear c i
  crossing_transverse := by
    intro c
    simpa only [Equiv.symm_apply_apply, contractCrossing, contractSource, contractIncoming,
      if_neg (S.incoming_ne_right c 0), if_neg (S.incoming_ne_right c 1)] using D.crossing_transverse c

/-- Concrete total source arc-label map into the constructed target. -/
def contractArcMap (e : Fin D.nArc) : Fin S.contractDiagram.nArc :=
  S.contractArcEquiv (S.contractMap e)

def contractWitness : EmptyTriangleContraction D S.contractDiagram where
  site := S
  arcMap := S.contractArcMap
  arcMap_surjective := S.contractArcEquiv.surjective.comp S.contractMap_surjective
  arcMap_fibers := by
    intro e f
    exact S.contractArcEquiv.injective.eq_iff.trans (S.contractMap_fibers e f)
  chord_start := by
    simp [contractArcMap, contractDiagram, contractMap, contractSource, S.distinct.symm, S.start_eq]
  chord_end := by
    simp [contractArcMap, contractDiagram, contractMap, contractTarget, S.end_eq]
  retained_start := by
    intro e hl hr
    simp [contractArcMap, contractDiagram, contractMap, contractSource, hl, hr]
  retained_end := by
    intro e hl hr
    simp [contractArcMap, contractDiagram, contractMap, contractTarget, hl]
  continuation_map := by
    intro e hl
    change S.contractArcEquiv (S.contractMap (D.continuation e)) =
      S.contractArcEquiv (S.contractPerm (S.contractArcEquiv.symm (S.contractArcEquiv (S.contractMap e))))
    rw [Equiv.symm_apply_apply]
    apply congrArg S.contractArcEquiv
    apply Subtype.ext
    rw [S.contractPerm_val, S.contractMap_of_ne e hl]
  crossingEquiv := Equiv.refl _
  crossing_point := by
    intro c
    simp only [contractDiagram, Equiv.refl_apply, Equiv.symm_apply_apply, contractCrossing]
  incoming_map := by
    intro c i
    change S.contractArcEquiv (S.contractIncoming c i) = S.contractArcEquiv (S.contractMap (D.incoming c i))
    apply congrArg S.contractArcEquiv
    apply Subtype.ext
    exact (S.contractMap_of_ne _ (S.incoming_ne_left c i)).symm
  outgoing_map := by
    intro c i
    change S.contractArcEquiv (S.contractOutgoing c i) = S.contractArcEquiv (S.contractMap (D.outgoing c i))
    apply congrArg S.contractArcEquiv
    apply Subtype.ext
    exact (S.contractMap_of_ne _ (S.outgoing_ne_left c i)).symm
  through_map := by intro c; rfl
  overBranch_map := by intro c; rfl

theorem contract_crossingDet (c : Fin D.nCrossing) :
    crossingDet S.contractDiagram c = crossingDet D c := by
  simp only [crossingDet, strandTangent, contractDiagram, Equiv.symm_apply_apply,
    contractCrossing, contractSource, contractIncoming,
    if_neg (S.incoming_ne_right c (D.overBranch c)),
    if_neg (S.incoming_ne_right c (otherBranch (D.overBranch c)))]

theorem contract_crossingSign (c : Fin D.nCrossing) :
    crossingSign S.contractDiagram c = crossingSign D c := by
  unfold crossingSign nonzeroScalarSign
  rw [S.contract_crossingDet]

end EmptyTriangleSite

theorem exists_emptyTriangleContraction (D : PLLinkDiagram) (S : EmptyTriangleSite D) :
    ∃ (E : PLLinkDiagram) (M : EmptyTriangleContraction D E), M.site = S :=
  ⟨S.contractDiagram, S.contractWitness, rfl⟩

end
end DirectGLSSW.HOMFLY





