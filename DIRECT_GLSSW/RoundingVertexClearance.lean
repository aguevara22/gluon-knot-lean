import ActualTangentLift
import DirectGLSSW.TruncationCommonRadius

set_option autoImplicit false
namespace DirectGLSSW.HOMFLY.PrincipalTurning

/-- Nonincident closed arcs genuinely exclude the actual vertex. -/
theorem vertex_ne_nonincident_closed_arc (D : PLLinkDiagram) (v : Fin D.nVertex)
    (e : Fin D.nArc) (hs : D.arcSource e ≠ v) (ht : D.arcTarget e ≠ v)
    (t : ℝ) (htI : t ∈ Set.Icc 0 1) :
    D.vertexPoint v ≠ affinePoint (D.vertexPoint (D.arcSource e))
      (D.vertexPoint (D.arcTarget e)) t := by
  by_cases h0 : t = 0
  · subst t
    rw [affinePoint_zero]
    exact fun h => hs (D.vertexPoint_injective h.symm)
  · by_cases h1 : t = 1
    · subst t
      rw [affinePoint_one]
      exact fun h => ht (D.vertexPoint_injective h.symm)
    · exact D.vertices_avoid_arc_interiors v e t
        (lt_of_le_of_ne htI.1 (Ne.symm h0)) (lt_of_le_of_ne htI.2 h1)

/-- Actual finite PL geometry provides a vertex neighborhood missing all
nonincident closed arcs, all other vertices, and a specified nonvertex point. -/
theorem exists_vertex_localization_radius (D : PLLinkDiagram) (b : PlanarPoint ℝ)
    (hb : ∀ v, D.vertexPoint v ≠ b) (v : Fin D.nVertex) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ x : PlanarPoint ℝ, dist x (D.vertexPoint v) < ρ →
      x ≠ b ∧
      (∀ w : Fin D.nVertex, w ≠ v → x ≠ D.vertexPoint w) ∧
      (∀ e : Fin D.nArc, D.arcSource e ≠ v → D.arcTarget e ≠ v →
        ∀ t : ℝ, t ∈ Set.Icc 0 1 →
          x ≠ affinePoint (D.vertexPoint (D.arcSource e))
            (D.vertexPoint (D.arcTarget e)) t) := by
  classical
  let E := {e : Fin D.nArc // D.arcSource e ≠ v ∧ D.arcTarget e ≠ v}
  let edgePoint : E × ℝ → PlanarPoint ℝ := fun z =>
    affinePoint (D.vertexPoint (D.arcSource z.1.val))
      (D.vertexPoint (D.arcTarget z.1.val)) z.2
  have hleft : Continuous (fun z : E × ℝ => D.vertexPoint (D.arcSource z.1.val)) :=
    (continuous_of_discreteTopology (f := fun e : E => D.vertexPoint (D.arcSource e.val))).comp continuous_fst
  have hright : Continuous (fun z : E × ℝ => D.vertexPoint (D.arcTarget z.1.val)) :=
    (continuous_of_discreteTopology (f := fun e : E => D.vertexPoint (D.arcTarget e.val))).comp continuous_fst
  have hedge : Continuous edgePoint := by
    dsimp only [edgePoint, affinePoint]
    exact (hleft.fst.add (continuous_snd.mul (hright.fst.sub hleft.fst))).prodMk
      (hleft.snd.add (continuous_snd.mul (hright.snd.sub hleft.snd)))
  let K : Set (PlanarPoint ℝ) := edgePoint ''
    ((Set.univ : Set E) ×ˢ (Set.Icc (0 : ℝ) 1))
  have hK : IsCompact K :=
    (Set.finite_univ.isCompact.prod isCompact_Icc).image hedge
  have hvK : D.vertexPoint v ∉ K := by
    rintro ⟨⟨e,t⟩,⟨_,hti⟩,heq⟩
    exact vertex_ne_nonincident_closed_arc D v e.val e.property.1 e.property.2 t hti heq.symm
  let W := {w : Fin D.nVertex // w ≠ v}
  let V : Set (PlanarPoint ℝ) := Set.range (fun w : W => D.vertexPoint w.val)
  have hV : IsCompact V := (Set.finite_range _).isCompact
  have hvV : D.vertexPoint v ∉ V := by
    rintro ⟨w,hw⟩
    exact w.property (D.vertexPoint_injective hw)
  have hclosed : IsClosed (K ∪ V ∪ {b}) :=
    (hK.isClosed.union hV.isClosed).union isClosed_singleton
  have hnot : D.vertexPoint v ∉ K ∪ V ∪ {b} := by
    simp only [Set.mem_union, Set.mem_singleton_iff, not_or]
    exact ⟨⟨hvK,hvV⟩,hb v⟩
  obtain ⟨ρ,hρ,hball⟩ := Metric.mem_nhds_iff.mp (hclosed.isOpen_compl.mem_nhds hnot)
  refine ⟨ρ,hρ,?_⟩
  intro x hx
  have hn : x ∉ K ∪ V ∪ {b} := hball (Metric.mem_ball.mpr hx)
  refine ⟨?_,?_,?_⟩
  · intro heq
    apply hn
    exact Or.inr (Set.mem_singleton_iff.mpr heq)
  · intro w hw heq
    apply hn
    exact Or.inl (Or.inr ⟨⟨w,hw⟩,heq.symm⟩)
  · intro e hs ht t hti heq
    apply hn
    exact Or.inl (Or.inl ⟨(⟨e,hs,ht⟩,t),⟨Set.mem_univ _,hti⟩,heq.symm⟩)

end DirectGLSSW.HOMFLY.PrincipalTurning


