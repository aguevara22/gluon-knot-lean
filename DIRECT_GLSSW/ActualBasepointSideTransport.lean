import NormalStripIndex

set_option autoImplicit false
noncomputable section
open DirectGLSSW Filter Topology
namespace DirectGLSSW.HOMFLY.PLWinding

theorem actual_base_parameter_regular {D : PLLinkDiagram}
    (T : BasedTraversal D) (C : diagramComponent D) (τ : ℝ) (hτ0 : 0 < τ) (hτ1 : τ < 1) :
    let e := (T.baseArc C).val
    let m := componentArcLength D e
    let q := actualComponentWord T C
    let i₀ : Fin m := ⟨0,componentArcLength_pos D e⟩
    ∀ j : Fin m, j ≠ i₀ → normalAtEdgeParameter q i₀ τ 0 ∉ edgeTrace q j := by
  intro e m q i₀ j hj hz
  have hcell := actualComponentWord_edge_cell T C i₀ τ ⟨hτ0.le,hτ1.le⟩
  have hucell := PrincipalTurning.uniformPLCurve_arc_cell D e (0 : ℤ) τ ⟨hτ0.le,hτ1.le⟩
  have hbase : normalAtEdgeParameter q i₀ τ 0 = Complex.equivRealProd.symm
      (affinePoint (D.vertexPoint (D.arcSource e)) (D.vertexPoint (D.arcTarget e)) τ) := by
    have h := hcell
    simp only [i₀,Nat.cast_zero,zero_add] at h
    rw [show τ = ((0 : ℤ) : ℝ) + τ by simp,hucell] at h
    simpa [normalAtEdgeParameter] using h.symm
  obtain ⟨t,ht0,ht1,heq⟩ := (edgeTrace_iff_literal q j _).mp hz
  have hcellj := actualComponentWord_edge_cell T C j t ⟨ht0,ht1⟩
  have hucellj := PrincipalTurning.uniformPLCurve_arc_cell D e (j.val : ℤ) t ⟨ht0,ht1⟩
  have htj : ((j.val : ℤ) : ℝ)+t=(j.val : ℝ)+t := by norm_cast
  rw [htj] at hucellj
  rw [hucellj] at hcellj
  have harc : (D.continuation ^ j.val) e ≠ e := by
    intro he
    apply hj
    apply actualComponentWord_arc_injective T C
    change (D.continuation ^ j.val) e = (D.continuation ^ i₀.val) e
    simpa [i₀] using he
  have hp : affinePoint (D.vertexPoint (D.arcSource e)) (D.vertexPoint (D.arcTarget e)) τ =
      affinePoint (D.vertexPoint (D.arcSource ((D.continuation ^ j.val) e)))
        (D.vertexPoint (D.arcTarget ((D.continuation ^ j.val) e))) t := by
    apply Complex.equivRealProd.symm.injective
    exact hbase.symm.trans (heq.trans hcellj.symm)
  by_cases ht0eq : t = 0
  · subst t
    exact D.vertices_avoid_arc_interiors (D.arcSource ((D.continuation ^ j.val) e)) e τ hτ0 hτ1
      (by simpa [affinePoint] using hp.symm)
  · by_cases ht1eq : t = 1
    · subst t
      exact D.vertices_avoid_arc_interiors (D.arcTarget ((D.continuation ^ j.val) e)) e τ hτ0 hτ1
        (by simpa [affinePoint] using hp.symm)
    · exact D.arc_interiors_disjoint e ((D.continuation ^ j.val) e) harc.symm τ t hτ0 hτ1
        (lt_of_le_of_ne ht0 (Ne.symm ht0eq)) (lt_of_le_of_ne ht1 ht1eq) hp

/-- Every interior point of the selected actual base arc has the same
ordered pair of genuine adjacent winding indices as its midpoint. -/
theorem actual_base_side_indices_at_parameter {D : PLLinkDiagram}
    (T : BasedTraversal D) (C : diagramComponent D) (τ : ℝ) (hτ0 : 0 < τ) (hτ1 : τ < 1) :
    let e := (T.baseArc C).val
    let m := componentArcLength D e
    let q := actualComponentWord T C
    let i₀ : Fin m := ⟨0,componentArcLength_pos D e⟩
    let pair := actualBaseSideIndexPair T C
    ∃ δ : ℝ, 0 < δ ∧
      (∀ ε ∈ Set.Ioo (0 : ℝ) δ,
        ∃ h : AvoidsPolygonEdges q (normalAtEdgeParameter q i₀ τ ε),
          windingIndex q _ h = pair.1) ∧
      (∀ ε ∈ Set.Ioo (-δ) (0 : ℝ),
        ∃ h : AvoidsPolygonEdges q (normalAtEdgeParameter q i₀ τ ε),
          windingIndex q _ h = pair.2) := by
  intro e m q i₀ pair
  let a : ℝ := min τ (1/2)
  let b : ℝ := max τ (1/2)
  have hτ : τ ∈ Set.Icc a b := ⟨min_le_left _ _,le_max_left _ _⟩
  have hmid : (1/2 : ℝ) ∈ Set.Icc a b := ⟨min_le_right _ _,le_max_right _ _⟩
  have hreg : ∀ t ∈ Set.Icc a b, ∀ j : Fin m, j ≠ i₀ →
      normalAtEdgeParameter q i₀ t 0 ∉ edgeTrace q j := by
    intro t ht
    have ha : 0 < a := lt_min hτ0 (by norm_num)
    have hb : b < 1 := max_lt hτ1 (by norm_num)
    exact actual_base_parameter_regular T C t (ha.trans_le ht.1) (ht.2.trans_lt hb)
  obtain ⟨δ₁,hδ₁,hstrip⟩ := exists_normal_strip q i₀ a b
    (actualComponentWord_base_dir_ne_zero T C) hreg
  obtain ⟨δ₂,hδ₂,hspec⟩ := (actualBaseSideIndexPair_characterization T C).1
  refine ⟨min δ₁ δ₂,lt_min hδ₁ hδ₂,?_,?_⟩
  · intro ε hε
    have hε1 : |ε| < δ₁ := by rw [abs_of_pos hε.1]; exact hε.2.trans_le (min_le_left _ _)
    have hε2 : ε ∈ Set.Ioo (0 : ℝ) δ₂ := ⟨hε.1,hε.2.trans_le (min_le_right _ _)⟩
    have ha := hstrip ε hε1 (ne_of_gt hε.1)
    obtain ⟨hm,heq⟩ := hspec.1 ε hε2
    refine ⟨ha τ hτ,?_⟩
    have he := windingIndex_eq_along_normal_strip q i₀ a b ε τ (1/2) ha hτ hmid
    exact he.trans (by simpa only [normalAtEdgeParameter_midpoint] using heq)
  · intro ε hε
    have hε1 : |ε| < δ₁ := by
      rw [abs_of_neg hε.2]
      have hmin := min_le_left δ₁ δ₂
      linarith [hε.1]
    have hε2 : ε ∈ Set.Ioo (-δ₂) (0 : ℝ) := by
      refine ⟨?_,hε.2⟩
      have hmin := min_le_right δ₁ δ₂
      linarith [hε.1]
    have ha := hstrip ε hε1 (ne_of_lt hε.2)
    obtain ⟨hm,heq⟩ := hspec.2 ε hε2
    refine ⟨ha τ hτ,?_⟩
    have he := windingIndex_eq_along_normal_strip q i₀ a b ε τ (1/2) ha hτ hmid
    exact he.trans (by simpa only [normalAtEdgeParameter_midpoint] using heq)

end DirectGLSSW.HOMFLY.PLWinding


