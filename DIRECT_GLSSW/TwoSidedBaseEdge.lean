import ActualComponentWord

set_option autoImplicit false
noncomputable section
open DirectGLSSW Filter Topology

namespace DirectGLSSW.HOMFLY.PLWinding

/-- The exact closed image of one finite affine edge. -/
def edgeTrace {n : ℕ} (q : Fin n → ℂ) (i : Fin n) : Set ℂ :=
  (fun t : ℝ => q i + (t : ℂ) *
    (q (cyclicSuccessorPerm n i) - q i)) '' Set.Icc 0 1

theorem edgeTrace_iff_literal {n : ℕ} (q : Fin n → ℂ) (i : Fin n) (z : ℂ) :
    z ∈ edgeTrace q i ↔ ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧
      z = q i + (t : ℂ) * (q (cyclicSuccessorPerm n i) - q i) := by
  simp only [edgeTrace, Set.mem_image, Set.mem_Icc]
  constructor
  · rintro ⟨t, ⟨ht0, ht1⟩, rfl⟩
    exact ⟨t, ht0, ht1, rfl⟩
  · rintro ⟨t, ht0, ht1, rfl⟩
    exact ⟨t, ⟨ht0, ht1⟩, rfl⟩

theorem isClosed_edgeTrace {n : ℕ} (q : Fin n → ℂ) (i : Fin n) :
    IsClosed (edgeTrace q i) := by
  have hc : Continuous (fun t : ℝ => q i + (t : ℂ) *
      (q (cyclicSuccessorPerm n i) - q i)) := by fun_prop
  exact (isCompact_Icc.image hc).isClosed

/-- Every off-trace point has an off-trace neighborhood. -/
theorem eventually_avoids_edges {n : ℕ} (q : Fin n → ℂ) (z : ℂ)
    (hAvoid : AvoidsPolygonEdges q z) :
    ∀ᶠ ζ in 𝓝 z, AvoidsPolygonEdges q ζ := by
  have hterm (i : Fin n) : ∀ᶠ ζ in 𝓝 z, ζ ∉ edgeTrace q i := by
    apply (isClosed_edgeTrace q i).isOpen_compl.mem_nhds
    intro hz
    obtain ⟨t, ht0, ht1, heq⟩ :=
      (edgeTrace_iff_literal q i z).mp hz
    exact hAvoid i t ht0 ht1 heq
  classical
  have hfinite (s : Finset (Fin n)) :
      ∀ᶠ ζ in 𝓝 z, ∀ i ∈ s, ζ ∉ edgeTrace q i := by
    induction s using Finset.induction_on with
    | empty => filter_upwards [] with ζ; simp
    | @insert i s hi ih =>
        filter_upwards [hterm i, ih] with ζ hzi hzs j hj
        rcases Finset.mem_insert.mp hj with rfl | hjs
        · exact hzi
        · exact hzs j hjs
  have hall : ∀ᶠ ζ in 𝓝 z, ∀ i : Fin n, ζ ∉ edgeTrace q i := by
    simpa using hfinite (Finset.univ : Finset (Fin n))
  filter_upwards [hall] with ζ hζ
  intro i t ht0 ht1 heq
  exact hζ i ((edgeTrace_iff_literal q i ζ).mpr ⟨t, ht0, ht1, heq⟩)

/-- The actual oriented affine midpoint, with normal displacement measured
in units of the directed edge vector. -/
def normalAtEdgeMidpoint {n : ℕ} (q : Fin n → ℂ)
    (i : Fin n) (ε : ℝ) : ℂ :=
  q i + ((1/2 : ℝ) : ℂ) *
      (q (cyclicSuccessorPerm n i) - q i) +
    (ε : ℂ) * Complex.I *
      (q (cyclicSuccessorPerm n i) - q i)

theorem normalAtEdgeMidpoint_eq_literal {n : ℕ} (q : Fin n → ℂ)
    (i : Fin n) (ε : ℝ) :
    normalAtEdgeMidpoint q i ε =
      q i + ((1/2 : ℝ) : ℂ) *
        (q (cyclicSuccessorPerm n i) - q i) +
      (ε : ℂ) * Complex.I *
        (q (cyclicSuccessorPerm n i) - q i) := rfl

theorem normalAtEdgeMidpoint_not_on_edge {n : ℕ} (q : Fin n → ℂ)
    (i : Fin n) (hdir : q (cyclicSuccessorPerm n i) - q i ≠ 0)
    (ε : ℝ) (hε : ε ≠ 0) :
    normalAtEdgeMidpoint q i ε ∉ edgeTrace q i := by
  intro hz
  obtain ⟨t, _, _, heq⟩ := (edgeTrace_iff_literal q i _).mp hz
  have hmul : (ε : ℂ) * Complex.I *
      (q (cyclicSuccessorPerm n i) - q i) =
      ((t - 1/2 : ℝ) : ℂ) *
        (q (cyclicSuccessorPerm n i) - q i) := by
    dsimp [normalAtEdgeMidpoint] at heq
    simp only [cyclicSuccessorPerm_apply] at *
    push_cast at heq ⊢
    linear_combination heq
  have heq' : (ε : ℂ) * Complex.I = ((t - 1/2 : ℝ) : ℂ) :=
    mul_right_cancel₀ hdir hmul
  have him := congrArg Complex.im heq'
  simp at him
  exact hε him

/-- A regular edge midpoint has two genuine off-trace normal germs. The
regularity premise names only absence of *other* actual edges at the
midpoint; no winding value or crossing formula is assumed. -/
theorem eventually_normal_avoids_edges {n : ℕ} (q : Fin n → ℂ)
    (i : Fin n) (hdir : q (cyclicSuccessorPerm n i) - q i ≠ 0)
    (hregular : ∀ j : Fin n, j ≠ i →
      normalAtEdgeMidpoint q i 0 ∉ edgeTrace q j) :
    ∀ᶠ ε in 𝓝 (0 : ℝ), ε ≠ 0 →
      AvoidsPolygonEdges q (normalAtEdgeMidpoint q i ε) := by
  have hterm (j : Fin n) : ∀ᶠ z in 𝓝 (normalAtEdgeMidpoint q i 0),
      j ≠ i → z ∉ edgeTrace q j := by
    by_cases hji : j = i
    · subst j
      filter_upwards [] with z hj
      exact (hj rfl).elim
    · filter_upwards [(isClosed_edgeTrace q j).isOpen_compl.mem_nhds
          (hregular j hji)] with z hz _
      exact hz
  classical
  have hfinite (s : Finset (Fin n)) :
      ∀ᶠ z in 𝓝 (normalAtEdgeMidpoint q i 0),
        ∀ j ∈ s, j ≠ i → z ∉ edgeTrace q j := by
    induction s using Finset.induction_on with
    | empty => filter_upwards [] with z; simp
    | @insert j s hj ih =>
        filter_upwards [hterm j, ih] with z hz hzs k hk hki
        rcases Finset.mem_insert.mp hk with rfl | hks
        · exact hz hki
        · exact hzs k hks hki
  have hall : ∀ᶠ z in 𝓝 (normalAtEdgeMidpoint q i 0),
      ∀ j : Fin n, j ≠ i → z ∉ edgeTrace q j := by
    simpa using hfinite (Finset.univ : Finset (Fin n))
  have hcont : ContinuousAt (normalAtEdgeMidpoint q i) (0 : ℝ) := by
    unfold normalAtEdgeMidpoint
    fun_prop
  filter_upwards [hcont.eventually hall] with ε hε hε0
  intro j t ht0 ht1 heq
  by_cases hji : j = i
  · subst j
    exact (normalAtEdgeMidpoint_not_on_edge q i hdir ε hε0)
      ((edgeTrace_iff_literal q i _).mpr ⟨t, ht0, ht1, heq⟩)
  · exact hε j hji ((edgeTrace_iff_literal q j _).mpr ⟨t, ht0, ht1, heq⟩)

theorem actualComponentWord_base_midpoint_regular {D : PLLinkDiagram}
    (T : BasedTraversal D) (C : diagramComponent D) :
    let e := (T.baseArc C).val
    let m := componentArcLength D e
    let q := actualComponentWord T C
    let i₀ : Fin m := ⟨0, componentArcLength_pos D e⟩
    ∀ j : Fin m, j ≠ i₀ →
      normalAtEdgeMidpoint q i₀ 0 ∉ edgeTrace q j := by
  intro e m q i₀ j hj
  have hmidcell := actualComponentWord_based_edge_cell T C i₀ (1/2)
    (by constructor <;> norm_num)
  have htime : ((i₀.val : ℝ) + 1/2 - 1/2) = 0 := by simp [i₀]
  rw [htime, PrincipalTurning.basedUniformPLCurve_midpoint] at hmidcell
  have hmid : normalAtEdgeMidpoint q i₀ 0 =
      Complex.equivRealProd.symm
        (affinePoint (D.vertexPoint (D.arcSource e))
          (D.vertexPoint (D.arcTarget e)) (1/2)) := by
    simpa [normalAtEdgeMidpoint] using hmidcell.symm
  intro hz
  obtain ⟨t, ht0, ht1, heq⟩ := (edgeTrace_iff_literal q j _).mp hz
  have hcell := actualComponentWord_edge_cell T C j t ⟨ht0,ht1⟩
  have hucell := PrincipalTurning.uniformPLCurve_arc_cell D e (j.val : ℤ) t ⟨ht0,ht1⟩
  have htimej : ((j.val : ℤ) : ℝ) + t = (j.val : ℝ) + t := by norm_cast
  rw [htimej] at hucell
  rw [hucell] at hcell
  have harc : (D.continuation ^ j.val) e ≠ e := by
    intro he
    apply hj
    apply actualComponentWord_arc_injective T C
    change (D.continuation ^ j.val) e = (D.continuation ^ i₀.val) e
    simpa [i₀] using he
  have hpoint : affinePoint (D.vertexPoint (D.arcSource e))
      (D.vertexPoint (D.arcTarget e)) (1/2) =
      affinePoint (D.vertexPoint (D.arcSource ((D.continuation ^ j.val) e)))
        (D.vertexPoint (D.arcTarget ((D.continuation ^ j.val) e))) t := by
    apply Complex.equivRealProd.symm.injective
    exact hmid.symm.trans (heq.trans hcell.symm)
  by_cases ht0eq : t = 0
  · subst t
    have hv := D.vertices_avoid_arc_interiors
      (D.arcSource ((D.continuation ^ j.val) e)) e (1/2)
      (by norm_num) (by norm_num)
    apply hv
    simpa [affinePoint] using hpoint.symm
  · by_cases ht1eq : t = 1
    · subst t
      have hv := D.vertices_avoid_arc_interiors
        (D.arcTarget ((D.continuation ^ j.val) e)) e (1/2)
        (by norm_num) (by norm_num)
      apply hv
      simpa [affinePoint] using hpoint.symm
    · exact D.arc_interiors_disjoint e ((D.continuation ^ j.val) e)
        harc.symm (1/2) t (by norm_num) (by norm_num)
        (lt_of_le_of_ne ht0 (Ne.symm ht0eq))
        (lt_of_le_of_ne ht1 ht1eq) hpoint

/-- Genuine off-trace normal germs on both sides of the actual selected
base arc. This is stated on a punctured neighborhood, without choosing
one side's index or using a Whitney identity. -/
theorem actualComponentWord_normal_eventually_offtrace {D : PLLinkDiagram}
    (T : BasedTraversal D) (C : diagramComponent D) :
    let e := (T.baseArc C).val
    let m := componentArcLength D e
    let q := actualComponentWord T C
    let i₀ : Fin m := ⟨0, componentArcLength_pos D e⟩
    ∀ᶠ ε in 𝓝 (0 : ℝ), ε ≠ 0 →
      AvoidsPolygonEdges q (normalAtEdgeMidpoint q i₀ ε) := by
  intro e m q i₀
  have hsource : q i₀ = Complex.equivRealProd.symm
      (D.vertexPoint (D.arcSource e)) := by
    simpa only [q, i₀] using actualComponentWord_zero T C
  have htarget : q (cyclicSuccessorPerm m i₀) =
      Complex.equivRealProd.symm (D.vertexPoint (D.arcTarget e)) := by
    simpa only [q, m, e] using actualComponentWord_successor T C i₀
  have hdir : q (cyclicSuccessorPerm m i₀) - q i₀ ≠ 0 := by
    rw [htarget, hsource]
    apply sub_ne_zero.mpr
    intro h
    exact D.arc_endpoints_distinct e
      (D.vertexPoint_injective (Complex.equivRealProd.symm.injective h.symm))
  exact eventually_normal_avoids_edges q i₀ hdir
    (actualComponentWord_base_midpoint_regular T C)

theorem actualComponentWord_normal_radius {D : PLLinkDiagram}
    (T : BasedTraversal D) (C : diagramComponent D) :
    let e := (T.baseArc C).val
    let m := componentArcLength D e
    let q := actualComponentWord T C
    let i₀ : Fin m := ⟨0, componentArcLength_pos D e⟩
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, |ε| < δ → ε ≠ 0 →
      AvoidsPolygonEdges q (normalAtEdgeMidpoint q i₀ ε) := by
  intro e m q i₀
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp
    (actualComponentWord_normal_eventually_offtrace T C)
  refine ⟨δ, hδ, ?_⟩
  intro ε hε hε0
  apply hball ?_ hε0
  simpa [Metric.mem_ball, Real.dist_eq, abs_sub_comm] using hε

end DirectGLSSW.HOMFLY.PLWinding


