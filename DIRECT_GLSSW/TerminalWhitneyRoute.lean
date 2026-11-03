import ActualWhitneyAtBasepoint
import SourceBasepointIndexSum
import ActualTerminalFramedValue
import SourceDescendingUnlink

set_option autoImplicit false
noncomputable section
open DirectGLSSW Topology unitInterval
namespace DirectGLSSW.HOMFLY
open PermutationOrbits PrincipalTurning PositionalIndex PLWinding Coefficients
open PolygonDrawingBridge ExposedOpenPrimitive SmoothingCornerGeometry LowestRowContract
attribute [local instance] Classical.propDecidable

private theorem unitPositionalIndex_congr_probe (γ : C(I, ℂ))
    (hclosed : γ 1 = γ 0) {z w : ℂ}
    (hz : ∀ u, γ u ≠ z) (hw : ∀ u, γ u ≠ w) (hzw : z = w) :
    unitPositionalIndex γ hclosed z hz = unitPositionalIndex γ hclosed w hw := by
  subst w
  rfl

/-- The general Whitney theorem and the source fixed-root index use the same
actual parent, the same retained base arc, and the same normal probes. -/
theorem source_parent_whitney_root_probe_identification
    {n : ℕ} (x : Fin (n+2) → PlanarPoint ℝ) (hx : CyclicGeneric x)
    {s : MarkedParentState}
    (htrace : MarkedParentTrace
      (positivePolygonMarkedState x hx (initialAnchorTraversal x hx)) s)
    (he : LeftExposed x 0) (τ ε : ℝ) :
    let p := (positivePolygonEventDiagram x hx).vertexPoint
      ((positivePolygonEventDiagram x hx).arcSource (eventFin x (initialAnchor x hx)))
    let q := (positivePolygonEventDiagram x hx).vertexPoint
      ((positivePolygonEventDiagram x hx).arcTarget (eventFin x (initialAnchor x hx)))
    let C := componentOf s.1.continuation ⟨0,source_parent_nArc_pos x hx htrace⟩
    let e := (s.2.1.baseArc C).val
    let i₀ : Fin (componentArcLength s.1 e) := ⟨0,componentArcLength_pos s.1 e⟩
    normalAtEdgeParameter (actualComponentWord s.2.1 C) i₀ τ ε =
      interiorRootProbe p q τ ε ∧
    normalAtEdgeParameter (actualComponentWord s.2.1 C) i₀ τ (-ε) =
      exteriorRootProbe p q τ ε := by
  dsimp only
  let C : diagramComponent s.1 :=
    componentOf s.1.continuation ⟨0,source_parent_nArc_pos x hx htrace⟩
  let e : Fin s.1.nArc := (s.2.1.baseArc C).val
  have heq : sourceRetainedBaseArc x hx htrace = e :=
    sourceRetainedBaseArc_eq x hx htrace
  have hend := sourceRetainedBaseArc_original_endpoints x hx htrace he
  rw [heq] at hend
  have hp := hend.1
  have hq := hend.2
  have hleft (η : ℝ) : normalAtEdgeParameter (actualComponentWord s.2.1 C)
      ⟨0,componentArcLength_pos s.1 e⟩ τ η =
      interiorRootProbe (s.1.vertexPoint (s.1.arcSource e))
        (s.1.vertexPoint (s.1.arcTarget e)) τ η := by
    rw [actual_normal_parameter_eq_coordinates]
    apply Complex.ext <;>
      simp [interiorRootProbe_eq,PrincipalTurning.arcVector,affinePoint,
        Complex.equivRealProd_symm_apply] <;> ring
  constructor
  · simpa only [hp,hq] using hleft ε
  · have h := hleft (-ε)
    simpa only [interiorRootProbe,neg_neg,hp,hq] using h

/-- Terminal framing via the general Whitney theorem and the two genuine
positional indices at the original retained exposed basepoint. -/
theorem positivePolygon_history_terminal_frame_via_general_whitney
    {n : ℕ} (x : Fin (n+2) → PlanarPoint ℝ) (hx : CyclicGeneric x)
    (he : LeftExposed x 0) (s : MarkedParentState)
    (htrace : MarkedParentTrace
      (positivePolygonMarkedState x hx (initialAnchorTraversal x hx)) s)
    (hterminal : ∀ c : Fin s.1.nCrossing, ¬ badAt s.2.1 c) :
    let C := componentOf s.1.continuation ⟨0,source_parent_nArc_pos x hx htrace⟩
    diagramWrithe s.1 + componentTurnInteger s.1 C = 1 := by
  intro C
  let e := (s.2.1.baseArc C).val
  let p := (positivePolygonEventDiagram x hx).vertexPoint
      ((positivePolygonEventDiagram x hx).arcSource (eventFin x (initialAnchor x hx)))
  let q := (positivePolygonEventDiagram x hx).vertexPoint
      ((positivePolygonEventDiagram x hx).arcTarget (eventFin x (initialAnchor x hx)))
  have hbase : sourceRetainedBaseArc x hx htrace = e :=
    sourceRetainedBaseArc_eq x hx htrace
  obtain ⟨δw,hδw,hw⟩ :=
    actualComponent_whitney_at_arbitrary_basepoint s.2.1 C (1/2)
      (by norm_num) (by norm_num)
  obtain ⟨δi,hδi,hi⟩ :=
    source_parent_basepoint_index_sum x hx htrace he (1/2)
      (by norm_num) (by norm_num)
  let ε : ℝ := min δw δi / 2
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hεw : ε < δw := by dsimp [ε]; have := min_le_left δw δi; linarith
  have hεi : ε < δi := by dsimp [ε]; have := min_le_right δw δi; linarith
  obtain ⟨hpos,hneg,hposPair,hnegPair,hwh⟩ := hw ε hε hεw
  obtain ⟨hRight,hLeft,hRightZero,hLeftOne,hIndexSum⟩ := hi ε hε hεi
  have hprobe := source_parent_whitney_root_probe_identification x hx htrace he (1/2) ε
  dsimp only at hprobe
  have hpositive : unitPositionalIndex (complexPLLoop s.1 e)
      (complexPLLoop_endpoint_eq s.1 e).symm
      (normalAtEdgeParameter (actualComponentWord s.2.1 C)
        ⟨0,componentArcLength_pos s.1 e⟩ (1/2) ε) hpos = 1 := by
    have hLeft' : ∀ u : I, complexPLLoop s.1 e u ≠ interiorRootProbe p q (1/2) ε := by
      simpa only [hbase] using hLeft
    have hv : unitPositionalIndex (complexPLLoop s.1 e)
        (complexPLLoop_endpoint_eq s.1 e).symm (interiorRootProbe p q (1/2) ε) hLeft' = 1 := by
      simpa only [hbase] using hLeftOne
    exact (unitPositionalIndex_congr_probe _ _ hpos hLeft' hprobe.1).trans hv
  have hnegative : unitPositionalIndex (complexPLLoop s.1 e)
      (complexPLLoop_endpoint_eq s.1 e).symm
      (normalAtEdgeParameter (actualComponentWord s.2.1 C)
        ⟨0,componentArcLength_pos s.1 e⟩ (1/2) (-ε)) hneg = 0 := by
    have hRight' : ∀ u : I, complexPLLoop s.1 e u ≠ exteriorRootProbe p q (1/2) ε := by
      simpa only [hbase] using hRight
    have hv : unitPositionalIndex (complexPLLoop s.1 e)
        (complexPLLoop_endpoint_eq s.1 e).symm (exteriorRootProbe p q (1/2) ε) hRight' = 0 := by
      simpa only [hbase] using hRightZero
    exact (unitPositionalIndex_congr_probe _ _ hneg hRight' hprobe.2).trans hv
  have hsum := hwh
  rw [hpositive,hnegative] at hsum
  have hconn := s.2.2.connected
  rw [actualComponentSelfCrossings_eq_univ_of_connected s.2.1 hconn C] at hsum
  have hsign :
      (∑ c : Fin s.1.nCrossing,
        if 0 < complexDet (crossingVector s.1 c (firstVisitedBranch s.2.1 c))
          (crossingVector s.1 c (otherBranch (firstVisitedBranch s.2.1 c)))
        then (1 : ℝ) else -1) =
      ∑ c : Fin s.1.nCrossing,
        if crossingSign s.1 c = Sign.pos then (1 : ℝ) else -1 := by
    apply Finset.sum_congr rfl
    intro c _
    simp only [firstVisit_det_eq_crossingDet_of_not_bad s.2.1 c (hterminal c),
      ← actual_crossingSign_pos_iff s.1 c]
  rw [hsign] at hsum
  have hwrithe : ((diagramWrithe s.1 : ℤ) : ℝ) =
      ∑ c : Fin s.1.nCrossing,
        if crossingSign s.1 c = Sign.pos then (1 : ℝ) else -1 := by
    simp only [diagramWrithe,Int.cast_sum]
    apply Finset.sum_congr rfl
    intro c _
    cases hs : crossingSign s.1 c <;> simp [writheSign,hs]
  rw [← hwrithe] at hsum
  have hreal : ((diagramWrithe s.1 + componentTurnInteger s.1 C : ℤ) : ℝ) = 1 := by
    norm_num at hsum ⊢
    linarith
  exact_mod_cast hreal

/-- Connectedness transports the root-component terminal framing identity to
every component of the same actual parent. -/
theorem positivePolygon_history_terminal_frame_all_components_via_general_whitney
    {n : ℕ} (x : Fin (n+2) → PlanarPoint ℝ) (hx : CyclicGeneric x)
    (he : LeftExposed x 0) (s : MarkedParentState)
    (htrace : MarkedParentTrace
      (positivePolygonMarkedState x hx (initialAnchorTraversal x hx)) s)
    (hterminal : ∀ c : Fin s.1.nCrossing, ¬ badAt s.2.1 c)
    (C : diagramComponent s.1) :
    diagramWrithe s.1 + componentTurnInteger s.1 C = 1 := by
  let C₀ : diagramComponent s.1 :=
    componentOf s.1.continuation ⟨0,source_parent_nArc_pos x hx htrace⟩
  have hC : C = C₀ := by
    calc
      C = componentOf s.1.continuation (s.2.1.baseArc C).val :=
        (s.2.1.baseArc C).property.symm
      _ = C₀ := (componentOf_eq_iff _ _ _).2
        (s.2.2.connected (s.2.1.baseArc C).val
          ⟨0,source_parent_nArc_pos x hx htrace⟩)
  rw [hC]
  exact positivePolygon_history_terminal_frame_via_general_whitney
    x hx he s htrace hterminal

/-- The same terminal identity with the existing source theorem's arbitrary
polygon size and arbitrary-component interface. -/
theorem positivePolygon_history_terminal_frame_all_sizes_via_general_whitney
    {m : ℕ} (q : Fin m → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (he : LeftExposed q ⟨0,by have := hq.size_ge_three; omega⟩)
    (t : MarkedParentState)
    (h : MarkedParentTrace
      (positivePolygonMarkedState q hq (initialAnchorTraversal q hq)) t)
    (hterminal : ∀ c : Fin t.1.nCrossing, ¬ badAt t.2.1 c)
    (C : diagramComponent t.1) :
    diagramWrithe t.1 + componentTurnInteger t.1 C = 1 := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, m = n+2 :=
    ⟨m-2, by have := hq.size_ge_three; omega⟩
  exact positivePolygon_history_terminal_frame_all_components_via_general_whitney
    q hq he t h hterminal C

/-- Same header as the historical terminal framed-value consumer; this
proof uses the all-basepoint Whitney route on the very same parent. -/
theorem positivePolygon_history_terminal_framed_value_via_general_whitney
    {m : ℕ} (q : Fin m → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (he : LeftExposed q ⟨0,by have := hq.size_ge_three; omega⟩)
    (t : MarkedParentState)
    (h : MarkedParentTrace
      (positivePolygonMarkedState q hq (initialAnchorTraversal q hq)) t)
    (hterminal : ∀ c : Fin t.1.nCrossing, ¬ badAt t.2.1 c)
    (C : diagramComponent t.1)
    (H : Evaluator) (hH : IsNormalizedDescendingSkeinEvaluator H) :
    framedKnotRow H t.1 (by exact Nat.zero_lt_of_lt (t.2.1.baseArc C).val.isLt) C =
      framedVariable := by
  have hframe := positivePolygon_history_terminal_frame_all_sizes_via_general_whitney
    q hq he t h hterminal C
  rw [framedKnotRow,hframe,
    normalizedEvaluator_connected_terminal_eq_one H hH t.1
      (by exact Nat.zero_lt_of_lt (t.2.1.baseArc C).val.isLt)
      t.2.1 t.2.2.connected hterminal,
    zRow_one_zero,mul_one]
  change aMonomial * (aMonomial - aInvMonomial) = aMonomial ^ 2 - 1
  rw [mul_sub,aMonomial_mul_aInvMonomial,pow_two]

theorem positivePolygon_history_canonical_terminal_framed_value_via_general_whitney
    {m : ℕ} (q : Fin m → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (he : LeftExposed q ⟨0,by have := hq.size_ge_three; omega⟩)
    (t : MarkedParentState)
    (h : MarkedParentTrace
      (positivePolygonMarkedState q hq (initialAnchorTraversal q hq)) t)
    (hterminal : ∀ c : Fin t.1.nCrossing, ¬ badAt t.2.1 c)
    (C : diagramComponent t.1) :
    framedKnotRow Gemini.candidateEvaluator t.1
      (by exact Nat.zero_lt_of_lt (t.2.1.baseArc C).val.isLt) C = framedVariable := by
  let ht : 0 < t.1.nArc := Nat.zero_lt_of_lt (t.2.1.baseArc C).val.isLt
  have hb : badCrossings t.2.1 = ∅ := by
    apply Finset.eq_empty_iff_forall_not_mem.mpr
    intro c hc
    exact hterminal c (Finset.mem_filter.mp hc).2
  have hvalue : Gemini.candidateEvaluator t.1 ht = 1 :=
    (DescendingSpatial.descending_actual_split_triangles_and_normalization
      t.1 ht t.2.1 hb).2.1
      (actual_connected_componentCount t.1 ht t.2.2.connected)
  have hframe := positivePolygon_history_terminal_frame_all_sizes_via_general_whitney
    q hq he t h hterminal C
  rw [framedKnotRow,hframe,hvalue,zRow_one_zero,mul_one]
  change aMonomial * (aMonomial - aInvMonomial) = aMonomial ^ 2 - 1
  rw [mul_sub,aMonomial_mul_aInvMonomial,pow_two]

end DirectGLSSW.HOMFLY






