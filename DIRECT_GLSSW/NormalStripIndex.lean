import ActualWhitneyGeneral
import Mathlib.Topology.Compactness.Compact

set_option autoImplicit false
noncomputable section
open DirectGLSSW Filter Topology
namespace DirectGLSSW.HOMFLY.PLWinding

/-- Literal affine basepoint with signed normal displacement. -/
def normalAtEdgeParameter {n : ℕ} (q : Fin n → ℂ) (i : Fin n)
    (τ ε : ℝ) : ℂ :=
  q i + (τ : ℂ) * (q (cyclicSuccessorPerm n i) - q i) +
    (ε : ℂ) * Complex.I * (q (cyclicSuccessorPerm n i) - q i)

theorem normalAtEdgeParameter_eq_literal {n : ℕ} (q : Fin n → ℂ) (i : Fin n)
    (τ ε : ℝ) : normalAtEdgeParameter q i τ ε =
      q i + (τ : ℂ) * (q (cyclicSuccessorPerm n i) - q i) +
        (ε : ℂ) * Complex.I * (q (cyclicSuccessorPerm n i) - q i) := rfl

theorem normalAtEdgeParameter_midpoint {n : ℕ} (q : Fin n → ℂ) (i : Fin n)
    (ε : ℝ) : normalAtEdgeParameter q i (1/2) ε = normalAtEdgeMidpoint q i ε := rfl

theorem normalAtEdgeParameter_not_on_base {n : ℕ} (q : Fin n → ℂ) (i : Fin n)
    (hdir : q (cyclicSuccessorPerm n i) - q i ≠ 0)
    (τ ε : ℝ) (hε : ε ≠ 0) : normalAtEdgeParameter q i τ ε ∉ edgeTrace q i := by
  intro hz
  obtain ⟨t,_,_,heq⟩ := (edgeTrace_iff_literal q i _).mp hz
  have hm : (ε : ℂ) * Complex.I * (q (cyclicSuccessorPerm n i)-q i) =
      ((t-τ : ℝ) : ℂ) * (q (cyclicSuccessorPerm n i)-q i) := by
    dsimp [normalAtEdgeParameter] at heq
    simp only [cyclicSuccessorPerm_apply] at *
    push_cast
    linear_combination heq
  have h := congrArg Complex.im (mul_right_cancel₀ hdir hm)
  simp at h
  exact hε h

/-- Compact actual base subsegments have one off-trace normal strip. -/
theorem exists_normal_strip {n : ℕ} (q : Fin n → ℂ) (i : Fin n) (a b : ℝ)
    (hdir : q (cyclicSuccessorPerm n i)-q i ≠ 0)
    (hregular : ∀ τ ∈ Set.Icc a b, ∀ j : Fin n, j ≠ i →
      normalAtEdgeParameter q i τ 0 ∉ edgeTrace q j) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, |ε| < δ → ε ≠ 0 →
      ∀ τ ∈ Set.Icc a b, AvoidsPolygonEdges q (normalAtEdgeParameter q i τ ε) := by
  classical
  have hp : ∀ τ ∈ Set.Icc a b, ∀ᶠ z : ℝ × ℝ in 𝓝 (0,τ),
      ∀ j : Fin n, j ≠ i → normalAtEdgeParameter q i z.2 z.1 ∉ edgeTrace q j := by
    intro τ hτ
    apply Filter.eventually_all.mpr
    intro j
    by_cases hj : j = i
    · filter_upwards [] with z hz
      exact (hz hj).elim
    · have hmem : ∀ᶠ w in 𝓝 (normalAtEdgeParameter q i τ 0), w ∉ edgeTrace q j :=
        (isClosed_edgeTrace q j).isOpen_compl.mem_nhds (hregular τ hτ j hj)
      have hc : ContinuousAt (fun z : ℝ × ℝ => normalAtEdgeParameter q i z.2 z.1)
          (0,τ) := by unfold normalAtEdgeParameter; fun_prop
      filter_upwards [hc.eventually hmem] with z hz _
      exact hz
  have hu : ∀ᶠ ε : ℝ in 𝓝 0, ∀ τ ∈ Set.Icc a b,
      ∀ j : Fin n, j ≠ i → normalAtEdgeParameter q i τ ε ∉ edgeTrace q j :=
    (isCompact_Icc : IsCompact (Set.Icc a b)).eventually_forall_of_forall_eventually hp
  obtain ⟨δ,hδ,hball⟩ := Metric.mem_nhds_iff.mp hu
  refine ⟨δ,hδ,?_⟩
  intro ε hεδ hε τ hτ j t ht0 ht1 heq
  have hz : normalAtEdgeParameter q i τ ε ∈ edgeTrace q j :=
    (edgeTrace_iff_literal q j _).mpr ⟨t,ht0,ht1,heq⟩
  by_cases hj : j = i
  · subst j
    exact normalAtEdgeParameter_not_on_base q i hdir τ ε hε hz
  · exact hball (by simpa [Metric.mem_ball,Real.dist_eq,abs_sub_comm] using hεδ) τ hτ j hj hz

/-- Winding is constant along each connected off-trace translated subsegment. -/
theorem windingIndex_eq_along_normal_strip {n : ℕ} (q : Fin n → ℂ) (i : Fin n)
    (a b ε τ σ : ℝ)
    (havoid : ∀ t ∈ Set.Icc a b, AvoidsPolygonEdges q (normalAtEdgeParameter q i t ε))
    (hτ : τ ∈ Set.Icc a b) (hσ : σ ∈ Set.Icc a b) :
    windingIndex q _ (havoid τ hτ) = windingIndex q _ (havoid σ hσ) := by
  classical
  let f : ℝ → ℤ := fun t => if h : AvoidsPolygonEdges q (normalAtEdgeParameter q i t ε)
    then windingIndex q _ h else 0
  have hf : ContinuousOn f (Set.Icc a b) := by
    intro t ht
    have hc : ContinuousAt (fun s : ℝ => normalAtEdgeParameter q i s ε) t := by
      unfold normalAtEdgeParameter; fun_prop
    have hA := hc.eventually (eventually_avoids_edges q _ (havoid t ht))
    have hI := hc.eventually (windingIndex_eventually_eq q _ (havoid t ht))
    have heq : f =ᶠ[𝓝 t] fun _ => f t := by
      filter_upwards [hA,hI] with s hs hi
      dsimp [f]
      rw [dif_pos hs,dif_pos (havoid t ht)]
      exact hi hs
    exact (ContinuousAt.congr_of_eventuallyEq continuousAt_const heq).continuousWithinAt
  have h := isPreconnected_Icc.constant hf hτ hσ
  simpa only [f,dif_pos (havoid τ hτ),dif_pos (havoid σ hσ)] using h

end DirectGLSSW.HOMFLY.PLWinding


