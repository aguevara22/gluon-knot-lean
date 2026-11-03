import TwoSidedBaseEdge
import Mathlib.Topology.Connected.TotallyDisconnected

set_option autoImplicit false
noncomputable section
open DirectGLSSW Filter Topology
attribute [local instance] Classical.propDecidable

namespace DirectGLSSW.HOMFLY.PLWinding

/-- Integer index when the normal test point is off the literal finite trace;
the default value is used only to make a total function for a continuity
argument. All geometric conclusions below restrict to the off-trace locus. -/
def normalIndexOrZero {n : ℕ} (q : Fin n → ℂ) (i : Fin n) (ε : ℝ) : ℤ :=
  if h : AvoidsPolygonEdges q (normalAtEdgeMidpoint q i ε) then
    windingIndex q (normalAtEdgeMidpoint q i ε) h else 0

theorem normalIndexOrZero_eq_windingIndex {n : ℕ} (q : Fin n → ℂ)
    (i : Fin n) (ε : ℝ)
    (h : AvoidsPolygonEdges q (normalAtEdgeMidpoint q i ε)) :
    normalIndexOrZero q i ε =
      windingIndex q (normalAtEdgeMidpoint q i ε) h := by
  simp [normalIndexOrZero, h]

theorem normalIndexOrZero_continuousAt {n : ℕ} (q : Fin n → ℂ)
    (i : Fin n) (ε : ℝ)
    (h : AvoidsPolygonEdges q (normalAtEdgeMidpoint q i ε)) :
    ContinuousAt (normalIndexOrZero q i) ε := by
  have hn : ContinuousAt (normalAtEdgeMidpoint q i) ε := by
    unfold normalAtEdgeMidpoint
    fun_prop
  have hAvoid := hn.eventually (eventually_avoids_edges q _ h)
  have hIndex := hn.eventually (windingIndex_eventually_eq q _ h)
  have hevent : normalIndexOrZero q i =ᶠ[𝓝 ε]
      fun _ => normalIndexOrZero q i ε := by
    filter_upwards [hAvoid, hIndex] with η hη hidx
    rw [normalIndexOrZero_eq_windingIndex q i η hη,
      normalIndexOrZero_eq_windingIndex q i ε h]
    exact hidx hη
  exact ContinuousAt.congr_of_eventuallyEq continuousAt_const hevent

/-- Every connected normal interval avoiding the trace has one integer
index, independently of which test point is chosen within it. -/
theorem normalIndexOrZero_eq_on_Ioo {n : ℕ} (q : Fin n → ℂ)
    (i : Fin n) (a b ε η : ℝ)
    (havoid : ∀ t ∈ Set.Ioo a b,
      AvoidsPolygonEdges q (normalAtEdgeMidpoint q i t))
    (hε : ε ∈ Set.Ioo a b) (hη : η ∈ Set.Ioo a b) :
    normalIndexOrZero q i ε = normalIndexOrZero q i η := by
  have hcont : ContinuousOn (normalIndexOrZero q i) (Set.Ioo a b) := by
    intro t ht
    exact (normalIndexOrZero_continuousAt q i t (havoid t ht)).continuousWithinAt
  exact isPreconnected_Ioo.constant hcont hε hη

/-- Canonical integer values on the two actual local sides of the selected
base edge. Their definitions come from the literal off-trace winding sum;
the proof shows independence of the chosen test point in each side. -/
theorem exists_actual_base_side_indices {D : PLLinkDiagram}
    (T : BasedTraversal D) (C : diagramComponent D) :
    let e := (T.baseArc C).val
    let m := componentArcLength D e
    let q := actualComponentWord T C
    let i₀ : Fin m := ⟨0, componentArcLength_pos D e⟩
    ∃ δ : ℝ, 0 < δ ∧ ∃ kpos kneg : ℤ,
      (∀ ε ∈ Set.Ioo (0 : ℝ) δ,
        ∃ h : AvoidsPolygonEdges q (normalAtEdgeMidpoint q i₀ ε),
          windingIndex q (normalAtEdgeMidpoint q i₀ ε) h = kpos) ∧
      (∀ ε ∈ Set.Ioo (-δ) (0 : ℝ),
        ∃ h : AvoidsPolygonEdges q (normalAtEdgeMidpoint q i₀ ε),
          windingIndex q (normalAtEdgeMidpoint q i₀ ε) h = kneg) := by
  intro e m q i₀
  obtain ⟨δ, hδ, hrad⟩ := actualComponentWord_normal_radius T C
  let ρ : ℝ := δ / 2
  have hρ : ρ ∈ Set.Ioo (0 : ℝ) δ := by
    dsimp [ρ]
    constructor <;> linarith
  have hρneg : -ρ ∈ Set.Ioo (-δ) (0 : ℝ) := by
    dsimp [ρ]
    constructor <;> linarith
  have hpos (ε : ℝ) (hε : ε ∈ Set.Ioo (0 : ℝ) δ) :
      AvoidsPolygonEdges q (normalAtEdgeMidpoint q i₀ ε) := by
    apply hrad ε
    · simpa only [abs_of_pos hε.1] using hε.2
    · exact ne_of_gt hε.1
  have hneg (ε : ℝ) (hε : ε ∈ Set.Ioo (-δ) (0 : ℝ)) :
      AvoidsPolygonEdges q (normalAtEdgeMidpoint q i₀ ε) := by
    apply hrad ε
    · rw [abs_of_neg hε.2]
      linarith [hε.1]
    · exact ne_of_lt hε.2
  refine ⟨δ, hδ, normalIndexOrZero q i₀ ρ,
    normalIndexOrZero q i₀ (-ρ), ?_, ?_⟩
  · intro ε hε
    refine ⟨hpos ε hε, ?_⟩
    rw [← normalIndexOrZero_eq_windingIndex q i₀ ε (hpos ε hε)]
    exact normalIndexOrZero_eq_on_Ioo q i₀ 0 δ ε ρ hpos hε hρ
  · intro ε hε
    refine ⟨hneg ε hε, ?_⟩
    rw [← normalIndexOrZero_eq_windingIndex q i₀ ε (hneg ε hε)]
    exact normalIndexOrZero_eq_on_Ioo q i₀ (-δ) 0 ε (-ρ) hneg hε hρneg

/-- A pair records the two literal winding values on some punctured normal
radius. This is a specification, not an alternate winding definition. -/
def BaseSideIndexSpec {n : ℕ} (q : Fin n → ℂ) (i : Fin n)
    (δ : ℝ) (kpos kneg : ℤ) : Prop :=
  (∀ ε ∈ Set.Ioo (0 : ℝ) δ,
    ∃ h : AvoidsPolygonEdges q (normalAtEdgeMidpoint q i ε),
      windingIndex q (normalAtEdgeMidpoint q i ε) h = kpos) ∧
  (∀ ε ∈ Set.Ioo (-δ) (0 : ℝ),
    ∃ h : AvoidsPolygonEdges q (normalAtEdgeMidpoint q i ε),
      windingIndex q (normalAtEdgeMidpoint q i ε) h = kneg)

theorem baseSideIndexSpec_iff_literal {n : ℕ} (q : Fin n → ℂ)
    (i : Fin n) (δ : ℝ) (kpos kneg : ℤ) :
    BaseSideIndexSpec q i δ kpos kneg ↔
      (∀ ε ∈ Set.Ioo (0 : ℝ) δ,
        ∃ h : AvoidsPolygonEdges q (normalAtEdgeMidpoint q i ε),
          windingIndex q (normalAtEdgeMidpoint q i ε) h = kpos) ∧
      (∀ ε ∈ Set.Ioo (-δ) (0 : ℝ),
        ∃ h : AvoidsPolygonEdges q (normalAtEdgeMidpoint q i ε),
          windingIndex q (normalAtEdgeMidpoint q i ε) h = kneg) := Iff.rfl

theorem baseSideIndexSpec_unique {n : ℕ} (q : Fin n → ℂ) (i : Fin n)
    (δ₁ δ₂ : ℝ) (hδ₁ : 0 < δ₁) (hδ₂ : 0 < δ₂)
    (kpos₁ kneg₁ kpos₂ kneg₂ : ℤ)
    (h₁ : BaseSideIndexSpec q i δ₁ kpos₁ kneg₁)
    (h₂ : BaseSideIndexSpec q i δ₂ kpos₂ kneg₂) :
    kpos₁ = kpos₂ ∧ kneg₁ = kneg₂ := by
  let ρ : ℝ := min δ₁ δ₂ / 2
  have hρ : 0 < ρ ∧ ρ < δ₁ ∧ ρ < δ₂ := by
    dsimp [ρ]
    have hmin : 0 < min δ₁ δ₂ := lt_min hδ₁ hδ₂
    have hle₁ := min_le_left δ₁ δ₂
    have hle₂ := min_le_right δ₁ δ₂
    refine ⟨?_, ?_, ?_⟩ <;> linarith
  have hρneg : -ρ ∈ Set.Ioo (-δ₁) (0 : ℝ) ∧
      -ρ ∈ Set.Ioo (-δ₂) (0 : ℝ) := by
    constructor <;> constructor <;> linarith [hρ.1, hρ.2.1, hρ.2.2]
  obtain ⟨hp₁, hkp₁⟩ := h₁.1 ρ ⟨hρ.1, hρ.2.1⟩
  obtain ⟨hp₂, hkp₂⟩ := h₂.1 ρ ⟨hρ.1, hρ.2.2⟩
  obtain ⟨hn₁, hkn₁⟩ := h₁.2 (-ρ) hρneg.1
  obtain ⟨hn₂, hkn₂⟩ := h₂.2 (-ρ) hρneg.2
  constructor
  · exact hkp₁.symm.trans ((Subsingleton.elim hp₁ hp₂) ▸ hkp₂)
  · exact hkn₁.symm.trans ((Subsingleton.elim hn₁ hn₂) ▸ hkn₂)

/-- The actual base component has a unique ordered pair of local side
indices, completely characterized by the finite off-trace angle sum. -/
theorem existsUnique_actual_base_side_index_pair {D : PLLinkDiagram}
    (T : BasedTraversal D) (C : diagramComponent D) :
    let e := (T.baseArc C).val
    let m := componentArcLength D e
    let q := actualComponentWord T C
    let i₀ : Fin m := ⟨0, componentArcLength_pos D e⟩
    ∃! k : ℤ × ℤ, ∃ δ : ℝ, 0 < δ ∧
      BaseSideIndexSpec q i₀ δ k.1 k.2 := by
  intro e m q i₀
  obtain ⟨δ, hδ, kpos, kneg, hpos, hneg⟩ := exists_actual_base_side_indices T C
  refine ⟨(kpos,kneg), ⟨δ,hδ,⟨hpos,hneg⟩⟩, ?_⟩
  intro k hk
  obtain ⟨δ', hδ', hspec'⟩ := hk
  obtain ⟨hkp,hkn⟩ := baseSideIndexSpec_unique q i₀ δ' δ hδ' hδ
    k.1 k.2 kpos kneg hspec' ⟨hpos,hneg⟩
  exact Prod.ext hkp hkn

/-- The canonical actual component pair of positive- and negative-normal
region indices at its selected base arc. -/
def actualBaseSideIndexPair {D : PLLinkDiagram}
    (T : BasedTraversal D) (C : diagramComponent D) : ℤ × ℤ :=
  Classical.choose (existsUnique_actual_base_side_index_pair T C)

theorem actualBaseSideIndexPair_characterization {D : PLLinkDiagram}
    (T : BasedTraversal D) (C : diagramComponent D) :
    let e := (T.baseArc C).val
    let m := componentArcLength D e
    let q := actualComponentWord T C
    let i₀ : Fin m := ⟨0, componentArcLength_pos D e⟩
    (∃ δ : ℝ, 0 < δ ∧ BaseSideIndexSpec q i₀ δ
      (actualBaseSideIndexPair T C).1 (actualBaseSideIndexPair T C).2) ∧
    (∀ pair : ℤ × ℤ,
      (∃ δ : ℝ, 0 < δ ∧ BaseSideIndexSpec q i₀ δ pair.1 pair.2) →
      pair = actualBaseSideIndexPair T C) :=
  Classical.choose_spec (existsUnique_actual_base_side_index_pair T C)

end DirectGLSSW.HOMFLY.PLWinding





