import ChamberContract.Contract
import Gemini.Solution

set_option autoImplicit false

namespace DirectGLSSW.GeminiChamber

open DirectGLSSW
open DirectGLSSW.HOMFLY
open DirectGLSSW.HOMFLY.Coefficients
open Filter Topology

noncomputable section

theorem signedDiagramIso_invariant_of_isNormalized
    (H : (D : PLLinkDiagram) → 0 < D.nArc → HOMFLYCoeff)
    (hH : IsNormalizedDescendingSkeinEvaluator H) :
    ∀ (D E : PLLinkDiagram) (hD : 0 < D.nArc) (hE : 0 < E.nArc),
      SignedDiagramIso D E → H D hD = H E hE := by
  obtain ⟨H₀, _, huniq, _, hiso, _⟩ :=
    DirectGLSSW.HOMFLY.Gemini.normalizedEvaluator_package
  have hEq : H = H₀ := huniq H hH
  subst hEq
  exact hiso

theorem stateSum_proof_irrel {n : ℕ}
    (H : (D : PLLinkDiagram) → 0 < D.nArc → HOMFLYCoeff)
    (q : Fin n → Plane) (hq₁ hq₂ : CyclicGeneric q) :
    stateSum H q hq₁ = stateSum H q hq₂ :=
  rfl

theorem eventually_stateSum_eq {n : ℕ}
    (H : (D : PLLinkDiagram) → 0 < D.nArc → HOMFLYCoeff)
    (hH : IsNormalizedDescendingSkeinEvaluator H)
    (q : Fin n → Plane) (hq : CyclicGeneric q) :
    ∀ᶠ q' in 𝓝 q, ∀ hq' : CyclicGeneric q',
      stateSum H q' hq' = stateSum H q hq := by
  have hloc := CornerStateSumLocality.eventually_cornerStateSum_eq H
    (signedDiagramIso_invariant_of_isNormalized H hH) q hq
  filter_upwards [hloc] with q' hq'
  rcases hq' with ⟨hq'₀, heq⟩
  intro hq'₁
  exact heq

theorem stateSum_eq_of_isPreconnected {n : ℕ}
    (H : (D : PLLinkDiagram) → 0 < D.nArc → HOMFLYCoeff)
    (hH : IsNormalizedDescendingSkeinEvaluator H)
    {S : Set (Fin n → Plane)} (hS : IsPreconnected S)
    (hgen : S ⊆ genericLocus n)
    {q r : Fin n → Plane} (hqS : q ∈ S) (hrS : r ∈ S)
    (hq : CyclicGeneric q) (hr : CyclicGeneric r) :
    stateSum H q hq = stateSum H r hr := by
  let U : Set (Fin n → Plane) :=
    interior {x | ∀ hx : CyclicGeneric x, stateSum H x hx = stateSum H q hq}
  let V : Set (Fin n → Plane) :=
    interior {x | ∀ hx : CyclicGeneric x, stateSum H x hx ≠ stateSum H q hq}
  have hSUV : S ⊆ U ∪ V := by
    intro x hxS
    have hx : CyclicGeneric x := hgen hxS
    have hev := eventually_stateSum_eq H hH x hx
    by_cases hxq : stateSum H x hx = stateSum H q hq
    · left
      rw [mem_interior_iff_mem_nhds]
      filter_upwards [hev] with y hy hy_gen
      exact (hy hy_gen).trans hxq
    · right
      rw [mem_interior_iff_mem_nhds]
      filter_upwards [hev] with y hy hy_gen
      rw [hy hy_gen]
      exact hxq
  have hqU : q ∈ U := by
    rw [mem_interior_iff_mem_nhds]
    exact eventually_stateSum_eq H hH q hq
  by_contra hne
  have hrV : r ∈ V := by
    rw [mem_interior_iff_mem_nhds]
    filter_upwards [eventually_stateSum_eq H hH r hr] with y hy hy_gen
    rw [hy hy_gen]
    exact Ne.symm hne
  obtain ⟨z, hzS, hzU, hzV⟩ :=
    hS U V isOpen_interior isOpen_interior hSUV ⟨q, hqS, hqU⟩ ⟨r, hrS, hrV⟩
  have hz : CyclicGeneric z := hgen hzS
  exact (interior_subset hzV hz) (interior_subset hzU hz)

instance time_preconnectedSpace : PreconnectedSpace Time :=
  Subtype.preconnectedSpace isPreconnected_Icc

theorem normalized_state_sum_path
    (H : (D : PLLinkDiagram) → 0 < D.nArc → HOMFLYCoeff)
    {n : ℕ}
    (p : Time → Fin n → Plane)
    (hH : IsNormalizedDescendingSkeinEvaluator H)
    (hp : Continuous p)
    (hg : ∀ t : Time, CyclicGeneric (p t))
    (h₀ : CyclicGeneric (p start))
    (h₁ : CyclicGeneric (p finish)) :
    stateSum H (p start) h₀ = stateSum H (p finish) h₁ := by
  apply stateSum_eq_of_isPreconnected H hH (isPreconnected_range hp)
  · rintro _ ⟨t, rfl⟩
    exact hg t
  · exact ⟨start, rfl⟩
  · exact ⟨finish, rfl⟩

theorem state_sum_path_constancy :
    ∃ H : (D : PLLinkDiagram) → 0 < D.nArc → HOMFLYCoeff,
      IsNormalizedDescendingSkeinEvaluator H ∧
      (∀ (K : (D : PLLinkDiagram) → 0 < D.nArc → HOMFLYCoeff),
        IsNormalizedDescendingSkeinEvaluator K → K = H) ∧
      ∀ {n : ℕ}
        (p : Time → Fin n → Plane),
        Continuous p →
        (∀ t : Time, CyclicGeneric (p t)) →
        ∀ (h₀ : CyclicGeneric (p start)) (h₁ : CyclicGeneric (p finish)),
        stateSum H (p start) h₀ = stateSum H (p finish) h₁ := by
  obtain ⟨H, hH, huniq⟩ := DirectGLSSW.HOMFLY.Gemini.normalizedEvaluator_existsUnique
  refine ⟨H, hH, huniq, ?_⟩
  intro n p hp hg h₀ h₁
  exact normalized_state_sum_path H p hH hp hg h₀ h₁

theorem state_sum_chamber_constancy :
    ∃ H : (D : PLLinkDiagram) → 0 < D.nArc → HOMFLYCoeff,
      IsNormalizedDescendingSkeinEvaluator H ∧
      (∀ (K : (D : PLLinkDiagram) → 0 < D.nArc → HOMFLYCoeff),
        IsNormalizedDescendingSkeinEvaluator K → K = H) ∧
      ∀ {n : ℕ}
        (q r : Fin n → Plane)
        (hq : CyclicGeneric q)
        (hr : CyclicGeneric r),
        r ∈ connectedComponentIn (genericLocus n) q →
        stateSum H q hq = stateSum H r hr := by
  obtain ⟨H, hH, huniq⟩ := DirectGLSSW.HOMFLY.Gemini.normalizedEvaluator_existsUnique
  refine ⟨H, hH, huniq, ?_⟩
  intro n q r hq hr hcomp
  exact stateSum_eq_of_isPreconnected H hH
    isPreconnected_connectedComponentIn
    (connectedComponentIn_subset (genericLocus n) q)
    (mem_connectedComponentIn hq)
    hcomp
    hq hr

end

end DirectGLSSW.GeminiChamber
