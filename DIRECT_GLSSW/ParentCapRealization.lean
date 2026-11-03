import OriginalOuterProperness

set_option autoImplicit false
namespace DirectGLSSW.ParentCapRealization
open ExtendedReturnArcGeometry GeometricSecantRegularity
open OriginalSecantProperness OriginalOuterProperness
noncomputable section

/-- Disjoint original six-label conditions imply the exact interior family
used by the established extension construction. -/
theorem interior_of_original_secants {n : ℕ} (hn : 3 ≤ n)
    (P : Fin n → PlanarPoint ℝ)
    (hU : (P (zeroIndex hn)).2=0) (hV : (P (lastIndex hn)).2=0)
    (h6 : ∀ l : Fin 6 → Fin n, Function.Injective l → secantNumerator (P ∘ l) ≠ 0) :
    InteriorSecantsSeparated hn P := by
  intro a b c d ha ha' hb hb' hc hc' hd hd' hab hcd hac had hbc hbd hs ht
  let l : Fin 6 → Fin n := ![zeroIndex hn, lastIndex hn, a, b, c, d]
  have hi : Function.Injective l := by
    intro i j hij
    simp only [ne_eq, Fin.ext_iff] at hac had hbc hbd
    fin_cases i <;> fin_cases j <;> dsimp [l] at hij ⊢ <;> try rfl
    all_goals
      have hv := congrArg Fin.val hij
      try dsimp [zeroIndex, lastIndex] at hv
      omega
  have hh := h6 l hi
  have hscale : secantNumerator (P ∘ l) =
      ((P (lastIndex hn)).1-(P (zeroIndex hn)).1) *
        secantCross (P (zeroIndex hn)) (P a) (P b) (P c) (P d) := by
    dsimp [secantNumerator, Function.comp_def, l, secantCross, planarDet]
    rw [hU, hV]
    ring
  have hnz : secantCross (P (zeroIndex hn)) (P a) (P b) (P c) (P d) ≠ 0 := by
    intro hz
    rw [hscale, hz, mul_zero] at hh
    exact hh rfl
  intro he
  apply hnz
  have he' := (div_eq_div_iff hs ht).mp he
  unfold secantCross
  nlinarith

/-- The four-label family supplies the only extra outer condition; triangles
need no extra exclusion because their two neighboring labels coincide. -/
theorem outer_of_original_directions {n : ℕ} (hn : 3 ≤ n)
    (P : Fin n → PlanarPoint ℝ)
    (h4 : ∀ l : Fin 4 → Fin n, Function.Injective l → outerNumerator (P ∘ l) ≠ 0) :
    OuterSecantRegular hn P := by
  by_cases he : n=3
  · subst n
    exact Or.inl rfl
  · apply Or.inr
    let l : Fin 4 → Fin n := ![firstIndex hn, zeroIndex hn, penultimateIndex hn, lastIndex hn]
    have hi : Function.Injective l := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> dsimp [l] at hij ⊢ <;> try rfl
      all_goals
        have hv := congrArg Fin.val hij
        dsimp [firstIndex, zeroIndex, penultimateIndex, lastIndex] at hv
        omega
    exact h4 l hi

/-- No injectivity or cap genericity is assumed: both are produced on the
explicit, separately proved dense original-parent exclusion locus. -/
theorem exists_extension_and_punctured_caps {n : ℕ} (hn : 3 ≤ n)
    (P : Fin n → PlanarPoint ℝ) (hP : CyclicGeneric P)
    (hU : (P (zeroIndex hn)).2=0) (hV : (P (lastIndex hn)).2=0)
    (hleft : (P (zeroIndex hn)).1 < (P (lastIndex hn)).1)
    (h6 : ∀ l : Fin 6 → Fin n, Function.Injective l → secantNumerator (P ∘ l) ≠ 0)
    (h4 : ∀ l : Fin 4 → Fin n, Function.Injective l → outerNumerator (P ∘ l) ≠ 0) :
    ∃ ε : ℝ, 0 < ε ∧ ε < geometricRadius hn P ∧
      Set.InjOn (CapCriticalEventGeometry.criticalRoot (extendedArc hn P ε))
        ↑(CapCriticalTimes.criticalPairs (extendedArc hn P ε) n) ∧
      ∀ t : ℝ, ∃ δ : ℝ, 0 < δ ∧ ∀ s : ℝ, 0 < |s| → |s| < δ →
        ∀ a b : Fin n, a.val < b.val →
          CyclicGeneric (GlobalCapEntry.lineCapCore
            (CapCrossingEvent.horizontalMove (extendedArc hn P ε) (t+s)) a b) := by
  obtain ⟨ε,hε,hbound,hroots⟩ := exists_extendedArc_injective_of_geometric hn P hP.g1
    hU hV hleft (interior_of_original_secants hn P hU hV h6)
      (outer_of_original_directions hn P h4)
  exact ⟨ε,hε,hbound,hroots,extendedArc_localCaps hn P hP hU hV ε hε hbound⟩




end
end DirectGLSSW.ParentCapRealization
