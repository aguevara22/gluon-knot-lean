import DirectGLSSW.FiniteCycleOrder

set_option autoImplicit false

namespace DirectGLSSW.MixedEdgeSupportOrder
open FiniteCycleOrder

/-- Two distinct points have exactly one order in either direction on a
strict cyclic arc anchored at a third distinct point. -/
theorem strictCyclicBetween_reverse_iff_not
    {m : ℕ} (a x y : Fin m) (hax : a ≠ x) (hay : a ≠ y) (hxy : x ≠ y) :
    strictCyclicBetween a y x ↔ ¬ strictCyclicBetween a x y := by
  have hax' : a.val ≠ x.val := fun h => hax (Fin.ext h)
  have hay' : a.val ≠ y.val := fun h => hay (Fin.ext h)
  have hxy' : x.val ≠ y.val := fun h => hxy (Fin.ext h)
  by_cases hAX : a.val < x.val <;>
    by_cases hAY : a.val < y.val <;>
    by_cases hXY : x.val < y.val <;>
    simp only [strictCyclicBetween, Fin.lt_def] <;> omega

/-- Once two points are known to follow an anchor in the linear order, their
anchored cyclic order is their ordinary linear order. -/
theorem strictCyclicBetween_lowerAnchor_iff_lt
    {m : ℕ} (a x y : Fin m) (hax : a < x) (hay : a < y) :
    strictCyclicBetween a x y ↔ x < y := by
  simp only [strictCyclicBetween, Fin.lt_def]
  change a.val < x.val at hax
  change a.val < y.val at hay
  omega

/-- Finite cyclic-order characterization of two chords whose endpoints lie in
opposite arcs cut by `A` and `B`. Endpoint labels may be independently flipped. -/
theorem fourEndpoint_nonAlternation_iff_reverseArcOrder
    {m : ℕ} (A B rC rD sC sD : Fin m)
    (hAB : A ≠ B) (hrr : rC ≠ rD) (hss : sC ≠ sD)
    (hrC : strictCyclicBetween A rC B)
    (hrD : strictCyclicBetween A rD B)
    (hsC : strictCyclicBetween B sC A)
    (hsD : strictCyclicBetween B sD A)
    (bc bd : Bool) :
    let c0 := if bc then sC else rC
    let c1 := if bc then rC else sC
    let d0 := if bd then sD else rD
    let d1 := if bd then rD else sD
    (strictCyclicBetween c0 d0 c1 ↔ strictCyclicBetween c0 d1 c1) ↔
      (strictCyclicBetween B sC sD ↔ strictCyclicBetween A rD rC) := by
  have hAB' : A.val ≠ B.val := fun h => hAB (Fin.ext h)
  have hrr' : rC.val ≠ rD.val := fun h => hrr (Fin.ext h)
  have hss' : sC.val ≠ sD.val := fun h => hss (Fin.ext h)
  have hRorder : rC.val < rD.val ∨ rD.val < rC.val := by omega
  have hSorder : sC.val < sD.val ∨ sD.val < sC.val := by omega
  cases bc <;> cases bd <;> dsimp
  all_goals
    by_cases hABlt : A.val < B.val
    · have hrC' : A.val < rC.val ∧ rC.val < B.val := by
        simp only [strictCyclicBetween, Fin.lt_def] at hrC
        rcases hrC with h | h | h
        · exact h
        · omega
        · omega
      have hrD' : A.val < rD.val ∧ rD.val < B.val := by
        simp only [strictCyclicBetween, Fin.lt_def] at hrD
        rcases hrD with h | h | h
        · exact h
        · omega
        · omega
      have hsC' : sC.val < A.val ∨ B.val < sC.val := by
        simp only [strictCyclicBetween, Fin.lt_def] at hsC
        rcases hsC with h | h | h
        · omega
        · exact Or.inl h.1
        · exact Or.inr h.2
      have hsD' : sD.val < A.val ∨ B.val < sD.val := by
        simp only [strictCyclicBetween, Fin.lt_def] at hsD
        rcases hsD with h | h | h
        · omega
        · exact Or.inl h.1
        · exact Or.inr h.2
      rcases hsC' with hsClo | hsChi <;>
      rcases hsD' with hsDlo | hsDhi <;>
      rcases hRorder with hRC | hCR <;>
      rcases hSorder with hSD | hDS <;>
      simp only [Bool.false_eq_true, if_false, if_true,
        strictCyclicBetween, Fin.lt_def] at * <;> omega
    · have hBAlt : B.val < A.val := by omega
      have hrC' : rC.val < B.val ∨ A.val < rC.val := by
        simp only [strictCyclicBetween, Fin.lt_def] at hrC
        rcases hrC with h | h | h
        · omega
        · exact Or.inl h.1
        · exact Or.inr h.2
      have hrD' : rD.val < B.val ∨ A.val < rD.val := by
        simp only [strictCyclicBetween, Fin.lt_def] at hrD
        rcases hrD with h | h | h
        · omega
        · exact Or.inl h.1
        · exact Or.inr h.2
      have hsC' : B.val < sC.val ∧ sC.val < A.val := by
        simp only [strictCyclicBetween, Fin.lt_def] at hsC
        rcases hsC with h | h | h
        · exact h
        · omega
        · omega
      have hsD' : B.val < sD.val ∧ sD.val < A.val := by
        simp only [strictCyclicBetween, Fin.lt_def] at hsD
        rcases hsD with h | h | h
        · exact h
        · omega
        · omega
      rcases hrC' with hrClo | hrChi <;>
      rcases hrD' with hrDlo | hrDhi <;>
      rcases hRorder with hRC | hCR <;>
      rcases hSorder with hSD | hDS <;>
      simp only [Bool.false_eq_true, if_false, if_true,
        strictCyclicBetween, Fin.lt_def] at * <;> omega

end DirectGLSSW.MixedEdgeSupportOrder


