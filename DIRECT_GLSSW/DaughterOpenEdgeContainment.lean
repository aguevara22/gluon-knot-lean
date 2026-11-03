import DirectGLSSW.DaughterCarrier
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.DaughterG2Inheritance
open DirectGLSSW DaughterFirstReturn PolygonNonalternation
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Exact affine parameter of a positive subsegment, including endpoint cases. -/
theorem affinePoint_subsegment (u v a b : PlanarPoint K) (s d t : K)
    (ha : a = affinePoint u v s) (hab : b - a = d • (v - u)) :
    affinePoint a b t = affinePoint u v (s + t * d) := by
  have hx := congrArg Prod.fst hab
  have hy := congrArg Prod.snd hab
  change b.1 - a.1 = d * (v.1 - u.1) at hx
  change b.2 - a.2 = d * (v.2 - u.2) at hy
  subst a
  apply Prod.ext
  · simp only [affinePoint, Prod.fst] at hx ⊢
    rw [hx]
    ring
  · simp only [affinePoint, Prod.snd] at hy ⊢
    rw [hy]
    ring

 theorem terminalParameterOn_le_one {n : ℕ}
    (q : Fin n → PlanarPoint K) (e : Fin n) (w : PolygonEvent q) :
    terminalParameterOn q e w ≤ 1 := by
  classical
  unfold terminalParameterOn
  split_ifs
  · exact (polygonEventParameter_bounds q w).2.le
  · exact le_rfl

/-- Every actual daughter open side is contained in its labelled parent open edge. -/
theorem daughter_edgeInterior_subset_parent {n : ℕ}
    (q : Fin n → PlanarPoint K) (hG2 : cyclicNoTripleIntersections q)
    (S : Finset (PolygonCrossing q)) (hn : 3 ≤ n)
    (root : PolygonEvent q) (hroot : retainedCorner q S root)
    (i : Fin (Fintype.card (CornerCoord q hG2 S root))) (z : PlanarPoint K)
    (hz : edgeInterior (daughterVertex q hG2 S root) i z) :
    edgeInterior q (daughterCarrier q hG2 S root i) z := by
  classical
  let c := cornerEnumeration q hG2 S root i
  let x := orbitEventAt q hG2 S root c.val
  let e := daughterCarrier q hG2 S root i
  let s := polygonEventParameter q x
  let d := daughterSideScale q hG2 S root c
  have hs : 0 ≤ s := (polygonEventParameter_bounds q x).1
  obtain ⟨hd, hside⟩ := daughterSide_positive_multiple q hG2 S hn root hroot i
  change 0 < d at hd
  have hterminal : s + d ≤ 1 := by
    have ht := terminalParameterOn_le_one q e
      (terminalEvent q hG2 (lastDartStart q hG2 S root c))
    dsimp [d, s, daughterSideScale, e, daughterCarrier, x, c] at ht ⊢
    linarith
  have hstart : daughterVertex q hG2 S root i =
      affinePoint (q e) (q (cyclicSuccessor e)) s := by
    exact polygonEventPoint_eq_affine q x
  have hstep : daughterVertex q hG2 S root (cyclicSuccessor i) -
      daughterVertex q hG2 S root i =
      d • (q (cyclicSuccessor e) - q e) := by
    exact hside
  obtain ⟨t, ht0, ht1, hzt⟩ := hz
  refine ⟨s + t * d, ?_, ?_, ?_⟩
  · exact add_pos_of_nonneg_of_pos hs (mul_pos ht0 hd)
  · have htd : t * d < d := by nlinarith
    linarith
  · rw [hzt]
    exact affinePoint_subsegment _ _ _ _ s d t hstart hstep

/-- Nonalternation makes distinct daughter sides have distinct parent carriers. -/
theorem daughter_cyclicNoTripleIntersections_retained {n : ℕ}
    (q : Fin n → PlanarPoint K) (hG2 : cyclicNoTripleIntersections q)
    (S : Finset (PolygonCrossing q)) (hn : 3 ≤ n)
    (hNA : polygonNonalternating q hG2 S)
    (root : PolygonEvent q) (hroot : retainedCorner q S root) :
    cyclicNoTripleIntersections (daughterVertex q hG2 S root) := by
  intro i j k z hij hjk hik hz
  have hcarrier := daughterCarrier_injective q hG2 S hn hNA root
  apply hG2 (daughterCarrier q hG2 S root i) (daughterCarrier q hG2 S root j)
    (daughterCarrier q hG2 S root k) z
    (fun h => hij (hcarrier h)) (fun h => hjk (hcarrier h))
    (fun h => hik (hcarrier h))
  exact ⟨daughter_edgeInterior_subset_parent q hG2 S hn root hroot i z hz.1,
    daughter_edgeInterior_subset_parent q hG2 S hn root hroot j z hz.2.1,
    daughter_edgeInterior_subset_parent q hG2 S hn root hroot k z hz.2.2⟩





end DirectGLSSW.DaughterG2Inheritance
