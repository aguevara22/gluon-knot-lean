import DirectGLSSW.DaughterFirstReturn

set_option autoImplicit false

namespace DirectGLSSW.MixedEdgeFirstReturn

open Equiv DaughterFirstReturn FiniteFirstReturn

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {n : ℕ}

theorem smoothing_pow_eq_original_before_corner
    (q : Fin n → PlanarPoint K) (hq : cyclicNoTripleIntersections q)
    (S : Finset (PolygonCrossing q)) (x : PolygonEvent q) (d : ℕ)
    (hno : ∀ k : ℕ, 0 < k → k < d →
      ¬ retainedCorner q S ((polygonEventSuccessor q hq ^ k) x))
    {k : ℕ} (hk : k < d) :
    (smoothingDartPermutation q hq S ^ k) x =
      (polygonEventSuccessor q hq ^ k) x := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [pow_succ', Perm.mul_apply, ih (by omega)]
      rw [smoothingDartPermutation_apply]
      have hstep : polygonEventSuccessor q hq
          ((polygonEventSuccessor q hq ^ k) x) =
            (polygonEventSuccessor q hq ^ (k + 1)) x := by
        rw [pow_succ', Perm.mul_apply]
      rw [hstep]
      exact pairing_fixes_noncorner q S _ (hno (k + 1) (by omega) hk)


theorem smoothing_pow_at_original_corner
    (q : Fin n → PlanarPoint K) (hq : cyclicNoTripleIntersections q)
    (S : Finset (PolygonCrossing q)) (x : PolygonEvent q) (d : ℕ)
    (hd : 0 < d)
    (hno : ∀ k : ℕ, 0 < k → k < d →
      ¬ retainedCorner q S ((polygonEventSuccessor q hq ^ k) x)) :
    (smoothingDartPermutation q hq S ^ d) x =
      smoothingPairing q S ((polygonEventSuccessor q hq ^ d) x) := by
  have hdm : d - 1 < d := by omega
  have heq : d = (d - 1) + 1 := by omega
  conv_lhs => rw [heq, pow_succ', Perm.mul_apply]
  rw [smoothing_pow_eq_original_before_corner q hq S x d hno hdm]
  rw [smoothingDartPermutation_apply]
  conv_rhs => rw [heq, pow_succ', Perm.mul_apply]


theorem cornerSuccessor_eq_pairing_of_original_firstReturn
    (q : Fin n → PlanarPoint K) (hq : cyclicNoTripleIntersections q)
    (S : Finset (PolygonCrossing q)) (root : PolygonEvent q)
    (c : CornerCoord q hq S root) (d : ℕ) (hd : 0 < d)
    (hterminal : retainedCorner q S
      ((polygonEventSuccessor q hq ^ d) (orbitEventAt q hq S root c.val)))
    (hno : ∀ k : ℕ, 0 < k → k < d →
      ¬ retainedCorner q S
        ((polygonEventSuccessor q hq ^ k) (orbitEventAt q hq S root c.val))) :
    orbitEventAt q hq S root (cornerSuccessor q hq S root c).val =
      smoothingPairing q S
        ((polygonEventSuccessor q hq ^ d) (orbitEventAt q hq S root c.val)) := by
  classical
  let next := cornerSuccessor q hq S root c
  let start := orbitEventAt q hq S root c.val
  let N := orbitCard q hq S root
  let P : Fin N → Prop := fun i => retainedCorner q S (orbitEventAt q hq S root i)
  let d₀ := forwardGap c.val next.val
  have hfr : 0 < d₀ ∧ d₀ ≤ N ∧
      (cyclicSuccessorPerm N ^ d₀) c.val = next.val ∧
      ∀ k : ℕ, 0 < k → k < d₀ → ¬ P ((cyclicSuccessorPerm N ^ k) c.val) := by
    simpa [d₀, next, N, P, cornerSuccessor] using orderedSubtype_firstReturn P c
  rcases hfr with ⟨hpos₀, _, hreach₀, hno₀⟩
  have hactual₀ : (smoothingDartPermutation q hq S ^ d₀) start =
      orbitEventAt q hq S root next.val := by
    have hi := orbitEventAt_iterate q hq S root c.val d₀
    rw [hreach₀] at hi
    exact hi.symm
  have hactual : (smoothingDartPermutation q hq S ^ d) start =
      smoothingPairing q S ((polygonEventSuccessor q hq ^ d) start) :=
    smoothing_pow_at_original_corner q hq S start d hd hno
  have hret : retainedCorner q S ((smoothingDartPermutation q hq S ^ d) start) := by
    rw [hactual]
    exact (pairing_preserves_retained q S _).mpr hterminal
  have hsmNo : ∀ k : ℕ, 0 < k → k < d₀ →
      ¬ retainedCorner q S ((smoothingDartPermutation q hq S ^ k) start) := by
    intro k hk hk₀ hretk
    apply hno₀ k hk hk₀
    change retainedCorner q S
      (orbitEventAt q hq S root ((cyclicSuccessorPerm N ^ k) c.val))
    rw [orbitEventAt_iterate]
    exact hretk
  have heq : d₀ = d := by
    rcases lt_trichotomy d₀ d with hlt | heq | hgt
    · have hbad := hno d₀ hpos₀ hlt
      have hbefore := smoothing_pow_eq_original_before_corner q hq S start d hno hlt
      have hgood : retainedCorner q S ((smoothingDartPermutation q hq S ^ d₀) start) := by
        rw [hactual₀]
        exact next.property
      rw [hbefore] at hgood
      exact (hbad hgood).elim
    · exact heq
    · exact (hsmNo d hd hgt hret).elim
  rw [heq] at hactual₀
  exact hactual₀.symm.trans hactual






end DirectGLSSW.MixedEdgeFirstReturn
