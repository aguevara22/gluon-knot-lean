import PLRootGerm

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.HOMFLY
open PermutationOrbits

/-- A continuation orbit does not revisit its starting arc before its full
finite component length. -/
theorem continuation_orbit_no_early_return (D : PLLinkDiagram)
    (e : Fin D.nArc) (k : ℕ) (hk : k < componentArcLength D e)
    (hreturn : (D.continuation ^ k) e = e) : k = 0 := by
  let N := componentArcLength D e
  let i : Fin N := ⟨k, hk⟩
  let z : Fin N := ⟨0, by exact componentArcLength_pos D e⟩
  have heq : orbitEnumeration D.continuation e i =
      orbitEnumeration D.continuation e z := by
    apply Subtype.ext
    simpa [i, z, orbitEnumeration_apply_val] using hreturn
  have hidx := (orbitEnumeration D.continuation e).injective heq
  exact congrArg Fin.val hidx

/-- An interior point of one arc is absent from every other arc, including
its endpoints, by the actual diagram's incidence geometry. -/
theorem diagramArc_avoids_other_interior_point (D : PLLinkDiagram)
    (base f : Fin D.nArc) (τ : ℝ) (hτ0 : 0 < τ) (hτ1 : τ < 1)
    (hfb : f ≠ base) (t : unitInterval) :
    diagramArcPath D f t ≠
      affinePoint (D.vertexPoint (D.arcSource base))
        (D.vertexPoint (D.arcTarget base)) τ := by
  intro hEq
  have hEq' : affinePoint (D.vertexPoint (D.arcSource f))
        (D.vertexPoint (D.arcTarget f)) t.val =
      affinePoint (D.vertexPoint (D.arcSource base))
        (D.vertexPoint (D.arcTarget base)) τ := by
    simpa only [diagramArcPath_apply] using hEq
  by_cases ht0 : t.val = 0
  · rw [ht0, affinePoint_zero] at hEq'
    exact (D.vertices_avoid_arc_interiors (D.arcSource f) base τ hτ0 hτ1) hEq'
  by_cases ht1 : t.val = 1
  · rw [ht1, affinePoint_one] at hEq'
    exact (D.vertices_avoid_arc_interiors (D.arcTarget f) base τ hτ0 hτ1) hEq'
  have ht0' : 0 < t.val := lt_of_le_of_ne t.property.1 (Ne.symm ht0)
  have ht1' : t.val < 1 := lt_of_le_of_ne t.property.2 ht1
  exact D.arc_interiors_disjoint f base hfb t.val τ ht0' ht1' hτ0 hτ1 hEq'

/-- Under avoidance of the later constituent arcs, an interior point of the
first arc has only its initial dyadic-time preimage along a continuation path. -/
theorem continuationPath_unique_initial_interior_preimage
    (D : PLLinkDiagram) (e : Fin D.nArc) (τ : ℝ)
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (N : ℕ)
    (havoid : ∀ k, 0 < k → k < N → ∀ t : unitInterval,
      diagramArcPath D ((D.continuation ^ k) e) t ≠
        affinePoint (D.vertexPoint (D.arcSource e))
          (D.vertexPoint (D.arcTarget e)) τ) :
    ∀ m, 1 ≤ m → m ≤ N → ∀ u : unitInterval,
      continuationPath D e m u =
        affinePoint (D.vertexPoint (D.arcSource e))
          (D.vertexPoint (D.arcTarget e)) τ →
        u.val = τ / (2 : ℝ) ^ (m - 1) := by
  intro m
  induction m with
  | zero => intro hm; omega
  | succ n ih =>
      intro hm hmn u hpoint
      by_cases hn0 : n = 0
      · subst n
        have hpath : diagramArcPath D e u =
            diagramArcPath D e ⟨τ, ⟨le_of_lt hτ0, le_of_lt hτ1⟩⟩ := by
          simpa [continuationPath, continuationArcPath, Path.cast_coe,
            diagramArcPath_apply] using hpoint
        have hparam := (diagramArcPath_injective D e) hpath
        have hval := congrArg Subtype.val hparam
        simpa using hval
      have hnpos : 1 ≤ n := by omega
      have hnpow : n ≤ N := by omega
      have hprev : n - 1 + 1 = n := by omega
      have hpoint' :
          ((continuationPath D e n).trans
            (continuationArcPath D ((D.continuation ^ n) e))) u =
          affinePoint (D.vertexPoint (D.arcSource e))
            (D.vertexPoint (D.arcTarget e)) τ := by
        have hlen : n + 1 = (n - 1) + 2 := by omega
        rw [hlen, continuationPath.eq_def, Path.cast_coe] at hpoint
        rw [hprev] at hpoint
        exact hpoint
      rw [Path.trans_apply] at hpoint'
      by_cases hfirst : u.val ≤ 1 / 2
      · simp only [dif_pos hfirst] at hpoint'
        let v : unitInterval := ⟨2 * u.val,
          ⟨by nlinarith [u.property.1], by linarith⟩⟩
        have hv := ih hnpos hnpow v hpoint'
        have hpow : (2 : ℝ) ^ n = (2 : ℝ) ^ (n - 1) * 2 := by
          have hnsub : n = (n - 1) + 1 := by omega
          calc
            (2 : ℝ) ^ n = (2 : ℝ) ^ ((n - 1) + 1) :=
              congrArg (fun j : ℕ => (2 : ℝ) ^ j) hnsub
            _ = (2 : ℝ) ^ (n - 1) * 2 := by rw [pow_succ]
        have hv' : 2 * u.val = τ / (2 : ℝ) ^ (n - 1) := by
          simpa [v] using hv
        calc
          u.val = (2 * u.val) / 2 := by field_simp
          _ = (τ / (2 : ℝ) ^ (n - 1)) / 2 := by rw [hv']
          _ = τ / (2 : ℝ) ^ n := by rw [hpow]; ring
      · simp only [dif_neg hfirst] at hpoint'
        have hlast : diagramArcPath D ((D.continuation ^ n) e)
            ⟨2 * u.val - 1, ⟨by linarith, by linarith [u.property.2]⟩⟩ =
            affinePoint (D.vertexPoint (D.arcSource e))
              (D.vertexPoint (D.arcTarget e)) τ := by
          simpa [continuationArcPath, Path.cast_coe] using hpoint'
        have hkl : n < N := by omega
        exact False.elim (havoid n (by omega) hkl _ hlast)

/-- The actual component PL loop has a unique preimage of a strict interior
point of its initial arc, with the source path's dyadic parameter. -/
theorem componentPLLoop_unique_interior_root_preimage
    (D : PLLinkDiagram) (base : Fin D.nArc) (τ : ℝ)
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (u : unitInterval)
    (hpoint : complexPLLoop D base u = Complex.equivRealProd.symm
      (affinePoint (D.vertexPoint (D.arcSource base))
        (D.vertexPoint (D.arcTarget base)) τ)) :
    u.val = τ / (2 : ℝ) ^ (componentArcLength D base - 1) := by
  let N := componentArcLength D base
  have hN : 0 < N := componentArcLength_pos D base
  have havoid : ∀ k, 0 < k → k < N → ∀ t : unitInterval,
      diagramArcPath D ((D.continuation ^ k) base) t ≠
        affinePoint (D.vertexPoint (D.arcSource base))
          (D.vertexPoint (D.arcTarget base)) τ := by
    intro k hk0 hkN t
    apply diagramArc_avoids_other_interior_point D base
      ((D.continuation ^ k) base) τ hτ0 hτ1 ?_ t
    intro hEq
    have hkzero := continuation_orbit_no_early_return D base k hkN hEq
    omega
  have hplanar : componentPLLoop D base u =
      affinePoint (D.vertexPoint (D.arcSource base))
        (D.vertexPoint (D.arcTarget base)) τ := by
    simpa [complexPLLoop] using Complex.equivRealProd.symm.injective hpoint
  have hpath : continuationPath D base N u =
      affinePoint (D.vertexPoint (D.arcSource base))
        (D.vertexPoint (D.arcTarget base)) τ := by
    have hc : componentPLLoop D base u = continuationPath D base N u := by
      simp [N, componentPLLoop, Path.cast_coe]
    exact hc.symm.trans hplanar
  have htime := continuationPath_unique_initial_interior_preimage
    D base τ hτ0 hτ1 N havoid N (by omega) le_rfl u hpath
  simpa [N] using htime

end DirectGLSSW.HOMFLY
end





