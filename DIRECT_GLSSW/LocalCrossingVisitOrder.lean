import LocalCrossingTransport
import DirectGLSSW.TruncationVisitTransport

namespace DirectGLSSW.LocalCrossingTransport
open DirectGLSSW
open DirectGLSSW.TruncationDirection
open Filter Topology

/-- Rational visit parameter with fixed original edge labels and fixed Boolean side. -/
noncomputable def parameterFormula {n : ℕ} (q : Fin n → PlanarPoint ℝ)
    (p : Fin n × Fin n) (b : Bool) : ℝ :=
  if b then rightParameter (q p.1) (q (cyclicSuccessor p.1))
    (q p.2) (q (cyclicSuccessor p.2))
  else leftParameter (q p.1) (q (cyclicSuccessor p.1))
    (q p.2) (q (cyclicSuccessor p.2))

theorem parameterFormula_eq_actual {n : ℕ} (q : Fin n → PlanarPoint ℝ)
    (hq : CyclicGeneric q) (v : CrossingVisit q) :
    parameterFormula q v.1.val v.2 = crossingVisitParameter q v := by
  obtain ⟨s0, s1, hs⟩ := crossingParameterLeft_spec q v.1
  obtain ⟨u0, u1, hu⟩ := crossingParameterRight_spec q v.1
  have hd := crossing_transverse hq.size_ge_three q hq.g1 v.1
  have hx := hs.symm.trans hu
  cases hb : v.2
  · simpa [parameterFormula, crossingVisitParameter, hb] using
      (leftParameter_eq _ _ _ _ (crossingParameterLeft q v.1) (crossingParameterRight q v.1) hd hx)
  · simpa [parameterFormula, crossingVisitParameter, hb] using
      (rightParameter_eq _ _ _ _ (crossingParameterLeft q v.1) (crossingParameterRight q v.1) hd hx)

theorem parameterFormula_continuousAt {n : ℕ}
    (Q : ℝ → Fin n → PlanarPoint ℝ)
    (hQ : ∀ v, Continuous (fun t => Q t v)) (h0 : CyclicGeneric (Q 0))
    (v : CrossingVisit (Q 0)) :
    ContinuousAt (fun t => parameterFormula (Q t) v.1.val v.2) 0 := by
  have hd := crossing_transverse h0.size_ge_three (Q 0) h0.g1 v.1
  cases hb : v.2
  · exact leftParameter_continuousAt _ _ _ _ (hQ _) (hQ _) (hQ _) (hQ _) hd
  · exact rightParameter_continuousAt _ _ _ _ (hQ _) (hQ _) (hQ _) (hQ _) hd

theorem parameterFormula_eq_mapped {n : ℕ}
    (q q' : Fin n → PlanarPoint ℝ) (hq' : CyclicGeneric q')
    (E : PolygonCrossing q ≃ PolygonCrossing q')
    (hlabels : ∀ c, (E c).val = c.val) (v : CrossingVisit q) :
    parameterFormula q' v.1.val v.2 =
      crossingVisitParameter q' (crossingVisit_mapEquiv E v) := by
  have h := parameterFormula_eq_actual q' hq' (crossingVisit_mapEquiv E v)
  simpa only [crossingVisit_mapEquiv, Equiv.coe_fn_mk, hlabels] using h

/-- G2 excludes an equal parameter for two distinct visits on the same edge. -/
theorem actual_visit_parameters_ne {n : ℕ} (q : Fin n → PlanarPoint ℝ)
    (hq : CyclicGeneric q) (v w : CrossingVisit q)
    (hne : v ≠ w) (he : crossingVisitEdge q v = crossingVisitEdge q w) :
    crossingVisitParameter q v ≠ crossingVisitParameter q w := by
  intro h
  exact hne (crossingVisitKey_injective q hq.g2 (Prod.ext he h))

/-- Strict order of fixed-label visit parameters is unchanged locally. -/
theorem eventually_parameterFormula_order {n : ℕ}
    (Q : ℝ → Fin n → PlanarPoint ℝ)
    (hQ : ∀ v, Continuous (fun t => Q t v)) (h0 : CyclicGeneric (Q 0))
    (v w : CrossingVisit (Q 0))
    (he : crossingVisitEdge (Q 0) v = crossingVisitEdge (Q 0) w) :
    ∀ᶠ t in 𝓝 (0 : ℝ),
      (crossingVisitParameter (Q 0) v < crossingVisitParameter (Q 0) w ↔
        parameterFormula (Q t) v.1.val v.2 < parameterFormula (Q t) w.1.val w.2) := by
  by_cases hvw : v = w
  · subst w
    exact Filter.Eventually.of_forall (fun _ => by simp)
  · have hne := actual_visit_parameters_ne (Q 0) h0 v w hvw he
    let D : ℝ → ℝ := fun t => parameterFormula (Q t) w.1.val w.2 -
      parameterFormula (Q t) v.1.val v.2
    have hc : ContinuousAt D 0 :=
      (parameterFormula_continuousAt Q hQ h0 w).sub (parameterFormula_continuousAt Q hQ h0 v)
    have hD0 : D 0 = crossingVisitParameter (Q 0) w - crossingVisitParameter (Q 0) v := by
      dsimp [D]
      rw [parameterFormula_eq_actual (Q 0) h0 w, parameterFormula_eq_actual (Q 0) h0 v]
    by_cases hlt : crossingVisitParameter (Q 0) v < crossingVisitParameter (Q 0) w
    · have hpos : 0 < D 0 := by rw [hD0]; exact sub_pos.mpr hlt
      have hg : ∀ᶠ t in 𝓝 (0 : ℝ), 0 < D t := hc.eventually (isOpen_Ioi.mem_nhds hpos)
      filter_upwards [hg] with t ht
      exact ⟨fun _ => sub_pos.mp ht, fun _ => hlt⟩
    · have hgt : crossingVisitParameter (Q 0) w < crossingVisitParameter (Q 0) v :=
        lt_of_le_of_ne (le_of_not_gt hlt) hne.symm
      have hneg : D 0 < 0 := by rw [hD0]; exact sub_neg.mpr hgt
      have hg : ∀ᶠ t in 𝓝 (0 : ℝ), D t < 0 := hc.eventually (isOpen_Iio.mem_nhds hneg)
      filter_upwards [hg] with t ht
      exact ⟨fun h => False.elim (hlt h), fun h => False.elim (not_lt_of_ge (le_of_lt (sub_neg.mp ht)) h)⟩

/-- Geometry supplies a label-preserving crossing equivalence and the actual visit order. -/
theorem exists_local_crossing_equiv_visit_order {n : ℕ}
    (Q : ℝ → Fin n → PlanarPoint ℝ)
    (hQ : ∀ v, Continuous (fun t => Q t v)) (h0 : CyclicGeneric (Q 0)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t, |t| < δ →
      ∃ ht : CyclicGeneric (Q t),
      ∃ E : PolygonCrossing (Q 0) ≃ PolygonCrossing (Q t),
        (∀ c, (E c).val = c.val) ∧
        ∀ v w : CrossingVisit (Q 0),
          crossingVisitEdge (Q 0) v = crossingVisitEdge (Q 0) w →
          (crossingVisitParameter (Q 0) v < crossingVisitParameter (Q 0) w ↔
            crossingVisitParameter (Q t) (crossingVisit_mapEquiv E v) <
            crossingVisitParameter (Q t) (crossingVisit_mapEquiv E w)) := by
  classical
  obtain ⟨δc, hδc, hc⟩ := exists_local_crossing_equiv Q hQ h0
  have ho : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ v w : CrossingVisit (Q 0),
      crossingVisitEdge (Q 0) v = crossingVisitEdge (Q 0) w →
      (crossingVisitParameter (Q 0) v < crossingVisitParameter (Q 0) w ↔
        parameterFormula (Q t) v.1.val v.2 < parameterFormula (Q t) w.1.val w.2) := by
    apply Filter.eventually_all.mpr
    intro v
    apply Filter.eventually_all.mpr
    intro w
    by_cases he : crossingVisitEdge (Q 0) v = crossingVisitEdge (Q 0) w
    · exact (eventually_parameterFormula_order Q hQ h0 v w he).mono (fun _ h _ => h)
    · exact Filter.Eventually.of_forall (fun _ h => False.elim (he h))
  obtain ⟨δo, hδo, hball⟩ := Metric.mem_nhds_iff.mp ho
  refine ⟨min δc δo, lt_min hδc hδo, ?_⟩
  intro t ht
  obtain ⟨hgt, E, hlabels⟩ := hc t (lt_of_lt_of_le ht (min_le_left _ _))
  refine ⟨hgt, E, hlabels, ?_⟩
  intro v w he
  have hh := hball (by simpa [Metric.mem_ball, Real.dist_eq] using
    (lt_of_lt_of_le ht (min_le_right δc δo))) v w he
  rw [parameterFormula_eq_mapped (Q 0) (Q t) hgt E hlabels v,
    parameterFormula_eq_mapped (Q 0) (Q t) hgt E hlabels w] at hh
  exact hh






end DirectGLSSW.LocalCrossingTransport
