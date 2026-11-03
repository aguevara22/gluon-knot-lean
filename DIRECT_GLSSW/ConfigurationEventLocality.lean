import LocalPolygonEventOrder
import PolygonGermStability

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace DirectGLSSW.ConfigurationEventLocality

open DirectGLSSW
open DirectGLSSW.LocalCrossingTransport
open DirectGLSSW.ShortEdgeGenericity
open DirectGLSSW.TruncationDirection
open Filter Topology

private theorem continuous_affinePoint {α : Type*} [TopologicalSpace α]
    (a b : α → PlanarPoint ℝ) (t : α → ℝ)
    (ha : Continuous a) (hb : Continuous b) (ht : Continuous t) :
    Continuous (fun x => affinePoint (a x) (b x) (t x)) := by
  exact (ha.fst.add (ht.mul (hb.fst.sub ha.fst))).prodMk
    (ha.snd.add (ht.mul (hb.snd.sub ha.snd)))

private theorem configuration_det_continuousAt {n : ℕ}
    (q : Fin n → PlanarPoint ℝ) (a b c d : Fin n) :
    ContinuousAt (fun r : Fin n → PlanarPoint ℝ =>
      planarDet (r b - r a) (r d - r c)) q := by
  have ha : ContinuousAt (fun r : Fin n → PlanarPoint ℝ => r a) q :=
    (continuous_apply a).continuousAt
  have hb : ContinuousAt (fun r : Fin n → PlanarPoint ℝ => r b) q :=
    (continuous_apply b).continuousAt
  have hc : ContinuousAt (fun r : Fin n → PlanarPoint ℝ => r c) q :=
    (continuous_apply c).continuousAt
  have hd : ContinuousAt (fun r : Fin n → PlanarPoint ℝ => r d) q :=
    (continuous_apply d).continuousAt
  unfold planarDet
  exact ((hb.fst.sub ha.fst).mul (hd.snd.sub hc.snd)).sub
    ((hb.snd.sub ha.snd).mul (hd.fst.sub hc.fst))

private theorem configuration_leftParameter_continuousAt {n : ℕ}
    (q : Fin n → PlanarPoint ℝ) (e f : Fin n)
    (hD : planarDet (q (cyclicSuccessor e) - q e)
      (q (cyclicSuccessor f) - q f) ≠ 0) :
    ContinuousAt (fun r : Fin n → PlanarPoint ℝ =>
      leftParameter (r e) (r (cyclicSuccessor e))
        (r f) (r (cyclicSuccessor f))) q := by
  unfold leftParameter
  apply ContinuousAt.div
  · exact configuration_det_continuousAt q e f f (cyclicSuccessor f)
  · exact configuration_det_continuousAt q e (cyclicSuccessor e) f (cyclicSuccessor f)
  · exact hD

private theorem configuration_rightParameter_continuousAt {n : ℕ}
    (q : Fin n → PlanarPoint ℝ) (e f : Fin n)
    (hD : planarDet (q (cyclicSuccessor e) - q e)
      (q (cyclicSuccessor f) - q f) ≠ 0) :
    ContinuousAt (fun r : Fin n → PlanarPoint ℝ =>
      rightParameter (r e) (r (cyclicSuccessor e))
        (r f) (r (cyclicSuccessor f))) q := by
  unfold rightParameter
  apply ContinuousAt.div
  · exact configuration_det_continuousAt q e f e (cyclicSuccessor e)
  · exact configuration_det_continuousAt q e (cyclicSuccessor e) f (cyclicSuccessor f)
  · exact hD

private theorem configuration_parameterFormula_continuousAt {n : ℕ}
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (v : CrossingVisit q) :
    ContinuousAt (fun r : Fin n → PlanarPoint ℝ =>
      parameterFormula r v.1.val v.2) q := by
  have hD := crossing_transverse hq.size_ge_three q hq.g1 v.1
  have hD' : planarDet (q (cyclicSuccessor v.1.val.1) - q v.1.val.1)
      (q (cyclicSuccessor v.1.val.2) - q v.1.val.2) ≠ 0 := by
    simpa [cyclicTangent] using hD
  cases hb : v.2
  · simpa [parameterFormula, hb] using
      configuration_leftParameter_continuousAt q v.1.val.1 v.1.val.2 hD'
  · simpa [parameterFormula, hb] using
      configuration_rightParameter_continuousAt q v.1.val.1 v.1.val.2 hD'

/-- Absence of a common point of two closed edges is open in the full
configuration space; the segment parameters range over the compact square. -/
private theorem isOpen_no_two_closed {n : ℕ} (e f : Fin n) :
    IsOpen {q : Fin n → PlanarPoint ℝ | ¬ ∃ x,
      edgeClosed q e x ∧ edgeClosed q f x} := by
  let I := Set.Icc (0 : ℝ) 1
  let T := I × I
  let C := Fin n → PlanarPoint ℝ
  let P : C × T → PlanarPoint ℝ := fun z =>
    affinePoint (z.1 e) (z.1 (cyclicSuccessor e)) z.2.1
  let F : C × T → PlanarPoint ℝ := fun z =>
    affinePoint (z.1 f) (z.1 (cyclicSuccessor f)) z.2.2
  have hP : Continuous P := continuous_affinePoint _ _ _
    ((continuous_apply e).comp continuous_fst)
    ((continuous_apply (cyclicSuccessor e)).comp continuous_fst)
    (continuous_subtype_val.comp (continuous_fst.comp continuous_snd))
  have hF : Continuous F := continuous_affinePoint _ _ _
    ((continuous_apply f).comp continuous_fst)
    ((continuous_apply (cyclicSuccessor f)).comp continuous_fst)
    (continuous_subtype_val.comp (continuous_snd.comp continuous_snd))
  let B : Set (C × T) := {z | P z = F z}
  have hB : IsClosed B := isClosed_eq hP hF
  have hprojected : IsClosed (Prod.fst '' B) := isClosedMap_fst_of_compactSpace B hB
  have hmem (q : C) : q ∈ Prod.fst '' B ↔
      ∃ x, edgeClosed q e x ∧ edgeClosed q f x := by
    constructor
    · rintro ⟨⟨q', s, t⟩, hz, hq⟩
      change q' = q at hq
      subst q'
      change affinePoint (q e) (q (cyclicSuccessor e)) s =
        affinePoint (q f) (q (cyclicSuccessor f)) t at hz
      exact ⟨affinePoint (q e) (q (cyclicSuccessor e)) s,
        ⟨s, s.property.1, s.property.2, rfl⟩,
        ⟨t, t.property.1, t.property.2, hz⟩⟩
    · rintro ⟨x, ⟨s, hs0, hs1, hxs⟩, ⟨t, ht0, ht1, hxt⟩⟩
      exact ⟨(q, (⟨s, hs0, hs1⟩, ⟨t, ht0, ht1⟩)), hxs.symm.trans hxt, rfl⟩
  have heq : {q : C | ¬ ∃ x, edgeClosed q e x ∧ edgeClosed q f x} =
      (Prod.fst '' B)ᶜ := by
    ext q
    exact not_congr (hmem q).symm
  rw [heq]
  exact hprojected.isOpen_compl

/-- A positive transverse crossing persists around its polygon in the full
finite-dimensional configuration space. -/
private theorem eventually_crossing_of_crossing {n : ℕ}
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q) (e f : Fin n)
    (hef : e ≠ f)
    (hx : ∃ x, edgeInterior q e x ∧ edgeInterior q f x) :
    ∀ᶠ r in 𝓝 q, ∃ x, edgeInterior r e x ∧ edgeInterior r f x := by
  obtain ⟨x, he, hf⟩ := hx
  have hD := cyclicTangent_det_ne_zero_of_intersection hq.size_ge_three q hq.g1 e f hef x he hf
  obtain ⟨s, hs0, hs1, hxs⟩ := he
  obtain ⟨u, hu0, hu1, hxu⟩ := hf
  let S : (Fin n → PlanarPoint ℝ) → ℝ := fun r =>
    leftParameter (r e) (r (cyclicSuccessor e)) (r f) (r (cyclicSuccessor f))
  let U : (Fin n → PlanarPoint ℝ) → ℝ := fun r =>
    rightParameter (r e) (r (cyclicSuccessor e)) (r f) (r (cyclicSuccessor f))
  have hD' : planarDet (q (cyclicSuccessor e) - q e)
      (q (cyclicSuccessor f) - q f) ≠ 0 := by
    simpa [cyclicTangent] using hD
  have hS := configuration_leftParameter_continuousAt q e f hD'
  have hU := configuration_rightParameter_continuousAt q e f hD'
  have hS0 : S q = s :=
    leftParameter_eq _ _ _ _ s u hD' (hxs.symm.trans hxu)
  have hU0 : U q = u :=
    rightParameter_eq _ _ _ _ s u hD' (hxs.symm.trans hxu)
  have hs' : ∀ᶠ r in 𝓝 q, S r ∈ Set.Ioo (0 : ℝ) 1 :=
    hS.eventually (isOpen_Ioo.mem_nhds (by change 0 < S q ∧ S q < 1; rw [hS0]; exact ⟨hs0, hs1⟩))
  have hu' : ∀ᶠ r in 𝓝 q, U r ∈ Set.Ioo (0 : ℝ) 1 :=
    hU.eventually (isOpen_Ioo.mem_nhds (by change 0 < U q ∧ U q < 1; rw [hU0]; exact ⟨hu0, hu1⟩))
  have hDetCont := configuration_det_continuousAt q e (cyclicSuccessor e) f (cyclicSuccessor f)
  have hdet : ∀ᶠ r in 𝓝 q,
      planarDet (r (cyclicSuccessor e) - r e)
        (r (cyclicSuccessor f) - r f) ≠ 0 := hDetCont.eventually_ne hD'
  filter_upwards [hs', hu', hdet] with r hsr hur hdr
  exact ⟨affinePoint (r e) (r (cyclicSuccessor e)) (S r),
    ⟨S r, hsr.1, hsr.2, rfl⟩,
    ⟨U r, hur.1, hur.2, carrier_parameter_equation _ _ _ _ hdr⟩⟩

/-- Actual open-edge intersection of a fixed pair is locally unchanged in
configuration space. -/
private theorem eventually_crossing_iff {n : ℕ}
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (e f : Fin n) (hef : e ≠ f) :
    ∀ᶠ r in 𝓝 q,
      (∃ x, edgeInterior q e x ∧ edgeInterior q f x) ↔
      (∃ x, edgeInterior r e x ∧ edgeInterior r f x) := by
  by_cases hx : ∃ x, edgeInterior q e x ∧ edgeInterior q f x
  · filter_upwards [eventually_crossing_of_crossing q hq e f hef hx] with r hr
    exact ⟨fun _ => hr, fun _ => hx⟩
  · by_cases hsf : cyclicSuccessor e = f
    · filter_upwards [PolygonGermStability.eventually_cyclicGeneric
        (Q := fun r : Fin n → PlanarPoint ℝ => r)
        (a := q) (fun v => (continuous_apply v).continuousAt) hq] with r hr
      refine ⟨fun h => False.elim (hx h), ?_⟩
      rintro ⟨x, he, hf⟩
      exact False.elim (cyclic_adjacent_interiors_disjoint hq.size_ge_three r hr.g1 e x he (hsf ▸ hf))
    · by_cases hse : cyclicSuccessor f = e
      · filter_upwards [PolygonGermStability.eventually_cyclicGeneric
          (Q := fun r : Fin n → PlanarPoint ℝ => r)
          (a := q) (fun v => (continuous_apply v).continuousAt) hq] with r hr
        refine ⟨fun h => False.elim (hx h), ?_⟩
        rintro ⟨x, he, hf⟩
        exact False.elim (cyclic_adjacent_interiors_disjoint hq.size_ge_three r hr.g1 f x hf (hse ▸ he))
      · have hclosed : ¬ ∃ x, edgeClosed q e x ∧ edgeClosed q f x := by
          intro h
          exact hx (closed_crossing_implies_open q hq e f hef (Ne.symm hse) hsf h)
        have hopen := (isOpen_no_two_closed e f).mem_nhds hclosed
        filter_upwards [hopen] with r hr
        refine ⟨fun h => False.elim (hx h), ?_⟩
        rintro ⟨x, ⟨s, hs0, hs1, hxs⟩, ⟨u, hu0, hu1, hxu⟩⟩
        exact False.elim (hr ⟨x, ⟨s, hs0.le, hs1.le, hxs⟩,
          ⟨u, hu0.le, hu1.le, hxu⟩⟩)

/-- With an unchanged edge, strict order of two actual visit parameters is
locally unchanged in full configuration space. -/
private theorem eventually_parameterFormula_order {n : ℕ}
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (v w : CrossingVisit q)
    (he : crossingVisitEdge q v = crossingVisitEdge q w) :
    ∀ᶠ r in 𝓝 q,
      (crossingVisitParameter q v < crossingVisitParameter q w ↔
        parameterFormula r v.1.val v.2 < parameterFormula r w.1.val w.2) := by
  by_cases hvw : v = w
  · subst w
    exact Filter.Eventually.of_forall (fun _ => by simp)
  · have hne := actual_visit_parameters_ne q hq v w hvw he
    let D : (Fin n → PlanarPoint ℝ) → ℝ := fun r =>
      parameterFormula r w.1.val w.2 - parameterFormula r v.1.val v.2
    have hc : ContinuousAt D q :=
      (configuration_parameterFormula_continuousAt q hq w).sub
        (configuration_parameterFormula_continuousAt q hq v)
    have hD0 : D q = crossingVisitParameter q w - crossingVisitParameter q v := by
      dsimp [D]
      rw [parameterFormula_eq_actual q hq w, parameterFormula_eq_actual q hq v]
    by_cases hlt : crossingVisitParameter q v < crossingVisitParameter q w
    · have hpos : 0 < D q := by rw [hD0]; exact sub_pos.mpr hlt
      have hg : ∀ᶠ r in 𝓝 q, 0 < D r := hc.eventually (isOpen_Ioi.mem_nhds hpos)
      filter_upwards [hg] with r hr
      exact ⟨fun _ => sub_pos.mp hr, fun _ => hlt⟩
    · have hgt : crossingVisitParameter q w < crossingVisitParameter q v :=
        lt_of_le_of_ne (le_of_not_gt hlt) hne.symm
      have hneg : D q < 0 := by rw [hD0]; exact sub_neg.mpr hgt
      have hg : ∀ᶠ r in 𝓝 q, D r < 0 := hc.eventually (isOpen_Iio.mem_nhds hneg)
      filter_upwards [hg] with r hr
      exact ⟨fun h => False.elim (hlt h), fun h =>
        False.elim (not_lt_of_ge (le_of_lt (sub_neg.mp hr)) h)⟩

/-- Full finite event traversal order is locally invariant at every generic
polygon under the canonical label-preserving crossing equivalence. -/
theorem eventually_configuration_event_order {n : ℕ}
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q) :
    ∀ᶠ r in 𝓝 q,
      ∃ hr : CyclicGeneric r,
      ∃ E : PolygonCrossing q ≃ PolygonCrossing r,
        (∀ c, (E c).val = c.val) ∧
        ∀ x y : PolygonEvent q,
          ((polygonEventOrder q hq.g2).lt x y ↔
            (polygonEventOrder r hr.g2).lt
              (polygonEventMapEquiv E x) (polygonEventMapEquiv E y)) := by
  classical
  have hgeneric : ∀ᶠ r in 𝓝 q, CyclicGeneric r :=
    PolygonGermStability.eventually_cyclicGeneric
      (Q := fun r : Fin n → PlanarPoint ℝ => r)
      (a := q) (fun v => (continuous_apply v).continuousAt) hq
  have hpairs : ∀ᶠ r in 𝓝 q, ∀ e f : Fin n, e ≠ f →
      ((∃ x, edgeInterior q e x ∧ edgeInterior q f x) ↔
       (∃ x, edgeInterior r e x ∧ edgeInterior r f x)) := by
    apply Filter.eventually_all.mpr
    intro e
    apply Filter.eventually_all.mpr
    intro f
    by_cases hef : e = f
    · exact Filter.Eventually.of_forall (fun _ h => False.elim (h hef))
    · exact (eventually_crossing_iff q hq e f hef).mono (fun _ h _ => h)
  have horder : ∀ᶠ r in 𝓝 q, ∀ v w : CrossingVisit q,
      crossingVisitEdge q v = crossingVisitEdge q w →
        (crossingVisitParameter q v < crossingVisitParameter q w ↔
          parameterFormula r v.1.val v.2 < parameterFormula r w.1.val w.2) := by
    apply Filter.eventually_all.mpr
    intro v
    apply Filter.eventually_all.mpr
    intro w
    by_cases he : crossingVisitEdge q v = crossingVisitEdge q w
    · exact (eventually_parameterFormula_order q hq v w he).mono (fun _ h _ => h)
    · exact Filter.Eventually.of_forall (fun _ h => False.elim (he h))
  filter_upwards [hgeneric, hpairs, horder] with r hr hp ho
  let forward : PolygonCrossing q → PolygonCrossing r := fun c =>
    ⟨c.val, c.property.1, (hp c.val.1 c.val.2 (ne_of_lt c.property.1)).mp c.property.2⟩
  let backward : PolygonCrossing r → PolygonCrossing q := fun c =>
    ⟨c.val, c.property.1, (hp c.val.1 c.val.2 (ne_of_lt c.property.1)).mpr c.property.2⟩
  let E : PolygonCrossing q ≃ PolygonCrossing r :=
    ⟨forward, backward, fun c => Subtype.ext rfl, fun c => Subtype.ext rfl⟩
  have hlabels : ∀ c, (E c).val = c.val := fun _ => rfl
  refine ⟨hr, E, hlabels, ?_⟩
  intro x y
  have hvisitOrder : ∀ v w : CrossingVisit q,
      crossingVisitEdge q v = crossingVisitEdge q w →
      (crossingVisitParameter q v < crossingVisitParameter q w ↔
        crossingVisitParameter r (crossingVisit_mapEquiv E v) <
          crossingVisitParameter r (crossingVisit_mapEquiv E w)) := by
    intro v w he
    have h := ho v w he
    rw [parameterFormula_eq_mapped q r hr E hlabels v,
      parameterFormula_eq_mapped q r hr E hlabels w] at h
    exact h
  exact polygonEventMapEquiv_order_iff q r hq hr E hlabels hvisitOrder x y

/-- Continuous coordinatewise parameter families inherit the full
configuration-space event-order neighborhood by composition. -/
theorem eventually_configuration_event_order_of_continuousAt
    {α : Type*} [TopologicalSpace α] {a : α} {n : ℕ}
    (Q : α → Fin n → PlanarPoint ℝ)
    (hQ : ∀ v, ContinuousAt (fun z => Q z v) a)
    (hq : CyclicGeneric (Q a)) :
    ∀ᶠ z in 𝓝 a,
      ∃ hz : CyclicGeneric (Q z),
      ∃ E : PolygonCrossing (Q a) ≃ PolygonCrossing (Q z),
        (∀ c, (E c).val = c.val) ∧
        ∀ x y : PolygonEvent (Q a),
          ((polygonEventOrder (Q a) hq.g2).lt x y ↔
            (polygonEventOrder (Q z) hz.g2).lt
              (polygonEventMapEquiv E x) (polygonEventMapEquiv E y)) := by
  have hQall : ContinuousAt Q a := continuousAt_pi.mpr hQ
  have hlocal := eventually_configuration_event_order (Q a) hq
  exact hQall.eventually hlocal




end DirectGLSSW.ConfigurationEventLocality
