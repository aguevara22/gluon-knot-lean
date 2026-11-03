import LocalPolygonEventOrder

namespace DirectGLSSW.LocalCrossingTransport
open DirectGLSSW
open DirectGLSSW.TruncationDirection

/-- Position of an old event using its fixed original edge labels. -/
noncomputable def eventPointFormula {n : ℕ}
    (q q' : Fin n → PlanarPoint ℝ) (x : PolygonEvent q) : PlanarPoint ℝ :=
  match x with
  | .inl e => q' e
  | .inr v => affinePoint (q' v.1.val.1) (q' (cyclicSuccessor v.1.val.1))
      (parameterFormula q' v.1.val false)

theorem crossingPoint_eq_formula {n : ℕ} (q : Fin n → PlanarPoint ℝ)
    (hq : CyclicGeneric q) (c : PolygonCrossing q) :
    crossingPoint q c = affinePoint (q c.val.1) (q (cyclicSuccessor c.val.1))
      (parameterFormula q c.val false) := by
  have hp := (crossingParameterLeft_spec q c).2.2
  have h := parameterFormula_eq_actual q hq (c, false)
  change parameterFormula q c.val false = crossingParameterLeft q c at h
  rw [h]
  exact hp

/-- Actual transported points agree with the continuous fixed-label formula. -/
theorem polygonEventPoint_map_eq_formula {n : ℕ}
    (q q' : Fin n → PlanarPoint ℝ) (hq' : CyclicGeneric q')
    (E : PolygonCrossing q ≃ PolygonCrossing q')
    (hlabels : ∀ c, (E c).val = c.val) (x : PolygonEvent q) :
    polygonEventPoint q' (polygonEventMapEquiv E x) = eventPointFormula q q' x := by
  cases x with
  | inl e => rfl
  | inr v =>
    change crossingPoint q' (E v.1) =
      affinePoint (q' v.1.val.1) (q' (cyclicSuccessor v.1.val.1))
        (parameterFormula q' v.1.val false)
    rw [crossingPoint_eq_formula q' hq' (E v.1), hlabels]

/-- Continuity of each retained original event position, before any daughter enumeration. -/
theorem eventPointFormula_continuousAt {n : ℕ}
    (Q : ℝ → Fin n → PlanarPoint ℝ)
    (hQ : ∀ v, Continuous (fun t => Q t v)) (h0 : CyclicGeneric (Q 0))
    (x : PolygonEvent (Q 0)) :
    ContinuousAt (fun t => eventPointFormula (Q 0) (Q t) x) 0 := by
  cases x with
  | inl e => exact (hQ e).continuousAt
  | inr v =>
    have ht := parameterFormula_continuousAt Q hQ h0 (v.1, false)
    have ha : ContinuousAt (fun t => Q t v.1.val.1) 0 := (hQ v.1.val.1).continuousAt
    have hb : ContinuousAt (fun t => Q t (cyclicSuccessor v.1.val.1)) 0 :=
      (hQ (cyclicSuccessor v.1.val.1)).continuousAt
    exact (ha.fst.add (ht.mul (hb.fst.sub ha.fst))).prodMk
      (ha.snd.add (ht.mul (hb.snd.sub ha.snd)))




end DirectGLSSW.LocalCrossingTransport
