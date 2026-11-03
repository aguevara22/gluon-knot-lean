import DirectGLSSW.PolygonEvents

set_option autoImplicit false

namespace DirectGLSSW

variable {K : Type*} [Field K] [LinearOrder K] {n : ℕ}

/-- An actual crossing with one incident edge fixed to `e`. -/
abbrev EdgeChord (q : Fin n → PlanarPoint K) (e : Fin n) :=
  {c : PolygonCrossing q // c.val.1 = e ∨ c.val.2 = e}

/-- Select the visit that belongs to the chosen polygon edge. -/
def edgeVisitSide (q : Fin n → PlanarPoint K) (e : Fin n)
    (c : EdgeChord q e) : Bool :=
  if c.val.val.1 = e then false else true

/-- The selected actual visit on the chosen edge. -/
def edgeVisit (q : Fin n → PlanarPoint K) (e : Fin n)
    (c : EdgeChord q e) : CrossingVisit q :=
  (c.val, edgeVisitSide q e c)

/-- The other actual visit of the same crossing. -/
def returnVisit (q : Fin n → PlanarPoint K) (e : Fin n)
    (c : EdgeChord q e) : CrossingVisit q :=
  crossingVisitFlip q (edgeVisit q e c)

/-- The selected visit is on `e`; its paired return visit is on another edge. -/
theorem edgeVisitSide_spec
    (q : Fin n → PlanarPoint K) (e : Fin n) (c : EdgeChord q e) :
    crossingVisitEdge q (edgeVisit q e c) = e ∧
      crossingVisitEdge q (returnVisit q e c) ≠ e := by
  rcases c.property with hfirst | hsecond
  · have hsecondNe : c.val.val.2 ≠ e := by
      intro he
      exact (crossing_edges_ne q c.val) (hfirst.trans he.symm)
    simp [edgeVisit, edgeVisitSide, returnVisit, crossingVisitFlip,
      crossingVisitEdge, hfirst, hsecondNe]
  · have hfirst : c.val.val.1 ≠ e := by
      intro he
      exact (crossing_edges_ne q c.val) (he.trans hsecond.symm)
    simp [edgeVisit, edgeVisitSide, returnVisit, crossingVisitFlip,
      crossingVisitEdge, hsecond, hfirst]

/-- Selecting the edge visit retains the actual crossing as its first field. -/
theorem edgeVisit_injective
    (q : Fin n → PlanarPoint K) (e : Fin n) :
    Function.Injective (edgeVisit q e) := by
  intro c d h
  apply Subtype.ext
  exact congrArg Prod.fst h

/-- Selecting the return visit also retains the actual crossing. -/
theorem returnVisit_injective
    (q : Fin n → PlanarPoint K) (e : Fin n) :
    Function.Injective (returnVisit q e) := by
  intro c d h
  apply Subtype.ext
  exact congrArg Prod.fst h

/-- The two selected visits are the same actual plane crossing point. -/
theorem edgeVisit_return_samePoint
    (q : Fin n → PlanarPoint K) (e : Fin n) (c : EdgeChord q e) :
    crossingVisitPoint q (edgeVisit q e c) =
      crossingVisitPoint q (returnVisit q e c) := rfl

/-- The chosen affine parameter is the parameter on the selected incident edge. -/
theorem edgeVisit_parameter_eq
    (q : Fin n → PlanarPoint K) (e : Fin n) (c : EdgeChord q e) :
    crossingVisitParameter q (edgeVisit q e c) =
      if c.val.val.1 = e then crossingParameterLeft q c.val
      else crossingParameterRight q c.val := by
  rcases c.property with hfirst | hsecond
  · simp [edgeVisit, edgeVisitSide, crossingVisitParameter, hfirst]
  · have hfirst : c.val.val.1 ≠ e := by
      intro he
      exact (crossing_edges_ne q c.val) (he.trans hsecond.symm)
    simp [edgeVisit, edgeVisitSide, crossingVisitParameter, hsecond, hfirst]

/-- The selected crossing point is the actual affine point on edge `e`. -/
theorem edgeVisit_point_eq_affine
    (q : Fin n → PlanarPoint K) (e : Fin n) (c : EdgeChord q e) :
    crossingPoint q c.val =
      affinePoint (q e) (q (cyclicSuccessor e))
        (crossingVisitParameter q (edgeVisit q e c)) := by
  have h := (crossingVisitParameter_spec q (edgeVisit q e c)).2.2
  rw [(edgeVisitSide_spec q e c).1] at h
  simpa [crossingVisitPoint] using h

section Ordered

variable [IsStrictOrderedRing K]

/-- Along a leftward horizontal edge, event order is reverse abscissa order. -/
theorem edgeVisit_order_iff_reverse_abscissa
    (q : Fin n → PlanarPoint K) (hq : cyclicNoTripleIntersections q)
    (e : Fin n)
    (hflat : (q e).2 = (q (cyclicSuccessor e)).2)
    (hleft : (q (cyclicSuccessor e)).1 < (q e).1)
    (c d : EdgeChord q e) :
    (polygonEventOrder q hq).lt
        (Sum.inr (edgeVisit q e c) : PolygonEvent q)
        (Sum.inr (edgeVisit q e d)) ↔
      (crossingPoint q d.val).1 < (crossingPoint q c.val).1 := by
  have he : polygonEventEdge q (Sum.inr (edgeVisit q e c)) =
      polygonEventEdge q (Sum.inr (edgeVisit q e d)) := by
    simp [polygonEventEdge, (edgeVisitSide_spec q e c).1,
      (edgeVisitSide_spec q e d).1]
  have hsame := polygonEvent_sameEdge_lt_iff q hq
    (Sum.inr (edgeVisit q e c)) (Sum.inr (edgeVisit q e d)) he
  have hsame' : (polygonEventOrder q hq).lt
      (Sum.inr (edgeVisit q e c) : PolygonEvent q)
      (Sum.inr (edgeVisit q e d)) ↔
      crossingVisitParameter q (edgeVisit q e c) <
        crossingVisitParameter q (edgeVisit q e d) := by
    simpa using hsame
  rw [hsame']
  have hxc := congrArg Prod.fst (edgeVisit_point_eq_affine q e c)
  have hxd := congrArg Prod.fst (edgeVisit_point_eq_affine q e d)
  simp only [affinePoint, Prod.fst] at hxc hxd
  rw [hxc, hxd]
  let tc := crossingVisitParameter q (edgeVisit q e c)
  let td := crossingVisitParameter q (edgeVisit q e d)
  have hslope : (q (cyclicSuccessor e)).1 - (q e).1 < 0 :=
    sub_lt_zero.mpr hleft
  change tc < td ↔ _
  constructor
  · intro hparam
    have hmul := mul_lt_mul_of_neg_left hparam hslope
    have hmul' : td * ((q (cyclicSuccessor e)).1 - (q e).1) <
        tc * ((q (cyclicSuccessor e)).1 - (q e).1) := by
      simpa [mul_comm] using hmul
    exact (add_lt_add_iff_left (q e).1).2 hmul'
  · intro habscissa
    have hmul : td * ((q (cyclicSuccessor e)).1 - (q e).1) <
        tc * ((q (cyclicSuccessor e)).1 - (q e).1) :=
      (add_lt_add_iff_left (q e).1).1 habscissa
    by_contra hnot
    have hge : td ≤ tc := le_of_not_gt hnot
    rcases lt_or_eq_of_le hge with hlt | heq
    · have hreverse := mul_lt_mul_of_neg_left hlt hslope
      have hreverse' : tc * ((q (cyclicSuccessor e)).1 - (q e).1) <
          td * ((q (cyclicSuccessor e)).1 - (q e).1) := by
        simpa [mul_comm] using hreverse
      exact (lt_asymm hmul hreverse')
    · rw [heq] at hmul
      exact (lt_irrefl _) hmul

end Ordered

/-- On a horizontal edge, actual crossing abscissae identify its edge chords. -/
theorem edgeChord_abscissa_injective
    (q : Fin n → PlanarPoint K) (hq : cyclicNoTripleIntersections q)
    (e : Fin n)
    (hflat : (q e).2 = (q (cyclicSuccessor e)).2)
    (c d : EdgeChord q e) :
    (crossingPoint q c.val).1 = (crossingPoint q d.val).1 → c = d := by
  intro hx
  have hcy := congrArg Prod.snd (edgeVisit_point_eq_affine q e c)
  have hdy := congrArg Prod.snd (edgeVisit_point_eq_affine q e d)
  have hcy' : (crossingPoint q c.val).2 = (q e).2 := by
    calc
      (crossingPoint q c.val).2 =
          (q e).2 + crossingVisitParameter q (edgeVisit q e c) *
            ((q (cyclicSuccessor e)).2 - (q e).2) := by
        simpa [affinePoint, Prod.snd] using hcy
      _ = (q e).2 := by rw [hflat, sub_self, mul_zero, add_zero]
  have hdy' : (crossingPoint q d.val).2 = (q e).2 := by
    calc
      (crossingPoint q d.val).2 =
          (q e).2 + crossingVisitParameter q (edgeVisit q e d) *
            ((q (cyclicSuccessor e)).2 - (q e).2) := by
        simpa [affinePoint, Prod.snd] using hdy
      _ = (q e).2 := by rw [hflat, sub_self, mul_zero, add_zero]
  have hp : crossingPoint q c.val = crossingPoint q d.val :=
    Prod.ext hx (hcy'.trans hdy'.symm)
  have hc := crossingPoint_injective q hq hp
  exact Subtype.ext hc














end DirectGLSSW
