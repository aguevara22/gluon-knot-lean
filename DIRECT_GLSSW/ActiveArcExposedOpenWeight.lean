import ActiveArcExposedAuxiliary

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.ExposedChart
open DirectGLSSW ExposedOpenPrimitive GeometricSmoothingWeights PermutationOrbits
attribute [local instance] Classical.propDecidable
variable {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ) (e : Fin (n+2))
variable (hq : CyclicGeneric q) (he : LeftExposed q e) (hAux : auxiliaryGenericity q hq)
variable (S : Primitive.Support (cutArc q e) (cutArc_regular q e hq))

theorem openLast_successor :
    cyclicSuccessor (RetainedWords.openLast (cutArc q e) (cutArc_regular q e hq) S.val)=
      RetainedWords.openFirst (cutArc q e) (cutArc_regular q e hq) S.val := by
  apply Fin.ext
  change ((RetainedWords.openCount (cutArc q e) (cutArc_regular q e hq) S.val-1)+1+0)%
    RetainedWords.openCount (cutArc q e) (cutArc_regular q e hq) S.val=0
  have hp := RetainedWords.open_count_ge_two (cutArc q e) (cutArc_regular q e hq) S.val
  rw [Nat.sub_add_cancel (by omega),Nat.add_zero,Nat.mod_self]

theorem openLast_point :
    Primitive.OpenVertex (cutArc q e) (cutArc_regular q e hq) S
      (RetainedWords.openLast (cutArc q e) (cutArc_regular q e hq) S.val)=q e := by
  rw [Primitive.OpenVertex,RetainedWords.open_vertex_last,cutArc_last]

theorem openFirst_point :
    Primitive.OpenVertex (cutArc q e) (cutArc_regular q e hq) S
      (RetainedWords.openFirst (cutArc q e) (cutArc_regular q e hq) S.val)=q (cyclicSuccessor e) := by
  rw [Primitive.OpenVertex,RetainedWords.open_vertex_first,cutArc_first]

theorem open_closing_tangent :
    cyclicTangent (Primitive.OpenVertex (cutArc q e) (cutArc_regular q e hq) S)
      (RetainedWords.openLast (cutArc q e) (cutArc_regular q e hq) S.val)=cyclicTangent q e := by
  rw [cyclicTangent,openLast_successor q e hq S,openFirst_point q e hq S,openLast_point q e hq S]
  rfl

include he hAux in
/-- The actual supporting edge is inherited by the true open retained word. -/
theorem open_leftExposed :
    LeftExposed (Primitive.OpenVertex (cutArc q e) (cutArc_regular q e hq) S)
      (RetainedWords.openLast (cutArc q e) (cutArc_regular q e hq) S.val) := by
  let Q := Primitive.OpenVertex (cutArc q e) (cutArc_regular q e hq) S
  let last := RetainedWords.openLast (cutArc q e) (cutArc_regular q e hq) S.val
  have hQ : CyclicGeneric Q := retained_generic q e hq he hAux S (ActiveArc.start (cutArc q e))
  intro i hi hs
  have hn : 0≤planarDet (cyclicTangent Q last) (Q i-Q last) := by
    have hlast : Q last=q e := openLast_point q e hq S
    rw [open_closing_tangent q e hq S,hlast]
    have hh := leftExposed_event_nonneg q e he
      (eventEquiv q e hq he (RetainedWords.cornerEvent (cutArc q e) (cutArc_regular q e hq)
        S.val (ActiveArc.start (cutArc q e)) i))
    rw [eventEquiv_point] at hh
    exact hh
  have hz := cyclic_vertex_carrier_det_ne_zero hQ.size_ge_three Q hQ.g1 last i hi hs
  exact lt_of_le_of_ne hn (Ne.symm hz)

theorem openCurrent_eq_component (hRI : GLSSWRootIndependence) :
    Primitive.openCurrent (cutArc q e) (cutArc_regular q e hq) S=
      componentAmplitude q hq (mappedSupport q e hq he S.val) hAux
        ((nonalternating_iff_parent q e hq he S.val).mp S.property)
        (dartComponentEquiv q e hq he S.val
          (ActiveArc.openComponent (cutArc q e) (cutArc_regular q e hq).noTriple S.val)) := by
  have hQ := retained_generic q e hq he hAux S (ActiveArc.start (cutArc q e))
  change openedEdgeCurrent (Primitive.OpenVertex (cutArc q e) (cutArc_regular q e hq) S)
      (RetainedWords.openLast (cutArc q e) (cutArc_regular q e hq) S.val)=_
  rw [openedEdgeCurrent_eq_amplitude _ hQ _ (open_leftExposed q e hq he hAux S) hRI]
  exact retainedAmplitude_eq_component q e hq he hAux hRI S (ActiveArc.start (cutArc q e))

end DirectGLSSW.ActiveArc.ExposedChart
