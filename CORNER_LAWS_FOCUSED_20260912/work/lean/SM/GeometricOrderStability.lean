import SM.GeometricParameters
import SM.GeometricCrossingStability

/-! One finite neighbourhood preserves every actual crossing-parameter order
and every positive over/under determinant sign, including at flat centres. -/

namespace SM

open Filter Topology

variable {n : ℕ} [NeZero n] {P : LabelledTuple n}

theorem geometric_parameter_order_persists (hP : CrossingGeometry P) :
    ∀ᶠ Q in 𝓝 P, ∀ i j k : ZMod n,
      IsCrossing P {i, j} → IsCrossing P {i, k} →
        (edgeParameter Q i j < edgeParameter Q i k ↔
          edgeParameter P i j < edgeParameter P i k) := by
  apply eventually_all.mpr
  intro i
  apply eventually_all.mpr
  intro j
  apply eventually_all.mpr
  intro k
  by_cases hij : IsCrossing P {i, j}
  swap
  · exact Eventually.of_forall (fun _ h => (hij h).elim)
  by_cases hik : IsCrossing P {i, k}
  swap
  · exact Eventually.of_forall (fun _ _ h => (hik h).elim)
  by_cases hjk : j = k
  · subst k
    exact Eventually.of_forall (fun _ _ _ => by simp)
  · exact (continuousAt_preserves_parameter_order
      (continuousAt_edgeParameter_of_geometry hP hij)
      (continuousAt_edgeParameter_of_geometry hP hik)
      (geometric_edgeParameters_ne hP hjk hij hik)).mono (fun _ h _ _ => h)

theorem crossingSign_locally_constant_of_geometry (hP : CrossingGeometry P)
    {i j : ZMod n} (hc : IsCrossing P {i, j}) :
    ∀ᶠ Q in 𝓝 P, crossingSign Q i j = crossingSign P i j := by
  have hf : ContinuousAt (fun Q : LabelledTuple n => crossingSign Q i j) P :=
    (continuousAt_sign_of_ne_zero (crossing_det_ne_zero_of_geometry hP hc)).comp
      (f := fun Q : LabelledTuple n => det (edge Q i) (edge Q j))
      (continuousAt_det (continuous_edge i).continuousAt (continuous_edge j).continuousAt)
  exact hf.eventually (isOpen_discrete _ |>.mem_nhds (Set.mem_singleton (crossingSign P i j)))

theorem geometric_crossing_signs_persist (hP : CrossingGeometry P) :
    ∀ᶠ Q in 𝓝 P, ∀ i j : ZMod n, IsCrossing P {i, j} →
      crossingSign Q i j = crossingSign P i j := by
  apply eventually_all.mpr
  intro i
  apply eventually_all.mpr
  intro j
  by_cases hc : IsCrossing P {i, j}
  · exact (crossingSign_locally_constant_of_geometry hP hc).mono (fun _ h _ => h)
  · exact Eventually.of_forall (fun _ h => (hc h).elim)

end SM
