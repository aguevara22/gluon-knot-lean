import SM.GeometricVisits
import SM.CrossingTransport

/-! Cramer's actual crossing parameters on the geometric record domain.
All bridges apply at flat centres and agree with the existing chosen points. -/

namespace SM

variable {n : ℕ} {P : LabelledTuple n}

theorem crossing_det_ne_zero_of_geometry (hP : CrossingGeometry P) {i j : ZMod n}
    (hc : IsCrossing P {i, j}) : det (edge P i) (edge P j) ≠ 0 := by
  obtain ⟨x, hi, hj⟩ := (isCrossing_pair P i j (crossing_pair_remote hc)).mp hc
  exact (hP.2.1 i j (crossing_pair_remote hc) x hi hj).2.2

theorem crossingParameter_eq_edgeParameter_of_geometry (hP : CrossingGeometry P)
    {i j : ZMod n} (hc : IsCrossing P {i, j}) :
    crossingParameter ⟨{i, j}, hc⟩ i (by simp) = edgeParameter P i j := by
  let c : Crossing P := ⟨{i, j}, hc⟩
  have hi : i ∈ c.val := by simp [c]
  have hj : j ∈ c.val := by simp [c]
  have hs := crossingParameter_spec c i hi
  have ht := crossingParameter_spec c j hj
  have he := hs.2.2.symm.trans ht.2.2
  exact ((div_eq_iff (crossing_det_ne_zero_of_geometry hP hc)).mpr
    (intersection_parameter_identity he)).symm

theorem crossingParameter_eq_of_support_pair_of_geometry (hP : CrossingGeometry P)
    (c : Crossing P) (i j : ZMod n) (hi : i ∈ c.val) (hs : c.val = {i, j}) :
    crossingParameter c i hi = edgeParameter P i j := by
  rcases c with ⟨s, hc⟩
  change s = {i, j} at hs
  subst s
  exact crossingParameter_eq_edgeParameter_of_geometry hP hc

theorem visitParameter_eq_of_support_pair_of_geometry (hP : CrossingGeometry P)
    (v : Visit P) (j : ZMod n) (hs : v.1.val = {v.2.val, j}) :
    visitParameter v = edgeParameter P v.2.val j :=
  crossingParameter_eq_of_support_pair_of_geometry hP v.1 v.2.val j v.2.property hs

theorem geometric_edgeParameters_ne (hP : CrossingGeometry P) {i j k : ZMod n}
    (hjk : j ≠ k) (hij : IsCrossing P {i, j}) (hik : IsCrossing P {i, k}) :
    edgeParameter P i j ≠ edgeParameter P i k := by
  intro heq
  let c : Crossing P := ⟨{i, j}, hij⟩
  let d : Crossing P := ⟨{i, k}, hik⟩
  have hcp := (crossingParameter_spec c i (by simp [c])).2.2
  have hdp := (crossingParameter_spec d i (by simp [d])).2.2
  have hp : crossingPoint c = crossingPoint d := by
    rw [hcp, hdp, crossingParameter_eq_edgeParameter_of_geometry hP hij,
      crossingParameter_eq_edgeParameter_of_geometry hP hik, heq]
  have hcd := crossingPoint_injective_of_geometry hP hp
  have hs : ({i, j} : Finset (ZMod n)) = {i, k} := congrArg Subtype.val hcd
  have hm : j ∈ ({i, k} : Finset (ZMod n)) := by rw [← hs]; simp
  have hji : j ≠ i := (remote_endpoints i j (crossing_pair_remote hij)).1
  exact hjk (by simpa [hji] using hm)

theorem continuousAt_edgeParameter_of_geometry (hP : CrossingGeometry P)
    {i j : ZMod n} (hc : IsCrossing P {i, j}) :
    ContinuousAt (fun Q : LabelledTuple n => edgeParameter Q i j) P :=
  continuousAt_cramerFirst (continuous_vertex i).continuousAt (continuous_vertex j).continuousAt
    (continuous_edge i).continuousAt (continuous_edge j).continuousAt
    (crossing_det_ne_zero_of_geometry hP hc)

end SM
