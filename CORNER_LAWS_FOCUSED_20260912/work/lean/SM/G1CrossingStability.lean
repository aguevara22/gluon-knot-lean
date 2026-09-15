import SM.ChamberPaths

/-! Local constancy of the complete actual crossing support at every G1
tuple, including a triple-intersection centre where G2 fails. -/

namespace SM

open Filter Topology

variable {n : ℕ} [NeZero n]

theorem chi_locally_constant_of_G1 {P : LabelledTuple n} (hP : G1 P) (i j k : ZMod n) :
    ∀ᶠ Q in 𝓝 P, chi Q i j k = chi P i j k := by
  by_cases hij : i = j
  · subst j
    exact Eventually.of_forall (fun _ => by simp)
  by_cases hjk : j = k
  · subst k
    exact Eventually.of_forall (fun _ => by simp)
  by_cases hik : i = k
  · subst k
    exact Eventually.of_forall (fun _ => by simp)
  have hc : ContinuousAt (fun Q : LabelledTuple n => chi Q i j k) P :=
    (continuousAt_sign_of_ne_zero (g1_area_ne_zero hP hij hjk hik)).comp
      (f := fun Q : LabelledTuple n => det (Q j - Q i) (Q k - Q i))
      (continuous_area i j k).continuousAt
  exact hc.eventually (isOpen_discrete _ |>.mem_nhds (Set.mem_singleton (chi P i j k)))

theorem g1_crossings_locally_constant (hn : 3 ≤ n) {P : LabelledTuple n} (hP : G1 P) :
    ∀ᶠ Q in 𝓝 P, G1 Q ∧ ∀ s : Finset (ZMod n), IsCrossing Q s ↔ IsCrossing P s := by
  have hc : ∀ᶠ Q in 𝓝 P, ∀ i j k, chi Q i j k = chi P i j k :=
    eventually_all.mpr fun i => eventually_all.mpr fun j => eventually_all.mpr fun k =>
      chi_locally_constant_of_G1 hP i j k
  filter_upwards [g1_persists hP, hc] with Q hQ hchi
  exact ⟨hQ, crossing_iff_of_chi_eq hn hQ hP hchi⟩

theorem continuousAt_edgeParameter (hn : 3 ≤ n) {P : LabelledTuple n} (hP : G1 P)
    {i j : ZMod n} (hc : IsCrossing P {i, j}) :
    ContinuousAt (fun Q : LabelledTuple n => edgeParameter Q i j) P :=
  continuousAt_cramerFirst (continuous_vertex i).continuousAt (continuous_vertex j).continuousAt
    (continuous_edge i).continuousAt (continuous_edge j).continuousAt
    (crossing_edgeParameter_det_ne_zero hn hP hc)

end SM
