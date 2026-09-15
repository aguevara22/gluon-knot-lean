import SM.TripleCenter

/-! At a G1 centre with one concurrence triple, exactly the three triangle
comparisons can be tied. Every other same-edge comparison persists. -/

namespace SM

open Filter Topology

variable {n : ℕ} [NeZero n] {P : LabelledTuple n}

theorem crossing_parameter_tie_concurrence (hn : 3 ≤ n) (hP : G1 P)
    {i j k : ZMod n} (hjk : j ≠ k)
    (hij : IsCrossing P {i, j}) (hik : IsCrossing P {i, k})
    (he : edgeParameter P i j = edgeParameter P i k) :
    ({i, j, k} : Finset (ZMod n)) ∈ concurrenceTriples P := by
  letI : Fact (1 < n) := ⟨by omega⟩
  let c : Crossing P := ⟨{i, j}, hij⟩
  let d : Crossing P := ⟨{i, k}, hik⟩
  have hp : crossingPoint c = crossingPoint d := by
    rw [crossingPoint_eq_edgeParameter hn hP hij,
      crossingPoint_eq_edgeParameter hn hP hik, he]
  have hi : crossingPoint c ∈ edgeInterior P i := crossingPoint_interior hP c i (by simp [c])
  have hj : crossingPoint c ∈ edgeInterior P j := crossingPoint_interior hP c j (by simp [c])
  have hk : crossingPoint c ∈ edgeInterior P k := hp ▸ crossingPoint_interior hP d k (by simp [d])
  have hrjk := g1_common_interiors_remote hn hP hjk hj hk
  exact (mem_concurrenceTriples P _).mpr
    ((concurrenceTriple_iff (crossing_pair_remote hij) hrjk (crossing_pair_remote hik)).mpr
      ⟨crossingPoint c, hi, hj, hk⟩)

theorem uniqueTriple_parameter_tie_iff (hn : 3 ≤ n) (hP : G1 P)
    {e f g i j k : ZMod n} (hc : concurrenceTriples P = {{e, f, g}})
    (hjk : j ≠ k) (hij : IsCrossing P {i, j}) (hik : IsCrossing P {i, k}) :
    edgeParameter P i j = edgeParameter P i k ↔
      ({i, j, k} : Finset (ZMod n)) = {e, f, g} := by
  constructor
  · intro he
    have hm := crossing_parameter_tie_concurrence hn hP hjk hij hik he
    simpa only [hc, Finset.mem_singleton] using hm
  · intro hs
    have hc' : concurrenceTriples P = {{i, j, k}} := by rw [hc, hs]
    exact uniqueTriple_parameters_eq hn hP hc'

def TripleUnchangedOrders (P Q : LabelledTuple n) (e f g : ZMod n) : Prop :=
  ∀ i j k : ZMod n, IsCrossing P {i, j} → IsCrossing P {i, k} →
    ({i, j, k} : Finset (ZMod n)) ≠ {e, f, g} →
    (edgeParameter Q i j < edgeParameter Q i k ↔ edgeParameter P i j < edgeParameter P i k)

theorem uniqueTriple_other_orders_persist (hn : 3 ≤ n) (hP : G1 P)
    {e f g : ZMod n} (hc : concurrenceTriples P = {{e, f, g}}) :
    ∀ᶠ Q in 𝓝 P, TripleUnchangedOrders P Q e f g := by
  apply eventually_all.mpr
  intro i
  apply eventually_all.mpr
  intro j
  apply eventually_all.mpr
  intro k
  by_cases h : IsCrossing P {i, j} ∧ IsCrossing P {i, k} ∧
      ({i, j, k} : Finset (ZMod n)) ≠ {e, f, g}
  · by_cases hjk : j = k
    · subst k
      exact Eventually.of_forall (fun _ _ _ _ => by simp)
    · have hne : edgeParameter P i j ≠ edgeParameter P i k :=
        fun he => h.2.2 ((uniqueTriple_parameter_tie_iff hn hP hc hjk h.1 h.2.1).mp he)
      exact (continuousAt_preserves_parameter_order (continuousAt_edgeParameter hn hP h.1)
        (continuousAt_edgeParameter hn hP h.2.1) hne).mono (fun _ hQ _ _ _ => hQ)
  · exact Eventually.of_forall (fun _ hij hik hnot => (h ⟨hij, hik, hnot⟩).elim)

end SM
