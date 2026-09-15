import SM.TripleAdjacency
import SM.GermNeighborhood

/-! Full source lem:triple-sides. All three crossings, distinct geometric
points and actual visit adjacency hold on one common punctured interval.
The central hypotheses are exactly the printed empty point-zero set and
singleton concurrence set. No sign-change hypothesis is used. -/

namespace SM

open Filter Topology

variable {n : ℕ} [NeZero n] {P : LabelledTuple n}

theorem isCrossing_pair_reverse {i j : ZMod n} (h : IsCrossing P {i, j}) :
    IsCrossing P {j, i} := by simpa only [Finset.pair_comm] using h

/-- The three named crossings, all three inequalities between actual points,
and consecutive positions in the actual Gauss list on each selected edge. -/
def TripleSides (hn : 3 ≤ n) (hP : Generic P) (i j k : ZMod n) : Prop :=
  ∃ hij : IsCrossing P {i, j}, ∃ hik : IsCrossing P {i, k},
    ∃ hjk : IsCrossing P {j, k},
      crossingPoint ⟨{i, j}, hij⟩ ≠ crossingPoint ⟨{i, k}, hik⟩ ∧
      crossingPoint ⟨{i, j}, hij⟩ ≠ crossingPoint ⟨{j, k}, hjk⟩ ∧
      crossingPoint ⟨{i, k}, hik⟩ ≠ crossingPoint ⟨{j, k}, hjk⟩ ∧
      VisitsAdjacent hn hP (pairVisit hij) (pairVisit hik) ∧
      VisitsAdjacent hn hP (pairVisit (isCrossing_pair_reverse hij)) (pairVisit hjk) ∧
      VisitsAdjacent hn hP (pairVisit (isCrossing_pair_reverse hik))
        (pairVisit (isCrossing_pair_reverse hjk))

theorem crossingPoints_ne_on_edge (hn : 3 ≤ n) (hP : Generic P)
    {i j k : ZMod n} (hjk : j ≠ k)
    (hcj : IsCrossing P {i, j}) (hck : IsCrossing P {i, k}) :
    crossingPoint ⟨{i, j}, hcj⟩ ≠ crossingPoint ⟨{i, k}, hck⟩ := by
  letI : Fact (1 < n) := ⟨by omega⟩
  intro he
  rw [crossingPoint_eq_edgeParameter hn hP.1 hcj,
    crossingPoint_eq_edgeParameter hn hP.1 hck] at he
  have hp := edgePoint_injective (g1_edge_ne_zero hn hP.1 i) he
  exact generic_edgeParameters_ne hn hP hjk hcj hck hp

theorem tripleSides_of_outside (hn : 3 ≤ n) (hP : Generic P) {i j k : ZMod n}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hcij : IsCrossing P {i, j}) (hcik : IsCrossing P {i, k})
    (hcjk : IsCrossing P {j, k})
    (hoi : OtherCrossingsOutside P i j k) (hoj : OtherCrossingsOutside P j i k)
    (hok : OtherCrossingsOutside P k i j) : TripleSides hn hP i j k := by
  have hcji := isCrossing_pair_reverse hcij
  have hcki := isCrossing_pair_reverse hcik
  have hckj := isCrossing_pair_reverse hcjk
  refine ⟨hcij, hcik, hcjk, crossingPoints_ne_on_edge hn hP hjk hcij hcik,
    ?_, ?_, pairVisits_adjacent hn hP hjk hcij hcik hoi,
    pairVisits_adjacent hn hP hik hcji hcjk hoj,
    pairVisits_adjacent hn hP hij hcki hckj hok⟩
  · simpa only [Finset.pair_comm i j] using
      crossingPoints_ne_on_edge hn hP hik hcji hcjk
  · simpa only [Finset.pair_comm i k, Finset.pair_comm j k] using
      crossingPoints_ne_on_edge hn hP hij hcki hckj

theorem uniqueTriple_sides_eventually (hn : 3 ≤ n) (hP : G1 P) {i j k : ZMod n}
    (hc : concurrenceTriples P = {{i, j, k}}) :
    ∀ᶠ Q in 𝓝 P, ∀ hQ : Generic Q, TripleSides hn hQ i j k := by
  have hcj : concurrenceTriples P = {{j, i, k}} := by
    simpa only [Finset.insert_comm i j] using hc
  have hck : concurrenceTriples P = {{k, i, j}} := by
    have he : ({i, j, k} : Finset (ZMod n)) = {k, i, j} := by
      ext a
      simp only [Finset.mem_insert, Finset.mem_singleton]
      tauto
    rw [hc, he]
  have hsel := uniqueTriple_crossings hc
  obtain ⟨hij, hjk, hik, _⟩ := uniqueTriple_data hc
  have hji' := (remote_endpoints i j hij).1
  have hki' := (remote_endpoints i k hik).1
  have hkj' := (remote_endpoints j k hjk).1
  filter_upwards [g1_crossings_locally_constant hn hP,
    uniqueTriple_outside_persists hn hP hc,
    uniqueTriple_outside_persists hn hP hcj,
    uniqueTriple_outside_persists hn hP hck] with Q hQ hoi hoj hok
  intro hgen
  exact tripleSides_of_outside hn hgen hji'.symm hki'.symm hkj'.symm
    ((hQ.2 {i, j}).mpr hsel.1) ((hQ.2 {i, k}).mpr hsel.2.1)
    ((hQ.2 {j, k}).mpr hsel.2.2) hoi hoj hok

/-- All clauses of original lem:triple-sides, on the actual interval of an
arbitrary continuous wall germ, with one radius covering both sides. -/
theorem triple_sides (hn : 3 ≤ n) (g : WallGerm n) {i j k : ZMod n}
    (hz : g.pointZeros = ∅) (hc : g.concurrences = {{i, j, k}}) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ g.radius ∧ ∀ t : g.Parameter,
      |t.val| < δ → ∀ ht : t.val ≠ 0,
        TripleSides hn (g.generic_punctured t ht) i j k := by
  have hG1 : G1 g.center := (g.pointZeros_empty_iff).mp hz
  have hcenter := uniqueTriple_sides_eventually hn hG1 hc
  have hcurve : ∀ᶠ t in 𝓝 g.zeroParameter,
      ∀ hQ : Generic (g.curve t), TripleSides hn hQ i j k :=
    g.continuous_curve.continuousAt.eventually hcenter
  apply (g.eventually_center_iff_radius
    (fun t => ∀ ht : t.val ≠ 0, TripleSides hn (g.generic_punctured t ht) i j k)).mp
  filter_upwards [hcurve] with t ht
  intro hne
  exact ht (g.generic_punctured t hne)

end SM
