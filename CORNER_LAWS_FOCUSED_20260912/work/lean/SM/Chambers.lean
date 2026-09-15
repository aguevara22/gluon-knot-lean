import SM.GenericTopology
import Mathlib.Topology.Algebra.Module.LocallyConvex
import Mathlib.Topology.Instances.Sign
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.Homeomorph.Lemmas

/-! The source's actual generic space, cyclic quotient and connected components.
No chamber is replaced by a combinatorial equivalence class. -/

namespace SM

open Filter Topology

abbrev GenericTuple (n : ℕ) := {P : LabelledTuple n // Generic P}

def genericCyclicSetoid (n : ℕ) : Setoid (GenericTuple n) :=
  (cyclicSetoid n).comap Subtype.val

abbrev GenericPolygon (n : ℕ) := Quotient (genericCyclicSetoid n)

def polygonProjection {n : ℕ} : GenericTuple n → GenericPolygon n := Quotient.mk _

/-- Labelled chambers are connected components in the actual generic locus. -/
def labelledChamber {n : ℕ} (P : GenericTuple n) : Set (GenericTuple n) :=
  connectedComponent P

/-- A chamber is a connected component of the genuine cyclic orbit space. -/
def chamber {n : ℕ} (P : GenericPolygon n) : Set (GenericPolygon n) :=
  connectedComponent P

theorem genericTuple_locallyPathConnected (hn : 3 ≤ n) :
    LocallyPathConnectedSpace (GenericTuple n) :=
  (isOpen_Generic hn).locallyPathConnectedSpace

theorem genericPolygon_locallyPathConnected (hn : 3 ≤ n) :
    LocallyPathConnectedSpace (GenericPolygon n) := by
  letI := genericTuple_locallyPathConnected hn
  infer_instance

theorem chambers_open_pathConnected (hn : 3 ≤ n) (P : GenericPolygon n) :
    IsOpen (chamber P) ∧ IsPathConnected (chamber P) := by
  letI := genericPolygon_locallyPathConnected hn
  refine ⟨isOpen_connectedComponent, ?_⟩
  change IsPathConnected (connectedComponent P)
  rw [← pathComponent_eq_connectedComponent P]
  exact isPathConnected_pathComponent

theorem labelledChambers_open_pathConnected (hn : 3 ≤ n) (P : GenericTuple n) :
    IsOpen (labelledChamber P) ∧ IsPathConnected (labelledChamber P) := by
  letI := genericTuple_locallyPathConnected hn
  refine ⟨isOpen_connectedComponent, ?_⟩
  change IsPathConnected (connectedComponent P)
  rw [← pathComponent_eq_connectedComponent P]
  exact isPathConnected_pathComponent

theorem continuous_generic_chi (i j k : ZMod n) :
    Continuous (fun P : GenericTuple n => chi P.val i j k) := by
  by_cases hij : i = j
  · subst j
    simpa using (continuous_const : Continuous (fun _ : GenericTuple n => (0 : SignType)))
  by_cases hjk : j = k
  · subst k
    simpa using (continuous_const : Continuous (fun _ : GenericTuple n => (0 : SignType)))
  by_cases hik : i = k
  · subst k
    simpa using (continuous_const : Continuous (fun _ : GenericTuple n => (0 : SignType)))
  rw [continuous_iff_continuousAt]
  intro P
  exact (continuousAt_sign_of_ne_zero (g1_area_ne_zero P.property.1 hij hjk hik)).comp
    (f := fun Q : GenericTuple n => det (Q.val j - Q.val i) (Q.val k - Q.val i))
    ((continuous_area i j k).comp continuous_subtype_val).continuousAt

theorem crossing_iff_of_chi_eq (hn : 3 ≤ n) {P Q : LabelledTuple n}
    (hP : G1 P) (hQ : G1 Q) (hchi : ∀ i j k, chi P i j k = chi Q i j k)
    (s : Finset (ZMod n)) : IsCrossing P s ↔ IsCrossing Q s := by
  have transfer {A B : LabelledTuple n} (hA : G1 A) (hB : G1 B)
      (hAB : ∀ i j k, chi A i j k = chi B i j k) (hs : IsCrossing A s) :
      IsCrossing B s := by
    obtain ⟨i, j, rfl, hr, hmeet⟩ := hs
    have hpair : IsCrossing A {i, j} := ⟨i, j, rfl, hr, hmeet⟩
    apply ((crossing_test hn B hB).1 i j hr).mpr
    simpa only [← hAB] using ((crossing_test hn A hA).1 i j hr).mp hpair
  exact ⟨transfer hP hQ hchi, transfer hQ hP (fun i j k => (hchi i j k).symm)⟩

/-- The directed parameter on the first segment; meaningful at an actual crossing. -/
noncomputable def edgeParameter (P : LabelledTuple n) (i j : ZMod n) : ℝ :=
  cramerFirst (P i) (P j) (edge P i) (edge P j)

theorem crossing_pair_remote {P : LabelledTuple n} {i j : ZMod n}
    (h : IsCrossing P {i, j}) : remote i j := by
  obtain ⟨a, b, heq, hr, _⟩ := h
  have hab : a ≠ b := (remote_endpoints a b hr).1.symm
  have hi : i = a ∨ i = b := by
    have : i ∈ ({a, b} : Finset (ZMod n)) := by rw [← heq]; simp
    simpa using this
  have hj : j = a ∨ j = b := by
    have : j ∈ ({a, b} : Finset (ZMod n)) := by rw [← heq]; simp
    simpa using this
  have hij : i ≠ j := by
    intro hij
    have hc := congrArg Finset.card heq
    simp [hij, Finset.card_pair hab] at hc
  rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
  · exact (hij rfl).elim
  · exact hr
  · exact remote_symm hr
  · exact (hij rfl).elim

theorem crossingParameter_eq_edgeParameter (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : G1 P) {i j : ZMod n} (h : IsCrossing P {i, j}) :
    crossingParameter ⟨{i, j}, h⟩ i (by simp) = edgeParameter P i j := by
  haveI : NeZero n := ⟨by omega⟩
  haveI : Fact (1 < n) := ⟨by omega⟩
  let c : Crossing P := ⟨{i, j}, h⟩
  have hi : i ∈ c.val := by simp [c]
  have hj : j ∈ c.val := by simp [c]
  have hs := crossingParameter_spec c i hi
  have hr := crossingParameter_spec c j hj
  have heq := hs.2.2.symm.trans hr.2.2
  have hd := g1_remote_intersection_det hP (crossing_pair_remote h) heq
  exact ((div_eq_iff hd).mpr (intersection_parameter_identity heq)).symm

theorem crossing_edgeParameter_det_ne_zero (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : G1 P) {i j : ZMod n} (h : IsCrossing P {i, j}) :
    det (edge P i) (edge P j) ≠ 0 := by
  haveI : NeZero n := ⟨by omega⟩
  haveI : Fact (1 < n) := ⟨by omega⟩
  obtain ⟨x, hi, hj⟩ := (isCrossing_pair P i j (crossing_pair_remote h)).mp h
  exact (g1_remote_meeting hP (crossing_pair_remote h) hi hj).2.2.1

theorem generic_edgeParameters_ne (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) {i j k : ZMod n} (hjk : j ≠ k)
    (hij : IsCrossing P {i, j}) (hik : IsCrossing P {i, k}) :
    edgeParameter P i j ≠ edgeParameter P i k := by
  classical
  intro heq
  let c : Crossing P := ⟨{i, j}, hij⟩
  let d : Crossing P := ⟨{i, k}, hik⟩
  have hcp := (crossingParameter_spec c i (by simp [c])).2.2
  have hdp := (crossingParameter_spec d i (by simp [d])).2.2
  have hp : crossingPoint c = crossingPoint d := by
    rw [hcp, hdp, crossingParameter_eq_edgeParameter hn hP.1 hij,
      crossingParameter_eq_edgeParameter hn hP.1 hik, heq]
  have hcd := generic_crossingPoint_injective hn hP hp
  have hs : ({i, j} : Finset (ZMod n)) = {i, k} := congrArg Subtype.val hcd
  have hmem : j ∈ ({i, k} : Finset (ZMod n)) := by rw [← hs]; simp
  have hj : j ≠ i := (remote_endpoints i j (crossing_pair_remote hij)).1
  exact hjk (by simpa [hj] using hmem)

end SM
