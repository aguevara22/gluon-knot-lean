import SM.Chambers

/-! The actual weakly generic locus of def:weak. In particular, disjoint remote
segments are allowed to be parallel or collinear: transversality is required
only when a common point exists. The openness lemma is a separate obligation. -/

namespace SM

variable {n : ℕ}

def WeakGeneric (P : LabelledTuple n) : Prop :=
  (∀ i, edge P i ≠ 0) ∧
  (∀ i, turn P i ≠ 0) ∧
  (∀ k i, ¬ incident k i → P k ∉ edgeSegment P i) ∧
  (∀ i j, remote i j →
    (∀ x, x ∈ edgeSegment P i → x ∈ edgeSegment P j → det (edge P i) (edge P j) ≠ 0) ∧
    (∀ x y, x ∈ edgeSegment P i → x ∈ edgeSegment P j →
      y ∈ edgeSegment P i → y ∈ edgeSegment P j → x = y)) ∧
  G2 P

def weakLocus (n : ℕ) : Set (LabelledTuple n) := {P | WeakGeneric P}

def silentLocus (n : ℕ) : Set (LabelledTuple n) := weakLocus n \ {P | Generic P}

abbrev WeakTuple (n : ℕ) := {P : LabelledTuple n // WeakGeneric P}

/-- Visible chambers, read on labelled representatives as in lem:weak-open. -/
def labelledVisibleChamber (P : WeakTuple n) : Set (WeakTuple n) := connectedComponent P

theorem generic_implies_weak (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P) :
    WeakGeneric P := by
  haveI : NeZero n := ⟨by omega⟩
  haveI : Fact (1 < n) := ⟨by omega⟩
  refine ⟨g1_edge_ne_zero hn hP.1, ?_, ?_, ?_, hP.2⟩
  · intro i
    rw [turn_det]
    exact sign_ne_zero.mpr (g1_turn_nonzero hn hP.1 i)
  · intro k i hki
    have hk0 : k ≠ i := by
      intro he
      apply hki
      exact Or.inr he.symm
    have hk1 : k ≠ i + 1 := by
      intro he
      apply hki
      left
      rw [he, add_sub_cancel_right]
    exact g1_vertex_not_mem_edge hP.1 i k (next_ne_self i).symm hk0 hk1
  · intro i j hr
    constructor
    · intro x hi hj
      exact (g1_remote_meeting hP.1 hr hi hj).2.2.1
    · intro x y hxi hxj hyi hyj
      exact ((g1_remote_meeting hP.1 hr hxi hxj).2.2.2 y hyi hyj).symm

theorem genericLocus_subset_weakLocus (hn : 3 ≤ n) :
    {P : LabelledTuple n | Generic P} ⊆ weakLocus n :=
  fun _ hP => generic_implies_weak hn hP

theorem mem_silentLocus (P : LabelledTuple n) :
    P ∈ silentLocus n ↔ WeakGeneric P ∧ ¬ Generic P := Iff.rfl

theorem weak_shift_forward (a : ZMod n) {P : LabelledTuple n} (hP : WeakGeneric P) :
    WeakGeneric (shift a P) := by
  refine ⟨?_, ?_, ?_, ?_, g2_shift_forward a hP.2.2.2.2⟩
  · intro i
    simpa only [edge_shift] using hP.1 (i + a)
  · intro i
    simpa only [turn_shift] using hP.2.1 (i + a)
  · intro k i hki
    have hshift : ¬ incident (k + a) (i + a) := by
      intro he
      apply hki
      rcases he with he | he
      · left
        have he' : i + a = (k - 1) + a := by simpa [sub_add_eq_add_sub] using he
        exact add_right_cancel he'
      · exact Or.inr (add_right_cancel he)
    simpa only [edgeSegment_shift, shift] using hP.2.2.1 (k + a) (i + a) hshift
  · intro i j hr
    have hr' : remote (i + a) (j + a) := by
      simpa only [remote, adjacent, add_sub_add_right_eq_sub] using hr
    simpa only [edgeSegment_shift, edge_shift] using hP.2.2.2.1 (i + a) (j + a) hr'

theorem weak_shift (a : ZMod n) (P : LabelledTuple n) :
    WeakGeneric (shift a P) ↔ WeakGeneric P := by
  constructor
  · intro h
    simpa only [shift_add, neg_add_cancel, shift_zero] using weak_shift_forward (-a) h
  · exact weak_shift_forward a

def weakCyclicSetoid (n : ℕ) : Setoid (WeakTuple n) :=
  (cyclicSetoid n).comap Subtype.val

abbrev WeakPolygon (n : ℕ) := Quotient (weakCyclicSetoid n)

/-- Visible chambers in the space of unlabelled weakly generic polygons. -/
def visibleChamber (P : WeakPolygon n) : Set (WeakPolygon n) := connectedComponent P

/-- Full def:weak: the genuine weak/silent loci, the inclusion asserted in the
source, and visible chambers as connected components. The labelled version is
also exposed for the next lemma, which explicitly works on representatives. -/
theorem weak_definition (hn : 3 ≤ n) :
    {P : LabelledTuple n | Generic P} ⊆ weakLocus n ∧
    silentLocus n = weakLocus n \ {P | Generic P} ∧
    (∀ P : WeakPolygon n, visibleChamber P = connectedComponent P) ∧
    (∀ P : WeakTuple n, labelledVisibleChamber P = connectedComponent P) ∧
    (∀ a : ZMod n, ∀ P : LabelledTuple n, WeakGeneric (shift a P) ↔ WeakGeneric P) :=
  ⟨genericLocus_subset_weakLocus hn, rfl, fun _ => rfl, fun _ => rfl, weak_shift⟩

end SM
