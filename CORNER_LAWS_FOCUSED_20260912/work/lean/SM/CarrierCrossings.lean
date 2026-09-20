import SM.CarrierActualCornerBlock
import SM.CarrierComponentCount

/-! Towards def:smoothing (sm-3-statesum.tex:14): crossings of a carrier, m_Q, corner directions, unselected non-neighbour ownership. Written 2026-09-13 by a Claude Code prover subagent of the pod
executor (workflow prove-smoothing-support / prove:smoothing-A), checked with `lake env lean` (placeholder-free, standard axioms) and
ported verbatim from work/drafts/SmoothingSupportA.lean (only this header added and #print lines removed). -/

/-! # SM15, `def:smoothing` (oriented smoothing and subpolygons), Task A

Source: reference/SM/sm-3-statesum.tex, lines 14–27 (`def:smoothing`), 29–39
(`conv:selected-visits`), 54–95 (`lem:carriers`) and its proof, lines 96–240
(the finite successor model `ρ`, `ρ_S`).

Encoding (all in the ported Carrier lane, namespace `SM.Carrier`):
* the marked traversal circle is `Mark P = ZMod n ⊕ Visit P`, its successor
  `ρ = markSuccessor hn hP`, the reconnected successor `ρ_S = smoothingSuccessor hn hP S`
  (`ρ_S a = ρ (selectedMarkPerm S a)`, i.e. `ρ_S(a) = ρ(b)` at a selected pair `a, b`);
* the carriers (subpolygons) of `S` are the cycles of `ρ_S`, `Component hn hP S`, and
  `owner hn hP S a` is the carrier of the mark `a` (the incoming-visit convention:
  a mark keeps its own node, hence its incoming arc);
* "the edge visited by `v`" is `v.2.val : ZMod n` (`visitPosition_edge`), `E_i` is
  `edgeSegment P i`, `ℓ_i = μ_{i+1} - μ_i` is `edge P i`, the segment of the carrier
  from `a` to `ρ_S a` is `smoothingSegment hn hP S a : ℝ → Plane`; the incoming segment
  at `a` is the segment of the predecessor `(smoothingSuccessor hn hP S).symm a`.

Statements proved here:
1. `carrierCrossings hn hP S q` = "the crossings `x ∈ X(P) \ S` both of whose visits lie
   on `Q`", `carrierCrossingCount` = `m_Q`; membership lemma; a selected crossing is a
   crossing of no carrier; distinct carriers have disjoint crossing sets.
2. `smoothing_corner_directions`: at a selected visit `v` owned by `q` (a smoothing
   corner of `Q` between `E_{v.2}` and `E_{(visitTwin v).2}`, the two edges of `v.1`),
   the incoming segment of `Q` lies on `E_{v.2}` with direction a positive multiple of
   `ℓ_{v.2}`, and the outgoing segment lies on `E_{(visitTwin v).2}` with direction a
   positive multiple of `ℓ_{(visitTwin v).2}` ("arrives along one of `ℓ_i, ℓ_j` and leaves
   along the other").
3. `vertex_corner_directions`: at an original vertex `i` owned by `q`, the incoming
   segment lies on `E_{i-1}` (direction a positive multiple of `ℓ_{i-1}`) and the outgoing
   segment on `E_i` (positive multiple of `ℓ_i`).
4. `unselected_nonneighbor_both_visits_one_carrier` and
   `unselected_nonneighbor_exists_unique_carrier`: for `S` independent and
   `x ∈ U(S) = supportUnselected hn hP S`, both visits of `x` have one owner, and `x` is a
   crossing of exactly one carrier (the "interlacing no element of `S`" half of
   `lem:carriers` (iii) and the last sentence of `def:smoothing`). -/

namespace SM.Carrier

noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ} [NeZero n]

/-! ## 1. The crossings of a carrier and `m_Q` -/

/-- `def:smoothing`: "The crossings of `Q` are the crossings `x ∈ X(P) \ S` both of whose
visits lie on `Q`". A visit lies on `Q` when its owner (under the incoming-visit
convention) is `Q`. -/
def carrierCrossings (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) (q : Component hn hP S) : Finset (Crossing P) :=
  Finset.univ.filter fun x : Crossing P =>
    x ∉ S ∧ ∀ v : Visit P, v.1 = x → owner hn hP S (Sum.inr v) = q

/-- `m_Q`, the number of crossings of the carrier `Q`. -/
def carrierCrossingCount (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) (q : Component hn hP S) : ℕ :=
  (carrierCrossings hn hP S q).card

theorem mem_carrierCrossings (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) (q : Component hn hP S) (x : Crossing P) :
    x ∈ carrierCrossings hn hP S q ↔
      x ∉ S ∧ ∀ v : Visit P, v.1 = x → owner hn hP S (Sum.inr v) = q := by
  simp only [carrierCrossings, Finset.mem_filter, Finset.mem_univ, true_and]

/-- The same membership, quantified over the two-element visit fibre of `x`. -/
theorem mem_carrierCrossings_iff_fiber (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) (q : Component hn hP S) (x : Crossing P) :
    x ∈ carrierCrossings hn hP S q ↔
      x ∉ S ∧ ∀ i : {k // k ∈ x.val}, owner hn hP S (Sum.inr ⟨x, i⟩) = q := by
  rw [mem_carrierCrossings]
  constructor
  · rintro ⟨hx, h⟩
    exact ⟨hx, fun i => h ⟨x, i⟩ rfl⟩
  · rintro ⟨hx, h⟩
    refine ⟨hx, ?_⟩
    rintro ⟨c, i⟩ hc
    change c = x at hc
    subst hc
    exact h i

/-- A selected crossing is a crossing of no carrier. -/
theorem selected_not_mem_carrierCrossings (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) (S : Finset (Crossing P)) (q : Component hn hP S)
    {x : Crossing P} (hx : x ∈ S) : x ∉ carrierCrossings hn hP S q :=
  fun h => ((mem_carrierCrossings hn hP S q x).mp h).1 hx

/-- Every crossing of a carrier is unselected. -/
theorem carrierCrossings_subset_compl (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) (S : Finset (Crossing P)) (q : Component hn hP S) :
    carrierCrossings hn hP S q ⊆ Finset.univ \ S := by
  intro x hx
  rw [Finset.mem_sdiff]
  exact ⟨Finset.mem_univ x, ((mem_carrierCrossings hn hP S q x).mp hx).1⟩

/-- A crossing is a crossing of at most one carrier: its visits have one owner. -/
theorem carrierCrossings_disjoint (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) {q r : Component hn hP S} (hqr : q ≠ r) :
    Disjoint (carrierCrossings hn hP S q) (carrierCrossings hn hP S r) := by
  rw [Finset.disjoint_left]
  intro x hxq hxr
  obtain ⟨i, _, _⟩ := crossing_visits_exist x
  have h1 := ((mem_carrierCrossings_iff_fiber hn hP S q x).mp hxq).2 i
  have h2 := ((mem_carrierCrossings_iff_fiber hn hP S r x).mp hxr).2 i
  exact hqr (h1.symm.trans h2)

theorem carrierCrossingCount_eq_card (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) (q : Component hn hP S) :
    carrierCrossingCount hn hP S q = (carrierCrossings hn hP S q).card := rfl

/-- `∑_Q m_Q` counts the crossings of all carriers, each once (the sets are disjoint). -/
theorem sum_carrierCrossingCount (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) :
    ∑ q : Component hn hP S, carrierCrossingCount hn hP S q =
      ((Finset.univ : Finset (Component hn hP S)).biUnion (carrierCrossings hn hP S)).card := by
  rw [Finset.card_biUnion]
  · rfl
  · intro q _ r _ hqr
    exact carrierCrossings_disjoint hn hP S hqr

/-! ## 2. Edges of incoming segments -/

/-- The mark immediately before a crossing visit lies on the visit's own edge. -/
theorem markSuccessor_symm_visit_edge (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (v : Visit P) :
    (markPosition hn hP.1 ((markSuccessor hn hP).symm (Sum.inr v))).1 = v.2.val := by
  have hb : markSuccessor hn hP ((markSuccessor hn hP).symm (Sum.inr v)) = Sum.inr v :=
    (markSuccessor hn hP).apply_symm_apply (Sum.inr v)
  rcases markSuccessor_position_cases hn hP ((markSuccessor hn hP).symm (Sum.inr v)) with
    ⟨hi, _⟩ | hv
  · rw [hb] at hi
    exact hi.symm
  · rw [hb] at hv
    exact (Sum.inr_ne_inl hv).elim

/-- The mark immediately before the original vertex `i` lies on the edge `i - 1`. -/
theorem markSuccessor_symm_vertex_edge (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (i : ZMod n) :
    (markPosition hn hP.1 ((markSuccessor hn hP).symm (Sum.inl i))).1 = i - 1 := by
  have hb : markSuccessor hn hP ((markSuccessor hn hP).symm (Sum.inl i)) = Sum.inl i :=
    (markSuccessor hn hP).apply_symm_apply (Sum.inl i)
  rcases markSuccessor_position_cases hn hP ((markSuccessor hn hP).symm (Sum.inl i)) with
    ⟨_, ht⟩ | hv
  · rw [hb] at ht
    have h0 : (0 : ℝ) ≤
        (markPosition hn hP.1 ((markSuccessor hn hP).symm (Sum.inl i))).2.val :=
      (markPosition hn hP.1 ((markSuccessor hn hP).symm (Sum.inl i))).2.property.1
    have hz : (markPosition hn hP.1 (Sum.inl i)).2.val = 0 := rfl
    rw [hz] at ht
    exact absurd ht (not_lt.mpr h0)
  · rw [hb] at hv
    have he := Sum.inl.inj hv
    exact eq_sub_iff_add_eq.mpr he.symm

/-- The smoothed segment ending at `a` (from its `ρ_S`-predecessor `b`) is a positive
multiple of the original edge carrying the `ρ`-predecessor of `a`: the incoming arc at a
node is never changed by the reconnection. -/
theorem smoothingSegment_positive_direction_of_succ (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) (S : Finset (Crossing P)) {a b : Mark P}
    (hba : smoothingSuccessor hn hP S b = a) :
    ∃ c : ℝ, 0 < c ∧
      traversalEvaluation P (markPosition hn hP.1 a) -
        traversalEvaluation P (markPosition hn hP.1 b) =
        c • edge P (markPosition hn hP.1 ((markSuccessor hn hP).symm a)).1 := by
  have hsel : selectedMarkPerm S b = (markSuccessor hn hP).symm a := by
    rw [Equiv.eq_symm_apply]
    exact hba
  obtain ⟨c, hc, he⟩ := smoothingSegment_positive_direction hn hP S b
  rw [hba, hsel] at he
  exact ⟨c, hc, he⟩

theorem smoothingSegment_incoming_positive_direction (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) (S : Finset (Crossing P)) (a : Mark P) :
    ∃ c : ℝ, 0 < c ∧
      traversalEvaluation P (markPosition hn hP.1 a) -
        traversalEvaluation P (markPosition hn hP.1 ((smoothingSuccessor hn hP S).symm a)) =
        c • edge P (markPosition hn hP.1 ((markSuccessor hn hP).symm a)).1 :=
  smoothingSegment_positive_direction_of_succ hn hP S
    ((smoothingSuccessor hn hP S).apply_symm_apply a)

/-- The incoming segment at `a` lies on the original edge carrying the `ρ`-predecessor. -/
theorem smoothingSegment_incoming_mem_edgeSegment (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) (S : Finset (Crossing P)) (a : Mark P) {u : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    smoothingSegment hn hP S ((smoothingSuccessor hn hP S).symm a) u ∈
      edgeSegment P (markPosition hn hP.1 ((markSuccessor hn hP).symm a)).1 := by
  have hsel : selectedMarkPerm S ((smoothingSuccessor hn hP S).symm a) =
      (markSuccessor hn hP).symm a := by
    rw [Equiv.eq_symm_apply]
    exact (smoothingSuccessor hn hP S).apply_symm_apply a
  have h := smoothingSegment_mem_edgeSegment hn hP S
    ((smoothingSuccessor hn hP S).symm a) hu0 hu1
  rwa [hsel] at h

/-! ## 3. The two edges of a crossing visit -/

omit [NeZero n] in
theorem visitTwin_snd_ne {P : LabelledTuple n} (v : Visit P) : (visitTwin v).2 ≠ v.2 :=
  Classical.choose_spec (crossing_other_visit v.1 v.2)

omit [NeZero n] in
/-- The twin visit is on the other edge of the crossing. -/
theorem visitTwin_edge_ne {P : LabelledTuple n} (v : Visit P) :
    (visitTwin v).2.val ≠ v.2.val :=
  fun h => visitTwin_snd_ne v (Subtype.ext h)

omit [NeZero n] in
/-- The crossing of `v` is the crossing of the edge of `v` and the edge of its twin:
`v.1` is a crossing "between `E_i` and `E_j`" with `{i, j} = {v.2, (visitTwin v).2}`. -/
theorem visit_crossing_val_eq_pair {P : LabelledTuple n} (v : Visit P) :
    v.1.val = {v.2.val, (visitTwin v).2.val} := by
  symm
  apply Finset.eq_of_subset_of_card_le
  · intro k hk
    rw [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl
    · exact v.2.property
    · exact (visitTwin v).2.property
  · rw [crossing_card_two, Finset.card_pair (visitTwin_edge_ne v).symm]

/-! ## 4. Directions at the corners -/

/-- Incoming segment at any crossing visit `v` (selected or not): its direction is a
positive multiple of `ℓ_{v.2}`, the direction of the edge visited by `v`. -/
theorem visit_incoming_direction (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) (v : Visit P) :
    ∃ c : ℝ, 0 < c ∧
      traversalEvaluation P (markPosition hn hP.1 (Sum.inr v)) -
        traversalEvaluation P
          (markPosition hn hP.1 ((smoothingSuccessor hn hP S).symm (Sum.inr v))) =
        c • edge P v.2.val := by
  obtain ⟨c, hc, he⟩ := smoothingSegment_incoming_positive_direction hn hP S (Sum.inr v)
  rw [markSuccessor_symm_visit_edge hn hP v] at he
  exact ⟨c, hc, he⟩

theorem visit_incoming_mem_edgeSegment (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) (v : Visit P) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    smoothingSegment hn hP S ((smoothingSuccessor hn hP S).symm (Sum.inr v)) u ∈
      edgeSegment P v.2.val := by
  have h := smoothingSegment_incoming_mem_edgeSegment hn hP S (Sum.inr v) hu0 hu1
  rwa [markSuccessor_symm_visit_edge hn hP v] at h

/-- Outgoing segment at a selected visit `v`: it leaves along the twin's edge, with
direction a positive multiple of `ℓ_{(visitTwin v).2}`. -/
theorem selected_visit_outgoing_direction (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) (S : Finset (Crossing P)) (v : Visit P) (hv : v.1 ∈ S) :
    ∃ c : ℝ, 0 < c ∧
      traversalEvaluation P (markPosition hn hP.1 (smoothingSuccessor hn hP S (Sum.inr v))) -
        traversalEvaluation P (markPosition hn hP.1 (Sum.inr v)) =
        c • edge P (visitTwin v).2.val := by
  obtain ⟨c, hc, he⟩ := smoothingSegment_positive_direction hn hP S (Sum.inr v)
  rw [selectedMarkPerm_visit, selectedVisitTwin_of_mem S v hv] at he
  exact ⟨c, hc, he⟩

theorem selected_visit_outgoing_mem_edgeSegment (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) (S : Finset (Crossing P)) (v : Visit P) (hv : v.1 ∈ S)
    {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    smoothingSegment hn hP S (Sum.inr v) u ∈ edgeSegment P (visitTwin v).2.val := by
  have h := smoothingSegment_mem_edgeSegment hn hP S (Sum.inr v) hu0 hu1
  rw [selectedMarkPerm_visit, selectedVisitTwin_of_mem S v hv] at h
  exact h

/-- Outgoing segment at an unselected visit: it continues along the visit's own edge. -/
theorem unselected_visit_outgoing_direction (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) (S : Finset (Crossing P)) (v : Visit P) (hv : v.1 ∉ S) :
    ∃ c : ℝ, 0 < c ∧
      traversalEvaluation P (markPosition hn hP.1 (smoothingSuccessor hn hP S (Sum.inr v))) -
        traversalEvaluation P (markPosition hn hP.1 (Sum.inr v)) =
        c • edge P v.2.val := by
  obtain ⟨c, hc, he⟩ := smoothingSegment_positive_direction hn hP S (Sum.inr v)
  rw [selectedMarkPerm_visit, selectedVisitTwin_of_not_mem S v hv] at he
  exact ⟨c, hc, he⟩

/-- Outgoing segment at an original vertex `i`: a positive multiple of `ℓ_i`. -/
theorem vertex_outgoing_direction (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) (i : ZMod n) :
    ∃ c : ℝ, 0 < c ∧
      traversalEvaluation P (markPosition hn hP.1 (smoothingSuccessor hn hP S (Sum.inl i))) -
        P i = c • edge P i := by
  obtain ⟨c, hc, he⟩ := smoothingSegment_positive_direction hn hP S (Sum.inl i)
  rw [selectedMarkPerm_vertex, markPosition_evaluation_vertex] at he
  exact ⟨c, hc, he⟩

theorem vertex_outgoing_mem_edgeSegment (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) (i : ZMod n) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    smoothingSegment hn hP S (Sum.inl i) u ∈ edgeSegment P i := by
  have h := smoothingSegment_mem_edgeSegment hn hP S (Sum.inl i) hu0 hu1
  rwa [selectedMarkPerm_vertex] at h

/-- Incoming segment at an original vertex `i`: a positive multiple of `ℓ_{i-1}`. -/
theorem vertex_incoming_direction (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) (i : ZMod n) :
    ∃ c : ℝ, 0 < c ∧
      P i - traversalEvaluation P
          (markPosition hn hP.1 ((smoothingSuccessor hn hP S).symm (Sum.inl i))) =
        c • edge P (i - 1) := by
  obtain ⟨c, hc, he⟩ := smoothingSegment_incoming_positive_direction hn hP S (Sum.inl i)
  rw [markSuccessor_symm_vertex_edge hn hP i, markPosition_evaluation_vertex] at he
  exact ⟨c, hc, he⟩

theorem vertex_incoming_mem_edgeSegment (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) (i : ZMod n) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    smoothingSegment hn hP S ((smoothingSuccessor hn hP S).symm (Sum.inl i)) u ∈
      edgeSegment P (i - 1) := by
  have h := smoothingSegment_incoming_mem_edgeSegment hn hP S (Sum.inl i) hu0 hu1
  rwa [markSuccessor_symm_vertex_edge hn hP i] at h

/-! ## 5. Corner statements for a carrier `Q` -/

/-- `def:smoothing`, smoothing corners: let `v` be a selected visit (`v.1 ∈ S`) owned by
the carrier `Q = q`. Then `v.1` is the crossing of the edges `E_{v.2}` and
`E_{(visitTwin v).2}` (distinct edges); the incoming segment of `Q` at this corner (from
`ρ_S⁻¹ v` to `v`, both owned by `Q`) lies on `E_{v.2}` and its direction is a positive
multiple of `ℓ_{v.2}`; the outgoing segment of `Q` (from `v` to `ρ_S v = ρ(visitTwin v)`,
both owned by `Q`) lies on `E_{(visitTwin v).2}` and its direction is a positive multiple of
`ℓ_{(visitTwin v).2}`. So `Q` "arrives along one of `ℓ_i, ℓ_j` and leaves along the other". -/
theorem smoothing_corner_directions (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) (q : Component hn hP S) (v : Visit P) (hv : v.1 ∈ S)
    (hq : owner hn hP S (Sum.inr v) = q) :
    (v.1.val = {v.2.val, (visitTwin v).2.val} ∧ v.2.val ≠ (visitTwin v).2.val) ∧
    (owner hn hP S ((smoothingSuccessor hn hP S).symm (Sum.inr v)) = q ∧
      (∀ u : ℝ, 0 ≤ u → u ≤ 1 →
        smoothingSegment hn hP S ((smoothingSuccessor hn hP S).symm (Sum.inr v)) u ∈
          edgeSegment P v.2.val) ∧
      ∃ c : ℝ, 0 < c ∧
        traversalEvaluation P (markPosition hn hP.1 (Sum.inr v)) -
          traversalEvaluation P
            (markPosition hn hP.1 ((smoothingSuccessor hn hP S).symm (Sum.inr v))) =
          c • edge P v.2.val) ∧
    (smoothingSuccessor hn hP S (Sum.inr v) = markSuccessor hn hP (Sum.inr (visitTwin v)) ∧
      owner hn hP S (smoothingSuccessor hn hP S (Sum.inr v)) = q ∧
      (∀ u : ℝ, 0 ≤ u → u ≤ 1 →
        smoothingSegment hn hP S (Sum.inr v) u ∈ edgeSegment P (visitTwin v).2.val) ∧
      ∃ c : ℝ, 0 < c ∧
        traversalEvaluation P
            (markPosition hn hP.1 (smoothingSuccessor hn hP S (Sum.inr v))) -
          traversalEvaluation P (markPosition hn hP.1 (Sum.inr v)) =
          c • edge P (visitTwin v).2.val) := by
  refine ⟨⟨visit_crossing_val_eq_pair v, (visitTwin_edge_ne v).symm⟩, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · rw [owner_predecessor]
    exact hq
  · intro u hu0 hu1
    exact visit_incoming_mem_edgeSegment hn hP S v hu0 hu1
  · exact visit_incoming_direction hn hP S v
  · exact smoothingSuccessor_visit_of_mem hn hP S v hv
  · rw [owner_successor]
    exact hq
  · intro u hu0 hu1
    exact selected_visit_outgoing_mem_edgeSegment hn hP S v hv hu0 hu1
  · exact selected_visit_outgoing_direction hn hP S v hv

/-- `def:smoothing`, original vertices: let the original vertex mark `i` be owned by the
carrier `Q = q`. Its incoming segment (from `ρ_S⁻¹ i`, owned by `Q`) lies on `E_{i-1}` with
direction a positive multiple of `ℓ_{i-1}`, and its outgoing segment (to `ρ_S i = ρ i`,
owned by `Q`) lies on `E_i` with direction a positive multiple of `ℓ_i`. -/
theorem vertex_corner_directions (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) (q : Component hn hP S) (i : ZMod n)
    (hq : owner hn hP S (Sum.inl i) = q) :
    (owner hn hP S ((smoothingSuccessor hn hP S).symm (Sum.inl i)) = q ∧
      (∀ u : ℝ, 0 ≤ u → u ≤ 1 →
        smoothingSegment hn hP S ((smoothingSuccessor hn hP S).symm (Sum.inl i)) u ∈
          edgeSegment P (i - 1)) ∧
      ∃ c : ℝ, 0 < c ∧
        P i - traversalEvaluation P
            (markPosition hn hP.1 ((smoothingSuccessor hn hP S).symm (Sum.inl i))) =
          c • edge P (i - 1)) ∧
    (smoothingSuccessor hn hP S (Sum.inl i) = markSuccessor hn hP (Sum.inl i) ∧
      owner hn hP S (smoothingSuccessor hn hP S (Sum.inl i)) = q ∧
      (∀ u : ℝ, 0 ≤ u → u ≤ 1 →
        smoothingSegment hn hP S (Sum.inl i) u ∈ edgeSegment P i) ∧
      ∃ c : ℝ, 0 < c ∧
        traversalEvaluation P
            (markPosition hn hP.1 (smoothingSuccessor hn hP S (Sum.inl i))) - P i =
          c • edge P i) := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · rw [owner_predecessor]
    exact hq
  · intro u hu0 hu1
    exact vertex_incoming_mem_edgeSegment hn hP S i hu0 hu1
  · exact vertex_incoming_direction hn hP S i
  · exact smoothingSuccessor_vertex hn hP S i
  · rw [owner_successor]
    exact hq
  · intro u hu0 hu1
    exact vertex_outgoing_mem_edgeSegment hn hP S i hu0 hu1
  · exact vertex_outgoing_direction hn hP S i

/-! ## 6. Unselected crossings interlacing no element of `S` -/

omit [NeZero n] in
/-- Adjoining to an independent `S` an unselected crossing that interlaces no element of
`S` (an element of `U(S)`) keeps it independent. -/
theorem insert_unselected_mem_independentSupports (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) {S : Finset (Crossing P)} (hS : S ∈ independentSupports hn hP)
    {x : Crossing P} (hx : x ∈ supportUnselected hn hP S) :
    insert x S ∈ independentSupports hn hP := by
  rw [mem_supportUnselected] at hx
  obtain ⟨_, hxN⟩ := hx
  rw [mem_supportNeighbors] at hxN
  rw [mem_independentSupports_iff] at hS ⊢
  intro a ha b hb hab hI
  rw [Finset.mem_insert] at ha hb
  rcases ha with rfl | ha
  · rcases hb with rfl | hb
    · exact hab rfl
    · exact hxN ⟨b, hb, hI⟩
  · rcases hb with rfl | hb
    · exact hxN ⟨a, ha, interlaces_symm hn hP hI⟩
    · exact hS a ha b hb hab hI

/-- `lem:carriers` (iii), second half, in twin form: for `S` independent and `x ∈ U(S)`,
a visit of `x` and its twin have the same owner. -/
theorem unselected_nonneighbor_visit_owner_eq_twin (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) {S : Finset (Crossing P)} (hS : S ∈ independentSupports hn hP)
    {x : Crossing P} (hx : x ∈ supportUnselected hn hP S) (v : Visit P) (hv : v.1 = x) :
    owner hn hP S (Sum.inr v) = owner hn hP S (Sum.inr (visitTwin v)) := by
  have hins := insert_unselected_mem_independentSupports hn hP hS hx
  have hxS : x ∉ S := ((mem_supportUnselected hn hP S x).mp hx).1
  refine independent_remaining_pair_owners hn hP hins S (Finset.subset_insert x S) v ?_ ?_
  · rw [hv]
    exact Finset.mem_insert_self x S
  · rw [hv]
    exact hxS

/-- `lem:carriers` (iii): "an unselected crossing interlacing no element of `S` has both
visits on one carrier". -/
theorem unselected_nonneighbor_both_visits_one_carrier (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) {S : Finset (Crossing P)} (hS : S ∈ independentSupports hn hP)
    {x : Crossing P} (hx : x ∈ supportUnselected hn hP S) (v w : Visit P)
    (hv : v.1 = x) (hw : w.1 = x) :
    owner hn hP S (Sum.inr v) = owner hn hP S (Sum.inr w) := by
  rcases visit_eq_or_twin v w (hw.trans hv.symm) with rfl | rfl
  · rfl
  · exact unselected_nonneighbor_visit_owner_eq_twin hn hP hS hx v hv

/-- An element of `U(S)` is a crossing of the carrier owning either of its visits. -/
theorem unselected_nonneighbor_mem_carrierCrossings (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) {S : Finset (Crossing P)} (hS : S ∈ independentSupports hn hP)
    {x : Crossing P} (hx : x ∈ supportUnselected hn hP S) (v : Visit P) (hv : v.1 = x) :
    x ∈ carrierCrossings hn hP S (owner hn hP S (Sum.inr v)) := by
  rw [mem_carrierCrossings]
  refine ⟨((mem_supportUnselected hn hP S x).mp hx).1, ?_⟩
  intro w hw
  exact unselected_nonneighbor_both_visits_one_carrier hn hP hS hx w v hw hv

/-- An element of `U(S)` is a crossing of exactly one carrier. -/
theorem unselected_nonneighbor_exists_unique_carrier (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) {S : Finset (Crossing P)} (hS : S ∈ independentSupports hn hP)
    {x : Crossing P} (hx : x ∈ supportUnselected hn hP S) :
    ∃! q : Component hn hP S, x ∈ carrierCrossings hn hP S q := by
  obtain ⟨i, _, _⟩ := crossing_visits_exist x
  refine ⟨owner hn hP S (Sum.inr ⟨x, i⟩),
    unselected_nonneighbor_mem_carrierCrossings hn hP hS hx ⟨x, i⟩ rfl, ?_⟩
  intro q hq
  exact (((mem_carrierCrossings hn hP S q x).mp hq).2 ⟨x, i⟩ rfl).symm

/-- Every element of `U(S)` is a crossing of some carrier. -/
theorem supportUnselected_subset_biUnion_carrierCrossings (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) {S : Finset (Crossing P)} (hS : S ∈ independentSupports hn hP) :
    supportUnselected hn hP S ⊆
      (Finset.univ : Finset (Component hn hP S)).biUnion (carrierCrossings hn hP S) := by
  intro x hx
  rw [Finset.mem_biUnion]
  obtain ⟨q, hq, _⟩ := unselected_nonneighbor_exists_unique_carrier hn hP hS hx
  exact ⟨q, Finset.mem_univ q, hq⟩

end
end SM.Carrier
