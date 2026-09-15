import SM.CarrierCrossings
import SM.CarrierNeighborSeparation
import SM.SmoothingDefinition
import SM.GeometricParameters

/-! Towards lem:carriers (ii) (sm-3-statesum.tex:54): block compression, the corner polygon of a carrier, its regularity and turn signs, at least three corners. Written 2026-09-13 by a Claude Code prover subagent of the pod
executor (workflow prove-carriers-lemma / prove:carriers-ii), checked with `lake env lean` (sorry-free, standard axioms) and
ported verbatim from work/drafts/CarriersCornerPolygon.lean (only this header added and #print lines removed). -/

/-! # lem:carriers clause (ii): the compressed corner polygon of a carrier

Source: reference/SM/sm-3-statesum.tex, lem:carriers (lines 54-95), clause (ii)
(lines 72-77) and its proof (lines 96-240), in particular the paragraph
"Nonzero segments and corner signs" (lines 182-231).

Encoding (the finite successor model of the source proof, namespace `SM.Carrier`):
`ρ = markSuccessor hn hP`, `ρ_S = smoothingSuccessor hn hP S`, carriers `Component hn hP S`,
ownership `owner hn hP S`. The marks owned by the carrier `q` in the cyclic order inherited
from the original traversal circle form `componentMarkList hn hP S q`; its true corners
(original vertices and selected visits, `IsTrueCorner S`) form `ccpCornerList hn hP S q`, whose
cyclic closure is `componentCornerCycle hn hP S q`. The corner polygon of `q` is the labelled
tuple `ccpCornerPolygon hn hP S q : LabelledTuple k`, `k = ccpCornerCount hn hP S q`, whose
`j`-th vertex is the plane point `traversalEvaluation P (markPosition hn hP.1 c_j)` of the
`j`-th corner mark `c_j = ccpCornerMark hn hP S q j`.

All helper names carry the prefix `ccp` (corner polygon) to avoid collisions with the lane. -/

namespace SM.Carrier

noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ} [NeZero n]

/-! ## 0. The outgoing slot of a mark and the incoming edge at a mark -/

/-- The original traversal position of the outgoing slot of `a` under the reconnection:
`a` itself if unselected, its twin if selected. The segment leaving `a` lies on the edge
`(ccpOutSlot a).1` and starts at parameter `(ccpOutSlot a).2`. -/
def ccpOutSlot (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P) (S : Finset (Crossing P))
    (a : Mark P) : TraversalPoint n :=
  markPosition hn hP.1 (selectedMarkPerm S a)

/-- The original edge carrying the incoming segment at `b` (the edge of the `ρ`-predecessor
of `b`; the incoming arc at a node is never changed by the reconnection). -/
def ccpInEdge (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P) (b : Mark P) : ZMod n :=
  (markPosition hn hP.1 ((markSuccessor hn hP).symm b)).1

omit [NeZero n] in
theorem ccpOutSlot_vertex (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) (i : ZMod n) :
    (ccpOutSlot hn hP S (Sum.inl i)).1 = i := rfl

theorem ccpOutSlot_selected (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) (v : Visit P) (hv : v.1 ∈ S) :
    (ccpOutSlot hn hP S (Sum.inr v)).1 = (visitTwin v).2.val := by
  unfold ccpOutSlot
  rw [selectedMarkPerm_visit, selectedVisitTwin_of_mem S v hv]
  rfl

theorem ccpOutSlot_unselected (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) (v : Visit P) (hv : v.1 ∉ S) :
    ccpOutSlot hn hP S (Sum.inr v) = visitPosition hn hP.1 v := by
  unfold ccpOutSlot
  rw [selectedMarkPerm_visit, selectedVisitTwin_of_not_mem S v hv]
  rfl

theorem ccpInEdge_vertex (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P) (i : ZMod n) :
    ccpInEdge hn hP (Sum.inl i) = i - 1 :=
  markSuccessor_symm_vertex_edge hn hP i

theorem ccpInEdge_visit (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P) (v : Visit P) :
    ccpInEdge hn hP (Sum.inr v) = v.2.val :=
  markSuccessor_symm_visit_edge hn hP v

/-- If `ρ_S x = b` then the outgoing slot of `x` is the `ρ`-predecessor of `b`, so the
outgoing edge of `x` is the incoming edge of `b`. -/
theorem ccpOutSlot_eq_of_succ (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) {x b : Mark P} (hxb : smoothingSuccessor hn hP S x = b) :
    (ccpOutSlot hn hP S x).1 = ccpInEdge hn hP b := by
  unfold ccpOutSlot ccpInEdge
  have hsel : selectedMarkPerm S x = (markSuccessor hn hP).symm b := by
    rw [Equiv.eq_symm_apply]
    exact hxb
  rw [hsel]

/-- The plane point of a mark, as the start of its outgoing slot. -/
theorem ccp_evaluation_eq_outSlot (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) (a : Mark P) :
    traversalEvaluation P (markPosition hn hP.1 a) =
      edgePoint P (ccpOutSlot hn hP S a).1 (ccpOutSlot hn hP S a).2.val :=
  (selectedMarkPerm_evaluation hn hP.1 S a).symm

/-- `smoothingSegment_subsegment_data` restated with the outgoing slot. -/
theorem ccp_subsegment_data (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) (a : Mark P) :
    ∃ t : ℝ, (ccpOutSlot hn hP S a).2.val < t ∧ t ≤ 1 ∧
      traversalEvaluation P (markPosition hn hP.1 (smoothingSuccessor hn hP S a)) =
        edgePoint P (ccpOutSlot hn hP S a).1 t ∧
      ∀ u : ℝ, smoothingSegment hn hP S a u =
        edgePoint P (ccpOutSlot hn hP S a).1
          ((ccpOutSlot hn hP S a).2.val + u * (t - (ccpOutSlot hn hP S a).2.val)) := by
  obtain ⟨t, hst, ht1, _, hend, hform⟩ := smoothingSegment_subsegment_data hn hP S a
  exact ⟨t, hst, ht1, hend, hform⟩

/-- Re-proof of the previous executor's `smoothingSuccessor_incoming_visit_position`
(work/checks/CarrierUnselectedDirection.body.lean, not in the ported lane): an incoming segment
ending at a crossing visit starts earlier on that visit's own edge. -/
theorem ccp_incoming_visit_position (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) (S : Finset (Crossing P)) (x : Mark P) (v : Visit P)
    (hx : smoothingSuccessor hn hP S x = Sum.inr v) :
    (ccpOutSlot hn hP S x).1 = v.2.val ∧
      (ccpOutSlot hn hP S x).2.val < visitParameter v := by
  unfold ccpOutSlot
  have he : markSuccessor hn hP (selectedMarkPerm S x) = Sum.inr v := hx
  rcases markSuccessor_position_cases hn hP (selectedMarkPerm S x) with ⟨hi, ht⟩ | hv
  · constructor
    · simpa only [he, markPosition_visit, visitPosition_edge] using hi.symm
    · simpa only [he, markPosition_visit, visitPosition_parameter] using ht
  · have hbad := he.symm.trans hv
    cases hbad

/-- A mark that is not a true corner is an unselected crossing visit. -/
theorem ccp_not_trueCorner {P : LabelledTuple n} (S : Finset (Crossing P)) {a : Mark P}
    (ha : ¬ IsTrueCorner S a) : ∃ v : Visit P, a = Sum.inr v ∧ v.1 ∉ S := by
  cases a with
  | inl i => exact (ha (isTrueCorner_vertex S i)).elim
  | inr v => exact ⟨v, rfl, ha⟩

/-! ## 1. Real-interval packet: the image of an affine reparametrization -/

/-- `u ↦ s + u (t - s)` maps `[0, 1]` onto `[s, t]` when `s < t`. -/
theorem ccp_image_affine_unit {s t : ℝ} (hst : s < t) :
    (fun u : ℝ => s + u * (t - s)) '' Set.Icc 0 1 = Set.Icc s t := by
  have h := Set.image_affine_Icc' (sub_pos.mpr hst) s 0 1
  have hf : (fun u : ℝ => s + u * (t - s)) = fun x : ℝ => (t - s) * x + s := by
    funext u
    ring
  rw [hf, h]
  congr 1 <;> ring

/-- The image of the outgoing smoothing segment of `a` is the parameter interval on its edge
between its outgoing slot parameter and the endpoint parameter `t`. -/
theorem ccp_smoothingSegment_image (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) (a : Mark P) {e : ZMod n} {s t : ℝ} (hst : s < t)
    (hf : ∀ u : ℝ, smoothingSegment hn hP S a u = edgePoint P e (s + u * (t - s))) :
    smoothingSegment hn hP S a '' Set.Icc 0 1 = edgePoint P e '' Set.Icc s t := by
  have hcomp : smoothingSegment hn hP S a = edgePoint P e ∘ (fun u : ℝ => s + u * (t - s)) :=
    funext hf
  rw [hcomp, Set.image_comp, ccp_image_affine_unit hst]

/-! ## 2. Block compression along `ρ_S` -/

/-- **Block compression.** Let `a` be a mark and `m ≥ 1` such that the marks
`ρ_S a, …, ρ_S^{m-1} a` are not true corners (hence unselected visits). Let `e` and `s` be the
edge and parameter of the outgoing slot of `a`. Then every segment of the block lies on the one
original edge `e`, the endpoint `ρ_S^m a` is the point of parameter `t > s` on `e`, and the union
of the `m` segment images is exactly the straight segment `edgePoint P e '' [s, t]`: omitting the
unselected marks joins the positive subsegments of one original edge in the same direction. -/
theorem ccp_block_compression (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) (a : Mark P) (m : ℕ) (hm : 1 ≤ m)
    (hmid : ∀ r, 1 ≤ r → r < m → ¬ IsTrueCorner S ((smoothingSuccessor hn hP S ^ r) a)) :
    (∀ r < m, (ccpOutSlot hn hP S ((smoothingSuccessor hn hP S ^ r) a)).1 =
      (ccpOutSlot hn hP S a).1) ∧
    ∃ t : ℝ, (ccpOutSlot hn hP S a).2.val < t ∧ t ≤ 1 ∧
      traversalEvaluation P (markPosition hn hP.1 ((smoothingSuccessor hn hP S ^ m) a)) =
        edgePoint P (ccpOutSlot hn hP S a).1 t ∧
      (⋃ r < m, smoothingSegment hn hP S ((smoothingSuccessor hn hP S ^ r) a) '' Set.Icc 0 1) =
        edgePoint P (ccpOutSlot hn hP S a).1 '' Set.Icc (ccpOutSlot hn hP S a).2.val t := by
  induction m with
  | zero => omega
  | succ m ih =>
    rcases Nat.eq_zero_or_pos m with hm0 | hmpos
    · -- base case `m + 1 = 1`
      subst hm0
      obtain ⟨t, hst, ht1, hend, hform⟩ := ccp_subsegment_data hn hP S a
      refine ⟨?_, t, hst, ht1, ?_, ?_⟩
      · intro r hr
        have hr0 : r = 0 := by omega
        subst hr0
        rw [pow_zero, Equiv.Perm.one_apply]
      · rw [zero_add, pow_one]
        exact hend
      · have hU : (⋃ r < 0 + 1,
            smoothingSegment hn hP S ((smoothingSuccessor hn hP S ^ r) a) '' Set.Icc (0:ℝ) 1) =
            smoothingSegment hn hP S a '' Set.Icc 0 1 := by
          rw [Set.biUnion_lt_succ]
          simp
        rw [hU]
        exact ccp_smoothingSegment_image hn hP S a hst hform
    · -- inductive step `m ≥ 1`
      have hmid' : ∀ r, 1 ≤ r → r < m →
          ¬ IsTrueCorner S ((smoothingSuccessor hn hP S ^ r) a) :=
        fun r h1 h2 => hmid r h1 (by omega)
      obtain ⟨hedges, t, hst, ht1, hend, himage⟩ := ih hmpos hmid'
      have hedge : edge P (ccpOutSlot hn hP S a).1 ≠ 0 := (g1 hn P hP.1).2.1 _
      -- the mark `x_m = ρ_S^m a` is an unselected visit
      obtain ⟨v, hxv, hvS⟩ := ccp_not_trueCorner S (hmid m hmpos (Nat.lt_succ_self m))
      -- `ρ_S x_{m-1} = x_m`
      have hprev : smoothingSuccessor hn hP S ((smoothingSuccessor hn hP S ^ (m - 1)) a) =
          (smoothingSuccessor hn hP S ^ m) a := by
        rw [← Equiv.Perm.mul_apply, ← pow_succ']
        congr 2
        omega
      have hin := ccp_incoming_visit_position hn hP S _ v (hprev.trans hxv)
      have hedge_prev : (ccpOutSlot hn hP S ((smoothingSuccessor hn hP S ^ (m - 1)) a)).1 =
          (ccpOutSlot hn hP S a).1 :=
        hedges (m - 1) (by omega)
      have hev : v.2.val = (ccpOutSlot hn hP S a).1 := hin.1.symm.trans hedge_prev
      have hslot : ccpOutSlot hn hP S ((smoothingSuccessor hn hP S ^ m) a) =
          visitPosition hn hP.1 v := by
        rw [hxv]
        exact ccpOutSlot_unselected hn hP S v hvS
      -- the endpoint parameter `t` of the block so far is the visit parameter of `v`
      have hxeval : traversalEvaluation P (markPosition hn hP.1 ((smoothingSuccessor hn hP S ^ m) a)) =
          edgePoint P (ccpOutSlot hn hP S a).1 (visitParameter v) := by
        rw [hxv, markPosition_visit]
        change edgePoint P v.2.val (visitParameter v) = _
        rw [hev]
      have htv : t = visitParameter v :=
        edgePoint_injective hedge (hend.symm.trans hxeval)
      -- the outgoing segment of `x_m`
      obtain ⟨t', hst', ht1', hend', hform'⟩ :=
        ccp_subsegment_data hn hP S ((smoothingSuccessor hn hP S ^ m) a)
      have hslot1 : (ccpOutSlot hn hP S ((smoothingSuccessor hn hP S ^ m) a)).1 =
          (ccpOutSlot hn hP S a).1 := by
        rw [hslot]
        exact hev
      have hslot2 : (ccpOutSlot hn hP S ((smoothingSuccessor hn hP S ^ m) a)).2.val = t := by
        rw [hslot, htv]
        rfl
      rw [hslot2] at hst'
      rw [hslot1] at hend'
      simp only [hslot1, hslot2] at hform'
      refine ⟨?_, t', lt_trans hst hst', ht1', ?_, ?_⟩
      · intro r hr
        rcases Nat.lt_succ_iff_lt_or_eq.mp hr with hr' | hr'
        · exact hedges r hr'
        · rw [hr']
          exact hslot1
      · rw [pow_succ', Equiv.Perm.mul_apply]
        exact hend'
      · rw [Set.biUnion_lt_succ, himage,
          ccp_smoothingSegment_image hn hP S _ hst' hform', ← Set.image_union,
          Set.Icc_union_Icc_eq_Icc hst.le hst'.le]

/-! ## 3. From a true corner to the next true corner along `ρ_S` -/

omit [NeZero n] in
/-- Generic closed-list adjacency: if a permutation `f` agrees with the cyclic permutation of a
duplicate-free list `a :: R` on that list, then the iterates of `f` at `a` read off the closed
list `(a :: R) ++ [a]`, including the closing return to `a`. -/
theorem ccp_pow_apply_closed_list {α : Type*} [DecidableEq α] (f : Equiv.Perm α) (a : α)
    (R : List α) (hN : (a :: R).Nodup)
    (hEq : Set.EqOn (a :: R).formPerm f {m | m ∈ a :: R}) :
    ∀ i (hi : i < R.length + 2),
      (f ^ i) a = ((a :: R) ++ [a])[i]'(by simp; omega) := by
  intro i
  induction i with
  | zero =>
    intro _
    simp
  | succ i ih =>
    intro hi
    have hi' : i < (a :: R).length := by simp only [List.length_cons]; omega
    have hmem : (a :: R)[i] ∈ a :: R := List.getElem_mem hi'
    rw [pow_succ', Equiv.Perm.mul_apply, ih (by omega),
      List.getElem_append_left hi', ← hEq hmem, List.formPerm_apply_getElem _ hN i hi']
    simp only [List.length_cons] at *
    rcases Nat.lt_or_ge (i + 1) (R.length + 1) with hlt | hge
    · simp only [Nat.mod_eq_of_lt hlt]
      exact (List.getElem_append_left (by simp only [List.length_cons]; omega)).symm
    · have heq : i + 1 = R.length + 1 := by omega
      simp only [heq, Nat.mod_self]
      simp

/-- **Corner-to-corner chain.** For a true corner `a` of the carrier `q` (with `S`
independent), the next corner of the inherited corner cycle is reached from `a` in `m ≥ 1`
steps of `ρ_S`, and every intermediate mark is not a true corner. Derived from the first
retained block of `CarrierActualCornerBlock`; no block is assumed. -/
theorem ccp_corner_chain (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    {S : Finset (Crossing P)} (hS : S ∈ independentSupports hn hP)
    (q : Component hn hP S) (a : Mark P) (ha : owner hn hP S a = q) (hac : IsTrueCorner S a) :
    ∃ m : ℕ, 1 ≤ m ∧
      (smoothingSuccessor hn hP S ^ m) a =
        (componentCornerCycle hn hP S q).next (componentCornerCycle_nodup hn hP S q) a
          ((mem_componentCornerCycle hn hP S q a).mpr ⟨ha, hac⟩) ∧
      ∀ r, 1 ≤ r → r < m → ¬ IsTrueCorner S ((smoothingSuccessor hn hP S ^ r) a) := by
  obtain ⟨k, R, M, b, B, hrot, hsplit, hnot, hbc, hbo, hprefix, hnext, heqOn⟩ :=
    component_first_trueCorner_block hn hP hS q a ha hac
  have hN : (a :: R).Nodup := by
    rw [← hrot]
    exact List.nodup_rotate.mpr (componentMarkList_data hn hP S q).1
  have hlen : M.length + 2 ≤ R.length + 2 := by
    have := hprefix.length_le
    simp at this
    omega
  have hpow : ∀ i (hi : i < M.length + 2),
      (smoothingSuccessor hn hP S ^ i) a = (a :: (M ++ [b]))[i]'(by simp; omega) := by
    intro i hi
    rw [ccp_pow_apply_closed_list _ a R hN heqOn i (by omega)]
    exact (hprefix.getElem (by simp; omega)).symm
  refine ⟨M.length + 1, by omega, ?_, ?_⟩
  · rw [hnext, hpow (M.length + 1) (by omega)]
    simp
  · intro r hr1 hrm
    rw [hpow r (by omega)]
    obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
    have hr' : r' < M.length := by omega
    rw [List.getElem_cons_succ, List.getElem_append_left hr']
    exact hnot _ (List.getElem_mem hr')

/-! ## 4. The corner list and the corner polygon of a carrier -/

/-- The true corners owned by `q`, in the cyclic order inherited from the original traversal
circle (a linear representative cut at label zero); its cyclic closure is
`componentCornerCycle hn hP S q`. -/
def ccpCornerList (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) (q : Component hn hP S) : List (Mark P) :=
  (componentMarkList hn hP S q).filter (fun a => decide (IsTrueCorner S a))

theorem ccpCornerList_coe (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) (q : Component hn hP S) :
    (ccpCornerList hn hP S q : Cycle (Mark P)) = componentCornerCycle hn hP S q := rfl

theorem ccpCornerList_nodup (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) (q : Component hn hP S) : (ccpCornerList hn hP S q).Nodup :=
  (componentMarkList_data hn hP S q).1.filter _

theorem mem_ccpCornerList (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) (q : Component hn hP S) (a : Mark P) :
    a ∈ ccpCornerList hn hP S q ↔ owner hn hP S a = q ∧ IsTrueCorner S a := by
  unfold ccpCornerList
  rw [List.mem_filter, (componentMarkList_data hn hP S q).2.2.2 a, decide_eq_true_eq]

theorem ccpCornerList_length_pos (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) (q : Component hn hP S) : 0 < (ccpCornerList hn hP S q).length := by
  obtain ⟨a, ha, hac⟩ := component_has_trueCorner hn hP S q
  exact List.length_pos_of_mem ((mem_ccpCornerList hn hP S q a).mpr ⟨ha, hac⟩)

/-- `k`, the number of corners of the carrier `q`. -/
def ccpCornerCount (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) (q : Component hn hP S) : ℕ :=
  (ccpCornerList hn hP S q).length

instance ccpCornerCount_neZero (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) (q : Component hn hP S) : NeZero (ccpCornerCount hn hP S q) :=
  ⟨(ccpCornerList_length_pos hn hP S q).ne'⟩

/-- The `j`-th corner mark of `q`, `j : ZMod k`, in inherited cyclic order. -/
def ccpCornerMark (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) (q : Component hn hP S) (j : ZMod (ccpCornerCount hn hP S q)) :
    Mark P :=
  (ccpCornerList hn hP S q)[j.val]'(ZMod.val_lt j)

/-- **The corner polygon of the carrier `q`**: the labelled `k`-tuple of the plane points of its
true corners in inherited cyclic order. -/
def ccpCornerPolygon (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) (q : Component hn hP S) : LabelledTuple (ccpCornerCount hn hP S q) :=
  fun j => traversalEvaluation P (markPosition hn hP.1 (ccpCornerMark hn hP S q j))

theorem ccpCornerPolygon_apply (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) (q : Component hn hP S) (j : ZMod (ccpCornerCount hn hP S q)) :
    ccpCornerPolygon hn hP S q j =
      traversalEvaluation P (markPosition hn hP.1 (ccpCornerMark hn hP S q j)) := rfl

theorem ccpCornerMark_mem (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) (q : Component hn hP S) (j : ZMod (ccpCornerCount hn hP S q)) :
    owner hn hP S (ccpCornerMark hn hP S q j) = q ∧ IsTrueCorner S (ccpCornerMark hn hP S q j) :=
  (mem_ccpCornerList hn hP S q _).mp (List.getElem_mem (ZMod.val_lt j))

theorem ccpCornerMark_owner (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) (q : Component hn hP S) (j : ZMod (ccpCornerCount hn hP S q)) :
    owner hn hP S (ccpCornerMark hn hP S q j) = q := (ccpCornerMark_mem hn hP S q j).1

theorem ccpCornerMark_isTrueCorner (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) (q : Component hn hP S) (j : ZMod (ccpCornerCount hn hP S q)) :
    IsTrueCorner S (ccpCornerMark hn hP S q j) := (ccpCornerMark_mem hn hP S q j).2

theorem ccpCornerMark_mem_cornerCycle (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) (q : Component hn hP S) (j : ZMod (ccpCornerCount hn hP S q)) :
    ccpCornerMark hn hP S q j ∈ componentCornerCycle hn hP S q :=
  (mem_componentCornerCycle hn hP S q _).mpr (ccpCornerMark_mem hn hP S q j)

theorem ccpCornerMark_injective (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) (q : Component hn hP S) :
    Function.Injective (ccpCornerMark hn hP S q) := by
  intro i j hij
  unfold ccpCornerMark at hij
  exact ZMod.val_injective _ ((ccpCornerList_nodup hn hP S q).getElem_inj_iff.mp hij)

/-- Every true corner owned by `q` is some corner mark `c_j`. -/
theorem ccpCornerMark_exists (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) (q : Component hn hP S) (a : Mark P)
    (ha : owner hn hP S a = q) (hac : IsTrueCorner S a) :
    ∃ j : ZMod (ccpCornerCount hn hP S q), ccpCornerMark hn hP S q j = a := by
  obtain ⟨i, hi, hia⟩ := List.mem_iff_getElem.mp ((mem_ccpCornerList hn hP S q a).mpr ⟨ha, hac⟩)
  refine ⟨(i : ZMod (ccpCornerCount hn hP S q)), ?_⟩
  unfold ccpCornerMark
  have hval : ((i : ℕ) : ZMod (ccpCornerCount hn hP S q)).val = i := by
    rw [ZMod.val_natCast]
    exact Nat.mod_eq_of_lt hi
  simp only [hval]
  exact hia

/-- The corner after `c_j` in the corner polygon is the next corner of the inherited corner
cycle: the modular index step matches `Cycle.next`, including the closing step. -/
theorem ccpCornerMark_add_one (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) (q : Component hn hP S) (j : ZMod (ccpCornerCount hn hP S q)) :
    ccpCornerMark hn hP S q (j + 1) =
      (componentCornerCycle hn hP S q).next (componentCornerCycle_nodup hn hP S q)
        (ccpCornerMark hn hP S q j) (ccpCornerMark_mem_cornerCycle hn hP S q j) := by
  change _ = (ccpCornerList hn hP S q).next (ccpCornerMark hn hP S q j)
    ((mem_ccpCornerList hn hP S q _).mpr (ccpCornerMark_mem hn hP S q j))
  unfold ccpCornerMark
  rw [List.next_getElem _ (ccpCornerList_nodup hn hP S q) j.val (ZMod.val_lt j)]
  have hval : (j + 1).val = (j.val + 1) % (ccpCornerList hn hP S q).length := by
    rw [ZMod.val_add, ZMod.val_one_eq_one_mod, Nat.add_mod_mod]
    rfl
  simp only [hval]

/-! ## 5. Edges of the corner polygon -/

/-- **Compressed block between consecutive corners.** From the corner `c_j` the corner `c_{j+1}`
is reached in `m ≥ 1` steps of `ρ_S`; the intermediate marks are unselected visits on the one
original edge `e` of the outgoing slot of `c_j`, with strictly increasing parameters; all `m`
segments lie on `e`; and the union of their images is exactly the straight segment from `c_j`
to `c_{j+1}`, which is a positive multiple `c • edge P e` of the direction of `e`. Moreover the
edge `e` is the incoming edge at `c_{j+1}`. -/
theorem ccpCornerPolygon_block (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    {S : Finset (Crossing P)} (hS : S ∈ independentSupports hn hP)
    (q : Component hn hP S) (j : ZMod (ccpCornerCount hn hP S q)) :
    let a := ccpCornerMark hn hP S q j
    let e := (ccpOutSlot hn hP S a).1
    ∃ m : ℕ, 1 ≤ m ∧
      (smoothingSuccessor hn hP S ^ m) a = ccpCornerMark hn hP S q (j + 1) ∧
      (∀ r, 1 ≤ r → r < m → ∃ v : Visit P,
        (smoothingSuccessor hn hP S ^ r) a = Sum.inr v ∧ v.1 ∉ S ∧ v.2.val = e) ∧
      (∀ r < m, (ccpOutSlot hn hP S ((smoothingSuccessor hn hP S ^ r) a)).1 = e) ∧
      (∀ r, r + 1 < m →
        (ccpOutSlot hn hP S ((smoothingSuccessor hn hP S ^ r) a)).2.val <
          (ccpOutSlot hn hP S ((smoothingSuccessor hn hP S ^ (r + 1)) a)).2.val) ∧
      (∃ c : ℝ, 0 < c ∧
        ccpCornerPolygon hn hP S q (j + 1) - ccpCornerPolygon hn hP S q j = c • edge P e) ∧
      e = ccpInEdge hn hP (ccpCornerMark hn hP S q (j + 1)) ∧
      (⋃ r < m, smoothingSegment hn hP S ((smoothingSuccessor hn hP S ^ r) a) '' Set.Icc 0 1) =
        (fun u : ℝ => ccpCornerPolygon hn hP S q j +
          u • (ccpCornerPolygon hn hP S q (j + 1) - ccpCornerPolygon hn hP S q j)) ''
            Set.Icc 0 1 := by
  intro a e
  obtain ⟨m, hm, hchain, hmid⟩ := ccp_corner_chain hn hP hS q a (ccpCornerMark_owner hn hP S q j)
    (ccpCornerMark_isTrueCorner hn hP S q j)
  rw [← ccpCornerMark_add_one hn hP S q j] at hchain
  obtain ⟨hedges, t, hst, ht1, hend, himage⟩ := ccp_block_compression hn hP S a m hm hmid
  have hstart : ccpCornerPolygon hn hP S q j = edgePoint P e (ccpOutSlot hn hP S a).2.val :=
    ccp_evaluation_eq_outSlot hn hP S a
  have hend' : ccpCornerPolygon hn hP S q (j + 1) = edgePoint P e t := by
    rw [ccpCornerPolygon_apply, ← hchain]
    exact hend
  refine ⟨m, hm, hchain, ?_, hedges, ?_, ?_, ?_, ?_⟩
  · intro r hr1 hrm
    obtain ⟨v, hv, hvS⟩ := ccp_not_trueCorner S (hmid r hr1 hrm)
    refine ⟨v, hv, hvS, ?_⟩
    have hprev : smoothingSuccessor hn hP S ((smoothingSuccessor hn hP S ^ (r - 1)) a) =
        (smoothingSuccessor hn hP S ^ r) a := by
      rw [← Equiv.Perm.mul_apply, ← pow_succ']
      congr 2
      omega
    exact (ccp_incoming_visit_position hn hP S _ v (hprev.trans hv)).1.symm.trans
      (hedges (r - 1) (by omega))
  · intro r hr
    obtain ⟨v, hv, hvS⟩ := ccp_not_trueCorner S (hmid (r + 1) (by omega) hr)
    have hprev : smoothingSuccessor hn hP S ((smoothingSuccessor hn hP S ^ r) a) =
        (smoothingSuccessor hn hP S ^ (r + 1)) a := by
      rw [pow_succ', Equiv.Perm.mul_apply]
    have hlt := (ccp_incoming_visit_position hn hP S _ v (hprev.trans hv)).2
    rw [hv, ccpOutSlot_unselected hn hP S v hvS]
    exact hlt
  · refine ⟨t - (ccpOutSlot hn hP S a).2.val, sub_pos.mpr hst, ?_⟩
    rw [hstart, hend', edgePoint_sub_edgePoint]
  · have hprev : smoothingSuccessor hn hP S ((smoothingSuccessor hn hP S ^ (m - 1)) a) =
        ccpCornerMark hn hP S q (j + 1) := by
      rw [← hchain, ← Equiv.Perm.mul_apply, ← pow_succ']
      congr 2
      omega
    rw [← ccpOutSlot_eq_of_succ hn hP S hprev]
    exact (hedges (m - 1) (by omega)).symm
  · rw [himage, hstart, hend']
    have hf : (fun u : ℝ => edgePoint P e (ccpOutSlot hn hP S a).2.val +
        u • (edgePoint P e t - edgePoint P e (ccpOutSlot hn hP S a).2.val)) =
        edgePoint P e ∘ (fun u : ℝ => (ccpOutSlot hn hP S a).2.val +
          u * (t - (ccpOutSlot hn hP S a).2.val)) := by
      funext u
      exact edgePoint_affine P e _ t u
    rw [hf, Set.image_comp, ccp_image_affine_unit hst]

/-- Each edge of the corner polygon is a positive multiple of the direction of the original
edge of the outgoing slot of its starting corner, which is also the incoming edge at its end. -/
theorem ccpCornerPolygon_edge (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    {S : Finset (Crossing P)} (hS : S ∈ independentSupports hn hP)
    (q : Component hn hP S) (j : ZMod (ccpCornerCount hn hP S q)) :
    ∃ c : ℝ, 0 < c ∧
      edge (ccpCornerPolygon hn hP S q) j =
        c • edge P (ccpOutSlot hn hP S (ccpCornerMark hn hP S q j)).1 := by
  obtain ⟨_, _, _, _, _, _, hc, _, _⟩ := ccpCornerPolygon_block hn hP hS q j
  exact hc

theorem ccpCornerPolygon_outEdge_eq_inEdge (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    {S : Finset (Crossing P)} (hS : S ∈ independentSupports hn hP)
    (q : Component hn hP S) (j : ZMod (ccpCornerCount hn hP S q)) :
    (ccpOutSlot hn hP S (ccpCornerMark hn hP S q j)).1 =
      ccpInEdge hn hP (ccpCornerMark hn hP S q (j + 1)) := by
  obtain ⟨_, _, _, _, _, _, _, he, _⟩ := ccpCornerPolygon_block hn hP hS q j
  exact he

/-- The incoming edge of the corner polygon at `c_j` (the edge `j - 1`) is a positive multiple
of the original edge `ccpInEdge c_j` carrying the incoming segment at `c_j`. -/
theorem ccpCornerPolygon_edge_pred (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    {S : Finset (Crossing P)} (hS : S ∈ independentSupports hn hP)
    (q : Component hn hP S) (j : ZMod (ccpCornerCount hn hP S q)) :
    ∃ c : ℝ, 0 < c ∧
      edge (ccpCornerPolygon hn hP S q) (j - 1) =
        c • edge P (ccpInEdge hn hP (ccpCornerMark hn hP S q j)) := by
  obtain ⟨c, hc, he⟩ := ccpCornerPolygon_edge hn hP hS q (j - 1)
  refine ⟨c, hc, ?_⟩
  rw [he, ccpCornerPolygon_outEdge_eq_inEdge hn hP hS q (j - 1), sub_add_cancel]

/-! ## 6. Corner turns: nonzero, vertex sign `τ_i`, smoothing signs `sgn det(d_i, d_j)` -/

omit [NeZero n] in
theorem ccp_det_smul_smul (c d : ℝ) (u v : Plane) : det (c • u) (d • v) = (c * d) * det u v := by
  simp only [det, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

/-- The corner turn determinant at `c_j` is a positive multiple of the determinant of the
original incoming and outgoing edge directions at that corner. -/
theorem ccpCornerPolygon_turn_det (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    {S : Finset (Crossing P)} (hS : S ∈ independentSupports hn hP)
    (q : Component hn hP S) (j : ZMod (ccpCornerCount hn hP S q)) :
    ∃ c : ℝ, 0 < c ∧
      det (edge (ccpCornerPolygon hn hP S q) (j - 1)) (edge (ccpCornerPolygon hn hP S q) j) =
        c * det (edge P (ccpInEdge hn hP (ccpCornerMark hn hP S q j)))
          (edge P (ccpOutSlot hn hP S (ccpCornerMark hn hP S q j)).1) := by
  obtain ⟨c₁, hc₁, he₁⟩ := ccpCornerPolygon_edge_pred hn hP hS q j
  obtain ⟨c₂, hc₂, he₂⟩ := ccpCornerPolygon_edge hn hP hS q j
  refine ⟨c₁ * c₂, mul_pos hc₁ hc₂, ?_⟩
  rw [he₁, he₂, ccp_det_smul_smul]

/-- The determinant of the original incoming and outgoing directions at a true corner is
nonzero: at a vertex by genericity (`τ_i ≠ 0`), at a selected crossing by transversality. -/
theorem ccp_corner_directions_det_ne_zero (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) (a : Mark P) (ha : IsTrueCorner S a) :
    det (edge P (ccpInEdge hn hP a)) (edge P (ccpOutSlot hn hP S a).1) ≠ 0 := by
  cases a with
  | inl i =>
    rw [ccpInEdge_vertex, ccpOutSlot_vertex]
    have ht := (g1 hn P hP.1).2.2.1 i
    have hne : turn P i ≠ 0 := by
      rcases ht with h | h <;> rw [h] <;> decide
    rw [turn_det] at hne
    exact sign_ne_zero.mp hne
  | inr v =>
    have hv : v.1 ∈ S := ha
    rw [ccpInEdge_visit, ccpOutSlot_selected hn hP S v hv]
    have hc : IsCrossing P {v.2.val, (visitTwin v).2.val} := by
      rw [← visit_crossing_val_eq_pair v]
      exact v.1.property
    exact crossing_det_ne_zero_of_geometry (generic_crossingGeometry hn hP) hc

theorem ccpCornerPolygon_det_ne_zero (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    {S : Finset (Crossing P)} (hS : S ∈ independentSupports hn hP)
    (q : Component hn hP S) (j : ZMod (ccpCornerCount hn hP S q)) :
    det (edge (ccpCornerPolygon hn hP S q) (j - 1)) (edge (ccpCornerPolygon hn hP S q) j) ≠ 0 := by
  obtain ⟨c, hc, he⟩ := ccpCornerPolygon_turn_det hn hP hS q j
  rw [he]
  exact mul_ne_zero hc.ne'
    (ccp_corner_directions_det_ne_zero hn hP S _ (ccpCornerMark_isTrueCorner hn hP S q j))

/-- All corner turns of a carrier are nonzero. -/
theorem ccpCornerPolygon_turn_ne_zero (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    {S : Finset (Crossing P)} (hS : S ∈ independentSupports hn hP)
    (q : Component hn hP S) (j : ZMod (ccpCornerCount hn hP S q)) :
    turn (ccpCornerPolygon hn hP S q) j ≠ 0 := by
  rw [turn_det]
  exact sign_ne_zero.mpr (ccpCornerPolygon_det_ne_zero hn hP hS q j)

/-- The corner turn sign is the sign of the determinant of the original incoming and outgoing
directions at that corner. -/
theorem ccpCornerPolygon_turn_eq_sign (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    {S : Finset (Crossing P)} (hS : S ∈ independentSupports hn hP)
    (q : Component hn hP S) (j : ZMod (ccpCornerCount hn hP S q)) :
    turn (ccpCornerPolygon hn hP S q) j =
      SignType.sign (det (edge P (ccpInEdge hn hP (ccpCornerMark hn hP S q j)))
        (edge P (ccpOutSlot hn hP S (ccpCornerMark hn hP S q j)).1)) := by
  obtain ⟨c, hc, he⟩ := ccpCornerPolygon_turn_det hn hP hS q j
  rw [turn_det, he, sign_mul, sign_pos hc, one_mul]

/-- **At an original vertex `i` the turn sign is `τ_i`.** -/
theorem ccpCornerPolygon_turn_vertex (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    {S : Finset (Crossing P)} (hS : S ∈ independentSupports hn hP)
    (q : Component hn hP S) (j : ZMod (ccpCornerCount hn hP S q)) (i : ZMod n)
    (hj : ccpCornerMark hn hP S q j = Sum.inl i) :
    turn (ccpCornerPolygon hn hP S q) j = turn P i := by
  rw [ccpCornerPolygon_turn_eq_sign hn hP hS q j, hj, ccpInEdge_vertex, ccpOutSlot_vertex,
    turn_det]

/-- **At a selected crossing of `E_i, E_j`** (`i` the edge of the selected visit `v`, arrived
along; `j` the edge of its twin, left along) **the smoothing corner at `v` has sign
`sgn det(d_i, d_j)`** `= crossingSign P i j`. -/
theorem ccpCornerPolygon_turn_smoothing (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    {S : Finset (Crossing P)} (hS : S ∈ independentSupports hn hP)
    (q : Component hn hP S) (j : ZMod (ccpCornerCount hn hP S q)) (v : Visit P)
    (hj : ccpCornerMark hn hP S q j = Sum.inr v) (hv : v.1 ∈ S) :
    turn (ccpCornerPolygon hn hP S q) j = crossingSign P v.2.val (visitTwin v).2.val := by
  rw [ccpCornerPolygon_turn_eq_sign hn hP hS q j, hj, ccpInEdge_visit,
    ccpOutSlot_selected hn hP S v hv]
  rfl

/-- **The two smoothing corners of a selected crossing**, one on each of the two carriers through
the site, have signs `sgn det(d_i, d_j)` and `sgn det(d_j, d_i)`: one left and one right. -/
theorem ccp_selected_crossing_two_corners (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    {S : Finset (Crossing P)} (hS : S ∈ independentSupports hn hP) (v : Visit P) (hv : v.1 ∈ S) :
    let q := owner hn hP S (Sum.inr v)
    let q' := owner hn hP S (Sum.inr (visitTwin v))
    q ≠ q' ∧
    ∃ (j : ZMod (ccpCornerCount hn hP S q)) (j' : ZMod (ccpCornerCount hn hP S q')),
      ccpCornerMark hn hP S q j = Sum.inr v ∧
      ccpCornerMark hn hP S q' j' = Sum.inr (visitTwin v) ∧
      turn (ccpCornerPolygon hn hP S q) j = crossingSign P v.2.val (visitTwin v).2.val ∧
      turn (ccpCornerPolygon hn hP S q') j' = crossingSign P (visitTwin v).2.val v.2.val ∧
      turn (ccpCornerPolygon hn hP S q') j' = - turn (ccpCornerPolygon hn hP S q) j ∧
      ((turn (ccpCornerPolygon hn hP S q) j = 1 ∧ turn (ccpCornerPolygon hn hP S q') j' = -1) ∨
        (turn (ccpCornerPolygon hn hP S q) j = -1 ∧ turn (ccpCornerPolygon hn hP S q') j' = 1)) := by
  intro q q'
  have hv' : (visitTwin v).1 ∈ S := by
    rw [visitTwin_crossing]
    exact hv
  obtain ⟨j, hj⟩ := ccpCornerMark_exists hn hP S q (Sum.inr v) rfl hv
  obtain ⟨j', hj'⟩ := ccpCornerMark_exists hn hP S q' (Sum.inr (visitTwin v)) rfl hv'
  have h1 := ccpCornerPolygon_turn_smoothing hn hP hS q j v hj hv
  have h2 := ccpCornerPolygon_turn_smoothing hn hP hS q' j' (visitTwin v) hj' hv'
  rw [visitTwin_involutive] at h2
  have hneg : turn (ccpCornerPolygon hn hP S q') j' = - turn (ccpCornerPolygon hn hP S q) j := by
    rw [h1, h2, crossingSign_swap]
  have hne := ccpCornerPolygon_turn_ne_zero hn hP hS q j
  refine ⟨independent_selected_pair_owners_ne hn hP hS v hv, j, j', hj, hj', h1, h2, hneg, ?_⟩
  rw [hneg]
  rcases SignType.trichotomy (turn (ccpCornerPolygon hn hP S q) j) with h | h | h
  · right
    rw [h]
    exact ⟨rfl, rfl⟩
  · exact (hne h).elim
  · left
    rw [h]
    exact ⟨rfl, rfl⟩

/-! ## 7. Nonzero edges, no antiparallel consecutive directions, regularity -/

/-- **Every carrier has nonzero edges.** -/
theorem ccpCornerPolygon_edge_ne_zero (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    {S : Finset (Crossing P)} (hS : S ∈ independentSupports hn hP)
    (q : Component hn hP S) (j : ZMod (ccpCornerCount hn hP S q)) :
    edge (ccpCornerPolygon hn hP S q) j ≠ 0 := by
  obtain ⟨c, hc, he⟩ := ccpCornerPolygon_edge hn hP hS q j
  rw [he]
  exact smul_ne_zero hc.ne' ((g1 hn P hP.1).2.1 _)

/-- **No antiparallel consecutive directions.** -/
theorem ccpCornerPolygon_not_antiparallel (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    {S : Finset (Crossing P)} (hS : S ∈ independentSupports hn hP)
    (q : Component hn hP S) (j : ZMod (ccpCornerCount hn hP S q)) :
    ¬ ∃ r : ℝ, r < 0 ∧
      edge (ccpCornerPolygon hn hP S q) j = r • edge (ccpCornerPolygon hn hP S q) (j - 1) := by
  rintro ⟨r, _, hr⟩
  apply ccpCornerPolygon_det_ne_zero hn hP hS q j
  rw [hr]
  exact det_smul_self _ r

/-- **Every carrier lies in the regular locus** (`SM.Regular`). -/
theorem ccpCornerPolygon_regular (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    {S : Finset (Crossing P)} (hS : S ∈ independentSupports hn hP) (q : Component hn hP S) :
    Regular (ccpCornerPolygon hn hP S q) := by
  rw [regular_iff_edges]
  intro j
  exact ⟨ccpCornerPolygon_edge_ne_zero hn hP hS q j, ccpCornerPolygon_not_antiparallel hn hP hS q j⟩

/-! ## 8. At least three corners -/

/-- **Every carrier has at least three corners.** One nonzero segment cannot close (`k = 1`
would force a zero edge); a closed polygon of two nonzero segments has antiparallel corners
(`k = 2` would force a zero corner determinant). -/
theorem ccpCornerCount_ge_three (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    {S : Finset (Crossing P)} (hS : S ∈ independentSupports hn hP) (q : Component hn hP S) :
    3 ≤ ccpCornerCount hn hP S q := by
  by_contra hlt
  have hpos : 0 < ccpCornerCount hn hP S q := ccpCornerList_length_pos hn hP S q
  rcases (show ccpCornerCount hn hP S q = 1 ∨ ccpCornerCount hn hP S q = 2 by omega) with h1 | h2
  · -- one corner: the single edge closes, so it is zero
    have hone : ((1 : ℕ) : ZMod (ccpCornerCount hn hP S q)) = 0 :=
      (ZMod.natCast_eq_zero_iff 1 _).mpr (by rw [h1])
    have hzero : edge (ccpCornerPolygon hn hP S q) 0 = 0 := by
      have h01 : (0 : ZMod (ccpCornerCount hn hP S q)) + 1 = 0 := by
        rw [zero_add]
        exact_mod_cast hone
      simp only [edge, h01, sub_self]
    exact ccpCornerPolygon_edge_ne_zero hn hP hS q 0 hzero
  · -- two corners: the two edges are opposite, so the corner determinant vanishes
    have htwo : ((2 : ℕ) : ZMod (ccpCornerCount hn hP S q)) = 0 :=
      (ZMod.natCast_eq_zero_iff 2 _).mpr (by rw [h2])
    have h11 : (1 : ZMod (ccpCornerCount hn hP S q)) + 1 = 0 := by
      have : ((2 : ℕ) : ZMod (ccpCornerCount hn hP S q)) = 1 + 1 := by push_cast; ring
      rw [← this]
      exact htwo
    have hsucc : (0 : ZMod (ccpCornerCount hn hP S q)) + 1 = 0 - 1 := by
      rw [zero_add, zero_sub, eq_neg_iff_add_eq_zero]
      exact h11
    have hopp : edge (ccpCornerPolygon hn hP S q) 0 =
        - edge (ccpCornerPolygon hn hP S q) (0 - 1) := by
      simp only [edge, hsucc, sub_add_cancel]
      abel
    apply ccpCornerPolygon_det_ne_zero hn hP hS q 0
    rw [hopp]
    simp only [det, Prod.fst_neg, Prod.snd_neg]
    ring

/-! ## 9. The traced curve of the carrier is its corner polygon -/

/-- Iterates of `ρ_S` stay in the same carrier. -/
theorem ccp_pow_owner (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) (a : Mark P) (r : ℕ) :
    owner hn hP S ((smoothingSuccessor hn hP S ^ r) a) = owner hn hP S a :=
  (owner_eq_iff hn hP S _ _).mpr (Equiv.Perm.SameCycle.symm ⟨r, by simp⟩)

/-- Every mark owned by `q` is reached from a true corner `a` owned by `q` by `r` steps of `ρ_S`
through non-corners only (the last corner before `x`). -/
theorem ccp_previous_corner (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) (q : Component hn hP S) (x : Mark P) (hx : owner hn hP S x = q) :
    ∃ (a : Mark P) (r : ℕ), owner hn hP S a = q ∧ IsTrueCorner S a ∧
      (smoothingSuccessor hn hP S ^ r) a = x ∧
      ∀ i, 1 ≤ i → i ≤ r → ¬ IsTrueCorner S ((smoothingSuccessor hn hP S ^ i) a) := by
  obtain ⟨a₀, ha₀, hc₀⟩ := component_has_trueCorner hn hP S q
  have hsc : (smoothingSuccessor hn hP S).SameCycle a₀ x :=
    (owner_eq_iff hn hP S a₀ x).mp (ha₀.trans hx.symm)
  obtain ⟨N, _, hN⟩ := hsc.exists_pow_eq'
  let Pr : ℕ → Prop := fun i => IsTrueCorner S ((smoothingSuccessor hn hP S ^ i) a₀)
  have hle : Nat.findGreatest Pr N ≤ N := Nat.findGreatest_le N
  have hPr0 : Pr 0 := by
    show IsTrueCorner S ((smoothingSuccessor hn hP S ^ 0) a₀)
    rw [pow_zero, Equiv.Perm.one_apply]
    exact hc₀
  have hspec : Pr (Nat.findGreatest Pr N) := Nat.findGreatest_spec (Nat.zero_le N) hPr0
  refine ⟨(smoothingSuccessor hn hP S ^ Nat.findGreatest Pr N) a₀, N - Nat.findGreatest Pr N,
    ?_, hspec, ?_, ?_⟩
  · rw [ccp_pow_owner]
    exact ha₀
  · rw [← Equiv.Perm.mul_apply, ← pow_add, Nat.sub_add_cancel hle]
    exact hN
  · intro i hi1 hir
    rw [← Equiv.Perm.mul_apply, ← pow_add, add_comm]
    exact @Nat.findGreatest_is_greatest (Nat.findGreatest Pr N + i) Pr _ N (by omega) (by omega)

/-- Each edge segment of the corner polygon is the straight segment between consecutive corners. -/
theorem ccpCornerPolygon_edgeSegment (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) (q : Component hn hP S) (j : ZMod (ccpCornerCount hn hP S q)) :
    edgeSegment (ccpCornerPolygon hn hP S q) j =
      (fun u : ℝ => ccpCornerPolygon hn hP S q j +
        u • (ccpCornerPolygon hn hP S q (j + 1) - ccpCornerPolygon hn hP S q j)) '' Set.Icc 0 1 := by
  ext x
  simp only [edgeSegment, Set.mem_ofPred_eq, Set.mem_image, Set.mem_Icc, edgePoint, edge]
  constructor
  · rintro ⟨t, h0, h1, rfl⟩
    exact ⟨t, ⟨h0, h1⟩, rfl⟩
  · rintro ⟨t, ⟨h0, h1⟩, rfl⟩
    exact ⟨t, h0, h1, rfl⟩

/-- **The carrier traced by its inherited straight subsegments is its corner polygon**: the union
of the outgoing segments of all marks owned by `q` equals the union of the edge segments of the
corner polygon of `q` (omitting the unselected marks changes no point of the traced curve). -/
theorem ccpCornerPolygon_trace (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    {S : Finset (Crossing P)} (hS : S ∈ independentSupports hn hP) (q : Component hn hP S) :
    (⋃ a ∈ {a : Mark P | owner hn hP S a = q}, smoothingSegment hn hP S a '' Set.Icc 0 1) =
      ⋃ j : ZMod (ccpCornerCount hn hP S q), edgeSegment (ccpCornerPolygon hn hP S q) j := by
  apply Set.Subset.antisymm
  · apply Set.iUnion₂_subset
    intro x hx
    obtain ⟨a, r, ha, hac, hrx, hmid⟩ := ccp_previous_corner hn hP S q x hx
    obtain ⟨j, hj⟩ := ccpCornerMark_exists hn hP S q a ha hac
    obtain ⟨m, hm, hchain, _, _, _, _, _, himage⟩ := ccpCornerPolygon_block hn hP hS q j
    rw [hj] at himage hchain
    have hrm : r < m := by
      by_contra hle
      exact hmid m hm (not_lt.mp hle)
        (hchain ▸ ccpCornerMark_isTrueCorner hn hP S q (j + 1))
    refine Set.Subset.trans ?_ (Set.subset_iUnion _ j)
    rw [ccpCornerPolygon_edgeSegment, ← himage, ← hrx]
    exact Set.subset_biUnion_of_mem (u := fun r =>
      smoothingSegment hn hP S ((smoothingSuccessor hn hP S ^ r) a) '' Set.Icc 0 1) hrm
  · apply Set.iUnion_subset
    intro j
    obtain ⟨m, _, _, _, _, _, _, _, himage⟩ := ccpCornerPolygon_block hn hP hS q j
    rw [ccpCornerPolygon_edgeSegment, ← himage]
    apply Set.iUnion₂_subset
    intro r _
    apply Set.subset_biUnion_of_mem (u := fun a => smoothingSegment hn hP S a '' Set.Icc (0:ℝ) 1)
    show owner hn hP S _ = q
    rw [ccp_pow_owner]
    exact ccpCornerMark_owner hn hP S q j

/-! ## 10. lem:carriers clause (ii), assembled -/

/-- **lem:carriers (ii).** For `P` generic with `n ≥ 3`, `S` independent and every carrier `q`:
the corner polygon `Q = ccpCornerPolygon hn hP S q : LabelledTuple k` (its corners being the
original vertices and selected visits owned by `q`, in inherited cyclic order) satisfies
* `Q` traces the carrier: the union of the inherited straight subsegments of `q` is the union of
  the edges of `Q`;
* every edge of `Q` is nonzero and a positive multiple of an original edge direction;
* `Q` has at least three corners;
* no antiparallel consecutive directions (`Q` is in the regular locus);
* all corner turns are nonzero;
* at an original vertex `i` the turn sign is `τ_i = turn P i`;
* at a selected crossing of `E_i, E_j` the two smoothing corners (on the two carriers through
  the site) have signs `sgn det(d_i, d_j)` and `sgn det(d_j, d_i)`, one left and one right. -/
theorem carriers_clause_ii (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    {S : Finset (Crossing P)} (hS : S ∈ independentSupports hn hP) :
    (∀ q : Component hn hP S,
      (⋃ a ∈ {a : Mark P | owner hn hP S a = q}, smoothingSegment hn hP S a '' Set.Icc 0 1) =
        ⋃ j : ZMod (ccpCornerCount hn hP S q), edgeSegment (ccpCornerPolygon hn hP S q) j) ∧
    (∀ (q : Component hn hP S) (j : ZMod (ccpCornerCount hn hP S q)),
      edge (ccpCornerPolygon hn hP S q) j ≠ 0 ∧
      ∃ (c : ℝ) (e : ZMod n), 0 < c ∧ edge (ccpCornerPolygon hn hP S q) j = c • edge P e) ∧
    (∀ q : Component hn hP S, 3 ≤ ccpCornerCount hn hP S q) ∧
    (∀ (q : Component hn hP S) (j : ZMod (ccpCornerCount hn hP S q)),
      ¬ ∃ r : ℝ, r < 0 ∧
        edge (ccpCornerPolygon hn hP S q) j = r • edge (ccpCornerPolygon hn hP S q) (j - 1)) ∧
    (∀ q : Component hn hP S, Regular (ccpCornerPolygon hn hP S q)) ∧
    (∀ (q : Component hn hP S) (j : ZMod (ccpCornerCount hn hP S q)),
      turn (ccpCornerPolygon hn hP S q) j ≠ 0) ∧
    (∀ (q : Component hn hP S) (j : ZMod (ccpCornerCount hn hP S q)) (i : ZMod n),
      ccpCornerMark hn hP S q j = Sum.inl i → turn (ccpCornerPolygon hn hP S q) j = turn P i) ∧
    (∀ (v : Visit P), v.1 ∈ S →
      owner hn hP S (Sum.inr v) ≠ owner hn hP S (Sum.inr (visitTwin v)) ∧
      ∃ (j : ZMod (ccpCornerCount hn hP S (owner hn hP S (Sum.inr v))))
        (j' : ZMod (ccpCornerCount hn hP S (owner hn hP S (Sum.inr (visitTwin v))))),
        ccpCornerMark hn hP S _ j = Sum.inr v ∧
        ccpCornerMark hn hP S _ j' = Sum.inr (visitTwin v) ∧
        turn (ccpCornerPolygon hn hP S _) j = crossingSign P v.2.val (visitTwin v).2.val ∧
        turn (ccpCornerPolygon hn hP S _) j' = crossingSign P (visitTwin v).2.val v.2.val ∧
        turn (ccpCornerPolygon hn hP S _) j' = - turn (ccpCornerPolygon hn hP S _) j ∧
        ((turn (ccpCornerPolygon hn hP S _) j = 1 ∧ turn (ccpCornerPolygon hn hP S _) j' = -1) ∨
          (turn (ccpCornerPolygon hn hP S _) j = -1 ∧ turn (ccpCornerPolygon hn hP S _) j' = 1))) := by
  refine ⟨fun q => ccpCornerPolygon_trace hn hP hS q, fun q j => ⟨ccpCornerPolygon_edge_ne_zero hn hP hS q j, ?_⟩,
    fun q => ccpCornerCount_ge_three hn hP hS q, fun q j => ccpCornerPolygon_not_antiparallel hn hP hS q j,
    fun q => ccpCornerPolygon_regular hn hP hS q, fun q j => ccpCornerPolygon_turn_ne_zero hn hP hS q j,
    fun q j i hj => ccpCornerPolygon_turn_vertex hn hP hS q j i hj,
    fun v hv => ccp_selected_crossing_two_corners hn hP hS v hv⟩
  obtain ⟨c, hc, he⟩ := ccpCornerPolygon_edge hn hP hS q j
  exact ⟨c, _, hc, he⟩

end
end SM.Carrier
