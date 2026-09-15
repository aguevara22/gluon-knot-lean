import SM.FrontRowsW2

/-! # Front certificate rows — sweep delta: the leaf `represent` and row 76 ng:commutation

Certificate rows lane, sweep delta (decision D-FR1: the lane is ported incrementally as fully proved modules).
This module imports `SM.FrontRowsW2` (the wave-2 clean subset: rows 81 ng:circle and 82 ng:cusp-skein with the
shared infrastructure U1-U4, U7, U8D and the U8R record layer) and adds, in this order:
* **the U8R sweep block** (`SM.FrontRows.U8R`, sections `SweepDefs`, `SweepLeaves`, `SlotMap`, `Traversal`,
  `Assembly`): the vertical sweep of the printed proof (sm-3:1938-1947) — the fibre lists and the cuts (S1), the
  cusp and crossing local models (S2, S3), the event word and its run through the hybrid cuts (S4), the slot map
  `Φ` (S5), the traversal `slotAt` and the circle bijection (S6), the record isomorphism `recordIso` and the
  theorem `sweep_proof : SweepStatement F`.  Taken verbatim from the sweep-lane merge
  `work/drafts/frontrows/W3S_Merged.lean` (W3S_MERGE_REPORT.md), minus the two leaves `dirBit_of_cont_before` /
  `dirBit_of_cont_after`, which are false as stated and consumed by nothing (their corrected forms
  `s1b_dirBit_of_cont_before` / `s1b_dirBit_of_cont_after`, with the extra hypothesis `¬ F.IsCusp q`, are proved here).
* **the leaf `SM.FrontRows.represent`** (the representation theorem of row 76), proved from `U8R.sweep_proof`
  through the reduction `U8R.represent_of_sweepStatement` of `SM.FrontRowsW2`.
* **row 76**: the statement `SM.NgCommutationClauses` (verbatim from `Skeleton_W2.lean` / `Statements_FINAL.lean`)
  and `SM.ng_commutation : NgCommutationClauses`, assembled from `comm_counts`, `P_comm`, `deform_downCount`,
  `deform_writhe`, `deform_P` (all in `SM.FrontRowsW2`) and `represent`.

Every declaration in this module is fully proved: the axioms of `SM.ng_commutation` are
`[propext, Classical.choice, Quot.sound, SM.lp_lm]` (`lp_lm` is the accepted literature interface reached through
`P`); those of `SM.FrontRows.represent`, `SM.FrontRows.U8R.sweep_proof` and `SM.FrontRows.U8R.recordIso` are
`[propext, Classical.choice, Quot.sound]`.  Provenance and line map: `work/drafts/frontrows/W2S_DELTA_REPORT.md`.

Not in this module (the final delta module imports this one and adds exactly these): the row statements
`NgFrontIClauses`, `NgFrontIIClauses`, `NgFrontIIIClauses`, `NgDeletionsClauses`, `NgLocalFrontBoundClauses`; the
L-geo leaves `typeIII_site`, `typeII_move`, `typeI_move`, `crossedCusp_move` and their consumers `P_typeIII`,
`P_typeII`, `P_typeI`, `P_crossedCusp`; the rows `ng_front_I`, `ng_front_II`, `ng_front_III`, `ng_deletions`
(77-80), `certificate_laws`, `word_bound`, `ng_local_front_bound` (83).

Checked with `cd work/lean && lake env lean`. -/

namespace SM

open SM.FrontWord SM.Link
open scoped ContDiff

namespace FrontRows

section Leaves

/-! ### U8R sweep — the leaf skeleton for `U8R.SweepStatement` (wave 3; plan `W3_U8R_PLAN.md`)

The vertical sweep of the printed proof (sm-3:1938-1947), organised in six units of leaves:
* **S1 the cut.** Over `x₀` the fibre is finite (`totalFibre_finite`); sorted by height (top to bottom) it is the
  list `fibreListBefore`/`fibreListAfter` (at a double point the over branch, of smaller slope, is above BEFORE the
  crossing and below AFTER it: the two sort keys `beforeLE`/`afterLE`).  Each fibre point carries the bits of its
  strands just before / just after its x-value (`beforeBits`/`afterBits`: none/two for a cusp, one otherwise), so
  `cutBefore x₀`/`cutAfter x₀` are the cuts just left/right of `x₀`, and `hybridCut x₀ z₀` (strands at height
  `≥ z₀` read "before", strands below read "after") is the cut between two events of one x-value.  The analytic
  leaves: the local graph structure at a regular point, compactness (no strands appear from nowhere), the two
  one-sided limits at the level of strand ENTRIES (`Cont`: an entry's continuation along the front), and the
  constancy of the cut between consecutive singular x-values.
* **S2 the cusp**, **S3 the crossing**: the local models (Taylor sign law `cusp_arm_sign`; `x` a strict local
  extremum at a cusp; the over branch above before / below after).
* **S4 the word.** The events (cusps and over-first crossing pairs) sorted by `(x, z)`, bottom first at equal `x`
  (`events`); the letter of an event at position `posOf` = 1 + the number of strands strictly above it in the
  hybrid cut; the run of the word through the hybrid cuts (`run_take_eq_hybrid`), closedness, the counts.
* **S5 the slot map** `Φ` (an occurrence ↦ `σSlotA`/`σSlotB` of its crossing's column) and the local record
  clauses `pair`, `isOver`, `sgn`.
* **S6 the traversal.** `slotAt i t` = the slot of the strand through `(i, t)` at the cut line of its x-value;
  its constancy along regular arcs and its `next`-jumps across singular x-values (through a regular point, a cusp
  vertex, a crossing); hence `succ ↔ firstReturn`, `comp`, and the circle bijection `e`.
The theorem `sweep_proof : SweepStatement F` and the leaf `represent` are PROVED from the leaves. -/
namespace U8R

open SM.FrontWord SM.FrontWord.Letter SM.FrontRealize Equiv

noncomputable section

section SweepDefs

variable (F : SmoothFront)

/-! #### S1. Coordinates, fibres, the sorted fibre lists and the cuts -/

/-- the x-coordinate of circle `i` at parameter `t` -/
def xOf (i : Fin F.c) (t : ℝ) : ℝ := ((F.comp i).γ t).1
/-- the z-coordinate (height) of circle `i` at parameter `t` -/
def zOf (i : Fin F.c) (t : ℝ) : ℝ := ((F.comp i).γ t).2
/-- the height of a parameter -/
def ht (p : Param F.c) : ℝ := (F.eval p).2
/-- the direction bit of a parameter: `true` iff the traversal moves rightward there -/
def dirBit (p : Param F.c) : Bool := decide (0 < xvel F p.1 p.2)

theorem xOf_def (i : Fin F.c) (t : ℝ) : xOf F i t = (F.eval (i, t)).1 := rfl
theorem zOf_def (i : Fin F.c) (t : ℝ) : zOf F i t = ht F (i, t) := rfl

/-- a default parameter (used only as the `getD` default of lists) -/
def dfltP : Param F.c := (⟨0, F.hc⟩, 0)

instance decIsCusp (p : Param F.c) : Decidable (F.IsCusp p) := by
  unfold SmoothFront.IsCusp; infer_instance
instance decIsLeftCusp (p : Param F.c) : Decidable (F.IsLeftCusp p) := by
  unfold SmoothFront.IsLeftCusp; infer_instance
instance decIsRightCusp (p : Param F.c) : Decidable (F.IsRightCusp p) := by
  unfold SmoothFront.IsRightCusp; infer_instance

/-- the finite fibre over `x₀` as a `Finset` (all circles, fundamental period) -/
def fibreFinset (x₀ : ℝ) : Finset (Param F.c) := (totalFibre_finite F x₀).toFinset

theorem mem_fibreFinset (x₀ : ℝ) (p : Param F.c) : p ∈ fibreFinset F x₀ ↔ p ∈ totalFibre F x₀ :=
  Set.Finite.mem_toFinset _

/-- the "before" order on fibre points: height descending, at equal height the smaller slope (the over branch)
first — the order of the strands just LEFT of a double point -/
def beforeLE (p q : Param F.c) : Bool :=
  decide (toLex (-(ht F p), F.slope p) ≤ toLex (-(ht F q), F.slope q))
/-- the "after" order: height descending, at equal height the larger slope (the under branch) first — the order
of the strands just RIGHT of a double point -/
def afterLE (p q : Param F.c) : Bool :=
  decide (toLex (-(ht F p), -(F.slope p)) ≤ toLex (-(ht F q), -(F.slope q)))

/-- the fibre over `x₀` sorted top to bottom in the "before" order -/
def fibreListBefore (x₀ : ℝ) : List (Param F.c) := (fibreFinset F x₀).toList.mergeSort (beforeLE F)
/-- the fibre over `x₀` sorted top to bottom in the "after" order -/
def fibreListAfter (x₀ : ℝ) : List (Param F.c) := (fibreFinset F x₀).toList.mergeSort (afterLE F)

theorem fibreListBefore_perm (x₀ : ℝ) : List.Perm (fibreListBefore F x₀) (fibreFinset F x₀).toList :=
  List.mergeSort_perm _ _
theorem fibreListAfter_perm (x₀ : ℝ) : List.Perm (fibreListAfter F x₀) (fibreFinset F x₀).toList :=
  List.mergeSort_perm _ _
theorem mem_fibreListBefore (x₀ : ℝ) (p : Param F.c) : p ∈ fibreListBefore F x₀ ↔ p ∈ totalFibre F x₀ := by
  rw [fibreListBefore, List.mem_mergeSort, Finset.mem_toList, mem_fibreFinset]
theorem mem_fibreListAfter (x₀ : ℝ) (p : Param F.c) : p ∈ fibreListAfter F x₀ ↔ p ∈ totalFibre F x₀ := by
  rw [fibreListAfter, List.mem_mergeSort, Finset.mem_toList, mem_fibreFinset]
theorem fibreListBefore_nodup (x₀ : ℝ) : (fibreListBefore F x₀).Nodup :=
  (fibreListBefore_perm F x₀).nodup_iff.mpr (Finset.nodup_toList _)
theorem fibreListAfter_nodup (x₀ : ℝ) : (fibreListAfter F x₀).Nodup :=
  (fibreListAfter_perm F x₀).nodup_iff.mpr (Finset.nodup_toList _)

theorem beforeLE_trans (p q r : Param F.c) (h1 : beforeLE F p q = true) (h2 : beforeLE F q r = true) :
    beforeLE F p r = true := by
  unfold beforeLE at *; rw [decide_eq_true_iff] at *; exact le_trans h1 h2
theorem beforeLE_total (p q : Param F.c) : (beforeLE F p q || beforeLE F q p) = true := by
  unfold beforeLE; rcases le_total (toLex (-(ht F p), F.slope p)) (toLex (-(ht F q), F.slope q)) with h | h <;> simp [h]
theorem afterLE_trans (p q r : Param F.c) (h1 : afterLE F p q = true) (h2 : afterLE F q r = true) :
    afterLE F p r = true := by
  unfold afterLE at *; rw [decide_eq_true_iff] at *; exact le_trans h1 h2
theorem afterLE_total (p q : Param F.c) : (afterLE F p q || afterLE F q p) = true := by
  unfold afterLE
  rcases le_total (toLex (-(ht F p), -(F.slope p))) (toLex (-(ht F q), -(F.slope q))) with h | h <;> simp [h]

theorem fibreListBefore_pairwise (x₀ : ℝ) : (fibreListBefore F x₀).Pairwise (fun p q => beforeLE F p q = true) :=
  List.pairwise_mergeSort (beforeLE_trans F) (beforeLE_total F) _
theorem fibreListAfter_pairwise (x₀ : ℝ) : (fibreListAfter F x₀).Pairwise (fun p q => afterLE F p q = true) :=
  List.pairwise_mergeSort (afterLE_trans F) (afterLE_total F) _

/-- The strands of a fibre point just BEFORE its x-value, top to bottom: none for a left cusp (both arms lie to
the right); two for a right cusp — the arriving arm travels rightward (`true`) and is the upper one iff the later
arm is the lower one, i.e. iff `cuspDisc < 0` (FR-2); one strand, with its direction bit, for any other point. -/
def beforeBits (p : Param F.c) : Cuts :=
  if F.IsLeftCusp p then []
  else if F.IsRightCusp p then (if F.cuspDisc p < 0 then [true, false] else [false, true])
  else [dirBit F p]

/-- The strands of a fibre point just AFTER its x-value, top to bottom: none for a right cusp; two for a left
cusp — the leaving arm travels rightward (`true`) and is the upper one iff `0 < cuspDisc` (FR-2); one otherwise. -/
def afterBits (p : Param F.c) : Cuts :=
  if F.IsRightCusp p then []
  else if F.IsLeftCusp p then (if 0 < F.cuspDisc p then [true, false] else [false, true])
  else [dirBit F p]

/-- the strand entries of a list of fibre points: `(p, j)`, `j` indexing the strands of `p` -/
def entriesOf (bits : Param F.c → Cuts) (L : List (Param F.c)) : List (Param F.c × ℕ) :=
  L.flatMap (fun p => (List.range (bits p).length).map (fun j => (p, j)))

/-- the bit of a strand entry -/
def entryBit (bits : Param F.c → Cuts) (a : Param F.c × ℕ) : Bool := (bits a.1).getD a.2 false

theorem map_entryBit_entriesOf (bits : Param F.c → Cuts) (L : List (Param F.c)) :
    (entriesOf F bits L).map (entryBit F bits) = L.flatMap bits := by
  unfold entriesOf
  rw [List.map_flatMap]
  congr 1
  funext p
  rw [List.map_map]
  apply List.ext_getElem
  · simp
  · intro j h1 h2
    simp only [List.getElem_map, List.getElem_range, Function.comp, entryBit]
    exact List.getD_eq_getElem _ _ h2

/-- The cut with the fibre points satisfying `P` read "before" and the others "after" (the `P`-points are the
still unprocessed events and everything above them; `P := fun _ => true` gives `cutBefore`, `P := fun _ => false`
gives `cutAfter`). -/
def hybridCutP (x₀ : ℝ) (P : Param F.c → Bool) : Cuts :=
  ((fibreListBefore F x₀).filter P).flatMap (beforeBits F) ++
    ((fibreListAfter F x₀).filter (fun p => !P p)).flatMap (afterBits F)

/-- the strand entries of the hybrid cut, in the order of its bits -/
def hybridEntriesP (x₀ : ℝ) (P : Param F.c → Bool) : List (Param F.c × ℕ) :=
  entriesOf F (beforeBits F) ((fibreListBefore F x₀).filter P) ++
    entriesOf F (afterBits F) ((fibreListAfter F x₀).filter (fun p => !P p))

/-- the cut just left of `x₀` -/
def cutBefore (x₀ : ℝ) : Cuts := (fibreListBefore F x₀).flatMap (beforeBits F)
/-- the cut just right of `x₀` -/
def cutAfter (x₀ : ℝ) : Cuts := (fibreListAfter F x₀).flatMap (afterBits F)
/-- the strand entries just left of `x₀` -/
def entriesBefore (x₀ : ℝ) : List (Param F.c × ℕ) := entriesOf F (beforeBits F) (fibreListBefore F x₀)
/-- the strand entries just right of `x₀` -/
def entriesAfter (x₀ : ℝ) : List (Param F.c × ℕ) := entriesOf F (afterBits F) (fibreListAfter F x₀)
/-- the cut between two events of one x-value `x₀`: the strands at height `≥ z₀` read "before", the strands below
read "after" — the cut just BEFORE the event at height `z₀` is processed -/
def hybridCut (x₀ z₀ : ℝ) : Cuts := hybridCutP F x₀ (fun p => decide (z₀ ≤ ht F p))
/-- the cut just AFTER the event at height `z₀` is processed -/
def hybridCutStrict (x₀ z₀ : ℝ) : Cuts := hybridCutP F x₀ (fun p => decide (z₀ < ht F p))
/-- the strand entries of `hybridCut` -/
def hybridEntries (x₀ z₀ : ℝ) : List (Param F.c × ℕ) := hybridEntriesP F x₀ (fun p => decide (z₀ ≤ ht F p))

theorem cutBefore_eq_hybridCutP (x₀ : ℝ) : cutBefore F x₀ = hybridCutP F x₀ (fun _ => true) := by
  simp [cutBefore, hybridCutP]
theorem cutAfter_eq_hybridCutP (x₀ : ℝ) : cutAfter F x₀ = hybridCutP F x₀ (fun _ => false) := by
  simp [cutAfter, hybridCutP]

/-- `Cont q a`: the parameter `q` lies on the strand of the entry `a = (p, j)`, on the cusp-free arc adjacent to
`p` (no cusp strictly between the lifted parameter `s` of `q` and `p.2`); for a cusp `p` the arm is fixed by `j`:
the upper arm (`j = 0`) is the EARLIER arm (`s < p.2`) iff `cuspDisc p < 0` (FR-2; the same formula for the two
arms before a right cusp and the two arms after a left cusp). -/
def Cont (q : Param F.c) (a : Param F.c × ℕ) : Prop :=
  q.1 = a.1.1 ∧ ∃ s : ℝ, SameParam q (a.1.1, s) ∧ s ≠ a.1.2 ∧
    (∀ u, min s a.1.2 < u → u < max s a.1.2 → ¬ F.IsCusp (a.1.1, u)) ∧
    (F.IsCusp a.1 → ((s < a.1.2) ↔ (a.2 = 0 ↔ F.cuspDisc a.1 < 0)))

/-- the position (1-based, from the top) of a fibre point `q` over `x₀` among the fibre points: one plus the
number of fibre points strictly above it (the position of its strand at a non-singular `x₀`) -/
def posAt (x₀ : ℝ) (q : Param F.c) : ℕ := ((fibreFinset F x₀).filter (fun p => ht F q < ht F p)).card + 1

/-! #### S4. Events, letters, the word -/

/-- the crossings: the over-first pairs -/
abbrev Cross : Type := {q : Param F.c × Param F.c // q ∈ F.crossingPairs}
/-- the singular events of the sweep: cusps and crossings -/
abbrev Event : Type := F.Cusp ⊕ Cross F

/-- a parameter of the event's point (the over branch for a crossing) -/
def evPt : Event F → Param F.c
  | Sum.inl c => c.1
  | Sum.inr q => q.1.1
/-- the x-value of an event -/
def evX (e : Event F) : ℝ := (F.eval (evPt F e)).1
/-- the height of an event -/
def evZ (e : Event F) : ℝ := ht F (evPt F e)
/-- the sweep order of events: by x-value, ties broken bottom to top -/
def evLE (e e' : Event F) : Bool := decide (toLex (evX F e, evZ F e) ≤ toLex (evX F e', evZ F e'))

theorem evLE_trans (e e' e'' : Event F) (h1 : evLE F e e' = true) (h2 : evLE F e' e'' = true) :
    evLE F e e'' = true := by
  unfold evLE at *; rw [decide_eq_true_iff] at *; exact le_trans h1 h2
theorem evLE_total (e e' : Event F) : (evLE F e e' || evLE F e' e) = true := by
  unfold evLE; rcases le_total (toLex (evX F e, evZ F e)) (toLex (evX F e', evZ F e')) with h | h <;> simp [h]

/-- the events in sweep order -/
def events : List (Event F) := (Finset.univ : Finset (Event F)).toList.mergeSort (evLE F)

theorem mem_events (e : Event F) : e ∈ events F := by
  rw [events, List.mem_mergeSort, Finset.mem_toList]; exact Finset.mem_univ _
theorem events_nodup : (events F).Nodup :=
  (List.mergeSort_perm _ _).nodup_iff.mpr (Finset.nodup_toList _)
theorem events_pairwise_le : (events F).Pairwise (fun e e' => evLE F e e' = true) :=
  List.pairwise_mergeSort (evLE_trans F) (evLE_total F) _

/-- a lawful `BEq` on events (the `Sum` instance is not lawful), for `List.idxOf` -/
instance (priority := high) instBEqEvent : BEq (Event F) := ⟨fun a b => decide (a = b)⟩
instance instLawfulBEqEvent : LawfulBEq (Event F) where
  eq_of_beq {a b} h := of_decide_eq_true h
  rfl {a} := decide_eq_true rfl

/-- some cusp (every front has one) -/
def someCusp : F.Cusp := (exists_two_cusps F ⟨0, F.hc⟩).choose
/-- the event of column `k` (junk beyond the last column) -/
def eventAt (k : ℕ) : Event F := (events F).getD k (Sum.inl (someCusp F))
/-- the column of an event -/
def evIdx (e : Event F) : ℕ := (events F).idxOf e
/-- the x-value of column `k` -/
def colX (k : ℕ) : ℝ := evX F (eventAt F k)
/-- the height of the event of column `k` -/
def colZ (k : ℕ) : ℝ := evZ F (eventAt F k)

theorem evIdx_lt_length (e : Event F) : evIdx F e < (events F).length :=
  List.idxOf_lt_length_iff.mpr (mem_events F e)
theorem eventAt_evIdx (e : Event F) : eventAt F (evIdx F e) = e := by
  unfold eventAt; rw [List.getD_eq_getElem _ _ (evIdx_lt_length F e)]; exact List.getElem_idxOf _
theorem evIdx_eventAt {k : ℕ} (hk : k < (events F).length) : evIdx F (eventAt F k) = k := by
  unfold eventAt; rw [List.getD_eq_getElem _ _ hk]
  exact List.Nodup.idxOf_getElem (events_nodup F) _ _

/-- the position of an event: one plus the number of strands strictly above it in the cut just before it -/
def posOf (e : Event F) : ℕ :=
  (((fibreListBefore F (evX F e)).filter (fun p => decide (evZ F e < ht F p))).flatMap (beforeBits F)).length + 1

/-- The letter read at an event: a left cusp is `l m d` with `d` = "the upper new arm travels rightward" = "the
later arm is the upper one" = `0 < cuspDisc`; a right cusp is `r m`; a crossing is `σ m` (the over branch, of
smaller slope, is the upper strand before the crossing and descends: `σSlotA`). -/
def letterOf (e : Event F) : Letter :=
  match e with
  | Sum.inl c => if F.IsLeftCusp c.1 then Letter.l (posOf F (Sum.inl c)) (decide (0 < F.cuspDisc c.1))
      else Letter.r (posOf F (Sum.inl c))
  | Sum.inr q => Letter.σ (posOf F (Sum.inr q))

/-- THE WORD OF THE SWEEP -/
def word : Word := (events F).map (letterOf F)

theorem length_word : (word F).length = (events F).length := List.length_map _

theorem letterAt_word {k : ℕ} (hk : k < (events F).length) : letterAt (word F) k = letterOf F (eventAt F k) := by
  unfold letterAt word eventAt
  rw [List.getD_eq_getElem _ _ (by rw [List.length_map]; exact hk), List.getD_eq_getElem _ _ hk, List.getElem_map]

theorem letterAt_word_evIdx (e : Event F) : letterAt (word F) (evIdx F e) = letterOf F e := by
  rw [letterAt_word F (evIdx_lt_length F e), eventAt_evIdx]

theorem evIdx_lt_length_word (e : Event F) : evIdx F e < (word F).length := by
  rw [length_word]; exact evIdx_lt_length F e

theorem letterAt_word_cross (q : Cross F) : letterAt (word F) (evIdx F (Sum.inr q)) = .σ (posOf F (Sum.inr q)) := by
  rw [letterAt_word_evIdx]; rfl

/-- the column of an x-value: the number of events strictly to its left (for `x ∉ singX` the cut line of `x`) -/
def colAt (x : ℝ) : ℕ := ((events F).filter (fun e => decide (evX F e < x))).length


end SweepDefs

section SweepLeaves

variable (F : SmoothFront)

/-! #### S1 leaves: the cut at a non-singular x-value and its one-sided limits -/

/-! ### S1a helpers -/
section S1aHelpers

/-- two fibre points over `x₀` with equal height and slope coincide: they would be a double point with equal
slopes, against `slope_ne_of_isDouble` -/
theorem s1a_eq_of_ht_slope_eq {x₀ : ℝ} {p q : Param F.c} (hp : p ∈ totalFibre F x₀)
    (hq : q ∈ totalFibre F x₀) (hz : ht F p = ht F q) (hs : F.slope p = F.slope q) : p = q := by
  by_contra hne
  have he : F.eval p = F.eval q := Prod.ext (hp.2.trans hq.2.symm) hz
  have hd : F.IsDouble p q := ⟨fun h => hne (SameParam.eq_of_mem_Ico hp.1 hq.1 h), he⟩
  exact F.slope_ne_of_isDouble hd hs

/-- `beforeLE` is antisymmetric on the fibre over `x₀` -/
theorem s1a_beforeLE_antisymm {x₀ : ℝ} {p q : Param F.c} (hp : p ∈ totalFibre F x₀)
    (hq : q ∈ totalFibre F x₀) (h1 : beforeLE F p q = true) (h2 : beforeLE F q p = true) : p = q := by
  unfold beforeLE at h1 h2
  rw [decide_eq_true_iff] at h1 h2
  have h := toLex.injective (le_antisymm h1 h2)
  rw [Prod.mk.injEq] at h
  exact s1a_eq_of_ht_slope_eq F hp hq (neg_inj.mp h.1) h.2

/-- `afterLE` is antisymmetric on the fibre over `x₀` -/
theorem s1a_afterLE_antisymm {x₀ : ℝ} {p q : Param F.c} (hp : p ∈ totalFibre F x₀)
    (hq : q ∈ totalFibre F x₀) (h1 : afterLE F p q = true) (h2 : afterLE F q p = true) : p = q := by
  unfold afterLE at h1 h2
  rw [decide_eq_true_iff] at h1 h2
  have h := toLex.injective (le_antisymm h1 h2)
  rw [Prod.mk.injEq] at h
  exact s1a_eq_of_ht_slope_eq F hp hq (neg_inj.mp h.1) (neg_inj.mp h.2)

/-- a `flatMap` of singletons is a `map` -/
theorem s1a_flatMap_eq_map {α β : Type*} (L : List α) (f : α → List β) (g : α → β)
    (h : ∀ p ∈ L, f p = [g p]) : L.flatMap f = L.map g := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    rw [List.flatMap_cons, List.map_cons, h a (List.mem_cons.mpr (Or.inl rfl)),
      ih (fun p hp => h p (List.mem_cons.mpr (Or.inr hp))), List.singleton_append]

/-- over a non-singular `x₀` no fibre point is a cusp -/
theorem s1a_not_isCusp_of_mem_totalFibre {x₀ : ℝ} (hx : x₀ ∉ singX F) {p : Param F.c}
    (hp : p ∈ totalFibre F x₀) : ¬ F.IsCusp p :=
  (regular_of_notMem_singX F (by rw [hp.2]; exact hx)).1

/-- over a non-singular `x₀` every fibre point has one "before" strand, with its direction bit -/
theorem s1a_beforeBits_eq {x₀ : ℝ} (hx : x₀ ∉ singX F) {p : Param F.c} (hp : p ∈ totalFibre F x₀) :
    beforeBits F p = [dirBit F p] := by
  have hc := s1a_not_isCusp_of_mem_totalFibre F hx hp
  have hl : ¬ F.IsLeftCusp p := fun h => hc h.1
  have hr : ¬ F.IsRightCusp p := fun h => hc h.1
  simp [beforeBits, hl, hr]

/-- over a non-singular `x₀` every fibre point has one "after" strand, with its direction bit -/
theorem s1a_afterBits_eq {x₀ : ℝ} (hx : x₀ ∉ singX F) {p : Param F.c} (hp : p ∈ totalFibre F x₀) :
    afterBits F p = [dirBit F p] := by
  have hc := s1a_not_isCusp_of_mem_totalFibre F hx hp
  have hl : ¬ F.IsLeftCusp p := fun h => hc h.1
  have hr : ¬ F.IsRightCusp p := fun h => hc h.1
  simp [afterBits, hl, hr]

/-- `F.eval` is continuous on `Fin c × ℝ` (the circle index is discrete) -/
theorem s1a_continuous_eval : Continuous (fun q : Param F.c => F.eval q) := by
  rw [continuous_iff_continuousAt]
  rintro ⟨i, t⟩
  have hopen : IsOpen ((Prod.fst : Param F.c → Fin F.c) ⁻¹' {i}) :=
    (isOpen_discrete _).preimage continuous_fst
  have hev : (fun q : Param F.c => (F.comp i).γ q.2) =ᶠ[nhds (i, t)] (fun q => F.eval q) := by
    filter_upwards [hopen.mem_nhds (by simp)] with q hq
    have hq1 : q.1 = i := hq
    show (F.comp i).γ q.2 = (F.comp q.1).γ q.2
    rw [hq1]
  exact ((F.comp i).continuous.comp continuous_snd).continuousAt.congr hev

end S1aHelpers

/-- LEAF (S1): the sorted fibre list is determined by its specification: a nodup list of exactly the fibre points,
sorted in the "before" order, is `fibreListBefore` (`List.Perm.eq_of_pairwise`; two fibre points with equal
height and slope would be a double point with equal slopes, against `slope_ne_of_isDouble`). -/
theorem fibreListBefore_eq_of (x₀ : ℝ) (L : List (Param F.c)) (hnd : L.Nodup)
    (hmem : ∀ p, p ∈ L ↔ p ∈ totalFibre F x₀) (hsort : L.Pairwise (fun p q => beforeLE F p q = true)) :
    fibreListBefore F x₀ = L := by
  have hperm : List.Perm (fibreListBefore F x₀) L := by
    rw [List.perm_ext_iff_of_nodup (fibreListBefore_nodup F x₀) hnd]
    intro p
    rw [mem_fibreListBefore, hmem]
  exact List.Perm.eq_of_pairwise
    (fun p q hp hq h1 h2 =>
      s1a_beforeLE_antisymm F ((mem_fibreListBefore F x₀ p).mp hp) ((hmem q).mp hq) h1 h2)
    (fibreListBefore_pairwise F x₀) hsort hperm

/-- LEAF (S1): the same for the "after" order. -/
theorem fibreListAfter_eq_of (x₀ : ℝ) (L : List (Param F.c)) (hnd : L.Nodup)
    (hmem : ∀ p, p ∈ L ↔ p ∈ totalFibre F x₀) (hsort : L.Pairwise (fun p q => afterLE F p q = true)) :
    fibreListAfter F x₀ = L := by
  have hperm : List.Perm (fibreListAfter F x₀) L := by
    rw [List.perm_ext_iff_of_nodup (fibreListAfter_nodup F x₀) hnd]
    intro p
    rw [mem_fibreListAfter, hmem]
  exact List.Perm.eq_of_pairwise
    (fun p q hp hq h1 h2 =>
      s1a_afterLE_antisymm F ((mem_fibreListAfter F x₀ p).mp hp) ((hmem q).mp hq) h1 h2)
    (fibreListAfter_pairwise F x₀) hsort hperm

/-- LEAF (S1): over a non-singular `x₀` every fibre point is regular (`regular_of_notMem_singX`), so both orders
agree (distinct heights, `snd_injOn_totalFibre`), every point has one strand, and the cut is the list of direction
bits of the fibre sorted by height. -/
theorem fibreListAfter_eq_fibreListBefore {x₀ : ℝ} (hx : x₀ ∉ singX F) :
    fibreListAfter F x₀ = fibreListBefore F x₀ := by
  refine fibreListAfter_eq_of F x₀ _ (fibreListBefore_nodup F x₀) (mem_fibreListBefore F x₀) ?_
  have hnd : (fibreListBefore F x₀).Pairwise (fun p q => p ≠ q) := fibreListBefore_nodup F x₀
  refine (hnd.and (fibreListBefore_pairwise F x₀)).imp_of_mem ?_
  intro p q hp hq hpq
  obtain ⟨hne, hle⟩ := hpq
  have hz : ht F p ≠ ht F q := fun h =>
    hne (snd_injOn_totalFibre F hx ((mem_fibreListBefore F x₀ p).mp hp)
      ((mem_fibreListBefore F x₀ q).mp hq) h)
  unfold beforeLE at hle
  unfold afterLE
  rw [decide_eq_true_iff] at hle ⊢
  simp only [Prod.Lex.toLex_le_toLex] at hle ⊢
  rcases hle with h | ⟨h, -⟩
  · exact Or.inl h
  · exact absurd (neg_inj.mp h) hz

theorem cutBefore_eq_map_dirBit {x₀ : ℝ} (hx : x₀ ∉ singX F) :
    cutBefore F x₀ = (fibreListBefore F x₀).map (dirBit F) := by
  unfold cutBefore
  exact s1a_flatMap_eq_map _ _ _
    (fun p hp => s1a_beforeBits_eq F hx ((mem_fibreListBefore F x₀ p).mp hp))

theorem cutAfter_eq_cutBefore {x₀ : ℝ} (hx : x₀ ∉ singX F) : cutAfter F x₀ = cutBefore F x₀ := by
  rw [cutBefore_eq_map_dirBit F hx]
  unfold cutAfter
  rw [fibreListAfter_eq_fibreListBefore F hx]
  exact s1a_flatMap_eq_map _ _ _
    (fun p hp => s1a_afterBits_eq F hx ((mem_fibreListBefore F x₀ p).mp hp))

theorem entriesBefore_eq_of_notMem_singX {x₀ : ℝ} (hx : x₀ ∉ singX F) :
    entriesBefore F x₀ = (fibreListBefore F x₀).map (fun p => (p, 0)) := by
  unfold entriesBefore entriesOf
  refine s1a_flatMap_eq_map _ _ _ (fun p hp => ?_)
  rw [s1a_beforeBits_eq F hx ((mem_fibreListBefore F x₀ p).mp hp)]
  rfl

/-- LEAF (S1): the local graph structure at a regular parameter: no cusp nearby, `x` injective near `t₀`, and
every `x` near `x(t₀)` has a preimage as close to `t₀` as required (continuity of the inverse; IVT on the
strictly monotone `x`, `strictMonoOn_x_of_isLeftCusp` / `strictAntiOn_x_of_isRightCusp` on the arc through `t₀`,
`exists_arc_mem`). -/
theorem regular_local_graph {i : Fin F.c} {t₀ : ℝ} (h : ¬ F.IsCusp (i, t₀)) :
    ∃ δ > 0, (∀ t ∈ Set.Ioo (t₀ - δ) (t₀ + δ), ¬ F.IsCusp (i, t)) ∧
      (∀ t₁ ∈ Set.Ioo (t₀ - δ) (t₀ + δ), ∀ t₂ ∈ Set.Ioo (t₀ - δ) (t₀ + δ), xOf F i t₁ = xOf F i t₂ → t₁ = t₂) ∧
      ∀ δ' ∈ Set.Ioc (0 : ℝ) δ, ∃ η > 0, ∀ x, |x - xOf F i t₀| < η →
        ∃ t ∈ Set.Ioo (t₀ - δ') (t₀ + δ'), xOf F i t = x := by
  have hne : xvel F i t₀ ≠ 0 := xvel_ne_zero_of_not_isCusp F h
  obtain ⟨δ, hδ, hδcusp⟩ : ∃ δ > 0, ∀ t, dist t t₀ < δ → ¬ F.IsCusp (i, t) := by
    obtain ⟨δ, hδ, hδ'⟩ := Metric.continuousAt_iff.mp (continuous_xvel F i).continuousAt
      (|xvel F i t₀|) (abs_pos.mpr hne)
    refine ⟨δ, hδ, fun t ht hc => ?_⟩
    have h0 := (isCusp_iff_xvel_eq_zero F i t).mp hc
    have := hδ' ht
    rw [Real.dist_eq, h0, zero_sub, abs_neg] at this
    exact lt_irrefl _ this
  have hnc : ∀ t ∈ Set.Ioo (t₀ - δ) (t₀ + δ), ¬ F.IsCusp (i, t) := by
    intro t ht
    apply hδcusp t
    rw [Real.dist_eq, abs_sub_lt_iff]
    exact ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have hcont : Continuous (xOf F i) := by
    unfold xOf; exact (F.comp i).continuous.fst
  have hderiv : ∀ t, HasDerivAt (xOf F i) (xvel F i t) t := hasDerivAt_x F i
  have hinj : ∀ t₁ ∈ Set.Ioo (t₀ - δ) (t₀ + δ), ∀ t₂ ∈ Set.Ioo (t₀ - δ) (t₀ + δ),
      xOf F i t₁ = xOf F i t₂ → t₁ = t₂ := by
    have key : ∀ s t, s ∈ Set.Ioo (t₀ - δ) (t₀ + δ) → t ∈ Set.Ioo (t₀ - δ) (t₀ + δ) → s < t →
        xOf F i s = xOf F i t → False := by
      intro s t hs ht hlt hst
      obtain ⟨u, hu, hu0⟩ := exists_hasDerivAt_eq_zero hlt hcont.continuousOn hst (fun x _ => hderiv x)
      exact hnc u ⟨lt_trans hs.1 hu.1, lt_trans hu.2 ht.2⟩ ((isCusp_iff_xvel_eq_zero F i u).mpr hu0)
    intro t₁ h₁ t₂ h₂ h12
    by_contra hne'
    rcases lt_or_gt_of_ne hne' with hlt | hlt
    · exact key t₁ t₂ h₁ h₂ hlt h12
    · exact key t₂ t₁ h₂ h₁ hlt h12.symm
  refine ⟨δ, hδ, hnc, hinj, ?_⟩
  intro δ' hδ'
  have hab : t₀ - δ' / 2 ≤ t₀ + δ' / 2 := by linarith [hδ'.1]
  have hsub : Set.Icc (t₀ - δ' / 2) (t₀ + δ' / 2) ⊆ Set.Ioo (t₀ - δ) (t₀ + δ) := fun t ht =>
    ⟨by linarith [ht.1, hδ'.1, hδ'.2], by linarith [ht.2, hδ'.1, hδ'.2]⟩
  have hinjOn : Set.InjOn (xOf F i) (Set.Icc (t₀ - δ' / 2) (t₀ + δ' / 2)) :=
    fun s hs t ht hst => hinj s (hsub hs) t (hsub ht) hst
  have ha : t₀ - δ' / 2 ∈ Set.Icc (t₀ - δ' / 2) (t₀ + δ' / 2) := ⟨le_rfl, hab⟩
  have hb : t₀ + δ' / 2 ∈ Set.Icc (t₀ - δ' / 2) (t₀ + δ' / 2) := ⟨hab, le_rfl⟩
  have h0 : t₀ ∈ Set.Icc (t₀ - δ' / 2) (t₀ + δ' / 2) := ⟨by linarith [hδ'.1], by linarith [hδ'.1]⟩
  have hat : t₀ - δ' / 2 < t₀ := by linarith [hδ'.1]
  have htb : t₀ < t₀ + δ' / 2 := by linarith [hδ'.1]
  have hIcc : ∀ t ∈ Set.Icc (t₀ - δ' / 2) (t₀ + δ' / 2), t ∈ Set.Ioo (t₀ - δ') (t₀ + δ') := fun t ht =>
    ⟨by linarith [ht.1, hδ'.1], by linarith [ht.2, hδ'.1]⟩
  rcases hcont.continuousOn.strictMonoOn_of_injOn_Icc' hab hinjOn with hmono | hanti
  · have h1 : xOf F i (t₀ - δ' / 2) < xOf F i t₀ := hmono ha h0 hat
    have h2 : xOf F i t₀ < xOf F i (t₀ + δ' / 2) := hmono h0 hb htb
    refine ⟨min (xOf F i t₀ - xOf F i (t₀ - δ' / 2)) (xOf F i (t₀ + δ' / 2) - xOf F i t₀),
      lt_min (by linarith) (by linarith), fun x hx => ?_⟩
    have hx1 := lt_of_lt_of_le hx (min_le_left _ _)
    have hx2 := lt_of_lt_of_le hx (min_le_right _ _)
    rw [abs_sub_lt_iff] at hx1 hx2
    have hmem : x ∈ Set.Icc (xOf F i (t₀ - δ' / 2)) (xOf F i (t₀ + δ' / 2)) :=
      ⟨by linarith [hx1.2], by linarith [hx2.1]⟩
    obtain ⟨t, ht, hxt⟩ := intermediate_value_Icc hab hcont.continuousOn hmem
    exact ⟨t, hIcc t ht, hxt⟩
  · have h1 : xOf F i t₀ < xOf F i (t₀ - δ' / 2) := hanti ha h0 hat
    have h2 : xOf F i (t₀ + δ' / 2) < xOf F i t₀ := hanti h0 hb htb
    refine ⟨min (xOf F i (t₀ - δ' / 2) - xOf F i t₀) (xOf F i t₀ - xOf F i (t₀ + δ' / 2)),
      lt_min (by linarith) (by linarith), fun x hx => ?_⟩
    have hx1 := lt_of_lt_of_le hx (min_le_left _ _)
    have hx2 := lt_of_lt_of_le hx (min_le_right _ _)
    rw [abs_sub_lt_iff] at hx1 hx2
    have hmem : x ∈ Set.Icc (xOf F i (t₀ + δ' / 2)) (xOf F i (t₀ - δ' / 2)) :=
      ⟨by linarith [hx2.2], by linarith [hx1.1]⟩
    obtain ⟨t, ht, hxt⟩ := intermediate_value_Icc' hab hcont.continuousOn hmem
    exact ⟨t, hIcc t ht, hxt⟩

/-- LEAF (S1, compactness): all fibre points over `x` near `x₀` lie (modulo the period) within `δ` of a fibre point
over `x₀` on the same circle — no strand appears from nowhere (`IsCompact.exists_isMinOn` of `|x − x₀|` on the
compact set of parameters of `Fin c × [0,1]` at distance `≥ δ` from the fibre). -/
theorem exists_eta_fibre_near (x₀ : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ η > 0, ∀ x, |x - x₀| < η → ∀ q ∈ totalFibre F x, ∃ p ∈ totalFibre F x₀, q.1 = p.1 ∧
      ∃ n : ℤ, |q.2 + n - p.2| < δ := by
  classical
  -- the open set of parameters close (modulo the period) to a fibre point over `x₀` on the same circle
  let U : Set (Param F.c) :=
    ⋃ p ∈ totalFibre F x₀, ⋃ n : ℤ, {q : Param F.c | q.1 = p.1 ∧ |q.2 + n - p.2| < δ}
  have hU : IsOpen U := by
    refine isOpen_biUnion fun p _ => isOpen_iUnion fun n => ?_
    have h1 : IsOpen {q : Param F.c | q.1 = p.1} :=
      (isOpen_discrete ({p.1} : Set (Fin F.c))).preimage continuous_fst
    have h2 : IsOpen {q : Param F.c | |q.2 + n - p.2| < δ} :=
      isOpen_lt (((continuous_snd.add continuous_const).sub continuous_const).abs) continuous_const
    exact h1.inter h2
  have hmemU : ∀ q, q ∈ U ↔ ∃ p ∈ totalFibre F x₀, q.1 = p.1 ∧ ∃ n : ℤ, |q.2 + n - p.2| < δ := by
    intro q
    simp only [U, Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop]
    constructor
    · rintro ⟨p, hp, n, h1, h2⟩; exact ⟨p, hp, h1, n, h2⟩
    · rintro ⟨p, hp, h1, n, h2⟩; exact ⟨p, hp, n, h1, h2⟩
  -- the compact set of parameters of the fundamental period far from the fibre
  let K : Set (Param F.c) := ((Set.univ : Set (Fin F.c)) ×ˢ Set.Icc (0 : ℝ) 1) \ U
  have hK : IsCompact K := (isCompact_univ.prod isCompact_Icc).diff hU
  have hcont : ContinuousOn (fun q : Param F.c => |(F.eval q).1 - x₀|) K :=
    (((s1a_continuous_eval F).fst.sub continuous_const).abs).continuousOn
  have hpos : ∀ q ∈ K, (0 : ℝ) < |(F.eval q).1 - x₀| := by
    intro q hq
    rw [abs_pos, sub_ne_zero]
    intro hx
    apply hq.2
    rw [hmemU]
    refine ⟨SameParam.rep q, ⟨SameParam.rep_mem_Ico q, ?_⟩, rfl, -⌊q.2⌋, ?_⟩
    · rw [SmoothFront.eval_of_sameParam (SameParam.sameParam_rep q)]; exact hx
    · show |q.2 + ((-⌊q.2⌋ : ℤ) : ℝ) - Int.fract q.2| < δ
      have h0 : q.2 + ((-⌊q.2⌋ : ℤ) : ℝ) - Int.fract q.2 = 0 := by
        rw [Int.cast_neg, ← Int.self_sub_floor]; ring
      rw [h0, abs_zero]; exact hδ
  obtain ⟨η, hη, hηK⟩ := hK.exists_forall_le' hcont hpos
  refine ⟨η, hη, fun x hx q hq => ?_⟩
  by_contra hcon
  have hqK : q ∈ K :=
    ⟨Set.mem_prod.mpr ⟨Set.mem_univ _, hq.1.1, hq.1.2.le⟩, fun hU' => hcon ((hmemU q).mp hU')⟩
  have := hηK q hqK
  rw [hq.2] at this
  linarith

/-! MERGER (W3S_Merged, 2026-09-14): the S2 and S3 leaves (skeleton L14952-14994) are placed here, BEFORE the S1b helpers, because the S1 one-sided limits use their statements (PLAN §4: S1 depends on S2, S3). Text verbatim. -/

/-! #### S2 leaves: the cusp local model -/

/-! ### S2 helpers -/
section S2Helpers

open Filter Topology

/-- a function differentiable everywhere with positive derivative on `Ioo a b` is strictly increasing on
`Icc a b` (`strictMonoOn_of_deriv_pos`) -/
theorem s2_strictMonoOn_Icc {f f' : ℝ → ℝ} (hf : ∀ t, HasDerivAt f (f' t) t) {a b : ℝ}
    (hpos : ∀ t ∈ Set.Ioo a b, 0 < f' t) : StrictMonoOn f (Set.Icc a b) := by
  refine strictMonoOn_of_deriv_pos (convex_Icc a b)
    (fun t _ => (hf t).continuousAt.continuousWithinAt) ?_
  intro t ht
  rw [interior_Icc] at ht
  rw [(hf t).deriv]
  exact hpos t ht

/-- mirror: negative derivative on `Ioo a b` gives strictly decreasing on `Icc a b` -/
theorem s2_strictAntiOn_Icc {f f' : ℝ → ℝ} (hf : ∀ t, HasDerivAt f (f' t) t) {a b : ℝ}
    (hneg : ∀ t ∈ Set.Ioo a b, f' t < 0) : StrictAntiOn f (Set.Icc a b) := by
  refine strictAntiOn_of_deriv_neg (convex_Icc a b)
    (fun t _ => (hf t).continuousAt.continuousWithinAt) ?_
  intro t ht
  rw [interior_Icc] at ht
  rw [(hf t).deriv]
  exact hneg t ht

/-- a function vanishing at `t₀` with positive derivative near `t₀` is negative just before and positive
just after -/
theorem s2_neg_pos_of_deriv_pos {f f' : ℝ → ℝ} (hf : ∀ t, HasDerivAt f (f' t) t) {t₀ δ : ℝ}
    (h0 : f t₀ = 0) (hpos : ∀ t ∈ Set.Ioo (t₀ - δ) (t₀ + δ), 0 < f' t) :
    ∀ t ∈ Set.Ioo (t₀ - δ) (t₀ + δ), (t < t₀ → f t < 0) ∧ (t₀ < t → 0 < f t) := by
  intro t ht
  constructor
  · intro hlt
    have hm : StrictMonoOn f (Set.Icc (t₀ - δ) t₀) :=
      s2_strictMonoOn_Icc hf fun s hs => hpos s ⟨hs.1, by linarith [hs.2, ht.1, ht.2]⟩
    have := hm ⟨ht.1.le, hlt.le⟩ ⟨by linarith [ht.1], le_rfl⟩ hlt
    linarith
  · intro hgt
    have hm : StrictMonoOn f (Set.Icc t₀ (t₀ + δ)) :=
      s2_strictMonoOn_Icc hf fun s hs => hpos s ⟨by linarith [hs.1, ht.1, ht.2], hs.2⟩
    have := hm ⟨le_rfl, by linarith [ht.2]⟩ ⟨hgt.le, ht.2.le⟩ hgt
    linarith

/-- a function vanishing at `t₀` whose derivative is negative just before and positive just after is
positive on both sides -/
theorem s2_pos_of_deriv_neg_pos {f f' : ℝ → ℝ} (hf : ∀ t, HasDerivAt f (f' t) t) {t₀ δ : ℝ}
    (h0 : f t₀ = 0)
    (hsgn : ∀ t ∈ Set.Ioo (t₀ - δ) (t₀ + δ), (t < t₀ → f' t < 0) ∧ (t₀ < t → 0 < f' t)) :
    ∀ t ∈ Set.Ioo (t₀ - δ) (t₀ + δ), t ≠ t₀ → 0 < f t := by
  intro t ht hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hm : StrictAntiOn f (Set.Icc (t₀ - δ) t₀) :=
      s2_strictAntiOn_Icc hf fun s hs => (hsgn s ⟨hs.1, by linarith [hs.2, ht.1, ht.2]⟩).1 hs.2
    have := hm ⟨ht.1.le, hlt.le⟩ ⟨by linarith [ht.1], le_rfl⟩ hlt
    linarith
  · have hm : StrictMonoOn f (Set.Icc t₀ (t₀ + δ)) :=
      s2_strictMonoOn_Icc hf fun s hs => (hsgn s ⟨by linarith [hs.1, ht.1, ht.2], hs.2⟩).2 hs.1
    have := hm ⟨le_rfl, by linarith [ht.2]⟩ ⟨hgt.le, ht.2.le⟩ hgt
    linarith

/-- a function whose derivative is positive near `t₀` except possibly at `t₀` itself is smaller before `t₀`
than after -/
theorem s2_lt_of_deriv_pos_off {f f' : ℝ → ℝ} (hf : ∀ t, HasDerivAt f (f' t) t) {t₀ δ : ℝ}
    (hpos : ∀ t ∈ Set.Ioo (t₀ - δ) (t₀ + δ), t ≠ t₀ → 0 < f' t) {t₁ t₂ : ℝ}
    (h1 : t₀ - δ < t₁) (h2 : t₁ < t₀) (h3 : t₀ < t₂) (h4 : t₂ < t₀ + δ) : f t₁ < f t₂ := by
  have hm1 : StrictMonoOn f (Set.Icc (t₀ - δ) t₀) :=
    s2_strictMonoOn_Icc hf fun s hs => hpos s ⟨hs.1, by linarith [hs.2]⟩ hs.2.ne
  have hm2 : StrictMonoOn f (Set.Icc t₀ (t₀ + δ)) :=
    s2_strictMonoOn_Icc hf fun s hs => hpos s ⟨by linarith [hs.1], hs.2⟩ hs.1.ne'
  have a := hm1 ⟨h1.le, h2.le⟩ ⟨by linarith, le_rfl⟩ h2
  have b := hm2 ⟨le_rfl, by linarith⟩ ⟨h3.le, h4.le⟩ h3
  linarith

/-- the cubic sign law: `φ' (t₀) = φ'' (t₀) = 0`, `φ''' (t₀) > 0`, `φ'''` continuous ⇒ near `t₀`, `φ` is
smaller before `t₀` than after (`φ'''` positive ⇒ `φ''` negative/positive ⇒ `φ'` positive off `t₀`) -/
theorem s2_cubic_lt {φ φ1 φ2 φ3 : ℝ → ℝ} {t₀ : ℝ} (h0 : ∀ t, HasDerivAt φ (φ1 t) t)
    (h1 : ∀ t, HasDerivAt φ1 (φ2 t) t) (h2 : ∀ t, HasDerivAt φ2 (φ3 t) t) (h3 : Continuous φ3)
    (hφ1 : φ1 t₀ = 0) (hφ2 : φ2 t₀ = 0) (hK : 0 < φ3 t₀) :
    ∃ δ > 0, ∀ t₁ t₂, t₀ - δ < t₁ → t₁ < t₀ → t₀ < t₂ → t₂ < t₀ + δ → φ t₁ < φ t₂ := by
  have hev : ∀ᶠ t in 𝓝 t₀, 0 < φ3 t := h3.continuousAt.eventually (lt_mem_nhds hK)
  rw [Metric.eventually_nhds_iff] at hev
  obtain ⟨δ, hδ, hev⟩ := hev
  have hpos3 : ∀ t ∈ Set.Ioo (t₀ - δ) (t₀ + δ), 0 < φ3 t := fun t ht =>
    hev (by rw [Real.dist_eq, abs_lt]; constructor <;> linarith [ht.1, ht.2])
  have hsgn2 := s2_neg_pos_of_deriv_pos h2 hφ2 hpos3
  have hpos1 := s2_pos_of_deriv_neg_pos h1 hφ1 hsgn2
  exact ⟨δ, hδ, fun t₁ t₂ a b c d => s2_lt_of_deriv_pos_off h0 hpos1 a b c d⟩

/-- the cubic sign law, both signs: `φ (t₁) < φ (t₂)` iff `φ''' (t₀) > 0` -/
theorem s2_cubic_iff {φ φ1 φ2 φ3 : ℝ → ℝ} {t₀ : ℝ} (h0 : ∀ t, HasDerivAt φ (φ1 t) t)
    (h1 : ∀ t, HasDerivAt φ1 (φ2 t) t) (h2 : ∀ t, HasDerivAt φ2 (φ3 t) t) (h3 : Continuous φ3)
    (hφ1 : φ1 t₀ = 0) (hφ2 : φ2 t₀ = 0) (hK : φ3 t₀ ≠ 0) :
    ∃ δ > 0, ∀ t₁ t₂, t₀ - δ < t₁ → t₁ < t₀ → t₀ < t₂ → t₂ < t₀ + δ → (φ t₁ < φ t₂ ↔ 0 < φ3 t₀) := by
  rcases lt_or_gt_of_ne hK with hneg | hpos
  · obtain ⟨δ, hδ, hlt⟩ := s2_cubic_lt (φ := fun t => -φ t) (φ1 := fun t => -φ1 t)
      (φ2 := fun t => -φ2 t) (φ3 := fun t => -φ3 t) (t₀ := t₀) (fun t => (h0 t).neg)
      (fun t => (h1 t).neg) (fun t => (h2 t).neg) h3.neg (by rw [hφ1, neg_zero]) (by rw [hφ2, neg_zero])
      (neg_pos.mpr hneg)
    refine ⟨δ, hδ, fun t₁ t₂ a b c d => ?_⟩
    have : -φ t₁ < -φ t₂ := hlt t₁ t₂ a b c d
    exact iff_of_false (by linarith) (by linarith)
  · obtain ⟨δ, hδ, hlt⟩ := s2_cubic_lt h0 h1 h2 h3 hφ1 hφ2 hpos
    exact ⟨δ, hδ, fun t₁ t₂ a b c d => iff_of_true (hlt t₁ t₂ a b c d) hpos⟩

/-- the first component of a plane-valued derivative -/
theorem s2_hasDerivAt_fst {f : ℝ → Plane} {f' : Plane} {t : ℝ} (h : HasDerivAt f f' t) :
    HasDerivAt (fun s => (f s).1) f'.1 t := h.fst

/-- the second component of a plane-valued derivative -/
theorem s2_hasDerivAt_snd {f : ℝ → Plane} {f' : Plane} {t : ℝ} (h : HasDerivAt f f' t) :
    HasDerivAt (fun s => (f s).2) f'.2 t := h.snd

/-- `γ'` has derivative `γ''` -/
theorem s2_hasDerivAt_deriv (L : SmoothLoop) (t : ℝ) :
    HasDerivAt (deriv L.γ) (iteratedDeriv 2 L.γ t) t := by
  have hd : Differentiable ℝ (deriv L.γ) := by
    have := L.contDiff_iteratedDeriv 1
    rw [iteratedDeriv_one] at this
    exact this.differentiable (by decide)
  have := (hd t).hasDerivAt
  rwa [show deriv (deriv L.γ) t = iteratedDeriv 2 L.γ t by rw [iteratedDeriv_succ, iteratedDeriv_one]] at this

/-- `γ''` has derivative `γ'''` -/
theorem s2_hasDerivAt_iteratedDeriv_two (L : SmoothLoop) (t : ℝ) :
    HasDerivAt (iteratedDeriv 2 L.γ) (iteratedDeriv 3 L.γ t) t := by
  have hd : Differentiable ℝ (iteratedDeriv 2 L.γ) :=
    (L.contDiff_iteratedDeriv 2).differentiable (by decide)
  have := (hd t).hasDerivAt
  rwa [show deriv (iteratedDeriv 2 L.γ) t = iteratedDeriv 3 L.γ t from
    (congrFun (iteratedDeriv_succ (n := 2) (f := L.γ)) t).symm] at this

/-- the combination `z − k·x` of a plane-valued function has derivative `z' − k·x'` -/
theorem s2_hasDerivAt_comb {f : ℝ → Plane} {f' : Plane} {t : ℝ} (h : HasDerivAt f f' t) (k : ℝ) :
    HasDerivAt (fun s => (f s).2 - k * (f s).1) (f'.2 - k * f'.1) t :=
  (s2_hasDerivAt_snd h).sub ((s2_hasDerivAt_fst h).const_mul k)

/-- the cusp sign law for one smooth loop: at a zero `t₀` of `γ'` with `x'' ≠ 0` and `det(γ'', γ''') ≠ 0`, two
parameters `t₁ < t₀ < t₂` near `t₀` with equal `x` have `z (t₁) < z (t₂)` iff `x'' · det(γ'', γ''') > 0`.
Proof: with `(a, c) = γ''(t₀)`, the function `φ = z − (c/a) x` has `φ' (t₀) = φ'' (t₀) = 0` and
`φ''' (t₀) = det(γ'', γ''')/a`, and `z (t₂) − z (t₁) = φ (t₂) − φ (t₁)` when `x (t₁) = x (t₂)`. -/
theorem s2_loop_cusp_sign (L : SmoothLoop) {t₀ : ℝ} (h : deriv L.γ t₀ = 0)
    (ha : (iteratedDeriv 2 L.γ t₀).1 ≠ 0)
    (hdet : det (iteratedDeriv 2 L.γ t₀) (iteratedDeriv 3 L.γ t₀) ≠ 0) :
    ∃ δ > 0, ∀ t₁ t₂, t₀ - δ < t₁ → t₁ < t₀ → t₀ < t₂ → t₂ < t₀ + δ → (L.γ t₁).1 = (L.γ t₂).1 →
      ((L.γ t₁).2 < (L.γ t₂).2 ↔
        0 < (iteratedDeriv 2 L.γ t₀).1 * det (iteratedDeriv 2 L.γ t₀) (iteratedDeriv 3 L.γ t₀)) := by
  obtain ⟨a, ha_def⟩ : ∃ a, a = (iteratedDeriv 2 L.γ t₀).1 := ⟨_, rfl⟩
  obtain ⟨c, hc_def⟩ : ∃ c, c = (iteratedDeriv 2 L.γ t₀).2 := ⟨_, rfl⟩
  obtain ⟨b, hb_def⟩ : ∃ b, b = (iteratedDeriv 3 L.γ t₀).1 := ⟨_, rfl⟩
  obtain ⟨d, hd_def⟩ : ∃ d, d = (iteratedDeriv 3 L.γ t₀).2 := ⟨_, rfl⟩
  have hdet'' : det (iteratedDeriv 2 L.γ t₀) (iteratedDeriv 3 L.γ t₀) = a * d - c * b := by
    unfold det; rw [← ha_def, ← hb_def, ← hc_def, ← hd_def]
  rw [hdet''] at hdet ⊢
  rw [← ha_def] at ha ⊢
  have e0 : ∀ t, HasDerivAt (fun t => (L.γ t).2 - c / a * (L.γ t).1)
      ((deriv L.γ t).2 - c / a * (deriv L.γ t).1) t := fun t => s2_hasDerivAt_comb (L.hasDerivAt t) _
  have e1 : ∀ t, HasDerivAt (fun t => (deriv L.γ t).2 - c / a * (deriv L.γ t).1)
      ((iteratedDeriv 2 L.γ t).2 - c / a * (iteratedDeriv 2 L.γ t).1) t :=
    fun t => s2_hasDerivAt_comb (s2_hasDerivAt_deriv L t) _
  have e2 : ∀ t, HasDerivAt (fun t => (iteratedDeriv 2 L.γ t).2 - c / a * (iteratedDeriv 2 L.γ t).1)
      ((iteratedDeriv 3 L.γ t).2 - c / a * (iteratedDeriv 3 L.γ t).1) t :=
    fun t => s2_hasDerivAt_comb (s2_hasDerivAt_iteratedDeriv_two L t) _
  have e3 : Continuous (fun t => (iteratedDeriv 3 L.γ t).2 - c / a * (iteratedDeriv 3 L.γ t).1) :=
    (L.continuous_iteratedDeriv 3).snd.sub ((L.continuous_iteratedDeriv 3).fst.const_mul _)
  have hφ1 : (deriv L.γ t₀).2 - c / a * (deriv L.γ t₀).1 = 0 := by
    rw [h, Prod.snd_zero, Prod.fst_zero, mul_zero, sub_zero]
  have hφ2 : (iteratedDeriv 2 L.γ t₀).2 - c / a * (iteratedDeriv 2 L.γ t₀).1 = 0 := by
    rw [← ha_def, ← hc_def, div_mul_cancel₀ c ha, sub_self]
  have hK : (iteratedDeriv 3 L.γ t₀).2 - c / a * (iteratedDeriv 3 L.γ t₀).1 = (a * d - c * b) / a := by
    rw [← hb_def, ← hd_def, sub_div, mul_div_cancel_left₀ d ha, div_mul_eq_mul_div]
  have hK0 : (iteratedDeriv 3 L.γ t₀).2 - c / a * (iteratedDeriv 3 L.γ t₀).1 ≠ 0 := by
    rw [hK]; exact div_ne_zero hdet ha
  obtain ⟨δ, hδ, hiff⟩ := s2_cubic_iff e0 e1 e2 e3 hφ1 hφ2 hK0
  refine ⟨δ, hδ, fun t₁ t₂ h1 h2 h3 h4 hx => ?_⟩
  have key := hiff t₁ t₂ h1 h2 h3 h4
  rw [hK] at key
  have key' : (L.γ t₁).2 - c / a * (L.γ t₂).1 < (L.γ t₂).2 - c / a * (L.γ t₂).1 ↔ 0 < (a * d - c * b) / a := by
    rw [hx] at key; exact key
  have hsq : 0 < a ^ 2 := by positivity
  have heq : (a * d - c * b) / a * a ^ 2 = a * (a * d - c * b) := by
    rw [div_mul_eq_mul_div, pow_two, ← mul_assoc, mul_div_assoc, div_self ha, mul_one, mul_comm]
  rw [← heq, mul_pos_iff_of_pos_right hsq, ← key']
  exact (sub_lt_sub_iff_right _).symm

/-- a point of the open `δ`-interval around `t₀` is at distance `< δ` -/
theorem s2_dist_lt_of_mem_Ioo {t₀ δ t : ℝ} (ht : t ∈ Set.Ioo (t₀ - δ) (t₀ + δ)) : dist t t₀ < δ := by
  rw [Real.dist_eq, abs_lt]; constructor <;> linarith [ht.1, ht.2]

/-- a strict local minimum from the sign of the derivative: negative before `t₀`, positive after
(within distance `δ`) gives strictly decreasing on `Ioc (t₀ − δ) t₀` and strictly increasing on
`Ico t₀ (t₀ + δ)` -/
theorem s2_local_min_of_sign {f f' : ℝ → ℝ} (hf : ∀ t, HasDerivAt f (f' t) t) {t₀ δ : ℝ}
    (hsgn : ∀ t, dist t t₀ < δ → (t < t₀ → f' t < 0) ∧ (t₀ < t → 0 < f' t)) :
    StrictAntiOn f (Set.Ioc (t₀ - δ) t₀) ∧ StrictMonoOn f (Set.Ico t₀ (t₀ + δ)) := by
  constructor
  · refine (s2_strictAntiOn_Icc hf fun t ht => ?_).mono Set.Ioc_subset_Icc_self
    exact (hsgn t (s2_dist_lt_of_mem_Ioo ⟨ht.1, by linarith [ht.1, ht.2]⟩)).1 ht.2
  · refine (s2_strictMonoOn_Icc hf fun t ht => ?_).mono Set.Ico_subset_Icc_self
    exact (hsgn t (s2_dist_lt_of_mem_Ioo ⟨by linarith [ht.1, ht.2], ht.2⟩)).2 ht.1

/-- mirror: a strict local maximum from the sign of the derivative -/
theorem s2_local_max_of_sign {f f' : ℝ → ℝ} (hf : ∀ t, HasDerivAt f (f' t) t) {t₀ δ : ℝ}
    (hsgn : ∀ t, dist t t₀ < δ → (t < t₀ → 0 < f' t) ∧ (t₀ < t → f' t < 0)) :
    StrictMonoOn f (Set.Ioc (t₀ - δ) t₀) ∧ StrictAntiOn f (Set.Ico t₀ (t₀ + δ)) := by
  constructor
  · refine (s2_strictMonoOn_Icc hf fun t ht => ?_).mono Set.Ioc_subset_Icc_self
    exact (hsgn t (s2_dist_lt_of_mem_Ioo ⟨ht.1, by linarith [ht.1, ht.2]⟩)).1 ht.2
  · refine (s2_strictAntiOn_Icc hf fun t ht => ?_).mono Set.Ico_subset_Icc_self
    exact (hsgn t (s2_dist_lt_of_mem_Ioo ⟨by linarith [ht.1, ht.2], ht.2⟩)).2 ht.1

/-- at a strict local minimum of a continuous function (decreasing on `Ioc (t₀ − δ) t₀`, increasing on
`Ico t₀ (t₀ + δ)`) every value slightly above `f t₀` is taken on both sides, as close to `t₀` as required
(IVT on each side) -/
theorem s2_arms_of_local_min {f : ℝ → ℝ} (hf : Continuous f) {t₀ δ : ℝ} (hδ : 0 < δ)
    (hanti : StrictAntiOn f (Set.Ioc (t₀ - δ) t₀)) (hmono : StrictMonoOn f (Set.Ico t₀ (t₀ + δ)))
    {δ' : ℝ} (hδ' : 0 < δ') :
    ∃ η > 0, ∀ x ∈ Set.Ioo (f t₀) (f t₀ + η),
      (∃ t₁ ∈ Set.Ioo (t₀ - δ') t₀, f t₁ = x) ∧ ∃ t₂ ∈ Set.Ioo t₀ (t₀ + δ'), f t₂ = x := by
  obtain ⟨ε, hε, hεδ, hεδ'⟩ : ∃ ε, 0 < ε ∧ ε < δ ∧ ε < δ' :=
    ⟨min δ δ' / 2, by positivity, by linarith [min_le_left δ δ'], by linarith [min_le_right δ δ']⟩
  have hL : f t₀ < f (t₀ - ε) :=
    hanti ⟨by linarith, by linarith⟩ ⟨by linarith, le_rfl⟩ (by linarith)
  have hR : f t₀ < f (t₀ + ε) :=
    hmono ⟨le_rfl, by linarith⟩ ⟨by linarith, by linarith⟩ (by linarith)
  refine ⟨min (f (t₀ - ε) - f t₀) (f (t₀ + ε) - f t₀), by positivity, fun x hx => ⟨?_, ?_⟩⟩
  · have hx' : x ∈ Set.Ioo (f t₀) (f (t₀ - ε)) := ⟨hx.1, by linarith [hx.2, min_le_left (f (t₀ - ε) - f t₀) (f (t₀ + ε) - f t₀)]⟩
    obtain ⟨t₁, ht₁, rfl⟩ := intermediate_value_Ioo' (by linarith : t₀ - ε ≤ t₀) hf.continuousOn hx'
    exact ⟨t₁, ⟨by linarith [ht₁.1], ht₁.2⟩, rfl⟩
  · have hx' : x ∈ Set.Ioo (f t₀) (f (t₀ + ε)) := ⟨hx.1, by linarith [hx.2, min_le_right (f (t₀ - ε) - f t₀) (f (t₀ + ε) - f t₀)]⟩
    obtain ⟨t₂, ht₂, rfl⟩ := intermediate_value_Ioo (by linarith : t₀ ≤ t₀ + ε) hf.continuousOn hx'
    exact ⟨t₂, ⟨ht₂.1, by linarith [ht₂.2]⟩, rfl⟩

/-- mirror: at a strict local maximum every value slightly below `f t₀` is taken on both sides -/
theorem s2_arms_of_local_max {f : ℝ → ℝ} (hf : Continuous f) {t₀ δ : ℝ} (hδ : 0 < δ)
    (hmono : StrictMonoOn f (Set.Ioc (t₀ - δ) t₀)) (hanti : StrictAntiOn f (Set.Ico t₀ (t₀ + δ)))
    {δ' : ℝ} (hδ' : 0 < δ') :
    ∃ η > 0, ∀ x ∈ Set.Ioo (f t₀ - η) (f t₀),
      (∃ t₁ ∈ Set.Ioo (t₀ - δ') t₀, f t₁ = x) ∧ ∃ t₂ ∈ Set.Ioo t₀ (t₀ + δ'), f t₂ = x := by
  have hanti' : StrictAntiOn (fun t => -f t) (Set.Ioc (t₀ - δ) t₀) :=
    fun a ha b hb hab => neg_lt_neg (hmono ha hb hab)
  have hmono' : StrictMonoOn (fun t => -f t) (Set.Ico t₀ (t₀ + δ)) :=
    fun a ha b hb hab => neg_lt_neg (hanti ha hb hab)
  obtain ⟨η, hη, harms⟩ := s2_arms_of_local_min (f := fun t => -f t) hf.neg hδ hanti' hmono' hδ'
  refine ⟨η, hη, fun x hx => ?_⟩
  obtain ⟨⟨t₁, ht₁, e₁⟩, ⟨t₂, ht₂, e₂⟩⟩ :=
    harms (-x) ⟨by show -f t₀ < -x; linarith [hx.2], by show -x < -f t₀ + η; linarith [hx.1]⟩
  exact ⟨⟨t₁, ht₁, by simpa using e₁⟩, ⟨t₂, ht₂, by simpa using e₂⟩⟩

end S2Helpers

/-- LEAF (S2, Taylor): the two arms of a cusp at equal `x` — the later arm is the higher one iff `0 < cuspDisc`
(FR-2).  Truth: with `γ'' = (a, c)`, `γ''' = (b, d)`, matched arms `t₁ < t₀ < t₂` satisfy
`z(t₂) − z(t₁) = u³ (ad − bc)/(3a) + o(u³)`, whose sign is that of `a·det(γ'', γ''') = cuspDisc`
(checked numerically, W3_U8R_PLAN.md §2). -/
theorem cusp_arm_sign {i : Fin F.c} {t₀ : ℝ} (h : F.IsCusp (i, t₀)) :
    ∃ δ > 0, ∀ t₁ t₂, t₀ - δ < t₁ → t₁ < t₀ → t₀ < t₂ → t₂ < t₀ + δ → xOf F i t₁ = xOf F i t₂ →
      (zOf F i t₁ < zOf F i t₂ ↔ 0 < F.cuspDisc (i, t₀)) := by
  have h' : deriv (F.comp i).γ t₀ = 0 := h
  have ha := F.acc_fst_ne_zero_of_isCusp h
  have hdet := F.det_acc_jerk_ne_zero_of_isCusp h
  rw [SmoothFront.acc_def] at ha
  rw [SmoothFront.acc_def, SmoothFront.jerk_def] at hdet
  obtain ⟨δ, hδ, hs⟩ := s2_loop_cusp_sign (F.comp i) h' ha hdet
  refine ⟨δ, hδ, fun t₁ t₂ h1 h2 h3 h4 hx => ?_⟩
  have key := hs t₁ t₂ h1 h2 h3 h4 hx
  unfold SmoothFront.cuspDisc
  rw [SmoothFront.acc_def, SmoothFront.jerk_def]
  exact key

/-- LEAF (S2): at a left cusp `x` has a strict local minimum — strictly decreasing before, increasing after — and no
other cusp lies nearby (`exists_no_cusp_near`, the arc monotonicity of §G on the two arcs meeting at the cusp). -/
theorem leftCusp_x_local {i : Fin F.c} {t₀ : ℝ} (h : F.IsLeftCusp (i, t₀)) :
    ∃ δ > 0, (∀ t ∈ Set.Ioo (t₀ - δ) (t₀ + δ), t ≠ t₀ → ¬ F.IsCusp (i, t)) ∧
      StrictAntiOn (xOf F i) (Set.Ioc (t₀ - δ) t₀) ∧ StrictMonoOn (xOf F i) (Set.Ico t₀ (t₀ + δ)) := by
  obtain ⟨δ, hδ, hs⟩ := exists_xvel_sign_of_isLeftCusp F h
  refine ⟨δ, hδ, fun t ht hne hc => ?_, s2_local_min_of_sign (hasDerivAt_x F i) hs⟩
  have h0 := (isCusp_iff_xvel_eq_zero F i t).mp hc
  have hs' := hs t (s2_dist_lt_of_mem_Ioo ht)
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have := hs'.1 hlt; linarith
  · have := hs'.2 hgt; linarith

/-- LEAF (S2): at a right cusp `x` has a strict local maximum. -/
theorem rightCusp_x_local {i : Fin F.c} {t₀ : ℝ} (h : F.IsRightCusp (i, t₀)) :
    ∃ δ > 0, (∀ t ∈ Set.Ioo (t₀ - δ) (t₀ + δ), t ≠ t₀ → ¬ F.IsCusp (i, t)) ∧
      StrictMonoOn (xOf F i) (Set.Ioc (t₀ - δ) t₀) ∧ StrictAntiOn (xOf F i) (Set.Ico t₀ (t₀ + δ)) := by
  obtain ⟨δ, hδ, hs⟩ := exists_xvel_sign_of_isRightCusp F h
  refine ⟨δ, hδ, fun t ht hne hc => ?_, s2_local_max_of_sign (hasDerivAt_x F i) hs⟩
  have h0 := (isCusp_iff_xvel_eq_zero F i t).mp hc
  have hs' := hs t (s2_dist_lt_of_mem_Ioo ht)
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have := hs'.1 hlt; linarith
  · have := hs'.2 hgt; linarith

/-- LEAF (S2): just right of a left cusp's x-value both arms are present, as close to the cusp parameter as
required (IVT on each monotone arm). -/
theorem leftCusp_arms {i : Fin F.c} {t₀ : ℝ} (h : F.IsLeftCusp (i, t₀)) {δ' : ℝ} (hδ' : 0 < δ') :
    ∃ η > 0, ∀ x ∈ Set.Ioo (xOf F i t₀) (xOf F i t₀ + η),
      (∃ t₁ ∈ Set.Ioo (t₀ - δ') t₀, xOf F i t₁ = x) ∧ ∃ t₂ ∈ Set.Ioo t₀ (t₀ + δ'), xOf F i t₂ = x := by
  obtain ⟨δ, hδ, -, hanti, hmono⟩ := leftCusp_x_local F h
  have hc : Continuous (xOf F i) := (F.comp i).continuous.fst
  exact s2_arms_of_local_min hc hδ hanti hmono hδ'

/-- LEAF (S2): just left of a right cusp's x-value both arms are present. -/
theorem rightCusp_arms {i : Fin F.c} {t₀ : ℝ} (h : F.IsRightCusp (i, t₀)) {δ' : ℝ} (hδ' : 0 < δ') :
    ∃ η > 0, ∀ x ∈ Set.Ioo (xOf F i t₀ - η) (xOf F i t₀),
      (∃ t₁ ∈ Set.Ioo (t₀ - δ') t₀, xOf F i t₁ = x) ∧ ∃ t₂ ∈ Set.Ioo t₀ (t₀ + δ'), xOf F i t₂ = x := by
  obtain ⟨δ, hδ, -, hmono, hanti⟩ := rightCusp_x_local F h
  have hc : Continuous (xOf F i) := (F.comp i).continuous.fst
  exact s2_arms_of_local_max hc hδ hmono hanti hδ'

/-! ### S3S5 helpers -/
section S3S5Helpers

/-- S3S5: the local graph bound at a regular parameter `r`: along the branch through `r`, `z − s·x` (with
`s = slope r`) is `o(x − x₀)` — for every `ε > 0`, within `δ` of `r.2` its variation is at most
`ε |x − x₀|` (both `hasDerivAt_iff_isLittleO` bounds, and `|x − x₀| ≥ |x'|/2 · |t − t₀|`). -/
theorem s3s5_graph_bound (r : Param F.c) (ha : xvel F r.1 r.2 ≠ 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ t, |t - r.2| < δ →
      |(zOf F r.1 t - F.slope r * xOf F r.1 t) - (zOf F r.1 r.2 - F.slope r * xOf F r.1 r.2)| ≤
        ε * |xOf F r.1 t - xOf F r.1 r.2| := by
  have hx : HasDerivAt (xOf F r.1) (xvel F r.1 r.2) r.2 := hasDerivAt_x F r.1 r.2
  have hz : HasDerivAt (zOf F r.1) (F.vel r).2 r.2 := ((F.comp r.1).hasDerivAt r.2).snd
  have hg : HasDerivAt (fun t => zOf F r.1 t - F.slope r * xOf F r.1 t) 0 r.2 := by
    have h0 : (F.vel r).2 - F.slope r * xvel F r.1 r.2 = 0 := by
      have ha' : (F.vel r).1 ≠ 0 := ha
      show (F.vel r).2 - (F.vel r).2 / (F.vel r).1 * (F.vel r).1 = 0
      rw [div_mul_cancel₀ _ ha', sub_self]
    have := hz.sub (hx.const_mul (F.slope r))
    rw [h0] at this
    exact this
  have habs : 0 < |xvel F r.1 r.2| := abs_pos.mpr ha
  have h1 := (hasDerivAt_iff_isLittleO.mp hg).def (div_pos (mul_pos hε habs) two_pos)
  have h2 := (hasDerivAt_iff_isLittleO.mp hx).def (div_pos habs two_pos)
  rw [Metric.eventually_nhds_iff] at h1 h2
  obtain ⟨δ₁, hδ₁, H1⟩ := h1
  obtain ⟨δ₂, hδ₂, H2⟩ := h2
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun t ht => ?_⟩
  have e1 := H1 (show dist t r.2 < δ₁ by rw [Real.dist_eq]; exact lt_of_lt_of_le ht (min_le_left _ _))
  have e2 := H2 (show dist t r.2 < δ₂ by rw [Real.dist_eq]; exact lt_of_lt_of_le ht (min_le_right _ _))
  simp only [smul_eq_mul, mul_zero, sub_zero, Real.norm_eq_abs] at e1 e2
  set a := xvel F r.1 r.2 with ha_def
  set X := xOf F r.1 t - xOf F r.1 r.2 with hX_def
  have e3 : |a| * |t - r.2| ≤ |X| + |X - (t - r.2) * a| := by
    rw [← abs_mul]
    calc |a * (t - r.2)| = |X - (X - (t - r.2) * a)| := by congr 1; ring
      _ ≤ |X| + |X - (t - r.2) * a| := abs_sub _ _
  calc _ ≤ ε * |a| / 2 * |t - r.2| := e1
    _ = ε * (|a| / 2 * |t - r.2|) := by ring
    _ ≤ ε * |X| := by apply mul_le_mul_of_nonneg_left _ hε.le; linarith

/-- S3S5: a list whose real key is nonincreasing splits its `z ≤ ·` filter as the `z < ·` filter followed by
the `· = z` filter. -/
theorem s3s5_filter_split {α : Type*} (f : α → ℝ) (z : ℝ) (L : List α)
    (hL : L.Pairwise (fun p q => f q ≤ f p)) :
    L.filter (fun p => decide (z ≤ f p)) =
      L.filter (fun p => decide (z < f p)) ++ L.filter (fun p => decide (f p = z)) := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    rw [List.pairwise_cons] at hL
    obtain ⟨ha, hL⟩ := hL
    have ih := ih hL
    rcases lt_trichotomy z (f a) with hlt | heq | hgt
    · rw [List.filter_cons_of_pos (by rw [decide_eq_true_eq]; exact hlt.le),
        List.filter_cons_of_pos (by rw [decide_eq_true_eq]; exact hlt),
        List.filter_cons_of_neg (by rw [decide_eq_true_eq]; exact hlt.ne'), ih, List.cons_append]
    · have h1 : L.filter (fun p => decide (z < f p)) = [] := by
        rw [List.filter_eq_nil_iff]
        intro p hp
        rw [decide_eq_true_eq]
        have := ha p hp
        linarith
      have h2 : L.filter (fun p => decide (z ≤ f p)) = L.filter (fun p => decide (f p = z)) := by
        rw [ih, h1, List.nil_append]
      rw [List.filter_cons_of_pos (by rw [decide_eq_true_eq]; exact heq.le),
        List.filter_cons_of_neg (by rw [decide_eq_true_eq, heq]; exact lt_irrefl _),
        List.filter_cons_of_pos (by rw [decide_eq_true_eq]; exact heq.symm), h1, List.nil_append, h2]
    · rw [List.filter_cons_of_neg (by rw [decide_eq_true_eq]; exact not_le.mpr hgt),
        List.filter_cons_of_neg (by rw [decide_eq_true_eq]; exact not_lt.mpr hgt.le),
        List.filter_cons_of_neg (by rw [decide_eq_true_eq]; exact hgt.ne), ih]

/-- S3S5: a nodup list with exactly the two members `a ≠ b`, sorted by `R` with `¬ R b a`, is `[a, b]`. -/
theorem s3s5_eq_pair {α : Type*} {R : α → α → Prop} {a b : α} (hab : a ≠ b) (hR : ¬ R b a) (L : List α)
    (hnd : L.Nodup) (hmem : ∀ x, x ∈ L ↔ x = a ∨ x = b) (hpw : L.Pairwise R) : L = [a, b] := by
  match L, hnd, hmem, hpw with
  | [], _, hmem, _ => exact absurd ((hmem a).mpr (Or.inl rfl)) (List.not_mem_nil)
  | [x], _, hmem, _ =>
    have h1 := (hmem a).mpr (Or.inl rfl)
    have h2 := (hmem b).mpr (Or.inr rfl)
    rw [List.mem_singleton] at h1 h2
    exact absurd (h1.trans h2.symm) hab
  | x :: y :: rest, hnd, hmem, hpw =>
    rw [List.nodup_cons, List.nodup_cons] at hnd
    obtain ⟨hx, hy, -⟩ := hnd
    have hxy : x ≠ y := fun h => hx (h ▸ List.mem_cons_self ..)
    have hx' := (hmem x).mp (List.mem_cons_self ..)
    have hy' := (hmem y).mp (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    have hrest : rest = [] := by
      rcases rest with _ | ⟨w, rest'⟩
      · rfl
      · exfalso
        have hw := (hmem w).mp (by simp)
        have hwx : w ≠ x := fun h => hx (by simp [h])
        have hwy : w ≠ y := fun h => hy (by simp [h])
        rcases hw with rfl | rfl <;> rcases hx' with rfl | rfl <;> rcases hy' with rfl | rfl <;>
          first | exact hwx rfl | exact hwy rfl | exact hxy rfl
    subst hrest
    rcases hx' with rfl | rfl <;> rcases hy' with rfl | rfl
    · exact absurd rfl hxy
    · rfl
    · exfalso
      rw [List.pairwise_cons] at hpw
      exact hR (hpw.1 _ (List.mem_cons_self ..))
    · exact absurd rfl hxy

/-- S3S5: over the x-value of a crossing `q`, the fibre points at the crossing's height are exactly its two
branches (`no_triple`). -/
theorem s3s5_mem_fibre_at_height (q : Cross F) (p : Param F.c) :
    (p ∈ totalFibre F (evX F (Sum.inr q)) ∧ ht F p = evZ F (Sum.inr q)) ↔ p = q.1.1 ∨ p = q.1.2 := by
  obtain ⟨⟨h1, h2, hne, he⟩, -⟩ := F.mem_crossingPairs'.mp q.2
  constructor
  · rintro ⟨⟨hp1, hp2⟩, hz⟩
    have hev : F.eval p = F.eval q.1.1 := Prod.ext hp2 hz
    by_contra hcon
    obtain ⟨hpa, hpb⟩ := not_or.mp hcon
    exact F.no_triple p q.1.1 q.1.2 (fun h => hpa (SameParam.eq_of_mem_Ico hp1 h1 h))
      (fun h => hne (SameParam.eq_of_mem_Ico h1 h2 h)) (fun h => hpb (SameParam.eq_of_mem_Ico hp1 h2 h)) hev he
  · rintro (rfl | rfl)
    · exact ⟨⟨h1, rfl⟩, rfl⟩
    · exact ⟨⟨h2, (congrArg Prod.fst he).symm⟩, (congrArg Prod.snd he).symm⟩

/-- S3S5: the fibre points at the height of a crossing, in the "before" order, are `[over, under]`. -/
theorem s3s5_filter_height_eq (q : Cross F) :
    (fibreListBefore F (evX F (Sum.inr q))).filter (fun p => decide (ht F p = evZ F (Sum.inr q))) =
      [q.1.1, q.1.2] := by
  obtain ⟨⟨-, -, hne, he⟩, hs⟩ := F.mem_crossingPairs'.mp q.2
  refine s3s5_eq_pair hne ?_ _ (List.Nodup.sublist List.filter_sublist (fibreListBefore_nodup F _)) ?_
    (List.Pairwise.sublist List.filter_sublist (fibreListBefore_pairwise F _))
  · show ¬ beforeLE F q.1.2 q.1.1 = true
    unfold beforeLE
    rw [decide_eq_true_eq, Prod.Lex.toLex_le_toLex]
    have hz : ht F q.1.2 = ht F q.1.1 := (congrArg Prod.snd he).symm
    simp only [hz, lt_self_iff_false, true_and, false_or]
    exact not_le.mpr hs
  · intro x
    rw [List.mem_filter, mem_fibreListBefore, decide_eq_true_eq]
    exact s3s5_mem_fibre_at_height F q x

/-- S3S5: a regular fibre point carries one strand before its x-value, with its direction bit. -/
theorem s3s5_beforeBits_of_not_isCusp {p : Param F.c} (hp : ¬ F.IsCusp p) : beforeBits F p = [dirBit F p] := by
  unfold beforeBits
  rw [ite_eq_right (fun h => hp h.1), ite_eq_right (fun h => hp h.1)]

/-- S3S5: the hybrid cut before a crossing event is `A ++ [dirBit over, dirBit under] ++ B` with
`A.length + 1 = posOf` (the fibre sorted by height splits at the crossing's height, `s3s5_filter_split`, and
the two points there are the two regular branches, over first). -/
theorem s3s5_hybridCut_cross (q : Cross F) :
    ∃ A B : Cuts, hybridCut F (evX F (Sum.inr q)) (evZ F (Sum.inr q)) =
      A ++ dirBit F q.1.1 :: dirBit F q.1.2 :: B ∧ A.length + 1 = posOf F (Sum.inr q) := by
  have hd : F.IsDouble q.1.1 q.1.2 := (F.isOverUnder_of_mem_crossingPairs q.2).1
  have hanti : (fibreListBefore F (evX F (Sum.inr q))).Pairwise (fun p p' => ht F p' ≤ ht F p) := by
    refine (fibreListBefore_pairwise F _).imp fun {p p'} h => ?_
    unfold beforeLE at h
    rw [decide_eq_true_eq, Prod.Lex.toLex_le_toLex] at h
    rcases h with h | ⟨h, -⟩
    · exact (neg_lt_neg_iff.mp h).le
    · exact (neg_inj.mp h).symm.le
  refine ⟨((fibreListBefore F (evX F (Sum.inr q))).filter
      (fun p => decide (evZ F (Sum.inr q) < ht F p))).flatMap (beforeBits F),
    ((fibreListAfter F (evX F (Sum.inr q))).filter
      (fun p => !decide (evZ F (Sum.inr q) ≤ ht F p))).flatMap (afterBits F), ?_, rfl⟩
  unfold hybridCut hybridCutP
  rw [s3s5_filter_split (ht F) (evZ F (Sum.inr q)) _ hanti, List.flatMap_append, s3s5_filter_height_eq,
    List.flatMap_cons, List.flatMap_cons, List.flatMap_nil,
    s3s5_beforeBits_of_not_isCusp F (F.not_isCusp_of_isDouble hd),
    s3s5_beforeBits_of_not_isCusp F (F.not_isCusp_of_isDouble hd.symm)]
  simp only [List.append_assoc, List.cons_append, List.nil_append, List.append_nil]

/-- S3S5: two regular parameters have the same direction bit iff their x-velocities have the same sign. -/
theorem s3s5_dirBit_eq_iff {o u : Param F.c} (ho : (F.vel o).1 ≠ 0) (hu : (F.vel u).1 ≠ 0) :
    dirBit F o = dirBit F u ↔ 0 < (F.vel o).1 * (F.vel u).1 := by
  show decide (0 < (F.vel o).1) = decide (0 < (F.vel u).1) ↔ 0 < (F.vel o).1 * (F.vel u).1
  rw [mul_pos_iff]
  rcases lt_or_gt_of_ne ho with h1 | h1 <;> rcases lt_or_gt_of_ne hu with h2 | h2 <;>
    simp [h1, h2, not_lt.mpr h1.le, not_lt.mpr h2.le]

/-- S3S5: the column determines the event. -/
theorem s3s5_evIdx_injective {e e' : Event F} (h : evIdx F e = evIdx F e') : e = e' := by
  have h1 := eventAt_evIdx F e
  rw [h, eventAt_evIdx] at h1
  exact h1.symm

/-- S3S5: a column whose letter is `σ` is the column of a crossing event. -/
theorem s3s5_eventAt_eq_inr {k m : ℕ} (hk : k < (events F).length) (hℓ : letterAt (word F) k = .σ m) :
    ∃ q : Cross F, eventAt F k = Sum.inr q := by
  rw [letterAt_word F hk] at hℓ
  cases he : eventAt F k with
  | inl c =>
    exfalso
    rw [he] at hℓ
    simp only [letterOf] at hℓ
    split_ifs at hℓ
  | inr q => exact ⟨q, rfl⟩

end S3S5Helpers

/-! #### S3 leaf: the crossing local model -/

/-- LEAF (S3): near a double point the over branch (smaller slope, `IsOverUnder`) is ABOVE the under branch to the
left of the crossing and BELOW it to the right (`z_over − z_under ≈ (s_over − s_under)(x − x₀)`; both branches
regular, `vel_ne_zero_of_isDouble`; derivatives of the two graphs from `hasDerivAt_x` and the chain rule, or the
mean value theorem). -/
theorem cross_height_order {p q : Param F.c} (h : F.IsOverUnder p q) :
    ∃ δ > 0, ∀ t₁ t₂, |t₁ - p.2| < δ → |t₂ - q.2| < δ → xOf F p.1 t₁ = xOf F q.1 t₂ →
      (xOf F p.1 t₁ < (F.eval p).1 → zOf F q.1 t₂ < zOf F p.1 t₁) ∧
      ((F.eval p).1 < xOf F p.1 t₁ → zOf F p.1 t₁ < zOf F q.1 t₂) := by
  obtain ⟨hd, hs⟩ := h
  have hap : xvel F p.1 p.2 ≠ 0 := F.vel_fst_ne_zero_of_isDouble hd
  have haq : xvel F q.1 q.2 ≠ 0 := F.vel_fst_ne_zero_of_isDouble hd.symm
  have hε : 0 < (F.slope q - F.slope p) / 4 := by linarith
  obtain ⟨δp, hδp, Hp⟩ := s3s5_graph_bound F p hap hε
  obtain ⟨δq, hδq, Hq⟩ := s3s5_graph_bound F q haq hε
  refine ⟨min δp δq, lt_min hδp hδq, fun t₁ t₂ h1 h2 hx => ?_⟩
  have Ep := Hp t₁ (lt_of_lt_of_le h1 (min_le_left _ _))
  have Eq := Hq t₂ (lt_of_lt_of_le h2 (min_le_right _ _))
  have hx0 : xOf F q.1 q.2 = xOf F p.1 p.2 := congrArg Prod.fst hd.2.symm
  have hz0 : zOf F q.1 q.2 = zOf F p.1 p.2 := congrArg Prod.snd hd.2.symm
  rw [← hx, hx0, hz0] at Eq
  have hx0' : (F.eval p).1 = xOf F p.1 p.2 := rfl
  rw [hx0']
  obtain ⟨Ep1, Ep2⟩ := abs_le.mp Ep
  obtain ⟨Eq1, Eq2⟩ := abs_le.mp Eq
  constructor
  · intro hlt
    have habs : |xOf F p.1 t₁ - xOf F p.1 p.2| = xOf F p.1 p.2 - xOf F p.1 t₁ := by
      rw [abs_sub_comm, abs_of_pos (sub_pos.mpr hlt)]
    rw [habs] at Ep1 Ep2 Eq1 Eq2
    have hpos : 0 < (F.slope q - F.slope p) * (xOf F p.1 p.2 - xOf F p.1 t₁) :=
      mul_pos (by linarith) (sub_pos.mpr hlt)
    nlinarith
  · intro hgt
    have habs : |xOf F p.1 t₁ - xOf F p.1 p.2| = xOf F p.1 t₁ - xOf F p.1 p.2 :=
      abs_of_pos (sub_pos.mpr hgt)
    rw [habs] at Ep1 Ep2 Eq1 Eq2
    have hpos : 0 < (F.slope q - F.slope p) * (xOf F p.1 t₁ - xOf F p.1 p.2) :=
      mul_pos (by linarith) (sub_pos.mpr hgt)
    nlinarith

/-! MERGER (W3S_Merged, 2026-09-14): S1b helpers and the 8 S1b leaves (skeleton L14910-14950) follow the S2/S3 leaves they cite. -/

/-! ### S1b helpers -/
section S1bHelpers

/-! generic: uniformising radii over a finite list, local constancy, `Forall₂` over `flatMap` -/

theorem s1b_uniform {α : Type*} (L : List α) (R : ℝ → α → Prop)
    (hanti : ∀ ⦃δ δ' : ℝ⦄, 0 < δ → δ ≤ δ' → ∀ a, R δ' a → R δ a)
    (h : ∀ a ∈ L, ∃ δ > 0, R δ a) : ∃ δ > 0, ∀ a ∈ L, R δ a := by
  induction L with
  | nil => exact ⟨1, one_pos, fun a ha => absurd ha (by simp)⟩
  | cons b L ih =>
    obtain ⟨δ₁, hδ₁, h₁⟩ := h b (List.mem_cons.mpr (Or.inl rfl))
    obtain ⟨δ₂, hδ₂, h₂⟩ := ih (fun a ha => h a (List.mem_cons_of_mem _ ha))
    refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun a ha => ?_⟩
    rcases List.mem_cons.mp ha with rfl | ha
    · exact hanti (lt_min hδ₁ hδ₂) (min_le_left _ _) _ h₁
    · exact hanti (lt_min hδ₁ hδ₂) (min_le_right _ _) _ (h₂ a ha)

theorem s1b_uniform_pairwise {α : Type*} (L : List α) (R : ℝ → α → α → Prop)
    (hanti : ∀ ⦃δ δ' : ℝ⦄, 0 < δ → δ ≤ δ' → ∀ a b, R δ' a b → R δ a b)
    (h : L.Pairwise (fun a b => ∃ δ > 0, R δ a b)) : ∃ δ > 0, L.Pairwise (R δ) := by
  induction L with
  | nil => exact ⟨1, one_pos, List.Pairwise.nil⟩
  | cons b L ih =>
    rw [List.pairwise_cons] at h
    obtain ⟨δ₁, hδ₁, h₁⟩ := s1b_uniform L (fun δ c => R δ b c)
      (fun δ δ' hδ hle c hc => hanti hδ hle b c hc) h.1
    obtain ⟨δ₂, hδ₂, h₂⟩ := ih h.2
    refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, List.pairwise_cons.mpr ⟨fun c hc => ?_, ?_⟩⟩
    · exact hanti (lt_min hδ₁ hδ₂) (min_le_left _ _) _ _ (h₁ c hc)
    · exact h₂.imp (fun hab => hanti (lt_min hδ₁ hδ₂) (min_le_right _ _) _ _ hab)

/-- a function locally constant on a preconnected subset of `ℝ` is constant on it -/
theorem s1b_const_of_locally_const_on {α : Type*} {s : Set ℝ} (hs : IsPreconnected s) {f : ℝ → α}
    (hloc : ∀ x ∈ s, ∃ ε > 0, ∀ y ∈ s, |y - x| < ε → f y = f x) {x y : ℝ} (hx : x ∈ s) (hy : y ∈ s) :
    f x = f y := by
  let _ : TopologicalSpace α := ⊥
  have : DiscreteTopology α := ⟨rfl⟩
  refine hs.constant (fun z hz => ?_) hx hy
  rw [ContinuousWithinAt, nhds_discrete, Filter.tendsto_pure]
  obtain ⟨ε, hε, h⟩ := hloc z hz
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff]
  exact ⟨ε, hε, fun w hw hws => h w hws (by rwa [Real.dist_eq] at hw)⟩

theorem s1b_forall₂_flatMap {α β γ : Type*} (R : β → γ → Prop) (P : List α) (f : α → List β)
    (g : α → List γ) (h : ∀ p ∈ P, List.Forall₂ R (f p) (g p)) :
    List.Forall₂ R (P.flatMap f) (P.flatMap g) := by
  induction P with
  | nil => simp
  | cons p P ih =>
    rw [List.flatMap_cons, List.flatMap_cons]
    exact List.rel_append (h p (List.mem_cons.mpr (Or.inl rfl)))
      (ih fun q hq => h q (List.mem_cons_of_mem _ hq))

theorem s1b_decide_pos_eq {u v : ℝ} (h : 0 < u * v) : decide (0 < u) = decide (0 < v) := by
  rcases pos_and_pos_or_neg_and_neg_of_mul_pos h with ⟨hu, hv⟩ | ⟨hu, hv⟩
  · simp [hu, hv]
  · simp [not_lt.mpr hu.le, not_lt.mpr hv.le]

theorem s1b_entriesOf_eq_map (bits : Param F.c → Cuts) (P : List (Param F.c))
    (h : ∀ p ∈ P, (bits p).length = 1) : entriesOf F bits P = P.map (fun p => (p, 0)) := by
  induction P with
  | nil => rfl
  | cons p P ih =>
    unfold entriesOf at *
    rw [List.flatMap_cons, List.map_cons, h p (List.mem_cons.mpr (Or.inl rfl)),
      ih (fun q hq => h q (List.mem_cons_of_mem _ hq))]
    rfl

/-! periodicity of the coordinates and invariance under `SameParam` -/

theorem s1b_xOf_add_int (i : Fin F.c) (t : ℝ) (n : ℤ) : xOf F i (t + n) = xOf F i t := by
  unfold xOf; rw [(F.comp i).eq_add_int]

theorem s1b_zOf_add_int (i : Fin F.c) (t : ℝ) (n : ℤ) : zOf F i (t + n) = zOf F i t := by
  unfold zOf; rw [(F.comp i).eq_add_int]

theorem s1b_xOf_of_sameParam {p q : Param F.c} (h : SameParam p q) : xOf F q.1 q.2 = xOf F p.1 p.2 := by
  show (F.eval q).1 = (F.eval p).1
  rw [SmoothFront.eval_of_sameParam h]

theorem s1b_ht_of_sameParam {p q : Param F.c} (h : SameParam p q) : ht F q = ht F p := by
  unfold ht; rw [SmoothFront.eval_of_sameParam h]

theorem s1b_dirBit_of_sameParam {p q : Param F.c} (h : SameParam p q) : dirBit F q = dirBit F p := by
  unfold dirBit; rw [xvel_def, xvel_def, SmoothFront.vel_of_sameParam h]

theorem s1b_sameParam_fract (i : Fin F.c) (s : ℝ) : SameParam (i, Int.fract s) (i, s) :=
  ⟨rfl, ⌊s⌋, (Int.fract_add_floor s).symm⟩

theorem s1b_cont_of_sameParam {q q' : Param F.c} {a : Param F.c × ℕ} (h : Cont F q a)
    (hqq : SameParam q q') : Cont F q' a := by
  obtain ⟨h1, s, hs, hne, hnc, hcusp⟩ := h
  exact ⟨hqq.1.symm.trans h1, s, hqq.symm.trans hs, hne, hnc, hcusp⟩

theorem s1b_ht_eq_zOf (i : Fin F.c) (t : ℝ) : ht F (i, t) = zOf F i t := rfl

theorem s1b_xOf_eq_of_mem_totalFibre {x : ℝ} {p : Param F.c} (hp : p ∈ totalFibre F x) :
    xOf F p.1 p.2 = x := hp.2

theorem s1b_mem_totalFibre_fract {i : Fin F.c} {s x : ℝ} (hx : xOf F i s = x) :
    (i, Int.fract s) ∈ totalFibre F x :=
  ⟨⟨Int.fract_nonneg _, Int.fract_lt_one _⟩, by
    exact (s1b_xOf_of_sameParam F (s1b_sameParam_fract F i s)).symm.trans hx⟩

/-! the singular values are avoided just left / right of any `a`; the x-value of an event is singular -/

theorem s1b_exists_eta_left (a : ℝ) : ∃ η > 0, ∀ x ∈ Set.Ioo (a - η) a, x ∉ singX F := by
  by_cases hne : ((singX F).filter (fun s => s < a)).Nonempty
  · obtain ⟨m, hm, hmax⟩ := Finset.exists_max_image _ id hne
    rw [Finset.mem_filter] at hm
    refine ⟨a - m, by linarith [hm.2], fun x hx hxs => ?_⟩
    have := hmax x (Finset.mem_filter.mpr ⟨hxs, hx.2⟩)
    simp only [id] at this
    linarith [hx.1]
  · exact ⟨1, one_pos, fun x hx hxs => hne ⟨x, Finset.mem_filter.mpr ⟨hxs, hx.2⟩⟩⟩

theorem s1b_exists_eta_right (a : ℝ) : ∃ η > 0, ∀ x ∈ Set.Ioo a (a + η), x ∉ singX F := by
  by_cases hne : ((singX F).filter (fun s => a < s)).Nonempty
  · obtain ⟨m, hm, hmin⟩ := Finset.exists_min_image _ id hne
    rw [Finset.mem_filter] at hm
    refine ⟨m - a, by linarith [hm.2], fun x hx hxs => ?_⟩
    have := hmin x (Finset.mem_filter.mpr ⟨hxs, hx.1⟩)
    simp only [id] at this
    linarith [hx.2]
  · exact ⟨1, one_pos, fun x hx hxs => hne ⟨x, Finset.mem_filter.mpr ⟨hxs, hx.1⟩⟩⟩

theorem s1b_evX_mem_singX (e : Event F) : evX F e ∈ singX F := by
  rcases e with c | q
  · exact mem_singX_of_isCusp F c.isCusp
  · exact mem_singX_of_isDouble F (F.isOverUnder_of_mem_crossingPairs q.2).1

/-! strict height order: consequences -/

theorem s1b_nodup_of_pairwise_lt {L : List (Param F.c)} (h : L.Pairwise (fun q q' => ht F q' < ht F q)) :
    L.Nodup :=
  h.imp (fun {a b} hab heq => by subst heq; exact lt_irrefl _ hab)

theorem s1b_beforeLE_of_lt {p q : Param F.c} (h : ht F q < ht F p) : beforeLE F p q = true := by
  unfold beforeLE; rw [decide_eq_true_iff]
  exact le_of_lt (Prod.Lex.toLex_lt_toLex.mpr (Or.inl (by simp only; linarith)))

theorem s1b_afterLE_of_lt {p q : Param F.c} (h : ht F q < ht F p) : afterLE F p q = true := by
  unfold afterLE; rw [decide_eq_true_iff]
  exact le_of_lt (Prod.Lex.toLex_lt_toLex.mpr (Or.inl (by simp only; linarith)))

/-- over a non-singular `a` the "before" list is strictly descending in height -/
theorem s1b_fibreListBefore_pairwise_lt {a : ℝ} (ha : a ∉ singX F) :
    (fibreListBefore F a).Pairwise (fun q q' => ht F q' < ht F q) := by
  have h := (fibreListBefore_pairwise F a).and (fibreListBefore_nodup F a)
  refine h.imp_of_mem ?_
  rintro p q hp hq ⟨hle, hne⟩
  unfold beforeLE at hle
  rw [decide_eq_true_iff, Prod.Lex.toLex_le_toLex] at hle
  rcases hle with hlt | ⟨heq, -⟩
  · simp only at hlt; linarith
  · exfalso
    apply hne
    apply snd_injOn_totalFibre F ha ((mem_fibreListBefore F a p).mp hp) ((mem_fibreListBefore F a q).mp hq)
    simp only at heq
    show ht F p = ht F q
    linarith

/-- `fibreListBefore x = L` identifies the fibre `Finset` with `L.toFinset` -/
theorem s1b_fibreFinset_eq {x : ℝ} {L : List (Param F.c)} (hL : fibreListBefore F x = L) :
    fibreFinset F x = L.toFinset := by
  ext p
  rw [List.mem_toFinset, ← hL, mem_fibreListBefore, mem_fibreFinset]

/-- the position of the `j`-th element of the strictly descending fibre list is `j + 1` -/
theorem s1b_posAt_eq_index {x : ℝ} {L : List (Param F.c)} (hL : fibreListBefore F x = L)
    (hpair : L.Pairwise (fun q q' => ht F q' < ht F q)) {j : ℕ} (hj : j < L.length) :
    posAt F x L[j] = j + 1 := by
  unfold posAt
  congr 1
  have hnd : L.Nodup := s1b_nodup_of_pairwise_lt F hpair
  rw [s1b_fibreFinset_eq F hL, List.filter_toFinset, List.toFinset_card_of_nodup (hnd.filter _)]
  have hpg := List.pairwise_iff_getElem.mp hpair
  obtain ⟨q, hq⟩ : ∃ q, q = L[j] := ⟨_, rfl⟩
  rw [← hq]
  have hsplit : L.filter (fun p => decide (ht F q < ht F p)) = L.take j := by
    conv_lhs => rw [← List.take_append_drop j L]
    rw [List.filter_append, List.filter_eq_self.mpr, List.filter_eq_nil_iff.mpr, List.append_nil]
    · intro b hb
      obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hb
      rw [List.getElem_drop, decide_eq_true_iff, not_lt, hq]
      rcases Nat.eq_zero_or_pos k with hk0 | hk0
      · subst hk0; simp
      · exact le_of_lt (hpg j (j + k) hj (by rw [List.length_drop] at hk; omega) (by omega))
    · intro b hb
      obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hb
      rw [List.getElem_take, decide_eq_true_iff, hq]
      have hkj : k < j := by rw [List.length_take] at hk; omega
      exact hpg k j (by omega) hj hkj
  rw [hsplit, List.length_take, min_eq_left hj.le]

/-! the local model of one fibre point and its instances -/

/-- The local model of a fibre point `p` over `a` at a nearby `x`: the list `l` of the parameters (within `δ` of
`p.2`, top to bottom) of the strands of `p` over `x`; complete; each strand a `Cont`-continuation of the entry
`(p, j)` carrying the entry's bit. -/
def s1b_Local (p : Param F.c) (bits : Param F.c → Cuts) (δ x : ℝ) (l : List ℝ) : Prop :=
  l.length = (bits p).length ∧
  (∀ s ∈ l, |s - p.2| < δ ∧ xOf F p.1 s = x) ∧
  (∀ t, |t - p.2| < δ → xOf F p.1 t = x → t ∈ l) ∧
  l.Pairwise (fun s s' => zOf F p.1 s' < zOf F p.1 s) ∧
  ∀ j (hj : j < l.length), Cont F (p.1, l[j]) (p, j) ∧ dirBit F (p.1, l[j]) = (bits p).getD j false

/-- a continuation within `δ` (in the parameter) of its entry -/
def s1b_ContNear (δ : ℝ) (q : Param F.c) (e : Param F.c × ℕ) : Prop :=
  Cont F q e ∧ ∃ s, SameParam q (e.1.1, s) ∧ |s - e.1.2| < δ

theorem s1b_bits_regular_before {p : Param F.c} (h : ¬ F.IsCusp p) : beforeBits F p = [dirBit F p] := by
  unfold beforeBits
  rw [ite_eq_right (fun hl => h hl.1), ite_eq_right (fun hr => h hr.1)]

theorem s1b_bits_regular_after {p : Param F.c} (h : ¬ F.IsCusp p) : afterBits F p = [dirBit F p] := by
  unfold afterBits
  rw [ite_eq_right (fun hr => h hr.1), ite_eq_right (fun hl => h hl.1)]

theorem s1b_mem_Ioo_of_abs {t₀ δ u : ℝ} (h : |u - t₀| < δ) : u ∈ Set.Ioo (t₀ - δ) (t₀ + δ) :=
  ⟨by linarith [(abs_sub_lt_iff.mp h).2], by linarith [(abs_sub_lt_iff.mp h).1]⟩

theorem s1b_abs_of_mem_Ioo {t₀ δ u : ℝ} (h : u ∈ Set.Ioo (t₀ - δ) (t₀ + δ)) : |u - t₀| < δ :=
  abs_sub_lt_iff.mpr ⟨by linarith [h.2], by linarith [h.1]⟩

/-- a strictly-between parameter of two parameters within `δ` of `t₀` is within `δ` of `t₀` and is not `t₀`
when one of them is `t₀` -/
theorem s1b_between_abs {t₀ δ s u : ℝ} (hs : |s - t₀| < δ) (hu1 : min s t₀ < u) (hu2 : u < max s t₀) :
    |u - t₀| < δ ∧ u ≠ t₀ := by
  have hs' := abs_sub_lt_iff.mp hs
  rcases le_total s t₀ with h | h
  · rw [min_eq_left h] at hu1; rw [max_eq_right h] at hu2
    exact ⟨abs_sub_lt_iff.mpr ⟨by linarith, by linarith⟩, ne_of_lt hu2⟩
  · rw [min_eq_right h] at hu1; rw [max_eq_left h] at hu2
    exact ⟨abs_sub_lt_iff.mpr ⟨by linarith, by linarith⟩, ne_of_gt hu1⟩

/-- the regular case: one strand, from `regular_local_graph` -/
theorem s1b_local_regular (a : ℝ) (bits : Param F.c → Cuts)
    {p : Param F.c} (hp : p ∈ totalFibre F a) (hreg : ¬ F.IsCusp p) (hbits : bits p = [dirBit F p]) :
    ∃ δ₀ > 0, ∀ δ, 0 < δ → δ ≤ δ₀ → ∃ η > 0, ∀ x, |x - a| < η → x ≠ a →
      ∃ l, s1b_Local F p bits δ x l := by
  obtain ⟨i, t₀⟩ := p
  have hx₀ : xOf F i t₀ = a := hp.2
  obtain ⟨δ₀, hδ₀, hnc, hinj, hpre⟩ := regular_local_graph F hreg
  refine ⟨δ₀, hδ₀, fun δ hδ hle => ?_⟩
  obtain ⟨η, hη, hex⟩ := hpre δ ⟨hδ, hle⟩
  refine ⟨η, hη, fun x hx hxa => ?_⟩
  rw [hx₀] at hex
  obtain ⟨t, ht, hxt⟩ := hex x hx
  have htδ : |t - t₀| < δ := s1b_abs_of_mem_Ioo ht
  have htne : t ≠ t₀ := fun h => hxa (by rw [← hxt, h, hx₀])
  refine ⟨[t], ?_, ?_, ?_, List.pairwise_singleton _ _, ?_⟩
  · rw [hbits]; rfl
  · intro s hs
    rw [List.mem_singleton] at hs
    subst hs
    exact ⟨htδ, hxt⟩
  · intro u hu hxu
    rw [List.mem_singleton]
    exact hinj u (s1b_mem_Ioo_of_abs (lt_of_lt_of_le hu hle)) t (s1b_mem_Ioo_of_abs (lt_of_lt_of_le htδ hle))
      (hxu.trans hxt.symm)
  · intro j hj
    have hj0 : j = 0 := by simpa using hj
    subst hj0
    simp only [List.getElem_singleton]
    refine ⟨⟨rfl, t, SameParam.refl _, htne, fun u hu1 hu2 => ?_, fun hc => absurd hc hreg⟩, ?_⟩
    · exact hnc u (s1b_mem_Ioo_of_abs (lt_of_lt_of_le (s1b_between_abs htδ hu1 hu2).1 hle))
    · rw [hbits]
      show decide (0 < xvel F i t) = decide (0 < xvel F i t₀)
      apply s1b_decide_pos_eq
      exact xvel_mul_pos_of_cuspFree F isPreconnected_Ioo hnc (s1b_mem_Ioo_of_abs (lt_of_lt_of_le htδ hle))
        (s1b_mem_Ioo_of_abs (by simpa using hδ₀))

/-- a cusp with no strand on the given side -/
theorem s1b_local_empty {i : Fin F.c} {t₀ δ x : ℝ} (bits : Param F.c → Cuts) (hbits : bits (i, t₀) = [])
    (hno : ∀ t, |t - t₀| < δ → xOf F i t ≠ x) : s1b_Local F (i, t₀) bits δ x [] :=
  ⟨by rw [hbits]; rfl, fun s hs => absurd hs (by simp), fun t ht hxt => absurd hxt (hno t ht),
    List.Pairwise.nil, fun j hj => absurd hj (by simp)⟩

/-- a cusp with its two arms: the earlier arm `t₁ < t₀` carries the bit `b₁`, the later arm `t₂` the bit `!b₁`; the
upper arm (`j = 0`) is the earlier one iff `cuspDisc < 0` (`cusp_arm_sign`). -/
theorem s1b_local_two_arms {i : Fin F.c} {t₀ δ x : ℝ}
    (hnc : ∀ t, |t - t₀| < δ → t ≠ t₀ → ¬ F.IsCusp (i, t))
    (bits : Param F.c → Cuts) (b₁ : Bool)
    (hbits : bits (i, t₀) = if F.cuspDisc (i, t₀) < 0 then [b₁, !b₁] else [!b₁, b₁])
    {t₁ t₂ : ℝ} (h1 : t₀ - δ < t₁) (h1' : t₁ < t₀) (h2 : t₀ < t₂) (h2' : t₂ < t₀ + δ)
    (hx1 : xOf F i t₁ = x) (hx2 : xOf F i t₂ = x)
    (hsign : zOf F i t₁ < zOf F i t₂ ↔ 0 < F.cuspDisc (i, t₀))
    (hdisc : F.cuspDisc (i, t₀) ≠ 0)
    (hne : zOf F i t₁ ≠ zOf F i t₂)
    (hv1 : dirBit F (i, t₁) = b₁) (hv2 : dirBit F (i, t₂) = !b₁)
    (hcompl : ∀ t, |t - t₀| < δ → xOf F i t = x → t = t₁ ∨ t = t₂) :
    ∃ l, s1b_Local F (i, t₀) bits δ x l := by
  have hcont : ∀ s, |s - t₀| < δ → s ≠ t₀ → ∀ j, (s < t₀ ↔ (j = 0 ↔ F.cuspDisc (i, t₀) < 0)) →
      Cont F (i, s) ((i, t₀), j) := by
    intro s hs hsne j hj
    refine ⟨rfl, s, SameParam.refl _, hsne, fun u hu1 hu2 => ?_, fun _ => hj⟩
    obtain ⟨hu, hune⟩ := s1b_between_abs hs hu1 hu2
    exact hnc u hu hune
  have hin1 : |t₁ - t₀| < δ := abs_sub_lt_iff.mpr ⟨by linarith, by linarith⟩
  have hin2 : |t₂ - t₀| < δ := abs_sub_lt_iff.mpr ⟨by linarith, by linarith⟩
  have hmem : ∀ s ∈ [t₁, t₂], |s - t₀| < δ ∧ xOf F i s = x := by
    intro s hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact ⟨hin1, hx1⟩
    · exact ⟨hin2, hx2⟩
  have hmem' : ∀ s ∈ [t₂, t₁], |s - t₀| < δ ∧ xOf F i s = x := by
    intro s hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact ⟨hin2, hx2⟩
    · exact ⟨hin1, hx1⟩
  by_cases hd : F.cuspDisc (i, t₀) < 0
  · -- the earlier arm is the upper one
    have hz : zOf F i t₂ < zOf F i t₁ := by
      rcases lt_or_gt_of_ne hne with h | h
      · exact absurd (hsign.mp h) (not_lt.mpr hd.le)
      · exact h
    refine ⟨[t₁, t₂], ?_, hmem, ?_, List.pairwise_pair.mpr hz, ?_⟩
    · rw [hbits, ite_eq_left hd]; rfl
    · intro t ht hxt
      rcases hcompl t ht hxt with rfl | rfl <;> simp
    · intro j hj
      have hj2 : j < 2 := by simpa using hj
      rw [hbits, ite_eq_left hd]
      interval_cases j
      · simp only [List.getElem_cons_zero, List.getD_cons_zero]
        exact ⟨hcont t₁ hin1 h1'.ne 0 ⟨fun _ => ⟨fun _ => hd, fun _ => rfl⟩, fun _ => h1'⟩, hv1⟩
      · simp only [List.getElem_cons_succ, List.getElem_cons_zero, List.getD_cons_succ, List.getD_cons_zero]
        exact ⟨hcont t₂ hin2 h2.ne' 1
          ⟨fun h => absurd h (not_lt.mpr h2.le), fun h => absurd (h.mpr hd) one_ne_zero⟩, hv2⟩
  · -- the later arm is the upper one
    have hd' : 0 < F.cuspDisc (i, t₀) := lt_of_le_of_ne (not_lt.mp hd) (Ne.symm hdisc)
    have hz : zOf F i t₁ < zOf F i t₂ := hsign.mpr hd'
    refine ⟨[t₂, t₁], ?_, hmem', ?_, List.pairwise_pair.mpr hz, ?_⟩
    · rw [hbits, ite_eq_right hd]; rfl
    · intro t ht hxt
      rcases hcompl t ht hxt with rfl | rfl <;> simp
    · intro j hj
      have hj2 : j < 2 := by simpa using hj
      rw [hbits, ite_eq_right hd]
      interval_cases j
      · simp only [List.getElem_cons_zero, List.getD_cons_zero]
        exact ⟨hcont t₂ hin2 h2.ne' 0
          ⟨fun h => absurd h (not_lt.mpr h2.le), fun h => absurd (h.mp rfl) hd⟩, hv2⟩
      · simp only [List.getElem_cons_succ, List.getElem_cons_zero, List.getD_cons_succ, List.getD_cons_zero]
        exact ⟨hcont t₁ hin1 h1'.ne 1
          ⟨fun _ => ⟨fun h => absurd h one_ne_zero, fun h => absurd h hd⟩, fun _ => h1'⟩, hv1⟩

/-- two arms of one cusp at equal height over a non-singular `x` would be a double point -/
theorem s1b_arms_ne {i : Fin F.c} {t₁ t₂ x : ℝ} (hlt : t₁ < t₂) (hsep : t₂ - t₁ < 1)
    (hx1 : xOf F i t₁ = x) (hx2 : xOf F i t₂ = x) (hxs : x ∉ singX F) : zOf F i t₁ ≠ zOf F i t₂ := by
  intro heq
  apply hxs
  have hd : F.IsDouble (i, t₁) (i, t₂) := by
    refine ⟨fun hs => ?_, Prod.ext (hx1.trans hx2.symm) heq⟩
    obtain ⟨-, n, hn⟩ := hs
    simp only at hn
    have h1 : (0 : ℝ) < n := by linarith
    have h2 : (n : ℝ) < 1 := by linarith
    have h1' : (0 : ℤ) < n := by exact_mod_cast h1
    have h2' : n < (1 : ℤ) := by exact_mod_cast h2
    omega
  rw [← hx1]
  exact mem_singX_of_isDouble F hd

/-- a right cusp just LEFT of its x-value: two arms, the arriving (earlier) one rightward -/
theorem s1b_local_rightCusp_before {a : ℝ} {p : Param F.c} (hp : p ∈ totalFibre F a) (hr : F.IsRightCusp p) :
    ∃ δ₀ > 0, ∀ δ, 0 < δ → δ ≤ δ₀ → ∃ η > 0, ∀ x, |x - a| < η → x < a → x ∉ singX F →
      ∃ l, s1b_Local F p (beforeBits F) δ x l := by
  obtain ⟨i, t₀⟩ := p
  have hx₀ : xOf F i t₀ = a := hp.2
  have hc : F.IsCusp (i, t₀) := hr.1
  obtain ⟨δ₁, hδ₁, hnc, hmono, hanti⟩ := rightCusp_x_local F hr
  obtain ⟨δ₂, hδ₂, hsign⟩ := cusp_arm_sign F hc
  obtain ⟨δ₃, hδ₃, hvel⟩ := exists_xvel_sign_of_isRightCusp F hr
  refine ⟨min (min δ₁ δ₂) (min δ₃ (1/4)), by positivity, fun δ hδ hle => ?_⟩
  have hle1 : δ ≤ δ₁ := le_trans hle (le_trans (min_le_left _ _) (min_le_left _ _))
  have hle2 : δ ≤ δ₂ := le_trans hle (le_trans (min_le_left _ _) (min_le_right _ _))
  have hle3 : δ ≤ δ₃ := le_trans hle (le_trans (min_le_right _ _) (min_le_left _ _))
  have hle4 : δ ≤ 1/4 := le_trans hle (le_trans (min_le_right _ _) (min_le_right _ _))
  obtain ⟨η, hη, harms⟩ := rightCusp_arms F hr hδ
  refine ⟨η, hη, fun x hx hxa hxs => ?_⟩
  have hxI : x ∈ Set.Ioo (xOf F i t₀ - η) (xOf F i t₀) := by
    rw [hx₀]; exact ⟨by linarith [(abs_sub_lt_iff.mp hx).2], hxa⟩
  obtain ⟨⟨t₁, ht₁, hx1⟩, ⟨t₂, ht₂, hx2⟩⟩ := harms x hxI
  have hbits : beforeBits F (i, t₀) =
      if F.cuspDisc (i, t₀) < 0 then [true, !true] else [!true, true] := by
    unfold beforeBits
    rw [ite_eq_right (fun hl => left_right_absurd F hl hr), ite_eq_left hr]
    rfl
  have hnc' : ∀ t, |t - t₀| < δ → t ≠ t₀ → ¬ F.IsCusp (i, t) := fun t ht hne =>
    hnc t (s1b_mem_Ioo_of_abs (lt_of_lt_of_le ht hle1)) hne
  have hsign' : zOf F i t₁ < zOf F i t₂ ↔ 0 < F.cuspDisc (i, t₀) :=
    hsign t₁ t₂ (by linarith [ht₁.1]) ht₁.2 ht₂.1 (by linarith [ht₂.2]) (hx1.trans hx2.symm)
  have hne : zOf F i t₁ ≠ zOf F i t₂ :=
    s1b_arms_ne F (ht₁.2.trans ht₂.1) (by linarith [ht₁.1, ht₂.2]) hx1 hx2 hxs
  have hv1 : dirBit F (i, t₁) = true := by
    unfold dirBit; rw [decide_eq_true_iff]
    exact (hvel t₁ (by rw [Real.dist_eq]; exact lt_of_lt_of_le (s1b_abs_of_mem_Ioo
      (⟨ht₁.1, by linarith [ht₁.2]⟩ : t₁ ∈ Set.Ioo (t₀ - δ) (t₀ + δ))) hle3)).1 ht₁.2
  have hv2 : dirBit F (i, t₂) = !true := by
    unfold dirBit; rw [Bool.not_true, decide_eq_false_iff_not, not_lt]
    exact ((hvel t₂ (by rw [Real.dist_eq]; exact lt_of_lt_of_le (s1b_abs_of_mem_Ioo
      (⟨by linarith [ht₂.1], ht₂.2⟩ : t₂ ∈ Set.Ioo (t₀ - δ) (t₀ + δ))) hle3)).2 ht₂.1).le
  have hcompl : ∀ t, |t - t₀| < δ → xOf F i t = x → t = t₁ ∨ t = t₂ := by
    intro t ht hxt
    have ht' := abs_sub_lt_iff.mp (lt_of_lt_of_le ht hle1)
    rcases lt_trichotomy t t₀ with hlt | heq | hgt
    · left
      exact hmono.injOn ⟨by linarith, hlt.le⟩ ⟨by linarith [ht₁.1], ht₁.2.le⟩ (hxt.trans hx1.symm)
    · exfalso; rw [heq, hx₀] at hxt; linarith
    · right
      exact hanti.injOn ⟨hgt.le, by linarith⟩ ⟨ht₂.1.le, by linarith [ht₂.2]⟩ (hxt.trans hx2.symm)
  exact s1b_local_two_arms F hnc' (beforeBits F) true hbits ht₁.1 ht₁.2 ht₂.1 ht₂.2 hx1 hx2 hsign'
    (F.cuspDisc_ne_zero_of_isCusp hc) hne hv1 hv2 hcompl

/-- a left cusp just RIGHT of its x-value: two arms, the leaving (later) one rightward -/
theorem s1b_local_leftCusp_after {a : ℝ} {p : Param F.c} (hp : p ∈ totalFibre F a) (hl : F.IsLeftCusp p) :
    ∃ δ₀ > 0, ∀ δ, 0 < δ → δ ≤ δ₀ → ∃ η > 0, ∀ x, |x - a| < η → a < x → x ∉ singX F →
      ∃ l, s1b_Local F p (afterBits F) δ x l := by
  obtain ⟨i, t₀⟩ := p
  have hx₀ : xOf F i t₀ = a := hp.2
  have hc : F.IsCusp (i, t₀) := hl.1
  obtain ⟨δ₁, hδ₁, hnc, hanti, hmono⟩ := leftCusp_x_local F hl
  obtain ⟨δ₂, hδ₂, hsign⟩ := cusp_arm_sign F hc
  obtain ⟨δ₃, hδ₃, hvel⟩ := exists_xvel_sign_of_isLeftCusp F hl
  refine ⟨min (min δ₁ δ₂) (min δ₃ (1/4)), by positivity, fun δ hδ hle => ?_⟩
  have hle1 : δ ≤ δ₁ := le_trans hle (le_trans (min_le_left _ _) (min_le_left _ _))
  have hle2 : δ ≤ δ₂ := le_trans hle (le_trans (min_le_left _ _) (min_le_right _ _))
  have hle3 : δ ≤ δ₃ := le_trans hle (le_trans (min_le_right _ _) (min_le_left _ _))
  have hle4 : δ ≤ 1/4 := le_trans hle (le_trans (min_le_right _ _) (min_le_right _ _))
  obtain ⟨η, hη, harms⟩ := leftCusp_arms F hl hδ
  refine ⟨η, hη, fun x hx hxa hxs => ?_⟩
  have hxI : x ∈ Set.Ioo (xOf F i t₀) (xOf F i t₀ + η) := by
    rw [hx₀]; exact ⟨hxa, by linarith [(abs_sub_lt_iff.mp hx).1]⟩
  obtain ⟨⟨t₁, ht₁, hx1⟩, ⟨t₂, ht₂, hx2⟩⟩ := harms x hxI
  have hdisc := F.cuspDisc_ne_zero_of_isCusp hc
  have hbits : afterBits F (i, t₀) =
      if F.cuspDisc (i, t₀) < 0 then [false, !false] else [!false, false] := by
    unfold afterBits
    rw [ite_eq_right (fun hr => left_right_absurd F hl hr), ite_eq_left hl]
    rcases lt_or_gt_of_ne hdisc with h | h
    · rw [ite_eq_right (not_lt.mpr h.le), ite_eq_left h]; rfl
    · rw [ite_eq_left h, ite_eq_right (not_lt.mpr h.le)]; rfl
  have hnc' : ∀ t, |t - t₀| < δ → t ≠ t₀ → ¬ F.IsCusp (i, t) := fun t ht hne =>
    hnc t (s1b_mem_Ioo_of_abs (lt_of_lt_of_le ht hle1)) hne
  have hsign' : zOf F i t₁ < zOf F i t₂ ↔ 0 < F.cuspDisc (i, t₀) :=
    hsign t₁ t₂ (by linarith [ht₁.1]) ht₁.2 ht₂.1 (by linarith [ht₂.2]) (hx1.trans hx2.symm)
  have hne : zOf F i t₁ ≠ zOf F i t₂ :=
    s1b_arms_ne F (ht₁.2.trans ht₂.1) (by linarith [ht₁.1, ht₂.2]) hx1 hx2 hxs
  have hv1 : dirBit F (i, t₁) = false := by
    unfold dirBit; rw [decide_eq_false_iff_not, not_lt]
    exact ((hvel t₁ (by rw [Real.dist_eq]; exact lt_of_lt_of_le (s1b_abs_of_mem_Ioo
      (⟨ht₁.1, by linarith [ht₁.2]⟩ : t₁ ∈ Set.Ioo (t₀ - δ) (t₀ + δ))) hle3)).1 ht₁.2).le
  have hv2 : dirBit F (i, t₂) = !false := by
    unfold dirBit; rw [Bool.not_false, decide_eq_true_iff]
    exact (hvel t₂ (by rw [Real.dist_eq]; exact lt_of_lt_of_le (s1b_abs_of_mem_Ioo
      (⟨by linarith [ht₂.1], ht₂.2⟩ : t₂ ∈ Set.Ioo (t₀ - δ) (t₀ + δ))) hle3)).2 ht₂.1
  have hcompl : ∀ t, |t - t₀| < δ → xOf F i t = x → t = t₁ ∨ t = t₂ := by
    intro t ht hxt
    have ht' := abs_sub_lt_iff.mp (lt_of_lt_of_le ht hle1)
    rcases lt_trichotomy t t₀ with hlt | heq | hgt
    · left
      exact hanti.injOn ⟨by linarith, hlt.le⟩ ⟨by linarith [ht₁.1], ht₁.2.le⟩ (hxt.trans hx1.symm)
    · exfalso; rw [heq, hx₀] at hxt; linarith
    · right
      exact hmono.injOn ⟨hgt.le, by linarith⟩ ⟨ht₂.1.le, by linarith [ht₂.2]⟩ (hxt.trans hx2.symm)
  exact s1b_local_two_arms F hnc' (afterBits F) false hbits ht₁.1 ht₁.2 ht₂.1 ht₂.2 hx1 hx2 hsign'
    hdisc hne hv1 hv2 hcompl

/-- a left cusp just LEFT of its x-value: no strand (`x` has a strict local minimum there) -/
theorem s1b_local_leftCusp_before {a : ℝ} {p : Param F.c} (hp : p ∈ totalFibre F a) (hl : F.IsLeftCusp p) :
    ∃ δ₀ > 0, ∀ δ, 0 < δ → δ ≤ δ₀ → ∃ η > 0, ∀ x, |x - a| < η → x < a → x ∉ singX F →
      ∃ l, s1b_Local F p (beforeBits F) δ x l := by
  obtain ⟨i, t₀⟩ := p
  have hx₀ : xOf F i t₀ = a := hp.2
  obtain ⟨δ₁, hδ₁, -, hanti, hmono⟩ := leftCusp_x_local F hl
  refine ⟨δ₁, hδ₁, fun δ hδ hle => ⟨1, one_pos, fun x _ hxa _ => ⟨[], s1b_local_empty F _ ?_ ?_⟩⟩⟩
  · unfold beforeBits; rw [ite_eq_left hl]
  · intro t ht hxt
    have ht' := abs_sub_lt_iff.mp (lt_of_lt_of_le ht hle)
    rcases lt_trichotomy t t₀ with hlt | heq | hgt
    · have := hanti ⟨by linarith, hlt.le⟩ ⟨by linarith, le_rfl⟩ hlt
      simp only [hx₀, hxt] at this; linarith
    · rw [heq, hx₀] at hxt; linarith
    · have := hmono ⟨le_rfl, by linarith⟩ ⟨hgt.le, by linarith⟩ hgt
      simp only [hx₀, hxt] at this; linarith

/-- a right cusp just RIGHT of its x-value: no strand (`x` has a strict local maximum there) -/
theorem s1b_local_rightCusp_after {a : ℝ} {p : Param F.c} (hp : p ∈ totalFibre F a) (hr : F.IsRightCusp p) :
    ∃ δ₀ > 0, ∀ δ, 0 < δ → δ ≤ δ₀ → ∃ η > 0, ∀ x, |x - a| < η → a < x → x ∉ singX F →
      ∃ l, s1b_Local F p (afterBits F) δ x l := by
  obtain ⟨i, t₀⟩ := p
  have hx₀ : xOf F i t₀ = a := hp.2
  obtain ⟨δ₁, hδ₁, -, hmono, hanti⟩ := rightCusp_x_local F hr
  refine ⟨δ₁, hδ₁, fun δ hδ hle => ⟨1, one_pos, fun x _ hxa _ => ⟨[], s1b_local_empty F _ ?_ ?_⟩⟩⟩
  · unfold afterBits; rw [ite_eq_left hr]
  · intro t ht hxt
    have ht' := abs_sub_lt_iff.mp (lt_of_lt_of_le ht hle)
    rcases lt_trichotomy t t₀ with hlt | heq | hgt
    · have := hmono ⟨by linarith, hlt.le⟩ ⟨by linarith, le_rfl⟩ hlt
      simp only [hx₀, hxt] at this; linarith
    · rw [heq, hx₀] at hxt; linarith
    · have := hanti ⟨le_rfl, by linarith⟩ ⟨hgt.le, by linarith⟩ hgt
      simp only [hx₀, hxt] at this; linarith

/-- two fibre points of different heights stay ordered nearby (continuity of `z`) -/
theorem s1b_ord_of_lt {p p' : Param F.c} (h : ht F p' < ht F p) :
    ∃ δ > 0, ∀ s s', |s - p.2| < δ → |s' - p'.2| < δ → zOf F p'.1 s' < zOf F p.1 s := by
  have hε : 0 < (ht F p - ht F p') / 2 := by linarith
  obtain ⟨δ₁, hδ₁, h₁⟩ := Metric.continuous_iff.mp ((F.comp p.1).continuous.snd) p.2 _ hε
  obtain ⟨δ₂, hδ₂, h₂⟩ := Metric.continuous_iff.mp ((F.comp p'.1).continuous.snd) p'.2 _ hε
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun s s' hs hs' => ?_⟩
  have e1 := h₁ s (by rw [Real.dist_eq]; exact lt_of_lt_of_le hs (min_le_left _ _))
  have e2 := h₂ s' (by rw [Real.dist_eq]; exact lt_of_lt_of_le hs' (min_le_right _ _))
  simp only [Real.dist_eq] at e1 e2
  have f1 := abs_sub_lt_iff.mp e1
  have f2 := abs_sub_lt_iff.mp e2
  have hp : ht F p = ((F.comp p.1).γ p.2).2 := rfl
  have hp' : ht F p' = ((F.comp p'.1).γ p'.2).2 := rfl
  show ((F.comp p'.1).γ s').2 < ((F.comp p.1).γ s).2
  linarith

/-! the combination over the fibre: the list of continuations -/

theorem s1b_combine (a : ℝ) (I : Set ℝ) (bits : Param F.c → Cuts) (P : List (Param F.c))
    (hP : ∀ p, p ∈ P ↔ p ∈ totalFibre F a)
    (hloc : ∀ p ∈ P, ∃ δ₀ > 0, ∀ δ, 0 < δ → δ ≤ δ₀ → ∃ η > 0, ∀ x, |x - a| < η → x ∈ I → x ∉ singX F →
      ∃ l, s1b_Local F p bits δ x l)
    (hord : P.Pairwise (fun p p' => ∃ δ > 0, ∀ s s', |s - p.2| < δ → |s' - p'.2| < δ →
      xOf F p.1 s = xOf F p'.1 s' → xOf F p.1 s ∈ I → zOf F p'.1 s' < zOf F p.1 s)) :
    ∃ δ₀ > 0, ∀ δ, 0 < δ → δ ≤ δ₀ → ∃ η > 0, ∀ x, |x - a| < η → x ∈ I → x ∉ singX F →
      ∃ L : List (Param F.c), (∀ q, q ∈ L ↔ q ∈ totalFibre F x) ∧
        L.Pairwise (fun q q' => ht F q' < ht F q) ∧
        List.Forall₂ (s1b_ContNear F δ) L (entriesOf F bits P) ∧ L.map (dirBit F) = P.flatMap bits := by
  obtain ⟨δ₁, hδ₁, hloc₁⟩ := s1b_uniform P
    (fun δ₀ p => ∀ δ, 0 < δ → δ ≤ δ₀ → ∃ η > 0, ∀ x, |x - a| < η → x ∈ I → x ∉ singX F →
      ∃ l, s1b_Local F p bits δ x l)
    (fun δ δ' _ hle p h δ'' hδ'' hle'' => h δ'' hδ'' (le_trans hle'' hle)) hloc
  obtain ⟨δ₂, hδ₂, hord₂⟩ := s1b_uniform_pairwise P
    (fun δ p p' => ∀ s s', |s - p.2| < δ → |s' - p'.2| < δ → xOf F p.1 s = xOf F p'.1 s' →
      xOf F p.1 s ∈ I → zOf F p'.1 s' < zOf F p.1 s)
    (fun δ δ' _ hle p p' h s s' hs hs' => h s s' (lt_of_lt_of_le hs hle) (lt_of_lt_of_le hs' hle)) hord
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun δ hδ hle => ?_⟩
  have hle1 : δ ≤ δ₁ := le_trans hle (min_le_left _ _)
  have hle2 : δ ≤ δ₂ := le_trans hle (min_le_right _ _)
  obtain ⟨η₁, hη₁, hloc₂⟩ := s1b_uniform P
    (fun η p => ∀ x, |x - a| < η → x ∈ I → x ∉ singX F → ∃ l, s1b_Local F p bits δ x l)
    (fun η η' _ hle p h x hx => h x (lt_of_lt_of_le hx hle)) (fun p hp => hloc₁ p hp δ hδ hle1)
  obtain ⟨η₂, hη₂, hnear⟩ := exists_eta_fibre_near F a hδ
  refine ⟨min η₁ η₂, lt_min hη₁ hη₂, fun x hx hxI hxs => ?_⟩
  have hx1 : |x - a| < η₁ := lt_of_lt_of_le hx (min_le_left _ _)
  have hx2 : |x - a| < η₂ := lt_of_lt_of_le hx (min_le_right _ _)
  have hex : ∀ p ∈ P, ∃ l, s1b_Local F p bits δ x l := fun p hp => hloc₂ p hp x hx1 hxI hxs
  choose! l hl using hex
  refine ⟨P.flatMap (fun p => (l p).map (fun s => (p.1, Int.fract s))), ?_, ?_, ?_, ?_⟩
  · -- membership: exactly the fibre over `x`
    intro q
    rw [List.mem_flatMap]
    constructor
    · rintro ⟨p, hp, hq⟩
      rw [List.mem_map] at hq
      obtain ⟨s, hs, rfl⟩ := hq
      exact s1b_mem_totalFibre_fract F ((hl p hp).2.1 s hs).2
    · intro hq
      obtain ⟨p, hp, hq1, n, hn⟩ := hnear x hx2 q hq
      have hpP : p ∈ P := (hP p).mpr hp
      refine ⟨p, hpP, ?_⟩
      rw [List.mem_map]
      refine ⟨q.2 + n, (hl p hpP).2.2.1 _ hn ?_, ?_⟩
      · rw [s1b_xOf_add_int, ← hq1]; exact hq.2
      · show (p.1, Int.fract (q.2 + n)) = q
        rw [Int.fract_add_intCast, Int.fract_eq_self.mpr hq.1]
        exact Prod.ext hq1.symm rfl
  · -- strictly descending in height
    rw [List.pairwise_flatMap]
    constructor
    · intro p hp
      rw [List.pairwise_map]
      refine ((hl p hp).2.2.2.1).imp ?_
      intro s s' hss'
      show ht F (p.1, Int.fract s') < ht F (p.1, Int.fract s)
      rw [← s1b_ht_of_sameParam F (s1b_sameParam_fract F p.1 s'), ← s1b_ht_of_sameParam F (s1b_sameParam_fract F p.1 s)]
      exact hss'
    · refine hord₂.imp_of_mem ?_
      intro p p' hp hp' h q hq q' hq'
      rw [List.mem_map] at hq hq'
      obtain ⟨s, hs, rfl⟩ := hq
      obtain ⟨s', hs', rfl⟩ := hq'
      have h1 := (hl p hp).2.1 s hs
      have h1' := (hl p' hp').2.1 s' hs'
      show ht F (p'.1, Int.fract s') < ht F (p.1, Int.fract s)
      rw [← s1b_ht_of_sameParam F (s1b_sameParam_fract F p'.1 s'), ← s1b_ht_of_sameParam F (s1b_sameParam_fract F p.1 s)]
      exact h s s' (lt_of_lt_of_le h1.1 hle2) (lt_of_lt_of_le h1'.1 hle2) (h1.2.trans h1'.2.symm)
        (by rw [h1.2]; exact hxI)
  · -- entrywise continuation
    unfold entriesOf
    apply s1b_forall₂_flatMap
    intro p hp
    rw [List.forall₂_iff_get]
    refine ⟨by simp [(hl p hp).1], ?_⟩
    intro j h₁ h₂
    simp only [List.get_eq_getElem, List.getElem_map, List.getElem_range]
    have hj : j < (l p).length := by simpa using h₁
    exact ⟨s1b_cont_of_sameParam F ((hl p hp).2.2.2.2 j hj).1 (s1b_sameParam_fract F p.1 _).symm,
      (l p)[j], s1b_sameParam_fract F p.1 _, ((hl p hp).2.1 _ (List.getElem_mem hj)).1⟩
  · -- the bits
    rw [List.map_flatMap]
    apply List.flatMap_congr
    intro p hp
    rw [List.map_map]
    apply List.ext_getElem
    · simp [(hl p hp).1]
    · intro j h₁ h₂
      have hj : j < (l p).length := by simpa using h₁
      simp only [List.getElem_map, Function.comp]
      rw [← s1b_dirBit_of_sameParam F (s1b_sameParam_fract F p.1 ((l p)[j]'hj)), ((hl p hp).2.2.2.2 j hj).2,
        List.getD_eq_getElem _ _ h₂]

/-! the two sides -/

/-- just LEFT of `a`: the fibre over `x` is the list of continuations of `entriesBefore a` -/
theorem s1b_before (a : ℝ) : ∃ δ₀ > 0, ∀ δ, 0 < δ → δ ≤ δ₀ → ∃ η > 0, ∀ x, |x - a| < η → x < a → x ∉ singX F →
    ∃ L : List (Param F.c), (∀ q, q ∈ L ↔ q ∈ totalFibre F x) ∧ L.Pairwise (fun q q' => ht F q' < ht F q) ∧
      List.Forall₂ (s1b_ContNear F δ) L (entriesBefore F a) ∧ L.map (dirBit F) = cutBefore F a := by
  have key := s1b_combine F a (Set.Iio a) (beforeBits F) (fibreListBefore F a) (mem_fibreListBefore F a) ?_ ?_
  · exact key
  · intro p hp
    have hp' := (mem_fibreListBefore F a p).mp hp
    by_cases hc : F.IsCusp p
    · rcases F.isLeftCusp_or_isRightCusp hc with hl | hr
      · exact s1b_local_leftCusp_before F hp' hl
      · exact s1b_local_rightCusp_before F hp' hr
    · obtain ⟨δ₀, hδ₀, h⟩ := s1b_local_regular F a (beforeBits F) hp' hc (s1b_bits_regular_before F hc)
      exact ⟨δ₀, hδ₀, fun δ hδ hle => (h δ hδ hle).imp fun η hη =>
        ⟨hη.1, fun x hx hxI _ => hη.2 x hx (ne_of_lt hxI)⟩⟩
  · have h := (fibreListBefore_pairwise F a).and (fibreListBefore_nodup F a)
    refine h.imp_of_mem ?_
    rintro p p' hp hp' ⟨hle, hne⟩
    have hpF := (mem_fibreListBefore F a p).mp hp
    have hp'F := (mem_fibreListBefore F a p').mp hp'
    unfold beforeLE at hle
    rw [decide_eq_true_iff, Prod.Lex.toLex_le_toLex] at hle
    rcases hle with hlt | ⟨heq, hsl⟩
    · simp only at hlt
      obtain ⟨δ, hδ, h⟩ := s1b_ord_of_lt F (p := p) (p' := p') (by linarith)
      exact ⟨δ, hδ, fun s s' hs hs' _ _ => h s s' hs hs'⟩
    · simp only at heq hsl
      have hd : F.IsDouble p p' := ⟨fun hs => hne (SameParam.eq_of_mem_Ico hpF.1 hp'F.1 hs),
        Prod.ext (hpF.2.trans hp'F.2.symm) (by show ht F p = ht F p'; linarith)⟩
      have hou : F.IsOverUnder p p' := ⟨hd, lt_of_le_of_ne hsl (F.slope_ne_of_isDouble hd)⟩
      obtain ⟨δ, hδ, h⟩ := cross_height_order F hou
      refine ⟨δ, hδ, fun s s' hs hs' hx hxI => ?_⟩
      exact (h s s' hs hs' hx).1 (by rw [hpF.2]; exact hxI)

/-- just RIGHT of `a`: the fibre over `x` is the list of continuations of `entriesAfter a` -/
theorem s1b_after (a : ℝ) : ∃ δ₀ > 0, ∀ δ, 0 < δ → δ ≤ δ₀ → ∃ η > 0, ∀ x, |x - a| < η → a < x → x ∉ singX F →
    ∃ L : List (Param F.c), (∀ q, q ∈ L ↔ q ∈ totalFibre F x) ∧ L.Pairwise (fun q q' => ht F q' < ht F q) ∧
      List.Forall₂ (s1b_ContNear F δ) L (entriesAfter F a) ∧ L.map (dirBit F) = cutAfter F a := by
  have key := s1b_combine F a (Set.Ioi a) (afterBits F) (fibreListAfter F a) (mem_fibreListAfter F a) ?_ ?_
  · exact key
  · intro p hp
    have hp' := (mem_fibreListAfter F a p).mp hp
    by_cases hc : F.IsCusp p
    · rcases F.isLeftCusp_or_isRightCusp hc with hl | hr
      · exact s1b_local_leftCusp_after F hp' hl
      · exact s1b_local_rightCusp_after F hp' hr
    · obtain ⟨δ₀, hδ₀, h⟩ := s1b_local_regular F a (afterBits F) hp' hc (s1b_bits_regular_after F hc)
      exact ⟨δ₀, hδ₀, fun δ hδ hle => (h δ hδ hle).imp fun η hη =>
        ⟨hη.1, fun x hx hxI _ => hη.2 x hx (ne_of_gt hxI)⟩⟩
  · have h := (fibreListAfter_pairwise F a).and (fibreListAfter_nodup F a)
    refine h.imp_of_mem ?_
    rintro p p' hp hp' ⟨hle, hne⟩
    have hpF := (mem_fibreListAfter F a p).mp hp
    have hp'F := (mem_fibreListAfter F a p').mp hp'
    unfold afterLE at hle
    rw [decide_eq_true_iff, Prod.Lex.toLex_le_toLex] at hle
    rcases hle with hlt | ⟨heq, hsl⟩
    · simp only at hlt
      obtain ⟨δ, hδ, h⟩ := s1b_ord_of_lt F (p := p) (p' := p') (by linarith)
      exact ⟨δ, hδ, fun s s' hs hs' _ _ => h s s' hs hs'⟩
    · simp only at heq hsl
      have hd : F.IsDouble p' p := ⟨fun hs => hne (SameParam.eq_of_mem_Ico hpF.1 hp'F.1 hs.symm),
        Prod.ext (hp'F.2.trans hpF.2.symm) (by show ht F p' = ht F p; linarith)⟩
      have hou : F.IsOverUnder p' p := ⟨hd, lt_of_le_of_ne (by linarith) (F.slope_ne_of_isDouble hd)⟩
      obtain ⟨δ, hδ, h⟩ := cross_height_order F hou
      refine ⟨δ, hδ, fun s s' hs hs' hx hxI => ?_⟩
      exact (h s' s hs' hs hx.symm).2 (by rw [hp'F.2, ← hx]; exact hxI)

/-! `posAt` and `colAt` along a regular arc -/

/-- the column is constant along an arc whose x-values avoid the singular set (IVT) -/
theorem s1b_colAt_const {i : Fin F.c} {t₀ t₁ : ℝ} (hreg : ∀ t ∈ Set.Icc t₀ t₁, xOf F i t ∉ singX F)
    {s s' : ℝ} (hs : s ∈ Set.Icc t₀ t₁) (hs' : s' ∈ Set.Icc t₀ t₁) :
    colAt F (xOf F i s) = colAt F (xOf F i s') := by
  have key : ∀ u v, u ∈ Set.Icc t₀ t₁ → v ∈ Set.Icc t₀ t₁ → ∀ e : Event F,
      evX F e < xOf F i u → evX F e < xOf F i v := by
    intro u v hu hv e hlt
    by_contra hge
    rw [not_lt] at hge
    have hcont : ContinuousOn (xOf F i) (Set.uIcc v u) := ((F.comp i).continuous.fst).continuousOn
    have hmem : evX F e ∈ Set.uIcc (xOf F i v) (xOf F i u) := Set.mem_uIcc.mpr (Or.inl ⟨hge, hlt.le⟩)
    obtain ⟨w, hw, hwe⟩ := intermediate_value_uIcc hcont hmem
    have hwI : w ∈ Set.Icc t₀ t₁ := by
      rcases Set.mem_uIcc.mp hw with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact ⟨le_trans hv.1 h1, le_trans h2 hu.2⟩
      · exact ⟨le_trans hu.1 h1, le_trans h2 hv.2⟩
    exact hreg w hwI (by rw [hwe]; exact s1b_evX_mem_singX F e)
  unfold colAt
  congr 1
  apply List.filter_congr
  intro e _
  rw [decide_eq_decide]
  exact ⟨key s s' hs hs' e, key s' s hs' hs e⟩

/-- the strand through `(i, t')` over a nearby non-singular `x` continues the entry of `(i, fract t)`: the two
positions agree (identification of the list indices through the continuation data) -/
theorem s1b_posAt_side {i : Fin F.c} {t t' a δ : ℝ} (ha : xOf F i t = a) (has : a ∉ singX F)
    (hkey : ∀ (p : Param F.c) (s : ℝ), p ∈ totalFibre F a → SameParam (i, Int.fract t') (p.1, s) →
      |s - p.2| < δ → p = (i, Int.fract t))
    {L : List (Param F.c)} (hmem : ∀ q, q ∈ L ↔ q ∈ totalFibre F (xOf F i t'))
    (hpair : L.Pairwise (fun q q' => ht F q' < ht F q))
    (hF : List.Forall₂ (s1b_ContNear F δ) L ((fibreListBefore F a).map (fun p => (p, 0)))) :
    posAt F (xOf F i t') (i, Int.fract t') = posAt F a (i, Int.fract t) := by
  have hL : fibreListBefore F (xOf F i t') = L := fibreListBefore_eq_of F _ L
    (s1b_nodup_of_pairwise_lt F hpair) hmem (hpair.imp (fun h => s1b_beforeLE_of_lt F h))
  have hPpair := s1b_fibreListBefore_pairwise_lt F has
  have hqa : (i, Int.fract t) ∈ fibreListBefore F a :=
    (mem_fibreListBefore F a _).mpr (s1b_mem_totalFibre_fract F ha)
  obtain ⟨j₀, hj₀, hPj₀⟩ := List.mem_iff_getElem.mp hqa
  have hqx : (i, Int.fract t') ∈ L := (hmem _).mpr (s1b_mem_totalFibre_fract F rfl)
  obtain ⟨j₁, hj₁, hLj₁⟩ := List.mem_iff_getElem.mp hqx
  rw [List.forall₂_iff_get] at hF
  have hj₁P : j₁ < (fibreListBefore F a).length := by
    have := hF.1; rw [List.length_map] at this; omega
  have hcn := hF.2 j₁ hj₁ (by rw [List.length_map]; exact hj₁P)
  simp only [List.get_eq_getElem, List.getElem_map, hLj₁] at hcn
  obtain ⟨-, s, hs, hsδ⟩ := hcn
  have hPj₁ : (fibreListBefore F a)[j₁] = (i, Int.fract t) :=
    hkey _ s ((mem_fibreListBefore F a _).mp (List.getElem_mem hj₁P)) hs hsδ
  have hj₁j₀ : j₁ = j₀ :=
    (List.Nodup.getElem_inj_iff (s1b_nodup_of_pairwise_lt F hPpair)).mp (hPj₁.trans hPj₀.symm)
  rw [← hLj₁, s1b_posAt_eq_index F hL hpair hj₁, ← hPj₀, s1b_posAt_eq_index F rfl hPpair hj₀, hj₁j₀]

/-- along a regular arc off the singular values the position is locally constant in the parameter -/
theorem s1b_posAt_locally_const {i : Fin F.c} {t₀ t₁ : ℝ} (hreg : ∀ t ∈ Set.Icc t₀ t₁, xOf F i t ∉ singX F) :
    ∀ t ∈ Set.Icc t₀ t₁, ∃ ε > 0, ∀ t' ∈ Set.Icc t₀ t₁, |t' - t| < ε →
      posAt F (xOf F i t') (i, Int.fract t') = posAt F (xOf F i t) (i, Int.fract t) := by
  intro t ht
  have has : xOf F i t ∉ singX F := hreg t ht
  have hreg_t : ¬ F.IsCusp (i, t) := (regular_of_notMem_singX F (p := (i, t)) has).1
  obtain ⟨δr, hδr, -, hinj, -⟩ := regular_local_graph F hreg_t
  obtain ⟨δb, hδb, hb⟩ := s1b_before F (xOf F i t)
  obtain ⟨δc, hδc, hc⟩ := s1b_after F (xOf F i t)
  obtain ⟨δ, hδ, hδb', hδc', hδr'⟩ : ∃ δ > 0, δ ≤ δb ∧ δ ≤ δc ∧ δ ≤ δr / 2 :=
    ⟨min (min δb δc) (δr / 2), by positivity, le_trans (min_le_left _ _) (min_le_left _ _),
      le_trans (min_le_left _ _) (min_le_right _ _), min_le_right _ _⟩
  obtain ⟨ηb, hηb, hb'⟩ := hb δ hδ hδb'
  obtain ⟨ηc, hηc, hc'⟩ := hc δ hδ hδc'
  obtain ⟨ε₁, hε₁, hcont⟩ :=
    Metric.continuous_iff.mp ((F.comp i).continuous.fst) t (min ηb ηc) (lt_min hηb hηc)
  refine ⟨min ε₁ (δr / 2), by positivity, fun t' ht' htt => ?_⟩
  have hx' : xOf F i t' ∉ singX F := hreg t' ht'
  have hnear : |xOf F i t' - xOf F i t| < min ηb ηc := by
    have := hcont t' (by rw [Real.dist_eq]; exact lt_of_lt_of_le htt (min_le_left _ _))
    rwa [Real.dist_eq] at this
  have htt' : |t' - t| < δr / 2 := lt_of_lt_of_le htt (min_le_right _ _)
  have hkey : ∀ (p : Param F.c) (s : ℝ), p ∈ totalFibre F (xOf F i t) →
      SameParam (i, Int.fract t') (p.1, s) → |s - p.2| < δ → p = (i, Int.fract t) := by
    intro p s hp hsp hsδ
    obtain ⟨hp1, n, hn⟩ := hsp
    dsimp only at hp1 hn
    have hp2 : xOf F p.1 p.2 = xOf F i t := hp.2
    rw [← hp1] at hp2
    have hvx : xOf F i (p.2 + ((⌊t'⌋ - n : ℤ) : ℝ)) = xOf F i t := by
      rw [s1b_xOf_add_int]; exact hp2
    have hvt : |p.2 + ((⌊t'⌋ - n : ℤ) : ℝ) - t| < δr := by
      have h1 : p.2 + ((⌊t'⌋ - n : ℤ) : ℝ) - t = (p.2 - s) + (t' - t) := by
        rw [hn]; push_cast
        have := Int.fract_add_floor t'
        linarith
      rw [h1]
      calc |(p.2 - s) + (t' - t)| ≤ |p.2 - s| + |t' - t| := abs_add_le _ _
        _ < δ + δr / 2 := add_lt_add (by rwa [abs_sub_comm]) htt'
        _ ≤ δr / 2 + δr / 2 := add_le_add hδr' le_rfl
        _ = δr := by ring
    have hvt' : p.2 + ((⌊t'⌋ - n : ℤ) : ℝ) = t :=
      hinj _ (s1b_mem_Ioo_of_abs hvt) t ⟨by linarith, by linarith⟩ hvx
    have hfr : Int.fract t = p.2 := by
      rw [Int.fract_eq_iff]
      refine ⟨hp.1.1, hp.1.2, ⌊t'⌋ - n, ?_⟩
      rw [← hvt']; push_cast; ring
    exact Prod.ext hp1.symm hfr.symm
  rcases lt_trichotomy (xOf F i t') (xOf F i t) with hlt | heq | hgt
  · obtain ⟨L, hmem, hpair, hF, -⟩ := hb' (xOf F i t') (lt_of_lt_of_le hnear (min_le_left _ _)) hlt hx'
    rw [entriesBefore_eq_of_notMem_singX F has] at hF
    exact s1b_posAt_side F rfl has hkey hmem hpair hF
  · have : t' = t :=
      hinj t' (s1b_mem_Ioo_of_abs (lt_of_lt_of_le htt' (by linarith))) t ⟨by linarith, by linarith⟩ heq
    rw [this]
  · obtain ⟨L, hmem, hpair, hF, -⟩ := hc' (xOf F i t') (lt_of_lt_of_le hnear (min_le_right _ _)) hgt hx'
    have hE : entriesAfter F (xOf F i t) = (fibreListBefore F (xOf F i t)).map (fun p => (p, 0)) := by
      unfold entriesAfter
      rw [fibreListAfter_eq_fibreListBefore F has]
      apply s1b_entriesOf_eq_map
      intro p hp
      have hp' := (mem_fibreListBefore F _ p).mp hp
      rw [s1b_bits_regular_after F (regular_of_notMem_singX F (by rw [hp'.2]; exact has)).1]
      rfl
    rw [hE] at hF
    exact s1b_posAt_side F rfl has hkey hmem hpair hF

/-! the corrected `dirBit_of_cont` statements (the leaves as stated are FALSE when `q` is a cusp; see the report) -/

/-- the two bits of a right cusp before its x-value, in the shape of `s1b_local_two_arms` -/
theorem s1b_beforeBits_rightCusp {p : Param F.c} (hr : F.IsRightCusp p) :
    beforeBits F p = if F.cuspDisc p < 0 then [true, !true] else [!true, true] := by
  unfold beforeBits
  rw [ite_eq_right (fun hl => left_right_absurd F hl hr), ite_eq_left hr]
  rfl

/-- the two bits of a left cusp after its x-value, in the shape of `s1b_local_two_arms` -/
theorem s1b_afterBits_leftCusp {p : Param F.c} (hl : F.IsLeftCusp p) :
    afterBits F p = if F.cuspDisc p < 0 then [false, !false] else [!false, false] := by
  unfold afterBits
  rw [ite_eq_right (fun hr => left_right_absurd F hl hr), ite_eq_left hl]
  rcases lt_or_gt_of_ne (F.cuspDisc_ne_zero_of_isCusp hl.1) with h | h
  · rw [ite_eq_right (not_lt.mpr h.le), ite_eq_left h]; rfl
  · rw [ite_eq_left h, ite_eq_right (not_lt.mpr h.le)]; rfl

/-- on the cusp-free arc from `s` towards the cusp `t₀`, `x'` keeps its sign up to a point as close to `t₀` as
required (on the side of `s`) -/
theorem s1b_xvel_side {i : Fin F.c} {s t₀ δ : ℝ} (hδ : 0 < δ) (hne : s ≠ t₀)
    (hnc : ∀ u, min s t₀ < u → u < max s t₀ → ¬ F.IsCusp (i, u)) (hsc : ¬ F.IsCusp (i, s)) :
    ∃ u, dist u t₀ < δ ∧ (s < t₀ → u < t₀) ∧ (t₀ < s → t₀ < u) ∧ 0 < xvel F i s * xvel F i u := by
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hu : max s (t₀ - δ / 2) < t₀ := max_lt hlt (by linarith)
    refine ⟨max s (t₀ - δ / 2), ?_, fun _ => hu, fun h => absurd h (not_lt.mpr hlt.le), ?_⟩
    · rw [Real.dist_eq, abs_sub_lt_iff]
      exact ⟨by linarith, by linarith [le_max_right s (t₀ - δ / 2)]⟩
    · apply xvel_mul_pos_of_cuspFree F isPreconnected_Ico (s := Set.Ico s t₀) _ ⟨le_rfl, hlt⟩
        ⟨le_max_left _ _, hu⟩
      intro u hu'
      rcases eq_or_lt_of_le hu'.1 with h | h
      · rw [← h]; exact hsc
      · exact hnc u (by rw [min_eq_left hlt.le]; exact h) (by rw [max_eq_right hlt.le]; exact hu'.2)
  · have hu : t₀ < min s (t₀ + δ / 2) := lt_min hgt (by linarith)
    refine ⟨min s (t₀ + δ / 2), ?_, fun h => absurd h (not_lt.mpr hgt.le), fun _ => hu, ?_⟩
    · rw [Real.dist_eq, abs_sub_lt_iff]
      exact ⟨by linarith [min_le_right s (t₀ + δ / 2)], by linarith⟩
    · apply xvel_mul_pos_of_cuspFree F isPreconnected_Ioc (s := Set.Ioc t₀ s) _ ⟨hgt, le_rfl⟩
        ⟨hu, min_le_left _ _⟩
      intro u hu'
      rcases eq_or_lt_of_le hu'.2 with h | h
      · rw [h]; exact hsc
      · exact hnc u (by rw [min_eq_right hgt.le]; exact hu'.1) (by rw [max_eq_left hgt.le]; exact h)

/-- the bit bookkeeping at a cusp entry: the arm on the side of `s` carries the bit determined by the side, and
`Cont` fixes the index `j` -/
theorem s1b_dirBit_of_cont_cusp_aux {i : Fin F.c} {t₀ s : ℝ} {j : ℕ} (bits : Param F.c → Cuts) (b₁ : Bool)
    (hbits : bits (i, t₀) = if F.cuspDisc (i, t₀) < 0 then [b₁, !b₁] else [!b₁, b₁])
    (hj : j < 2) (hcusp : s < t₀ ↔ (j = 0 ↔ F.cuspDisc (i, t₀) < 0))
    (hsgn : dirBit F (i, s) = if s < t₀ then b₁ else !b₁) :
    dirBit F (i, s) = (bits (i, t₀)).getD j false := by
  rw [hsgn, hbits]
  by_cases hd : F.cuspDisc (i, t₀) < 0
  · rw [ite_eq_left hd]
    by_cases hlt : s < t₀
    · have hj0 : j = 0 := (hcusp.mp hlt).mpr hd
      subst hj0; simp [hlt]
    · have hj1 : j = 1 := by
        have : ¬ (j = 0) := fun h0 => hlt (hcusp.mpr ⟨fun _ => hd, fun _ => h0⟩)
        omega
      subst hj1; simp [hlt]
  · rw [ite_eq_right hd]
    by_cases hlt : s < t₀
    · have hj1 : j = 1 := by
        have : ¬ (j = 0) := fun h0 => hd ((hcusp.mp hlt).mp h0)
        omega
      subst hj1; simp [hlt]
    · have hj0 : j = 0 := by
        by_contra h0
        exact hlt (hcusp.mpr ⟨fun h => absurd h h0, fun h => absurd h hd⟩)
      subst hj0; simp [hlt]

/-- the closed parameter interval between a regular `s` and a regular `t₀` with no cusp strictly between is
cusp-free, so the direction bits agree -/
theorem s1b_dirBit_eq_of_cuspFree {i : Fin F.c} {s t₀ : ℝ}
    (hnc : ∀ u, min s t₀ < u → u < max s t₀ → ¬ F.IsCusp (i, u)) (hsc : ¬ F.IsCusp (i, s))
    (htc : ¬ F.IsCusp (i, t₀)) : dirBit F (i, s) = dirBit F (i, t₀) := by
  show decide (0 < xvel F i s) = decide (0 < xvel F i t₀)
  apply s1b_decide_pos_eq
  apply xvel_mul_pos_of_cuspFree F isPreconnected_uIcc (s := Set.uIcc s t₀) _ Set.left_mem_uIcc
    Set.right_mem_uIcc
  intro u hu
  rcases eq_or_ne u s with rfl | hus
  · exact hsc
  rcases eq_or_ne u t₀ with rfl | hut
  · exact htc
  apply hnc u
  · rcases Set.mem_uIcc.mp hu with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [min_eq_left (le_trans h1 h2)]; exact lt_of_le_of_ne h1 (Ne.symm hus)
    · rw [min_eq_right (le_trans h1 h2)]; exact lt_of_le_of_ne h1 (Ne.symm hut)
  · rcases Set.mem_uIcc.mp hu with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [max_eq_right (le_trans h1 h2)]; exact lt_of_le_of_ne h2 hut
    · rw [max_eq_left (le_trans h1 h2)]; exact lt_of_le_of_ne h2 hus

/-- CORRECTED `dirBit_of_cont_before`: with the extra hypothesis `¬ F.IsCusp q` (automatic for a fibre point over
a non-singular `x`) a continuation carries the bit of its entry.  Without it the leaf is false: `Cont F q a`
allows `q` to be the cusp bounding the cusp-free arc adjacent to `a.1`, where `dirBit q = false`. -/
theorem s1b_dirBit_of_cont_before {q : Param F.c} {a : Param F.c × ℕ} (hq : ¬ F.IsCusp q)
    (hj : a.2 < (beforeBits F a.1).length) (h : Cont F q a) : dirBit F q = entryBit F (beforeBits F) a := by
  obtain ⟨⟨i, t₀⟩, j⟩ := a
  obtain ⟨-, s, hs, hne, hnc, hcusp⟩ := h
  dsimp only at hs hne hnc hcusp hj ⊢
  have hsc : ¬ F.IsCusp (i, s) := fun hc => hq ((F.isCusp_iff_of_sameParam hs).mp hc)
  unfold entryBit
  dsimp only
  rw [← s1b_dirBit_of_sameParam F hs]
  by_cases hc : F.IsCusp (i, t₀)
  · have hr : F.IsRightCusp (i, t₀) := by
      rcases F.isLeftCusp_or_isRightCusp hc with hl | hr
      · exfalso; rw [beforeBits, ite_eq_left hl] at hj; exact absurd hj (by simp)
      · exact hr
    have hbits := s1b_beforeBits_rightCusp F hr
    have hj2 : j < 2 := by rw [hbits] at hj; split_ifs at hj <;> simpa using hj
    obtain ⟨δ, hδ, hvel⟩ := exists_xvel_sign_of_isRightCusp F hr
    obtain ⟨u, hu, hu1, hu2, hmul⟩ := s1b_xvel_side F hδ hne hnc hsc
    apply s1b_dirBit_of_cont_cusp_aux F (beforeBits F) true hbits hj2 (hcusp hc)
    unfold dirBit
    split_ifs with hlt
    · rw [decide_eq_true_iff]; exact (pos_iff_pos_of_mul_pos hmul).mpr ((hvel u hu).1 (hu1 hlt))
    · rw [Bool.not_true, decide_eq_false_iff_not, not_lt]
      exact ((neg_iff_neg_of_mul_pos hmul).mpr
        ((hvel u hu).2 (hu2 (lt_of_le_of_ne (not_lt.mp hlt) (Ne.symm hne))))).le
  · rw [s1b_bits_regular_before F hc] at hj ⊢
    have hj0 : j = 0 := by simpa using hj
    subst hj0
    exact s1b_dirBit_eq_of_cuspFree F hnc hsc hc

/-- CORRECTED `dirBit_of_cont_after` (same extra hypothesis). -/
theorem s1b_dirBit_of_cont_after {q : Param F.c} {a : Param F.c × ℕ} (hq : ¬ F.IsCusp q)
    (hj : a.2 < (afterBits F a.1).length) (h : Cont F q a) : dirBit F q = entryBit F (afterBits F) a := by
  obtain ⟨⟨i, t₀⟩, j⟩ := a
  obtain ⟨-, s, hs, hne, hnc, hcusp⟩ := h
  dsimp only at hs hne hnc hcusp hj ⊢
  have hsc : ¬ F.IsCusp (i, s) := fun hc => hq ((F.isCusp_iff_of_sameParam hs).mp hc)
  unfold entryBit
  dsimp only
  rw [← s1b_dirBit_of_sameParam F hs]
  by_cases hc : F.IsCusp (i, t₀)
  · have hl : F.IsLeftCusp (i, t₀) := by
      rcases F.isLeftCusp_or_isRightCusp hc with hl | hr
      · exact hl
      · exfalso; rw [afterBits, ite_eq_left hr] at hj; exact absurd hj (by simp)
    have hbits := s1b_afterBits_leftCusp F hl
    have hj2 : j < 2 := by rw [hbits] at hj; split_ifs at hj <;> simpa using hj
    obtain ⟨δ, hδ, hvel⟩ := exists_xvel_sign_of_isLeftCusp F hl
    obtain ⟨u, hu, hu1, hu2, hmul⟩ := s1b_xvel_side F hδ hne hnc hsc
    apply s1b_dirBit_of_cont_cusp_aux F (afterBits F) false hbits hj2 (hcusp hc)
    unfold dirBit
    split_ifs with hlt
    · rw [decide_eq_false_iff_not, not_lt]
      exact ((neg_iff_neg_of_mul_pos hmul).mpr ((hvel u hu).1 (hu1 hlt))).le
    · rw [Bool.not_false, decide_eq_true_iff]
      exact (pos_iff_pos_of_mul_pos hmul).mpr
        ((hvel u hu).2 (hu2 (lt_of_le_of_ne (not_lt.mp hlt) (Ne.symm hne))))
  · rw [s1b_bits_regular_after F hc] at hj ⊢
    have hj0 : j = 0 := by simpa using hj
    subst hj0
    exact s1b_dirBit_eq_of_cuspFree F hnc hsc hc

end S1bHelpers

/-- LEAF (S1, the left limit at the level of strand entries): just left of any `a`, the entries of the cut are, in
order, continuations (`Cont`) of the entries of `entriesBefore a` (local models S2/S3 at the singular fibre points,
`regular_local_graph` at the regular ones, `exists_eta_fibre_near`, order preserved by continuity of heights, the
list identified through `fibreListBefore_eq_of`). -/
theorem entriesBefore_left_limit (a : ℝ) :
    ∃ η > 0, ∀ x ∈ Set.Ioo (a - η) a, (entriesBefore F x).length = (entriesBefore F a).length ∧
      ∀ j < (entriesBefore F a).length,
        Cont F ((entriesBefore F x).getD j (dfltP F, 0)).1 ((entriesBefore F a).getD j (dfltP F, 0)) := by
  obtain ⟨δ₀, hδ₀, h⟩ := s1b_before F a
  obtain ⟨η₁, hη₁, h₁⟩ := h δ₀ hδ₀ le_rfl
  obtain ⟨η₂, hη₂, h₂⟩ := s1b_exists_eta_left F a
  refine ⟨min η₁ η₂, lt_min hη₁ hη₂, fun x hx => ?_⟩
  have hxs : x ∉ singX F := h₂ x ⟨by linarith [hx.1, min_le_right η₁ η₂], hx.2⟩
  have hxa : |x - a| < η₁ := abs_sub_lt_iff.mpr ⟨by linarith [hx.2], by linarith [hx.1, min_le_left η₁ η₂]⟩
  obtain ⟨L, hmem, hpair, hF, -⟩ := h₁ x hxa hx.2 hxs
  have hL : fibreListBefore F x = L := fibreListBefore_eq_of F x L (s1b_nodup_of_pairwise_lt F hpair) hmem
    (hpair.imp (fun h => s1b_beforeLE_of_lt F h))
  have hE : entriesBefore F x = L.map (fun p => (p, 0)) := by
    rw [entriesBefore_eq_of_notMem_singX F hxs, hL]
  rw [List.forall₂_iff_get] at hF
  refine ⟨by rw [hE, List.length_map, hF.1], fun j hj => ?_⟩
  have hjL : j < L.length := by rw [hF.1]; exact hj
  rw [hE, List.getD_eq_getElem _ _ (by rw [List.length_map]; exact hjL), List.getD_eq_getElem _ _ hj,
    List.getElem_map]
  exact (hF.2 j hjL hj).1

/-- LEAF (S1, the right limit): just right of any `a`, the entries of the cut are continuations of `entriesAfter a`. -/
theorem entriesAfter_right_limit (a : ℝ) :
    ∃ η > 0, ∀ x ∈ Set.Ioo a (a + η), (entriesBefore F x).length = (entriesAfter F a).length ∧
      ∀ j < (entriesAfter F a).length,
        Cont F ((entriesBefore F x).getD j (dfltP F, 0)).1 ((entriesAfter F a).getD j (dfltP F, 0)) := by
  obtain ⟨δ₀, hδ₀, h⟩ := s1b_after F a
  obtain ⟨η₁, hη₁, h₁⟩ := h δ₀ hδ₀ le_rfl
  obtain ⟨η₂, hη₂, h₂⟩ := s1b_exists_eta_right F a
  refine ⟨min η₁ η₂, lt_min hη₁ hη₂, fun x hx => ?_⟩
  have hxs : x ∉ singX F := h₂ x ⟨hx.1, by linarith [hx.2, min_le_right η₁ η₂]⟩
  have hxa : |x - a| < η₁ := abs_sub_lt_iff.mpr ⟨by linarith [hx.2, min_le_left η₁ η₂], by linarith [hx.1]⟩
  obtain ⟨L, hmem, hpair, hF, -⟩ := h₁ x hxa hx.1 hxs
  have hL : fibreListBefore F x = L := fibreListBefore_eq_of F x L (s1b_nodup_of_pairwise_lt F hpair) hmem
    (hpair.imp (fun h => s1b_beforeLE_of_lt F h))
  have hE : entriesBefore F x = L.map (fun p => (p, 0)) := by
    rw [entriesBefore_eq_of_notMem_singX F hxs, hL]
  rw [List.forall₂_iff_get] at hF
  refine ⟨by rw [hE, List.length_map, hF.1], fun j hj => ?_⟩
  have hjL : j < L.length := by rw [hF.1]; exact hj
  rw [hE, List.getD_eq_getElem _ _ (by rw [List.length_map]; exact hjL), List.getD_eq_getElem _ _ hj,
    List.getElem_map]
  exact (hF.2 j hjL hj).1

/-! `dirBit_of_cont_before` / `dirBit_of_cont_after` removed: false as stated (W3S_MERGE_REPORT.md §4; consumed by
nothing), replaced by the proved `s1b_dirBit_of_cont_before` / `s1b_dirBit_of_cont_after` (extra hypothesis `¬ F.IsCusp q`). -/

/-- LEAF (S1): the one-sided limits of the cut itself (bits), from the entry-level limits. -/
theorem cutBefore_left_limit (a : ℝ) : ∃ η > 0, ∀ x ∈ Set.Ioo (a - η) a, cutBefore F x = cutBefore F a := by
  obtain ⟨δ₀, hδ₀, h⟩ := s1b_before F a
  obtain ⟨η₁, hη₁, h₁⟩ := h δ₀ hδ₀ le_rfl
  obtain ⟨η₂, hη₂, h₂⟩ := s1b_exists_eta_left F a
  refine ⟨min η₁ η₂, lt_min hη₁ hη₂, fun x hx => ?_⟩
  have hxs : x ∉ singX F := h₂ x ⟨by linarith [hx.1, min_le_right η₁ η₂], hx.2⟩
  have hxa : |x - a| < η₁ := abs_sub_lt_iff.mpr ⟨by linarith [hx.2], by linarith [hx.1, min_le_left η₁ η₂]⟩
  obtain ⟨L, hmem, hpair, -, hbits⟩ := h₁ x hxa hx.2 hxs
  have hL : fibreListBefore F x = L := fibreListBefore_eq_of F x L (s1b_nodup_of_pairwise_lt F hpair) hmem
    (hpair.imp (fun h => s1b_beforeLE_of_lt F h))
  rw [cutBefore_eq_map_dirBit F hxs, hL, hbits]

theorem cutAfter_right_limit (a : ℝ) : ∃ η > 0, ∀ x ∈ Set.Ioo a (a + η), cutBefore F x = cutAfter F a := by
  obtain ⟨δ₀, hδ₀, h⟩ := s1b_after F a
  obtain ⟨η₁, hη₁, h₁⟩ := h δ₀ hδ₀ le_rfl
  obtain ⟨η₂, hη₂, h₂⟩ := s1b_exists_eta_right F a
  refine ⟨min η₁ η₂, lt_min hη₁ hη₂, fun x hx => ?_⟩
  have hxs : x ∉ singX F := h₂ x ⟨hx.1, by linarith [hx.2, min_le_right η₁ η₂]⟩
  have hxa : |x - a| < η₁ := abs_sub_lt_iff.mpr ⟨by linarith [hx.2, min_le_left η₁ η₂], by linarith [hx.1]⟩
  obtain ⟨L, hmem, hpair, -, hbits⟩ := h₁ x hxa hx.1 hxs
  have hL : fibreListBefore F x = L := fibreListBefore_eq_of F x L (s1b_nodup_of_pairwise_lt F hpair) hmem
    (hpair.imp (fun h => s1b_beforeLE_of_lt F h))
  rw [cutBefore_eq_map_dirBit F hxs, hL, hbits]

/-- LEAF (S1): between consecutive singular x-values the cut is constant (`IsLocallyConstant` on the preconnected
gap, from the two limits and `cutAfter_eq_cutBefore`): the cut just right of `a` is the cut just left of `b`. -/
theorem cutAfter_eq_cutBefore_of_gap {a b : ℝ} (hab : a < b) (hgap : ∀ x ∈ Set.Ioo a b, x ∉ singX F) :
    cutAfter F a = cutBefore F b := by
  have hloc : ∀ x ∈ Set.Ioo a b, ∃ ε > 0, ∀ y ∈ Set.Ioo a b, |y - x| < ε → cutBefore F y = cutBefore F x := by
    intro x hx
    obtain ⟨η₁, hη₁, h₁⟩ := cutBefore_left_limit F x
    obtain ⟨η₂, hη₂, h₂⟩ := cutAfter_right_limit F x
    refine ⟨min η₁ η₂, lt_min hη₁ hη₂, fun y _ hy => ?_⟩
    rw [abs_sub_lt_iff] at hy
    rcases lt_trichotomy y x with hlt | heq | hgt
    · exact h₁ y ⟨by linarith [min_le_left η₁ η₂], hlt⟩
    · rw [heq]
    · rw [h₂ y ⟨hgt, by linarith [min_le_right η₁ η₂]⟩, cutAfter_eq_cutBefore F (hgap x hx)]
  obtain ⟨η₁, hη₁, h₁⟩ := cutAfter_right_limit F a
  obtain ⟨η₂, hη₂, h₂⟩ := cutBefore_left_limit F b
  have hm₁ : 0 < min (η₁ / 2) ((b - a) / 2) := lt_min (by linarith) (by linarith)
  have hm₂ : 0 < min (η₂ / 2) ((b - a) / 2) := lt_min (by linarith) (by linarith)
  have hx : a + min (η₁ / 2) ((b - a) / 2) ∈ Set.Ioo a b :=
    ⟨by linarith, by linarith [min_le_right (η₁ / 2) ((b - a) / 2)]⟩
  have hy : b - min (η₂ / 2) ((b - a) / 2) ∈ Set.Ioo a b :=
    ⟨by linarith [min_le_right (η₂ / 2) ((b - a) / 2)], by linarith⟩
  rw [← h₁ (a + min (η₁ / 2) ((b - a) / 2)) ⟨by linarith, by linarith [min_le_left (η₁ / 2) ((b - a) / 2)]⟩,
    ← h₂ (b - min (η₂ / 2) ((b - a) / 2)) ⟨by linarith [min_le_left (η₂ / 2) ((b - a) / 2)], by linarith⟩]
  exact s1b_const_of_locally_const_on isPreconnected_Ioo hloc hx hy

/-- LEAF (S1): along a regular arc whose x-values avoid the singular set, the position of the strand in the fibre
and the column of its x-value are constant (the entry-level limits at each non-singular `x` give local constancy). -/
theorem posAt_const_of_arc {i : Fin F.c} {t₀ t₁ : ℝ} (h01 : t₀ ≤ t₁)
    (hreg : ∀ t ∈ Set.Icc t₀ t₁, xOf F i t ∉ singX F) :
    posAt F (xOf F i t₀) (i, Int.fract t₀) = posAt F (xOf F i t₁) (i, Int.fract t₁) ∧
      colAt F (xOf F i t₀) = colAt F (xOf F i t₁) := by
  constructor
  · exact s1b_const_of_locally_const_on isPreconnected_Icc
      (f := fun t => posAt F (xOf F i t) (i, Int.fract t)) (s1b_posAt_locally_const F hreg)
      ⟨le_rfl, h01⟩ ⟨h01, le_rfl⟩
  · exact s1b_colAt_const F hreg ⟨le_rfl, h01⟩ ⟨h01, le_rfl⟩

/-! #### S4 leaves: events and the word -/

/-! ### S4a helpers -/
section S4aHelpers

/-! Pure list combinatorics: splitting a filter of a sorted list, and identifying short lists by their members. -/

/-- Splitting the filter of a `Pairwise R` list: if no `Q`-element precedes a `P`-element and `P`, `Q` are
disjoint, the `P ∨ Q`-elements are the `P`-elements followed by the `Q`-elements. -/
theorem s4a_filter_or_split {α : Type*} {R : α → α → Prop} {L : List α} (hL : L.Pairwise R)
    (P Q : α → Bool) (hdisj : ∀ a, P a = true → Q a = false)
    (hord : ∀ a b, R a b → Q a = true → P b = false) :
    L.filter (fun a => P a || Q a) = L.filter P ++ L.filter Q := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    rw [List.pairwise_cons] at hL
    obtain ⟨ha, hL⟩ := hL
    have ih := ih hL
    by_cases hP : P a = true
    · have hQ : Q a = false := hdisj a hP
      simp [hP, hQ, ih]
    · have hP' : P a = false := by simpa using hP
      by_cases hQ : Q a = true
      · have hnil : L.filter P = [] := by
          rw [List.filter_eq_nil_iff]
          intro b hb
          have := hord a b (ha b hb) hQ
          simp [this]
        simp [hP', hQ, ih, hnil]
      · have hQ' : Q a = false := by simpa using hQ
        simp [hP', hQ', ih]

/-- a nodup list whose members are exactly `{p}` is `[p]` -/
theorem s4a_eq_singleton_of {α : Type*} {L : List α} (hnd : L.Nodup) {p : α}
    (hmem : ∀ x, x ∈ L ↔ x = p) : L = [p] := by
  match L, hnd, hmem with
  | [], _, hmem => exact absurd ((hmem p).2 rfl) (List.not_mem_nil)
  | a :: L, hnd, hmem =>
    have ha : a = p := (hmem a).1 (List.mem_cons_self ..)
    subst ha
    have hL : L = [] := by
      rw [List.eq_nil_iff_forall_not_mem]
      intro x hx
      have hx' : x = a := (hmem x).1 (List.mem_cons_of_mem _ hx)
      subst hx'
      exact (List.nodup_cons.1 hnd).1 hx
    rw [hL]

/-- a nodup list, `Pairwise R`, whose members are exactly `{o, u}` with `¬ R u o`, is `[o, u]` -/
theorem s4a_eq_pair_of {α : Type*} {R : α → α → Prop} {L : List α} (hnd : L.Nodup) (hR : L.Pairwise R)
    {o u : α} (hne : o ≠ u) (hmem : ∀ x, x ∈ L ↔ x = o ∨ x = u) (hnR : ¬ R u o) :
    L = [o, u] := by
  match L, hnd, hR, hmem with
  | [], _, _, hmem => exact absurd ((hmem o).2 (Or.inl rfl)) (List.not_mem_nil)
  | [a], _, _, hmem =>
    have ho : o = a := by simpa using (hmem o).2 (Or.inl rfl)
    have hu : u = a := by simpa using (hmem u).2 (Or.inr rfl)
    exact absurd (ho.trans hu.symm) hne
  | a :: b :: L, hnd, hR, hmem =>
    have hab : a ≠ b := by
      intro h; subst h
      exact (List.nodup_cons.1 hnd).1 (List.mem_cons_self ..)
    have ha : a = o ∨ a = u := (hmem a).1 (List.mem_cons_self ..)
    have hb : b = o ∨ b = u := (hmem b).1 (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    have hL : L = [] := by
      rw [List.eq_nil_iff_forall_not_mem]
      intro x hx
      have hx' : x = o ∨ x = u := (hmem x).1 (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hx))
      have hxa : x ≠ a := fun h => (List.nodup_cons.1 hnd).1 (h ▸ List.mem_cons_of_mem _ hx)
      have hxb : x ≠ b := fun h => (List.nodup_cons.1 (List.nodup_cons.1 hnd).2).1 (h ▸ hx)
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> rcases hx' with rfl | rfl <;>
        first | exact hab rfl | exact hxa rfl | exact hxb rfl
    subst hL
    have hRab : R a b := (List.pairwise_cons.1 hR).1 b (List.mem_cons_self ..)
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact absurd rfl hab
    · rfl
    · exact absurd hRab hnR
    · exact absurd rfl hab

/-! The sort keys and the bits. -/

theorem s4a_ht_le_of_beforeLE {p q : Param F.c} (h : beforeLE F p q = true) : ht F q ≤ ht F p := by
  unfold beforeLE at h
  rw [decide_eq_true_eq, Prod.Lex.toLex_le_toLex] at h
  rcases h with h | ⟨h, -⟩ <;> dsimp only at h <;> linarith

theorem s4a_ht_le_of_afterLE {p q : Param F.c} (h : afterLE F p q = true) : ht F q ≤ ht F p := by
  unfold afterLE at h
  rw [decide_eq_true_eq, Prod.Lex.toLex_le_toLex] at h
  rcases h with h | ⟨h, -⟩ <;> dsimp only at h <;> linarith

theorem s4a_beforeBits_of_regular {p : Param F.c} (h : ¬ F.IsCusp p) : beforeBits F p = [dirBit F p] := by
  unfold beforeBits
  rw [ite_eq_right (fun hl => h hl.1), ite_eq_right (fun hr => h hr.1)]

theorem s4a_afterBits_of_regular {p : Param F.c} (h : ¬ F.IsCusp p) : afterBits F p = [dirBit F p] := by
  unfold afterBits
  rw [ite_eq_right (fun hr => h hr.1), ite_eq_right (fun hl => h hl.1)]

/-- over `x₀`, if every `P`-point of the fibre is regular, the "before" and "after" sublists of `P`-points agree
(both are the `P`-points sorted by strictly descending height) -/
theorem s4a_filter_before_eq_after (x₀ : ℝ) (P : Param F.c → Bool)
    (hreg : ∀ p ∈ totalFibre F x₀, P p = true → ¬ F.IsCusp p ∧ ∀ q, ¬ F.IsDouble p q) :
    (fibreListBefore F x₀).filter P = (fibreListAfter F x₀).filter P := by
  have : Std.Irrefl (fun p q : Param F.c => ht F q < ht F p) := ⟨fun a => lt_irrefl _⟩
  apply List.Pairwise.eq_of_mem_iff (r := fun p q : Param F.c => ht F q < ht F p)
  · have h1 := ((fibreListBefore_pairwise F x₀).and (fibreListBefore_nodup F x₀)).filter P
    refine h1.imp_of_mem ?_
    intro a b ha hb hab
    obtain ⟨hle, hne⟩ := hab
    rw [List.mem_filter] at ha hb
    have ha' := (mem_fibreListBefore F x₀ a).1 ha.1
    have hb' := (mem_fibreListBefore F x₀ b).1 hb.1
    refine lt_of_le_of_ne (s4a_ht_le_of_beforeLE F hle) ?_
    intro heq
    exact (hreg a ha' ha.2).2 b ⟨fun hs => hne (SameParam.eq_of_mem_Ico ha'.1 hb'.1 hs),
      Prod.ext (ha'.2.trans hb'.2.symm) heq.symm⟩
  · have h1 := ((fibreListAfter_pairwise F x₀).and (fibreListAfter_nodup F x₀)).filter P
    refine h1.imp_of_mem ?_
    intro a b ha hb hab
    obtain ⟨hle, hne⟩ := hab
    rw [List.mem_filter] at ha hb
    have ha' := (mem_fibreListAfter F x₀ a).1 ha.1
    have hb' := (mem_fibreListAfter F x₀ b).1 hb.1
    refine lt_of_le_of_ne (s4a_ht_le_of_afterLE F hle) ?_
    intro heq
    exact (hreg a ha' ha.2).2 b ⟨fun hs => hne (SameParam.eq_of_mem_Ico ha'.1 hb'.1 hs),
      Prod.ext (ha'.2.trans hb'.2.symm) heq.symm⟩
  · intro x
    rw [List.mem_filter, List.mem_filter, mem_fibreListBefore, mem_fibreListAfter]

theorem s4a_flatMap_congr {α β : Type*} {f g : α → List β} :
    ∀ {L : List α}, (∀ a ∈ L, f a = g a) → L.flatMap f = L.flatMap g
  | [], _ => rfl
  | a :: L, h => by
    rw [List.flatMap_cons, List.flatMap_cons, h a (List.mem_cons_self ..),
      s4a_flatMap_congr (fun b hb => h b (List.mem_cons_of_mem _ hb))]

/-- the bits of the regular `P`-points: "before" = "after" -/
theorem s4a_flatMap_before_eq_after (x₀ : ℝ) (P : Param F.c → Bool)
    (hreg : ∀ p ∈ totalFibre F x₀, P p = true → ¬ F.IsCusp p ∧ ∀ q, ¬ F.IsDouble p q) :
    ((fibreListBefore F x₀).filter P).flatMap (beforeBits F) =
      ((fibreListAfter F x₀).filter P).flatMap (afterBits F) := by
  rw [← s4a_filter_before_eq_after F x₀ P hreg]
  apply s4a_flatMap_congr
  intro a ha
  rw [List.mem_filter, mem_fibreListBefore] at ha
  rw [s4a_beforeBits_of_regular F (hreg a ha.1 ha.2).1, s4a_afterBits_of_regular F (hreg a ha.1 ha.2).1]

/-! Events: their points, the singular points, the strict order. -/

theorem s4a_evPt_mem_totalFibre (e : Event F) : evPt F e ∈ totalFibre F (evX F e) := by
  refine ⟨?_, rfl⟩
  rcases e with c | q
  · exact c.mem_Ico
  · exact (F.mem_crossingPairs'.1 q.2).1.1

theorem s4a_exists_event_of_singular {x₀ : ℝ} {p : Param F.c} (hp : p ∈ totalFibre F x₀)
    (hs : F.IsCusp p ∨ ∃ q, F.IsDouble p q) : ∃ e : Event F, evX F e = x₀ ∧ evZ F e = ht F p := by
  rcases hs with hc | ⟨q, hd⟩
  · exact ⟨Sum.inl ⟨p, F.mem_cuspSet.mpr ⟨hp.1, hc⟩⟩, hp.2, rfl⟩
  · have hmem := rep_pair_mem_doubleSet F hd
    have hrep : SameParam.rep p = p := by
      show (p.1, Int.fract p.2) = p
      rw [Int.fract_eq_self.mpr hp.1]
    have hq : F.eval (SameParam.rep q) = F.eval p := by
      rw [SmoothFront.eval_of_sameParam (SameParam.sameParam_rep q), hd.2]
    rcases F.mem_crossingPairs_or_swap hmem with h | h
    · refine ⟨Sum.inr ⟨_, h⟩, ?_, ?_⟩
      · show (F.eval (SameParam.rep p)).1 = x₀
        rw [hrep]; exact hp.2
      · show ht F (SameParam.rep p) = ht F p
        rw [hrep]
    · refine ⟨Sum.inr ⟨_, h⟩, ?_, ?_⟩
      · show (F.eval (SameParam.rep q)).1 = x₀
        rw [hq]; exact hp.2
      · show ht F (SameParam.rep q) = ht F p
        unfold ht; rw [hq]

/-- a fibre point over `x₀` at whose height no event of `x₀` sits is regular -/
theorem s4a_regular_of_no_event {x₀ : ℝ} {p : Param F.c} (hp : p ∈ totalFibre F x₀)
    (hno : ∀ e : Event F, evX F e = x₀ → evZ F e = ht F p → False) :
    ¬ F.IsCusp p ∧ ∀ q, ¬ F.IsDouble p q := by
  have key : ¬ (F.IsCusp p ∨ ∃ q, F.IsDouble p q) := fun hs => by
    obtain ⟨e, hex, hez⟩ := s4a_exists_event_of_singular F hp hs
    exact hno e hex hez
  exact ⟨fun hc => key (Or.inl hc), fun q hd => key (Or.inr ⟨q, hd⟩)⟩

theorem s4a_evKey_injective : Function.Injective (fun e : Event F => (evX F e, evZ F e)) := by
  intro e e' h
  have hev : F.eval (evPt F e) = F.eval (evPt F e') := h
  have h1 := (s4a_evPt_mem_totalFibre F e).1
  have h2 := (s4a_evPt_mem_totalFibre F e').1
  have hns : ∀ {a b : Param F.c}, a.2 ∈ Set.Ico (0:ℝ) 1 → b.2 ∈ Set.Ico (0:ℝ) 1 → a ≠ b → ¬ SameParam a b :=
    fun ha hb hne hs => hne (SameParam.eq_of_mem_Ico ha hb hs)
  rcases e with c | q <;> rcases e' with c' | q'
  · by_contra hne
    have hne' : c.1 ≠ c'.1 := fun h => hne (by rw [Subtype.ext h])
    exact F.cusp_alone c.1 c'.1 (hns h1 h2 hne') c.isCusp hev
  · exfalso
    have hd := (F.isOverUnder_of_mem_crossingPairs q'.2).isDouble
    by_cases hs : SameParam c.1 q'.1.1
    · exact F.not_isCusp_of_isDouble hd ((F.isCusp_iff_of_sameParam hs).mpr c.isCusp)
    · exact F.cusp_alone c.1 q'.1.1 hs c.isCusp hev
  · exfalso
    have hd := (F.isOverUnder_of_mem_crossingPairs q.2).isDouble
    by_cases hs : SameParam c'.1 q.1.1
    · exact F.not_isCusp_of_isDouble hd ((F.isCusp_iff_of_sameParam hs).mpr c'.isCusp)
    · exact F.cusp_alone c'.1 q.1.1 hs c'.isCusp hev.symm
  · obtain ⟨⟨ho, hu, hou, heq⟩, -⟩ := F.mem_crossingPairs'.1 q.2
    obtain ⟨⟨ho', hu', hou', heq'⟩, -⟩ := F.mem_crossingPairs'.1 q'.2
    by_cases hoo : q.1.1 = q'.1.1
    · have huu : q.1.2 = q'.1.2 := by
        by_contra hne
        exact F.no_triple q.1.1 q.1.2 q'.1.2 (hns ho hu hou) (hns hu hu' hne)
          (hns ho hu' (by rw [hoo]; exact hou')) heq (heq.symm.trans (hev.trans heq'))
      congr 1
      exact Subtype.ext (Prod.ext hoo huu)
    · have hh1 : q.1.2 = q'.1.1 := by
        by_contra hne
        exact F.no_triple q.1.1 q.1.2 q'.1.1 (hns ho hu hou) (hns hu ho' hne) (hns ho ho' hoo) heq
          (heq.symm.trans hev)
      have hh2 : q'.1.2 = q.1.1 := by
        by_contra hne
        exact F.no_triple q'.1.1 q'.1.2 q.1.1 (hns ho' hu' hou') (hns hu' ho hne) (hns ho' ho (Ne.symm hoo))
          heq' (heq'.symm.trans hev.symm)
      exfalso
      apply F.not_swap_mem_crossingPairs q.2
      have hsw : q.1.swap = q'.1 := Prod.ext hh1 hh2.symm
      rw [hsw]; exact q'.2

theorem s4a_events_pairwise_lt :
    (events F).Pairwise (fun e e' => toLex (evX F e, evZ F e) < toLex (evX F e', evZ F e')) := by
  have h := (events_pairwise_le F).and (events_nodup F)
  refine h.imp ?_
  intro e e' hh
  obtain ⟨hle, hne⟩ := hh
  unfold evLE at hle
  rw [decide_eq_true_eq] at hle
  refine lt_of_le_of_ne hle ?_
  intro heq
  exact hne (s4a_evKey_injective F (toLex.injective heq))

theorem s4a_eventAt_eq {k : ℕ} (hk : k < (events F).length) : eventAt F k = (events F)[k] := by
  unfold eventAt; exact List.getD_eq_getElem _ _ hk

/-- the keys of the columns are strictly increasing -/
theorem s4a_key_lt {k k' : ℕ} (hk : k < k') (hk' : k' < (events F).length) :
    toLex (colX F k, colZ F k) < toLex (colX F k', colZ F k') := by
  unfold colX colZ
  rw [s4a_eventAt_eq F (hk.trans hk'), s4a_eventAt_eq F hk']
  exact List.pairwise_iff_getElem.1 (s4a_events_pairwise_lt F) k k' (hk.trans hk') hk' hk

/-- no event has its key strictly between the keys of two consecutive columns -/
theorem s4a_no_event_between {k : ℕ} (hk : k + 1 < (events F).length) (e : Event F)
    (h1 : toLex (colX F k, colZ F k) < toLex (evX F e, evZ F e))
    (h2 : toLex (evX F e, evZ F e) < toLex (colX F (k + 1), colZ F (k + 1))) : False := by
  have he : (evX F e, evZ F e) = (colX F (evIdx F e), colZ F (evIdx F e)) := by
    unfold colX colZ; rw [eventAt_evIdx]
  rw [he] at h1 h2
  have hj := evIdx_lt_length F e
  rcases Nat.lt_or_ge (evIdx F e) (k + 1) with hlt | hge
  · rcases Nat.lt_or_ge (evIdx F e) k with hlt' | hge'
    · exact lt_asymm h1 (s4a_key_lt F hlt' (by omega))
    · have heq : evIdx F e = k := by omega
      rw [heq] at h1; exact lt_irrefl _ h1
  · rcases Nat.lt_or_ge (k + 1) (evIdx F e) with hlt' | hge'
    · exact lt_asymm h2 (s4a_key_lt F hlt' hj)
    · have heq : evIdx F e = k + 1 := by omega
      rw [heq] at h2; exact lt_irrefl _ h2

/-! The letter of an event and the points at the event's height. -/

theorem s4a_letterOf_inl_left (c : F.Cusp) (hl : F.IsLeftCusp c.1) :
    letterOf F (Sum.inl c) = Letter.l (posOf F (Sum.inl c)) (decide (0 < F.cuspDisc c.1)) := by
  show (if F.IsLeftCusp c.1 then Letter.l (posOf F (Sum.inl c)) (decide (0 < F.cuspDisc c.1))
    else Letter.r (posOf F (Sum.inl c))) = _
  exact ite_eq_left hl

theorem s4a_letterOf_inl_right (c : F.Cusp) (hl : ¬ F.IsLeftCusp c.1) :
    letterOf F (Sum.inl c) = Letter.r (posOf F (Sum.inl c)) := by
  show (if F.IsLeftCusp c.1 then Letter.l (posOf F (Sum.inl c)) (decide (0 < F.cuspDisc c.1))
    else Letter.r (posOf F (Sum.inl c))) = _
  exact ite_eq_right hl

theorem s4a_idx_letterOf (e : Event F) : (letterOf F e).idx = posOf F e := by
  rcases e with c | q
  · by_cases hl : F.IsLeftCusp c.1
    · rw [s4a_letterOf_inl_left F c hl]; rfl
    · rw [s4a_letterOf_inl_right F c hl]; rfl
  · rfl

theorem s4a_letterOf_inr (q : Cross F) : letterOf F (Sum.inr q) = Letter.σ (posOf F (Sum.inr q)) := rfl

/-- membership in the filter "height `= z₀`" of a list of the fibre points over `x₀` -/
theorem s4a_mem_filter_eq_iff (x₀ z₀ : ℝ) (L : List (Param F.c)) (hL : ∀ p, p ∈ L ↔ p ∈ totalFibre F x₀)
    (x : Param F.c) :
    x ∈ L.filter (fun p => decide (ht F p = z₀)) ↔ x.2 ∈ Set.Ico (0:ℝ) 1 ∧ F.eval x = (x₀, z₀) := by
  rw [List.mem_filter, hL, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h1, Prod.ext h2 h3⟩
  · rintro ⟨h1, h2⟩; exact ⟨⟨h1, congrArg Prod.fst h2⟩, congrArg Prod.snd h2⟩

/-- at a cusp event the only fibre point at the event's height is the cusp (`cusp_alone`) -/
theorem s4a_filter_eq_cusp (c : F.Cusp) (L : List (Param F.c)) (hnd : L.Nodup)
    (hL : ∀ p, p ∈ L ↔ p ∈ totalFibre F (evX F (Sum.inl c))) :
    L.filter (fun p => decide (ht F p = evZ F (Sum.inl c))) = [c.1] := by
  apply s4a_eq_singleton_of (hnd.filter _)
  intro x
  rw [s4a_mem_filter_eq_iff F _ _ L hL]
  constructor
  · rintro ⟨h1, h2⟩
    by_contra hne
    have hev : F.eval c.1 = F.eval x := by rw [h2]; rfl
    exact F.cusp_alone c.1 x (fun hs => hne (SameParam.eq_of_mem_Ico c.mem_Ico h1 hs).symm) c.isCusp hev
  · rintro rfl
    exact ⟨c.mem_Ico, rfl⟩

/-- at a crossing event the fibre points at the event's height are the two branches (`no_triple`) -/
theorem s4a_mem_filter_cross (q : Cross F) (L : List (Param F.c))
    (hL : ∀ p, p ∈ L ↔ p ∈ totalFibre F (evX F (Sum.inr q))) (x : Param F.c) :
    x ∈ L.filter (fun p => decide (ht F p = evZ F (Sum.inr q))) ↔ x = q.1.1 ∨ x = q.1.2 := by
  obtain ⟨⟨ho, hu, hou, heq⟩, -⟩ := F.mem_crossingPairs'.1 q.2
  rw [s4a_mem_filter_eq_iff F _ _ L hL]
  constructor
  · rintro ⟨h1, h2⟩
    have hev : F.eval q.1.1 = F.eval x := by rw [h2]; rfl
    by_contra hne
    obtain ⟨hne1, hne2⟩ := not_or.mp hne
    exact F.no_triple q.1.1 q.1.2 x (fun hs => hou (SameParam.eq_of_mem_Ico ho hu hs))
      (fun hs => hne2 (SameParam.eq_of_mem_Ico hu h1 hs).symm)
      (fun hs => hne1 (SameParam.eq_of_mem_Ico ho h1 hs).symm) heq (heq.symm.trans hev)
  · rintro (rfl | rfl)
    · exact ⟨ho, rfl⟩
    · exact ⟨hu, heq.symm⟩

theorem s4a_before_filter_cross (q : Cross F) :
    (fibreListBefore F (evX F (Sum.inr q))).filter (fun p => decide (ht F p = evZ F (Sum.inr q))) =
      [q.1.1, q.1.2] := by
  obtain ⟨⟨-, -, hou, heq⟩, hs⟩ := F.mem_crossingPairs'.1 q.2
  apply s4a_eq_pair_of ((fibreListBefore_nodup F _).filter _) ((fibreListBefore_pairwise F _).filter _) hou
    (s4a_mem_filter_cross F q _ (mem_fibreListBefore F _))
  unfold beforeLE
  rw [decide_eq_true_eq, Prod.Lex.toLex_le_toLex]
  have hz : ht F q.1.2 = ht F q.1.1 := by unfold ht; rw [heq]
  rintro (h | ⟨-, h⟩) <;> dsimp only at h
  · rw [hz] at h; exact lt_irrefl _ h
  · exact absurd hs (not_lt.mpr h)

theorem s4a_after_filter_cross (q : Cross F) :
    (fibreListAfter F (evX F (Sum.inr q))).filter (fun p => decide (ht F p = evZ F (Sum.inr q))) =
      [q.1.2, q.1.1] := by
  obtain ⟨⟨-, -, hou, heq⟩, hs⟩ := F.mem_crossingPairs'.1 q.2
  apply s4a_eq_pair_of ((fibreListAfter_nodup F _).filter _) ((fibreListAfter_pairwise F _).filter _) hou.symm
    (fun x => (s4a_mem_filter_cross F q _ (mem_fibreListAfter F _) x).trans or_comm)
  unfold afterLE
  rw [decide_eq_true_eq, Prod.Lex.toLex_le_toLex]
  have hz : ht F q.1.2 = ht F q.1.1 := by unfold ht; rw [heq]
  rintro (h | ⟨-, h⟩) <;> dsimp only at h
  · rw [hz] at h; exact lt_irrefl _ h
  · exact absurd hs (not_lt.mpr (by linarith))

/-- the local action of an event's letter on the bits of the points at its height -/
theorem s4a_core (e : Event F) :
    (((fibreListBefore F (evX F e)).filter (fun p => decide (ht F p = evZ F e))).flatMap
        (beforeBits F)).length = (letterOf F e).arity ∧
    (letterOf F e).act (((fibreListBefore F (evX F e)).filter (fun p => decide (ht F p = evZ F e))).flatMap
        (beforeBits F)) =
      some (((fibreListAfter F (evX F e)).filter (fun p => decide (ht F p = evZ F e))).flatMap (afterBits F)) := by
  rcases e with c | q
  · rw [s4a_filter_eq_cusp F c _ (fibreListBefore_nodup F _) (mem_fibreListBefore F _),
      s4a_filter_eq_cusp F c _ (fibreListAfter_nodup F _) (mem_fibreListAfter F _)]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    by_cases hl : F.IsLeftCusp c.1
    · have hnr : ¬ F.IsRightCusp c.1 := fun hr => lt_asymm hl.2 hr.2
      rw [s4a_letterOf_inl_left F c hl]
      have hb : beforeBits F c.1 = [] := by unfold beforeBits; rw [ite_eq_left hl]
      have ha : afterBits F c.1 = [decide (0 < F.cuspDisc c.1), !decide (0 < F.cuspDisc c.1)] := by
        unfold afterBits; rw [ite_eq_right hnr, ite_eq_left hl]
        by_cases hd : 0 < F.cuspDisc c.1 <;> simp [hd]
      rw [hb, ha]
      exact ⟨rfl, rfl⟩
    · have hr : F.IsRightCusp c.1 := (F.isLeftCusp_or_isRightCusp c.isCusp).resolve_left hl
      rw [s4a_letterOf_inl_right F c hl]
      have ha : afterBits F c.1 = [] := by unfold afterBits; rw [ite_eq_left hr]
      have hb : beforeBits F c.1 = if F.cuspDisc c.1 < 0 then [true, false] else [false, true] := by
        unfold beforeBits; rw [ite_eq_right hl, ite_eq_left hr]
      rw [hb, ha]
      split_ifs <;> exact ⟨rfl, rfl⟩
  · rw [s4a_before_filter_cross F q, s4a_after_filter_cross F q, s4a_letterOf_inr F q]
    have hd := (F.isOverUnder_of_mem_crossingPairs q.2).isDouble
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rw [s4a_beforeBits_of_regular F (F.not_isCusp_of_isDouble hd),
      s4a_beforeBits_of_regular F (F.not_isCusp_of_isDouble hd.symm),
      s4a_afterBits_of_regular F (F.not_isCusp_of_isDouble hd),
      s4a_afterBits_of_regular F (F.not_isCusp_of_isDouble hd.symm)]
    exact ⟨rfl, rfl⟩

/-! Splitting the hybrid cuts at a height. -/

/-- `filter (z₀ ≤ ht)` of the "before" list = `filter (z₀ < ht) ++ filter (ht = z₀)` -/
theorem s4a_before_split_le (x₀ z₀ : ℝ) :
    (fibreListBefore F x₀).filter (fun p => decide (z₀ ≤ ht F p)) =
      (fibreListBefore F x₀).filter (fun p => decide (z₀ < ht F p)) ++
        (fibreListBefore F x₀).filter (fun p => decide (ht F p = z₀)) := by
  rw [← s4a_filter_or_split (fibreListBefore_pairwise F x₀) (fun p => decide (z₀ < ht F p))
    (fun p => decide (ht F p = z₀)) ?_ ?_]
  · apply List.filter_congr
    intro p _
    rw [Bool.eq_iff_iff]
    simp only [Bool.or_eq_true, decide_eq_true_eq]
    exact le_iff_lt_or_eq.trans (or_congr_right eq_comm)
  · intro a ha
    rw [decide_eq_true_eq] at ha
    rw [decide_eq_false_iff_not]
    exact ne_of_gt ha
  · intro a b hab hQ
    have hle := s4a_ht_le_of_beforeLE F hab
    rw [decide_eq_true_eq] at hQ
    rw [decide_eq_false_iff_not, not_lt]
    linarith

/-- `filter (¬ z₀ < ht)` of the "after" list = `filter (ht = z₀) ++ filter (¬ z₀ ≤ ht)` -/
theorem s4a_after_split_not_lt (x₀ z₀ : ℝ) :
    (fibreListAfter F x₀).filter (fun p => !decide (z₀ < ht F p)) =
      (fibreListAfter F x₀).filter (fun p => decide (ht F p = z₀)) ++
        (fibreListAfter F x₀).filter (fun p => !decide (z₀ ≤ ht F p)) := by
  rw [← s4a_filter_or_split (fibreListAfter_pairwise F x₀) (fun p => decide (ht F p = z₀))
    (fun p => !decide (z₀ ≤ ht F p)) ?_ ?_]
  · apply List.filter_congr
    intro p _
    rw [Bool.eq_iff_iff]
    simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq, not_lt, not_le]
    exact le_iff_eq_or_lt
  · intro a ha
    rw [decide_eq_true_eq] at ha
    rw [Bool.not_eq_false', decide_eq_true_eq]
    exact le_of_eq ha.symm
  · intro a b hab hQ
    have hle := s4a_ht_le_of_afterLE F hab
    rw [Bool.not_eq_true', decide_eq_false_iff_not, not_le] at hQ
    rw [decide_eq_false_iff_not]
    intro h; linarith

/-- a list equals its `P`-part followed by its `¬P`-part when the `P`-part precedes (for a `Pairwise R` list) -/
theorem s4a_split_self {α : Type*} {R : α → α → Prop} {L : List α} (hL : L.Pairwise R) (P : α → Bool)
    (hord : ∀ a b, R a b → (!P a) = true → P b = false) :
    L = L.filter P ++ L.filter (fun a => !P a) := by
  rw [← s4a_filter_or_split hL P (fun a => !P a) (fun a ha => by rw [ha]; rfl) hord]
  symm
  rw [List.filter_eq_self]
  intro a _
  exact Bool.or_not_self _

end S4aHelpers

/-- LEAF (S4): distinct events have distinct points (`cusp_alone` for a cusp against anything, `no_triple` and
`not_swap_mem_crossingPairs` for two crossings). -/
theorem evKey_injective : Function.Injective (fun e : Event F => (evX F e, evZ F e)) :=
  s4a_evKey_injective F

/-- LEAF (S4): the events are strictly sorted by `(x, z)` (`events_pairwise_le`, `events_nodup`, `evKey_injective`). -/
theorem events_pairwise_lt :
    (events F).Pairwise (fun e e' => toLex (evX F e, evZ F e) < toLex (evX F e', evZ F e')) :=
  s4a_events_pairwise_lt F

/-- LEAF (S4): columns are ordered by x-value. -/
theorem colX_mono {k k' : ℕ} (hk : k < k') (hk' : k' < (events F).length) : colX F k ≤ colX F k' := by
  have h := s4a_key_lt F hk hk'
  rw [Prod.Lex.toLex_lt_toLex] at h
  rcases h with h | ⟨h, -⟩ <;> dsimp only at h
  · exact h.le
  · exact h.le

/-- LEAF (S4): the point of an event lies in the fibre over its x-value. -/
theorem evPt_mem_totalFibre (e : Event F) : evPt F e ∈ totalFibre F (evX F e) :=
  s4a_evPt_mem_totalFibre F e

/-- LEAF (S4): every singular fibre point is the point of an event at that x-value (a cusp is `Sum.inl` of its
representative; a double point lies in an over-first pair, `mem_crossingPairs_or_swap`). -/
theorem exists_event_of_singular {x₀ : ℝ} {p : Param F.c} (hp : p ∈ totalFibre F x₀)
    (hs : F.IsCusp p ∨ ∃ q, F.IsDouble p q) : ∃ e : Event F, evX F e = x₀ ∧ evZ F e = ht F p :=
  s4a_exists_event_of_singular F hp hs

/-- LEAF (S4, the local step): the letter of an event is typed at the hybrid cut before it and produces the
hybrid cut after it (`step_prefix` with the prefix of length `posOf e − 1`; the points at height `evZ e` are
exactly the event's point(s), over branch first in the "before" order and under branch first in the "after" order;
`act` on `beforeBits`/`afterBits` of the event: `l` pushes `[d, !d] = afterBits`, `r` removes `beforeBits`
(two distinct bits), `σ` swaps the two branches). -/
theorem step_hybrid (e : Event F) :
    (letterOf F e).step (hybridCut F (evX F e) (evZ F e)) = some (hybridCutStrict F (evX F e) (evZ F e)) := by
  have hidx : (letterOf F e).idx = posOf F e := s4a_idx_letterOf F e
  obtain ⟨hw, hcore⟩ := s4a_core F e
  unfold hybridCut hybridCutStrict hybridCutP
  rw [s4a_before_split_le F (evX F e) (evZ F e), s4a_after_split_not_lt F (evX F e) (evZ F e),
    List.flatMap_append, List.flatMap_append, List.append_assoc]
  refine (step_prefix ?_ ?_).trans ?_
  · rw [hidx]; exact Nat.le_add_left 1 _
  · rw [hidx]; unfold posOf; omega
  · rw [act_append hw, hcore]; rfl

/-- LEAF (S4): between two consecutive events of one x-value there are only regular strands (`before` = `after`
bits and orders), so the cut after the lower event is the cut before the upper one. -/
theorem hybridCutStrict_eq_hybridCut {k : ℕ} (hk : k + 1 < (events F).length) (hx : colX F k = colX F (k + 1)) :
    hybridCutStrict F (colX F k) (colZ F k) = hybridCut F (colX F (k + 1)) (colZ F (k + 1)) := by
  have hz : colZ F k < colZ F (k + 1) := by
    have h := s4a_key_lt F (Nat.lt_succ_self k) hk
    rw [Prod.Lex.toLex_lt_toLex] at h
    rcases h with h | ⟨-, h⟩ <;> dsimp only at h
    · exact absurd hx (ne_of_lt h)
    · exact h
  rw [← hx]
  set x₀ := colX F k with hx₀
  set z₁ := colZ F k with hz₁
  set z₂ := colZ F (k + 1) with hz₂
  have hreg : ∀ p ∈ totalFibre F x₀, (decide (z₁ < ht F p) && decide (ht F p < z₂)) = true →
      ¬ F.IsCusp p ∧ ∀ q, ¬ F.IsDouble p q := by
    intro p hp hmid
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hmid
    refine s4a_regular_of_no_event F hp (fun e hex hez => s4a_no_event_between F hk e ?_ ?_)
    · rw [hex, hez]; exact Prod.Lex.toLex_lt_toLex.2 (Or.inr ⟨rfl, hmid.1⟩)
    · rw [hex, hez, ← hx]; exact Prod.Lex.toLex_lt_toLex.2 (Or.inr ⟨rfl, hmid.2⟩)
  have hB : (fibreListBefore F x₀).filter (fun p => decide (z₁ < ht F p)) =
      (fibreListBefore F x₀).filter (fun p => decide (z₂ ≤ ht F p)) ++
        (fibreListBefore F x₀).filter (fun p => decide (z₁ < ht F p) && decide (ht F p < z₂)) := by
    rw [← s4a_filter_or_split (fibreListBefore_pairwise F x₀) (fun p => decide (z₂ ≤ ht F p))
      (fun p => decide (z₁ < ht F p) && decide (ht F p < z₂)) ?_ ?_]
    · apply List.filter_congr
      intro p _
      rw [Bool.eq_iff_iff]
      simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
      constructor
      · intro h
        by_cases h2 : z₂ ≤ ht F p
        · exact Or.inl h2
        · exact Or.inr ⟨h, not_le.mp h2⟩
      · rintro (h | ⟨h, -⟩)
        · linarith
        · exact h
    · intro a ha
      rw [decide_eq_true_eq] at ha
      rw [Bool.and_eq_false_iff, decide_eq_false_iff_not, decide_eq_false_iff_not]
      exact Or.inr (not_lt.mpr ha)
    · intro a b hab hQ
      have hle := s4a_ht_le_of_beforeLE F hab
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hQ
      rw [decide_eq_false_iff_not, not_le]
      linarith [hQ.2]
  have hA : (fibreListAfter F x₀).filter (fun p => !decide (z₂ ≤ ht F p)) =
      (fibreListAfter F x₀).filter (fun p => decide (z₁ < ht F p) && decide (ht F p < z₂)) ++
        (fibreListAfter F x₀).filter (fun p => !decide (z₁ < ht F p)) := by
    rw [← s4a_filter_or_split (fibreListAfter_pairwise F x₀)
      (fun p => decide (z₁ < ht F p) && decide (ht F p < z₂)) (fun p => !decide (z₁ < ht F p)) ?_ ?_]
    · apply List.filter_congr
      intro p _
      rw [Bool.eq_iff_iff]
      simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
        decide_eq_true_eq, not_lt, not_le]
      constructor
      · intro h
        by_cases h1 : z₁ < ht F p
        · exact Or.inl ⟨h1, h⟩
        · exact Or.inr (not_lt.mp h1)
      · rintro (⟨-, h⟩ | h)
        · exact h
        · linarith
    · intro a ha
      simp only [Bool.and_eq_true, decide_eq_true_eq] at ha
      rw [Bool.not_eq_false', decide_eq_true_eq]
      exact ha.1
    · intro a b hab hQ
      have hle := s4a_ht_le_of_afterLE F hab
      rw [Bool.not_eq_true', decide_eq_false_iff_not, not_lt] at hQ
      rw [Bool.and_eq_false_iff, decide_eq_false_iff_not, decide_eq_false_iff_not]
      exact Or.inl (not_lt.mpr (by linarith))
  unfold hybridCutStrict hybridCut hybridCutP
  rw [hB, hA, List.flatMap_append, List.flatMap_append, List.append_assoc,
    s4a_flatMap_before_eq_after F x₀ _ hreg]

/-- LEAF (S4): after the topmost event of an x-value the cut is `cutAfter`. -/
theorem hybridCutStrict_eq_cutAfter {k : ℕ} (hk : k < (events F).length)
    (htop : ∀ e : Event F, evX F e = colX F k → evZ F e ≤ colZ F k) :
    hybridCutStrict F (colX F k) (colZ F k) = cutAfter F (colX F k) := by
  set x₀ := colX F k with hx₀
  set z₀ := colZ F k with hz₀
  have hreg : ∀ p ∈ totalFibre F x₀, decide (z₀ < ht F p) = true →
      ¬ F.IsCusp p ∧ ∀ q, ¬ F.IsDouble p q := by
    intro p hp hz
    rw [decide_eq_true_eq] at hz
    refine s4a_regular_of_no_event F hp (fun e hex hez => ?_)
    have h := htop e hex
    rw [hez] at h
    exact absurd h (not_le.mpr hz)
  have hord : ∀ a b, afterLE F a b = true → (!decide (z₀ < ht F a)) = true →
      decide (z₀ < ht F b) = false := by
    intro a b hab hQ
    have hle := s4a_ht_le_of_afterLE F hab
    rw [Bool.not_eq_true', decide_eq_false_iff_not, not_lt] at hQ
    rw [decide_eq_false_iff_not, not_lt]
    linarith
  have hA := s4a_split_self (fibreListAfter_pairwise F x₀) (fun p => decide (z₀ < ht F p)) hord
  unfold hybridCutStrict hybridCutP cutAfter
  conv_rhs => rw [hA]
  rw [List.flatMap_append, s4a_flatMap_before_eq_after F x₀ _ hreg]

/-- LEAF (S4): before the lowest event of an x-value the cut is `cutBefore`. -/
theorem hybridCut_eq_cutBefore {k : ℕ} (hk : k < (events F).length)
    (hbot : ∀ e : Event F, evX F e = colX F k → colZ F k ≤ evZ F e) :
    hybridCut F (colX F k) (colZ F k) = cutBefore F (colX F k) := by
  set x₀ := colX F k with hx₀
  set z₀ := colZ F k with hz₀
  have hreg : ∀ p ∈ totalFibre F x₀, (!decide (z₀ ≤ ht F p)) = true →
      ¬ F.IsCusp p ∧ ∀ q, ¬ F.IsDouble p q := by
    intro p hp hz
    rw [Bool.not_eq_true', decide_eq_false_iff_not, not_le] at hz
    refine s4a_regular_of_no_event F hp (fun e hex hez => ?_)
    have h := hbot e hex
    rw [hez] at h
    exact absurd h (not_le.mpr hz)
  have hord : ∀ a b, beforeLE F a b = true → (!decide (z₀ ≤ ht F a)) = true →
      decide (z₀ ≤ ht F b) = false := by
    intro a b hab hQ
    have hle := s4a_ht_le_of_beforeLE F hab
    rw [Bool.not_eq_true', decide_eq_false_iff_not, not_le] at hQ
    rw [decide_eq_false_iff_not, not_le]
    linarith
  have hB := s4a_split_self (fibreListBefore_pairwise F x₀) (fun p => decide (z₀ ≤ ht F p)) hord
  unfold hybridCut hybridCutP cutBefore
  conv_rhs => rw [hB]
  rw [List.flatMap_append, s4a_flatMap_before_eq_after F x₀ _ hreg]

/-! ### S4b helpers -/
section S4bHelpers

/-! generic list lemmas: splitting a sorted list's filter, the filter of a sorted list is a prefix, singletons -/

theorem s4b_filter_split {α : Type*} {R : α → α → Prop} {P Q S : α → Bool} (hS : ∀ a, S a = (P a || Q a))
    (hPQ : ∀ a, P a = true → Q a = false) (hQP : ∀ a b, R a b → Q a = true → P b = true → False) :
    ∀ L : List α, L.Pairwise R → L.filter S = L.filter P ++ L.filter Q := by
  intro L hL
  induction L with
  | nil => rfl
  | cons a L ih =>
    rw [List.pairwise_cons] at hL
    have ih' := ih hL.2
    by_cases hPa : P a = true
    · have hQa := hPQ a hPa
      simp [hS, hPa, hQa, ih']
    · have hPa' : P a = false := by simpa using hPa
      by_cases hQa : Q a = true
      · have hnone : L.filter P = [] := by
          rw [List.filter_eq_nil_iff]
          intro b hb hPb
          exact hQP a b (hL.1 b hb) hQa hPb
        simp [hS, hPa', hQa, ih', hnone]
      · have hQa' : Q a = false := by simpa using hQa
        simp [hS, hPa', hQa', ih']

theorem s4b_filter_length_iff {α : Type*} {R : α → α → Prop} {P : α → Bool}
    (hdown : ∀ a b, R a b → P b = true → P a = true) :
    ∀ (L : List α), L.Pairwise R → ∀ j (hj : j < L.length), (j < (L.filter P).length ↔ P L[j] = true) := by
  intro L hL
  induction L with
  | nil => intro j hj; exact absurd hj (Nat.not_lt_zero _)
  | cons a L ih =>
    rw [List.pairwise_cons] at hL
    intro j hj
    by_cases hPa : P a = true
    · rw [List.filter_cons_of_pos hPa]
      cases j with
      | zero => simp [hPa]
      | succ j =>
        simp only [List.length_cons, Nat.add_lt_add_iff_right, List.getElem_cons_succ]
        exact ih hL.2 j (by simpa using hj)
    · have hnone : (a :: L).filter P = [] := by
        rw [List.filter_eq_nil_iff]
        intro b hb hPb
        rcases List.mem_cons.mp hb with rfl | hb
        · exact hPa hPb
        · exact hPa (hdown _ _ (hL.1 b hb) hPb)
      rw [hnone]
      simp only [List.length_nil, Nat.not_lt_zero, false_iff]
      intro hPj
      have hmem : (a :: L)[j] ∈ a :: L := List.getElem_mem hj
      rcases List.mem_cons.mp hmem with h | h
      · rw [h] at hPj; exact hPa hPj
      · exact hPa (hdown _ _ (hL.1 _ h) hPj)

theorem s4b_eq_singleton_of_nodup {α : Type*} {l : List α} {a : α} (hnd : l.Nodup) (ha : a ∈ l)
    (hall : ∀ b ∈ l, b = a) : l = [a] := by
  rcases l with _ | ⟨b, _ | ⟨c, l⟩⟩
  · simp at ha
  · rw [hall b (by simp)]
  · exfalso
    have hb := hall b (by simp)
    have hc := hall c (by simp)
    rw [List.nodup_cons] at hnd
    exact hnd.1 (by rw [hb, ← hc]; simp)

/-! events: columns, sortedness by index -/

theorem s4b_colX_def (k : ℕ) : evX F (eventAt F k) = colX F k := rfl
theorem s4b_colZ_def (k : ℕ) : evZ F (eventAt F k) = colZ F k := rfl

theorem s4b_eventAt_eq {k : ℕ} (hk : k < (events F).length) : eventAt F k = (events F)[k] :=
  List.getD_eq_getElem _ _ hk

theorem s4b_evX_eq_colX (e : Event F) : evX F e = colX F (evIdx F e) := by
  rw [colX, eventAt_evIdx]
theorem s4b_evZ_eq_colZ (e : Event F) : evZ F e = colZ F (evIdx F e) := by
  rw [colZ, eventAt_evIdx]

theorem s4b_events_length_pos : 0 < (events F).length :=
  List.length_pos_of_mem (mem_events F (Sum.inl (someCusp F)))

theorem s4b_lex_lt {k k' : ℕ} (hkk : k < k') (hk' : k' < (events F).length) :
    toLex (colX F k, colZ F k) < toLex (colX F k', colZ F k') := by
  have h := List.pairwise_iff_getElem.mp (events_pairwise_lt F) k k' (lt_trans hkk hk') hk' hkk
  rwa [colX, colZ, colX, colZ, s4b_eventAt_eq F (lt_trans hkk hk'), s4b_eventAt_eq F hk']

theorem s4b_colX_le {k k' : ℕ} (hkk : k ≤ k') (hk' : k' < (events F).length) : colX F k ≤ colX F k' := by
  rcases hkk.lt_or_eq with h | rfl
  · rcases Prod.Lex.lt_iff.mp (s4b_lex_lt F h hk') with h | ⟨h, -⟩
    · exact le_of_lt h
    · exact le_of_eq h
  · exact le_rfl

theorem s4b_colZ_lt {k k' : ℕ} (hkk : k < k') (hk' : k' < (events F).length) (hx : colX F k = colX F k') :
    colZ F k < colZ F k' := by
  rcases Prod.Lex.lt_iff.mp (s4b_lex_lt F hkk hk') with h | ⟨-, h⟩
  · exact absurd hx (ne_of_lt h)
  · exact h

/-! every event's x-value is singular; every singular x-value is an event's -/

theorem s4b_evX_mem_singX (e : Event F) : evX F e ∈ singX F := by
  cases e with
  | inl c => exact mem_singX_of_isCusp F c.isCusp
  | inr q => exact mem_singX_of_isDouble F (F.isOverUnder_of_mem_crossingPairs q.2).1

theorem s4b_exists_event_of_mem_singX {x : ℝ} (hx : x ∈ singX F) : ∃ e : Event F, evX F e = x := by
  unfold singX at hx
  rw [Finset.mem_union, Finset.mem_image, Finset.mem_image] at hx
  rcases hx with ⟨p, hp, rfl⟩ | ⟨q, hq, rfl⟩
  · exact ⟨Sum.inl ⟨p, hp⟩, rfl⟩
  · rcases F.mem_crossingPairs_or_swap hq with h | h
    · exact ⟨Sum.inr ⟨q, h⟩, rfl⟩
    · refine ⟨Sum.inr ⟨q.swap, h⟩, ?_⟩
      show (F.eval q.2).1 = (F.eval q.1).1
      rw [(F.isDouble_of_mem_doubleSet hq).eval_eq]

theorem s4b_notMem_singX_of_no_event {a b : ℝ} (h : ∀ e : Event F, ¬ (a < evX F e ∧ evX F e < b)) :
    ∀ x ∈ Set.Ioo a b, x ∉ singX F := by
  intro x hx hxs
  obtain ⟨e, he⟩ := s4b_exists_event_of_mem_singX F hxs
  exact h e (by rw [he]; exact hx)

theorem s4b_no_sing_between {k : ℕ} (hk : k + 1 < (events F).length) :
    ∀ x ∈ Set.Ioo (colX F k) (colX F (k + 1)), x ∉ singX F := by
  apply s4b_notMem_singX_of_no_event
  intro e ⟨h1, h2⟩
  rw [s4b_evX_eq_colX] at h1 h2
  have hj := evIdx_lt_length F e
  rcases Nat.lt_or_ge (evIdx F e) (k + 1) with h | h
  · exact absurd (s4b_colX_le F (Nat.lt_succ_iff.mp h) (by omega)) (not_le.mpr h1)
  · exact absurd (s4b_colX_le F h hj) (not_le.mpr h2)

/-! the "lowest / topmost event of its x-value" hypotheses of `hybridCut_eq_cutBefore` /
`hybridCutStrict_eq_cutAfter`, and the cut between consecutive columns -/

theorem s4b_hbot {k : ℕ} (hprev : ∀ j < k, colX F j ≠ colX F k) :
    ∀ e : Event F, evX F e = colX F k → colZ F k ≤ evZ F e := by
  intro e he
  rw [s4b_evX_eq_colX] at he
  rw [s4b_evZ_eq_colZ]
  rcases lt_trichotomy (evIdx F e) k with h | h | h
  · exact absurd he (hprev _ h)
  · rw [h]
  · exact le_of_lt (s4b_colZ_lt F h (evIdx_lt_length F e) he.symm)

theorem s4b_htop {k : ℕ} (hk : k < (events F).length)
    (hnext : ∀ j, k < j → j < (events F).length → colX F j ≠ colX F k) :
    ∀ e : Event F, evX F e = colX F k → evZ F e ≤ colZ F k := by
  intro e he
  rw [s4b_evX_eq_colX] at he
  rw [s4b_evZ_eq_colZ]
  rcases lt_trichotomy (evIdx F e) k with h | h | h
  · exact le_of_lt (s4b_colZ_lt F h hk he)
  · rw [h]
  · exact absurd he (hnext _ h (evIdx_lt_length F e))

theorem s4b_hybridCutStrict_eq_next {k : ℕ} (hk : k + 1 < (events F).length) :
    hybridCutStrict F (colX F k) (colZ F k) = hybridCut F (colX F (k + 1)) (colZ F (k + 1)) := by
  by_cases hx : colX F k = colX F (k + 1)
  · exact hybridCutStrict_eq_hybridCut F hk hx
  · have hlt : colX F k < colX F (k + 1) := lt_of_le_of_ne (s4b_colX_le F (Nat.le_succ k) hk) hx
    have hnext : ∀ j, k < j → j < (events F).length → colX F j ≠ colX F k := by
      intro j hj hjn heq
      have := s4b_colX_le F (Nat.succ_le_of_lt hj) hjn
      rw [heq] at this; exact absurd this (not_le.mpr hlt)
    have hprev : ∀ j < k + 1, colX F j ≠ colX F (k + 1) := by
      intro j hj heq
      have := s4b_colX_le F (Nat.lt_succ_iff.mp hj) (by omega)
      rw [heq] at this; exact absurd this (not_le.mpr hlt)
    rw [hybridCutStrict_eq_cutAfter F (by omega) (s4b_htop F (by omega) hnext),
      cutAfter_eq_cutBefore_of_gap F hlt (s4b_no_sing_between F hk),
      hybridCut_eq_cutBefore F hk (s4b_hbot F hprev)]

/-! compactness: the extreme x-values of the front are attained, at cusps (`x' = 0`), at left (min) / right (max)
cusps (`rightCusp_x_local` / `leftCusp_x_local` would otherwise continue beyond the extremum) -/

theorem s4b_eval_fract (i : Fin F.c) (t : ℝ) : F.eval (i, Int.fract t) = F.eval (i, t) :=
  SmoothFront.eval_of_sameParam (SameParam.sameParam_rep (i, t))

theorem s4b_exists_xmin :
    ∃ p : Param F.c, p.2 ∈ Set.Ico (0 : ℝ) 1 ∧ ∀ q : Param F.c, (F.eval p).1 ≤ (F.eval q).1 := by
  have hcont : ∀ i : Fin F.c, ContinuousOn (fun t => ((F.comp i).γ t).1) (Set.Icc 0 1) :=
    fun i => ((F.comp i).continuous.fst).continuousOn
  have hex : ∀ i : Fin F.c, ∃ t ∈ Set.Icc (0:ℝ) 1, IsMinOn (fun t => ((F.comp i).γ t).1) (Set.Icc 0 1) t :=
    fun i => isCompact_Icc.exists_isMinOn (Set.nonempty_Icc.mpr zero_le_one) (hcont i)
  choose t ht using hex
  obtain ⟨i₀, -, hi₀⟩ := Finset.exists_min_image Finset.univ (fun i => ((F.comp i).γ (t i)).1)
    ⟨⟨0, F.hc⟩, Finset.mem_univ _⟩
  refine ⟨(i₀, Int.fract (t i₀)), ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩, fun q => ?_⟩
  obtain ⟨i, s⟩ := q
  rw [s4b_eval_fract F i₀ (t i₀), ← s4b_eval_fract F i s]
  calc ((F.comp i₀).γ (t i₀)).1 ≤ ((F.comp i).γ (t i)).1 := hi₀ i (Finset.mem_univ _)
    _ ≤ ((F.comp i).γ (Int.fract s)).1 :=
        (isMinOn_iff.mp (ht i).2) _ ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩

theorem s4b_exists_xmax :
    ∃ p : Param F.c, p.2 ∈ Set.Ico (0 : ℝ) 1 ∧ ∀ q : Param F.c, (F.eval q).1 ≤ (F.eval p).1 := by
  have hcont : ∀ i : Fin F.c, ContinuousOn (fun t => ((F.comp i).γ t).1) (Set.Icc 0 1) :=
    fun i => ((F.comp i).continuous.fst).continuousOn
  have hex : ∀ i : Fin F.c, ∃ t ∈ Set.Icc (0:ℝ) 1, IsMaxOn (fun t => ((F.comp i).γ t).1) (Set.Icc 0 1) t :=
    fun i => isCompact_Icc.exists_isMaxOn (Set.nonempty_Icc.mpr zero_le_one) (hcont i)
  choose t ht using hex
  obtain ⟨i₀, -, hi₀⟩ := Finset.exists_max_image Finset.univ (fun i => ((F.comp i).γ (t i)).1)
    ⟨⟨0, F.hc⟩, Finset.mem_univ _⟩
  refine ⟨(i₀, Int.fract (t i₀)), ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩, fun q => ?_⟩
  obtain ⟨i, s⟩ := q
  rw [s4b_eval_fract F i₀ (t i₀), ← s4b_eval_fract F i s]
  calc ((F.comp i).γ (Int.fract s)).1 ≤ ((F.comp i).γ (t i)).1 :=
        (isMaxOn_iff.mp (ht i).2) _ ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩
    _ ≤ ((F.comp i₀).γ (t i₀)).1 := hi₀ i (Finset.mem_univ _)

theorem s4b_isCusp_of_min {i : Fin F.c} {t : ℝ} (hmin : ∀ q : Param F.c, (F.eval (i, t)).1 ≤ (F.eval q).1) :
    F.IsCusp (i, t) := by
  have hloc : IsLocalMin (fun s => ((F.comp i).γ s).1) t := Filter.Eventually.of_forall (fun s => hmin (i, s))
  exact (isCusp_iff_xvel_eq_zero F i t).mpr (hloc.hasDerivAt_eq_zero (hasDerivAt_x F i t))

theorem s4b_isCusp_of_max {i : Fin F.c} {t : ℝ} (hmax : ∀ q : Param F.c, (F.eval q).1 ≤ (F.eval (i, t)).1) :
    F.IsCusp (i, t) := by
  have hloc : IsLocalMax (fun s => ((F.comp i).γ s).1) t := Filter.Eventually.of_forall (fun s => hmax (i, s))
  exact (isCusp_iff_xvel_eq_zero F i t).mpr (hloc.hasDerivAt_eq_zero (hasDerivAt_x F i t))

theorem s4b_isLeftCusp_of_min {i : Fin F.c} {t : ℝ} (hmin : ∀ q : Param F.c, (F.eval (i, t)).1 ≤ (F.eval q).1) :
    F.IsLeftCusp (i, t) := by
  have hc := s4b_isCusp_of_min F hmin
  rcases F.isLeftCusp_or_isRightCusp hc with h | h
  · exact h
  · exfalso
    obtain ⟨δ, hδ, -, hmono, -⟩ := rightCusp_x_local F h
    have h1 : xOf F i (t - δ / 2) < xOf F i t :=
      hmono ⟨by linarith, by linarith⟩ ⟨by linarith, le_rfl⟩ (by linarith)
    exact absurd (hmin (i, t - δ / 2)) (not_le.mpr h1)

theorem s4b_isRightCusp_of_max {i : Fin F.c} {t : ℝ} (hmax : ∀ q : Param F.c, (F.eval q).1 ≤ (F.eval (i, t)).1) :
    F.IsRightCusp (i, t) := by
  have hc := s4b_isCusp_of_max F hmax
  rcases F.isLeftCusp_or_isRightCusp hc with h | h
  · exfalso
    obtain ⟨δ, hδ, -, -, hmono⟩ := leftCusp_x_local F h
    have h1 : xOf F i t < xOf F i (t + δ / 2) :=
      hmono ⟨le_rfl, by linarith⟩ ⟨by linarith, by linarith⟩ (by linarith)
    exact absurd (hmax (i, t + δ / 2)) (not_le.mpr h1)
  · exact h

/-! the letters of cusp events are cusp letters -/

theorem s4b_isCrossing_letterOf_inl (c : F.Cusp) : (letterOf F (Sum.inl c)).isCrossing = false := by
  dsimp only [letterOf]; split_ifs <;> rfl

theorem s4b_isCrossing_letterOf_inr (q : Cross F) : (letterOf F (Sum.inr q)).isCrossing = true := rfl

/-! the hybrid cut at a cusp event, split at the event: the strands strictly above, then `beforeBits c` -/

theorem s4b_ht_le_of_beforeLE {p q : Param F.c} (h : beforeLE F p q = true) : ht F q ≤ ht F p := by
  unfold beforeLE at h
  rw [decide_eq_true_iff] at h
  rcases Prod.Lex.le_iff.mp h with h | ⟨h, -⟩
  · exact le_of_lt (neg_lt_neg_iff.mp h)
  · exact le_of_eq (neg_inj.mp h).symm

theorem s4b_filter_le_split (x₀ z₀ : ℝ) :
    (fibreListBefore F x₀).filter (fun p => decide (z₀ ≤ ht F p)) =
      (fibreListBefore F x₀).filter (fun p => decide (z₀ < ht F p)) ++
        (fibreListBefore F x₀).filter (fun p => decide (ht F p = z₀)) := by
  apply s4b_filter_split (R := fun p q => beforeLE F p q = true)
  · intro p
    by_cases h : z₀ ≤ ht F p
    · rcases lt_or_eq_of_le h with h' | h'
      · simp [h, h', ne_of_gt h']
      · simp [h'.symm]
    · have h1 : ¬ z₀ < ht F p := fun h' => h h'.le
      have h2 : ht F p ≠ z₀ := fun h' => h h'.ge
      simp [h, h1, h2]
  · intro p hp
    rw [decide_eq_true_iff] at hp
    exact decide_eq_false (ne_of_gt hp)
  · intro p q hpq hQ hP
    rw [decide_eq_true_iff] at hQ hP
    have := s4b_ht_le_of_beforeLE F hpq
    linarith
  · exact fibreListBefore_pairwise F x₀

theorem s4b_filter_eq_cusp (c : F.Cusp) :
    (fibreListBefore F (evX F (Sum.inl c))).filter (fun p => decide (ht F p = evZ F (Sum.inl c))) = [c.1] := by
  apply s4b_eq_singleton_of_nodup ((fibreListBefore_nodup F _).filter _)
  · rw [List.mem_filter, mem_fibreListBefore]
    exact ⟨⟨c.mem_Ico, rfl⟩, by simp [evZ, evPt]⟩
  · intro p hp
    rw [List.mem_filter, mem_fibreListBefore, decide_eq_true_iff] at hp
    obtain ⟨⟨hp1, hp2⟩, hz⟩ := hp
    have he : F.eval c.1 = F.eval p := Prod.ext hp2.symm hz.symm
    by_contra hne
    have hsp : ¬ SameParam c.1 p := fun hs => hne (SameParam.eq_of_mem_Ico c.mem_Ico hp1 hs).symm
    exact F.cusp_alone c.1 p hsp c.isCusp he

theorem s4b_hybridCut_drop_cusp (c : F.Cusp) :
    ∃ R : Cuts, (hybridCut F (evX F (Sum.inl c)) (evZ F (Sum.inl c))).drop (posOf F (Sum.inl c) - 1) =
      beforeBits F c.1 ++ R := by
  refine ⟨((fibreListAfter F (evX F (Sum.inl c))).filter
    (fun p => !decide (evZ F (Sum.inl c) ≤ ht F p))).flatMap (afterBits F), ?_⟩
  rw [hybridCut, hybridCutP, s4b_filter_le_split, s4b_filter_eq_cusp, List.flatMap_append, List.flatMap_singleton,
    List.append_assoc, posOf, Nat.add_sub_cancel, List.drop_left]

/-! the down count along the run: one contribution per event -/

/-- the down-bit contribution of an event, read at the hybrid cut before it -/
def s4b_dcont (e : Event F) : ℕ := (letterOf F e).downBit (hybridCut F (evX F e) (evZ F e))

theorem s4b_downCountFrom_cons_of_step {a : Letter} {W : Word} {c c' : Cuts} (h : a.step c = some c') :
    Word.downCountFrom (a :: W) c = a.downBit c + Word.downCountFrom W c' := by
  simp only [Word.downCountFrom, h]

theorem s4b_downCountFrom_drop : ∀ m k : ℕ, k + m = (events F).length →
    Word.downCountFrom ((word F).drop k) (hybridCut F (colX F k) (colZ F k)) =
      (((events F).drop k).map (s4b_dcont F)).sum := by
  intro m
  induction m with
  | zero =>
    intro k hk
    rw [Nat.add_zero] at hk
    rw [List.drop_of_length_le (by rw [length_word]; omega), List.drop_of_length_le (by omega)]
    rfl
  | succ m ih =>
    intro k hk
    have hkn : k < (events F).length := by omega
    have hkw : k < (word F).length := by rw [length_word]; exact hkn
    have hs := step_hybrid F (eventAt F k)
    rw [s4b_colX_def, s4b_colZ_def] at hs
    rw [List.drop_eq_getElem_cons hkw, ← letterAt_eq _ hkw, letterAt_word F hkn,
      s4b_downCountFrom_cons_of_step hs, List.drop_eq_getElem_cons hkn, ← s4b_eventAt_eq F hkn, List.map_cons,
      List.sum_cons]
    congr 1
    rcases Nat.lt_or_ge (k + 1) (events F).length with h | h
    · rw [s4b_hybridCutStrict_eq_next F h]; exact ih (k + 1) (by omega)
    · have h1 : (word F).drop (k + 1) = [] := List.drop_of_length_le (by rw [length_word]; omega)
      have h2 : (events F).drop (k + 1) = [] := List.drop_of_length_le h
      rw [h1, h2]; rfl

theorem s4b_dcont_inr (q : Cross F) : s4b_dcont F (Sum.inr q) = 0 := rfl

theorem s4b_dcont_inl (c : F.Cusp) : s4b_dcont F (Sum.inl c) = if F.cuspDisc c.1 < 0 then 1 else 0 := by
  obtain ⟨R, hR⟩ := s4b_hybridCut_drop_cusp F c
  have hne := F.cuspDisc_ne_zero_of_isCusp c.isCusp
  unfold s4b_dcont
  by_cases hL : F.IsLeftCusp c.1
  · simp only [letterOf, ite_eq_left hL, Letter.downBit]
    rcases lt_or_gt_of_ne hne with h | h
    · simp [h, not_lt.mpr h.le]
    · simp [h, h.le]
  · have hR' : F.IsRightCusp c.1 := (F.isLeftCusp_or_isRightCusp c.isCusp).resolve_left hL
    simp only [letterOf, ite_eq_right hL, Letter.downBit]
    rw [hR, beforeBits, ite_eq_right hL, ite_eq_left hR']
    rcases lt_or_gt_of_ne hne with h | h
    · simp [h]
    · simp [not_lt.mpr h.le]

theorem s4b_sum_univ_toList (f : Event F → ℕ) : ((Finset.univ : Finset (Event F)).toList.map f).sum = ∑ e, f e := by
  rw [Finset.sum_eq_multiset_sum, ← Multiset.sum_coe, ← Multiset.map_coe, Finset.coe_toList]

theorem s4b_sum_cusp (g : Param F.c → ℕ) : ∑ c : F.Cusp, g c.1 = ∑ p ∈ F.cuspSet, g p :=
  Finset.sum_coe_sort F.cuspSet g

theorem s4b_sum_dcont : ((events F).map (s4b_dcont F)).sum = F.downCount := by
  rw [events, List.Perm.sum_eq ((List.mergeSort_perm _ _).map _), s4b_sum_univ_toList, Fintype.sum_sum_type]
  simp only [s4b_dcont_inr, s4b_dcont_inl, Finset.sum_const_zero, add_zero]
  rw [s4b_sum_cusp F (fun p => if F.cuspDisc p < 0 then 1 else 0), SmoothFront.downCount, Finset.card_filter]
  refine Finset.sum_congr rfl (fun p hp => ?_)
  have hc := F.isCusp_of_mem_cuspSet hp
  by_cases h : F.cuspDisc p < 0 <;> simp [h, SmoothFront.IsDownCusp, hc]

end S4bHelpers

/-- LEAF (S4): nothing lies left of the first event: the minimum of `x` on the compact front is a cusp (`x' = 0`
there, `no_vertical`), a left cusp, and every fibre point over that x-value is a left cusp (a regular point or a
right cusp would continue to smaller `x`). -/
theorem cutBefore_first : cutBefore F (colX F 0) = [] :=
by
  obtain ⟨⟨i, t⟩, hp, hmin⟩ := s4b_exists_xmin F
  have hcusp := s4b_isCusp_of_min F hmin
  let c : F.Cusp := ⟨(i, t), F.mem_cuspSet.mpr ⟨hp, hcusp⟩⟩
  have hx : colX F 0 = (F.eval (i, t)).1 := by
    apply le_antisymm
    · have := s4b_colX_le F (Nat.zero_le (evIdx F (Sum.inl c))) (evIdx_lt_length F _)
      rwa [← s4b_evX_eq_colX] at this
    · exact hmin _
  rw [hx, cutBefore, List.flatMap_eq_nil_iff]
  intro q hq
  rw [mem_fibreListBefore] at hq
  obtain ⟨j, s⟩ := q
  have hminq : ∀ r : Param F.c, (F.eval (j, s)).1 ≤ (F.eval r).1 := fun r => by
    rw [hq.2]; exact hmin r
  rw [beforeBits, ite_eq_left (s4b_isLeftCusp_of_min F hminq)]

/-- LEAF (S4): nothing lies right of the last event. -/
theorem cutAfter_last : cutAfter F (colX F ((events F).length - 1)) = [] :=
by
  obtain ⟨⟨i, t⟩, hp, hmax⟩ := s4b_exists_xmax F
  have hcusp := s4b_isCusp_of_max F hmax
  let c : F.Cusp := ⟨(i, t), F.mem_cuspSet.mpr ⟨hp, hcusp⟩⟩
  have hn := s4b_events_length_pos F
  have hx : colX F ((events F).length - 1) = (F.eval (i, t)).1 := by
    apply le_antisymm
    · exact hmax _
    · have hj := evIdx_lt_length F (Sum.inl c)
      have := s4b_colX_le F (Nat.le_sub_one_of_lt hj) (by omega)
      rwa [← s4b_evX_eq_colX] at this
  rw [hx, cutAfter, List.flatMap_eq_nil_iff]
  intro q hq
  rw [mem_fibreListAfter] at hq
  obtain ⟨j, s⟩ := q
  have hmaxq : ∀ r : Param F.c, (F.eval r).1 ≤ (F.eval (j, s)).1 := fun r => by
    rw [hq.2]; exact hmax r
  rw [afterBits, ite_eq_left (s4b_isRightCusp_of_max F hmaxq)]

/-- LEAF (S4, THE INVARIANT): the run of the word up to column `k` is the hybrid cut before the event of column
`k` (induction on `k`: `cutBefore_first`, `step_hybrid`, then `hybridCutStrict_eq_hybridCut` at a tie or
`hybridCutStrict_eq_cutAfter`, `cutAfter_eq_cutBefore_of_gap`, `hybridCut_eq_cutBefore` at a new x-value). -/
theorem run_take_eq_hybrid {k : ℕ} (hk : k < (events F).length) :
    Word.run ((word F).take k) [] = some (hybridCut F (colX F k) (colZ F k)) :=
by
  induction k with
  | zero =>
    rw [List.take_zero, Word.run_nil,
      hybridCut_eq_cutBefore F hk (s4b_hbot F (fun j hj => absurd hj (Nat.not_lt_zero _))), cutBefore_first]
  | succ k ih =>
    have hk' : k < (events F).length := Nat.lt_of_succ_lt hk
    have hkw : k < (word F).length := by rw [length_word]; exact hk'
    have hs := step_hybrid F (eventAt F k)
    rw [s4b_colX_def, s4b_colZ_def] at hs
    rw [List.take_succ_eq_append_getElem hkw, Word.run_append, ih hk', Option.bind_some, Word.run_singleton,
      ← letterAt_eq _ hkw, letterAt_word F hk', hs, s4b_hybridCutStrict_eq_next F hk]

/-! MERGER (W3S_Merged, 2026-09-14): `word_closed`, `oword`, `oword_letters` (skeleton L14849-14857, section SweepDefs) are declared here, after `run_take_eq_hybrid`, because the proof of `word_closed` needs it (S4b). Text verbatim; same `F`. -/

/-! #### S4 leaves: the word is closed; its counts -/

/-- LEAF (S4): the word of the sweep is closed. -/
theorem word_closed : (word F).Closed :=
by
  have hn := s4b_events_length_pos F
  have hkw : (events F).length - 1 < (word F).length := by rw [length_word]; omega
  have hW : (word F).take ((events F).length - 1) ++ [(word F)[(events F).length - 1]] = word F := by
    rw [← List.take_succ_eq_append_getElem hkw, Nat.sub_add_cancel hn, ← length_word, List.take_length]
  have hs := step_hybrid F (eventAt F ((events F).length - 1))
  rw [s4b_colX_def, s4b_colZ_def] at hs
  unfold Word.Closed
  rw [← hW, Word.run_append, run_take_eq_hybrid F (by omega), Option.bind_some, Word.run_singleton,
    ← letterAt_eq _ hkw, letterAt_word F (by omega), hs,
    hybridCutStrict_eq_cutAfter F (by omega) (s4b_htop F (by omega) (fun j hj hjn => absurd hjn (by omega))),
    cutAfter_last]

/-- the closed word of the sweep -/
def oword : OWord := ⟨word F, word_closed F⟩

@[simp] theorem oword_letters : (oword F).letters = word F := rfl

/-- LEAF (S4): the word is nonempty (every circle has a cusp, `exists_two_cusps`). -/
theorem word_ne_nil : (oword F).letters ≠ [] :=
by
  rw [oword_letters, word, Ne, List.map_eq_nil_iff]
  exact List.ne_nil_of_mem (mem_events F (Sum.inl (someCusp F)))

/-- LEAF (S4): one cusp letter per cusp (`List.countP_map`, `Fintype.card` of the `Sum`, `card_cusp`). -/
theorem cuspCount_eq : (word F).cuspCount = F.cuspSet.card :=
by
  rw [Word.cuspCount, word, List.countP_map, events, List.Perm.countP_eq _ (List.mergeSort_perm _ _),
    List.countP_eq_length_filter]
  have hperm : ((Finset.univ : Finset (Event F)).toList.filter ((fun ℓ : Letter => !ℓ.isCrossing) ∘ letterOf F)).Perm
      ((Finset.univ : Finset F.Cusp).toList.map Sum.inl) := by
    rw [List.perm_ext_iff_of_nodup ((Finset.nodup_toList _).filter _)
      ((Finset.nodup_toList _).map Sum.inl_injective)]
    intro e
    rw [List.mem_filter, List.mem_map]
    cases e with
    | inl c => simp [Function.comp, s4b_isCrossing_letterOf_inl]
    | inr q => simp [Function.comp, s4b_isCrossing_letterOf_inr]
  rw [hperm.length_eq, List.length_map, Finset.length_toList, Finset.card_univ, F.card_cusp]

/-- LEAF (S4): the letter-traced down count is `D(F)`: at a left cusp `downBit (l m d) = 1 ↔ d = false ↔ cuspDisc < 0`;
at a right cusp the bit at position `m` of the hybrid cut (`run_take_eq_hybrid`, `step_hybrid`) is the upper
`beforeBit`, `true ↔ cuspDisc < 0`; crossings contribute `0` (`downCountFrom` unfolded along the run). -/
theorem downCountSyn_eq : (oword F).downCountSyn = F.downCount :=
by
  rw [OWord.downCountSyn, oword_letters, ← s4b_sum_dcont]
  have := s4b_downCountFrom_drop F (events F).length 0 (Nat.zero_add _)
  rw [List.drop_zero, List.drop_zero] at this
  rw [← this, hybridCut_eq_cutBefore F (s4b_events_length_pos F)
    (s4b_hbot F (fun j hj => absurd hj (Nat.not_lt_zero _))), cutBefore_first]

/-- LEAF (S4/S6): for a non-singular `x` the cut of the word at the column of `x` is `cutBefore x`
(`run_take_eq_hybrid`, `hybridCut_eq_cutBefore` / `hybridCutStrict_eq_cutAfter`, `cutAfter_eq_cutBefore_of_gap`;
`[]` on both sides beyond the front). -/
theorem cut_word_colAt {x : ℝ} (hx : x ∉ singX F) : cut (word F) (colAt F x) = cutBefore F x :=
by
  have hn := s4b_events_length_pos F
  have hdown : ∀ a b : Event F, toLex (evX F a, evZ F a) < toLex (evX F b, evZ F b) →
      decide (evX F b < x) = true → decide (evX F a < x) = true := by
    intro a b hab hb
    rw [decide_eq_true_iff] at hb ⊢
    rcases Prod.Lex.lt_iff.mp hab with h | ⟨h, -⟩
    · exact lt_trans h hb
    · rw [show evX F a = evX F b from h]; exact hb
  have hiff := s4b_filter_length_iff hdown (events F) (events_pairwise_lt F)
  have hiff' : ∀ j (hj : j < (events F).length), (j < colAt F x ↔ colX F j < x) := by
    intro j hj
    rw [colAt, hiff j hj, decide_eq_true_iff, colX, s4b_eventAt_eq F hj]
  have hle : colAt F x ≤ (events F).length := List.length_filter_le _ _
  rcases hle.lt_or_eq with hlt | heq
  · have hxk : x < colX F (colAt F x) := by
      have h1 : ¬ colX F (colAt F x) < x := fun h => lt_irrefl _ ((hiff' _ hlt).mpr h)
      rcases lt_or_eq_of_le (not_lt.mp h1) with h | h
      · exact h
      · have := s4b_evX_mem_singX F (eventAt F (colAt F x))
        rw [s4b_colX_def, ← h] at this
        exact absurd this hx
    have hprev : ∀ j < colAt F x, colX F j ≠ colX F (colAt F x) := by
      intro j hj heq
      have := (hiff' j (lt_trans hj hlt)).mp hj
      rw [heq] at this; exact absurd this (not_lt.mpr hxk.le)
    have hgap : ∀ y ∈ Set.Ioo x (colX F (colAt F x)), y ∉ singX F := by
      apply s4b_notMem_singX_of_no_event
      intro e ⟨h1, h2⟩
      rw [s4b_evX_eq_colX] at h1 h2
      rcases Nat.lt_or_ge (evIdx F e) (colAt F x) with h | h
      · exact absurd ((hiff' _ (evIdx_lt_length F e)).mp h) (not_lt.mpr h1.le)
      · exact absurd (s4b_colX_le F h (evIdx_lt_length F e)) (not_le.mpr h2)
    rw [cut, run_take_eq_hybrid F hlt, Option.getD_some, hybridCut_eq_cutBefore F hlt (s4b_hbot F hprev),
      ← cutAfter_eq_cutBefore_of_gap F hxk hgap, cutAfter_eq_cutBefore F hx]
  · have hlast : colX F ((events F).length - 1) < x := (hiff' _ (by omega)).mp (by omega)
    have hgap : ∀ y ∈ Set.Ioo (colX F ((events F).length - 1)) x, y ∉ singX F := by
      apply s4b_notMem_singX_of_no_event
      intro e ⟨h1, h2⟩
      rw [s4b_evX_eq_colX] at h1
      exact absurd (s4b_colX_le F (Nat.le_sub_one_of_lt (evIdx_lt_length F e)) (by omega)) (not_le.mpr h1)
    rw [heq, ← length_word, cut_length _ (word_closed F), ← cutAfter_eq_cutBefore_of_gap F hlast hgap, cutAfter_last]

end SweepLeaves

/-! #### S5. The slot map `Φ` and the local record clauses -/

section SlotMap

variable (F : SmoothFront)

theorem frontOver_partner_eq_true_of {p : F.Occ} (h : ¬ frontOver F p = true) : frontOver F (partner F p) = true := by
  rw [frontOver_partner]; simpa using h

/-- the crossing (over-first pair) of an occurrence -/
def crossOf (p : F.Occ) : Cross F :=
  if h : frontOver F p = true then ⟨(p.1, (partner F p).1), over_pair_mem_crossingPairs F p h⟩
  else ⟨((partner F p).1, p.1), by
    have := over_pair_mem_crossingPairs F (partner F p) (frontOver_partner_eq_true_of F h)
    rwa [partner_partner] at this⟩

/-- THE SLOT OF AN OCCURRENCE: the descending strand `σSlotA` of its crossing's column if it is the over branch
(smaller slope: above before, below after), the ascending strand `σSlotB` otherwise. -/
def ΦFun (p : F.Occ) : Slot (word F) :=
  if frontOver F p = true then
    σSlotA (word_closed F) (evIdx_lt_length_word F (Sum.inr (crossOf F p))) (letterAt_word_cross F (crossOf F p))
  else σSlotB (word_closed F) (evIdx_lt_length_word F (Sum.inr (crossOf F p))) (letterAt_word_cross F (crossOf F p))

theorem isσSlot_ΦFun (p : F.Occ) : U2.IsσSlot (ΦFun F p) := by
  unfold ΦFun
  split_ifs
  · exact U2.isσSlot_σSlotA (word_closed F) _ _
  · exact U2.isσSlot_σSlotB (word_closed F) _ _

/-- the slot map into the `σ` slots -/
def ΦSub (p : F.Occ) : {u : Slot (word F) // U2.IsσSlot u} := ⟨ΦFun F p, isσSlot_ΦFun F p⟩

/-- LEAF (S5): `Φ` is a bijection onto the `σ` slots (injective: the column determines the crossing and the bit
the branch; surjective: `U2.isσSlot_iff` — every `σ` slot is `σSlotA`/`σSlotB` of a crossing column, whose event is
`Sum.inr q`, the image of `q`'s over/under branch). -/
theorem ΦSub_bijective : Function.Bijective (ΦSub F) := by
  have hcol : ∀ r, colOf (ΦFun F r) = evIdx F (Sum.inr (crossOf F r)) := by
    intro r; unfold ΦFun; split_ifs
    · exact (σSlotA_spec _ _ _).1
    · exact (σSlotB_spec _ _ _).1
  have hdesc : ∀ r, U2.isDesc (ΦFun F r) = frontOver F r := by
    intro r; unfold ΦFun; split_ifs with h
    · rw [U2.isDesc_σSlotA, h]
    · rw [U2.isDesc_σSlotB, Bool.eq_false_iff.mpr h]
  have hval : ∀ r, (crossOf F r).1 =
      if frontOver F r = true then (r.1, (partner F r).1) else ((partner F r).1, r.1) := by
    intro r; unfold crossOf; split_ifs <;> rfl
  constructor
  · intro p p' h
    have h1 : ΦFun F p = ΦFun F p' := congrArg Subtype.val h
    have h2 : crossOf F p = crossOf F p' := by
      apply Sum.inr_injective
      apply s3s5_evIdx_injective F
      rw [← hcol, ← hcol, h1]
    have h3 : frontOver F p = frontOver F p' := by rw [← hdesc, ← hdesc, h1]
    apply Subtype.ext
    have h4 := congrArg Subtype.val h2
    rw [hval, hval, h3] at h4
    split_ifs at h4
    · exact (Prod.mk.inj h4).1
    · exact (Prod.mk.inj h4).2
  · rintro ⟨u, hu⟩
    obtain ⟨k, m, hk, hℓ, hu'⟩ := (U2.isσSlot_iff (word_closed F) u).mp hu
    have hk' : k < (events F).length := by rwa [length_word] at hk
    obtain ⟨q, hq⟩ := s3s5_eventAt_eq_inr F hk' hℓ
    have hidx : evIdx F (Sum.inr q) = k := by rw [← hq]; exact evIdx_eventAt F hk'
    set po : F.Occ := ⟨q.1.1, fst_mem_occSet_of_mem_crossingPairs F q.2⟩ with hpo
    have hover : frontOver F po = true := frontOver_of_mem_crossingPairs F q.2
    have hpv : (partner F po).1 = q.1.2 := partner_val_of_mem_crossingPairs F q.2
    have hcross : crossOf F po = q := by
      apply Subtype.ext
      rw [hval, ite_eq_left hover, hpv]
    have hcross' : crossOf F (partner F po) = q := by
      apply Subtype.ext
      rw [hval, ite_eq_right (by rw [frontOver_partner, hover]; simp), partner_partner, hpv]
    rcases hu' with rfl | rfl
    · refine ⟨po, Subtype.ext ?_⟩
      show ΦFun F po = σSlotA (word_closed F) hk hℓ
      apply U2.σslot_ext (word_closed F) (isσSlot_ΦFun F _) (U2.isσSlot_σSlotA _ hk hℓ)
      · rw [hcol, hcross, hidx, (σSlotA_spec _ hk hℓ).1]
      · rw [hdesc, hover, U2.isDesc_σSlotA]
    · refine ⟨partner F po, Subtype.ext ?_⟩
      show ΦFun F (partner F po) = σSlotB (word_closed F) hk hℓ
      apply U2.σslot_ext (word_closed F) (isσSlot_ΦFun F _) (U2.isσSlot_σSlotB _ hk hℓ)
      · rw [hcol, hcross', hidx, (σSlotB_spec _ hk hℓ).1]
      · rw [hdesc, frontOver_partner, hover, U2.isDesc_σSlotB]; rfl

/-- the occurrence bijection of the record isomorphism -/
def occEquiv : F.Occ ≃ {u : Slot (word F) // U2.IsσSlot u} := Equiv.ofBijective _ (ΦSub_bijective F)

/-- LEAF (S5): the partner goes to the twin slot (`crossOf (partner p) = crossOf p`, `frontOver_partner`,
`U2.σtwin_σSlotA/B`). -/
theorem ΦFun_partner (p : F.Occ) : ΦFun F (partner F p) = U2.σtwin (word_closed F) (ΦFun F p) := by
  have hcol : ∀ r, colOf (ΦFun F r) = evIdx F (Sum.inr (crossOf F r)) := by
    intro r; unfold ΦFun; split_ifs
    · exact (σSlotA_spec _ _ _).1
    · exact (σSlotB_spec _ _ _).1
  have hdesc : ∀ r, U2.isDesc (ΦFun F r) = frontOver F r := by
    intro r; unfold ΦFun; split_ifs with h
    · rw [U2.isDesc_σSlotA, h]
    · rw [U2.isDesc_σSlotB, Bool.eq_false_iff.mpr h]
  have hc : crossOf F (partner F p) = crossOf F p := by
    unfold crossOf
    by_cases h : frontOver F p = true
    · have h' : ¬ frontOver F (partner F p) = true := by rw [frontOver_partner, h]; simp
      rw [dite_eq_right h', dite_eq_left h]
      apply Subtype.ext
      show ((partner F (partner F p)).1, (partner F p).1) = (p.1, (partner F p).1)
      rw [partner_partner]
    · have h' : frontOver F (partner F p) = true := frontOver_partner_eq_true_of F h
      rw [dite_eq_left h', dite_eq_right h]
      apply Subtype.ext
      show ((partner F p).1, (partner F (partner F p)).1) = ((partner F p).1, p.1)
      rw [partner_partner]
  apply U2.σslot_ext (word_closed F) (isσSlot_ΦFun F _) (U2.isσSlot_σtwin _ (isσSlot_ΦFun F p))
  · rw [U2.colOf_σtwin _ (isσSlot_ΦFun F p), hcol, hcol, hc]
  · rw [U2.isDesc_σtwin _ (isσSlot_ΦFun F p), hdesc, hdesc, frontOver_partner]

/-- LEAF (S5): over = descending (`U2.isDesc_σSlotA/B`). -/
theorem isDesc_ΦFun (p : F.Occ) : U2.isDesc (ΦFun F p) = frontOver F p := by
  unfold ΦFun
  split_ifs with h
  · rw [U2.isDesc_σSlotA, h]
  · rw [U2.isDesc_σSlotB, Bool.eq_false_iff.mpr h]

/-- LEAF (S5): the signs agree: `σsgn` is `+1` iff the two bits of the column agree (`U2.coe_σsgnCol`); by
`run_take_eq_hybrid`/`step_hybrid` those bits are the direction bits of the over and under branches, and
`frontSgn = +1` iff their x-velocities have the same sign (`crossSign_eq_one_iff_of_isOverUnder`,
`crossSign_eq_sign`). -/
theorem σsgn_ΦFun (p : F.Occ) : U2.σsgn (ΦFun F p) = frontSgn F p := by
  have hk : evIdx F (Sum.inr (crossOf F p)) < (events F).length := evIdx_lt_length F _
  have hcol : colOf (ΦFun F p) = evIdx F (Sum.inr (crossOf F p)) := by
    unfold ΦFun; split_ifs
    · exact (σSlotA_spec _ _ _).1
    · exact (σSlotB_spec _ _ _).1
  have hcut : cut (word F) (evIdx F (Sum.inr (crossOf F p))) =
      hybridCut F (evX F (Sum.inr (crossOf F p))) (evZ F (Sum.inr (crossOf F p))) := by
    unfold cut; rw [run_take_eq_hybrid F hk, Option.getD_some]
    unfold colX colZ; rw [eventAt_evIdx]
  obtain ⟨A, B, hAB, hlen⟩ := s3s5_hybridCut_cross F (crossOf F p)
  have hb1 : bit (word F) (evIdx F (Sum.inr (crossOf F p))) (posOf F (Sum.inr (crossOf F p))) =
      dirBit F (crossOf F p).1.1 := by
    unfold bit
    rw [hcut, hAB, ← hlen, Nat.add_sub_cancel, List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self]
    rfl
  have hb2 : bit (word F) (evIdx F (Sum.inr (crossOf F p))) (posOf F (Sum.inr (crossOf F p)) + 1) =
      dirBit F (crossOf F p).1.2 := by
    unfold bit
    rw [hcut, hAB, ← hlen, Nat.add_sub_cancel, List.getD_append_right _ _ _ _ (Nat.le_succ _)]
    show (_ :: _ :: B).getD (A.length + 1 - A.length) false = _
    rw [Nat.add_sub_cancel_left]
    rfl
  have hℓ : letterAt (word F) (evIdx F (Sum.inr (crossOf F p))) = .σ (posOf F (Sum.inr (crossOf F p))) :=
    letterAt_word_cross F _
  have hou : F.IsOverUnder (crossOf F p).1.1 (crossOf F p).1.2 := F.isOverUnder_of_mem_crossingPairs (crossOf F p).2
  have hd := hou.1
  have hpair : (frontOver F p = true ∧ (crossOf F p).1 = (p.1, (partner F p).1)) ∨
      (frontOver F p = false ∧ (crossOf F p).1 = ((partner F p).1, p.1)) := by
    unfold crossOf
    by_cases h : frontOver F p = true
    · left; exact ⟨h, by rw [dite_eq_left h]⟩
    · right; exact ⟨Bool.eq_false_iff.mpr h, by rw [dite_eq_right h]⟩
  have hsgn : frontSgn F p = SignType.sign (det (F.vel (crossOf F p).1.1) (F.vel (crossOf F p).1.2)) := by
    unfold frontSgn
    rcases hpair with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · unfold frontOver at h1
      rw [h2, ite_eq_left (of_decide_eq_true h1)]
    · unfold frontOver at h1
      rw [h2, ite_eq_right (of_decide_eq_false h1)]
  apply signType_intCast_injective
  show ((U2.σsgn (ΦFun F p) : SignType) : ℤ) = ((frontSgn F p : SignType) : ℤ)
  rw [hsgn, ← F.crossSign_eq_sign hd, U2.σsgn, hcol, U2.coe_σsgnCol, hℓ]
  simp only [Letter.idx, hb1, hb2]
  unfold SmoothFront.crossSign
  have ho := F.vel_fst_ne_zero_of_isDouble hd
  have hu := F.vel_fst_ne_zero_of_isDouble hd.symm
  by_cases hdet : 0 < det (F.vel (crossOf F p).1.1) (F.vel (crossOf F p).1.2)
  · rw [ite_eq_left hdet, ite_eq_left]
    rw [s3s5_dirBit_eq_iff F ho hu]
    exact (F.crossSign_eq_one_iff_of_isOverUnder hou).mp ((F.crossSign_eq_one_iff _ _).mpr hdet)
  · rw [ite_eq_right hdet, ite_eq_right]
    rw [s3s5_dirBit_eq_iff F ho hu]
    intro hpos
    exact hdet ((F.crossSign_eq_one_iff _ _).mp ((F.crossSign_eq_one_iff_of_isOverUnder hou).mpr hpos))

end SlotMap

/-! #### S6. The traversal: cusp vertices, the slot of a strand at its cut line, jumps, `succ ↔ firstReturn` -/

section Traversal

variable (F : SmoothFront)

theorem isSlot_cuspVertex (c : F.Cusp) : IsSlot (word F) (evIdx F (Sum.inl c), 0) := by
  refine Or.inl ⟨rfl, evIdx_lt_length_word F _, ?_⟩
  show (letterAt (word F) (evIdx F (Sum.inl c))).isCrossing = false
  rw [letterAt_word_evIdx]
  dsimp only [letterOf]; split_ifs <;> rfl

/-- the cusp vertex slot of a cusp -/
def cuspVertex (c : F.Cusp) : Slot (word F) := ⟨(evIdx F (Sum.inl c), 0), isSlot_cuspVertex F c⟩

/-- a cusp on each circle -/
def someCuspOn (i : Fin F.c) : F.Cusp := (circleCusps_nonempty F i).choose

theorem someCuspOn_fst (i : Fin F.c) : (someCuspOn F i).1.1 = i :=
  (mem_circleCusps F i _).mp (circleCusps_nonempty F i).choose_spec

/-- the component of a circle: the `next`-cycle of the cusp vertex of one of its cusps -/
def circleComp (i : Fin F.c) : Fin (numComp (word_closed F)) :=
  U2.slotComp (word_closed F) (cuspVertex F (someCuspOn F i))

/-! ### S6a helpers -/
section S6aHelpers

/-! #### Generic list lemmas -/

section S6aLists

variable {α : Type*}

/-- An upward-closed filter (along the sorting relation) is a prefix of the filter. -/
theorem s6a_filter_split {R : α → α → Prop} {L : List α} (hL : L.Pairwise R) {P Q : α → Bool}
    (hQP : ∀ a ∈ L, Q a = true → P a = true)
    (hup : ∀ a ∈ L, ∀ b ∈ L, R a b → Q b = true → Q a = true) :
    L.filter P = L.filter Q ++ L.filter (fun a => P a && !Q a) := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    rw [List.pairwise_cons] at hL
    obtain ⟨hRa, hL'⟩ := hL
    have ih' := ih hL' (fun b hb => hQP b (List.mem_cons_of_mem _ hb))
      (fun b hb c hc => hup b (List.mem_cons_of_mem _ hb) c (List.mem_cons_of_mem _ hc))
    by_cases hQa : Q a = true
    · have hPa : P a = true := hQP a (List.mem_cons_self ..) hQa
      simp only [List.filter_cons, hPa, hQa, Bool.not_true, Bool.and_false, Bool.false_eq_true, ↓reduceIte, ih', List.cons_append]
    · have hQa' : Q a = false := by simpa using hQa
      have hQ : ∀ b ∈ L, Q b = false := by
        intro b hb
        by_contra h
        rw [Bool.not_eq_false] at h
        exact hQa (hup a (List.mem_cons_self ..) b (List.mem_cons_of_mem _ hb) (hRa b hb) h)
      have h1 : List.filter Q (a :: L) = [] := by
        rw [List.filter_eq_nil_iff]
        intro b hb
        rcases List.mem_cons.mp hb with rfl | hb
        · simp [hQa']
        · simp [hQ b hb]
      have h2 : List.filter (fun a => P a && !Q a) (a :: L) = List.filter P (a :: L) := by
        apply List.filter_congr
        intro b hb
        rcases List.mem_cons.mp hb with rfl | hb
        · simp [hQa']
        · simp [hQ b hb]
      rw [h1, h2, List.nil_append]

/-- A downward-closed filter is a suffix of the filter. -/
theorem s6a_filter_split' {R : α → α → Prop} {L : List α} (hL : L.Pairwise R) {P Q : α → Bool}
    (hQP : ∀ a ∈ L, Q a = true → P a = true)
    (hdown : ∀ a ∈ L, ∀ b ∈ L, R a b → Q a = true → Q b = true) :
    L.filter P = L.filter (fun a => P a && !Q a) ++ L.filter Q := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    rw [List.pairwise_cons] at hL
    obtain ⟨hRa, hL'⟩ := hL
    have ih' := ih hL' (fun b hb => hQP b (List.mem_cons_of_mem _ hb))
      (fun b hb c hc => hdown b (List.mem_cons_of_mem _ hb) c (List.mem_cons_of_mem _ hc))
    by_cases hQa : Q a = true
    · have hQ : ∀ b ∈ L, Q b = true := fun b hb =>
        hdown a (List.mem_cons_self ..) b (List.mem_cons_of_mem _ hb) (hRa b hb) hQa
      have hPa : P a = true := hQP a (List.mem_cons_self ..) hQa
      have h1 : List.filter (fun a => P a && !Q a) (a :: L) = [] := by
        rw [List.filter_eq_nil_iff]
        intro b hb
        rcases List.mem_cons.mp hb with rfl | hb
        · simp [hQa]
        · simp [hQ b hb]
      have h2 : List.filter Q (a :: L) = List.filter P (a :: L) := by
        apply List.filter_congr
        intro b hb
        rcases List.mem_cons.mp hb with rfl | hb
        · simp [hQa, hPa]
        · simp [hQ b hb, hQP b (List.mem_cons_of_mem _ hb) (hQ b hb)]
      rw [h1, h2, List.nil_append]
    · have hQa' : Q a = false := by simpa using hQa
      by_cases hPa : P a = true
      · simp only [List.filter_cons, hPa, hQa', Bool.not_false, Bool.and_true, Bool.false_eq_true, ↓reduceIte, ih', List.cons_append]
      · have hPa' : P a = false := by simpa using hPa
        simp only [List.filter_cons, hPa', hQa', Bool.not_false, Bool.and_true, Bool.false_eq_true, ↓reduceIte, ih']

/-- In a sorted list, an upward-closed predicate holds exactly at the indices below the filter's length. -/
theorem s6a_filter_getElem_iff {R : α → α → Prop} {L : List α} (hL : L.Pairwise R) {Q : α → Bool}
    (hup : ∀ a ∈ L, ∀ b ∈ L, R a b → Q b = true → Q a = true) (j : ℕ) (hj : j < L.length) :
    Q L[j] = true ↔ j < (L.filter Q).length := by
  have hsplit := s6a_filter_split hL (P := fun _ => true) (Q := Q) (fun _ _ _ => rfl) hup
  rw [List.filter_true] at hsplit
  have hlen : L.length = (L.filter Q).length + (L.filter (fun a => true && !Q a)).length := by
    have := congrArg List.length hsplit
    rwa [List.length_append] at this
  have hLj : L[j] = (L.filter Q ++ L.filter (fun a => true && !Q a))[j]'(by rw [← hsplit]; exact hj) :=
    List.getElem_of_eq hsplit hj
  constructor
  · intro hQ
    by_contra hge
    rw [not_lt] at hge
    have hj' : j - (L.filter Q).length < (L.filter (fun a => true && !Q a)).length := by omega
    have h := List.getElem_filter (xs := L) (p := fun a => true && !Q a) hj'
    rw [hLj, List.getElem_append_right hge] at hQ
    rw [hQ] at h
    simp at h
  · intro hlt
    have h := List.getElem_filter (xs := L) (p := Q) hlt
    rw [hLj, List.getElem_append_left hlt]
    exact h

/-- A sorted nodup list splits around an element of unique key: the elements of larger key, the element,
the elements of smaller key. -/
theorem s6a_sorted_split {R : α → α → Prop} {key : α → ℝ} (hkey : ∀ a b, R a b → key b ≤ key a)
    {L : List α} (hL : L.Pairwise R) (hnd : L.Nodup) {q : α} (hq : q ∈ L)
    (huniq : ∀ p ∈ L, key p = key q → p = q) :
    L = L.filter (fun p => decide (key q < key p)) ++ q :: L.filter (fun p => decide (key p < key q)) := by
  induction L with
  | nil => exact absurd hq (by simp)
  | cons a L ih =>
    rw [List.pairwise_cons] at hL
    obtain ⟨hRa, hL'⟩ := hL
    rw [List.nodup_cons] at hnd
    obtain ⟨haL, hnd'⟩ := hnd
    by_cases hqa : a = q
    · subst hqa
      have hlt : ∀ b ∈ L, key b < key a := by
        intro b hb
        have hle := hkey _ _ (hRa b hb)
        have hne : key b ≠ key a := by
          intro h
          rw [huniq b (List.mem_cons_of_mem _ hb) h] at hb
          exact haL hb
        exact lt_of_le_of_ne hle hne
      have h1 : List.filter (fun p => decide (key a < key p)) (a :: L) = [] := by
        rw [List.filter_eq_nil_iff]
        intro b hb
        rcases List.mem_cons.mp hb with rfl | hb
        · simp
        · simp [not_lt.mpr (hlt b hb).le]
      have h2 : List.filter (fun p => decide (key p < key a)) (a :: L) = L := by
        rw [List.filter_cons_of_neg (by simp), List.filter_eq_self]
        intro b hb; simpa using hlt b hb
      rw [h1, h2, List.nil_append]
    · have hq' : q ∈ L := by
        rcases List.mem_cons.mp hq with h | h
        · exact absurd h.symm hqa
        · exact h
      have ih' := ih hL' hnd' hq' (fun p hp h => huniq p (List.mem_cons_of_mem _ hp) h)
      have hgt : key q < key a := by
        have hle := hkey _ _ (hRa q hq')
        have hne : key a ≠ key q := fun h => hqa (huniq a (List.mem_cons_self ..) h)
        exact lt_of_le_of_ne hle (Ne.symm hne)
      rw [List.filter_cons_of_pos (by simpa using hgt), List.filter_cons_of_neg (by simp [not_lt.mpr hgt.le]),
        List.cons_append]
      exact congrArg (a :: ·) ih'

/-- A filter of a nodup list with exactly one satisfying element is that singleton. -/
theorem s6a_filter_eq_singleton {L : List α} (hnd : L.Nodup) {P : α → Bool} {q : α} (hq : q ∈ L)
    (hPq : P q = true) (huniq : ∀ p ∈ L, P p = true → p = q) : L.filter P = [q] := by
  have hmem : ∀ p, p ∈ L.filter P ↔ p = q := by
    intro p
    rw [List.mem_filter]
    constructor
    · rintro ⟨hp, hPp⟩; exact huniq p hp hPp
    · rintro rfl; exact ⟨hq, hPq⟩
  have hnd' : (L.filter P).Nodup := hnd.filter P
  rcases hfil : L.filter P with _ | ⟨a, _ | ⟨b, rest⟩⟩
  · rw [hfil] at hmem; exact absurd ((hmem q).mpr rfl) (by simp)
  · rw [hfil] at hmem; rw [(hmem a).mp (List.mem_singleton_self a)]
  · rw [hfil] at hmem hnd'
    have ha : a = q := (hmem a).mp (List.mem_cons_self ..)
    have hb : b = q := (hmem b).mp (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    rw [List.nodup_cons] at hnd'
    exact absurd (by rw [ha, hb]; exact List.mem_cons_self ..) hnd'.1

/-- A filter of a sorted nodup list with exactly two satisfying elements `o ≠ u`, `u` not before `o`, is `[o, u]`. -/
theorem s6a_filter_eq_pair {R : α → α → Prop} {L : List α} (hL : L.Pairwise R) (hnd : L.Nodup) {P : α → Bool}
    {o u : α} (hou : o ≠ u) (ho : o ∈ L) (hu : u ∈ L) (hPo : P o = true) (hPu : P u = true)
    (huniq : ∀ p ∈ L, P p = true → p = o ∨ p = u) (hR : ¬ R u o) : L.filter P = [o, u] := by
  have hmem : ∀ p, p ∈ L.filter P ↔ p = o ∨ p = u := by
    intro p; rw [List.mem_filter]
    constructor
    · rintro ⟨hp, hPp⟩; exact huniq p hp hPp
    · rintro (rfl | rfl)
      · exact ⟨ho, hPo⟩
      · exact ⟨hu, hPu⟩
  have hnd' : (L.filter P).Nodup := hnd.filter P
  have hpw : (L.filter P).Pairwise R := hL.sublist List.filter_sublist
  rcases hfil : L.filter P with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
  · rw [hfil] at hmem; exact absurd ((hmem o).mpr (Or.inl rfl)) (by simp)
  · rw [hfil] at hmem
    have h1 : o = a := by simpa using (hmem o).mpr (Or.inl rfl)
    have h2 : u = a := by simpa using (hmem u).mpr (Or.inr rfl)
    exact absurd (h1.trans h2.symm) hou
  · rw [hfil] at hmem hnd' hpw
    have ha := (hmem a).mp (by simp)
    have hb := (hmem b).mp (by simp)
    rw [List.nodup_cons, List.nodup_cons] at hnd'
    have hab : a ≠ b := fun h => hnd'.1 (by simp [h])
    rw [List.pairwise_cons] at hpw
    have hRab : R a b := hpw.1 b (by simp)
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact absurd rfl hab
    · rfl
    · exact absurd hRab hR
    · exact absurd rfl hab
  · rw [hfil] at hmem hnd'
    have ha := (hmem a).mp (by simp)
    have hb := (hmem b).mp (by simp)
    have hc := (hmem c).mp (by simp)
    rw [List.nodup_cons, List.nodup_cons] at hnd'
    have hab : a ≠ b := fun h => hnd'.1 (by simp [h])
    have hac : a ≠ c := fun h => hnd'.1 (by simp [h])
    have hbc : b ≠ c := fun h => hnd'.2.1 (by simp [h])
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> rcases hc with rfl | rfl <;>
      first | exact absurd rfl hab | exact absurd rfl hac | exact absurd rfl hbc

/-- `getElem` on a three-part concatenation. -/
theorem s6a_getElem_A {β : Type*} (A E R : List β) (j : ℕ) (hj : j < A.length) :
    (A ++ E ++ R)[j]'(by simp; omega) = A[j] := by
  rw [List.getElem_append_left (by simp; omega), List.getElem_append_left hj]

theorem s6a_getElem_E {β : Type*} (A E R : List β) (j : ℕ) (hj : j < E.length) :
    (A ++ E ++ R)[A.length + j]'(by simp; omega) = E[j] := by
  rw [List.getElem_append_left (by simp; omega), List.getElem_append_right (by omega)]
  simp

theorem s6a_getElem_R {β : Type*} (A E R : List β) (j : ℕ) (hj : j < R.length) :
    (A ++ E ++ R)[A.length + E.length + j]'(by simp; omega) = R[j] := by
  rw [List.getElem_append_right (by simp)]
  simp

theorem s6a_getElem_three {β : Type*} (A E R : List β) (J : ℕ) (hJ : J < (A ++ E ++ R).length) :
    (∃ h : J < A.length, (A ++ E ++ R)[J] = A[J]'h) ∨
    (∃ h : A.length ≤ J ∧ J < A.length + E.length, (A ++ E ++ R)[J] = E[J - A.length]'(by omega)) ∨
    (∃ h : A.length + E.length ≤ J, (A ++ E ++ R)[J] = R[J - (A.length + E.length)]'(by simp at hJ; omega)) := by
  have hJ' := hJ
  simp only [List.length_append] at hJ'
  rcases Nat.lt_or_ge J A.length with h1 | h1
  · left
    refine ⟨h1, ?_⟩
    rw [List.getElem_append_left (by simp; omega), List.getElem_append_left h1]
  · rcases Nat.lt_or_ge J (A.length + E.length) with h2 | h2
    · right; left
      refine ⟨⟨h1, h2⟩, ?_⟩
      rw [List.getElem_append_left (by simp; omega), List.getElem_append_right h1]
    · right; right
      refine ⟨h2, ?_⟩
      rw [List.getElem_append_right (by simp; omega)]
      simp

end S6aLists

/-! #### Height order, events at one x-value, the window of an event -/

section S6aFront

variable (F : SmoothFront)

theorem s6a_ht_of_beforeLE {p q : Param F.c} (h : beforeLE F p q = true) : ht F q ≤ ht F p := by
  unfold beforeLE at h
  simp only [decide_eq_true_iff, Prod.Lex.toLex_le_toLex] at h
  rcases h with h | ⟨h, -⟩ <;> linarith

theorem s6a_ht_of_afterLE {p q : Param F.c} (h : afterLE F p q = true) : ht F q ≤ ht F p := by
  unfold afterLE at h
  simp only [decide_eq_true_iff, Prod.Lex.toLex_le_toLex] at h
  rcases h with h | ⟨h, -⟩ <;> linarith

theorem s6a_Lb_pairwise (x₀ : ℝ) : (fibreListBefore F x₀).Pairwise (fun p q => ht F q ≤ ht F p) :=
  (fibreListBefore_pairwise F x₀).imp (fun h => s6a_ht_of_beforeLE F h)

theorem s6a_La_pairwise (x₀ : ℝ) : (fibreListAfter F x₀).Pairwise (fun p q => ht F q ≤ ht F p) :=
  (fibreListAfter_pairwise F x₀).imp (fun h => s6a_ht_of_afterLE F h)

theorem s6a_eval_eq_of_mem {x₀ : ℝ} {p q : Param F.c} (hp : p ∈ totalFibre F x₀) (hq : q ∈ totalFibre F x₀)
    (hz : ht F p = ht F q) : F.eval p = F.eval q :=
  Prod.ext (hp.2.trans hq.2.symm) hz

theorem s6a_isDouble_of_mem {x₀ : ℝ} {p q : Param F.c} (hp : p ∈ totalFibre F x₀) (hq : q ∈ totalFibre F x₀)
    (hne : p ≠ q) (hz : ht F p = ht F q) : F.IsDouble p q :=
  ⟨fun hs => hne (SameParam.eq_of_mem_Ico hp.1 hq.1 hs), s6a_eval_eq_of_mem F hp hq hz⟩

theorem s6a_evX_mem_singX (e : Event F) : evX F e ∈ singX F := by
  cases e with
  | inl c => exact mem_singX_of_isCusp F c.isCusp
  | inr q => exact mem_singX_of_isDouble F (F.isOverUnder_of_mem_crossingPairs q.2).1

theorem s6a_regular_of_no_event {x₀ : ℝ} {p : Param F.c} (hp : p ∈ totalFibre F x₀)
    (h : ∀ e : Event F, evX F e = x₀ → evZ F e ≠ ht F p) : ¬ F.IsCusp p ∧ ∀ q, ¬ F.IsDouble p q := by
  constructor
  · intro hc
    obtain ⟨e, he1, he2⟩ := exists_event_of_singular F hp (Or.inl hc)
    exact h e he1 he2
  · intro q hq
    obtain ⟨e, he1, he2⟩ := exists_event_of_singular F hp (Or.inr ⟨q, hq⟩)
    exact h e he1 he2

theorem s6a_bits_of_not_cusp {p : Param F.c} (h : ¬ F.IsCusp p) :
    beforeBits F p = [dirBit F p] ∧ afterBits F p = [dirBit F p] := by
  have h1 : ¬ F.IsLeftCusp p := fun h' => h h'.1
  have h2 : ¬ F.IsRightCusp p := fun h' => h h'.1
  unfold beforeBits afterBits
  simp [h1, h2]

theorem s6a_under_mem_totalFibre (q : Cross F) : q.1.2 ∈ totalFibre F (evX F (Sum.inr q)) := by
  have hq := F.mem_crossingPairs'.mp q.2
  refine ⟨hq.1.2.1, ?_⟩
  show (F.eval q.1.2).1 = (F.eval q.1.1).1
  rw [hq.1.2.2.2]

theorem s6a_ht_under (q : Cross F) : ht F q.1.2 = evZ F (Sum.inr q) := by
  have hq := F.mem_crossingPairs'.mp q.2
  show (F.eval q.1.2).2 = (F.eval q.1.1).2
  rw [hq.1.2.2.2]

/-- The fibre points at the height of an event over its x-value are exactly the event's point(s). -/
theorem s6a_ht_eq_evZ_iff {x₀ : ℝ} (e : Event F) (he : evX F e = x₀) {p : Param F.c} (hp : p ∈ totalFibre F x₀) :
    ht F p = evZ F e ↔ p = evPt F e ∨ ∃ q : Cross F, e = Sum.inr q ∧ p = q.1.2 := by
  have hev : evPt F e ∈ totalFibre F x₀ := he ▸ evPt_mem_totalFibre F e
  constructor
  · intro hz
    by_cases hpe : p = evPt F e
    · exact Or.inl hpe
    · have hd : F.IsDouble p (evPt F e) := s6a_isDouble_of_mem F hp hev hpe hz
      cases e with
      | inl c => exact absurd c.isCusp (F.vel_ne_zero_of_isDouble hd.symm)
      | inr q =>
        right
        refine ⟨q, rfl, ?_⟩
        by_contra hpq
        have hq := F.mem_crossingPairs'.mp q.2
        obtain ⟨⟨hq1, hq2, hqne, hqe⟩, -⟩ := hq
        have hs1 : ¬ SameParam p q.1.1 := hd.1
        have hs2 : ¬ SameParam q.1.1 q.1.2 := fun hs => hqne (SameParam.eq_of_mem_Ico hq1 hq2 hs)
        have hs3 : ¬ SameParam p q.1.2 := fun hs => hpq (SameParam.eq_of_mem_Ico hp.1 hq2 hs)
        exact F.no_triple p q.1.1 q.1.2 hs1 hs2 hs3 hd.2 hqe
  · rintro (rfl | ⟨q, rfl, rfl⟩)
    · rfl
    · exact s6a_ht_under F q

theorem s6a_filter_ht_cusp {x₀ : ℝ} (c : F.Cusp) (he : evX F (Sum.inl c) = x₀) :
    (fibreListBefore F x₀).filter (fun p => decide (ht F p = evZ F (Sum.inl c))) = [c.1] ∧
    (fibreListAfter F x₀).filter (fun p => decide (ht F p = evZ F (Sum.inl c))) = [c.1] := by
  have hc : c.1 ∈ totalFibre F x₀ := he ▸ evPt_mem_totalFibre F (Sum.inl c)
  have huniq : ∀ p ∈ totalFibre F x₀, decide (ht F p = evZ F (Sum.inl c)) = true → p = c.1 := by
    intro p hp hz
    rw [decide_eq_true_iff] at hz
    rcases (s6a_ht_eq_evZ_iff F _ he hp).mp hz with h | ⟨q, hq, -⟩
    · exact h
    · cases hq
  constructor
  · exact s6a_filter_eq_singleton (fibreListBefore_nodup F x₀) ((mem_fibreListBefore F x₀ _).mpr hc)
      (decide_eq_true rfl) (fun p hp hz => huniq p ((mem_fibreListBefore F x₀ p).mp hp) hz)
  · exact s6a_filter_eq_singleton (fibreListAfter_nodup F x₀) ((mem_fibreListAfter F x₀ _).mpr hc)
      (decide_eq_true rfl) (fun p hp hz => huniq p ((mem_fibreListAfter F x₀ p).mp hp) hz)

theorem s6a_filter_ht_cross {x₀ : ℝ} (q : Cross F) (he : evX F (Sum.inr q) = x₀) :
    (fibreListBefore F x₀).filter (fun p => decide (ht F p = evZ F (Sum.inr q))) = [q.1.1, q.1.2] ∧
    (fibreListAfter F x₀).filter (fun p => decide (ht F p = evZ F (Sum.inr q))) = [q.1.2, q.1.1] := by
  have hq := F.mem_crossingPairs'.mp q.2
  obtain ⟨⟨hq1, hq2, hqne, hqe⟩, hslope⟩ := hq
  have ho : q.1.1 ∈ totalFibre F x₀ := he ▸ evPt_mem_totalFibre F (Sum.inr q)
  have hu : q.1.2 ∈ totalFibre F x₀ := he ▸ s6a_under_mem_totalFibre F q
  have hzo : decide (ht F q.1.1 = evZ F (Sum.inr q)) = true := decide_eq_true rfl
  have hzu : decide (ht F q.1.2 = evZ F (Sum.inr q)) = true := decide_eq_true (s6a_ht_under F q)
  have huniq : ∀ p ∈ totalFibre F x₀, decide (ht F p = evZ F (Sum.inr q)) = true → p = q.1.1 ∨ p = q.1.2 := by
    intro p hp hz
    rw [decide_eq_true_iff] at hz
    rcases (s6a_ht_eq_evZ_iff F _ he hp).mp hz with h | ⟨q', hq', h⟩
    · exact Or.inl h
    · cases hq'; exact Or.inr h
  have hzeq : ht F q.1.2 = ht F q.1.1 := s6a_ht_under F q
  constructor
  · apply s6a_filter_eq_pair (fibreListBefore_pairwise F x₀) (fibreListBefore_nodup F x₀) hqne
      ((mem_fibreListBefore F x₀ _).mpr ho) ((mem_fibreListBefore F x₀ _).mpr hu) hzo hzu
      (fun p hp hz => huniq p ((mem_fibreListBefore F x₀ p).mp hp) hz)
    unfold beforeLE
    simp only [decide_eq_true_iff, Prod.Lex.toLex_le_toLex, hzeq, lt_self_iff_false, true_and, false_or, not_le]
    exact hslope
  · apply s6a_filter_eq_pair (fibreListAfter_pairwise F x₀) (fibreListAfter_nodup F x₀) (Ne.symm hqne)
      ((mem_fibreListAfter F x₀ _).mpr hu) ((mem_fibreListAfter F x₀ _).mpr ho) hzu hzo
      (fun p hp hz => (huniq p ((mem_fibreListAfter F x₀ p).mp hp) hz).symm)
    unfold afterLE
    simp only [decide_eq_true_iff, Prod.Lex.toLex_le_toLex, hzeq, lt_self_iff_false, true_and, false_or, not_le,
      neg_lt_neg_iff]
    exact hslope

/-- `entriesOf` facts -/
theorem s6a_entriesOf_append (bits : Param F.c → Cuts) (L₁ L₂ : List (Param F.c)) :
    entriesOf F bits (L₁ ++ L₂) = entriesOf F bits L₁ ++ entriesOf F bits L₂ := by
  unfold entriesOf; rw [List.flatMap_append]

theorem s6a_entriesOf_cons (bits : Param F.c → Cuts) (p : Param F.c) (L : List (Param F.c)) :
    entriesOf F bits (p :: L) = (List.range (bits p).length).map (fun j => (p, j)) ++ entriesOf F bits L := by
  unfold entriesOf; rw [List.flatMap_cons]

theorem s6a_entriesOf_nil (bits : Param F.c → Cuts) : entriesOf F bits [] = [] := rfl

theorem s6a_length_entriesOf (bits : Param F.c → Cuts) (L : List (Param F.c)) :
    (entriesOf F bits L).length = (L.flatMap bits).length := by
  rw [← map_entryBit_entriesOf F bits L, List.length_map]

theorem s6a_mem_entriesOf {bits : Param F.c → Cuts} {L : List (Param F.c)} {a : Param F.c × ℕ} :
    a ∈ entriesOf F bits L ↔ a.1 ∈ L ∧ a.2 < (bits a.1).length := by
  unfold entriesOf
  rw [List.mem_flatMap]
  constructor
  · rintro ⟨p, hp, ha⟩
    rw [List.mem_map] at ha
    obtain ⟨j, hj, rfl⟩ := ha
    rw [List.mem_range] at hj
    exact ⟨hp, hj⟩
  · rintro ⟨hp, hj⟩
    exact ⟨a.1, hp, List.mem_map.mpr ⟨a.2, List.mem_range.mpr hj, rfl⟩⟩

theorem s6a_entriesOf_congr {bits bits' : Param F.c → Cuts} {L : List (Param F.c)}
    (h : ∀ p ∈ L, (bits p).length = (bits' p).length) : entriesOf F bits L = entriesOf F bits' L := by
  induction L with
  | nil => rfl
  | cons p L ih =>
    rw [s6a_entriesOf_cons, s6a_entriesOf_cons, h p (List.mem_cons_self ..),
      ih (fun q hq => h q (List.mem_cons_of_mem _ hq))]

theorem s6a_entriesOf_nodup (bits : Param F.c → Cuts) {L : List (Param F.c)} (hL : L.Nodup) :
    (entriesOf F bits L).Nodup := by
  unfold entriesOf
  rw [List.nodup_flatMap]
  constructor
  · intro p _
    exact List.nodup_range.map (fun j j' h => by simpa using congrArg Prod.snd h)
  · refine hL.imp ?_
    intro p q hpq
    rw [Function.onFun, List.disjoint_left]
    rintro a ha hb
    rw [List.mem_map] at ha hb
    obtain ⟨j, -, rfl⟩ := ha
    obtain ⟨j', -, hj'⟩ := hb
    exact hpq (congrArg Prod.fst hj').symm

/-- The hybrid entries are nodup. -/
theorem s6a_hybridEntriesP_nodup (x₀ : ℝ) (P : Param F.c → Bool) : (hybridEntriesP F x₀ P).Nodup := by
  unfold hybridEntriesP
  rw [List.nodup_append]
  refine ⟨s6a_entriesOf_nodup F _ ((fibreListBefore_nodup F x₀).filter _),
    s6a_entriesOf_nodup F _ ((fibreListAfter_nodup F x₀).filter _), ?_⟩
  intro a ha b hb hab
  rw [s6a_mem_entriesOf, List.mem_filter] at ha hb
  rw [hab] at ha
  rw [ha.1.2] at hb
  simp at hb

/-- the "before" list at threshold `z ≤ ht`: the points strictly above, then the points at height `z` -/
theorem s6a_Lb_filter_le (x₀ z : ℝ) :
    (fibreListBefore F x₀).filter (fun p => decide (z ≤ ht F p)) =
      (fibreListBefore F x₀).filter (fun p => decide (z < ht F p)) ++
        (fibreListBefore F x₀).filter (fun p => decide (ht F p = z)) := by
  rw [s6a_filter_split (fibreListBefore_pairwise F x₀) (P := fun p => decide (z ≤ ht F p))
    (Q := fun p => decide (z < ht F p))]
  · congr 1
    apply List.filter_congr
    intro p _
    rcases lt_trichotomy z (ht F p) with h | h | h
    · simp [h, h.le, h.ne']
    · simp [h]
    · simp [not_le.mpr h, h.ne]
  · intro p _ h; simp only [decide_eq_true_iff] at h ⊢; exact h.le
  · intro p _ q _ hpq hq
    simp only [decide_eq_true_iff] at hq ⊢
    exact lt_of_lt_of_le hq (s6a_ht_of_beforeLE F hpq)

/-- the "after" list at threshold `¬ (z < ht)`: the points at height `z`, then the points strictly below -/
theorem s6a_La_filter_not_lt (x₀ z : ℝ) :
    (fibreListAfter F x₀).filter (fun p => !decide (z < ht F p)) =
      (fibreListAfter F x₀).filter (fun p => decide (ht F p = z)) ++
        (fibreListAfter F x₀).filter (fun p => decide (ht F p < z)) := by
  rw [s6a_filter_split' (fibreListAfter_pairwise F x₀) (P := fun p => !decide (z < ht F p))
    (Q := fun p => decide (ht F p < z))]
  · congr 1
    apply List.filter_congr
    intro p _
    rcases lt_trichotomy z (ht F p) with h | h | h
    · simp [h, not_lt.mpr h.le, h.ne']
    · simp [h]
    · simp [h, not_lt.mpr h.le, h.ne]
  · intro p _ h; simp only [decide_eq_true_iff, Bool.not_eq_true', decide_eq_false_iff_not, not_lt] at h ⊢; exact h.le
  · intro p _ q _ hpq hp
    simp only [decide_eq_true_iff] at hp ⊢
    exact lt_of_le_of_lt (s6a_ht_of_afterLE F hpq) hp

theorem s6a_La_filter_not_le (x₀ z : ℝ) :
    (fibreListAfter F x₀).filter (fun p => !decide (z ≤ ht F p)) =
      (fibreListAfter F x₀).filter (fun p => decide (ht F p < z)) := by
  apply List.filter_congr
  intro p _
  rcases le_or_gt z (ht F p) with h | h
  · simp [h, not_lt.mpr h]
  · simp [h, not_le.mpr h]

/-- The hybrid entries are insensitive to moving the threshold across regular points only. -/
theorem s6a_hybridEntriesP_eq (x₀ : ℝ) (P P' : Param F.c → Bool)
    (hP : ∀ p q, ht F q ≤ ht F p → P q = true → P p = true)
    (hP' : ∀ p q, ht F q ≤ ht F p → P' q = true → P' p = true)
    (hPP' : ∀ p, P' p = true → P p = true)
    (hreg : ∀ p ∈ totalFibre F x₀, P p = true → P' p = false → ¬ F.IsCusp p ∧ ∀ q, ¬ F.IsDouble p q) :
    hybridEntriesP F x₀ P = hybridEntriesP F x₀ P' := by
  unfold hybridEntriesP
  have h1 : (fibreListBefore F x₀).filter P =
      (fibreListBefore F x₀).filter P' ++ (fibreListBefore F x₀).filter (fun p => P p && !P' p) :=
    s6a_filter_split (fibreListBefore_pairwise F x₀) (fun p _ => hPP' p)
      (fun p _ q _ hpq hq => hP' p q (s6a_ht_of_beforeLE F hpq) hq)
  have h2 : (fibreListAfter F x₀).filter (fun p => !P' p) =
      (fibreListAfter F x₀).filter (fun p => P p && !P' p) ++ (fibreListAfter F x₀).filter (fun p => !P p) := by
    rw [s6a_filter_split' (fibreListAfter_pairwise F x₀) (P := fun p => !P' p) (Q := fun p => !P p)]
    · congr 1
      apply List.filter_congr
      intro p _
      cases P p <;> cases P' p <;> rfl
    · intro p _ h
      simp only [Bool.not_eq_true'] at h ⊢
      by_contra h'
      rw [Bool.not_eq_false] at h'
      rw [hPP' p h'] at h
      exact Bool.noConfusion h
    · intro p _ q _ hpq hp
      simp only [Bool.not_eq_true'] at hp ⊢
      by_contra h'
      rw [Bool.not_eq_false] at h'
      rw [hP p q (s6a_ht_of_afterLE F hpq) h'] at hp
      exact Bool.noConfusion hp
  have hMb_reg : ∀ p ∈ (fibreListBefore F x₀).filter (fun p => P p && !P' p),
      ¬ F.IsCusp p ∧ ∀ q, ¬ F.IsDouble p q := by
    intro p hp
    rw [List.mem_filter, Bool.and_eq_true, Bool.not_eq_true'] at hp
    exact hreg p ((mem_fibreListBefore F x₀ p).mp hp.1) hp.2.1 hp.2.2
  have hMa_reg : ∀ p ∈ (fibreListAfter F x₀).filter (fun p => P p && !P' p),
      ¬ F.IsCusp p ∧ ∀ q, ¬ F.IsDouble p q := by
    intro p hp
    rw [List.mem_filter, Bool.and_eq_true, Bool.not_eq_true'] at hp
    exact hreg p ((mem_fibreListAfter F x₀ p).mp hp.1) hp.2.1 hp.2.2
  have hMbMa : (fibreListBefore F x₀).filter (fun p => P p && !P' p) =
      (fibreListAfter F x₀).filter (fun p => P p && !P' p) := by
    apply List.Perm.eq_of_pairwise (le := fun p q => ht F q ≤ ht F p)
    · intro a b ha hb h1 h2
      by_contra hne
      have hz : ht F a = ht F b := le_antisymm h2 h1
      have ha' := (mem_fibreListBefore F x₀ a).mp (List.mem_of_mem_filter ha)
      have hb' := (mem_fibreListAfter F x₀ b).mp (List.mem_of_mem_filter hb)
      exact (hMb_reg a ha).2 b (s6a_isDouble_of_mem F ha' hb' hne hz)
    · exact (s6a_Lb_pairwise F x₀).sublist List.filter_sublist
    · exact (s6a_La_pairwise F x₀).sublist List.filter_sublist
    · exact ((fibreListBefore_perm F x₀).trans (fibreListAfter_perm F x₀).symm).filter _
  rw [h1, h2, s6a_entriesOf_append, s6a_entriesOf_append, List.append_assoc]
  congr 1
  congr 1
  rw [s6a_entriesOf_congr F (bits := beforeBits F) (bits' := afterBits F) (fun p hp => by
        obtain ⟨hb, ha⟩ := s6a_bits_of_not_cusp F (hMb_reg p hp).1; rw [hb, ha]), hMbMa]

end S6aFront

/-! #### The columns of one x-value -/

section S6aColumns

variable (F : SmoothFront) (x₀ : ℝ)

/-- the first column at `x₀`: the number of events strictly left of `x₀` -/
def s6a_k0 : ℕ := colAt F x₀
/-- one past the last column at `x₀`: the number of events left of or at `x₀` -/
def s6a_K : ℕ := ((events F).filter (fun e => decide (evX F e ≤ x₀))).length

theorem s6a_eventAt_eq {k : ℕ} (hk : k < (events F).length) : eventAt F k = (events F)[k] := by
  unfold eventAt; exact List.getD_eq_getElem _ _ hk

theorem s6a_evX_lt_iff {k : ℕ} (hk : k < (events F).length) : evX F (eventAt F k) < x₀ ↔ k < s6a_k0 F x₀ := by
  rw [s6a_eventAt_eq F hk]
  have := s6a_filter_getElem_iff (events_pairwise_lt F) (Q := fun e => decide (evX F e < x₀)) ?_ k hk
  · simpa only [decide_eq_true_iff, s6a_k0, colAt] using this
  · intro a _ b _ hab hb
    simp only [decide_eq_true_iff, Prod.Lex.toLex_lt_toLex] at hb hab ⊢
    rcases hab with h | ⟨h, -⟩
    · exact h.trans hb
    · rw [h]; exact hb

theorem s6a_evX_le_iff {k : ℕ} (hk : k < (events F).length) : evX F (eventAt F k) ≤ x₀ ↔ k < s6a_K F x₀ := by
  rw [s6a_eventAt_eq F hk]
  have := s6a_filter_getElem_iff (events_pairwise_lt F) (Q := fun e => decide (evX F e ≤ x₀)) ?_ k hk
  · simpa only [decide_eq_true_iff, s6a_K] using this
  · intro a _ b _ hab hb
    simp only [decide_eq_true_iff, Prod.Lex.toLex_lt_toLex] at hb hab ⊢
    rcases hab with h | ⟨h, -⟩
    · exact h.le.trans hb
    · rw [h]; exact hb

theorem s6a_K_le : s6a_K F x₀ ≤ (events F).length := List.length_filter_le _ _
theorem s6a_k0_le : s6a_k0 F x₀ ≤ (events F).length := List.length_filter_le _ _

theorem s6a_k0_le_K : s6a_k0 F x₀ ≤ s6a_K F x₀ := by
  by_contra h
  rw [not_le] at h
  have hK : s6a_K F x₀ < (events F).length := lt_of_lt_of_le h (s6a_k0_le F x₀)
  have h1 := (s6a_evX_lt_iff F x₀ hK).mpr h
  have h2 := (s6a_evX_le_iff F x₀ hK).mp h1.le
  exact lt_irrefl _ h2

theorem s6a_colX_eq {k : ℕ} (hk0 : s6a_k0 F x₀ ≤ k) (hkK : k < s6a_K F x₀) : colX F k = x₀ := by
  have hk : k < (events F).length := lt_of_lt_of_le hkK (s6a_K_le F x₀)
  have h1 : ¬ evX F (eventAt F k) < x₀ := fun h => absurd ((s6a_evX_lt_iff F x₀ hk).mp h) (not_lt.mpr hk0)
  have h2 : evX F (eventAt F k) ≤ x₀ := (s6a_evX_le_iff F x₀ hk).mpr hkK
  exact le_antisymm h2 (not_lt.mp h1)

theorem s6a_colZ_lt {k k' : ℕ} (hk0 : s6a_k0 F x₀ ≤ k) (hkk' : k < k') (hk'K : k' < s6a_K F x₀) :
    colZ F k < colZ F k' := by
  have hk' : k' < (events F).length := lt_of_lt_of_le hk'K (s6a_K_le F x₀)
  have hk : k < (events F).length := lt_trans hkk' hk'
  have h := List.pairwise_iff_getElem.mp (events_pairwise_lt F) k k' hk hk' hkk'
  have hx : colX F k = colX F k' := by
    rw [s6a_colX_eq F x₀ hk0 (lt_trans hkk' hk'K), s6a_colX_eq F x₀ (le_of_lt (lt_of_le_of_lt hk0 hkk')) hk'K]
  unfold colX at hx
  unfold colZ
  rw [s6a_eventAt_eq F hk, s6a_eventAt_eq F hk'] at hx ⊢
  simp only [Prod.Lex.toLex_lt_toLex] at h
  rcases h with h | ⟨-, h⟩
  · rw [hx] at h; exact absurd h (lt_irrefl _)
  · exact h

theorem s6a_colZ_le {k k' : ℕ} (hk0 : s6a_k0 F x₀ ≤ k) (hkk' : k ≤ k') (hk'K : k' < s6a_K F x₀) :
    colZ F k ≤ colZ F k' := by
  rcases Nat.lt_or_ge k k' with h | h
  · exact (s6a_colZ_lt F x₀ hk0 h hk'K).le
  · have : k = k' := le_antisymm hkk' h
    rw [this]

theorem s6a_evIdx_mem {e : Event F} (he : evX F e = x₀) : s6a_k0 F x₀ ≤ evIdx F e ∧ evIdx F e < s6a_K F x₀ := by
  have hk := evIdx_lt_length F e
  constructor
  · by_contra h
    rw [not_le] at h
    have := (s6a_evX_lt_iff F x₀ hk).mpr h
    rw [eventAt_evIdx, he] at this
    exact lt_irrefl _ this
  · rw [← s6a_evX_le_iff F x₀ hk, eventAt_evIdx, he]

theorem s6a_evZ_eq_colZ (e : Event F) : evZ F e = colZ F (evIdx F e) := by
  unfold colZ; rw [eventAt_evIdx]

theorem s6a_colAt_eq_k0 {x : ℝ} (hx : x < x₀) (hgap : ∀ e : Event F, evX F e < x₀ → evX F e < x) :
    colAt F x = s6a_k0 F x₀ := by
  unfold s6a_k0 colAt
  congr 1
  apply List.filter_congr
  intro e _
  simp only [decide_eq_decide]
  exact ⟨fun h => lt_trans h hx, hgap e⟩

theorem s6a_colAt_eq_K {x : ℝ} (hx : x₀ < x) (hgap : ∀ e : Event F, x₀ < evX F e → x < evX F e) :
    colAt F x = s6a_K F x₀ := by
  unfold colAt s6a_K
  congr 1
  apply List.filter_congr
  intro e _
  simp only [decide_eq_decide]
  constructor
  · intro h; by_contra h'; rw [not_le] at h'; exact absurd (hgap e h') (not_lt.mpr h.le)
  · intro h; exact lt_of_le_of_lt h hx

theorem s6a_singX_gap : ∃ η > 0, ∀ y ∈ singX F, y ≠ x₀ → η ≤ |y - x₀| := by
  by_cases hne : ((singX F).erase x₀).Nonempty
  · obtain ⟨y₀, hy₀, hmin⟩ := Finset.exists_min_image _ (fun y => |y - x₀|) hne
    refine ⟨|y₀ - x₀|, ?_, fun y hy hyx => hmin y (Finset.mem_erase.mpr ⟨hyx, hy⟩)⟩
    rw [Finset.mem_erase] at hy₀
    exact abs_pos.mpr (sub_ne_zero.mpr hy₀.1)
  · refine ⟨1, one_pos, fun y hy hyx => ?_⟩
    exact absurd ⟨y, Finset.mem_erase.mpr ⟨hyx, hy⟩⟩ hne

/-- a singular x-value carries an event -/
theorem s6a_exists_event_of_mem_singX (hx : x₀ ∈ singX F) : ∃ e : Event F, evX F e = x₀ := by
  unfold singX at hx
  rw [Finset.mem_union, Finset.mem_image, Finset.mem_image] at hx
  rcases hx with ⟨p, hp, hpx⟩ | ⟨q, hq, hqx⟩
  · rw [SmoothFront.mem_cuspSet] at hp
    obtain ⟨e, he, -⟩ := exists_event_of_singular F (x₀ := x₀) (p := p) ⟨hp.1, hpx⟩ (Or.inl hp.2)
    exact ⟨e, he⟩
  · have hd := F.isDouble_of_mem_doubleSet hq
    have hq1 := (F.mem_doubleSet.mp hq).1
    obtain ⟨e, he, -⟩ := exists_event_of_singular F (x₀ := x₀) (p := q.1) ⟨hq1, hqx⟩ (Or.inr ⟨q.2, hd⟩)
    exact ⟨e, he⟩

theorem s6a_k0_lt_K (hx : x₀ ∈ singX F) : s6a_k0 F x₀ < s6a_K F x₀ := by
  obtain ⟨e, he⟩ := s6a_exists_event_of_mem_singX F x₀ hx
  have := s6a_evIdx_mem F x₀ he
  omega

/-- the cut at a column of `x₀` -/
theorem s6a_cut_eq {k : ℕ} (hk0 : s6a_k0 F x₀ ≤ k) (hkK : k < s6a_K F x₀) :
    cut (word F) k = hybridCutP F x₀ (fun p => decide (colZ F k ≤ ht F p)) := by
  have hk : k < (events F).length := lt_of_lt_of_le hkK (s6a_K_le F x₀)
  unfold cut
  rw [run_take_eq_hybrid F hk, Option.getD_some, s6a_colX_eq F x₀ hk0 hkK]
  rfl

/-- the cut after a column of `x₀` -/
theorem s6a_cut_succ_eq {k : ℕ} (hk0 : s6a_k0 F x₀ ≤ k) (hkK : k < s6a_K F x₀) :
    cut (word F) (k + 1) = hybridCutP F x₀ (fun p => decide (colZ F k < ht F p)) := by
  have hk : k < (events F).length := lt_of_lt_of_le hkK (s6a_K_le F x₀)
  have hk' : k < (word F).length := by rw [length_word]; exact hk
  have h1 := step_cut (word F) (word_closed F) hk'
  rw [letterAt_word F hk, s6a_cut_eq F x₀ hk0 hkK] at h1
  have h2 := step_hybrid F (eventAt F k)
  have hx : evX F (eventAt F k) = x₀ := s6a_colX_eq F x₀ hk0 hkK
  rw [hx] at h2
  have h3 : hybridCut F x₀ (evZ F (eventAt F k)) = hybridCutP F x₀ (fun p => decide (colZ F k ≤ ht F p)) := rfl
  rw [h3, h1] at h2
  exact Option.some.inj h2

end S6aColumns

/-! #### The window of an event, the bit of an entry, the transport of an entry through a column -/

section S6aWindow

variable (F : SmoothFront) (x₀ : ℝ)

/-- the entries strictly above an event (read "before") -/
def s6a_A (e : Event F) : List (Param F.c × ℕ) :=
  entriesOf F (beforeBits F) ((fibreListBefore F x₀).filter (fun p => decide (evZ F e < ht F p)))
/-- the entries at the event's height, read "before" (the window the letter consumes) -/
def s6a_Eb (e : Event F) : List (Param F.c × ℕ) :=
  entriesOf F (beforeBits F) ((fibreListBefore F x₀).filter (fun p => decide (ht F p = evZ F e)))
/-- the entries at the event's height, read "after" (the window the letter produces) -/
def s6a_Ea (e : Event F) : List (Param F.c × ℕ) :=
  entriesOf F (afterBits F) ((fibreListAfter F x₀).filter (fun p => decide (ht F p = evZ F e)))
/-- the entries strictly below an event (read "after") -/
def s6a_R (e : Event F) : List (Param F.c × ℕ) :=
  entriesOf F (afterBits F) ((fibreListAfter F x₀).filter (fun p => decide (ht F p < evZ F e)))

theorem s6a_hE_le (e : Event F) :
    hybridEntriesP F x₀ (fun p => decide (evZ F e ≤ ht F p)) = s6a_A F x₀ e ++ s6a_Eb F x₀ e ++ s6a_R F x₀ e := by
  unfold hybridEntriesP s6a_A s6a_Eb s6a_R
  rw [s6a_Lb_filter_le, s6a_La_filter_not_le, s6a_entriesOf_append]

theorem s6a_hE_lt (e : Event F) :
    hybridEntriesP F x₀ (fun p => decide (evZ F e < ht F p)) = s6a_A F x₀ e ++ s6a_Ea F x₀ e ++ s6a_R F x₀ e := by
  unfold hybridEntriesP s6a_A s6a_Ea s6a_R
  rw [s6a_La_filter_not_lt, s6a_entriesOf_append, List.append_assoc]

theorem s6a_idx_letterOf (e : Event F) : (letterOf F e).idx = posOf F e := by
  cases e with
  | inl c =>
    show (if F.IsLeftCusp c.1 then Letter.l (posOf F (Sum.inl c)) (decide (0 < F.cuspDisc c.1))
      else Letter.r (posOf F (Sum.inl c))).idx = posOf F (Sum.inl c)
    split_ifs <;> rfl
  | inr q => rfl

theorem s6a_idx_pos (e : Event F) : 1 ≤ (letterOf F e).idx := by
  rw [s6a_idx_letterOf]; unfold posOf; omega

theorem s6a_length_A (e : Event F) (he : evX F e = x₀) : (s6a_A F x₀ e).length = (letterOf F e).idx - 1 := by
  rw [s6a_idx_letterOf]; unfold s6a_A posOf
  rw [he, s6a_length_entriesOf]; omega

theorem s6a_length_Eb (e : Event F) (he : evX F e = x₀) : (s6a_Eb F x₀ e).length = (letterOf F e).arity := by
  unfold s6a_Eb
  rw [s6a_length_entriesOf]
  cases e with
  | inl c =>
    rw [(s6a_filter_ht_cusp F c he).1]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    unfold letterOf beforeBits
    by_cases hl : F.IsLeftCusp c.1
    · simp [hl, Letter.arity]
    · have hr : F.IsRightCusp c.1 := (F.isLeftCusp_or_isRightCusp c.isCusp).resolve_left hl
      simp only [hl, hr, ↓reduceIte, Letter.arity]
      split_ifs <;> rfl
  | inr q =>
    rw [(s6a_filter_ht_cross F q he).1]
    have hd := (F.isOverUnder_of_mem_crossingPairs q.2).1
    obtain ⟨ho, -⟩ := s6a_bits_of_not_cusp F (F.not_isCusp_of_isDouble hd)
    obtain ⟨hu, -⟩ := s6a_bits_of_not_cusp F (F.not_isCusp_of_isDouble hd.symm)
    simp [ho, hu, letterOf, Letter.arity]

theorem s6a_length_Ea (e : Event F) (he : evX F e = x₀) : (s6a_Ea F x₀ e).length = (letterOf F e).coarity := by
  unfold s6a_Ea
  rw [s6a_length_entriesOf]
  cases e with
  | inl c =>
    rw [(s6a_filter_ht_cusp F c he).2]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    unfold letterOf afterBits
    by_cases hl : F.IsLeftCusp c.1
    · have hr : ¬ F.IsRightCusp c.1 := fun hr => left_right_absurd F hl hr
      simp only [hl, hr, ↓reduceIte, Letter.coarity]
      split_ifs <;> rfl
    · have hr : F.IsRightCusp c.1 := (F.isLeftCusp_or_isRightCusp c.isCusp).resolve_left hl
      simp [hl, hr, Letter.coarity]
  | inr q =>
    rw [(s6a_filter_ht_cross F q he).2]
    have hd := (F.isOverUnder_of_mem_crossingPairs q.2).1
    obtain ⟨-, ho⟩ := s6a_bits_of_not_cusp F (F.not_isCusp_of_isDouble hd)
    obtain ⟨-, hu⟩ := s6a_bits_of_not_cusp F (F.not_isCusp_of_isDouble hd.symm)
    simp [ho, hu, letterOf, Letter.coarity]

theorem s6a_Eb_cusp (c : F.Cusp) (he : evX F (Sum.inl c) = x₀) :
    s6a_Eb F x₀ (Sum.inl c) = (List.range (beforeBits F c.1).length).map (fun j => (c.1, j)) := by
  unfold s6a_Eb; rw [(s6a_filter_ht_cusp F c he).1, s6a_entriesOf_cons, s6a_entriesOf_nil, List.append_nil]

theorem s6a_Ea_cusp (c : F.Cusp) (he : evX F (Sum.inl c) = x₀) :
    s6a_Ea F x₀ (Sum.inl c) = (List.range (afterBits F c.1).length).map (fun j => (c.1, j)) := by
  unfold s6a_Ea; rw [(s6a_filter_ht_cusp F c he).2, s6a_entriesOf_cons, s6a_entriesOf_nil, List.append_nil]

theorem s6a_Eb_cross (q : Cross F) (he : evX F (Sum.inr q) = x₀) :
    s6a_Eb F x₀ (Sum.inr q) = [(q.1.1, 0), (q.1.2, 0)] := by
  unfold s6a_Eb; rw [(s6a_filter_ht_cross F q he).1]
  have hd := (F.isOverUnder_of_mem_crossingPairs q.2).1
  obtain ⟨ho, -⟩ := s6a_bits_of_not_cusp F (F.not_isCusp_of_isDouble hd)
  obtain ⟨hu, -⟩ := s6a_bits_of_not_cusp F (F.not_isCusp_of_isDouble hd.symm)
  rw [s6a_entriesOf_cons, s6a_entriesOf_cons, s6a_entriesOf_nil, ho, hu]; rfl

theorem s6a_Ea_cross (q : Cross F) (he : evX F (Sum.inr q) = x₀) :
    s6a_Ea F x₀ (Sum.inr q) = [(q.1.2, 0), (q.1.1, 0)] := by
  unfold s6a_Ea; rw [(s6a_filter_ht_cross F q he).2]
  have hd := (F.isOverUnder_of_mem_crossingPairs q.2).1
  obtain ⟨-, ho⟩ := s6a_bits_of_not_cusp F (F.not_isCusp_of_isDouble hd)
  obtain ⟨-, hu⟩ := s6a_bits_of_not_cusp F (F.not_isCusp_of_isDouble hd.symm)
  rw [s6a_entriesOf_cons, s6a_entriesOf_cons, s6a_entriesOf_nil, ho, hu]; rfl

theorem s6a_ht_of_mem_Eb {e : Event F} {a : Param F.c × ℕ} (ha : a ∈ s6a_Eb F x₀ e) : ht F a.1 = evZ F e := by
  unfold s6a_Eb at ha; rw [s6a_mem_entriesOf, List.mem_filter, decide_eq_true_iff] at ha; exact ha.1.2

theorem s6a_ht_of_mem_Ea {e : Event F} {a : Param F.c × ℕ} (ha : a ∈ s6a_Ea F x₀ e) : ht F a.1 = evZ F e := by
  unfold s6a_Ea at ha; rw [s6a_mem_entriesOf, List.mem_filter, decide_eq_true_iff] at ha; exact ha.1.2

/-- the bits of a hybrid cut are the entry bits of its entries -/
theorem s6a_hybridCutP_eq_map (P : Param F.c → Bool) :
    hybridCutP F x₀ P =
      (entriesOf F (beforeBits F) ((fibreListBefore F x₀).filter P)).map (entryBit F (beforeBits F)) ++
      (entriesOf F (afterBits F) ((fibreListAfter F x₀).filter (fun p => !P p))).map (entryBit F (afterBits F)) := by
  unfold hybridCutP; rw [map_entryBit_entriesOf, map_entryBit_entriesOf]

theorem s6a_length_hybridCutP (P : Param F.c → Bool) :
    (hybridCutP F x₀ P).length = (hybridEntriesP F x₀ P).length := by
  rw [s6a_hybridCutP_eq_map]; unfold hybridEntriesP; simp only [List.length_append, List.length_map]

theorem s6a_bit_of_entry (P : Param F.c → Bool) {J : ℕ} (hJ : J < (hybridEntriesP F x₀ P).length) :
    (hybridCutP F x₀ P).getD J false =
      (if P (hybridEntriesP F x₀ P)[J].1 = true then entryBit F (beforeBits F) (hybridEntriesP F x₀ P)[J]
       else entryBit F (afterBits F) (hybridEntriesP F x₀ P)[J]) := by
  have hJ' : J < (hybridCutP F x₀ P).length := by rw [s6a_length_hybridCutP]; exact hJ
  rw [List.getD_eq_getElem _ _ hJ']
  have hcut := s6a_hybridCutP_eq_map F x₀ P
  have hent : hybridEntriesP F x₀ P = entriesOf F (beforeBits F) ((fibreListBefore F x₀).filter P) ++
      entriesOf F (afterBits F) ((fibreListAfter F x₀).filter (fun p => !P p)) := rfl
  have hlen : J < (entriesOf F (beforeBits F) ((fibreListBefore F x₀).filter P) ++
      entriesOf F (afterBits F) ((fibreListAfter F x₀).filter (fun p => !P p))).length := by
    rw [← hent]; exact hJ
  rw [List.getElem_of_eq hcut hJ', List.getElem_of_eq hent hJ]
  rcases Nat.lt_or_ge J (entriesOf F (beforeBits F) ((fibreListBefore F x₀).filter P)).length with h | h
  · rw [List.getElem_append_left (by simpa using h), List.getElem_append_left h, List.getElem_map]
    obtain ⟨⟨-, hP⟩, -⟩ := ((s6a_mem_entriesOf F).mp (List.getElem_mem h)).imp_left List.mem_filter.mp
    simp only [hP, ↓reduceIte]
  · have h' : (List.map (entryBit F (beforeBits F))
        (entriesOf F (beforeBits F) ((fibreListBefore F x₀).filter P))).length ≤ J := by simpa using h
    rw [List.getElem_append_right h', List.getElem_append_right h, List.getElem_map]
    have hJ2 : J - (entriesOf F (beforeBits F) ((fibreListBefore F x₀).filter P)).length <
        (entriesOf F (afterBits F) ((fibreListAfter F x₀).filter (fun p => !P p))).length := by
      rw [List.length_append] at hlen; omega
    obtain ⟨⟨-, hP⟩, -⟩ := ((s6a_mem_entriesOf F).mp (List.getElem_mem hJ2)).imp_left List.mem_filter.mp
    rw [Bool.not_eq_true'] at hP
    simp only [List.length_map, hP, Bool.false_eq_true, ↓reduceIte]

/-- transport of an entry (not in the window) rightward through the column of `e` -/
theorem s6a_step_right (e : Event F) (he : evX F e = x₀) {J : ℕ}
    (hJ : J < (s6a_A F x₀ e ++ s6a_Eb F x₀ e ++ s6a_R F x₀ e).length)
    (hne : ht F ((s6a_A F x₀ e ++ s6a_Eb F x₀ e ++ s6a_R F x₀ e)[J]).1 ≠ evZ F e) :
    ∃ J', ∃ hJ' : J' < (s6a_A F x₀ e ++ s6a_Ea F x₀ e ++ s6a_R F x₀ e).length,
      (s6a_A F x₀ e ++ s6a_Ea F x₀ e ++ s6a_R F x₀ e)[J'] = (s6a_A F x₀ e ++ s6a_Eb F x₀ e ++ s6a_R F x₀ e)[J] ∧
      (letterOf F e).posR (J + 1) = some (J' + 1) ∧
      (J + 1 < (letterOf F e).idx ∨ (letterOf F e).idx + (letterOf F e).arity ≤ J + 1) := by
  have hA := s6a_length_A F x₀ e he
  have hEb := s6a_length_Eb F x₀ e he
  have hEa := s6a_length_Ea F x₀ e he
  have hidx := s6a_idx_pos F e
  rcases s6a_getElem_three _ _ _ J hJ with ⟨h, hEq⟩ | ⟨h, hEq⟩ | ⟨h, hEq⟩
  · refine ⟨J, by simp; omega, ?_, ?_, Or.inl (by omega)⟩
    · rw [hEq, s6a_getElem_A _ _ _ J h]
    · exact posR_of_lt (by omega)
  · exfalso
    apply hne
    rw [hEq]
    exact s6a_ht_of_mem_Eb F x₀ (List.getElem_mem _)
  · refine ⟨(s6a_A F x₀ e).length + (s6a_Ea F x₀ e).length + (J - ((s6a_A F x₀ e).length + (s6a_Eb F x₀ e).length)),
      by simp at hJ ⊢; omega, ?_, ?_, Or.inr (by omega)⟩
    · rw [hEq, s6a_getElem_R]
    · rw [posR_of_ge (by omega)]
      congr 1
      omega

/-- transport of an entry (not in the window) leftward through the column of `e` -/
theorem s6a_step_left (e : Event F) (he : evX F e = x₀) {J : ℕ}
    (hJ : J < (s6a_A F x₀ e ++ s6a_Ea F x₀ e ++ s6a_R F x₀ e).length)
    (hne : ht F ((s6a_A F x₀ e ++ s6a_Ea F x₀ e ++ s6a_R F x₀ e)[J]).1 ≠ evZ F e) :
    ∃ J', ∃ hJ' : J' < (s6a_A F x₀ e ++ s6a_Eb F x₀ e ++ s6a_R F x₀ e).length,
      (s6a_A F x₀ e ++ s6a_Eb F x₀ e ++ s6a_R F x₀ e)[J'] = (s6a_A F x₀ e ++ s6a_Ea F x₀ e ++ s6a_R F x₀ e)[J] ∧
      (letterOf F e).posL (J + 1) = some (J' + 1) ∧
      (J + 1 < (letterOf F e).idx ∨ (letterOf F e).idx + (letterOf F e).coarity ≤ J + 1) := by
  have hA := s6a_length_A F x₀ e he
  have hEb := s6a_length_Eb F x₀ e he
  have hEa := s6a_length_Ea F x₀ e he
  have hidx := s6a_idx_pos F e
  rcases s6a_getElem_three _ _ _ J hJ with ⟨h, hEq⟩ | ⟨h, hEq⟩ | ⟨h, hEq⟩
  · refine ⟨J, by simp; omega, ?_, ?_, Or.inl (by omega)⟩
    · rw [hEq, s6a_getElem_A _ _ _ J h]
    · exact posL_of_lt (by omega)
  · exfalso
    apply hne
    rw [hEq]
    exact s6a_ht_of_mem_Ea F x₀ (List.getElem_mem _)
  · refine ⟨(s6a_A F x₀ e).length + (s6a_Eb F x₀ e).length + (J - ((s6a_A F x₀ e).length + (s6a_Ea F x₀ e).length)),
      by simp at hJ ⊢; omega, ?_, ?_, Or.inr (by omega)⟩
    · rw [hEq, s6a_getElem_R]
    · rw [posL_of_ge (by omega)]
      congr 1
      omega

end S6aWindow

/-! #### Slots that are not `σ` slots -/

section S6aNotSigma

variable (F : SmoothFront)

theorem s6a_σSlotA_val {k m : ℕ} (hk : k < (word F).length) (hℓ : letterAt (word F) k = .σ m) :
    (σSlotA (word_closed F) hk hℓ).1 = if bit (word F) k m then (k, m) else (k + 1, m + 1) := by
  unfold σSlotA; split_ifs <;> rfl

theorem s6a_σSlotB_val {k m : ℕ} (hk : k < (word F).length) (hℓ : letterAt (word F) k = .σ m) :
    (σSlotB (word_closed F) hk hℓ).1 = if bit (word F) k (m + 1) then (k, m + 1) else (k + 1, m) := by
  unfold σSlotB; split_ifs <;> rfl

/-- a rightward cut slot outside the window of a crossing letter is not a `σ` slot -/
theorem s6a_not_σ_right {u : Slot (word F)} {k p : ℕ} (hu : u.1 = (k, p)) (hp : p ≠ 0)
    (hb : bit (word F) k p = true)
    (h : p < (letterAt (word F) k).idx ∨ (letterAt (word F) k).idx + (letterAt (word F) k).arity ≤ p) :
    ¬ U2.IsσSlot u := by
  intro hσ
  obtain ⟨k', m, hk', hℓ', hu'⟩ := (U2.isσSlot_iff (word_closed F) u).mp hσ
  obtain ⟨hm1, -, -, hb1, hb2⟩ := σ_facts (word_closed F) hk' hℓ'
  rcases hu' with rfl | rfl
  · rw [s6a_σSlotA_val] at hu
    split_ifs at hu with hbm
    · simp only [Prod.mk.injEq] at hu
      obtain ⟨rfl, rfl⟩ := hu
      rw [hℓ'] at h; simp only [Letter.idx, Letter.arity] at h; omega
    · simp only [Prod.mk.injEq] at hu
      obtain ⟨rfl, rfl⟩ := hu
      rw [hb1] at hb
      simp [hbm] at hb
  · rw [s6a_σSlotB_val] at hu
    split_ifs at hu with hbm
    · simp only [Prod.mk.injEq] at hu
      obtain ⟨rfl, rfl⟩ := hu
      rw [hℓ'] at h; simp only [Letter.idx, Letter.arity] at h; omega
    · simp only [Prod.mk.injEq] at hu
      obtain ⟨rfl, rfl⟩ := hu
      rw [hb2] at hb
      simp [hbm] at hb

/-- a leftward cut slot outside the window of a crossing letter is not a `σ` slot -/
theorem s6a_not_σ_left {u : Slot (word F)} {k p : ℕ} (hu : u.1 = (k + 1, p)) (hp : p ≠ 0)
    (hb : bit (word F) (k + 1) p = false)
    (h : p < (letterAt (word F) k).idx ∨ (letterAt (word F) k).idx + (letterAt (word F) k).coarity ≤ p) :
    ¬ U2.IsσSlot u := by
  intro hσ
  obtain ⟨k', m, hk', hℓ', hu'⟩ := (U2.isσSlot_iff (word_closed F) u).mp hσ
  obtain ⟨hm1, -, -, hb1, hb2⟩ := σ_facts (word_closed F) hk' hℓ'
  rcases hu' with rfl | rfl
  · rw [s6a_σSlotA_val] at hu
    split_ifs at hu with hbm
    · simp only [Prod.mk.injEq] at hu
      obtain ⟨hk, rfl⟩ := hu
      subst hk
      rw [hbm] at hb
      exact Bool.noConfusion hb
    · simp only [Prod.mk.injEq, Nat.add_right_cancel_iff] at hu
      obtain ⟨rfl, rfl⟩ := hu
      rw [hℓ'] at h; simp only [Letter.idx, Letter.coarity] at h; omega
  · rw [s6a_σSlotB_val] at hu
    split_ifs at hu with hbm
    · simp only [Prod.mk.injEq] at hu
      obtain ⟨hk, rfl⟩ := hu
      subst hk
      rw [hbm] at hb
      exact Bool.noConfusion hb
    · simp only [Prod.mk.injEq, Nat.add_right_cancel_iff] at hu
      obtain ⟨rfl, rfl⟩ := hu
      rw [hℓ'] at h; simp only [Letter.idx, Letter.coarity] at h; omega

/-- a cusp vertex is not a `σ` slot -/
theorem s6a_not_σ_vertex {u : Slot (word F)} {k : ℕ} (hu : u.1 = (k, 0)) : ¬ U2.IsσSlot u := by
  intro hσ
  obtain ⟨k', m, hk', hℓ', hu'⟩ := (U2.isσSlot_iff (word_closed F) u).mp hσ
  obtain ⟨hm1, -⟩ := σ_facts (word_closed F) hk' hℓ'
  rcases hu' with rfl | rfl
  · rw [s6a_σSlotA_val] at hu; split_ifs at hu <;> simp only [Prod.mk.injEq] at hu <;> omega
  · rw [s6a_σSlotB_val] at hu; split_ifs at hu <;> simp only [Prod.mk.injEq] at hu <;> omega

end S6aNotSigma

/-! #### The entries at each column of one x-value and the walk through its columns -/

section S6aWalk

variable (F : SmoothFront) (x₀ : ℝ)

/-- the strand entries at the cut line `k` of `x₀`, for `k0 ≤ k ≤ K` -/
def s6a_entCol (k : ℕ) : List (Param F.c × ℕ) :=
  if k < s6a_K F x₀ then hybridEntriesP F x₀ (fun p => decide (colZ F k ≤ ht F p))
  else hybridEntriesP F x₀ (fun p => decide (colZ F (s6a_K F x₀ - 1) < ht F p))

theorem s6a_entCol_of_lt {k : ℕ} (hk : k < s6a_K F x₀) :
    s6a_entCol F x₀ k = hybridEntriesP F x₀ (fun p => decide (colZ F k ≤ ht F p)) := ite_eq_left hk

theorem s6a_entCol_K :
    s6a_entCol F x₀ (s6a_K F x₀) = hybridEntriesP F x₀ (fun p => decide (colZ F (s6a_K F x₀ - 1) < ht F p)) :=
  ite_eq_right (lt_irrefl _)

theorem s6a_regular_between {k : ℕ} (hk0 : s6a_k0 F x₀ ≤ k) (hkK : k + 1 < s6a_K F x₀) {p : Param F.c}
    (hp : p ∈ totalFibre F x₀) (h1 : colZ F k < ht F p) (h2 : ht F p < colZ F (k + 1)) :
    ¬ F.IsCusp p ∧ ∀ q, ¬ F.IsDouble p q := by
  apply s6a_regular_of_no_event F hp
  intro e he hz
  obtain ⟨hk0', hkK'⟩ := s6a_evIdx_mem F x₀ he
  rw [s6a_evZ_eq_colZ] at hz
  rcases Nat.lt_or_ge (evIdx F e) (k + 1) with h | h
  · have := s6a_colZ_le F x₀ hk0' (by omega : evIdx F e ≤ k) (by omega); linarith
  · have := s6a_colZ_le F x₀ (by omega : s6a_k0 F x₀ ≤ k + 1) h hkK'; linarith

theorem s6a_regular_below {p : Param F.c} (hp : p ∈ totalFibre F x₀)
    (h : ht F p < colZ F (s6a_k0 F x₀)) : ¬ F.IsCusp p ∧ ∀ q, ¬ F.IsDouble p q := by
  apply s6a_regular_of_no_event F hp
  intro e he hz
  obtain ⟨hk0', hkK'⟩ := s6a_evIdx_mem F x₀ he
  rw [s6a_evZ_eq_colZ] at hz
  have := s6a_colZ_le F x₀ le_rfl hk0' hkK'
  linarith

theorem s6a_regular_above (hx : x₀ ∈ singX F) {p : Param F.c} (hp : p ∈ totalFibre F x₀)
    (h : colZ F (s6a_K F x₀ - 1) < ht F p) : ¬ F.IsCusp p ∧ ∀ q, ¬ F.IsDouble p q := by
  apply s6a_regular_of_no_event F hp
  intro e he hz
  obtain ⟨hk0', hkK'⟩ := s6a_evIdx_mem F x₀ he
  rw [s6a_evZ_eq_colZ] at hz
  have hK := s6a_k0_lt_K F x₀ hx
  have := s6a_colZ_le F x₀ hk0' (by omega : evIdx F e ≤ s6a_K F x₀ - 1) (by omega)
  linarith

theorem s6a_entCol_succ {k : ℕ} (hk0 : s6a_k0 F x₀ ≤ k) (hkK : k < s6a_K F x₀) :
    s6a_entCol F x₀ (k + 1) = hybridEntriesP F x₀ (fun p => decide (colZ F k < ht F p)) := by
  unfold s6a_entCol
  split_ifs with h
  · symm
    apply s6a_hybridEntriesP_eq
    · intro p q hpq hq; simp only [decide_eq_true_iff] at hq ⊢; exact lt_of_lt_of_le hq hpq
    · intro p q hpq hq; simp only [decide_eq_true_iff] at hq ⊢; exact le_trans hq hpq
    · intro p hp; simp only [decide_eq_true_iff] at hp ⊢
      exact lt_of_lt_of_le (s6a_colZ_lt F x₀ hk0 (Nat.lt_succ_self k) h) hp
    · intro p hp h1 h2
      simp only [decide_eq_true_iff, decide_eq_false_iff_not, not_le] at h1 h2
      exact s6a_regular_between F x₀ hk0 h hp h1 h2
  · have : s6a_K F x₀ - 1 = k := by omega
    rw [this]

theorem s6a_entCol_k0 (hx : x₀ ∈ singX F) : s6a_entCol F x₀ (s6a_k0 F x₀) = entriesBefore F x₀ := by
  rw [s6a_entCol_of_lt F x₀ (s6a_k0_lt_K F x₀ hx)]
  have h0 : entriesBefore F x₀ = hybridEntriesP F x₀ (fun _ => true) := by
    unfold entriesBefore hybridEntriesP
    simp [s6a_entriesOf_nil]
  rw [h0]
  symm
  apply s6a_hybridEntriesP_eq
  · intros; rfl
  · intro p q hpq hq; simp only [decide_eq_true_iff] at hq ⊢; exact le_trans hq hpq
  · intros; rfl
  · intro p hp _ h2
    simp only [decide_eq_false_iff_not, not_le] at h2
    exact s6a_regular_below F x₀ hp h2

theorem s6a_entCol_K_eq (hx : x₀ ∈ singX F) : s6a_entCol F x₀ (s6a_K F x₀) = entriesAfter F x₀ := by
  rw [s6a_entCol_K]
  have h0 : entriesAfter F x₀ = hybridEntriesP F x₀ (fun _ => false) := by
    unfold entriesAfter hybridEntriesP
    simp [s6a_entriesOf_nil]
  rw [h0]
  apply s6a_hybridEntriesP_eq
  · intro p q hpq hq; simp only [decide_eq_true_iff] at hq ⊢; exact lt_of_lt_of_le hq hpq
  · intros; simp_all
  · intro p h; simp at h
  · intro p hp h1 _
    simp only [decide_eq_true_iff] at h1
    exact s6a_regular_above F x₀ hx hp h1

/-- one `next` step rightward through column `k` for an entry outside the window -/
theorem s6a_next_right_step {k : ℕ} (hk0 : s6a_k0 F x₀ ≤ k) (hkK : k < s6a_K F x₀) {J : ℕ} {a : Param F.c × ℕ}
    (hJ : J < (s6a_entCol F x₀ k).length) (ha : (s6a_entCol F x₀ k)[J] = a)
    (hne : ht F a.1 ≠ colZ F k)
    (hbit : (if colZ F k ≤ ht F a.1 then entryBit F (beforeBits F) a else entryBit F (afterBits F) a) = true)
    (u : Slot (word F)) (hu : u.1 = (k, J + 1)) :
    ∃ J', ∃ hJ' : J' < (s6a_entCol F x₀ (k + 1)).length, (s6a_entCol F x₀ (k + 1))[J'] = a ∧
      (next (word_closed F) u).1 = (k + 1, J' + 1) ∧ ¬ U2.IsσSlot u := by
  have hk : k < (events F).length := lt_of_lt_of_le hkK (s6a_K_le F x₀)
  set e := eventAt F k with he_def
  have he : evX F e = x₀ := s6a_colX_eq F x₀ hk0 hkK
  have hz : evZ F e = colZ F k := rfl
  have hcol : s6a_entCol F x₀ k = s6a_A F x₀ e ++ s6a_Eb F x₀ e ++ s6a_R F x₀ e := by
    rw [s6a_entCol_of_lt F x₀ hkK, ← hz, s6a_hE_le]
  have hcol' : s6a_entCol F x₀ (k + 1) = s6a_A F x₀ e ++ s6a_Ea F x₀ e ++ s6a_R F x₀ e := by
    rw [s6a_entCol_succ F x₀ hk0 hkK, ← hz, s6a_hE_lt]
  have hJ1 : J < (s6a_A F x₀ e ++ s6a_Eb F x₀ e ++ s6a_R F x₀ e).length := by rw [← hcol]; exact hJ
  have ha1 : (s6a_A F x₀ e ++ s6a_Eb F x₀ e ++ s6a_R F x₀ e)[J] = a := by
    rw [← List.getElem_of_eq hcol hJ]; exact ha
  have hbitk : bit (word F) k (J + 1) = true := by
    have hJ2 : J < (hybridEntriesP F x₀ (fun p => decide (colZ F k ≤ ht F p))).length := by
      rw [← s6a_entCol_of_lt F x₀ hkK]; exact hJ
    have h1 := s6a_bit_of_entry F x₀ (fun p => decide (colZ F k ≤ ht F p)) hJ2
    have ha2 : (hybridEntriesP F x₀ (fun p => decide (colZ F k ≤ ht F p)))[J] = a := by
      rw [← List.getElem_of_eq (s6a_entCol_of_lt F x₀ hkK) hJ]; exact ha
    rw [bit_eq, Nat.add_sub_cancel, s6a_cut_eq F x₀ hk0 hkK, h1, ha2]
    simpa [decide_eq_true_iff] using hbit
  have hne' : ht F ((s6a_A F x₀ e ++ s6a_Eb F x₀ e ++ s6a_R F x₀ e)[J]).1 ≠ evZ F e := by
    rw [ha1, hz]; exact hne
  obtain ⟨J', hJ', hJ'a, hpos, hreg⟩ := s6a_step_right F x₀ e he hJ1 hne'
  refine ⟨J', by rw [hcol']; exact hJ', ?_, ?_, ?_⟩
  · rw [List.getElem_of_eq hcol', hJ'a, ha1]
  · rw [next_val, hu]
    rw [nextPair_right (word F) (Nat.succ_ne_zero J) hbitk (by rw [letterAt_word F hk]; exact hpos)]
  · apply s6a_not_σ_right F hu (Nat.succ_ne_zero J) hbitk
    rw [letterAt_word F hk]
    exact hreg

/-- one `next` step leftward through column `k` (from cut `k+1` to cut `k`) for an entry outside the window -/
theorem s6a_next_left_step {k : ℕ} (hk0 : s6a_k0 F x₀ ≤ k) (hkK : k < s6a_K F x₀) {J : ℕ} {a : Param F.c × ℕ}
    (hJ : J < (s6a_entCol F x₀ (k + 1)).length) (ha : (s6a_entCol F x₀ (k + 1))[J] = a)
    (hne : ht F a.1 ≠ colZ F k)
    (hbit : (if colZ F k < ht F a.1 then entryBit F (beforeBits F) a else entryBit F (afterBits F) a) = false)
    (u : Slot (word F)) (hu : u.1 = (k + 1, J + 1)) :
    ∃ J', ∃ hJ' : J' < (s6a_entCol F x₀ k).length, (s6a_entCol F x₀ k)[J'] = a ∧
      (next (word_closed F) u).1 = (k, J' + 1) ∧ ¬ U2.IsσSlot u := by
  have hk : k < (events F).length := lt_of_lt_of_le hkK (s6a_K_le F x₀)
  set e := eventAt F k with he_def
  have he : evX F e = x₀ := s6a_colX_eq F x₀ hk0 hkK
  have hz : evZ F e = colZ F k := rfl
  have hcol : s6a_entCol F x₀ k = s6a_A F x₀ e ++ s6a_Eb F x₀ e ++ s6a_R F x₀ e := by
    rw [s6a_entCol_of_lt F x₀ hkK, ← hz, s6a_hE_le]
  have hcol' : s6a_entCol F x₀ (k + 1) = s6a_A F x₀ e ++ s6a_Ea F x₀ e ++ s6a_R F x₀ e := by
    rw [s6a_entCol_succ F x₀ hk0 hkK, ← hz, s6a_hE_lt]
  have hJ1 : J < (s6a_A F x₀ e ++ s6a_Ea F x₀ e ++ s6a_R F x₀ e).length := by rw [← hcol']; exact hJ
  have ha1 : (s6a_A F x₀ e ++ s6a_Ea F x₀ e ++ s6a_R F x₀ e)[J] = a := by
    rw [← List.getElem_of_eq hcol' hJ]; exact ha
  have hbitk : bit (word F) (k + 1) (J + 1) = false := by
    have hJ2 : J < (hybridEntriesP F x₀ (fun p => decide (colZ F k < ht F p))).length := by
      rw [← s6a_entCol_succ F x₀ hk0 hkK]; exact hJ
    have h1 := s6a_bit_of_entry F x₀ (fun p => decide (colZ F k < ht F p)) hJ2
    have ha2 : (hybridEntriesP F x₀ (fun p => decide (colZ F k < ht F p)))[J] = a := by
      rw [← List.getElem_of_eq (s6a_entCol_succ F x₀ hk0 hkK) hJ]; exact ha
    rw [bit_eq, Nat.add_sub_cancel, s6a_cut_succ_eq F x₀ hk0 hkK, h1, ha2]
    simpa [decide_eq_true_iff] using hbit
  have hne' : ht F ((s6a_A F x₀ e ++ s6a_Ea F x₀ e ++ s6a_R F x₀ e)[J]).1 ≠ evZ F e := by
    rw [ha1, hz]; exact hne
  obtain ⟨J', hJ', hJ'a, hpos, hreg⟩ := s6a_step_left F x₀ e he hJ1 hne'
  refine ⟨J', by rw [hcol]; exact hJ', ?_, ?_, ?_⟩
  · rw [List.getElem_of_eq hcol, hJ'a, ha1]
  · rw [next_val, hu]
    rw [nextPair_left (word F) (Nat.succ_ne_zero J) hbitk
      (by rw [Nat.add_sub_cancel, letterAt_word F hk]; exact hpos), Nat.add_sub_cancel]
  · apply s6a_not_σ_left F hu (Nat.succ_ne_zero J) hbitk
    rw [letterAt_word F hk]
    exact hreg

/-- the rightward walk through the columns `k, …, k + d - 1` of `x₀` -/
theorem s6a_walk_right (a : Param F.c × ℕ) :
    ∀ d k, s6a_k0 F x₀ ≤ k → k + d ≤ s6a_K F x₀ →
      (∀ k', k ≤ k' → k' < k + d → ht F a.1 ≠ colZ F k') →
      (∀ k', k ≤ k' → k' < k + d →
        (if colZ F k' ≤ ht F a.1 then entryBit F (beforeBits F) a else entryBit F (afterBits F) a) = true) →
      ∀ J (hJ : J < (s6a_entCol F x₀ k).length), (s6a_entCol F x₀ k)[J] = a →
      ∀ u : Slot (word F), u.1 = (k, J + 1) →
      ∃ J', ∃ hJ' : J' < (s6a_entCol F x₀ (k + d)).length, (s6a_entCol F x₀ (k + d))[J'] = a ∧
        ((next (word_closed F))^[d] u).1 = (k + d, J' + 1) ∧
        ∀ j < d, ¬ U2.IsσSlot ((next (word_closed F))^[j] u) := by
  intro d
  induction d with
  | zero =>
    intro k hk0 hkK hne hbit J hJ ha u hu
    exact ⟨J, hJ, ha, by simpa using hu, fun j hj => absurd hj (Nat.not_lt_zero _)⟩
  | succ d ih =>
    intro k hk0 hkK hne hbit J hJ ha u hu
    have hkK' : k < s6a_K F x₀ := by omega
    obtain ⟨J₁, hJ₁, ha₁, hnext, hσ⟩ := s6a_next_right_step F x₀ hk0 hkK' hJ ha (hne k le_rfl (by omega))
      (hbit k le_rfl (by omega)) u hu
    obtain ⟨J', hJ', ha', hpath, hσ'⟩ := ih (k + 1) (by omega) (by omega)
      (fun k' h1 h2 => hne k' (by omega) (by omega)) (fun k' h1 h2 => hbit k' (by omega) (by omega))
      J₁ hJ₁ ha₁ (next (word_closed F) u) hnext
    refine ⟨J', by rw [show k + (d + 1) = k + 1 + d by omega]; exact hJ', ?_, ?_, ?_⟩
    · rw [List.getElem_of_eq (show s6a_entCol F x₀ (k + (d + 1)) = s6a_entCol F x₀ (k + 1 + d) by
        rw [show k + (d + 1) = k + 1 + d by omega])]
      exact ha'
    · rw [Function.iterate_succ_apply, hpath]; congr 1; omega
    · intro j hj
      rcases j with _ | j
      · simpa using hσ
      · rw [Function.iterate_succ_apply]; exact hσ' j (by omega)

/-- the leftward walk through the columns `k + d - 1, …, k` of `x₀` (from cut `k + d` to cut `k`) -/
theorem s6a_walk_left (a : Param F.c × ℕ) :
    ∀ d k, s6a_k0 F x₀ ≤ k → k + d ≤ s6a_K F x₀ →
      (∀ k', k ≤ k' → k' < k + d → ht F a.1 ≠ colZ F k') →
      (∀ k', k ≤ k' → k' < k + d →
        (if colZ F k' < ht F a.1 then entryBit F (beforeBits F) a else entryBit F (afterBits F) a) = false) →
      ∀ J (hJ : J < (s6a_entCol F x₀ (k + d)).length), (s6a_entCol F x₀ (k + d))[J] = a →
      ∀ u : Slot (word F), u.1 = (k + d, J + 1) →
      ∃ J', ∃ hJ' : J' < (s6a_entCol F x₀ k).length, (s6a_entCol F x₀ k)[J'] = a ∧
        ((next (word_closed F))^[d] u).1 = (k, J' + 1) ∧
        ∀ j < d, ¬ U2.IsσSlot ((next (word_closed F))^[j] u) := by
  intro d
  induction d with
  | zero =>
    intro k hk0 hkK hne hbit J hJ ha u hu
    exact ⟨J, hJ, ha, by simpa using hu, fun j hj => absurd hj (Nat.not_lt_zero _)⟩
  | succ d ih =>
    intro k hk0 hkK hne hbit J hJ ha u hu
    have hkd : k + d < s6a_K F x₀ := by omega
    have hJ0 : J < (s6a_entCol F x₀ (k + d + 1)).length := by
      rw [show k + d + 1 = k + (d + 1) by omega]; exact hJ
    have ha0 : (s6a_entCol F x₀ (k + d + 1))[J] = a := by
      rw [List.getElem_of_eq (show s6a_entCol F x₀ (k + d + 1) = s6a_entCol F x₀ (k + (d + 1)) by
        rw [show k + d + 1 = k + (d + 1) by omega])]
      exact ha
    obtain ⟨J₁, hJ₁, ha₁, hnext, hσ⟩ := s6a_next_left_step F x₀ (by omega : s6a_k0 F x₀ ≤ k + d) hkd hJ0 ha0
      (hne (k + d) (by omega) (by omega)) (hbit (k + d) (by omega) (by omega)) u
      (by rw [hu]; rfl)
    obtain ⟨J', hJ', ha', hpath, hσ'⟩ := ih k hk0 (by omega)
      (fun k' h1 h2 => hne k' (by omega) (by omega)) (fun k' h1 h2 => hbit k' (by omega) (by omega))
      J₁ hJ₁ ha₁ (next (word_closed F) u) hnext
    refine ⟨J', hJ', ha', ?_, ?_⟩
    · rw [Function.iterate_succ_apply, hpath]
    · intro j hj
      rcases j with _ | j
      · simpa using hσ
      · rw [Function.iterate_succ_apply]; exact hσ' j (by omega)

end S6aWalk

/-! #### Cusp-free intervals, injectivity of `x`, and the identification of a continued entry -/

section S6aAnalytic

variable (F : SmoothFront)

/-- no cusp strictly between `s` and `t` -/
def s6a_Free (i : Fin F.c) (s t : ℝ) : Prop :=
  ∀ u, (s < u ∧ u < t) ∨ (t < u ∧ u < s) → ¬ F.IsCusp (i, u)

theorem s6a_between_iff {s t u : ℝ} : (min s t < u ∧ u < max s t) ↔ (s < u ∧ u < t) ∨ (t < u ∧ u < s) := by
  rcases le_total s t with h | h
  · rw [min_eq_left h, max_eq_right h]
    constructor
    · rintro ⟨h1, h2⟩; exact Or.inl ⟨h1, h2⟩
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact ⟨h1, h2⟩
      · exact ⟨by linarith, by linarith⟩
  · rw [min_eq_right h, max_eq_left h]
    constructor
    · rintro ⟨h1, h2⟩; exact Or.inr ⟨h1, h2⟩
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact ⟨by linarith, by linarith⟩
      · exact ⟨h1, h2⟩

theorem s6a_Free_of_minmax {i : Fin F.c} {s t : ℝ}
    (h : ∀ u, min s t < u → u < max s t → ¬ F.IsCusp (i, u)) : s6a_Free F i s t :=
  fun u hu => h u (s6a_between_iff.mpr hu).1 (s6a_between_iff.mpr hu).2

theorem s6a_Free_symm {i : Fin F.c} {s t : ℝ} (h : s6a_Free F i s t) : s6a_Free F i t s :=
  fun u hu => h u hu.symm

/-- cusp-free intervals join across a non-cusp point (for any position of the point) -/
theorem s6a_Free_join {i : Fin F.c} {s m t : ℝ} (h1 : s6a_Free F i s m) (h2 : s6a_Free F i m t)
    (hm : ¬ F.IsCusp (i, m)) : s6a_Free F i s t := by
  intro u hu
  by_cases hum : u = m
  · rw [hum]; exact hm
  · rcases hu with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;> rcases lt_or_gt_of_ne hum with h | h
    · exact h1 u (Or.inl ⟨h3, h⟩)
    · exact h2 u (Or.inl ⟨h, h4⟩)
    · exact h2 u (Or.inr ⟨h3, h⟩)
    · exact h1 u (Or.inr ⟨h, h4⟩)

/-- cusp-free intervals join across a point when both ends lie on the same side of it -/
theorem s6a_Free_same_side {i : Fin F.c} {β τ σ : ℝ} (h1 : s6a_Free F i β τ) (h2 : s6a_Free F i τ σ)
    (hside : β < τ ↔ σ < τ) : s6a_Free F i β σ := by
  intro u hu
  by_cases hβ : β < τ
  · have hσ : σ < τ := hside.mp hβ
    rcases hu with ⟨h3, h4⟩ | ⟨h3, h4⟩
    · exact h1 u (Or.inl ⟨h3, by linarith⟩)
    · exact h2 u (Or.inr ⟨h3, by linarith⟩)
  · have hσ : ¬ σ < τ := fun h => hβ (hside.mpr h)
    rw [not_lt] at hβ hσ
    rcases hu with ⟨h3, h4⟩ | ⟨h3, h4⟩
    · exact h2 u (Or.inl ⟨by linarith, h4⟩)
    · exact h1 u (Or.inr ⟨by linarith, h4⟩)

theorem s6a_injOn_x {i : Fin F.c} {a b : ℝ} (hab : a ≤ b) (hfree : ∀ u, a < u → u < b → ¬ F.IsCusp (i, u)) :
    Set.InjOn (xOf F i) (Set.Icc a b) := by
  intro s hs t ht hst
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · obtain ⟨u, hu, hu0⟩ := exists_hasDerivAt_eq_zero h ((F.comp i).continuous.fst).continuousOn hst
      (fun x _ => hasDerivAt_x F i x)
    exact hfree u (lt_of_le_of_lt hs.1 hu.1) (lt_of_lt_of_le hu.2 ht.2) ((isCusp_iff_xvel_eq_zero F i u).mpr hu0)
  · obtain ⟨u, hu, hu0⟩ := exists_hasDerivAt_eq_zero h ((F.comp i).continuous.fst).continuousOn hst.symm
      (fun x _ => hasDerivAt_x F i x)
    exact hfree u (lt_of_le_of_lt ht.1 hu.1) (lt_of_lt_of_le hu.2 hs.2) ((isCusp_iff_xvel_eq_zero F i u).mpr hu0)

theorem s6a_x_inj_of_Free {i : Fin F.c} {s t : ℝ} (hfree : s6a_Free F i s t) (h : xOf F i s = xOf F i t) :
    s = t := by
  rcases le_total s t with hst | hst
  · exact s6a_injOn_x F hst (fun u h1 h2 => hfree u (Or.inl ⟨h1, h2⟩)) ⟨le_rfl, hst⟩ ⟨hst, le_rfl⟩ h
  · exact (s6a_injOn_x F hst (fun u h1 h2 => hfree u (Or.inr ⟨h1, h2⟩)) ⟨le_rfl, hst⟩ ⟨hst, le_rfl⟩ h.symm).symm

theorem s6a_xOf_add_int (i : Fin F.c) (t : ℝ) (n : ℤ) : xOf F i (t + n) = xOf F i t := by
  unfold xOf; rw [(F.comp i).eq_add_int]

theorem s6a_isCusp_add_int (i : Fin F.c) (t : ℝ) (n : ℤ) : F.IsCusp (i, t + n) ↔ F.IsCusp (i, t) :=
  F.isCusp_iff_of_sameParam ⟨rfl, n, rfl⟩

theorem s6a_Free_add_int {i : Fin F.c} {s t : ℝ} (h : s6a_Free F i s t) (n : ℤ) :
    s6a_Free F i (s + n) (t + n) := by
  intro u hu
  have hu' : (s < u - n ∧ u - n < t) ∨ (t < u - n ∧ u - n < s) := by
    rcases hu with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨by linarith, by linarith⟩
    · exact Or.inr ⟨by linarith, by linarith⟩
  have := h (u - n) hu'
  rwa [← s6a_isCusp_add_int F i (u - n) n, sub_add_cancel] at this

/-- START core: the continuation of an entry `α` over `x(t)` by the strand at the lifted parameter
`s = t' + n` (no cusp between `s` and `α`, `t'` regular, no cusp between `t` and `t'`) forces `α = t + n`. -/
theorem s6a_cont_start_core {i : Fin F.c} {t t' s α : ℝ} (hfree : s6a_Free F i t t') (ht' : ¬ F.IsCusp (i, t'))
    (hα : xOf F i α = xOf F i t) {n : ℤ} (hs : s = t' + n) (hfree' : s6a_Free F i s α) : α = t + n := by
  subst hs
  have h1 : s6a_Free F i (t + n) (t' + n) := s6a_Free_add_int F hfree n
  have h2 : ¬ F.IsCusp (i, t' + n) := by rwa [s6a_isCusp_add_int]
  have h3 : s6a_Free F i (t + n) α := s6a_Free_join F h1 hfree' h2
  have hx : xOf F i (t + n) = xOf F i α := by rw [s6a_xOf_add_int, hα]
  exact (s6a_x_inj_of_Free F h3 hx).symm

/-- END core: the lifted parameter `s` of a strand over `x(t')` continuing the entry at `t + n` is `t' + n`
(when `t` is regular, or when `s` and `t'` lie on the same side of the cusp `t`). -/
theorem s6a_cont_end_core {i : Fin F.c} {t t' s : ℝ} {n : ℤ} (hfree : s6a_Free F i t t')
    (hx : xOf F i s = xOf F i t') (hfree' : s6a_Free F i s (t + n))
    (hside : ¬ F.IsCusp (i, t) ∨ (s < t + n ↔ t' < t)) : s = t' + n := by
  have h1 : s6a_Free F i (t + n) (t' + n) := s6a_Free_add_int F hfree n
  have h3 : s6a_Free F i s (t' + n) := by
    rcases hside with hc | hside
    · exact s6a_Free_join F hfree' h1 (by rwa [s6a_isCusp_add_int])
    · exact s6a_Free_same_side F hfree' h1 (by rw [hside]; constructor <;> intro h <;> linarith)
  have hx' : xOf F i s = xOf F i (t' + n) := by rw [s6a_xOf_add_int, hx]
  exact s6a_x_inj_of_Free F h3 hx'

/-- START: the entry of the cut at `x(t)` continued (`Cont`) by the strand `(i, fract t')` is an entry of
`(i, fract t)`; for a cusp its arm index is read off the side of `t'`. -/
theorem s6a_cont_start {i : Fin F.c} {t t' : ℝ} (hfree : s6a_Free F i t t') (ht' : ¬ F.IsCusp (i, t'))
    {a : Param F.c × ℕ} (ha : a.1 ∈ totalFibre F (xOf F i t)) (hc : Cont F (i, Int.fract t') a) :
    a.1 = (i, Int.fract t) ∧ (F.IsCusp a.1 → (t' < t ↔ (a.2 = 0 ↔ F.cuspDisc a.1 < 0))) := by
  obtain ⟨hi, s, hsp, hsne, hfr, harm⟩ := hc
  have hi' : a.1.1 = i := hi.symm
  obtain ⟨-, m, hm⟩ := hsp
  simp only at hm
  have hs : s = t' + ((m - ⌊t'⌋ : ℤ) : ℝ) := by
    rw [hm, ← Int.self_sub_floor]; push_cast; ring
  have hα : xOf F i a.1.2 = xOf F i t := by rw [← ha.2, ← hi']; rfl
  have hfree' : s6a_Free F i s a.1.2 := s6a_Free_of_minmax F (by rw [hi'] at hfr; exact hfr)
  have hα' := s6a_cont_start_core F hfree ht' hα hs hfree'
  refine ⟨Prod.ext hi' ?_, fun hcusp => ?_⟩
  · symm; rw [Int.fract_eq_iff]
    refine ⟨ha.1.1, ha.1.2, -(m - ⌊t'⌋), ?_⟩
    rw [hα']; push_cast; ring
  · rw [← harm hcusp, hα', hs]; constructor <;> intro h <;> linarith

/-- END: the strand of the cut at `x(t')` continuing (`Cont`) an entry of `(i, fract t)` is `(i, fract t')`. -/
theorem s6a_cont_end {i : Fin F.c} {t t' : ℝ} (hfree : s6a_Free F i t t') {a : Param F.c × ℕ}
    (ha : a.1 = (i, Int.fract t)) {q : Param F.c} (hq : q ∈ totalFibre F (xOf F i t')) (hc : Cont F q a)
    (hside : ¬ F.IsCusp (i, t) ∨ ((a.2 = 0 ↔ F.cuspDisc a.1 < 0) ↔ t' < t)) :
    q = (i, Int.fract t') := by
  obtain ⟨hi, s, hsp, hsne, hfr, harm⟩ := hc
  rw [ha] at hi hsp hsne hfr harm hside
  simp only at hi hsp hsne hfr harm
  obtain ⟨-, m, hm⟩ := hsp
  simp only at hm
  have hxs : xOf F i s = xOf F i t' := by
    rw [hm, s6a_xOf_add_int, ← hq.2, ← hi]; rfl
  have hfract : Int.fract t = t + ((-⌊t⌋ : ℤ) : ℝ) := by rw [← Int.self_sub_floor]; push_cast; ring
  have hfree' : s6a_Free F i s (t + ((-⌊t⌋ : ℤ) : ℝ)) := by
    rw [← hfract]; exact s6a_Free_of_minmax F hfr
  have hside' : ¬ F.IsCusp (i, t) ∨ (s < t + ((-⌊t⌋ : ℤ) : ℝ) ↔ t' < t) := by
    rcases hside with h | h
    · exact Or.inl h
    · by_cases hct : F.IsCusp (i, t)
      · right
        have hcf : F.IsCusp (i, Int.fract t) := by rw [hfract, s6a_isCusp_add_int]; exact hct
        rw [← hfract]
        exact (harm hcf).trans h
      · exact Or.inl hct
  have hs := s6a_cont_end_core F hfree hxs hfree' hside'
  refine Prod.ext hi ?_
  show q.2 = Int.fract t'
  symm; rw [Int.fract_eq_iff]
  refine ⟨hq.1.1, hq.1.2, ⌊t⌋ + m, ?_⟩
  have : q.2 = s - m := by rw [hm]; ring
  rw [this, hs]; push_cast; ring

/-- just left of a regular rightward point `x` is smaller, just right it is larger -/
theorem s6a_side_pos {i : Fin F.c} {t : ℝ} (h : 0 < xvel F i t) :
    ∃ δ > 0, ∀ s, dist s t < δ → (s < t → xOf F i s < xOf F i t) ∧ (t < s → xOf F i t < xOf F i s) := by
  have hd : HasDerivAt (fun s => xOf F i s - xOf F i t) (xvel F i t) t := (hasDerivAt_x F i t).sub_const _
  obtain ⟨δ, hδ, hs⟩ := sign_near_simple_zero hd (sub_self _) h
  refine ⟨δ, hδ, fun s hst => ⟨fun hlt => ?_, fun hgt => ?_⟩⟩
  · have := (hs s hst).1 hlt; linarith
  · have := (hs s hst).2 hgt; linarith

theorem s6a_side_neg {i : Fin F.c} {t : ℝ} (h : xvel F i t < 0) :
    ∃ δ > 0, ∀ s, dist s t < δ → (s < t → xOf F i t < xOf F i s) ∧ (t < s → xOf F i s < xOf F i t) := by
  have hd : HasDerivAt (fun s => xOf F i t - xOf F i s) (-xvel F i t) t := (hasDerivAt_x F i t).const_sub _
  obtain ⟨δ, hδ, hs⟩ := sign_near_simple_zero hd (sub_self _) (neg_pos.mpr h)
  refine ⟨δ, hδ, fun s hst => ⟨fun hlt => ?_, fun hgt => ?_⟩⟩
  · have := (hs s hst).1 hlt; linarith
  · have := (hs s hst).2 hgt; linarith

theorem s6a_x_cont {i : Fin F.c} (t : ℝ) {η : ℝ} (hη : 0 < η) :
    ∃ δ > 0, ∀ s, dist s t < δ → |xOf F i s - xOf F i t| < η := by
  have hc : Continuous (xOf F i) := (F.comp i).continuous.fst
  obtain ⟨δ, hδ, h⟩ := Metric.continuous_iff.mp hc t η hη
  exact ⟨δ, hδ, fun s hs => by have := h s hs; rwa [Real.dist_eq] at this⟩

theorem s6a_no_cusp_near {i : Fin F.c} {t : ℝ} (h : ¬ F.IsCusp (i, t)) :
    ∃ δ > 0, ∀ s, dist s t < δ → ¬ F.IsCusp (i, s) := by
  have hne := xvel_ne_zero_of_not_isCusp F h
  obtain ⟨δ, hδ, hc⟩ := Metric.continuous_iff.mp (continuous_xvel F i) t |xvel F i t| (abs_pos.mpr hne)
  refine ⟨δ, hδ, fun s hs hcs => ?_⟩
  have h0 := (isCusp_iff_xvel_eq_zero F i s).mp hcs
  have := hc s hs
  rw [h0, Real.dist_eq, zero_sub, abs_neg] at this
  exact lt_irrefl _ this

theorem s6a_eval_rep (i : Fin F.c) (t : ℝ) : F.eval (i, Int.fract t) = F.eval (i, t) :=
  SmoothFront.eval_of_sameParam (SameParam.sameParam_rep (i, t))

theorem s6a_rep_mem_totalFibre (i : Fin F.c) (t : ℝ) : (i, Int.fract t) ∈ totalFibre F (xOf F i t) := by
  refine ⟨⟨Int.fract_nonneg _, Int.fract_lt_one _⟩, ?_⟩
  show (F.eval (i, Int.fract t)).1 = (F.eval (i, t)).1
  rw [s6a_eval_rep]

theorem s6a_regular_rep {i : Fin F.c} {t : ℝ} (hc : ¬ F.IsCusp (i, t)) (hd : ∀ q, ¬ F.IsDouble (i, t) q) :
    ¬ F.IsCusp (i, Int.fract t) ∧ ∀ q, ¬ F.IsDouble (i, Int.fract t) q := by
  have hsp : SameParam (i, t) (i, Int.fract t) := SameParam.sameParam_rep (i, t)
  constructor
  · rwa [F.isCusp_iff_of_sameParam hsp]
  · intro q hq
    apply hd q
    exact ⟨fun h => hq.1 (hsp.symm.trans h), (s6a_eval_rep F i t).symm.trans hq.2⟩

theorem s6a_xvel_rep (i : Fin F.c) (t : ℝ) : xvel F i (Int.fract t) = xvel F i t := by
  rw [xvel_def, xvel_def]
  exact congrArg Prod.fst (SmoothFront.vel_of_sameParam (SameParam.sameParam_rep (i, t)))

theorem s6a_dirBit_rep (i : Fin F.c) (t : ℝ) : dirBit F (i, Int.fract t) = decide (0 < xvel F i t) := by
  show decide (0 < xvel F i (Int.fract t)) = _
  rw [s6a_xvel_rep]

theorem s6a_card_filter_eq (x : ℝ) (P : Param F.c → Prop) [DecidablePred P] :
    ((fibreFinset F x).filter P).card = ((fibreListBefore F x).filter (fun p => decide (P p))).length := by
  rw [Finset.card_def, Finset.filter_val, ← Finset.coe_toList, Multiset.filter_coe, Multiset.coe_card]
  exact ((fibreListBefore_perm F x).filter _).length_eq.symm

/-- the position of a fibre point at a non-singular `x` is one plus its index in the sorted fibre list -/
theorem s6a_posAt_eq {x : ℝ} (hx : x ∉ singX F) {J : ℕ} (hJ : J < (fibreListBefore F x).length) :
    posAt F x (fibreListBefore F x)[J] = J + 1 := by
  unfold posAt
  rw [s6a_card_filter_eq]
  congr 1
  have hpw := fibreListBefore_pairwise F x
  have hup : ∀ a ∈ fibreListBefore F x, ∀ b ∈ fibreListBefore F x, beforeLE F a b = true →
      decide (ht F (fibreListBefore F x)[J] < ht F b) = true →
      decide (ht F (fibreListBefore F x)[J] < ht F a) = true := by
    intro a _ b _ hab hb
    simp only [decide_eq_true_iff] at hb ⊢
    exact lt_of_lt_of_le hb (s6a_ht_of_beforeLE F hab)
  have hiff := fun j hj => s6a_filter_getElem_iff hpw hup j hj
  have h1 : ¬ J < ((fibreListBefore F x).filter
      (fun p => decide (ht F (fibreListBefore F x)[J] < ht F p))).length := by
    rw [← hiff J hJ]; simp
  rcases Nat.eq_zero_or_pos J with hJ0 | hJ0
  · omega
  · have h2 : J - 1 < ((fibreListBefore F x).filter
        (fun p => decide (ht F (fibreListBefore F x)[J] < ht F p))).length := by
      rw [← hiff (J - 1) (by omega)]
      simp only [decide_eq_true_iff]
      have hle : ht F (fibreListBefore F x)[J] ≤ ht F (fibreListBefore F x)[J - 1] :=
        s6a_ht_of_beforeLE F (List.pairwise_iff_getElem.mp hpw (J - 1) J (by omega) hJ (by omega))
      have hne : ht F (fibreListBefore F x)[J] ≠ ht F (fibreListBefore F x)[J - 1] := by
        intro h
        have := snd_injOn_totalFibre F hx ((mem_fibreListBefore F x _).mp (List.getElem_mem hJ))
          ((mem_fibreListBefore F x _).mp (List.getElem_mem (by omega))) h
        rw [(fibreListBefore_nodup F x).getElem_inj_iff] at this
        omega
      exact lt_of_le_of_ne hle hne
    omega

theorem s6a_entriesBefore_length {x : ℝ} (hx : x ∉ singX F) :
    (entriesBefore F x).length = (fibreListBefore F x).length := by
  rw [entriesBefore_eq_of_notMem_singX F hx, List.length_map]

theorem s6a_entriesBefore_getD {x : ℝ} (hx : x ∉ singX F) {J : ℕ} (hJ : J < (fibreListBefore F x).length) :
    (entriesBefore F x).getD J (dfltP F, 0) = ((fibreListBefore F x)[J], 0) := by
  rw [entriesBefore_eq_of_notMem_singX F hx, List.getD_eq_getElem _ _ (by rw [List.length_map]; exact hJ),
    List.getElem_map]

/-- a regular fibre point is at no event's height -/
theorem s6a_ht_ne_colZ_of_regular {x₀ : ℝ} {q : Param F.c} (hq : q ∈ totalFibre F x₀) (hc : ¬ F.IsCusp q)
    (hd : ∀ r, ¬ F.IsDouble q r) {k : ℕ} (hk0 : s6a_k0 F x₀ ≤ k) (hkK : k < s6a_K F x₀) :
    ht F q ≠ colZ F k := by
  intro h
  have hx : evX F (eventAt F k) = x₀ := s6a_colX_eq F x₀ hk0 hkK
  rcases (s6a_ht_eq_evZ_iff F (eventAt F k) hx hq).mp h with h1 | ⟨q', hq', h1⟩
  · cases he : eventAt F k with
    | inl c => rw [he] at h1; exact hc (by rw [h1]; exact c.isCusp)
    | inr q' => rw [he] at h1; exact hd q'.1.2 (by rw [h1]; exact (F.isOverUnder_of_mem_crossingPairs q'.2).1)
  · exact hd q'.1.1 (by rw [h1]; exact (F.isOverUnder_of_mem_crossingPairs q'.2).1.symm)

end S6aAnalytic

/-! #### From the one-sided entry limits to positions: the START and END of a jump -/

section S6aStartEnd

variable (F : SmoothFront)

theorem s6a_Free_of_near {i : Fin F.c} {t t' δ : ℝ} (hnc : ∀ s, dist s t < δ → ¬ F.IsCusp (i, s))
    (hε : |t' - t| < δ) : s6a_Free F i t t' := by
  intro u hu
  apply hnc
  rw [Real.dist_eq, abs_lt]
  rw [abs_lt] at hε
  rcases hu with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> constructor <;> linarith

theorem s6a_Free_of_local {i : Fin F.c} {t t' δ : ℝ}
    (hnc : ∀ s ∈ Set.Ioo (t - δ) (t + δ), s ≠ t → ¬ F.IsCusp (i, s)) (hε : |t' - t| < δ) :
    s6a_Free F i t t' := by
  intro u hu
  rw [abs_lt] at hε
  rcases hu with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact hnc u ⟨by linarith, by linarith⟩ (ne_of_gt h1)
  · exact hnc u ⟨by linarith, by linarith⟩ (ne_of_lt h2)

theorem s6a_dist_sub (t ε' : ℝ) (h : 0 < ε') : dist (t - ε') t = ε' := by
  rw [Real.dist_eq, sub_sub_cancel_left, abs_neg, abs_of_pos h]

theorem s6a_dist_add (t ε' : ℝ) (h : 0 < ε') : dist (t + ε') t = ε' := by
  rw [Real.dist_eq, add_sub_cancel_left, abs_of_pos h]

theorem s6a_entryBit_regular {q : Param F.c} (hq : ¬ F.IsCusp q) :
    entryBit F (beforeBits F) (q, 0) = dirBit F q ∧ entryBit F (afterBits F) (q, 0) = dirBit F q := by
  obtain ⟨h1, h2⟩ := s6a_bits_of_not_cusp F hq
  unfold entryBit
  rw [h1, h2]
  exact ⟨rfl, rfl⟩

/-- the columns of nearby non-singular x-values -/
theorem s6a_colAt_near (x₀ : ℝ) {η : ℝ} (hgap : ∀ y ∈ singX F, y ≠ x₀ → η ≤ |y - x₀|) {x : ℝ}
    (hx : |x - x₀| < η) :
    x ≠ x₀ → x ∉ singX F ∧ (x < x₀ → colAt F x = s6a_k0 F x₀) ∧ (x₀ < x → colAt F x = s6a_K F x₀) := by
  intro hne
  refine ⟨fun hs => absurd (hgap x hs hne) (not_le.mpr hx), fun hlt => ?_, fun hgt => ?_⟩
  · apply s6a_colAt_eq_k0 F x₀ hlt
    intro e he
    have h1 := hgap _ (s6a_evX_mem_singX F e) (ne_of_lt he)
    rw [abs_of_neg (by linarith)] at h1
    rw [abs_lt] at hx
    linarith
  · apply s6a_colAt_eq_K F x₀ hgt
    intro e he
    have h1 := hgap _ (s6a_evX_mem_singX F e) (ne_of_gt he)
    rw [abs_of_pos (by linarith)] at h1
    rw [abs_lt] at hx
    linarith

/-- START from the left of `x₀ = x(t)`: the strand `(i, fract t')` at `x' = x(t') < x₀` sits at the position
`J + 1` where `J` is the index of an entry of `(i, fract t)` in `entriesBefore x₀`. -/
theorem s6a_start_before {i : Fin F.c} {t t' : ℝ} (hfree : s6a_Free F i t t') (ht' : ¬ F.IsCusp (i, t'))
    (hx' : xOf F i t' ∉ singX F)
    (hlim : (entriesBefore F (xOf F i t')).length = (entriesBefore F (xOf F i t)).length ∧
      ∀ j < (entriesBefore F (xOf F i t)).length,
        Cont F ((entriesBefore F (xOf F i t')).getD j (dfltP F, 0)).1
          ((entriesBefore F (xOf F i t)).getD j (dfltP F, 0))) :
    ∃ J, ∃ hJ : J < (entriesBefore F (xOf F i t)).length,
      ((entriesBefore F (xOf F i t))[J]).1 = (i, Int.fract t) ∧
      (F.IsCusp (i, Int.fract t) →
        (t' < t ↔ (((entriesBefore F (xOf F i t))[J]).2 = 0 ↔ F.cuspDisc (i, Int.fract t) < 0))) ∧
      posAt F (xOf F i t') (i, Int.fract t') = J + 1 := by
  obtain ⟨J, hJ', hq'⟩ := List.mem_iff_getElem.mp
    ((mem_fibreListBefore F _ _).mpr (s6a_rep_mem_totalFibre F i t'))
  have hJ : J < (entriesBefore F (xOf F i t)).length := by
    rw [← hlim.1, s6a_entriesBefore_length F hx']; exact hJ'
  have hc := hlim.2 J hJ
  rw [s6a_entriesBefore_getD F hx' hJ', hq', List.getD_eq_getElem _ _ hJ] at hc
  have hmem : ((entriesBefore F (xOf F i t))[J]).1 ∈ totalFibre F (xOf F i t) := by
    have := List.getElem_mem hJ
    unfold entriesBefore at this
    rw [s6a_mem_entriesOf, mem_fibreListBefore] at this
    exact this.1
  obtain ⟨h1, h2⟩ := s6a_cont_start F hfree ht' hmem hc
  refine ⟨J, hJ, h1, ?_, ?_⟩
  · rw [← h1]; exact h2
  · rw [← hq', s6a_posAt_eq F hx' hJ']

/-- START from the right of `x₀ = x(t)`: the strand `(i, fract t')` at `x' = x(t') > x₀`. -/
theorem s6a_start_after {i : Fin F.c} {t t' : ℝ} (hfree : s6a_Free F i t t') (ht' : ¬ F.IsCusp (i, t'))
    (hx' : xOf F i t' ∉ singX F)
    (hlim : (entriesBefore F (xOf F i t')).length = (entriesAfter F (xOf F i t)).length ∧
      ∀ j < (entriesAfter F (xOf F i t)).length,
        Cont F ((entriesBefore F (xOf F i t')).getD j (dfltP F, 0)).1
          ((entriesAfter F (xOf F i t)).getD j (dfltP F, 0))) :
    ∃ J, ∃ hJ : J < (entriesAfter F (xOf F i t)).length,
      ((entriesAfter F (xOf F i t))[J]).1 = (i, Int.fract t) ∧
      (F.IsCusp (i, Int.fract t) →
        (t' < t ↔ (((entriesAfter F (xOf F i t))[J]).2 = 0 ↔ F.cuspDisc (i, Int.fract t) < 0))) ∧
      posAt F (xOf F i t') (i, Int.fract t') = J + 1 := by
  obtain ⟨J, hJ', hq'⟩ := List.mem_iff_getElem.mp
    ((mem_fibreListBefore F _ _).mpr (s6a_rep_mem_totalFibre F i t'))
  have hJ : J < (entriesAfter F (xOf F i t)).length := by
    rw [← hlim.1, s6a_entriesBefore_length F hx']; exact hJ'
  have hc := hlim.2 J hJ
  rw [s6a_entriesBefore_getD F hx' hJ', hq', List.getD_eq_getElem _ _ hJ] at hc
  have hmem : ((entriesAfter F (xOf F i t))[J]).1 ∈ totalFibre F (xOf F i t) := by
    have := List.getElem_mem hJ
    unfold entriesAfter at this
    rw [s6a_mem_entriesOf, mem_fibreListAfter] at this
    exact this.1
  obtain ⟨h1, h2⟩ := s6a_cont_start F hfree ht' hmem hc
  refine ⟨J, hJ, h1, ?_, ?_⟩
  · rw [← h1]; exact h2
  · rw [← hq', s6a_posAt_eq F hx' hJ']

/-- END to the left of `x₀ = x(t)`: the entry `a` of `(i, fract t)` at index `J` of `entriesBefore x₀` is
continued at `x' = x(t') < x₀` by the strand `(i, fract t')`, at position `J + 1`. -/
theorem s6a_end_before {i : Fin F.c} {t t' : ℝ} (hfree : s6a_Free F i t t') (hx' : xOf F i t' ∉ singX F)
    (hlim : (entriesBefore F (xOf F i t')).length = (entriesBefore F (xOf F i t)).length ∧
      ∀ j < (entriesBefore F (xOf F i t)).length,
        Cont F ((entriesBefore F (xOf F i t')).getD j (dfltP F, 0)).1
          ((entriesBefore F (xOf F i t)).getD j (dfltP F, 0)))
    {J : ℕ} (hJ : J < (entriesBefore F (xOf F i t)).length)
    (ha : ((entriesBefore F (xOf F i t))[J]).1 = (i, Int.fract t))
    (hside : ¬ F.IsCusp (i, t) ∨
      ((((entriesBefore F (xOf F i t))[J]).2 = 0 ↔ F.cuspDisc ((entriesBefore F (xOf F i t))[J]).1 < 0) ↔ t' < t)) :
    posAt F (xOf F i t') (i, Int.fract t') = J + 1 := by
  have hJ' : J < (fibreListBefore F (xOf F i t')).length := by
    rw [← s6a_entriesBefore_length F hx', hlim.1]; exact hJ
  have hc := hlim.2 J hJ
  rw [s6a_entriesBefore_getD F hx' hJ', List.getD_eq_getElem _ _ hJ] at hc
  have hq : (fibreListBefore F (xOf F i t'))[J] ∈ totalFibre F (xOf F i t') :=
    (mem_fibreListBefore F _ _).mp (List.getElem_mem hJ')
  have := s6a_cont_end F hfree ha hq hc hside
  rw [← this, s6a_posAt_eq F hx' hJ']

/-- END to the right of `x₀ = x(t)`: the entry `a` of `(i, fract t)` at index `J` of `entriesAfter x₀`. -/
theorem s6a_end_after {i : Fin F.c} {t t' : ℝ} (hfree : s6a_Free F i t t') (hx' : xOf F i t' ∉ singX F)
    (hlim : (entriesBefore F (xOf F i t')).length = (entriesAfter F (xOf F i t)).length ∧
      ∀ j < (entriesAfter F (xOf F i t)).length,
        Cont F ((entriesBefore F (xOf F i t')).getD j (dfltP F, 0)).1
          ((entriesAfter F (xOf F i t)).getD j (dfltP F, 0)))
    {J : ℕ} (hJ : J < (entriesAfter F (xOf F i t)).length)
    (ha : ((entriesAfter F (xOf F i t))[J]).1 = (i, Int.fract t))
    (hside : ¬ F.IsCusp (i, t) ∨
      ((((entriesAfter F (xOf F i t))[J]).2 = 0 ↔ F.cuspDisc ((entriesAfter F (xOf F i t))[J]).1 < 0) ↔ t' < t)) :
    posAt F (xOf F i t') (i, Int.fract t') = J + 1 := by
  have hJ' : J < (fibreListBefore F (xOf F i t')).length := by
    rw [← s6a_entriesBefore_length F hx', hlim.1]; exact hJ
  have hc := hlim.2 J hJ
  rw [s6a_entriesBefore_getD F hx' hJ', List.getD_eq_getElem _ _ hJ] at hc
  have hq : (fibreListBefore F (xOf F i t'))[J] ∈ totalFibre F (xOf F i t') :=
    (mem_fibreListBefore F _ _).mp (List.getElem_mem hJ')
  have := s6a_cont_end F hfree ha hq hc hside
  rw [← this, s6a_posAt_eq F hx' hJ']

end S6aStartEnd

/-! #### Passing a cusp vertex -/

section S6aCusp

variable (F : SmoothFront)

theorem s6a_afterBits_left {p : Param F.c} (hl : F.IsLeftCusp p) :
    afterBits F p = if 0 < F.cuspDisc p then [true, false] else [false, true] := by
  have hr : ¬ F.IsRightCusp p := fun hr => left_right_absurd F hl hr
  unfold afterBits; simp [hl, hr]

theorem s6a_beforeBits_right {p : Param F.c} (hr : F.IsRightCusp p) :
    beforeBits F p = if F.cuspDisc p < 0 then [true, false] else [false, true] := by
  have hl : ¬ F.IsLeftCusp p := fun hl => left_right_absurd F hl hr
  unfold beforeBits; simp [hl, hr]

theorem s6a_afterBits_left_getD {p : Param F.c} (hl : F.IsLeftCusp p) (j : ℕ) (hj : j < 2) :
    (afterBits F p).getD j false = decide (j = 0 ↔ 0 < F.cuspDisc p) := by
  rw [s6a_afterBits_left F hl]
  interval_cases j <;> split_ifs with h <;> simp [h]

theorem s6a_beforeBits_right_getD {p : Param F.c} (hr : F.IsRightCusp p) (j : ℕ) (hj : j < 2) :
    (beforeBits F p).getD j false = decide (j = 0 ↔ F.cuspDisc p < 0) := by
  rw [s6a_beforeBits_right F hr]
  interval_cases j <;> split_ifs with h <;> simp [h]

theorem s6a_afterBits_left_length {p : Param F.c} (hl : F.IsLeftCusp p) : (afterBits F p).length = 2 := by
  rw [s6a_afterBits_left F hl]; split_ifs <;> rfl

theorem s6a_beforeBits_right_length {p : Param F.c} (hr : F.IsRightCusp p) : (beforeBits F p).length = 2 := by
  rw [s6a_beforeBits_right F hr]; split_ifs <;> rfl

/-- a rightward cut slot whose column letter is not a crossing is not a `σ` slot -/
theorem s6a_not_σ_letter_right {u : Slot (word F)} {k p : ℕ} (hu : u.1 = (k, p)) (hp : p ≠ 0)
    (hb : bit (word F) k p = true) (hℓ : (letterAt (word F) k).isCrossing = false) : ¬ U2.IsσSlot u := by
  intro hσ
  obtain ⟨k', m, hk', hℓ', hu'⟩ := (U2.isσSlot_iff (word_closed F) u).mp hσ
  obtain ⟨hm1, -, -, hb1, hb2⟩ := σ_facts (word_closed F) hk' hℓ'
  rcases hu' with rfl | rfl
  · rw [s6a_σSlotA_val] at hu
    split_ifs at hu with hbm
    · simp only [Prod.mk.injEq] at hu; obtain ⟨rfl, rfl⟩ := hu
      rw [hℓ'] at hℓ; simp [Letter.isCrossing] at hℓ
    · simp only [Prod.mk.injEq] at hu; obtain ⟨rfl, rfl⟩ := hu
      rw [hb1] at hb; simp [hbm] at hb
  · rw [s6a_σSlotB_val] at hu
    split_ifs at hu with hbm
    · simp only [Prod.mk.injEq] at hu; obtain ⟨rfl, rfl⟩ := hu
      rw [hℓ'] at hℓ; simp [Letter.isCrossing] at hℓ
    · simp only [Prod.mk.injEq] at hu; obtain ⟨rfl, rfl⟩ := hu
      rw [hb2] at hb; simp [hbm] at hb

/-- a leftward cut slot whose column letter is not a crossing is not a `σ` slot -/
theorem s6a_not_σ_letter_left {u : Slot (word F)} {k p : ℕ} (hu : u.1 = (k + 1, p)) (hp : p ≠ 0)
    (hb : bit (word F) (k + 1) p = false) (hℓ : (letterAt (word F) k).isCrossing = false) : ¬ U2.IsσSlot u := by
  intro hσ
  obtain ⟨k', m, hk', hℓ', hu'⟩ := (U2.isσSlot_iff (word_closed F) u).mp hσ
  obtain ⟨hm1, -, -, hb1, hb2⟩ := σ_facts (word_closed F) hk' hℓ'
  rcases hu' with rfl | rfl
  · rw [s6a_σSlotA_val] at hu
    split_ifs at hu with hbm
    · simp only [Prod.mk.injEq] at hu
      obtain ⟨hk, rfl⟩ := hu
      subst hk
      rw [hbm] at hb
      exact Bool.noConfusion hb
    · simp only [Prod.mk.injEq, Nat.add_right_cancel_iff] at hu
      obtain ⟨rfl, rfl⟩ := hu
      rw [hℓ'] at hℓ; simp [Letter.isCrossing] at hℓ
  · rw [s6a_σSlotB_val] at hu
    split_ifs at hu with hbm
    · simp only [Prod.mk.injEq] at hu
      obtain ⟨hk, rfl⟩ := hu
      subst hk
      rw [hbm] at hb
      exact Bool.noConfusion hb
    · simp only [Prod.mk.injEq, Nat.add_right_cancel_iff] at hu
      obtain ⟨rfl, rfl⟩ := hu
      rw [hℓ'] at hℓ; simp [Letter.isCrossing] at hℓ

theorem s6a_cuspVertex_val (c : F.Cusp) : (cuspVertex F c).1 = (evIdx F (Sum.inl c), 0) := rfl

/-- Through a LEFT cusp `c`: arriving leftward at cut `k_c + 1` on the arm `(c.1, j₁)` (`j₁ = 0 ↔ cuspDisc < 0`),
`next` reaches the cusp vertex and then the other arm `(c.1, j₂)` at cut `k_c + 1`. -/
theorem s6a_leftCusp_pass (c : F.Cusp) (hl : F.IsLeftCusp c.1) {j₁ : ℕ} (hj₁ : j₁ = 0 ↔ F.cuspDisc c.1 < 0)
    {J₂ : ℕ} (hJ₂ : J₂ < (s6a_entCol F (evX F (Sum.inl c)) (evIdx F (Sum.inl c) + 1)).length)
    (ha : (s6a_entCol F (evX F (Sum.inl c)) (evIdx F (Sum.inl c) + 1))[J₂] = (c.1, j₁))
    (u : Slot (word F)) (hu : u.1 = (evIdx F (Sum.inl c) + 1, J₂ + 1)) :
    ∃ J₃, ∃ hJ₃ : J₃ < (s6a_entCol F (evX F (Sum.inl c)) (evIdx F (Sum.inl c) + 1)).length,
      (s6a_entCol F (evX F (Sum.inl c)) (evIdx F (Sum.inl c) + 1))[J₃] =
        (c.1, if 0 < F.cuspDisc c.1 then 0 else 1) ∧
      next (word_closed F) u = cuspVertex F c ∧
      (next (word_closed F) (cuspVertex F c)).1 = (evIdx F (Sum.inl c) + 1, J₃ + 1) ∧
      ¬ U2.IsσSlot u := by
  obtain ⟨hk0, hkK⟩ := s6a_evIdx_mem F (evX F (Sum.inl c)) (e := Sum.inl c) rfl
  have hkn : evIdx F (Sum.inl c) < (events F).length := evIdx_lt_length F _
  have hℓ : letterAt (word F) (evIdx F (Sum.inl c)) = letterOf F (Sum.inl c) := letterAt_word_evIdx F _
  have hℓ' : letterOf F (Sum.inl c) =
      Letter.l (posOf F (Sum.inl c)) (decide (0 < F.cuspDisc c.1)) := by
    show (if F.IsLeftCusp c.1 then _ else _) = _; rw [ite_eq_left hl]
  have hz : evZ F (Sum.inl c) = colZ F (evIdx F (Sum.inl c)) := s6a_evZ_eq_colZ F _
  have hcd := F.cuspDisc_ne_zero_of_isCusp hl.1
  have hcol : s6a_entCol F (evX F (Sum.inl c)) (evIdx F (Sum.inl c) + 1) =
      s6a_A F (evX F (Sum.inl c)) (Sum.inl c) ++ s6a_Ea F (evX F (Sum.inl c)) (Sum.inl c) ++
        s6a_R F (evX F (Sum.inl c)) (Sum.inl c) := by
    rw [s6a_entCol_succ F _ hk0 hkK, ← hz, s6a_hE_lt]
  have hEa : s6a_Ea F (evX F (Sum.inl c)) (Sum.inl c) = [(c.1, 0), (c.1, 1)] := by
    rw [s6a_Ea_cusp F _ c rfl, s6a_afterBits_left_length F hl]; rfl
  have hA : (s6a_A F (evX F (Sum.inl c)) (Sum.inl c)).length = posOf F (Sum.inl c) - 1 := by
    rw [s6a_length_A F _ _ rfl, hℓ']; rfl
  have hm1 : 1 ≤ posOf F (Sum.inl c) := by
    have := s6a_idx_pos F (Sum.inl c); rw [hℓ'] at this; exact this
  have hnd : (s6a_entCol F (evX F (Sum.inl c)) (evIdx F (Sum.inl c) + 1)).Nodup := by
    rw [s6a_entCol_succ F _ hk0 hkK]; exact s6a_hybridEntriesP_nodup F _ _
  -- `j₁ < 2` and `J₂ = |A| + j₁`
  have hmem : (c.1, j₁) ∈ s6a_A F (evX F (Sum.inl c)) (Sum.inl c) ++ s6a_Ea F (evX F (Sum.inl c)) (Sum.inl c) ++
      s6a_R F (evX F (Sum.inl c)) (Sum.inl c) := by
    rw [← hcol, ← ha]; exact List.getElem_mem hJ₂
  have hj₁2 : j₁ < 2 := by
    rw [List.mem_append, List.mem_append] at hmem
    rcases hmem with (hmA | hmE) | hmR
    · exfalso
      unfold s6a_A at hmA
      rw [s6a_mem_entriesOf, List.mem_filter, decide_eq_true_iff] at hmA
      exact lt_irrefl _ hmA.1.2
    · rw [hEa] at hmE
      simp only [List.mem_cons, List.mem_singleton, Prod.mk.injEq, true_and, List.not_mem_nil, or_false] at hmE
      omega
    · exfalso
      unfold s6a_R at hmR
      rw [s6a_mem_entriesOf, List.mem_filter, decide_eq_true_iff] at hmR
      exact lt_irrefl _ hmR.1.2
  have hEaj : ∀ j (hj : j < 2), (s6a_Ea F (evX F (Sum.inl c)) (Sum.inl c))[j]'(by rw [hEa]; simpa using hj) = (c.1, j) := by
    intro j hj
    rw [List.getElem_of_eq hEa]
    interval_cases j <;> rfl
  have hlenA : (s6a_A F (evX F (Sum.inl c)) (Sum.inl c)).length + j₁ <
      (s6a_entCol F (evX F (Sum.inl c)) (evIdx F (Sum.inl c) + 1)).length := by
    rw [hcol]; simp only [List.length_append, hEa]; simp; omega
  have hJ₂eq : J₂ = (s6a_A F (evX F (Sum.inl c)) (Sum.inl c)).length + j₁ := by
    have h1 : (s6a_entCol F (evX F (Sum.inl c)) (evIdx F (Sum.inl c) + 1))[(s6a_A F (evX F (Sum.inl c)) (Sum.inl c)).length + j₁] = (c.1, j₁) := by
      rw [List.getElem_of_eq hcol, s6a_getElem_E _ _ _ j₁ (by rw [hEa]; simpa using hj₁2), hEaj j₁ hj₁2]
    rw [← hnd.getElem_inj_iff (hi := hJ₂) (hj := hlenA), ha, h1]
  -- the bit of `u`
  have hbit : bit (word F) (evIdx F (Sum.inl c) + 1) (J₂ + 1) = false := by
    have hJ₂' : J₂ < (hybridEntriesP F (evX F (Sum.inl c)) (fun p => decide (colZ F (evIdx F (Sum.inl c)) < ht F p))).length := by
      rw [← s6a_entCol_succ F _ hk0 hkK]; exact hJ₂
    have h1 := s6a_bit_of_entry F _ (fun p => decide (colZ F (evIdx F (Sum.inl c)) < ht F p)) hJ₂'
    have ha' : (hybridEntriesP F (evX F (Sum.inl c)) (fun p => decide (colZ F (evIdx F (Sum.inl c)) < ht F p)))[J₂] = (c.1, j₁) := by
      rw [← List.getElem_of_eq (s6a_entCol_succ F _ hk0 hkK) hJ₂]; exact ha
    rw [bit_eq, Nat.add_sub_cancel, s6a_cut_succ_eq F _ hk0 hkK, h1, ha']
    have hzc : colZ F (evIdx F (Sum.inl c)) = ht F c.1 := hz.symm
    simp only [hzc, lt_self_iff_false, decide_false, Bool.false_eq_true, ↓reduceIte]
    unfold entryBit
    rw [s6a_afterBits_left_getD F hl j₁ hj₁2, decide_eq_false_iff_not]
    intro h
    rcases lt_or_gt_of_ne hcd with hn | hp
    · exact lt_asymm hn (h.mp (hj₁.mpr hn))
    · exact lt_asymm hp (hj₁.mp (h.mpr hp))
  have hℓc : (letterAt (word F) (evIdx F (Sum.inl c))).isCrossing = false := by rw [hℓ, hℓ']; rfl
  have hJ₂1 : J₂ + 1 = posOf F (Sum.inl c) + j₁ := by omega
  -- `next u = cuspVertex c`
  have hq : (letterAt (word F) (evIdx F (Sum.inl c) + 1 - 1)).posL (J₂ + 1) = none := by
    rw [Nat.add_sub_cancel, hℓ, hℓ', hJ₂1]
    rcases (by omega : j₁ = 0 ∨ j₁ = 1) with h | h
    · rw [h, Nat.add_zero]; exact posL_l_idx _ _
    · rw [h]; exact posL_l_idx_succ _ _
  have hnext : next (word_closed F) u = cuspVertex F c := by
    apply Subtype.ext
    rw [next_val, hu, s6a_cuspVertex_val]
    rw [nextPair_left_none (word F) (Nat.succ_ne_zero J₂) hbit hq, Nat.add_sub_cancel]
  -- `next (cuspVertex c)`
  have hj₂2 : (if 0 < F.cuspDisc c.1 then 0 else 1) < 2 := by split_ifs <;> omega
  refine ⟨(s6a_A F (evX F (Sum.inl c)) (Sum.inl c)).length + (if 0 < F.cuspDisc c.1 then 0 else 1),
    by rw [hcol]; simp only [List.length_append, hEa]; simp; omega, ?_, hnext, ?_, ?_⟩
  · rw [List.getElem_of_eq hcol, s6a_getElem_E _ _ _ _ (by rw [hEa]; simpa using hj₂2), hEaj _ hj₂2]
  · rw [next_val, s6a_cuspVertex_val, nextPair_cusp_l (word F) (hℓ.trans hℓ')]
    congr 1
    rw [hA]
    by_cases hp : 0 < F.cuspDisc c.1
    · simp [hp]; omega
    · simp [hp]; omega
  · exact s6a_not_σ_letter_left F hu (Nat.succ_ne_zero J₂) hbit hℓc

/-- Through a RIGHT cusp `c`: arriving rightward at cut `k_c` on the arm `(c.1, j₁)` (`j₁ = 0 ↔ cuspDisc < 0`),
`next` reaches the cusp vertex and then the other arm `(c.1, j₂)` at cut `k_c`. -/
theorem s6a_rightCusp_pass (c : F.Cusp) (hr : F.IsRightCusp c.1) {j₁ : ℕ} (hj₁ : j₁ = 0 ↔ F.cuspDisc c.1 < 0)
    {J₂ : ℕ} (hJ₂ : J₂ < (s6a_entCol F (evX F (Sum.inl c)) (evIdx F (Sum.inl c))).length)
    (ha : (s6a_entCol F (evX F (Sum.inl c)) (evIdx F (Sum.inl c)))[J₂] = (c.1, j₁))
    (u : Slot (word F)) (hu : u.1 = (evIdx F (Sum.inl c), J₂ + 1)) :
    ∃ J₃, ∃ hJ₃ : J₃ < (s6a_entCol F (evX F (Sum.inl c)) (evIdx F (Sum.inl c))).length,
      (s6a_entCol F (evX F (Sum.inl c)) (evIdx F (Sum.inl c)))[J₃] =
        (c.1, if F.cuspDisc c.1 < 0 then 1 else 0) ∧
      next (word_closed F) u = cuspVertex F c ∧
      (next (word_closed F) (cuspVertex F c)).1 = (evIdx F (Sum.inl c), J₃ + 1) ∧
      ¬ U2.IsσSlot u := by
  obtain ⟨hk0, hkK⟩ := s6a_evIdx_mem F (evX F (Sum.inl c)) (e := Sum.inl c) rfl
  have hkn : evIdx F (Sum.inl c) < (events F).length := evIdx_lt_length F _
  have hℓ : letterAt (word F) (evIdx F (Sum.inl c)) = letterOf F (Sum.inl c) := letterAt_word_evIdx F _
  have hnl : ¬ F.IsLeftCusp c.1 := fun hl => left_right_absurd F hl hr
  have hℓ' : letterOf F (Sum.inl c) = Letter.r (posOf F (Sum.inl c)) := by
    show (if F.IsLeftCusp c.1 then _ else _) = _; rw [ite_eq_right hnl]
  have hz : evZ F (Sum.inl c) = colZ F (evIdx F (Sum.inl c)) := s6a_evZ_eq_colZ F _
  have hcol : s6a_entCol F (evX F (Sum.inl c)) (evIdx F (Sum.inl c)) =
      s6a_A F (evX F (Sum.inl c)) (Sum.inl c) ++ s6a_Eb F (evX F (Sum.inl c)) (Sum.inl c) ++
        s6a_R F (evX F (Sum.inl c)) (Sum.inl c) := by
    rw [s6a_entCol_of_lt F _ hkK, ← hz, s6a_hE_le]
  have hEb : s6a_Eb F (evX F (Sum.inl c)) (Sum.inl c) = [(c.1, 0), (c.1, 1)] := by
    rw [s6a_Eb_cusp F _ c rfl, s6a_beforeBits_right_length F hr]; rfl
  have hA : (s6a_A F (evX F (Sum.inl c)) (Sum.inl c)).length = posOf F (Sum.inl c) - 1 := by
    rw [s6a_length_A F _ _ rfl, hℓ']; rfl
  have hm1 : 1 ≤ posOf F (Sum.inl c) := by
    have := s6a_idx_pos F (Sum.inl c); rw [hℓ'] at this; exact this
  have hnd : (s6a_entCol F (evX F (Sum.inl c)) (evIdx F (Sum.inl c))).Nodup := by
    rw [s6a_entCol_of_lt F _ hkK]; exact s6a_hybridEntriesP_nodup F _ _
  have hmem : (c.1, j₁) ∈ s6a_A F (evX F (Sum.inl c)) (Sum.inl c) ++ s6a_Eb F (evX F (Sum.inl c)) (Sum.inl c) ++
      s6a_R F (evX F (Sum.inl c)) (Sum.inl c) := by
    rw [← hcol, ← ha]; exact List.getElem_mem hJ₂
  have hj₁2 : j₁ < 2 := by
    rw [List.mem_append, List.mem_append] at hmem
    rcases hmem with (hmA | hmE) | hmR
    · exfalso
      unfold s6a_A at hmA
      rw [s6a_mem_entriesOf, List.mem_filter, decide_eq_true_iff] at hmA
      exact lt_irrefl _ hmA.1.2
    · rw [hEb] at hmE
      simp only [List.mem_cons, List.mem_singleton, Prod.mk.injEq, true_and, List.not_mem_nil, or_false] at hmE
      omega
    · exfalso
      unfold s6a_R at hmR
      rw [s6a_mem_entriesOf, List.mem_filter, decide_eq_true_iff] at hmR
      exact lt_irrefl _ hmR.1.2
  have hEbj : ∀ j (hj : j < 2), (s6a_Eb F (evX F (Sum.inl c)) (Sum.inl c))[j]'(by rw [hEb]; simpa using hj) = (c.1, j) := by
    intro j hj
    rw [List.getElem_of_eq hEb]
    interval_cases j <;> rfl
  have hlenA : ∀ j, j < 2 → (s6a_A F (evX F (Sum.inl c)) (Sum.inl c)).length + j <
      (s6a_entCol F (evX F (Sum.inl c)) (evIdx F (Sum.inl c))).length := by
    intro j hj; rw [hcol]; simp only [List.length_append, hEb]; simp; omega
  have hidx : ∀ j (hj : j < 2), (s6a_entCol F (evX F (Sum.inl c)) (evIdx F (Sum.inl c)))[(s6a_A F (evX F (Sum.inl c)) (Sum.inl c)).length + j]'(hlenA j hj) = (c.1, j) := by
    intro j hj
    rw [List.getElem_of_eq hcol, s6a_getElem_E _ _ _ j (by rw [hEb]; simpa using hj), hEbj j hj]
  have hJ₂eq : J₂ = (s6a_A F (evX F (Sum.inl c)) (Sum.inl c)).length + j₁ := by
    rw [← hnd.getElem_inj_iff (hi := hJ₂) (hj := hlenA j₁ hj₁2), ha, hidx j₁ hj₁2]
  -- the bit at an arm index
  have hbitj : ∀ j (hj : j < 2), bit (word F) (evIdx F (Sum.inl c)) ((s6a_A F (evX F (Sum.inl c)) (Sum.inl c)).length + j + 1) =
      decide (j = 0 ↔ F.cuspDisc c.1 < 0) := by
    intro j hj
    have hJ' : (s6a_A F (evX F (Sum.inl c)) (Sum.inl c)).length + j <
        (hybridEntriesP F (evX F (Sum.inl c)) (fun p => decide (colZ F (evIdx F (Sum.inl c)) ≤ ht F p))).length := by
      rw [← s6a_entCol_of_lt F _ hkK]; exact hlenA j hj
    have h1 := s6a_bit_of_entry F _ (fun p => decide (colZ F (evIdx F (Sum.inl c)) ≤ ht F p)) hJ'
    have ha' : (hybridEntriesP F (evX F (Sum.inl c)) (fun p => decide (colZ F (evIdx F (Sum.inl c)) ≤ ht F p)))[(s6a_A F (evX F (Sum.inl c)) (Sum.inl c)).length + j] = (c.1, j) := by
      rw [← List.getElem_of_eq (s6a_entCol_of_lt F _ hkK) (hlenA j hj)]; exact hidx j hj
    rw [bit_eq, Nat.add_sub_cancel, s6a_cut_eq F _ hk0 hkK, h1, ha']
    have hzc : colZ F (evIdx F (Sum.inl c)) = ht F c.1 := hz.symm
    simp only [hzc, le_refl, decide_true, ↓reduceIte]
    unfold entryBit
    exact s6a_beforeBits_right_getD F hr j hj
  have hbit : bit (word F) (evIdx F (Sum.inl c)) (J₂ + 1) = true := by
    rw [hJ₂eq, hbitj j₁ hj₁2]; simp [hj₁]
  have hℓc : (letterAt (word F) (evIdx F (Sum.inl c))).isCrossing = false := by rw [hℓ, hℓ']; rfl
  have hJ₂1 : J₂ + 1 = posOf F (Sum.inl c) + j₁ := by omega
  have hq : (letterAt (word F) (evIdx F (Sum.inl c))).posR (J₂ + 1) = none := by
    rw [hℓ, hℓ', hJ₂1]
    rcases (by omega : j₁ = 0 ∨ j₁ = 1) with h | h
    · rw [h, Nat.add_zero]; exact posR_r_idx _
    · rw [h]; exact posR_r_idx_succ _
  have hnext : next (word_closed F) u = cuspVertex F c := by
    apply Subtype.ext
    rw [next_val, hu, s6a_cuspVertex_val]
    rw [nextPair_right_none (word F) (Nat.succ_ne_zero J₂) hbit hq]
  have hj₂2 : (if F.cuspDisc c.1 < 0 then 1 else 0) < 2 := by split_ifs <;> omega
  have hbm : bit (word F) (evIdx F (Sum.inl c)) (posOf F (Sum.inl c)) = decide (F.cuspDisc c.1 < 0) := by
    have := hbitj 0 (by omega)
    rw [hA, Nat.add_zero, Nat.sub_add_cancel hm1] at this
    rw [this]; simp
  refine ⟨(s6a_A F (evX F (Sum.inl c)) (Sum.inl c)).length + (if F.cuspDisc c.1 < 0 then 1 else 0),
    hlenA _ hj₂2, hidx _ hj₂2, hnext, ?_, ?_⟩
  · rw [next_val, s6a_cuspVertex_val, nextPair_cusp_r (word F) (hℓ.trans hℓ'), hbm]
    congr 1
    rw [hA]
    by_cases hn : F.cuspDisc c.1 < 0
    · simp [hn]; omega
    · simp [hn]; omega
  · exact s6a_not_σ_letter_right F hu (Nat.succ_ne_zero J₂) hbit hℓc

end S6aCusp

/-! #### Passing a crossing -/

section S6aCross

variable (F : SmoothFront)

theorem s6a_crossOf_over {p : F.Occ} (h : frontOver F p = true) :
    (crossOf F p).1 = (p.1, (partner F p).1) := by
  unfold crossOf; simp [h]

theorem s6a_crossOf_under {p : F.Occ} (h : frontOver F p = false) :
    (crossOf F p).1 = ((partner F p).1, p.1) := by
  unfold crossOf; simp [h]

theorem s6a_evX_crossOf (p : F.Occ) : evX F (Sum.inr (crossOf F p)) = xOf F p.1.1 p.1.2 := by
  cases h : frontOver F p
  · show (F.eval (crossOf F p).1.1).1 = (F.eval p.1).1
    rw [s6a_crossOf_under F h]
    show (F.eval (partner F p)).1 = _
    rw [eval_partner]
  · show (F.eval (crossOf F p).1.1).1 = (F.eval p.1).1
    rw [s6a_crossOf_over F h]

theorem s6a_evZ_crossOf (p : F.Occ) : evZ F (Sum.inr (crossOf F p)) = ht F p.1 := by
  cases h : frontOver F p
  · show (F.eval (crossOf F p).1.1).2 = (F.eval p.1).2
    rw [s6a_crossOf_under F h]
    show (F.eval (partner F p)).2 = _
    rw [eval_partner]
  · show (F.eval (crossOf F p).1.1).2 = (F.eval p.1).2
    rw [s6a_crossOf_over F h]

theorem s6a_ΦFun_val_over {p : F.Occ} (h : frontOver F p = true) :
    (ΦFun F p).1 = if bit (word F) (evIdx F (Sum.inr (crossOf F p))) (posOf F (Sum.inr (crossOf F p))) then
        (evIdx F (Sum.inr (crossOf F p)), posOf F (Sum.inr (crossOf F p)))
      else (evIdx F (Sum.inr (crossOf F p)) + 1, posOf F (Sum.inr (crossOf F p)) + 1) := by
  rw [ΦFun, ite_eq_left h]; exact s6a_σSlotA_val F _ _

theorem s6a_ΦFun_val_under {p : F.Occ} (h : frontOver F p = false) :
    (ΦFun F p).1 = if bit (word F) (evIdx F (Sum.inr (crossOf F p))) (posOf F (Sum.inr (crossOf F p)) + 1) then
        (evIdx F (Sum.inr (crossOf F p)), posOf F (Sum.inr (crossOf F p)) + 1)
      else (evIdx F (Sum.inr (crossOf F p)) + 1, posOf F (Sum.inr (crossOf F p))) := by
  rw [ΦFun, ite_eq_right (by simp [h])]; exact s6a_σSlotB_val F _ _

theorem s6a_over_not_cusp (q : Cross F) : ¬ F.IsCusp q.1.1 :=
  F.not_isCusp_of_isDouble (F.isOverUnder_of_mem_crossingPairs q.2).1

theorem s6a_under_not_cusp (q : Cross F) : ¬ F.IsCusp q.1.2 :=
  F.not_isCusp_of_isDouble (F.isOverUnder_of_mem_crossingPairs q.2).1.symm

/-- the window of a crossing column: the entries at cut `k_x` and cut `k_x + 1` -/
theorem s6a_cw_col (x₀ : ℝ) (q : Cross F) (hex : evX F (Sum.inr q) = x₀) :
    s6a_entCol F x₀ (evIdx F (Sum.inr q)) =
      s6a_A F x₀ (Sum.inr q) ++ [(q.1.1, 0), (q.1.2, 0)] ++ s6a_R F x₀ (Sum.inr q) := by
  obtain ⟨hk0, hkK⟩ := s6a_evIdx_mem F x₀ hex
  rw [s6a_entCol_of_lt F _ hkK, ← s6a_evZ_eq_colZ, s6a_hE_le, s6a_Eb_cross F x₀ q hex]

theorem s6a_cw_col' (x₀ : ℝ) (q : Cross F) (hex : evX F (Sum.inr q) = x₀) :
    s6a_entCol F x₀ (evIdx F (Sum.inr q) + 1) =
      s6a_A F x₀ (Sum.inr q) ++ [(q.1.2, 0), (q.1.1, 0)] ++ s6a_R F x₀ (Sum.inr q) := by
  obtain ⟨hk0, hkK⟩ := s6a_evIdx_mem F x₀ hex
  rw [s6a_entCol_succ F _ hk0 hkK, ← s6a_evZ_eq_colZ, s6a_hE_lt, s6a_Ea_cross F x₀ q hex]

theorem s6a_cw_A (x₀ : ℝ) (q : Cross F) (hex : evX F (Sum.inr q) = x₀) :
    (s6a_A F x₀ (Sum.inr q)).length = posOf F (Sum.inr q) - 1 := by
  rw [s6a_length_A F _ _ hex]; rfl

theorem s6a_cw_pos (q : Cross F) : 1 ≤ posOf F (Sum.inr q) := s6a_idx_pos F (Sum.inr q)

theorem s6a_cw_len (x₀ : ℝ) (q : Cross F) (hex : evX F (Sum.inr q) = x₀) (j : ℕ) (hj : j < 2) :
    (s6a_A F x₀ (Sum.inr q)).length + j < (s6a_entCol F x₀ (evIdx F (Sum.inr q))).length ∧
    (s6a_A F x₀ (Sum.inr q)).length + j < (s6a_entCol F x₀ (evIdx F (Sum.inr q) + 1)).length := by
  rw [s6a_cw_col F x₀ q hex, s6a_cw_col' F x₀ q hex]
  simp only [List.length_append, List.length_cons, List.length_nil]
  omega

theorem s6a_cw_get (x₀ : ℝ) (q : Cross F) (hex : evX F (Sum.inr q) = x₀) (j : ℕ) (hj : j < 2) :
    (s6a_entCol F x₀ (evIdx F (Sum.inr q)))[(s6a_A F x₀ (Sum.inr q)).length + j]'((s6a_cw_len F x₀ q hex j hj).1) =
      [(q.1.1, 0), (q.1.2, 0)][j]'(by simpa using hj) ∧
    (s6a_entCol F x₀ (evIdx F (Sum.inr q) + 1))[(s6a_A F x₀ (Sum.inr q)).length + j]'((s6a_cw_len F x₀ q hex j hj).2) =
      [(q.1.2, 0), (q.1.1, 0)][j]'(by simpa using hj) := by
  constructor
  · rw [List.getElem_of_eq (s6a_cw_col F x₀ q hex), s6a_getElem_E _ _ _ j (by simpa using hj)]
  · rw [List.getElem_of_eq (s6a_cw_col' F x₀ q hex), s6a_getElem_E _ _ _ j (by simpa using hj)]

/-- the bits of the two crossing strands at cut `k_x` (before the crossing) and cut `k_x + 1` (after) -/
theorem s6a_cw_bit (x₀ : ℝ) (q : Cross F) (hex : evX F (Sum.inr q) = x₀) (j : ℕ) (hj : j < 2) :
    bit (word F) (evIdx F (Sum.inr q)) ((s6a_A F x₀ (Sum.inr q)).length + j + 1) =
      dirBit F ([q.1.1, q.1.2][j]'(by simpa using hj)) ∧
    bit (word F) (evIdx F (Sum.inr q) + 1) ((s6a_A F x₀ (Sum.inr q)).length + j + 1) =
      dirBit F ([q.1.2, q.1.1][j]'(by simpa using hj)) := by
  obtain ⟨hk0, hkK⟩ := s6a_evIdx_mem F x₀ hex
  have hz : colZ F (evIdx F (Sum.inr q)) = evZ F (Sum.inr q) := (s6a_evZ_eq_colZ F _).symm
  have hzo : ht F q.1.1 = evZ F (Sum.inr q) := rfl
  have hzu : ht F q.1.2 = evZ F (Sum.inr q) := s6a_ht_under F q
  obtain ⟨hlen1, hlen2⟩ := s6a_cw_len F x₀ q hex j hj
  obtain ⟨hget1, hget2⟩ := s6a_cw_get F x₀ q hex j hj
  obtain ⟨hbo, hbo'⟩ := s6a_bits_of_not_cusp F (s6a_over_not_cusp F q)
  obtain ⟨hbu, hbu'⟩ := s6a_bits_of_not_cusp F (s6a_under_not_cusp F q)
  constructor
  · have hJ' : (s6a_A F x₀ (Sum.inr q)).length + j <
        (hybridEntriesP F x₀ (fun p => decide (colZ F (evIdx F (Sum.inr q)) ≤ ht F p))).length := by
      rw [← s6a_entCol_of_lt F _ hkK]; exact hlen1
    have h1 := s6a_bit_of_entry F x₀ (fun p => decide (colZ F (evIdx F (Sum.inr q)) ≤ ht F p)) hJ'
    have ha' : (hybridEntriesP F x₀ (fun p => decide (colZ F (evIdx F (Sum.inr q)) ≤ ht F p)))[(s6a_A F x₀ (Sum.inr q)).length + j] =
        [(q.1.1, 0), (q.1.2, 0)][j]'(by simpa using hj) := by
      rw [← List.getElem_of_eq (s6a_entCol_of_lt F _ hkK) hlen1]; exact hget1
    rw [bit_eq, Nat.add_sub_cancel, s6a_cut_eq F x₀ hk0 hkK, h1, ha']
    interval_cases j
    · simp only [List.getElem_cons_zero, hz, hzo, le_refl, decide_true, ↓reduceIte]
      unfold entryBit; rw [hbo]; rfl
    · simp only [List.getElem_cons_succ, List.getElem_cons_zero, hz, hzu, le_refl, decide_true, ↓reduceIte]
      unfold entryBit; rw [hbu]; rfl
  · have hJ' : (s6a_A F x₀ (Sum.inr q)).length + j <
        (hybridEntriesP F x₀ (fun p => decide (colZ F (evIdx F (Sum.inr q)) < ht F p))).length := by
      rw [← s6a_entCol_succ F _ hk0 hkK]; exact hlen2
    have h1 := s6a_bit_of_entry F x₀ (fun p => decide (colZ F (evIdx F (Sum.inr q)) < ht F p)) hJ'
    have ha' : (hybridEntriesP F x₀ (fun p => decide (colZ F (evIdx F (Sum.inr q)) < ht F p)))[(s6a_A F x₀ (Sum.inr q)).length + j] =
        [(q.1.2, 0), (q.1.1, 0)][j]'(by simpa using hj) := by
      rw [← List.getElem_of_eq (s6a_entCol_succ F _ hk0 hkK) hlen2]; exact hget2
    rw [bit_eq, Nat.add_sub_cancel, s6a_cut_succ_eq F x₀ hk0 hkK, h1, ha']
    interval_cases j
    · simp only [List.getElem_cons_zero, hz, hzu, lt_self_iff_false, decide_false, Bool.false_eq_true, ↓reduceIte]
      unfold entryBit; rw [hbu']; rfl
    · simp only [List.getElem_cons_succ, List.getElem_cons_zero, hz, hzo, lt_self_iff_false, decide_false,
        Bool.false_eq_true, ↓reduceIte]
      unfold entryBit; rw [hbo']; rfl

/-- the index of a crossing strand's entry at cut `k_x` / `k_x + 1` is one of the two window indices -/
theorem s6a_cw_index (x₀ : ℝ) (q : Cross F) (hex : evX F (Sum.inr q) = x₀) {a : Param F.c × ℕ}
    (ha : a = (q.1.1, 0) ∨ a = (q.1.2, 0)) :
    (∀ J (hJ : J < (s6a_entCol F x₀ (evIdx F (Sum.inr q))).length), (s6a_entCol F x₀ (evIdx F (Sum.inr q)))[J] = a →
      J = (s6a_A F x₀ (Sum.inr q)).length + (if a = (q.1.1, 0) then 0 else 1)) ∧
    (∀ J (hJ : J < (s6a_entCol F x₀ (evIdx F (Sum.inr q) + 1)).length), (s6a_entCol F x₀ (evIdx F (Sum.inr q) + 1))[J] = a →
      J = (s6a_A F x₀ (Sum.inr q)).length + (if a = (q.1.1, 0) then 1 else 0)) := by
  obtain ⟨hk0, hkK⟩ := s6a_evIdx_mem F x₀ hex
  have hnd : (s6a_entCol F x₀ (evIdx F (Sum.inr q))).Nodup := by
    rw [s6a_entCol_of_lt F _ hkK]; exact s6a_hybridEntriesP_nodup F _ _
  have hnd' : (s6a_entCol F x₀ (evIdx F (Sum.inr q) + 1)).Nodup := by
    rw [s6a_entCol_succ F _ hk0 hkK]; exact s6a_hybridEntriesP_nodup F _ _
  have hne : q.1.1 ≠ q.1.2 := (F.mem_crossingPairs'.mp q.2).1.2.2.1
  constructor
  · intro J hJ hJa
    rcases ha with rfl | rfl
    · rw [if_pos rfl]
      have := (s6a_cw_get F x₀ q hex 0 (by omega)).1
      rw [← hnd.getElem_inj_iff (hi := hJ) (hj := (s6a_cw_len F x₀ q hex 0 (by omega)).1), hJa, this]; rfl
    · rw [if_neg (by simp [Ne.symm hne])]
      have := (s6a_cw_get F x₀ q hex 1 (by omega)).1
      rw [← hnd.getElem_inj_iff (hi := hJ) (hj := (s6a_cw_len F x₀ q hex 1 (by omega)).1), hJa, this]; rfl
  · intro J hJ hJa
    rcases ha with rfl | rfl
    · rw [if_pos rfl]
      have := (s6a_cw_get F x₀ q hex 1 (by omega)).2
      rw [← hnd'.getElem_inj_iff (hi := hJ) (hj := (s6a_cw_len F x₀ q hex 1 (by omega)).2), hJa, this]; rfl
    · rw [if_neg (by simp [Ne.symm hne])]
      have := (s6a_cw_get F x₀ q hex 0 (by omega)).2
      rw [← hnd'.getElem_inj_iff (hi := hJ) (hj := (s6a_cw_len F x₀ q hex 0 (by omega)).2), hJa, this]; rfl

theorem s6a_occ_mem_totalFibre (p : F.Occ) : p.1 ∈ totalFibre F (xOf F p.1.1 p.1.2) := ⟨p.2.1, rfl⟩

theorem s6a_occ_not_cusp (p : F.Occ) : ¬ F.IsCusp p.1 := F.not_isCusp_of_isDouble (isDouble_partner F p)

theorem s6a_occ_eq_over_or_under (p : F.Occ) :
    ((p.1, 0) : Param F.c × ℕ) = ((crossOf F p).1.1, 0) ∨ ((p.1, 0) : Param F.c × ℕ) = ((crossOf F p).1.2, 0) := by
  cases h : frontOver F p
  · right; rw [s6a_crossOf_under F h]
  · left; rw [s6a_crossOf_over F h]

/-- Through a crossing, rightward: the strand of `p` at cut `k_x` IS `Φ p`, and `next` moves it to cut `k_x + 1`. -/
theorem s6a_cross_pass_right (p : F.Occ) (hdir : 0 < xvel F p.1.1 p.1.2) {J : ℕ}
    (hJ : J < (s6a_entCol F (xOf F p.1.1 p.1.2) (evIdx F (Sum.inr (crossOf F p)))).length)
    (ha : (s6a_entCol F (xOf F p.1.1 p.1.2) (evIdx F (Sum.inr (crossOf F p))))[J] = (p.1, 0))
    (u : Slot (word F)) (hu : u.1 = (evIdx F (Sum.inr (crossOf F p)), J + 1)) :
    u = ΦFun F p ∧ ∃ J', ∃ hJ' : J' < (s6a_entCol F (xOf F p.1.1 p.1.2) (evIdx F (Sum.inr (crossOf F p)) + 1)).length,
      (s6a_entCol F (xOf F p.1.1 p.1.2) (evIdx F (Sum.inr (crossOf F p)) + 1))[J'] = (p.1, 0) ∧
      (next (word_closed F) u).1 = (evIdx F (Sum.inr (crossOf F p)) + 1, J' + 1) := by
  have hex : evX F (Sum.inr (crossOf F p)) = xOf F p.1.1 p.1.2 := s6a_evX_crossOf F p
  have hkn : evIdx F (Sum.inr (crossOf F p)) < (events F).length := evIdx_lt_length F _
  have hℓ : letterAt (word F) (evIdx F (Sum.inr (crossOf F p))) = Letter.σ (posOf F (Sum.inr (crossOf F p))) :=
    letterAt_word_cross F _
  have hA := s6a_cw_A F _ _ hex
  have hm1 := s6a_cw_pos F (crossOf F p)
  have hdb : dirBit F p.1 = true := decide_eq_true hdir
  cases hfo : frontOver F p
  · -- `p` is the under branch: at position `m + 1`
    have hq := s6a_crossOf_under F hfo
    have hJeq := (s6a_cw_index F _ _ hex (a := (p.1, 0)) (Or.inr (by rw [hq]))).1 J hJ ha
    rw [if_neg (by rw [hq]; intro h; exact partner_ne F p (Subtype.ext (congrArg Prod.fst h)).symm)] at hJeq
    have hbit : bit (word F) (evIdx F (Sum.inr (crossOf F p))) (J + 1) = true := by
      rw [hJeq, (s6a_cw_bit F _ _ hex 1 (by omega)).1]
      show dirBit F (crossOf F p).1.2 = true
      rw [hq]; exact hdb
    have hpr : (letterAt (word F) (evIdx F (Sum.inr (crossOf F p)))).posR (J + 1) =
        some ((s6a_A F (xOf F p.1.1 p.1.2) (Sum.inr (crossOf F p))).length + 0 + 1) := by
      rw [hℓ, show J + 1 = posOf F (Sum.inr (crossOf F p)) + 1 by omega, posR_σ_idx_succ]
      congr 1; omega
    refine ⟨?_, (s6a_A F (xOf F p.1.1 p.1.2) (Sum.inr (crossOf F p))).length + 0,
      (s6a_cw_len F _ _ hex 0 (by omega)).2, ?_, ?_⟩
    · apply Subtype.ext
      rw [hu, s6a_ΦFun_val_under F hfo]
      have : J + 1 = posOf F (Sum.inr (crossOf F p)) + 1 := by omega
      rw [this, ite_eq_left (by rw [← this]; exact hbit)]
    · rw [(s6a_cw_get F _ _ hex 0 (by omega)).2]; show ((crossOf F p).1.2, 0) = _; rw [hq]
    · rw [next_val, hu, nextPair_right (word F) (Nat.succ_ne_zero J) hbit hpr]
  · -- `p` is the over branch: at position `m`
    have hq := s6a_crossOf_over F hfo
    have hJeq := (s6a_cw_index F _ _ hex (a := (p.1, 0)) (Or.inl (by rw [hq]))).1 J hJ ha
    rw [if_pos (by rw [hq])] at hJeq
    have hbit : bit (word F) (evIdx F (Sum.inr (crossOf F p))) (J + 1) = true := by
      rw [hJeq, (s6a_cw_bit F _ _ hex 0 (by omega)).1]
      show dirBit F (crossOf F p).1.1 = true
      rw [hq]; exact hdb
    have hpr : (letterAt (word F) (evIdx F (Sum.inr (crossOf F p)))).posR (J + 1) =
        some ((s6a_A F (xOf F p.1.1 p.1.2) (Sum.inr (crossOf F p))).length + 1 + 1) := by
      rw [hℓ, show J + 1 = posOf F (Sum.inr (crossOf F p)) by omega, posR_σ_idx]
      congr 1; omega
    refine ⟨?_, (s6a_A F (xOf F p.1.1 p.1.2) (Sum.inr (crossOf F p))).length + 1,
      (s6a_cw_len F _ _ hex 1 (by omega)).2, ?_, ?_⟩
    · apply Subtype.ext
      rw [hu, s6a_ΦFun_val_over F hfo]
      have : J + 1 = posOf F (Sum.inr (crossOf F p)) := by omega
      rw [this, ite_eq_left (by rw [← this]; exact hbit)]
    · rw [(s6a_cw_get F _ _ hex 1 (by omega)).2]; show ((crossOf F p).1.1, 0) = _; rw [hq]
    · rw [next_val, hu, nextPair_right (word F) (Nat.succ_ne_zero J) hbit hpr]

/-- Through a crossing, leftward: the strand of `p` at cut `k_x + 1` IS `Φ p`, and `next` moves it to cut `k_x`. -/
theorem s6a_cross_pass_left (p : F.Occ) (hdir : xvel F p.1.1 p.1.2 < 0) {J : ℕ}
    (hJ : J < (s6a_entCol F (xOf F p.1.1 p.1.2) (evIdx F (Sum.inr (crossOf F p)) + 1)).length)
    (ha : (s6a_entCol F (xOf F p.1.1 p.1.2) (evIdx F (Sum.inr (crossOf F p)) + 1))[J] = (p.1, 0))
    (u : Slot (word F)) (hu : u.1 = (evIdx F (Sum.inr (crossOf F p)) + 1, J + 1)) :
    u = ΦFun F p ∧ ∃ J', ∃ hJ' : J' < (s6a_entCol F (xOf F p.1.1 p.1.2) (evIdx F (Sum.inr (crossOf F p)))).length,
      (s6a_entCol F (xOf F p.1.1 p.1.2) (evIdx F (Sum.inr (crossOf F p))))[J'] = (p.1, 0) ∧
      (next (word_closed F) u).1 = (evIdx F (Sum.inr (crossOf F p)), J' + 1) := by
  have hex : evX F (Sum.inr (crossOf F p)) = xOf F p.1.1 p.1.2 := s6a_evX_crossOf F p
  have hkn : evIdx F (Sum.inr (crossOf F p)) < (events F).length := evIdx_lt_length F _
  have hℓ : letterAt (word F) (evIdx F (Sum.inr (crossOf F p))) = Letter.σ (posOf F (Sum.inr (crossOf F p))) :=
    letterAt_word_cross F _
  have hA := s6a_cw_A F _ _ hex
  have hm1 := s6a_cw_pos F (crossOf F p)
  have hdb : dirBit F p.1 = false := decide_eq_false (not_lt.mpr hdir.le)
  cases hfo : frontOver F p
  · -- `p` is the under branch: after the crossing at position `m`
    have hq := s6a_crossOf_under F hfo
    have hJeq := (s6a_cw_index F _ _ hex (a := (p.1, 0)) (Or.inr (by rw [hq]))).2 J hJ ha
    rw [if_neg (by rw [hq]; intro h; exact partner_ne F p (Subtype.ext (congrArg Prod.fst h)).symm)] at hJeq
    have hbit : bit (word F) (evIdx F (Sum.inr (crossOf F p)) + 1) (J + 1) = false := by
      rw [hJeq, (s6a_cw_bit F _ _ hex 0 (by omega)).2]
      show dirBit F (crossOf F p).1.2 = false
      rw [hq]; exact hdb
    have hbitB : bit (word F) (evIdx F (Sum.inr (crossOf F p))) (posOf F (Sum.inr (crossOf F p)) + 1) = false := by
      have := (s6a_cw_bit F _ _ hex 1 (by omega)).1
      rw [hA, show posOf F (Sum.inr (crossOf F p)) - 1 + 1 + 1 = posOf F (Sum.inr (crossOf F p)) + 1 by omega] at this
      rw [this]; show dirBit F (crossOf F p).1.2 = false; rw [hq]; exact hdb
    have hpl : (letterAt (word F) (evIdx F (Sum.inr (crossOf F p)) + 1 - 1)).posL (J + 1) =
        some ((s6a_A F (xOf F p.1.1 p.1.2) (Sum.inr (crossOf F p))).length + 1 + 1) := by
      rw [Nat.add_sub_cancel, hℓ, show J + 1 = posOf F (Sum.inr (crossOf F p)) by omega, posL_σ_idx]
      congr 1; omega
    refine ⟨?_, (s6a_A F (xOf F p.1.1 p.1.2) (Sum.inr (crossOf F p))).length + 1,
      (s6a_cw_len F _ _ hex 1 (by omega)).1, ?_, ?_⟩
    · apply Subtype.ext
      rw [hu, s6a_ΦFun_val_under F hfo, ite_eq_right (by rw [hbitB]; exact Bool.false_ne_true)]
      congr 1; omega
    · rw [(s6a_cw_get F _ _ hex 1 (by omega)).1]; show ((crossOf F p).1.2, 0) = _; rw [hq]
    · rw [next_val, hu, nextPair_left (word F) (Nat.succ_ne_zero J) hbit hpl, Nat.add_sub_cancel]
  · -- `p` is the over branch: after the crossing at position `m + 1`
    have hq := s6a_crossOf_over F hfo
    have hJeq := (s6a_cw_index F _ _ hex (a := (p.1, 0)) (Or.inl (by rw [hq]))).2 J hJ ha
    rw [if_pos (by rw [hq])] at hJeq
    have hbit : bit (word F) (evIdx F (Sum.inr (crossOf F p)) + 1) (J + 1) = false := by
      rw [hJeq, (s6a_cw_bit F _ _ hex 1 (by omega)).2]
      show dirBit F (crossOf F p).1.1 = false
      rw [hq]; exact hdb
    have hbitA : bit (word F) (evIdx F (Sum.inr (crossOf F p))) (posOf F (Sum.inr (crossOf F p))) = false := by
      have := (s6a_cw_bit F _ _ hex 0 (by omega)).1
      rw [hA, Nat.add_zero, Nat.sub_add_cancel hm1] at this
      rw [this]; show dirBit F (crossOf F p).1.1 = false; rw [hq]; exact hdb
    have hpl : (letterAt (word F) (evIdx F (Sum.inr (crossOf F p)) + 1 - 1)).posL (J + 1) =
        some ((s6a_A F (xOf F p.1.1 p.1.2) (Sum.inr (crossOf F p))).length + 0 + 1) := by
      rw [Nat.add_sub_cancel, hℓ, show J + 1 = posOf F (Sum.inr (crossOf F p)) + 1 by omega, posL_σ_idx_succ]
      congr 1; omega
    refine ⟨?_, (s6a_A F (xOf F p.1.1 p.1.2) (Sum.inr (crossOf F p))).length + 0,
      (s6a_cw_len F _ _ hex 0 (by omega)).1, ?_, ?_⟩
    · apply Subtype.ext
      rw [hu, s6a_ΦFun_val_over F hfo, ite_eq_right (by rw [hbitA]; exact Bool.false_ne_true)]
      congr 1; omega
    · rw [(s6a_cw_get F _ _ hex 0 (by omega)).1]; show ((crossOf F p).1.1, 0) = _; rw [hq]
    · rw [next_val, hu, nextPair_left (word F) (Nat.succ_ne_zero J) hbit hpl, Nat.add_sub_cancel]

end S6aCross

/-! #### The singular parameters of an interval -/

section S6aPath

variable (F : SmoothFront)

/-- the parameters of an interval over one singular value are finitely many -/
theorem s6a_params_over_finite (i : Fin F.c) (t₀ t₁ y : ℝ) :
    {s : ℝ | s ∈ Set.Icc t₀ t₁ ∧ xOf F i s = y}.Finite := by
  have hsub : {s : ℝ | s ∈ Set.Icc t₀ t₁ ∧ xOf F i s = y} ⊆
      ⋃ n ∈ (Finset.Icc ⌊t₀⌋ ⌊t₁⌋ : Set ℤ), (fun r => r + (n : ℝ)) '' fibre F i y := by
    intro s ⟨hs, hxs⟩
    rw [Set.mem_iUnion₂]
    refine ⟨⌊s⌋, ?_, Int.fract s, ⟨⟨Int.fract_nonneg _, Int.fract_lt_one _⟩, ?_⟩, ?_⟩
    · simp only [Finset.coe_Icc, Set.mem_Icc]
      exact ⟨Int.floor_le_floor hs.1, Int.floor_le_floor hs.2⟩
    · show xOf F i (Int.fract s) = y
      rw [← hxs, ← Int.self_sub_floor, show s - (⌊s⌋ : ℝ) = s + ((-⌊s⌋ : ℤ) : ℝ) by push_cast; ring, s6a_xOf_add_int]
    · show Int.fract s + (⌊s⌋ : ℝ) = s
      exact Int.fract_add_floor s
  exact (Set.Finite.biUnion (Finset.finite_toSet _) (fun n _ => (fibre_finite F i y).image _)).subset hsub

/-- the singular parameters of a closed interval are finitely many -/
theorem s6a_sing_params_finite (i : Fin F.c) (t₀ t₁ : ℝ) :
    {s : ℝ | s ∈ Set.Icc t₀ t₁ ∧ xOf F i s ∈ singX F}.Finite := by
  have hsub : {s : ℝ | s ∈ Set.Icc t₀ t₁ ∧ xOf F i s ∈ singX F} ⊆
      ⋃ y ∈ (singX F : Set ℝ), {s : ℝ | s ∈ Set.Icc t₀ t₁ ∧ xOf F i s = y} := by
    intro s ⟨hs, hxs⟩
    rw [Set.mem_iUnion₂]
    exact ⟨xOf F i s, hxs, hs, rfl⟩
  exact (Set.Finite.biUnion (Finset.finite_toSet _) (fun y _ => s6a_params_over_finite F i t₀ t₁ y)).subset hsub

/-- a double point of a circle gives an occurrence at the same parameter -/
theorem s6a_occ_of_isDouble {i : Fin F.c} {s : ℝ} {r : Param F.c} (h : F.IsDouble (i, s) r) :
    ∃ p : F.Occ, p.1.1 = i ∧ SameParam p.1 (i, s) := by
  have hsp : SameParam (i, s) (SameParam.rep (i, s)) := SameParam.sameParam_rep (i, s)
  have hsr : SameParam r (SameParam.rep r) := SameParam.sameParam_rep r
  refine ⟨⟨SameParam.rep (i, s), SameParam.rep_mem_Ico _, SameParam.rep r, SameParam.rep_mem_Ico _, ?_, ?_⟩, rfl, hsp.symm⟩
  · intro heq
    apply h.1
    exact hsp.trans (heq ▸ hsr.symm)
  · rw [SmoothFront.eval_of_sameParam hsp, SmoothFront.eval_of_sameParam hsr]
    exact h.2

end S6aPath








end S6aHelpers

/-- LEAF (S6): the slot of a strand at its cut line is a slot (`cut_word_colAt`; `posAt ≤` the fibre size). -/
theorem isSlot_slotAt {i : Fin F.c} {t : ℝ} (h : xOf F i t ∉ singX F) :
    IsSlot (word F) (colAt F (xOf F i t), posAt F (xOf F i t) (i, Int.fract t)) := by
  right
  refine ⟨?_, ?_, ?_⟩
  · unfold posAt; omega
  · rw [cut_word_colAt F h, cutBefore_eq_map_dirBit F h, List.length_map]
    obtain ⟨J, hJ, hq⟩ := List.mem_iff_getElem.mp
      ((mem_fibreListBefore F _ _).mpr (s6a_rep_mem_totalFibre F i t))
    rw [← hq, s6a_posAt_eq F h hJ]
    exact hJ
  · unfold colAt; rw [length_word]; exact List.length_filter_le _ _

/-- THE SLOT OF A STRAND at a non-singular x-value: the cut line of that x-value and the strand's position. -/
def slotAt (i : Fin F.c) (t : ℝ) (h : xOf F i t ∉ singX F) : Slot (word F) := ⟨_, isSlot_slotAt F h⟩

/-- LEAF (S6): the slot is constant along a regular arc avoiding the singular x-values (`posAt_const_of_arc`). -/
theorem slotAt_const {i : Fin F.c} {t₀ t₁ : ℝ} (h01 : t₀ ≤ t₁)
    (hreg : ∀ t ∈ Set.Icc t₀ t₁, xOf F i t ∉ singX F) :
    slotAt F i t₀ (hreg t₀ ⟨le_rfl, h01⟩) = slotAt F i t₁ (hreg t₁ ⟨h01, le_rfl⟩) := by
  apply Subtype.ext
  obtain ⟨h1, h2⟩ := posAt_const_of_arc F h01 hreg
  show (colAt F (xOf F i t₀), posAt F (xOf F i t₀) (i, Int.fract t₀)) =
    (colAt F (xOf F i t₁), posAt F (xOf F i t₁) (i, Int.fract t₁))
  rw [h1, h2]

/-- LEAF (S6, jump through a regular point over a singular x-value): the slot advances by `next` steps through the
tie columns (`posR`/`posL` on positions not touched by the letters, `next_cases`, `run_take_eq_hybrid`), meeting no
`σ` slot. -/
theorem jump_regular {i : Fin F.c} {t : ℝ} (hx : xOf F i t ∈ singX F) (hc : ¬ F.IsCusp (i, t))
    (hd : ∀ q, ¬ F.IsDouble (i, t) q) :
    ∃ ε > 0, ∀ ε' ∈ Set.Ioo (0 : ℝ) ε, ∃ (h₁ : xOf F i (t - ε') ∉ singX F) (h₂ : xOf F i (t + ε') ∉ singX F) (m : ℕ),
      0 < m ∧ (next (word_closed F))^[m] (slotAt F i (t - ε') h₁) = slotAt F i (t + ε') h₂ ∧
      ∀ j < m, ¬ U2.IsσSlot ((next (word_closed F))^[j] (slotAt F i (t - ε') h₁)) := by
  -- the regular fibre point and the analytic data
  have hq₀mem : (i, Int.fract t) ∈ totalFibre F (xOf F i t) := s6a_rep_mem_totalFibre F i t
  obtain ⟨hq₀c, hq₀d⟩ := s6a_regular_rep F hc hd
  obtain ⟨hb1, hb2⟩ := s6a_entryBit_regular F hq₀c
  obtain ⟨δ₁, hδ₁, hnc⟩ := s6a_no_cusp_near F hc
  obtain ⟨η₁, hη₁, hL⟩ := entriesBefore_left_limit F (xOf F i t)
  obtain ⟨η₂, hη₂, hR⟩ := entriesAfter_right_limit F (xOf F i t)
  obtain ⟨η₃, hη₃, hgap⟩ := s6a_singX_gap F (xOf F i t)
  obtain ⟨δ₂, hδ₂, hcont⟩ := s6a_x_cont F (i := i) t (lt_min (lt_min hη₁ hη₂) hη₃)
  have hxv := xvel_ne_zero_of_not_isCusp F hc
  have hk0K := s6a_k0_lt_K F (xOf F i t) hx
  have hne : ∀ k', s6a_k0 F (xOf F i t) ≤ k' → k' < s6a_k0 F (xOf F i t) + (s6a_K F (xOf F i t) - s6a_k0 F (xOf F i t)) →
      ht F ((i, Int.fract t), 0).1 ≠ colZ F k' := fun k' h1 h2 =>
    s6a_ht_ne_colZ_of_regular F hq₀mem hq₀c hq₀d h1 (by omega)
  -- the two candidate directions
  rcases lt_or_gt_of_ne hxv with hneg | hpos
  · -- leftward: `t - ε'` lies to the RIGHT of `x₀`, the walk goes leftward from cut `K` to cut `k0`
    obtain ⟨δ₃, hδ₃, hside⟩ := s6a_side_neg F hneg
    refine ⟨min δ₁ (min δ₂ δ₃), lt_min hδ₁ (lt_min hδ₂ hδ₃), fun ε' hε' => ?_⟩
    have hε'0 : 0 < ε' := hε'.1
    have hε'1 : ε' < δ₁ := lt_of_lt_of_le hε'.2 (min_le_left _ _)
    have hε'2 : ε' < δ₂ := lt_of_lt_of_le hε'.2 (le_trans (min_le_right _ _) (min_le_left _ _))
    have hε'3 : ε' < δ₃ := lt_of_lt_of_le hε'.2 (le_trans (min_le_right _ _) (min_le_right _ _))
    have hdm := s6a_dist_sub t ε' hε'.1
    have hdp := s6a_dist_add t ε' hε'.1
    have hxm : xOf F i t < xOf F i (t - ε') := (hside _ (by rw [hdm]; exact hε'3)).1 (by linarith)
    have hxp : xOf F i (t + ε') < xOf F i t := (hside _ (by rw [hdp]; exact hε'3)).2 (by linarith)
    have hcm := hcont _ (by rw [hdm]; exact hε'2)
    have hcp := hcont _ (by rw [hdp]; exact hε'2)
    obtain ⟨hnm, -, hcolm⟩ := s6a_colAt_near F (xOf F i t) hgap
      (lt_of_lt_of_le hcm (min_le_right _ _)) (ne_of_gt hxm)
    obtain ⟨hnp, hcolp, -⟩ := s6a_colAt_near F (xOf F i t) hgap
      (lt_of_lt_of_le hcp (min_le_right _ _)) (ne_of_lt hxp)
    have hfm : s6a_Free F i t (t - ε') := s6a_Free_of_near F hnc (by rw [← Real.dist_eq, hdm]; exact hε'1)
    have hfp : s6a_Free F i t (t + ε') := s6a_Free_of_near F hnc (by rw [← Real.dist_eq, hdp]; exact hε'1)
    have hncm : ¬ F.IsCusp (i, t - ε') := hnc _ (by rw [hdm]; exact hε'1)
    refine ⟨hnm, hnp, s6a_K F (xOf F i t) - s6a_k0 F (xOf F i t), by omega, ?_⟩
    -- START at cut `K`
    have hlimR := hR (xOf F i (t - ε')) ⟨hxm, by
      linarith [(abs_lt.mp hcm).2, min_le_left (min η₁ η₂) η₃, min_le_right η₁ η₂]⟩
    obtain ⟨J, hJ, haJ, -, hposJ⟩ := s6a_start_after F hfm hncm hnm hlimR
    have ha : (entriesAfter F (xOf F i t))[J] = ((i, Int.fract t), 0) := by
      have hm := (s6a_mem_entriesOf F).mp (show (entriesAfter F (xOf F i t))[J] ∈
        entriesOf F (afterBits F) (fibreListAfter F (xOf F i t)) from List.getElem_mem hJ)
      rw [haJ, (s6a_bits_of_not_cusp F hq₀c).2] at hm
      exact Prod.ext haJ (by simpa using hm.2)
    have hentK := s6a_entCol_K_eq F (xOf F i t) hx
    have hJ' : J < (s6a_entCol F (xOf F i t) (s6a_K F (xOf F i t))).length := by rw [hentK]; exact hJ
    have ha' : (s6a_entCol F (xOf F i t) (s6a_K F (xOf F i t)))[J] = ((i, Int.fract t), 0) := by
      rw [List.getElem_of_eq hentK]; exact ha
    have hu : (slotAt F i (t - ε') hnm).1 = (s6a_k0 F (xOf F i t) + (s6a_K F (xOf F i t) - s6a_k0 F (xOf F i t)), J + 1) := by
      show (colAt F (xOf F i (t - ε')), posAt F (xOf F i (t - ε')) (i, Int.fract (t - ε'))) = _
      rw [hcolm hxm, hposJ]; congr 1; omega
    have hbit : ∀ k', s6a_k0 F (xOf F i t) ≤ k' → k' < s6a_k0 F (xOf F i t) + (s6a_K F (xOf F i t) - s6a_k0 F (xOf F i t)) →
        (if colZ F k' < ht F ((i, Int.fract t), 0).1 then entryBit F (beforeBits F) ((i, Int.fract t), 0)
          else entryBit F (afterBits F) ((i, Int.fract t), 0)) = false := by
      intro k' _ _
      rw [hb1, hb2, ite_self, s6a_dirBit_rep]
      simp [not_lt.mpr hneg.le]
    have hJ'' : J < (s6a_entCol F (xOf F i t) (s6a_k0 F (xOf F i t) + (s6a_K F (xOf F i t) - s6a_k0 F (xOf F i t)))).length := by
      rw [show s6a_k0 F (xOf F i t) + (s6a_K F (xOf F i t) - s6a_k0 F (xOf F i t)) = s6a_K F (xOf F i t) by omega]; exact hJ'
    have ha'' : (s6a_entCol F (xOf F i t) (s6a_k0 F (xOf F i t) + (s6a_K F (xOf F i t) - s6a_k0 F (xOf F i t))))[J] = ((i, Int.fract t), 0) := by
      rw [List.getElem_of_eq (show s6a_entCol F (xOf F i t) (s6a_k0 F (xOf F i t) + (s6a_K F (xOf F i t) - s6a_k0 F (xOf F i t))) = s6a_entCol F (xOf F i t) (s6a_K F (xOf F i t)) by
        rw [show s6a_k0 F (xOf F i t) + (s6a_K F (xOf F i t) - s6a_k0 F (xOf F i t)) = s6a_K F (xOf F i t) by omega])]
      exact ha'
    obtain ⟨J', hJ'₁, ha'₁, hpath, hσ⟩ := s6a_walk_left F (xOf F i t) ((i, Int.fract t), 0) _ _ le_rfl (by omega) hne hbit J hJ'' ha'' _ hu
    refine ⟨?_, hσ⟩
    -- END at cut `k0`
    apply Subtype.ext
    rw [hpath]
    have hentk0 := s6a_entCol_k0 F (xOf F i t) hx
    have hJ'₂ : J' < (entriesBefore F (xOf F i t)).length := by rw [← hentk0]; exact hJ'₁
    have ha'₂ : (entriesBefore F (xOf F i t))[J'] = ((i, Int.fract t), 0) := by
      rw [← List.getElem_of_eq hentk0 hJ'₁]; exact ha'₁
    have hlimL := hL (xOf F i (t + ε')) ⟨by
      linarith [(abs_lt.mp hcp).1, min_le_left (min η₁ η₂) η₃, min_le_left η₁ η₂], hxp⟩
    have hpos' := s6a_end_before F hfp hnp hlimL hJ'₂ (congrArg Prod.fst ha'₂) (Or.inl hc)
    show _ = (colAt F (xOf F i (t + ε')), posAt F (xOf F i (t + ε')) (i, Int.fract (t + ε')))
    rw [hcolp hxp, hpos']
  · -- rightward: `t - ε'` lies to the LEFT of `x₀`, the walk goes rightward from cut `k0` to cut `K`
    obtain ⟨δ₃, hδ₃, hside⟩ := s6a_side_pos F hpos
    refine ⟨min δ₁ (min δ₂ δ₃), lt_min hδ₁ (lt_min hδ₂ hδ₃), fun ε' hε' => ?_⟩
    have hε'0 : 0 < ε' := hε'.1
    have hε'1 : ε' < δ₁ := lt_of_lt_of_le hε'.2 (min_le_left _ _)
    have hε'2 : ε' < δ₂ := lt_of_lt_of_le hε'.2 (le_trans (min_le_right _ _) (min_le_left _ _))
    have hε'3 : ε' < δ₃ := lt_of_lt_of_le hε'.2 (le_trans (min_le_right _ _) (min_le_right _ _))
    have hdm := s6a_dist_sub t ε' hε'.1
    have hdp := s6a_dist_add t ε' hε'.1
    have hxm : xOf F i (t - ε') < xOf F i t := (hside _ (by rw [hdm]; exact hε'3)).1 (by linarith)
    have hxp : xOf F i t < xOf F i (t + ε') := (hside _ (by rw [hdp]; exact hε'3)).2 (by linarith)
    have hcm := hcont _ (by rw [hdm]; exact hε'2)
    have hcp := hcont _ (by rw [hdp]; exact hε'2)
    obtain ⟨hnm, hcolm, -⟩ := s6a_colAt_near F (xOf F i t) hgap
      (lt_of_lt_of_le hcm (min_le_right _ _)) (ne_of_lt hxm)
    obtain ⟨hnp, -, hcolp⟩ := s6a_colAt_near F (xOf F i t) hgap
      (lt_of_lt_of_le hcp (min_le_right _ _)) (ne_of_gt hxp)
    have hfm : s6a_Free F i t (t - ε') := s6a_Free_of_near F hnc (by rw [← Real.dist_eq, hdm]; exact hε'1)
    have hfp : s6a_Free F i t (t + ε') := s6a_Free_of_near F hnc (by rw [← Real.dist_eq, hdp]; exact hε'1)
    have hncm : ¬ F.IsCusp (i, t - ε') := hnc _ (by rw [hdm]; exact hε'1)
    refine ⟨hnm, hnp, s6a_K F (xOf F i t) - s6a_k0 F (xOf F i t), by omega, ?_⟩
    -- START at cut `k0`
    have hlimL := hL (xOf F i (t - ε')) ⟨by
      linarith [(abs_lt.mp hcm).1, min_le_left (min η₁ η₂) η₃, min_le_left η₁ η₂], hxm⟩
    obtain ⟨J, hJ, haJ, -, hposJ⟩ := s6a_start_before F hfm hncm hnm hlimL
    have ha : (entriesBefore F (xOf F i t))[J] = ((i, Int.fract t), 0) := by
      have hm := (s6a_mem_entriesOf F).mp (show (entriesBefore F (xOf F i t))[J] ∈
        entriesOf F (beforeBits F) (fibreListBefore F (xOf F i t)) from List.getElem_mem hJ)
      rw [haJ, (s6a_bits_of_not_cusp F hq₀c).1] at hm
      exact Prod.ext haJ (by simpa using hm.2)
    have hentk0 := s6a_entCol_k0 F (xOf F i t) hx
    have hJ' : J < (s6a_entCol F (xOf F i t) (s6a_k0 F (xOf F i t))).length := by rw [hentk0]; exact hJ
    have ha' : (s6a_entCol F (xOf F i t) (s6a_k0 F (xOf F i t)))[J] = ((i, Int.fract t), 0) := by
      rw [List.getElem_of_eq hentk0]; exact ha
    have hu : (slotAt F i (t - ε') hnm).1 = (s6a_k0 F (xOf F i t), J + 1) := by
      show (colAt F (xOf F i (t - ε')), posAt F (xOf F i (t - ε')) (i, Int.fract (t - ε'))) = _
      rw [hcolm hxm, hposJ]
    have hbit : ∀ k', s6a_k0 F (xOf F i t) ≤ k' → k' < s6a_k0 F (xOf F i t) + (s6a_K F (xOf F i t) - s6a_k0 F (xOf F i t)) →
        (if colZ F k' ≤ ht F ((i, Int.fract t), 0).1 then entryBit F (beforeBits F) ((i, Int.fract t), 0)
          else entryBit F (afterBits F) ((i, Int.fract t), 0)) = true := by
      intro k' _ _
      rw [hb1, hb2, ite_self, s6a_dirBit_rep]
      simp [hpos]
    obtain ⟨J', hJ'₁, ha'₁, hpath, hσ⟩ := s6a_walk_right F (xOf F i t) ((i, Int.fract t), 0) _ _ le_rfl (by omega) hne hbit J hJ' ha' _ hu
    refine ⟨?_, hσ⟩
    -- END at cut `K`
    apply Subtype.ext
    rw [hpath]
    have hentK := s6a_entCol_K_eq F (xOf F i t) hx
    have hKeq : s6a_k0 F (xOf F i t) + (s6a_K F (xOf F i t) - s6a_k0 F (xOf F i t)) = s6a_K F (xOf F i t) := by omega
    have hJK : J' < (s6a_entCol F (xOf F i t) (s6a_K F (xOf F i t))).length := by rw [← hKeq]; exact hJ'₁
    have haK : (s6a_entCol F (xOf F i t) (s6a_K F (xOf F i t)))[J'] = ((i, Int.fract t), 0) := by
      rw [List.getElem_of_eq (show s6a_entCol F (xOf F i t) (s6a_K F (xOf F i t)) =
        s6a_entCol F (xOf F i t) (s6a_k0 F (xOf F i t) + (s6a_K F (xOf F i t) - s6a_k0 F (xOf F i t))) by rw [hKeq])]
      exact ha'₁
    have hJ'₂ : J' < (entriesAfter F (xOf F i t)).length := by rw [← hentK]; exact hJK
    have ha'₂ : (entriesAfter F (xOf F i t))[J'] = ((i, Int.fract t), 0) :=
      (List.getElem_of_eq hentK hJK).symm.trans haK
    have hlimR := hR (xOf F i (t + ε')) ⟨hxp, by
      linarith [(abs_lt.mp hcp).2, min_le_left (min η₁ η₂) η₃, min_le_right η₁ η₂]⟩
    have hpos' := s6a_end_after F hfp hnp hlimR hJ'₂ (congrArg Prod.fst ha'₂) (Or.inl hc)
    show _ = (colAt F (xOf F i (t + ε')), posAt F (xOf F i (t + ε')) (i, Int.fract (t + ε')))
    rw [hcolp hxp, hpos', hKeq]

/-- LEAF (S6, jump through a cusp): the slot path passes the cusp vertex (`nextPair_cusp_l/r`, `posR_r_idx`,
`posL_l_idx`) and meets no `σ` slot. -/
theorem jump_cusp (c : F.Cusp) :
    ∃ ε > 0, ∀ ε' ∈ Set.Ioo (0 : ℝ) ε, ∃ (h₁ : xOf F c.1.1 (c.1.2 - ε') ∉ singX F)
      (h₂ : xOf F c.1.1 (c.1.2 + ε') ∉ singX F) (m : ℕ),
      0 < m ∧ (next (word_closed F))^[m] (slotAt F c.1.1 (c.1.2 - ε') h₁) = slotAt F c.1.1 (c.1.2 + ε') h₂ ∧
      (∀ j < m, ¬ U2.IsσSlot ((next (word_closed F))^[j] (slotAt F c.1.1 (c.1.2 - ε') h₁))) ∧
      ∃ a < m, (next (word_closed F))^[a] (slotAt F c.1.1 (c.1.2 - ε') h₁) = cuspVertex F c := by
  have hx₀ : evX F (Sum.inl c) = xOf F c.1.1 c.1.2 := rfl
  have hfr : Int.fract c.1.2 = c.1.2 := Int.fract_eq_self.mpr ⟨c.mem_Ico.1, c.mem_Ico.2⟩
  have hcp : ((c.1.1, Int.fract c.1.2) : Param F.c) = c.1 := by rw [hfr]
  have hx : xOf F c.1.1 c.1.2 ∈ singX F := mem_singX_of_isCusp F c.isCusp
  have hk0K := s6a_k0_lt_K F (xOf F c.1.1 c.1.2) hx
  obtain ⟨hk0c, hkcK⟩ := s6a_evIdx_mem F (xOf F c.1.1 c.1.2) (e := Sum.inl c) rfl
  have hz : ht F c.1 = colZ F (evIdx F (Sum.inl c)) := s6a_evZ_eq_colZ F (Sum.inl c)
  have hcd := F.cuspDisc_ne_zero_of_isCusp c.isCusp
  have hentK := s6a_entCol_K_eq F (xOf F c.1.1 c.1.2) hx
  have hentk0 := s6a_entCol_k0 F (xOf F c.1.1 c.1.2) hx
  have hnσv : ¬ U2.IsσSlot (cuspVertex F c) := s6a_not_σ_vertex F (s6a_cuspVertex_val F c)
  obtain ⟨η₁, hη₁, hL⟩ := entriesBefore_left_limit F (xOf F c.1.1 c.1.2)
  obtain ⟨η₂, hη₂, hR⟩ := entriesAfter_right_limit F (xOf F c.1.1 c.1.2)
  obtain ⟨η₃, hη₃, hgap⟩ := s6a_singX_gap F (xOf F c.1.1 c.1.2)
  obtain ⟨δ₂, hδ₂, hcont⟩ := s6a_x_cont F (i := c.1.1) c.1.2 (lt_min (lt_min hη₁ hη₂) hη₃)
  rcases F.isLeftCusp_or_isRightCusp c.isCusp with hl | hr
  · -- LEFT cusp: both arms lie to the right of `x₀`; arrive leftward at cut `K`, leave rightward to cut `K`
    obtain ⟨δ, hδ, hnc, hanti, hmono⟩ := leftCusp_x_local F hl
    refine ⟨min δ δ₂, lt_min hδ hδ₂, fun ε' hε' => ?_⟩
    have hε'0 : 0 < ε' := hε'.1
    have hε'1 : ε' < δ := lt_of_lt_of_le hε'.2 (min_le_left _ _)
    have hε'2 : ε' < δ₂ := lt_of_lt_of_le hε'.2 (min_le_right _ _)
    have hdm := s6a_dist_sub c.1.2 ε' hε'0
    have hdp := s6a_dist_add c.1.2 ε' hε'0
    have hxm : xOf F c.1.1 c.1.2 < xOf F c.1.1 (c.1.2 - ε') :=
      hanti ⟨by linarith, by linarith⟩ ⟨by linarith, le_rfl⟩ (by linarith)
    have hxp : xOf F c.1.1 c.1.2 < xOf F c.1.1 (c.1.2 + ε') :=
      hmono ⟨le_rfl, by linarith⟩ ⟨by linarith, by linarith⟩ (by linarith)
    have hcm := hcont _ (by rw [hdm]; exact hε'2)
    have hcp' := hcont _ (by rw [hdp]; exact hε'2)
    obtain ⟨hnm, -, hcolm⟩ := s6a_colAt_near F _ hgap (lt_of_lt_of_le hcm (min_le_right _ _)) (ne_of_gt hxm)
    obtain ⟨hnp, -, hcolp⟩ := s6a_colAt_near F _ hgap (lt_of_lt_of_le hcp' (min_le_right _ _)) (ne_of_gt hxp)
    have hfm : s6a_Free F c.1.1 c.1.2 (c.1.2 - ε') :=
      s6a_Free_of_local F hnc (by rw [← Real.dist_eq, hdm]; exact hε'1)
    have hfp : s6a_Free F c.1.1 c.1.2 (c.1.2 + ε') :=
      s6a_Free_of_local F hnc (by rw [← Real.dist_eq, hdp]; exact hε'1)
    have hncm : ¬ F.IsCusp (c.1.1, c.1.2 - ε') := hnc _ ⟨by linarith, by linarith⟩ (ne_of_lt (by linarith))
    -- START at cut `K`
    have hlimR := hR (xOf F c.1.1 (c.1.2 - ε')) ⟨hxm, by
      linarith [(abs_lt.mp hcm).2, min_le_left (min η₁ η₂) η₃, min_le_right η₁ η₂]⟩
    obtain ⟨J₁, hJ₁, haJ, harm, hposJ⟩ := s6a_start_after F hfm hncm hnm hlimR
    rw [hcp] at haJ harm
    have hj₁ : ((entriesAfter F (xOf F c.1.1 c.1.2))[J₁]).2 = 0 ↔ F.cuspDisc c.1 < 0 :=
      (harm c.isCusp).mp (by linarith)
    have ha₁ : (entriesAfter F (xOf F c.1.1 c.1.2))[J₁] = (c.1, ((entriesAfter F (xOf F c.1.1 c.1.2))[J₁]).2) :=
      Prod.ext haJ rfl
    have hj₁2 : ((entriesAfter F (xOf F c.1.1 c.1.2))[J₁]).2 < 2 := by
      have hm := (s6a_mem_entriesOf F).mp (show (entriesAfter F (xOf F c.1.1 c.1.2))[J₁] ∈
        entriesOf F (afterBits F) (fibreListAfter F (xOf F c.1.1 c.1.2)) from List.getElem_mem hJ₁)
      rw [haJ, s6a_afterBits_left_length F hl] at hm
      exact hm.2
    have hKeq : evIdx F (Sum.inl c) + 1 + (s6a_K F (xOf F c.1.1 c.1.2) - (evIdx F (Sum.inl c) + 1)) =
        s6a_K F (xOf F c.1.1 c.1.2) := by omega
    have hJK : J₁ < (s6a_entCol F (xOf F c.1.1 c.1.2) (evIdx F (Sum.inl c) + 1 +
        (s6a_K F (xOf F c.1.1 c.1.2) - (evIdx F (Sum.inl c) + 1)))).length := by
      rw [hKeq, hentK]; exact hJ₁
    have haK : (s6a_entCol F (xOf F c.1.1 c.1.2) (evIdx F (Sum.inl c) + 1 +
        (s6a_K F (xOf F c.1.1 c.1.2) - (evIdx F (Sum.inl c) + 1))))[J₁] =
        (entriesAfter F (xOf F c.1.1 c.1.2))[J₁] := by
      rw [List.getElem_of_eq (show s6a_entCol F (xOf F c.1.1 c.1.2) (evIdx F (Sum.inl c) + 1 +
        (s6a_K F (xOf F c.1.1 c.1.2) - (evIdx F (Sum.inl c) + 1))) = entriesAfter F (xOf F c.1.1 c.1.2) by
          rw [hKeq, hentK])]
    have hu₀ : (slotAt F c.1.1 (c.1.2 - ε') hnm).1 = (evIdx F (Sum.inl c) + 1 +
        (s6a_K F (xOf F c.1.1 c.1.2) - (evIdx F (Sum.inl c) + 1)), J₁ + 1) := by
      show (colAt F (xOf F c.1.1 (c.1.2 - ε')), posAt F (xOf F c.1.1 (c.1.2 - ε')) (c.1.1, Int.fract (c.1.2 - ε'))) = _
      rw [hcolm hxm, hposJ, hKeq]
    -- walk leftward from cut `K` to cut `k_c + 1`
    have hne1 : ∀ k', evIdx F (Sum.inl c) + 1 ≤ k' → k' < evIdx F (Sum.inl c) + 1 +
        (s6a_K F (xOf F c.1.1 c.1.2) - (evIdx F (Sum.inl c) + 1)) →
        ht F ((entriesAfter F (xOf F c.1.1 c.1.2))[J₁]).1 ≠ colZ F k' := by
      intro k' h1 h2
      rw [haJ, hz]
      exact ne_of_lt (s6a_colZ_lt F _ hk0c (by omega) (by omega))
    have hbit1 : ∀ k', evIdx F (Sum.inl c) + 1 ≤ k' → k' < evIdx F (Sum.inl c) + 1 +
        (s6a_K F (xOf F c.1.1 c.1.2) - (evIdx F (Sum.inl c) + 1)) →
        (if colZ F k' < ht F ((entriesAfter F (xOf F c.1.1 c.1.2))[J₁]).1 then
          entryBit F (beforeBits F) (entriesAfter F (xOf F c.1.1 c.1.2))[J₁]
          else entryBit F (afterBits F) (entriesAfter F (xOf F c.1.1 c.1.2))[J₁]) = false := by
      intro k' h1 h2
      have hlt : ¬ colZ F k' < ht F ((entriesAfter F (xOf F c.1.1 c.1.2))[J₁]).1 := by
        rw [haJ, hz]; exact not_lt.mpr (s6a_colZ_lt F _ hk0c (by omega) (by omega)).le
      rw [ite_eq_right hlt]
      unfold entryBit
      rw [haJ, s6a_afterBits_left_getD F hl _ hj₁2, decide_eq_false_iff_not]
      intro h
      rcases lt_or_gt_of_ne hcd with hn | hp
      · exact lt_asymm hn (h.mp (hj₁.mpr hn))
      · exact lt_asymm hp (hj₁.mp (h.mpr hp))
    obtain ⟨J₂, hJ₂, ha₂, hpath1, hσ1⟩ := s6a_walk_left F (xOf F c.1.1 c.1.2) _
      (s6a_K F (xOf F c.1.1 c.1.2) - (evIdx F (Sum.inl c) + 1)) (evIdx F (Sum.inl c) + 1)
      (by omega) (by omega) hne1 hbit1 J₁ hJK haK _ hu₀
    -- pass the cusp vertex
    obtain ⟨J₃, hJ₃, ha₃, hnext1, hnext2, hσu⟩ :=
      s6a_leftCusp_pass F c hl hj₁ hJ₂ (ha₂.trans ha₁) _ hpath1
    -- walk rightward from cut `k_c + 1` to cut `K`
    have hj₂2 : (if 0 < F.cuspDisc c.1 then 0 else 1) < 2 := by split_ifs <;> omega
    have hj₂iff : (if 0 < F.cuspDisc c.1 then 0 else 1) = 0 ↔ 0 < F.cuspDisc c.1 := by
      split_ifs with h <;> simp [h]
    have hne2 : ∀ k', evIdx F (Sum.inl c) + 1 ≤ k' → k' < evIdx F (Sum.inl c) + 1 +
        (s6a_K F (xOf F c.1.1 c.1.2) - (evIdx F (Sum.inl c) + 1)) →
        ht F ((c.1, if 0 < F.cuspDisc c.1 then 0 else 1) : Param F.c × ℕ).1 ≠ colZ F k' := by
      intro k' h1 h2
      show ht F c.1 ≠ _
      rw [hz]; exact ne_of_lt (s6a_colZ_lt F _ hk0c (by omega) (by omega))
    have hbit2 : ∀ k', evIdx F (Sum.inl c) + 1 ≤ k' → k' < evIdx F (Sum.inl c) + 1 +
        (s6a_K F (xOf F c.1.1 c.1.2) - (evIdx F (Sum.inl c) + 1)) →
        (if colZ F k' ≤ ht F ((c.1, if 0 < F.cuspDisc c.1 then 0 else 1) : Param F.c × ℕ).1 then
          entryBit F (beforeBits F) (c.1, if 0 < F.cuspDisc c.1 then 0 else 1)
          else entryBit F (afterBits F) (c.1, if 0 < F.cuspDisc c.1 then 0 else 1)) = true := by
      intro k' h1 h2
      have hlt : ¬ colZ F k' ≤ ht F ((c.1, if 0 < F.cuspDisc c.1 then 0 else 1) : Param F.c × ℕ).1 := by
        show ¬ colZ F k' ≤ ht F c.1
        rw [hz]; exact not_le.mpr (s6a_colZ_lt F _ hk0c (by omega) (by omega))
      rw [ite_eq_right hlt]
      show (afterBits F c.1).getD (if 0 < F.cuspDisc c.1 then 0 else 1) false = true
      rw [s6a_afterBits_left_getD F hl _ hj₂2, decide_eq_true_iff]; exact hj₂iff
    obtain ⟨J₄, hJ₄, ha₄, hpath2, hσ2⟩ := s6a_walk_right F (xOf F c.1.1 c.1.2) _
      (s6a_K F (xOf F c.1.1 c.1.2) - (evIdx F (Sum.inl c) + 1)) (evIdx F (Sum.inl c) + 1)
      (by omega) (by omega) hne2 hbit2 J₃ hJ₃ ha₃ _ hnext2
    -- END at cut `K`
    have hJ₄K : J₄ < (entriesAfter F (xOf F c.1.1 c.1.2)).length := by rw [← hentK, ← hKeq]; exact hJ₄
    have ha₄K : (entriesAfter F (xOf F c.1.1 c.1.2))[J₄] = (c.1, if 0 < F.cuspDisc c.1 then 0 else 1) := by
      rw [← ha₄]
      exact (List.getElem_of_eq (show s6a_entCol F (xOf F c.1.1 c.1.2) (evIdx F (Sum.inl c) + 1 +
        (s6a_K F (xOf F c.1.1 c.1.2) - (evIdx F (Sum.inl c) + 1))) = entriesAfter F (xOf F c.1.1 c.1.2) by
          rw [hKeq, hentK]) hJ₄).symm
    have hlimR' := hR (xOf F c.1.1 (c.1.2 + ε')) ⟨hxp, by
      linarith [(abs_lt.mp hcp').2, min_le_left (min η₁ η₂) η₃, min_le_right η₁ η₂]⟩
    have hside : ¬ F.IsCusp (c.1.1, c.1.2) ∨
        ((((entriesAfter F (xOf F c.1.1 c.1.2))[J₄]).2 = 0 ↔
          F.cuspDisc ((entriesAfter F (xOf F c.1.1 c.1.2))[J₄]).1 < 0) ↔ c.1.2 + ε' < c.1.2) := by
      right
      rw [ha₄K]
      show ((if 0 < F.cuspDisc c.1 then 0 else 1) = 0 ↔ F.cuspDisc c.1 < 0) ↔ c.1.2 + ε' < c.1.2
      constructor
      · intro h; exfalso
        rcases lt_or_gt_of_ne hcd with hn | hp
        · exact lt_asymm hn (hj₂iff.mp (h.mpr hn))
        · exact lt_asymm hp (h.mp (hj₂iff.mpr hp))
      · intro h; exfalso; linarith
    have hpos' := s6a_end_after F hfp hnp hlimR' hJ₄K (by rw [ha₄K]; exact hcp.symm) hside
    -- assemble
    refine ⟨hnm, hnp, (s6a_K F (xOf F c.1.1 c.1.2) - (evIdx F (Sum.inl c) + 1)) + 2 +
      (s6a_K F (xOf F c.1.1 c.1.2) - (evIdx F (Sum.inl c) + 1)), by omega, ?_, ?_,
      (s6a_K F (xOf F c.1.1 c.1.2) - (evIdx F (Sum.inl c) + 1)) + 1, by omega, ?_⟩
    · rw [show (s6a_K F (xOf F c.1.1 c.1.2) - (evIdx F (Sum.inl c) + 1)) + 2 +
          (s6a_K F (xOf F c.1.1 c.1.2) - (evIdx F (Sum.inl c) + 1)) =
          (s6a_K F (xOf F c.1.1 c.1.2) - (evIdx F (Sum.inl c) + 1)) + (1 + (1 +
          (s6a_K F (xOf F c.1.1 c.1.2) - (evIdx F (Sum.inl c) + 1)))) by omega,
        Function.iterate_add_apply, Function.iterate_add_apply, Function.iterate_one,
        Function.iterate_add_apply, Function.iterate_one, hnext1]
      apply Subtype.ext
      rw [hpath2]
      show _ = (colAt F (xOf F c.1.1 (c.1.2 + ε')), posAt F (xOf F c.1.1 (c.1.2 + ε')) (c.1.1, Int.fract (c.1.2 + ε')))
      rw [hcolp hxp, hpos', hKeq]
    · intro j hj
      rcases Nat.lt_or_ge j (s6a_K F (xOf F c.1.1 c.1.2) - (evIdx F (Sum.inl c) + 1)) with h | h
      · exact hσ1 j h
      · rcases (by omega : j = (s6a_K F (xOf F c.1.1 c.1.2) - (evIdx F (Sum.inl c) + 1)) ∨
            j = (s6a_K F (xOf F c.1.1 c.1.2) - (evIdx F (Sum.inl c) + 1)) + 1 ∨
            (s6a_K F (xOf F c.1.1 c.1.2) - (evIdx F (Sum.inl c) + 1)) + 2 ≤ j) with h | h | h
        · rw [h]; exact hσu
        · rw [h, Function.iterate_succ_apply', hnext1]; exact hnσv
        · obtain ⟨j', rfl⟩ : ∃ j', j = j' + (2 + (s6a_K F (xOf F c.1.1 c.1.2) - (evIdx F (Sum.inl c) + 1))) :=
            ⟨j - (2 + (s6a_K F (xOf F c.1.1 c.1.2) - (evIdx F (Sum.inl c) + 1))), by omega⟩
          rw [Function.iterate_add_apply, show 2 + (s6a_K F (xOf F c.1.1 c.1.2) - (evIdx F (Sum.inl c) + 1)) =
            1 + (1 + (s6a_K F (xOf F c.1.1 c.1.2) - (evIdx F (Sum.inl c) + 1))) by omega,
            Function.iterate_add_apply, Function.iterate_one, Function.iterate_add_apply, Function.iterate_one, hnext1]
          exact hσ2 j' (by omega)
    · rw [Function.iterate_succ_apply', hnext1]
  · -- RIGHT cusp: both arms lie to the left of `x₀`; arrive rightward at cut `k0`, leave leftward to cut `k0`
    obtain ⟨δ, hδ, hnc, hmono, hanti⟩ := rightCusp_x_local F hr
    refine ⟨min δ δ₂, lt_min hδ hδ₂, fun ε' hε' => ?_⟩
    have hε'0 : 0 < ε' := hε'.1
    have hε'1 : ε' < δ := lt_of_lt_of_le hε'.2 (min_le_left _ _)
    have hε'2 : ε' < δ₂ := lt_of_lt_of_le hε'.2 (min_le_right _ _)
    have hdm := s6a_dist_sub c.1.2 ε' hε'0
    have hdp := s6a_dist_add c.1.2 ε' hε'0
    have hxm : xOf F c.1.1 (c.1.2 - ε') < xOf F c.1.1 c.1.2 :=
      hmono ⟨by linarith, by linarith⟩ ⟨by linarith, le_rfl⟩ (by linarith)
    have hxp : xOf F c.1.1 (c.1.2 + ε') < xOf F c.1.1 c.1.2 :=
      hanti ⟨le_rfl, by linarith⟩ ⟨by linarith, by linarith⟩ (by linarith)
    have hcm := hcont _ (by rw [hdm]; exact hε'2)
    have hcp' := hcont _ (by rw [hdp]; exact hε'2)
    obtain ⟨hnm, hcolm, -⟩ := s6a_colAt_near F _ hgap (lt_of_lt_of_le hcm (min_le_right _ _)) (ne_of_lt hxm)
    obtain ⟨hnp, hcolp, -⟩ := s6a_colAt_near F _ hgap (lt_of_lt_of_le hcp' (min_le_right _ _)) (ne_of_lt hxp)
    have hfm : s6a_Free F c.1.1 c.1.2 (c.1.2 - ε') :=
      s6a_Free_of_local F hnc (by rw [← Real.dist_eq, hdm]; exact hε'1)
    have hfp : s6a_Free F c.1.1 c.1.2 (c.1.2 + ε') :=
      s6a_Free_of_local F hnc (by rw [← Real.dist_eq, hdp]; exact hε'1)
    have hncm : ¬ F.IsCusp (c.1.1, c.1.2 - ε') := hnc _ ⟨by linarith, by linarith⟩ (ne_of_lt (by linarith))
    -- START at cut `k0`
    have hlimL := hL (xOf F c.1.1 (c.1.2 - ε')) ⟨by
      linarith [(abs_lt.mp hcm).1, min_le_left (min η₁ η₂) η₃, min_le_left η₁ η₂], hxm⟩
    obtain ⟨J₁, hJ₁, haJ, harm, hposJ⟩ := s6a_start_before F hfm hncm hnm hlimL
    rw [hcp] at haJ harm
    have hj₁ : ((entriesBefore F (xOf F c.1.1 c.1.2))[J₁]).2 = 0 ↔ F.cuspDisc c.1 < 0 :=
      (harm c.isCusp).mp (by linarith)
    have ha₁ : (entriesBefore F (xOf F c.1.1 c.1.2))[J₁] = (c.1, ((entriesBefore F (xOf F c.1.1 c.1.2))[J₁]).2) :=
      Prod.ext haJ rfl
    have hj₁2 : ((entriesBefore F (xOf F c.1.1 c.1.2))[J₁]).2 < 2 := by
      have hm := (s6a_mem_entriesOf F).mp (show (entriesBefore F (xOf F c.1.1 c.1.2))[J₁] ∈
        entriesOf F (beforeBits F) (fibreListBefore F (xOf F c.1.1 c.1.2)) from List.getElem_mem hJ₁)
      rw [haJ, s6a_beforeBits_right_length F hr] at hm
      exact hm.2
    have hJk0 : J₁ < (s6a_entCol F (xOf F c.1.1 c.1.2) (s6a_k0 F (xOf F c.1.1 c.1.2))).length := by
      rw [hentk0]; exact hJ₁
    have hak0 : (s6a_entCol F (xOf F c.1.1 c.1.2) (s6a_k0 F (xOf F c.1.1 c.1.2)))[J₁] =
        (entriesBefore F (xOf F c.1.1 c.1.2))[J₁] := by
      rw [List.getElem_of_eq hentk0]
    have hu₀ : (slotAt F c.1.1 (c.1.2 - ε') hnm).1 = (s6a_k0 F (xOf F c.1.1 c.1.2), J₁ + 1) := by
      show (colAt F (xOf F c.1.1 (c.1.2 - ε')), posAt F (xOf F c.1.1 (c.1.2 - ε')) (c.1.1, Int.fract (c.1.2 - ε'))) = _
      rw [hcolm hxm, hposJ]
    have hkeq : s6a_k0 F (xOf F c.1.1 c.1.2) + (evIdx F (Sum.inl c) - s6a_k0 F (xOf F c.1.1 c.1.2)) =
        evIdx F (Sum.inl c) := by omega
    -- walk rightward from cut `k0` to cut `k_c`
    have hne1 : ∀ k', s6a_k0 F (xOf F c.1.1 c.1.2) ≤ k' → k' < s6a_k0 F (xOf F c.1.1 c.1.2) +
        (evIdx F (Sum.inl c) - s6a_k0 F (xOf F c.1.1 c.1.2)) →
        ht F ((entriesBefore F (xOf F c.1.1 c.1.2))[J₁]).1 ≠ colZ F k' := by
      intro k' h1 h2
      rw [haJ, hz]
      exact ne_of_gt (s6a_colZ_lt F _ h1 (by omega) hkcK)
    have hbit1 : ∀ k', s6a_k0 F (xOf F c.1.1 c.1.2) ≤ k' → k' < s6a_k0 F (xOf F c.1.1 c.1.2) +
        (evIdx F (Sum.inl c) - s6a_k0 F (xOf F c.1.1 c.1.2)) →
        (if colZ F k' ≤ ht F ((entriesBefore F (xOf F c.1.1 c.1.2))[J₁]).1 then
          entryBit F (beforeBits F) (entriesBefore F (xOf F c.1.1 c.1.2))[J₁]
          else entryBit F (afterBits F) (entriesBefore F (xOf F c.1.1 c.1.2))[J₁]) = true := by
      intro k' h1 h2
      have hle : colZ F k' ≤ ht F ((entriesBefore F (xOf F c.1.1 c.1.2))[J₁]).1 := by
        rw [haJ, hz]; exact (s6a_colZ_lt F _ h1 (by omega) hkcK).le
      rw [ite_eq_left hle]
      unfold entryBit
      rw [haJ, s6a_beforeBits_right_getD F hr _ hj₁2, decide_eq_true_iff]
      exact hj₁
    obtain ⟨J₂, hJ₂, ha₂, hpath1, hσ1⟩ := s6a_walk_right F (xOf F c.1.1 c.1.2) _
      (evIdx F (Sum.inl c) - s6a_k0 F (xOf F c.1.1 c.1.2)) (s6a_k0 F (xOf F c.1.1 c.1.2))
      le_rfl (by omega) hne1 hbit1 J₁ hJk0 hak0 _ hu₀
    have hJ₂' : J₂ < (s6a_entCol F (xOf F c.1.1 c.1.2) (evIdx F (Sum.inl c))).length := by
      rw [← hkeq]; exact hJ₂
    have ha₂' : (s6a_entCol F (xOf F c.1.1 c.1.2) (evIdx F (Sum.inl c)))[J₂] =
        (c.1, ((entriesBefore F (xOf F c.1.1 c.1.2))[J₁]).2) := by
      rw [← ha₁, ← ha₂]
      exact (List.getElem_of_eq (show s6a_entCol F (xOf F c.1.1 c.1.2) (s6a_k0 F (xOf F c.1.1 c.1.2) +
        (evIdx F (Sum.inl c) - s6a_k0 F (xOf F c.1.1 c.1.2))) = s6a_entCol F (xOf F c.1.1 c.1.2) (evIdx F (Sum.inl c))
        by rw [hkeq]) hJ₂).symm
    have hpath1' : ((next (word_closed F))^[evIdx F (Sum.inl c) - s6a_k0 F (xOf F c.1.1 c.1.2)]
        (slotAt F c.1.1 (c.1.2 - ε') hnm)).1 = (evIdx F (Sum.inl c), J₂ + 1) := by
      rw [hpath1, hkeq]
    -- pass the cusp vertex
    obtain ⟨J₃, hJ₃, ha₃, hnext1, hnext2, hσu⟩ :=
      s6a_rightCusp_pass F c hr hj₁ hJ₂' ha₂' _ hpath1'
    -- walk leftward from cut `k_c` to cut `k0`
    have hj₂2 : (if F.cuspDisc c.1 < 0 then 1 else 0) < 2 := by split_ifs <;> omega
    have hj₂iff : (if F.cuspDisc c.1 < 0 then 1 else 0) = 0 ↔ ¬ F.cuspDisc c.1 < 0 := by
      split_ifs with h <;> simp [h]
    have hne2 : ∀ k', s6a_k0 F (xOf F c.1.1 c.1.2) ≤ k' → k' < s6a_k0 F (xOf F c.1.1 c.1.2) +
        (evIdx F (Sum.inl c) - s6a_k0 F (xOf F c.1.1 c.1.2)) →
        ht F ((c.1, if F.cuspDisc c.1 < 0 then 1 else 0) : Param F.c × ℕ).1 ≠ colZ F k' := by
      intro k' h1 h2
      show ht F c.1 ≠ _
      rw [hz]; exact ne_of_gt (s6a_colZ_lt F _ h1 (by omega) hkcK)
    have hbit2 : ∀ k', s6a_k0 F (xOf F c.1.1 c.1.2) ≤ k' → k' < s6a_k0 F (xOf F c.1.1 c.1.2) +
        (evIdx F (Sum.inl c) - s6a_k0 F (xOf F c.1.1 c.1.2)) →
        (if colZ F k' < ht F ((c.1, if F.cuspDisc c.1 < 0 then 1 else 0) : Param F.c × ℕ).1 then
          entryBit F (beforeBits F) (c.1, if F.cuspDisc c.1 < 0 then 1 else 0)
          else entryBit F (afterBits F) (c.1, if F.cuspDisc c.1 < 0 then 1 else 0)) = false := by
      intro k' h1 h2
      have hlt : colZ F k' < ht F ((c.1, if F.cuspDisc c.1 < 0 then 1 else 0) : Param F.c × ℕ).1 := by
        show colZ F k' < ht F c.1
        rw [hz]; exact s6a_colZ_lt F _ h1 (by omega) hkcK
      rw [ite_eq_left hlt]
      show (beforeBits F c.1).getD (if F.cuspDisc c.1 < 0 then 1 else 0) false = false
      rw [s6a_beforeBits_right_getD F hr _ hj₂2, decide_eq_false_iff_not, hj₂iff]
      exact fun h => iff_not_self h.symm
    obtain ⟨J₄, hJ₄, ha₄, hpath2, hσ2⟩ := s6a_walk_left F (xOf F c.1.1 c.1.2) _
      (evIdx F (Sum.inl c) - s6a_k0 F (xOf F c.1.1 c.1.2)) (s6a_k0 F (xOf F c.1.1 c.1.2))
      le_rfl (by omega) hne2 hbit2 J₃
      (by rw [hkeq]; exact hJ₃) (by rw [List.getElem_of_eq (show s6a_entCol F (xOf F c.1.1 c.1.2)
        (s6a_k0 F (xOf F c.1.1 c.1.2) + (evIdx F (Sum.inl c) - s6a_k0 F (xOf F c.1.1 c.1.2))) =
        s6a_entCol F (xOf F c.1.1 c.1.2) (evIdx F (Sum.inl c)) by rw [hkeq])]; exact ha₃)
      _ (by rw [hnext2, hkeq])
    -- END at cut `k0`
    have hJ₄' : J₄ < (entriesBefore F (xOf F c.1.1 c.1.2)).length := by rw [← hentk0]; exact hJ₄
    have ha₄' : (entriesBefore F (xOf F c.1.1 c.1.2))[J₄] = (c.1, if F.cuspDisc c.1 < 0 then 1 else 0) :=
      (List.getElem_of_eq hentk0 hJ₄).symm.trans ha₄
    have hlimL' := hL (xOf F c.1.1 (c.1.2 + ε')) ⟨by
      linarith [(abs_lt.mp hcp').1, min_le_left (min η₁ η₂) η₃, min_le_left η₁ η₂], hxp⟩
    have hside : ¬ F.IsCusp (c.1.1, c.1.2) ∨
        ((((entriesBefore F (xOf F c.1.1 c.1.2))[J₄]).2 = 0 ↔
          F.cuspDisc ((entriesBefore F (xOf F c.1.1 c.1.2))[J₄]).1 < 0) ↔ c.1.2 + ε' < c.1.2) := by
      right
      rw [ha₄']
      show ((if F.cuspDisc c.1 < 0 then 1 else 0) = 0 ↔ F.cuspDisc c.1 < 0) ↔ c.1.2 + ε' < c.1.2
      rw [hj₂iff]
      constructor
      · intro h; exfalso
        rcases lt_or_gt_of_ne hcd with hn | hp
        · exact (h.mpr hn) hn
        · exact absurd (h.mp (not_lt.mpr hp.le)) (not_lt.mpr hp.le)
      · intro h; exfalso; linarith
    have hpos' := s6a_end_before F hfp hnp hlimL' hJ₄' (by rw [ha₄']; exact hcp.symm) hside
    -- assemble
    refine ⟨hnm, hnp, (evIdx F (Sum.inl c) - s6a_k0 F (xOf F c.1.1 c.1.2)) + 2 +
      (evIdx F (Sum.inl c) - s6a_k0 F (xOf F c.1.1 c.1.2)), by omega, ?_, ?_,
      (evIdx F (Sum.inl c) - s6a_k0 F (xOf F c.1.1 c.1.2)) + 1, by omega, ?_⟩
    · rw [show (evIdx F (Sum.inl c) - s6a_k0 F (xOf F c.1.1 c.1.2)) + 2 +
          (evIdx F (Sum.inl c) - s6a_k0 F (xOf F c.1.1 c.1.2)) =
          (evIdx F (Sum.inl c) - s6a_k0 F (xOf F c.1.1 c.1.2)) + (1 + (1 +
          (evIdx F (Sum.inl c) - s6a_k0 F (xOf F c.1.1 c.1.2)))) by omega,
        Function.iterate_add_apply, Function.iterate_add_apply, Function.iterate_one,
        Function.iterate_add_apply, Function.iterate_one, hnext1]
      apply Subtype.ext
      rw [hpath2]
      show _ = (colAt F (xOf F c.1.1 (c.1.2 + ε')), posAt F (xOf F c.1.1 (c.1.2 + ε')) (c.1.1, Int.fract (c.1.2 + ε')))
      rw [hcolp hxp, hpos']
    · intro j hj
      rcases Nat.lt_or_ge j (evIdx F (Sum.inl c) - s6a_k0 F (xOf F c.1.1 c.1.2)) with h | h
      · exact hσ1 j h
      · rcases (by omega : j = (evIdx F (Sum.inl c) - s6a_k0 F (xOf F c.1.1 c.1.2)) ∨
            j = (evIdx F (Sum.inl c) - s6a_k0 F (xOf F c.1.1 c.1.2)) + 1 ∨
            (evIdx F (Sum.inl c) - s6a_k0 F (xOf F c.1.1 c.1.2)) + 2 ≤ j) with h | h | h
        · rw [h]; exact hσu
        · rw [h, Function.iterate_succ_apply', hnext1]; exact hnσv
        · obtain ⟨j', rfl⟩ : ∃ j', j = j' + (2 + (evIdx F (Sum.inl c) - s6a_k0 F (xOf F c.1.1 c.1.2))) :=
            ⟨j - (2 + (evIdx F (Sum.inl c) - s6a_k0 F (xOf F c.1.1 c.1.2))), by omega⟩
          rw [Function.iterate_add_apply, show 2 + (evIdx F (Sum.inl c) - s6a_k0 F (xOf F c.1.1 c.1.2)) =
            1 + (1 + (evIdx F (Sum.inl c) - s6a_k0 F (xOf F c.1.1 c.1.2))) by omega,
            Function.iterate_add_apply, Function.iterate_one, Function.iterate_add_apply, Function.iterate_one, hnext1]
          exact hσ2 j' (by omega)
    · rw [Function.iterate_succ_apply', hnext1]

/-- LEAF (S6, jump through a crossing): the slot path passes exactly one `σ` slot, `Φ p` — reached when the strand
enters the crossing's column `k = evIdx (Sum.inr (crossOf p))` at position `m` (over) or `m+1` (under) from the
left, or at cut `k+1` from the right (`σSlotA`/`σSlotB` unfolded; `posR_σ_idx`, `posL_σ_idx`); NOTE the strand
may first pass tie columns of the same x-value below the crossing, so `Φ p` is in general NOT `slotAt (t_p − ε)`. -/
theorem jump_cross (p : F.Occ) :
    ∃ ε > 0, ∀ ε' ∈ Set.Ioo (0 : ℝ) ε, ∃ (h₁ : xOf F p.1.1 (p.1.2 - ε') ∉ singX F)
      (h₂ : xOf F p.1.1 (p.1.2 + ε') ∉ singX F) (m : ℕ),
      0 < m ∧ (next (word_closed F))^[m] (slotAt F p.1.1 (p.1.2 - ε') h₁) = slotAt F p.1.1 (p.1.2 + ε') h₂ ∧
      ∃ a < m, (next (word_closed F))^[a] (slotAt F p.1.1 (p.1.2 - ε') h₁) = ΦFun F p ∧
        ∀ j < m, j ≠ a → ¬ U2.IsσSlot ((next (word_closed F))^[j] (slotAt F p.1.1 (p.1.2 - ε') h₁)) := by
  have hfr : Int.fract p.1.2 = p.1.2 := Int.fract_eq_self.mpr ⟨p.2.1.1, p.2.1.2⟩
  have hcp : ((p.1.1, Int.fract p.1.2) : Param F.c) = p.1 := by rw [hfr]
  have hx : xOf F p.1.1 p.1.2 ∈ singX F := mem_singX_of_isDouble F (isDouble_partner F p)
  have hc : ¬ F.IsCusp (p.1.1, p.1.2) := s6a_occ_not_cusp F p
  have hqmem : p.1 ∈ totalFibre F (xOf F p.1.1 p.1.2) := s6a_occ_mem_totalFibre F p
  obtain ⟨hb1, hb2⟩ := s6a_entryBit_regular F (s6a_occ_not_cusp F p)
  have hbb := (s6a_bits_of_not_cusp F (s6a_occ_not_cusp F p)).1
  have hab := (s6a_bits_of_not_cusp F (s6a_occ_not_cusp F p)).2
  have hex : evX F (Sum.inr (crossOf F p)) = xOf F p.1.1 p.1.2 := s6a_evX_crossOf F p
  obtain ⟨hk0x, hkxK⟩ := s6a_evIdx_mem F (xOf F p.1.1 p.1.2) hex
  have hz : ht F p.1 = colZ F (evIdx F (Sum.inr (crossOf F p))) :=
    (s6a_evZ_crossOf F p).symm.trans (s6a_evZ_eq_colZ F _)
  have hentK := s6a_entCol_K_eq F (xOf F p.1.1 p.1.2) hx
  have hentk0 := s6a_entCol_k0 F (xOf F p.1.1 p.1.2) hx
  obtain ⟨δ₁, hδ₁, hnc⟩ := s6a_no_cusp_near F hc
  obtain ⟨η₁, hη₁, hL⟩ := entriesBefore_left_limit F (xOf F p.1.1 p.1.2)
  obtain ⟨η₂, hη₂, hR⟩ := entriesAfter_right_limit F (xOf F p.1.1 p.1.2)
  obtain ⟨η₃, hη₃, hgap⟩ := s6a_singX_gap F (xOf F p.1.1 p.1.2)
  obtain ⟨δ₂, hδ₂, hcont⟩ := s6a_x_cont F (i := p.1.1) p.1.2 (lt_min (lt_min hη₁ hη₂) hη₃)
  have hxv := xvel_ne_zero_of_not_isCusp F hc
  have hne_lt : ∀ k', s6a_k0 F (xOf F p.1.1 p.1.2) ≤ k' → k' < evIdx F (Sum.inr (crossOf F p)) →
      ht F ((p.1, 0) : Param F.c × ℕ).1 ≠ colZ F k' := by
    intro k' h1 h2; show ht F p.1 ≠ _; rw [hz]; exact ne_of_gt (s6a_colZ_lt F _ h1 h2 hkxK)
  have hne_gt : ∀ k', evIdx F (Sum.inr (crossOf F p)) + 1 ≤ k' → k' < s6a_K F (xOf F p.1.1 p.1.2) →
      ht F ((p.1, 0) : Param F.c × ℕ).1 ≠ colZ F k' := by
    intro k' h1 h2; show ht F p.1 ≠ _; rw [hz]; exact ne_of_lt (s6a_colZ_lt F _ hk0x (by omega) h2)
  rcases lt_or_gt_of_ne hxv with hneg | hpos
  · -- leftward: arrive at cut `K`, walk to cut `k_x + 1`, cross, walk to cut `k0`
    obtain ⟨δ₃, hδ₃, hside⟩ := s6a_side_neg F hneg
    refine ⟨min δ₁ (min δ₂ δ₃), lt_min hδ₁ (lt_min hδ₂ hδ₃), fun ε' hε' => ?_⟩
    have hε'0 : 0 < ε' := hε'.1
    have hε'1 : ε' < δ₁ := lt_of_lt_of_le hε'.2 (min_le_left _ _)
    have hε'2 : ε' < δ₂ := lt_of_lt_of_le hε'.2 (le_trans (min_le_right _ _) (min_le_left _ _))
    have hε'3 : ε' < δ₃ := lt_of_lt_of_le hε'.2 (le_trans (min_le_right _ _) (min_le_right _ _))
    have hdm := s6a_dist_sub p.1.2 ε' hε'0
    have hdp := s6a_dist_add p.1.2 ε' hε'0
    have hxm : xOf F p.1.1 p.1.2 < xOf F p.1.1 (p.1.2 - ε') := (hside _ (by rw [hdm]; exact hε'3)).1 (by linarith)
    have hxp : xOf F p.1.1 (p.1.2 + ε') < xOf F p.1.1 p.1.2 := (hside _ (by rw [hdp]; exact hε'3)).2 (by linarith)
    have hcm := hcont _ (by rw [hdm]; exact hε'2)
    have hcp' := hcont _ (by rw [hdp]; exact hε'2)
    obtain ⟨hnm, -, hcolm⟩ := s6a_colAt_near F _ hgap (lt_of_lt_of_le hcm (min_le_right _ _)) (ne_of_gt hxm)
    obtain ⟨hnp, hcolp, -⟩ := s6a_colAt_near F _ hgap (lt_of_lt_of_le hcp' (min_le_right _ _)) (ne_of_lt hxp)
    have hfm : s6a_Free F p.1.1 p.1.2 (p.1.2 - ε') := s6a_Free_of_near F hnc (by rw [← Real.dist_eq, hdm]; exact hε'1)
    have hfp : s6a_Free F p.1.1 p.1.2 (p.1.2 + ε') := s6a_Free_of_near F hnc (by rw [← Real.dist_eq, hdp]; exact hε'1)
    have hncm : ¬ F.IsCusp (p.1.1, p.1.2 - ε') := hnc _ (by rw [hdm]; exact hε'1)
    -- START at cut `K`
    have hlimR := hR (xOf F p.1.1 (p.1.2 - ε')) ⟨hxm, by
      linarith [(abs_lt.mp hcm).2, min_le_left (min η₁ η₂) η₃, min_le_right η₁ η₂]⟩
    obtain ⟨J₁, hJ₁, haJ, -, hposJ⟩ := s6a_start_after F hfm hncm hnm hlimR
    rw [hcp] at haJ
    have ha : (entriesAfter F (xOf F p.1.1 p.1.2))[J₁] = (p.1, 0) := by
      have hm := (s6a_mem_entriesOf F).mp (show (entriesAfter F (xOf F p.1.1 p.1.2))[J₁] ∈
        entriesOf F (afterBits F) (fibreListAfter F (xOf F p.1.1 p.1.2)) from List.getElem_mem hJ₁)
      rw [haJ, hab] at hm
      exact Prod.ext haJ (by simpa using hm.2)
    have hKeq : evIdx F (Sum.inr (crossOf F p)) + 1 + (s6a_K F (xOf F p.1.1 p.1.2) - (evIdx F (Sum.inr (crossOf F p)) + 1)) =
        s6a_K F (xOf F p.1.1 p.1.2) := by omega
    have hJK : J₁ < (s6a_entCol F (xOf F p.1.1 p.1.2) (evIdx F (Sum.inr (crossOf F p)) + 1 +
        (s6a_K F (xOf F p.1.1 p.1.2) - (evIdx F (Sum.inr (crossOf F p)) + 1)))).length := by
      rw [hKeq, hentK]; exact hJ₁
    have haK : (s6a_entCol F (xOf F p.1.1 p.1.2) (evIdx F (Sum.inr (crossOf F p)) + 1 +
        (s6a_K F (xOf F p.1.1 p.1.2) - (evIdx F (Sum.inr (crossOf F p)) + 1))))[J₁] = (p.1, 0) := by
      rw [List.getElem_of_eq (show s6a_entCol F (xOf F p.1.1 p.1.2) (evIdx F (Sum.inr (crossOf F p)) + 1 +
        (s6a_K F (xOf F p.1.1 p.1.2) - (evIdx F (Sum.inr (crossOf F p)) + 1))) = entriesAfter F (xOf F p.1.1 p.1.2) by
          rw [hKeq, hentK])]
      exact ha
    have hu₀ : (slotAt F p.1.1 (p.1.2 - ε') hnm).1 = (evIdx F (Sum.inr (crossOf F p)) + 1 +
        (s6a_K F (xOf F p.1.1 p.1.2) - (evIdx F (Sum.inr (crossOf F p)) + 1)), J₁ + 1) := by
      show (colAt F (xOf F p.1.1 (p.1.2 - ε')), posAt F (xOf F p.1.1 (p.1.2 - ε')) (p.1.1, Int.fract (p.1.2 - ε'))) = _
      rw [hcolm hxm, hposJ, hKeq]
    have hbitL : ∀ k', (if colZ F k' < ht F ((p.1, 0) : Param F.c × ℕ).1 then entryBit F (beforeBits F) (p.1, 0)
        else entryBit F (afterBits F) (p.1, 0)) = false := by
      intro k'; rw [hb1, hb2, ite_self]; exact decide_eq_false (not_lt.mpr hneg.le)
    -- walk leftward from cut `K` to cut `k_x + 1`
    obtain ⟨J₂, hJ₂, ha₂, hpath1, hσ1⟩ := s6a_walk_left F (xOf F p.1.1 p.1.2) (p.1, 0)
      (s6a_K F (xOf F p.1.1 p.1.2) - (evIdx F (Sum.inr (crossOf F p)) + 1)) (evIdx F (Sum.inr (crossOf F p)) + 1)
      (by omega) (by omega) (fun k' h1 h2 => hne_gt k' h1 (by omega)) (fun k' _ _ => hbitL k') J₁ hJK haK _ hu₀
    -- cross
    obtain ⟨hΦ, J₃, hJ₃, ha₃, hnext⟩ := s6a_cross_pass_left F p hneg hJ₂ ha₂ _ hpath1
    -- walk leftward from cut `k_x` to cut `k0`
    have hkeq : s6a_k0 F (xOf F p.1.1 p.1.2) + (evIdx F (Sum.inr (crossOf F p)) - s6a_k0 F (xOf F p.1.1 p.1.2)) =
        evIdx F (Sum.inr (crossOf F p)) := by omega
    obtain ⟨J₄, hJ₄, ha₄, hpath2, hσ2⟩ := s6a_walk_left F (xOf F p.1.1 p.1.2) (p.1, 0)
      (evIdx F (Sum.inr (crossOf F p)) - s6a_k0 F (xOf F p.1.1 p.1.2)) (s6a_k0 F (xOf F p.1.1 p.1.2))
      le_rfl (by omega) (fun k' h1 h2 => hne_lt k' h1 (by omega)) (fun k' _ _ => hbitL k') J₃
      (by rw [hkeq]; exact hJ₃)
      (by rw [List.getElem_of_eq (show s6a_entCol F (xOf F p.1.1 p.1.2) (s6a_k0 F (xOf F p.1.1 p.1.2) +
        (evIdx F (Sum.inr (crossOf F p)) - s6a_k0 F (xOf F p.1.1 p.1.2))) =
        s6a_entCol F (xOf F p.1.1 p.1.2) (evIdx F (Sum.inr (crossOf F p))) by rw [hkeq])]; exact ha₃)
      _ (by rw [hnext, hkeq])
    -- END at cut `k0`
    have hJ₄' : J₄ < (entriesBefore F (xOf F p.1.1 p.1.2)).length := by rw [← hentk0]; exact hJ₄
    have ha₄' : (entriesBefore F (xOf F p.1.1 p.1.2))[J₄] = (p.1, 0) :=
      (List.getElem_of_eq hentk0 hJ₄).symm.trans ha₄
    have hlimL := hL (xOf F p.1.1 (p.1.2 + ε')) ⟨by
      linarith [(abs_lt.mp hcp').1, min_le_left (min η₁ η₂) η₃, min_le_left η₁ η₂], hxp⟩
    have hpos' := s6a_end_before F hfp hnp hlimL hJ₄' (by rw [ha₄']; exact hcp.symm) (Or.inl hc)
    -- assemble
    refine ⟨hnm, hnp, (evIdx F (Sum.inr (crossOf F p)) - s6a_k0 F (xOf F p.1.1 p.1.2)) + 1 +
      (s6a_K F (xOf F p.1.1 p.1.2) - (evIdx F (Sum.inr (crossOf F p)) + 1)), by omega, ?_,
      (s6a_K F (xOf F p.1.1 p.1.2) - (evIdx F (Sum.inr (crossOf F p)) + 1)), by omega, hΦ, ?_⟩
    · rw [Function.iterate_add_apply, Function.iterate_add_apply, Function.iterate_one]
      apply Subtype.ext
      rw [hpath2]
      show _ = (colAt F (xOf F p.1.1 (p.1.2 + ε')), posAt F (xOf F p.1.1 (p.1.2 + ε')) (p.1.1, Int.fract (p.1.2 + ε')))
      rw [hcolp hxp, hpos']
    · intro j hj hja
      rcases Nat.lt_or_ge j (s6a_K F (xOf F p.1.1 p.1.2) - (evIdx F (Sum.inr (crossOf F p)) + 1)) with h | h
      · exact hσ1 j h
      · obtain ⟨j', rfl⟩ : ∃ j', j = j' + (1 + (s6a_K F (xOf F p.1.1 p.1.2) - (evIdx F (Sum.inr (crossOf F p)) + 1))) :=
          ⟨j - (1 + (s6a_K F (xOf F p.1.1 p.1.2) - (evIdx F (Sum.inr (crossOf F p)) + 1))), by omega⟩
        rw [Function.iterate_add_apply, Function.iterate_add_apply, Function.iterate_one]
        exact hσ2 j' (by omega)
  · -- rightward: arrive at cut `k0`, walk to cut `k_x`, cross, walk to cut `K`
    obtain ⟨δ₃, hδ₃, hside⟩ := s6a_side_pos F hpos
    refine ⟨min δ₁ (min δ₂ δ₃), lt_min hδ₁ (lt_min hδ₂ hδ₃), fun ε' hε' => ?_⟩
    have hε'0 : 0 < ε' := hε'.1
    have hε'1 : ε' < δ₁ := lt_of_lt_of_le hε'.2 (min_le_left _ _)
    have hε'2 : ε' < δ₂ := lt_of_lt_of_le hε'.2 (le_trans (min_le_right _ _) (min_le_left _ _))
    have hε'3 : ε' < δ₃ := lt_of_lt_of_le hε'.2 (le_trans (min_le_right _ _) (min_le_right _ _))
    have hdm := s6a_dist_sub p.1.2 ε' hε'0
    have hdp := s6a_dist_add p.1.2 ε' hε'0
    have hxm : xOf F p.1.1 (p.1.2 - ε') < xOf F p.1.1 p.1.2 := (hside _ (by rw [hdm]; exact hε'3)).1 (by linarith)
    have hxp : xOf F p.1.1 p.1.2 < xOf F p.1.1 (p.1.2 + ε') := (hside _ (by rw [hdp]; exact hε'3)).2 (by linarith)
    have hcm := hcont _ (by rw [hdm]; exact hε'2)
    have hcp' := hcont _ (by rw [hdp]; exact hε'2)
    obtain ⟨hnm, hcolm, -⟩ := s6a_colAt_near F _ hgap (lt_of_lt_of_le hcm (min_le_right _ _)) (ne_of_lt hxm)
    obtain ⟨hnp, -, hcolp⟩ := s6a_colAt_near F _ hgap (lt_of_lt_of_le hcp' (min_le_right _ _)) (ne_of_gt hxp)
    have hfm : s6a_Free F p.1.1 p.1.2 (p.1.2 - ε') := s6a_Free_of_near F hnc (by rw [← Real.dist_eq, hdm]; exact hε'1)
    have hfp : s6a_Free F p.1.1 p.1.2 (p.1.2 + ε') := s6a_Free_of_near F hnc (by rw [← Real.dist_eq, hdp]; exact hε'1)
    have hncm : ¬ F.IsCusp (p.1.1, p.1.2 - ε') := hnc _ (by rw [hdm]; exact hε'1)
    -- START at cut `k0`
    have hlimL := hL (xOf F p.1.1 (p.1.2 - ε')) ⟨by
      linarith [(abs_lt.mp hcm).1, min_le_left (min η₁ η₂) η₃, min_le_left η₁ η₂], hxm⟩
    obtain ⟨J₁, hJ₁, haJ, -, hposJ⟩ := s6a_start_before F hfm hncm hnm hlimL
    rw [hcp] at haJ
    have ha : (entriesBefore F (xOf F p.1.1 p.1.2))[J₁] = (p.1, 0) := by
      have hm := (s6a_mem_entriesOf F).mp (show (entriesBefore F (xOf F p.1.1 p.1.2))[J₁] ∈
        entriesOf F (beforeBits F) (fibreListBefore F (xOf F p.1.1 p.1.2)) from List.getElem_mem hJ₁)
      rw [haJ, hbb] at hm
      exact Prod.ext haJ (by simpa using hm.2)
    have hJk0 : J₁ < (s6a_entCol F (xOf F p.1.1 p.1.2) (s6a_k0 F (xOf F p.1.1 p.1.2))).length := by
      rw [hentk0]; exact hJ₁
    have hak0 : (s6a_entCol F (xOf F p.1.1 p.1.2) (s6a_k0 F (xOf F p.1.1 p.1.2)))[J₁] = (p.1, 0) := by
      rw [List.getElem_of_eq hentk0]; exact ha
    have hu₀ : (slotAt F p.1.1 (p.1.2 - ε') hnm).1 = (s6a_k0 F (xOf F p.1.1 p.1.2), J₁ + 1) := by
      show (colAt F (xOf F p.1.1 (p.1.2 - ε')), posAt F (xOf F p.1.1 (p.1.2 - ε')) (p.1.1, Int.fract (p.1.2 - ε'))) = _
      rw [hcolm hxm, hposJ]
    have hbitR : ∀ k', (if colZ F k' ≤ ht F ((p.1, 0) : Param F.c × ℕ).1 then entryBit F (beforeBits F) (p.1, 0)
        else entryBit F (afterBits F) (p.1, 0)) = true := by
      intro k'; rw [hb1, hb2, ite_self]; exact decide_eq_true hpos
    have hkeq : s6a_k0 F (xOf F p.1.1 p.1.2) + (evIdx F (Sum.inr (crossOf F p)) - s6a_k0 F (xOf F p.1.1 p.1.2)) =
        evIdx F (Sum.inr (crossOf F p)) := by omega
    -- walk rightward from cut `k0` to cut `k_x`
    obtain ⟨J₂, hJ₂, ha₂, hpath1, hσ1⟩ := s6a_walk_right F (xOf F p.1.1 p.1.2) (p.1, 0)
      (evIdx F (Sum.inr (crossOf F p)) - s6a_k0 F (xOf F p.1.1 p.1.2)) (s6a_k0 F (xOf F p.1.1 p.1.2))
      le_rfl (by omega) (fun k' h1 h2 => hne_lt k' h1 (by omega)) (fun k' _ _ => hbitR k') J₁ hJk0 hak0 _ hu₀
    have hJ₂' : J₂ < (s6a_entCol F (xOf F p.1.1 p.1.2) (evIdx F (Sum.inr (crossOf F p)))).length := by
      rw [← hkeq]; exact hJ₂
    have ha₂' : (s6a_entCol F (xOf F p.1.1 p.1.2) (evIdx F (Sum.inr (crossOf F p))))[J₂] = (p.1, 0) := by
      rw [← ha₂]
      exact (List.getElem_of_eq (show s6a_entCol F (xOf F p.1.1 p.1.2) (s6a_k0 F (xOf F p.1.1 p.1.2) +
        (evIdx F (Sum.inr (crossOf F p)) - s6a_k0 F (xOf F p.1.1 p.1.2))) =
        s6a_entCol F (xOf F p.1.1 p.1.2) (evIdx F (Sum.inr (crossOf F p))) by rw [hkeq]) hJ₂).symm
    have hpath1' : ((next (word_closed F))^[evIdx F (Sum.inr (crossOf F p)) - s6a_k0 F (xOf F p.1.1 p.1.2)]
        (slotAt F p.1.1 (p.1.2 - ε') hnm)).1 = (evIdx F (Sum.inr (crossOf F p)), J₂ + 1) := by
      rw [hpath1, hkeq]
    -- cross
    obtain ⟨hΦ, J₃, hJ₃, ha₃, hnext⟩ := s6a_cross_pass_right F p hpos hJ₂' ha₂' _ hpath1'
    -- walk rightward from cut `k_x + 1` to cut `K`
    obtain ⟨J₄, hJ₄, ha₄, hpath2, hσ2⟩ := s6a_walk_right F (xOf F p.1.1 p.1.2) (p.1, 0)
      (s6a_K F (xOf F p.1.1 p.1.2) - (evIdx F (Sum.inr (crossOf F p)) + 1)) (evIdx F (Sum.inr (crossOf F p)) + 1)
      (by omega) (by omega) (fun k' h1 h2 => hne_gt k' h1 (by omega)) (fun k' _ _ => hbitR k') J₃ hJ₃ ha₃ _ hnext
    -- END at cut `K`
    have hKeq : evIdx F (Sum.inr (crossOf F p)) + 1 + (s6a_K F (xOf F p.1.1 p.1.2) - (evIdx F (Sum.inr (crossOf F p)) + 1)) =
        s6a_K F (xOf F p.1.1 p.1.2) := by omega
    have hJ₄K : J₄ < (entriesAfter F (xOf F p.1.1 p.1.2)).length := by rw [← hentK, ← hKeq]; exact hJ₄
    have ha₄K : (entriesAfter F (xOf F p.1.1 p.1.2))[J₄] = (p.1, 0) := by
      rw [← ha₄]
      exact (List.getElem_of_eq (show s6a_entCol F (xOf F p.1.1 p.1.2) (evIdx F (Sum.inr (crossOf F p)) + 1 +
        (s6a_K F (xOf F p.1.1 p.1.2) - (evIdx F (Sum.inr (crossOf F p)) + 1))) = entriesAfter F (xOf F p.1.1 p.1.2) by
          rw [hKeq, hentK]) hJ₄).symm
    have hlimR := hR (xOf F p.1.1 (p.1.2 + ε')) ⟨hxp, by
      linarith [(abs_lt.mp hcp').2, min_le_left (min η₁ η₂) η₃, min_le_right η₁ η₂]⟩
    have hpos' := s6a_end_after F hfp hnp hlimR hJ₄K (by rw [ha₄K]; exact hcp.symm) (Or.inl hc)
    -- assemble
    refine ⟨hnm, hnp, (s6a_K F (xOf F p.1.1 p.1.2) - (evIdx F (Sum.inr (crossOf F p)) + 1)) + 1 +
      (evIdx F (Sum.inr (crossOf F p)) - s6a_k0 F (xOf F p.1.1 p.1.2)), by omega, ?_,
      (evIdx F (Sum.inr (crossOf F p)) - s6a_k0 F (xOf F p.1.1 p.1.2)), by omega, hΦ, ?_⟩
    · rw [Function.iterate_add_apply, Function.iterate_add_apply, Function.iterate_one]
      apply Subtype.ext
      rw [hpath2]
      show _ = (colAt F (xOf F p.1.1 (p.1.2 + ε')), posAt F (xOf F p.1.1 (p.1.2 + ε')) (p.1.1, Int.fract (p.1.2 + ε')))
      rw [hcolp hxp, hpos', hKeq]
    · intro j hj hja
      rcases Nat.lt_or_ge j (evIdx F (Sum.inr (crossOf F p)) - s6a_k0 F (xOf F p.1.1 p.1.2)) with h | h
      · exact hσ1 j h
      · obtain ⟨j', rfl⟩ : ∃ j', j = j' + (1 + (evIdx F (Sum.inr (crossOf F p)) - s6a_k0 F (xOf F p.1.1 p.1.2))) :=
          ⟨j - (1 + (evIdx F (Sum.inr (crossOf F p)) - s6a_k0 F (xOf F p.1.1 p.1.2))), by omega⟩
        rw [Function.iterate_add_apply, Function.iterate_add_apply, Function.iterate_one]
        exact hσ2 j' (by omega)


/-- LEAF (S6, the path): along a parameter interval containing no occurrence of the circle, the slot path
(finitely many singular parameters in `[t₀, t₁]`; `slotAt_const` between them, `jump_regular`/`jump_cusp` at them)
meets no `σ` slot. -/
theorem path_no_occ {i : Fin F.c} {t₀ t₁ : ℝ} (h01 : t₀ < t₁) (h₀ : xOf F i t₀ ∉ singX F)
    (h₁ : xOf F i t₁ ∉ singX F) (hno : ∀ p : F.Occ, p.1.1 = i → ∀ s ∈ Set.Ioo t₀ t₁, ¬ SameParam p.1 (i, s)) :
    ∃ m, (next (word_closed F))^[m] (slotAt F i t₀ h₀) = slotAt F i t₁ h₁ ∧
      ∀ j < m, ¬ U2.IsσSlot ((next (word_closed F))^[j] (slotAt F i t₀ h₀)) := by
  -- induction on the number of singular parameters of `[t₀, t₁]`
  suffices key : ∀ N : ℕ, ∀ t₀, t₀ < t₁ → ∀ (h₀ : xOf F i t₀ ∉ singX F),
      (∀ p : F.Occ, p.1.1 = i → ∀ s ∈ Set.Ioo t₀ t₁, ¬ SameParam p.1 (i, s)) →
      (s6a_sing_params_finite F i t₀ t₁).toFinset.card ≤ N →
      ∃ m, (next (word_closed F))^[m] (slotAt F i t₀ h₀) = slotAt F i t₁ h₁ ∧
        ∀ j < m, ¬ U2.IsσSlot ((next (word_closed F))^[j] (slotAt F i t₀ h₀)) from
    key _ t₀ h01 h₀ hno le_rfl
  intro N
  induction N with
  | zero =>
    intro t₀ h01 h₀ hno hcard
    have hS : ∀ s ∈ Set.Icc t₀ t₁, xOf F i s ∉ singX F := by
      intro s hs hsx
      have hmem : s ∈ (s6a_sing_params_finite F i t₀ t₁).toFinset := by
        rw [Set.Finite.mem_toFinset]; exact ⟨hs, hsx⟩
      have := Finset.card_pos.mpr ⟨s, hmem⟩
      omega
    refine ⟨0, ?_, fun j hj => absurd hj (Nat.not_lt_zero _)⟩
    exact slotAt_const F h01.le hS
  | succ N ih =>
    intro t₀ h01 h₀ hno hcard
    by_cases hne : ((s6a_sing_params_finite F i t₀ t₁).toFinset).Nonempty
    · -- split at the smallest singular parameter `s₁`
      obtain ⟨s₁, hs₁mem, hmin'⟩ := Finset.exists_min_image _ (fun s => s) hne
      rw [Set.Finite.mem_toFinset] at hs₁mem
      obtain ⟨⟨hs₁0, hs₁1⟩, hs₁x⟩ := hs₁mem
      have hmin : ∀ s ∈ Set.Icc t₀ t₁, xOf F i s ∈ singX F → s₁ ≤ s := fun s hs hsx =>
        hmin' s (by rw [Set.Finite.mem_toFinset]; exact ⟨hs, hsx⟩)
      have hs₁0' : t₀ < s₁ := lt_of_le_of_ne hs₁0 (fun h => h₀ (h ▸ hs₁x))
      have hs₁1' : s₁ < t₁ := lt_of_le_of_ne hs₁1 (fun h => h₁ (h ▸ hs₁x))
      -- the jump across `s₁`
      have hjump : ∃ ε > 0, ∀ ε' ∈ Set.Ioo (0 : ℝ) ε, ∃ (hm : xOf F i (s₁ - ε') ∉ singX F)
          (hp : xOf F i (s₁ + ε') ∉ singX F) (m : ℕ),
          (next (word_closed F))^[m] (slotAt F i (s₁ - ε') hm) = slotAt F i (s₁ + ε') hp ∧
          ∀ j < m, ¬ U2.IsσSlot ((next (word_closed F))^[j] (slotAt F i (s₁ - ε') hm)) := by
        by_cases hc : F.IsCusp (i, s₁)
        · -- a cusp: `jump_cusp` at its representative, transported by the period
          obtain ⟨ε, hε, hjc⟩ := jump_cusp F ⟨SameParam.rep (i, s₁), F.rep_mem_cuspSet hc⟩
          refine ⟨ε, hε, fun ε' hε' => ?_⟩
          obtain ⟨hm, hp, m, -, hpath, hσ, -⟩ := hjc ε' hε'
          have heqm : s₁ - ε' = (Int.fract s₁ - ε') + (⌊s₁⌋ : ℝ) := by linarith [Int.fract_add_floor s₁]
          have heqp : s₁ + ε' = (Int.fract s₁ + ε') + (⌊s₁⌋ : ℝ) := by linarith [Int.fract_add_floor s₁]
          have hm' : xOf F i (s₁ - ε') ∉ singX F := by rw [heqm, s6a_xOf_add_int]; exact hm
          have hp' : xOf F i (s₁ + ε') ∉ singX F := by rw [heqp, s6a_xOf_add_int]; exact hp
          have hsm : slotAt F i (s₁ - ε') hm' = slotAt F i (Int.fract s₁ - ε') hm := by
            apply Subtype.ext
            show (colAt F (xOf F i (s₁ - ε')), posAt F (xOf F i (s₁ - ε')) (i, Int.fract (s₁ - ε'))) =
              (colAt F (xOf F i (Int.fract s₁ - ε')),
                posAt F (xOf F i (Int.fract s₁ - ε')) (i, Int.fract (Int.fract s₁ - ε')))
            rw [heqm, s6a_xOf_add_int, Int.fract_add_intCast]
          have hsp : slotAt F i (s₁ + ε') hp' = slotAt F i (Int.fract s₁ + ε') hp := by
            apply Subtype.ext
            show (colAt F (xOf F i (s₁ + ε')), posAt F (xOf F i (s₁ + ε')) (i, Int.fract (s₁ + ε'))) =
              (colAt F (xOf F i (Int.fract s₁ + ε')),
                posAt F (xOf F i (Int.fract s₁ + ε')) (i, Int.fract (Int.fract s₁ + ε')))
            rw [heqp, s6a_xOf_add_int, Int.fract_add_intCast]
          refine ⟨hm', hp', m, ?_, ?_⟩
          · rw [hsm, hsp]; exact hpath
          · rw [hsm]; exact hσ
        · -- regular, and not a double point (that would be an occurrence inside `(t₀, t₁)`)
          have hd : ∀ r, ¬ F.IsDouble (i, s₁) r := by
            intro r hr
            obtain ⟨p, hp1, hps⟩ := s6a_occ_of_isDouble F hr
            exact hno p hp1 s₁ ⟨hs₁0', hs₁1'⟩ hps
          obtain ⟨ε, hε, hj⟩ := jump_regular F hs₁x hc hd
          refine ⟨ε, hε, fun ε' hε' => ?_⟩
          obtain ⟨hm, hp, m, -, hpath, hσ⟩ := hj ε' hε'
          exact ⟨hm, hp, m, hpath, hσ⟩
      obtain ⟨ε, hε, hjump⟩ := hjump
      -- the step size
      obtain ⟨ε', hε'0, hε'ε, hε'a, hε'b⟩ : ∃ ε' : ℝ, 0 < ε' ∧ ε' < ε ∧ ε' < s₁ - t₀ ∧ ε' < t₁ - s₁ := by
        refine ⟨min (ε / 2) (min ((s₁ - t₀) / 2) ((t₁ - s₁) / 2)), ?_, ?_, ?_, ?_⟩
        · exact lt_min (half_pos hε) (lt_min (half_pos (by linarith)) (half_pos (by linarith)))
        · exact lt_of_le_of_lt (min_le_left _ _) (half_lt_self hε)
        · exact lt_of_le_of_lt (le_trans (min_le_right _ _) (min_le_left _ _)) (half_lt_self (by linarith))
        · exact lt_of_le_of_lt (le_trans (min_le_right _ _) (min_le_right _ _)) (half_lt_self (by linarith))
      obtain ⟨hm, hp, m₁, hpath1, hσ1⟩ := hjump ε' ⟨hε'0, hε'ε⟩
      -- constancy on `[t₀, s₁ - ε']`
      have hreg1 : ∀ s ∈ Set.Icc t₀ (s₁ - ε'), xOf F i s ∉ singX F := by
        intro s hs hsx
        have := hmin s ⟨hs.1, by linarith [hs.2]⟩ hsx
        linarith [hs.2]
      have hconst : slotAt F i t₀ h₀ = slotAt F i (s₁ - ε') hm := slotAt_const F (by linarith) hreg1
      -- the induction hypothesis on `[s₁ + ε', t₁]`
      have hcard' : (s6a_sing_params_finite F i (s₁ + ε') t₁).toFinset.card ≤ N := by
        have hsub : (s6a_sing_params_finite F i (s₁ + ε') t₁).toFinset ⊆
            (s6a_sing_params_finite F i t₀ t₁).toFinset.erase s₁ := by
          intro s hs
          rw [Set.Finite.mem_toFinset] at hs
          rw [Finset.mem_erase, Set.Finite.mem_toFinset]
          exact ⟨by linarith [hs.1.1], ⟨⟨by linarith [hs.1.1], hs.1.2⟩, hs.2⟩⟩
        have h1 := Finset.card_le_card hsub
        rw [Finset.card_erase_of_mem (by rw [Set.Finite.mem_toFinset]; exact ⟨⟨hs₁0, hs₁1⟩, hs₁x⟩)] at h1
        omega
      obtain ⟨m₂, hpath2, hσ2⟩ := ih (s₁ + ε') (by linarith) hp
        (fun p hp1 s hs => hno p hp1 s ⟨by linarith [hs.1], hs.2⟩) hcard'
      refine ⟨m₂ + m₁, ?_, ?_⟩
      · rw [Function.iterate_add_apply, hconst, hpath1, hpath2]
      · intro j hj
        rcases Nat.lt_or_ge j m₁ with h | h
        · rw [hconst]; exact hσ1 j h
        · obtain ⟨j', rfl⟩ : ∃ j', j = j' + m₁ := ⟨j - m₁, by omega⟩
          rw [Function.iterate_add_apply, hconst, hpath1]
          exact hσ2 j' (by omega)
    · -- no singular parameter at all: the slot is constant
      rw [Finset.not_nonempty_iff_eq_empty] at hne
      have hS : ∀ s ∈ Set.Icc t₀ t₁, xOf F i s ∉ singX F := by
        intro s hs hsx
        have hmem : s ∈ (s6a_sing_params_finite F i t₀ t₁).toFinset := by
          rw [Set.Finite.mem_toFinset]; exact ⟨hs, hsx⟩
        rw [hne] at hmem
        simp at hmem
      refine ⟨0, ?_, fun j hj => absurd hj (Nat.not_lt_zero _)⟩
      exact slotAt_const F h01.le hS

/-! ### S6b helpers -/
section S6bHelpers

/-! #### periodicity of `xOf` and `slotAt` in the parameter -/

theorem s6b_xOf_add_int (i : Fin F.c) (t : ℝ) (n : ℤ) : xOf F i (t + n) = xOf F i t := by
  unfold xOf; rw [(F.comp i).eq_add_int n t]

theorem s6b_fract_add_int (t : ℝ) (n : ℤ) : Int.fract (t + n) = Int.fract t := Int.fract_add_intCast t n

theorem s6b_slotAt_add_int {i : Fin F.c} {t : ℝ} (n : ℤ) (h : xOf F i t ∉ singX F)
    (h' : xOf F i (t + n) ∉ singX F) : slotAt F i (t + n) h' = slotAt F i t h := by
  apply Subtype.ext
  show (colAt F (xOf F i (t + n)), posAt F (xOf F i (t + n)) (i, Int.fract (t + n))) =
    (colAt F (xOf F i t), posAt F (xOf F i t) (i, Int.fract t))
  rw [s6b_xOf_add_int, s6b_fract_add_int]

theorem s6b_notMem_singX_add_int {i : Fin F.c} {t : ℝ} (n : ℤ) (h : xOf F i t ∉ singX F) :
    xOf F i (t + n) ∉ singX F := by rwa [s6b_xOf_add_int]

/-! #### the singular parameters of a circle in a bounded interval form a finite set -/

theorem s6b_singParams_finite (i : Fin F.c) (a b : ℝ) :
    {s : ℝ | s ∈ Set.Ioo a b ∧ xOf F i s ∈ singX F}.Finite := by
  have hsub : {s : ℝ | s ∈ Set.Ioo a b ∧ xOf F i s ∈ singX F} ⊆
      ⋃ x ∈ (singX F : Set ℝ), {s : ℝ | s ∈ Set.Icc a b ∧ xOf F i s = x} := by
    intro s hs
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq, Finset.mem_coe, exists_prop]
    exact ⟨xOf F i s, hs.2, ⟨hs.1.1.le, hs.1.2.le⟩, rfl⟩
  refine Set.Finite.subset (Set.Finite.biUnion (Finset.finite_toSet _) fun x _ => ?_) hsub
  -- `s ↦ (fract s, ⌊s⌋)` is injective into `fibre × Icc ⌊a⌋ ⌊b⌋`
  have hfin : ((fibre F i x) ×ˢ (Set.Icc (⌊a⌋ : ℤ) ⌊b⌋)).Finite :=
    (fibre_finite F i x).prod (Set.finite_Icc _ _)
  refine Set.Finite.of_finite_image (f := fun s : ℝ => (Int.fract s, ⌊s⌋)) (hfin.subset ?_) ?_
  · rintro ⟨u, n⟩ ⟨s, ⟨⟨hsa, hsb⟩, hsx⟩, hsu⟩
    simp only [Prod.mk.injEq] at hsu
    obtain ⟨rfl, rfl⟩ := hsu
    refine ⟨⟨⟨Int.fract_nonneg s, Int.fract_lt_one s⟩, ?_⟩, Int.floor_le_floor hsa, Int.floor_le_floor hsb⟩
    show xOf F i (Int.fract s) = x
    rw [← hsx]
    have : s = Int.fract s + (⌊s⌋ : ℤ) := by rw [Int.fract]; ring
    conv_rhs => rw [this]
    rw [s6b_xOf_add_int]
  · intro s _ s' _ hss'
    simp only [Prod.mk.injEq] at hss'
    have h1 : s = Int.fract s + (⌊s⌋ : ℤ) := by rw [Int.fract]; ring
    have h2 : s' = Int.fract s' + (⌊s'⌋ : ℤ) := by rw [Int.fract]; ring
    rw [h1, h2, hss'.1, hss'.2]

/-- the finite set of singular parameters strictly between `a` and `b` -/

def s6b_singParams (i : Fin F.c) (a b : ℝ) : Finset ℝ := (s6b_singParams_finite F i a b).toFinset

theorem s6b_mem_singParams (i : Fin F.c) (a b s : ℝ) :
    s ∈ s6b_singParams F i a b ↔ s ∈ Set.Ioo a b ∧ xOf F i s ∈ singX F := by
  unfold s6b_singParams; rw [Set.Finite.mem_toFinset]; rfl

/-! #### occurrences and cusps at lifted parameters -/

theorem s6b_isCusp_of_cusp_sameParam {i : Fin F.c} {s : ℝ} (c : F.Cusp) (h : SameParam c.1 (i, s)) :
    F.IsCusp (i, s) := (F.isCusp_iff_of_sameParam h).mpr c.isCusp

theorem s6b_not_isCusp_occ (p : F.Occ) : ¬ F.IsCusp p.1 := F.not_isCusp_of_isDouble (isDouble_partner F p)

theorem s6b_isDouble_of_occ_sameParam {i : Fin F.c} {s : ℝ} (p : F.Occ) (h : SameParam p.1 (i, s)) :
    F.IsDouble (i, s) (partner F p).1 := by
  obtain ⟨hne, he⟩ := isDouble_partner F p
  refine ⟨fun hs => hne (h.trans hs), ?_⟩
  rw [SmoothFront.eval_of_sameParam h]; exact he

theorem s6b_not_isCusp_of_occ_sameParam {i : Fin F.c} {s : ℝ} (p : F.Occ) (h : SameParam p.1 (i, s)) :
    ¬ F.IsCusp (i, s) := F.not_isCusp_of_isDouble (s6b_isDouble_of_occ_sameParam F p h)

/-- two occurrences at the same lifted parameter coincide -/

theorem s6b_occ_eq_of_sameParam {i : Fin F.c} {s : ℝ} (p p' : F.Occ) (h : SameParam p.1 (i, s))
    (h' : SameParam p'.1 (i, s)) : p = p' :=
  Subtype.ext (SameParam.eq_of_mem_Ico p.2.1 p'.2.1 (h.trans h'.symm))

theorem s6b_cusp_eq_of_sameParam {i : Fin F.c} {s : ℝ} (c c' : F.Cusp) (h : SameParam c.1 (i, s))
    (h' : SameParam c'.1 (i, s)) : c = c' :=
  Subtype.ext (SameParam.eq_of_mem_Ico c.mem_Ico c'.mem_Ico (h.trans h'.symm))

theorem s6b_sameParam_rep (i : Fin F.c) (s : ℝ) : SameParam (i, Int.fract s) (i, s) :=
  (SameParam.sameParam_rep (i, s)).symm

theorem s6b_eq_fract_add_floor (s : ℝ) : s = Int.fract s + (⌊s⌋ : ℤ) := by rw [Int.fract]; ring

theorem s6b_slotAt_eq_of_eq_add {i : Fin F.c} {t t' : ℝ} {n : ℤ} (e : t' = t + n) (h : xOf F i t ∉ singX F)
    (h' : xOf F i t' ∉ singX F) : slotAt F i t' h' = slotAt F i t h := by
  subst e; exact s6b_slotAt_add_int F n h h'

theorem s6b_notMem_singX_of_eq_add {i : Fin F.c} {t t' : ℝ} {n : ℤ} (e : t' = t + n) (h : xOf F i t ∉ singX F) :
    xOf F i t' ∉ singX F := by subst e; exact s6b_notMem_singX_add_int F n h

/-- the occurrence of a double point at an arbitrary (lifted) parameter -/

theorem s6b_occ_of_isDouble {i : Fin F.c} {s : ℝ} {q : Param F.c} (hd : F.IsDouble (i, s) q) :
    (i, Int.fract s) ∈ F.occSet := by
  refine ⟨⟨Int.fract_nonneg s, Int.fract_lt_one s⟩, SameParam.rep q, SameParam.rep_mem_Ico q, ?_, ?_⟩
  · intro heq
    apply hd.1
    have h1 : SameParam (i, s) (i, Int.fract s) := SameParam.sameParam_rep (i, s)
    have h2 : SameParam q (SameParam.rep q) := SameParam.sameParam_rep q
    rw [← heq] at h2
    exact h1.trans h2.symm
  · rw [SmoothFront.eval_of_sameParam (SameParam.sameParam_rep q)]
    exact (SmoothFront.eval_of_sameParam (SameParam.sameParam_rep (i, s))).trans hd.2

/-- THE JUMP AT ANY SINGULAR PARAMETER (lifted from the three jump leaves by periodicity): the slot path across a
singular parameter `s` of circle `i`; every `σ` slot on it is `Φ` of an occurrence at `s`, and the cusp vertex of
every cusp at `s` is on it. -/

theorem s6b_jump {i : Fin F.c} {s : ℝ} (hs : xOf F i s ∈ singX F) :
    ∃ ε > 0, ∀ ε' ∈ Set.Ioo (0 : ℝ) ε, ∃ (h₁ : xOf F i (s - ε') ∉ singX F) (h₂ : xOf F i (s + ε') ∉ singX F) (m : ℕ),
      0 < m ∧ (next (word_closed F))^[m] (slotAt F i (s - ε') h₁) = slotAt F i (s + ε') h₂ ∧
      (∀ j < m, U2.IsσSlot ((next (word_closed F))^[j] (slotAt F i (s - ε') h₁)) →
        ∃ p : F.Occ, SameParam p.1 (i, s) ∧ (next (word_closed F))^[j] (slotAt F i (s - ε') h₁) = ΦFun F p) ∧
      (∀ c : F.Cusp, SameParam c.1 (i, s) →
        ∃ a < m, (next (word_closed F))^[a] (slotAt F i (s - ε') h₁) = cuspVertex F c) := by
  by_cases hc : F.IsCusp (i, s)
  · -- a cusp: `jump_cusp` at its representative, shifted by `⌊s⌋`
    obtain ⟨ε, hε, H⟩ := jump_cusp F ⟨SameParam.rep (i, s), F.rep_mem_cuspSet hc⟩
    refine ⟨ε, hε, fun ε' hε' => ?_⟩
    obtain ⟨h₁', h₂', m, hm, hpath, hnoσ, a, ha, hav⟩ := H ε' hε'
    have e₁ : s - ε' = (Int.fract s - ε') + (⌊s⌋ : ℤ) := by rw [Int.fract]; ring
    have e₂ : s + ε' = (Int.fract s + ε') + (⌊s⌋ : ℤ) := by rw [Int.fract]; ring
    have h₁'' : xOf F i (Int.fract s - ε') ∉ singX F := h₁'
    have h₂'' : xOf F i (Int.fract s + ε') ∉ singX F := h₂'
    refine ⟨s6b_notMem_singX_of_eq_add F e₁ h₁'', s6b_notMem_singX_of_eq_add F e₂ h₂'', m, hm, ?_, ?_, ?_⟩
    · rw [s6b_slotAt_eq_of_eq_add F e₁ h₁'', s6b_slotAt_eq_of_eq_add F e₂ h₂'']; exact hpath
    · intro j hj hσ
      rw [s6b_slotAt_eq_of_eq_add F e₁ h₁''] at hσ
      exact absurd hσ (hnoσ j hj)
    · intro c' hc'
      have hcc : c' = ⟨SameParam.rep (i, s), F.rep_mem_cuspSet hc⟩ :=
        s6b_cusp_eq_of_sameParam F c' _ hc' (s6b_sameParam_rep F i s)
      subst hcc
      refine ⟨a, ha, ?_⟩
      rw [s6b_slotAt_eq_of_eq_add F e₁ h₁'']; exact hav
  · by_cases hd : ∃ q, F.IsDouble (i, s) q
    · -- a double point: `jump_cross` at its occurrence, shifted by `⌊s⌋`
      obtain ⟨q, hq⟩ := hd
      obtain ⟨ε, hε, H⟩ := jump_cross F ⟨(i, Int.fract s), s6b_occ_of_isDouble F hq⟩
      refine ⟨ε, hε, fun ε' hε' => ?_⟩
      obtain ⟨h₁', h₂', m, hm, hpath, a, ha, hav, hnoσ⟩ := H ε' hε'
      have e₁ : s - ε' = (Int.fract s - ε') + (⌊s⌋ : ℤ) := by rw [Int.fract]; ring
      have e₂ : s + ε' = (Int.fract s + ε') + (⌊s⌋ : ℤ) := by rw [Int.fract]; ring
      have h₁'' : xOf F i (Int.fract s - ε') ∉ singX F := h₁'
      have h₂'' : xOf F i (Int.fract s + ε') ∉ singX F := h₂'
      refine ⟨s6b_notMem_singX_of_eq_add F e₁ h₁'', s6b_notMem_singX_of_eq_add F e₂ h₂'', m, hm, ?_, ?_, ?_⟩
      · rw [s6b_slotAt_eq_of_eq_add F e₁ h₁'', s6b_slotAt_eq_of_eq_add F e₂ h₂'']; exact hpath
      · intro j hj hσ
        rw [s6b_slotAt_eq_of_eq_add F e₁ h₁''] at hσ ⊢
        by_cases hja : j = a
        · subst hja
          exact ⟨_, s6b_sameParam_rep F i s, hav⟩
        · exact absurd hσ (hnoσ j hj hja)
      · intro c' hc'
        exact absurd (s6b_isCusp_of_cusp_sameParam F c' hc') hc
    · -- a regular point over a singular x-value
      push Not at hd
      obtain ⟨ε, hε, H⟩ := jump_regular F hs hc hd
      refine ⟨ε, hε, fun ε' hε' => ?_⟩
      obtain ⟨h₁', h₂', m, hm, hpath, hnoσ⟩ := H ε' hε'
      exact ⟨h₁', h₂', m, hm, hpath, fun j hj hσ => absurd hσ (hnoσ j hj),
        fun c' hc' => absurd (s6b_isCusp_of_cusp_sameParam F c' hc') hc⟩

/-! #### THE PATH along a parameter interval: induction on the singular parameters inside it -/

/-- `slotAt t₀` reaches `slotAt t₁` by `next` steps; every `σ` slot on the way is `Φ` of an occurrence of the
circle at a parameter strictly inside `(t₀, t₁)`; the cusp vertex of every cusp of the circle strictly inside is
on the way.  (Strong induction on the number of singular parameters inside; `slotAt_const` up to the first one,
`s6b_jump` across it.) -/

theorem s6b_path_aux {i : Fin F.c} {t₁ : ℝ} (h₁ : xOf F i t₁ ∉ singX F) (N : ℕ) :
    ∀ (t₀ : ℝ) (_h01 : t₀ < t₁) (h₀ : xOf F i t₀ ∉ singX F), (s6b_singParams F i t₀ t₁).card = N →
    ∃ m, (next (word_closed F))^[m] (slotAt F i t₀ h₀) = slotAt F i t₁ h₁ ∧
      (∀ j < m, U2.IsσSlot ((next (word_closed F))^[j] (slotAt F i t₀ h₀)) →
        ∃ p : F.Occ, (∃ s ∈ Set.Ioo t₀ t₁, SameParam p.1 (i, s)) ∧
          (next (word_closed F))^[j] (slotAt F i t₀ h₀) = ΦFun F p) ∧
      (∀ c : F.Cusp, ∀ s ∈ Set.Ioo t₀ t₁, SameParam c.1 (i, s) →
        ∃ a < m, (next (word_closed F))^[a] (slotAt F i t₀ h₀) = cuspVertex F c) := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro t₀ h01 h₀ hN
  by_cases hemp : s6b_singParams F i t₀ t₁ = ∅
  · -- no singular parameter inside: the slot is constant
    have hreg : ∀ t ∈ Set.Icc t₀ t₁, xOf F i t ∉ singX F := by
      intro t ht hsing
      rcases eq_or_lt_of_le ht.1 with rfl | hlt
      · exact h₀ hsing
      rcases eq_or_lt_of_le ht.2 with rfl | hlt'
      · exact h₁ hsing
      have : t ∈ s6b_singParams F i t₀ t₁ := (s6b_mem_singParams F i t₀ t₁ t).mpr ⟨⟨hlt, hlt'⟩, hsing⟩
      rw [hemp] at this; exact absurd this (Finset.notMem_empty t)
    refine ⟨0, ?_, fun j hj => absurd hj (Nat.not_lt_zero j), fun c s hs hcs => ?_⟩
    · rw [Function.iterate_zero_apply]
      exact slotAt_const F h01.le hreg
    · exfalso
      have hsing : xOf F i s ∈ singX F := mem_singX_of_isCusp F (s6b_isCusp_of_cusp_sameParam F c hcs)
      have : s ∈ s6b_singParams F i t₀ t₁ := (s6b_mem_singParams F i t₀ t₁ s).mpr ⟨hs, hsing⟩
      rw [hemp] at this; exact absurd this (Finset.notMem_empty s)
  · -- split at the smallest singular parameter `s₁`
    have hne : (s6b_singParams F i t₀ t₁).Nonempty := Finset.nonempty_iff_ne_empty.mpr hemp
    obtain ⟨s₁, hs₁mem, hmin⟩ : ∃ s₁ ∈ s6b_singParams F i t₀ t₁, ∀ s ∈ s6b_singParams F i t₀ t₁, s₁ ≤ s :=
      ⟨_, Finset.min'_mem _ hne, fun s hs => Finset.min'_le _ s hs⟩
    obtain ⟨hs₁Ioo, hs₁sing⟩ := (s6b_mem_singParams F i t₀ t₁ s₁).mp hs₁mem
    -- the gap to the next singular parameter
    obtain ⟨g, hg, hgap⟩ : ∃ g > 0, ∀ s ∈ s6b_singParams F i t₀ t₁, s ≠ s₁ → s₁ + g ≤ s := by
      by_cases hne' : ((s6b_singParams F i t₀ t₁).erase s₁).Nonempty
      · refine ⟨((s6b_singParams F i t₀ t₁).erase s₁).min' hne' - s₁, ?_, fun s hs hss => ?_⟩
        · have hm := Finset.min'_mem _ hne'
          rw [Finset.mem_erase] at hm
          have h1 := hmin _ hm.2
          have h2 := lt_of_le_of_ne h1 (Ne.symm hm.1)
          linarith
        · have : ((s6b_singParams F i t₀ t₁).erase s₁).min' hne' ≤ s :=
            Finset.min'_le _ _ (Finset.mem_erase.mpr ⟨hss, hs⟩)
          linarith
      · exact ⟨1, one_pos, fun s hs hss => absurd ⟨s, Finset.mem_erase.mpr ⟨hss, hs⟩⟩ hne'⟩
    obtain ⟨ε, hε, H⟩ := s6b_jump F hs₁sing
    obtain ⟨ε', hε'pos, hε'ε, hε'a, hε'b, hε'g⟩ :
        ∃ ε' > 0, ε' < ε ∧ ε' < s₁ - t₀ ∧ ε' < t₁ - s₁ ∧ ε' < g := by
      have h1 : 0 < s₁ - t₀ := by linarith [hs₁Ioo.1]
      have h2 : 0 < t₁ - s₁ := by linarith [hs₁Ioo.2]
      have hpos : 0 < min (min ε (s₁ - t₀)) (min (t₁ - s₁) g) := lt_min (lt_min hε h1) (lt_min h2 hg)
      have m1 : min (min ε (s₁ - t₀)) (min (t₁ - s₁) g) ≤ ε := (min_le_left _ _).trans (min_le_left _ _)
      have m2 : min (min ε (s₁ - t₀)) (min (t₁ - s₁) g) ≤ s₁ - t₀ := (min_le_left _ _).trans (min_le_right _ _)
      have m3 : min (min ε (s₁ - t₀)) (min (t₁ - s₁) g) ≤ t₁ - s₁ := (min_le_right _ _).trans (min_le_left _ _)
      have m4 : min (min ε (s₁ - t₀)) (min (t₁ - s₁) g) ≤ g := (min_le_right _ _).trans (min_le_right _ _)
      exact ⟨min (min ε (s₁ - t₀)) (min (t₁ - s₁) g) / 2, half_pos hpos, by linarith, by linarith, by linarith,
        by linarith⟩
    obtain ⟨h₁', h₂', m₁, hm₁, hpath₁, hσ₁, hcusp₁⟩ := H ε' ⟨hε'pos, hε'ε⟩
    -- the slot is constant from `t₀` to `s₁ - ε'`
    have hA : ∀ t ∈ Set.Icc t₀ (s₁ - ε'), xOf F i t ∉ singX F := by
      intro t ht hsing
      rcases eq_or_lt_of_le ht.1 with rfl | hlt
      · exact h₀ hsing
      have htS : t ∈ s6b_singParams F i t₀ t₁ :=
        (s6b_mem_singParams F i t₀ t₁ t).mpr ⟨⟨hlt, by linarith [ht.2, hs₁Ioo.2]⟩, hsing⟩
      have := hmin t htS
      linarith [ht.2]
    have hconst : slotAt F i t₀ h₀ = slotAt F i (s₁ - ε') h₁' := slotAt_const F (by linarith) hA
    -- the induction hypothesis from `s₁ + ε'`
    have hcard : (s6b_singParams F i (s₁ + ε') t₁).card < N := by
      rw [← hN]
      apply Finset.card_lt_card
      have hsub : s6b_singParams F i (s₁ + ε') t₁ ⊆ s6b_singParams F i t₀ t₁ := by
        intro s hs
        obtain ⟨hsI, hss⟩ := (s6b_mem_singParams F i _ _ s).mp hs
        exact (s6b_mem_singParams F i t₀ t₁ s).mpr ⟨⟨by linarith [hsI.1, hs₁Ioo.1], hsI.2⟩, hss⟩
      refine (Finset.ssubset_iff_of_subset hsub).mpr ⟨s₁, hs₁mem, fun h => ?_⟩
      have := ((s6b_mem_singParams F i _ _ s₁).mp h).1.1
      linarith
    obtain ⟨m₂, hpath₂, hσ₂, hcusp₂⟩ := ih _ hcard (s₁ + ε') (by linarith) h₂' rfl
    refine ⟨m₂ + m₁, ?_, ?_, ?_⟩
    · rw [Function.iterate_add_apply, hconst, hpath₁, hpath₂]
    · intro j hj hσ
      rw [hconst] at hσ ⊢
      by_cases hjm : j < m₁
      · obtain ⟨p, hp, hpj⟩ := hσ₁ j hjm hσ
        exact ⟨p, ⟨s₁, hs₁Ioo, hp⟩, hpj⟩
      · obtain ⟨j', rfl⟩ : ∃ j', j = j' + m₁ := ⟨j - m₁, by omega⟩
        rw [Function.iterate_add_apply, hpath₁] at hσ ⊢
        obtain ⟨p, ⟨s, hs, hp⟩, hpj⟩ := hσ₂ j' (by omega) hσ
        exact ⟨p, ⟨s, ⟨by linarith [hs.1, hs₁Ioo.1], hs.2⟩, hp⟩, hpj⟩
    · intro c s hs hcs
      have hsing : xOf F i s ∈ singX F := mem_singX_of_isCusp F (s6b_isCusp_of_cusp_sameParam F c hcs)
      have hsS : s ∈ s6b_singParams F i t₀ t₁ := (s6b_mem_singParams F i t₀ t₁ s).mpr ⟨hs, hsing⟩
      rw [hconst]
      by_cases hss : s = s₁
      · rw [hss] at hcs
        obtain ⟨a, ha, hav⟩ := hcusp₁ c hcs
        exact ⟨a, by omega, hav⟩
      · have hge := hgap s hsS hss
        obtain ⟨a, ha, hav⟩ := hcusp₂ c s ⟨by linarith, hs.2⟩ hcs
        refine ⟨a + m₁, by omega, ?_⟩
        rw [Function.iterate_add_apply, hpath₁]; exact hav

/-- the path lemma in its direct form -/

theorem s6b_path {i : Fin F.c} {t₀ t₁ : ℝ} (h01 : t₀ < t₁) (h₀ : xOf F i t₀ ∉ singX F)
    (h₁ : xOf F i t₁ ∉ singX F) :
    ∃ m, (next (word_closed F))^[m] (slotAt F i t₀ h₀) = slotAt F i t₁ h₁ ∧
      (∀ j < m, U2.IsσSlot ((next (word_closed F))^[j] (slotAt F i t₀ h₀)) →
        ∃ p : F.Occ, (∃ s ∈ Set.Ioo t₀ t₁, SameParam p.1 (i, s)) ∧
          (next (word_closed F))^[j] (slotAt F i t₀ h₀) = ΦFun F p) ∧
      (∀ c : F.Cusp, ∀ s ∈ Set.Ioo t₀ t₁, SameParam c.1 (i, s) →
        ∃ a < m, (next (word_closed F))^[a] (slotAt F i t₀ h₀) = cuspVertex F c) :=
  s6b_path_aux F h₁ _ t₀ h01 h₀ rfl

/-! #### cycles: slots of one circle lie on one cycle; a slot with position `0` is a cusp vertex -/

theorem s6b_sameCycle_slotAt {i : Fin F.c} {t t' : ℝ} (h : xOf F i t ∉ singX F) (h' : xOf F i t' ∉ singX F) :
    (nextPerm (word_closed F)).SameCycle (slotAt F i t h) (slotAt F i t' h') := by
  rcases lt_trichotomy t t' with hlt | rfl | hgt
  · obtain ⟨m, hm, -, -⟩ := s6b_path F hlt h h'
    exact sameCycle_of_iterate (word_closed F) (a := m) (b := 0) (by rw [Function.iterate_zero_apply]; exact hm)
  · exact Equiv.Perm.SameCycle.refl _ _
  · obtain ⟨m, hm, -, -⟩ := s6b_path F hgt h' h
    exact (sameCycle_of_iterate (word_closed F) (a := m) (b := 0)
      (by rw [Function.iterate_zero_apply]; exact hm)).symm

theorem s6b_slotAt_fst_eq {i j : Fin F.c} (hij : j = i) {t : ℝ} (h : xOf F j t ∉ singX F)
    (h' : xOf F i t ∉ singX F) : slotAt F j t h = slotAt F i t h' := by subst hij; rfl

/-- the cusp vertex of a cusp lies on the cycle of its circle -/

theorem s6b_sameCycle_cuspVertex (c : F.Cusp) {t : ℝ} (h : xOf F c.1.1 t ∉ singX F) :
    (nextPerm (word_closed F)).SameCycle (slotAt F c.1.1 t h) (cuspVertex F c) := by
  obtain ⟨ε, hε, H⟩ := jump_cusp F c
  obtain ⟨h₁, -, m, -, -, -, a, -, hav⟩ := H (ε / 2) ⟨half_pos hε, half_lt_self hε⟩
  exact (s6b_sameCycle_slotAt F h h₁).trans
    (sameCycle_of_iterate (word_closed F) (a := a) (b := 0) (by rw [Function.iterate_zero_apply]; exact hav))

/-- the slot of an occurrence lies on the cycle of its circle -/

theorem s6b_sameCycle_ΦFun (p : F.Occ) {t : ℝ} (h : xOf F p.1.1 t ∉ singX F) :
    (nextPerm (word_closed F)).SameCycle (slotAt F p.1.1 t h) (ΦFun F p) := by
  obtain ⟨ε, hε, H⟩ := jump_cross F p
  obtain ⟨h₁, -, m, -, -, a, -, hav, -⟩ := H (ε / 2) ⟨half_pos hε, half_lt_self hε⟩
  exact (s6b_sameCycle_slotAt F h h₁).trans
    (sameCycle_of_iterate (word_closed F) (a := a) (b := 0) (by rw [Function.iterate_zero_apply]; exact hav))

/-- every circle has a non-singular parameter -/

theorem s6b_exists_regular (i : Fin F.c) : ∃ t : ℝ, xOf F i t ∉ singX F := by
  obtain ⟨ε, hε, H⟩ := jump_cusp F (someCuspOn F i)
  obtain ⟨h₁, -⟩ := H (ε / 2) ⟨half_pos hε, half_lt_self hε⟩
  refine ⟨(someCuspOn F i).1.2 - ε / 2, ?_⟩
  rwa [someCuspOn_fst] at h₁

/-- the cycle of a cusp vertex is the component of its circle -/

theorem s6b_slotComp_cuspVertex (c : F.Cusp) :
    U2.slotComp (word_closed F) (cuspVertex F c) = circleComp F c.1.1 := by
  unfold circleComp
  rw [U2.slotComp_eq_iff]
  obtain ⟨t, ht⟩ := s6b_exists_regular F c.1.1
  have ht' : xOf F (someCuspOn F c.1.1).1.1 t ∉ singX F := by rwa [someCuspOn_fst]
  have e := s6b_slotAt_fst_eq F (someCuspOn_fst F c.1.1) ht' ht
  have h2 := s6b_sameCycle_cuspVertex F (someCuspOn F c.1.1) ht'
  rw [e] at h2
  exact (s6b_sameCycle_cuspVertex F c ht).symm.trans h2

/-- a slot at position `0` is the cusp vertex of the cusp of its column -/

theorem s6b_cuspVertex_of_snd_eq_zero (u : Slot (word F)) (h : u.1.2 = 0) : ∃ c : F.Cusp, u = cuspVertex F c := by
  obtain ⟨⟨k, p⟩, hu⟩ := u
  simp only at h
  subst h
  rcases hu with ⟨-, hk, hσ⟩ | ⟨h1, -, -⟩
  · have hk' : k < (events F).length := by rwa [length_word] at hk
    have hl := letterAt_word F hk'
    rcases he : eventAt F k with c | q
    · refine ⟨c, Subtype.ext ?_⟩
      show (k, 0) = (evIdx F (Sum.inl c), 0)
      rw [← he, evIdx_eventAt F hk']
    · exfalso
      simp only at hσ
      rw [hl, he] at hσ
      exact absurd hσ (by simp [letterOf, isCrossing])
  · simp at h1

/-! #### the cyclic successor of an occurrence: no occurrence strictly between, and the shifted crossing jump -/

/-- `jump_cross` at the parameter `p.1.2 + n` (periodicity) -/

theorem s6b_jump_cross_shift (p : F.Occ) (n : ℤ) :
    ∃ ε > 0, ∀ ε' ∈ Set.Ioo (0 : ℝ) ε, ∃ (h₁ : xOf F p.1.1 (p.1.2 + n - ε') ∉ singX F)
      (h₂ : xOf F p.1.1 (p.1.2 + n + ε') ∉ singX F) (m : ℕ),
      0 < m ∧ (next (word_closed F))^[m] (slotAt F p.1.1 (p.1.2 + n - ε') h₁) = slotAt F p.1.1 (p.1.2 + n + ε') h₂ ∧
      ∃ a < m, (next (word_closed F))^[a] (slotAt F p.1.1 (p.1.2 + n - ε') h₁) = ΦFun F p ∧
        ∀ j < m, j ≠ a → ¬ U2.IsσSlot ((next (word_closed F))^[j] (slotAt F p.1.1 (p.1.2 + n - ε') h₁)) := by
  obtain ⟨ε, hε, H⟩ := jump_cross F p
  refine ⟨ε, hε, fun ε' hε' => ?_⟩
  obtain ⟨h₁', h₂', m, hm, hpath, a, ha, hav, hnoσ⟩ := H ε' hε'
  have e₁ : p.1.2 + n - ε' = (p.1.2 - ε') + n := by ring
  have e₂ : p.1.2 + n + ε' = (p.1.2 + ε') + n := by ring
  refine ⟨s6b_notMem_singX_of_eq_add F e₁ h₁', s6b_notMem_singX_of_eq_add F e₂ h₂', m, hm, ?_, a, ha, ?_, ?_⟩
  · rw [s6b_slotAt_eq_of_eq_add F e₁ h₁', s6b_slotAt_eq_of_eq_add F e₂ h₂']; exact hpath
  · rw [s6b_slotAt_eq_of_eq_add F e₁ h₁']; exact hav
  · intro j hj hja
    rw [s6b_slotAt_eq_of_eq_add F e₁ h₁']
    exact hnoσ j hj hja

/-- no occurrence of the circle lies strictly between `p` and its cyclic successor (lifted to the real line:
the successor's parameter is read in `(p.1.2, p.1.2 + 1]`) -/

theorem s6b_no_occ_between (p q : F.Occ) {n : ℤ}
    (hn : n = if p.1.2 < (cycNext (occComp F) (occKey F) (occKey_inj F) p).1.2 then 0 else 1) {s : ℝ}
    (hs : s ∈ Set.Ioo p.1.2 ((cycNext (occComp F) (occKey F) (occKey_inj F) p).1.2 + n))
    (hq : SameParam q.1 (p.1.1, s)) : False := by
  obtain ⟨p', hp'⟩ : ∃ p', p' = cycNext (occComp F) (occKey F) (occKey_inj F) p := ⟨_, rfl⟩
  rw [← hp'] at hn hs
  have hcomp : occComp F p' = occComp F p := by rw [hp']; exact comp_cycNext (occComp F) (occKey F) (occKey_inj F) p
  have hqcomp : occComp F q = occComp F p := hq.1
  have hnb : ¬ cycBetween p.1.2 q.1.2 p'.1.2 := by
    have := cycNext_no_between (occComp F) (occKey F) (occKey_inj F) p q hqcomp
    rw [← hp'] at this
    exact this
  obtain ⟨-, z, hz⟩ := hq
  simp only at hz
  have hq0 := (SmoothFront.Occ.mem_Ico F q).1
  have hq1 := (SmoothFront.Occ.mem_Ico F q).2
  have hp0 := (SmoothFront.Occ.mem_Ico F p).1
  have hp1 := (SmoothFront.Occ.mem_Ico F p).2
  have hp'0 := (SmoothFront.Occ.mem_Ico F p').1
  have hp'1 := (SmoothFront.Occ.mem_Ico F p').2
  obtain ⟨hs1, hs2⟩ := hs
  by_cases hab : p.1.2 < p'.1.2
  · rw [if_pos hab] at hn
    subst hn
    push_cast at hs2
    -- `s ∈ (a, b) ⊆ [0, 1)`, so `z = 0`
    have hz1 : (z : ℝ) < 1 := by linarith
    have hz2 : (-1 : ℝ) < z := by linarith
    have hz3 : z < 1 := by exact_mod_cast hz1
    have hz4 : -1 < z := by exact_mod_cast hz2
    have hz0 : z = 0 := by omega
    subst hz0
    simp only [Int.cast_zero, add_zero] at hz
    exact hnb (Or.inl ⟨by linarith, by linarith⟩)
  · rw [if_neg hab] at hn
    subst hn
    push_cast at hs2
    push Not at hab
    rcases eq_or_lt_of_le hab with heq | hlt
    · -- `p' = p`: `p` is alone on its circle, so `q = p`, impossible strictly inside one period
      have hpp : p' = p := occKey_inj F p' p hcomp heq
      have halone : ∀ w : F.Occ, occComp F w = occComp F p → w = p := by
        intro w hw
        by_contra hne
        exact cycNext_ne_self (occComp F) (occKey F) (occKey_inj F) p w hw hne (hpp ▸ hp'.symm)
      have hqp : q = p := halone q hqcomp
      subst hqp
      rw [heq] at hs2
      have hz1 : (z : ℝ) < 1 := by linarith
      have hz2 : (0 : ℝ) < z := by linarith
      have hz3 : z < 1 := by exact_mod_cast hz1
      have hz4 : 0 < z := by exact_mod_cast hz2
      omega
    · by_cases hs1' : s < 1
      · have hz1 : (z : ℝ) < 1 := by linarith
        have hz2 : (-1 : ℝ) < z := by linarith
        have hz3 : z < 1 := by exact_mod_cast hz1
        have hz4 : -1 < z := by exact_mod_cast hz2
        have hz0 : z = 0 := by omega
        subst hz0
        simp only [Int.cast_zero, add_zero] at hz
        exact hnb (Or.inr (Or.inr ⟨hlt, by linarith⟩))
      · push Not at hs1'
        have hz1 : (z : ℝ) < 2 := by linarith
        have hz2 : (0 : ℝ) < z := by linarith
        have hz3 : z < 2 := by exact_mod_cast hz1
        have hz4 : 0 < z := by exact_mod_cast hz2
        have hz0 : z = 1 := by omega
        subst hz0
        simp only [Int.cast_one] at hz
        exact hnb (Or.inr (Or.inl ⟨by linarith, hlt⟩))

/-! #### CORE: the circle of a slot is preserved by `next`.  Stage 1: list lemmas -/

/-- splitting a filter of a list antitone in `f`: `P = Q ∨ R` with every `R`-value strictly below every `Q`-value -/

theorem s6b_filter_split {α : Type*} (f : α → ℝ) (P Q R : α → Bool) (hPQR : ∀ p, P p = (Q p || R p))
    (hRQ : ∀ p q, R p = true → Q q = true → f p < f q) :
    ∀ L : List α, L.Pairwise (fun p q => f q ≤ f p) → L.filter P = L.filter Q ++ L.filter R := by
  intro L
  induction L with
  | nil => intro _; rfl
  | cons p L ih =>
    intro hL
    rw [List.pairwise_cons] at hL
    obtain ⟨hp, hL⟩ := hL
    have ih' := ih hL
    by_cases hQ : Q p = true
    · have hP : P p = true := by rw [hPQR, hQ]; rfl
      have hR : R p = false := by
        by_contra h
        exact lt_irrefl _ (hRQ p p (by simpa using h) hQ)
      simp [List.filter_cons, hP, hQ, hR, ih']
    · have hQ' : Q p = false := by simpa using hQ
      by_cases hR : R p = true
      · have hP : P p = true := by rw [hPQR, hR]; simp
        have hQL : L.filter Q = [] := by
          rw [List.filter_eq_nil_iff]
          intro q hq hQq
          have h1 := hRQ p q hR hQq
          have h2 := hp q hq
          linarith
        have hPL : L.filter P = L.filter R := by
          apply List.filter_congr
          intro q hq
          rw [hPQR]
          have hQq : Q q = false := by
            by_contra h
            have h' : Q q = true := by simpa using h
            have h1 := hRQ p q hR h'
            have h2 := hp q hq
            linarith
          rw [hQq]; rfl
        simp [List.filter_cons, hP, hQ', hR, hQL, hPL]
      · have hR' : R p = false := by simpa using hR
        have hP : P p = false := by rw [hPQR, hQ', hR']; rfl
        simp [List.filter_cons, hP, hQ', hR', ih']

theorem s6b_entriesOf_append (bits : Param F.c → Cuts) (L L' : List (Param F.c)) :
    entriesOf F bits (L ++ L') = entriesOf F bits L ++ entriesOf F bits L' := by
  unfold entriesOf; rw [List.flatMap_append]

/-- the entries depend only on the number of bits of each point -/

theorem s6b_entriesOf_congr (bits bits' : Param F.c → Cuts) (L : List (Param F.c))
    (h : ∀ p ∈ L, (bits p).length = (bits' p).length) : entriesOf F bits L = entriesOf F bits' L := by
  unfold entriesOf
  induction L with
  | nil => rfl
  | cons p L ih =>
    rw [List.flatMap_cons, List.flatMap_cons, h p (by simp), ih (fun q hq => h q (by simp [hq]))]

theorem s6b_entriesOf_singleton (bits : Param F.c → Cuts) (p : Param F.c) :
    entriesOf F bits [p] = (List.range (bits p).length).map (fun j => (p, j)) := by
  unfold entriesOf; simp

theorem s6b_entriesOf_eq_map (bits : Param F.c → Cuts) (L : List (Param F.c)) (h : ∀ p ∈ L, (bits p).length = 1) :
    entriesOf F bits L = L.map (fun p => (p, 0)) := by
  unfold entriesOf
  induction L with
  | nil => rfl
  | cons p L ih =>
    rw [List.flatMap_cons, List.map_cons, h p (by simp), ih (fun q hq => h q (by simp [hq]))]
    rfl

theorem s6b_length_entriesOf (bits : Param F.c → Cuts) (L : List (Param F.c)) :
    (entriesOf F bits L).length = (L.flatMap bits).length := by
  rw [← map_entryBit_entriesOf F bits L, List.length_map]

theorem s6b_eq_singleton_of_nodup {α : Type*} {L : List α} {a : α} (hnd : L.Nodup) (ha : a ∈ L)
    (h : ∀ b ∈ L, b = a) : L = [a] := by
  cases L with
  | nil => exact absurd ha (List.not_mem_nil)
  | cons b L' =>
    cases L' with
    | nil => rw [h b (by simp)]
    | cons c L'' =>
      exfalso
      have hb := h b (by simp)
      have hc := h c (by simp)
      rw [List.nodup_cons] at hnd
      exact hnd.1 (by rw [hb, ← hc]; simp)

theorem s6b_eq_pair_of_nodup_sorted {α : Type*} {L : List α} {o u : α} (R : α → α → Prop) (hnd : L.Nodup)
    (hmem : ∀ p, p ∈ L ↔ p = o ∨ p = u) (hne : o ≠ u) (hsort : L.Pairwise R) (hR : ¬ R u o) : L = [o, u] := by
  have hperm : L.Perm [o, u] :=
    (List.perm_ext_iff_of_nodup hnd (by simp [hne])).mpr (fun p => by rw [hmem]; simp)
  have hlen : L.length = 2 := by rw [hperm.length_eq]; rfl
  obtain ⟨a, b, rfl⟩ := List.length_eq_two.mp hlen
  have ha : a = o ∨ a = u := (hmem a).mp (by simp)
  have hb : b = o ∨ b = u := (hmem b).mp (by simp)
  have hab : a ≠ b := by rw [List.nodup_cons] at hnd; simpa using hnd.1
  rw [List.pairwise_cons] at hsort
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · exact absurd rfl hab
  · rfl
  · exact absurd (hsort.1 _ (by simp)) hR
  · exact absurd rfl hab

/-- two strictly `f`-sorted lists with the same members are equal -/

theorem s6b_sorted_eq {α : Type*} (f : α → ℝ) {L L' : List α} (hL : L.Pairwise (fun p q => f q < f p))
    (hL' : L'.Pairwise (fun p q => f q < f p)) (hmem : ∀ p, p ∈ L ↔ p ∈ L') : L = L' := by
  have : Std.Irrefl (fun p q : α => f q < f p) := ⟨fun p => lt_irrefl _⟩
  have : Std.Antisymm (fun p q : α => f q < f p) := ⟨fun p q h1 h2 => absurd (h1.trans h2) (lt_irrefl _)⟩
  exact List.Pairwise.eq_of_mem_iff hL hL' hmem

/-! #### Stage 2: the sorted events and regular fibre points -/

theorem s6b_colX_evIdx (e : Event F) : colX F (evIdx F e) = evX F e := by unfold colX; rw [eventAt_evIdx]

theorem s6b_colZ_evIdx (e : Event F) : colZ F (evIdx F e) = evZ F e := by unfold colZ; rw [eventAt_evIdx]

theorem s6b_fst_le_of_lex_lt {a b : ℝ × ℝ} (h : toLex a < toLex b) : a.1 ≤ b.1 := by
  rw [Prod.Lex.lt_iff] at h
  rcases h with h | ⟨h, -⟩
  · exact h.le
  · exact h.le

theorem s6b_key_lt_of_idx_lt {j j' : ℕ} (hj' : j' < (events F).length) (hjj' : j < j') :
    toLex (colX F j, colZ F j) < toLex (colX F j', colZ F j') := by
  have h := List.pairwise_iff_getElem.mp (events_pairwise_lt F) j j' (lt_trans hjj' hj') hj' hjj'
  unfold colX colZ eventAt
  rw [List.getD_eq_getElem _ _ (lt_trans hjj' hj'), List.getD_eq_getElem _ _ hj']
  exact h

theorem s6b_idx_lt_of_key_lt (e e' : Event F) (h : toLex (evX F e, evZ F e) < toLex (evX F e', evZ F e')) :
    evIdx F e < evIdx F e' := by
  by_contra hle
  push Not at hle
  rcases eq_or_lt_of_le hle with heq | hlt
  · have hee : e = e' := by rw [← eventAt_evIdx F e, ← eventAt_evIdx F e', heq]
    subst hee
    exact lt_irrefl _ h
  · have h2 := s6b_key_lt_of_idx_lt F (evIdx_lt_length F e) hlt
    rw [s6b_colX_evIdx, s6b_colZ_evIdx, s6b_colX_evIdx, s6b_colZ_evIdx] at h2
    exact lt_asymm h h2

/-- no event lies strictly between two consecutive columns in the `(x, z)` order -/

theorem s6b_no_event_between {k : ℕ} (hk : k + 1 < (events F).length) (e : Event F)
    (h₀ : toLex (colX F k, colZ F k) < toLex (evX F e, evZ F e))
    (h₁ : toLex (evX F e, evZ F e) < toLex (colX F (k + 1), colZ F (k + 1))) : False := by
  have hk' : k < (events F).length := by omega
  have h0 := s6b_idx_lt_of_key_lt F (eventAt F k) e h₀
  have h1 := s6b_idx_lt_of_key_lt F e (eventAt F (k + 1)) h₁
  rw [evIdx_eventAt F hk'] at h0
  rw [evIdx_eventAt F hk] at h1
  omega

/-- the top event of an x-value: when the next column has a larger `x` (or there is none), no event at this `x`
is higher -/

theorem s6b_top {k : ℕ} (hk : k < (events F).length)
    (hnext : k + 1 = (events F).length ∨ colX F k < colX F (k + 1)) (e : Event F) (hx : evX F e = colX F k) :
    evZ F e ≤ colZ F k := by
  by_contra hlt
  push Not at hlt
  have hkey : toLex (colX F k, colZ F k) < toLex (evX F e, evZ F e) := by
    rw [Prod.Lex.lt_iff]; right; exact ⟨hx.symm, hlt⟩
  have hidx := s6b_idx_lt_of_key_lt F (eventAt F k) e hkey
  rw [evIdx_eventAt F hk] at hidx
  have hlen := evIdx_lt_length F e
  rcases hnext with hn | hn
  · omega
  · rcases eq_or_lt_of_le (show k + 1 ≤ evIdx F e by omega) with heq | hlt'
    · have := s6b_colX_evIdx F e
      rw [← heq] at this
      linarith
    · have h2 := s6b_fst_le_of_lex_lt (s6b_key_lt_of_idx_lt F hlen hlt')
      simp only at h2
      rw [s6b_colX_evIdx] at h2
      linarith

/-- the bottom event of an x-value: when the previous column has a smaller `x` (or there is none), no event at
this `x` is lower -/

theorem s6b_bot {k : ℕ} (hk : k < (events F).length) (hprev : k = 0 ∨ colX F (k - 1) < colX F k) (e : Event F)
    (hx : evX F e = colX F k) : colZ F k ≤ evZ F e := by
  by_contra hlt
  push Not at hlt
  have hkey : toLex (evX F e, evZ F e) < toLex (colX F k, colZ F k) := by
    rw [Prod.Lex.lt_iff]; right; exact ⟨hx, hlt⟩
  have hidx := s6b_idx_lt_of_key_lt F e (eventAt F k) hkey
  rw [evIdx_eventAt F hk] at hidx
  rcases hprev with hn | hn
  · omega
  · rcases eq_or_lt_of_le (show evIdx F e ≤ k - 1 by omega) with heq | hlt'
    · have := s6b_colX_evIdx F e
      rw [heq] at this
      linarith
    · have h2 := s6b_fst_le_of_lex_lt (s6b_key_lt_of_idx_lt F (show k - 1 < (events F).length by omega) hlt')
      simp only at h2
      rw [s6b_colX_evIdx] at h2
      linarith

/-- a fibre point whose height is not the height of any event at its x-value is regular -/

theorem s6b_regular_of_no_event {x : ℝ} {p : Param F.c} (hp : p ∈ totalFibre F x)
    (hno : ∀ e : Event F, evX F e = x → evZ F e ≠ ht F p) : ¬ F.IsCusp p ∧ ∀ q, ¬ F.IsDouble p q := by
  by_contra h
  have hs : F.IsCusp p ∨ ∃ q, F.IsDouble p q := by
    by_cases hc : F.IsCusp p
    · exact Or.inl hc
    · right
      by_contra hq
      push Not at hq
      exact h ⟨hc, hq⟩
  obtain ⟨e, hex, hez⟩ := exists_event_of_singular F hp hs
  exact hno e hex hez

theorem s6b_beforeBits_regular {p : Param F.c} (hc : ¬ F.IsCusp p) : beforeBits F p = [dirBit F p] := by
  unfold beforeBits
  rw [if_neg (fun h => hc h.1), if_neg (fun h => hc h.1)]

theorem s6b_afterBits_regular {p : Param F.c} (hc : ¬ F.IsCusp p) : afterBits F p = [dirBit F p] := by
  unfold afterBits
  rw [if_neg (fun h => hc h.1), if_neg (fun h => hc h.1)]

theorem s6b_ht_le_of_beforeLE {p q : Param F.c} (h : beforeLE F p q = true) : ht F q ≤ ht F p := by
  unfold beforeLE at h
  rw [decide_eq_true_iff, Prod.Lex.le_iff] at h
  rcases h with h | ⟨h, -⟩ <;> simp only [ofLex_toLex] at h <;> linarith

theorem s6b_ht_le_of_afterLE {p q : Param F.c} (h : afterLE F p q = true) : ht F q ≤ ht F p := by
  unfold afterLE at h
  rw [decide_eq_true_iff, Prod.Lex.le_iff] at h
  rcases h with h | ⟨h, -⟩ <;> simp only [ofLex_toLex] at h <;> linarith

theorem s6b_fibreListBefore_antitone (x : ℝ) : (fibreListBefore F x).Pairwise (fun p q => ht F q ≤ ht F p) :=
  (fibreListBefore_pairwise F x).imp (s6b_ht_le_of_beforeLE F)

theorem s6b_fibreListAfter_antitone (x : ℝ) : (fibreListAfter F x).Pairwise (fun p q => ht F q ≤ ht F p) :=
  (fibreListAfter_pairwise F x).imp (s6b_ht_le_of_afterLE F)

/-- two fibre points over one `x` at the same height coincide when one of them is not a double point -/

theorem s6b_ht_inj_of_regular {x : ℝ} {p q : Param F.c} (hp : p ∈ totalFibre F x) (hq : q ∈ totalFibre F x)
    (hreg : ∀ q', ¬ F.IsDouble p q') (h : ht F p = ht F q) : p = q := by
  by_contra hne
  exact hreg q ⟨fun hs => hne (SameParam.eq_of_mem_Ico hp.1 hq.1 hs), Prod.ext (hp.2.trans hq.2.symm) h⟩

theorem s6b_pairwise_lt_of_regular (x : ℝ) (L : List (Param F.c)) (hnd : L.Nodup)
    (hmemL : ∀ p ∈ L, p ∈ totalFibre F x) (hL : L.Pairwise (fun p q => ht F q ≤ ht F p))
    (hreg : ∀ p ∈ L, ∀ q, ¬ F.IsDouble p q) : L.Pairwise (fun p q => ht F q < ht F p) := by
  have hnd' : L.Pairwise (fun p q => p ≠ q) := hnd
  refine (hnd'.and hL).imp_of_mem ?_
  intro p q hp hq ⟨hne, hle⟩
  exact lt_of_le_of_ne hle (fun heq => hne (s6b_ht_inj_of_regular F (hmemL p hp) (hmemL q hq) (hreg p hp) heq.symm))

/-- over one `x`, the "before" and "after" orders agree on a set of regular points, and so do their entries -/

theorem s6b_filter_eq_of_regular (x : ℝ) (P : Param F.c → Bool)
    (hreg : ∀ p ∈ totalFibre F x, P p = true → ∀ q, ¬ F.IsDouble p q) :
    (fibreListBefore F x).filter P = (fibreListAfter F x).filter P := by
  apply s6b_sorted_eq (ht F)
  · refine s6b_pairwise_lt_of_regular F x _ ((fibreListBefore_nodup F x).filter P) ?_
      ((s6b_fibreListBefore_antitone F x).filter P) ?_
    · intro p hp
      rw [List.mem_filter, mem_fibreListBefore] at hp
      exact hp.1
    · intro p hp
      rw [List.mem_filter, mem_fibreListBefore] at hp
      exact hreg p hp.1 hp.2
  · refine s6b_pairwise_lt_of_regular F x _ ((fibreListAfter_nodup F x).filter P) ?_
      ((s6b_fibreListAfter_antitone F x).filter P) ?_
    · intro p hp
      rw [List.mem_filter, mem_fibreListAfter] at hp
      exact hp.1
    · intro p hp
      rw [List.mem_filter, mem_fibreListAfter] at hp
      exact hreg p hp.1 hp.2
  · intro p
    rw [List.mem_filter, List.mem_filter, mem_fibreListBefore, mem_fibreListAfter]

theorem s6b_entries_regular_eq (x : ℝ) (P : Param F.c → Bool)
    (hreg : ∀ p ∈ totalFibre F x, P p = true → ¬ F.IsCusp p ∧ ∀ q, ¬ F.IsDouble p q) :
    entriesOf F (beforeBits F) ((fibreListBefore F x).filter P) =
      entriesOf F (afterBits F) ((fibreListAfter F x).filter P) := by
  rw [s6b_filter_eq_of_regular F x P (fun p hp hP => (hreg p hp hP).2)]
  apply s6b_entriesOf_congr
  intro p hp
  rw [List.mem_filter, mem_fibreListAfter] at hp
  rw [s6b_beforeBits_regular F (hreg p hp.1 hp.2).1, s6b_afterBits_regular F (hreg p hp.1 hp.2).1]

/-! #### Stage 3: the entry structure of a column: `A ++ E_b ++ B` before its event, `A ++ E_a ++ B` after it -/

/-- the entry list of column `k` (the hybrid cut before its event) -/

def s6b_entries (k : ℕ) : List (Param F.c × ℕ) := hybridEntries F (colX F k) (colZ F k)

/-- the entry list just after the event of column `k` -/

def s6b_entriesAfter (k : ℕ) : List (Param F.c × ℕ) :=
  hybridEntriesP F (colX F k) (fun p => decide (colZ F k < ht F p))

/-- the entries strictly above the event of column `k` -/

def s6b_A (k : ℕ) : List (Param F.c × ℕ) :=
  entriesOf F (beforeBits F) ((fibreListBefore F (colX F k)).filter (fun p => decide (colZ F k < ht F p)))

/-- the entries of the event's point(s) before the event -/

def s6b_Eb (k : ℕ) : List (Param F.c × ℕ) :=
  entriesOf F (beforeBits F) ((fibreListBefore F (colX F k)).filter (fun p => decide (ht F p = colZ F k)))

/-- the entries of the event's point(s) after the event -/

def s6b_Ea (k : ℕ) : List (Param F.c × ℕ) :=
  entriesOf F (afterBits F) ((fibreListAfter F (colX F k)).filter (fun p => decide (ht F p = colZ F k)))

/-- the entries strictly below the event of column `k` -/

def s6b_B (k : ℕ) : List (Param F.c × ℕ) :=
  entriesOf F (afterBits F) ((fibreListAfter F (colX F k)).filter (fun p => decide (ht F p < colZ F k)))

theorem s6b_not_decide_le (z : ℝ) (p : Param F.c) : (!decide (z ≤ ht F p)) = decide (ht F p < z) := by
  by_cases h : z ≤ ht F p
  · simp [h, not_lt.mpr h]
  · simp [h, not_le.mp h]

theorem s6b_not_decide_lt (z : ℝ) (p : Param F.c) : (!decide (z < ht F p)) = decide (ht F p ≤ z) := by
  by_cases h : z < ht F p
  · simp [h, not_le.mpr h]
  · simp [h, not_lt.mp h]

/-- `filter (z ≤ ht) = filter (z < ht) ++ filter (ht = z)` on an antitone list -/

theorem s6b_split_le (z : ℝ) (L : List (Param F.c)) (hL : L.Pairwise (fun p q => ht F q ≤ ht F p)) :
    L.filter (fun p => decide (z ≤ ht F p)) =
      L.filter (fun p => decide (z < ht F p)) ++ L.filter (fun p => decide (ht F p = z)) := by
  apply s6b_filter_split (ht F) _ _ _ _ _ L hL
  · intro p
    rw [Bool.eq_iff_iff]
    simp only [decide_eq_true_eq, Bool.or_eq_true]
    exact ⟨fun h => (lt_or_eq_of_le h).imp id Eq.symm, fun h => h.elim le_of_lt (fun h => h.symm.le)⟩
  · intro p q hp hq
    simp only [decide_eq_true_eq] at hp hq
    rw [hp]; exact hq

/-- `filter (ht ≤ z) = filter (ht = z) ++ filter (ht < z)` on an antitone list -/

theorem s6b_split_ge (z : ℝ) (L : List (Param F.c)) (hL : L.Pairwise (fun p q => ht F q ≤ ht F p)) :
    L.filter (fun p => decide (ht F p ≤ z)) =
      L.filter (fun p => decide (ht F p = z)) ++ L.filter (fun p => decide (ht F p < z)) := by
  apply s6b_filter_split (ht F) _ _ _ _ _ L hL
  · intro p
    rw [Bool.eq_iff_iff]
    simp only [decide_eq_true_eq, Bool.or_eq_true]
    exact ⟨fun h => (lt_or_eq_of_le h).symm, fun h => h.elim (fun h => h.le) le_of_lt⟩
  · intro p q hp hq
    simp only [decide_eq_true_eq] at hp hq
    rw [hq]; exact hp

/-- `L = filter (z < ht) ++ filter (ht ≤ z)` on an antitone list -/

theorem s6b_split_all_lt (z : ℝ) (L : List (Param F.c)) (hL : L.Pairwise (fun p q => ht F q ≤ ht F p)) :
    L = L.filter (fun p => decide (z < ht F p)) ++ L.filter (fun p => decide (ht F p ≤ z)) := by
  have := s6b_filter_split (ht F) (fun _ => true) (fun p => decide (z < ht F p)) (fun p => decide (ht F p ≤ z))
    (fun p => by by_cases h : z < ht F p <;> simp [h, not_lt.mp]) (fun p q hp hq => by
      simp only [decide_eq_true_eq] at hp hq; linarith) L hL
  rwa [List.filter_true] at this

/-- `L = filter (z ≤ ht) ++ filter (ht < z)` on an antitone list -/

theorem s6b_split_all_le (z : ℝ) (L : List (Param F.c)) (hL : L.Pairwise (fun p q => ht F q ≤ ht F p)) :
    L = L.filter (fun p => decide (z ≤ ht F p)) ++ L.filter (fun p => decide (ht F p < z)) := by
  have := s6b_filter_split (ht F) (fun _ => true) (fun p => decide (z ≤ ht F p)) (fun p => decide (ht F p < z))
    (fun p => by by_cases h : z ≤ ht F p <;> simp [h, not_le.mp]) (fun p q hp hq => by
      simp only [decide_eq_true_eq] at hp hq; linarith) L hL
  rwa [List.filter_true] at this

/-- `filter (z₀ < ht) = filter (z₁ ≤ ht) ++ filter (z₀ < ht < z₁)` on an antitone list -/

theorem s6b_split_between_upper {z₀ z₁ : ℝ} (h : z₀ < z₁) (L : List (Param F.c))
    (hL : L.Pairwise (fun p q => ht F q ≤ ht F p)) :
    L.filter (fun p => decide (z₀ < ht F p)) =
      L.filter (fun p => decide (z₁ ≤ ht F p)) ++ L.filter (fun p => decide (z₀ < ht F p ∧ ht F p < z₁)) := by
  apply s6b_filter_split (ht F) _ _ _ _ _ L hL
  · intro p
    rw [Bool.eq_iff_iff]
    simp only [decide_eq_true_eq, Bool.or_eq_true]
    constructor
    · intro hp
      by_cases h1 : z₁ ≤ ht F p
      · exact Or.inl h1
      · exact Or.inr ⟨hp, not_le.mp h1⟩
    · rintro (h1 | ⟨h1, -⟩)
      · linarith
      · exact h1
  · intro p q hp hq
    simp only [decide_eq_true_eq] at hp hq
    linarith [hp.2]

/-- `filter (ht < z₁) = filter (z₀ < ht < z₁) ++ filter (ht ≤ z₀)` on an antitone list -/

theorem s6b_split_between_lower {z₀ z₁ : ℝ} (h : z₀ < z₁) (L : List (Param F.c))
    (hL : L.Pairwise (fun p q => ht F q ≤ ht F p)) :
    L.filter (fun p => decide (ht F p < z₁)) =
      L.filter (fun p => decide (z₀ < ht F p ∧ ht F p < z₁)) ++ L.filter (fun p => decide (ht F p ≤ z₀)) := by
  apply s6b_filter_split (ht F) _ _ _ _ _ L hL
  · intro p
    rw [Bool.eq_iff_iff]
    simp only [decide_eq_true_eq, Bool.or_eq_true]
    constructor
    · intro hp
      by_cases h1 : ht F p ≤ z₀
      · exact Or.inr h1
      · exact Or.inl ⟨not_le.mp h1, hp⟩
    · rintro (⟨-, h1⟩ | h1)
      · exact h1
      · linarith
  · intro p q hp hq
    simp only [decide_eq_true_eq] at hp hq
    linarith [hq.1]

/-- T1: the entries of a column are `A ++ E_b ++ B` -/

theorem s6b_entries_eq (k : ℕ) : s6b_entries F k = s6b_A F k ++ s6b_Eb F k ++ s6b_B F k := by
  unfold s6b_entries hybridEntries hybridEntriesP s6b_A s6b_Eb s6b_B
  rw [s6b_split_le F _ _ (s6b_fibreListBefore_antitone F _), s6b_entriesOf_append,
    List.filter_congr (fun p _ => s6b_not_decide_le F (colZ F k) p)]

/-- T2: the entries just after the event of a column are `A ++ E_a ++ B` -/

theorem s6b_entriesAfter_eq (k : ℕ) : s6b_entriesAfter F k = s6b_A F k ++ s6b_Ea F k ++ s6b_B F k := by
  unfold s6b_entriesAfter hybridEntriesP s6b_A s6b_Ea s6b_B
  rw [List.filter_congr (fun p _ => s6b_not_decide_lt F (colZ F k) p),
    s6b_split_ge F _ _ (s6b_fibreListAfter_antitone F _), s6b_entriesOf_append, List.append_assoc]

theorem s6b_idx_letterOf (e : Event F) : (letterOf F e).idx = posOf F e := by
  cases e with
  | inl c => simp only [letterOf]; split_ifs <;> rfl
  | inr q => rfl

/-- T3: the letter's index is one more than the number of entries above its event -/

theorem s6b_length_A {k : ℕ} (hk : k < (events F).length) : (s6b_A F k).length + 1 = (letterAt (word F) k).idx := by
  rw [letterAt_word F hk, s6b_idx_letterOf]
  unfold s6b_A
  rw [s6b_length_entriesOf]
  rfl

/-! the points at the event's height -/

theorem s6b_mem_totalFibre_iff' (x : ℝ) (p : Param F.c) :
    p ∈ totalFibre F x ↔ p.2 ∈ Set.Ico (0 : ℝ) 1 ∧ (F.eval p).1 = x := Iff.rfl

theorem s6b_mem_midB_iff (k : ℕ) (p : Param F.c) :
    p ∈ (fibreListBefore F (colX F k)).filter (fun p => decide (ht F p = colZ F k)) ↔
      p.2 ∈ Set.Ico (0 : ℝ) 1 ∧ F.eval p = F.eval (evPt F (eventAt F k)) := by
  rw [List.mem_filter, mem_fibreListBefore, s6b_mem_totalFibre_iff', decide_eq_true_iff, Prod.ext_iff]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h1, h2, h3⟩
  · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h1, h2⟩, h3⟩

theorem s6b_mem_midA_iff (k : ℕ) (p : Param F.c) :
    p ∈ (fibreListAfter F (colX F k)).filter (fun p => decide (ht F p = colZ F k)) ↔
      p.2 ∈ Set.Ico (0 : ℝ) 1 ∧ F.eval p = F.eval (evPt F (eventAt F k)) := by
  rw [List.mem_filter, mem_fibreListAfter, s6b_mem_totalFibre_iff', decide_eq_true_iff, Prod.ext_iff]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h1, h2, h3⟩
  · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h1, h2⟩, h3⟩

/-- at a cusp event the only point at the event's height is the cusp (`cusp_alone`) -/

theorem s6b_mid_cusp {k : ℕ} {c : F.Cusp} (he : eventAt F k = Sum.inl c) :
    (fibreListBefore F (colX F k)).filter (fun p => decide (ht F p = colZ F k)) = [c.1] ∧
    (fibreListAfter F (colX F k)).filter (fun p => decide (ht F p = colZ F k)) = [c.1] := by
  have key : ∀ b : Param F.c, b.2 ∈ Set.Ico (0 : ℝ) 1 → F.eval b = F.eval c.1 → b = c.1 := by
    intro b hb heq
    by_contra hne
    have hns : ¬ SameParam c.1 b := fun hs => hne (SameParam.eq_of_mem_Ico c.mem_Ico hb hs).symm
    exact F.cusp_alone c.1 b hns c.isCusp heq.symm
  constructor
  · apply s6b_eq_singleton_of_nodup ((fibreListBefore_nodup F _).filter _)
    · rw [s6b_mem_midB_iff, he]; exact ⟨c.mem_Ico, rfl⟩
    · intro b hb
      rw [s6b_mem_midB_iff, he] at hb
      exact key b hb.1 hb.2
  · apply s6b_eq_singleton_of_nodup ((fibreListAfter_nodup F _).filter _)
    · rw [s6b_mem_midA_iff, he]; exact ⟨c.mem_Ico, rfl⟩
    · intro b hb
      rw [s6b_mem_midA_iff, he] at hb
      exact key b hb.1 hb.2

/-- at a crossing event the points at the event's height are the over and the under branch, over first in the
"before" order and under first in the "after" order (`no_triple`) -/

theorem s6b_mid_cross {k : ℕ} {q : Cross F} (he : eventAt F k = Sum.inr q) :
    (fibreListBefore F (colX F k)).filter (fun p => decide (ht F p = colZ F k)) = [q.1.1, q.1.2] ∧
    (fibreListAfter F (colX F k)).filter (fun p => decide (ht F p = colZ F k)) = [q.1.2, q.1.1] := by
  obtain ⟨⟨ho, hu, hne, heval⟩, hslope⟩ := F.mem_crossingPairs'.mp q.2
  have hht : ht F q.1.2 = ht F q.1.1 := by unfold ht; rw [heval]
  have hmem : ∀ p : Param F.c, p.2 ∈ Set.Ico (0 : ℝ) 1 ∧ F.eval p = F.eval q.1.1 ↔ p = q.1.1 ∨ p = q.1.2 := by
    intro p
    constructor
    · rintro ⟨hp, hpe⟩
      by_contra hpq
      push Not at hpq
      exact F.no_triple p q.1.1 q.1.2 (fun hs => hpq.1 (SameParam.eq_of_mem_Ico hp ho hs))
        (fun hs => hne (SameParam.eq_of_mem_Ico ho hu hs)) (fun hs => hpq.2 (SameParam.eq_of_mem_Ico hp hu hs))
        hpe heval
    · rintro (rfl | rfl)
      · exact ⟨ho, rfl⟩
      · exact ⟨hu, heval.symm⟩
  constructor
  · apply s6b_eq_pair_of_nodup_sorted (fun p q => beforeLE F p q = true) ((fibreListBefore_nodup F _).filter _)
    · intro p; rw [s6b_mem_midB_iff, he]; exact hmem p
    · exact hne
    · exact (fibreListBefore_pairwise F _).filter _
    · intro h
      unfold beforeLE at h
      rw [decide_eq_true_iff, Prod.Lex.le_iff] at h
      simp only [ofLex_toLex] at h
      rcases h with h | ⟨-, h⟩
      · linarith
      · linarith
  · apply s6b_eq_pair_of_nodup_sorted (fun p q => afterLE F p q = true) ((fibreListAfter_nodup F _).filter _)
    · intro p; rw [s6b_mem_midA_iff, he]; exact (hmem p).trans or_comm
    · exact hne.symm
    · exact (fibreListAfter_pairwise F _).filter _
    · intro h
      unfold afterLE at h
      rw [decide_eq_true_iff, Prod.Lex.le_iff] at h
      simp only [ofLex_toLex] at h
      rcases h with h | ⟨-, h⟩
      · linarith
      · linarith

theorem s6b_length_afterBits_left {c : F.Cusp} (hl : F.IsLeftCusp c.1) : (afterBits F c.1).length = 2 := by
  unfold afterBits
  rw [if_neg (fun hr => left_right_absurd F hl hr), if_pos hl]
  split_ifs <;> rfl

theorem s6b_length_beforeBits_right {c : F.Cusp} (hr : F.IsRightCusp c.1) : (beforeBits F c.1).length = 2 := by
  unfold beforeBits
  rw [if_neg (fun hl => left_right_absurd F hl hr), if_pos hr]
  split_ifs <;> rfl

/-- the event entries at a left cusp -/

theorem s6b_Eb_Ea_left {k : ℕ} {c : F.Cusp} (he : eventAt F k = Sum.inl c) (hl : F.IsLeftCusp c.1) :
    s6b_Eb F k = [] ∧ s6b_Ea F k = [(c.1, 0), (c.1, 1)] := by
  obtain ⟨h1, h2⟩ := s6b_mid_cusp F he
  unfold s6b_Eb s6b_Ea
  rw [h1, h2, s6b_entriesOf_singleton, s6b_entriesOf_singleton, s6b_length_afterBits_left F hl]
  unfold beforeBits
  rw [if_pos hl]
  exact ⟨rfl, rfl⟩

/-- the event entries at a right cusp -/

theorem s6b_Eb_Ea_right {k : ℕ} {c : F.Cusp} (he : eventAt F k = Sum.inl c) (hl : ¬ F.IsLeftCusp c.1) :
    s6b_Eb F k = [(c.1, 0), (c.1, 1)] ∧ s6b_Ea F k = [] := by
  have hr : F.IsRightCusp c.1 := (F.isLeftCusp_or_isRightCusp c.isCusp).resolve_left hl
  obtain ⟨h1, h2⟩ := s6b_mid_cusp F he
  unfold s6b_Eb s6b_Ea
  rw [h1, h2, s6b_entriesOf_singleton, s6b_entriesOf_singleton, s6b_length_beforeBits_right F hr]
  unfold afterBits
  rw [if_pos hr]
  exact ⟨rfl, rfl⟩

/-- the event entries at a crossing -/

theorem s6b_Eb_Ea_cross {k : ℕ} {q : Cross F} (he : eventAt F k = Sum.inr q) :
    s6b_Eb F k = [(q.1.1, 0), (q.1.2, 0)] ∧ s6b_Ea F k = [(q.1.2, 0), (q.1.1, 0)] := by
  have hd := F.isOverUnder_of_mem_crossingPairs q.2
  have hno : ¬ F.IsCusp q.1.1 := F.not_isCusp_of_isDouble hd.1
  have hnu : ¬ F.IsCusp q.1.2 := F.not_isCusp_of_isDouble hd.1.symm
  obtain ⟨h1, h2⟩ := s6b_mid_cross F he
  unfold s6b_Eb s6b_Ea
  rw [h1, h2]
  constructor
  · rw [s6b_entriesOf_eq_map]
    · rfl
    · intro p hp
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · rw [s6b_beforeBits_regular F hno]; rfl
      · rw [s6b_beforeBits_regular F hnu]; rfl
  · rw [s6b_entriesOf_eq_map]
    · rfl
    · intro p hp
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · rw [s6b_afterBits_regular F hnu]; rfl
      · rw [s6b_afterBits_regular F hno]; rfl

/-! the letter of a column determines the kind of its event -/

theorem s6b_event_of_letter_l {k m : ℕ} {d : Bool} (hk : k < (events F).length) (h : letterAt (word F) k = .l m d) :
    ∃ c : F.Cusp, eventAt F k = Sum.inl c ∧ F.IsLeftCusp c.1 ∧ m = posOf F (Sum.inl c) := by
  rw [letterAt_word F hk] at h
  rcases he : eventAt F k with c | q
  · rw [he] at h
    by_cases hl : F.IsLeftCusp c.1
    · simp only [letterOf, if_pos hl] at h
      exact ⟨c, rfl, hl, (Letter.l.inj h).1.symm⟩
    · simp only [letterOf, if_neg hl] at h
      cases h
  · rw [he] at h
    simp [letterOf] at h

theorem s6b_event_of_letter_r {k m : ℕ} (hk : k < (events F).length) (h : letterAt (word F) k = .r m) :
    ∃ c : F.Cusp, eventAt F k = Sum.inl c ∧ ¬ F.IsLeftCusp c.1 ∧ m = posOf F (Sum.inl c) := by
  rw [letterAt_word F hk] at h
  rcases he : eventAt F k with c | q
  · rw [he] at h
    by_cases hl : F.IsLeftCusp c.1
    · simp only [letterOf, if_pos hl] at h
      cases h
    · simp only [letterOf, if_neg hl] at h
      exact ⟨c, rfl, hl, (Letter.r.inj h).symm⟩
  · rw [he] at h
    simp [letterOf] at h

theorem s6b_event_of_letter_σ {k m : ℕ} (hk : k < (events F).length) (h : letterAt (word F) k = .σ m) :
    ∃ q : Cross F, eventAt F k = Sum.inr q ∧ m = posOf F (Sum.inr q) := by
  rw [letterAt_word F hk] at h
  rcases he : eventAt F k with c | q
  · rw [he] at h
    by_cases hl : F.IsLeftCusp c.1
    · simp only [letterOf, if_pos hl] at h
      cases h
    · simp only [letterOf, if_neg hl] at h
      cases h
  · rw [he] at h
    exact ⟨q, rfl, (Letter.σ.inj h).symm⟩

/-! #### Stage 4: the transition from a column to the next one (tie: list surgery; gap: the S1 limits) -/

/-- after the top event of an x-value the entries are `entriesAfter` -/

theorem s6b_entriesAfter_top {k : ℕ} (hk : k < (events F).length)
    (hnext : k + 1 = (events F).length ∨ colX F k < colX F (k + 1)) :
    s6b_entriesAfter F k = entriesAfter F (colX F k) := by
  unfold s6b_entriesAfter hybridEntriesP entriesAfter
  rw [List.filter_congr (fun p _ => s6b_not_decide_lt F (colZ F k) p)]
  conv_rhs => rw [s6b_split_all_lt F (colZ F k) _ (s6b_fibreListAfter_antitone F _)]
  rw [s6b_entriesOf_append]
  congr 1
  apply s6b_entries_regular_eq
  intro p hp hP
  rw [decide_eq_true_iff] at hP
  apply s6b_regular_of_no_event F hp
  intro e hex hez
  have := s6b_top F hk hnext e hex
  linarith

/-- before the bottom event of an x-value the entries are `entriesBefore` -/

theorem s6b_entries_bot {k : ℕ} (hk : k < (events F).length) (hprev : k = 0 ∨ colX F (k - 1) < colX F k) :
    s6b_entries F k = entriesBefore F (colX F k) := by
  unfold s6b_entries hybridEntries hybridEntriesP entriesBefore
  rw [List.filter_congr (fun p _ => s6b_not_decide_le F (colZ F k) p)]
  conv_rhs => rw [s6b_split_all_le F (colZ F k) _ (s6b_fibreListBefore_antitone F _)]
  rw [s6b_entriesOf_append]
  congr 1
  symm
  apply s6b_entries_regular_eq
  intro p hp hP
  rw [decide_eq_true_iff] at hP
  apply s6b_regular_of_no_event F hp
  intro e hex hez
  have := s6b_bot F hk hprev e hex
  linarith

theorem s6b_colZ_lt_of_tie {k : ℕ} (hk : k + 1 < (events F).length) (hx : colX F k = colX F (k + 1)) :
    colZ F k < colZ F (k + 1) := by
  have h := s6b_key_lt_of_idx_lt F hk (Nat.lt_succ_self k)
  rw [Prod.Lex.lt_iff] at h
  simp only [ofLex_toLex] at h
  rcases h with h | ⟨-, h⟩
  · rw [hx] at h; exact absurd h (lt_irrefl _)
  · exact h

/-- two consecutive events of one x-value: the entries after the lower one are the entries before the upper one -/

theorem s6b_entries_tie {k : ℕ} (hk : k + 1 < (events F).length) (hx : colX F k = colX F (k + 1)) :
    s6b_entries F (k + 1) = s6b_entriesAfter F k := by
  have hz := s6b_colZ_lt_of_tie F hk hx
  unfold s6b_entries s6b_entriesAfter hybridEntries hybridEntriesP
  rw [← hx]
  rw [List.filter_congr (fun p _ => s6b_not_decide_le F (colZ F (k + 1)) p),
    List.filter_congr (fun p _ => s6b_not_decide_lt F (colZ F k) p),
    s6b_split_between_upper F hz _ (s6b_fibreListBefore_antitone F _),
    s6b_split_between_lower F hz _ (s6b_fibreListAfter_antitone F _),
    s6b_entriesOf_append, s6b_entriesOf_append, List.append_assoc]
  congr 2
  symm
  apply s6b_entries_regular_eq
  intro p hp hP
  rw [decide_eq_true_iff] at hP
  apply s6b_regular_of_no_event F hp
  intro e hex hez
  apply s6b_no_event_between F hk e
  · rw [Prod.Lex.lt_iff]; simp only [ofLex_toLex]; exact Or.inr ⟨hex.symm, by rw [hez]; exact hP.1⟩
  · rw [Prod.Lex.lt_iff]; simp only [ofLex_toLex]; exact Or.inr ⟨by rw [hex, hx], by rw [hez]; exact hP.2⟩

/-- the circle of a strand entry -/

def s6b_circOf (a : Param F.c × ℕ) : Fin F.c := a.1.1

theorem s6b_entriesAfter_eq_entriesBefore {x : ℝ} (hx : x ∉ singX F) : entriesAfter F x = entriesBefore F x := by
  rw [entriesBefore_eq_of_notMem_singX F hx]
  unfold entriesAfter
  rw [fibreListAfter_eq_fibreListBefore F hx]
  apply s6b_entriesOf_eq_map
  intro p hp
  rw [mem_fibreListBefore] at hp
  have hreg := regular_of_notMem_singX F (p := p) (by rw [hp.2]; exact hx)
  rw [s6b_afterBits_regular F hreg.1]; rfl

/-- continuations preserve the circles of an entry list -/

theorem s6b_map_circ_eq_of_cont (L L' : List (Param F.c × ℕ)) (hlen : L.length = L'.length)
    (hc : ∀ j < L'.length, Cont F ((L.getD j (dfltP F, 0)).1) (L'.getD j (dfltP F, 0))) :
    L.map (s6b_circOf F) = L'.map (s6b_circOf F) := by
  apply List.ext_getElem
  · simp [hlen]
  · intro j h1 h2
    simp only [List.getElem_map]
    rw [List.length_map] at h1 h2
    have := (hc j h2).1
    rw [List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ h2] at this
    exact this

/-- the circle list of the cut is locally constant at a non-singular `x` (the S1 limits) -/

theorem s6b_circ_eventually {x : ℝ} (hx : x ∉ singX F) :
    ∀ᶠ y in nhds x, (entriesBefore F y).map (s6b_circOf F) = (entriesBefore F x).map (s6b_circOf F) := by
  obtain ⟨η₁, hη₁, H₁⟩ := entriesBefore_left_limit F x
  obtain ⟨η₂, hη₂, H₂⟩ := entriesAfter_right_limit F x
  have hmem : Set.Ioo (x - η₁) (x + η₂) ∈ nhds x := Ioo_mem_nhds (by linarith) (by linarith)
  filter_upwards [hmem] with y hy
  rcases lt_trichotomy y x with hlt | rfl | hgt
  · obtain ⟨hlen, hc⟩ := H₁ y ⟨hy.1, hlt⟩
    exact s6b_map_circ_eq_of_cont F _ _ hlen hc
  · rfl
  · obtain ⟨hlen, hc⟩ := H₂ y ⟨hgt, hy.2⟩
    rw [← s6b_entriesAfter_eq_entriesBefore F hx]
    exact s6b_map_circ_eq_of_cont F _ _ hlen hc

/-- across a gap between singular x-values the circle list of the cut is constant: the circles just right of
`a` are the circles just left of `b` -/

theorem s6b_circ_gap {a b : ℝ} (hab : a < b) (hgap : ∀ x ∈ Set.Ioo a b, x ∉ singX F) :
    (entriesAfter F a).map (s6b_circOf F) = (entriesBefore F b).map (s6b_circOf F) := by
  let _ : TopologicalSpace (List (Fin F.c)) := ⊥
  have _ : DiscreteTopology (List (Fin F.c)) := ⟨rfl⟩
  have hcont : ContinuousOn (fun y => (entriesBefore F y).map (s6b_circOf F)) (Set.Ioo a b) := by
    intro y hy
    rw [ContinuousWithinAt, nhds_discrete, Filter.tendsto_pure]
    exact (s6b_circ_eventually F (hgap y hy)).filter_mono nhdsWithin_le_nhds
  obtain ⟨η₁, hη₁, H₁⟩ := entriesAfter_right_limit F a
  obtain ⟨η₂, hη₂, H₂⟩ := entriesBefore_left_limit F b
  obtain ⟨y₁, hy₁⟩ : ∃ y, y = a + min η₁ (b - a) / 2 := ⟨_, rfl⟩
  obtain ⟨y₂, hy₂⟩ : ∃ y, y = b - min η₂ (b - a) / 2 := ⟨_, rfl⟩
  have hm1 : 0 < min η₁ (b - a) := lt_min hη₁ (by linarith)
  have hm2 : 0 < min η₂ (b - a) := lt_min hη₂ (by linarith)
  have hm1a : min η₁ (b - a) ≤ η₁ := min_le_left _ _
  have hm1b : min η₁ (b - a) ≤ b - a := min_le_right _ _
  have hm2a : min η₂ (b - a) ≤ η₂ := min_le_left _ _
  have hm2b : min η₂ (b - a) ≤ b - a := min_le_right _ _
  have hy₁I : y₁ ∈ Set.Ioo a b := ⟨by linarith, by linarith⟩
  have hy₂I : y₂ ∈ Set.Ioo a b := ⟨by linarith, by linarith⟩
  have e1 : (entriesBefore F y₁).map (s6b_circOf F) = (entriesAfter F a).map (s6b_circOf F) := by
    obtain ⟨hlen, hc⟩ := H₁ y₁ ⟨by linarith, by linarith⟩
    exact s6b_map_circ_eq_of_cont F _ _ hlen hc
  have e2 : (entriesBefore F y₂).map (s6b_circOf F) = (entriesBefore F b).map (s6b_circOf F) := by
    obtain ⟨hlen, hc⟩ := H₂ y₂ ⟨by linarith, by linarith⟩
    exact s6b_map_circ_eq_of_cont F _ _ hlen hc
  rw [← e1, ← e2]
  exact isPreconnected_Ioo.constant hcont hy₁I hy₂I

/-- every singular x-value is the x-value of an event -/

theorem s6b_exists_event_of_mem_singX {x : ℝ} (hx : x ∈ singX F) : ∃ e : Event F, evX F e = x := by
  unfold singX at hx
  rw [Finset.mem_union, Finset.mem_image, Finset.mem_image] at hx
  rcases hx with ⟨p, hp, hpx⟩ | ⟨q, hq, hqx⟩
  · exact ⟨Sum.inl ⟨p, hp⟩, hpx⟩
  · rcases F.mem_crossingPairs_or_swap hq with h | h
    · exact ⟨Sum.inr ⟨q, h⟩, hqx⟩
    · refine ⟨Sum.inr ⟨q.swap, h⟩, ?_⟩
      show (F.eval q.2).1 = x
      rw [← (F.mem_doubleSet.mp hq).2.2.2]; exact hqx

/-- THE TRANSITION: the circles of the entries of column `k + 1` are the circles of the entries just after the
event of column `k` -/

theorem s6b_circ_trans {k : ℕ} (hk : k + 1 < (events F).length) :
    (s6b_entries F (k + 1)).map (s6b_circOf F) = (s6b_entriesAfter F k).map (s6b_circOf F) := by
  have hk' : k < (events F).length := by omega
  have hle : colX F k ≤ colX F (k + 1) := colX_mono F (Nat.lt_succ_self k) hk
  rcases eq_or_lt_of_le hle with hx | hx
  · rw [s6b_entries_tie F hk hx]
  · rw [s6b_entriesAfter_top F hk' (Or.inr hx), s6b_entries_bot F hk (Or.inr (by simpa using hx))]
    symm
    apply s6b_circ_gap F hx
    intro x hxI hsing
    obtain ⟨e, he⟩ := s6b_exists_event_of_mem_singX F hsing
    apply s6b_no_event_between F hk e
    · rw [Prod.Lex.lt_iff]; simp only [ofLex_toLex]; exact Or.inl (by rw [he]; exact hxI.1)
    · rw [Prod.Lex.lt_iff]; simp only [ofLex_toLex]; exact Or.inl (by rw [he]; exact hxI.2)

/-! #### Stage 5: the per-step invariance of the circle -/

/-- the circle at position `p` (1-based) of an entry list -/

def s6b_circAt (L : List (Param F.c × ℕ)) (p : ℕ) : Fin F.c := (L.getD (p - 1) (dfltP F, 0)).1.1

theorem s6b_circAt_eq_of_map_eq {L L' : List (Param F.c × ℕ)}
    (h : L.map (s6b_circOf F) = L'.map (s6b_circOf F)) (p : ℕ) : s6b_circAt F L p = s6b_circAt F L' p := by
  have h1 : s6b_circAt F L p = (L.map (s6b_circOf F)).getD (p - 1) (s6b_circOf F (dfltP F, 0)) := by
    rw [List.getD_map]; rfl
  have h2 : s6b_circAt F L' p = (L'.map (s6b_circOf F)).getD (p - 1) (s6b_circOf F (dfltP F, 0)) := by
    rw [List.getD_map]; rfl
  rw [h1, h2, h]

theorem s6b_getD_three (A E B : List (Param F.c × ℕ)) (n : ℕ) (d : Param F.c × ℕ) :
    (A ++ E ++ B).getD n d = if n < A.length then A.getD n d
      else if n < A.length + E.length then E.getD (n - A.length) d else B.getD (n - A.length - E.length) d := by
  rw [List.append_assoc]
  by_cases h1 : n < A.length
  · rw [List.getD_append _ _ _ _ h1, if_pos h1]
  · rw [List.getD_append_right _ _ _ _ (not_lt.mp h1), if_neg h1]
    by_cases h2 : n < A.length + E.length
    · rw [List.getD_append _ _ _ _ (by omega), if_pos h2]
    · rw [List.getD_append_right _ _ _ _ (by omega), if_neg h2]

theorem s6b_length_Eb_Ea {k : ℕ} (hk : k < (events F).length) :
    (s6b_Eb F k).length = (letterAt (word F) k).arity ∧ (s6b_Ea F k).length = (letterAt (word F) k).coarity := by
  rcases hℓ : letterAt (word F) k with ⟨m, d⟩ | ⟨m⟩ | ⟨m⟩
  · obtain ⟨c, he, hl, -⟩ := s6b_event_of_letter_l F hk hℓ
    obtain ⟨h1, h2⟩ := s6b_Eb_Ea_left F he hl
    rw [h1, h2]; exact ⟨rfl, rfl⟩
  · obtain ⟨c, he, hl, -⟩ := s6b_event_of_letter_r F hk hℓ
    obtain ⟨h1, h2⟩ := s6b_Eb_Ea_right F he hl
    rw [h1, h2]; exact ⟨rfl, rfl⟩
  · obtain ⟨q, he, -⟩ := s6b_event_of_letter_σ F hk hℓ
    obtain ⟨h1, h2⟩ := s6b_Eb_Ea_cross F he
    rw [h1, h2]; exact ⟨rfl, rfl⟩

/-- THE STEP: a strand passing a column rightward keeps its circle (`posR`) -/

theorem s6b_circAt_step {k : ℕ} (hk : k < (events F).length) {p q : ℕ} (hp : 1 ≤ p)
    (hq : (letterAt (word F) k).posR p = some q) :
    s6b_circAt F (s6b_entriesAfter F k) q = s6b_circAt F (s6b_entries F k) p := by
  have hA := s6b_length_A F hk
  obtain ⟨hEb, hEa⟩ := s6b_length_Eb_Ea F hk
  rw [s6b_entries_eq, s6b_entriesAfter_eq]
  unfold s6b_circAt
  rw [s6b_getD_three, s6b_getD_three]
  rcases lt_or_ge p (letterAt (word F) k).idx with hlt | hge
  · -- above the event: the position is kept
    rw [posR_of_lt hlt] at hq
    obtain rfl := Option.some.inj hq
    have h1 : p - 1 < (s6b_A F k).length := by omega
    rw [if_pos h1, if_pos h1]
  · rcases lt_or_ge p ((letterAt (word F) k).idx + (letterAt (word F) k).arity) with hmid | hge'
    · -- the event's own strands: only a crossing lets them pass, exchanging them
      rcases hℓ : letterAt (word F) k with ⟨m, d⟩ | ⟨m⟩ | ⟨m⟩
      · rw [hℓ] at hge hmid; simp only [idx, arity] at hge hmid; omega
      · rw [hℓ] at hq hge hmid; simp only [idx, arity] at hge hmid
        rw [posR_r, if_neg (not_lt.mpr hge), if_pos hmid] at hq
        cases hq
      · obtain ⟨q', he, -⟩ := s6b_event_of_letter_σ F hk hℓ
        obtain ⟨h1, h2⟩ := s6b_Eb_Ea_cross F he
        rw [hℓ] at hq hge hmid hA
        simp only [idx, arity] at hge hmid hA
        rw [posR_σ, if_neg (not_lt.mpr hge), if_pos hmid] at hq
        have hq' := Option.some.inj hq
        rw [h1, h2]
        simp only [List.length_cons, List.length_nil]
        rcases eq_or_lt_of_le hge with hpm | hlt'
        · -- p = m: the over strand descends to m + 1
          rw [if_pos hpm.symm] at hq'
          subst hq'
          split_ifs <;> try omega
          have e1 : m + 1 - 1 - (s6b_A F k).length = 1 := by omega
          have e2 : p - 1 - (s6b_A F k).length = 0 := by omega
          rw [e1, e2]; rfl
        · -- p = m + 1: the under strand ascends to m
          have hpm : p = m + 1 := by omega
          rw [if_neg (by omega)] at hq'
          subst hq'
          split_ifs <;> try omega
          have e1 : m - 1 - (s6b_A F k).length = 0 := by omega
          have e2 : p - 1 - (s6b_A F k).length = 1 := by omega
          rw [e1, e2]; rfl
    · -- below the event: the position shifts by the strand-count change
      rw [posR_of_ge hge'] at hq
      obtain rfl := Option.some.inj hq
      split_ifs <;> try omega
      have e : p + (letterAt (word F) k).coarity - (letterAt (word F) k).arity - 1 - (s6b_A F k).length -
          (s6b_Ea F k).length = p - 1 - (s6b_A F k).length - (s6b_Eb F k).length := by omega
      rw [e]

/-- the circle of a slot given as a pair: the cusp's circle at a cusp vertex, the entry's circle at a cut slot -/

def s6b_circPair (s : ℕ × ℕ) : Fin F.c :=
  if s.2 = 0 then (evPt F (eventAt F s.1)).1 else s6b_circAt F (s6b_entries F s.1) s.2

/-- THE CIRCLE OF A SLOT -/

def s6b_circ (u : Slot (word F)) : Fin F.c := s6b_circPair F u.1

theorem s6b_circPair_cusp (k : ℕ) : s6b_circPair F (k, 0) = (evPt F (eventAt F k)).1 := by simp [s6b_circPair]

theorem s6b_circPair_cut (k p : ℕ) (hp : p ≠ 0) : s6b_circPair F (k, p) = s6b_circAt F (s6b_entries F k) p := by
  simp [s6b_circPair, hp]

/-- at a right cusp the two arm positions before the event carry the cusp's circle -/

theorem s6b_circAt_arms_r {k m p : ℕ} (hk : k < (events F).length) (hℓ : letterAt (word F) k = .r m)
    (hpm : p = m ∨ p = m + 1) : s6b_circAt F (s6b_entries F k) p = (evPt F (eventAt F k)).1 := by
  obtain ⟨c, he, hl, -⟩ := s6b_event_of_letter_r F hk hℓ
  obtain ⟨hEb, -⟩ := s6b_Eb_Ea_right F he hl
  have hA := s6b_length_A F hk
  rw [hℓ] at hA; simp only [idx] at hA
  rw [he, s6b_entries_eq, hEb]
  unfold s6b_circAt
  rw [s6b_getD_three]
  simp only [List.length_cons, List.length_nil]
  rcases hpm with hpm | hpm
  · split_ifs <;> try omega
    have e : p - 1 - (s6b_A F k).length = 0 := by omega
    rw [e]; rfl
  · split_ifs <;> try omega
    have e : p - 1 - (s6b_A F k).length = 1 := by omega
    rw [e]; rfl

/-- at a left cusp the two arm positions after the event carry the cusp's circle -/

theorem s6b_circAt_arms_l {k m p : ℕ} {d : Bool} (hk : k < (events F).length) (hℓ : letterAt (word F) k = .l m d)
    (hpm : p = m ∨ p = m + 1) : s6b_circAt F (s6b_entriesAfter F k) p = (evPt F (eventAt F k)).1 := by
  obtain ⟨c, he, hl, -⟩ := s6b_event_of_letter_l F hk hℓ
  obtain ⟨-, hEa⟩ := s6b_Eb_Ea_left F he hl
  have hA := s6b_length_A F hk
  rw [hℓ] at hA; simp only [idx] at hA
  rw [he, s6b_entriesAfter_eq, hEa]
  unfold s6b_circAt
  rw [s6b_getD_three]
  simp only [List.length_cons, List.length_nil]
  rcases hpm with hpm | hpm
  · split_ifs <;> try omega
    have e : p - 1 - (s6b_A F k).length = 0 := by omega
    rw [e]; rfl
  · split_ifs <;> try omega
    have e : p - 1 - (s6b_A F k).length = 1 := by omega
    rw [e]; rfl

/-- `posL` is inverse to `posR` -/

theorem s6b_posR_of_posL {ℓ : Letter} {p q : ℕ} (h : ℓ.posL p = some q) : ℓ.posR q = some p := by
  unfold posL at h
  split_ifs at h with h1 h2
  · obtain rfl := Option.some.inj h
    exact posR_of_lt h1
  · cases ℓ with
    | l m d => cases h
    | r m => cases h
    | σ m =>
      simp only at h
      obtain rfl := Option.some.inj h
      simp only [idx, coarity] at h1 h2
      rw [posR_σ]
      by_cases hpm : p = m
      · subst hpm; simp
      · have hpm' : p = m + 1 := by omega
        subst hpm'; simp
  · obtain rfl := Option.some.inj h
    rw [posR_of_ge (by omega)]
    congr 1; omega

theorem s6b_cut_col_lt {k p : ℕ} (hp : 1 ≤ p) (hpk : p ≤ (cut (word F) k).length) : k < (events F).length := by
  have := (cutSlot_pos (word_closed F) hp hpk).2
  rwa [length_word] at this

/-- a slot with a positive position is a cut slot of a real column -/

theorem s6b_col_lt_of_slot {k p : ℕ} (h : IsSlot (word F) (k, p)) (hp : p ≠ 0) : k < (events F).length := by
  rcases h with ⟨h0, -, -⟩ | ⟨h1, h2, -⟩
  · exact absurd h0 hp
  · exact s6b_cut_col_lt F h1 h2

/-- THE INVARIANT: `next` preserves the circle of a slot -/

theorem s6b_circ_next (u : Slot (word F)) : s6b_circ F (next (word_closed F) u) = s6b_circ F u := by
  have hn := length_word F
  have hu := u.2
  have hnu := (next (word_closed F) u).2
  unfold s6b_circ
  rcases next_cases (word_closed F) u with
    ⟨k, p, q, hs, hp, -, hnx, hq, -, hposR, hk⟩ | ⟨k, p, m, hs, hp, -, hℓ, hpm, hnx, -, hk⟩ |
    ⟨k, p, q, hs, hp, -, hnx, hq, -, hposL, hk1, -⟩ | ⟨k, p, m, d, hs, hp, -, hℓ, hpm, hnx, -, -, hk1, -⟩ |
    ⟨k, m, d, hs, hℓ, hnx, -, -, hm, hk⟩ | ⟨k, m, hs, hℓ, hnx, -, hm, hk⟩
  · -- (1) rightward pass through the column
    rw [hnx] at hnu
    have hk1 : k + 1 < (events F).length := s6b_col_lt_of_slot F hnu (by omega)
    have hk' : k < (events F).length := by rwa [hn] at hk
    rw [hnx, hs, s6b_circPair_cut F _ _ (by omega), s6b_circPair_cut F _ _ (by omega),
      s6b_circAt_eq_of_map_eq F (s6b_circ_trans F hk1)]
    exact s6b_circAt_step F hk' hp hposR
  · -- (2) rightward into a right cusp vertex
    have hk' : k < (events F).length := by rwa [hn] at hk
    rw [hnx, hs, s6b_circPair_cusp, s6b_circPair_cut F _ _ (by omega)]
    exact (s6b_circAt_arms_r F hk' hℓ hpm).symm
  · -- (3) leftward pass through the column
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [hs] at hu
    have hk1 : k' + 1 < (events F).length := s6b_col_lt_of_slot F hu (by omega)
    have hk' : k' < (events F).length := by omega
    simp only [Nat.add_sub_cancel] at hnx hposL
    rw [hnx, hs, s6b_circPair_cut F _ _ (by omega), s6b_circPair_cut F _ _ (by omega),
      s6b_circAt_eq_of_map_eq F (s6b_circ_trans F hk1)]
    exact (s6b_circAt_step F hk' hq (s6b_posR_of_posL hposL)).symm
  · -- (4) leftward into a left cusp vertex
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [hs] at hu
    have hk1 : k' + 1 < (events F).length := s6b_col_lt_of_slot F hu (by omega)
    have hk' : k' < (events F).length := by omega
    simp only [Nat.add_sub_cancel] at hnx hℓ
    rw [hnx, hs, s6b_circPair_cusp, s6b_circPair_cut F _ _ (by omega),
      s6b_circAt_eq_of_map_eq F (s6b_circ_trans F hk1)]
    exact (s6b_circAt_arms_l F hk' hℓ hpm).symm
  · -- (5) out of a left cusp vertex along the new arms
    have hq : (if d = true then m else m + 1) = m ∨ (if d = true then m else m + 1) = m + 1 := by
      cases d <;> simp
    have hq0 : (if d = true then m else m + 1) ≠ 0 := by rcases hq with h | h <;> rw [h] <;> omega
    rw [hnx] at hnu
    have hk1 : k + 1 < (events F).length := s6b_col_lt_of_slot F hnu hq0
    have hk' : k < (events F).length := by omega
    rw [hnx, hs, s6b_circPair_cusp, s6b_circPair_cut F _ _ hq0, s6b_circAt_eq_of_map_eq F (s6b_circ_trans F hk1)]
    exact s6b_circAt_arms_l F hk' hℓ hq
  · -- (6) out of a right cusp vertex along the arriving arm
    have hq : (if bit (word F) k m = true then m + 1 else m) = m ∨
        (if bit (word F) k m = true then m + 1 else m) = m + 1 := by
      split_ifs <;> simp
    have hq0 : (if bit (word F) k m = true then m + 1 else m) ≠ 0 := by
      rcases hq with h | h <;> rw [h] <;> omega
    have hk' : k < (events F).length := by rwa [hn] at hk
    rw [hnx, hs, s6b_circPair_cusp, s6b_circPair_cut F _ _ hq0]
    exact s6b_circAt_arms_r F hk' hℓ hq

theorem s6b_circ_iterate (u : Slot (word F)) (j : ℕ) :
    s6b_circ F ((next (word_closed F))^[j] u) = s6b_circ F u := by
  induction j with
  | zero => rfl
  | succ j ih => rw [Function.iterate_succ_apply', s6b_circ_next, ih]

theorem s6b_circ_of_sameCycle {u v : Slot (word F)} (h : (nextPerm (word_closed F)).SameCycle u v) :
    s6b_circ F u = s6b_circ F v := by
  obtain ⟨j, hj⟩ := exists_iterate_of_sameCycle (word_closed F) h
  rw [← hj, s6b_circ_iterate]

theorem s6b_circ_cuspVertex (c : F.Cusp) : s6b_circ F (cuspVertex F c) = c.1.1 := by
  show s6b_circPair F (evIdx F (Sum.inl c), 0) = c.1.1
  rw [s6b_circPair_cusp, eventAt_evIdx]; rfl

/-- the slot of a strand of circle `i` has circle `i` -/

theorem s6b_circ_slotAt {i : Fin F.c} {t : ℝ} (h : xOf F i t ∉ singX F) : s6b_circ F (slotAt F i t h) = i := by
  have ht' : xOf F (someCuspOn F i).1.1 t ∉ singX F := by rwa [someCuspOn_fst]
  have e := s6b_slotAt_fst_eq F (someCuspOn_fst F i) ht' h
  have hc := s6b_sameCycle_cuspVertex F (someCuspOn F i) ht'
  rw [e] at hc
  rw [s6b_circ_of_sameCycle F hc, s6b_circ_cuspVertex, someCuspOn_fst]

end S6bHelpers

/-- LEAF (S6, the path and the cusps): the slot path along a parameter interval passes the cusp vertex of every
cusp of the circle inside it, and every cusp vertex it passes belongs to a cusp of the circle. -/
theorem path_cusps {i : Fin F.c} {t₀ t₁ : ℝ} (h01 : t₀ < t₁) (h₀ : xOf F i t₀ ∉ singX F)
    (h₁ : xOf F i t₁ ∉ singX F) :
    ∃ m, (next (word_closed F))^[m] (slotAt F i t₀ h₀) = slotAt F i t₁ h₁ ∧
      (∀ c : F.Cusp, c.1.1 = i → ∀ s ∈ Set.Ioo t₀ t₁, SameParam c.1 (i, s) →
        ∃ j < m, (next (word_closed F))^[j] (slotAt F i t₀ h₀) = cuspVertex F c) ∧
      ∀ j < m, ∀ c : F.Cusp, (next (word_closed F))^[j] (slotAt F i t₀ h₀) = cuspVertex F c → c.1.1 = i := by
  obtain ⟨m, hm, -, hcusp⟩ := s6b_path F h01 h₀ h₁
  refine ⟨m, hm, fun c _ s hs hcs => hcusp c s hs hcs, ?_⟩
  intro j _ c hjc
  have := s6b_circ_iterate F (slotAt F i t₀ h₀) j
  rw [hjc, s6b_circ_cuspVertex, s6b_circ_slotAt] at this
  exact this

/-- LEAF (S6): every cycle of `next` carries a cusp vertex (a cycle of cut slots only would keep its x-direction,
`xsign_next_iff`, and strictly increase `xcoord2`, `xcoord2_next` — impossible on a finite cycle). -/
theorem exists_cuspVertex_sameCycle (u : Slot (word F)) :
    ∃ c : F.Cusp, (nextPerm (word_closed F)).SameCycle u (cuspVertex F c) := by
  by_contra hno
  push Not at hno
  have hcut : ∀ j, ((next (word_closed F))^[j] u).1.2 ≠ 0 := by
    intro j hj
    obtain ⟨c, hc⟩ := s6b_cuspVertex_of_snd_eq_zero F _ hj
    exact hno c (sameCycle_of_iterate (word_closed F) (a := j) (b := 0)
      (by rw [Function.iterate_zero_apply]; exact hc))
  have hsign : ∀ j, xsign ((next (word_closed F))^[j] u) = xsign u := by
    intro j
    induction j with
    | zero => rfl
    | succ j ih =>
      rw [Function.iterate_succ_apply', ← ih]
      have hc := hcut (j + 1)
      rw [Function.iterate_succ_apply'] at hc
      exact (xsign_next_iff (word_closed F) _).2 hc
  have hP := period_pos (word_closed F) u
  have hper := iterate_period (word_closed F) u
  cases hx : xsign u with
  | true =>
    have hmono : ∀ j, xcoord2 u + j ≤ xcoord2 ((next (word_closed F))^[j] u) := by
      intro j
      induction j with
      | zero => simp
      | succ j ih =>
        rw [Function.iterate_succ_apply']
        have := (xcoord2_next (word_closed F) _).1 (by rw [hsign j]; exact hx)
        omega
    have := hmono (period (word_closed F) u)
    rw [hper] at this
    omega
  | false =>
    have hmono : ∀ j, xcoord2 ((next (word_closed F))^[j] u) + j ≤ xcoord2 u := by
      intro j
      induction j with
      | zero => simp
      | succ j ih =>
        rw [Function.iterate_succ_apply']
        have := (xcoord2_next (word_closed F) _).2 (by rw [hsign j]; exact hx)
        omega
    have := hmono (period (word_closed F) u)
    rw [hper] at this
    omega

/-- LEAF (S6, `comp`): the slot of an occurrence lies on the cycle of its circle (`jump_cross` puts `Φ p` on the
path from `slotAt (t_p − ε)`, then `path_cusps` over one period reaches the cusp vertex of `someCuspOn`). -/
theorem slotComp_ΦFun (p : F.Occ) : U2.slotComp (word_closed F) (ΦFun F p) = circleComp F p.1.1 := by
  unfold circleComp
  rw [U2.slotComp_eq_iff]
  obtain ⟨t, ht⟩ := s6b_exists_regular F p.1.1
  have ht' : xOf F (someCuspOn F p.1.1).1.1 t ∉ singX F := by rwa [someCuspOn_fst]
  have e := s6b_slotAt_fst_eq F (someCuspOn_fst F p.1.1) ht' ht
  have h2 := s6b_sameCycle_cuspVertex F (someCuspOn F p.1.1) ht'
  rw [e] at h2
  exact (s6b_sameCycle_ΦFun F p ht).symm.trans h2

/-- LEAF (S6, `succ`, THE HEART): the first `σ` slot after `Φ p` along `next` is `Φ` of the next occurrence on the
circle (`jump_cross` at `p` puts `Φ p` at index `a` of the path from `slotAt (t_p − ε)`, `path_no_occ` up to the
successor — no occurrence strictly between, `cycNext_no_between` on `occComp`/`occKey`; `slotAt` is 1-periodic in
`t` for the wrap-around when `p` is alone — and `jump_cross` at the successor; then `firstReturn_eq_of_path`). -/
theorem ΦFun_cycNext (p : F.Occ) :
    ΦFun F (cycNext (occComp F) (occKey F) (occKey_inj F) p) =
      (firstReturn (nextPerm (word_closed F)) U2.IsσSlot (ΦSub F p)).1 := by
  obtain ⟨p', hp'⟩ : ∃ p', p' = cycNext (occComp F) (occKey F) (occKey_inj F) p := ⟨_, rfl⟩
  have hcomp : p'.1.1 = p.1.1 := by rw [hp']; exact comp_cycNext (occComp F) (occKey F) (occKey_inj F) p
  obtain ⟨n, hn⟩ : ∃ n : ℤ, n = if p.1.2 < p'.1.2 then 0 else 1 := ⟨_, rfl⟩
  have hlt : p.1.2 < p'.1.2 + n := by
    rw [hn]
    split_ifs with h
    · simpa using h
    · have := (SmoothFront.Occ.mem_Ico F p).2
      have := (SmoothFront.Occ.mem_Ico F p').1
      push_cast; linarith
  have hno : ∀ q : F.Occ, ∀ s ∈ Set.Ioo p.1.2 (p'.1.2 + n), ¬ SameParam q.1 (p.1.1, s) := by
    intro q s hs hq
    rw [hp'] at hn hs
    exact s6b_no_occ_between F p q hn hs hq
  rw [← hp']
  -- the three pieces of the path: across `p`, between, across `p'`
  obtain ⟨ε₁, hε₁, H₁⟩ := jump_cross F p
  obtain ⟨ε₃, hε₃, H₃⟩ := s6b_jump_cross_shift F p' n
  obtain ⟨ε', hε'pos, hε'1, hε'3, hε'mid⟩ : ∃ ε' > 0, ε' < ε₁ ∧ ε' < ε₃ ∧ 2 * ε' < p'.1.2 + n - p.1.2 := by
    have hpos : 0 < min (min ε₁ ε₃) ((p'.1.2 + n - p.1.2) / 2) :=
      lt_min (lt_min hε₁ hε₃) (by linarith)
    have m1 : min (min ε₁ ε₃) ((p'.1.2 + n - p.1.2) / 2) ≤ ε₁ := (min_le_left _ _).trans (min_le_left _ _)
    have m2 : min (min ε₁ ε₃) ((p'.1.2 + n - p.1.2) / 2) ≤ ε₃ := (min_le_left _ _).trans (min_le_right _ _)
    have m3 : min (min ε₁ ε₃) ((p'.1.2 + n - p.1.2) / 2) ≤ (p'.1.2 + n - p.1.2) / 2 := min_le_right _ _
    exact ⟨_ / 2, half_pos hpos, by linarith, by linarith, by linarith⟩
  obtain ⟨h₁, h₂, m₁, hm₁, hpathA, a₁, ha₁, hΦA, hnoσA⟩ := H₁ ε' ⟨hε'pos, hε'1⟩
  obtain ⟨h₃, h₄, m₃, hm₃, hpathC, a₃, ha₃, hΦC, hnoσC⟩ := H₃ ε' ⟨hε'pos, hε'3⟩
  have h₃' : xOf F p.1.1 (p'.1.2 + n - ε') ∉ singX F := by rw [← hcomp]; exact h₃
  obtain ⟨m₂, hpathB, hσB, -⟩ := s6b_path F (i := p.1.1) (t₀ := p.1.2 + ε') (t₁ := p'.1.2 + n - ε') (by linarith) h₂ h₃'
  have hfst : slotAt F p.1.1 (p'.1.2 + n - ε') h₃' = slotAt F p'.1.1 (p'.1.2 + n - ε') h₃ :=
    (s6b_slotAt_fst_eq F hcomp h₃ h₃').symm
  have hiter : ∀ k, (next (word_closed F))^[k] (ΦFun F p) =
      (next (word_closed F))^[k + a₁] (slotAt F p.1.1 (p.1.2 - ε') h₁) := by
    intro k; rw [← hΦA, ← Function.iterate_add_apply]
  have hBC : (next (word_closed F))^[a₃ + (m₂ + m₁)] (slotAt F p.1.1 (p.1.2 - ε') h₁) = ΦFun F p' := by
    rw [Function.iterate_add_apply, Function.iterate_add_apply, hpathA, hpathB, hfst, hΦC]
  have hMa : (m₁ - a₁) + m₂ + a₃ + a₁ = a₃ + (m₂ + m₁) := by omega
  have hend : (next (word_closed F))^[(m₁ - a₁) + m₂ + a₃] (ΦFun F p) = ΦFun F p' := by
    rw [hiter, hMa, hBC]
  have hMpos : 0 < (m₁ - a₁) + m₂ + a₃ := by omega
  rw [U2.firstReturn_eq_of_path (nextPerm (word_closed F)) U2.IsσSlot (ΦSub F p) hMpos ?_ ?_]
  · show ΦFun F p' = ((nextPerm (word_closed F)) ^ ((m₁ - a₁) + m₂ + a₃)) (ΦFun F p)
    rw [U2.nextPerm_pow_apply, hend]
  · show U2.IsσSlot (((nextPerm (word_closed F)) ^ ((m₁ - a₁) + m₂ + a₃)) (ΦFun F p))
    rw [U2.nextPerm_pow_apply, hend]
    exact isσSlot_ΦFun F p'
  · intro j hj0 hjM
    show ¬ U2.IsσSlot (((nextPerm (word_closed F)) ^ j) (ΦFun F p))
    rw [U2.nextPerm_pow_apply, hiter]
    by_cases hA : j + a₁ < m₁
    · exact hnoσA (j + a₁) hA (by omega)
    · by_cases hB : j + a₁ < m₁ + m₂
      · obtain ⟨j', hj'⟩ : ∃ j', j + a₁ = j' + m₁ := ⟨j + a₁ - m₁, by omega⟩
        rw [hj', Function.iterate_add_apply, hpathA]
        intro hσ
        obtain ⟨q, ⟨s, hs, hq⟩, -⟩ := hσB j' (by omega) hσ
        exact hno q s ⟨by linarith [hs.1], by linarith [hs.2]⟩ hq
      · obtain ⟨j'', hj''⟩ : ∃ j'', j + a₁ = j'' + (m₂ + m₁) := ⟨j + a₁ - (m₂ + m₁), by omega⟩
        rw [hj'', Function.iterate_add_apply, Function.iterate_add_apply, hpathA, hpathB, hfst]
        exact hnoσC j'' (by omega) (by omega)

/-! MERGER (W3S_Merged, 2026-09-14): `circleComp_bijective` and `circleEquiv` (skeleton L15151-15158) are declared here, after `ΦFun_cycNext`, because the proof needs `slotAt`, the jump leaves, `path_cusps`, `exists_cuspVertex_sameCycle` (S6b). Text verbatim. -/

/-- LEAF (S6): the circles of `F` correspond bijectively to the cycles of `next` (injective: every cusp vertex on the
cycle of a circle's traversal is a cusp of that circle, `path_cusps`; surjective: every cycle carries a cusp
vertex, `exists_cuspVertex_sameCycle`). -/
theorem circleComp_bijective : Function.Bijective (circleComp F) := by
  refine ⟨?_, ?_⟩
  · intro i i' h
    unfold circleComp at h
    rw [U2.slotComp_eq_iff] at h
    have := s6b_circ_of_sameCycle F h
    rwa [s6b_circ_cuspVertex, s6b_circ_cuspVertex, someCuspOn_fst, someCuspOn_fst] at this
  · intro j
    obtain ⟨c, hc⟩ := exists_cuspVertex_sameCycle F (rep (word_closed F) j)
    refine ⟨c.1.1, ?_⟩
    rw [← s6b_slotComp_cuspVertex, (U2.slotComp_eq_iff _ _ _).mpr hc.symm, U2.slotComp_eq_equivFin, orbitOf_rep,
      Equiv.apply_symm_apply]

/-- the circle bijection of the record isomorphism -/
def circleEquiv : Fin F.c ≃ Fin (numComp (word_closed F)) := Equiv.ofBijective _ (circleComp_bijective F)

end Traversal

/-! #### The assembly: the record isomorphism, the sweep statement, the leaf -/

section Assembly

variable (F : SmoothFront)

/-- THE RECORD ISOMORPHISM of the sweep, from the leaves. -/
def recordIso : RecordIso (frontRecord F) (U2.slotRecord (word_closed F) U2.IsσSlot (U2.allActive (word_closed F))) where
  e := circleEquiv F
  Φ := occEquiv F
  comp_eq p := slotComp_ΦFun F p
  succ_eq p := Subtype.ext (ΦFun_cycNext F p)
  pair_eq p := Subtype.ext (ΦFun_partner F p)
  bit_eq p := isDesc_ΦFun F p
  sgn_eq p := σsgn_ΦFun F p

/-- THE SWEEP STATEMENT, proved from the leaves. -/
theorem sweep_proof : SweepStatement F :=
  ⟨oword F, word_ne_nil F, (downCountSyn_eq F).symm, (cuspCount_eq F).symm, ⟨recordIso F⟩⟩

end Assembly

end

end U8R

/-- LEAF = THE REPRESENTATION THEOREM (ng:commutation sm-3:1924-1925, proof 1938-1947 "separate them by small
local x translations ... Reading successive vertical cuts then gives the finite elementary word"): the
block's analytic bridge (FINAL §8 risk 1; 7.5-11k lines; attacked last; rows 76 and 83 wait for it). -/
theorem represent (F : SmoothFront) : ∃ W : OWord,
    F.downCount = (realize W).downCount ∧ F.writhe = (realize W).writhe ∧ F.sCount = (realize W).sCount ∧
    ∀ S : Diagram, F.IsRounding S → Nonempty (RecordIso S.record (realize W).diagram.record) :=
  U8R.represent_of_sweepStatement F (U8R.sweep_proof F)

end Leaves

end FrontRows

/-! ## Statement of row 76 (verbatim from `Skeleton_W2.lean` L57-73 = `Statements_FINAL.lean`) -/

structure NgCommutationClauses : Prop where
  comm_D : ∀ W W' : OWord, IsComm W.letters W'.letters →
    (realize W).downCount = (realize W').downCount
  comm_w : ∀ W W' : OWord, IsComm W.letters W'.letters → (realize W).writhe = (realize W').writhe
  comm_d : ∀ W W' : OWord, IsComm W.letters W'.letters →
    degAZ (P (realize W).diagram) = degAZ (P (realize W').diagram)
  comm_B : ∀ W W' : OWord, IsComm W.letters W'.letters → (realize W).defect = (realize W').defect
  deform_D : ∀ F F' : SmoothFront, Nonempty (F.NonsingularDeformation F') → F.downCount = F'.downCount
  deform_w : ∀ F F' : SmoothFront, Nonempty (F.NonsingularDeformation F') → F.writhe = F'.writhe
  deform_d : ∀ F F' : SmoothFront, Nonempty (F.NonsingularDeformation F') →
    ∀ S S' : Diagram, F.IsRounding S → F'.IsRounding S' → degAZ (P S) = degAZ (P S')
  deform_B : ∀ F F' : SmoothFront, Nonempty (F.NonsingularDeformation F') →
    ∀ S S' : Diagram, F.IsRounding S → F'.IsRounding S' → F.defect S = F'.defect S'
  represent : ∀ F : SmoothFront, ∃ W : OWord,
    F.downCount = (realize W).downCount ∧ F.writhe = (realize W).writhe ∧ F.sCount = (realize W).sCount ∧
    ∀ S : Diagram, F.IsRounding S → Nonempty (RecordIso S.record (realize W).diagram.record)

open FrontRows

/-! ## Assembly of row 76 -/

/-- **ng:commutation** (row 76), assembled. -/
theorem ng_commutation : NgCommutationClauses where
  comm_D := fun _ _ h => (comm_counts h).1
  comm_w := fun _ _ h => (comm_counts h).2
  comm_d := fun _ _ h => by rw [P_comm h]
  comm_B := fun _ _ h => by
    unfold PLFront.defect
    rw [(comm_counts h).1, (comm_counts h).2, P_comm h]
  deform_D := deform_downCount
  deform_w := deform_writhe
  deform_d := fun F F' h S S' hS hS' => by rw [deform_P F F' h S S' hS hS']
  deform_B := fun F F' h S S' hS hS' => by
    unfold SmoothFront.defect SmoothFront.dOf
    rw [deform_downCount F F' h, deform_writhe F F' h, deform_P F F' h S S' hS hS']
  represent := represent

end SM
