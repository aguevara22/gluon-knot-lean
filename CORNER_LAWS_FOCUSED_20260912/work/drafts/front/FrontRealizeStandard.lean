import SM.FrontRealizeCorrespondence

/-! Front block, lane β, unit β2 (2026-09-14): module `SM/FrontRealizeStandard.lean` (intended home).
Adopted design work/reports/front-block-design-FINAL-20260913.md (§2 G1 (iii), §4 `Base`, §5 item 6
ng:circle); β1 report work/drafts/front/BETA1_REPORT.md §5 item 3.

# The grid realization, part 4: the standard-circle base

* The standard front circle `l₁ r₁`, in either orientation, realizes to a union of standard circles
  (`stdCircle_isStandardCircles`): no crossing, one component, one left and one right cusp.
* The planarity fact needed by row 81's `base_B`: a realization that is a union of standard circles has
  exactly one downward cusp per component, `downCount = c` (`IsStandardCircles.downCount_eq_c`).  Proof: with
  no `σ` letter the vertical order of two strands is preserved across every column (`posR_order`), so the
  rightward arc leaving the left cusp on its upper arm (`d = true`) arrives at the right cusp on its upper
  arm; exactly one of the two cusps is traversed upper → lower.

All declarations live in `SM.FrontRealize`.  Checked with `lake env lean` (sorry-free, standard axioms). -/

namespace SM.FrontRealize

open SM SM.Link SM.FrontWord SM.FrontWord.Letter

noncomputable section

/-! ## 1. The standard circle `l₁ r₁` -/

section StdCircle

variable (d : Bool)

/-- the standard circle word with the upper arm rightward iff `d` -/
def circleWord : Word := [.l 1 d, .r 1]

theorem circleWord_closed : (circleWord d).Closed := by cases d <;> decide

theorem circleWord_ne_nil : circleWord d ≠ [] := by simp [circleWord]

theorem circleWord_length : (circleWord d).length = 2 := rfl

theorem circle_letterAt_zero : letterAt (circleWord d) 0 = .l 1 d := rfl
theorem circle_letterAt_one : letterAt (circleWord d) 1 = .r 1 := rfl

/-- the four slots of the standard circle -/
theorem circle_slots (s : ℕ × ℕ) (h : IsSlot (circleWord d) s) :
    s = (0, 0) ∨ s = (1, 1) ∨ s = (1, 2) ∨ s = (1, 0) := by
  obtain ⟨h1, h2⟩ := isSlot_bound (circleWord d) h
  rw [circleWord_length] at h1 h2
  obtain ⟨a, b⟩ := s
  simp only at h1 h2
  interval_cases a <;> interval_cases b <;> first | decide | (exfalso; revert h; cases d <;> decide)

theorem circle_isSlot_00 : IsSlot (circleWord d) (0, 0) := by cases d <;> decide
theorem circle_isSlot_10 : IsSlot (circleWord d) (1, 0) := by cases d <;> decide

/-- Every slot of the standard circle lies on the cycle of `(0, 0)`: the cycle is
`(0,0) → (1,1) → (1,0) → (1,2) → (0,0)` for `d = true` and `(0,0) → (1,2) → (1,0) → (1,1) → (0,0)` for
`d = false`. -/
theorem circle_sameCycle (u : Slot (circleWord d)) :
    (nextPerm (circleWord_closed d)).SameCycle ⟨(0, 0), circle_isSlot_00 d⟩ u := by
  have hslots := circle_slots d u.1 u.2
  cases d
  · have n1 : (next (circleWord_closed false) ⟨(0, 0), circle_isSlot_00 false⟩).1 = (1, 2) := by
      rw [next_val]; decide
    have n2 : ((next (circleWord_closed false))^[2] ⟨(0, 0), circle_isSlot_00 false⟩).1 = (1, 0) := by
      show (next (circleWord_closed false) (next (circleWord_closed false) ⟨(0, 0), circle_isSlot_00 false⟩)).1 = _
      rw [next_val, n1]; decide
    have n3 : ((next (circleWord_closed false))^[3] ⟨(0, 0), circle_isSlot_00 false⟩).1 = (1, 1) := by
      show (next (circleWord_closed false) ((next (circleWord_closed false))^[2] ⟨(0, 0), circle_isSlot_00 false⟩)).1 = _
      rw [next_val, n2]; decide
    rcases hslots with h | h | h | h
    · exact sameCycle_of_iterate _ (a := 0) (b := 0) (Subtype.ext h.symm)
    · exact sameCycle_of_iterate _ (a := 3) (b := 0) (Subtype.ext (by rw [n3, Function.iterate_zero_apply, h]))
    · exact sameCycle_of_iterate _ (a := 1) (b := 0)
        (Subtype.ext (by rw [Function.iterate_one, n1, Function.iterate_zero_apply, h]))
    · exact sameCycle_of_iterate _ (a := 2) (b := 0) (Subtype.ext (by rw [n2, Function.iterate_zero_apply, h]))
  · have n1 : (next (circleWord_closed true) ⟨(0, 0), circle_isSlot_00 true⟩).1 = (1, 1) := by
      rw [next_val]; decide
    have n2 : ((next (circleWord_closed true))^[2] ⟨(0, 0), circle_isSlot_00 true⟩).1 = (1, 0) := by
      show (next (circleWord_closed true) (next (circleWord_closed true) ⟨(0, 0), circle_isSlot_00 true⟩)).1 = _
      rw [next_val, n1]; decide
    have n3 : ((next (circleWord_closed true))^[3] ⟨(0, 0), circle_isSlot_00 true⟩).1 = (1, 2) := by
      show (next (circleWord_closed true) ((next (circleWord_closed true))^[2] ⟨(0, 0), circle_isSlot_00 true⟩)).1 = _
      rw [next_val, n2]; decide
    rcases hslots with h | h | h | h
    · exact sameCycle_of_iterate _ (a := 0) (b := 0) (Subtype.ext h.symm)
    · exact sameCycle_of_iterate _ (a := 1) (b := 0)
        (Subtype.ext (by rw [Function.iterate_one, n1, Function.iterate_zero_apply, h]))
    · exact sameCycle_of_iterate _ (a := 3) (b := 0) (Subtype.ext (by rw [n3, Function.iterate_zero_apply, h]))
    · exact sameCycle_of_iterate _ (a := 2) (b := 0) (Subtype.ext (by rw [n2, Function.iterate_zero_apply, h]))

theorem circle_numComp : numComp (circleWord_closed d) = 1 := by
  unfold numComp
  rw [Fintype.card_eq_one_iff]
  refine ⟨orbitOf _ ⟨(0, 0), circle_isSlot_00 d⟩, fun o => ?_⟩
  obtain ⟨u, rfl⟩ := orbitOf_surjective _ o
  exact (orbitOf_eq_iff _ _ _).2 (circle_sameCycle d u).symm

/-- The standard circle has no crossing letter. -/
theorem circle_no_σ (k : σIdx (W := circleWord d)) : False := by
  obtain ⟨m, hm⟩ := σIdx_letter k
  have hk : (k.1 : ℕ) < 2 := k.1.2
  interval_cases hk' : (k.1 : ℕ)
  · rw [circle_letterAt_zero] at hm; cases hm
  · rw [circle_letterAt_one] at hm; cases hm

/-- The left cusp of the standard circle is the vertex `(0, 0)`, the right cusp the vertex `(1, 0)`. -/
theorem circle_cusp_l {u : Slot (circleWord d)} (h : u.1.2 = 0)
    (hl : ∃ m d', letterAt (circleWord d) u.1.1 = .l m d') : u.1 = (0, 0) := by
  rcases circle_slots d u.1 u.2 with h' | h' | h' | h'
  · exact h'
  · rw [h'] at h; simp at h
  · rw [h'] at h; simp at h
  · exfalso
    obtain ⟨m, d', hm⟩ := hl
    rw [h', circle_letterAt_one] at hm
    cases hm

theorem circle_cusp_r {u : Slot (circleWord d)} (h : u.1.2 = 0)
    (hr : ∃ m, letterAt (circleWord d) u.1.1 = .r m) : u.1 = (1, 0) := by
  rcases circle_slots d u.1 u.2 with h' | h' | h' | h'
  · exfalso
    obtain ⟨m, hm⟩ := hr
    rw [h', circle_letterAt_zero] at hm
    cases hm
  · rw [h'] at h; simp at h
  · rw [h'] at h; simp at h
  · exact h'

/-- A set of strands consisting of exactly the strand at one slot has one element. -/
theorem card_strand_slot (pl : Placement) {W : Word} (hW : W.Closed) (hne : W ≠ []) (u : Slot W)
    (p : (realizeAt pl hW hne).Γ.Strand → Prop) (hp : ∀ s, p s ↔ slotOf pl hW hne s = u) :
    Nat.card {s : (realizeAt pl hW hne).Γ.Strand // p s} = 1 := by
  rw [Nat.card_eq_one_iff_unique]
  refine ⟨⟨fun a b => Subtype.ext (slotOf_injective pl hW hne (((hp a.1).1 a.2).trans ((hp b.1).1 b.2).symm))⟩,
    ⟨⟨strandOfSlot pl hW hne u, (hp _).2 (slotOf_strandOfSlot pl hW hne u)⟩⟩⟩

/-- ng:circle: the standard front circle, in either orientation, realizes to a union of standard circles. -/
theorem circle_isStandardCircles (pl : Placement) :
    (realizeAt pl (circleWord_closed d) (circleWord_ne_nil d)).IsStandardCircles := by
  have hc : (realizeAt pl (circleWord_closed d) (circleWord_ne_nil d)).Γ.c = 1 := circle_numComp d
  have hi : ∀ (i : Fin (realizeAt pl (circleWord_closed d) (circleWord_ne_nil d)).Γ.c)
      (s : (realizeAt pl (circleWord_closed d) (circleWord_ne_nil d)).Γ.Strand), s.1 = i := fun i s =>
    Fin.ext (by have := s.1.2; have := i.2; omega)
  refine ⟨?_, fun i => ⟨?_, ?_⟩⟩
  · exact ⟨fun x => circle_no_σ d (crossingEquiv pl _ _ x)⟩
  · apply card_strand_slot pl _ _ ⟨(0, 0), circle_isSlot_00 d⟩
    intro s
    rw [isLeftCusp_iff]
    constructor
    · rintro ⟨-, hc, hl⟩
      exact Subtype.ext (circle_cusp_l d hc hl)
    · intro h
      refine ⟨hi i s, ?_, ?_⟩
      · rw [h]
      · rw [h]; exact ⟨1, d, rfl⟩
  · apply card_strand_slot pl _ _ ⟨(1, 0), circle_isSlot_10 d⟩
    intro s
    rw [isRightCusp_iff]
    constructor
    · rintro ⟨-, hc, hr⟩
      exact Subtype.ext (circle_cusp_r d hc hr)
    · intro h
      refine ⟨hi i s, ?_, ?_⟩
      · rw [h]
      · rw [h]; exact ⟨1, rfl⟩

theorem stdCircleWord_isStandardCircles :
    (realizeAt .std stdCircleWord.closed stdCircleWord_ne_nil).IsStandardCircles :=
  circle_isStandardCircles true .std

end StdCircle

/-! ## 2. The planarity fact: a union of standard circles has one downward cusp per component -/

section Planarity

variable (pl : Placement) {W : Word} (hW : W.Closed) (hne : W ≠ [])
include hW

/-- A crossing-free realization comes from a word without `σ` letters. -/
theorem no_σ_of_isEmpty (h : IsEmpty (realizeAt pl hW hne).Γ.Crossing) {k m : ℕ} (hk : k < W.length)
    (hℓ : letterAt W k = .σ m) : False :=
  h.elim ((crossingEquiv pl hW hne).symm ⟨⟨k, hk⟩, by rw [hℓ]; rfl⟩)

omit hW in
/-- Without a crossing letter the order of positions is preserved across a column. -/
theorem posR_lt_of_not_σ {ℓ : Letter} (hℓ : ∀ m, ℓ ≠ .σ m) {p q p' q' : ℕ} (h : ℓ.posR p = some q)
    (h' : ℓ.posR p' = some q') (hpp : p < p') : q < q' := by
  rcases Shape.posR_order h h' hpp with h1 | ⟨m, hm, -⟩
  · exact h1
  · exact absurd hm (hℓ m)

/-- A rightward cut slot whose successor is a cut slot passes to the next cut, keeping its direction. -/
theorem next_cut_right {u : Slot W} {k p : ℕ} (hu : u.1 = (k, p)) (hp : p ≠ 0) (hx : xsign u = true)
    (hn : (next hW u).1.2 ≠ 0) :
    ∃ q, (next hW u).1 = (k + 1, q) ∧ q ≠ 0 ∧ xsign (next hW u) = true ∧ (letterAt W k).posR p = some q ∧
      k < W.length := by
  rcases next_cases hW u with
    ⟨k', p', q, hs, hp', hb, hn', hq, hbq, hpq, hk⟩ | ⟨k', p', m, hs, hp', hb, hℓ, -, hn', -, -⟩ |
    ⟨k', p', q, hs, hp', hb, -, -, -, -, -, -⟩ | ⟨k', p', m, d, hs, hp', hb, -, -, -, -, -, -, -⟩ |
    ⟨k', m, d, hs, -, -, -, -, -, -⟩ | ⟨k', m, hs, -, -, -, -, -⟩
  · rw [hu] at hs; simp only [Prod.mk.injEq] at hs; obtain ⟨rfl, rfl⟩ := hs
    exact ⟨q, hn', by omega, by rw [xsign_cut hn' (by omega)]; exact hbq, hpq, hk⟩
  · rw [hn'] at hn; exact absurd rfl hn
  · rw [hu] at hs; simp only [Prod.mk.injEq] at hs; obtain ⟨rfl, rfl⟩ := hs
    rw [xsign_cut hu hp] at hx; rw [hx] at hb; exact absurd hb (by decide)
  · rw [hu] at hs; simp only [Prod.mk.injEq] at hs; obtain ⟨rfl, rfl⟩ := hs
    rw [xsign_cut hu hp] at hx; rw [hx] at hb; exact absurd hb (by decide)
  · rw [hu] at hs; simp at hs; omega
  · rw [hu] at hs; simp at hs; omega

/-- A rightward cut slot whose successor is a cusp enters a right cusp at its own cut. -/
theorem next_cusp_of_right {u : Slot W} {k p : ℕ} (hu : u.1 = (k, p)) (hp : p ≠ 0) (hx : xsign u = true)
    (hn : (next hW u).1.2 = 0) :
    ∃ m, letterAt W k = .r m ∧ (next hW u).1 = (k, 0) ∧ (p = m ∨ p = m + 1) ∧ bit W k p = true := by
  rcases next_cases hW u with
    ⟨k', p', q, hs, -, -, hn', hq, -, -, -⟩ | ⟨k', p', m, hs, hp', hb, hℓ, hpm, hn', -, -⟩ |
    ⟨k', p', q, hs, hp', hb, -, -, -, -, -, -⟩ | ⟨k', p', m, d, hs, hp', hb, -, -, -, -, -, -, -⟩ |
    ⟨k', m, d, hs, -, -, -, -, -, -⟩ | ⟨k', m, hs, -, -, -, -, -⟩
  · rw [hn'] at hn; simp at hn; omega
  · rw [hu] at hs; simp only [Prod.mk.injEq] at hs; obtain ⟨rfl, rfl⟩ := hs
    exact ⟨m, hℓ, hn', hpm, hb⟩
  · rw [hu] at hs; simp only [Prod.mk.injEq] at hs; obtain ⟨rfl, rfl⟩ := hs
    rw [xsign_cut hu hp] at hx; rw [hx] at hb; exact absurd hb (by decide)
  · rw [hu] at hs; simp only [Prod.mk.injEq] at hs; obtain ⟨rfl, rfl⟩ := hs
    rw [xsign_cut hu hp] at hx; rw [hx] at hb; exact absurd hb (by decide)
  · rw [hu] at hs; simp at hs; omega
  · rw [hu] at hs; simp at hs; omega

/-- Going backwards from a leftward cut slot whose predecessor is a cut slot moves one cut to the right,
keeping the leftward direction. -/
theorem prev_cut_right {u : Slot W} {k q : ℕ} (hu : u.1 = (k, q)) (hq : q ≠ 0) (hx : xsign u = false)
    (hn : (prev hW u).1.2 ≠ 0) :
    ∃ q', (prev hW u).1 = (k + 1, q') ∧ q' ≠ 0 ∧ xsign (prev hW u) = false ∧ (letterAt W k).posR q = some q' ∧
      k < W.length := by
  have hb : bit W k q = false := by rw [← xsign_cut hu hq]; exact hx
  have hpk : 1 ≤ q ∧ q ≤ (cut W k).length := by
    have := u.2; rw [hu] at this
    rcases this with ⟨h0, -⟩ | ⟨h1, h2, -⟩
    · simp at h0; exact absurd h0 hq
    · exact ⟨h1, h2⟩
  obtain ⟨-, hk⟩ := cutSlot_pos hW hpk.1 hpk.2
  have hpv : (prev hW u).1 = prevPair W (k, q) := by rw [prev_val, hu]
  cases hpos : (letterAt W k).posR q with
  | none => rw [hpv, prevPair_left_none W hq hb hpos] at hn; exact absurd rfl hn
  | some q' =>
    obtain ⟨D⟩ := decomp hW k hk
    obtain ⟨hq1, -, hbq, -⟩ := D.posR_some hpk.1 hpk.2 hpos
    have hpv' : (prev hW u).1 = (k + 1, q') := by rw [hpv, prevPair_left W hq hb hpos]
    refine ⟨q', hpv', by omega, ?_, rfl, hk⟩
    rw [xsign_cut hpv' (by omega), bit_eq, hbq]; exact hb

/-- Going backwards from a leftward cut slot whose predecessor is a cusp reaches a right cusp at its own
cut, on the arm the traversal leaves by. -/
theorem prev_cusp_of_left {u : Slot W} {k q : ℕ} (hu : u.1 = (k, q)) (hq : q ≠ 0) (hx : xsign u = false)
    (hn : (prev hW u).1.2 = 0) :
    ∃ m, letterAt W k = .r m ∧ (prev hW u).1 = (k, 0) ∧ (q = m ∨ q = m + 1) := by
  have hb : bit W k q = false := by rw [← xsign_cut hu hq]; exact hx
  have hpk : 1 ≤ q ∧ q ≤ (cut W k).length := by
    have := u.2; rw [hu] at this
    rcases this with ⟨h0, -⟩ | ⟨h1, h2, -⟩
    · simp at h0; exact absurd h0 hq
    · exact ⟨h1, h2⟩
  obtain ⟨-, hk⟩ := cutSlot_pos hW hpk.1 hpk.2
  have hpv : (prev hW u).1 = prevPair W (k, q) := by rw [prev_val, hu]
  cases hpos : (letterAt W k).posR q with
  | none =>
    obtain ⟨m, hm, hqm⟩ := posR_eq_none_iff.1 hpos
    exact ⟨m, hm, by rw [hpv, prevPair_left_none W hq hb hpos], hqm⟩
  | some q' =>
    obtain ⟨D⟩ := decomp hW k hk
    obtain ⟨hq1, -, -, -⟩ := D.posR_some hpk.1 hpk.2 hpos
    rw [hpv, prevPair_left W hq hb hpos] at hn; simp at hn; omega

variable {kL m : ℕ} {d : Bool} {uL : Slot W} (hL : uL.1 = (kL, 0)) (hℓL : letterAt W kL = .l m d)
include hL hℓL

theorem next_uL : (next hW uL).1 = (kL + 1, if d then m else m + 1) := by
  rw [next_val, hL, nextPair_cusp_l W hℓL]

theorem prev_uL : (prev hW uL).1 = (kL + 1, if d then m + 1 else m) := by
  rw [prev_val, hL, prevPair_cusp_l W hℓL]

theorem one_le_m : 1 ≤ m := by
  have := uL.2; rw [hL] at this
  rcases this with ⟨-, hk, -⟩ | ⟨h0, -⟩
  · obtain ⟨D⟩ := decomp hW kL hk; rw [hℓL] at D; have := D.hm; simpa [idx] using this
  · simp at h0

theorem xsign_next_uL : xsign (next hW uL) = true := by
  rw [xsign_next_of_cut hW (next_cusp_cut hW (by rw [hL])), xsign_cusp_l hL hℓL]

theorem xsign_prev_uL : xsign (prev hW uL) = false := by
  have h := xsign_next_iff hW (prev hW uL)
  rw [next_prev, hL] at h
  simp only [ne_eq, not_true_eq_false, iff_false] at h
  rw [xsign_cusp_l hL hℓL] at h
  cases hx : xsign (prev hW uL)
  · rfl
  · exact absurd hx.symm h

/-- The rightward run from the left cusp: as long as no cusp is met, the `j`-th successor is a rightward
cut slot at cut `kL + j`. -/
theorem run_right : ∀ j, 1 ≤ j → (∀ i, 1 ≤ i → i ≤ j → ((next hW)^[i] uL).1.2 ≠ 0) →
    ∃ p, ((next hW)^[j] uL).1 = (kL + j, p) ∧ p ≠ 0 ∧ xsign ((next hW)^[j] uL) = true := by
  intro j hj
  induction j with
  | zero => omega
  | succ j ih =>
    intro hcut
    rcases Nat.eq_zero_or_pos j with rfl | hjpos
    · refine ⟨if d then m else m + 1, ?_, ?_, ?_⟩
      · rw [Function.iterate_one, next_uL hW hL hℓL]
      · have := one_le_m hW hL hℓL; split_ifs <;> omega
      · rw [Function.iterate_one]; exact xsign_next_uL hW hL hℓL
    · obtain ⟨p, hp, hp0, hx⟩ := ih hjpos (fun i hi1 hi2 => hcut i hi1 (by omega))
      rw [Function.iterate_succ_apply']
      have hc := hcut (j + 1) (by omega) le_rfl
      rw [Function.iterate_succ_apply'] at hc
      obtain ⟨q, hq, hq0, hxq, -, -⟩ := next_cut_right hW hp hp0 hx hc
      exact ⟨q, by rw [hq]; congr 1, hq0, hxq⟩

/-- The backward run from the left cusp: the `j`-th predecessor is a leftward cut slot at cut `kL + j`. -/
theorem run_left : ∀ j, 1 ≤ j → (∀ i, 1 ≤ i → i ≤ j → ((prev hW)^[i] uL).1.2 ≠ 0) →
    ∃ q, ((prev hW)^[j] uL).1 = (kL + j, q) ∧ q ≠ 0 ∧ xsign ((prev hW)^[j] uL) = false := by
  intro j hj
  induction j with
  | zero => omega
  | succ j ih =>
    intro hcut
    rcases Nat.eq_zero_or_pos j with rfl | hjpos
    · refine ⟨if d then m + 1 else m, ?_, ?_, ?_⟩
      · rw [Function.iterate_one, prev_uL hW hL hℓL]
      · have := one_le_m hW hL hℓL; split_ifs <;> omega
      · rw [Function.iterate_one]; exact xsign_prev_uL hW hL hℓL
    · obtain ⟨q, hq, hq0, hx⟩ := ih hjpos (fun i hi1 hi2 => hcut i hi1 (by omega))
      rw [Function.iterate_succ_apply']
      have hc := hcut (j + 1) (by omega) le_rfl
      rw [Function.iterate_succ_apply'] at hc
      obtain ⟨q', hq', hq0', hxq, -, -⟩ := prev_cut_right hW hq hq0 hx hc
      exact ⟨q', by rw [hq']; congr 1, hq0', hxq⟩

/-- The order invariant: without crossing letters, the rightward run stays above the backward run iff it
left the left cusp on the upper arm. -/
theorem run_order (hσ : ∀ k m', k < W.length → letterAt W k ≠ .σ m') :
    ∀ j, 1 ≤ j → (∀ i, 1 ≤ i → i ≤ j → ((next hW)^[i] uL).1.2 ≠ 0 ∧ ((prev hW)^[i] uL).1.2 ≠ 0) →
    ∃ p q, ((next hW)^[j] uL).1 = (kL + j, p) ∧ ((prev hW)^[j] uL).1 = (kL + j, q) ∧ (p < q ↔ d = true) := by
  intro j hj
  induction j with
  | zero => omega
  | succ j ih =>
    intro hcut
    rcases Nat.eq_zero_or_pos j with rfl | hjpos
    · refine ⟨if d then m else m + 1, if d then m + 1 else m, ?_, ?_, ?_⟩
      · rw [Function.iterate_one, next_uL hW hL hℓL]
      · rw [Function.iterate_one, prev_uL hW hL hℓL]
      · cases d <;> simp
    · obtain ⟨p, q, hp, hq, hpq⟩ := ih hjpos (fun i hi1 hi2 => hcut i hi1 (by omega))
      obtain ⟨p₁, hp₁, hp₀, hxp⟩ := run_right hW hL hℓL j hjpos (fun i hi1 hi2 => (hcut i hi1 (by omega)).1)
      obtain ⟨q₁, hq₁, hq₀, hxq⟩ := run_left hW hL hℓL j hjpos (fun i hi1 hi2 => (hcut i hi1 (by omega)).2)
      rw [hp] at hp₁; rw [hq] at hq₁
      simp only [Prod.mk.injEq, true_and] at hp₁ hq₁
      subst hp₁ hq₁
      have hc := hcut (j + 1) (by omega) le_rfl
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply'] at hc
      obtain ⟨p', hp', hp'0, -, hposp, hk⟩ := next_cut_right hW hp hp₀ hxp hc.1
      obtain ⟨q', hq', hq'0, -, hposq, -⟩ := prev_cut_right hW hq hq₀ hxq hc.2
      have hpq' : p ≠ q := by
        intro h
        have : (next hW)^[j] uL = (prev hW)^[j] uL := Subtype.ext (by rw [hp, hq, h])
        rw [this] at hxp; rw [hxp] at hxq; exact absurd hxq (by decide)
      have hnotσ : ∀ m', letterAt W (kL + j) ≠ .σ m' := fun m' => hσ _ m' hk
      refine ⟨p', q', ?_, ?_, ?_⟩
      · rw [Function.iterate_succ_apply', hp']; congr 1
      · rw [Function.iterate_succ_apply', hq']; congr 1
      · rw [← hpq]
        constructor
        · intro h
          by_contra hc
          rcases Nat.lt_or_gt_of_ne hpq' with h1 | h1
          · exact hc h1
          · exact lt_asymm h (posR_lt_of_not_σ hnotσ hposq hposp h1)
        · intro h
          exact posR_lt_of_not_σ hnotσ hposp hposq h

/-- The first cusp met along the rightward run is a right cusp, entered from the arm with rightward bit. -/
theorem first_hit_right (n₀ : ℕ) (hn₀1 : 1 ≤ n₀) (hcusp : ((next hW)^[n₀] uL).1.2 = 0)
    (hmin : ∀ i, 1 ≤ i → i < n₀ → ((next hW)^[i] uL).1.2 ≠ 0) :
    2 ≤ n₀ ∧ ∃ p m', ((next hW)^[n₀ - 1] uL).1 = (kL + (n₀ - 1), p) ∧ letterAt W (kL + (n₀ - 1)) = .r m' ∧
      ((next hW)^[n₀] uL).1 = (kL + (n₀ - 1), 0) ∧ (p = m' ∨ p = m' + 1) ∧ bit W (kL + (n₀ - 1)) p = true := by
  obtain ⟨n₁, rfl⟩ : ∃ n₁, n₀ = n₁ + 1 := ⟨n₀ - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have h2 : 2 ≤ n₁ + 1 := by
    by_contra h
    have : n₁ = 0 := by omega
    subst this
    rw [Function.iterate_one] at hcusp
    exact next_cusp_cut hW (by rw [hL]) hcusp
  obtain ⟨p, hp, hp0, hx⟩ := run_right hW hL hℓL n₁ (by omega) (fun i hi1 hi2 => hmin i hi1 (by omega))
  rw [Function.iterate_succ_apply'] at hcusp ⊢
  obtain ⟨m', hℓ, hn', hpm, hb⟩ := next_cusp_of_right hW hp hp0 hx hcusp
  exact ⟨h2, p, m', hp, hℓ, hn', hpm, hb⟩

/-- The first cusp met along the backward run is a right cusp, left along the arm with leftward bit. -/
theorem first_hit_left (m₀ : ℕ) (hm₀1 : 1 ≤ m₀) (hcusp : ((prev hW)^[m₀] uL).1.2 = 0)
    (hmin : ∀ i, 1 ≤ i → i < m₀ → ((prev hW)^[i] uL).1.2 ≠ 0) :
    2 ≤ m₀ ∧ ∃ q m', ((prev hW)^[m₀ - 1] uL).1 = (kL + (m₀ - 1), q) ∧ letterAt W (kL + (m₀ - 1)) = .r m' ∧
      ((prev hW)^[m₀] uL).1 = (kL + (m₀ - 1), 0) ∧ (q = m' ∨ q = m' + 1) ∧ bit W (kL + (m₀ - 1)) q = false := by
  obtain ⟨m₁, rfl⟩ : ∃ m₁, m₀ = m₁ + 1 := ⟨m₀ - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have h2 : 2 ≤ m₁ + 1 := by
    by_contra h
    have : m₁ = 0 := by omega
    subst this
    rw [Function.iterate_one, prev_uL hW hL hℓL] at hcusp
    have := one_le_m hW hL hℓL
    simp at hcusp; split_ifs at hcusp <;> omega
  obtain ⟨q, hq, hq0, hx⟩ := run_left hW hL hℓL m₁ (by omega) (fun i hi1 hi2 => hmin i hi1 (by omega))
  rw [Function.iterate_succ_apply'] at hcusp ⊢
  obtain ⟨m', hℓ, hn', hqm⟩ := prev_cusp_of_left hW hq hq0 hx hcusp
  exact ⟨h2, q, m', hq, hℓ, hn', hqm, by rw [← xsign_cut hq hq0]; exact hx⟩

end Planarity

/-! ### Assembly -/

section Assembly

variable (pl : Placement) {W : Word} (hW : W.Closed) (hne : W ≠ [])
include hW

omit hW in
/-- the down bit of a right cusp letter reads the bit of its upper arm -/
theorem downBit_r_iff {m : ℕ} {c : Cuts} (hlen : m + 1 ≤ c.length) :
    (Letter.r m).downBit c = 1 ↔ c.getD (m - 1) false = true := by
  have hlt : m - 1 < c.length := by omega
  obtain ⟨b, hb⟩ : ∃ b, c.getD (m - 1) false = b := ⟨_, rfl⟩
  have hdrop : c.drop (m - 1) = b :: c.drop (m - 1 + 1) := by
    rw [List.drop_eq_getElem_cons hlt]
    congr 1
    rw [← hb, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]; rfl
  simp only [downBit]
  rw [hdrop, hb]
  cases b <;> simp

omit hW in
/-- the down bit of a left cusp letter is `1` iff its upper arm travels leftward -/
theorem downBit_l_iff {m : ℕ} {d : Bool} (c : Cuts) : (Letter.l m d).downBit c = 1 ↔ d = false := by
  cases d <;> simp [downBit]

theorem prev_iterate_next_iterate (n : ℕ) (u : Slot W) : (prev hW)^[n] ((next hW)^[n] u) = u :=
  (Function.LeftInverse.iterate (prev_next hW) n) u

theorem next_iterate_prev_iterate (n : ℕ) (u : Slot W) : (next hW)^[n] ((prev hW)^[n] u) = u :=
  (Function.LeftInverse.iterate (next_prev hW) n) u

/-- A component with exactly one left and one right cusp and no crossing has exactly one downward cusp:
the left cusp is downward iff the right cusp is not. -/
theorem down_iff_not_down (h : IsEmpty (realizeAt pl hW hne).Γ.Crossing) (i : Fin (realizeAt pl hW hne).Γ.c)
    (L : (realizeAt pl hW hne).Γ.Strand) (hLi : L.1 = i) (hL : (realizeAt pl hW hne).IsLeftCusp L)
    (R : (realizeAt pl hW hne).Γ.Strand) (hRi : R.1 = i) (hR : (realizeAt pl hW hne).IsRightCusp R)
    (hRu : ∀ s, s.1 = i → (realizeAt pl hW hne).IsRightCusp s → s = R) :
    ((realizeAt pl hW hne).IsDownCusp L ↔ ¬ (realizeAt pl hW hne).IsDownCusp R) := by
  classical
  have hσ : ∀ k m', k < W.length → letterAt W k ≠ .σ m' := fun k m' hk hℓ => no_σ_of_isEmpty pl hW hne h hk hℓ
  -- the left cusp
  obtain ⟨hL0, m, d, hℓL⟩ := (isLeftCusp_iff pl hW hne L).1 hL
  set uL := slotOf pl hW hne L with huL
  have hLs : uL.1 = (uL.1.1, 0) := Prod.ext rfl hL0
  -- the right cusp
  obtain ⟨hR0, m', hℓR⟩ := (isRightCusp_iff pl hW hne R).1 hR
  set uR := slotOf pl hW hne R with huR
  have hRs : uR.1 = (uR.1.1, 0) := Prod.ext rfl hR0
  -- any right-cusp slot on the cycle of `uL` is `uR`
  have hRslot : ∀ v : Slot W, (nextPerm hW).SameCycle v uL → v.1.2 = 0 → (∃ m'', letterAt W v.1.1 = .r m'') →
      v = uR := by
    intro v hcyc hv0 hvr
    have hS : (strandOfSlot pl hW hne v).1 = i := by
      rw [← hLi]
      exact (toSlot_fst_eq_iff hW _ _).2 (by
        show (nextPerm hW).SameCycle (toSlot hW (strandOfSlot pl hW hne v)) (toSlot hW L)
        rw [show toSlot hW (strandOfSlot pl hW hne v) = v from slotOf_strandOfSlot pl hW hne v]
        exact hcyc)
    have hSR : (realizeAt pl hW hne).IsRightCusp (strandOfSlot pl hW hne v) := by
      rw [isRightCusp_iff, slotOf_strandOfSlot]; exact ⟨hv0, hvr⟩
    have := hRu _ hS hSR
    rw [← slotOf_strandOfSlot pl hW hne v, this]
  -- the first cusp along the rightward run
  have hex : ∃ n, 1 ≤ n ∧ ((next hW)^[n] uL).1.2 = 0 :=
    ⟨period hW uL, period_pos hW uL, by rw [iterate_period, hL0]⟩
  set n₀ := Nat.find hex with hn₀
  have hn₀spec := Nat.find_spec hex
  have hmin : ∀ j, 1 ≤ j → j < n₀ → ((next hW)^[j] uL).1.2 ≠ 0 := fun j h1 h2 hc =>
    Nat.find_min hex h2 ⟨h1, hc⟩
  obtain ⟨hn₀2, p, m₁, hp, hℓ₁, hn₀c, hpm, hbp⟩ := first_hit_right hW hLs hℓL n₀ hn₀spec.1 hn₀spec.2 hmin
  have hRn : (next hW)^[n₀] uL = uR :=
    hRslot ((next hW)^[n₀] uL)
      (sameCycle_of_iterate hW (s := (next hW)^[n₀] uL) (t := uL) (a := 0) (b := n₀) rfl) hn₀spec.2
      ⟨m₁, by rw [hn₀c]; exact hℓ₁⟩
  have hkR : uR.1.1 = uL.1.1 + (n₀ - 1) := by rw [← hRn, hn₀c]
  have hm₁ : m' = m₁ := by
    have := hℓR; rw [hkR, hℓ₁] at this; exact (Letter.r.inj this).symm
  subst hm₁
  -- the first cusp along the backward run
  have hprevper : (prev hW)^[period hW uL] uL = uL := by
    have h := prev_iterate_next_iterate hW (period hW uL) uL
    rwa [iterate_period] at h
  have hex' : ∃ n, 1 ≤ n ∧ ((prev hW)^[n] uL).1.2 = 0 :=
    ⟨period hW uL, period_pos hW uL, by rw [hprevper, hL0]⟩
  set m₀ := Nat.find hex' with hm₀
  have hm₀spec := Nat.find_spec hex'
  have hmin' : ∀ j, 1 ≤ j → j < m₀ → ((prev hW)^[j] uL).1.2 ≠ 0 := fun j h1 h2 hc =>
    Nat.find_min hex' h2 ⟨h1, hc⟩
  obtain ⟨hm₀2, q, m₂, hq, hℓ₂, hm₀c, hqm, hbq⟩ := first_hit_left hW hLs hℓL m₀ hm₀spec.1 hm₀spec.2 hmin'
  have hRm : (prev hW)^[m₀] uL = uR :=
    hRslot ((prev hW)^[m₀] uL)
      (sameCycle_of_iterate hW (s := (prev hW)^[m₀] uL) (t := uL) (a := m₀) (b := 0)
        (next_iterate_prev_iterate hW m₀ uL)) hm₀spec.2 ⟨m₂, by rw [hm₀c]; exact hℓ₂⟩
  have hkR' : uR.1.1 = uL.1.1 + (m₀ - 1) := by rw [← hRm, hm₀c]
  have hnm : m₀ = n₀ := by omega
  have hm₂ : m' = m₂ := by
    have := hℓR; rw [hkR', hℓ₂] at this; exact (Letter.r.inj this).symm
  subst hm₂
  -- the order invariant at the last cut before the right cusp
  obtain ⟨p₁, q₁, hp₁, hq₁, hpq⟩ := run_order hW hLs hℓL hσ (n₀ - 1) (by omega)
    (fun j hj1 hj2 => ⟨hmin j hj1 (by omega), hmin' j hj1 (by omega)⟩)
  rw [hnm] at hq hbq
  rw [hp] at hp₁; rw [hq] at hq₁
  simp only [Prod.mk.injEq, true_and] at hp₁ hq₁
  subst hp₁ hq₁
  have hpq' : p ≠ q := by
    intro h; rw [h] at hbp; rw [hbp] at hbq; exact absurd hbq (by decide)
  -- `p < q ↔ p = m' ↔ bit kR m' = true`
  have hkey : (p < q ↔ bit W (uL.1.1 + (n₀ - 1)) m' = true) := by
    rcases hpm with rfl | rfl <;> rcases hqm with rfl | rfl
    · exact absurd rfl hpq'
    · simp only [Nat.lt_succ_self, true_iff]; exact hbp
    · constructor
      · intro h; omega
      · intro h; rw [h] at hbq; exact absurd hbq (by decide)
    · exact absurd rfl hpq'
  -- down-ness of the two cusps
  have hlen : m' + 1 ≤ (cut W uR.1.1).length := by
    have hk : uR.1.1 < W.length := by
      have := uR.2; rw [hRs] at this
      rcases this with ⟨-, hk, -⟩ | ⟨h0, -⟩
      · exact hk
      · simp at h0
    obtain ⟨D⟩ := decomp hW uR.1.1 hk; rw [hℓR] at D; exact D.bits_r.2
  rw [isDownCusp_iff, isDownCusp_iff, ← huL, ← huR, hℓL, hℓR, downBit_l_iff, downBit_r_iff hlen]
  rw [← bit_eq, hkR, ← hkey, hpq]
  simp [hL0, hR0]

/-- Each component of a union of standard circles has exactly one downward cusp. -/
theorem IsStandardCircles.card_down_eq_one (hstd : (realizeAt pl hW hne).IsStandardCircles)
    (i : Fin (realizeAt pl hW hne).Γ.c) :
    Nat.card {s : (realizeAt pl hW hne).Γ.Strand // s.1 = i ∧ (realizeAt pl hW hne).IsDownCusp s} = 1 := by
  obtain ⟨hcross, hcusps⟩ := hstd
  obtain ⟨hLc, hRc⟩ := hcusps i
  rw [Nat.card_eq_one_iff_unique] at hLc hRc
  obtain ⟨⟨hLsub⟩, ⟨⟨L, hLi, hL⟩⟩⟩ := hLc
  obtain ⟨⟨hRsub⟩, ⟨⟨R, hRi, hR⟩⟩⟩ := hRc
  have hLu : ∀ s, s.1 = i → (realizeAt pl hW hne).IsLeftCusp s → s = L := fun s hs hsl =>
    congrArg Subtype.val (hLsub ⟨s, hs, hsl⟩ ⟨L, hLi, hL⟩)
  have hRu : ∀ s, s.1 = i → (realizeAt pl hW hne).IsRightCusp s → s = R := fun s hs hsr =>
    congrArg Subtype.val (hRsub ⟨s, hs, hsr⟩ ⟨R, hRi, hR⟩)
  have hiff := down_iff_not_down pl hW hne hcross i L hLi hL R hRi hR hRu
  -- every cusp of the component is `L` or `R`
  have hcusp : ∀ s, s.1 = i → (realizeAt pl hW hne).IsCusp s → s = L ∨ s = R := fun s hs hc => by
    rcases ((realizeAt pl hW hne).isCusp_iff s).1 hc with hl | hr
    · exact Or.inl (hLu s hs hl)
    · exact Or.inr (hRu s hs hr)
  rw [Nat.card_eq_one_iff_unique]
  by_cases hdL : (realizeAt pl hW hne).IsDownCusp L
  · have hdR : ¬ (realizeAt pl hW hne).IsDownCusp R := hiff.1 hdL
    refine ⟨⟨fun a b => ?_⟩, ⟨⟨L, hLi, hdL⟩⟩⟩
    have ha : a.1 = L := by
      rcases hcusp a.1 a.2.1 a.2.2.isCusp with h | h
      · exact h
      · exact absurd (h ▸ a.2.2) hdR
    have hb : b.1 = L := by
      rcases hcusp b.1 b.2.1 b.2.2.isCusp with h | h
      · exact h
      · exact absurd (h ▸ b.2.2) hdR
    exact Subtype.ext (ha.trans hb.symm)
  · have hdR : (realizeAt pl hW hne).IsDownCusp R := by
      by_contra hc; exact hdL (hiff.2 hc)
    refine ⟨⟨fun a b => ?_⟩, ⟨⟨R, hRi, hdR⟩⟩⟩
    have ha : a.1 = R := by
      rcases hcusp a.1 a.2.1 a.2.2.isCusp with h | h
      · exact absurd (h ▸ a.2.2) hdL
      · exact h
    have hb : b.1 = R := by
      rcases hcusp b.1 b.2.1 b.2.2.isCusp with h | h
      · exact absurd (h ▸ b.2.2) hdL
      · exact h
    exact Subtype.ext (ha.trans hb.symm)

/-- The planarity fact for row 81's `base_B`: a realization that is a union of standard circles has exactly
one downward cusp per component, `D = c`. -/
theorem IsStandardCircles.downCount_eq_c (hstd : (realizeAt pl hW hne).IsStandardCircles) :
    (realizeAt pl hW hne).downCount = (realizeAt pl hW hne).Γ.c := by
  unfold PLFront.downCount
  rw [PLFront.card_subtype_eq_sum_comp]
  rw [Finset.sum_congr rfl fun i _ => IsStandardCircles.card_down_eq_one pl hW hne hstd i]
  simp only [Finset.sum_const, smul_eq_mul, mul_one]
  exact Finset.card_fin _

end Assembly

end

end SM.FrontRealize

namespace SM

open SM.FrontWord SM.FrontRealize

/-- The planarity fact on `realize`: a union of standard circles has `D = c` (nonempty words). -/
theorem realize_downCount_eq_c_of_isStandardCircles (W : OWord) (h : W.letters ≠ [])
    (hstd : (realize W).IsStandardCircles) : (realize W).downCount = (realize W).Γ.c := by
  rw [realize_eq_realizeAt W h] at hstd ⊢
  exact IsStandardCircles.downCount_eq_c _ _ _ hstd

/-- The realization of the empty word (the standard circle) is a union of standard circles with `D = c`. -/
theorem realize_nil_isStandardCircles (W : OWord) (h : W.letters = []) : (realize W).IsStandardCircles := by
  rw [realize_nil W h]; exact stdCircleWord_isStandardCircles

/-- The standard circle `l₁ r₁` in either orientation: `realize ⟨[l 1 d, r 1], _⟩` is a union of standard
circles. -/
theorem realize_circle_isStandardCircles (d : Bool) :
    (realize ⟨circleWord d, circleWord_closed d⟩).IsStandardCircles := by
  rw [realize_eq_realizeAt _ (circleWord_ne_nil d)]
  exact circle_isStandardCircles d .std

end SM
