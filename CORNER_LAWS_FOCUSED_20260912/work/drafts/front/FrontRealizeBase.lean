import SM.FrontInterfaces
import SM.FrontRealizeStandard

/-! Front block, lane β, unit β2 (2026-09-14): module `SM/FrontRealizeBase.lean` (intended home).
Adopted design work/reports/front-block-design-FINAL-20260913.md (§2 G1 (iii), §4 `Base`); statement unit
`SM/FrontInterfaces.lean` R2 ("Recorded obligation for β2: `(realize W).IsStandardCircles ↔
W.IsStandardCircleBase`").

# The grid realization, part 5: the syntactic base is the geometric base

`Word.IsStandardCircleBase W` (FrontInterfaces §1: a labelled run in which the left cusp at letter index
`k` pushes two strands labelled `k`, a right cusp is typed only on two strands of the same label, and a
crossing is never typed) implies `(realizeAt pl hW hne).IsStandardCircles`
(`isStandardCircles_of_isStandardCircleBase`): with the labels transported along the traversal
(`lab_next`: the label is constant on every cycle), every component has exactly one left cusp (its label),
and from that left cusp the rightward run meets its first cusp at a right cusp and the leftward run from
there returns to the same left cusp, so the cycle has exactly two cusps.  Together with
`IsStandardCircles.downCount_eq_c` this gives `D = c` on every word of the syntactic base
(`downCount_eq_c_of_isStandardCircleBase`), which is what row 81's `base_B` needs, and it transports the
axiom's `FiniteWordStatement (wordMovesOf s B OWord.IsStandardCircleBase)` to the geometric
`SM.wordMoves` (`finiteWordStatement_wordMoves_of`).  The converse direction is stated in §4 as an open item.

All declarations live in `SM.FrontRealize` (top-level results in `SM`).  Checked with `lake env lean`
(sorry-free, standard axioms; nothing here cites `SM.ng_finite_word`). -/

namespace SM.FrontRealize

open SM SM.Link SM.FrontWord SM.FrontWord.Letter SM.FrontWord.Word

noncomputable section

/-! ## 1. Labelled cuts -/

section Labels

variable (W : Word)

/-- The labelled cut before column `k`. -/
def lcut (k : ℕ) : List ℕ := (labelRun (W.take k) 0 []).getD []

/-- The label of position `p` (1-based) at cut `k`. -/
def lbl (k p : ℕ) : ℕ := (lcut W k).getD (p - 1) 0

theorem labelRun_append (V V' : Word) (k : ℕ) (c : List ℕ) :
    labelRun (V ++ V') k c = (labelRun V k c).bind (labelRun V' (k + V.length)) := by
  induction V generalizing k c with
  | nil => simp
  | cons a V ih =>
    simp only [List.cons_append, labelRun_cons, Option.bind_assoc, List.length_cons]
    congr 1
    funext c'
    rw [ih, Nat.add_assoc, Nat.add_comm 1]

variable {W}

theorem lrun_take (hB : W.IsStandardCircleBase) (k : ℕ) : labelRun (W.take k) 0 [] = some (lcut W k) := by
  unfold IsStandardCircleBase at hB
  rw [← List.take_append_drop k W, labelRun_append] at hB
  obtain ⟨c, hc, -⟩ := Option.bind_eq_some_iff.1 hB
  rw [lcut, hc]; rfl

theorem lstep_cut (hB : W.IsStandardCircleBase) {k : ℕ} (hk : k < W.length) :
    (letterAt W k).labelStep k (lcut W k) = some (lcut W (k + 1)) := by
  have h1 := lrun_take hB k
  have h2 := lrun_take hB (k + 1)
  rw [List.take_succ_eq_append_getElem hk, labelRun_append, h1, Option.bind_some, ← letterAt_eq W hk] at h2
  simp only [labelRun_cons, List.length_take, Nat.zero_add, Nat.min_eq_left hk.le] at h2
  cases h : (letterAt W k).labelStep k (lcut W k) with
  | none => rw [h] at h2; simp at h2
  | some c' =>
    rw [h] at h2
    simp only [Option.bind_some, labelRun_nil] at h2
    exact h2

/-- A word of the base has no crossing letter. -/
theorem no_σ_of_base (hB : W.IsStandardCircleBase) {k m : ℕ} (hk : k < W.length) (hℓ : letterAt W k = .σ m) :
    False := by
  have := lstep_cut hB hk
  rw [hℓ, labelStep_σ] at this
  exact absurd this (by simp)

/-- The decomposition of a typed labelled step. -/
theorem labelStep_eq_some_iff {ℓ : Letter} {k : ℕ} {c c' : List ℕ} :
    ℓ.labelStep k c = some c' ↔
      ∃ A L L' : List ℕ, 1 ≤ ℓ.idx ∧ A.length = ℓ.idx - 1 ∧ c = A ++ L ∧ ℓ.labelAct k L = some L' ∧ c' = A ++ L' := by
  constructor
  · intro h
    unfold labelStep at h
    split_ifs at h with hc
    · obtain ⟨L', hL', rfl⟩ := Option.map_eq_some_iff.1 h
      refine ⟨c.take (ℓ.idx - 1), c.drop (ℓ.idx - 1), L', hc.1, ?_, (List.take_append_drop _ _).symm, hL', rfl⟩
      simp only [List.length_take]; omega
  · rintro ⟨A, L, L', h1, hA, rfl, hL, rfl⟩
    unfold labelStep
    rw [ite_eq_left ⟨h1, by simp only [List.length_append]; omega⟩, List.take_left' hA, List.drop_left' hA, hL]
    rfl

/-- The labelled decomposition of column `k` of a base word: above/below windows as for the bit cuts. -/
theorem lcut_decomp (hB : W.IsStandardCircleBase) {k : ℕ} (hk : k < W.length) :
    ∃ A w w' R : List ℕ, 1 ≤ (letterAt W k).idx ∧ A.length = (letterAt W k).idx - 1 ∧
      w.length = (letterAt W k).arity ∧ w'.length = (letterAt W k).coarity ∧
      lcut W k = A ++ w ++ R ∧ lcut W (k + 1) = A ++ w' ++ R ∧
      ((∃ m d, letterAt W k = .l m d ∧ w = [] ∧ w' = [k, k]) ∨
       (∃ m a, letterAt W k = .r m ∧ w = [a, a] ∧ w' = [])) := by
  have h := lstep_cut hB hk
  obtain ⟨A, L, L', h1, hA, hc, hL, hc'⟩ := labelStep_eq_some_iff.1 h
  cases hℓ : letterAt W k with
  | l m d =>
    rw [hℓ] at hL h1 hA
    simp only [labelAct, Option.some.injEq] at hL
    exact ⟨A, [], [k, k], L, h1, hA, rfl, rfl, by rw [hc]; simp, by rw [hc', ← hL]; simp,
      Or.inl ⟨m, d, rfl, rfl, rfl⟩⟩
  | r m =>
    rw [hℓ] at hL h1 hA
    obtain ⟨a, b, L₀, hLab⟩ : ∃ a b L₀, L = a :: b :: L₀ := by
      match L with
      | [] => simp [labelAct] at hL
      | [a] => simp [labelAct] at hL
      | a :: b :: L₀ => exact ⟨a, b, L₀, rfl⟩
    subst hLab
    simp only [labelAct] at hL
    split_ifs at hL with hab
    · subst hab
      simp only [Option.some.injEq] at hL
      subst hL
      exact ⟨A, [a, a], [], L₀, h1, hA, rfl, rfl, by rw [hc]; simp, by rw [hc']; simp,
        Or.inr ⟨m, a, rfl, rfl, rfl⟩⟩
  | σ m => exact (no_σ_of_base hB hk hℓ).elim

/-- Labels above the letter are unchanged. -/
theorem lbl_above (hB : W.IsStandardCircleBase) {k p : ℕ} (hk : k < W.length) (hp1 : 1 ≤ p)
    (hp : p < (letterAt W k).idx) : lbl W (k + 1) p = lbl W k p := by
  obtain ⟨A, w, w', R, h1, hA, -, -, hc, hc', -⟩ := lcut_decomp hB hk
  unfold lbl
  rw [hc, hc', List.append_assoc, List.append_assoc, List.getD_append _ _ _ _ (by omega),
    List.getD_append _ _ _ _ (by omega)]

/-- Labels below the letter are unchanged (shifted by the strand-count change). -/
theorem lbl_below (hB : W.IsStandardCircleBase) {k p : ℕ} (hk : k < W.length)
    (hp : (letterAt W k).idx + (letterAt W k).arity ≤ p) :
    lbl W (k + 1) (p + (letterAt W k).coarity - (letterAt W k).arity) = lbl W k p := by
  obtain ⟨A, w, w', R, h1, hA, hw, hw', hc, hc', -⟩ := lcut_decomp hB hk
  unfold lbl
  rw [hc, hc', List.getD_append_right _ _ _ _ (by simp [hA, hw]; omega),
    List.getD_append_right _ _ _ _ (by simp [hA, hw']; omega)]
  congr 1
  simp only [List.length_append, hA, hw, hw']
  omega

/-- The two arms created by `l m d` at column `k` carry the label `k`. -/
theorem lbl_l (hB : W.IsStandardCircleBase) {k m : ℕ} {d : Bool} (hk : k < W.length) (hℓ : letterAt W k = .l m d) :
    lbl W (k + 1) m = k ∧ lbl W (k + 1) (m + 1) = k := by
  obtain ⟨A, w, w', R, h1, hA, -, -, -, hc', hcase⟩ := lcut_decomp hB hk
  rw [hℓ] at h1 hA
  simp only [idx] at h1 hA
  rcases hcase with ⟨m', d', hℓ', -, rfl⟩ | ⟨m', a, hℓ', -, -⟩
  · rw [hℓ] at hℓ'
    obtain ⟨rfl, -⟩ := Letter.l.inj hℓ'
    unfold lbl
    rw [hc']
    constructor
    · rw [List.append_assoc, List.getD_append_right _ _ _ _ (by omega), show m - 1 - A.length = 0 by omega]; rfl
    · rw [List.append_assoc, List.getD_append_right _ _ _ _ (by omega), show m + 1 - 1 - A.length = 1 by omega]; rfl
  · rw [hℓ] at hℓ'; cases hℓ'

/-- The two strands joined by `r m` at column `k` carry the same label. -/
theorem lbl_r (hB : W.IsStandardCircleBase) {k m : ℕ} (hk : k < W.length) (hℓ : letterAt W k = .r m) :
    lbl W k m = lbl W k (m + 1) := by
  obtain ⟨A, w, w', R, h1, hA, -, -, hc, -, hcase⟩ := lcut_decomp hB hk
  rw [hℓ] at h1 hA
  simp only [idx] at h1 hA
  rcases hcase with ⟨m', d', hℓ', -, -⟩ | ⟨m', a, hℓ', rfl, -⟩
  · rw [hℓ] at hℓ'; cases hℓ'
  · unfold lbl
    rw [hc, List.append_assoc]
    have e1 : (A ++ ([a, a] ++ R)).getD (m - 1) 0 = a := by
      rw [List.getD_append_right _ _ _ _ (by omega), show m - 1 - A.length = 0 by omega]; rfl
    have e2 : (A ++ ([a, a] ++ R)).getD (m + 1 - 1) 0 = a := by
      rw [List.getD_append_right _ _ _ _ (by omega), show m + 1 - 1 - A.length = 1 by omega]; rfl
    rw [e1, e2]

/-- Labels are transported along a passing strand (no crossing letter in a base word). -/
theorem lbl_posR (hB : W.IsStandardCircleBase) {k p q : ℕ} (hk : k < W.length) (hp1 : 1 ≤ p)
    (hpq : (letterAt W k).posR p = some q) : lbl W (k + 1) q = lbl W k p := by
  unfold posR at hpq
  split_ifs at hpq with h1 h2
  · obtain rfl := Option.some.inj hpq
    exact lbl_above hB hk hp1 h1
  · exfalso
    cases hℓ : letterAt W k with
    | l m d => rw [hℓ] at h1 h2; simp [idx, arity] at h1 h2; omega
    | r m => rw [hℓ] at hpq; simp at hpq
    | σ m => exact no_σ_of_base hB hk hℓ
  · obtain rfl := Option.some.inj hpq
    exact lbl_below hB hk (by omega)

end Labels

/-! ## 2. The label of a slot is constant along the traversal -/

section Lab

variable {W : Word} (hW : W.Closed) (hB : W.IsStandardCircleBase)

/-- The label of a slot: the label of its position at a cut slot; at a left-cusp vertex of column `k` the
label `k` it creates; at a right-cusp vertex the (common) label of the two strands it joins. -/
def lab (u : Slot W) : ℕ :=
  if u.1.2 = 0 then
    (match letterAt W u.1.1 with
      | .l _ _ => u.1.1
      | .r m => lbl W u.1.1 m
      | .σ _ => 0)
  else lbl W u.1.1 u.1.2

theorem lab_cut {u : Slot W} {k p : ℕ} (hu : u.1 = (k, p)) (hp : p ≠ 0) : lab u = lbl W k p := by
  simp [lab, hu, hp]

theorem lab_cusp_l {u : Slot W} {k m : ℕ} {d : Bool} (hu : u.1 = (k, 0)) (hℓ : letterAt W k = .l m d) :
    lab u = k := by simp [lab, hu, hℓ]

theorem lab_cusp_r {u : Slot W} {k m : ℕ} (hu : u.1 = (k, 0)) (hℓ : letterAt W k = .r m) :
    lab u = lbl W k m := by simp [lab, hu, hℓ]

include hW hB

/-- The label is constant along `next`. -/
theorem lab_next (u : Slot W) : lab (next hW u) = lab u := by
  rcases next_cases hW u with
    ⟨k, p, q, hs, hp, hb, hn, hq, hbq, hpq, hk⟩ | ⟨k, p, m, hs, hp, hb, hℓ, hpm, hn, hne, hk⟩ |
    ⟨k, p, q, hs, hp, hb, hn, hq, hbq, hpq, hk1, hk⟩ | ⟨k, p, m, d, hs, hp, hb, hℓ, hpm, hn, hb1, hb2, hk1, hk⟩ |
    ⟨k, m, d, hs, hℓ, hn, hb1, hb2, hm, hk⟩ | ⟨k, m, hs, hℓ, hn, hne, hm, hk⟩
  · rw [lab_cut hn (by omega), lab_cut hs (by omega)]
    exact lbl_posR hB hk hp hpq
  · rw [lab_cusp_r hn hℓ, lab_cut hs (by omega)]
    rcases hpm with rfl | rfl
    · rfl
    · exact lbl_r hB hk hℓ
  · rw [lab_cut hn (by omega), lab_cut hs (by omega)]
    -- `posL ℓ p = some q` ↔ `posR ℓ q = some p` for the letter of column `k − 1`
    obtain ⟨D⟩ := decomp hW (k - 1) (by omega)
    rw [show k - 1 + 1 = k by omega] at D
    have hpk : p ≤ (cut W k).length := by
      have := u.2; rw [hs] at this
      rcases this with ⟨h0, -⟩ | ⟨-, h1, -⟩
      · simp at h0; omega
      · exact h1
    obtain ⟨-, -, -, hqp⟩ := D.posL_some hp hpk hpq
    have := lbl_posR hB (k := k - 1) (by omega) hq hqp
    rw [show k - 1 + 1 = k by omega] at this
    exact this.symm
  · rw [lab_cusp_l hn hℓ, lab_cut hs (by omega)]
    obtain ⟨h1, h2⟩ := lbl_l hB (k := k - 1) (by omega) hℓ
    rw [show k - 1 + 1 = k by omega] at h1 h2
    rcases hpm with rfl | rfl
    · exact h1.symm
    · exact h2.symm
  · rw [lab_cusp_l hs hℓ, lab_cut hn (by split_ifs <;> omega)]
    obtain ⟨h1, h2⟩ := lbl_l hB hk hℓ
    cases d
    · simpa using h2
    · simpa using h1
  · rw [lab_cusp_r hs hℓ, lab_cut hn (by split_ifs <;> omega)]
    cases bit W k m
    · rfl
    · simpa using (lbl_r hB hk hℓ).symm

theorem lab_iterate (u : Slot W) (n : ℕ) : lab ((next hW)^[n] u) = lab u := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', lab_next hW hB, ih]

/-- The label is constant on every cycle. -/
theorem lab_eq_of_sameCycle {u v : Slot W} (h : (nextPerm hW).SameCycle u v) : lab u = lab v := by
  obtain ⟨n, hn⟩ := exists_iterate_of_sameCycle hW h
  rw [← hn, lab_iterate hW hB]

end Lab

/-! ## 3. Every cycle has exactly one left and one right cusp -/

section Cycles

variable {W : Word} (hW : W.Closed)
include hW

/-- A leftward cut slot whose successor is a cusp enters a left cusp at the previous column. -/
theorem next_cusp_of_left {u : Slot W} {k p : ℕ} (hu : u.1 = (k, p)) (hp : p ≠ 0) (hx : xsign u = false)
    (hn : (next hW u).1.2 = 0) :
    ∃ m d, letterAt W (k - 1) = .l m d ∧ (next hW u).1 = (k - 1, 0) := by
  rcases next_cases hW u with
    ⟨k', p', q, hs, -, hb, hn', hq, -, -, -⟩ | ⟨k', p', m, hs, hp', hb, -, -, -, -, -⟩ |
    ⟨k', p', q, hs, -, -, hn', hq, -, -, -, -⟩ | ⟨k', p', m, d, hs, hp', hb, hℓ, hpm, hn', -, -, -, -⟩ |
    ⟨k', m, d, hs, -, -, -, -, -, -⟩ | ⟨k', m, hs, -, -, -, -, -⟩
  · rw [hu] at hs; simp only [Prod.mk.injEq] at hs; obtain ⟨rfl, rfl⟩ := hs
    rw [xsign_cut hu hp] at hx; rw [hx] at hb; exact absurd hb (by decide)
  · rw [hu] at hs; simp only [Prod.mk.injEq] at hs; obtain ⟨rfl, rfl⟩ := hs
    rw [xsign_cut hu hp] at hx; rw [hx] at hb; exact absurd hb (by decide)
  · rw [hn'] at hn; simp at hn; omega
  · rw [hu] at hs; simp only [Prod.mk.injEq] at hs; obtain ⟨rfl, rfl⟩ := hs
    exact ⟨m, d, hℓ, hn'⟩
  · rw [hu] at hs; simp at hs; omega
  · rw [hu] at hs; simp at hs; omega

/-- From a rightward cut slot, the successors stay rightward cut slots (with increasing x-coordinate)
until the first cusp, which is a right cusp. -/
theorem hit_r (u : Slot W) (hu : u.1.2 ≠ 0) (hx : xsign u = true) :
    ∃ n, 1 ≤ n ∧ ((next hW)^[n] u).1.2 = 0 ∧ (∃ m, letterAt W ((next hW)^[n] u).1.1 = .r m) ∧
      ∀ i, i < n → ((next hW)^[i] u).1.2 ≠ 0 ∧ xsign ((next hW)^[i] u) = true := by
  classical
  have run : ∀ j, (∀ i, i ≤ j → ((next hW)^[i] u).1.2 ≠ 0) →
      xsign ((next hW)^[j] u) = true ∧ xcoord2 u + j ≤ xcoord2 ((next hW)^[j] u) := by
    intro j
    induction j with
    | zero => intro _; exact ⟨hx, le_rfl⟩
    | succ j ih =>
      intro hcut
      obtain ⟨hxj, hcj⟩ := ih (fun i hi => hcut i (by omega))
      have hc := hcut (j + 1) le_rfl
      rw [Function.iterate_succ_apply'] at hc ⊢
      refine ⟨by rw [xsign_next_of_cut hW hc]; exact hxj, ?_⟩
      have := (xcoord2_next hW ((next hW)^[j] u)).1 hxj
      omega
  have hex : ∃ n, 1 ≤ n ∧ ((next hW)^[n] u).1.2 = 0 := by
    by_contra hcon
    push_neg at hcon
    have hcut : ∀ i, i ≤ period hW u → ((next hW)^[i] u).1.2 ≠ 0 := by
      intro i hi
      rcases Nat.eq_zero_or_pos i with rfl | hi0
      · exact hu
      · exact hcon i hi0
    obtain ⟨-, hle⟩ := run (period hW u) hcut
    rw [iterate_period] at hle
    have := period_pos hW u
    omega
  refine ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2, ?_, ?_⟩
  · have hmin : ∀ i, i < Nat.find hex → ((next hW)^[i] u).1.2 ≠ 0 := by
      intro i hi
      rcases Nat.eq_zero_or_pos i with rfl | hi0
      · exact hu
      · exact fun hc => Nat.find_min hex hi ⟨hi0, hc⟩
    obtain ⟨n₁, hn₁⟩ : ∃ n₁, Nat.find hex = n₁ + 1 := ⟨Nat.find hex - 1, by have := (Nat.find_spec hex).1; omega⟩
    have hcut1 := hmin n₁ (by omega)
    obtain ⟨hxn, -⟩ := run n₁ (fun i hi => hmin i (by omega))
    have hcusp := (Nat.find_spec hex).2
    rw [hn₁, Function.iterate_succ_apply'] at hcusp ⊢
    obtain ⟨m, hℓ, hn, -, -⟩ := next_cusp_of_right hW (u := (next hW)^[n₁] u) (k := ((next hW)^[n₁] u).1.1)
      (p := ((next hW)^[n₁] u).1.2) rfl hcut1 hxn hcusp
    exact ⟨m, by rw [hn]; exact hℓ⟩
  · intro i hi
    have hmin : ∀ i, i < Nat.find hex → ((next hW)^[i] u).1.2 ≠ 0 := by
      intro i hi
      rcases Nat.eq_zero_or_pos i with rfl | hi0
      · exact hu
      · exact fun hc => Nat.find_min hex hi ⟨hi0, hc⟩
    exact ⟨hmin i hi, (run i (fun j hj => hmin j (by omega))).1⟩

/-- From a leftward cut slot, the successors stay leftward cut slots (with decreasing x-coordinate) until
the first cusp, which is a left cusp. -/
theorem hit_l (u : Slot W) (hu : u.1.2 ≠ 0) (hx : xsign u = false) :
    ∃ n, 1 ≤ n ∧ ((next hW)^[n] u).1.2 = 0 ∧ (∃ m d, letterAt W ((next hW)^[n] u).1.1 = .l m d) ∧
      ∀ i, i < n → ((next hW)^[i] u).1.2 ≠ 0 ∧ xsign ((next hW)^[i] u) = false := by
  classical
  have run : ∀ j, (∀ i, i ≤ j → ((next hW)^[i] u).1.2 ≠ 0) →
      xsign ((next hW)^[j] u) = false ∧ xcoord2 ((next hW)^[j] u) + j ≤ xcoord2 u := by
    intro j
    induction j with
    | zero => intro _; exact ⟨hx, le_rfl⟩
    | succ j ih =>
      intro hcut
      obtain ⟨hxj, hcj⟩ := ih (fun i hi => hcut i (by omega))
      have hc := hcut (j + 1) le_rfl
      rw [Function.iterate_succ_apply'] at hc ⊢
      refine ⟨by rw [xsign_next_of_cut hW hc]; exact hxj, ?_⟩
      have := (xcoord2_next hW ((next hW)^[j] u)).2 hxj
      omega
  have hex : ∃ n, 1 ≤ n ∧ ((next hW)^[n] u).1.2 = 0 := by
    by_contra hcon
    push_neg at hcon
    have hcut : ∀ i, i ≤ period hW u → ((next hW)^[i] u).1.2 ≠ 0 := by
      intro i hi
      rcases Nat.eq_zero_or_pos i with rfl | hi0
      · exact hu
      · exact hcon i hi0
    obtain ⟨-, hle⟩ := run (period hW u) hcut
    rw [iterate_period] at hle
    have := period_pos hW u
    omega
  refine ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2, ?_, ?_⟩
  · have hmin : ∀ i, i < Nat.find hex → ((next hW)^[i] u).1.2 ≠ 0 := by
      intro i hi
      rcases Nat.eq_zero_or_pos i with rfl | hi0
      · exact hu
      · exact fun hc => Nat.find_min hex hi ⟨hi0, hc⟩
    obtain ⟨n₁, hn₁⟩ : ∃ n₁, Nat.find hex = n₁ + 1 := ⟨Nat.find hex - 1, by have := (Nat.find_spec hex).1; omega⟩
    have hcut1 := hmin n₁ (by omega)
    obtain ⟨hxn, -⟩ := run n₁ (fun i hi => hmin i (by omega))
    have hcusp := (Nat.find_spec hex).2
    rw [hn₁, Function.iterate_succ_apply'] at hcusp ⊢
    obtain ⟨m, d, hℓ, hn⟩ := next_cusp_of_left hW (u := (next hW)^[n₁] u) (k := ((next hW)^[n₁] u).1.1)
      (p := ((next hW)^[n₁] u).1.2) rfl hcut1 hxn hcusp
    exact ⟨m, d, by rw [hn]; exact hℓ⟩
  · intro i hi
    have hmin : ∀ i, i < Nat.find hex → ((next hW)^[i] u).1.2 ≠ 0 := by
      intro i hi
      rcases Nat.eq_zero_or_pos i with rfl | hi0
      · exact hu
      · exact fun hc => Nat.find_min hex hi ⟨hi0, hc⟩
    exact ⟨hmin i hi, (run i (fun j hj => hmin j (by omega))).1⟩

/-- Every cycle contains a left cusp. -/
theorem exists_lcusp (u : Slot W) :
    ∃ v : Slot W, (nextPerm hW).SameCycle u v ∧ v.1.2 = 0 ∧ ∃ m d, letterAt W v.1.1 = .l m d := by
  -- reduce to a leftward cut slot on the cycle
  suffices h : ∃ w : Slot W, (nextPerm hW).SameCycle u w ∧ w.1.2 ≠ 0 ∧ xsign w = false by
    obtain ⟨w, hcyc, hw, hx⟩ := h
    obtain ⟨n, -, hc, hl, -⟩ := hit_l hW w hw hx
    exact ⟨_, hcyc.trans (sameCycle_of_iterate hW (s := w) (a := n) (b := 0) rfl), hc, hl⟩
  by_cases hu : u.1.2 = 0
  · -- a cusp: its successor is a cut slot
    have hc := next_cusp_cut hW hu
    cases hx : xsign (next hW u)
    · exact ⟨next hW u, sameCycle_of_iterate hW (s := u) (a := 1) (b := 0) rfl |>.symm.symm, hc, hx⟩
    · obtain ⟨n, -, hcR, ⟨m, hℓ⟩, -⟩ := hit_r hW (next hW u) hc hx
      -- the right cusp reached; its successor is a leftward cut slot
      have hR : ((next hW)^[n] (next hW u)).1 = (((next hW)^[n] (next hW u)).1.1, 0) := Prod.ext rfl hcR
      refine ⟨next hW ((next hW)^[n] (next hW u)), ?_, next_cusp_cut hW hcR, ?_⟩
      · have : next hW ((next hW)^[n] (next hW u)) = (next hW)^[n + 2] u := by
          rw [Function.iterate_succ_apply', Function.iterate_succ_apply]
        rw [this]
        exact (sameCycle_of_iterate hW (s := u) (a := n + 2) (b := 0) rfl).symm.symm
      · rw [xsign_next_of_cut hW (next_cusp_cut hW hcR), xsign_cusp_r hR hℓ]
  · cases hx : xsign u
    · exact ⟨u, Equiv.Perm.SameCycle.refl _ _, hu, hx⟩
    · obtain ⟨n, -, hcR, ⟨m, hℓ⟩, -⟩ := hit_r hW u hu hx
      have hR : ((next hW)^[n] u).1 = (((next hW)^[n] u).1.1, 0) := Prod.ext rfl hcR
      refine ⟨next hW ((next hW)^[n] u), ?_, next_cusp_cut hW hcR, ?_⟩
      · have e : next hW ((next hW)^[n] u) = (next hW)^[n + 1] u := (Function.iterate_succ_apply' _ _ _).symm
        rw [e]
        exact sameCycle_of_iterate hW (s := u) (a := n + 1) (b := 0) rfl
      · rw [xsign_next_of_cut hW (next_cusp_cut hW hcR), xsign_cusp_r hR hℓ]

variable (hB : W.IsStandardCircleBase)
include hB

/-- The cycle of a left cusp `L` of a base word: the rightward run meets a right cusp `R`, the leftward
run from `R` returns to `L` (same label), and these are the only cusps of the cycle. -/
theorem cycle_cusps (L : Slot W) {k m : ℕ} {d : Bool} (hL : L.1 = (k, 0)) (hℓ : letterAt W k = .l m d) :
    ∃ R : Slot W, R.1.2 = 0 ∧ (∃ m', letterAt W R.1.1 = .r m') ∧ (nextPerm hW).SameCycle L R ∧
      ∀ v : Slot W, (nextPerm hW).SameCycle L v → v.1.2 = 0 → v = L ∨ v = R := by
  -- the rightward run from `L`
  have ha0 : (next hW L).1.2 ≠ 0 := next_cusp_cut hW (by rw [hL])
  have hxa : xsign (next hW L) = true := by
    rw [xsign_next_of_cut hW ha0, xsign_cusp_l hL hℓ]
  obtain ⟨n₁, hn₁, hR0, ⟨m', hℓR⟩, hcutA⟩ := hit_r hW (next hW L) ha0 hxa
  set R := (next hW)^[n₁] (next hW L) with hRdef
  have hRit : R = (next hW)^[n₁ + 1] L := by
    show (next hW)^[n₁] (next hW L) = _
    rw [Function.iterate_succ_apply]
  have hRs : R.1 = (R.1.1, 0) := Prod.ext rfl hR0
  -- the leftward run from `next R`
  have hb0 : (next hW R).1.2 ≠ 0 := next_cusp_cut hW hR0
  have hxb : xsign (next hW R) = false := by
    rw [xsign_next_of_cut hW hb0, xsign_cusp_r hRs hℓR]
  obtain ⟨n₂, hn₂, hL'0, ⟨m₂, d₂, hℓL'⟩, hcutB⟩ := hit_l hW (next hW R) hb0 hxb
  set L' := (next hW)^[n₂] (next hW R) with hL'def
  have hL'it : L' = (next hW)^[n₁ + n₂ + 2] L := by
    show (next hW)^[n₂] (next hW R) = _
    rw [hRit, ← Function.iterate_succ_apply' (next hW) (n₁ + 1) L, ← Function.iterate_add_apply]
    congr 1; omega
  -- `L' = L` by the label
  have hlabL' : lab L' = lab L := by rw [hL'it]; exact lab_iterate hW hB L _
  have hL's : L'.1 = (L'.1.1, 0) := Prod.ext rfl hL'0
  rw [lab_cusp_l hL's hℓL', lab_cusp_l hL hℓ] at hlabL'
  have hL'L : L' = L := Subtype.ext (by rw [hL's, hL, hlabL'])
  have hper : (next hW)^[n₁ + n₂ + 2] L = L := by rw [← hL'it, hL'L]
  refine ⟨R, hR0, ⟨m', hℓR⟩, sameCycle_of_iterate hW (s := L) (a := n₁ + 1) (b := 0) (by rw [← hRit]; rfl), ?_⟩
  intro v hcyc hv
  obtain ⟨j, hj⟩ := exists_iterate_of_sameCycle hW hcyc
  have hjmod : (next hW)^[j % (n₁ + n₂ + 2)] L = v := by
    rw [← hj]; exact Function.IsPeriodicPt.iterate_mod_apply hper j
  set j' := j % (n₁ + n₂ + 2) with hj'
  have hj'lt : j' < n₁ + n₂ + 2 := Nat.mod_lt _ (by omega)
  rcases Nat.eq_zero_or_pos j' with hj0 | hj0
  · left; rw [← hjmod, hj0]; rfl
  · by_cases hj1 : j' ≤ n₁ + 1
    · -- on the rightward run or at `R`
      rcases Nat.eq_or_lt_of_le hj1 with hje | hjl
      · right; rw [← hjmod, hje, ← hRit]
      · exfalso
        have := (hcutA (j' - 1) (by omega)).1
        rw [← Function.iterate_succ_apply (next hW) (j' - 1) L, Nat.succ_eq_add_one,
          show j' - 1 + 1 = j' by omega, hjmod] at this
        exact this hv
    · exfalso
      have := (hcutB (j' - (n₁ + 2)) (by omega)).1
      rw [hRit, ← Function.iterate_succ_apply' (next hW) (n₁ + 1) L, ← Function.iterate_add_apply,
        Nat.succ_eq_add_one, show j' - (n₁ + 2) + (n₁ + 1 + 1) = j' by omega, hjmod] at this
      exact this hv

end Cycles

/-! ## 4. The syntactic base realizes to a union of standard circles -/

section Assembly

variable (pl : Placement) {W : Word} (hW : W.Closed) (hne : W ≠ []) (hB : W.IsStandardCircleBase)
include hW hB

/-- The recorded obligation of `SM/FrontInterfaces.lean` R2, forward direction: a word of the syntactic
standard-circle base realizes to a union of standard circles. -/
theorem isStandardCircles_of_base : (realizeAt pl hW hne).IsStandardCircles := by
  refine ⟨⟨fun x => ?_⟩, fun i => ?_⟩
  · obtain ⟨m, hm⟩ := σIdx_letter (crossingEquiv pl hW hne x)
    exact no_σ_of_base hB (crossingEquiv pl hW hne x).1.2 hm
  · -- the left cusp of component `i`
    obtain ⟨L, hcyc, hL0, m, d, hℓ⟩ := exists_lcusp hW (slotOf pl hW hne ⟨i, 0⟩)
    have hLs : L.1 = (L.1.1, 0) := Prod.ext rfl hL0
    obtain ⟨R, hR0, ⟨m', hℓR⟩, hLR, huniq⟩ := cycle_cusps hW hB L hLs hℓ
    have hRs : R.1 = (R.1.1, 0) := Prod.ext rfl hR0
    have hcomp : ∀ s : (realizeAt pl hW hne).Γ.Strand, s.1 = i ↔ (nextPerm hW).SameCycle L (slotOf pl hW hne s) := by
      intro s
      have h1 : s.1 = i ↔ (nextPerm hW).SameCycle (slotOf pl hW hne ⟨i, 0⟩) (slotOf pl hW hne s) :=
        ⟨fun h => (toSlot_fst_eq_iff hW ⟨i, 0⟩ s).1 h.symm, fun h => ((toSlot_fst_eq_iff hW ⟨i, 0⟩ s).2 h).symm⟩
      rw [h1]
      exact ⟨fun h => hcyc.symm.trans h, fun h => hcyc.trans h⟩
    constructor
    · apply card_strand_slot pl hW hne L
      intro s
      rw [isLeftCusp_iff]
      constructor
      · rintro ⟨hsi, hc, m₁, d₁, hℓ₁⟩
        rcases huniq _ ((hcomp s).1 hsi) hc with h | h
        · exact h
        · exfalso; rw [h] at hℓ₁; rw [hℓR] at hℓ₁; cases hℓ₁
      · intro h
        refine ⟨(hcomp s).2 (by rw [h]), by rw [h]; exact hL0,
          by rw [h]; exact ⟨m, d, hℓ⟩⟩
    · apply card_strand_slot pl hW hne R
      intro s
      rw [isRightCusp_iff]
      constructor
      · rintro ⟨hsi, hc, m₁, hℓ₁⟩
        rcases huniq _ ((hcomp s).1 hsi) hc with h | h
        · exfalso; rw [h] at hℓ₁; rw [hℓ] at hℓ₁; cases hℓ₁
        · exact h
      · intro h
        refine ⟨(hcomp s).2 (by rw [h]; exact hLR), by rw [h]; exact hR0, by rw [h]; exact ⟨m', hℓR⟩⟩

/-- `D = c` on the syntactic base (row 81's `base_B`, geometric half). -/
theorem downCount_eq_c_of_base : (realizeAt pl hW hne).downCount = (realizeAt pl hW hne).Γ.c :=
  IsStandardCircles.downCount_eq_c pl hW hne (isStandardCircles_of_base pl hW hne hB)

end Assembly

end

end SM.FrontRealize

namespace SM

open SM.FrontWord SM.FrontRealize

/-- The forward direction of the recorded β2 obligation, on `SM.realize`. -/
theorem realize_isStandardCircles_of_base (W : OWord) (hB : W.IsStandardCircleBase) :
    (realize W).IsStandardCircles := by
  by_cases h : W.letters = []
  · exact realize_nil_isStandardCircles W h
  · rw [realize_eq_realizeAt W h]; exact isStandardCircles_of_base _ _ _ hB

/-- `D = c` on the syntactic base, on `SM.realize`. -/
theorem realize_downCount_eq_c_of_base (W : OWord) (hB : W.IsStandardCircleBase) :
    (realize W).downCount = (realize W).Γ.c := by
  by_cases h : W.letters = []
  · rw [realize_nil W h]
    exact IsStandardCircles.downCount_eq_c _ _ _ stdCircleWord_isStandardCircles
  · rw [realize_eq_realizeAt W h]; exact downCount_eq_c_of_base _ _ _ hB

/-- A principal chain for a smaller base is a principal chain for a larger base (same moves). -/
theorem Moves.Chain.mono_base (K : Moves) (Base' : K.α → Prop) (hb : ∀ F, K.Base F → Base' F) {F : K.α}
    (h : K.Chain F) : Moves.Chain { K with Base := Base' } F := by
  induction h with
  | base hF => exact Moves.Chain.base (hb _ hF)
  | del hd => exact Moves.Chain.del hd
  | pres hp _ ih => exact Moves.Chain.pres hp ih
  | skein hs _ ih => exact Moves.Chain.skein hs ih

/-- Transport of the finite-word statement from the syntactic base (the axiom's shape,
`ng_finite_word_finiteWordStatement`) to the geometric `wordMoves`: a chain stopping at a syntactic base word
stops at a geometric base word. -/
theorem finiteWordStatement_wordMoves_of
    (h : FiniteWordStatement (wordMovesOf (fun W => (realize W).sCount) (fun W => (realize W).defect)
      OWord.IsStandardCircleBase)) : FiniteWordStatement wordMoves := by
  intro W
  have this := Moves.Chain.mono_base
    (wordMovesOf (fun W => (realize W).sCount) (fun W => (realize W).defect) OWord.IsStandardCircleBase)
    (fun W : OWord => (realize W).IsStandardCircles) (fun F hF => realize_isStandardCircles_of_base F hF) (h W)
  exact this

end SM
