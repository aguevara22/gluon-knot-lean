import Mathlib.Data.List.GetD
import SM.FrontPL
import SM.FrontWords


/-! Ported 2026-09-14 05:50Z from work/drafts/front/FrontRealizeSlots.lean (front lane β2, grid realization of front words; report work/drafts/front/BETA2_REPORT.md). Library module (not a row): the PL realization `SM.realize : OWord → PLFront` and its correspondence with the word layer. Only this header added (one prose word reworded). -/
/-! Front block, lane β, unit β2 (2026-09-14): module `SM/FrontRealizeSlots.lean` (intended home).
Adopted design work/reports/front-block-design-FINAL-20260913.md (§2 G1, §4 `realize`, §7, §8 risk 3,
§9 FR-5); β1 report work/drafts/front/BETA1_REPORT.md §5.

# The grid realization, part 1: cuts, positions and the slot permutation of a closed word

A closed oriented Rutherford word `W = ℓ₀ ℓ₁ … ℓ_{n−1}` is realized on a grid: letter `ℓ_k` occupies
COLUMN `k`, the strands of the cut before it sit at the CUT LINE `k` at integer heights `−p` (position
`p`, 1-based from the top, so the top strand is highest), and every cusp letter has one CUSP VERTEX in the
open middle of its column.  The vertices of the realization are the *slots*:
* `(k, p)` with `p ≥ 1`: position `p` of the cut `k` (a strand passes the cut line there);
* `(k, 0)`: the cusp vertex of the cusp letter `ℓ_k`.

The oriented traversal visits the slots along `next`: a rightward strand at `(k, p)` enters column `k`
and, unless it is consumed by a right cusp, reappears at `(k+1, q)` where `q` is its position after the
letter (`Letter.posR`); a leftward strand enters column `k−1` symmetrically (`Letter.posL`); a left-cusp
vertex sends the traversal out along its rightward arm, a right-cusp vertex along its leftward arm.
`next` is a permutation of the finite slot set (`prev` is its inverse); the cycles of `next` are the
components of the realization (part 2, `SM/FrontRealize.lean`).

Conventions (documented for the review; the realization is a proof device, FR-5):
* cut `k` = `Word.run (W.take k) []`, the cut before letter `k`; `cut 0 = cut n = []` for a closed word;
* `bit k p` = the rightward bit of position `p` at cut `k` (`true` = travels rightward);
* the two strands of a crossing letter `σ_m` exchange positions `m ↔ m+1` and keep their bits;
* a left cusp `l_m d` puts its upper arm (position `m`) rightward iff `d`; a right cusp `r_m` is entered
  on its rightward arm and left on its leftward arm.

All declarations live in `SM.FrontRealize`; the position maps `posR`/`posL` in `SM.FrontWord.Letter`.
Checked with `lake env lean` (placeholder-free, standard axioms). -/

/-! ## 0. The position maps of a letter (in `SM.FrontWord.Letter`) -/

namespace SM.FrontWord.Letter

/-- The position after the letter of the strand at position `p` before it (`none`: consumed by a
right cusp).  Strands above the letter keep their position, strands below shift by the letter's
strand-count change, the two strands of a crossing exchange positions. -/
def posR (ℓ : Letter) (p : ℕ) : Option ℕ :=
  if p < ℓ.idx then some p
  else if p < ℓ.idx + ℓ.arity then
    match ℓ with
    | .σ m => some (if p = m then m + 1 else m)
    | _ => none
  else some (p + ℓ.coarity - ℓ.arity)

/-- The position before the letter of the strand at position `q` after it (`none`: created by a left
cusp). -/
def posL (ℓ : Letter) (q : ℕ) : Option ℕ :=
  if q < ℓ.idx then some q
  else if q < ℓ.idx + ℓ.coarity then
    match ℓ with
    | .σ m => some (if q = m then m + 1 else m)
    | _ => none
  else some (q + ℓ.arity - ℓ.coarity)

theorem posR_of_lt {ℓ : Letter} {p : ℕ} (h : p < ℓ.idx) : ℓ.posR p = some p := by
  unfold posR; rw [ite_eq_left h]

theorem posL_of_lt {ℓ : Letter} {q : ℕ} (h : q < ℓ.idx) : ℓ.posL q = some q := by
  unfold posL; rw [ite_eq_left h]

theorem posR_of_ge {ℓ : Letter} {p : ℕ} (h : ℓ.idx + ℓ.arity ≤ p) : ℓ.posR p = some (p + ℓ.coarity - ℓ.arity) := by
  unfold posR; rw [ite_eq_right (by omega), ite_eq_right (by omega)]

theorem posL_of_ge {ℓ : Letter} {q : ℕ} (h : ℓ.idx + ℓ.coarity ≤ q) : ℓ.posL q = some (q + ℓ.arity - ℓ.coarity) := by
  unfold posL; rw [ite_eq_right (by omega), ite_eq_right (by omega)]

@[simp] theorem posR_l (m : ℕ) (d : Bool) (p : ℕ) : (Letter.l m d).posR p = if p < m then some p else some (p + 2) := by
  unfold posR; by_cases h : p < m <;> simp [idx, arity, coarity, h]

@[simp] theorem posL_r (m : ℕ) (q : ℕ) : (Letter.r m).posL q = if q < m then some q else some (q + 2) := by
  unfold posL; by_cases h : q < m <;> simp [idx, arity, coarity, h]

theorem posR_r (m p : ℕ) : (Letter.r m).posR p =
    if p < m then some p else if p < m + 2 then none else some (p - 2) := by
  unfold posR; simp [idx, arity, coarity]

theorem posL_l (m : ℕ) (d : Bool) (q : ℕ) : (Letter.l m d).posL q =
    if q < m then some q else if q < m + 2 then none else some (q - 2) := by
  unfold posL; simp [idx, arity, coarity]

theorem posR_σ (m p : ℕ) : (Letter.σ m).posR p =
    if p < m then some p else if p < m + 2 then some (if p = m then m + 1 else m) else some p := by
  unfold posR; simp [idx, arity, coarity]

theorem posL_σ (m q : ℕ) : (Letter.σ m).posL q =
    if q < m then some q else if q < m + 2 then some (if q = m then m + 1 else m) else some q := by
  unfold posL; simp [idx, arity, coarity]

theorem posR_σ_idx (m : ℕ) : (Letter.σ m).posR m = some (m + 1) := by simp [posR_σ]
theorem posR_σ_idx_succ (m : ℕ) : (Letter.σ m).posR (m + 1) = some m := by simp [posR_σ]
theorem posL_σ_idx (m : ℕ) : (Letter.σ m).posL m = some (m + 1) := by simp [posL_σ]
theorem posL_σ_idx_succ (m : ℕ) : (Letter.σ m).posL (m + 1) = some m := by simp [posL_σ]

theorem posR_r_idx (m : ℕ) : (Letter.r m).posR m = none := by simp [posR_r]
theorem posR_r_idx_succ (m : ℕ) : (Letter.r m).posR (m + 1) = none := by simp [posR_r]
theorem posL_l_idx (m : ℕ) (d : Bool) : (Letter.l m d).posL m = none := by simp [posL_l]
theorem posL_l_idx_succ (m : ℕ) (d : Bool) : (Letter.l m d).posL (m + 1) = none := by simp [posL_l]

/-- `posR` never returns `none` for a crossing or a left cusp. -/
theorem posR_isSome_of_not_r {ℓ : Letter} (h : ∀ m, ℓ ≠ .r m) (p : ℕ) : (ℓ.posR p).isSome := by
  cases ℓ with
  | l m d => simp [posR_l]; split_ifs <;> rfl
  | r m => exact absurd rfl (h m)
  | σ m => rw [posR_σ]; split_ifs <;> rfl

theorem posL_isSome_of_not_l {ℓ : Letter} (h : ∀ m d, ℓ ≠ .l m d) (q : ℕ) : (ℓ.posL q).isSome := by
  cases ℓ with
  | l m d => exact absurd rfl (h m d)
  | r m => simp [posL_r]; split_ifs <;> rfl
  | σ m => rw [posL_σ]; split_ifs <;> rfl

theorem posR_eq_none_iff {ℓ : Letter} {p : ℕ} : ℓ.posR p = none ↔ ∃ m, ℓ = .r m ∧ (p = m ∨ p = m + 1) := by
  cases ℓ with
  | l m d => simp only [posR_l]; constructor
             · intro h; split_ifs at h
             · rintro ⟨m', h, -⟩; cases h
  | r m => rw [posR_r]; constructor
           · intro h
             by_cases h1 : p < m
             · rw [ite_eq_left h1] at h; simp at h
             · by_cases h2 : p < m + 2
               · exact ⟨m, rfl, by omega⟩
               · rw [ite_eq_right h1, ite_eq_right h2] at h; simp at h
           · rintro ⟨m', hm, hp⟩; cases hm; rw [ite_eq_right (by omega), ite_eq_left (by omega)]
  | σ m => rw [posR_σ]; constructor
           · intro h; split_ifs at h
           · rintro ⟨m', h, -⟩; cases h

theorem posL_eq_none_iff {ℓ : Letter} {q : ℕ} : ℓ.posL q = none ↔ ∃ m d, ℓ = .l m d ∧ (q = m ∨ q = m + 1) := by
  cases ℓ with
  | l m d => rw [posL_l]; constructor
             · intro h
               by_cases h1 : q < m
               · rw [ite_eq_left h1] at h; simp at h
               · by_cases h2 : q < m + 2
                 · exact ⟨m, d, rfl, by omega⟩
                 · rw [ite_eq_right h1, ite_eq_right h2] at h; simp at h
             · rintro ⟨m', d', hm, hq⟩; cases hm; rw [ite_eq_right (by omega), ite_eq_left (by omega)]
  | r m => simp only [posL_r]; constructor
           · intro h; split_ifs at h
           · rintro ⟨m', d', h, -⟩; cases h
  | σ m => rw [posL_σ]; constructor
           · intro h; split_ifs at h
           · rintro ⟨m', d', h, -⟩; cases h

end SM.FrontWord.Letter

namespace SM.FrontRealize

open SM.FrontWord SM.FrontWord.Letter SM.FrontWord.Word

/-! ## 1. Cuts and letters of a closed word -/

section Cuts

variable (W : Word)

/-- The cut before column `k`: the strands (rightward bits, top to bottom) after the first `k` letters,
read from the empty cut.  (`[]` if the prefix is untyped; for a closed word every prefix is typed.) -/
def cut (k : ℕ) : Cuts := (Word.run (W.take k) []).getD []

/-- The letter of column `k` (junk beyond the word). -/
def letterAt (k : ℕ) : Letter := W.getD k (.l 0 false)

/-- The rightward bit of position `p` (1-based) at cut `k`. -/
def bit (k p : ℕ) : Bool := (cut W k).getD (p - 1) false

/-- The number of strands at cut `k`. -/
def cutLen (k : ℕ) : ℕ := (cut W k).length

@[simp] theorem cut_zero : cut W 0 = [] := by simp [cut]

theorem exists_run_take (hW : W.Closed) (k : ℕ) : ∃ c, Word.run (W.take k) [] = some c := by
  unfold Closed at hW
  rw [← List.take_append_drop k W, run_append] at hW
  obtain ⟨c, hc, -⟩ := Option.bind_eq_some_iff.1 hW
  exact ⟨c, hc⟩

theorem run_take (hW : W.Closed) (k : ℕ) : Word.run (W.take k) [] = some (cut W k) := by
  obtain ⟨c, hc⟩ := exists_run_take W hW k
  rw [cut, hc]; rfl

theorem cut_of_length_le {k : ℕ} (hk : W.length ≤ k) : cut W k = cut W W.length := by
  simp [cut, List.take_of_length_le hk]

theorem cut_length (hW : W.Closed) : cut W W.length = [] := by
  have := run_take W hW W.length
  rw [List.take_length] at this
  unfold Closed at hW
  rw [hW] at this
  exact (Option.some.inj this).symm

theorem cut_eq_nil_of_le (hW : W.Closed) {k : ℕ} (hk : W.length ≤ k) : cut W k = [] := by
  rw [cut_of_length_le W hk, cut_length W hW]

theorem letterAt_eq {k : ℕ} (hk : k < W.length) : letterAt W k = W[k] := by
  simp [letterAt, List.getD_eq_getElem?_getD, hk]

/-- The letter of column `k` is typed at cut `k` and produces cut `k+1`. -/
theorem step_cut (hW : W.Closed) {k : ℕ} (hk : k < W.length) :
    (letterAt W k).step (cut W k) = some (cut W (k + 1)) := by
  have h1 := run_take W hW k
  have h2 := run_take W hW (k + 1)
  rw [List.take_succ_eq_append_getElem hk, run_append, h1, Option.bind_some, run_singleton,
    ← letterAt_eq W hk] at h2
  exact h2

/-- Each letter adds at most two strands. -/
theorem length_run_le : ∀ (V : Word) (c c' : Cuts), Word.run V c = some c' → c'.length ≤ c.length + 2 * V.length := by
  intro V
  induction V with
  | nil => intro c c' h; simp at h; subst h; simp
  | cons a V ih =>
    intro c c' h
    rw [run_cons] at h
    obtain ⟨c₁, h1, h2⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨A, L, L', -, -, rfl, hL, rfl⟩ := step_eq_some_iff.1 h1
    obtain ⟨w, w', R, rfl, hw, -, hw'len, rfl⟩ := act_window hL
    have := ih _ _ h2
    have hco : a.coarity ≤ 2 := by cases a <;> simp [coarity]
    simp only [List.length_append, List.length_cons] at this ⊢
    omega

theorem cutLen_le (k : ℕ) : cutLen W k ≤ 2 * k := by
  unfold cutLen cut
  cases h : Word.run (W.take k) [] with
  | none => simp
  | some c =>
    have := length_run_le (W.take k) [] c h
    simp only [List.length_nil, zero_add, List.length_take] at this
    simp only [Option.getD_some]
    omega

end Cuts

/-! ## 2. The position maps of a letter and the transport of bits across a column -/



/-! ### The decomposition of a typed step -/

/-- A typed step `ℓ.step c = some c'` decomposed: `c = A ++ w ++ R`, `c' = A ++ w' ++ R` with `|A| = m − 1`
(the strands above the letter), `w` the `arity` strands the letter reads, `w'` the `coarity` strands it
writes, `R` the strands below. -/
structure StepDecomp (ℓ : Letter) (c c' : Cuts) where
  A : Cuts
  w : Cuts
  w' : Cuts
  R : Cuts
  hm : 1 ≤ ℓ.idx
  hA : A.length = ℓ.idx - 1
  hw : w.length = ℓ.arity
  hw' : w'.length = ℓ.coarity
  hact : ℓ.act w = some w'
  hc : c = A ++ w ++ R
  hc' : c' = A ++ w' ++ R

theorem stepDecomp_of {ℓ : Letter} {c c' : Cuts} (h : ℓ.step c = some c') : Nonempty (StepDecomp ℓ c c') := by
  obtain ⟨A, L, L', h1, hA, rfl, hL, rfl⟩ := step_eq_some_iff.1 h
  obtain ⟨w, w', R, rfl, hw, hw', hw'len, rfl⟩ := act_window hL
  exact ⟨⟨A, w, w', R, h1, hA, hw, hw'len, hw', by simp, by simp⟩⟩

namespace StepDecomp

variable {ℓ : Letter} {c c' : Cuts}

theorem length_c (D : StepDecomp ℓ c c') : c.length = ℓ.idx - 1 + ℓ.arity + D.R.length := by
  obtain ⟨A, w, w', R, hm, hA, hw, hw', hact, rfl, rfl⟩ := D
  simp [hA, hw]; omega

theorem length_c' (D : StepDecomp ℓ c c') : c'.length = ℓ.idx - 1 + ℓ.coarity + D.R.length := by
  obtain ⟨A, w, w', R, hm, hA, hw, hw', hact, rfl, rfl⟩ := D
  simp [hA, hw']; omega

theorem length_add (D : StepDecomp ℓ c c') : c'.length + ℓ.arity = c.length + ℓ.coarity := by
  rw [D.length_c, D.length_c']; ring

/-- Strands above the letter keep their bits. -/
theorem getD_above (D : StepDecomp ℓ c c') {p : ℕ} (hp1 : 1 ≤ p) (hp : p < ℓ.idx) :
    c'.getD (p - 1) false = c.getD (p - 1) false := by
  obtain ⟨A, w, w', R, hm, hA, hw, hw', hact, rfl, rfl⟩ := D
  rw [List.append_assoc, List.append_assoc, List.getD_append _ _ _ _ (by rw [hA]; omega),
    List.getD_append _ _ _ _ (by rw [hA]; omega)]

/-- Strands below the letter keep their bits (shifted by the strand-count change). -/
theorem getD_below (D : StepDecomp ℓ c c') {p : ℕ} (hp : ℓ.idx + ℓ.arity ≤ p) :
    c'.getD (p + ℓ.coarity - ℓ.arity - 1) false = c.getD (p - 1) false := by
  obtain ⟨A, w, w', R, hm, hA, hw, hw', hact, rfl, rfl⟩ := D
  rw [List.getD_append_right _ _ _ _ (by simp [hA, hw]; omega),
    List.getD_append_right _ _ _ _ (by simp [hA, hw']; omega)]
  congr 1
  simp only [List.length_append, hA, hw, hw']
  omega

theorem getD_above' (D : StepDecomp ℓ c c') {p : ℕ} (hp1 : 1 ≤ p) (hp : p < ℓ.idx) :
    c.getD (p - 1) false = c'.getD (p - 1) false :=
  (D.getD_above hp1 hp).symm

/-- the read window of a left cusp is empty and it writes `[d, !d]` -/
theorem w_l {m : ℕ} {d : Bool} (D : StepDecomp (.l m d) c c') : D.w = [] ∧ D.w' = [d, !d] := by
  have hw := D.hw
  have hact := D.hact
  simp only [arity] at hw
  have hw0 : D.w = [] := List.eq_nil_of_length_eq_zero hw
  rw [hw0] at hact
  simp only [act_l, Option.some.injEq] at hact
  exact ⟨hw0, hact.symm⟩

/-- a right cusp reads two strands of opposite bits and writes nothing -/
theorem w_r {m : ℕ} (D : StepDecomp (.r m) c c') : ∃ a b : Bool, a ≠ b ∧ D.w = [a, b] ∧ D.w' = [] := by
  have hact := D.hact
  have hw'0 : D.w' = [] := by
    have := D.hw'
    simp only [coarity] at this
    exact List.eq_nil_of_length_eq_zero this
  obtain ⟨a, b, hw, hab⟩ := act_r_eq_some_iff.1 hact
  rw [hw'0] at hw
  exact ⟨a, b, hab, hw, hw'0⟩

/-- a crossing exchanges two strands -/
theorem w_σ {m : ℕ} (D : StepDecomp (.σ m) c c') : ∃ a b : Bool, D.w = [a, b] ∧ D.w' = [b, a] := by
  have hact := D.hact
  obtain ⟨a, b, L₀, hw, hw'⟩ := act_σ_eq_some_iff.1 hact
  have hwl := D.hw
  rw [hw] at hwl
  simp only [arity, List.length_cons] at hwl
  have : L₀ = [] := List.eq_nil_of_length_eq_zero (by omega)
  subst this
  exact ⟨a, b, hw, hw'⟩

/-- the bits written by a left cusp -/
theorem bits_l {m : ℕ} {d : Bool} (D : StepDecomp (.l m d) c c') :
    c'.getD (m - 1) false = d ∧ c'.getD m false = !d ∧ m + 1 ≤ c'.length := by
  obtain ⟨-, hw'⟩ := D.w_l
  obtain ⟨A, w, w', R, hm, hA, hwl, hw'l, hact, rfl, rfl⟩ := D
  simp only [idx] at hA hm
  simp only at hw'
  subst hw'
  refine ⟨?_, ?_, ?_⟩
  · rw [List.append_assoc, List.getD_append_right _ _ _ _ (by omega),
      show m - 1 - A.length = 0 by omega]; rfl
  · rw [List.append_assoc, List.getD_append_right _ _ _ _ (by omega),
      show m - A.length = 1 by omega]; rfl
  · simp; omega

/-- the bits read by a right cusp -/
theorem bits_r {m : ℕ} (D : StepDecomp (.r m) c c') :
    c.getD (m - 1) false ≠ c.getD m false ∧ m + 1 ≤ c.length := by
  obtain ⟨a, b, hab, hw, -⟩ := D.w_r
  obtain ⟨A, w, w', R, hm, hA, hwl, hw'l, hact, rfl, rfl⟩ := D
  simp only [idx] at hA hm
  simp only at hw
  subst hw
  have h1 : (A ++ ([a, b] ++ R)).getD (m - 1) false = a := by
    rw [List.getD_append_right _ _ _ _ (by omega), show m - 1 - A.length = 0 by omega]; rfl
  have h2 : (A ++ ([a, b] ++ R)).getD m false = b := by
    rw [List.getD_append_right _ _ _ _ (by omega), show m - A.length = 1 by omega]; rfl
  rw [List.append_assoc, h1, h2]
  refine ⟨hab, ?_⟩
  simp; omega

/-- the bits exchanged by a crossing -/
theorem bits_σ {m : ℕ} (D : StepDecomp (.σ m) c c') :
    c'.getD m false = c.getD (m - 1) false ∧ c'.getD (m - 1) false = c.getD m false ∧
    m + 1 ≤ c.length ∧ c'.length = c.length := by
  obtain ⟨a, b, hw, hw'⟩ := D.w_σ
  obtain ⟨A, w, w', R, hm, hA, hwl, hw'l, hact, rfl, rfl⟩ := D
  simp only [idx] at hA hm
  simp only at hw hw'
  subst hw hw'
  have h1 : (A ++ ([a, b] ++ R)).getD (m - 1) false = a := by
    rw [List.getD_append_right _ _ _ _ (by omega), show m - 1 - A.length = 0 by omega]; rfl
  have h2 : (A ++ ([a, b] ++ R)).getD m false = b := by
    rw [List.getD_append_right _ _ _ _ (by omega), show m - A.length = 1 by omega]; rfl
  have h1' : (A ++ ([b, a] ++ R)).getD (m - 1) false = b := by
    rw [List.getD_append_right _ _ _ _ (by omega), show m - 1 - A.length = 0 by omega]; rfl
  have h2' : (A ++ ([b, a] ++ R)).getD m false = a := by
    rw [List.getD_append_right _ _ _ _ (by omega), show m - A.length = 1 by omega]; rfl
  rw [List.append_assoc, List.append_assoc, h1, h2, h1', h2']
  refine ⟨rfl, rfl, ?_, ?_⟩
  · simp; omega
  · simp

/-- Transport of a strand through a column, left to right: its position after the letter is in range,
its bit is unchanged, and `posL` brings it back. -/
theorem posR_some (D : StepDecomp ℓ c c') {p q : ℕ} (hp : 1 ≤ p) (hpc : p ≤ c.length)
    (hq : ℓ.posR p = some q) :
    1 ≤ q ∧ q ≤ c'.length ∧ c'.getD (q - 1) false = c.getD (p - 1) false ∧ ℓ.posL q = some p := by
  have hlen := D.length_add
  have hlc := D.length_c
  have hlc' := D.length_c'
  have hm := D.hm
  unfold posR at hq
  split_ifs at hq with h1 h2
  · obtain rfl := Option.some.inj hq
    exact ⟨hp, by omega, D.getD_above hp h1, posL_of_lt h1⟩
  · -- the gadget: only a crossing survives here
    cases ℓ with
    | l m d => simp [arity] at h2; omega
    | r m => simp at hq
    | σ m =>
      simp only [Option.some.injEq] at hq
      obtain ⟨hb1, hb2, hmc, hcc⟩ := D.bits_σ
      simp only [idx, arity] at h1 h2 hm
      subst hq
      by_cases hpm : p = m
      · subst hpm
        rw [ite_eq_left rfl]
        refine ⟨by omega, by omega, ?_, posL_σ_idx_succ p⟩
        rw [show p + 1 - 1 = p by omega]; exact hb1
      · have hpm' : p = m + 1 := by omega
        subst hpm'
        rw [ite_eq_right (by omega)]
        refine ⟨by omega, by omega, ?_, posL_σ_idx m⟩
        rw [show m + 1 - 1 = m by omega]; exact hb2
  · obtain rfl := Option.some.inj hq
    refine ⟨by omega, by omega, D.getD_below (by omega), ?_⟩
    rw [posL_of_ge (by omega)]
    congr 1
    omega

/-- Transport of a strand through a column, right to left. -/
theorem posL_some (D : StepDecomp ℓ c c') {p q : ℕ} (hq : 1 ≤ q) (hqc : q ≤ c'.length)
    (hp : ℓ.posL q = some p) :
    1 ≤ p ∧ p ≤ c.length ∧ c.getD (p - 1) false = c'.getD (q - 1) false ∧ ℓ.posR p = some q := by
  have hlen := D.length_add
  have hlc := D.length_c
  have hlc' := D.length_c'
  have hm := D.hm
  unfold posL at hp
  split_ifs at hp with h1 h2
  · obtain rfl := Option.some.inj hp
    exact ⟨hq, by omega, D.getD_above' hq h1, posR_of_lt h1⟩
  · cases ℓ with
    | l m d => simp at hp
    | r m => simp [coarity] at h2; omega
    | σ m =>
      simp only [Option.some.injEq] at hp
      obtain ⟨hb1, hb2, hmc, hcc⟩ := D.bits_σ
      simp only [idx, coarity] at h1 h2 hm
      subst hp
      by_cases hqm : q = m
      · subst hqm
        rw [ite_eq_left rfl]
        refine ⟨by omega, by omega, ?_, posR_σ_idx_succ q⟩
        rw [show q + 1 - 1 = q by omega]; exact hb2.symm
      · have hqm' : q = m + 1 := by omega
        subst hqm'
        rw [ite_eq_right (by omega)]
        refine ⟨by omega, by omega, ?_, posR_σ_idx m⟩
        rw [show m + 1 - 1 = m by omega]; exact hb1.symm
  · obtain rfl := Option.some.inj hp
    have hb := D.getD_below (p := q + ℓ.arity - ℓ.coarity) (by omega)
    rw [show q + ℓ.arity - ℓ.coarity + ℓ.coarity - ℓ.arity = q by omega] at hb
    refine ⟨by omega, by omega, hb.symm, ?_⟩
    rw [posR_of_ge (by omega)]
    congr 1
    omega

end StepDecomp

/-! ## 3. Slots and the successor permutation -/

section Slots

variable (W : Word)

/-- `(k, 0)` is the cusp vertex of the cusp letter of column `k`; `(k, p)` with `p ≥ 1` is position `p`
of the cut `k` (the point where the strand at that position passes the cut line). -/
def IsSlot (s : ℕ × ℕ) : Prop :=
  (s.2 = 0 ∧ s.1 < W.length ∧ (letterAt W s.1).isCrossing = false) ∨
  (1 ≤ s.2 ∧ s.2 ≤ (cut W s.1).length ∧ s.1 ≤ W.length)

instance : DecidablePred (IsSlot W) := fun s => by unfold IsSlot; infer_instance

/-- The slots (vertices) of the realization of `W`. -/
abbrev Slot := {s : ℕ × ℕ // IsSlot W s}

theorem isSlot_bound {s : ℕ × ℕ} (h : IsSlot W s) : s.1 ≤ W.length ∧ s.2 ≤ 2 * W.length := by
  rcases h with ⟨h0, hk, -⟩ | ⟨-, hp, hk⟩
  · exact ⟨hk.le, by omega⟩
  · have := cutLen_le W s.1
    unfold cutLen at this
    exact ⟨hk, by omega⟩

instance : Finite (Slot W) := by
  apply Finite.of_injective (fun s : Slot W =>
    ((⟨s.1.1, Nat.lt_succ_of_le (isSlot_bound W s.2).1⟩ : Fin (W.length + 1)),
      (⟨s.1.2, Nat.lt_succ_of_le (isSlot_bound W s.2).2⟩ : Fin (2 * W.length + 1))))
  intro s t h
  simp only [Prod.mk.injEq, Fin.mk.injEq] at h
  exact Subtype.ext (Prod.ext h.1 h.2)

noncomputable instance : Fintype (Slot W) := Fintype.ofFinite _

/-- The successor of a slot along the oriented traversal (see the module docstring). -/
def nextPair (s : ℕ × ℕ) : ℕ × ℕ :=
  if s.2 = 0 then
    match letterAt W s.1 with
    | .l m d => (s.1 + 1, if d then m else m + 1)
    | .r m => (s.1, if bit W s.1 m then m + 1 else m)
    | .σ _ => s
  else if bit W s.1 s.2 then
    match (letterAt W s.1).posR s.2 with
    | some q => (s.1 + 1, q)
    | none => (s.1, 0)
  else
    match (letterAt W (s.1 - 1)).posL s.2 with
    | some q => (s.1 - 1, q)
    | none => (s.1 - 1, 0)

/-- The predecessor of a slot along the oriented traversal. -/
def prevPair (s : ℕ × ℕ) : ℕ × ℕ :=
  if s.2 = 0 then
    match letterAt W s.1 with
    | .l m d => (s.1 + 1, if d then m + 1 else m)
    | .r m => (s.1, if bit W s.1 m then m else m + 1)
    | .σ _ => s
  else if bit W s.1 s.2 then
    match (letterAt W (s.1 - 1)).posL s.2 with
    | some q => (s.1 - 1, q)
    | none => (s.1 - 1, 0)
  else
    match (letterAt W s.1).posR s.2 with
    | some q => (s.1 + 1, q)
    | none => (s.1, 0)

theorem nextPair_cusp_l {k m : ℕ} {d : Bool} (h : letterAt W k = .l m d) :
    nextPair W (k, 0) = (k + 1, if d then m else m + 1) := by simp [nextPair, h]

theorem nextPair_cusp_r {k m : ℕ} (h : letterAt W k = .r m) :
    nextPair W (k, 0) = (k, if bit W k m then m + 1 else m) := by simp [nextPair, h]

theorem nextPair_right {k p q : ℕ} (hp : p ≠ 0) (hb : bit W k p = true)
    (hq : (letterAt W k).posR p = some q) : nextPair W (k, p) = (k + 1, q) := by
  simp [nextPair, hp, hb, hq]

theorem nextPair_right_none {k p : ℕ} (hp : p ≠ 0) (hb : bit W k p = true)
    (hq : (letterAt W k).posR p = none) : nextPair W (k, p) = (k, 0) := by
  simp [nextPair, hp, hb, hq]

theorem nextPair_left {k p q : ℕ} (hp : p ≠ 0) (hb : bit W k p = false)
    (hq : (letterAt W (k - 1)).posL p = some q) : nextPair W (k, p) = (k - 1, q) := by
  simp [nextPair, hp, hb, hq]

theorem nextPair_left_none {k p : ℕ} (hp : p ≠ 0) (hb : bit W k p = false)
    (hq : (letterAt W (k - 1)).posL p = none) : nextPair W (k, p) = (k - 1, 0) := by
  simp [nextPair, hp, hb, hq]

theorem prevPair_cusp_l {k m : ℕ} {d : Bool} (h : letterAt W k = .l m d) :
    prevPair W (k, 0) = (k + 1, if d then m + 1 else m) := by simp [prevPair, h]

theorem prevPair_cusp_r {k m : ℕ} (h : letterAt W k = .r m) :
    prevPair W (k, 0) = (k, if bit W k m then m else m + 1) := by simp [prevPair, h]

theorem prevPair_right {k p q : ℕ} (hp : p ≠ 0) (hb : bit W k p = true)
    (hq : (letterAt W (k - 1)).posL p = some q) : prevPair W (k, p) = (k - 1, q) := by
  simp [prevPair, hp, hb, hq]

theorem prevPair_right_none {k p : ℕ} (hp : p ≠ 0) (hb : bit W k p = true)
    (hq : (letterAt W (k - 1)).posL p = none) : prevPair W (k, p) = (k - 1, 0) := by
  simp [prevPair, hp, hb, hq]

theorem prevPair_left {k p q : ℕ} (hp : p ≠ 0) (hb : bit W k p = false)
    (hq : (letterAt W k).posR p = some q) : prevPair W (k, p) = (k + 1, q) := by
  simp [prevPair, hp, hb, hq]

theorem prevPair_left_none {k p : ℕ} (hp : p ≠ 0) (hb : bit W k p = false)
    (hq : (letterAt W k).posR p = none) : prevPair W (k, p) = (k, 0) := by
  simp [prevPair, hp, hb, hq]

theorem bit_succ (k m : ℕ) : bit W k (m + 1) = (cut W k).getD m false := by simp [bit]

theorem bit_eq (k m : ℕ) : bit W k m = (cut W k).getD (m - 1) false := rfl

end Slots

/-! ### Facts for a closed word -/

section Closed

variable {W : Word} (hW : W.Closed)
include hW

/-- Cut slots lie strictly between the first and the last cut line. -/
theorem cutSlot_pos {k p : ℕ} (hp : 1 ≤ p) (hpk : p ≤ (cut W k).length) : 0 < k ∧ k < W.length := by
  constructor
  · rcases Nat.eq_zero_or_pos k with rfl | h
    · simp at hpk; omega
    · exact h
  · by_contra h
    rw [not_lt] at h
    rw [cut_eq_nil_of_le W hW h] at hpk
    simp at hpk; omega

/-- The step decomposition of column `k`. -/
theorem decomp (k : ℕ) (hk : k < W.length) :
    Nonempty (StepDecomp (letterAt W k) (cut W k) (cut W (k + 1))) :=
  stepDecomp_of (step_cut W hW hk)

/-- The first letter of a nonempty closed word is `l 1 d`. -/
theorem letterAt_zero (hne : W ≠ []) : ∃ d, letterAt W 0 = .l 1 d := by
  have hk : 0 < W.length := List.length_pos_of_ne_nil hne
  have h := step_cut W hW hk
  rw [cut_zero] at h
  obtain ⟨A, L, L', h1, hA, hAL, hL, -⟩ := step_eq_some_iff.1 h
  have hA0 : A = [] := List.eq_nil_of_append_eq_nil hAL.symm |>.1
  have hL0 : L = [] := List.eq_nil_of_append_eq_nil hAL.symm |>.2
  subst hL0
  cases hℓ : letterAt W 0 with
  | l m d =>
    refine ⟨d, ?_⟩
    rw [hℓ] at hA h1
    simp only [idx] at hA h1
    rw [hA0] at hA
    simp at hA
    congr 1
    omega
  | r m => rw [hℓ] at hL; simp [act] at hL
  | σ m => rw [hℓ] at hL; simp [act] at hL

theorem isSlot_nextPair {s : ℕ × ℕ} (hs : IsSlot W s) : IsSlot W (nextPair W s) := by
  obtain ⟨k, p⟩ := s
  rcases hs with ⟨hp0, hk, hσ⟩ | ⟨hp1, hpk, hkn⟩
  · simp only at hp0 hk hσ
    subst hp0
    obtain ⟨D⟩ := decomp hW k hk
    cases hℓ : letterAt W k with
    | l m d =>
      rw [hℓ] at D
      obtain ⟨hb1, hb2, hlen⟩ := D.bits_l
      have hm := D.hm
      simp only [idx] at hm
      rw [nextPair_cusp_l W hℓ]
      right
      dsimp only
      refine ⟨?_, ?_, by omega⟩ <;> split_ifs <;> omega
    | r m =>
      rw [hℓ] at D
      obtain ⟨hne, hlen⟩ := D.bits_r
      have hm := D.hm
      simp only [idx] at hm
      rw [nextPair_cusp_r W hℓ]
      right
      dsimp only
      refine ⟨?_, ?_, by omega⟩ <;> split_ifs <;> omega
    | σ m => rw [hℓ] at hσ; simp [isCrossing] at hσ
  · simp only at hp1 hpk hkn
    obtain ⟨hk0, hkn'⟩ := cutSlot_pos hW hp1 hpk
    cases hb : bit W k p with
    | true =>
      obtain ⟨D⟩ := decomp hW k hkn'
      cases hq : (letterAt W k).posR p with
      | some q =>
        rw [nextPair_right W (by omega) hb hq]
        obtain ⟨hq1, hq2, -, -⟩ := D.posR_some hp1 hpk hq
        right; exact ⟨hq1, hq2, by omega⟩
      | none =>
        rw [nextPair_right_none W (by omega) hb hq]
        obtain ⟨m, hm, -⟩ := posR_eq_none_iff.1 hq
        left; exact ⟨rfl, hkn', by rw [hm]; rfl⟩
    | false =>
      obtain ⟨D⟩ := decomp hW (k - 1) (by omega)
      rw [show k - 1 + 1 = k by omega] at D
      cases hq : (letterAt W (k - 1)).posL p with
      | some q =>
        rw [nextPair_left W (by omega) hb hq]
        obtain ⟨hq1, hq2, -, -⟩ := D.posL_some hp1 hpk hq
        right; exact ⟨hq1, hq2, by omega⟩
      | none =>
        rw [nextPair_left_none W (by omega) hb hq]
        obtain ⟨m, d, hm, -⟩ := posL_eq_none_iff.1 hq
        left; exact ⟨rfl, by omega, by rw [hm]; rfl⟩

theorem isSlot_prevPair {s : ℕ × ℕ} (hs : IsSlot W s) : IsSlot W (prevPair W s) := by
  obtain ⟨k, p⟩ := s
  rcases hs with ⟨hp0, hk, hσ⟩ | ⟨hp1, hpk, hkn⟩
  · simp only at hp0 hk hσ
    subst hp0
    obtain ⟨D⟩ := decomp hW k hk
    cases hℓ : letterAt W k with
    | l m d =>
      rw [hℓ] at D
      obtain ⟨hb1, hb2, hlen⟩ := D.bits_l
      have hm := D.hm
      simp only [idx] at hm
      rw [prevPair_cusp_l W hℓ]
      right
      dsimp only
      refine ⟨?_, ?_, by omega⟩ <;> split_ifs <;> omega
    | r m =>
      rw [hℓ] at D
      obtain ⟨hne, hlen⟩ := D.bits_r
      have hm := D.hm
      simp only [idx] at hm
      rw [prevPair_cusp_r W hℓ]
      right
      dsimp only
      refine ⟨?_, ?_, by omega⟩ <;> split_ifs <;> omega
    | σ m => rw [hℓ] at hσ; simp [isCrossing] at hσ
  · simp only at hp1 hpk hkn
    obtain ⟨hk0, hkn'⟩ := cutSlot_pos hW hp1 hpk
    cases hb : bit W k p with
    | true =>
      obtain ⟨D⟩ := decomp hW (k - 1) (by omega)
      rw [show k - 1 + 1 = k by omega] at D
      cases hq : (letterAt W (k - 1)).posL p with
      | some q =>
        rw [prevPair_right W (by omega) hb hq]
        obtain ⟨hq1, hq2, -, -⟩ := D.posL_some hp1 hpk hq
        right; exact ⟨hq1, hq2, by omega⟩
      | none =>
        rw [prevPair_right_none W (by omega) hb hq]
        obtain ⟨m, d, hm, -⟩ := posL_eq_none_iff.1 hq
        left; exact ⟨rfl, by omega, by rw [hm]; rfl⟩
    | false =>
      obtain ⟨D⟩ := decomp hW k hkn'
      cases hq : (letterAt W k).posR p with
      | some q =>
        rw [prevPair_left W (by omega) hb hq]
        obtain ⟨hq1, hq2, -, -⟩ := D.posR_some hp1 hpk hq
        right; exact ⟨hq1, hq2, by omega⟩
      | none =>
        rw [prevPair_left_none W (by omega) hb hq]
        obtain ⟨m, hm, -⟩ := posR_eq_none_iff.1 hq
        left; exact ⟨rfl, hkn', by rw [hm]; rfl⟩

theorem prevPair_nextPair {s : ℕ × ℕ} (hs : IsSlot W s) : prevPair W (nextPair W s) = s := by
  obtain ⟨k, p⟩ := s
  rcases hs with ⟨hp0, hk, hσ⟩ | ⟨hp1, hpk, hkn⟩
  · simp only at hp0 hk hσ
    subst hp0
    obtain ⟨D⟩ := decomp hW k hk
    have hk' : k + 1 - 1 = k := by omega
    cases hℓ : letterAt W k with
    | l m d =>
      rw [hℓ] at D
      obtain ⟨hb1, hb2, hlen⟩ := D.bits_l
      have hm := D.hm
      simp only [idx] at hm
      rw [nextPair_cusp_l W hℓ]
      cases d
      · simp only [Bool.false_eq_true, ↓reduceIte]
        rw [prevPair_right_none W (by omega) (by rw [bit_succ]; exact hb2)
          (by rw [hk', hℓ]; exact posL_l_idx_succ m false), hk']
      · simp only [↓reduceIte]
        rw [prevPair_right_none W (by omega) hb1 (by rw [hk', hℓ]; exact posL_l_idx m true), hk']
    | r m =>
      rw [hℓ] at D
      obtain ⟨hne, hlen⟩ := D.bits_r
      have hm := D.hm
      simp only [idx] at hm
      rw [nextPair_cusp_r W hℓ]
      cases hb : bit W k m
      · simp only [Bool.false_eq_true, ↓reduceIte]
        rw [prevPair_left_none W (by omega) hb (by rw [hℓ]; exact posR_r_idx m)]
      · simp only [↓reduceIte]
        have hb' : bit W k (m + 1) = false := by
          rw [bit_succ]; rw [bit_eq] at hb; cases h : (cut W k).getD m false
          · rfl
          · rw [h, hb] at hne; exact absurd rfl hne
        rw [prevPair_left_none W (by omega) hb' (by rw [hℓ]; exact posR_r_idx_succ m)]
    | σ m => rw [hℓ] at hσ; simp [isCrossing] at hσ
  · simp only at hp1 hpk hkn
    obtain ⟨hk0, hkn'⟩ := cutSlot_pos hW hp1 hpk
    cases hb : bit W k p with
    | true =>
      obtain ⟨D⟩ := decomp hW k hkn'
      cases hq : (letterAt W k).posR p with
      | some q =>
        rw [nextPair_right W (by omega) hb hq]
        obtain ⟨hq1, hq2, hbq, hq'⟩ := D.posR_some hp1 hpk hq
        have hk' : k + 1 - 1 = k := by omega
        rw [prevPair_right W (by omega) (by rw [bit_eq, hbq]; exact hb) (by rw [hk']; exact hq'), hk']
      | none =>
        rw [nextPair_right_none W (by omega) hb hq]
        obtain ⟨m, hm, hpm⟩ := posR_eq_none_iff.1 hq
        rw [hm] at D
        obtain ⟨hne, hlen⟩ := D.bits_r
        rw [prevPair_cusp_r W hm]
        rcases hpm with rfl | rfl
        · rw [hb]; rfl
        · have hb' : bit W k m = false := by
            rw [bit_eq]; rw [bit_succ] at hb
            cases h : (cut W k).getD (m - 1) false
            · rfl
            · rw [h, hb] at hne; exact absurd rfl hne
          rw [hb']; rfl
    | false =>
      obtain ⟨D⟩ := decomp hW (k - 1) (by omega)
      have hk' : k - 1 + 1 = k := by omega
      rw [hk'] at D
      cases hq : (letterAt W (k - 1)).posL p with
      | some q =>
        rw [nextPair_left W (by omega) hb hq]
        obtain ⟨hq1, hq2, hbq, hq'⟩ := D.posL_some hp1 hpk hq
        rw [prevPair_left W (by omega) (by rw [bit_eq, hbq]; exact hb) hq', hk']
      | none =>
        rw [nextPair_left_none W (by omega) hb hq]
        obtain ⟨m, d, hm, hpm⟩ := posL_eq_none_iff.1 hq
        rw [hm] at D
        obtain ⟨hb1, hb2, hlen⟩ := D.bits_l
        rw [prevPair_cusp_l W hm, hk']
        rcases hpm with rfl | rfl
        · -- the leftward arm is position `m`, so `d = false`
          have : d = false := by rw [bit_eq] at hb; rw [hb] at hb1; exact hb1.symm
          subst this; rfl
        · have : d = true := by
            rw [bit_succ] at hb; rw [hb] at hb2
            cases d
            · simp at hb2
            · rfl
          subst this; rfl

theorem nextPair_prevPair {s : ℕ × ℕ} (hs : IsSlot W s) : nextPair W (prevPair W s) = s := by
  obtain ⟨k, p⟩ := s
  rcases hs with ⟨hp0, hk, hσ⟩ | ⟨hp1, hpk, hkn⟩
  · simp only at hp0 hk hσ
    subst hp0
    obtain ⟨D⟩ := decomp hW k hk
    have hk' : k + 1 - 1 = k := by omega
    cases hℓ : letterAt W k with
    | l m d =>
      rw [hℓ] at D
      obtain ⟨hb1, hb2, hlen⟩ := D.bits_l
      have hm := D.hm
      simp only [idx] at hm
      rw [prevPair_cusp_l W hℓ]
      cases d
      · simp only [Bool.false_eq_true, ↓reduceIte]
        rw [nextPair_left_none W (by omega) hb1 (by rw [hk', hℓ]; exact posL_l_idx m false), hk']
      · simp only [↓reduceIte]
        rw [nextPair_left_none W (by omega) (by rw [bit_succ]; exact hb2)
          (by rw [hk', hℓ]; exact posL_l_idx_succ m true), hk']
    | r m =>
      rw [hℓ] at D
      obtain ⟨hne, hlen⟩ := D.bits_r
      have hm := D.hm
      simp only [idx] at hm
      rw [prevPair_cusp_r W hℓ]
      cases hb : bit W k m
      · simp only [Bool.false_eq_true, ↓reduceIte]
        have hb' : bit W k (m + 1) = true := by
          rw [bit_succ]; rw [bit_eq] at hb; cases h : (cut W k).getD m false
          · rw [h, hb] at hne; exact absurd rfl hne
          · rfl
        rw [nextPair_right_none W (by omega) hb' (by rw [hℓ]; exact posR_r_idx_succ m)]
      · simp only [↓reduceIte]
        rw [nextPair_right_none W (by omega) hb (by rw [hℓ]; exact posR_r_idx m)]
    | σ m => rw [hℓ] at hσ; simp [isCrossing] at hσ
  · simp only at hp1 hpk hkn
    obtain ⟨hk0, hkn'⟩ := cutSlot_pos hW hp1 hpk
    cases hb : bit W k p with
    | true =>
      obtain ⟨D⟩ := decomp hW (k - 1) (by omega)
      have hk' : k - 1 + 1 = k := by omega
      rw [hk'] at D
      cases hq : (letterAt W (k - 1)).posL p with
      | some q =>
        rw [prevPair_right W (by omega) hb hq]
        obtain ⟨hq1, hq2, hbq, hq'⟩ := D.posL_some hp1 hpk hq
        rw [nextPair_right W (by omega) (by rw [bit_eq, hbq]; exact hb) hq', hk']
      | none =>
        rw [prevPair_right_none W (by omega) hb hq]
        obtain ⟨m, d, hm, hpm⟩ := posL_eq_none_iff.1 hq
        rw [hm] at D
        obtain ⟨hb1, hb2, hlen⟩ := D.bits_l
        rw [nextPair_cusp_l W hm, hk']
        rcases hpm with rfl | rfl
        · have : d = true := by rw [bit_eq] at hb; rw [hb] at hb1; exact hb1.symm
          subst this; rfl
        · have : d = false := by
            rw [bit_succ] at hb; rw [hb] at hb2
            cases d
            · rfl
            · simp at hb2
          subst this; rfl
    | false =>
      obtain ⟨D⟩ := decomp hW k hkn'
      cases hq : (letterAt W k).posR p with
      | some q =>
        rw [prevPair_left W (by omega) hb hq]
        obtain ⟨hq1, hq2, hbq, hq'⟩ := D.posR_some hp1 hpk hq
        have hk' : k + 1 - 1 = k := by omega
        rw [nextPair_left W (by omega) (by rw [bit_eq, hbq]; exact hb) (by rw [hk']; exact hq'), hk']
      | none =>
        rw [prevPair_left_none W (by omega) hb hq]
        obtain ⟨m, hm, hpm⟩ := posR_eq_none_iff.1 hq
        rw [hm] at D
        obtain ⟨hne, hlen⟩ := D.bits_r
        rw [nextPair_cusp_r W hm]
        rcases hpm with rfl | rfl
        · rw [hb]; rfl
        · have hb' : bit W k m = true := by
            rw [bit_eq]; rw [bit_succ] at hb
            cases h : (cut W k).getD (m - 1) false
            · rw [h, hb] at hne; exact absurd rfl hne
            · rfl
          rw [hb']; rfl

/-- The successor slot. -/
def next (s : Slot W) : Slot W := ⟨nextPair W s.1, isSlot_nextPair hW s.2⟩

/-- The predecessor slot. -/
def prev (s : Slot W) : Slot W := ⟨prevPair W s.1, isSlot_prevPair hW s.2⟩

theorem next_val (s : Slot W) : (next hW s).1 = nextPair W s.1 := rfl
theorem prev_val (s : Slot W) : (prev hW s).1 = prevPair W s.1 := rfl

theorem prev_next (s : Slot W) : prev hW (next hW s) = s := Subtype.ext (prevPair_nextPair hW s.2)
theorem next_prev (s : Slot W) : next hW (prev hW s) = s := Subtype.ext (nextPair_prevPair hW s.2)

/-- The successor permutation of the slots: its cycles are the components of the realization. -/
def nextPerm : Equiv.Perm (Slot W) := ⟨next hW, prev hW, prev_next hW, next_prev hW⟩

@[simp] theorem nextPerm_apply (s : Slot W) : nextPerm hW s = next hW s := rfl
@[simp] theorem nextPerm_symm_apply (s : Slot W) : (nextPerm hW).symm s = prev hW s := rfl

theorem next_injective : Function.Injective (next hW) := (nextPerm hW).injective

theorem next_ne (s : Slot W) : next hW s ≠ s := by
  intro h
  have h1 := congrArg (fun t : Slot W => t.1) h
  simp only [next_val] at h1
  obtain ⟨⟨k, p⟩, hs⟩ := s
  rcases hs with ⟨hp0, hk, hσ⟩ | ⟨hp1, hpk, hkn⟩
  · simp only at hp0 hk hσ
    subst hp0
    cases hℓ : letterAt W k with
    | l m d => rw [nextPair_cusp_l W hℓ] at h1; simp at h1
    | r m =>
      obtain ⟨D⟩ := decomp hW k hk
      rw [hℓ] at D
      have hm := D.hm
      simp only [idx] at hm
      rw [nextPair_cusp_r W hℓ] at h1
      simp only [Prod.mk.injEq, true_and] at h1
      split_ifs at h1 <;> omega
    | σ m => rw [hℓ] at hσ; simp [isCrossing] at hσ
  · simp only at hp1 hpk hkn
    obtain ⟨hk0, hkn'⟩ := cutSlot_pos hW hp1 hpk
    cases hb : bit W k p with
    | true =>
      cases hq : (letterAt W k).posR p with
      | some q => rw [nextPair_right W (by omega) hb hq] at h1; simp at h1
      | none => rw [nextPair_right_none W (by omega) hb hq] at h1; simp at h1; omega
    | false =>
      cases hq : (letterAt W (k - 1)).posL p with
      | some q => rw [nextPair_left W (by omega) hb hq] at h1; simp at h1; omega
      | none => rw [nextPair_left_none W (by omega) hb hq] at h1; simp at h1; omega

/-! ### The six shapes of a successor step -/

/-- The successor of a slot, by cases: (1) a rightward strand passes the column; (2) a rightward strand
enters a right cusp; (3) a leftward strand passes the column; (4) a leftward strand enters a left cusp;
(5) a left-cusp vertex sends the traversal out along its rightward arm; (6) a right-cusp vertex sends it
out along its leftward arm. -/
theorem next_cases (s : Slot W) :
    (∃ k p q, s.1 = (k, p) ∧ 1 ≤ p ∧ bit W k p = true ∧ (next hW s).1 = (k + 1, q) ∧ 1 ≤ q ∧
      bit W (k + 1) q = true ∧ (letterAt W k).posR p = some q ∧ k < W.length) ∨
    (∃ k p m, s.1 = (k, p) ∧ 1 ≤ p ∧ bit W k p = true ∧ letterAt W k = .r m ∧ (p = m ∨ p = m + 1) ∧
      (next hW s).1 = (k, 0) ∧ bit W k m ≠ bit W k (m + 1) ∧ k < W.length) ∨
    (∃ k p q, s.1 = (k, p) ∧ 1 ≤ p ∧ bit W k p = false ∧ (next hW s).1 = (k - 1, q) ∧ 1 ≤ q ∧
      bit W (k - 1) q = false ∧ (letterAt W (k - 1)).posL p = some q ∧ 1 ≤ k ∧ k ≤ W.length) ∨
    (∃ k p m d, s.1 = (k, p) ∧ 1 ≤ p ∧ bit W k p = false ∧ letterAt W (k - 1) = .l m d ∧
      (p = m ∨ p = m + 1) ∧ (next hW s).1 = (k - 1, 0) ∧ bit W k m = d ∧ bit W k (m + 1) = !d ∧
      1 ≤ k ∧ k ≤ W.length) ∨
    (∃ k m d, s.1 = (k, 0) ∧ letterAt W k = .l m d ∧ (next hW s).1 = (k + 1, if d then m else m + 1) ∧
      bit W (k + 1) m = d ∧ bit W (k + 1) (m + 1) = !d ∧ 1 ≤ m ∧ k < W.length) ∨
    (∃ k m, s.1 = (k, 0) ∧ letterAt W k = .r m ∧ (next hW s).1 = (k, if bit W k m then m + 1 else m) ∧
      bit W k m ≠ bit W k (m + 1) ∧ 1 ≤ m ∧ k < W.length) := by
  obtain ⟨k, p, hkp⟩ : ∃ k p, s.1 = (k, p) := ⟨s.1.1, s.1.2, rfl⟩
  have hs := s.2
  rw [hkp] at hs
  have hn : (next hW s).1 = nextPair W (k, p) := by rw [next_val, hkp]
  rcases hs with ⟨hp0, hk, hσ⟩ | ⟨hp1, hpk, hkn⟩
  · simp only at hp0 hk hσ
    subst hp0
    obtain ⟨D⟩ := decomp hW k hk
    cases hℓ : letterAt W k with
    | l m d =>
      rw [hℓ] at D
      obtain ⟨hb1, hb2, -⟩ := D.bits_l
      have hm := D.hm
      simp only [idx] at hm
      refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨k, m, d, hkp, hℓ, by rw [hn, nextPair_cusp_l W hℓ], hb1, ?_, hm, hk⟩))))
      rw [bit_succ]; exact hb2
    | r m =>
      rw [hℓ] at D
      obtain ⟨hne, -⟩ := D.bits_r
      have hm := D.hm
      simp only [idx] at hm
      refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨k, m, hkp, hℓ, by rw [hn, nextPair_cusp_r W hℓ], ?_, hm, hk⟩))))
      rw [bit_succ]; exact hne
    | σ m => rw [hℓ] at hσ; simp [isCrossing] at hσ
  · simp only at hp1 hpk hkn
    obtain ⟨hk0, hkn'⟩ := cutSlot_pos hW hp1 hpk
    cases hb : bit W k p with
    | true =>
      obtain ⟨D⟩ := decomp hW k hkn'
      cases hq : (letterAt W k).posR p with
      | some q =>
        obtain ⟨hq1, -, hbq, -⟩ := D.posR_some hp1 hpk hq
        exact Or.inl ⟨k, p, q, hkp, hp1, hb, by rw [hn, nextPair_right W (by omega) hb hq], hq1,
          by rw [bit_eq, hbq]; exact hb, hq, hkn'⟩
      | none =>
        obtain ⟨m, hm, hpm⟩ := posR_eq_none_iff.1 hq
        rw [hm] at D
        obtain ⟨hne, -⟩ := D.bits_r
        refine Or.inr (Or.inl ⟨k, p, m, hkp, hp1, hb, hm, hpm, by rw [hn, nextPair_right_none W (by omega) hb hq], ?_, hkn'⟩)
        rw [bit_succ]; exact hne
    | false =>
      obtain ⟨D⟩ := decomp hW (k - 1) (by omega)
      have hk' : k - 1 + 1 = k := by omega
      rw [hk'] at D
      cases hq : (letterAt W (k - 1)).posL p with
      | some q =>
        obtain ⟨hq1, -, hbq, -⟩ := D.posL_some hp1 hpk hq
        exact Or.inr (Or.inr (Or.inl ⟨k, p, q, hkp, hp1, hb, by rw [hn, nextPair_left W (by omega) hb hq], hq1,
          by rw [bit_eq, hbq]; exact hb, hq, hk0, hkn⟩))
      | none =>
        obtain ⟨m, d, hm, hpm⟩ := posL_eq_none_iff.1 hq
        rw [hm] at D
        obtain ⟨hb1, hb2, -⟩ := D.bits_l
        refine Or.inr (Or.inr (Or.inr (Or.inl ⟨k, p, m, d, hkp, hp1, hb, hm, hpm,
          by rw [hn, nextPair_left_none W (by omega) hb hq], hb1, ?_, hk0, hkn⟩)))
        rw [bit_succ]; exact hb2

/-! ### The x-direction of a slot and its propagation -/

/-- The rightward bit of the traversal leaving a slot: the cut bit at a cut slot; `true` at a left-cusp
vertex (the traversal leaves a left cusp moving rightward), `false` at a right-cusp vertex. -/
def xsign (s : Slot W) : Bool :=
  if s.1.2 = 0 then (match letterAt W s.1.1 with | .l _ _ => true | _ => false) else bit W s.1.1 s.1.2

omit hW in
theorem xsign_cut {s : Slot W} {k p : ℕ} (h : s.1 = (k, p)) (hp : p ≠ 0) : xsign s = bit W k p := by
  simp [xsign, h, hp]

omit hW in
theorem xsign_cusp_l {s : Slot W} {k m : ℕ} {d : Bool} (h0 : s.1 = (k, 0)) (h : letterAt W k = .l m d) :
    xsign s = true := by simp [xsign, h0, h]

omit hW in
theorem xsign_cusp_r {s : Slot W} {k m : ℕ} (h0 : s.1 = (k, 0)) (h : letterAt W k = .r m) :
    xsign s = false := by simp [xsign, h0, h]

omit hW in
/-- A cusp vertex carries a cusp letter. -/
theorem letterAt_of_cusp {s : Slot W} (h0 : s.1.2 = 0) :
    (∃ m d, letterAt W s.1.1 = .l m d) ∨ (∃ m, letterAt W s.1.1 = .r m) := by
  obtain ⟨⟨k, p⟩, hs⟩ := s
  simp only at h0
  subst h0
  rcases hs with ⟨-, -, hσ⟩ | ⟨h, -, -⟩
  · cases hℓ : letterAt W k with
    | l m d => exact Or.inl ⟨m, d, rfl⟩
    | r m => exact Or.inr ⟨m, rfl⟩
    | σ m => simp only at hσ; rw [hℓ] at hσ; simp [isCrossing] at hσ
  · simp at h

/-- Twice the x-coordinate of a slot on the standard grid: `2k` at a cut slot, `2k + 1` at a cusp
vertex. -/
def xcoord2 (s : Slot W) : ℕ := 2 * s.1.1 + (if s.1.2 = 0 then 1 else 0)

/-- The x-direction is kept when the successor is a cut slot and reversed when it is a cusp vertex. -/
theorem xsign_next_iff (s : Slot W) : xsign (next hW s) = xsign s ↔ (next hW s).1.2 ≠ 0 := by
  rcases next_cases hW s with
    ⟨k, p, q, hs, hp, hb, hn, hq, hbq, -, -⟩ | ⟨k, p, m, hs, hp, hb, hℓ, -, hn, -, -⟩ |
    ⟨k, p, q, hs, hp, hb, hn, hq, hbq, -, -, -⟩ | ⟨k, p, m, d, hs, hp, hb, hℓ, -, hn, -, -, -, -⟩ |
    ⟨k, m, d, hs, hℓ, hn, hb1, hb2, hm, -⟩ | ⟨k, m, hs, hℓ, hn, hne, hm, -⟩
  · rw [xsign_cut hs (by omega), xsign_cut hn (by omega), hn, hb, hbq]; simp; omega
  · rw [xsign_cut hs (by omega), xsign_cusp_r hn hℓ, hn, hb]; simp
  · rw [xsign_cut hs (by omega), xsign_cut hn (by omega), hn, hb, hbq]; simp; omega
  · rw [xsign_cut hs (by omega), xsign_cusp_l hn hℓ, hn, hb]; simp
  · rw [xsign_cusp_l hs hℓ, xsign_cut hn (by split_ifs <;> omega), hn]
    cases d
    · simp only [Bool.false_eq_true, ↓reduceIte, ne_eq]
      rw [hb2]; simp
    · simp only [↓reduceIte, ne_eq]
      rw [hb1]; simp; omega
  · rw [xsign_cusp_r hs hℓ, xsign_cut hn (by split_ifs <;> omega), hn]
    cases hb : bit W k m
    · simp only [Bool.false_eq_true, ↓reduceIte, ne_eq]
      rw [hb]; simp; omega
    · simp only [↓reduceIte, ne_eq]
      have : bit W k (m + 1) = false := by
        cases h : bit W k (m + 1)
        · rfl
        · exact absurd (hb.trans h.symm) hne
      rw [this]; simp

theorem xsign_next_of_cut {s : Slot W} (h : (next hW s).1.2 ≠ 0) : xsign (next hW s) = xsign s :=
  (xsign_next_iff hW s).2 h

theorem xsign_next_of_cusp {s : Slot W} (h : (next hW s).1.2 = 0) : xsign (next hW s) ≠ xsign s :=
  fun h' => ((xsign_next_iff hW s).1 h') h

/-- The successor of a cusp vertex is a cut slot. -/
theorem next_cusp_cut {s : Slot W} (h : s.1.2 = 0) : (next hW s).1.2 ≠ 0 := by
  rcases next_cases hW s with
    ⟨k, p, q, hs, hp, -⟩ | ⟨k, p, m, hs, hp, -⟩ | ⟨k, p, q, hs, hp, -⟩ | ⟨k, p, m, d, hs, hp, -⟩ |
    ⟨k, m, d, hs, hℓ, hn, -, -, hm, -⟩ | ⟨k, m, hs, hℓ, hn, -, hm, -⟩
  · rw [hs] at h; simp at h; omega
  · rw [hs] at h; simp at h; omega
  · rw [hs] at h; simp at h; omega
  · rw [hs] at h; simp at h; omega
  · rw [hn]; dsimp only; split_ifs <;> omega
  · rw [hn]; dsimp only; split_ifs <;> omega

/-- A rightward step increases the x-coordinate, a leftward step decreases it. -/
theorem xcoord2_next (s : Slot W) :
    (xsign s = true → xcoord2 s < xcoord2 (next hW s)) ∧ (xsign s = false → xcoord2 (next hW s) < xcoord2 s) := by
  rcases next_cases hW s with
    ⟨k, p, q, hs, hp, hb, hn, hq, -⟩ | ⟨k, p, m, hs, hp, hb, hℓ, -, hn, -⟩ |
    ⟨k, p, q, hs, hp, hb, hn, hq, -, -, hk, -⟩ | ⟨k, p, m, d, hs, hp, hb, hℓ, -, hn, -, -, hk, -⟩ |
    ⟨k, m, d, hs, hℓ, hn, -, -, hm, -⟩ | ⟨k, m, hs, hℓ, hn, -, hm, -⟩
  · have hp' : p ≠ 0 := by omega
    have hq' : q ≠ 0 := by omega
    rw [xsign_cut hs (by omega), hb]; simp [xcoord2, hs, hn, hp', hq']
  · have hp' : p ≠ 0 := by omega
    rw [xsign_cut hs (by omega), hb]; simp [xcoord2, hs, hn, hp']
  · have hp' : p ≠ 0 := by omega
    have hq' : q ≠ 0 := by omega
    rw [xsign_cut hs (by omega), hb]; simp [xcoord2, hs, hn, hp', hq']; omega
  · have hp' : p ≠ 0 := by omega
    rw [xsign_cut hs (by omega), hb]; simp [xcoord2, hs, hn, hp']; omega
  · have h' : (if d then m else m + 1) ≠ 0 := by cases d <;> simp <;> omega
    rw [xsign_cusp_l hs hℓ]; simp [xcoord2, hs, hn, h']; omega
  · have h' : (if bit W k m then m + 1 else m) ≠ 0 := by split_ifs <;> omega
    rw [xsign_cusp_r hs hℓ]; simp [xcoord2, hs, hn, h']

/-- No slot returns to itself in two steps. -/
theorem next_next_ne (s : Slot W) : next hW (next hW s) ≠ s := by
  intro h
  by_cases hs : s.1.2 = 0
  · -- a cusp vertex: its successor is a cut slot whose successor (= `s`) is a cusp, flipping the sign twice
    have h1 : (next hW s).1.2 ≠ 0 := next_cusp_cut hW hs
    have h2 := xsign_next_of_cut hW h1
    have h3 : (next hW (next hW s)).1.2 = 0 := by rw [h]; exact hs
    have h4 := xsign_next_of_cusp hW h3
    rw [h, h2] at h4
    exact h4 rfl
  · by_cases hn : (next hW s).1.2 = 0
    · have h2 := xsign_next_of_cusp hW hn
      have h3 : (next hW (next hW s)).1.2 ≠ 0 := next_cusp_cut hW hn
      have h4 := xsign_next_of_cut hW h3
      rw [h] at h4
      exact h2 h4.symm
    · have h2 := xsign_next_of_cut hW hn
      have ⟨a1, a2⟩ := xcoord2_next hW s
      have ⟨b1, b2⟩ := xcoord2_next hW (next hW s)
      rw [h, h2] at b1 b2
      cases hx : xsign s
      · have := a2 hx; have := b2 hx; omega
      · have := a1 hx; have := b1 hx; omega

/-! ### Cycles of the successor permutation: the components -/

/-- The cycle length through a slot. -/
noncomputable def period (s : Slot W) : ℕ := Function.minimalPeriod (next hW) s

theorem mem_periodicPts (s : Slot W) : s ∈ Function.periodicPts (next hW) :=
  (next_injective hW).mem_periodicPts s

theorem period_pos (s : Slot W) : 0 < period hW s :=
  Function.minimalPeriod_pos_of_mem_periodicPts (mem_periodicPts hW s)

theorem iterate_period (s : Slot W) : (next hW)^[period hW s] s = s :=
  Function.iterate_minimalPeriod

theorem iterate_mod_period (s : Slot W) (n : ℕ) : (next hW)^[n % period hW s] s = (next hW)^[n] s :=
  Function.iterate_mod_minimalPeriod_eq

theorem period_next (s : Slot W) : period hW (next hW s) = period hW s :=
  Function.minimalPeriod_apply (mem_periodicPts hW s)

theorem period_iterate (s : Slot W) (n : ℕ) : period hW ((next hW)^[n] s) = period hW s :=
  Function.minimalPeriod_apply_iterate (mem_periodicPts hW s) n

/-- Every cycle has at least three slots (`PolyComp.hk`). -/
theorem three_le_period (s : Slot W) : 3 ≤ period hW s := by
  have hpos := period_pos hW s
  have hper := iterate_period hW s
  by_contra h
  rw [not_le] at h
  interval_cases hp : period hW s
  · exact next_ne hW s hper
  · exact next_next_ne hW s hper

theorem iterate_injOn (s : Slot W) {a b : ℕ} (ha : a < period hW s) (hb : b < period hW s)
    (h : (next hW)^[a] s = (next hW)^[b] s) : a = b :=
  Function.iterate_injOn_Iio_minimalPeriod ha hb h

/-- The components: the cycles of the successor permutation. -/
def Orbit : Type := Quotient (Equiv.Perm.SameCycle.setoid (nextPerm hW))

noncomputable instance : Fintype (Orbit hW) := by
  classical
  exact Quotient.fintype _

/-- the cycle of a slot -/
def orbitOf (s : Slot W) : Orbit hW := Quotient.mk _ s

theorem orbitOf_eq_iff (s t : Slot W) : orbitOf hW s = orbitOf hW t ↔ (nextPerm hW).SameCycle s t :=
  Quotient.eq

theorem orbitOf_surjective : Function.Surjective (orbitOf hW) := Quotient.mk_surjective

theorem sameCycle_of_iterate {s t : Slot W} {a b : ℕ} (h : (next hW)^[a] s = (next hW)^[b] t) :
    (nextPerm hW).SameCycle s t := by
  refine ⟨-(b : ℤ) + a, ?_⟩
  have ha : ((nextPerm hW) ^ a) s = (next hW)^[a] s := by rw [Equiv.Perm.coe_pow]; rfl
  have hb : ((nextPerm hW) ^ b) t = (next hW)^[b] t := by rw [Equiv.Perm.coe_pow]; rfl
  rw [zpow_add, zpow_neg, zpow_natCast, zpow_natCast, Equiv.Perm.mul_apply, ha, h, ← hb,
    Equiv.Perm.inv_def]
  exact Equiv.symm_apply_apply _ _

theorem exists_iterate_of_sameCycle {s t : Slot W} (h : (nextPerm hW).SameCycle s t) :
    ∃ n, (next hW)^[n] s = t := by
  obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
  exact ⟨n, by rw [← hn, Equiv.Perm.coe_pow]; rfl⟩

/-- The number of components. -/
noncomputable abbrev numComp : ℕ := Fintype.card (Orbit hW)

/-- The representative slot of a component. -/
noncomputable def rep (i : Fin (numComp hW)) : Slot W :=
  ((Fintype.equivFin (Orbit hW)).symm i).out

theorem orbitOf_rep (i : Fin (numComp hW)) : orbitOf hW (rep hW i) = (Fintype.equivFin (Orbit hW)).symm i :=
  Quotient.out_eq _

theorem rep_injective_orbit {i j : Fin (numComp hW)} (h : (nextPerm hW).SameCycle (rep hW i) (rep hW j)) : i = j := by
  have := (orbitOf_eq_iff hW _ _).2 h
  rw [orbitOf_rep, orbitOf_rep] at this
  exact (Fintype.equivFin (Orbit hW)).symm.injective this

/-- Every slot is an iterate of the representative of its component. -/
theorem exists_rep_iterate (s : Slot W) :
    ∃ (i : Fin (numComp hW)) (n : ℕ), n < period hW (rep hW i) ∧ (next hW)^[n] (rep hW i) = s := by
  refine ⟨Fintype.equivFin (Orbit hW) (orbitOf hW s), ?_⟩
  have h : (nextPerm hW).SameCycle (rep hW (Fintype.equivFin (Orbit hW) (orbitOf hW s))) s := by
    rw [← orbitOf_eq_iff, orbitOf_rep, Equiv.symm_apply_apply]
  obtain ⟨n, hn⟩ := exists_iterate_of_sameCycle hW h
  refine ⟨n % period hW _, Nat.mod_lt _ (period_pos hW _), ?_⟩
  rw [iterate_mod_period, hn]

/-- The strand indices of the realization: a component and a position on its cycle. -/
abbrev Idx : Type := Σ i : Fin (numComp hW), ZMod (period hW (rep hW i))

instance (i : Fin (numComp hW)) : NeZero (period hW (rep hW i)) := ⟨(period_pos hW _).ne'⟩

/-- The slot of a strand index. -/
noncomputable def toSlot (x : Idx hW) : Slot W := (next hW)^[x.2.val] (rep hW x.1)

theorem toSlot_injective : Function.Injective (toSlot hW) := by
  rintro ⟨i, a⟩ ⟨j, b⟩ h
  simp only [toSlot] at h
  have hij : i = j := rep_injective_orbit hW (sameCycle_of_iterate hW h)
  subst hij
  have hab : a.val = b.val := iterate_injOn hW _ (ZMod.val_lt a) (ZMod.val_lt b) h
  rw [ZMod.val_injective _ hab]

theorem toSlot_surjective : Function.Surjective (toSlot hW) := by
  intro s
  obtain ⟨i, n, hn, hs⟩ := exists_rep_iterate hW s
  refine ⟨⟨i, (n : ZMod (period hW (rep hW i)))⟩, ?_⟩
  simp only [toSlot]
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt hn, hs]

theorem toSlot_bijective : Function.Bijective (toSlot hW) := ⟨toSlot_injective hW, toSlot_surjective hW⟩

/-- The strand indices are in bijection with the slots. -/
noncomputable def idxEquiv : Idx hW ≃ Slot W := Equiv.ofBijective _ (toSlot_bijective hW)

@[simp] theorem idxEquiv_apply (x : Idx hW) : idxEquiv hW x = toSlot hW x := rfl

omit hW in
theorem val_add_one {n : ℕ} [NeZero n] (hn : 2 ≤ n) (a : ZMod n) : (a + 1).val = (a.val + 1) % n := by
  rw [ZMod.val_add, ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt (by omega : 1 < n)]

/-- Moving one step along the cycle is `next`. -/
theorem toSlot_succ (i : Fin (numComp hW)) (j : ZMod (period hW (rep hW i))) :
    toSlot hW ⟨i, j + 1⟩ = next hW (toSlot hW ⟨i, j⟩) := by
  simp only [toSlot]
  have h2 : 2 ≤ period hW (rep hW i) := le_trans (by norm_num) (three_le_period hW (rep hW i))
  rw [val_add_one h2, iterate_mod_period, Function.iterate_succ_apply']

theorem toSlot_pred (i : Fin (numComp hW)) (j : ZMod (period hW (rep hW i))) :
    toSlot hW ⟨i, j - 1⟩ = prev hW (toSlot hW ⟨i, j⟩) := by
  have := toSlot_succ hW i (j - 1)
  rw [sub_add_cancel] at this
  rw [this, prev_next]

/-- The slots of one component are exactly one cycle. -/
theorem toSlot_fst_eq_iff (x y : Idx hW) : x.1 = y.1 ↔ (nextPerm hW).SameCycle (toSlot hW x) (toSlot hW y) := by
  constructor
  · intro h
    obtain ⟨i, a⟩ := x
    obtain ⟨j, b⟩ := y
    simp only at h
    subst h
    have : (next hW)^[b.val] (toSlot hW ⟨i, a⟩) = (next hW)^[a.val] (toSlot hW ⟨i, b⟩) := by
      simp only [toSlot, ← Function.iterate_add_apply, Nat.add_comm]
    exact sameCycle_of_iterate hW this
  · intro h
    obtain ⟨i, a⟩ := x
    obtain ⟨j, b⟩ := y
    have h1 : (nextPerm hW).SameCycle (rep hW i) (toSlot hW ⟨i, a⟩) :=
      sameCycle_of_iterate hW (s := rep hW i) (t := toSlot hW ⟨i, a⟩) (a := a.val) (b := 0) rfl
    have h2 : (nextPerm hW).SameCycle (rep hW j) (toSlot hW ⟨j, b⟩) :=
      sameCycle_of_iterate hW (s := rep hW j) (t := toSlot hW ⟨j, b⟩) (a := b.val) (b := 0) rfl
    exact rep_injective_orbit hW (h1.trans (h.trans h2.symm))

end Closed

end SM.FrontRealize
