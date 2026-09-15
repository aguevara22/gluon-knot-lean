import Mathlib.Tactic

/-! Ported 2026-09-14 from work/drafts/front/FrontWords.lean (front lane unit β1: oriented Rutherford front words, typing, counts, the eight rewrite relations with closedness preservation, Moves / Chain / Laws descent; library module, no row; the literature axiom ng:finite-word is NOT declared here). Only this header added. -/

/-! Front block, lane β, unit β1 (2026-09-14): module `SM/FrontWords.lean` (intended home), adopted design
work/reports/front-block-design-FINAL-20260913.md (§2 "Judge's additions", §4 `SM/FrontWords.lean`, §9
FR-5/FR-6, §11).

# Oriented Rutherford front words, the eight word-move patterns and the descent skeleton

Printed source (reference/SM/sm-3-statesum.tex): the certificate section sm-3:1900-1919 ("Use Rutherford's
elementary front words: l_m inserts a left cusp in positions m, m+1, r_m joins those positions at a right
cusp, and σ_m crosses them.  Number cut positions from top to bottom, read words from left to right, and
type each operation by its incoming and outgoing strand counts. ... The permitted orientations need not
produce a single component."), the move rows ng:commutation (1921-1948), ng:front-I/II/III (1950-2006),
ng:deletions (2008-2044), ng:circle (2046-2074), ng:cusp-skein (2076-2168) and the literature interface
ng:finite-word (2170-2206) with its transcription notes (2208-2304, including the two index corrections at
2284-2290).

Design (FINAL §2, FR-5): Rutherford's letters are unoriented; here every left cusp carries a DIRECTION BIT
`d` (the upper new arm travels rightward iff `d`), a right cusp requires its two strands to travel in
opposite x-directions, and a crossing transports the bits.  A cut is the list of the rightward bits of the
strands, top to bottom (`Cuts`).  The typing quantifies over all consistent orientations and FORCES the
printed orientation facts (sanity checks below by `decide`: sm-3:1958-1960, the (t,u) table sm-3:2107-2118).

Word-level `s`, `B` and the base are read GEOMETRICALLY from the grid realization (FINAL §2 G1; unit β2
builds `realize : OWord → PLFront`), so the descent engine is parametrized by them (`wordMovesOf`).  The
syntactic counts (`Word.sCount`, letter-tracing `downCountFrom`/`writheFrom`) are the correspondence targets
of β2 and give the `s`-clauses of the laws now (`Pres.sCountSyn_le`, `Del.sCountSyn_lt`, `Skein.sCountSyn`).

The two placeholders of the FINAL sketch are resolved here (review-sensitive, FR-6): `IsComm` carries the
two-strand index shift through the letters' strand footprints (`Letter.arity`/`coarity`; docstring of
`IsCommStep`), and the direction bits of the cusp-skein interchange are fixed from the printed (t,u) table
(docstring of `IsCuspSkeinStep`: `A'` carries the same bit as `A`, and the compatible smoothing is `C_top`
iff the through-strand bit is opposite to the cusp bit).  Type II also has its right-cusp versions ("follow
these same local strands backwards"), which the finite-word table uses ("Right cusp strictly inside a
string: Commute to expose type II").  Every rewrite pattern preserves closedness (section 4), so the moves
act on `OWord`.

All declarations live in `SM.FrontWord`.  Checked with `lake env lean` (clean, standard axioms). -/

namespace SM.FrontWord

/-! ## 1. Letters, cuts and the 1-based typing (sm-3:1906-1910; FR-6) -/

/-- Rutherford's three elementary letters with orientation bits.  `l m d` inserts a left cusp in positions
`m, m+1` (1-based, from the top), the upper new arm travelling rightward iff `d` (so the lower new arm
travels the other way); `r m` joins positions `m, m+1` at a right cusp (they must travel in opposite
x-directions); `σ m` crosses positions `m, m+1` (the incoming upper strand goes to the lower output, so
the two bits are exchanged). -/
inductive Letter
  | l (m : ℕ) (d : Bool)
  | r (m : ℕ)
  | σ (m : ℕ)
  deriving DecidableEq, Repr

/-- The directions (`true` = rightward) of the strands at a cut, top to bottom. -/
abbrev Cuts := List Bool

namespace Letter

/-- the position index `m` of a letter -/
def idx : Letter → ℕ
  | .l m _ => m
  | .r m => m
  | .σ m => m

/-- the same letter at another position -/
def reindex : Letter → ℕ → Letter
  | .l _ d, n => .l n d
  | .r _, n => .r n
  | .σ _, n => .σ n

/-- `true` for a crossing letter -/
def isCrossing : Letter → Bool
  | .σ _ => true
  | _ => false

/-- the number of incoming strands a letter acts on (`l`: none, it creates two; `r`, `σ`: two) -/
def arity : Letter → ℕ
  | .l _ _ => 0
  | .r _ => 2
  | .σ _ => 2

/-- the number of outgoing strands a letter produces (`l`: two, `r`: none, `σ`: two) -/
def coarity : Letter → ℕ
  | .l _ _ => 2
  | .r _ => 0
  | .σ _ => 2

/-- The local action of a letter on the strands from its position downward: `l _ d` pushes the two new
arms `d, !d`; `r` removes two strands of opposite directions; `σ` exchanges two strands.  `none` when the
letter is not typed there. -/
def act : Letter → Cuts → Option Cuts
  | .l _ d, L => some (d :: (!d) :: L)
  | .r _, a :: b :: L => if a ≠ b then some L else none
  | .r _, _ => none
  | .σ _, a :: b :: L => some (b :: a :: L)
  | .σ _, _ => none

/-- The typing step: the cut after the letter, or `none` if the letter is not typed at this cut.  The letter
acts at its 1-based position: the first `m − 1` strands are untouched, `act` applies to the rest.  (This is
FINAL's `Letter.step` written through `take`/`drop`; same values.) -/
def step (ℓ : Letter) (c : Cuts) : Option Cuts :=
  if 1 ≤ ℓ.idx ∧ ℓ.idx - 1 ≤ c.length then (ℓ.act (c.drop (ℓ.idx - 1))).map (c.take (ℓ.idx - 1) ++ ·)
  else none

@[simp] theorem idx_reindex (ℓ : Letter) (n : ℕ) : (ℓ.reindex n).idx = n := by cases ℓ <;> rfl

@[simp] theorem act_reindex (ℓ : Letter) (n : ℕ) : (ℓ.reindex n).act = ℓ.act := by
  cases ℓ <;> funext L <;> rcases L with _ | ⟨a, _ | ⟨b, L⟩⟩ <;> rfl

@[simp] theorem isCrossing_reindex (ℓ : Letter) (n : ℕ) : (ℓ.reindex n).isCrossing = ℓ.isCrossing := by
  cases ℓ <;> rfl

@[simp] theorem reindex_reindex (ℓ : Letter) (n k : ℕ) : (ℓ.reindex n).reindex k = ℓ.reindex k := by
  cases ℓ <;> rfl

@[simp] theorem reindex_self (ℓ : Letter) : ℓ.reindex ℓ.idx = ℓ := by cases ℓ <;> rfl

@[simp] theorem act_l (m : ℕ) (d : Bool) (L : Cuts) : (Letter.l m d).act L = some (d :: (!d) :: L) := rfl

@[simp] theorem act_σ_cons (m : ℕ) (a b : Bool) (L : Cuts) : (Letter.σ m).act (a :: b :: L) = some (b :: a :: L) := rfl

@[simp] theorem act_r_cons (m : ℕ) (a b : Bool) (L : Cuts) :
    (Letter.r m).act (a :: b :: L) = if a ≠ b then some L else none := rfl

theorem act_σ_eq_some_iff {m : ℕ} {L L' : Cuts} :
    (Letter.σ m).act L = some L' ↔ ∃ a b L₀, L = a :: b :: L₀ ∧ L' = b :: a :: L₀ := by
  constructor
  · intro h
    match L, h with
    | a :: b :: L₀, h => exact ⟨a, b, L₀, rfl, (Option.some.inj h).symm⟩
  · rintro ⟨a, b, L₀, rfl, rfl⟩; rfl

theorem act_r_eq_some_iff {m : ℕ} {L L' : Cuts} :
    (Letter.r m).act L = some L' ↔ ∃ a b, L = a :: b :: L' ∧ a ≠ b := by
  constructor
  · intro h
    match L, h with
    | a :: b :: L₀, h =>
      simp only [act_r_cons] at h
      split_ifs at h with hab
      · exact ⟨a, b, by rw [Option.some.inj h], hab⟩
  · rintro ⟨a, b, rfl, hab⟩
    simp [hab]

/-- The letter is typed at `A ++ L` with `|A| = m − 1`: it acts on `L` and keeps `A`. -/
theorem step_prefix {ℓ : Letter} {A L : Cuts} (h1 : 1 ≤ ℓ.idx) (hA : A.length = ℓ.idx - 1) :
    ℓ.step (A ++ L) = (ℓ.act L).map (A ++ ·) := by
  unfold step
  rw [ite_eq_left ⟨h1, by simp only [List.length_append]; omega⟩, List.take_left' hA, List.drop_left' hA]

theorem step_of_prefix {ℓ : Letter} {A L L' : Cuts} (h1 : 1 ≤ ℓ.idx) (hA : A.length = ℓ.idx - 1)
    (hL : ℓ.act L = some L') : ℓ.step (A ++ L) = some (A ++ L') := by
  rw [step_prefix h1 hA, hL]; rfl

/-- A typed step decomposes the cut at the letter's position. -/
theorem step_eq_some_iff {ℓ : Letter} {c c' : Cuts} :
    ℓ.step c = some c' ↔
      ∃ A L L' : Cuts, 1 ≤ ℓ.idx ∧ A.length = ℓ.idx - 1 ∧ c = A ++ L ∧ ℓ.act L = some L' ∧ c' = A ++ L' := by
  constructor
  · intro h
    unfold step at h
    split_ifs at h with hc
    · obtain ⟨L', hL', rfl⟩ := Option.map_eq_some_iff.1 h
      refine ⟨c.take (ℓ.idx - 1), c.drop (ℓ.idx - 1), L', hc.1, ?_, (List.take_append_drop _ _).symm, hL', rfl⟩
      simp only [List.length_take]; omega
  · rintro ⟨A, L, L', h1, hA, rfl, hL, rfl⟩
    exact step_of_prefix h1 hA hL

/-- `act` only reads the first `arity` strands: the rest is carried along. -/
theorem act_append {ℓ : Letter} {w R : Cuts} (hw : w.length = ℓ.arity) :
    ℓ.act (w ++ R) = (ℓ.act w).map (· ++ R) := by
  cases ℓ with
  | l m d =>
    obtain rfl := List.eq_nil_of_length_eq_zero hw
    simp
  | r m =>
    obtain ⟨a, b, rfl⟩ : ∃ a b, w = [a, b] := by
      match w, hw with
      | [a, b], _ => exact ⟨a, b, rfl⟩
    by_cases hab : a ≠ b <;> simp [hab]
  | σ m =>
    obtain ⟨a, b, rfl⟩ : ∃ a b, w = [a, b] := by
      match w, hw with
      | [a, b], _ => exact ⟨a, b, rfl⟩
    simp

/-- A typed local action splits off its window of `arity` incoming strands, producing `coarity` outgoing
strands and carrying the rest along. -/
theorem act_window {ℓ : Letter} {L L' : Cuts} (h : ℓ.act L = some L') :
    ∃ w w' R : Cuts, L = w ++ R ∧ w.length = ℓ.arity ∧ ℓ.act w = some w' ∧ w'.length = ℓ.coarity ∧
      L' = w' ++ R := by
  cases ℓ with
  | l m d =>
    refine ⟨[], [d, !d], L, rfl, rfl, by simp, rfl, ?_⟩
    simpa using h.symm
  | r m =>
    obtain ⟨a, b, rfl, hab⟩ := act_r_eq_some_iff.1 h
    exact ⟨[a, b], [], L', rfl, rfl, by simp [hab], rfl, rfl⟩
  | σ m =>
    obtain ⟨a, b, L₀, rfl, rfl⟩ := act_σ_eq_some_iff.1 h
    exact ⟨[a, b], [b, a], L₀, rfl, rfl, rfl, rfl, rfl⟩

end Letter

/-! ## 2. Words, the run of the typing, closedness -/

/-- A front word: a list of letters, read left to right. -/
abbrev Word := List Letter

namespace Word

/-- The cut after a word, starting from the cut `c`; `none` if some letter is not typed. -/
def run : Word → Cuts → Option Cuts
  | [], c => some c
  | a :: W, c => (a.step c).bind (Word.run W)

@[simp] theorem run_nil (c : Cuts) : Word.run [] c = some c := rfl

@[simp] theorem run_cons (a : Letter) (W : Word) (c : Cuts) : Word.run (a :: W) c = (a.step c).bind (Word.run W) := rfl

@[simp] theorem run_singleton (a : Letter) (c : Cuts) : Word.run [a] c = a.step c := by
  simp only [run_cons, run_nil]
  cases a.step c <;> rfl

theorem run_append (V W : Word) (c : Cuts) : Word.run (V ++ W) c = (Word.run V c).bind (Word.run W) := by
  induction V generalizing c with
  | nil => simp
  | cons a V ih =>
    simp only [List.cons_append, run_cons, Option.bind_assoc]
    congr 1
    funext c'
    exact ih c'

/-- A *closed* oriented front word: typed from no strands back to no strands (sm-3:1909-1910 "type each
operation by its incoming and outgoing strand counts"; closed fronts). -/
def Closed (W : Word) : Prop := Word.run W [] = some []

instance (W : Word) : Decidable W.Closed := inferInstanceAs (Decidable (Word.run W [] = some []))

/-- Replacing a factor by one with the same typing effect preserves closedness (the exterior cuts `X`, `Y`
are untouched: "fixed ordered boundary attachments, and an unchanged common exterior", sm-3:1914-1916). -/
theorem Closed.replace {X Y P P' : Word} (hW : (X ++ P ++ Y).Closed)
    (h : ∀ c c' : Cuts, Word.run P c = some c' → Word.run P' c = some c') : (X ++ P' ++ Y).Closed := by
  unfold Closed at *
  rw [run_append, run_append] at hW ⊢
  obtain ⟨c₁, hXP, hY⟩ := Option.bind_eq_some_iff.1 hW
  obtain ⟨c₀, hX, hP⟩ := Option.bind_eq_some_iff.1 hXP
  exact Option.bind_eq_some_iff.2 ⟨c₁, Option.bind_eq_some_iff.2 ⟨c₀, hX, h c₀ c₁ hP⟩, hY⟩

/-- The cut before a factor of a closed word. -/
theorem Closed.exists_run {X P Y : Word} (hW : (X ++ P ++ Y).Closed) :
    ∃ c₀ c₁ : Cuts, Word.run X [] = some c₀ ∧ Word.run P c₀ = some c₁ ∧ Word.run Y c₁ = some [] := by
  unfold Closed at hW
  rw [run_append, run_append] at hW
  obtain ⟨c₁, hXP, hY⟩ := Option.bind_eq_some_iff.1 hW
  obtain ⟨c₀, hX, hP⟩ := Option.bind_eq_some_iff.1 hXP
  exact ⟨c₀, c₁, hX, hP, hY⟩

/-! ### Syntactic counts: every letter is one singularity -/

/-- the number of crossing letters -/
def crossingCount (W : Word) : ℕ := W.countP (fun ℓ => ℓ.isCrossing)

/-- the number of cusp letters -/
def cuspCount (W : Word) : ℕ := W.countP (fun ℓ => !ℓ.isCrossing)

/-- the syntactic singularity count: crossings plus cusps -/
def sCount (W : Word) : ℕ := W.crossingCount + W.cuspCount

theorem sCount_eq_length (W : Word) : W.sCount = W.length := by
  unfold sCount crossingCount cuspCount
  induction W with
  | nil => rfl
  | cons a W ih =>
    simp only [List.countP_cons, List.length_cons]
    cases h : a.isCrossing <;> simp <;> omega

theorem sCount_append (V W : Word) : (V ++ W).sCount = V.sCount + W.sCount := by
  simp [sCount_eq_length]

@[simp] theorem sCount_nil : Word.sCount ([] : Word) = 0 := rfl

theorem sCount_reindex_pair (X Y : Word) (a b : Letter) (n : ℕ) :
    (X ++ [b, a.reindex n] ++ Y).sCount = (X ++ [a, b] ++ Y).sCount := by
  simp [sCount_eq_length]

/-! ### Letter tracing of the oriented data (the correspondence targets of β2; FINAL adopts the geometric
reading of `D`, `w` on the realization) -/

/-- The down-cusp indicator of a letter at a cut.  `l _ d`: the strand arrives on the lower arm and leaves
on the upper one iff the upper arm travels rightward (`d`), so the cusp is downward iff `d = false`.  `r m`:
the strand arrives on the upper arm iff that arm (position `m`) travels rightward, so the cusp is downward
iff the upper bit is `true`.  (Consistent with the printed (t,u) table: `u = 1`, "the orientation from 1 to
3, a downward cusp", is the left cusp `l₂ false`; checked below by `decide`.) -/
def _root_.SM.FrontWord.Letter.downBit : Letter → Cuts → ℕ
  | .l _ d, _ => if d then 0 else 1
  | .r m, c => match c.drop (m - 1) with
    | true :: _ => 1
    | _ => 0
  | .σ _, _ => 0

/-- The sign of a crossing letter at a cut: positive iff the two strands travel in the same x-direction
(the printed sign rule sm-3:1908-1912, on a PL front `SM.PLFront.isPositive_iff_xdir_eq`). -/
def _root_.SM.FrontWord.Letter.signBit : Letter → Cuts → ℤ
  | .σ m, c => match c.drop (m - 1) with
    | a :: b :: _ => if a = b then 1 else -1
    | _ => 0
  | _, _ => 0

/-- The letter-traced number of downward cusps of a word from the cut `c` (zero beyond a typing failure). -/
def downCountFrom : Word → Cuts → ℕ
  | [], _ => 0
  | a :: W, c => match a.step c with
    | none => 0
    | some c' => a.downBit c + Word.downCountFrom W c'

/-- The letter-traced writhe of a word from the cut `c`. -/
def writheFrom : Word → Cuts → ℤ
  | [], _ => 0
  | a :: W, c => match a.step c with
    | none => 0
    | some c' => a.signBit c + Word.writheFrom W c'

end Word

/-- A closed oriented front word ("an actual finite front word", ng:finite-word). -/
structure OWord where
  letters : Word
  closed : letters.Closed

namespace OWord

/-- the syntactic singularity count of a closed word -/
def sCountSyn (W : OWord) : ℕ := W.letters.sCount

/-- the letter-traced number of downward cusps -/
def downCountSyn (W : OWord) : ℕ := W.letters.downCountFrom []

/-- the letter-traced writhe -/
def writheSyn (W : OWord) : ℤ := W.letters.writheFrom []

end OWord

/-! ### Sanity checks against the printed text (all by `decide`) -/

/-- a standard circle, either orientation (ng:circle: "in either orientation") -/
example : Word.Closed [.l 1 true, .r 1] := by decide
example : Word.Closed [.l 1 false, .r 1] := by decide
/-- a standard circle has `D = 1`, `w = 0` in either orientation (sm-3:2052-2053) -/
example : Word.downCountFrom [.l 1 true, .r 1] [] = 1 := by decide
example : Word.downCountFrom [.l 1 false, .r 1] [] = 1 := by decide
/-- the standard crossing template `l₁ σ₁ r₁` is well typed -/
example : Word.Closed [.l 1 true, .σ 1, .r 1] := by decide
/-- the type-I curl on a through-strand: the typing FORCES the cusp bit from the through-strand direction
("Both crossing arrows are therefore rightward, or both are leftward when the entire strand is reversed",
sm-3:1958-1960) -/
example : Word.run [.l 2 true, .σ 1, .r 2] [true] = some [true] := by decide
example : Word.run [.l 2 false, .σ 1, .r 2] [false] = some [false] := by decide
example : Word.run [.l 2 true, .σ 1, .r 2] [false] = none := by decide
example : Word.run [.l 2 false, .σ 1, .r 2] [true] = none := by decide
/-- the type-I crossing is positive and exactly one of its cusps is downward (ng:type-I-counts) -/
example : Word.writheFrom [.l 2 true, .σ 1, .r 2] [true] = 1 := by decide
example : Word.downCountFrom [.l 2 true, .σ 1, .r 2] [true] = 1 := by decide
example : Word.writheFrom [.l 2 false, .σ 1, .r 2] [false] = 1 := by decide
example : Word.downCountFrom [.l 2 false, .σ 1, .r 2] [false] = 1 := by decide
/-- the crossed cusp `l_i σ_i`: "The arms are oppositely directed, so the old crossing has sign −1"
(sm-3:2030-2031) -/
example : Word.writheFrom [.l 1 true, .σ 1] [] = -1 := by decide
example : Word.writheFrom [.l 1 false, .σ 1] [] = -1 := by decide
/-- the zigzag `l_m r_{m+1}`: both cusps downward or both upward (sm-3:2015-2017) -/
example : Word.downCountFrom [.l 1 false, .r 2] [false] = 2 := by decide
example : Word.downCountFrom [.l 1 true, .r 2] [true] = 0 := by decide

/-- The printed (t,u) table of ng:cusp-skein (sm-3:2100-2118) on `A = l₂σ₁`, `A' = l₁σ₂` over the cut
`[a]`: `t = +1 ↔ a = true` (through-strand `L → 2` rightward), `u = +1 ↔ d = false` (cusp strand `1 → 3`,
a downward cusp).  Rows `(+,+), (+,−), (−,+), (−,−)`: `sign(A) = −1, +1, +1, −1`, `sign(A') = +1, −1, −1,
+1`, local `D = 1, 0, 1, 0`. -/
example : Word.writheFrom [.l 2 false, .σ 1] [true] = -1 ∧ Word.writheFrom [.l 1 false, .σ 2] [true] = 1 ∧
    Word.downCountFrom [.l 2 false, .σ 1] [true] = 1 := by decide
example : Word.writheFrom [.l 2 true, .σ 1] [true] = 1 ∧ Word.writheFrom [.l 1 true, .σ 2] [true] = -1 ∧
    Word.downCountFrom [.l 2 true, .σ 1] [true] = 0 := by decide
example : Word.writheFrom [.l 2 false, .σ 1] [false] = 1 ∧ Word.writheFrom [.l 1 false, .σ 2] [false] = -1 ∧
    Word.downCountFrom [.l 2 false, .σ 1] [false] = 1 := by decide
example : Word.writheFrom [.l 2 true, .σ 1] [false] = -1 ∧ Word.writheFrom [.l 1 true, .σ 2] [false] = 1 ∧
    Word.downCountFrom [.l 2 true, .σ 1] [false] = 0 := by decide
/-- the compatible smoothing has the same output cut as `A` and `A'` (`t = u`: `C_top = l₁`; `t = −u`:
`C_bottom = l₂`), and the new cusp direction is `u` in either case (sm-3:2119-2126) -/
example : Word.run [.l 2 false, .σ 1] [true] = Word.run [.l 1 false] [true] := by decide
example : Word.run [.l 2 true, .σ 1] [true] = Word.run [.l 2 true] [true] := by decide
example : Word.run [.l 2 false, .σ 1] [false] = Word.run [.l 2 false] [false] := by decide
example : Word.run [.l 2 true, .σ 1] [false] = Word.run [.l 1 true] [false] := by decide
/-- the crossing-free single-component zigzag word `l₁ l₂ r₁ r₁` (FINAL §2 G1 (iii) prints it as
`l₁ l₂ r₁ r₂`, which is not typed: after `r₁` two strands remain) is closed with `s = 4`, `D = 3`: NOT a union
of standard circles, so the base must be the geometric predicate -/
example : Word.Closed [.l 1 true, .l 2 false, .r 1, .r 1] ∧ Word.sCount [.l 1 true, .l 2 false, .r 1, .r 1] = 4 ∧
    Word.downCountFrom [.l 1 true, .l 2 false, .r 1, .r 1] [] = 3 := by
  decide

/-! ## 3. The printed letter patterns (rows 76a-82, ng:finite-word items 1-3), as list rewrites -/

/-! ### Commutations with the two-strand index shift (ng:commutation, sm-3:1929-1931) -/

/-- Two consecutive letters `a` then `b` are *disjoint gadgets* when the strands `b` acts on lie entirely
above the strands `a` touches or creates (`b.idx + b.arity ≤ a.idx`) or entirely below them
(`a.idx + a.coarity ≤ b.idx`).  Exchanging them keeps the exterior cuts; "the index changes track the same
physical positions after insertion or removal of two strands": a letter that moves past a gadget below it
keeps its index, a letter that moves past a gadget above it is shifted by that gadget's strand-count change
(`+2` past a left cusp, `−2` past a right cusp, `0` past a crossing).  One direction of the exchange. -/
def IsCommStep (W W' : Word) : Prop :=
  ∃ (X Y : Word) (a b : Letter), W = X ++ [a, b] ++ Y ∧
    ((b.idx + b.arity ≤ a.idx ∧ W' = X ++ [b, a.reindex (a.idx + b.coarity - b.arity)] ++ Y) ∨
     (a.idx + a.coarity ≤ b.idx ∧ W' = X ++ [b.reindex (b.idx + a.arity - a.coarity), a] ++ Y))

/-- Disjoint-gadget commutation, in either direction. -/
def IsComm (W W' : Word) : Prop := IsCommStep W W' ∨ IsCommStep W' W

/-! ### The three local front moves, deletion directions only (FR-6: "Only deletion directions of types I
and II occur here; type III, commutations and cusp-skein changes preserve s") -/

/-- ng:front-I (sm-3:1955-1956): the curl `l_m σ_{m−1} r_m` or `l_m σ_{m+1} r_m` on one through-strand is
deleted (`W ↦ W'`). -/
def IsTypeI (W W' : Word) : Prop :=
  ∃ (X Y : Word) (m : ℕ) (d : Bool),
    ((2 ≤ m ∧ W = X ++ [.l m d, .σ (m - 1), .r m] ++ Y) ∨ (1 ≤ m ∧ W = X ++ [.l m d, .σ (m + 1), .r m] ++ Y)) ∧
    W' = X ++ Y

/-- ng:front-II (sm-3:1977-1978, 1988-1989): `l_{m−1} σ_m σ_{m−1}` or `l_{m+1} σ_m σ_{m+1}` is replaced by
`l_m` (the bit is carried by the cusp arms through both crossings); the right-cusp versions "follow these
same local strands backwards": `σ_{m−1} σ_m r_{m−1}` or `σ_{m+1} σ_m r_{m+1}` is replaced by `r_m`. -/
def IsTypeII (W W' : Word) : Prop :=
  ∃ (X Y : Word) (m : ℕ),
    ((∃ d : Bool, 2 ≤ m ∧ W = X ++ [.l (m - 1) d, .σ m, .σ (m - 1)] ++ Y ∧ W' = X ++ [.l m d] ++ Y) ∨
     (∃ d : Bool, 1 ≤ m ∧ W = X ++ [.l (m + 1) d, .σ m, .σ (m + 1)] ++ Y ∧ W' = X ++ [.l m d] ++ Y) ∨
     (2 ≤ m ∧ W = X ++ [.σ (m - 1), .σ m, .r (m - 1)] ++ Y ∧ W' = X ++ [.r m] ++ Y) ∨
     (1 ≤ m ∧ W = X ++ [.σ (m + 1), .σ m, .r (m + 1)] ++ Y ∧ W' = X ++ [.r m] ++ Y))

/-- ng:front-III (sm-3:1995-1996): `σ_{m+1} σ_m σ_{m+1} ↔ σ_m σ_{m+1} σ_m`, either direction. -/
def IsTypeIII (W W' : Word) : Prop :=
  ∃ (X Y : Word) (m : ℕ), 1 ≤ m ∧
    ((W = X ++ [.σ (m + 1), .σ m, .σ (m + 1)] ++ Y ∧ W' = X ++ [.σ m, .σ (m + 1), .σ m] ++ Y) ∨
     (W = X ++ [.σ m, .σ (m + 1), .σ m] ++ Y ∧ W' = X ++ [.σ (m + 1), .σ m, .σ (m + 1)] ++ Y))

/-! ### The deletions (ng:deletions, ng:circle) -/

/-- ng:deletions, empty zigzag (sm-3:2014-2018): two consecutive cusps on one strand with no crossing,
`l_m r_{m+1}` (the strand passes below the new cusp) or `l_{m+1} r_m` (above), deleted. -/
def IsZigzagDeletion (W W' : Word) : Prop :=
  ∃ (X Y : Word) (m : ℕ) (d : Bool), 1 ≤ m ∧
    (W = X ++ [.l m d, .r (m + 1)] ++ Y ∨ W = X ++ [.l (m + 1) d, .r m] ++ Y) ∧ W' = X ++ Y

/-- ng:deletions, crossed-cusp shortcut (sm-3:2027-2037): `l_i σ_i ↦ l_i` with the cusp direction flipped
("the boundary arms exchange places"), and `σ_i r_i ↦ r_i`. -/
def IsCrossedCuspShortcut (W W' : Word) : Prop :=
  ∃ (X Y : Word) (i : ℕ), 1 ≤ i ∧
    ((∃ d : Bool, W = X ++ [.l i d, .σ i] ++ Y ∧ W' = X ++ [.l i (!d)] ++ Y) ∨
     (W = X ++ [.σ i, .r i] ++ Y ∧ W' = X ++ [.r i] ++ Y))

/-- ng:circle (sm-3:2046-2049): deletion of a separated standard front circle `l_m r_m` (no letter acts
between its two cusps, so it has no crossing; nesting allowed) with nonempty remainder. -/
def IsCircleDeletion (W W' : Word) : Prop :=
  ∃ (X Y : Word) (m : ℕ) (d : Bool), 1 ≤ m ∧ W = X ++ [.l m d, .r m] ++ Y ∧ W' = X ++ Y ∧ X ++ Y ≠ []

/-! ### The cusp-skein interchange (ng:cusp-skein, eq. ng:cusp-words, sm-3:2087-2126) -/

/-- One principal direction of the oriented cusp-skein interchange with spectator offset `m − 1`
(`m = 1` is the printed `A = l₂σ₁`, `A' = l₁σ₂`, `C_top = l₁`, `C_bottom = l₂`).  The through-strand is
the strand at position `m` of the cut `c₀` before the factor, with bit `a` (`t = +1 ↔ a = true`); the cusp
bit `d` gives `u = +1 ↔ d = false`.  `A'` carries the SAME bit `d` (the three right endpoints then have
the same bits `d, a, !d` in `A` and `A'`: identical boundary attachments).  The compatible smoothing pairs
"1 with 2 and L with 3" (`C_top = l_m`) when `t = u`, i.e. `a = !d`, and "L with 1 and 2 with 3"
(`C_bottom = l_{m+1}`) when `t = −u`, i.e. `a = d`; "the new cusp direction is u in either case": bit `d`. -/
def IsCuspSkeinStep (A A' C : Word) : Prop :=
  ∃ (X Y : Word) (m : ℕ) (d a : Bool) (P L : Cuts), 1 ≤ m ∧
    Word.run X [] = some (P ++ a :: L) ∧ P.length = m - 1 ∧
    A = X ++ [.l (m + 1) d, .σ m] ++ Y ∧ A' = X ++ [.l m d, .σ (m + 1)] ++ Y ∧
    ((a = !d ∧ C = X ++ [.l m d] ++ Y) ∨ (a = d ∧ C = X ++ [.l (m + 1) d] ++ Y))

/-- The oriented cusp-skein interchange in either principal direction ("or its reflected pattern": the
reflection `z ↦ −z` of `l₂σ₁` is `l₁σ₂`), with its unique compatible smoothing `C`. -/
def IsCuspSkein (A A' C : Word) : Prop := IsCuspSkeinStep A A' C ∨ IsCuspSkeinStep A' A C

/-! ## 4. Each pattern keeps the exterior cuts: closedness is preserved -/

section Closedness

open Letter Word

/-- unfolding the run of one, two, three letters -/
theorem run_one_iff {a : Letter} {c c' : Cuts} : Word.run [a] c = some c' ↔ a.step c = some c' := by
  simp only [run_cons, run_nil, Option.bind_eq_some_iff, Option.some.injEq, exists_eq_right]

theorem run_two_iff {a b : Letter} {c c' : Cuts} :
    Word.run [a, b] c = some c' ↔ ∃ c₁, a.step c = some c₁ ∧ b.step c₁ = some c' := by
  simp only [run_cons, run_nil, Option.bind_eq_some_iff, Option.some.injEq, exists_eq_right]

theorem run_three_iff {a b e : Letter} {c c' : Cuts} :
    Word.run [a, b, e] c = some c' ↔
      ∃ c₁, a.step c = some c₁ ∧ ∃ c₂, b.step c₁ = some c₂ ∧ e.step c₂ = some c' := by
  simp only [run_cons, run_nil, Option.bind_eq_some_iff, Option.some.injEq, exists_eq_right]

/-- discharges the index and length side conditions of `step_prefix` / `step_of_prefix` -/
macro "idxomega" : tactic =>
  `(tactic| ((try simp only [Letter.idx, Letter.idx_reindex, List.length_append, List.length_singleton,
      List.length_cons, List.length_nil] at *) <;> omega))

/-- the same for generic letters (no unfolding of `idx`) -/
macro "lenomega" : tactic =>
  `(tactic| ((try simp only [Letter.idx_reindex, List.length_append, List.length_singleton,
      List.length_cons, List.length_nil] at *) <;> omega))

/-- split a list at a length -/
theorem exists_split (c : Cuts) (n : ℕ) (h : n ≤ c.length) : ∃ A B : Cuts, c = A ++ B ∧ A.length = n :=
  ⟨c.take n, c.drop n, (List.take_append_drop n c).symm, by simp only [List.length_take]; omega⟩

theorem exists_split_last (A : Cuts) (n : ℕ) (h : A.length = n + 1) :
    ∃ (A' : Cuts) (a : Bool), A = A' ++ [a] ∧ A'.length = n := by
  obtain ⟨A', B, rfl, hA'⟩ := exists_split A n (by omega)
  have hB : B.length = 1 := by simp only [List.length_append] at h; omega
  obtain ⟨a, rfl⟩ := List.length_eq_one_iff.1 hB
  exact ⟨A', a, rfl, hA'⟩

/-- a crossing typed at `m + 1` on `A ++ d :: L` with `|A| = m` needs a strand below `d` -/
theorem exists_cons_of_σ_succ {m : ℕ} {A L c₁ : Cuts} {d : Bool} (hA : A.length = m)
    (h : (Letter.σ (m + 1)).step (A ++ d :: L) = some c₁) : ∃ b L₀, L = b :: L₀ := by
  rw [step_prefix (ℓ := .σ (m + 1)) (by idxomega) (by idxomega)] at h
  obtain ⟨L₂', hL₂, -⟩ := Option.map_eq_some_iff.1 h
  obtain ⟨p, q, L₃, hpq, -⟩ := act_σ_eq_some_iff.1 hL₂
  cases L with
  | nil => simp at hpq
  | cons b L₀ => exact ⟨b, L₀, rfl⟩

/-! ### Type I -/

theorem run_typeI_left {m : ℕ} {d : Bool} {c c' : Cuts} (hm : 2 ≤ m)
    (h : Word.run [.l m d, .σ (m - 1), .r m] c = some c') : c' = c := by
  rw [run_three_iff] at h
  obtain ⟨c₁, h1, c₂, h2, h3⟩ := h
  obtain ⟨A, L, L', -, hA, rfl, hL, rfl⟩ := step_eq_some_iff.1 h1
  simp only [act_l, Option.some.injEq, idx] at hL hA
  subst hL
  obtain ⟨A', a, rfl, hA'⟩ := exists_split_last A (m - 2) (by omega)
  rw [List.append_assoc, List.singleton_append,
    step_of_prefix (ℓ := .σ (m - 1)) (by idxomega) (by idxomega) (act_σ_cons _ _ _ _)] at h2
  obtain rfl := Option.some.inj h2
  rw [show A' ++ d :: a :: (!d) :: L = (A' ++ [d]) ++ a :: (!d) :: L by simp,
    step_prefix (ℓ := .r m) (by idxomega) (by idxomega), act_r_cons] at h3
  split_ifs at h3 with had
  · simp only [Option.map_some, Option.some.injEq] at h3
    obtain rfl : a = d := Bool.not_eq_not.mp had
    rw [← h3]
  · simp at h3

theorem run_typeI_right {m : ℕ} {d : Bool} {c c' : Cuts} (hm : 1 ≤ m)
    (h : Word.run [.l m d, .σ (m + 1), .r m] c = some c') : c' = c := by
  rw [run_three_iff] at h
  obtain ⟨c₁, h1, c₂, h2, h3⟩ := h
  obtain ⟨A, L, L', -, hA, rfl, hL, rfl⟩ := step_eq_some_iff.1 h1
  simp only [act_l, Option.some.injEq, idx] at hL hA
  subst hL
  obtain ⟨b, L₀, rfl⟩ : ∃ b L₀, L = b :: L₀ :=
    exists_cons_of_σ_succ (m := m) (A := A ++ [d]) (by idxomega)
      (by rw [show (A ++ [d]) ++ (!d) :: L = A ++ d :: (!d) :: L by simp]; exact h2)
  rw [show A ++ d :: (!d) :: b :: L₀ = (A ++ [d]) ++ (!d) :: b :: L₀ by simp,
    step_of_prefix (ℓ := .σ (m + 1)) (by idxomega) (by idxomega) (act_σ_cons _ _ _ _)] at h2
  obtain rfl := Option.some.inj h2
  rw [show A ++ [d] ++ b :: (!d) :: L₀ = A ++ d :: b :: (!d) :: L₀ by simp,
    step_prefix (ℓ := .r m) (by idxomega) (by idxomega), act_r_cons] at h3
  split_ifs at h3 with hdb
  · simp only [Option.map_some, Option.some.injEq] at h3
    obtain rfl : b = !d := Bool.eq_not.mpr (Ne.symm hdb)
    exact h3.symm
  · simp at h3

theorem IsTypeI.closed {W W' : Word} (h : IsTypeI W W') (hW : W.Closed) : W'.Closed := by
  obtain ⟨X, Y, m, d, hpat, rfl⟩ := h
  rcases hpat with ⟨hm, rfl⟩ | ⟨hm, rfl⟩
  · have := Closed.replace (P' := []) hW (fun c c' h => by obtain rfl := run_typeI_left hm h; rfl)
    simpa using this
  · have := Closed.replace (P' := []) hW (fun c c' h => by obtain rfl := run_typeI_right hm h; rfl)
    simpa using this

/-! ### Type II -/

theorem run_typeII_l_left {m : ℕ} {d : Bool} {c c' : Cuts} (hm : 2 ≤ m)
    (h : Word.run [.l (m - 1) d, .σ m, .σ (m - 1)] c = some c') : Word.run [.l m d] c = some c' := by
  rw [run_three_iff] at h
  rw [run_one_iff]
  obtain ⟨c₁, h1, c₂, h2, h3⟩ := h
  obtain ⟨A, L, L', -, hA, rfl, hL, rfl⟩ := step_eq_some_iff.1 h1
  simp only [act_l, Option.some.injEq, idx] at hL hA
  subst hL
  obtain ⟨b, L₀, rfl⟩ : ∃ b L₀, L = b :: L₀ := by
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    exact exists_cons_of_σ_succ (m := m') (A := A ++ [d]) (by idxomega)
      (by rw [show (A ++ [d]) ++ (!d) :: L = A ++ d :: (!d) :: L by simp]; exact h2)
  rw [show A ++ d :: (!d) :: b :: L₀ = (A ++ [d]) ++ (!d) :: b :: L₀ by simp,
    step_of_prefix (ℓ := .σ m) (by idxomega) (by idxomega) (act_σ_cons _ _ _ _)] at h2
  obtain rfl := Option.some.inj h2
  rw [show A ++ [d] ++ b :: (!d) :: L₀ = A ++ d :: b :: (!d) :: L₀ by simp,
    step_of_prefix (ℓ := .σ (m - 1)) (by idxomega) (by idxomega) (act_σ_cons _ _ _ _)] at h3
  obtain rfl := Option.some.inj h3
  rw [show A ++ b :: L₀ = (A ++ [b]) ++ L₀ by simp,
    step_of_prefix (ℓ := .l m d) (by idxomega) (by idxomega) (act_l _ _ _)]
  simp

theorem run_typeII_l_right {m : ℕ} {d : Bool} {c c' : Cuts} (hm : 1 ≤ m)
    (h : Word.run [.l (m + 1) d, .σ m, .σ (m + 1)] c = some c') : Word.run [.l m d] c = some c' := by
  rw [run_three_iff] at h
  rw [run_one_iff]
  obtain ⟨c₁, h1, c₂, h2, h3⟩ := h
  obtain ⟨A, L, L', -, hA, rfl, hL, rfl⟩ := step_eq_some_iff.1 h1
  simp only [act_l, Option.some.injEq, idx] at hL hA
  subst hL
  obtain ⟨A', b, rfl, hA'⟩ := exists_split_last A (m - 1) (by omega)
  rw [List.append_assoc, List.singleton_append,
    step_of_prefix (ℓ := .σ m) (by idxomega) (by idxomega) (act_σ_cons _ _ _ _)] at h2
  obtain rfl := Option.some.inj h2
  rw [show A' ++ d :: b :: (!d) :: L = (A' ++ [d]) ++ b :: (!d) :: L by simp,
    step_of_prefix (ℓ := .σ (m + 1)) (by idxomega) (by idxomega) (act_σ_cons _ _ _ _)] at h3
  obtain rfl := Option.some.inj h3
  rw [List.append_assoc, List.singleton_append,
    step_of_prefix (ℓ := .l m d) (by idxomega) (by idxomega) (act_l _ _ _)]
  simp

theorem run_typeII_r_left {m : ℕ} {c c' : Cuts} (hm : 2 ≤ m)
    (h : Word.run [.σ (m - 1), .σ m, .r (m - 1)] c = some c') : Word.run [.r m] c = some c' := by
  rw [run_three_iff] at h
  rw [run_one_iff]
  obtain ⟨c₁, h1, c₂, h2, h3⟩ := h
  obtain ⟨A, L, L', -, hA, rfl, hL, rfl⟩ := step_eq_some_iff.1 h1
  obtain ⟨p, q, L₀, rfl, rfl⟩ := act_σ_eq_some_iff.1 hL
  simp only [idx] at hA
  obtain ⟨r, L₁, rfl⟩ : ∃ r L₁, L₀ = r :: L₁ := by
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    exact exists_cons_of_σ_succ (m := m') (A := A ++ [q]) (by idxomega)
      (by rw [show (A ++ [q]) ++ p :: L₀ = A ++ q :: p :: L₀ by simp]; exact h2)
  rw [show A ++ q :: p :: r :: L₁ = (A ++ [q]) ++ p :: r :: L₁ by simp,
    step_of_prefix (ℓ := .σ m) (by idxomega) (by idxomega) (act_σ_cons _ _ _ _)] at h2
  obtain rfl := Option.some.inj h2
  rw [show A ++ [q] ++ r :: p :: L₁ = A ++ q :: r :: p :: L₁ by simp,
    step_prefix (ℓ := .r (m - 1)) (by idxomega) (by idxomega), act_r_cons] at h3
  split_ifs at h3 with hqr
  · simp only [Option.map_some, Option.some.injEq] at h3
    subst h3
    rw [show A ++ p :: q :: r :: L₁ = (A ++ [p]) ++ q :: r :: L₁ by simp,
      step_prefix (ℓ := .r m) (by idxomega) (by idxomega), act_r_cons, ite_eq_left hqr]
    simp
  · simp at h3

theorem run_typeII_r_right {m : ℕ} {c c' : Cuts} (hm : 1 ≤ m)
    (h : Word.run [.σ (m + 1), .σ m, .r (m + 1)] c = some c') : Word.run [.r m] c = some c' := by
  rw [run_three_iff] at h
  rw [run_one_iff]
  obtain ⟨c₁, h1, c₂, h2, h3⟩ := h
  obtain ⟨A, L, L', -, hA, rfl, hL, rfl⟩ := step_eq_some_iff.1 h1
  obtain ⟨q, r, L₀, rfl, rfl⟩ := act_σ_eq_some_iff.1 hL
  simp only [idx] at hA
  obtain ⟨A', p, rfl, hA'⟩ := exists_split_last A (m - 1) (by omega)
  rw [List.append_assoc, List.singleton_append,
    step_of_prefix (ℓ := .σ m) (by idxomega) (by idxomega) (act_σ_cons _ _ _ _)] at h2
  obtain rfl := Option.some.inj h2
  rw [show A' ++ r :: p :: q :: L₀ = (A' ++ [r]) ++ p :: q :: L₀ by simp,
    step_prefix (ℓ := .r (m + 1)) (by idxomega) (by idxomega), act_r_cons] at h3
  split_ifs at h3 with hpq
  · simp only [Option.map_some, Option.some.injEq] at h3
    subst h3
    rw [List.append_assoc, List.singleton_append, step_prefix (ℓ := .r m) (by idxomega) (by idxomega),
      act_r_cons, ite_eq_left hpq]
    simp
  · simp at h3

theorem IsTypeII.closed {W W' : Word} (h : IsTypeII W W') (hW : W.Closed) : W'.Closed := by
  obtain ⟨X, Y, m, hpat⟩ := h
  rcases hpat with ⟨d, hm, rfl, rfl⟩ | ⟨d, hm, rfl, rfl⟩ | ⟨hm, rfl, rfl⟩ | ⟨hm, rfl, rfl⟩
  · exact Closed.replace hW (fun c c' h => run_typeII_l_left hm h)
  · exact Closed.replace hW (fun c c' h => run_typeII_l_right hm h)
  · exact Closed.replace hW (fun c c' h => run_typeII_r_left hm h)
  · exact Closed.replace hW (fun c c' h => run_typeII_r_right hm h)

/-! ### Type III -/

/-- both braid words permute three consecutive strands `p q r ↦ r q p` -/
theorem run_typeIII_aux {m : ℕ} {c c' : Cuts} (hm : 1 ≤ m)
    (h : Word.run [.σ (m + 1), .σ m, .σ (m + 1)] c = some c') :
    ∃ (A : Cuts) (p q r : Bool) (L : Cuts), A.length = m - 1 ∧ c = A ++ p :: q :: r :: L ∧
      c' = A ++ r :: q :: p :: L := by
  rw [run_three_iff] at h
  obtain ⟨c₁, h1, c₂, h2, h3⟩ := h
  obtain ⟨A, L, L', -, hA, rfl, hL, rfl⟩ := step_eq_some_iff.1 h1
  obtain ⟨q, r, L₀, rfl, rfl⟩ := act_σ_eq_some_iff.1 hL
  simp only [idx] at hA
  obtain ⟨A', p, rfl, hA'⟩ := exists_split_last A (m - 1) (by omega)
  rw [List.append_assoc, List.singleton_append,
    step_of_prefix (ℓ := .σ m) (by idxomega) (by idxomega) (act_σ_cons _ _ _ _)] at h2
  obtain rfl := Option.some.inj h2
  rw [show A' ++ r :: p :: q :: L₀ = (A' ++ [r]) ++ p :: q :: L₀ by simp,
    step_of_prefix (ℓ := .σ (m + 1)) (by idxomega) (by idxomega) (act_σ_cons _ _ _ _)] at h3
  obtain rfl := Option.some.inj h3
  exact ⟨A', p, q, r, L₀, hA', by simp, by simp⟩

theorem run_typeIII_aux' {m : ℕ} {c c' : Cuts} (hm : 1 ≤ m)
    (h : Word.run [.σ m, .σ (m + 1), .σ m] c = some c') :
    ∃ (A : Cuts) (p q r : Bool) (L : Cuts), A.length = m - 1 ∧ c = A ++ p :: q :: r :: L ∧
      c' = A ++ r :: q :: p :: L := by
  rw [run_three_iff] at h
  obtain ⟨c₁, h1, c₂, h2, h3⟩ := h
  obtain ⟨A, L, L', -, hA, rfl, hL, rfl⟩ := step_eq_some_iff.1 h1
  obtain ⟨p, q, L₀, rfl, rfl⟩ := act_σ_eq_some_iff.1 hL
  simp only [idx] at hA
  obtain ⟨r, L₁, rfl⟩ : ∃ r L₁, L₀ = r :: L₁ :=
    exists_cons_of_σ_succ (m := m) (A := A ++ [q]) (by idxomega)
      (by rw [show (A ++ [q]) ++ p :: L₀ = A ++ q :: p :: L₀ by simp]; exact h2)
  rw [show A ++ q :: p :: r :: L₁ = (A ++ [q]) ++ p :: r :: L₁ by simp,
    step_of_prefix (ℓ := .σ (m + 1)) (by idxomega) (by idxomega) (act_σ_cons _ _ _ _)] at h2
  obtain rfl := Option.some.inj h2
  rw [show A ++ [q] ++ r :: p :: L₁ = A ++ q :: r :: p :: L₁ by simp,
    step_of_prefix (ℓ := .σ m) (by idxomega) (by idxomega) (act_σ_cons _ _ _ _)] at h3
  obtain rfl := Option.some.inj h3
  exact ⟨A, p, q, r, L₁, hA, rfl, rfl⟩

theorem run_typeIII_of_split {m : ℕ} {A L : Cuts} {p q r : Bool} (hm : 1 ≤ m) (hA : A.length = m - 1) :
    Word.run [.σ (m + 1), .σ m, .σ (m + 1)] (A ++ p :: q :: r :: L) = some (A ++ r :: q :: p :: L) ∧
    Word.run [.σ m, .σ (m + 1), .σ m] (A ++ p :: q :: r :: L) = some (A ++ r :: q :: p :: L) := by
  rw [run_three_iff, run_three_iff]
  constructor
  · refine ⟨A ++ p :: r :: q :: L, ?_, A ++ r :: p :: q :: L, ?_, ?_⟩
    · rw [show A ++ p :: q :: r :: L = (A ++ [p]) ++ q :: r :: L by simp,
        step_of_prefix (ℓ := .σ (m + 1)) (by idxomega) (by idxomega) (act_σ_cons _ _ _ _)]
      simp
    · exact step_of_prefix (ℓ := .σ m) (by idxomega) (by idxomega) (act_σ_cons _ _ _ _)
    · rw [show A ++ r :: p :: q :: L = (A ++ [r]) ++ p :: q :: L by simp,
        step_of_prefix (ℓ := .σ (m + 1)) (by idxomega) (by idxomega) (act_σ_cons _ _ _ _)]
      simp
  · refine ⟨A ++ q :: p :: r :: L, ?_, A ++ q :: r :: p :: L, ?_, ?_⟩
    · exact step_of_prefix (ℓ := .σ m) (by idxomega) (by idxomega) (act_σ_cons _ _ _ _)
    · rw [show A ++ q :: p :: r :: L = (A ++ [q]) ++ p :: r :: L by simp,
        step_of_prefix (ℓ := .σ (m + 1)) (by idxomega) (by idxomega) (act_σ_cons _ _ _ _)]
      simp
    · exact step_of_prefix (ℓ := .σ m) (by idxomega) (by idxomega) (act_σ_cons _ _ _ _)

theorem IsTypeIII.closed {W W' : Word} (h : IsTypeIII W W') (hW : W.Closed) : W'.Closed := by
  obtain ⟨X, Y, m, hm, hpat⟩ := h
  rcases hpat with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · refine Closed.replace hW (fun c c' h => ?_)
    obtain ⟨A, p, q, r, L, hA, rfl, rfl⟩ := run_typeIII_aux hm h
    exact (run_typeIII_of_split hm hA).2
  · refine Closed.replace hW (fun c c' h => ?_)
    obtain ⟨A, p, q, r, L, hA, rfl, rfl⟩ := run_typeIII_aux' hm h
    exact (run_typeIII_of_split hm hA).1

/-! ### Zigzag, crossed cusp, circle -/

theorem run_zigzag_below {m : ℕ} {d : Bool} {c c' : Cuts} (hm : 1 ≤ m)
    (h : Word.run [.l m d, .r (m + 1)] c = some c') : c' = c := by
  rw [run_two_iff] at h
  obtain ⟨c₁, h1, h2⟩ := h
  obtain ⟨A, L, L', -, hA, rfl, hL, rfl⟩ := step_eq_some_iff.1 h1
  simp only [act_l, Option.some.injEq, idx] at hL hA
  subst hL
  rw [show A ++ d :: (!d) :: L = (A ++ [d]) ++ (!d) :: L by simp,
    step_prefix (ℓ := .r (m + 1)) (by idxomega) (by idxomega)] at h2
  obtain ⟨L₁, hL₁, rfl⟩ := Option.map_eq_some_iff.1 h2
  obtain ⟨p, q, hpq, hne⟩ := act_r_eq_some_iff.1 hL₁
  cases L with
  | nil => simp at hpq
  | cons b L₀ =>
    simp only [List.cons.injEq] at hpq
    obtain ⟨hp, hq, hL⟩ := hpq
    subst hp hq hL
    obtain rfl : b = d := Bool.not_eq_not.mp (Ne.symm hne)
    simp

theorem run_zigzag_above {m : ℕ} {d : Bool} {c c' : Cuts} (hm : 1 ≤ m)
    (h : Word.run [.l (m + 1) d, .r m] c = some c') : c' = c := by
  rw [run_two_iff] at h
  obtain ⟨c₁, h1, h2⟩ := h
  obtain ⟨A, L, L', -, hA, rfl, hL, rfl⟩ := step_eq_some_iff.1 h1
  simp only [act_l, Option.some.injEq, idx] at hL hA
  subst hL
  obtain ⟨A', b, rfl, hA'⟩ := exists_split_last A (m - 1) (by omega)
  rw [List.append_assoc, List.singleton_append, step_prefix (ℓ := .r m) (by idxomega) (by idxomega),
    act_r_cons] at h2
  split_ifs at h2 with hbd
  · simp only [Option.map_some, Option.some.injEq] at h2
    obtain rfl : b = !d := Bool.eq_not.mpr hbd
    rw [← h2]
    simp
  · simp at h2

theorem IsZigzagDeletion.closed {W W' : Word} (h : IsZigzagDeletion W W') (hW : W.Closed) : W'.Closed := by
  obtain ⟨X, Y, m, d, hm, hpat, rfl⟩ := h
  rcases hpat with rfl | rfl
  · have := Closed.replace (P' := []) hW (fun c c' h => by obtain rfl := run_zigzag_below hm h; rfl)
    simpa using this
  · have := Closed.replace (P' := []) hW (fun c c' h => by obtain rfl := run_zigzag_above hm h; rfl)
    simpa using this

theorem run_crossedCusp_l {i : ℕ} {d : Bool} {c c' : Cuts} (hi : 1 ≤ i)
    (h : Word.run [.l i d, .σ i] c = some c') : Word.run [.l i (!d)] c = some c' := by
  rw [run_two_iff] at h
  rw [run_one_iff]
  obtain ⟨c₁, h1, h2⟩ := h
  obtain ⟨A, L, L', -, hA, rfl, hL, rfl⟩ := step_eq_some_iff.1 h1
  simp only [act_l, Option.some.injEq, idx] at hL hA
  subst hL
  rw [step_of_prefix (ℓ := .σ i) (by idxomega) (by idxomega) (act_σ_cons _ _ _ _)] at h2
  obtain rfl := Option.some.inj h2
  rw [step_of_prefix (ℓ := .l i (!d)) (by idxomega) (by idxomega) (act_l _ _ _)]
  simp

theorem run_crossedCusp_r {i : ℕ} {c c' : Cuts} (hi : 1 ≤ i)
    (h : Word.run [.σ i, .r i] c = some c') : Word.run [.r i] c = some c' := by
  rw [run_two_iff] at h
  rw [run_one_iff]
  obtain ⟨c₁, h1, h2⟩ := h
  obtain ⟨A, L, L', -, hA, rfl, hL, rfl⟩ := step_eq_some_iff.1 h1
  obtain ⟨p, q, L₀, rfl, rfl⟩ := act_σ_eq_some_iff.1 hL
  simp only [idx] at hA
  rw [step_prefix (ℓ := .r i) (by idxomega) (by idxomega), act_r_cons] at h2
  split_ifs at h2 with hqp
  · simp only [Option.map_some, Option.some.injEq] at h2
    subst h2
    rw [step_prefix (ℓ := .r i) (by idxomega) (by idxomega), act_r_cons, ite_eq_left (Ne.symm hqp)]
    simp
  · simp at h2

theorem IsCrossedCuspShortcut.closed {W W' : Word} (h : IsCrossedCuspShortcut W W') (hW : W.Closed) :
    W'.Closed := by
  obtain ⟨X, Y, i, hi, hpat⟩ := h
  rcases hpat with ⟨d, rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact Closed.replace hW (fun c c' h => run_crossedCusp_l hi h)
  · exact Closed.replace hW (fun c c' h => run_crossedCusp_r hi h)

theorem run_circle {m : ℕ} {d : Bool} {c c' : Cuts} (hm : 1 ≤ m)
    (h : Word.run [.l m d, .r m] c = some c') : c' = c := by
  rw [run_two_iff] at h
  obtain ⟨c₁, h1, h2⟩ := h
  obtain ⟨A, L, L', -, hA, rfl, hL, rfl⟩ := step_eq_some_iff.1 h1
  simp only [act_l, Option.some.injEq, idx] at hL hA
  subst hL
  rw [step_prefix (ℓ := .r m) (by idxomega) (by idxomega), act_r_cons] at h2
  split_ifs at h2 with hdd
  · simp only [Option.map_some, Option.some.injEq] at h2
    exact h2.symm
  · simp at h2

theorem IsCircleDeletion.closed {W W' : Word} (h : IsCircleDeletion W W') (hW : W.Closed) : W'.Closed := by
  obtain ⟨X, Y, m, d, hm, rfl, rfl, -⟩ := h
  have := Closed.replace (P' := []) hW (fun c c' h => by obtain rfl := run_circle hm h; rfl)
  simpa using this

/-! ### Cusp-skein: `A`, `A'` and the compatible `C` have the same output cut -/

theorem run_skein_A {m : ℕ} {d a : Bool} {P L : Cuts} (hm : 1 ≤ m) (hP : P.length = m - 1) :
    Word.run [.l (m + 1) d, .σ m] (P ++ a :: L) = some (P ++ d :: a :: (!d) :: L) := by
  rw [run_two_iff]
  refine ⟨P ++ a :: d :: (!d) :: L, ?_, ?_⟩
  · rw [show P ++ a :: L = (P ++ [a]) ++ L by simp,
      step_of_prefix (ℓ := .l (m + 1) d) (by idxomega) (by idxomega) (act_l _ _ _)]
    simp
  · exact step_of_prefix (ℓ := .σ m) (by idxomega) (by idxomega) (act_σ_cons _ _ _ _)

theorem run_skein_A' {m : ℕ} {d a : Bool} {P L : Cuts} (hm : 1 ≤ m) (hP : P.length = m - 1) :
    Word.run [.l m d, .σ (m + 1)] (P ++ a :: L) = some (P ++ d :: a :: (!d) :: L) := by
  rw [run_two_iff]
  refine ⟨P ++ d :: (!d) :: a :: L, ?_, ?_⟩
  · exact step_of_prefix (ℓ := .l m d) (by idxomega) (by idxomega) (act_l _ _ _)
  · rw [show P ++ d :: (!d) :: a :: L = (P ++ [d]) ++ (!d) :: a :: L by simp,
      step_of_prefix (ℓ := .σ (m + 1)) (by idxomega) (by idxomega) (act_σ_cons _ _ _ _)]
    simp

theorem run_skein_Ctop {m : ℕ} {d : Bool} {P L : Cuts} (hm : 1 ≤ m) (hP : P.length = m - 1) :
    Word.run [.l m d] (P ++ (!d) :: L) = some (P ++ d :: (!d) :: (!d) :: L) := by
  rw [run_one_iff]
  exact step_of_prefix (ℓ := .l m d) (by idxomega) (by idxomega) (act_l _ _ _)

theorem run_skein_Cbottom {m : ℕ} {d : Bool} {P L : Cuts} (hm : 1 ≤ m) (hP : P.length = m - 1) :
    Word.run [.l (m + 1) d] (P ++ d :: L) = some (P ++ d :: d :: (!d) :: L) := by
  rw [run_one_iff, show P ++ d :: L = (P ++ [d]) ++ L by simp,
    step_of_prefix (ℓ := .l (m + 1) d) (by idxomega) (by idxomega) (act_l _ _ _)]
  simp

/-- the cut before a factor of a closed word is determined by the prefix -/
theorem run_prefix_unique {X P Y : Word} {c : Cuts} (hW : (X ++ P ++ Y).Closed) (hX : Word.run X [] = some c) :
    ∃ c₁, Word.run P c = some c₁ ∧ Word.run Y c₁ = some [] := by
  obtain ⟨c₀, c₁, hX', hP, hY⟩ := hW.exists_run
  rw [hX] at hX'
  obtain rfl := Option.some.inj hX'
  exact ⟨c₁, hP, hY⟩

theorem IsCuspSkeinStep.closed_A' {A A' C : Word} (h : IsCuspSkeinStep A A' C) (hA : A.Closed) : A'.Closed := by
  obtain ⟨X, Y, m, d, a, P, L, hm, hX, hP, rfl, rfl, -⟩ := h
  obtain ⟨c₁, hPA, hY⟩ := run_prefix_unique hA hX
  unfold Closed
  rw [run_append, run_append, hX, Option.bind_some, run_skein_A' hm hP, Option.bind_some]
  rw [run_skein_A hm hP] at hPA
  obtain rfl := Option.some.inj hPA
  exact hY

theorem IsCuspSkeinStep.closed_C {A A' C : Word} (h : IsCuspSkeinStep A A' C) (hA : A.Closed) : C.Closed := by
  obtain ⟨X, Y, m, d, a, P, L, hm, hX, hP, rfl, rfl, hC⟩ := h
  obtain ⟨c₁, hPA, hY⟩ := run_prefix_unique hA hX
  rw [run_skein_A hm hP] at hPA
  obtain rfl := Option.some.inj hPA
  rcases hC with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · unfold Closed
    rw [run_append, run_append, hX, Option.bind_some, run_skein_Ctop hm hP, Option.bind_some]
    simpa using hY
  · unfold Closed
    rw [run_append, run_append, hX, Option.bind_some, run_skein_Cbottom hm hP, Option.bind_some]
    exact hY

theorem IsCuspSkeinStep.closed_A {A A' C : Word} (h : IsCuspSkeinStep A A' C) (hA' : A'.Closed) : A.Closed := by
  obtain ⟨X, Y, m, d, a, P, L, hm, hX, hP, rfl, rfl, -⟩ := h
  obtain ⟨c₁, hPA', hY⟩ := run_prefix_unique hA' hX
  unfold Closed
  rw [run_append, run_append, hX, Option.bind_some, run_skein_A hm hP, Option.bind_some]
  rw [run_skein_A' hm hP] at hPA'
  obtain rfl := Option.some.inj hPA'
  exact hY

theorem IsCuspSkein.closed_A' {A A' C : Word} (h : IsCuspSkein A A' C) (hA : A.Closed) : A'.Closed := by
  rcases h with h | h
  · exact h.closed_A' hA
  · exact h.closed_A hA

theorem IsCuspSkein.closed_C {A A' C : Word} (h : IsCuspSkein A A' C) (hA : A.Closed) : C.Closed := by
  rcases h with h | h
  · exact h.closed_C hA
  · exact h.closed_C (h.closed_A hA)

/-! ### Commutations: the general disjoint-gadget argument (uniform over the letter kinds) -/

/-- `b` acts above `a`: exchanging them (with `a` reindexed through `b`) keeps the cut. -/
theorem run_comm_above {a b : Letter} {c c' : Cuts} (hab : b.idx + b.arity ≤ a.idx)
    (h : Word.run [a, b] c = some c') :
    Word.run [b, a.reindex (a.idx + b.coarity - b.arity)] c = some c' := by
  rw [run_two_iff] at h
  rw [run_two_iff]
  obtain ⟨c₁, h1, h2⟩ := h
  obtain ⟨A, L, L', ha1, hA, rfl, hL, rfl⟩ := step_eq_some_iff.1 h1
  obtain ⟨B, M, M', hb1, hB, hc₁, hM, rfl⟩ := step_eq_some_iff.1 h2
  obtain ⟨w, w', R, rfl, hw, hw', hw'len, rfl⟩ := act_window hM
  -- `A = B ++ w ++ H`
  obtain ⟨A₁, H, rfl, hA₁⟩ := exists_split A (b.idx - 1 + b.arity) (by omega)
  have hlen : A₁.length = (B ++ w).length := by simp only [List.length_append]; omega
  rw [List.append_assoc, ← List.append_assoc B w R] at hc₁
  obtain ⟨rfl, hR⟩ := List.append_inj hc₁ hlen
  refine ⟨B ++ w' ++ H ++ L, ?_, ?_⟩
  · rw [show B ++ w ++ H ++ L = B ++ (w ++ (H ++ L)) by simp only [List.append_assoc],
      step_of_prefix hb1 hB (L' := w' ++ (H ++ L)) (by rw [act_append hw, hw']; rfl)]
    simp only [List.append_assoc]
  · rw [show B ++ w' ++ H ++ L = (B ++ w' ++ H) ++ L by simp only [List.append_assoc],
      step_of_prefix (ℓ := a.reindex _) (A := B ++ w' ++ H) (by lenomega) (by lenomega)
        (by rw [act_reindex]; exact hL)]
    rw [← hR]
    simp only [List.append_assoc]

/-- `b` acts below `a`: exchanging them (with `b` reindexed through `a`) keeps the cut. -/
theorem run_comm_below {a b : Letter} {c c' : Cuts} (hab : a.idx + a.coarity ≤ b.idx)
    (h : Word.run [a, b] c = some c') :
    Word.run [b.reindex (b.idx + a.arity - a.coarity), a] c = some c' := by
  rw [run_two_iff] at h
  rw [run_two_iff]
  obtain ⟨c₁, h1, h2⟩ := h
  obtain ⟨A, L, L', ha1, hA, rfl, hL, rfl⟩ := step_eq_some_iff.1 h1
  obtain ⟨w, w', R, rfl, hw, hw', hw'len, rfl⟩ := act_window hL
  obtain ⟨B, M, M', hb1, hB, hc₁, hM, rfl⟩ := step_eq_some_iff.1 h2
  -- `B = A ++ w' ++ H`
  obtain ⟨B₁, H, rfl, hB₁⟩ := exists_split B (a.idx - 1 + a.coarity) (by omega)
  have hlen : (A ++ w').length = B₁.length := by simp only [List.length_append]; omega
  rw [← List.append_assoc, List.append_assoc B₁ H M] at hc₁
  obtain ⟨hB₁eq, hR⟩ := List.append_inj hc₁ hlen
  subst hB₁eq
  refine ⟨A ++ w ++ H ++ M', ?_, ?_⟩
  · rw [hR, show A ++ (w ++ (H ++ M)) = (A ++ w ++ H) ++ M by simp only [List.append_assoc],
      step_of_prefix (ℓ := b.reindex _) (A := A ++ w ++ H) (by lenomega) (by lenomega)
        (by rw [act_reindex]; exact hM)]
  · rw [show A ++ w ++ H ++ M' = A ++ (w ++ (H ++ M')) by simp only [List.append_assoc],
      step_of_prefix ha1 hA (L' := w' ++ (H ++ M')) (by rw [act_append hw, hw']; rfl)]
    simp only [List.append_assoc]

theorem IsCommStep.closed {W W' : Word} (h : IsCommStep W W') (hW : W.Closed) : W'.Closed := by
  obtain ⟨X, Y, a, b, rfl, hpat⟩ := h
  rcases hpat with ⟨hab, rfl⟩ | ⟨hab, rfl⟩
  · exact Closed.replace hW (fun c c' h => run_comm_above hab h)
  · exact Closed.replace hW (fun c c' h => run_comm_below hab h)

theorem IsComm.closed {W W' : Word} (h : IsComm W W') (hW : W.Closed) : W'.Closed := by
  rcases h with h | h
  · exact h.closed hW
  · -- the reverse direction: the exchanged pair is itself a disjoint pair, exchanged back
    obtain ⟨X, Y, a, b, rfl, hpat⟩ := h
    rcases hpat with ⟨hab, rfl⟩ | ⟨hab, rfl⟩
    · refine Closed.replace hW (fun c c' h => ?_)
      have hb : b.idx + b.coarity ≤ (a.reindex (a.idx + b.coarity - b.arity)).idx := by
        rw [idx_reindex]; omega
      have := run_comm_below hb h
      rwa [idx_reindex, reindex_reindex,
        show a.idx + b.coarity - b.arity + b.arity - b.coarity = a.idx by omega, reindex_self] at this
    · refine Closed.replace hW (fun c c' h => ?_)
      have hb : a.idx + a.arity ≤ (b.reindex (b.idx + a.arity - a.coarity)).idx := by
        rw [idx_reindex]; omega
      have := run_comm_above hb h
      rwa [idx_reindex, reindex_reindex,
        show b.idx + a.arity - a.coarity + a.coarity - a.arity = b.idx by omega, reindex_self] at this

end Closedness

/-! ## 5. The moves on closed words and the syntactic `s`-laws -/

/-- The `B`-preserving steps of ng:finite-word item 1: commutations, type III, and types I/II in the
deletion direction. -/
def Pres (W W' : OWord) : Prop :=
  IsComm W.letters W'.letters ∨ IsTypeI W.letters W'.letters ∨ IsTypeII W.letters W'.letters ∨
    IsTypeIII W.letters W'.letters

/-- The deletions of item 3: zigzag, crossed-cusp shortcut, separated standard circle. -/
def Del (W W' : OWord) : Prop :=
  IsZigzagDeletion W.letters W'.letters ∨ IsCrossedCuspShortcut W.letters W'.letters ∨
    IsCircleDeletion W.letters W'.letters

/-- The cusp-skein interchange of item 2, with its compatible smoothing. -/
def Skein (A A' C : OWord) : Prop := IsCuspSkein A.letters A'.letters C.letters

/-- Lifting a word rewrite to closed words. -/
def OWord.ofRewrite (W : OWord) (V : Word) (h : W.letters.Closed → V.Closed) : OWord := ⟨V, h W.closed⟩

section SCount

open Word

theorem IsCommStep.sCount {W W' : Word} (h : IsCommStep W W') : W'.sCount = W.sCount := by
  obtain ⟨X, Y, a, b, rfl, hpat⟩ := h
  rcases hpat with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> simp [sCount_eq_length]

theorem IsComm.sCount {W W' : Word} (h : IsComm W W') : W'.sCount = W.sCount := by
  rcases h with h | h
  · exact h.sCount
  · exact h.sCount.symm

/-- type I deletes one crossing and two cusps: `Δs = −3` -/
theorem IsTypeI.sCount {W W' : Word} (h : IsTypeI W W') : W'.sCount + 3 = W.sCount := by
  obtain ⟨X, Y, m, d, hpat, rfl⟩ := h
  rcases hpat with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> simp [sCount_eq_length] <;> omega

/-- type II removes two crossings: `Δs = −2` -/
theorem IsTypeII.sCount {W W' : Word} (h : IsTypeII W W') : W'.sCount + 2 = W.sCount := by
  obtain ⟨X, Y, m, hpat⟩ := h
  rcases hpat with ⟨d, -, rfl, rfl⟩ | ⟨d, -, rfl, rfl⟩ | ⟨-, rfl, rfl⟩ | ⟨-, rfl, rfl⟩ <;>
    simp [sCount_eq_length] <;> omega

theorem IsTypeIII.sCount {W W' : Word} (h : IsTypeIII W W') : W'.sCount = W.sCount := by
  obtain ⟨X, Y, m, -, hpat⟩ := h
  rcases hpat with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [sCount_eq_length]

/-- "Deleting an empty zigzag lowers s by two" -/
theorem IsZigzagDeletion.sCount {W W' : Word} (h : IsZigzagDeletion W W') : W'.sCount + 2 = W.sCount := by
  obtain ⟨X, Y, m, d, -, hpat, rfl⟩ := h
  rcases hpat with rfl | rfl <;> simp [sCount_eq_length] <;> omega

/-- "applying the crossed-cusp shortcut lowers s by one" -/
theorem IsCrossedCuspShortcut.sCount {W W' : Word} (h : IsCrossedCuspShortcut W W') : W'.sCount + 1 = W.sCount := by
  obtain ⟨X, Y, i, -, hpat⟩ := h
  rcases hpat with ⟨d, rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [sCount_eq_length] <;> omega

/-- deleting a standard circle removes its two cusps -/
theorem IsCircleDeletion.sCount {W W' : Word} (h : IsCircleDeletion W W') : W'.sCount + 2 = W.sCount := by
  obtain ⟨X, Y, m, d, -, rfl, rfl, -⟩ := h
  simp [sCount_eq_length]; omega

/-- "The smoothing has one fewer singularity; the principal branches have the same singularity count." -/
theorem IsCuspSkeinStep.sCount {A A' C : Word} (h : IsCuspSkeinStep A A' C) :
    A'.sCount = A.sCount ∧ C.sCount + 1 = A.sCount := by
  obtain ⟨X, Y, m, d, a, P, L, -, -, -, rfl, rfl, hC⟩ := h
  rcases hC with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> simp [sCount_eq_length] <;> omega

theorem IsCuspSkein.sCount {A A' C : Word} (h : IsCuspSkein A A' C) :
    A'.sCount = A.sCount ∧ C.sCount + 1 = A.sCount := by
  rcases h with h | h
  · exact h.sCount
  · obtain ⟨h1, h2⟩ := h.sCount
    exact ⟨h1.symm, by omega⟩

theorem Pres.closed {W W' : OWord} (h : Pres W W') : W'.letters.Closed := by
  rcases h with h | h | h | h
  · exact h.closed W.closed
  · exact h.closed W.closed
  · exact h.closed W.closed
  · exact h.closed W.closed

theorem Del.closed {W W' : OWord} (h : Del W W') : W'.letters.Closed := by
  rcases h with h | h | h
  · exact h.closed W.closed
  · exact h.closed W.closed
  · exact h.closed W.closed

/-- the `pres_s` clause on the syntactic count: `s` does not increase -/
theorem Pres.sCountSyn_le {W W' : OWord} (h : Pres W W') : W'.sCountSyn ≤ W.sCountSyn := by
  unfold OWord.sCountSyn
  rcases h with h | h | h | h
  · rw [h.sCount]
  · have := h.sCount; omega
  · have := h.sCount; omega
  · rw [h.sCount]

/-- the `del_s` clause on the syntactic count: `s` strictly decreases -/
theorem Del.sCountSyn_lt {W W' : OWord} (h : Del W W') : W'.sCountSyn < W.sCountSyn := by
  unfold OWord.sCountSyn
  rcases h with h | h | h
  · have := h.sCount; omega
  · have := h.sCount; omega
  · have := h.sCount; omega

/-- the `skein_s` clause on the syntactic count -/
theorem Skein.sCountSyn {A A' C : OWord} (h : Skein A A' C) :
    A'.sCountSyn = A.sCountSyn ∧ C.sCountSyn < A.sCountSyn := by
  obtain ⟨h1, h2⟩ := IsCuspSkein.sCount h
  unfold OWord.sCountSyn
  exact ⟨h1, by omega⟩

end SCount

/-! ## 6. The descent engine (FINAL §4, §8: `Moves` = definitions only, so that `SM.ng_finite_word` can be
stated before any row is proved; `Laws` = the seven B/s clauses of rows 76a-82) -/

/-- The moves of the finite reduction on a type `α` of fronts: `s`, `B`, the `B`-preserving steps `Pres`
(commutations, type III, and types I/II in the deletion direction), the deletions `Del` (zigzag, crossed
cusp, standard circle), the cusp-skein interchange `Skein F F' C` and the standard-circle `Base`. -/
structure Moves where
  α : Type
  s : α → ℕ
  B : α → ℤ
  Pres : α → α → Prop
  Del : α → α → Prop
  Skein : α → α → α → Prop
  Base : α → Prop

namespace Moves

variable (K : Moves)

/-- A principal chain from `F` (ng:finite-word): `Pres`/`Skein` steps, stopped at the first strict decrease
of `s` (a `Del` step) or at the standard-circle base.  "Before that decrease the selected procedure does not
increase s" is NOT a clause here: it is a consequence of `Laws.pres_s` and `Laws.skein_s` (FR-6). -/
inductive Chain : K.α → Prop
  | base {F} : K.Base F → Chain F
  | del {F F'} : K.Del F F' → Chain F
  | pres {F F'} : K.Pres F F' → Chain F' → Chain F
  | skein {F F' C} : K.Skein F F' C → Chain F' → Chain F

/-- The seven B/s clauses of rows 76a-82 (theorems about the moves, NOT part of the axiom). -/
structure Laws : Prop where
  pres_B : ∀ F F', K.Pres F F' → K.B F = K.B F'
  pres_s : ∀ F F', K.Pres F F' → K.s F' ≤ K.s F
  del_B : ∀ F F', K.Del F F' → K.B F' ≤ K.B F
  del_s : ∀ F F', K.Del F F' → K.s F' < K.s F
  skein_B : ∀ F F' C, K.Skein F F' C → min (K.B F') (K.B C) ≤ K.B F
  skein_s : ∀ F F' C, K.Skein F F' C → K.s F' = K.s F ∧ K.s C < K.s F
  base_B : ∀ F, K.Base F → 0 ≤ K.B F

theorem nonneg_of_chain (L : K.Laws) (n : ℕ) (ih : ∀ G, K.s G < n → 0 ≤ K.B G) :
    ∀ F, K.s F ≤ n → K.Chain F → 0 ≤ K.B F := by
  intro F hF hc
  induction hc with
  | base h => exact L.base_B _ h
  | del h => exact le_trans (ih _ (lt_of_lt_of_le (L.del_s _ _ h) hF)) (L.del_B _ _ h)
  | pres h _ ihc => rw [L.pres_B _ _ h]; exact ihc (le_trans (L.pres_s _ _ h) hF)
  | skein h _ ihc =>
    obtain ⟨hs, hC⟩ := L.skein_s _ _ _ h
    have h1 := ihc (hs ▸ hF)
    have h2 := ih _ (lt_of_lt_of_le hC hF)
    exact le_trans (le_min h1 h2) (L.skein_B _ _ _ h)

/-- The degree induction of ng:local-front-bound (sm-3:2316-2348): `B ≥ 0` everywhere, by strong induction
on `s` along principal chains. -/
theorem defect_nonneg (L : K.Laws) (hfw : ∀ F, K.Chain F) : ∀ F, 0 ≤ K.B F := by
  suffices h : ∀ n, ∀ F, K.s F ≤ n → 0 ≤ K.B F from fun F => h _ F le_rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro F hF
    exact K.nonneg_of_chain L n (fun G hG => ih _ hG G le_rfl) F hF (hfw F)

/-- Along a principal chain `s` never increases before the stop (the printed "Before that decrease the
selected procedure does not increase s", derived from the laws). -/
theorem step_s_le (L : K.Laws) {F F' : K.α} (hF' : K.Pres F F' ∨ ∃ C, K.Skein F F' C) :
    K.s F' ≤ K.s F := by
  rcases hF' with h | ⟨C, h⟩
  · exact L.pres_s _ _ h
  · exact (L.skein_s _ _ _ h).1.le

end Moves

/-- The word moves of ng:finite-word on closed oriented words, with the geometric readings `s`, `B` and
`Base` supplied by the realization (FINAL §2 G1: `s W := (realize W).sCount`, `B W := (realize W).defect`,
`Base W := (realize W).IsStandardCircles`; unit β2). -/
def wordMovesOf (s : OWord → ℕ) (B : OWord → ℤ) (Base : OWord → Prop) : Moves where
  α := OWord
  s := s
  B := B
  Pres := Pres
  Del := Del
  Skein := Skein
  Base := Base

@[simp] theorem wordMovesOf_α (s : OWord → ℕ) (B : OWord → ℤ) (Base : OWord → Prop) :
    (wordMovesOf s B Base).α = OWord := rfl

@[simp] theorem wordMovesOf_Pres (s : OWord → ℕ) (B : OWord → ℤ) (Base : OWord → Prop) :
    (wordMovesOf s B Base).Pres = Pres := rfl

@[simp] theorem wordMovesOf_Del (s : OWord → ℕ) (B : OWord → ℤ) (Base : OWord → Prop) :
    (wordMovesOf s B Base).Del = Del := rfl

@[simp] theorem wordMovesOf_Skein (s : OWord → ℕ) (B : OWord → ℤ) (Base : OWord → Prop) :
    (wordMovesOf s B Base).Skein = Skein := rfl

/-- The `s`-clauses of the laws (`pres_s`, `del_s`, `skein_s` of `wordMovesOf s B Base`) hold for any `s`
that agrees with the syntactic count (the correspondence β2 proves for `(realize W).sCount`). -/
theorem laws_s_of_syn (s : OWord → ℕ) (hs : ∀ W, s W = W.sCountSyn) :
    (∀ F F' : OWord, Pres F F' → s F' ≤ s F) ∧ (∀ F F' : OWord, Del F F' → s F' < s F) ∧
    (∀ F F' C : OWord, Skein F F' C → s F' = s F ∧ s C < s F) := by
  refine ⟨fun F F' h => ?_, fun F F' h => ?_, fun F F' C h => ?_⟩
  · rw [hs, hs]; exact Pres.sCountSyn_le h
  · rw [hs, hs]; exact Del.sCountSyn_lt h
  · rw [hs, hs, hs]; exact Skein.sCountSyn h

/-- The shape of the literature input ng:finite-word (policy name `SM.ng_finite_word`, declared in the
statement unit, never here): every closed oriented word has a finite principal chain. -/
def FiniteWordStatement (K : Moves) : Prop := ∀ W : K.α, K.Chain W

/-- ng:local-front-bound on words follows from the laws and the finite-word statement. -/
theorem word_bound_of {K : Moves} (hL : K.Laws) (hfw : FiniteWordStatement K) : ∀ W, 0 ≤ K.B W :=
  K.defect_nonneg hL hfw

end SM.FrontWord
