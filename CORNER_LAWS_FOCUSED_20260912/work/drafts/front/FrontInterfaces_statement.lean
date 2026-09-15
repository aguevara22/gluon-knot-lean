import SM.FrontWords

/-! Front block, statement unit (2026-09-14): module `SM/FrontInterfaces.lean` (intended home); draft
work/drafts/front/FrontInterfaces_statement.lean; report work/drafts/front/FINITEWORD_REPORT.md.

**THIS FILE DECLARES AN AXIOM.**  `SM.ng_finite_word` is the literature input ng:finite-word of
blueprint/AXIOM_REGISTRY.md, with the policy name fixed by work/lean/axiom-policy.json ("literature":
"ng:finite-word": "SM.ng_finite_word").  It is the fourth of the five admitted literature inputs (the three
knot-theory interfaces are in `SM/LinkInterfaces.lean`; the fifth, `SM.src_contact`, is planned for this
module by work/reports/front-block-design-FINAL-20260913.md §11 and is NOT declared here).  Exactly one
`axiom` is declared in this file; everything else is a `def`, an inductive `Prop`, a `structure`, or a
proved `theorem`.  The declaration must be independently reviewed against the registry text BEFORE any
consumer cites it (FINAL §8 risk 4, §9 FR-6).

# ng:finite-word — Finite front-word reduction (AXIOM)

**Source of the statement.** blueprint/AXIOM_REGISTRY.md:78-120 = reference/SM/sm-3-statesum.tex:2170-2206
(`\begin{literature}[Finite front-word reduction]\label{ng:finite-word}`; the registry's own line numbers
are used for every quotation below, the tex lines in parentheses).  The block's aftermatter in the source
(NOT part of the literature block and NOT axiom clauses) fixes the readings of the moves: the arm-string
setting `X l_m Y` and the fourteen-row case table (sm-3:2208-2271), the nested-descent paragraph
(sm-3:2273-2282: "Only deletion directions of types I and II occur here; type III, commutations and
cusp-skein changes preserve s"), the two Rutherford index corrections (sm-3:2284-2290), and the scope
paragraph (sm-3:2293-2300).  The moves themselves are the library relations of `SM/FrontWords.lean`
(unit β1, built), which transcribe ng:commutation (sm-3:1921-1948), ng:front-I/II/III (1950-2006),
ng:deletions (2008-2044), ng:circle (2046-2074) and ng:cusp-skein with eq. ng:cusp-words (2076-2168);
`s` and the word domain are those of ng:front-domain (sm-3:1825-1841) and the certificate section
(sm-3:1906-1919).  Design of record: FINAL §2 G3 ("the literature axiom `SM.ng_finite_word` must be
statable before rows 76-82 are proved"), §4, §8 risk 4, §9 FR-5/FR-6, §11; unit β1's report
work/drafts/front/BETA1_REPORT.md §3.2-3.3, §5.

## The printed block, sentence by sentence, and what each sentence becomes here

* AXIOM_REGISTRY.md:84-88 (sm-3:2171-2175) "For an actual finite front word on the domain of Definition
  ng:front-domain, the procedure of Ng [pp. 6-8 and Figure 1] and the elementary-word proof of Rutherford
  [Lemma 3.2, pp. 8-12 of the arXiv version] supplies a finite principal chain using:" — THE FIELD
  `NgFiniteWordClauses.finite_principal_chain : ∀ W : OWord, PrincipalChain OWord.sCountSyn
  OWord.IsStandardCircleBase W`.  "an actual finite front word" is a closed oriented Rutherford word
  (`SM.FrontWord.OWord`: typed from no strands to no strands, FR-6 "closed oriented words only");
  "finite principal chain" is a derivation of the inductive `PrincipalChain` (finite by construction);
  the procedures of Ng and Rutherford are the SOURCES of the chain, not formalized: the chain is
  existential over move sequences.
* :90-91 (2177-2178) item 1 "typed disjoint-gadget commutations and the three local front moves in
  Lemmas ng:front-I, ng:front-II and ng:front-III;" — the disjunct `Pres` of `Move` (`IsComm ∨ IsTypeI ∨
  IsTypeII ∨ IsTypeIII` on `OWord`; types I and II in the deletion direction only, sm-3:2278-2279).
* :92-93 (2179-2180) item 2 "the cusp-skein crossing interchange (ng:cusp-words), or its reflected
  pattern;" — the disjunct `∃ C, Skein W W' C` of `Move` (`IsCuspSkein`, either principal direction,
  with its unique compatible smoothing `C`).
* :94-96 (2181-2183) item 3 "zigzag deletion, the crossed-cusp shortcut of Lemma ng:deletions, or
  deletion of a separated standard front circle." — the disjunct `Del` of `Move` (`IsZigzagDeletion ∨
  IsCrossedCuspShortcut ∨ IsCircleDeletion`).
* :98 (2185) "Stop at the first strict decrease of s or at the standard-circle base." — the three
  constructors of `PrincipalChain`: `stop` (a move with `s W' < s W` ends the chain), `base` (the word is
  a union of standard front circles, `IsStandardCircleBase`), `step` (a move that is not a strict
  decrease continues the chain).  `s` is explicit in the inductive, so WHICH moves stop the chain is
  decided by `s` exactly as printed (a type-I or type-II deletion step strictly decreases `s` and
  therefore ends the chain; see the report, mismatch M1, for the library's `Moves.Chain`).
* :99 (2186) "Before that decrease the selected procedure does not increase s." — NOT a field (FR-6:
  a consequence of the move laws, not an axiom clause): theorem `PrincipalChain.step_sCountSyn_eq`
  (every continuing step keeps `s`, from the library's `Pres.sCountSyn_le`, `Del.sCountSyn_lt`,
  `Skein.sCountSyn`).
* :100-103 (2187-2190) "Secondary progress is measured at the boundaries of complete finite blocks of
  the word procedure: a completed nonterminal block moves a singularity to the left of the selected
  rightmost left cusp, and hence decreases the number on its right." — NOT a field: the source's
  termination argument, whose formal content is the finiteness of the chain (a derivation of an
  inductive Prop).  No block structure, no secondary measure and NO chain-length bound is added (FR-6).
* :103-104 (2190-2191) "This is not a strict decrease at every individual elementary move." — NOT a
  field: same; consistent with `step` (moves with equal `s` continue the chain).
* :104-105 (2191-2192) "Arm-string extension within a block is bounded by the active strand count." —
  NOT a field: termination argument of the source; the arm strings are the source's case analysis and
  appear nowhere in the statement.
* :105-106 (2192-2193) "Thus every nonbase front has a finite principal chain to a front of smaller s."
  — NOT a field: the block's conclusion ("Thus") restating the chain clause for nonbase words.  Theorem
  `Descends.of_principalChain` derives it from the field, conditional on ONE named lemma left to the
  base/realization unit: the commutation-invariance of `IsStandardCircleBase` (a disjoint-gadget
  commutation is the same front, ng:commutation) — see the report.
* :106-108 (2193-2195) "At each cusp-skein interchange, the compatible smoothing branch has smaller s
  than the front at that stage." — NOT a field: theorem `Skein.smoothing_sCountSyn_lt` (the library's
  `Skein.sCountSyn`); with the geometric `s` it is the law `skein_s` of rows 76a-82.
* :110-117 (2197-2204) the scope paragraph "This is the constructive word procedure, not a
  quantification over arbitrary Legendrian isotopies. The imported content is the source's finite
  descent, not its printed sentence: Ng's Lemma 1 gives one step, iterated here until s decreases;
  Rutherford's two ruling-polynomial terminal branches are replaced here by the geometric shortcuts of
  Lemma ng:deletions; and the finiteness of arm-string extension, which Rutherford asserts, is given its
  reason here" — no formal content; honoured: the axiom is the finite chain on closed words, not a
  statement about Legendrian isotopies or about any knot invariant; the terminal branches are the `Del`
  moves; nothing about arm strings is stated.
* :118 the status line — none.

## Reading choices (recorded for the reviewer; details and the clause → field map in the report)

* R1 (`s` on words).  ng:front-domain: "s(F) for the number of crossings plus cusps" (sm-3:1835-1836).
  On a word every letter is one crossing or one cusp (sm-3:1906-1908), so `s` is the syntactic count
  `OWord.sCountSyn` (= `Word.sCount` = crossings + cusps = the length).  The geometric `s` of the grid
  realization (unit β2, `(realize W).sCount`) is not in the library; β2's correspondence
  `(realize W).sCount = W.sCountSyn` transports the chain by `PrincipalChain.congr`.
* R2 (the base).  "the standard-circle base" (:98) is ng:circle's "A single standard front circle, and
  any union of such circles" (sm-3:2048-2049; "A simple crossing-free component with exactly one left and
  one right cusp", 2053-2054), the "union of standard front circles encountered as a terminal base" of
  the consumer's proof (sm-3:2319-2320); FR-6: "unions allowed, nesting allowed".  FINAL §4 reads it
  geometrically as `(realize W).IsStandardCircles`; `realize` is not in the library, so the base is
  defined here ON WORDS: `IsStandardCircleBase W` := the word has no crossing letter and every right cusp
  joins the two arms of one left cusp (a labelled run, `Word.labelRun`, decidable).  Recorded obligation
  for β2: `(realize W).IsStandardCircles ↔ W.IsStandardCircleBase`.  Sanity checks by `decide` below.
* R3 (the stop rule).  Encoded with `s` explicit (`stop`/`step`), so the printed rule decides which
  moves end the chain.  The library's `Moves.Chain` (FINAL §4) stops only at `Del` and lets type-I/II
  deletion steps continue: the two shapes agree as ∀-statements (`principalChain_iff_chain`, by strong
  induction on `sCountSyn`), so consumers receive `FiniteWordStatement (wordMovesOf s B
  IsStandardCircleBase)` for every `s`, `B` (`ng_finite_word_finiteWordStatement`) and the bound
  `ng_finite_word_bound` from `word_bound_of` once the laws are proved.  Not a change to the library.
* R4 ("or its reflected pattern").  The reflection `z ↦ −z` of eq. ng:cusp-words' `A = l₂σ₁` is `A' =
  l₁σ₂`: the reflected pattern is the other principal direction, `IsCuspSkein` (either direction), as
  ng:cusp-skein states it ("For either principal direction").  Right-cusp interchange templates
  (`σ₁r₂ ↔ σ₂r₁`) are NOT included: item 2 cites eq. ng:cusp-words and its reflection only, the
  procedure's interchanges are always at the rightmost LEFT cusp (case rows sm-3:2247-2249, 2268-2270),
  and ng:cusp-skein's proof mentions right-cusp templates only as following "by relabeling" (2162-2164),
  outside the cited display.
* R5 (the (t,u) bits).  `IsCuspSkeinStep` was re-derived against the printed table sm-3:2100-2118 for
  this file: with the through-strand bit `a` and the cusp bit `d`, `t = +1 ↔ a = true`, `u = +1 ↔
  d = false`; rows (+,+), (+,−), (−,+), (−,−) give `sign(A) = −1, +1, +1, −1`, `sign(A') = +1, −1, −1,
  +1`, compatible smoothing `C_top, C_bottom, C_bottom, C_top` (= `l_m` iff `a = !d`), local `D = 1, 0,
  1, 0`, and the new cusp direction `u` in either case (bit `d`); all match (β1's `decide` checks).
* R6 (the two Rutherford corrections, sm-3:2284-2290).  "Two impossible printed ranges m−N₁>i>m on
  Rutherford's pp. 11-12 are transcribed here as the interior range m−N₁<i<m ... The duplicated m+2 in
  the increasing string on p. 11 continues with m+3, with the corresponding two-strand shift on p. 12.
  The malformed literal strings are not imported as identities: the actual strand operations and Ng's
  Figure 1 specify the moves used here."  These fix the source's CASE ANALYSIS (which move applies to
  which first letter of `Y`), which the axiom does not encode (the chain is existential over move
  sequences); the moves are "the actual strand operations" = the library relations, and the "correct
  two-strand index shift" (case row sm-3:2251) is `IsComm`'s reindexing by `± 2` past a cusp.  No literal
  string is imported.
* R7 (no `∃`).  Unlike lit:homfly and lp:lm the block supplies no map; the existence of a chain IS the
  Prop `PrincipalChain … W`.  So the axiom is the Prop structure itself, `axiom ng_finite_word :
  NgFiniteWordClauses`, one field for the one printed claim.
* R8 (uniform test).  Every move, including the deletions of item 3, is subject to the same printed
  test "the first strict decrease of s" (`stop`/`step`); that a deletion is always a `stop` is a theorem
  about the moves (`Del.sCountSyn_lt`), not a clause.
* R9 (closedness).  The moves are the library's relations on `OWord`, whose closedness lemmas
  (`Pres.closed`, `Del.closed`, `IsCuspSkein.closed_A'`) make every word of a chain closed.

`s`, `B`, `Base` of `wordMovesOf` are parameters in the consumer theorems because `Moves.Chain` does not
depend on `s` or `B`; nothing is assumed about them.  Checked with `cd work/lean && lake env lean
../drafts/front/FrontInterfaces_statement.lean` (no `sorry`; `#print axioms ng_finite_word_bound` =
standard three + `SM.ng_finite_word`). -/

namespace SM.FrontWord

/-! ## 1. The standard-circle base on words (ng:circle, sm-3:2046-2049, 2053-2054; R2)

"A simple crossing-free component with exactly one left and one right cusp" and "any union of such
circles": a closed word is a union of standard front circles iff it has no crossing letter and every right
cusp joins the two arms created by one left cusp.  Tracked by a run over cuts of LABELS: the left cusp at
letter index `k` pushes two strands labelled `k`; a right cusp is typed only on two strands of the same
label; a crossing is never typed.  Nesting (`l₁ l₂ r₂ r₁`) and interleaving (`l₁ l₃ r₁ r₁`) are unions of
standard circles; the crossing-free zigzag `l₁ l₂ r₁ r₁` (β1 §4) is not. -/

namespace Letter

/-- The label action of a letter at letter index `k` on the labelled strands from its position downward:
a left cusp pushes two arms labelled `k`; a right cusp removes two strands of the SAME label (the two arms
of one left cusp), else it is untyped; a crossing is untyped. -/
def labelAct : Letter → ℕ → List ℕ → Option (List ℕ)
  | .l _ _, k, L => some (k :: k :: L)
  | .r _, _, a :: b :: L => if a = b then some L else none
  | .r _, _, _ => none
  | .σ _, _, _ => none

/-- The labelled typing step at the letter's 1-based position (the first `m − 1` strands untouched, as
`Letter.step`). -/
def labelStep (ℓ : Letter) (k : ℕ) (c : List ℕ) : Option (List ℕ) :=
  if 1 ≤ ℓ.idx ∧ ℓ.idx - 1 ≤ c.length then
    (ℓ.labelAct k (c.drop (ℓ.idx - 1))).map (c.take (ℓ.idx - 1) ++ ·)
  else none

@[simp] theorem labelAct_σ (m k : ℕ) (L : List ℕ) : (Letter.σ m).labelAct k L = none := rfl

@[simp] theorem labelStep_σ (m k : ℕ) (c : List ℕ) : (Letter.σ m).labelStep k c = none := by
  unfold labelStep
  split_ifs <;> simp

end Letter

namespace Word

/-- The labelled run of a word from letter index `k` and labelled cut `c`; `none` if some letter is not
typed (in particular whenever the word contains a crossing). -/
def labelRun : Word → ℕ → List ℕ → Option (List ℕ)
  | [], _, c => some c
  | a :: W, k, c => (a.labelStep k c).bind (labelRun W (k + 1))

@[simp] theorem labelRun_nil (k : ℕ) (c : List ℕ) : labelRun [] k c = some c := rfl

@[simp] theorem labelRun_cons (a : Letter) (W : Word) (k : ℕ) (c : List ℕ) :
    labelRun (a :: W) k c = (a.labelStep k c).bind (labelRun W (k + 1)) := rfl

/-- "the standard-circle base" on words: a union of standard front circles (ng:circle; unions and
nesting allowed).  The word typed from no labelled strands back to none. -/
def IsStandardCircleBase (W : Word) : Prop := labelRun W 0 [] = some []

instance (W : Word) : Decidable W.IsStandardCircleBase :=
  inferInstanceAs (Decidable (labelRun W 0 [] = some []))

/-- A word containing a crossing letter has no labelled run. -/
theorem labelRun_eq_none_of_σ_mem {W : Word} {m : ℕ} (h : Letter.σ m ∈ W) (k : ℕ) (c : List ℕ) :
    labelRun W k c = none := by
  induction W generalizing k c with
  | nil => simp at h
  | cons a W ih =>
    rw [List.mem_cons] at h
    rcases h with rfl | h
    · simp
    · rw [labelRun_cons]
      cases a.labelStep k c with
      | none => rfl
      | some c' => exact ih h (k + 1) c'

/-- A union of standard front circles contains no crossing letter. -/
theorem not_isStandardCircleBase_of_σ_mem {W : Word} {m : ℕ} (h : Letter.σ m ∈ W) :
    ¬ W.IsStandardCircleBase := by
  unfold IsStandardCircleBase
  rw [labelRun_eq_none_of_σ_mem h]
  simp

/-- "crossing-free": a union of standard front circles has crossing count zero. -/
theorem IsStandardCircleBase.crossingCount_eq_zero {W : Word} (h : W.IsStandardCircleBase) :
    W.crossingCount = 0 := by
  unfold crossingCount
  rw [List.countP_eq_zero]
  intro a ha hc
  cases a with
  | l m d => simp [Letter.isCrossing] at hc
  | r m => simp [Letter.isCrossing] at hc
  | σ m => exact not_isStandardCircleBase_of_σ_mem ha h

end Word

/-- The standard-circle base on closed oriented words. -/
def OWord.IsStandardCircleBase (W : OWord) : Prop := W.letters.IsStandardCircleBase

instance (W : OWord) : Decidable W.IsStandardCircleBase :=
  inferInstanceAs (Decidable W.letters.IsStandardCircleBase)

/-! ### Sanity checks of the base against the printed text (by `decide`) -/

/-- a single standard front circle, in either orientation (ng:circle "in either orientation") -/
example : Word.IsStandardCircleBase [.l 1 true, .r 1] := by decide
example : Word.IsStandardCircleBase [.l 1 false, .r 1] := by decide
/-- nested standard circles ("Nesting is allowed", sm-3:2056-2057) -/
example : Word.IsStandardCircleBase [.l 1 true, .l 2 false, .r 2, .r 1] := by decide
/-- disjoint standard circles, adjacent and interleaved letters -/
example : Word.IsStandardCircleBase [.l 1 true, .r 1, .l 1 false, .r 1] := by decide
example : Word.IsStandardCircleBase [.l 1 true, .l 3 true, .r 3, .r 1] := by decide
example : Word.IsStandardCircleBase [.l 1 true, .l 3 true, .r 1, .r 1] := by decide
/-- the crossing-free one-component zigzag word (β1 §4: closed, `s = 4`, `D = 3`) is NOT a base -/
example : ¬ Word.IsStandardCircleBase [.l 1 true, .l 2 false, .r 1, .r 1] := by decide
/-- a crossed cusp is not a base -/
example : ¬ Word.IsStandardCircleBase [.l 1 true, .σ 1, .r 1] := by decide
/-- the empty word is (vacuously) typed; it is not a closed front of the domain ("nonempty finite union of
parameter circles", sm-3:1826) but it is a closed word; recorded, harmless: a chain from it is `base` -/
example : Word.IsStandardCircleBase [] := by decide

/-! ## 2. The moves of items 1-3 and the principal chain with the printed stop rule (:84-98; R3, R8) -/

/-- One move of the finite reduction, items 1-3 of ng:finite-word (AXIOM_REGISTRY.md:90-96): item 1
"typed disjoint-gadget commutations and the three local front moves in Lemmas ng:front-I, ng:front-II and
ng:front-III" = `Pres` (types I, II in the deletion direction only, sm-3:2278-2279); item 2 "the
cusp-skein crossing interchange (ng:cusp-words), or its reflected pattern" = `Skein W W' C` for the unique
compatible smoothing `C` (either principal direction); item 3 "zigzag deletion, the crossed-cusp shortcut
of Lemma ng:deletions, or deletion of a separated standard front circle" = `Del`. -/
def Move (W W' : OWord) : Prop := Pres W W' ∨ Del W W' ∨ ∃ C : OWord, Skein W W' C

/-- "a finite principal chain using [items 1-3].  Stop at the first strict decrease of s or at the
standard-circle base." (AXIOM_REGISTRY.md:84-98): a finite sequence of moves from `W`, following the
principal branch at each cusp-skein interchange, that ends with the first move strictly decreasing `s`
(`stop`) or at a union of standard front circles (`base`); a move that is not a strict decrease continues
the chain (`step`).  `s` and `Base` are parameters so that β2's geometric readings transport by `congr`;
the axiom fixes `s := OWord.sCountSyn`, `Base := OWord.IsStandardCircleBase`. -/
inductive PrincipalChain (s : OWord → ℕ) (Base : OWord → Prop) : OWord → Prop
  /-- "or at the standard-circle base" -/
  | base {W : OWord} : Base W → PrincipalChain s Base W
  /-- "Stop at the first strict decrease of s": a move with `s W' < s W` ends the chain -/
  | stop {W W' : OWord} : Move W W' → s W' < s W → PrincipalChain s Base W
  /-- a move that is not a strict decrease of `s` continues the chain -/
  | step {W W' : OWord} : Move W W' → ¬ s W' < s W → PrincipalChain s Base W' → PrincipalChain s Base W

/-- "a finite principal chain to a front of smaller s" (AXIOM_REGISTRY.md:105-106): a principal chain
that ends at a strict decrease (never at the base). -/
inductive Descends (s : OWord → ℕ) : OWord → Prop
  | stop {W W' : OWord} : Move W W' → s W' < s W → Descends s W
  | step {W W' : OWord} : Move W W' → ¬ s W' < s W → Descends s W' → Descends s W

theorem Descends.principalChain {s : OWord → ℕ} {Base : OWord → Prop} {W : OWord} (h : Descends s W) :
    PrincipalChain s Base W := by
  induction h with
  | stop hm hlt => exact PrincipalChain.stop hm hlt
  | step hm hn _ ih => exact PrincipalChain.step hm hn ih

/-- Transport of a chain along pointwise equal `s` and equivalent `Base` (β2: the geometric readings). -/
theorem PrincipalChain.congr {s s' : OWord → ℕ} {Base Base' : OWord → Prop} (hs : ∀ W, s W = s' W)
    (hb : ∀ W, Base W ↔ Base' W) {W : OWord} (h : PrincipalChain s Base W) : PrincipalChain s' Base' W := by
  induction h with
  | base h => exact PrincipalChain.base ((hb _).1 h)
  | stop hm hlt => exact PrincipalChain.stop hm (by rw [← hs, ← hs]; exact hlt)
  | step hm hn _ ih => exact PrincipalChain.step hm (by rw [← hs, ← hs]; exact hn) ih

/-! ## 3. The `s`-sentences of the block as theorems about the moves (:99, :106-108; FR-6) -/

/-- No move increases the syntactic `s` (items 1-3; the library's `s`-lemmas). -/
theorem Move.sCountSyn_le {W W' : OWord} (h : Move W W') : W'.sCountSyn ≤ W.sCountSyn := by
  rcases h with hp | hd | ⟨C, hs⟩
  · exact Pres.sCountSyn_le hp
  · exact (Del.sCountSyn_lt hd).le
  · exact (Skein.sCountSyn hs).1.le

/-- "Before that decrease the selected procedure does not increase s" (AXIOM_REGISTRY.md:99), as the
theorem it is (FR-6): a continuing step of a principal chain keeps `s`. -/
theorem PrincipalChain.step_sCountSyn_eq {W W' : OWord} (h : Move W W') (hn : ¬ W'.sCountSyn < W.sCountSyn) :
    W'.sCountSyn = W.sCountSyn := by
  have := h.sCountSyn_le
  omega

/-- "At each cusp-skein interchange, the compatible smoothing branch has smaller s than the front at that
stage" (AXIOM_REGISTRY.md:106-108), as the theorem it is (the library's `Skein.sCountSyn`). -/
theorem Skein.smoothing_sCountSyn_lt {A A' C : OWord} (h : Skein A A' C) : C.sCountSyn < A.sCountSyn :=
  (Skein.sCountSyn h).2

/-- Every deletion of item 3 is a `stop` (the library's `Del.sCountSyn_lt`). -/
theorem Del.principalChain {Base : OWord → Prop} {W W' : OWord} (h : Del W W') :
    PrincipalChain OWord.sCountSyn Base W :=
  PrincipalChain.stop (Or.inr (Or.inl h)) (Del.sCountSyn_lt h)

/-! ## 4. Agreement with the library's descent skeleton `Moves.Chain` (FINAL §4; R3, mismatch M1)

`Moves.Chain` stops only at `Del` and lets every `Pres` step continue, including the type-I/II deletion
steps, which strictly decrease `s`; `PrincipalChain` stops at them as printed.  As ∀-statements the two
agree (for any `s`, `B` of `wordMovesOf`, on which `Chain` does not depend). -/

section Chain

variable (s : OWord → ℕ) (B : OWord → ℤ) (Base : OWord → Prop)

/-- A library chain is a principal chain (truncate at the first strict decrease). -/
theorem Moves.Chain.principalChain {W : (wordMovesOf s B Base).α} (h : (wordMovesOf s B Base).Chain W) :
    PrincipalChain OWord.sCountSyn Base W := by
  induction h with
  | base h => exact PrincipalChain.base h
  | del h => exact Del.principalChain h
  | pres h hc ih =>
    rename_i F F'
    by_cases hlt : OWord.sCountSyn F' < OWord.sCountSyn F
    · exact PrincipalChain.stop (Or.inl h) hlt
    · exact PrincipalChain.step (Or.inl h) hlt ih
  | skein h hc ih =>
    exact PrincipalChain.step (Or.inr (Or.inr ⟨_, h⟩)) (by have := (Skein.sCountSyn h).1; omega) ih

/-- If every closed word has a principal chain, every closed word has a library chain (strong induction
on `sCountSyn`: a `stop` at a type-I/II step continues with the chain of the smaller word). -/
theorem chain_of_principalChain (hall : ∀ W : OWord, PrincipalChain OWord.sCountSyn Base W) :
    ∀ W : OWord, (wordMovesOf s B Base).Chain W := by
  suffices h : ∀ n, ∀ W : OWord, W.sCountSyn ≤ n → (wordMovesOf s B Base).Chain W from
    fun W => h _ W le_rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro W hW
    have hc := hall W
    revert hW
    induction hc with
    | base h => exact fun _ => Moves.Chain.base h
    | stop hm hlt =>
      rename_i F F'
      intro hF
      rcases hm with hp | hd | ⟨C, hs⟩
      · exact Moves.Chain.pres hp (ih _ (by omega) F' le_rfl)
      · exact Moves.Chain.del hd
      · exact Moves.Chain.skein hs (ih _ (by omega) F' le_rfl)
    | step hm hn hc' ihc =>
      rename_i F F'
      intro hF
      have hle := hm.sCountSyn_le
      rcases hm with hp | hd | ⟨C, hs⟩
      · exact Moves.Chain.pres hp (ihc (by omega))
      · exact Moves.Chain.del hd
      · exact Moves.Chain.skein hs (ihc (by omega))

/-- The two shapes of ng:finite-word agree as ∀-statements: the printed stop rule (`PrincipalChain`) and
the library's `FiniteWordStatement` (FINAL §4 `∀ W, wordMoves.Chain W`). -/
theorem principalChain_iff_chain :
    (∀ W : OWord, PrincipalChain OWord.sCountSyn Base W) ↔ FiniteWordStatement (wordMovesOf s B Base) :=
  ⟨chain_of_principalChain s B Base, fun h W => Moves.Chain.principalChain s B Base (h W)⟩

end Chain

/-! ## 5. The block's conclusion (:105-106) as a theorem, conditional on one lemma of the base unit -/

/-- A type-III move leaves a crossing letter in the result. -/
theorem IsTypeIII.exists_σ_mem {W W' : Word} (h : IsTypeIII W W') : ∃ m, Letter.σ m ∈ W' := by
  obtain ⟨X, Y, m, -, hpat⟩ := h
  rcases hpat with ⟨-, rfl⟩ | ⟨-, rfl⟩
  · exact ⟨m, by simp⟩
  · exact ⟨m + 1, by simp⟩

/-- The other principal branch of a cusp-skein interchange contains a crossing letter. -/
theorem IsCuspSkein.exists_σ_mem {A A' C : Word} (h : IsCuspSkein A A' C) : ∃ m, Letter.σ m ∈ A' := by
  rcases h with ⟨X, Y, m, d, a, P, L, -, -, -, -, rfl, -⟩ | ⟨X, Y, m, d, a, P, L, -, -, -, rfl, -, -⟩
  · exact ⟨m + 1, by simp⟩
  · exact ⟨m, by simp⟩

/-- "Thus every nonbase front has a finite principal chain to a front of smaller s" (AXIOM_REGISTRY.md:
105-106), derived from the chain clause: along the continuing steps of a principal chain a nonbase word
stays nonbase — type III and the cusp-skein branch contain a crossing, types I/II and the deletions
strictly decrease `s` and so never continue, and a disjoint-gadget commutation preserves the base by the
hypothesis `hinv` (the same front, ng:commutation; a lemma of the base/realization unit, not proved
here). -/
theorem Descends.of_principalChain
    (hinv : ∀ W W' : OWord, IsComm W.letters W'.letters → (W.IsStandardCircleBase ↔ W'.IsStandardCircleBase))
    {W : OWord} (hc : PrincipalChain OWord.sCountSyn OWord.IsStandardCircleBase W)
    (hW : ¬ W.IsStandardCircleBase) : Descends OWord.sCountSyn W := by
  revert hW
  induction hc with
  | base h => exact fun hW => absurd h hW
  | stop hm hlt => exact fun _ => Descends.stop hm hlt
  | step hm hn hc' ih =>
    rename_i F F'
    intro hF
    refine Descends.step hm hn (ih ?_)
    rcases hm with hp | hd | ⟨C, hs⟩
    · rcases hp with hcomm | hI | hII | hIII
      · exact fun h' => hF ((hinv F F' hcomm).2 h')
      · exact absurd (by have := IsTypeI.sCount hI; unfold OWord.sCountSyn; omega) hn
      · exact absurd (by have := IsTypeII.sCount hII; unfold OWord.sCountSyn; omega) hn
      · obtain ⟨m, hm⟩ := hIII.exists_σ_mem
        exact Word.not_isStandardCircleBase_of_σ_mem hm
    · exact absurd (Del.sCountSyn_lt hd) hn
    · obtain ⟨m, hm⟩ := IsCuspSkein.exists_σ_mem hs
      exact Word.not_isStandardCircleBase_of_σ_mem hm

end SM.FrontWord

namespace SM

open SM.FrontWord

/-! ## 6. The literature input ng:finite-word (AXIOM_REGISTRY.md:78-120, sm-3:2170-2206) -/

/-- The printed clause of ng:finite-word with formal content, one field (the other sentences of the
block are consequences, the source's termination argument, or scope commentary — module header). -/
structure NgFiniteWordClauses : Prop where
  /-- "For an actual finite front word on the domain of Definition ng:front-domain, the procedure of Ng
  [pp. 6-8 and Figure 1] and the elementary-word proof of Rutherford [Lemma 3.2, pp. 8-12 of the arXiv
  version] supplies a finite principal chain using: (1) typed disjoint-gadget commutations and the three
  local front moves in Lemmas ng:front-I, ng:front-II and ng:front-III; (2) the cusp-skein crossing
  interchange (ng:cusp-words), or its reflected pattern; (3) zigzag deletion, the crossed-cusp shortcut of
  Lemma ng:deletions, or deletion of a separated standard front circle.  Stop at the first strict decrease
  of s or at the standard-circle base." (AXIOM_REGISTRY.md:84-98, sm-3:2171-2185).  On every closed
  oriented word (`OWord`), with the moves `Move` (items 1-3), `s = OWord.sCountSyn` (R1) and the base
  `OWord.IsStandardCircleBase` (R2). -/
  finite_principal_chain : ∀ W : OWord, PrincipalChain OWord.sCountSyn OWord.IsStandardCircleBase W

/-- **ng:finite-word** (AXIOM_REGISTRY.md:78-120, sm-3:2170-2206; policy name `SM.ng_finite_word`):
"Finite front-word reduction.  For an actual finite front word on the domain of Definition
ng:front-domain, the procedure of Ng and the elementary-word proof of Rutherford supplies a finite
principal chain using: typed disjoint-gadget commutations and the three local front moves in Lemmas
ng:front-I, ng:front-II and ng:front-III; the cusp-skein crossing interchange (ng:cusp-words), or its
reflected pattern; zigzag deletion, the crossed-cusp shortcut of Lemma ng:deletions, or deletion of a
separated standard front circle.  Stop at the first strict decrease of s or at the standard-circle base.
Before that decrease the selected procedure does not increase s.  Secondary progress is measured at the
boundaries of complete finite blocks of the word procedure: a completed nonterminal block moves a
singularity to the left of the selected rightmost left cusp, and hence decreases the number on its right.
This is not a strict decrease at every individual elementary move.  Arm-string extension within a block
is bounded by the active strand count.  Thus every nonbase front has a finite principal chain to a front
of smaller s.  At each cusp-skein interchange, the compatible smoothing branch has smaller s than the
front at that stage.  This is the constructive word procedure, not a quantification over arbitrary
Legendrian isotopies. ..."  The clause with formal content is the field of `NgFiniteWordClauses`; the
remaining sentences are theorems here (`PrincipalChain.step_sCountSyn_eq`, `Skein.smoothing_sCountSyn_lt`,
`Descends.of_principalChain`) or the source's termination argument and scope, which add no clause (no
chain-length bound, FR-6).  AXIOM: independent review required before any consumer cites it. -/
axiom ng_finite_word : NgFiniteWordClauses

/-! ## 7. Projections for consumers (the chain, and the library shapes of FINAL §4) -/

/-- ng:finite-word: every closed oriented word has a finite principal chain with the printed stop rule. -/
theorem ng_finite_word_chain (W : OWord) :
    PrincipalChain OWord.sCountSyn OWord.IsStandardCircleBase W :=
  ng_finite_word.finite_principal_chain W

/-- ng:finite-word in the library's shape (FINAL §4 `ng_finite_word_statement`): `FiniteWordStatement`
for the word moves with the standard-circle base, for every `s`, `B` (on which `Moves.Chain` does not
depend; β2 supplies the geometric ones). -/
theorem ng_finite_word_finiteWordStatement (s : OWord → ℕ) (B : OWord → ℤ) :
    FiniteWordStatement (wordMovesOf s B OWord.IsStandardCircleBase) :=
  (principalChain_iff_chain s B OWord.IsStandardCircleBase).1 ng_finite_word.finite_principal_chain

/-- ng:local-front-bound on words (row 83 on words, FINAL §4 `word_bound_of`): once the seven laws of
rows 76a-82 are proved for `s`, `B`, the defect is nonnegative on every closed oriented word.  Consumes
`SM.ng_finite_word`. -/
theorem ng_finite_word_bound (s : OWord → ℕ) (B : OWord → ℤ)
    (hL : (wordMovesOf s B OWord.IsStandardCircleBase).Laws) : ∀ W : OWord, 0 ≤ B W :=
  word_bound_of hL (ng_finite_word_finiteWordStatement s B)

/-- The block's conclusion for consumers: every nonbase closed word descends (conditional on the
commutation-invariance of the base, `Descends.of_principalChain`). -/
theorem ng_finite_word_nonbase_descends
    (hinv : ∀ W W' : OWord, IsComm W.letters W'.letters → (W.IsStandardCircleBase ↔ W'.IsStandardCircleBase))
    (W : OWord) (hW : ¬ W.IsStandardCircleBase) : Descends OWord.sCountSyn W :=
  Descends.of_principalChain hinv (ng_finite_word_chain W) hW

end SM
