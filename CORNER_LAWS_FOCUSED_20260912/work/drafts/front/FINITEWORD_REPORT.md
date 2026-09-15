# Statement unit — `SM.ng_finite_word` (ng:finite-word, AXIOM) — report

Written 2026-09-14 04:20 UTC / 12:20am ET by the front-lane statement subagent. Deliverable:
`work/drafts/front/FrontInterfaces_statement.lean` (intended home `work/lean/SM/FrontInterfaces.lean`),
508 lines, ONE `axiom` declaration (`SM.ng_finite_word : SM.NgFiniteWordClauses`), no `sorry`/`admit`/
`native_decide` (`grep -n 'sorry\|admit\|native_decide'` hits only two prose lines of the header: "admitted
literature inputs" and "no `sorry`").
Check: `cd work/lean && lake env lean ../drafts/front/FrontInterfaces_statement.lean` → no errors, no warnings
(Lean v4.34.0-rc2, project Mathlib pin, ~5 s). Imports: `SM.FrontWords` only (built). Nothing written under
`work/lean`. `#print axioms` (run on a copy in /tmp with the print lines appended):

| declaration | axioms |
|---|---|
| `SM.ng_finite_word` | `propext`, `SM.ng_finite_word` |
| `SM.ng_finite_word_chain` | `propext`, `SM.ng_finite_word` |
| `SM.ng_finite_word_finiteWordStatement` | `propext`, `Quot.sound`, `SM.ng_finite_word` |
| `SM.ng_finite_word_bound` | standard three + `SM.ng_finite_word` |
| `SM.ng_finite_word_nonbase_descends` | standard three + `SM.ng_finite_word` |
| `SM.FrontWord.principalChain_iff_chain`, `Descends.of_principalChain`, `PrincipalChain.congr`, `Word.IsStandardCircleBase.crossingCount_eq_zero` | standard only |

The axiom must be independently reviewed against blueprint/AXIOM_REGISTRY.md:78-120 before any consumer
cites it (FINAL §8 risk 4, §9 FR-6). This report gives the clause → field map, every reading, and the
mismatches with `SM/FrontWords.lean`.

## 1. The structure and the axiom (pasted)

```lean
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

axiom ng_finite_word : NgFiniteWordClauses
```

with (namespace `SM.FrontWord`)

```lean
def Move (W W' : OWord) : Prop := Pres W W' ∨ Del W W' ∨ ∃ C : OWord, Skein W W' C

inductive PrincipalChain (s : OWord → ℕ) (Base : OWord → Prop) : OWord → Prop
  | base {W : OWord} : Base W → PrincipalChain s Base W
  | stop {W W' : OWord} : Move W W' → s W' < s W → PrincipalChain s Base W
  | step {W W' : OWord} : Move W W' → ¬ s W' < s W → PrincipalChain s Base W' → PrincipalChain s Base W

def Word.IsStandardCircleBase (W : Word) : Prop := labelRun W 0 [] = some []   -- decidable
def OWord.IsStandardCircleBase (W : OWord) : Prop := W.letters.IsStandardCircleBase
```

`Pres`, `Del`, `Skein`, `OWord`, `OWord.sCountSyn`, `wordMovesOf`, `Moves.Chain`, `FiniteWordStatement`,
`word_bound_of` are the library's (`SM/FrontWords.lean`). No `∃` in the axiom: the block supplies no map, and
the existence of a chain is the Prop `PrincipalChain … W` itself (reading R7) — the ∃-form of
`SM/LinkInterfaces.lean` degenerates to the Prop structure.

## 2. Clause → field map (registry lines; tex lines in parentheses)

| AXIOM_REGISTRY.md | printed sentence | disposition in the file |
|---|---|---|
| 84-88 (2171-2175) | "For an actual finite front word on the domain of Definition ng:front-domain, the procedure of Ng ... and the elementary-word proof of Rutherford ... supplies a finite principal chain using:" | **FIELD** `finite_principal_chain : ∀ W : OWord, PrincipalChain OWord.sCountSyn OWord.IsStandardCircleBase W`. "actual finite front word" = closed oriented word `OWord` (FR-6); "finite principal chain" = a derivation of the inductive `PrincipalChain` (finite by construction; principal = follows `W → W'` at a skein step, the smoothing `C` is the side branch); the sources' procedures are not formalized (the chain is existential over move sequences). |
| 90-91 (2177-2178) | item 1 "typed disjoint-gadget commutations and the three local front moves in Lemmas ng:front-I, ng:front-II and ng:front-III;" | disjunct `Pres W W'` of `Move` = `IsComm ∨ IsTypeI ∨ IsTypeII ∨ IsTypeIII` (types I, II in the deletion direction only, sm-3:2278-2279; type II with its right-cusp versions, sm-3:1986-1987). |
| 92-93 (2179-2180) | item 2 "the cusp-skein crossing interchange (ng:cusp-words), or its reflected pattern;" | disjunct `∃ C, Skein W W' C` of `Move` = `IsCuspSkein` in either principal direction with its unique compatible smoothing (R4, R5). |
| 94-96 (2181-2183) | item 3 "zigzag deletion, the crossed-cusp shortcut of Lemma ng:deletions, or deletion of a separated standard front circle." | disjunct `Del W W'` of `Move` = `IsZigzagDeletion ∨ IsCrossedCuspShortcut ∨ IsCircleDeletion` (nonempty remainder). |
| 98 (2185) | "Stop at the first strict decrease of s or at the standard-circle base." | the constructors `stop` (a move with `s W' < s W` ends the chain), `base` (`IsStandardCircleBase`), `step` (a move that is not a strict decrease continues). `s` explicit (R1, R3). |
| 99 (2186) | "Before that decrease the selected procedure does not increase s." | NOT a field (FR-6, task brief): **theorem** `PrincipalChain.step_sCountSyn_eq` — a continuing step keeps `s` (`Move.sCountSyn_le` from the library's `Pres.sCountSyn_le`, `Del.sCountSyn_lt`, `Skein.sCountSyn`). |
| 100-103 (2187-2190) | "Secondary progress is measured at the boundaries of complete finite blocks of the word procedure: a completed nonterminal block moves a singularity to the left of the selected rightmost left cusp, and hence decreases the number on its right." | NOT a field: the source's termination argument; its formal content is that the chain is a finite derivation. No blocks, no secondary measure, **no chain-length bound** (FR-6). |
| 103-104 (2190-2191) | "This is not a strict decrease at every individual elementary move." | NOT a field: same; consistent with `step` (equal-`s` moves continue). |
| 104-105 (2191-2192) | "Arm-string extension within a block is bounded by the active strand count." | NOT a field: termination argument; arm strings are the source's case analysis, absent from the statement. |
| 105-106 (2192-2193) | "Thus every nonbase front has a finite principal chain to a front of smaller s." | NOT a field: the block's conclusion ("Thus"). **theorem** `Descends.of_principalChain` (and the projection `ng_finite_word_nonbase_descends`) derives `∀ W, ¬ Base W → Descends sCountSyn W` from the field, CONDITIONAL on `hinv : ∀ W W', IsComm W.letters W'.letters → (Base W ↔ Base W')` — the commutation-invariance of the base predicate, left to the base/realization unit (§5). |
| 106-108 (2193-2195) | "At each cusp-skein interchange, the compatible smoothing branch has smaller s than the front at that stage." | NOT a field: **theorem** `Skein.smoothing_sCountSyn_lt` (library `Skein.sCountSyn`); with the geometric `s` it is `Laws.skein_s` (row 82). |
| 110-117 (2197-2204) | scope paragraph ("This is the constructive word procedure, not a quantification over arbitrary Legendrian isotopies. The imported content is the source's finite descent, not its printed sentence: ...") | no formal content; honoured: the axiom is the finite chain on closed words, says nothing about Legendrian isotopy or any knot invariant, the terminal branches are the `Del` moves, arm strings do not appear. |
| 118 | status line | none. |

No field without a printed clause: the structure has exactly one field, quoting :84-98.

## 3. Readings (all also in the module header)

* **R1 (`s`).** ng:front-domain sm-3:1835-1836 "s(F) for the number of crossings plus cusps"; on a word every
  letter is one crossing or one cusp (sm-3:1906-1908), so `s = OWord.sCountSyn` (= crossings + cusps letters =
  length). The geometric `(realize W).sCount` is not in the library (β2); `PrincipalChain.congr` transports the
  chain once β2 proves `(realize W).sCount = W.sCountSyn`.
* **R2 (the base).** "the standard-circle base" = ng:circle's "A single standard front circle, and any union of
  such circles" (sm-3:2048-2049), "A simple crossing-free component with exactly one left and one right cusp"
  (2053-2054), "Nesting is allowed" (2056-2057); the consumer proof's "Any union of standard front circles
  encountered as a terminal base" (2319-2320); FR-6 "unions allowed, nesting allowed". FINAL §4 reads it as
  `(realize W).IsStandardCircles`; `realize` does not exist yet, so the base is defined on words:
  `Word.IsStandardCircleBase W := labelRun W 0 [] = some []` — a run over cuts of LABELS (the left cusp at letter
  index `k` pushes two arms labelled `k`; a right cusp is typed only on two strands of the same label; a crossing
  is never typed). Sanity by `decide`: `l₁r₁` (both orientations), nested `l₁l₂r₂r₁`, disjoint `l₁r₁l₁r₁`,
  interleaved `l₁l₃r₃r₁` and `l₁l₃r₁r₁` are bases; the crossing-free zigzag `l₁l₂r₁r₁` (β1 §4) and `l₁σ₁r₁`
  are not; `IsStandardCircleBase.crossingCount_eq_zero` proved. The empty word is a base (harmless: it is not a
  front of the domain, a chain from it is `base`; recorded).
  **Obligation for β2:** `(realize W).IsStandardCircles ↔ W.IsStandardCircleBase` (geometrically: without
  crossings each component is `l`-arm-`r`-arm-`l`, so "exactly one left and one right cusp per component" ⟺
  "every right cusp joins the two arms of one left cusp").
* **R3 (the stop rule).** Encoded with `s` explicit so the printed rule decides which moves stop the chain (see
  mismatch M1). Agreement with the library's shape: `principalChain_iff_chain : (∀ W, PrincipalChain sCountSyn
  Base W) ↔ FiniteWordStatement (wordMovesOf s B Base)` for every `s`, `B`, `Base` (→ by strong induction on
  `sCountSyn`, ← pointwise by truncation).
* **R4 ("or its reflected pattern").** The reflection `z ↦ −z` of eq. ng:cusp-words' `A = l₂σ₁` (positions
  reversed, over/under redetermined by the slopes) is `A' = l₁σ₂`; so the reflected pattern is the other principal
  direction, `IsCuspSkein` (either direction), as ng:cusp-skein states ("For either principal direction",
  sm-3:2077). **Right-cusp templates excluded** (β1's open item, decided by the text): item 2 cites eq.
  ng:cusp-words and its reflection only; the procedure's cusp interchanges are all at the rightmost LEFT cusp
  (case rows "Middle crossing, both strings nonempty" sm-3:2247-2249 and "Middle right cusp, both strings
  nonempty" 2268-2270 act on `l_m` with its first string letter); ng:cusp-skein's proof mentions right-cusp
  templates only as following "by relabeling their actual attachments and arrows in this local calculation"
  (2162-2164), outside the cited display.
* **R5 (the (t,u) bits).** Re-derived for this file against sm-3:2100-2118 on `A = l₂σ₁`, `A' = l₁σ₂` over the cut
  `[a]` (through-strand bit `a`, cusp bit `d`): outputs `[d, a, !d]` in both (identical boundary attachments);
  `t = +1 ↔ a = true` ("orientation from L to 2"); `u = +1 ↔ d = false` ("from 1 to 3, a downward cusp": endpoint
  1 has bit `d`, entered leftward, and `l₂ false` is a down cusp); `sign(A) = −tu`, `sign(A') = tu`: rows (+,+),
  (+,−), (−,+), (−,−) give `−1,+1,+1,−1` and `+1,−1,−1,+1` (σ positive iff the two bits agree); compatible
  smoothing `C_top = l₁` iff `t = u` iff `a = !d`, else `C_bottom = l₂`, with the same output cut as `A`; local
  `D = 1,0,1,0`; "The new cusp direction is u in either case" = bit `d`. All as `IsCuspSkeinStep` has them (β1's
  `decide` checks). "Only the one compatible smoothing is used, never both unoriented smoothings" (2124-2125) —
  `C` is unique in `IsCuspSkeinStep`.
* **R6 (the two Rutherford index corrections, sm-3:2284-2290).** "Two impossible printed ranges m−N₁>i>m on
  Rutherford's pp. 11-12 are transcribed here as the interior range m−N₁<i<m, as the neighboring cases and
  actual strands require. The duplicated m+2 in the increasing string on p. 11 continues with m+3, with the
  corresponding two-strand shift on p. 12. The malformed literal strings are not imported as identities: the
  actual strand operations and Ng's Figure 1 specify the moves used here." These correct the source's CASE
  ANALYSIS (which move the procedure applies to which first letter of `Y`); the axiom encodes no case analysis
  (the chain is existential over move sequences), so they leave no clause. They are honoured in that the moves are
  "the actual strand operations" (the library relations) and the "correct two-strand index shift" of case row
  sm-3:2251 is `IsComm`'s reindexing by the gadget's strand-count change (`+2` past `l`, `−2` past `r`, `0` past
  `σ`). No literal string (arm string, `N₁`, `N₂`) is imported.
* **R7 (no `∃`).** See §1.
* **R8 (uniform test).** Every move, including item 3's deletions, is subject to the same printed test "the first
  strict decrease of s"; that a deletion is always a `stop` is the theorem `Del.principalChain`
  (`Del.sCountSyn_lt`), not a clause.
* **R9 (closedness).** The moves are the library's relations on `OWord`; every word of a chain is closed by the
  library's `.closed` lemmas.
* **R10 ("typed").** "typed disjoint-gadget commutations" = `IsComm` on closed words (the typing is `Word.run`;
  the footprint condition `b.idx + b.arity ≤ a.idx` / `a.idx + a.coarity ≤ b.idx` is β1's, reviewed there).

## 4. Mismatches with `SM/FrontWords.lean` (library untouched)

* **M1 — the stop rule vs `Moves.Chain`.** `Moves.Chain` (FINAL §4) stops only at `Del` (`del`) and lets every
  `Pres` step continue (`pres`), including the type-I and type-II deletion steps, which strictly decrease `s`
  (`IsTypeI.sCount`: −3, `IsTypeII.sCount`: −2). The printed rule "Stop at the first strict decrease of s" stops
  at them. `PrincipalChain` (local) encodes the printed rule with `s` explicit; `principalChain_iff_chain` proves
  the two agree as ∀-statements, so `ng_finite_word_finiteWordStatement` gives consumers exactly FINAL's
  `FiniteWordStatement (wordMovesOf s B Base)` and `ng_finite_word_bound` the word bound via `word_bound_of`.
  Small; resolved locally.
* **M2 — the base.** `wordMovesOf` takes `Base` as a parameter and FINAL fixes it as `(realize W).IsStandardCircles`;
  `realize` is not in the library. Resolved by the syntactic `IsStandardCircleBase` (R2) with the recorded β2
  obligation. `PrincipalChain.congr` transports the chain to any equivalent base.
* **M3 — `s`, `B` of `wordMovesOf`.** `Moves.Chain` does not depend on `s` or `B`; the consumer theorems quantify
  over them (no assumption on them is made or needed).
* **No mismatch found in the eight rewrite relations** against their printed patterns: `IsComm` (ng:commutation
  1929-1931), `IsTypeI` (`l_mσ_{m∓1}r_m` deleted, 1955-1956), `IsTypeII` (`l_{m∓1}σ_mσ_{m∓1} ↦ l_m` and the
  right-cusp versions, 1977-1978, 1986-1987), `IsTypeIII` (1995-1996, both directions), `IsZigzagDeletion`
  (`l_mr_{m+1}`, `l_{m+1}r_m`, 2015-2017), `IsCrossedCuspShortcut` (`l_iσ_i ↦ l_i` bit flipped, `σ_ir_i ↦ r_i`,
  2028-2033), `IsCircleDeletion` (`l_mr_m`, nonempty remainder, 2047-2048), `IsCuspSkein` (R4, R5). The side
  conditions `1 ≤ m` / `2 ≤ m` guard natural subtraction only.

## 5. Open items handed on

1. **β2 / base unit:** `(realize W).IsStandardCircles ↔ W.IsStandardCircleBase`; and the commutation-invariance
   `IsComm W.letters W'.letters → (W.IsStandardCircleBase ↔ W'.IsStandardCircleBase)` (the `hinv` of
   `Descends.of_principalChain`; geometrically immediate — a disjoint-gadget commutation is the same front,
   ng:commutation — syntactically a relabelling argument on `labelRun`). With it, the "Thus" sentence (:105-106)
   becomes an unconditional theorem and the axiom is exactly as strong as its one field.
2. **β2:** `(realize W).sCount = W.sCountSyn`, then `PrincipalChain.congr` gives the chain with the geometric `s`.
3. **Rows 76a-82:** prove `(wordMovesOf s B IsStandardCircleBase).Laws` for the geometric `s`, `B`; then
   `ng_finite_word_bound` is row 83 on words.
4. **Review items (FR-6):** the one-field reading of the block (§2); the syntactic base (R2); the explicit-`s` stop
   rule (M1); the exclusion of right-cusp skein templates (R4); the empty word as a base (R2).
5. `SM.src_contact` (the fifth literature input, planned for the same module by FINAL §11) is not part of this unit.
