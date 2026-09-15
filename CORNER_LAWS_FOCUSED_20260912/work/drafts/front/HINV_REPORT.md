# Base unit — `hinv` (commutation invariance of the standard-circle base) and the unconditional descent — report

Written 2026-09-14 05:22 UTC / 1:22am ET by the front-lane base subagent. Deliverable: `work/drafts/front/FrontWordsBase.lean`
(intended home `work/lean/SM/FrontWordsBase.lean`), 480 lines, imports `SM.FrontInterfaces` only. No
placeholder tactics, no `admit`/`native_decide`, no new `axiom` (`grep -n -i` over the file: zero hits).
Check: `cd work/lean && lake env lean ../drafts/front/FrontWordsBase.lean` → no errors, no warnings
(Lean v4.34.0-rc2, project Mathlib pin, ~6 s). Nothing written under `work/lean`; `SM/FrontWords.lean` and
the accepted `SM/FrontInterfaces.lean` (axiom `SM.ng_finite_word`) are untouched and nothing in them is
restated. `#print axioms` (run on a copy in /tmp with the print lines appended):

| declaration | axioms |
|---|---|
| `SM.FrontWord.IsCommStep.isStandardCircleBase_iff` | `propext`, `Classical.choice`, `Quot.sound` |
| `SM.FrontWord.IsComm.oword_isStandardCircleBase_iff` (= `hinv`) | standard three |
| `SM.FrontWord.isStandardCircleBase_comm_invariant` (`hinv` in its exact ∀-shape) | standard three |
| `SM.FrontWord.Descends.of_principalChain'` | standard three |
| `SM.ng_finite_word_nonbase_descends'` | standard three + `SM.ng_finite_word` |
| `labelRun_comm_above`, `labelRun_comm_below`, `Word.labelRun_map` | `propext`, `Quot.sound` |

The projection has exactly the axiom footprint of the accepted conditional theorem
`SM.ng_finite_word_nonbase_descends` (standard three + `SM.ng_finite_word`); `hinv` itself uses no
literature input.

## 1. What was owed and what is delivered

`SM/FrontInterfaces.lean` §5 derives the registry sentence "Thus every nonbase front has a finite principal
chain to a front of smaller s" (AXIOM_REGISTRY.md:105-106) in `Descends.of_principalChain` and projects it
as `ng_finite_word_nonbase_descends`, both under

```lean
hinv : ∀ W W' : OWord, IsComm W.letters W'.letters → (W.IsStandardCircleBase ↔ W'.IsStandardCircleBase)
```

("a disjoint-gadget commutation is the same front, ng:commutation; a lemma of the base/realization unit").
The review of the statement unit recorded the obligation to prove `hinv`. Delivered (namespace
`SM.FrontWord` unless stated):

```lean
theorem IsCommStep.isStandardCircleBase_iff {W W' : Word} (h : IsCommStep W W') :
    W.IsStandardCircleBase ↔ W'.IsStandardCircleBase
theorem IsComm.isStandardCircleBase_iff {W W' : Word} (h : IsComm W W') :
    W.IsStandardCircleBase ↔ W'.IsStandardCircleBase
theorem IsComm.oword_isStandardCircleBase_iff {W W' : OWord} (h : IsComm W.letters W'.letters) :
    W.IsStandardCircleBase ↔ W'.IsStandardCircleBase
theorem isStandardCircleBase_comm_invariant :
    ∀ W W' : OWord, IsComm W.letters W'.letters → (W.IsStandardCircleBase ↔ W'.IsStandardCircleBase)
theorem Descends.of_principalChain' {W : OWord}
    (hc : PrincipalChain OWord.sCountSyn OWord.IsStandardCircleBase W) (hW : ¬ W.IsStandardCircleBase) :
    Descends OWord.sCountSyn W
theorem SM.ng_finite_word_nonbase_descends' :
    ∀ W : OWord, ¬ W.IsStandardCircleBase → Descends OWord.sCountSyn W
```

The last one is `ng_finite_word_nonbase_descends isStandardCircleBase_comm_invariant`, i.e. the accepted
conditional theorem with `hinv` supplied; its conclusion is unchanged. `Descends.of_principalChain'` is the
same for the accepted derivation from a chain, and needs no axiom at all.

## 2. What `labelRun` does, and the one thing that is not obvious about it

`Word.IsStandardCircleBase W := labelRun W 0 [] = some []` (FrontInterfaces §1). `labelRun W k c` runs the
word over a cut of LABELS `c : List ℕ`, with `k` the letter index (0-based position in the word), incremented
for every letter: `Letter.labelStep ℓ k c` acts at the 1-based strand position `ℓ.idx` (take/drop, exactly
as `Letter.step`) with `Letter.labelAct`: a left cusp pushes `k :: k :: _` (its two arms carry the fresh
label `k` = the index of the letter), a right cusp removes two adjacent strands iff they carry the SAME label
(the two arms of one left cusp), a crossing is untyped (`none`). So the fresh labels are allocated by
POSITION IN THE WORD, not by a counter of left cusps.

Consequence for a commutation `X ++ [a, b] ++ Y ↦ X ++ [b', a'] ++ Y` (`IsCommStep`; `a'`, `b'` the
reindexed letters): `a` moves from letter index `|X|` to `|X| + 1`, `b` the other way, so whichever of the
two is a left cusp allocates the OTHER fresh label. The two label cuts after the factor are therefore NOT
equal in general; they differ by the transposition `|X| ↔ |X| + 1` of labels. Kernel-checked in the file:

```lean
example : Word.labelRun [.l 1 true, .l 3 false] 0 [] = some [0, 0, 1, 1] ∧
    Word.labelRun [.l 1 false, .l 1 true] 0 [] = some [1, 1, 0, 0] := by decide
```

(`l₁ l₃ ↦ l₁ l₁` is the "below" commutation, `b = l 3` reindexed by `−2`). So the naive lemma
"`labelRun (X ++ [a, b] ++ Y) = labelRun (X ++ [b', a'] ++ Y)`" is false; what is true is invariance up to
an injective relabelling, and `= some []` is invariant under relabelling. Two facts make the transposition
harmless: the labels present before the factor are `< |X|` (they were allocated by letters of index
`< |X|`; `Word.labelRun_lt`), and the labels `Y` allocates are `≥ |X| + 2`; the transposition fixes both.

## 3. Route (file sections)

1. **Relabelling** (§1-2). `Letter.labelAct_map`: for injective `f`,
   `ℓ.labelAct (f k) (L.map f) = (ℓ.labelAct k L).map (List.map f)` (the right cusp's equality test is
   invariant under an injection; the left cusp pushes the mapped fresh label; a crossing is `none` on both
   sides). `Letter.labelStep_map`: the same through take/drop (`List.map_take`, `List.map_drop`).
   `Word.labelRun_map`: for injective `f` with `f j = j` for all `j ≥ k`,
   `labelRun W k (c.map f) = (labelRun W k c).map (List.map f)` (induction on `W`; the fixing hypothesis is
   needed because the counter `k, k+1, …` is not mapped).
2. **Positional lemmas** (§1). β1's `step_prefix`, `step_of_prefix`, `step_eq_some_iff`, `act_append`,
   `act_window` repeated for `labelStep`/`labelAct` (`labelStep_prefix`, `labelStep_of_prefix`,
   `labelStep_eq_some_iff`, `labelAct_append`, `labelAct_window`), plus `labelAct_reindex`,
   `labelAct_r_eq_some_iff`, `labelAct_mem`. β1's lemmas are stated for `Cuts = List Bool` and its
   `exists_split` too, so a `List ℕ` copy `exists_split_labels` was needed.
3. **Exchange** (§3). `labelRun_comm_above` / `labelRun_comm_below`: for any injective `f` with
   `f k = k + 1` and `f (k + 1) = k`, if `labelRun [a, b] k c = some c'` and the gadgets are disjoint
   (`b.idx + b.arity ≤ a.idx`, resp. `a.idx + a.coarity ≤ b.idx`), then the exchanged pair run on `c.map f`
   gives `some (c'.map f)`. Same window bookkeeping as β1's `run_comm_above`/`run_comm_below`
   (`A = B ++ w ++ H`, `R = H ++ L'`); the two local actions are transported by `labelAct_map` with
   `f (k+1) = k` (for the letter that moves to index `k`) and `f k = k + 1` (for the one that moves to
   `k + 1`). Stated for abstract `f` so that no `Equiv` coercions appear in the proofs.
4. **The base** (§4). `IsCommStep.isStandardCircleBase` (one direction): split the run at the factor
   (`labelRun_append` twice), get `c₀` after `X` with labels `< |X|` (`labelRun_lt`), take
   `f := Equiv.swap |X| (|X|+1)` (packaged as `exists_swap_fun`), so `c₀.map f = c₀`; apply the exchange
   lemma to the factor and `labelRun_map` to `Y` (fixing labels `≥ |X| + 2`); `(some []).map _ = some []`.
   `IsCommStep.symm`: the reverse exchange is again a commutation step (the two reindexings cancel:
   `a.idx + b.coarity - b.arity + b.arity - b.coarity = a.idx` under the disjointness bound), so the iff
   follows without a second computation; `IsComm` is the symmetric closure.
5. **Projection** (§5). `Descends.of_principalChain'` and `SM.ng_finite_word_nonbase_descends'`.

## 4. Sanity checks in the file (by `decide`)

* the transposition example of §2 above;
* both closings `l₁ l₃ r₃ r₁` and `l₁ l₁ r₃ r₁` are unions of standard circles;
* a right cusp commuted past a left cusp above it (`r₃ l₁ ↦ l₁ r₅`, reindex `+2`) inside a closed base
  word: both words have `labelRun … 0 [] = some []`.

## 5. Notes for the reviewer

* `IsCommStep` carries no `1 ≤ idx` clause; typedness supplies it (`labelStep_eq_some_iff` yields
  `1 ≤ ℓ.idx` for every letter that acts), exactly as in β1's closedness proofs.
* `if_pos` is deprecated in this toolchain ("use `ite_eq_left`"), which is why β1 uses `ite_eq_left`; the
  file follows it.
* The three `IsStandardCircleBase` results are on `Word`, `Word` (`IsComm`), and `OWord`; the `OWord` one
  unfolds `OWord.IsStandardCircleBase` by definition. `Descends.of_principalChain'` and the projection use
  `isStandardCircleBase_comm_invariant`, whose statement is character-for-character the `hinv` binder of
  `Descends.of_principalChain` and `ng_finite_word_nonbase_descends`.
* Nothing here depends on the geometric realization (unit β2); the obligation recorded for β2,
  `(realize W).IsStandardCircles ↔ W.IsStandardCircleBase`, is separate and still open.
