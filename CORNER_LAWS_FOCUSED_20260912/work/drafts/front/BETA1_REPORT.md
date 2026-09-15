# Lane β, unit β1 — PL fronts and oriented Rutherford words (report)

Written 2026-09-14 03:25 UTC / 11:25pm ET by the β1 prover subagent. Design of record:
`work/reports/front-block-design-FINAL-20260913.md` (§2 G1 and "Judge's additions", §4, §7, §9 FR-5/FR-6, §11).
Nothing was written under `work/lean`; no axiom was declared.

## 1. Deliverables and status

| file | intended home | lines | `lake env lean` | `sorry` | `#print axioms` |
|---|---|---|---|---|---|
| `work/drafts/front/FrontPL.lean` | `work/lean/SM/FrontPL.lean` | 560 | 0 errors, 0 warnings | none | standard (`propext`, `Classical.choice`, `Quot.sound`) for every lemma; `PLFront.defect` and `IsStandardCircles.defect_eq` additionally reach the registered literature interface `SM.lp_lm` through `P` (`SM/LocalPolynomial.lean`), as every use of `P` does |
| `work/drafts/front/FrontWords.lean` | `work/lean/SM/FrontWords.lean` | 1238 | 0 errors, 0 warnings | none | standard only (`propext`, `Quot.sound`; `Classical.choice` in `Moves.defect_nonneg`/`word_bound_of` via `Nat.strong_induction_on`) |

Checked with `cd work/lean && lake env lean <file>` (Lean v4.34.0-rc2, Mathlib pin of the project). Imports:
`FrontPL` imports `SM.LocalPolynomial` (brings `SM.Link.Shadow`/`Diagram`, `degAZ`, `P`); `FrontWords` imports
only `Mathlib.Tactic` (the word layer does not depend on the PL layer: the geometric readings are parameters of
`wordMovesOf`; the home module may add `import SM.FrontPL` if convenient). Total 1,798 lines (estimate was
1,100-1,600; the excess is docstrings and 26 `decide` sanity checks against the printed text).

## 2. FrontPL.lean — namespace `SM.PLFront` (graft G1)

Class (`structure PLFront`): `Γ : Shadow`, `generic : Γ.Generic`, `nonvertical : ∀ s, (Γ.dir s).1 ≠ 0`
(sm-3:1825-1831: PL reading of "actual map of a nonempty finite union of parameter circles", "finitely many
transverse double points ... no other singularities", "no vertical tangencies", "cusps meet no other strand"
= `Generic.tail_off`).

| declaration | renders | source |
|---|---|---|
| `prev`, `eIn`, `eOut`, `eIn_fst_ne_zero`, `eOut_fst_ne_zero` | incoming/outgoing edge at the tail vertex of a strand | — |
| `IsCusp s := (eIn s).1 * (eOut s).1 < 0` | "ordinary semicubical cusps" (PL reading: x-reversal vertex) | 1827 |
| `IsLeftCusp`, `IsRightCusp`, `isCusp_iff`, `isLeftCusp_xor_isRightCusp`, `not_isLeftCusp_and_isRightCusp` | left/right by the signs of the incident edges; every cusp is left xor right | 1906-1908 (l_m, r_m) |
| `not_isCusp_iff`, `xdir`, `xdir_prev_eq_of_not_isCusp`, `xdir_prev_ne_of_isCusp` | the rightward bit of a strand; constant along a cusp-free run, flipped at a cusp (the direction bit of the word layer) | — |
| `cuspDisc s := (eOut s).1 * det (eIn s) (eOut s)`, `IsDownCusp`, `IsUpCusp` | "A downward cusp is traversed from its locally upper arm to its locally lower arm" | 1833-1834 |
| `cusp_det_ne_zero` (A's proof), `cuspDisc_ne_zero`, `isDownCusp_or_isUpCusp`, `isDownCusp_xor_isUpCusp`, `isUpCusp_iff_not_isDownCusp` | arms not collinear (from `Regular`); every cusp is down xor up | 1833; src:contact 3349-3350 |
| `isDownCusp_iff_of_isLeftCusp`, `isDownCusp_iff_of_isRightCusp` | at a left cusp down ⇔ `0 < det`, at a right cusp down ⇔ `det < 0` | 1833 |
| `armIn`, `armOut`, `armHeight`, `isDownCusp_iff_armIn_above` | the literal reading: arms as rays from the vertex, the upper arm has the larger height `z/|x|`; down ⇔ the incoming arm is upper | 1833-1834 |
| `slope`, `strandA/B` (+ `_mem`, `_ne`, `not_adjacent`, `det_..._ne_zero`, `slope_strandA_ne_slope_strandB`), `overStrand`, `overStrand_mem`, `diagram`, `diagram_underStrand`, `slope_overStrand_lt` | "At a crossing the branch with smaller dz/dx is over"; the front is its own `Diagram` (identity rounding, FINAL G1 (ii)) | 1832 |
| `det_pos_iff_of_slope_lt`, `det_eq_mul_slope_sub`, `det_eq_zero_of_slope_eq`, `isPositive_iff`, `isPositive_iff_xdir_eq`, `sign_eq_one_iff_xdir_eq`, `sign_eq_neg_one_iff_xdir_ne`, `sign_eq_ite`, `writhe_eq_sum_ite` | the printed sign rule: positive ⇔ both x-directions agree (the bridge to the word bits) | 1908-1912; 2030-2031 |
| `downCount`, `upCount`, `cuspCount`, `leftCount`, `rightCount`, `crossingCount`, `writhe := diagram.writhe`, `sCount`, `defect := D − w − degAZ (P diagram) − 1` | `D(F)`, `w(F)`, `s(F)`, display ng:defect on the identity rounding | 1834-1837, 1897-1898 |
| `card_subtype_add_of_iff`, `cuspCount_eq_downCount_add_upCount`, `cuspCount_eq_leftCount_add_rightCount`, `downCount_le_cuspCount`, `sCount_eq` | `cusps = D + U = left + right` | — |
| `IsStandardCircles` (no crossing; per component exactly one left and one right cusp), `.writhe_eq_zero`, `.crossingCount_eq_zero`, `card_subtype_eq_sum_comp`, `.cuspCount_eq : cuspCount = 2c`, `.sCount_eq`, `.defect_eq` | the base of ng:finite-word / ng:circle ("simple crossing-free component with exactly one left and one right cusp"; unions and nesting allowed) | 2046-2053 |

**Correction to design A (recorded for the review).** A's sketch (and FINAL §4, copied from A) has
`IsDownCusp s := IsCusp s ∧ 0 < det (eIn s) (eOut s)`. Checked on a right cusp with arms `(−1, 1)` (upper) and
`(−1, −1)` (lower), traversed upper → lower: `eIn = (1, −1)`, `eOut = (−1, −1)`, `det = −2 < 0`, so A's formula
calls this DOWN cusp an up cusp. The formula is right only at left cusps (where the two rays from the vertex point
right and "counterclockwise from the outgoing ray" means "above"). The definition here carries the x-side factor
`(eOut s).1` — exactly as design B's smooth criterion carries `x''` (FINAL §1, "downward cusp" row, "checked
correct on both cusp sides") — and `isDownCusp_iff_armIn_above` proves the literal arm-height reading for both
sides. The letter-tracing conventions of the word layer (below) were re-derived from this corrected reading and
agree with every printed orientation fact (§4 checks).

## 3. FrontWords.lean — namespace `SM.FrontWord`

### 3.1 Letters, cuts, typing (sm-3:1906-1910; FR-5, FR-6 1-based)

| declaration | renders |
|---|---|
| `inductive Letter := l (m) (d : Bool) \| r (m) \| σ (m)` | Rutherford's letters with the direction bit on `l` (FINAL "Judge's additions": the upper new arm travels rightward iff `d`) |
| `abbrev Cuts := List Bool` | rightward bits of the strands at a cut, top to bottom |
| `Letter.idx`, `reindex`, `isCrossing`, `arity` (strands read: l 0, r 2, σ 2), `coarity` (strands written: l 2, r 0, σ 2) | bookkeeping |
| `Letter.act` | the local action from the letter's position down: `l _ d ↦ d :: !d :: L`; `r` removes two strands of OPPOSITE bits (else untyped); `σ` exchanges two strands |
| `Letter.step ℓ c := if 1 ≤ idx ∧ idx − 1 ≤ c.length then (act (c.drop (idx−1))).map (c.take (idx−1) ++ ·) else none` | FINAL's `Letter.step` written through `take`/`drop`/`act` (same values; the `decide` checks of the FINAL sketch all pass) |
| `step_prefix`, `step_of_prefix`, `step_eq_some_iff`, `act_append`, `act_window`, `act_σ_eq_some_iff`, `act_r_eq_some_iff`, `reindex_*` | the locality lemmas: a typed letter acts on the suffix after `idx − 1` strands, reads `arity` strands and writes `coarity` |
| `Word.run`, `run_nil/cons/singleton/append`, `run_one/two/three_iff` | the typing of a word from a cut |
| `Word.Closed W := run W [] = some []` (decidable), `Closed.replace`, `Closed.exists_run`, `run_prefix_unique` | closed words = no strands to no strands; replacing a factor with the same typing effect keeps closedness |
| `Word.crossingCount`, `cuspCount`, `sCount`, `sCount_eq_length`, `sCount_append` | the syntactic `s` (every letter is one singularity) |
| `Letter.downBit`, `signBit`, `Word.downCountFrom`, `writheFrom` | letter tracing of `D` and `w` (β2 correspondence targets; FINAL adopts the geometric reading): `l _ d` is down iff `d = false`; `r m` is down iff the upper strand travels rightward; `σ` positive iff the two bits agree (`PLFront.isPositive_iff_xdir_eq`) |
| `structure OWord := letters, closed`, `OWord.sCountSyn/downCountSyn/writheSyn` | "an actual finite front word" |

### 3.2 The eight word-move patterns (list rewrites, 1-based, FR-6) and closedness

| relation | pattern (source) | closedness lemma | syntactic Δs |
|---|---|---|---|
| `IsCommStep`, `IsComm` (symmetric) | `[a, b] ↦ [b, a']` when `b` acts strictly above `a`'s footprint (`b.idx + b.arity ≤ a.idx`; `a'` = `a` reindexed by `+coarity(b) − arity(b)`), or `[a, b] ↦ [b', a]` when `b` acts strictly below (`a.idx + a.coarity ≤ b.idx`; `b'` reindexed by `+arity(a) − coarity(a)`): the "two-strand index shift" (1929-1931) | `IsComm.closed` via the uniform `run_comm_above/below` (no case split on letter kinds) | 0 |
| `IsTypeI` | `l_m σ_{m−1} r_m` or `l_m σ_{m+1} r_m` deleted (1955-1956) | `IsTypeI.closed` (`run_typeI_left/right`: the cut is unchanged) | −3 |
| `IsTypeII` | `l_{m−1} σ_m σ_{m−1} ↦ l_m`, `l_{m+1} σ_m σ_{m+1} ↦ l_m` (1977-1978), same bit; right-cusp versions `σ_{m−1} σ_m r_{m−1} ↦ r_m`, `σ_{m+1} σ_m r_{m+1} ↦ r_m` (1988-1989 "follow these same local strands backwards") | `IsTypeII.closed` (four `run_typeII_*`) | −2 |
| `IsTypeIII` | `σ_{m+1} σ_m σ_{m+1} ↔ σ_m σ_{m+1} σ_m`, both directions (1995-1996) | `IsTypeIII.closed` (`run_typeIII_aux/aux'/of_split`: both permute `p q r ↦ r q p`) | 0 |
| `IsZigzagDeletion` | `l_m r_{m+1}` or `l_{m+1} r_m` deleted (2014-2018) | `IsZigzagDeletion.closed` | −2 |
| `IsCrossedCuspShortcut` | `l_i d σ_i ↦ l_i (!d)` (bit flipped: "the boundary arms exchange places"), `σ_i r_i ↦ r_i` (2027-2037) | `IsCrossedCuspShortcut.closed` | −1 |
| `IsCircleDeletion` | `l_m r_m` deleted, `X ++ Y ≠ []` (2046-2049) | `IsCircleDeletion.closed` | −2 |
| `IsCuspSkeinStep`, `IsCuspSkein` (either principal direction) | `A = X l_{m+1}d σ_m Y`, `A' = X l_m d σ_{m+1} Y`, `C = X l_m d Y` if `a = !d`, `X l_{m+1} d Y` if `a = d`, where `a` is the bit of the through-strand (position `m` of `run X []`) (2087-2126) | `IsCuspSkein.closed_A'`, `.closed_C` (`run_skein_A/A'/Ctop/Cbottom`: all three factors produce the same output cut) | `s(A') = s(A)`, `s(C) = s(A) − 1` |

`Pres`, `Del`, `Skein` on `OWord` (items 1-3 of ng:finite-word; deletion directions of I/II only in `Pres`),
`Pres.closed`, `Del.closed`, `OWord.ofRewrite`, and the syntactic `s`-laws `Pres.sCountSyn_le`,
`Del.sCountSyn_lt`, `Skein.sCountSyn` (+ per-pattern `.sCount` lemmas).

**Resolution of the FINAL placeholders (review-sensitive).**
* `IsComm`: the disjointness condition is on strand footprints in the intermediate cut. A letter moving past a
  gadget below it keeps its index; moving past a gadget above it, its index changes by that gadget's strand-count
  change (+2 past `l`, −2 past `r`, 0 past `σ`). The only non-strict case is `[r_i, l_i d]`, whose two commuted
  forms `[l_i d, r_{i+2}]` and `[l_{i+2} d, r_i]` are reached through the symmetrisation (each is a strict
  exchange back to `[r_i, l_i d]`).
* Cusp-skein bits, derived from the printed (t,u) definitions on `A = l₂σ₁`, `A' = l₁σ₂` over the cut `[a]`:
  `t = +1 ↔ a = true` ("orientation from L to 2"), `u = +1 ↔ d = false` ("from 1 to 3, a downward cusp" — and
  `l₂ false` IS a down cusp under the corrected `IsDownCusp`). The right endpoints `1, 2, 3` carry bits `d, a, !d`
  in `A` and in `A'` iff `A'` has the same bit `d` ("identical ... boundary attachments"); `C_top = l₁ d''`
  matches iff `d'' = d ∧ a = !d` (`t = u`), `C_bottom = l₂ d''` iff `d'' = d ∧ a = d` (`t = −u`); "the new cusp
  direction is u in either case" = bit `d`. The whole printed table (signs `−tu`, `tu`; local `D`) is then
  reproduced by `decide` (§4). An incompatible smoothing is NOT admitted (it would break `skein_B`).
* Right-cusp cusp-skein templates (`σ₁r₂ ↔ σ₂r₁`) are not included: item 2 of the axiom cites eq. ng:cusp-words
  "or its reflected pattern" only (the reflection of `l₂σ₁` is `l₁σ₂`, i.e. the other direction). Open item if the
  procedure's "Middle right cusp" rows are read as needing them.

### 3.3 The descent skeleton (FINAL §4/§8, verbatim + one lemma)

`structure Moves` (α, s, B, Pres, Del, Skein, Base); `inductive Moves.Chain` (base | del | pres | skein: stop
at the first strict decrease of `s` or at the base); `structure Moves.Laws : Prop` (pres_B, pres_s, del_B,
del_s, skein_B, skein_s, base_B); `nonneg_of_chain`, `defect_nonneg` (proved, FINAL's proof); `step_s_le`
("Before that decrease the selected procedure does not increase s" as a CONSEQUENCE of the laws, FR-6);
`wordMovesOf (s B Base) : Moves` with `Pres/Del/Skein` fixed and the geometric readings as parameters (+ `rfl`
simp lemmas); `laws_s_of_syn` (the three `s`-clauses for any `s` agreeing with `sCountSyn`);
`FiniteWordStatement K := ∀ W : K.α, K.Chain W` (the SHAPE of ng:finite-word; the axiom `SM.ng_finite_word`
itself is NOT declared here); `word_bound_of : Laws → FiniteWordStatement → ∀ W, 0 ≤ B W`.

## 4. Sanity checks against the printed text (26 `example`s by `decide`, all pass)

Standard circle closed in either orientation with `D = 1`, `w = 0` (2052-2053); `l₁σ₁r₁` typed; the type-I curl
typed on `[true]` with bit `true` and on `[false]` with bit `false`, REJECTED with mismatched bits (1958-1960),
its crossing positive and exactly one of its cusps down (ng:type-I-counts); the crossed cusp `l₁σ₁` has sign −1
(2030-2031); the zigzag's two cusps are both down or both up (2015-2017); the four rows of the (t,u) table
(2107-2118) for `sign(A)`, `sign(A')`, local `D`, and the compatible smoothing's output cut (2119-2126); the
crossing-free single-component zigzag `l₁ l₂ r₁ r₁` is closed with `s = 4`, `D = 3` (FINAL §2 G1 (iii) prints it
as `l₁ l₂ r₁ r₂`, which is not typed — after `r₁` only two strands remain; the FINAL's point stands: it is closed,
crossing-free, not a union of standard circles, so the base must be the geometric predicate).

## 5. Open items for β2 (realization) and later units

1. `realize : OWord → PLFront` (grid, letter `k` in column `[k, k+1]`, strands at integer heights, cusps as wedge
   corners) and the correspondence lemmas: `(realize W).sCount = W.sCountSyn` (then `laws_s_of_syn` gives
   `pres_s`, `del_s`, `skein_s` of `wordMovesOf`), `(realize W).downCount = W.downCountSyn`,
   `(realize W).writhe = W.writheSyn` (via `PLFront.sign_eq_ite`/`writhe_eq_sum_ite` and `xdir` = the cut bits),
   `(realize W).crossingCount = W.letters.crossingCount`, `cuspCount`.
2. `wordMoves := wordMovesOf (fun W => (realize W).sCount) (fun W => (realize W).defect) (fun W => (realize W).IsStandardCircles)`
   and `ng_finite_word_statement := FiniteWordStatement wordMoves` (statement unit; fixed name `SM.ng_finite_word`).
3. `IsStandardCircles → downCount = Γ.c` (each standard circle has exactly one down cusp) is a planarity fact
   (the two x-monotone arcs of a crossing-free component do not cross, so one is above the other); not provable
   from the local data in `FrontPL`. Row 81's `base_B` needs it — on realized words it is a direct computation.
4. The home `FrontWords.lean` may `import SM.FrontPL`; nothing in it requires that.
5. `PLFront.defect` depends on `SM.lp_lm` (through `P`); any `Laws` instance inherits it, as intended by the policy.
6. Independent review items (FR-6): the `IsCommStep` footprint rule and shifts; the cusp-skein bit table; the
   right-cusp type-II versions; the exclusion of right-cusp skein templates; side conditions `1 ≤ m` / `2 ≤ m`
   (only where natural subtraction appears; untyped patterns never occur in closed words).
