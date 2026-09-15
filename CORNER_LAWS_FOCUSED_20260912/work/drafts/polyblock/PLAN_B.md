# PLAN_B — the five polynomial rows by a RECORD-LEVEL `(N, b)` induction (tag B)

Written 2026-09-13/14 by a Claude Code proof-architect subagent (tag B) of the pod executor.
Skeleton: `work/drafts/polyblock/Skeleton_B.lean` (1,218 lines) — typechecks with `lake env lean`
(no errors).

**Status at hand-back (2026-09-14).**  The skeleton went beyond a skeleton: the complete chains of
**rp:record-polynomial, lp:core, lp:split-circle and lc:presentations are PROVED** (no `sorry` in
§0-§5), and `#print axioms` gives
* `SM.record_polynomial`, `SM.split_circle`, `SM.presentations`: `[propext, Classical.choice,
  Quot.sound, SM.lp_lm]`;
* `SM.lp_core`: `[propext, Classical.choice, Quot.sound, SM.lit_homfly, SM.lp_lm, SM.lp_lm_uniqueness]`
  (the three interfaces lp:core consumes; `lp_lm_uniqueness` enters through the accepted
  lp:coefficient-transport, see D4);
* `SM.stack`: `sorryAx` — the 7 mp:stack chain statements S3-S9 of §6 (`smoothBlock`,
  `rBlockOrdered_smooth`, `restrictSmoothIsoInternal`, `restrictSmoothIsoExternal`,
  `RBasing.restrict`, `rUnderFirst_restrict`, `stack_formula`) are the only `sorry`s left; S1
  (`exists_blockCompatible_rbasing`) and S2 (`isBad_internal`) are proved, and `stack` /
  `split_union` are proved from `stack_formula`.  Skeleton: 1,247 lines, 106 declarations.
  Remaining mp:stack work ≈ 640 lines (§7, S3-S10).

The five row bundles are copied verbatim from `work/drafts/*_statement.lean`.  What remains to do
for the four finished rows is the acceptance procedure (independent statement review; the drafts
`LpCore_statement.lean` etc. already carry the reviewed statements) and porting §0-§5 into
`work/lean` as a library module plus the four row modules.  mp:stack has its own unit list (§7).

Rows: rp:record-polynomial (sm-3:1215-1305), lp:core (1041-1178), lp:split-circle (1180-1213),
lc:presentations (1306-1344), mp:stack (1494-1536).  Frame SM15.

---------------------------------------------------------------------------------------------------

## 0. The design decisions (and the insight that shapes everything)

**D1 — one induction principle, consumed by every row.**  The printed proofs all run the same
lexicographic induction on `(N, b)` (crossing count, bad-crossing count for a chosen based order).
The skeleton proves it ONCE as a diagram-level induction principle

```
Diagram.skein_induction_based (Φ : ∀ D, RBasing D.record → Prop)
  (init : ∀ D B, B.RUnderFirst → Φ D B)
  (step : ∀ D B v, B.IsBad v → Φ (D.switch v.1) (D.rbasingSwitch v.1 B) →
     (∀ D₀ B₀, IsOrientedSmoothing D v.1 D₀ → Φ D₀ B₀) → Φ D B) : ∀ D B, Φ D B
```
(and the plain form `skein_induction` with `init` handed a `Diagram.Basing` with `Diagram.UnderFirst`
and the step at an arbitrary crossing).  Proof: outer strong induction on `N = Fintype.card
D.Γ.Crossing`, inner induction on `b = B.badCount`; it consumes `badCount_eq_zero_iff`,
`exists_isBad_of_badCount_ne_zero`, `badCount_rbasingSwitch`, `IsOrientedSmoothing.card_crossing`.
The rows are thereby insulated from the measure implementation.

**D2 — the measure lives on RECORDS (`Record.RBasing`).**  A record-level based order is an injective
rank `comps → ℕ` plus a *base occurrence* per circle (`base : M → M`, constant on circles, landing on
the circle).  The based rank of an occurrence is `key v := toLex (rank (comp v), pos v)` with
`pos v := Nat.find (∃ n, succ^n (base v) = v)` (succ-iterates from the base).  Bad: `isOver v ∧ key v <
key (pair v)`.  This is the "cleaner alternative" of the brief, and it is NEEDED, but for a different
reason than the brief anticipated:

> With D1, the induction runs on ONE diagram `D`; the partner `D'` of rp:record-polynomial is
> quantified INSIDE `Φ` (`Φ D B := ∀ D', RecordIso D.record D'.record → lmF D = lmF D'`).  So no
> synchronised bad count on `D'` is ever needed — the step transports the switch and the smoothing
> through `RecordIso.switch` / `RecordIso.smooth` and the two accepted diagram bridges.  BUT at
> `b = 0` we must know `lmF D' = μ^{c−1}`, i.e. that `D'` is UNDER-first for SOME `Diagram.Basing`.
> That is exactly "UNDER-first is a record-level property transported by record isomorphisms":
> `RBasing.map ι`, `rUnderFirst_map`, and then the ONE geometric bridge
> `exists_underFirst_of_rUnderFirst : B.RUnderFirst → ∃ B' : D.Basing, D.UnderFirst B'`.
> A diagram-level bad count (on `Diagram.Basing`) could not deliver this without the same bridge.

**D3 — any bad crossing, not the first.**  Switching ANY bad occurrence `x` of a fixed based order
lowers `badCount` by exactly one (`x` becomes good; `pair x` was not bad and is still not bad since
`key x < key (pair x)`; every other crossing keeps its bits and its keys).  The printed "first bad
crossing" is a device of LM's construction and is not needed for the lexicographic induction.  For
mp:stack the block-compatible based order makes every bad crossing internal (`isBad_internal`).

**D4 — lp:core without re-deriving the descent.**  `P` is an `RCompetitor` (planar/RI/II/III by
`congrArg` through `lmF`'s clauses; `circle` from `lmF_unknot`; `skein` from `lmF_sourceSkein` through
`φ ∘ T.toTG` and the additive `R`-linear `reMap` — no descent needed).  Hence the accepted
lp:coefficient-transport gives `gaussian` (`RCompetitor.toRG_eq_phi_toTG_lmF P`) and `eq_homfly`
(`coefficient_transport P homfly`) with NO induction.  The induction still proves `support`,
`ne_zero`, `unique` exactly as printed.  Axiom footprint unchanged (lp:core consumes lp_lm,
lp_lm_uniqueness (through the accepted transport lemma) and lit_homfly anyway).  Reviewer note: the
printed proof derives the descent by induction; the Lean route proves the same fixed `Prop`
differently — fidelity is about the statement, which is untouched.

---------------------------------------------------------------------------------------------------

## 1. The chain, in dependency order, with statements, sketches and line counts

Notation: `S` = proved in the skeleton (line counts are actual); `sorry` = open (est. lines).

### §0 Algebra (all S, 45 lines)

| lemma | statement | proof |
|---|---|---|
| `T.eq_of_skein_l` | `l a + l⁻¹ b + m c = 0 → l a' + l⁻¹ b + m c = 0 → a = a'` | `l (a−a') = 0`, multiply by `lInv` (`T.lInv_mul_l`). |
| `T.eq_of_skein_lInv` | same with `l⁻¹` in front of `a` | multiply by `l` (`T.l_mul_lInv`). |
| `Diagram.skeinTriple_of_smoothing` | `IsOrientedSmoothing D x D₀ → (IsPositive x ∧ IsSkeinTriple D (D.switch x) D₀) ∨ (¬IsPositive x ∧ IsSkeinTriple (D.switch x) D D₀)` | `switch_isPositive_self`, `switch_switch`, `IsOrientedSmoothing.switch`. |
| `skein_recursion_pos` | any `Q : Diagram → R` with the campaign skein: `IsPositive x → Q D = aInv·aInv·Q(D.switch x) + aInv·z·Q D₀` | `linear_combination aInv * hs − Q D * (aInv_mul_a)`. |
| `skein_recursion_neg` | `¬IsPositive x → Q D = a·a·Q(D.switch x) − a·z·Q D₀` | `linear_combination (−a) * hs − Q D * (a_mul_aInv)`. |

### §1 Record-level based order (`Record.RBasing`, all S, ≈ 200 lines)

| lemma | statement | proof |
|---|---|---|
| `RBasing` | `rank : comps → ℕ`, `rank_inj`, `base : M → M`, `base_comp`, `base_const` | — |
| `exists_pow_base_eq` | `∃ n, (succ^n) (base v) = v` | `succ_cycle` + `SameCycle.exists_pow_eq'`. |
| `pos`, `pow_pos_base`, `pos_le`, `pos_eq_zero_iff` | `pos v := Nat.find …`; spec; minimality; `pos v = 0 ↔ base v = v` | `Nat.find_spec/min'/eq_zero`. |
| `key`, `key_injective` | `key v := toLex (rank (comp v), pos v)`; injective | `rank_inj`, `base_const`, `pow_pos_base` (calc). |
| `IsBad`, `RUnderFirst`, `badCount` | `isOver v = true ∧ key v < key (pair v)`; `∀ v, isOver v → key (pair v) < key v`; `(univ.filter IsBad).card` (classical) | — |
| `badCount_eq_zero_iff` | `badCount = 0 ↔ RUnderFirst` | `filter_eq_empty_iff`, `lt_trichotomy`, `key_injective`, `pair_ne`. |
| `exists_isBad_of_badCount_ne_zero` | `badCount ≠ 0 → ∃ v, IsBad v` | `Finset.card_pos`. |
| `switch`, `key_switch` | `B.switch x : RBasing (ρ.switch x)` (same fields); `key` unchanged (`rfl`) | — |
| `badCount_switch` | `IsBad x → (B.switch x).badCount + 1 = B.badCount` | `filter (switch).IsBad = (filter IsBad).erase x` (stated over `ρ.M` to dodge reducible-transparency issues), `switch_isOver_self/pair/of_ne`, `card_erase_of_mem`. |
| `map`, `key_map`, `isBad_map`, `badCount_map`, `rUnderFirst_map` | transport along `ι : RecordIso ρ ρ'`; `key (map) (Φ v) = key v` etc. | `Nat.find_congr'` with `Φ_pow`; `Finset.card_map`. |
| `default` | `RBasing ρ` for every `ρ` | `Fintype.equivFin`; `Classical.choose` base (constancy by `subst`). |

### §2 Diagram side: the bridge and the induction principles (all S, ≈ 230 lines)

| lemma | statement | proof |
|---|---|---|
| `cyclicOffset_lt_of_cycBetween` | reals on `[0,k)`: `off c₀ < off cu → off c₀ < off co → cycBetween c₀ cu co → off cu < off co` | `split_ifs; rcases; linarith` (24 cases, all automatic). |
| `exists_rank_equiv` | injective `Fin c → ℕ` sorts into `Fin c ≃ Fin c` with `r i < r j ↔ rank i < rank j` | `Finset.orderIsoOfFin` on the image, `Equiv.ofBijective`. |
| `exists_base_before`, `exists_base_before'` | nonsingular basepoint immediately before an occurrence (offset form; component named) | from accepted `exists_basing_first`; dependent rewrite via a `subst` helper. |
| `visitBetween_of_pos_lt` | `compOf u = compOf o → 0 < pos u → pos u < pos o → VisitBetween (base u) u o` | `ent`, `visitSucc_pow_ent`, `exists_ent`, `ent_add_sub`, `pos_le`, `visitBetween_ent_iff`. |
| `rbasingSwitch`, `badCount_rbasingSwitch` | the based order of `(D.switch x).record`; count drops by one | `switchRecordIso` (identity on `M`), `badCount_map`, `rfl`, `Record.badCount_switch`. |
| `exists_underFirst_of_rUnderFirst` | **the geometric bridge**: `B.RUnderFirst → ∃ B' : D.Basing, D.UnderFirst B'` | rank via `exists_rank_equiv`; basepoints via `exists_base_before'` (or `exists_nonsingular_base` on an occurrence-free circle); UNDER-first: rank case is `Prod.Lex` left; same-circle case: `pos u = 0` gives `u = base` and the "first" property, else `visitBetween_of_pos_lt` + `cyclicOffset_lt_of_cycBetween`; a `subst` helper `hcast` moves the dependent `base i` across `compOf u = compOf o`. |
| `skein_induction_based`, `skein_induction` | D1 | 25 + 8 lines. |

### §3 lp:core (all S, ≈ 170 lines)

`P_congr`, `P_planar`, `P_reidemeister_I/II/III`, `P_circle`; `G := φ ∘ T.toTG ∘ lmF`;
`gaussI_alg_sq`, `phi_lInv'`, `phi_mInv'` (normal forms `−(i•aInv)`, `i•zInv`); `G_skein` (apply
`φ ∘ toTG` to `lmF_sourceSkein`, `Algebra.smul_def`, `linear_combination` with `i² = −1`); `P_skein`
(`reMap` of `G_skein`, `reMap_toRG_mul`); `P_rcompetitor`, `homfly_rcompetitor`; `P_gaussian`,
`P_eq_homfly` (coefficient transport); `phi_toTG_mu : φ(μ) = δ` (same normal forms +
`linear_combination`); `P_of_lmF_eq_mu_pow`, `P_underFirst_init`, `P_crossingFree`;
`P_recursion_pos/neg`; `P_support` (`skein_induction`; `exists_smoothing_counts` for `c ± 1`;
`InSupportM.delta_pow/a_mul/aInv_mul/z_mul/z_mul_of_pred/add/sub`); `P_specQ` (`specQ_delta`,
`specQ_positive/negative_identity`); `P_ne_zero`; `P_unique` (`funext`, `skein_induction`, the two
recursions for `Q` and `P`); `P_knot_support`.

### §4 rp:record-polynomial, lc:presentations (all S, ≈ 75 lines)

`sign_eq_of_recordIso`, `isPositive_iff_of_recordIso`, `recordIso_switch`, `exists_smoothing_pair`,
`exists_underFirst_of_recordIso`, `componentCount_eq_of_recordIso`; **`lmF_eq_of_recordIso`** by
`skein_induction_based` with the partner quantified inside `Φ` (init: both values `μ^{c−1}`; step:
equal switched values, equal smoothed values, common sign case, `T.eq_of_skein_l/lInv`).

### §5 lp:split-circle (all S, ≈ 150 lines)

`Record.addFree` (comps `Option comps`); `componentCount_addFree`; `addFree_switch` (`rfl`);
`freeCompAddFreeEquiv : FreeComp (addFree) ≃ Option (FreeComp ρ)`; `addFreeSmoothIso` (`Φ := refl`,
`e` by `sumCongr`/`optionEquivSumPUnit`/`sumAssoc`, all clauses `rfl`); `RecordIso.addFree`;
`eraseFreeAddFreeIso` (`Equiv.optionSubtypeNe`, `subtypeUnivEquiv`, `restrict_succ_val_of_keep`);
`RBasing.addFree`, `pos_addFree` (`rfl`), `key_addFree_lt_iff` (`omega`), `rUnderFirst_addFree`;
**`P_addFree`** by `skein_induction_based` (init: `δ^{c}` vs `δ·δ^{c−1}`; step: `addFree_switch`,
`addFreeSmoothIso`, `RecordIso.addFree`, signs via `sgn_eq`, `P_recursion_pos/neg`, `ring`);
`P_split_circle` from `IsSplitCircleAddition` (`P_planar (of_reparam)`, `eraseFreeAddFreeIso`,
`restrictRecordIso`).

### §6 mp:stack — statements in the skeleton, own unit list (see §7 below)

---------------------------------------------------------------------------------------------------

## 2. Dependency order (as built)

§0 → §1 → §2 → §3 → §4 → §5 (all done) → §6 mp:stack units S1-S10 (§7).  For porting into
`work/lean`: one library module `SM/SkeinInduction.lean` (= §0-§2), then `SM/LpCore.lean` (§3 +
row), `SM/RecordPolynomial.lean` (§4 + row), `SM/Presentations.lean`, `SM/SplitCircle.lean` (§5 +
row); mp:stack later.

---------------------------------------------------------------------------------------------------

## 3. Reuse list (verified by reading; file:line in work/lean)

Interfaces: `SM/LinkInterfaces.lean` — `homfly` :131, `homfly_spec` :134, `lmF` :190, `lmF_planar`
:399, `lmF_sourceSkein` :403, `lmF_underFirst_init` :409, `lmF_crossingFree` :415, `lmF_unknot` :421,
`lmF_reidemeister_I/II/III` :425/429/433.
`SM/LocalPolynomial.lean` — `P` :23, `P_eq_one_of_lmF_eq_one` :27.
`SM/CoefficientTransport.lean` — `RCompetitor` :26, `RCompetitor.toRG_eq_phi_toTG_lmF` :131,
`coefficient_transport` :138.
Rings: `SM/LinkLaurentRing.lean` — `R.a_mul_aInv` :177, `R.aInv_mul_a` :178, `R.delta` :193,
`T.l_mul_lInv` :217, `T.lInv_mul_l` :218, `T.mu` :226, `coeffAt` :286, `InSupportM` :846, `.add` :852,
`.sub` :863, `.a_mul` :902, `.aInv_mul` :904, `.z_mul` :913, `.z_mul_of_pred` :943, `.delta_pow` :972,
`gaussI_mul_gaussI` :988, `R.toRG` :1016, `R.toRG_a/z/aInv/zInv` :1030-1033, `T.toTG_l/m/lInv/mInv`
:1044-1053, `reMap_toRG` :1098, `reMap_toRG_mul` :1126, `phi` :1288, `phi_l'` :1311, `phi_m'` :1321,
`phi_lInv` :1325, `phi_mInv` :1332, `specQ` :1477, `specQ_delta` :1496, `specQ_positive_identity`
:1502, `specQ_negative_identity` :1509.
Diagrams: `SM/LinkDiagram.lean` — `IsPositive` :547, `isPositive_iff_sign_eq_one` :559,
`componentCount_pos` :582, `switch` :650, `switch_isPositive_self` :699, `switch_switch` :710,
`restrict` :1082, `visitPt` :1435, `Basing` :1477, `cyclicOffset` :1487, `traversalKey_nonneg/lt_card`
:1512/1515, `basedRank` :1526, `UnderFirst` :1545, `exists_nonsingular_base` :1559.
Moves: `SM/LinkMoves.lean` — `PlanarIsotopic.of_reparam` :519, `IsOrientedSmoothing` :743,
`IsSkeinTriple` :751, `IsOrientedSmoothing.card_crossing` :1051, `IsSplitCircleAddition` :1088,
`IsOrientedSmoothing.switch` :1988.
Records: `SM/LinkRecord.lean` — `Record` :309, `FreeComp` :518, `RecordIso` :539, `.symm` :569,
`.trans` :588, `Φ_pow` :597, `componentCount_eq` :613, `Record.switch` :655, `switch_isOver_self`
:695, `switch_isOver_pair` :698, `switch_isOver_of_ne` :701, `RecordIso.switch` :778, `SmoothComps`
:880, `smooth` :895, `restrict` :1144, `restrict_succ_val_of_keep` :1176.
`SM/LinkRecordExtras.lean` — `RecordIso.smooth` :432.
Bridges: `SM/LinkDiagramRecord.lean` — `cycBetween` :78, `compOf` :164, `compList_length` :248,
`overBit_overVisit` :474, `record` :500, `record_componentCount` :537, `switchRecordIso` :686,
`VisitBetween` :882, `ent` :912, `exists_ent` :926, `visitSucc_pow_ent` :937, `ent_add_sub` :953,
`visitBetween_ent_iff` :960, `restrictRecordIso` :1454.
Gate: `SM/Smoothing.lean` — `exists_smoothing` :8170, `exists_smoothing_record_visit` :8185,
`exists_smoothing_counts` :8202.  `SM/SingleCrossing.lean` — `exists_basing_first` :84.
Mathlib (pinned): `Equiv.Perm.SameCycle.exists_pow_eq'`, `Nat.find_congr'`, `Equiv.optionSubtypeNe`
(+`_symm_of_ne`), `Prod.Lex.toLex_lt_toLex`, `Finset.orderIsoOfFin`, `Equiv.optionEquivSumPUnit`,
`Equiv.sumAssoc`, `Fin.prod_univ_two`, `Fintype.card_option`, `AddMonoidAlgebra.smul_single`,
`AddMonoidAlgebra.single_neg`.

---------------------------------------------------------------------------------------------------

## 4. Lines

Written and compiling: ≈ 1,100 lines of proof for the four rows (Skeleton_B.lean is 1,218 lines
including docstrings and the mp:stack statements).  Remaining: mp:stack ≈ 680 lines (§7).
**Total ≈ 1,800.**

---------------------------------------------------------------------------------------------------

## 5. Residual risks

1. **Porting into `work/lean`.**  The skeleton was checked with `lake env lean` against the current
   oleans; when ported as modules nothing should change, but the classical-instance `badCount`
   (`open scoped Classical in`) and the `rfl` casts (`rbasingSwitch`, `key_switch`,
   `addFree_switch`, `pos_addFree`) are the spots to re-check if a Mathlib bump changes
   reducibility.
2. **Statement review** of the four rows is already on file in `work/drafts/*_statement.lean`; the
   new library definitions (`RBasing`, `addFree`, …) are helpers, not row statements, but the
   accepted-declaration policy binds helper definitions to the rows' hashes — keep them in a
   separate library module.
3. **mp:stack** — §7; the restriction/smoothing commutation (S5/S6) is the only heavy item of the
   block.

---------------------------------------------------------------------------------------------------

## 6. Fidelity notes for the reviewer

* All five bundles are copied verbatim; nothing is weakened.  `record_polynomial.subst_eq` is proved
  by rewriting the `lmF` equality under any ring hom; `coeff_eq` by rewriting `P`.
* lp:core's `gaussian`/`eq_homfly`/`skein` are obtained through the accepted lp:coefficient-transport
  instead of by the printed induction (D4); the induction still proves `support`, `ne_zero`,
  `unique` exactly as printed (`M_c` closure lemmas, `specQ` identities, same solved recurrences).
* The "first bad crossing" of the printed proofs is replaced by "any bad crossing" (D3); the printed
  re-choice of bases after every smoothing is the `∀ B₀` in `step`.
* The record-level based order is the printed "order on the components and one basepoint on each
  component", with the basepoint replaced by the first occurrence after it (an equivalent datum for
  every purpose of the proof); `exists_underFirst_of_rUnderFirst` realises the printed "choose its new
  basepoint in the interval just preceding the image of the old first crossing occurrence".
* lp:split-circle is proved for the relational `IsSplitCircleAddition` through the record-level
  `addFree` (the added circle is a `FreeComp` of the smoothing, sm-3:1198-1200 "Switching or smoothing
  does not touch the extra component").

---------------------------------------------------------------------------------------------------

## 7. mp:stack — own unit list (honest estimates)

The printed proof needs "the restriction of the smoothed diagram in that block is exactly the
oriented smoothing of the old block restriction; the other restrictions do not change".  There is no
way around this commutation; it is stated at the record level in the skeleton so that only
`restrictRecordIso` (accepted) and lc:presentations (now proved) connect it to diagrams.

| unit | statement (skeleton name) | sketch | est. |
|---|---|---|---|
| S1 | `exists_blockCompatible_rbasing β : ∃ B, B.BlockCompatible β` | rank `c ↦ (β c).val * card comps + equivFin c`; injective; block-monotone (`Nat.succ_mul`, `Nat.mul_le_mul_right`). | 25 |
| S2 | `RBasing.isBad_internal : RBlockOrdered β → BlockCompatible → IsBad v → β (comp v) = β (comp (pair v))` | trichotomy on blocks: `<` contradicts `isOver v`; `>` contradicts `key v < key (pair v)`. | 12 |
| S3 | `smoothBlock β x hx : (ρ.smooth x).comps → Fin q` | `Sum.elim (Quotient.lift (β ∘ comp) _) (β ∘ Subtype.val)`; well-defined because `reconnect = succ * swap x (pair x)` keeps blocks (`sameCycle` induction along `mul_swap`). | 35 |
| S4 | `rBlockOrdered_smooth` | bits unchanged (`smooth_isOver`), blocks of retained occurrences unchanged (`Quotient.lift` computes). | 20 |
| S5 | `restrictSmoothIsoInternal` (block of `x`) | `M`: `{w // SmoothKeep x w ∧ RestrictKeep S₀ w} ≃ {w // RestrictKeep S w ∧ SmoothKeep x' w}`; `succ`: first return of `reconnect` to the retained set on nested subtypes (new lemma `firstReturn_subtype`, ~40); `comps`: `{c : Quotient ⊕ Free // block c = i} ≃ Quotient(reconnect') ⊕ Free(restrict)` — cycles of `reconnect` in block `i` with a retained occurrence ↔ cycles of `reconnect'`; cycles without retained occurrence and free comps of block `i` ↔ `FreeComp (ρ.restrict S)`. | 200 |
| S6 | `restrictSmoothIsoExternal` (other blocks) | retained occurrences of block `j ≠ block x` are never `x, pair x`; `smooth_succ_val_of_comp_ne`; cycles of `reconnect` on block `j` are `succ`-cycles. | 120 |
| S7 | `RBasing.restrict B S : RBasing (ρ.restrict S)` | rank restricted; base: first retained occurrence at/after the old base (`Nat.find` on `RestrictKeep (succ^k (base v))`). | 40 |
| S8 | `rUnderFirst_restrict` | `pos'` is monotone in `pos` on retained occurrences (`pos' u = card {w retained ∣ pos w < pos u}`, a first-return enumeration lemma). | 80 |
| S9 | `stack_formula` assembly | `skein_induction_based`, `Φ D B := ∀ q blk hblk, BlockOrdered D blk → B.BlockCompatible blk → P D = δ^{q−1} ∏ P (blockRestrict …)`. init: `P_underFirst_init`; `P (blockRestrict …) = δ^{c_i−1}` via `restrictRecordIso`, `rUnderFirst_restrict`, `rUnderFirst_map`, the bridge; `Σ c_i = c`. step at bad (hence internal, S2) `v`: switched via `restrict_switch` / `switch_restrict_of_external`; smoothed via `exists_smoothing_record_visit`, `blk₀ := smoothBlock ∘ ι₀.e`, S4, S5/S6 + `restrictRecordIso` + `presentations`; `P_recursion_pos/neg` on `D` and on the block restriction (`restrict_sign`), factor `∏_{i ≠ i₀}`, `ring`. | 120 |
| S10 | glue: `BlockOrdered D blk ↔ RBlockOrdered D.record blk`, fibre cardinalities, `blockRestrict` unfolding | — | 40 |

Total mp:stack ≈ 680 lines; critical path S5 → S9.  Recommendation: port the four finished rows
first; start mp:stack with S1-S4, S7-S8, S10 (independent of S5/S6) and the assembly S9 against
`sorry`'d S5/S6, then S6, then S5.
