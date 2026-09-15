# PLAN_FINAL — the polynomial block (rp:record-polynomial, lp:core, lp:split-circle, lc:presentations, mp:stack)

Judge's synthesis, 2026-09-14.  Skeleton of record: **`work/drafts/polyblock/Skeleton_FINAL.lean`**
(1,533 lines, 130 declarations; `cd work/lean && lake env lean ../drafts/polyblock/Skeleton_FINAL.lean`
exits 0 with exactly 13 `declaration uses 'sorry'` warnings, all in the mp:stack chain §6).
Inputs judged: `PLAN_A.md` / `Skeleton_A.lean` (tag A, diagram-level `(N, b)` induction) and
`PLAN_B.md` / `Skeleton_B.lean` (tag B, record-level based order).  Both compile; both claimed
axiom footprints were re-verified with `#print axioms` on this pod.

## 0. Verdict

**Winner: B**, with three grafts from A (§2).  Scores (1-10):

| criterion | A | B | why |
|---|---|---|---|
| (a) mathematical correctness against the fixed statements | 8 | 9 | Both `(N, b)` principles are kernel-checked with standard axioms only (`skein_induction`, `skein_induction_based`); both handle the negative crossing by the triple `(D^sw, D, D⁰)` through `switch_isPositive_self`, `switch_switch`, `IsOrientedSmoothing.switch` (kernel-checked in both).  A's record/diagram bridge for rp:record-polynomial (`underFirst_of_recordIso`) is a plausible 8-leaf plan (dependent `Option`-indexed basings, an unproved 8-way real case split); B's bridge `exists_underFirst_of_rUnderFirst` is PROVED and rp:record-polynomial is sorry-free.  B's only blemish: the mp:stack commutations were stated in terms of a `sorry`'d *definition* (`smoothBlock`), which couples the provers and is a policy smell; fixed here by graft G2. |
| (b) provability in Lean with the existing library | 6 | 8 | A: 29 leaves, ≈1,900 lines left (U3 transport 425, split-circle 460, stack 1,015); its `restrictSmoothFreeIso` for split-circle is the same kind of dependent-subtype iso as the stack ones.  B: 7 leaves, all mp:stack, ≈640-1,000 lines; lp:split-circle is closed by `Record.addFree` (all clauses `rfl`) instead of a restriction iso.  The heavy item is identical in both (restriction ∘ smoothing commutation, ≈320 lines + two perm lemmas). |
| (c) minimality | 6 | 8 | A duplicates the ring layer (`solvedT`/`solvedR`/`solvedRG`) and needs a second scaffold `stack_value`; its UNDER-first transport is a 425-line one-off.  B pays ≈200 lines for `RBasing` once and reuses it for rp, split-circle and stack (transport is `RBasing.map`, 30 lines).  B routes `gaussian` through lp:coefficient-transport (a shortcut the printed proof does not take) — replaced by graft G1. |

Verified status of the row theorems in `Skeleton_FINAL.lean` (`#print axioms`):

| row | theorem | axioms |
|---|---|---|
| lp:core | `SM.lp_core` | `propext, Classical.choice, Quot.sound, SM.lit_homfly, SM.lp_lm, SM.lp_lm_uniqueness` — **no sorryAx** |
| rp:record-polynomial | `SM.record_polynomial` | `propext, Classical.choice, Quot.sound, SM.lp_lm` — **no sorryAx** |
| lc:presentations | `SM.presentations` | `propext, Classical.choice, Quot.sound, SM.lp_lm` — **no sorryAx** |
| lp:split-circle | `SM.split_circle` | `propext, Classical.choice, Quot.sound, SM.lp_lm` — **no sorryAx** |
| mp:stack | `SM.stack` | `propext, sorryAx, Classical.choice, Quot.sound, SM.lp_lm` (13 leaves of §6; `stack_formula` and `stack` are proved from them) |
| (lp:core field) | `SM.P_gaussian` | `propext, Classical.choice, Quot.sound, SM.lp_lm` (graft G1: printed integral descent, no `lp_lm_uniqueness`) |

## 1. The route (B) in one page

* **Measure** = `(N, b)`, `N = Fintype.card D.Γ.Crossing`, `b = B.badCount` for a **record-level based
  order** `B : Record.RBasing D.record` (injective rank `comps → ℕ`, a base occurrence per circle;
  `key v = toLex (rank (comp v), pos v)` with `pos` the succ-distance from the base; `IsBad v :=
  isOver v ∧ key v < key (pair v)`; `RUnderFirst := ∀ v, isOver v → key (pair v) < key v`).
* **Switch** keeps the based order (`rbasingSwitch`, fields unchanged) and lowers `b` by one at ANY bad
  occurrence (`badCount_switch`, via `switchRecordIso` which is the identity on occurrences); the printed
  "first bad crossing" is inessential.  **Smoothing** lowers `N` (`IsOrientedSmoothing.card_crossing`);
  the step quantifies over every smoothing and every based order of it.
* **Principle** (PROVED, standard axioms): `skein_induction_based Φ init step : ∀ D B, Φ D B` with
  `init : ∀ D B, B.RUnderFirst → Φ D B` and
  `step : ∀ D B v, B.IsBad v → Φ (D.switch v.1) (D.rbasingSwitch v.1 B) → (∀ D₀ B₀, IsOrientedSmoothing D v.1 D₀ → Φ D₀ B₀) → Φ D B`;
  plain form `skein_induction Φ init step` with `init` handed a `Diagram.Basing` with `Diagram.UnderFirst`.
* **The one geometric bridge** (PROVED): `exists_underFirst_of_rUnderFirst : B.RUnderFirst → ∃ B' : D.Basing, D.UnderFirst B'`
  (rank sorted by `exists_rank_equiv`; basepoint just before the base occurrence by the accepted
  `exists_basing_first`; offsets vs succ-iterates by `visitBetween_ent_iff` + `cyclicOffset_lt_of_cycBetween`).
  This is the printed "choose its new basepoint in the interval just preceding the image of the old first
  crossing occurrence" (sm-3:1232-1234) and it is what makes rp:record-polynomial's `b = 0` case work
  for the partner: `RBasing.map ι` + `rUnderFirst_map`.
* **rp:record-polynomial**: `Φ D B := ∀ D', Nonempty (RecordIso D.record D'.record) → lmF D = lmF D'`
  (partner inside the predicate; no synchronised bad count).  Step: `recordIso_switch`
  (`switchRecordIso ≫ ι.switch ≫ switchRecordIso⁻¹`), `exists_smoothing_pair` (gate on both sides around
  `ι.smooth`), equal signs (`ι.sgn_eq`), cancellation `T.eq_of_skein_l` / `T.eq_of_skein_lInv` in the common
  sign case — exactly rp:positive-skein / rp:negative-skein (sm-3:1274-1287).
* **lc:presentations** = `P_congr (lmF_eq_of_recordIso …)`.
* **lp:core**: `G := φ ∘ T.toTG ∘ lmF`, `G_skein` (lp:gaussian-skein × (−i)), **`G_descent`** by
  `skein_induction` (integral descent + support, eqs. lp:self-support / lp:mixed-support via
  `exists_smoothing_counts`), `P_gaussian` and `P_support` from it, `P_skein` from `G_skein` by the additive
  `R`-linear `reMap`, `P_underFirst_init` via `phi_toTG_mu : φ(μ) = δ`, `P_specQ`/`P_ne_zero` and `P_unique`
  by `skein_induction`, `P_eq_homfly` by the accepted lp:coefficient-transport (as printed, sm-3:1163-1171).
* **lp:split-circle**: `Record.addFree` (comps `Option comps`, everything else unchanged);
  `addFree_switch` is `rfl`, `addFreeSmoothIso` has all clauses `rfl`; `P_addFree` by `skein_induction_based`
  with `Φ D B := ∀ D', Nonempty (RecordIso D'.record D.record.addFree) → P D' = δ P D`; the relational
  `IsSplitCircleAddition D D'` is reduced to it by `eraseFreeAddFreeIso` + `restrictRecordIso` + `P_planar`.
* **mp:stack**: §6 below.

## 2. Grafts from A (what changed relative to `Skeleton_B.lean`)

* **G1 — printed integral descent for `gaussian`/`support`** (Skeleton_A §5).  B obtained `gaussian`
  from `RCompetitor.toRG_eq_phi_toTG_lmF` (which consumes `lp_lm_uniqueness`).  FINAL proves
  `G_recursion_pos/neg` (lp:positive / lp:negative in `R_G`), `G_underFirst`, `G_descent : ∀ D, ∃ p : R,
  InSupportM c(D) p ∧ R.toRG p = G D` by `skein_induction`, then `P_gaussian` and `P_support` in three
  lines each.  Net: −25 lines of B, +55 lines; `P_gaussian` now has axioms `{propext, Classical.choice,
  Quot.sound, lp_lm}`; B's fidelity note D4 is void (only `eq_homfly` uses coefficient transport, as
  printed).  Also added A's `solvedR`, `solvedR_mul_left`, `solvedR_of_skein` (the two recursions under a
  classical `if`; used by the stack step).
* **G2 — decoupled mp:stack commutations** (Skeleton_A §11.3).  B's `restrictSmoothIsoInternal/External`
  were stated through the `sorry`'d def `smoothBlock`, so they could not be proved before it.  FINAL states
  `restrictSmoothIso` / `restrictSmoothDisjointIso` with the target block `B' : Finset (ρ.smooth v).comps`
  characterised by two hypotheses (`hB' : inl ⟦u⟧ ∈ B' ↔ comp u ∈ B`, `hB'' : inr f ∈ B' ↔ f.1 ∈ B`), adds
  A's two permutation lemmas `firstReturn_firstReturn`, `firstReturn_mul_swap`, and makes the block function
  of the smoothing a **transparent** `Quotient.lift` (`Record.smoothBlock`, computation rules `rfl`) whose
  only content is `beta_comp_eq_of_reconnect_sameCycle`.  B's `rBlockOrdered_smooth`, `RBasing.restrict`,
  `rUnderFirst_restrict` are dropped.
* **G3 — diagram-level `restrict_underFirst`** (Skeleton_A §10) for the stack initialization instead of
  B's record-level `RBasing.restrict` + `rUnderFirst_restrict` (which needed a first-return enumeration
  lemma).  At the diagram level the basepoints and traversal coordinates of the restriction are literally
  the old ones (`restrict_visitPt_snd`), so no enumeration is needed.

Kept from B verbatim: §0-§5 (all proved), `exists_blockCompatible_rbasing`, `RBasing.isBad_internal`,
`RBlockOrdered`, `BlockCompatible`, the row bundles.  From A's stack lane: the diagram-level block
lemmas, `blocks_of_smoothing` (A's `exists_blocks_of_smoothing`, restated on `smoothBlock ∘ ι₀.e`),
`stack_init`, `stack_step` (restated at an occurrence `v` with `ι₀ : D₀.record ≅ D.record.smooth v`).
The assembly `stack_formula` is PROVED in FINAL from `skein_induction_based` + `stack_init` + `stack_step`
(replacing A's second scaffold `stack_value`).

## 3. Reuse (verified by reading; file:line in work/lean)

Interfaces `SM/LinkInterfaces.lean`: `homfly` :131, `homfly_spec` :134, `lmF` :190, `lmF_planar` :399,
`lmF_sourceSkein` :403, `lmF_underFirst_init` :409, `lmF_crossingFree` :415, `lmF_unknot` :421,
`lmF_reidemeister_I/II/III` :425/429/433.  `SM/LocalPolynomial.lean`: `P` :23 (`reMap (phi (T.toTG (lmF D)))`),
`P_eq_one_of_lmF_eq_one` :27.  `SM/CoefficientTransport.lean`: `RCompetitor` :26, `coefficient_transport` :138.
Rings `SM/LinkLaurentRing.lean`: `R.a_mul_aInv` :177, `R.aInv_mul_a` :178, `R.delta` :193, `T.l_mul_lInv` :217,
`T.lInv_mul_l` :218, `T.mu` :226, `RG.a_mul_aInv` :251, `InSupportM` :846 (+ `.add` :852, `.sub` :863,
`.a_mul` :902, `.aInv_mul` :904, `.z_mul` :913, `.z_mul_of_pred` :943, `.delta_pow` :972), `gaussI_mul_gaussI` :988,
`R.toRG` :1016, `R.toRG_injective` :1020, `R.toRG_a/z/aInv` :1030-1032, `T.toTG_*` :1044-1053, `reMap_toRG` :1098,
`reMap_toRG_mul` :1126, `phi_l'` :1311, `phi_m'` :1321, `phi_lInv` :1325, `phi_mInv` :1332, `specQ_delta` :1496,
`specQ_positive/negative_identity` :1502/1509.
Diagrams `SM/LinkDiagram.lean`: `underStrand` :505, `mem_iff` :519, `eq_under_of_mem_of_ne` :523, `IsPositive` :547,
`isPositive_iff_sign_eq_one` :559, `componentCount_pos` :582, `overVisit`/`underVisit` :597/600, `switch` :650,
`switch_isPositive_self` :699, `switch_switch` :710, `mapCrossing` :815, `crossingPoint_mapCrossing` :846,
`restrictShadow` :974 (`comp j := Γ.comp (B.orderEmbOfFin rfl j)`), `restrictMap` :980,
`restrict_mapCrossing_range_iff` :1037, `Diagram.restrict` :1082, `restrict_componentCount` :1085, `restrict_sign` :1088,
`Basing` :1477, `cyclicOffset` :1487, `traversalKey_nonneg/lt_card` :1512/1515, `basedRank` :1526, `UnderFirst` :1545,
`exists_nonsingular_base` :1559, `exists_basing` :1570.
`SM/LinkDiagramExtras.lean`: `toFun_restrict_overStrand/underStrand` :71/78, `mapVisit` :525,
`restrict_isPositive_iff` :585, `switch_restrict_of_internal` :735, `restrict_switch` :740,
`switch_restrict_of_external` :746, `restrict_visitPt_fst/snd` :832/837.
Moves `SM/LinkMoves.lean`: `PlanarIsotopic.of_reparam` :519, `IsOrientedSmoothing` :743, `IsSkeinTriple` :751,
`IsOrientedSmoothing.card_crossing` :1051, `IsSplitCircleAddition` :1088, `IsOrientedSmoothing.switch` :1988.
Records `SM/LinkRecord.lean`: `returnTime` :59 (+ `_pos/_spec/_min/_eq_iff` :62-70), `firstReturn` :100,
`firstReturn_apply` :103, `firstReturn_apply_of_mem` :106, `firstReturn_pow_of_pow` :162,
`firstReturn_sameCycle_iff` :188, `mul_swap_apply_of_ne_of_ne` :202, `Record` :309, `comp_pow` :365, `FreeComp` :518,
`RecordIso` :539 (+ `.symm` :569, `.trans` :588, `Φ_pow` :597, `componentCount_eq` :613), `switch` :655,
`switch_isOver_self/pair/of_ne` :695-701, `reconnect` :822 (`succ * swap x (pair x)`), `reconnect_apply_of_ne` :824,
`SmoothKeep` :849, `smoothKeep_iff` :855, `SmoothComps` :880 (quotient over ALL of `M`, incl. `x, pair x`),
`smooth` :895, `smooth_comp` :918, `smooth_isOver` :920, `smooth_pair_val` :922, `smooth_succ_val` :925,
`smooth_succ_val_of_comp_ne` :1104, `RestrictKeep` :1130, `restrict` :1144, `restrict_comp_val` :1167,
`restrict_pair_val` :1172, `restrict_succ_val_of_keep` :1176, `componentCount_restrict` :1183.
`SM/LinkRecordExtras.lean`: `componentCount_smooth` :333, `map_pow_apply` :358, `sameCycle_map_iff` :370,
`returnTime_map` :383, `firstReturn_map_val` :394, `RecordIso.reconnect_eq` :406, `RecordIso.smooth` :432,
`RecordIso.restrictKeep_iff` :448, `RecordIso.restrict` :456.
Bridges `SM/LinkDiagramRecord.lean`: `compOf` :164, `compOf_overVisit/underVisit` :171/174, `twin` :413,
`twin_overVisit/underVisit` :454/456, `overBit` :470, `overBit_eq_true_iff` :472, `record` :500 (abbrev),
`record_comp/pair_apply/isOver/sgn` :520-528, `record_isOver_iff` :529, `record_componentCount` :537,
`switchRecordIso` :686, `restrictVisit` :1222, `restrictVisit_fst` :1226, `compOf_restrictVisit` :1231,
`twin_restrictVisit` :1252, `restrictKeep_restrictVisit` :1260, `exists_restrictVisit` :1268,
`restrictVisitEquiv` :1285, `restrictVisitEquiv_apply_val` :1293, `restrictRecordIso` :1454.
Gate `SM/Smoothing.lean`: `exists_smoothing` :8170, `exists_smoothing_record` :8178,
`exists_smoothing_record_visit` :8185, `exists_smoothing_counts` :8202.  `SM/SingleCrossing.lean`:
`exists_basing_first` :84.
Mathlib (pinned): `Finset.mul_prod_erase`, `Finset.prod_pow_eq_pow_sum`, `Finset.card_eq_sum_card_fiberwise`,
`Finset.orderIsoOfFin`, `Finset.orderEmbOfFin_mem`, `Equiv.Perm.SameCycle.exists_nat_pow_eq`,
`Quotient.lift`/`Quotient.ind`, `Prod.lex_def`, `Prod.Lex.toLex_lt_toLex`, `Fin.prod_univ_two`.

## 4. The proved layer (nothing to do but port)

§0 algebra (`T.eq_of_skein_l/lInv`, `skeinTriple_of_smoothing`, `skein_recursion_pos/neg`, `solvedR`,
`solvedR_mul_left`, `solvedR_of_skein`); §1 `Record.RBasing` (+ `pos`, `key`, `key_injective`, `IsBad`,
`RUnderFirst`, `badCount`, `badCount_eq_zero_iff`, `exists_isBad_of_badCount_ne_zero`, `switch`, `key_switch`,
`badCount_switch`, `map`, `key_map`, `isBad_map`, `badCount_map`, `rUnderFirst_map`, `default`); §2
(`cyclicOffset_lt_of_cycBetween`, `rbasingSwitch`, `badCount_rbasingSwitch`, `exists_rank_equiv`,
`exists_base_before`, `exists_base_before'`, `visitBetween_of_pos_lt`, `exists_underFirst_of_rUnderFirst`,
`skein_induction_based`, `skein_induction`); §3 lp:core (`P_congr`, `P_planar`, `P_reidemeister_*`, `P_circle`,
`G`, `gaussI_alg_sq`, `phi_lInv'`, `phi_mInv'`, `G_skein`, `P_skein`, `P_rcompetitor`, `homfly_rcompetitor`,
`P_eq_homfly`, `phi_toTG_mu`, `P_of_lmF_eq_mu_pow`, `P_underFirst_init`, `P_crossingFree`, `P_recursion_pos/neg`,
`G_recursion_pos/neg`, `G_underFirst`, `G_descent`, `P_eq_reMap_G`, `P_gaussian`, `P_support`, `P_specQ`,
`P_ne_zero`, `P_unique`, `P_knot_support`, `lp_core`); §4 (`sign_eq_of_recordIso`, `isPositive_iff_of_recordIso`,
`recordIso_switch`, `exists_smoothing_pair`, `exists_underFirst_of_recordIso`, `componentCount_eq_of_recordIso`,
`lmF_eq_of_recordIso`, `record_polynomial`, `presentations`); §5 (`Record.addFree` + lemmas, `freeCompAddFreeEquiv`,
`addFreeSmoothIso`, `RecordIso.addFree`, `eraseFreeAddFreeIso`, `RBasing.addFree`, `pos_addFree`,
`key_addFree_lt_iff`, `rUnderFirst_addFree`, `P_addFree`, `P_split_circle`, `split_circle`).

Port plan (library helpers in modules separate from the row statements, per the accepted-declaration hash
policy): `SM/SkeinInduction.lean` (§0-§2), `SM/LpCore.lean` (§3 + `LpCoreData`, `lp_core`),
`SM/RecordPolynomial.lean` (§4 + bundle), `SM/Presentations.lean`, `SM/SplitCircle.lean` (§5 + bundle),
`SM/StackBlocks.lean` (§6 chain), `SM/Stack.lean` (bundle).  Re-check after porting: the classical instance
of `badCount` (`open scoped Classical in` / `classical`), and the `rfl` casts `rbasingSwitch`, `key_switch`,
`addFree_switch`, `pos_addFree`, `(rbasingSwitch B).map switchRecordIso = B.switch v`, `P_eq_reMap_G`.

## 5. Order of rows (which rows close first)

1. **lp:core** — port §0-§3, `lp_core`; statement review already on file (`LpCore_statement.lean`).
   Closes first: it consumes nothing outside the accepted library and the three interfaces.
2. **rp:record-polynomial** — §4 (`lmF_eq_of_recordIso`) on top of 1.
3. **lc:presentations** — one line from 2 (`P_congr`).
4. **lp:split-circle** — §5 on top of 1-2 (uses `P_recursion_pos/neg`, `skein_induction_based`, the bridge).
5. **mp:stack** — §6, the only open chain; units U1-U5 below (U1/U3/U4 in parallel, then U2, then U5).

## 6. mp:stack — ordered lemma list with exact statements (the 13 `sorry` leaves of `Skeleton_FINAL.lean`)

Notation: `blockSet D blk i := univ.filter (blk · = i)`, `blockRestrict D blk hblk i = D.restrict (blockSet D blk i) _` (`rfl`),
`mem_blockSet_iff`.  Statements are copied from the skeleton; the estimates are for the proof bodies.

### 6.1 Permutation layer (unit U1, ≈160 lines; `namespace SM.Link`)

```lean
theorem firstReturn_firstReturn {α : Type*} [Fintype α] (f : Equiv.Perm α) (p q : α → Prop)
    [DecidablePred p] [DecidablePred q] (m : {m : {m // p m} // q m.1}) :
    ((firstReturn (firstReturn f p) (fun m => q m.1)) m).1.1 =
      ((firstReturn f (fun m => p m ∧ q m)) ⟨m.1.1, m.1.2, m.2⟩).1
```
Both sides are `(f ^ n) m` for the least `n > 0` with `p ∧ q` at `f^n m`.  LHS: `(firstReturn f p)^k m = f^(T k) m`
with `T` the sum of the first `k` return times (`firstReturn_apply`, induction; `firstReturn_pow_of_pow` for the
converse), every `p`-point of the orbit is hit, so the first `q`-return along `firstReturn f p` is the first
`p ∧ q`-point along `f`.  Conclude with `returnTime_eq_iff` on both sides (≈70).
```lean
theorem firstReturn_mul_swap {α : Type*} [Fintype α] [DecidableEq α] (f : Equiv.Perm α)
    (p : α → Prop) [DecidablePred p] (a b : α) (ha : p a) (hb : p b) :
    firstReturn (f * Equiv.swap a b) p =
      firstReturn f p * Equiv.swap (⟨a, ha⟩ : {m // p m}) ⟨b, hb⟩
```
`ext u; Subtype.ext`.  `u ∉ {a, b}`: `(f * swap a b)^n u = f^n u` as long as no intermediate iterate is a
`p`-point (`a, b` are `p`-points; `mul_swap_apply_of_ne_of_ne`), so the return times agree
(`returnTime_eq_iff`).  `u = a`: `(f * swap a b) a = f b` and then as before from `f b`, which is
`firstReturn f p ⟨b⟩`; `u = b` symmetric (≈90).
Helper worth stating (≈15): `firstReturn_congr_pred (h : ∀ m, p m ↔ p' m) (m) : (firstReturn f p m).1 =
(firstReturn f p' ⟨m.1, (h _).mp m.2⟩).1` (via `returnTime_eq_iff`) — the two record isos need to rewrite
`RestrictKeep B' w ↔ RestrictKeep B w.1` and `SmoothKeep ⟨v⟩ w ↔ SmoothKeep v w.1` under a `firstReturn`.

### 6.2 Record layer (unit U2, ≈360 lines; `namespace SM.Link.Record`, `variable (ρ : Record)`)

```lean
theorem beta_comp_eq_of_reconnect_sameCycle {γ : Sort*} (β : ρ.comps → γ) (v : ρ.M)
    (hv : β (ρ.comp v) = β (ρ.comp (ρ.pair v))) {u w : ρ.M}
    (h : (ρ.reconnect v).SameCycle u w) : β (ρ.comp u) = β (ρ.comp w)
```
One step: `reconnect v u = succ (swap v (pair v) u)`; `u = v ↦ comp (succ (pair v)) = comp (pair v)`
(`succ_comp`) and `hv`; `u = pair v` symmetric (`pair_invol`); otherwise `comp (succ u) = comp u`.  Then
`h.exists_nat_pow_eq` and induction on `n` (≈40).  This is the whole content of `smoothBlock` (a
`Quotient.lift`; `smoothBlock_inl`/`_inr` are `rfl`).
```lean
open scoped Classical in
theorem restrictSmoothIso (v : ρ.M) (B : Finset ρ.comps) (hv : ρ.RestrictKeep B v)
    (B' : Finset (ρ.smooth v).comps)
    (hB' : ∀ u : ρ.M, (Sum.inl (Quotient.mk _ u) : ρ.SmoothComps v) ∈ B' ↔ ρ.comp u ∈ B)
    (hB'' : ∀ f : ρ.FreeComp, (Sum.inr f : ρ.SmoothComps v) ∈ B' ↔ f.1 ∈ B) :
    Nonempty (RecordIso ((ρ.smooth v).restrict B')
      ((ρ.restrict B).smooth (⟨v, hv⟩ : {u : ρ.M // ρ.RestrictKeep B u})))
```
`Φ`: both `M`s are `{u // SmoothKeep v u ∧ RestrictKeep B u}` up to `Subtype` repackaging
(`(smooth v).comp w = inl ⟦w.1⟧` (`smooth_comp`), `smooth_pair_val`, `hB'`, `smoothKeep_iff`, `Subtype.ext_iff`).
`succ_eq`: LHS = `firstReturn (firstReturn (reconnect v) (SmoothKeep v)) (RestrictKeep B' ∘ val)`
= `firstReturn (reconnect v) (SmoothKeep v ∧ RestrictKeep B)` (`firstReturn_congr_pred`, `firstReturn_firstReturn`);
RHS = `firstReturn ((restrict B).reconnect ⟨v⟩) (SmoothKeep ⟨v⟩)` with
`(restrict B).reconnect ⟨v⟩ = firstReturn succ (RestrictKeep B) * swap ⟨v⟩ ⟨pair v⟩`
(`restrict_pair_val` is `rfl`) `= firstReturn (succ * swap v (pair v)) (RestrictKeep B)` (`firstReturn_mul_swap`,
both points kept by `hv`, `restrictKeep_pair_iff`) `= firstReturn (reconnect v) (RestrictKeep B)`; so RHS =
`firstReturn (reconnect v) (RestrictKeep B ∧ SmoothKeep v)` (`firstReturn_firstReturn`, `and_comm`).
`e` — **careful, this is where A's sketch was too naive**: LHS comps are `{s : SmoothComps v // s ∈ B'}`, i.e.
(a) `inl ⟦u⟧` for the `s₁`-cycles carrying an occurrence `u` with `comp u ∈ B` — `u` need NOT be
internal (its pair may lie outside `B`), and `u` may be `v` or `pair v` — and (b) `inr f` for free circles of
`ρ` in `B`.  RHS comps are `Quotient (SameCycle ((restrict B).reconnect ⟨v⟩)) ⊕ FreeComp (restrict B)`.
Map (a): if the `s₁`-cycle of `u` contains a `RestrictKeep B` occurrence `u'` (e.g. `v` itself), send it to
`inl ⟦⟨u', _⟩⟧` — well defined because two kept occurrences on one `s₁`-cycle lie on one cycle of
`firstReturn (reconnect v) (RestrictKeep B) = (restrict B).reconnect ⟨v⟩` (`firstReturn_sameCycle_iff`);
otherwise the cycle avoids `v, pair v`, so `s₁ = s` on it and it is the single circle `comp u ∈ B` with no
internal occurrence (`succ_cycle`): send it to `inr ⟨⟨comp u, _⟩, free-in-restrict⟩`.  Map (b):
`inr f ↦ inr ⟨⟨f.1, _⟩, _⟩`.  Inverse: `inl ⟦w⟧ ↦ inl ⟦w.1⟧`; `inr ⟨c, hfree⟩ ↦` if some `u` has `comp u = c`
then `inl ⟦u⟧` (case (a), no internal occurrence) else `inr ⟨c, _⟩`.  Bijectivity by the two case analyses
(`Quotient.ind`, `Classical.choice` for the witnesses).  `comp_eq` for `w` kept: the chosen `u'` for the cycle of
`w.1.1` may be replaced by `w.1.1` itself (well-definedness).  `pair_eq`, `bit_eq`, `sgn_eq`: `rfl`/`Subtype.ext`
(≈200-250; the largest single lemma; **risk: high**).  B's PLAN_B §7 S5 sketch of `comps` is the correct one.
```lean
open scoped Classical in
theorem restrictSmoothDisjointIso (v : ρ.M) (B : Finset ρ.comps) (hv : ρ.comp v ∉ B)
    (hv' : ρ.comp (ρ.pair v) ∉ B) (B' : Finset (ρ.smooth v).comps)
    (hB' : ∀ u : ρ.M, (Sum.inl (Quotient.mk _ u) : ρ.SmoothComps v) ∈ B' ↔ ρ.comp u ∈ B)
    (hB'' : ∀ f : ρ.FreeComp, (Sum.inr f : ρ.SmoothComps v) ∈ B' ↔ f.1 ∈ B) :
    Nonempty (RecordIso ((ρ.smooth v).restrict B') (ρ.restrict B))
```
`Φ`: `{w : {u // SmoothKeep v u} // RestrictKeep B' w} ≃ {u // RestrictKeep B u}` (a kept `u` is `≠ v, pair v`
since `comp v, comp (pair v) ∉ B`).  `succ_eq`: LHS = `firstReturn (reconnect v) (SmoothKeep v ∧ RestrictKeep B)`
(`firstReturn_firstReturn`) = `firstReturn (reconnect v) (RestrictKeep B)` (the first conjunct is implied) =
`firstReturn succ (RestrictKeep B)`: `(reconnect v)^n u = succ^n u` for `comp u ∈ B` (every iterate keeps
`comp` (`comp_pow`), and `swap v (pair v)` fixes points whose `comp ∉ {comp v, comp (pair v)}`), hence equal
return times (`returnTime_eq_iff`).  `e`: `inl ⟦u⟧ ↦ ⟨comp u, _⟩` (well defined: on `B`-circles
`SameCycle (reconnect v) u w → comp u = comp w`), `inr f ↦ ⟨f.1, _⟩`; injective (`inl` vs `inr` by freeness,
`inl` vs `inl` by `succ_cycle`); surjective (a `B`-circle carries an occurrence or is free) (≈120;
**risk: medium-high**).

### 6.3 Diagram-level block bookkeeping (unit U4, ≈190 lines)

```lean
theorem Link.Diagram.rBlockOrdered_of_blockOrdered (D : Diagram) {q : ℕ} {blk : Fin D.Γ.c → Fin q}
    (hord : BlockOrdered D blk) : D.record.RBlockOrdered blk
```
For `v = ⟨x, s⟩`: `record.comp v = s.1` (`record_comp`, `compOf` is `v.2.val.1`), `record.pair v = twin v`
carries `other x s` (`record_pair_apply`, `twin`), so `hord x s (other …) … : underStrand x = s`, hence
`s ≠ overStrand x` (`under_ne_over`) and `isOver v = false` (`record_isOver`, `overBit`, `decide_eq_false`) (≈20).
```lean
theorem BlockOrdered.switch_of_internal {D : Diagram} {q : ℕ} {blk : Fin D.Γ.c → Fin q}
    (hord : BlockOrdered D blk) {v : D.Γ.Visit}
    (hx : blk (D.compOf v) = blk (D.compOf (D.twin v))) : BlockOrdered (D.switch v.1) blk
```
`(D.switch x).Γ = D.Γ` (`rfl`), `switch_underStrand_self` / `switch_underStrand_of_ne`; at `x = v.1` the two
strands are `v.2.val` and `(twin v).2.val` (`mem_iff`), with equal `blk` by `hx`, so the premise
`blk s.1 < blk t.1` is impossible; at `y ≠ x` the under strand is unchanged (≈25).
```lean
theorem blockRestrict_switch_of_internal (D : Diagram) {q : ℕ} (blk : Fin D.Γ.c → Fin q)
    (hblk : Function.Surjective blk) (v : D.Γ.Visit) (i : Fin q)
    (y : (blockRestrict D blk hblk i).Γ.Crossing)
    (hy : (D.Γ.restrictMap (blockSet D blk i) (blockSet_nonempty D blk hblk i)).mapCrossing y = v.1) :
    blockRestrict (D.switch v.1) blk hblk i = (blockRestrict D blk hblk i).switch y
```
`rw [blockRestrict_eq, blockRestrict_eq, ← hy]; exact D.switch_restrict_of_internal _ _ y` (≈10).
```lean
theorem blockRestrict_switch_of_external (D : Diagram) {q : ℕ} (blk : Fin D.Γ.c → Fin q)
    (hblk : Function.Surjective blk) (v : D.Γ.Visit) (i : Fin q) (hi : i ≠ blk (D.compOf v)) :
    blockRestrict (D.switch v.1) blk hblk i = blockRestrict D blk hblk i
```
`switch_restrict_of_external` with `¬ ∀ s ∈ v.1.val, s.1 ∈ blockSet D blk i` witnessed by `v.2.val`
(`mem_blockSet_iff`, `compOf v = v.2.val.1`) (≈15).
```lean
theorem blocks_of_smoothing (D : Diagram) {q : ℕ} (blk : Fin D.Γ.c → Fin q)
    (hblk : Function.Surjective blk) (hord : BlockOrdered D blk) (v : D.Γ.Visit)
    (hx : blk (D.compOf v) = blk (D.compOf (D.twin v))) (D₀ : Diagram)
    (ι₀ : RecordIso D₀.record (D.record.smooth v)) :
    Function.Surjective (D.record.smoothBlock blk v hx ∘ ι₀.e) ∧
      BlockOrdered D₀ (D.record.smoothBlock blk v hx ∘ ι₀.e)
```
Surjective: for `i` pick `k` with `blk k = i`; if some `u` has `compOf u = k`, `ι₀.e.symm (inl ⟦u⟧)`
(`smoothBlock_inl`), else `ι₀.e.symm (inr ⟨k, _⟩)` (`smoothBlock_inr`).  Block-ordered: for `y` with strands
`s, t ∈ y.val`, `blk₀ s.1 < blk₀ t.1`: `u := ι₀.Φ ⟨y, s⟩`, `ι₀.Φ ⟨y, t⟩ = (smooth).pair u` (`ι₀.pair_eq`;
`⟨y, t⟩ = twin ⟨y, s⟩`), `ι₀.comp_eq` gives `ι₀.e s.1 = inl ⟦u.1⟧` so `blk₀ s.1 = blk (compOf u.1)` and likewise
for `t`; `hord` at `u.1.1` with the two strands of `u.1`, `twin u.1` gives `underStrand = u.1`'s strand, hence
`overBit u.1 = false`, `D₀.record.isOver ⟨y, s⟩ = false` (`ι₀.bit_eq`, `smooth_isOver`), `s ≠ overStrand y`,
`s = underStrand y` (`eq_under_of_mem_of_ne`) (≈120).

### 6.4 Initialization (unit U3, ≈170 lines)

```lean
theorem Link.Diagram.restrict_underFirst (D : Diagram) (B : D.Basing) (h : D.UnderFirst B)
    (S : Finset (Fin D.Γ.c)) (hS : S.Nonempty) :
    ∃ B' : (D.restrict S hS).Basing, (D.restrict S hS).UnderFirst B'
```
Rank: `exists_rank_equiv (fun j => (B.rank (S.orderEmbOfFin rfl j)).val) (injective)` gives
`r : Fin S.card ≃ Fin S.card` with `r j < r j' ↔ B.rank (emb j) < B.rank (emb j')`.  Base:
`base' j := B.base (S.orderEmbOfFin rfl j)` — typechecks since `(D.restrict S hS).Γ.comp j = D.Γ.comp (emb j)`
is `rfl` (`restrictShadow`); nonsingular: `(D.restrict S hS).Γ.eval ⟨j, b⟩ = D.Γ.eval ⟨emb j, b⟩` (`rfl`) and
`crossingPoint (mapCrossing y) = crossingPoint y` (`crossingPoint_mapCrossing`, `restrictMap.f = id`).
UNDER-first: for `y`, put `x := mapCrossing y`; `mapVisit (underVisit y) = underVisit x` and
`mapVisit (overVisit y) = overVisit x` (`Sigma.ext`, `toFun_restrict_underStrand/overStrand`);
`restrict_visitPt_fst`: `emb ((restrict).visitPt w).1 = (D.visitPt (mapVisit w)).1`;
`restrict_visitPt_snd`: the traversal points agree.  Unfold `basedRank`, `Prod.lex_def`; first components by
`r`'s monotonicity; second components literally equal after `restrict_visitPt_snd` (dependent rewrite: state
a `subst`-helper as in `exists_underFirst_of_rUnderFirst`'s `hcast`) (≈110; **risk: medium**, dependent types).
```lean
theorem stack_init (D : Diagram) {q : ℕ} (blk : Fin D.Γ.c → Fin q) (hblk : Function.Surjective blk)
    (B : D.Basing) (h : D.UnderFirst B) :
    P D = R.delta ^ (q - 1) * ∏ i : Fin q, P (blockRestrict D blk hblk i)
```
`P_underFirst_init D B h`; for each `i`, `restrict_underFirst B h (blockSet D blk i) _` and
`P_underFirst_init` give `P (D_i) = δ^{c_i − 1}` with `c_i = (blockSet D blk i).card` (`restrict_componentCount`);
`Finset.prod_pow_eq_pow_sum`; `∑ i, c_i = c` (`Finset.card_eq_sum_card_fiberwise` with `f := blk`,
`Finset.card_univ`, `Fintype.card_fin`); each `c_i ≥ 1` (`blockSet_nonempty`), so
`∑ (c_i − 1) = c − q` (`Nat` bookkeeping via `Finset.sum_const`/`Finset.sum_tsub_distrib`); `q ≤ c`;
`δ^{q−1} · δ^{c−q} = δ^{c−1}` (`← pow_add`, `omega`) (≈60).

### 6.5 The step (unit U5, ≈130 lines)

```lean
theorem stack_step (D : Diagram) {q : ℕ} (blk : Fin D.Γ.c → Fin q) (hblk : Function.Surjective blk)
    (hord : BlockOrdered D blk) (v : D.Γ.Visit)
    (hx : blk (D.compOf v) = blk (D.compOf (D.twin v))) (D₀ : Diagram)
    (h₀ : IsOrientedSmoothing D v.1 D₀) (ι₀ : RecordIso D₀.record (D.record.smooth v))
    (ihsw : P (D.switch v.1) =
      R.delta ^ (q - 1) * ∏ i : Fin q, P (blockRestrict (D.switch v.1) blk hblk i))
    (ih₀ : ∀ (blk₀ : Fin D₀.Γ.c → Fin q) (hblk₀ : Function.Surjective blk₀), BlockOrdered D₀ blk₀ →
      P D₀ = R.delta ^ (q - 1) * ∏ i : Fin q, P (blockRestrict D₀ blk₀ hblk₀ i)) :
    P D = R.delta ^ (q - 1) * ∏ i : Fin q, P (blockRestrict D blk hblk i)
```
Set `i₀ := blk (compOf v)`, `S := blockSet D blk i₀`, `hv : D.record.RestrictKeep S v := ⟨by simp, by simp [hx.symm]⟩`,
`F := blockRestrict D blk hblk i₀`, `ψ := D.restrictRecordIso S _ : F.record ≅ D.record.restrict S`,
`v' := ψ.Φ.symm ⟨v, hv⟩` (so `D.restrictVisit S _ v' = v` by `restrictVisitEquiv_apply_val` +
`Equiv.apply_symm_apply`), `y := v'.1`, `hy : mapCrossing y = v.1 := restrictVisit_fst …`.
1. `P D = solvedR (D.IsPositive v.1) (P (D.switch v.1)) (P D₀)` (`solvedR_of_skein (fun _ _ _ h => P_skein h) h₀`).
2. Switch: in `ihsw` rewrite the factor `i₀` by `blockRestrict_switch_of_internal … y hy` (= `F.switch y`) and
   every `i ≠ i₀` by `blockRestrict_switch_of_external`; `Finset.mul_prod_erase univ _ (mem_univ i₀)`.
3. Smoothing: `blk₀ := D.record.smoothBlock blk v hx ∘ ι₀.e`; `⟨hblk₀, hord₀⟩ := blocks_of_smoothing …`;
   `ih₀ blk₀ hblk₀ hord₀`.  For each `i`, `B'ᵢ := univ.filter (fun s => D.record.smoothBlock blk v hx s = i)`,
   `hB'ᵢ`/`hB''ᵢ` by `Finset.mem_filter`, `smoothBlock_inl/inr`, `mem_blockSet_iff`;
   `hBᵢ : ∀ c, ι₀.e c ∈ B'ᵢ ↔ c ∈ blockSet D₀ blk₀ i` (`rfl` after `mem_filter`).
   * `i ≠ i₀`: `(blockRestrict D₀ blk₀ hblk₀ i).record ≅ D₀.record.restrict (blockSet D₀ blk₀ i)` (`restrictRecordIso`)
     `≅ (D.record.smooth v).restrict B'ᵢ` (`ι₀.restrict _ _ hBᵢ`) `≅ D.record.restrict (blockSet D blk i)`
     (`restrictSmoothDisjointIso`, with `comp v ∉ blockSet i` and `comp (pair v) ∉ blockSet i` from `hx`, `hi`)
     `≅ (blockRestrict D blk hblk i).record` (`restrictRecordIso.symm`); `presentations` gives equal `P`.
   * `i = i₀`: `… ≅ (D.record.smooth v).restrict B'ᵢ₀ ≅ (D.record.restrict S).smooth ⟨v, hv⟩` (`restrictSmoothIso`)
     `≅ F.record.smooth v'` (`ψ.symm.smooth ⟨v, hv⟩`) `≅ F₀.record` for `⟨F₀, hF₀, ⟨ιF⟩⟩ :=
     exists_smoothing_record_visit F y v' rfl`; so `P (blockRestrict D₀ blk₀ hblk₀ i₀) = P F₀` (`presentations`).
4. `P F = solvedR (F.IsPositive y) (P (F.switch y)) (P F₀)` (`solvedR_of_skein … hF₀`) and
   `F.IsPositive y ↔ D.IsPositive v.1` (`restrict_isPositive_iff`, `hy`; rewrite the `Prop` argument of `solvedR`
   with `propext`/`simp only [this]`).
5. Algebra: with `c := δ^{q−1} * ∏_{i ≠ i₀} P (blockRestrict D blk hblk i)`, the two rewritten IHs read
   `P (D.switch v.1) = c * P (F.switch y)` and `P D₀ = c * P F₀`; `solvedR_mul_left`; conclude with
   `Finset.mul_prod_erase` on the target product (≈130; **risk: medium**, bookkeeping; every link exists).

`stack_formula` (PROVED in the skeleton) = `skein_induction_based` with
`Φ D B := ∀ q blk hblk, BlockOrdered D blk → B.BlockCompatible blk → P D = δ^{q−1} ∏ P (D_i)`, started at
`exists_blockCompatible_rbasing blk`; init through `exists_underFirst_of_rUnderFirst` + `stack_init`; step:
`isBad_internal (rBlockOrdered_of_blockOrdered hord) hBc hv` gives `hx`, `exists_smoothing_record_visit D v.1 v rfl`
gives `D₀, h₀, ι₀`, `ihsw` at `(hord.switch_of_internal hx)` (block-compatibility of `rbasingSwitch` is
definitional), `ih₀` from `ihsm` at `exists_blockCompatible_rbasing blk₀`.

## 7. Prover units

Independent units; each may assume the PROVED layer §0-§5 of `Skeleton_FINAL.lean` and all of `work/lean`,
plus only the *statements* listed in "may assume".

| unit | lemmas | may assume (beyond §0-§5) | est. lines |
|---|---|---|---|
| **U0 port-and-accept** | port §0-§5 into `SM/SkeinInduction.lean`, `SM/LpCore.lean`, `SM/RecordPolynomial.lean`, `SM/Presentations.lean`, `SM/SplitCircle.lean`; run the acceptance cycle for lp:core, rp:record-polynomial, lc:presentations, lp:split-circle (statement reviews on file); write the AUTHOR_NOTES entries of §8 | — | ≈60 (module scaffolding; no new proofs) |
| **U1 perm** | `firstReturn_firstReturn`, `firstReturn_mul_swap` (+ helper `firstReturn_congr_pred`) | `work/lean` only (`SM/LinkRecord.lean` §A/§B, `SM/LinkRecordExtras.lean` transport section) | 160 |
| **U2 record isos** | `beta_comp_eq_of_reconnect_sameCycle`, `restrictSmoothIso`, `restrictSmoothDisjointIso` | U1 statements | 360 |
| **U3 init** | `restrict_underFirst`, `stack_init` | — | 170 |
| **U4 block bookkeeping** | `rBlockOrdered_of_blockOrdered`, `BlockOrdered.switch_of_internal`, `blockRestrict_switch_of_internal`, `blockRestrict_switch_of_external`, `blocks_of_smoothing` | `smoothBlock_inl/inr` (`rfl`; `smoothBlock` is transparent, `beta_comp_eq…` may stay `sorry` while U4 works) | 190 |
| **U5 step** | `stack_step` (then `stack_formula`, `stack` are already proved) | statements of U1-U4 | 130 |

Total open ≈1,010 lines (A's per-lemma estimates, more conservative than B's 640).  Critical path
U1 → U2 → U5; U3, U4 in parallel with U1/U2; U0 in parallel with everything.

## 8. Deviations to record in `work/AUTHOR_NOTES.md`

* Any bad crossing is switched, not the printed "first bad crossing" (D3 of PLAN_B): `badCount_switch`
  shows the count drops by one for any bad occurrence of a fixed based order.
* The based order is record-level (`RBasing`: component rank + base occurrence = the first occurrence after
  the printed basepoint); the printed basepoint is recovered by the bridge `exists_underFirst_of_rUnderFirst`
  (`exists_basing_first`).  The bridge is used at `b = 0` only.
* rp:record-polynomial: the partner `D'` is quantified inside the induction predicate; no synchronised
  bad count on `D'` is maintained (the printed "Both numbers agree for the two based diagrams" is not needed).
* lp:core: `gaussian`, `support`, `skein`, `underFirst_init`, `unique`, `ne_zero` are proved by the printed
  induction (`G_descent`, `P_specQ`, `P_unique`); `P_skein` uses the additivity/`R`-linearity of `reMap`
  instead of injectivity after descent (equivalent); only `eq_homfly` consumes lp:coefficient-transport (as printed).
* lp:split-circle is proved through the record-level `Record.addFree` for the relational
  `IsSplitCircleAddition` (sm-3:1198-1200 "Switching or smoothing does not touch the extra component").
* mp:stack: the printed `N`, `b` count INTERNAL crossings only; FINAL counts all crossings of `D` with a
  block-compatible based order, under which every bad crossing is internal (`isBad_internal`) — the same
  induction, one fewer bookkeeping invariant.  The block of a smoothed component is `smoothBlock`
  (`Quotient.lift`), the printed "Every new component inherits the same block as the strands smoothed".

## 9. Risks and fallbacks

1. `restrictSmoothIso` (U2): the circle bijection must treat `s₁`-cycles in `B` **without** internal
   occurrence as free circles of `restrict B` (§6.2).  If the explicit inverse is painful, prove bijectivity by
   injectivity + `Fintype.card` equality (`Fintype.bijective_iff_injective_and_card`) only if the counts are
   cheaper; otherwise finish the explicit inverse.  Fallback for the block: land the four finished rows (U0)
   and keep mp:stack as its own lane with U1-U5.
2. `restrict_underFirst` (U3): dependent `TraversalPoint` types.  Use `show`/`subst`-helpers exactly as
   `exists_underFirst_of_rUnderFirst` does (`hcast`).  Fallback: B's record-level `RBasing.restrict` +
   `rUnderFirst_restrict` (first-return enumeration lemma, ≈120 lines) — the assembly is unchanged since the
   init only needs `∃ B', (D.restrict S hS).UnderFirst B'`.
3. `firstReturn_firstReturn` (U1): the two-level subtype `{m : {m // p m} // q m.1}` — prove it as "both are
   `f^n m` with the same minimal `n`" via `returnTime_eq_iff` on the flat side and `firstReturn_pow_of_pow` on
   the nested side; state the pointwise return-time identity first if needed.
4. Porting: re-check the `rfl` casts and the classical `badCount` instance after any toolchain change (§4).
