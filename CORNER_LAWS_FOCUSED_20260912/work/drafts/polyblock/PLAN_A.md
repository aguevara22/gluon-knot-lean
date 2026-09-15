# PLAN_A — the (N, b) skein induction and its five consumer rows

Architect tag **A** (diagram-level induction mirroring the printed proof), 2026-09-13/14.
Skeleton: **`work/drafts/polyblock/Skeleton_A.lean`** (1042 lines; `lake env lean` exit 0, only
`sorry` warnings; 29 sorry-leaves; all five row theorems proved from the chain).  `#print axioms`:
`SM.lp_core` — `propext, Classical.choice, Quot.sound, SM.lit_homfly, SM.lp_lm, SM.lp_lm_uniqueness`
(**no `sorryAx`: lp:core is completely proved**, since its whole chain — ring layer §1, badness §2,
principle §3, solved skeins §4, descent/uniqueness/nonvanishing §5 — is proved);
`SM.Link.Diagram.skein_induction` — `propext, Classical.choice, Quot.sound`;
`record_polynomial`, `presentations`, `split_circle`, `stack` — `propext, sorryAx, Classical.choice,
Quot.sound, SM.lp_lm` (the `sorryAx` is the remaining chain of §4, §6, §7 below).

Rows covered (bundles copied verbatim from `work/drafts/*_statement.lean`):

| row | theorem | status in skeleton |
|---|---|---|
| rp:record-polynomial | `SM.record_polynomial : RecordPolynomialData` | proved from chain |
| lp:core | `SM.lp_core : LpCoreData` | **FULLY PROVED** (no `sorry` anywhere in its chain; axioms = the three interfaces + standard) |
| lp:split-circle | `SM.split_circle : SplitCircleData` | proved from chain |
| lc:presentations | `SM.presentations` | proved (= `record_polynomial.P_eq`) |
| mp:stack | `SM.stack : StackData` | proved from chain; chain has its own unit list (§7) and is the risk |

## 0. The architecture in one page

**Measure.**  The printed proofs (sm-3:1083-1103, 1237-1243, 1192-1203, 1514-1533) all run a
lexicographic induction on `(N, b)`, `N` = crossing count, `b` = bad crossings for a chosen basing
(bad = first encounter OVER).  Lean rendering (skeleton §2-3):

* `N := Fintype.card D.Γ.Crossing`; outer **strong induction** on `N` (`Nat.strong_induction_on`).
* For a basing `B : D.Basing`, `D.Bad B x := Lex (basedRank B (overVisit x)) (basedRank B (underVisit x))`
  and `D.badCount B := #{x | Bad B x}`; `D.UnderFirst B ↔ badCount B = 0`
  (`underFirst_iff_badCount_eq_zero`, via `not_bad_iff` = trichotomy of the total lexicographic
  order on distinct based ranks, `basedRank_injective`).
* Inner **ordinary induction on `b`**, generalising `D` and `B`, with `N` fixed.
* **The switch keeps the basing** (`Basing.switch B x : (D.switch x).Basing := ⟨B.rank, B.base, B.nonsingular⟩`
  — typechecks because `(D.switch x).Γ = D.Γ` is `rfl`; `basedRank_switch` is `rfl`).  Switching ANY
  bad crossing `x` lowers `badCount` by exactly one for the same basing (`bad_switch_iff`,
  `badCount_switch_of_bad`): the printed "first bad crossing" is inessential; any bad crossing serves.
* **The smoothing changes the shadow**; a new basing is chosen on `D₀` by `exists_basing` inside the
  outer step (the outer hypothesis is quantified over all diagrams with fewer crossings).  The gate
  `exists_smoothing_record D x` supplies `D₀` with `IsOrientedSmoothing D x D₀` and
  `RecordIso D₀.record (D.record.smooth (D.overVisit x))`; `N(D₀) + 1 = N(D)` is
  `IsOrientedSmoothing.card_crossing`.

This gives the **reusable principle** (skeleton §3, PROVED):
```lean
theorem Diagram.skein_induction (motive : Diagram → Prop)
    (init : ∀ (D : Diagram) (B : D.Basing), D.UnderFirst B → motive D)
    (step : ∀ (D : Diagram) (x : D.Γ.Crossing) (D₀ : Diagram), IsOrientedSmoothing D x D₀ →
      Nonempty (RecordIso D₀.record (D.record.smooth (D.overVisit x))) →
      motive (D.switch x) → motive D₀ → motive D) : ∀ D, motive D
```
The step gets the record isomorphism because every consumer needs it: lp:core for the component
count `c ± 1` (`componentCount_of_smoothing_iso`), rp/presentations/split/stack to transport the
smoothing to the second diagram or to the block restrictions.

**The two solved recursions** (skeleton §1, PROVED, and §4 PROVED):
`solvedT pos u w := if pos then −l⁻²·u − l⁻¹m·w else −l²·u − lm·w` (rp:positive/negative-recursion),
`solvedR pos u w := if pos then a⁻²·u + a⁻¹z·w else a²·u − az·w` (lp:positive/lp:negative),
`solvedRG` the same in `R_G`; `pos : Prop` (classical `if`), so rewriting the positivity of the
crossing through a record isomorphism is a plain `rw` with an `Iff`.
`solvedT_of_skein F hF D x D₀ h : F D = solvedT (D.IsPositive x) (F (D.switch x)) (F D₀)` for any `F`
with the source skein and ANY oriented smoothing `D₀` of `D` at `x`: at a positive `x` the triple is
`(D, D.switch x, D₀)`; at a negative `x` it is `(D.switch x, D, D₀)` by `switch_isPositive_self`,
`switch_switch`, `IsOrientedSmoothing.switch` (LinkMoves 1988).  `solvedR_of_skein` is the same for
the campaign skein.  `phi_toTG_solvedT : φ(solvedT …) = solvedRG (φ …) (φ …)` is the printed
`lp:gaussian-skein → lp:positive/lp:negative` computation with `i² = −1` (`RG.iota_mul_iota`).

**The second diagram lives inside the motive.**  For rp:record-polynomial the motive is
`fun D => ∀ D', Nonempty (RecordIso D.record D'.record) → lmF D = lmF D'`; the step transports the
switch (`switch_recordIso_transport`, PROVED: `switchRecordIso ≫ ι.switch ≫ switchRecordIso⁻¹`) and
the smoothing (`exists_smoothing_recordIso_transport`, PROVED: gate on `D'` at the image occurrence
`ι.Φ (overVisit x)` + `ι.smooth`), and equal signs (`isPositive_iff_of_recordIso`, PROVED, from
`sgn_eq`).  No badness on `D'` is ever needed: only the **initialization** needs a basing of `D'`,
and that is the transported basing of the printed proof (§4 below), built with `exists_basing_before`
(the "basepoint just before the image of the first occurrence" device generalising
`exists_basing_first`) and justified through `RecordIso.visitBetween_iff`.

**lp:split-circle** is reformulated as a record statement (`SplitMotive E`: for a crossing-free
component `j` of `E`, every `D'` with `D'.record ≅ (E.restrict (univ.erase j)).record` has
`P E = δ P D'`); the printed `IsSplitCircleAddition D D'` is exactly `E := D'` plus a reparametrisation
of `D` (planar isotopy) to the restriction.  The step needs two record-level commutations,
`restrictSwitchIso` and `restrictSmoothFreeIso`.

**mp:stack** needs a block-compatible basing, so it has its own scaffold `stack_value` (PROVED from
its chain, same shape as `skein_induction`) and the heavy record-level block transport under
smoothing (`restrictSmoothIso`, `restrictSmoothDisjointIso`).  See §7.

## 1. Dependency order (units)

```
U0  ring layer            §1 skeleton — DONE (RG.iota_mul_iota, phi_*_eq, phi_toTG_solvedT, phi_toTG_mu,
                           InSupportM.solvedR, specQ_solvedR, solvedR_mul_left, toRG_solvedR)
U1  badness               §2 — DONE (basedRank_injective, not_bad_iff, underFirst_iff_badCount_eq_zero,
                           exists_bad_of_badCount_pos, bad_switch_iff, badCount_switch_of_bad)
                           → skein_induction DONE (standard axioms only)
U2  lp:core assembly      §4-5 — DONE (G_solved, G_underFirst, P_underFirst, G_skein, G_descent,
                           toRG_P, P_inSupportM, P_skein, P_unique, specQ_P, P_ne_zero, RCompetitor P/H,
                           P_eq_homfly); lp_core has no sorry in its cone
U3  UNDER-first transport §6: exists_isFirst, IsFirst.unique, exists_base_before, exists_basing_before,
                           cycBetween_cyclicOffset, offset_lt_iff_of_isFirst,
                           underFirst_of_recordIso_of_isFirst, underFirst_of_recordIso
U4  rp + presentations    §7-8 — DONE modulo U1, U3
U5  restriction init      restrict_underFirst (shared by split-circle and stack)
U6  split-circle          restrictSwitchIso, restrictSmoothFreeIso, splitMotive_init (U3, U5), splitMotive_step
U7  stack (own list §7)   perm lemmas → record isos → block structure → stack_init (U5) → stack_step
```
Units U1, U3, U5, U6a (record isos), U7a (perm lemmas) are mutually independent and can be proved in
parallel; U6b/U7 assembly last.

## 2. Ring layer (skeleton §1, all PROVED; recorded for the reviewer)

| lemma | statement | proof |
|---|---|---|
| `RG.iota_mul_iota` | `algebraMap ℤ[i] R_G i * algebraMap … i = -1` | `map_mul`, `gaussI_mul_gaussI` (LinkLaurentRing 988) |
| `phi_l_eq`, `phi_m_eq`, `phi_lInv_eq`, `phi_mInv_eq` | `φ l = i·a`, `φ m = −(i·z)`, `φ l⁻¹ = −(i·a⁻¹)`, `φ m⁻¹ = i·z⁻¹` as ring products | `phi_l'` 1311, `phi_m'` 1321, `phi_lInv` 1325, `phi_mInv` 1332, `Algebra.smul_def`, `AddMonoidAlgebra.smul_single`, `single_neg` |
| `phi_toTG_solvedT` | `φ(toTG (solvedT pos u w)) = solvedRG pos (φ(toTG u)) (φ(toTG w))` | `split_ifs`, `simp only [map_*, T.toTG_*, phi_*_eq]`, `linear_combination c * hI` |
| `phi_toTG_mu` | `φ(toTG μ) = toRG δ` | `T.mu` 226, `phi_l_add_lInv` 1443, `phi_mInv_eq`, `R.delta` 193, `linear_combination` |
| `InSupportM.solvedR` | `u ∈ M_c → w ∈ M_{c₀} → (c₀ = c+1 ∨ c₀+1 = c) → solvedR pos u w ∈ M_c` | `InSupportM.z_mul` 913 / `z_mul_of_pred` 943, `a_mul` 902, `aInv_mul` 904, `add`/`sub` 852/863 |
| `specQ_solvedR` | `specQ u = 1 → specQ w = 1 → specQ (solvedR pos u w) = 1` | `specQ_positive_identity` 1502, `specQ_negative_identity` 1509 |
| `solvedR_mul_left`, `toRG_solvedR` | linearity; `toRG` commutes | `ring`; `simp [map_*]` |

## 3. Badness (skeleton §2, unit U1) — all 6 PROVED (sketches kept as the record of the proofs)

All in `namespace SM.Link.Diagram`, `variable (D : Diagram)`.  Two details that mattered: the based
rank's first component is a `Fin` cast to `ℕ`, so `B.rank i = B.rank j` needs `Fin.ext`; and the
switched diagram's crossing type `(D.switch x).Γ.Crossing` is only definitionally `D.Γ.Crossing`, so
the `Finset` identity behind `badCount_switch_of_bad` must be stated on `D.Γ.Crossing` and the goal
brought to that form with `show` before `rw` (otherwise `ext`/`subst`/`rw` fail at implicit
transparency).  Every `Finset.filter` proof is under `open scoped Classical in` to match the
instance of `badCount`.

* `basedRank_injective (B) : Function.Injective (D.basedRank B)` (~35).  From
  `basedRank B v = basedRank B w`: first components → `B.rank (compOf v) = B.rank (compOf w)` →
  `compOf v = compOf w` (`Equiv.injective`); second components → `cyclicOffset k a (visitCoord v) =
  cyclicOffset k a (visitCoord w)` with `a, visitCoord ∈ [0,k)` → `visitCoord v = visitCoord w`
  (unfold `cyclicOffset` 1487, `split_ifs`, `linarith` with `traversalKey_nonneg` 1512,
  `traversalKey_lt_card` 1515) → `visitCoord_injOn` (LinkDiagramRecord 189).  Note
  `(D.basedRank B v).1 = B.rank (compOf v)` and `.2 = cyclicOffset … (visitCoord v)` are `rfl`
  (`compOf_eq_visitPt_fst` 169, `visitCoord` 181).
* `not_bad_iff (B x) : ¬ Bad B x ↔ Lex (basedRank B (underVisit x)) (basedRank B (overVisit x))` (~25).
  `Prod.lex_def`; the based ranks of the two occurrences are distinct (`basedRank_injective`,
  `overVisit_ne_underVisit` LinkDiagram 608); trichotomy of `<` on `ℕ` and on `ℝ`.
* `underFirst_iff_badCount_eq_zero (B) : D.UnderFirst B ↔ D.badCount B = 0` (~20).
  `Finset.card_eq_zero`, `Finset.filter_eq_empty_iff`, `not_bad_iff`; `UnderFirst` is LinkDiagram 1545.
* `exists_bad_of_badCount_pos` (~8): `Finset.card_pos` → `Finset.Nonempty` → `Finset.mem_filter`.
* `bad_switch_iff (B x y) : (D.switch x).Bad (B.switch x) y ↔ if y = x then ¬ Bad B x else Bad B y` (~40).
  `basedRank_switch` is `rfl`; `y = x`: `switch_overVisit_self` (LinkMoves 1904),
  `switch_underVisit_self` 1908 exchange the two occurrences, then `not_bad_iff`; `y ≠ x`:
  `switch_overVisit_of_ne` 1912, `switch_underVisit_of_ne` 1917.
* `badCount_switch_of_bad (B) (hx : Bad B x) : (D.switch x).badCount (B.switch x) + 1 = D.badCount B` (~25).
  The filtered set of the switch is `(filter Bad).erase x` (`Finset.ext`, `bad_switch_iff`), then
  `Finset.card_erase_add_one` / `Finset.card_erase_of_mem` with `x ∈ filter`.

## 4. UNDER-first transport (skeleton §6, unit U3) — 8 leaves, ~425 lines

Printed device (sm-3:1230-1236): transfer the component order; on a component with crossings put the
new basepoint just before the image of the old first occurrence.

* `IsFirst B v := ∀ w, compOf w = compOf v → w ≠ v → (basedRank B v).2 < (basedRank B w).2`.
* `exists_isFirst (B i) (h : ∃ v, compOf v = i) : ∃ v, compOf v = i ∧ IsFirst B v` (~30):
  `Finset.exists_min_image (compVisits i) (fun v => (basedRank B v).2)` (Mathlib
  Data/Finset/Max.lean 534; `compVisits`/`mem_compVisits` LinkDiagramRecord 228/230), strictness from
  `basedRank_injective` (equal offsets on one component ⇒ equal ranks ⇒ equal visits).
* `IsFirst.unique` (~10): two firsts on one component bound each other strictly.
* `exists_base_before (i v) (hv : compOf v = i) : ∃ b : TraversalPoint (comp i).k, nonsingular ∧ ∀ w on i, w ≠ v → cyclicOffset k (key b) (visitCoord v) < cyclicOffset k (key b) (visitCoord w)` (~70).
  `subst hv`; this is the body of `exists_basing_first` (SingleCrossing 84-152) with the basing
  packaging removed: `exists_param_before` (SingleCrossing 44) on the edge of `v` gives `tb`, then
  `cyclicOffset_of_le`/`of_lt` (LinkDiagram 1492/1495), `traversalKey_lt_iff`,
  `traversalKey_injective`, `visitPt_injective` 1453 — copy that proof.
* `exists_basing_before (rank) (f : ∀ i, Option {v // compOf v = i}) : ∃ B, B.rank = rank ∧ ∀ i v, f i = some v → IsFirst B v.1` (~50).
  `base i := match f i with | some ⟨v, hv⟩ => choose (exists_base_before i v hv) | none => choose (exists_nonsingular_base i)`
  (LinkDiagram 1559); `nonsingular` by cases; `IsFirst` unfolds to the offset clause of
  `exists_base_before` since `(basedRank B w).2` is `cyclicOffset … (key (B.base (compOf w))) (visitCoord w)` by `rfl`
  and `compOf w = i`.
* `cycBetween_cyclicOffset (0 ≤ a, x, y, z < k) : cycBetween (off a x) (off a y) (off a z) ↔ cycBetween x y z` (~45).
  `cycBetween` is LinkDiagramRecord 78 (three disjuncts); unfold `cyclicOffset`, `split_ifs` (8 cases),
  each direction by `rcases` + `linarith` (all points in `[0,k)`).  Pure real arithmetic; a mechanical
  but long case split — consider `omega`-free `nlinarith`-free `linarith` only.
* `offset_lt_iff_of_isFirst (B) (h₁ : IsFirst B v₁) (hu ho) (huo : u ≠ o) : (basedRank B u).2 < (basedRank B o).2 ↔ (u = v₁ ∨ (o ≠ v₁ ∧ VisitBetween v₁ u o))` (~70).
  Let `t w := (basedRank B w).2 = cyclicOffset k (key b) (visitCoord w)`.  `VisitBetween v₁ u o =
  cycBetween (visitCoord v₁) (visitCoord u) (visitCoord o)` (882) `↔ cycBetween (t v₁) (t u) (t o)`
  by `cycBetween_cyclicOffset`.  Cases: `u = v₁` (LHS true by `h₁`, RHS true); `o = v₁` (LHS false by
  `h₁` + asymmetry, RHS false); both `≠ v₁`: `t v₁ < t u`, `t v₁ < t o`, `t u ≠ t o`
  (`basedRank_injective`), so `cycBetween (t v₁) (t u) (t o) ↔ t u < t o` (only the first disjunct
  can hold; `linarith`).
* `underFirst_of_recordIso_of_isFirst (ι B B') (hrank : ∀ i k, B'.rank (ι.e i) < B'.rank (ι.e k) ↔ B.rank i < B.rank k) (hfirst : ∀ v, IsFirst B v → IsFirst B' (ι.Φ v)) (h : UnderFirst B) : UnderFirst B'` (~90).
  For `y : D'.Γ.Crossing` let `u := ι.Φ.symm (D'.underVisit y)`, `o := ι.Φ.symm (D'.overVisit y)`;
  `ι.pair_eq` + `record_pair_apply` (524) ⇒ `o = D.twin u` ⇒ `o.1 = u.1 =: x`; `ι.bit_eq` +
  `record_isOver_iff` (529) ⇒ `o = D.overVisit x`, `u = D.underVisit x`.  `h x : Lex (rank u) (rank o)`.
  First-component case: `ι.comp_eq` (`compOf (Φ v) = ι.e (compOf v)`, `record_comp` 520) + `hrank`.
  Equal-component case: `exists_isFirst` gives `v₁` on that component; `hfirst v₁`;
  `offset_lt_iff_of_isFirst` on both sides; `ι.visitBetween_iff` (LinkDiagramRecord 1146) and
  `ι.Φ.injective` identify the right-hand sides.  `Prod.lex_def` throughout.
* `underFirst_of_recordIso (ι B) (h) : ∃ B', D'.UnderFirst B'` (~60).
  `hc : D.Γ.c = D'.Γ.c` from `ι.componentCount_eq` + `record_componentCount` (537);
  `rank' := ι.e.symm.trans (B.rank.trans (finCongr hc))` (so `rank' (ι.e i) = finCongr hc (B.rank i)`
  and `hrank` is `Fin.lt_def`/`finCongr_apply`);
  `f j := if h : ∃ v, compOf v = ι.e.symm j then some ⟨ι.Φ (choose (exists_isFirst B _ h)), comp_eq⟩ else none`;
  `exists_basing_before rank' f` gives `B'`; `hfirst`: a first `v` on component `i` equals the chosen
  first (`IsFirst.unique`), so `ι.Φ v` is designated ⇒ `IsFirst B' (ι.Φ v)`; conclude by
  `underFirst_of_recordIso_of_isFirst`.

## 5. rp:record-polynomial, lc:presentations, lp:core assembly (skeleton §4-5, §7-9) — PROVED

Proved from U1 + U3 in the skeleton; nothing to do.  Record of the reuse:
`lmF_sourceSkein` (LinkInterfaces 403), `lmF_underFirst_init` 409, `lmF_unknot` 421, `lmF_planar` 399,
`lmF_reidemeister_I/II/III` 425/429/433, `homfly_planar` 382, `homfly_reidemeister_I` 370 (+II/III),
`homfly_circle` 386, `homfly_skein` 390, `RCompetitor` (CoefficientTransport 23),
`coefficient_transport` 137, `P` (LocalPolynomial 23), `P_eq_one_of_lmF_eq_one` 26,
`R.toRG_injective` (LinkLaurentRing 1020), `R.toRG_a/z/aInv/zInv` 1030-1033, `T.toTG_l/m/lInv/mInv`
1044-1053, `reMap_toRG` 1098, `InSupportM.delta_pow` 972, `inSupportM_iff` 875, `specQ_delta` 1496,
`Diagram.switchRecordIso` (LinkDiagramRecord 686), `RecordIso.switch` (LinkRecord 778),
`RecordIso.smooth` (LinkRecordExtras 432), `RecordIso.componentCount_eq` (LinkRecord 613),
`Record.componentCount_smooth` (LinkRecordExtras 333), `two_le_componentCount_of_mixed` 328,
`exists_smoothing_record` (Smoothing 8178), `exists_smoothing_record_visit` 8185,
`IsOrientedSmoothing.card_crossing` (LinkMoves 1051), `IsOrientedSmoothing.switch` 1988,
`switch_isPositive_self` (LinkDiagram 699), `switch_switch` 710, `isPositive_iff_sign_eq_one` 559,
`exists_basing` 1570, `underFirst_of_isEmpty` 1550, `componentCount_pos` 582.

## 6. lp:split-circle (skeleton §10, units U5-U6) — 5 leaves, ~460 lines

* `Record.restrictKeep_of_free` — PROVED (trivial).
* `Record.restrictSwitchIso (B v hv) : Nonempty (RecordIso ((ρ.switch v).restrict B) ((ρ.restrict B).switch ⟨v, hv⟩))` (~35).
  `e := Equiv.refl`, `Φ := Equiv.refl` (both `M`s are literally `{u // ρ.RestrictKeep B u}`: `switch`
  keeps `comp`, `pair`, `succ` — LinkRecord 655 — and `restrict` 1144 uses only those, with the same
  classical `DecidablePred` instance 1139), `succ_eq`/`pair_eq`/`comp_eq := rfl`;
  `bit_eq`: `Record.switch_isOver` 688 on both sides with `w ∈ {⟨v⟩, pair ⟨v⟩} ↔ w.1 ∈ {v, pair v}`
  (`Subtype.ext_iff`, `restrict_pair_val`); `sgn_eq` likewise with `switch_sgn` 692.
* `Record.restrictSmoothFreeIso (hj : ∀ u, comp u ≠ j) (v) : Nonempty (RecordIso ((ρ.smooth v).restrict (univ.erase (inr ⟨j,hj⟩))) ((ρ.restrict (univ.erase j)).smooth ⟨v,_⟩))` (~150).
  `M`: both are `{u // SmoothKeep v u}` up to the always-true `RestrictKeep`
  (`restrictKeep_of_free`; on the smoothing `(ρ.smooth v).comp w = inl _ ≠ inr _`, `smooth_comp` 918);
  `Φ := Equiv.subtypeEquiv`-style repackaging.  `succ_eq`: LHS succ is `firstReturn (smooth.succ) (RestrictKeep …)`
  = `smooth.succ` (`restrict_succ_val_of_keep` 1176 since every value is kept)
  = `firstReturn (ρ.reconnect v) (SmoothKeep v)`; RHS succ is `firstReturn ((ρ.restrict _).reconnect ⟨v⟩) (SmoothKeep ⟨v⟩)`
  and `(ρ.restrict _).reconnect ⟨v⟩ ⟨u⟩ = ⟨ρ.reconnect v u⟩` (restricted `succ` = `succ` by
  `restrict_succ_val_of_keep`, `Equiv.swap` on subtypes); conclude by `firstReturn_map_val`
  (LinkRecordExtras 394) along `u ↦ ⟨u, _⟩`.  `e`: `inl q ↦ inl (Quotient.map …)` via
  `sameCycle_map_iff` 370 with the same `Φ`, `inr f ↦ inr ⟨⟨f.1, mem_erase⟩, free⟩`; inverse explicit;
  `comp_eq` by `Quotient.ind`.  **Risk: medium** (dependent subtype bookkeeping; the perm content is
  already in `firstReturn_map_val`).
* `Diagram.restrict_underFirst (B) (h : UnderFirst B) (S hS) : ∃ B', (D.restrict S hS).UnderFirst B'` (~110).
  Rank: `g := B.rank ∘ S.orderEmbOfFin rfl` is injective into `Fin c`; `rank' := (image.orderIsoOfFin rfl).symm ∘ Equiv.ofInjective g`
  (Mathlib Data/Finset/Sort.lean 186) — strictly monotone in `g`.  Base: `base' i' := B.base (S.orderEmbOfFin rfl i')`;
  nonsingular because `(D.restrict S hS).Γ.comp i' = D.Γ.comp (emb i')` (`restrictShadow` LinkDiagram 974, `rfl`)
  and crossing points of the restriction are crossing points of `D`
  (`StrandMap.crossingPoint_mapCrossing` 846).  For a crossing `y` of the restriction with
  `x := mapCrossing y`: `restrict_visitPt_fst/snd` (LinkDiagramExtras 832/837) give
  `compOf`/offset of `restrictVisit` = those of the image, `toFun_restrict_underStrand` 78 /
  `toFun_restrict_overStrand` 71 identify `underVisit y ↦ underVisit x`; `h x` transfers through
  monotone `rank'` (`Prod.lex_def`).  Shared with mp:stack's `stack_init`.
* `splitMotive_init (E B) (h : UnderFirst B) : SplitMotive E` (~45).
  `P E = δ^{c−1}` (`P_underFirst`); `hne` ⇒ `2 ≤ c` (`Finset.card_pos`, `card_erase_of_mem`);
  `restrict_underFirst B h (univ.erase j) hne` ⇒ `underFirst_of_recordIso ι` on `D'` ⇒
  `P D' = δ^{(c−1)−1}` (`restrict_componentCount` LinkDiagram 1085, `ι.componentCount_eq`);
  `δ^{c−1} = δ * δ^{c−2}` (`pow_succ`, `Nat.sub_add_cancel`).
* `splitMotive_step (E x E₀ h₀ ι₀ ihsw ih₀) : SplitMotive E` (~120).
  Given `j hj hne D' ⟨ι'⟩` with `ι' : D'.record ≅ (E.restrict (erase j)).record`; let
  `ψ := E.restrictRecordIso (erase j) hne` (LinkDiagramRecord 1454), `κ := ι'.trans ψ : D'.record ≅ E.record.restrict (erase j)`,
  `v' := κ.Φ.symm ⟨E.overVisit x, restrictKeep_of_free hj _⟩`, `y := v'.1`.
  Switch: `(D'.switch y).record ≅ D'.record.switch v'` (`switch_record` 697) `≅ (E.record.restrict _).switch (κ.Φ v')`
  (`κ.switch`) `= (…).switch ⟨overVisit x, _⟩` (`Equiv.apply_symm_apply`, proof irrelevance)
  `≅ (E.record.switch (overVisit x)).restrict (erase j)` (`restrictSwitchIso`) `≅ ((E.switch x).record).restrict (erase j)`
  (`RecordIso.restrict` LinkRecordExtras 456 of `(E.switchRecordIso x _ rfl).symm`, `hB` trivial since `e = refl`)
  `≅ ((E.switch x).restrict (erase j) hne).record` (`restrictRecordIso.symm`); `j` is free in `E.switch x`
  (`switch_compOf` 611 is `rfl`); `ihsw j hj hne (D'.switch y)`.
  Smoothing: `exists_smoothing_record_visit D' y v' rfl` gives `D'₀`, `D'₀.record ≅ D'.record.smooth v' ≅ (E.record.restrict _).smooth ⟨overVisit x,_⟩`
  (`κ.smooth v'`) `≅ (E.record.smooth (overVisit x)).restrict (erase (inr j))` (`restrictSmoothFreeIso.symm`)
  `≅ E₀.record.restrict (erase j₀)` with `j₀ := ι₀.e.symm (inr ⟨j, hj⟩)` (`(ι₀.restrict …).symm`, `hB : ι₀.e c ∈ erase (inr j) ↔ c ∈ erase j₀` by `e.injective`)
  `≅ (E₀.restrict (erase j₀) hne₀).record`; `j₀` free in `E₀` (a visit on `j₀` would map to a
  `comp = inl _` ≠ `inr _`, `ι₀.comp_eq`); `hne₀` from `ι₀.e.symm (inl ⟦overVisit x⟧) ≠ j₀`;
  `ih₀ j₀ _ hne₀ D'₀`.
  Sign: `E.IsPositive x ↔ D'.IsPositive y` from `κ.sgn_eq v'` (`restrict_sgn` is `rfl`).
  Algebra: `P E = solvedR pos (P (E.switch x)) (P E₀)` (`solvedR_of_skein P P_skein E x E₀ h₀`),
  `P D' = solvedR pos (P (D'.switch y)) (P D'₀)`, substitute the two IH equalities, `solvedR_mul_left`.
  A small helper `RecordIso.ofEq (h : ρ = ρ') : RecordIso ρ ρ'` (`h ▸ refl`) or stating
  `restrictSwitchIso`/`restrictSmoothFreeIso` for an arbitrary proof term avoids the
  `apply_symm_apply` cast.  **Risk: medium** (long `trans` chain; each link exists).

## 7. mp:stack (skeleton §11, unit U7) — 16 leaves, ~1015 lines — THE RISK

Own scaffold `stack_value` (PROVED from the chain): outer strong induction on `N`, inner induction on
`badCount B` for a **block-compatible** basing (`BlockCompatible D blk B := blk i < blk k → B.rank i < B.rank k`),
generalising `D, q, blk, hblk, B`; `blk_eq_of_bad` makes every bad crossing internal.

### 7.1 Diagram-level, easy (~135 lines)
* `exists_blockCompatible (D blk) : ∃ B, BlockCompatible D blk B` (~40): key `i ↦ toLex (blk i, i) : Fin q ×ₗ Fin c`
  injective; `rank := (image.orderIsoOfFin rfl).symm ∘ Equiv.ofInjective key`; base/nonsingular from
  `exists_basing`.  `Prod.Lex.lt_iff` for `blk i < blk k → key i < key k`.
* `blk_eq_of_bad (hB hord hx)` (~30): if `blk (under) < blk (over)` then `rank (comp under) < rank (comp over)`
  ⇒ `Lex (rank under) (rank over)` contradicts `hx` (`not_bad_iff`); if `blk (over) < blk (under)` then
  `hord x over under … : underStrand x = overStrand x`, contradicting `over_ne_under` (LinkDiagram 512).
  `Fin` is linear: `lt_trichotomy`.
* `BlockOrdered.switch_of_internal` (~25): `switch_underStrand_self` 673 / `switch_underStrand_of_ne` 680,
  `x.val` unchanged; at `x` both strands have equal `blk` so the premise `blk s.1 < blk t.1` is false.
* `exists_blockCrossing` (~15): `restrict_mapCrossing_range_iff` (LinkDiagram 1037) with `mem_iff` 519
  (`s ∈ x.val ↔ s = over ∨ s = under`) and `hx`.
* `blockRestrict_switch_of_internal` (~10): `blockRestrict_eq` (`rfl`), `switch_restrict_of_internal`
  (LinkDiagramExtras 735) after `subst hy`.
* `blockRestrict_switch_of_external` (~15): `switch_restrict_of_external` 746; `¬ ∀ s ∈ x.val, s.1 ∈ blockSet i`
  witnessed by `overStrand x`.

### 7.2 Permutation lemmas (~160 lines, independent of everything else)
* `firstReturn_firstReturn (f p q m) : (firstReturn (firstReturn f p) (q ∘ val) m).1.1 = (firstReturn f (p ∧ q) ⟨m,_⟩).1` (~70).
  Both sides are `(f ^ n) m` for the least `n > 0` with `p ∧ q`; the LHS iterates `firstReturn f p`
  whose `k`-th power is `f ^ (sum of return times)` (`firstReturn_pow_of_pow` LinkRecord 162 /
  `firstReturn_apply` 103, `returnTime_spec` 64, `returnTime_min` 67); minimality on both sides via
  `returnTime_eq_iff` 70.
* `firstReturn_mul_swap (f p a b ha hb) : firstReturn (f * swap a b) p = firstReturn f p * swap ⟨a⟩ ⟨b⟩` (~90).
  Pointwise: for `u ∉ {a,b}`, `(f * swap a b)^n u = f^n u` while no intermediate point is a `p`-point
  (`a, b` are `p`-points), so the return times agree (`Perm.mul_swap_apply_of_ne_of_ne` LinkRecord 202);
  for `u = a`: `(f * swap) a = f b`, then as before from `f b`, matching `firstReturn f p ⟨b⟩`;
  symmetric for `b`.  Induction on `n` with the invariant "`f^k u ∉ {a,b}` for `0 < k < n`".

### 7.3 Record isos (~390 lines)
* `comp_mem_iff_of_reconnect_sameCycle (v B hvB) : SameCycle (reconnect v) u w → (comp u ∈ B ↔ comp w ∈ B)` (~40).
  One step: `reconnect v u = succ (swap v (pair v) u)` (LinkRecord 822): `u = v ↦ comp (succ (pair v)) = comp (pair v)`
  (`succ_comp`), `↔ comp v ∈ B` by `hvB`; `u = pair v` symmetric; else `comp (succ u) = comp u`.
  Then `zpow` induction (`Perm.SameCycle` is `∃ n : ℤ, (f ^ n) u = w`; `map_pow_apply`-style as in
  LinkRecordExtras 359).
* `exists_smoothBlock (v B hvB) : ∃ B', (∀ u, inl ⟦u⟧ ∈ B' ↔ comp u ∈ B) ∧ (∀ f, inr f ∈ B' ↔ f.1 ∈ B)` (~30).
  `B' := univ.filter (Sum.elim (Quotient.liftOn' · (comp · ∈ B) (propext ∘ comp_mem_iff…)) (·.1 ∈ B))`;
  `Finset.mem_filter`, `Quotient.liftOn'_mk`.
* `restrictSmoothIso (v B hv B' hB' hB'')` (~200): `M`-equiv `{w : {u // SmoothKeep} // RestrictKeep B' w} ≃ {w : {u // RestrictKeep B} // SmoothKeep ⟨v⟩ w}`
  via `hB'` (`(smooth).comp w = inl ⟦w.1⟧` 918, `smooth_pair_val`) and `SmoothKeep ⟨v⟩ w ↔ SmoothKeep v w.1`
  (`smoothKeep_iff` 855, `Subtype.ext_iff`).  `succ_eq`: LHS = `firstReturn (firstReturn (reconnect v) SmoothKeep) (RestrictKeep B' ∘ val)`
  = `firstReturn (reconnect v) (SmoothKeep ∧ RestrictKeep B)` (`firstReturn_firstReturn`); RHS =
  `firstReturn ((restrict B).reconnect ⟨v⟩) SmoothKeep` with `(restrict B).reconnect ⟨v⟩ = firstReturn succ (RestrictKeep B) * swap ⟨v⟩ ⟨pair v⟩ = firstReturn (succ * swap v (pair v)) (RestrictKeep B) = firstReturn (reconnect v) (RestrictKeep B)`
  (`firstReturn_mul_swap`) so RHS = `firstReturn (firstReturn (reconnect v) (RestrictKeep B)) (SmoothKeep ∘ val)`
  = `firstReturn (reconnect v) (RestrictKeep ∧ SmoothKeep)` (`firstReturn_firstReturn`, `and_comm`).
  `e`: `inl ⟦u⟧ ↦ inl ⟦⟨u,_⟩⟧` for `comp u ∈ B` (`sameCycle_map_iff` along the subtype inclusion with
  `reconnect_eq`), `inr f ↦ inr ⟨⟨f.1,_⟩, free⟩`; bijectivity by explicit inverse; `comp_eq` by `Quotient.ind`.
  **Risk: high** (largest single lemma; the two perm lemmas carry the content).
* `restrictSmoothDisjointIso (v B hv hv' B' hB' hB'')` (~120): `M`-equiv `{w : {u // SmoothKeep} // RestrictKeep B' w} ≃ {u // RestrictKeep B u}`
  (`RestrictKeep B u → u ≠ v, pair v` since `comp v ∉ B`); `succ_eq`: LHS = `firstReturn (reconnect v) (SmoothKeep ∧ RestrictKeep B)`
  (`firstReturn_firstReturn`) = `firstReturn (reconnect v) (RestrictKeep B)` (the conjunct is implied)
  = `firstReturn succ (RestrictKeep B)`: `(reconnect v)^n u = succ^n u` for every `n` when `comp u ∈ B`
  (all iterates have `comp = comp u ∈ B ∌ comp v, comp (pair v)`, so `swap` acts trivially;
  `comp_pow` LinkRecord 365), hence equal return times (`returnTime_eq_iff`).  `e`: `inl ⟦u⟧ ↦ comp u`
  is NOT the map — components of the restriction are `{c // c ∈ B}`; use `inl ⟦u⟧ ↦ ⟨comp u, _⟩`
  (well defined by `comp_mem_iff…` and, on `B`-cycles, `SameCycle (reconnect v) u w → comp u = comp w`
  since `reconnect = succ` there), `inr f ↦ ⟨f.1,_⟩`; surjectivity: a `B`-circle either carries an
  occurrence (`inl ⟦u⟧`) or is free (`inr`).  **Risk: medium-high.**

### 7.4 Block structure of the smoothing and the step (~330 lines)
* `exists_smoothBlk (D blk x hx) : ∃ blkS : (smooth).comps → Fin q, blkS (inl ⟦u⟧) = blk (compOf u) ∧ blkS (inr f) = blk f.1` (~30).
  `Sum.elim (Quotient.lift (blk ∘ compOf) wd) (blk ∘ Subtype.val)`; `wd` from
  `comp_mem_iff_of_reconnect_sameCycle` applied to `B := blockSet (blk (compOf u))` (`hvB` from `hx`).
* `exists_blocks_of_smoothing (…ι₀) : ∃ blk₀ hblk₀, BlockOrdered D₀ blk₀ ∧ fibre characterisation` (~120).
  `blk₀ := blkS ∘ ι₀.e`.  Surjective: for block `i` pick `k` with `blk k = i`; if some visit `u` has
  `compOf u = k` then `ι₀.e.symm (inl ⟦u⟧)`, else `ι₀.e.symm (inr ⟨k, free⟩)`.  `BlockOrdered`: for `y`
  with strands `s, t` and `blk₀ s.1 < blk₀ t.1`, `u := ι₀.Φ ⟨y, s⟩`, `ι₀.Φ ⟨y, t⟩ = pair u` (`pair_eq`,
  the other strand is `twin`, LinkDiagramRecord 413/442), `ι₀.comp_eq` gives `inl ⟦u.1⟧ = ι₀.e s.1` so
  `blk₀ s.1 = blk (compOf u.1)`; `hord` at `u.1.1` ⇒ `u.1 = underVisit _` ⇒ `record.isOver u.1 = false`
  ⇒ `D₀.record.isOver ⟨y,s⟩ = false` (`ι₀.bit_eq`, `smooth_isOver`) ⇒ `s = underStrand y`
  (`record_isOver_iff` 529, `eq_under_of_mem_of_ne` 523).  Fibre clause by `Quotient.ind`/`Sum.rec` on `ι₀.e c`.
* `stack_init (D blk hblk B h)` (~60): `P_underFirst`; each `blockRestrict D blk hblk i` is UNDER-first
  (`restrict_underFirst B h`), value `δ^{c_i − 1}` with `c_i = (blockSet i).card` (`restrict_componentCount`);
  `Finset.prod_pow_eq_pow_sum`; `∑ i, c_i = c` (`Finset.card_eq_sum_card_fiberwise`, Mathlib
  BigOperators/Group/Finset/Basic.lean 993); `∑ (c_i − 1) = c − q` (each `c_i ≥ 1`, `Finset.sum_tsub_distrib`
  or `Nat.sub` bookkeeping via `Finset.sum_const`, `card_fin`); `δ^{q−1} δ^{c−q} = δ^{c−1}` (`pow_add`, `q ≤ c`).
* `stack_step (…)` (~120): `i₀ := blk (overStrand x).1`; `y` from `exists_blockCrossing`;
  `F := blockRestrict D blk hblk i₀`.  `P D = solvedR pos (P (D.switch x)) (P D₀)` (`solvedR_of_skein`).
  `ihsw` rewritten with `blockRestrict_switch_of_internal` (factor `i₀`: `F.switch y`) and
  `blockRestrict_switch_of_external` (others).  `exists_blocks_of_smoothing` gives `blk₀`; `ih₀ blk₀`.
  Factor `i ≠ i₀`: `(blockRestrict D₀ blk₀ _ i).record ≅ D₀.record.restrict (blockSet₀ i)` (`restrictRecordIso`)
  `≅ (D.record.smooth v).restrict B'` (`ι₀.restrict`, `hB` = fibre clause + `exists_smoothBlock`)
  `≅ D.record.restrict (blockSet i)` (`restrictSmoothDisjointIso`, `comp v ∉ blockSet i` since `blk (compOf v) = i₀ ≠ i`)
  `≅ (blockRestrict D blk hblk i).record` ⇒ `P` equal by `presentations`.  Factor `i₀`:
  `… ≅ (D.record.restrict (blockSet i₀)).smooth ⟨v,_⟩` (`restrictSmoothIso`) `≅ F.record.smooth (ψ.Φ.symm ⟨v,_⟩)`
  (`(ψ.symm).smooth`, `ψ := restrictRecordIso`) `≅ F₀.record` for `F₀` from `exists_smoothing_record_visit F y _ rfl`
  (`ψ.Φ.symm ⟨v,_⟩` has crossing `y` because `restrictVisit_fst` 1226 + `hy`).  So
  `P (blockRestrict D₀ blk₀ _ i₀) = P F₀`, and `P F = solvedR pos' (P (F.switch y)) (P F₀)` with
  `pos' ↔ pos` (`restrict_isPositive_iff` LinkDiagramExtras 585 + `hy`).  Finish:
  `Finset.mul_prod_erase` (Mathlib BigOperators/Group/Finset/Basic.lean 749) on both products,
  `solvedR_mul_left`, `ring`-free `rw`.  **Risk: medium** (bookkeeping heavy; every link exists).

### 7.5 Fallback for mp:stack
If §7.3 stalls: deliver rp, lp:core, split-circle, presentations (they do not depend on §7), and
reduce stack to **q = 2 with an induction on q** — it does NOT remove `restrictSmoothIso`/`DisjointIso`,
so the honest fallback is to land the four rows and keep `stack_step` as the single open leaf with
the 7.2-7.4 unit list above (~700 lines) as its own lane.

## 8. Riskiest steps and fallbacks (whole lane)

1. **`restrictSmoothIso` / `restrictSmoothDisjointIso`** (stack only): dependent-subtype bookkeeping on
   top of two perm lemmas.  Fallback: §7.5.
2. **`restrictSmoothFreeIso`** (split-circle): the same kind of iso in the easy "everything kept" case.
   Fallback: prove the split-circle motive with a `Record.dropFree j` operation (comps `{c // c ≠ j}`,
   same `M`/`succ`), for which the smoothing commutation is `Φ = Equiv.refl` and only `e` needs work;
   then `ρ.restrict (erase j) ≅ ρ.dropFree j` is a one-off (`restrict_succ_val_of_keep`).
3. **`underFirst_of_recordIso`** (rp, presentations, split init): the dependent `Option`-indexed basing
   and the cast `compOf (ι.Φ v₁) = ι.e (compOf v₁)`.  Fallback: state `exists_basing_before` with
   `f : Fin c → Option D.Γ.Visit` plus `hf : f i = some v → compOf v = i` and do the cast once inside.
4. **`cycBetween_cyclicOffset`**: 8-way `split_ifs` × 3 disjuncts each way; mechanical; if `linarith`
   is slow, prove the two rotation lemmas `cycBetween_shift`/`cycBetween_wrap` separately.
5. **`exists_base_before`**: a copy of an accepted 60-line proof; low risk.
6. The relational `IsOrientedSmoothing D x D₀ → RecordIso …` is NOT available (only the constructive
   gate); every step therefore uses the smoothing produced by the gate.  This is why the second
   diagram is inside the motive and why `skein_induction`'s step receives the gate's `D₀`.

## 9. Estimates

| unit | leaves | lines |
|---|---|---|
| U0 ring | 0 (done) | 0 |
| U1 badness | 0 (done) | 0 |
| U2 lp:core assembly | 0 (done; `lp_core` sorry-free) | 0 |
| U3 transport | 8 | 425 |
| U5 restrict_underFirst | 1 | 110 |
| U6 split-circle | 4 | 350 |
| U7 stack | 16 | 1015 |
| **remaining** | **29** | **≈ 1900** |
| skeleton written (defs, principle, proved chain incl. all of lp:core, 5 rows) | 81 theorems | 1042 |

Everything except U7 is ≈ 900 lines; rp / presentations need U3 only (8 leaves), split-circle needs
U3 + U5 + U6 (13 leaves), lp:core needs nothing.
