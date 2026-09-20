# W5_SITE_REPORT — wave 5, unit W5-SITE (prefix `w5s_`): the contact carrier pair data, 2026-09-19 08:46 UTC / 4:46am ET (D-AUTH-20260919, no bound)

File: **`work/drafts/corner/W5_SITE.lean`** (20,219 lines, sha256 `ed43e974e8ef2440eb77ecee11efa1857071186db756b0ca98d4d565a4e23cb8`)
= `W4_Assembled.lean` (19,974 lines, `9c0ec3b7…`, verified) + ONE inserted block of 245 lines (`diff` = `19853a19854,20098`, a pure
insertion, 0 deleted lines), placed inside `section W4Bigon` immediately BEFORE the docstring of the black box `w4_box_returnedRows`
(now at 20102).  20 declarations (18 theorems, 2 defs), all `w5s_`-prefixed, all PROVED.  No frozen statement, name or docstring touched;
no import added; nothing under `work/lean` written.
**Compile** (`cd work/lean && lake env lean ../drafts/corner/W5_SITE.lean`, 42 s): **0 errors, 0 warnings other than the same five
`declaration uses sorry`** as W4 (4437 `s7q_box_ret`, 18053 `s7z_F_exists`, 18494 `s7z_returned_of_FSector`, 20102
`w4_box_returnedRows`, 20167 `s7_bigon_law_at`).  **`grep -c sorry`: 16 before, 16 after** (the block contains no `sorry`, neither as a
body nor as prose).  `tools/stmt_check.py W5_SITE.lean --base W3_Skeleton.lean`: 5/5 PASS; `tail -n 43` identical to `W3_Skeleton.lean`;
`tools/clash_scan.py`: `duplicates_in_assembled: []`, `full_name_clashes: {}` (its `prefix_stats` calls `w5s_` "UNPREFIXED", cosmetic as
for `w4_`).
**Axioms** (`#print axioms` on the scratch copy `<scratchpad>/w5s/Probe3.lean` = the block against the W4 prefix olean): every `w5s_`
theorem checked — `w5s_ContactRowData_e`, `w5s_exists_contactRowData`, `w5s_ContactRowData`, `w5s_site`, `w5s_rotation`, `w5s_qL_eq`,
`w5s_hSS'`, `w5s_x_eq_liftGen`, `w5s_exists_wall`, `w5s_hT`, `w5s_markMap_markMap`, `w5s_hxq'`, `w5s_x_apply` — depends on
**`[propext, Classical.choice, Quot.sound]` only**: no `sorryAx`, no literature axiom.

## 0. In one paragraph

**W5-SITE is CLOSED with no black box.**  The two fields of BLOCK's `s7k_ContactRowData` are instantiated on the actual carriers of
`lift T₀` / `T₀` from material that is already proved: `site` from SITE's `s7s_site` (wall data `s7s_siteData_of_wall` ←
`s7s_wallTriangleData_of_bigon`, SITEC) + SITEH's `s7sh_hrec_prop_side`, cast from the geo lift to the accepted `positiveLift`;
`rotation` from **A2's `s7a2_carrierRotation_eq` applied to the contact carrier itself** — the report's remark "A2's family excludes it"
(W4_ASSEMBLY_REPORT §5) does not apply: A2 requires a PERSISTENT SUPPORT (`hSp`), not that the carrier avoids the contact, and every
corner mark of a carrier of the newborn-free lift is persistent (`s7fc_hSp'`), so A2's corner-polygon family of `q_H` is regular
through the wall (its corners are vertices and selected persistent visits; `x`, `y` are not corners).  Hence no FB2-style family
adaptation and no `s7i_full_rotation_germ` instance were needed, and the unit is 245 lines instead of the estimated 600-1,000.
The consumed shapes were all TRUE as stated; the only bridge lemmas are the direction reversal of FB3's `hSS'` (`w5s_hSS'`) and the
identification of SITEH's `q_L` with FB3's `(s7fc_e …).symm q_H` (`w5s_qL_eq`).

## 1. Delivered (all inside `section W4Bigon`, whose `variable (hn) (g) {M a} (h) (h₁) (h₂)` are in scope; `h₁ h₂` unused)

Vocabulary: `P₂ := g.curve (g.sideTime (s7f_side g M a) t)`, `P₀ := g.curve (g.sideTime (!s7f_side g M a) t)`, `hP₂ := s7f_hP₂ g M a t`,
`hP₀ := s7f_hP₀ g M a t`, `T := s7f_lift hn g h t T₀`.  Section `W5Site` has `variable (t) {r η δ} (hloc : s7a2_IntervalLocal hn g M a r η δ)
(ht : t.val < δ) (T₀) (hT₀ : IsDecomposition hn hP₀ T₀) (qH : Component hn hP₂ T)`; `hloc ht` are `include`d where they enter proofs only.

| line | declaration | statement / role |
|---|---|---|
| 19881 | `w5s_hx hn g h t` | `IsCrossing P₂ {M − 1, a}` (SITE's edge order; `Finset.pair_comm` on `s7f_pattern`) |
| 19886 | `w5s_hy hn g h t` | `IsCrossing P₂ {a, M}` |
| 19889/92 | `w5s_xPair_eq`, `w5s_yPair_eq` | `xPair (w5s_hx …) = s7f_x hn h t` (`Subtype.ext (Finset.pair_comm _ _)`), `xPair (w5s_hy …) = s7f_y hn h t` (`rfl`) |
| 19900 | `w5s_hSS' hn g h t hloc ht T₀` | U110-A's `hSS'` in the direction `P₂ → P₀`: `∀ v : Visit P₂, ∀ hv, (s7a_visit (s7a_side_hs hn g (s7fc_hL hn g t hloc ht) (s7f_side g M a) (!s7f_side g M a)) v hv).1 ∈ T₀ ↔ v.1 ∈ T` (`s7f_mem_lift`, `Subtype.ext`) |
| 19916 | `w5s_hT hn g h t hloc ht T₀ hT₀` | `IsDecomposition hn hP₂ T` (FB3's `s7fc_isDecomposition_lift`) |
| 19923 | **`def w5s_qL hn g h t hloc ht T₀ qH : Component hn hP₀ T₀`** | `s7a_sideComponentEquiv hn g (s7fc_hL …) (s7f_side g M a) (!s7f_side g M a) T T₀ (w5s_hSS' …) (s7fc_hSp' …) (s7fc_hSp …) qH` — SITEH's `q_L` |
| 19930 | `w5s_markMap_markMap hs hs' m hm` | `s7a_markMap hs' (s7a_markMap hs m) = m` for persistent `m` (`rfl` after `s7a_markMap_inr`, structure eta) |
| 19942 | **`w5s_qL_eq hn g h t hloc ht T₀ qH`** | **`(s7fc_e hn g h t hloc ht T₀).symm qH = w5s_qL … qH`** — `Equiv.symm_apply_eq`, then on `m := ccpCornerMark … qH 0` (`ccpCornerMark_owner`, persistent by `s7a_isTrueCorner_persistent … (s7fc_hSp' …)`) both transports are `s7a_sideComponentEquiv_owner` and the mark maps cancel |
| 19960/66 | `w5s_hxq' … qH hxq`, `w5s_hyq' … qH hyq` | `xPair (w5s_hx …) ∈ geoCarrierCrossings (s7s_cg hn hP₂).cg T (s7s_geoComp hn hP₂ T qH)` from `hxq : s7f_x hn h t ∈ carrierCrossings hn hP₂ T qH` (`s7s_mem_geoCarrierCrossings_iff`); same for `y` |
| 19973 | **`def w5s_x hn g h t T₀ qH hT hxq : (positiveLift hn hP₂ T qH hT).Γ.Crossing`** | `(carrierCrossingEquiv hn hP₂ T qH hT).symm ⟨s7f_x hn h t, hxq⟩` — the contact crossing of the high lift |
| 19978 | `w5s_x_apply` | `carrierCrossingEquiv … (w5s_x …) = ⟨s7f_x hn h t, hxq⟩` |
| 19985 | `w5s_x_eq_liftGen` | `w5s_x … = s7s_liftGen hn hP₂ T hT qH _ (w5s_hxq' …)` (`s7s_liftGen_eq_carrierCrossingEquiv`) |
| 19999 | **`w5s_site hn g h t hloc ht T₀ hT₀ qH hW hT hxq hyq`** | **field `site`**: `∃ B : BigonData ((positiveLift hn hP₂ T qH hT).switch (w5s_x …)), Nonempty (RecordIso B.reducedRecord (positiveLift hn hP₀ T₀ (w5s_qL … qH) hT₀).record)` — `hW : s7s_WallTriangleData P₂ M a (w5s_hx …) (w5s_hy …)` |
| 20035 | **`w5s_rotation hn g h t hloc ht T₀ qH hT`** | **field `rotation`**: `|carrierRotationInt hn hP₂ T qH| = |carrierRotationInt hn hP₀ T₀ (w5s_qL … qH)|` (`s7a2_carrierRotation_eq hn g h.1 hloc ht (s7fc_hL …) (s7f_side g M a) (!s7f_side g M a) T T₀ (w5s_hSS' …) (s7fc_hSp' …) (s7fc_hSp …) hT qH`, then `unfold carrierRotationInt w5s_qL; rw`) |
| 20046 | **`w5s_ContactRowData hn g h t hloc ht T₀ hT₀ qH hW hT hxq hyq`** | `s7k_ContactRowData hn hP₂ hP₀ hT hT₀ qH (w5s_qL … qH) (w5s_x …)` := `⟨w5s_site …, w5s_rotation …⟩` |
| 20058 | **`w5s_ContactRowData_e hn g h t hloc ht T₀ hT₀ qH hW hT hxq hyq`** | **the report's shape**: `s7k_ContactRowData hn hP₂ hP₀ hT hT₀ qH ((s7fc_e hn g h t hloc ht T₀).symm qH) (w5s_x hn g h t T₀ qH hT hxq)` (`rw [w5s_qL_eq]`) |
| 20074 | `w5s_exists_wall hn g h` | `∃ δ > 0, ∀ t, t.val < δ → s7s_WallTriangleData P₂ M a (w5s_hx …) (w5s_hy …)` (`s7s_wallTriangleData_of_bigon` at `b := s7f_side g M a`; `(g.sideTuple b t).1 ≡ g.curve (g.sideTime b t)` definitionally) |
| 20082 | **`w5s_exists_contactRowData hn g h`** | `∃ δ > 0, ∀ t, t.val < δ → ∀ {r η δ'} (hloc : s7a2_IntervalLocal hn g M a r η δ') (ht : t.val < δ') T₀ hT₀ hT qH hxq (_hyq), s7k_ContactRowData hn hP₂ hP₀ hT hT₀ qH ((s7fc_e hn g h t hloc ht T₀).symm qH) (w5s_x hn g h t T₀ qH hT hxq)` |

## 2. How to consume (W5-ROW / W5-BR)

* Per `t`: hold `hloc ht` (from `s7a2_exists_intervalLocal hn g M a h.1`, the same pair that names `s7fc_e`), take `T₀ ∈ w4_EligDec hn g h t`
  (so `hT : IsDecomposition hn hP₂ T` is `((w4_mem_EligDec …).mp hmem).2` and `hT₀ := (s7fc_isDecomposition_lift hn g h t hloc ht T₀).mp hT`),
  the contact carrier `qH` of `T` with `hxq hyq : s7f_x/y hn h t ∈ carrierCrossings hn hP₂ T qH` (W5-RT's vocabulary), the wall datum
  `hW` from `w5s_exists_wall` below its radius; then `w5s_ContactRowData_e … : s7k_ContactRowData hn hP₂ hP₀ hT hT₀ qH ((s7fc_e …).symm qH) (w5s_x …)`
  feeds `s7k_interlacing_row` / `s7k_noninterlacing_row` / `s7k_different_block_row` as their `hc` (with `x := w5s_x hn g h t T₀ qH hT hxq`).
  `w5s_exists_contactRowData` packages the radius.
* `hP₂ = s7f_hP₂ g M a t` and `s7a_sideGeneric g (s7f_side g M a)` (also `(g.sideTuple _ _).property`) are proofs of one Prop, so the
  `w5s_` statements unify with either spelling by `exact` (proof irrelevance); likewise `hT`, `hT₀`.
* The skein at `x` (`s7k_skein_on`, W5-ROW) needs a visit `v` with `v.1 = w5s_x …`; `w5s_x_apply` / `w5s_x_eq_liftGen` give `x`'s two
  readings (`carrierCrossingEquiv` inverse at `s7f_x`; SITE's `s7s_liftGen` at `xPair (w5s_hx …)`), and `crossingPoint_carrierCrossingEquiv`
  its point.  For `D_A` (W5-BR) use `s7s_cornerHomfly_skein` or `s7g_cornerHomfly_skein` at `w5s_x`, as BLOCK's design says.
* If a consumer holds `q_L` as `w5s_qL … qH` (SITEH's orientation), `w5s_ContactRowData` is the version without the `symm`; `w5s_qL_eq`
  converts.  `w5s_qL_eq` also gives the spectator bookkeeping of W5-RT the identity `s7fc_e (w5s_qL qH) = qH`.

## 3. Consumed (all PROVED in `W4_Assembled.lean` or the library; nothing sorried, nothing believed false)

SITE `s7s_site`, `s7s_siteData_of_wall` (→ SITEC's `s7s_clear_local`, `s7s_wallTriangleData_of_bigon`), `s7s_reducedRecord_eq`,
`s7s_mem_geoCarrierCrossings_iff`, `s7s_liftGen_eq_carrierCrossingEquiv`, `s7s_switch_castCrossing`, `s7s_geoPositiveLift_eq`, `s7s_cg`,
`s7s_geoIndependent`, `s7s_geoComp`, `s7s_liftGen`, `s7s_lift`; SITEH `s7sh_hrec_prop_side`; FB3 `s7fc_e`, `s7fc_hL`, `s7fc_hSp`,
`s7fc_hSp'`, `s7fc_isDecomposition_lift`; F `s7f_pattern`, `s7f_x`, `s7f_y`, `s7f_lift`, `s7f_mem_lift`, `s7f_hP₂`, `s7f_hP₀`, `s7f_side`;
A2 (`SM.CS7Sliding`) `s7a2_carrierRotation_eq`, `s7a2_IntervalLocal`; U110-A (`SM.CornerChainUnits`) `s7a_sideComponentEquiv`,
`s7a_sideComponentEquiv_owner`, `s7a_side_hs`, `s7a_visit`, `s7a_visit_support`, `s7a_markMap`, `s7a_markMap_inr`, `s7a_markMap_persistent`,
`s7a_isTrueCorner_persistent`, `s7a_Persistent`; library `ccpCornerMark_owner`, `ccpCornerMark_isTrueCorner`, `carrierCrossingEquiv`,
`carrierRotationInt`, `BigonData.reducedRecord`, `RProof.xPair`.  **Black boxes stated: none.**  No shape consumed was false as stated;
the report's SUGGESTED route for `rotation` (an FB2-style family or `s7i_full_rotation_germ_centre`) was not needed because A2's theorem
already covers the contact carrier (§0).

## 4. Method audit (reassessment discipline)

No lemma needed a second attempt.  Probe 1 (block 1 only) had three elaboration slips fixed in one pass — missing `include hn h in` on
`w5s_hx/hy` (statements mention only `g t`), an under-determined visit argument in `s7a_markMap_inr hs' _ hm` (pass `(s7a_visit hs v hm)`),
and the persistence side goal of the last `rw [w5s_markMap_markMap]` (pass `_ _ m hpers`); probe 2 (the whole block) compiled with 0 errors
and one unused-binder linter note (`hyq` → `_hyq` in the radius wrapper).  Then the full file compiled first time.  Timeline: 08:21 UTC
start (assembly report §3-5, BLOCK/SITE/SITEH/FB3/A2/U110-I interfaces); 08:31 signature probe against the W4 prefix olean
(`<scratchpad>/w4/pfx/W4Prefix.olean`, 20 s per probe); 08:37 probe 1; 08:40 probe 2 clean; 08:42 `W5_SITE.lean` compiles; 08:44 axioms,
stmt/clash checks; 08:46 report.

## 5. Lean pitfalls hit (v4.34.0-rc2 pin)

1. `rw [lemma_with_hyp]` where the hypothesis argument is left to unification creates a NAMED side goal (`case hm`) rather than failing;
   pass the proof explicitly.
2. `s7a_markMap_inr hs' _ hm` with `hm : s7a_Persistent M a (Sum.inr v)`: the expected type `¬ContactAffected M a ↑(Sigma.fst ?m)` is not
   unfolded against the metavariable; give the visit.
3. `rw` under a bound `∃ B : BigonData (D.switch x), …` works (motive abstracts the diagram / the crossing uniformly); the equality
   `D'.switch (s7s_liftGen …) = D.switch (s7s_lift …)` is `s7s_switch_castCrossing _ _` by unfolding the `def` `s7s_liftGen`.
4. `unfold carrierRotationInt w5s_qL; rw [hrot]` matches `carrierRotation hn (s7f_hP₂ g M a t) …` against A2's
   `carrierRotation hn (s7a_sideGeneric g _) …` (proof-irrelevant arguments unify inside `rw`).

## 6. Notes for the assembler

* Pure insertion `19853a19854,20098` inside `section W4Bigon` (uses its `hn g h`; `h₁ h₂` unused, not `include`d); nested sections
  `W5Site` (per `t`) and `W5SiteRadius`; may be moved anywhere after FB3, SITEC, SITEH and BLOCK (it references no `w4_` name).
* The unit closes nothing of the frozen file (its content is an input of W5-ROW); the black box `w4_box_returnedRows` and the leaf keep
  their `sorry`, so `grep -c sorry` is unchanged at 16 and `thm_C_S7` still carries `sorryAx` through the leaf only.
* Reproduce: `cd work/lean && lake env lean ../drafts/corner/W5_SITE.lean` (0 errors; 5 × sorry notes at 4437 18053 18494 20102 20167);
  axioms: `<scratchpad>/w5s/Probe3.lean` against the W4 prefix olean.
