# W3D_RESID_REPORT — W3D unit RESID (`w3di_`): the IDENTIFICATION clause of `w3cx_outer_residue`

Prover (subagent), 2026-09-19, 05:40Z → 07:30Z / 1:40am → 3:30am ET.  No time bound (D-AUTH-20260919 §2).
File: `work/drafts/moves/W3D_RESID.lean` = `W3C_Assembled.lean` (16 945 lines, 1428 declarations) + ONE import line
(`import RProof.ExtremeTransportUnits`, line 8) + ONE block (`section W3DI_RESID … end W3DI_RESID`, lines
16435–18970, 97 `w3di_`-prefixed declarations, ≈ 2 530 lines) inserted inside `section W3CK_Outer`
immediately before the leaf, + the leaf body `w3cx_outer_residue_data : w3cx_outer_residue := w3di_outer_residue_proof`
(line 18974; was `by sorry`).  19 493 lines, 1525 declarations, sha256 `9c78d56a73cffc59…`.  Nothing frozen
edited (statements, names, docstrings; the five frozen blocks IDENTICAL; 40/42 skeleton statements byte-identical, the two
others the deliberately restated `w3g_` sub-leaves of Wave 3c); nothing under `work/lean` written; no `lake build`.

## 0. Result in one paragraph

**The identification clause is PROVED on registered axioms only.**  `w3di_ident_at` (line 18822) proves, at every
configuration of `w3cx_outer_residue` and for every `Λ` with the parity `#w3cb_mixedSet Q' (Q' ∪ T') q₀' = 2Λ`, the clause
`w3ck_three_components_ident_occ (carrierDiagram q₀') (pt x_ef') (pt x_eg') Λ (groupedPoly w3ca_A) (groupedPoly w3ca_B)
(groupedPoly w3ca_C)` — i.e. for every `x_L` over `x_ef'`, every oriented smoothing `D_L0` with an occurrence-compatible
record clause, every `y_L` of `D_L0` over `x_eg'` and every `J_L` record-isomorphic to the second smoothing:
`twoLambda J_L = 2Λ` and a bijection `σ : Fin 3 ≃ Fin J_L.Γ.c` with `homfly (J_L.knotRestrict (σ i)) = groupedPoly A / B / C`.
`#print axioms w3di_ident_at = [propext, Classical.choice, Quot.sound, lit_homfly, lp_lm, lp_lm_uniqueness]` — no
`sorryAx`.  The parity clause (unit RESPAR) is the black box `w3di_parity : Prop` / `w3di_parity_data` (one `sorry`,
line 18812; binders = those of `w3cx_outer_residue`).  `w3di_outer_residue_proof : w3cx_outer_residue`
(line 18962) combines the two at the same `Λ`, and the leaf `w3cx_outer_residue_data` now has this body: its only
`sorryAx` source is `w3di_parity_data`.  **`sorry` terms 4 → 4** (the residue's term moved into the parity box);
`w3ck_extreme_selected`'s `sorryAx` sources are now exactly `w3di_parity_data` (RESPAR) and `w3cs_not_kink_site_data` (SITE).

## 1. Compile and checks (mandated)

* `cd work/lean && lake env lean ../drafts/moves/W3D_RESID.lean`: **exit 0, 0 errors**, 51–63 s wall over three runs (the base alone
  took 51 s in this session; the block adds little — its declarations are record-level or `omega`-closed).  Warnings: the inherited deprecations
  (`if_pos/if_neg/dif_pos/dif_neg`), the inherited unused-variable lints, `unusedSectionVars` lints of the new block, and
  exactly **4 `declaration uses sorry`**: 4094 `w3b_reparam_switch`, 11690 `w3bi_esc_outer_data`, 13746
  `w3cs_not_kink_site_data`, 18812 `w3di_parity_data`.  (`w3cx_outer_residue_data` at 18974 is no longer a `sorry` declaration.)
* `grep -c sorry`: **6 before → 6 after**: 4 terms (4096, 11691, 13747, 18813) + the 2 inherited prose mentions
  (7857, 14707).  The block's prose never uses the word.
* `check_W3_identity.py Port_GenericTransportSw_draft.lean W3D_RESID.lean`: `structure G11_ConfigSw` 1206 B, `namespace
  G11_ConfigSw` block 1252 B, `def G11_core_sw_statement` 1015 B, `theorem G11_core_sw` statement 136 B, `theorem
  esc_switch_riii_of_chain` 694 B — all **IDENTICAL**; `imports = draft's + SM.BigonDeletion: False` (inherited: the
  `RProof.RALedgers` import of Wave 3b; now also `RProof.ExtremeTransportUnits`, §5); `G11_core_sw body starts with sorry:
  False` (inherited: the core is proved).
* `check_W3_statements.py W3D_RESID.lean`: skeleton statements 42, in target 42, **byte-identical 40**, differing =
  `['w3g_bigonData_smooth_arcST', 'w3g_bigonData_smooth_arcTS']` (the Wave-3c restatements, W3C §1.2), `w3a_` 20/20, no
  missing name.
* `clash_scan_W3.py work/lean W3D_RESID.lean`: 1525 declarations, 1525 distinct fully-qualified names, 0 internal
  duplicates, **0 fully-qualified clashes**; 925 informational short-name coincidences (the inherited `G11_ParamsSw` ↔
  `RProof.G11_Params` ones; none from the new import — the `r176*_` / `s176_` / `est_` names are used qualified-free under
  the existing `open RProof`).
* `#print axioms` (scratch copy `W3D_Axioms_scratch.lean` = the file + 28 `#print axioms` lines before `end SM.Link`,
  compiled from this directory, 0 errors, deleted; output `W3D_AXIOMS.log` next to this report):
  | declaration | axioms |
  |---|---|
  | **`w3di_ident_at`**, `w3di_ident_abstract`, `w3di_ident_β`, `w3di_ident_γ`, `w3di_core` | `[propext, Classical.choice, Quot.sound, lit_homfly, lp_lm, lp_lm_uniqueness]` — no `sorryAx` (the HOMFLY axioms enter only through `r176s_homfly_eq_groupedPoly` / `r176s_homfly_of_liftBlock` / `r176c_homfly_of_liftBlock_curl`) |
  | `w3di_count`, `w3di_double_exists`, `w3di_arcs_ident`, `w3di_kinks`, `w3di_KB_iff`, `w3di_posData_exists`, `w3di_owner_α_iff`, `w3di_arcBetween_restrictCrossings_iff`, `w3di_restrictRestrictIso`, `w3di_restrictRestrictBlockIso`, `w3di_rsIso`, `w3di_rdIso`, `w3di_twoLambda_eq_card`, `w3di_pattern'`, `w3di_not_succ_of_mirror` | `[propext, Classical.choice, Quot.sound]` |
  | `w3di_parity_data` | `[propext, sorryAx, Classical.choice, Quot.sound]` |
  | `w3di_outer_residue_proof`, **`w3cx_outer_residue_data`**, `w3ck_split_ident_data`, `w3cb_split_core_data`, `w3ck_esc_outer_occ_holds` | standard + `lit_homfly, lp_lm, lp_lm_uniqueness` + `sorryAx` (through `w3di_parity_data` ONLY) |
  | `w3ck_extreme_selected`, `w3bi_extreme_selected` | `[propext, sorryAx, Classical.choice, Quot.sound, lit_homfly, lit_homfly_descent, lp_lm, lp_lm_uniqueness, ng_finite_word, src_contact]` (unchanged list; `sorryAx` now from `w3di_parity_data` and `w3cs_not_kink_site_data`; `w3bi_extreme_selected` in addition from `w3bi_esc_outer_data`) |
  No unregistered axiom anywhere.
* Iteration: private scratch dir `…/scratchpad/w3di/` (`T1`–`T6.lean`, standalone files importing `SM.BigonDeletion`,
  `RProof.RALedgers`, `RProof.ExtremeTransportUnits`; 9–25 s each); the configuration wrapper (§2 D) was iterated in the
  full file (3 compiles).

## 2. What is PROVED (file order; line = declaration)

**R0 (16703–16780) the two mp:stack isomorphisms as definitions.**  `Record.restrictSmoothIso` /
`restrictSmoothDisjointIso` are `Nonempty` theorems, so their occurrence maps are opaque; the identification needs them to be
the identity on the underlying occurrences.  `w3di_rsIso` (16703) and `w3di_rdIso` (16760) are `def`s with
`Φ := ρ.rsOccEquiv …` / `ρ.rdOccEquiv …` (the library's own equivalences) and bodies = the accepted proofs of
`Record.restrictSmoothIso'` / `restrictSmoothDisjointIso'` (SM/Stack.lean 855–905, 590–621) verbatim; `w3di_rsIso_Φ_val`,
`w3di_rdIso_Φ_val` are `rfl`.

**R1–R3 (16444–16671) restriction lemmas the library lacks.**  `w3di_restrictRestrictIso` (16492):
`(ρ|K)|K' ≅ ρ|K''` with `K'' = w3di_innerKeep ρ K K'` (the crossings of `K` whose chord in `ρ|K` is in `K'`;
`w3di_crossKeep_innerKeep_iff`) — the general form of `r176c_restrictRestrictIso`, same proof shape
(`firstReturn_congr_pred` + `restrictCrossings_firstReturn_val`).  `w3di_restrictRestrictBlockIso` (16539):
`(ρ|B)|B₁ ≅ ρ|B₂` for blocks (`B₂` = `B₁` read in `ρ.comps`, given by a membership predicate to avoid `Finset.map` through
the subtype).  **`w3di_arcBetween_restrictCrossings_iff`** (16671): on a one-circle record the cyclic
order of three retained occurrences in `ρ|K` is their cyclic order in `ρ` — via the position function `w3di_pos x k :=
ρ.steps x ((ρ|K).succ^k x)` which is strictly increasing below `#(ρ|K).M` (`w3di_steps_rsucc`: the restricted successor
adds the return time without wrap-around, from `returnTime_le_steps`, `steps_eq_of_base`, `steps_eq_iff`).

**R4 (16805–17048) the three components of a double smoothing.**  `structure w3di_DoubleData ρ v w'` (16874):
components `κB κ₁ κ₂` of `J := (ρ.smooth v).smooth w'`, pairwise distinct, `count3`, crossing sets `K₁ K₂` with
`keep₁/keep₂` (`CrossKeep K₁ u ↔ (ArcA v u ∧ ArcA v τu) ∧ (ArcBetween w u τw ∧ ArcBetween w τu τw)`, `keep₂` with `τw, w`
exchanged — all read in `ρ`), the three restriction isomorphisms `J.restrict {κ} ≅ ρ|K_B / ρ|K₁ / ρ|K₂`, and
`RestrictKeep {κ} m ↔ CrossKeep K_κ m.1.1` (`rkB rk₁ rk₂`).  **`w3di_double_exists`** (16908) builds it for `w'`
with both ends on the arc `A = (v → τv)`: the `A`-side chain `J.restrict B' ≅ (σ.restrict smoothB).smooth w'' ≅
ρ_A.smooth w₃` (`w3di_rsIso`, `r176s_smoothRestrictIso`, `RecordIso.smooth`) restricted to the two components of the
one-circle `ρ_A := ρ|K_A` (`r176s_smoothRestrictIso`/`'` again) and pulled back to `ρ` by R1, with the arcs of `ρ_A`
read in `ρ` by R3; the `B`-side by `w3di_rdIso` + `r176s_smoothRestrictIso'`, its block a singleton by the circle count
(`Finset.card_eq_of_equiv`).  `w3di_block_exists` supplies the blocks over a block through `Record.smoothBlock`.

**G (17062–17926) the word on the contact carrier.**  `structure w3di_WordData hP Q S q₀ α₁ α₂ β₁ β₂ γ₁ γ₂`
(17062): twins, distinct crossings outside `Q`, `S = Q ∪ {α, β, γ}`, the three adjacencies `σ α₁ = β₁`, `σ β₂ = γ₁`,
`σ γ₂ = α₂` (the word `α₁ β₁ | X | β₂ γ₁ | Y | γ₂ α₂ | W`), `α₁` on `q₀`, and the three outer `S`-carriers `owner_S α₁`,
`owner_S β₂`, `owner_S γ₂` pairwise distinct.  `w3di_PosData` (17147) / **`w3di_posData_exists`** (17215): the
positions `α₁ = 0, β₁ = 1, β₂ = p, γ₁ = p+1, γ₂ = r, α₂ = r+1` on the `Q`-orbit of `α₁` with `1 < p`, `p+1 < r`,
`r+1 < N` (`r176o_exists_pow`, `r176o_pow_inj`; the ORDER `p < r` from the distinctness of the outer carriers by
`r176o_orbit_transfer`: `r < p` would put `β₂` on the carrier of `α₁`).  `w3di_agree` (17175): off the six visits the
`S`-successor is the `Q`-successor.  **`w3di_owner_α/β/γ_iff`** (17322, 17364, 17404): `owner_S m = owner_S α₁ ↔ i = 0 ∨
r+1 < i`, `= owner_S β₂ ↔ i = p ∨ 1 < i < p`, `= owner_S γ₂ ↔ i = r ∨ p+1 < i < r` (`r176o_sameCycle_transfer_iff`).
`w3di_mem_S_iff` (17443): a retained visit is at a crossing of `S` iff its index is one of the six.  On the lift:
`w3di_arc_idx` (17523) `ρ.ArcBetween x u y ↔` the index order (`CV.arcBetween_iff_key` + `r176o_cyc_iff`;
`geometricVisitKey = geoMarkKey ∘ inr` by `rfl`), `w3di_SixLift` (17599) the six occurrences of the lift, `w3di_arcs_idx`
(17650) the six arcs of the record as index intervals, `w3di_occ_idx` (17682) the index data of an occurrence and its
twin (incl. the six twin relations `i = r → i' = p+1` etc.), **`w3di_KB_iff`** (17559) `K_B(v ↦ α₁) = liftBlock (gCC S
(owner_S α₁))`, **`w3di_arcs_ident`** (17747) the four `A`-side arc conditions = the blocks of `owner_S β₂`, of `owner_S γ₂`
∪ the chord of `γ`, of `owner_S γ₂`, of `owner_S β₂` ∪ the chord of `β` (all by `omega` on the indices),
`w3di_arcA_of_βγ` (17813) the four `β, γ` visits lie on `A`, **`w3di_kinks`** (17836) in `ρ|(block γ₂ ∪ {χ_γ})` the successor
of `c₂` is `c₁`, likewise for `β` (the kink of `r176c_homfly_of_liftBlock_curl`; trichotomy + `not_arcBetween_firstReturn`).

**A (17919–18001) `2Λ` = the mixed crossings.**  `w3di_twoLambda_eq_card` (17971): on an all-positive diagram
`twoLambda D = #{x | (overStrand x).1 ≠ (underStrand x).1}` (`r176l_mixedSignSum_eq_card` summed over the unordered pairs,
`w3di_pair_sum`).

**B (18020–18652) the assembly.**  `w3di_owner_cover` (18037), `w3di_owner_eq_iff` (18054) (off `S`: the two visits of a retained
crossing have the same `S`-owner iff it is a retained crossing of one of the three outer carriers),
`w3di_isSelfCrossing_iff_restrictKeep` (18083), `w3di_exists_equiv_fin3` (18097).  **`w3di_count`** (18122):
`twoLambda J_L = #w3cb_mixedSet Q S q₀` — the mixed crossings of `J_L` are the chords of the lift with occurrences on
different components, and (`Finset.card_bij` through the label `liftVisit`) these are exactly the retained crossings of
`q₀` off `S` whose two visits have different `S`-owners; the chord of the third triangle crossing is the kink, hence self.
**`w3di_core`** (18366): from components with identified crossing sets, the count and `∃ σ` with the three `homfly`
(`r176s_homfly_of_liftBlock` twice, `r176c_homfly_of_liftBlock_curl` once).  **`w3di_ident_β`** (18472) /
**`w3di_ident_γ`** (18572): the second smoothing at `β` (resp. `γ`), each in the two sub-cases `y ↦ b₁ / b₂` (the roles of
`κ₁, κ₂` exchanged).

**C (18683) `w3di_ident_abstract`**: the clause in occurrence form for the lift of the contact carrier of any word
data — the over occurrence of `x_L` is normalised to the `α₁` occurrence through `Record.smoothPairIso` when it lies over
`α₂`.

**D (?–18970) the configuration.**  `w3di_pattern'` (?): SPLITA's `w3ca_pattern` with the support given by its
membership predicate (the classical-`insert` bridge, as `w3ca_core` does it); `w3di_not_succ_of_mirror` (18772): in the
mirror pattern `σ a₁ ≠ b₁` (a 2-cycle of the mark circle would exclude `c₁`).  **`w3di_ident_at`** (18822): pattern P1
(`σ a₁ = b₁ ∧ σ b₂ = c₁ ∧ σ c₂ = a₂`) gives the word data with `(α, β, γ) = (a, b, c)` and `w3ca_A/B/C = owner_S a₁ / b₂
/ c₂`; pattern P2 (`σ b₁ = a₁ ∧ σ c₁ = b₂ ∧ σ a₂ = c₂`) gives it with `(α, β, γ) = (a, c, b)` (visits `a₂, a₁, c₂, c₁,
b₂, b₁`) and `w3ca_A/B/C = owner_S a₂ / b₁ / c₁`; the outer-carrier distinctness is SPLITA's `core.distinct`
(`w3ca_split_config`), `q₀'` owns `a₁` by `esc_not_triangleDisjoint_iff` + `w3ca_six_on_contact`; `r176s_homfly_eq_groupedPoly`
at `X := geoPositiveLift …` with `RecordIso.refl` reads each lift as `groupedPoly` (`carrierDiagram` unfolds to the same
lift; the independence proofs are irrelevant).  **`w3di_outer_residue_proof`** (18962) and the leaf body.

## 3. The black box (unit RESPAR) and how it is wired

`def w3di_parity : Prop` (18791) = `w3cx_outer_residue` with the identification conjunct dropped: under exactly the
residue's binders, `∃ Λ, (w3cb_mixedSet (geomAt E t' ht'.1) (transportSupport hs Q) (transportSupport hs Q ∪
triangleCrossings (E.curve t') e f g) q₀').card = 2 * Λ`.  `theorem w3di_parity_data : w3di_parity := by sorry`
(18812).  Consumer: `w3di_outer_residue_proof` destructures it and feeds `Λ, hpar` to `w3di_ident_at`.  For the
assembler: RESPAR's proof replaces the body of `w3di_parity_data` (or, if RESPAR states its own Prop, a one-line bridge to
`w3di_parity`); nothing else changes.  `w3di_ident_at` takes `Λ` and the parity equation as HYPOTHESES, so it is usable
with any parity proof.

## 4. Leaf status

| decl | line | status |
|---|---|---|
| `w3cx_outer_residue_data : w3cx_outer_residue` | 18974 | body `:= w3di_outer_residue_proof`; `sorryAx` only through `w3di_parity_data` |
| `w3di_parity_data : w3di_parity` | 18812 | OPEN — unit RESPAR's clause, verbatim |
| `w3cs_not_kink_site_data`, `w3bi_esc_outer_data`, `w3b_reparam_switch` | 13746, 11690, 4094 | untouched (other units / superseded / optional) |

Chain: `w3ck_extreme_selected := w3ck_esc_ledger w3ck_esc_interface_ext_occ_holds CV.carrierSlotFloor`, …,
`w3ck_split_ident_data := w3cx_split_ident_of_residue w3cx_outer_residue_data`, `w3cx_outer_residue_data :=
w3di_outer_residue_proof`, whose `sorryAx` is `w3di_parity_data`.  So the `sorryAx` sources of `w3ck_extreme_selected`
are now exactly **`w3di_parity_data` (RESPAR) and `w3cs_not_kink_site_data` (SITE)**.

## 5. Rules, findings, reassessment

* Rule (1): no existing statement, name or docstring edited; only the leaf body replaced; all new material `w3di_`.
  ONE header change: `import RProof.ExtremeTransportUnits` (line 8), the accepted row-176 module the task names as
  importable; it is required for `r176s_smoothRestrictIso`, `r176s_homfly_of_liftBlock`, `r176c_homfly_of_liftBlock_curl`,
  `r176l_mixedSignSum_eq_card`, `r176o_exists_pow / pow_inj / cyc_iff / sameCycle_transfer_iff / orbit_transfer /
  crossing_set_ext`, `r176s_KA/KB`, `r176s_smooth_comp_eq_pair_iff`.  The identity checker's `imports` line was already
  `False` (Wave 3b's `RProof.RALedgers`); the port plan (W3C §7) is unaffected (`RProof/ExtremeSelectedUnits.lean` may import
  `RProof.ExtremeTransportUnits`, an accepted module).  No name clash (§1).
* Rule (2): the parity clause is the black box `w3di_parity_data` (§3); no other unit's leaf touched.
* Rule (3): **the leaf is TRUE as stated**: both clauses hold at every configuration (the identification unconditionally,
  the parity by RESPAR); no corrected form needed.  In particular the record-clause form `w3ck_three_components_ident_occ`
  is exactly what the geometry gives; `twoLambda J_L = 2Λ` holds with the parity's `Λ` because the mixed crossings of `J_L`
  are the `2Λ` mixed retained crossings (§2 B), all positive.
* Rule (4) reassessment audits (after two failed attempts, method changed):
  1. the occurrence-identity of the composed A-side isomorphism (`rfl` failed twice): cause found by bisection — the
     `Nonempty` Stack theorems hide their `Φ`; method changed to R0 (the isomorphisms as `def`s with the library's
     `rsOccEquiv`/`rdOccEquiv`), after which the whole chain is `rfl`;
  2. the heartbeat timeout of `w3di_count`: bisected to `congr 1` on the cast cardinality equation (it tries `rfl`, hence
     `whnf` of two `Finset.card`s of filters over the crossings) — replaced by `Nat.cast_inj`; and a second `whnf`
     timeout from `exact geoPositiveLift_sign … _` unifying through the positive lift — replaced by a syntactic `rfl`
     equation for the two `smooth_sgn` layers + `rw [Diagram.record_sgn]`;
  3. `tauto` on a disjunction of crossing equalities (the P2 `hSeq'`) timed out — replaced by the explicit shuffle.
  No lemma failed for a mathematical reason.
* Estimate: the task's 0.4–0.8k; actual ≈ 2.5k lines.  The excess is the record-level infrastructure the library lacked
  (R0–R4 ≈ 0.9k: two isomorphism `def`s, restriction-of-restriction twice, arc inheritance, the double-smoothing
  components) and the four-case geometry (G ≈ 0.9k, needed once per pattern per smoothed occurrence).

## 6. Pitfalls / notes for the assembler and the porter

* `Record.restrictSmoothIso` / `restrictSmoothDisjointIso` return `Nonempty`; whenever the underlying occurrence map
  matters, use `w3di_rsIso` / `w3di_rdIso` (or, at port time, expose the library's construction as a `def`).
* `rw` fails "at implicit transparency" on nested subtypes of `Record.M` (`(ρ.restrictCrossings K).M` vs
  `{v // …}`, `(ρ.smooth x).comps` vs `Quotient … ⊕ FreeComp`): use term-mode `.mp/.mpr` applications, `change`, or
  the library's `hmem … .trans Iff.rfl` idiom (Stack.lean 1249–1262) for block membership.
* `congr 1` on `((s.card : ℕ) : ℤ) = ((t.card : ℕ) : ℤ)` for filters over crossings hits the heartbeat limit (it tries
  `rfl` first); `rw [Nat.cast_inj]`.  `exact geoPositiveLift_sign … _` against a record `sgn` likewise: state the
  `smooth_sgn` unfolding as an explicit `rfl` equation and `rw [Diagram.record_sgn]`.
* `w3ca_pattern` and everything in `section W3CA_Core` is stated with the classical `insert`; from the configuration
  (`RProof.instDecidableEqCrossing`) reach it through a lemma in a classical sub-section that takes the membership predicate
  (`w3di_pattern'`, the `w3ca_core` idiom) — never `▸` a Finset equality across the two instances.
* `w3ca_A/B/C` unfold to `if σ a₁ = b₁ then … else …`: `simp only [w3ca_A, w3ca_Ac, h1, ↓reduceIte]` (P1) and with
  `hn1 : ¬ σ a₁ = b₁` from `w3di_not_succ_of_mirror` (P2); `rw [if_pos]` rewrites only the first `if`.
* `hλ` is not an identifier (`λ` is a token).  `omega` needs the `w3di_PosData` bounds and the twin-index relations of
  `w3di_occ_idx` in the context (both indices of a chord are needed for every set identity).
* `geometricVisitKey hP v = geoMarkKey hP (Sum.inr v)` is `rfl`; `CV.carrierDiagram hn hG hS q` unfolds to `geoPositiveLift
  hn (CarrierGeometry.ofDiagrammatic (hG.diagrammatic hn)) (geoIndependent_of_mem_Ind _ hS) q`, and every `GeoComponent hP …`
  / `GeoComponent hG.cg …` coincidence is by proof irrelevance (`exact`/application see it, `rw` does not).
* Port: the block is self-contained under `RProof.ExtremeTransportUnits` + the SPLITA/SPLITB/KNOT material it consumes
  (`w3ca_SixData`, `w3ca_pattern`, `w3ca_sixData_config`, `w3ca_split_config`, `w3ca_six_on_contact`, `w3ca_visit_six`,
  `w3ca_A/B/C`, `w3cb_mixedSet`, `w3ck_three_components_ident_occ`, `w3ck_IdentData`); it belongs in
  `RProof/ExtremeSelectedUnits.lean` after them (W3C §7).  The docstrings of the block are reworded-`sorry`-free.

## 7. Times (UTC / ET)

05:40 / 1:40am start (author response already recorded 05:36Z; reading the register, W3C/KNOT/SPLITA/SPLITB reports, the
r176 library); 06:05 design fixed (record-level chain + word geometry); 06:15 T1 (R1–R3) compiled; 06:30 T2 (R4) after
the Stack-`Nonempty` finding; 06:45 T3 (G) compiled; 06:55 T4 (A); 07:05 T6 (B, C) compiled; 07:10 first full compile of
`W3D_RESID.lean` (3 errors: `hλ`); 07:14 second (2 timeouts: `tauto`); 07:20 third: **0 errors**, checks, axioms;
07:30 this report.
