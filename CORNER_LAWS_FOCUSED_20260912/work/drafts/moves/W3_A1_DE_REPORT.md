# W3_A1_DE_REPORT — unit W3-A1 (second prover, Units D / D8 / E of the trans-free copy), Wave 3, row 177

W3-A1-DE (subagent), 2026-09-15 21:44 UTC / 5:44pm ET (bounded test, audit A-177-1; hard stop 00:15 UTC not
reached).  Inputs: W3_SKELETON_REPORT.md §1.1, §2.0–2.2, §3, §5, §6; Skeleton_W3.lean; the accepted
RProof/GenericTransport.lean (235–8630 = `namespace G11_Params`; the copy source 4918–8630); SM/LinkDiagram.lean
(`withOver` :637, `switch` :650); SM/LinkMoves.lean (`OutsideMatch` :316, `OutsideMatch.switch` :1926,
`Clean.switch` :1948, `beforeOn_iff_before` :3001).  Nothing under `work/lean` was written.

## 0. Deliverables and checks

| item | result |
|---|---|
| `work/drafts/moves/W3_A1_DE.lean` | 3955 lines = Skeleton_W3.lean (1231, every line kept in order) + a 2723-line block `section W3DECopy … end W3DECopy` spliced after the skeleton's line 506 (`M₁sw_componentCount`, i.e. after all of `X₀ … M₀ M₁ st₀ st₁ y_* w_* w'_* x₀ x₁ M₀sw M₁sw` and before the sub-leaf `w3a_y_ne`) |
| compile `cd work/lean && lake env lean ../drafts/moves/W3_A1_DE.lean` | exit 0, **0 errors**, 25–50 s under load; warnings: 39× `declaration uses sorry`, 14× `if_pos`/`if_neg` deprecation (the skeleton's, cosmetic) |
| `grep -c sorry` | skeleton **30** → first compiling copy **41** (30 + 11 black boxes) → **39** after closing the two unit sub-leaves; the word occurs in no docstring, so 39 = the `declaration uses sorry` count |
| statement identity | all **42** `w3a_/w3b_/w3c_/w3d_/w3e_/w3g_/w3h_` theorem statements (from `theorem` to `:= by`) byte-identical to Skeleton_W3.lean; `check_W3_identity.py Port_GenericTransportSw_draft.lean W3_A1_DE.lean`: the 5 frozen blocks IDENTICAL, imports OK |
| **closed** | **`w3a_riii_param`** (the parametrised D8), **`w3a_exists_Ψ₁`** (E1 + the three crossing-correspondence clauses) — both bodies are one `exact π.w3de_…` of a theorem proved inside the block |
| `#print axioms` (scratch copy) | `w3a_riii_param`, `w3a_exists_Ψ₁`, `gu6_Ψ₁_overBit`, `w3c_riii_sw`: `[propext, sorryAx, Classical.choice, Quot.sound]` — the `sorryAx` enters ONLY through the BC-owned inputs (the sub-leaves `w3a_X₀_generic`, `w3a_X₁_generic`, `w3a_X*_cross_*` behind the aliases, and the 11 black boxes below); the new transport `w3de_moveMatch_withOver`: `[propext, Classical.choice, Quot.sound]` (sorry-free) |
| lines copied | **2167** lines of the accepted 4918–8629 (the 397 `π`/`C`-dependent declarations of Units D, D8, E; 3630 − 1216 lines of the 80 `C`-free helpers, which are NOT copied) + 8 alias lines + 11 black-box statements + 477 lines of new `w3de_` material |

## 1. Method (mechanical, scripted; scripts in the session scratchpad, not in the tree)

1. **Inventory** (`inventory.py`): the 1056 declarations of 235–8630 with line ranges and a `π`/`C`-dependence flag
   (regex on the docstring-stripped block).  Measured: B–C 579 declarations (512 dependent), D/D8/E **477 (397
   dependent, 2414 lines)**; the D/D8/E dependent declarations reference **43** B–C names directly, whose transitive
   closure inside B–C is 529 declarations (essentially all of B–C, 4.3k lines) — copying B–C too was not feasible in
   the window, hence the black-box route (§3).
2. **Copy** (`gen.py`): lines 4918–8629 with `G11_Config → G11_ConfigSw`, `G11_Params → G11_ParamsSw`,
   `G11_discOf → G11_discOfSw`, `G11_centroid → G11_centroidSw` (only 27 + 2 tokens in range), MINUS the `C`-free
   declarations (reached instead through `open RProof.G11_Params (…52 names…)` at the top of the block — the
   `gu6_*` helpers `gu6_riii_of_strands`, `gu6_over_under_of_pos/neg`, `gu6_visit_ext`, `gu6_tb_*`, `gu6_D9_core_*`,
   the `GU6Single`/`GU6Single2` sections, …), MINUS `gu6_htrans` (uses `C.trans`; replaced by the hypothesis
   `htrans`), `riii` (re-typed, §2), `homfly_M₁`, `core_of_params` (the skeleton's `w3c_homfly_M₁sw`/`G11_core_sw`),
   and the closing `end G11_Params`.  `variable {n : ℕ} [NeZero n]` added for the `omit [NeZero n] in` helpers;
   `open SM.GeoCarrier SM.Carrier` added (the accepted file's opens).
3. **The eight B–C names the skeleton restates as sub-leaves** (`X₀_generic`, `X₁_generic`, `X₀_cross_mp/mq/pq`,
   `X₁_cross_pC/qB/pq`) are ALIASES with the accepted statements verbatim and body `π.w3a_…` — NOT a name
   substitution: the skeleton types `w3a_X₀_generic` over `π.comp₀`, the accepted copy over the literal
   `⟨k + 3, π.hk₃, π.X₀⟩`; substituting the names made 8 `rw`/unification steps fail (`Shadow.single_crossingPoint`
   pattern, `Cp.P` in `gu6_det_ne_zero_single`), the aliases make the copy elaborate exactly as the accepted file
   (proof irrelevance identifies `positiveDiagram π.X₀_generic` with `π.M₀`).
4. **Black boxes**: the 11 B–C facts the copy consumes that the skeleton does not provide (§3), stated verbatim
   (docstring-stripped statement + `:= by sorry`) under their accepted names.
5. Compile → fix → 0 errors after one fix (step 3).  Then the two unit theorems (§2), compile → 0 errors first time.

## 2. The two closed sub-leaves

**`w3a_riii_param`** := `π.w3de_riii_param …` (W3_A1_DE.lean :2878–3168), the accepted `riii` :7172–7440 transformed:
* new generic transport (all sorry-free, inside the block, generic in `D D'`): `w3de_overVisit_withOver`
  (`(D.withOver f hf).overVisit y = v` from `v.1 = y`, `v.2.val = f y`, by `gu6_svisit_ext`),
  `w3de_underVisit_withOver` (from `w.2.val ≠ f y`, by `Shadow.eq_other_of_mem_of_ne`), the `_of_eq` forms,
  `w3de_outsideMatch_withOver` / `w3de_moveMatch_withOver` (the mirror of `OutsideMatch.switch`: `φ ψ e comp_eq`
  unchanged, `over_eq`/`under_eq` from `f y = D.overStrand y` at every outer crossing), `w3de_localFrame_withOver`
  (`Clean` rebuilt by fields, as `Clean.switch`);
* the outer agreement `hout₀ : crossingPoint y ∉ interior U → f₀ y = M₀.overStrand y` from `h₀` and `gu6_inner0`;
* the six `hov_*` blocks regenerated: `Rmp → OverOn Am y_mp ∧ UnderOn Ap y_mp` etc. via the two visit lemmas, the
  strand facts `w3de_w_*_strand : π.w_mp.2.val = π.st₀ π.mB` (`gu6_sv_strand`) and the label inequalities from
  `P1.ne_of_isCrossing_pair` on the six crossing facts (`w3de_mB_ne_p'`, …);
* `Separates`/`BeforeOn`/`beforeOn_iff_before` re-typed over `withOver` (shadow-level facts `Inner`, `Before`,
  `visitPt`, `ArcCover`, `eval` are untouched: `(D.withOver f hf).Γ = D.Γ` by `rfl`, every `exact` closed by defeq);
* `gu6_riii_of_strands (w3de_localFrame_withOver ⟨disc_isDisc, clean_M₀, clean_M₁⟩ …) mm' … Rmp Rmq Rpq hov_* htrans rev_*`.
  The positive instance (`f₀ := M₀.overStrand`, `Rmp := 0 < det …`, `htrans := gu6_htrans`) is the accepted `riii`
  (not restated here; the skeleton's switched instance `w3c_riii_sw` now compiles through it).

**`w3a_exists_Ψ₁`** := `π.w3de_exists_Ψ₁ …` (:3170–3241): the accepted `exists_Ψ₁` body (`gu6_Ψ₁`, `gu6_Ψ₁_twin`,
`gu6_Ψ₁_overBit`, `gu6_Ψ₁_sign`, the `σ₀` gap argument with `gu6_key_lt` + `GT_cyc_congr_of_lt`) plus the three
clauses `(Ψ₁ v).1 = y' ↔ v.1 = y` from the skeleton's PROVED `w3b_fst_eq_iff_of_twin gu6_Ψ₁ gu6_Ψ₁_twin v w_mp`
rewritten with `gu6_Ψ₁_w_mp : Ψ₁ w_mp = gu6_w'_Cp`, `gu6_w'_Cp_fst`, `gu6_w_mp_fst` (and `w_mq ↦ w'_Bq`, `w_pq ↦ w'_pq`).

Both `w3de_` theorems are stated with the copy's names `gu6_y_mp`, `gu6_y'_pC`; the `w3a_` connectors' `exact` closes
the skeleton's `y_mp`, `y'_pC` by `rfl` (`w3de_y_mp_eq : π.y_mp = π.gu6_y_mp := rfl` etc. are also provided).

## 3. Open / owned by the BC prover — the 11 black boxes (W3_A1_DE.lean :539–590, `sorry`)

`X₁_cross_iff` (:2887), `X₁_sign_pC` (:2901), `X₁_sign_qB` (:2911), `disc_isDisc` (:3130), `triangle_sub_interior`
(:3136), `inner_M₀` (:3346), `inner_M₁` (:3559), `clean_M₀` (:4875), `clean_M₁` (:4880), `exists_moveMatch` (:4883),
`exists_arcCovers` (:4890) — accepted line numbers; statements verbatim under the substitutions, accepted names kept
so the assembler can de-duplicate against W3_A1_BC.lean's proved copies (drop mine, keep BC's).  `homfly_M₀` and
`exists_Ψ₀` were NOT needed (their only D/E consumers `homfly_M₁`, `core_of_params` are dropped).  The 8 alias
theorems (:527–534) likewise duplicate BC names and must be dropped by the assembler when BC's copies (typed over the
literal `⟨k + 3, π.hk₃, π.X₀⟩`, as the accepted ones) are present — BC's versions then feed the copy unchanged.

All other 28 `sorry`s are the skeleton's untouched sub-leaves (`w3a_X₀_generic` … `w3a_exists_params` = BC's unit;
`w3b_reparam_switch` optional; `w3e_*`, `w3g_*`, `w3h_*` = units E/G/H).

## 4. Deviations from the unit prompt (executor-visible)

* **Insertion point**: the prompt's "immediately after `end G11_ConfigSw` (line 207)" is impossible for D/D8/E — the
  copy is typed over `π : G11_ParamsSw C` (defined at skeleton :359) and uses `M₀ M₁ w_*` (:421–480); the block goes
  after :506 instead, before the first sub-leaf whose body it serves.  Every skeleton line is kept, in order.
* **No B–C copy**: the transitive B–C closure of D/D8/E is all of B–C; black boxes (11) + aliases (8) instead.
* **`C`-free helpers by selective `open`** rather than by fully-qualified names (equivalent; 52 names listed at :515).
* **`omit [NeZero k] in`** kept on every copied helper as in the accepted file; the `variable {n}` and the two `open`s
  are scoped to `section W3DECopy` and do not reach the skeleton's later declarations (compile confirms).

## 5. Pitfalls met

* Name substitution `X₀_generic → w3a_X₀_generic` broke 8 proofs (`rw [Shadow.single_crossingPoint _ π.X₀_generic]`
  looked for `(Shadow.single π.comp₀).crossingPoint`; `gu6_det_ne_zero_single π.X₁_generic (by rw [Finset.pair_comm]; …)`
  elaborated `{π.mC, π.p'}` at `ZMod π.comp₁.k` and the `DecidableEq` instance no longer matched).  Aliases with the
  accepted statement fix all 8 (§1.3).  Rule of thumb for the BC prover: keep the accepted literal `⟨k + 3, π.hk₃, π.X₀⟩`
  in every copied statement; `M₀ := positiveDiagram π.w3a_X₀_generic` still matches by proof irrelevance.
* `(D.withOver f hf).underVisit y` needs `Shadow.eq_other_of_mem_of_ne y (hf y) hw (h : w.2.val ≠ f y)` (argument order
  `hs ht hne`, conclusion `t = other x hs`); the `∈ y.val` membership of `w.2.val` is `w.2.property` after `rw [← h1]`.
* The mirror of `OutsideMatch.switch` for `withOver` needs BOTH sides rebuilt (`(m.over_eq y).trans (Subtype.ext …)`
  on the right, `congrArg m.φ (Subtype.ext …)` on the left), each closed by `rw [w3de_overVisit_withOver_of_eq …]; rfl`.
* Compile time of the 4k-line file: 25–50 s (not minutes) — the D/D8/E copy is cheap; the `#print axioms` scratch copy
  the same.

## 6. Suggested next steps

* Assembler: W3_A1_BC.lean's `namespace G11_ParamsSw` block first, then this block minus :527–534 (aliases) and :536–590
  (black boxes); the `open RProof.G11_Params (…)` line must be merged with BC's (or both kept — duplicates in `open`
  are harmless).
* The positive instance `riii : RIII π.M₀ π.M₁` is NOT restated: over `G11_ConfigSw` it would need the transitivity
  of the positive height order (`gu6_htrans`'s conclusion), which is exactly the hypothesis the switched configuration
  lacks (`trans` was removed).  It is recoverable as `w3de_riii_param M₀.overStrand M₀.over_mem M₁.overStrand M₁.over_mem
  (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl) (0 < det …) (0 < det …) (0 < det …) (from w3a_over_*) htrans` whenever
  such an `htrans` is available; the row uses only the switched instance `w3c_riii_sw` (PROVED in the skeleton, now
  compiling through `w3a_riii_param`).
