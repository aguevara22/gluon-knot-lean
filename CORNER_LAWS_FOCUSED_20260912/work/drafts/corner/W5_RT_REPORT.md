# W5_RT_REPORT — wave-5 unit RT (prefix `w5t_`; W4_ASSEMBLY_REPORT §5 W5-RT: the RETURNED TRANSPORT), 2026-09-19 09:40 UTC / 5:40am ET

File: **`work/drafts/corner/W5_RT.lean`** (22,573 lines, sha256 `16a1c2f50f635c23…`) = `W4_Assembled.lean` (19,974 lines,
`9c0ec3b7a8b631a8…`) + ONE inserted block: `diff W4_Assembled.lean W5_RT.lean` = **`19853a19854,22452`** (2,599 lines, 0
deleted lines), inside `section W4Bigon` (variables `hn g {M a} h h₁ h₂`) immediately BEFORE the docstring of
`w4_box_returnedRows` (now line 22453-22455, its body `sorry` at 22457 untouched: this unit is NOT W5-ROW).
**Compile** (`cd work/lean && lake env lean ../drafts/corner/W5_RT.lean`): **0 errors, 0 warnings other than exactly the
same 5 `declaration uses sorry` as W4** — 4437 `s7q_box_ret`, 18053 `s7z_F_exists`, 18494 `s7z_returned_of_FSector`,
22456 `w4_box_returnedRows` (was 19857), 22521 `s7_bigon_law_at` (was 19922); 48 s.  **`grep -c sorry`: 16 before → 16
after** (the block contains no `sorry` token, not even in prose).  `tools/stmt_check.py --base W3_Skeleton.lean`: 5/5 frozen
statements byte-identical and unique (PASS).  `tools/clash_scan.py`: `duplicates_in_assembled: []`, `full_name_clashes: {}`
(39 short-name coincidences, all in different namespaces; the scanner's `prefix_stats` calls `w5t_` "UNPREFIXED" because its
regex knows only `s7[a-z]_`, cosmetic as for `w4_`).  No import, `open`, `attribute` or top-level `variable` added; every
top-level name carries `w5t_` (the 44 members of `namespace w5t_ReturnedTransport` are `w5t_ReturnedTransport.*`);
146 declarations in eight nested sections `W5TGlue, W5TReturn, W5TCarriers, W5TCornerTransport, W5TTurns, W5TSpectators,
W5TRotation, W5TWall`.  Nothing written under `work/lean`; `lake build` never run.

**Closed: the whole of W5-RT — no `w5t_` Prop is left with `sorry`; no black box of another unit was consumed.**
**Axioms** (`#print axioms` on the scratch copy `<scratchpad>/rt/W5_RT_axioms.lean`, 21 queries, `axioms.log`):
standard `[propext, Classical.choice, Quot.sound]` for all the geometric/combinatorial content (`w5t_glue_sameCycle_iff`,
`w5t_glued_sameCycle_inl_inr`, `w5t_returnedTransport_of`, `w5t_ReturnedTransport.specEquiv`,
`.carrierCrossings_eq_img_first`, `w5t_ct_cornerMark_shift`, `w5t_ct_carrierWeight_eq`, `.carrierWeight_first`,
`w5t_carrierRotation_first/second`, `w5t_transport`, `w5t_x_mem_qH`, `w5t_y_mem_qH`, `w5t_weight_P₀`); standard +
`SM.lit_homfly, SM.lp_lm, SM.lp_lm_uniqueness` (the registered literature interfaces, entering only through
`cornerCoefficient` / U110-D's `s7d_cornerCoefficient_eq_of_cut` and FB3's `s7fc_coef_eq`, exactly as in FB2/FB3) for
`.coef_first`, `w5t_spec_prod`, `w5t_spec_prod_P₀`, **`w5t_returned_terms`**.  **No `sorryAx` in any `w5t_` declaration.**
`w4_box_returnedRows`, `s7_bigon_law_at`, `thm_C_S7` carry `sorryAx` exactly as in W4 (the black box's own body / the leaf's).

## 0. What is proved, in one paragraph

For the newborn-free row `T = lift T₀` of the newborn side `P₂(t)` (every crossing of `T` carried from a half, `x, y ∉ T`),
the smoothing successor is the FIRST-RETURN map of the **glued** sum permutation `g₁ ⊔ g₂ * swap (inl 0₁) (inr 0₂)` on the
image of FB2's bigon mark map restricted to the half marks (`λ₁`'s vertex `0 ↦ y_a`, `λ₂`'s vertex `0 ↦ x_ℓ`): `λ₁`'s vertex `0`
continues from `y_a` up `E_a` into `λ₂`'s edge `0`, and `λ₂`'s vertex `0` continues from `x_ℓ` through `μ_M`, `y_ℓ` (both off
the image) into `λ₁`'s edge `0`; every other chain is FB2's, with `x_a`, `y_ℓ` now TRANSIT marks — so **no interlacing
hypothesis is needed** (the law holds for `ε = 0` and `ε = 1` alike; FB2 needed `y_a < x_a`).  Composing a permutation with
a transposition of two points on DIFFERENT cycles merges exactly those two cycles (`w5t_glue_sameCycle_iff`, pure
combinatorics), so the carriers of `T` are the half carriers with the two half contact carriers `L₁ = owner λ₁ 0`,
`L₂ = owner λ₂ 0` identified to the FULL CONTACT CARRIER `q_H = owner (inl M)`, which carries `x` and `y` as self-crossings
(`x_mem_carrierCrossings`, `y_mem_carrierCrossings`); the SPECTATORS `{q ≠ q_H} ≃ {L ≠ L₁} ⊕ {L ≠ L₂}` (`specEquiv`)
carry exactly the images of their half carrier's crossings (`carrierCrossings_eq_img_first/second`), corner lists up to a
cyclic shift (`cornerMark_shift_first/second`, through the ABSTRACT corner transport `w5t_ct_*`), equal weights
(`carrierWeight_first/second`), equal rotations (`w5t_carrierRotation_first/second`, FB2's corner family) and equal
coefficients (`coef_first/second`, U110-D's cut form).  On `P₀`, FB3's `s7fc_e` with the per-carrier weight equality
`w5t_weight_P₀` and `s7fc_coef_eq` off the contact carrier.  Hence **`w5t_returned_terms`**: with the common spectator
products `Spec₁ = ∏_{L ≠ L₁} wt(L) c(L)`, `Spec₂ = ∏_{L ≠ L₂} wt(L) c(L)` (`w5t_spec₁/₂`),
```
term₂(T)  = wt(q_H) c(q_H) · (Spec₁ · Spec₂)          term(T₁) = wt(L₁) c(L₁) · Spec₁
term₀(T₀) = wt(q_L) c(q_L) · (Spec₁ · Spec₂)          term(T₂) = wt(L₂) c(L₂) · Spec₂      (q_L := s7fc_e⁻¹ q_H)
```
so Prop B2' `w4_ReturnedRow` reduces to the CONTACT-CARRIER identity
`wt(q_H) c(q_H) − wt(q_L) c(q_L) = ε · (δ_dir · s) · (wt(L₁) c(L₁)) (wt(L₂) c(L₂))` — BLOCK's `s7k_interlacing_term` /
`s7k_noninterlacing_term` on the rows `Ω_H − Ω_L = −ω₁ω₂` / `= 0` (W5-SITE, W5-BR) — and the multiplication through by
`Spec₁ Spec₂` (W5-ROW).

## 1. Proved (all `w5t_`; W5_RT lines 19854-22452; `hn g {M a} h h₁ h₂` from `section W4Bigon`)

### A. `section W5TGlue` (19868-20092) — cycles of `g * swap p q`, `p`, `q` on different `g`-cycles (pure combinatorics)
| declaration | content |
|---|---|
| `w5t_glue_apply_of_ne/_left/_right` | `(g * swap p q) x = g x` off `{p, q}`; `= g q` at `p`; `= g p` at `q` |
| `w5t_glue_pow_of_off`, `w5t_glue_sameCycle_iff_of_off` | off the cycles of `p`, `q` the iterates and `SameCycle` are those of `g` |
| `w5t_glue_pow_p`, `w5t_glue_sameCycle_pq`, `w5t_glue_sameCycle_of_q/_of_p` | the glued orbit of `p` runs through the whole `g`-cycle of `q` (first return of `q` to itself, `Nat.find`) and of `p` |
| **`w5t_glue_sameCycle_iff`** | `SameCycle (g * swap p q) x y ↔ SameCycle g x y ∨ (x, y both on the cycles of p or q)` |
| `w5t_glued g₁ g₂ p₁ p₂ := sumCongr g₁ g₂ * swap (inl p₁) (inr p₂)`, `_apply_inl/_inl_p/_inr/_inr_p`, **`_sameCycle_inl_inl/_inr_inr/_inl_inr`** | the glued sum: `inl x ~ inl y ↔ x ~₁ y`, `inr x ~ inr y ↔ x ~₂ y`, `inl x ~ inr y ↔ x ~₁ p₁ ∧ y ~₂ p₂` |

### B. `section W5TReturn` (20094-20862) — the returned first-return law (FB2's Part B for `x, y ∉ T`)
Variables as FB2's `S7FBReturn` (`hQ hsep hz hm hr hr0 hr1 hη hQC hw hord hside hg₁ hg₂ hcx hcy`), support `T` with
`hxT : x ∉ T`, `hyT : y ∉ T`, `hTimg : ∀ z ∈ T, z ∈ range ι₁ ∪ range ι₂`.
| declaration | content |
|---|---|
| `w5t_mark b := s7fb_mark … (inl b)`, `_apply`, `_injective`, `_inl_zero` (`= inr y_a`), `_inr_zero` (`= inr x_ℓ`), `_inl_inl/_inl_inr/_inr_inl/_inr_inr` | the returned mark map `Mark λ₁ ⊕ Mark λ₂ → Mark Q` |
| `w5t_mem_range_iff` (`range = range s7fb_mark ∖ {inl M}`), `w5t_M_not_mem_range`, `w5t_inr_mem_range_iff`, `w5t_xa/yl_not_mem_range`, `w5t_ya/xl_mem_range`, `w5t_inl_mem_range` (every vertex `≠ M`) | the image |
| `w5t_transit_of` (a visit `≠ y_a, x_ℓ`, carried from neither half, is transit — `x_a`, `y_ℓ` included), `w5t_transit_window` | RET's `s7r_Transit` for the returned map (4 exclusions instead of FB2's 6) |
| `w5t_qmark₂ m₂ := if m₂ = inl 0 then inr y_a else w5t_mark (inr m₂)`, `_zero/_of_ne/_inl/_inr`, `w5t_edge_second`, `w5t_param_second`, `w5t_qmark₂_param_zero` | the second-half chain start (`λ₂`'s vertex `0` is left from `y_a`); the first-half chain start is FB2's `s7fb_qmark₁` unchanged |
| **`w5t_reach_first`**, **`w5t_reach_second`** | from the chain start of `m` the smoothing successor reaches the image of `nextMark m` through transit marks only (FB2's proofs with the cut windows bounded by `y_a` and `x_a` transit; `s7r_reach_of_transit`, `s7r_nextMark_shape`, `s7r_no_half_between`, `s7r_first/second_order`, `s7r_first_cut_lt`, `s7r_second_cut_gt`, `s7e_persist_M/_M_sub_one`) |
| `w5t_step_first m (m ≠ 0)`, `w5t_step_second m (m ≠ 0)` | `s7r_step_of_reach` with `selectedMarkPerm T (ι b) = qmark (selectedMarkPerm S b)` |
| **`w5t_step_first_zero`** (`y_a ↦ ι (inr (g₂ 0))` via `w5t_reach_second (inl 0)`), **`w5t_step_second_zero`** (`x_ℓ → μ_M → y_ℓ → ι (inl (g₁ 0))`, `s7fb_nextMark_xl`, `s7fb_succ_M`, `w5t_reach_first (inl 0)`; `k' + 3` steps) | the two glued steps |
| `w5t_hit` | every mark reaches the image (beacon `y_a`; every off-image mark is transit) |
| **`structure w5t_ReturnedTransport S₁ S₂`** (`x_not y_not first_pre second_pre img ret`), **`w5t_returnedTransport_of`** | `ret : s7b_ReturnTransport (σ_T) (w5t_glued g₁ g₂ (inl 0) (inl 0)) w5t_mark`, proved |

### C. `section W5TCarriers` (20864-21343) — the carriers of a returned row
| declaration | content |
|---|---|
| `w5t_qH hn hQ T M := owner (inl M)`, `w5t_L₁ := owner λ₁ (inl 0)`, `w5t_L₂`, `w5t_rep` / `w5t_owner_rep` (a representative mark of a carrier, `Quotient.out`) | the contact carriers |
| `w5t_nextMark_xa` (`x_a < y_a → nextMark x_a = y_a`, the twin of `s7fb_nextMark_ya`), `w5t_owner_yl` (any support) | |
| **`w5t_smoothingSuccessor_insert`** | `σ_{insert x T} = σ_T * swap (inr v₁) (inr v₂)` for `x ∉ T` with visits `v₁ ≠ v₂` (pointwise) |
| `namespace w5t_ReturnedTransport` (`hT`): `owner_inl_eq_inl_iff`, `owner_inr_eq_inr_iff`, **`owner_inl_eq_inr_iff`** (`↔ owner m = L₁ ∧ owner m' = L₂`), `owner_xl/_yl/_inr_zero/_inl_zero/_ya/_xa` (all `= q_H`; `x_a` by `w5t_nextMark_xa`/`s7fb_nextMark_ya` in either order), `owner_inl_eq_qH_iff`, `owner_inr_eq_qH_iff`, `exists_mark` | owners (through `hT.ret.sameCycle_iff` and Part A) |
| **`x_mem_carrierCrossings`, `y_mem_carrierCrossings`** | `x, y ∈ carrierCrossings q_H` |
| `rep_inl_ne_qH`, `rep_inr_ne_qH`, `specMap`, `specMap_inl/_inr`, `specMap_injective/_surjective`, **`specEquiv : {L ≠ L₁} ⊕ {L ≠ L₂} ≃ {q ≠ q_H}`**, `specEquiv_inl_owner_iff` (`owner (ι (inl m)) = q ↔ owner m = L`), `specEquiv_inr_owner_iff`, `specEquiv_inl_ne_inr`, `specEquiv_inr_ne_inl` | the spectator correspondence |
| **`carrierCrossings_mem_range`** | a carrier crossing of a spectator is carried from a half: a crossing off both images and off the newborns interlaces `x` (the split's `x_split`), `insert x T` is a decomposition (`x_free₁/₂`), lem:carriers (iii) `interlacing_visit_owners_ne` separates its visits there, and by `w5t_smoothingSuccessor_insert` + `w5t_glue_sameCycle_iff_of_off` the carriers of `T` and `insert x T` agree off `q_H` — **no window analysis, no new geometry** |
| `firstCrossingQ_mem_carrierCrossings_iff`, `secondCrossingQ_…`, **`carrierCrossings_eq_img_first/second`** | `carrierCrossings (specEquiv (inl ⟨L, _⟩)) = img ι₁ (carrierCrossings L)` |

### D. `section W5TCornerTransport` (21345-21596) — the ABSTRACT corner-list transport (`w5t_ct_`)
Generic in `ι : Mark L → Mark Q` (injective), carriers `q` of `T` and `qL` of `S` with `hown : ∀ c, owner (ι c) = q ↔ owner c = qL`,
`hstep` (the first-return step on `qL`'s marks), `hcorner` (true corners correspond on `qL`'s marks), `hoff` (no true corner
of `q` off the image): `w5t_ct_pow`, `w5t_ct_not_corner_of_orbit`, `w5t_ct_cornerMark_succ`, `w5t_ct_mem_cornerList_iff`,
`w5t_ct_cornerList_rotated`, **`w5t_ct_cornerMark_shift`** (`k_q = k_qL ∧ ∃ s, ccpCornerMark q j = ι (ccpCornerMark qL (j + s))`),
**`w5t_ct_carrierWeight_eq`** (equal mark turns ⇒ `wt(q) = wt(qL)`).  FB2's D1/D2 (`pow_first … carrierWeight_first`)
with the transport structure abstracted away — written once, instantiated twice.

### E. `W5TTurns` (21598-21700), `W5TSpectators` (21702-21957), `W5TRotation` (21959-22064)
`w5t_markTurn_first/second` (FB2's `markTurn_first/second` without `hT`), `w5t_cutFirst_of/_cutSecond_of` (the `s7q_CutFirst`
data from the rotation equality); in the namespace: `step_first/second`, `corner_first/second`, `off_first/second` (the
inputs of Part D for the spectators), `mem_cornerList_first/second_iff`, **`cornerMark_shift_first/second`**,
**`carrierWeight_first/second`**, **`coef_first/second`** (U110-D's `s7d_cornerCoefficient_eq_of_cut` with
`carrierCrossings_eq_img_*` as `hmem`); at the wall (`hloc hdet …`, as FB2's `S7FBRotation`): `w5t_kind_first/second`,
**`w5t_carrierRotation_first/second`** (FB2's `s7fb_family_rotation` on the spectator's corner family + `Reindexed` through
`cornerMark_shift_*` and `s7fb_point_first/second`).

### F. `section W5TWall` (22066-22450) — at the bigon wall, `t < δ`
| declaration | content |
|---|---|
| `w5t_prod_split` | `∏ x, f x = f a₀ * ∏ x : {x ≠ a₀}, f x` |
| `w5t_hcx`, `w5t_hcy`, `w5t_x_eq`, `w5t_y_eq` | the newborns as `IsCrossing P₂ {a, contactLeg _ M}`; `(s7e_va hcx).1 = s7f_x`, `… = s7f_y` |
| **`w5t_transport T₀ (hE : s7f_Eligible T₀)`** | `w5t_ReturnedTransport hn hP₂ h.1.1 h.1.2.2.2.1 (s7f_hQC …) h₁ h₂ hcx hcy (lift T₀) (pre ι₁ (lift T₀)) (pre ι₂ (lift T₀))` |
| `w5t_hw`, **`w5t_x_mem_qH`, `w5t_y_mem_qH`** | `s7f_x, s7f_y ∈ carrierCrossings (lift T₀) (w5t_qH hn hP₂ (lift T₀) M)` |
| `w5t_weight_P₀` | `carrierWeight P₀ T₀ q = carrierWeight P₂ (lift T₀) (s7fc_e q)` (the body of FB3's `s7fc_wind_eq`, per carrier) |
| `w5t_T₁ T₀ := pre ι₁ (lift T₀)`, `w5t_T₂`, `_def` (`rfl`; = `w4_eligibleEquiv_fst/_snd`) | the half preimages |
| `w5t_spec₁ T₁ hd₁ := ∏_{L ≠ L₁} wt(L) c(L)`, `w5t_spec₂`, **`w5t_term_half₁/₂`** (`term(T_i) = wt(L_i) c(L_i) · Spec_i`) | |
| `w5t_split'`, `w5t_spec_factor₁/₂` (a spectator carries `wt · c` of its half carrier), **`w5t_spec_prod`** (`∏_{q ≠ q_H} wt c = Spec₁ Spec₂`), `w5t_spec_prod_P₀` (`= ∏_{q ≠ q_H} wt₀(e⁻¹q) c₀(e⁻¹q)`: the newborns are self-crossings of no spectator, `s7fc_coef_eq`) | |
| **`w5t_returned_terms T₀ hE hsplit hd hd₁ hd₂ hd₀`** (22398) | the four term identities of §0 |

## 2. Deviations from W4_ASSEMBLY_REPORT §5 W5-RT, disclosed

1. **The component correspondence is delivered as `specEquiv : {L ≠ L₁} ⊕ {L ≠ L₂} ≃ {q ≠ q_H}` plus the owner lemmas**, not as a
   quotient-level `Component P₂ T ≃ (C₁ ⊕ C₂)/(L₁ ∼ L₂)`: the first-return engine gives `Component P₂ T ≃ cycles(glued)`
   (`hT.ret.cycleEquiv`), and the cycles of the glued permutation are described by `w5t_glue_sameCycle_iff`; the spectator
   equivalence is what the products need.  Nothing believed false in §5's shape; this is the same content.
2. **The returned transport needs no interlacing case split.** FB2's `hlt : y_a < x_a` was needed only because `x_a` was a
   smoothing corner of the two-newborn row; here `x_a`, `y_ℓ` are transit, and the reach lemmas are stated for any position
   of `x_a` relative to `y_a`.  `w5t_returned_terms` therefore holds for `ε = 0` and `ε = 1` uniformly (the `ε` enters W5-ROW
   only through the contact-carrier identity).
3. **Carrier crossings of the spectators without geometry**: the `N`-crossings (chords through the cut, in neither half image)
   are excluded from the spectators by lem:carriers (iii) applied in `insert x T` and the one-transposition relation between
   the two smoothings (`w5t_smoothingSuccessor_insert`), not by locating their visits on the chains.  An `N`-crossing CAN be
   a carrier crossing of `q_H`; so `carrierCrossings q_H` is NOT characterised here (only `x, y ∈ carrierCrossings q_H`);
   BLOCK derives `m_H = m_L + 2` from the site (`s7k_count_of_site`), so W5-SITE does not need it.
4. **Abstract corner transport** (Part D, ≈290 lines) instead of two concrete copies of FB2's D1 (≈600 lines each): the
   `w5t_ct_*` lemmas take the step/owner/corner/off-image data as hypotheses and are instantiated per half.
5. **`hdet`/`δ'`**: the rotation equalities need FB2's determinant radius (`s7fb_exists_detRadius`) exactly as FB2's do; the
   wall-level theorems carry `(hdet) (ht' : t.val < δ')` as hypotheses, to be discharged by W5-ROW with
   `s7fb_exists_detRadius hn g h hloc hr hr1 hδ` and `min δ δ'` (as `s7fb_exists_twoNewbornTerm` does).
6. Size: 2,599 lines against the estimate 1,000-1,500.  The surplus is Parts A (214, the glue combinatorics, not in the
   estimate) and B (≈800: the two reach lemmas had to be re-proved because FB2's are stated with `hlt` and for the
   two-newborn exclusions) and the explicit spectator bookkeeping of Part F.

## 3. Black boxes (rule 2)

**None.** Every consumed statement is a proved theorem of `W4_Assembled.lean` or the library: FB2's `s7fb_mark` and its
computation/range lemmas, `s7fb_qmark₁` and its parameter lemmas, `s7fb_param_first/second`, `s7fb_transit`-style windows
(re-proved), `s7fb_nextMark_xl/_M/_ya`, `s7fb_succ_M`, `s7fb_visit_cases`, `s7fb_persistent_of_edge_a`, `s7fb_persist_a_cases`,
`s7fb_xa/ya_near`, `s7fb_xl/yl_param`, `s7fb_markTurn_ya/_xl`, `s7fb_turn_eq/_first/_second`, `s7fb_crossingSign_centre`,
`s7fb_edge_first/second_smul`, `s7fb_sign_smul_pos`, `s7fb_cycle_next_congr`, `s7fb_Kind`, `s7fb_family_rotation`,
`s7fb_point_first/second`, `s7fb_hord`, `s7fb_hside`; RET's `s7r_Transit`, `s7r_reach_of_transit`, `s7r_hit_of_transit`,
`s7r_step_of_reach`, `s7r_between_*`, `s7r_nextMark_shape`, `s7r_no_half_between`, `s7r_first/second_order`,
`s7r_first_cut_lt`, `s7r_second_cut_gt`; ROT's `s7q_CutFirst/Second`, `s7q_cutFirst_of/_cutSecond_of`; U110-B's
`s7b_ReturnTransport` (`sameCycle_iff`, `hit`, `step`), `s7b_sumCongr_*`, `s7b_pre/img`, the half crossing/visit maps;
U110-C's `s7c_carrierWeight_eq_sel`, `s7c_map_univ_eq_of_equiv`; U110-D's `s7d_cornerCoefficient_eq_of_cut`,
`s7d_positiveOverBit_eq_of_crossingSign`; A2's `s7a2_cornerFamily_side_self`, `s7a2_point_eq_evaluation`; FB3's `s7fc_e`,
`s7fc_isDecomposition_lift`, `s7fc_coef_eq`, `s7fc_hs/hpar/hSS'/hSp/hSp'/hL`; F's `s7f_lift`, `s7f_x/y`, `s7f_pattern`,
`s7f_hQC`, `s7f_BigonSplit` fields, `w4_lift_mem_range`; library `interlacing_visit_owners_ne`, `ccp_corner_chain`,
`ccpCornerMark_*`, `owner_eq_iff`, `smoothingSuccessor_*`, `s7e_nextMark_inr_eq_inr`, `Reindexed`,
`rotationNumber_of_reindexed`, `s7a_ccpCornerCount_eq`, `s7a_turn_ccpCornerPolygon`, `s7a_side_turn/_sgn`.
Nothing found false as stated; no frozen statement touched.

## 4. For W5-ROW / W5-SITE / W5-BR

* **W5-ROW** consumes `w5t_returned_terms hn g h h₁ h₂ hloc hδ hr hr0 hr1 hη hηr hηr1 hdet t ht ht' T₀ hE hsplit hd hd₁ hd₂ hd₀`
  with `hE, hd := (w4_mem_EligDec …).mp hT₀`, `hd₁ := (w4_eligibleEquiv … ⟨T₀, hT₀⟩).1.2` (its type is
  `IsDecomposition … (s7b_pre ι₁ (lift T₀)) = … (w5t_T₁ …)` by `rfl`), `hd₂ := (…).2.2`, `hd₀ := (s7fc_isDecomposition_lift … T₀).mp hd`;
  the radii `hloc/δ` from `s7a2_exists_intervalLocal`, `δ'` from `s7fb_exists_detRadius`.  Subtracting the first and fourth
  identities and multiplying the second and third: `w4_ReturnedRow` ⇐ `wt(q_H) c(q_H) − wt(q_L) c(q_L) = ε s₀ (wt(L₁) c(L₁))(wt(L₂) c(L₂))`
  (`s7k_interlacing_term` with `hwt`, `hrow`; `s7k_noninterlacing_term`), then `ring`-level regrouping with `Spec₁ Spec₂`.
* **W5-SITE / W5-BR** take the carriers as `q_H = w5t_qH hn (s7f_hP₂ g M a t) (s7f_lift hn g h t T₀) M`,
  `q_L = (s7fc_e hn g h t hloc ht T₀).symm q_H`, `L₁ = w5t_L₁ hn h.1.1 h₁ (w5t_T₁ hn g h t T₀)`, `L₂ = w5t_L₂ …`; the newborns are
  self-crossings of `q_H` (`w5t_x_mem_qH`, `w5t_y_mem_qH`); the transport `hT := w5t_transport … T₀ hE` gives the owners of
  every mark (`hT.owner_*`, `hT.owner_inl_eq_qH_iff`, `hT.exists_mark`) and the first-return structure `hT.ret` for the
  corner list of `q_H` (its corners are the images of the corners of `L₁`, `L₂` other than the two vertices `0`, plus `μ_M`;
  not stated here).

## 5. Method audit (D-AUTH-20260919 §2, the reassessment rule)

No lemma failed twice on substance; the plan of §0 (decided before writing: glue combinatorics → re-proved reach with
transit newborn visits → owner lemmas via `sameCycle_iff` → `insert x T` trick for carrier crossings → abstract corner
transport → FB2's family for rotations → cut-form coefficients → product bookkeeping) was executed as designed.  Compile-fix
rounds, all mechanical: Part A twice (instance generality `[DecidableEq β]` so that `Equiv.swap` on the sum type unifies;
`SameCycle.symm` on an anonymous constructor); Part B once (`pow_succ` vs `pow_succ'`); Part C four (`Quotient.out` on the
`Component` def trips `rw`'s transparency check → `w5t_rep`; `rw` under `≠` needs `intro`; `subst` for a subtype equality;
`s7e_visit_of_fst` wants the `.val` form; the representative helper generalised from `n` to the half sizes); Part D none;
Part E once (`include hcx hcy`; `show` before `rw` on a beta-redex); Part F four (argument orders of section-variable
theorems, un-inferable `_` placeholders in the statement → `w5t_T₁/T₂`, a heartbeat timeout from `congr 1` trying `rfl` on
big products → `congrArg₂`, final `rfl` after unfolding `w5t_T₁`).  The reassessment rule was not triggered.

## 6. Verification record

```
cd work/lean && lake env lean ../drafts/corner/W5_RT.lean         # 0 errors; 5 × "declaration uses sorry" (4437 18053 18494 22456 22521); 48 s
grep -c sorry work/drafts/corner/W4_Assembled.lean work/drafts/corner/W5_RT.lean      # 16 / 16
diff work/drafts/corner/W4_Assembled.lean work/drafts/corner/W5_RT.lean | grep '^[0-9]'  # 19853a19854,22452
python3 work/drafts/corner/tools/stmt_check.py work/drafts/corner/W5_RT.lean --base work/drafts/corner/W3_Skeleton.lean   # 5/5 PASS
python3 work/drafts/corner/tools/clash_scan.py work/drafts/corner/W5_RT.lean          # duplicates [], full-name clashes {}
cd work/lean && lake env lean <scratchpad>/rt/W5_RT_axioms.lean                        # the 21 axiom lines of the header → axioms.log
```
Scratch (private, `<scratchpad>/rt/`): `pfx/W5Prefix.lean` + `.olean` (W4 lines 1-19852 closed, 52 s), `lean.sh` (project
`LEAN_PATH` + the prefix), `partA.lean … partF.lean` (the block in pieces), `ProbeA … ProbeF.lean` (prefix-based probes,
13-25 s each), `w5t_block.lean` (the inserted block), `full_compile.log`, `W5_RT_axioms.lean`, `axioms.log`.
Timeline: 08:20 UTC start (reports, W4 glue, FB2/FB3/RET/U110-B code); 08:44 prefix olean; 08:50 Part A; 09:00 Part B;
09:12 Part C; 09:17 Part D; 09:22 Part E; 09:32 Part F; 09:33 `W5_RT.lean` compiles; 09:34 axioms, checks; 09:40 report.
