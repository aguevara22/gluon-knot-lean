# W4_FB3_REPORT — unit FB3 (wave 4, prefix `s7fc_`: F box 3 `s7f_exists_ineligible_transport`), 2026-09-19 06:15 UTC / 2:15am ET

File: `work/drafts/corner/W4_FB3.lean` (9802 lines, sha256 `28afd2ff…`) = `W3_Assembled.lean` (8958 lines, sha256
`109050d9…`) + ONE inserted block + ONE body replacement:
`diff W3_Assembled.lean W4_FB3.lean` = `5716a5717,6559` (843 lines, the `s7fc_` block, inside `section S7FPersistent`
immediately BEFORE the docstring of `s7f_exists_ineligible_transport`) and `5729c6572,6573` (the black box's `sorry`
replaced by its two-line proof).  **0 deleted lines other than that `sorry`**; no import, `open` or `attribute` added; the
five frozen declarations are byte-identical (`s7_sliding_law_at` 4844, `s7_bigon_law_at` 8906 → 9750, `thm_C_S7_of`
8924 → 9768, `thm_C_S7_of_floor` 8949 → 9793, `thm_C_S7` 8954 → 9798: shifted by 844, text untouched); every other
statement / name / docstring untouched.
Check (official): `cd work/lean && lake env lean ../drafts/corner/W4_FB3.lean` — **0 errors, 0 non-sorry warnings, exit 0**,
22 s warm (load 3-5); **11 `declaration uses sorry`** = the 12 of W3_ASSEMBLY_REPORT §3 minus this box: `s7q_box_ret` 4437,
`s7q_box_carriers` 4519, `s7_sliding_law_at` 4844, `s7f_exists_bigonSplit` 5371, `s7f_exists_twoNewbornTerm` 5388,
`s7s_clear_local` 7816, `s7s_wallTriangleData_of_bigon` 7862, `s7z_F_exists` 9444, `s7z_returned_of_FSector` 9464,
`s7z_oneNewborn_exists` 9483, `s7_bigon_law_at` 9750 (the last six = the W3 lines + 844).
`grep -c sorry`: **20 → 19** = 11 bodies (4453, 4545, 4852, 5379, 5405, 7825, 7867, 9458, 9479, 9486, 9759) + the same 8
prose mentions as before (6, 3431, 4723, 4757, 4761, 4888, 9439, 9707; reword at port, OPEN_ITEMS §E-23).  The block
contains no `sorry` token.
Declarations: **56** (`s7fc_` only: 11 `def`/`noncomputable def`, 45 theorems), in two nested sections `S7FCArcs`,
`S7FCTransport`.  Clash scan: `grep -rln s7fc_ work/lean/{SM,CV,Bridge,RProof}` empty; no other `work/drafts/corner/*.lean`
uses the prefix; `python3 work/drafts/corner/tools/clash_scan.py W4_FB3.lean` (namespace-aware, 697 library files, 22 222
library declarations, 526 new declarations in the file): `duplicates_in_assembled: []`, `full_name_clashes: {}`; the 23
short-name coincidences are the pre-existing RET `s7r_SlidingTransport'.*` vs U110-B `s7b_SlidingTransport.*` namespace
pairs, none involving `s7fc_`.
`tools/stmt_check.py` does not exist in this package (only the port tool `port/tools/port_stmt_check.py`, which compares
port MODULES against `Wave2a_Assembled.lean` — not applicable to a draft); the frozen-statement check is the diff above.
Axioms (`#print axioms` on a scratch copy, 15 queries, `scratchpad/fb3/axioms.log`):
**`s7f_exists_ineligible_transport` = `[propext, Classical.choice, Quot.sound, SM.lit_homfly, SM.lp_lm,
SM.lp_lm_uniqueness]`** — the registered set, **no `sorryAx`** (`lit_homfly` through `cornerCoefficient`/`s7e_term`,
`lp_lm`/`lp_lm_uniqueness` through U110-D's record route exactly as `s7e_term_eq`); the same for `s7fc_ineligible_transport_at`,
`s7fc_term_eq`, `s7fc_coef_eq`; **standard axioms only** (`[propext, Classical.choice, Quot.sound]`) for every geometric
lemma: `s7fc_wind_eq`, `s7fc_side_of_r`, `s7fc_exists_inA_inB`, `s7fc_mem_range_first`, `s7fc_mem_range_second`,
`s7fc_interlaces_x`, `s7fc_interlaces_y`, `s7fc_between_iff_kappa`, `s7fc_not_mem_carrierCrossings_of_interlaces`.
Consumers: `s7f_persistent_difference_of_transport` (takes `htr` as a hypothesis) is `sorryAx`-free as before;
`s7f_exists_law_residual` still carries `sorryAx` through boxes 1 and 2 only.

**Closed: `s7f_exists_ineligible_transport` (decl 6564, formerly 5725).**  Not touched: the other 11 sorried bodies
(black boxes of other units, rule 2).  Nothing believed false; no missing hypothesis found in the frozen statement.

## 0. What was proved, in one paragraph

For an INELIGIBLE persistent support `T₀` of `P₀` (some `z ∈ T₀` lifts into neither half image, i.e. `liftCross z ∈ N`),
`s7e_term hn hP₂ (lift T₀) = s7e_term hn hP₀ T₀` below the radius `δ` of `s7a2_exists_intervalLocal` (= `vertex_sides`'
radius).  Two ingredients.  (i) **Geometry**: on the newborn side `P₂(t)` the persistent visits split into the arc `A`
(edge labels `M, …, a`, on `E_a` below `r`) and the arc `B` (labels `a, …, M−1`, on `E_a` above `r`); a persistent crossing
with both visits on `A` is the image of a crossing of `λ₁` (`s7fc_mem_range_first`, **the converse of
`s7b_isCrossing_firstHalf_image`** that W2_S7E_REPORT §2 item 1 flagged as missing), likewise for `B`/`λ₂`; hence a chord
of `N` has one visit on each arc (`s7fc_exists_inA_inB`) and INTERLACES both newborns (`s7fc_interlaces_x`,
`s7fc_interlaces_y`): on the traversal key rotated to start at `μ_M` (`s7fc_kappa`), the leg visit of `x` is the last
mark (`> n − η`), that of `y` the first (`< η`), both `a`-visits sit at `d + r ± η`, an `A`-visit in `(η, d + r − 3η)`, a
`B`-visit in `(d + r + 3η, n − 3η)` — all from `ContactParameterWindows` and `4η < r`, `4η < 1 − r`.  (ii) **Transport**:
`s7e_term_eq`'s pattern with the ALL-persistent visit map `s7fc_visitMap := s7a_visit` (every crossing of `P₀` is
persistent, so unlike the sliding case there is no relocation): decompositions by `s7a_side_isDecomposition_iff`, selector
weights by `s7a_turn_ccpCornerPolygon`, coefficients by `s7d_cornerCoefficient_eq_of_strictMono` whose `hmem` needs the
newborns to be MIXED crossings of every carrier of `lift T₀` — which is `interlacing_visit_owners_ne` (lem:carriers (iii),
`SM/CarrierNeighborSeparation.lean`, **already in the accepted library**: the "separation lemma on the successor
permutation, 300-500 lines" of W3_F_REPORT §2.3 did not have to be built) applied to the interlacing selected chord `z`;
`hr` by `s7a2_carrierRotation_eq`.  The side of `r` of a persistent `a`-visit is the same on `P₂` and on the centre
(`s7fc_side_of_r`, `s7e_sign_const`'s argument with the centre `u = 0` as the second point of `|u| ≤ t`), which is what lets
the converse range lemmas read the cut condition on the centre where `λ₁, λ₂` live.

## 1. Proved (all `s7fc_`; `{n} [NeZero n]`, `hn g {M a} h t` from `section S7FPersistent`)

### 1.A Rotated keys (section `S7FCArcs`, first part; generic `Q`, `hQ : Generic Q`)
| declaration | content |
|---|---|
| `s7fc_Between3 u v w`, `s7fc_rho c N x` | cyclic betweenness of three reals; the rotation of `[0, N)` by `c` |
| `s7fc_between3_rho` | cyclic betweenness on `[0, N)` is invariant under the rotation (8 × 2 × 3 `linarith` cases) |
| `s7fc_val_sub_real e M` | `((e − M).val : ℝ) = if e.val < M.val then e.val + n − M.val else e.val − M.val` (`ZMod.val_add`, `ZMod.val_sub`) |
| `s7fc_key_visit` (`rfl`), `s7fc_kappa M v := (v.edge − M).val + param v`, `s7fc_kappa_eq_rho` | the key rotated to start at `μ_M` is `ρ_{M.val, n}` of the traversal key |
| **`s7fc_between_iff_kappa hn hQ M v₁ v₂ v₃`** | `traversalBetween (visitPosition v₁) (visitPosition v₂) (visitPosition v₃) ↔ s7fc_Between3 (κ v₁) (κ v₂) (κ v₃)` |

### 1.B The two arcs and the converse range lemmas (section `S7FCArcs`, second part; `C` the centre, `hQC`, windows)
| declaration | content |
|---|---|
| `s7fc_InA M a r v`, `s7fc_InB M a r v` | `(edge − M).val < firstHalfSize ∧ (edge = a → param < r)`; `(edge − a).val < secondHalfSize ∧ (edge = a → r < param)` |
| **`s7fc_inA_or_inB hn hQ hw hη v hv`** | every persistent visit lies on `A` or on `B` (`s7e_persist_a` for `param ≠ r`; `ZMod.val_sub` for the label ranges) |
| `s7fc_cut_param_iff` | for `a ∈ z.val`: `param(a-visit of z on Q) < r ↔ u < r` where `crossingPoint z_C = edgePoint C a u` (`ContactPairData.point_eq`, `edgePoint_injective`, `hside`) |
| **`s7fc_mem_range_first hn hQ hsep hz hm hr hr0 hQC hside z hzp hA`** | both visits on `A` ⟹ `∃ c : Crossing λ₁, s7b_firstCrossingQ hn hsep hm hQC c = z` (remoteness by `s7b_remote_firstHalfIndex_iff`, the wrap pair is the affected `{a, M}`; segments by `s7b_edgeSegment_firstHalf` off the cut and `s7b_mem_edgeSegment_firstHalf_cut` on it) |
| **`s7fc_mem_range_second … hr1 …`** | both visits on `B` ⟹ image of a crossing of `λ₂` (`secondHalfEdgeIndex`, wrap pair `{a, M−1}`, `s7b_mem_edgeSegment_secondHalf_cut`) |
| **`s7fc_exists_inA_inB … hw hη z hzp h1 h2`** | `z` persistent, in neither image ⟹ `∃ i j : {k // k ∈ z.val}, i ≠ j ∧ InA ⟨z,i⟩ ∧ InB ⟨z,j⟩` |
`hside : ∀ j, IsCrossing C {a, j} → ¬ CA {a, j} → (edgeParameter Q a j < r ↔ edgeParameter C a j < r)` is a section
hypothesis here, discharged at the wall by `s7fc_side_of_r` (§1.D).

### 1.C The newborn visits and the interlacement (section `S7FCArcs`, third part)
| declaration | content |
|---|---|
| `s7fc_xl hx`, `s7fc_xa hx`, `s7fc_yl hy`, `s7fc_ya hy` (+ `_edge` (`rfl`), `_param`) | the leg / `a`-visits of `x = {a, M−1}`, `y = {a, M}`; parameters `edgeParameter Q (M−1) a`, `Q a (M−1)`, `Q M a`, `Q a M` |
| `s7fc_kappa_xl` (`n − η < κ < n`), `s7fc_kappa_xa` (`|κ − (d + r)| < η`), `s7fc_kappa_yl` (`0 ≤ κ < η`), `s7fc_kappa_ya` | the newborn keys from the windows' third clause (`hw.2.2 false/true`) |
| `s7fc_kappa_inA` (`η < κ < d + r − 3η`), `s7fc_kappa_inB` (`d + r + 3η < κ < n − 3η`) | the persistent keys on each arc (`s7e_persist_M`, `s7e_persist_M_sub_one`, `s7e_persist_a`; `4η < r`, `4η < 1 − r`) |
| **`s7fc_interlaces_x hn hQ hw hη hηr hηr1 hsep hx z hzp i j hij hA hB : Interlaces hn hQ ⟨{a, M−1}, hx⟩ z`** | witnesses `x₀ = ⟨M−1,_⟩`, `x₁ = ⟨a,_⟩`, `y₀ = i`, `y₁ = j`; both `crossingVisitBetween`s by `s7fc_between_iff_kappa` + `linarith` (`2 ≤ d ≤ n − 3` from `contactDistance_bounds`) |
| **`s7fc_interlaces_y … hy … : Interlaces hn hQ ⟨{a, M}, hy⟩ z`** | likewise with `y₀ = ⟨M,_⟩`, `y₁ = ⟨a,_⟩` |
| **`s7fc_not_mem_carrierCrossings_of_interlaces hn hP hS hzS hint q`** | generic: `S` a decomposition, `z ∈ S`, `Interlaces w z` ⟹ `w ∉ carrierCrossings hn hP S q` (`mem_carrierCrossings_iff_fiber` + `interlacing_visit_owners_ne`) |

### 1.D The transport (section `S7FCTransport`; `hloc : s7a2_IntervalLocal hn g M a r η δ`, `ht : t.val < δ`)
| declaration | content |
|---|---|
| `s7fc_hL`, `s7fc_hs`, `s7fc_hpar` | `s7a2_sideLocal`; `s7a_side_hs`/`s7a_side_hpar` from side `!side` (`P₀`) to side `side` (`P₂`) |
| **`s7fc_visitMap hn g h t hloc ht v := s7a_visit (s7fc_hs …) v (s7f_P₀_not_affected …)`**, `_fst` (`= s7f_liftCross v.1`, `Subtype.ext rfl`), `_not_affected` | the ALL-persistent visit map `Visit P₀ → Visit P₂` |
| `s7fc_hSS'`, `s7fc_hSp`, `s7fc_hSp'` | U110-A's support hypotheses for `S := T₀`, `S' := s7f_lift T₀` (`s7f_liftCross_mem_lift`, `s7f_mem_lift`) |
| `s7fc_e T₀ : Component P₀ T₀ ≃ Component P₂ (lift T₀)`, `s7fc_isDecomposition_lift` | `s7a_sideComponentEquiv`, `s7a_side_isDecomposition_iff` |
| `s7fc_wind_eq` | `wind hP₂ (lift T₀) = wind hP₀ T₀` (the `s7e_wind_eq` pattern: `Fintype.prod_equiv`, `s7c_carrierWeight_eq_sel`, `s7c_map_univ_eq_of_equiv`, `s7a_ccpCornerCount_eq`, `s7a_turn_ccpCornerPolygon`, `s7a_side_turn`, `s7a_side_sgn`) |
| `s7fc_hmono` | U110-D's `hmono`: `s7a_markKey_lt` + `s7a_markMap_inr` (`geometricVisitKey (CB.cg hn hP) v = markKey hn hP.1 (inr v)` is `rfl`) |
| **`s7fc_hmem T₀ q hx hy`** | U110-D's `hmem` for a carrier owning neither newborn as a self-crossing: affected `w` — both sides false (`s7f_eq_x_or_y_of_affected`, `s7fc_visitMap_not_affected`); persistent `w` — `s7a_visit_surjective` + `s7a_side_mem_carrierCrossings` + `s7a_visit_injective` |
| `s7fc_htwin` (`s7a_visit_twin`), `s7fc_hbit` (`s7d_positiveOverBit_eq_of_crossingSign` + `s7a_side_sgn`) | U110-D's `htwin`, `hbit` |
| **`s7fc_coef_eq T₀ hdec q hx hy`** | `cornerCoefficient hP₀ T₀ q hdec = cornerCoefficient hP₂ (lift T₀) (e q) _` by `s7d_cornerCoefficient_eq_of_strictMono` with `hr := s7a2_carrierRotation_eq` |
| **`s7fc_term_eq T₀ hnb`** | `s7e_term hP₂ (lift T₀) = s7e_term hP₀ T₀` given `hnb : IsDecomposition (lift T₀) → ∀ q', x ∉ cc q' ∧ y ∉ cc q'` (`s7e_term_of_decomposition`, `s7d_cornerProduct_eq_of_equiv`; the non-decomposition case by `s7e_term_of_not`) |
| **`s7fc_side_of_r hn g h t hloc ht hη j hc hnot`** | `edgeParameter P₂ a j < r ↔ edgeParameter g.center a j < r` (`s7a2_continuousAt_edgeParameter`, the windows at every `|u| < δ`, `s7a2_pos_of_ne_zero` applied to `ψ` resp. `−ψ` from the side time, evaluated at `g.zeroParameter`; `g.center = g.curve g.zeroParameter` by definition) |
| **`s7fc_ineligible_transport_at hn g h t hloc ht T₀ hη hηr hηr1 hr hT`** | the transport at one `t`: extract `z ∈ T₀ ∩ N` from `¬ s7f_Eligible`, `s7fc_exists_inA_inB` (with `hsep := h.1.1`, `hz := h.1.2.1`, `hm := h.1.2.2.2.1`, `hQC := s7f_hQC hn h.1 t side`, `hside := s7fc_side_of_r`, `hw := (s7fc_hL … side).windows`), `s7fc_interlaces_x/_y` at `s7f_x`/`s7f_y`, then `s7fc_term_eq` with `s7fc_not_mem_carrierCrossings_of_interlaces` |
| **`s7f_exists_ineligible_transport`** (frozen statement, body replaced) | `obtain ⟨r, η, -, -, hr, hη, hηr, hηr1, δ, hδ, -, hloc⟩ := s7a2_exists_intervalLocal hn g M a h.1; exact ⟨δ, hδ, fun t ht T₀ hT => s7fc_ineligible_transport_at hn g h t hloc ht T₀ hη hηr hηr1 hr hT⟩` |

## 2. What changed against the W3_F_REPORT §2.3 plan

* The plan's "separation lemma on the successor permutation (not in the library, ≈ 300-500 lines)" **is in the accepted
  library**: `SM.Carrier.interlacing_visit_owners_ne` (SM/CarrierNeighborSeparation.lean, lem:carriers (iii), standard
  axioms).  Only the 12-line wrapper `s7fc_not_mem_carrierCrossings_of_interlaces` was needed.
* The geometric content that WAS missing is the one W2_S7E_REPORT §2 item 1 named for the sliding branch: the CONVERSE
  of `s7b_isCrossing_firstHalf_image` / `_secondHalf_image` (a persistent crossing of the side polygon with both labels in
  a half's range, and the right side of `r` on `E_a`, is a crossing of that half).  It is now proved
  (`s7fc_mem_range_first/_second`, 46 + 48 lines) for the bigon side; the statements are generic in the side polygon `Q`
  (hypotheses `hQC`, `hside`) and apply verbatim to a sliding side.
* `hmem` is stated with the carrier crossing sets literally in bijection (`s7fc_hmem`), as the black box's docstring
  announced; the newborn exclusion is by interlacement, not by adjacency (the sliding analogue `s7e_xm_mem_iff` used
  adjacency).
* Size: 843 lines against the estimate 500-800 (the κ-key calculus and the two converse range lemmas are the surplus; the
  transport itself is 300 lines, as estimated).

## 3. Hand-offs (what other units can consume)

* **FB1 (box 1, `s7f_exists_bigonSplit`, §A-07)**: the fields `x_split`/`y_split` of `s7f_BigonSplit` — "`z ≠ x, y`, `z`
  interlaces neither newborn ⟹ `z ∈ range ι₁ ∪ range ι₂`" — follow by contraposition from `s7fc_exists_inA_inB` +
  `s7fc_interlaces_x` (resp. `_y`) exactly as in `s7fc_ineligible_transport_at` (a persistent `z` in neither image
  interlaces `x`; `z ≠ x, y` gives persistence via `s7f_eq_x_or_y_of_affected`).  `x_free`/`y_free` (a half crossing does
  not interlace a newborn): both visits of a half crossing are on ONE arc (`s7fc_inA_or_inB` + the direct half-image
  reading), so by `not_interlaces_iff_one_open_arc` … — the κ-bounds `s7fc_kappa_inA/_inB/_xl/_xa/_yl/_ya` give the two
  visits on the same side of both newborn visits.  `rel₁ rel₂ cross cross'` need the key order INSIDE an arc against the
  halves' labelling (cut form): `s7fc_kappa` is the rotated key that makes `A`'s order literal; `B`'s labelling starts at
  the cut (`secondHalfEdgeIndex 0 = a`), so `s7d_gaussList_isRotated_of_cut`'s shape applies.
* **S3 (`s7q_box_carriers`, §A-05)** and any sliding-side lane: `s7fc_mem_range_first/_second` give the converse image
  membership on a sliding side polygon with `hside` from `s7e_sign_const` (both sides) or `s7fc_side_of_r`'s argument.
* **B2 (`s7z_returned_of_FSector`)**: for an ELIGIBLE `T₀` the same transport data (`s7fc_e`, `s7fc_hSS'`, `s7fc_wind_eq`,
  `s7fc_hmono/_htwin/_hbit`, `s7fc_isDecomposition_lift`) are available; only `hmem` changes (there `x, y` ARE
  self-crossings of the full contact carrier — the skein branch).

## 4. Method audit (D-AUTH-20260919 §2; reassessment rule)

No lemma needed a second METHOD: the plan of §0 was executed as designed.  Compile-fix rounds: the abstract arcs scratch
(`scratchpad/fb3/Arcs1.lean`) needed two rounds (missing `include hn hQ`, `Subtype.ext` goal shape, `le_of_not_lt` gone; then
two missing `r`-bounds in the κ lemmas and three `omit`s), the transport in the truncated dev file (`Dev1.lean`) one round
(two missing `include`s).  No audit was triggered; nothing was abandoned.  Wall time 05:42-06:15 UTC (1:42-2:15am ET), ≈ 33 min.

## 5. Mathlib / Lean pitfalls hit (v4.34.0-rc2 pin)

1. `le_of_not_lt` no longer exists; use `not_lt.mp`.  `ZMod.val_sub (h : b.val ≤ a.val)`, `ZMod.val_add`, `ZMod.val_add_of_lt`
   exist; `ZMod.val_neg_one` is on `ZMod (n+1)` — use `last_index_val_succ`.
2. After `apply Subtype.ext` on a `Crossing Q` equality the goal shows `↑(…) = ↑z` with a coercion at `{s // IsCrossing Q s}`
   that `rw` rejects ("not type-correct under the implicit transparency level"); use `refine ⟨…, Subtype.ext ?_⟩` and
   `show Finset.image … = z.val` (the `_val` lemmas are `rfl`).
3. Section variables used only in proofs must be `include`d, per declaration (`include hn hQ in`, `include h hloc ht in`);
   the error is "Unknown identifier" or, for a def whose args shifted, a misleading "expected `WallGerm`" at the callers.
   `omit [NeZero n] in` for lemmas that mention `n` only through `Visit Q` / `ZMod n`.
4. `unfold X at h ⊢` fails when `X` does not occur in the goal; unfold at the hypothesis only.
5. `s7a2_pos_of_ne_zero` propagates positivity FROM a side time to all `|u| ≤ t`; for the other direction apply it to `−ψ`
   (`ContinuousAt.neg`, `neg_ne_zero`).  `g.center` is `g.curve g.zeroParameter` by definition — `exact` closes the
   change of spelling; `(g.zeroParameter).val` is `0` by `show |(0 : ℝ)| ≤ t.val`.
6. Deprecated `if_pos`/`if_neg` avoided by `simp only [h, hcond.mp h, ↓reduceIte]` (with `h : ¬c`, `simp only [h]` rewrites
   `c` to `False`); `split_ifs <;> constructor <;> rintro (…|…|…) <;> first | exact Or.inl ⟨by linarith, by linarith⟩ | …`
   closes the 48-case rotation lemma in a few seconds.
7. `linear_combination h2` closes `e = M − 1` from `h2 : e − M = −1`; `sub_left_injective`, `sub_eq_zero.mp`,
   `ZMod.val_injective n`, `(ZMod.val_eq_zero _).mp` convert between `val` facts and label equalities.

## 6. Verification record

```
cd work/lean && lake env lean ../drafts/corner/W4_FB3.lean      # 0 errors; 11 × "declaration uses sorry" (lines above)
grep -c sorry W3_Assembled.lean W4_FB3.lean                         # 20 / 19
diff W3_Assembled.lean W4_FB3.lean | grep '^[0-9]'                  # 5716a5717,6559  5729c6572,6573
lake env lean scratchpad/fb3/W4_FB3_axioms.lean                    # #print axioms × 15 → scratchpad/fb3/axioms.log (§ header)
grep -rln s7fc_ work/lean/{SM,CV,Bridge,RProof}                     # empty
python3 work/drafts/corner/tools/clash_scan.py W4_FB3.lean          # duplicates [], full-name clashes {} (header)
```
Scratch files (private, `scratchpad/fb3/`): `Probe0.lean` (name/Mathlib probe), `Arcs1.lean` (the abstract arcs section,
standalone), `Dev1.lean` (the truncated working file: W4 lines 1-5716 + block + the box), `W4_FB3_axioms.lean`,
`full_compile.log`, `axioms.log`, `block_arcs.lean`, `block_transport.lean`, `bb_body.lean`.

## 7. Left

Of FB3: nothing.  Of unit F: boxes 1 and 2 (`s7f_exists_bigonSplit` 5371, `s7f_exists_twoNewbornTerm` 5388) — black boxes of
other units, untouched; §3 lists what this block offers box 1.  The leaf `s7_bigon_law_at` and the other 9 sorried bodies
are untouched.  Port note: the block sits inside `section S7FPersistent` (W4 lines 5717-6559) and goes to `SM/CS7Units.lean`
with the rest of the F block under the §6 recipe of W3_ASSEMBLY_REPORT; it adds no import.
