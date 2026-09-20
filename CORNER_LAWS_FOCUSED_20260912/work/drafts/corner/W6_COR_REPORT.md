# W6_COR_REPORT — wave-6 unit COR (prefix `w6c_`; W5_ASSEMBLY_REPORT §6 W6-COR: the CONTACT-CORNER CORRESPONDENCE), 2026-09-19 11:45 UTC / 7:45am ET

File: **`work/drafts/corner/W6_COR.lean`** (25,681 lines, sha256 `ebc3a942b8dc1a54…`) = `W5_Assembled.lean` (25,237 lines,
`69b01559712ba9b7…`) + ONE inserted block + ONE body replacement:
`diff W5_Assembled.lean W6_COR.lean | grep '^[0-9]'` = **`25067a25068,25503`** (436 lines, `section W6Cor … end W6Cor`, inside
`section W5Row` ⊂ `section W4Bigon`, immediately BEFORE the docstring of `w5r_box_corners`) and **`25073c25509,25517`** (the
`  sorry` body of `w5r_box_corners` → a 9-line proof).  Every other line is byte-identical; no statement, name or docstring
touched; no import, `open`, `attribute` or top-level `variable` added; every new top-level name carries `w6c_` (10 declarations).

**Compile** (`cd work/lean && lake env lean ../drafts/corner/W6_COR.lean`): **0 errors**, exactly **9** `declaration uses sorry`
warnings = W5's 10 minus the one at `w5r_box_corners` (4439 `s7q_box_ret`, 18055 `s7z_F_exists`, 18496 `s7z_returned_of_FSector`,
23881 `w5b_box_returnedData`, 24278/24287/24304 BR's three turn/curl boxes, 25534 `w5r_box_branch`, 25629 `s7_bigon_law_at`);
see §4 for the timing.  **`grep -c sorry`: 22 → 21** (the replaced body; the block contains no `sorry` token, not even in prose,
and no `#print`/`#check`).  `tools/stmt_check.py W6_COR.lean --base W3_Skeleton.lean`: 5/5 frozen statements byte-identical and
unique (PASS); `tail -n 43` identical to `W3_Skeleton.lean`.  `tools/clash_scan.py W6_COR.lean`: `duplicates_in_assembled: []`,
`full_name_clashes: {}` (45 short-name coincidences in different namespaces; the scanner calls `w6c_` "UNPREFIXED" as it does
`w4_`/`w5t_`, cosmetic).  Nothing written under `work/lean`; `lake build` never run.

**CLOSED: `w5r_box_corners` (25507).**  `#print axioms` (scratch copy `<scratchpad>/w6cor/W6_COR_axioms.lean` = the file + 19
`#print axioms` lines after `end SM`, 70 s, log `axioms.log`):

| declaration | axioms |
|---|---|
| **`w5r_box_corners`**, `w6c_cornerData`, `w6c_glued_corners_wall`, `w6c_glued_corners`, `w6c_turn_M`, `w6c_turn_M_of_gt`, `w6c_turn_firstHalf_zero`, `w6c_turn_secondHalf_zero`, `w6c_interlacing_iff`, `w6c_chi_P₂` | **`[propext, Classical.choice, Quot.sound]` — no `sorryAx`, no literature axiom** |
| `w4_box_returnedRows` (B2') | standard + `sorryAx` + `lit_homfly, lp_lm, lp_lm_uniqueness` — the `sorryAx` now enters ONLY through `w5_box_branch` ← BR's `w5b_box_interlacingTurnData` (24278), `w5b_box_noninterlacingTurnData` (24287), `w5b_box_curlData` (24304) |
| `w5r_box_transport` | standard + `lit_homfly, lp_lm, lp_lm_uniqueness` (unchanged) |
| `w5r_box_contact` | standard (unchanged) |
| `s7_bigon_law_at`, `thm_C_S7` | `sorryAx` exactly as in W5 (the leaf's own `sorry`; not wired, merge rule) |

## 1. What is proved (W6_COR 25068-25503; variables `hn g {M a} h h₁ h₂` of `section W4Bigon`)

The key observation (docstring 25070-25084): **`w5r_CornerData` asks for a turn-preserving BIJECTION of corner-index sets, not
for the cyclic order**, so the "merge of the corner lists cut at the vertex-`0` corners with `μ_M` inserted" of §6 is not
needed as a list statement.  The corners of `q_H` are characterised as a SET by `mem_ccpCornerList` (owner + `IsTrueCorner`),
and RT's `w5t_transport` gives owners (`owner_inl/inr_eq_qH_iff`) and the mark map's image; `IsTrueCorner` is "vertex or
selected-crossing visit", so true corners correspond under the mark map except at the two vertex-`0` marks (their images
`y_a`, `x_ℓ` are visits of the UNSELECTED newborns) and at `μ_M` (off the image).  The bijection is then built from
`ccpCornerMark_exists` / `ccpCornerMark_injective`.  RT's Part-D rotation machinery (`w5t_ct_*`) is NOT needed and not used.

| section / declaration | content |
|---|---|
| `W6CorAbstract` (25086-25204): `w6c_idx`, `w6c_idx_spec` | the chosen index of a true corner owned by `q` (`ccpCornerMark_exists`) |
| **`w6c_glued_corners`** (25105) | ABSTRACT: injections `ι₁ : Mark L₁ → Mark Q`, `ι₂` with disjoint ranges, carriers `q, q₁, q₂` with `hown₁/₂ : owner (ι c) = q ↔ owner c = q_i`, contact marks `c₁ c₂` (true corners of `q₁, q₂` whose images are NOT true corners of `T`), `hcorner₁/₂` (true corners correspond off `c_i`), `μ` (a true corner of `q` off both images), `hoff` (every off-image true corner of `q` is `μ`) ⟹ `∃ j j₁ j₂ (e : {i ≠ j₁} ⊕ {i ≠ j₂} ≃ {i ≠ j}), (∀ x, ccpCornerMark q (e x).1 = Sum.elim (ι₁ ∘ ccpCornerMark q₁) (ι₂ ∘ ccpCornerMark q₂) x) ∧ ccpCornerMark q₁ j₁ = c₁ ∧ ccpCornerMark q₂ j₂ = c₂ ∧ ccpCornerMark q j = μ` (`Equiv.ofBijective`; injective by `ccpCornerMark_injective` + `hinj`/`hdisj`, surjective by `hoff` + `hcorner` + `ccpCornerMark_exists`) |
| `W6CorTurnM` (25206-25292): **`w6c_turn_M_of_gt`** | `y_a < x_a → turn Q M = χ_Q(a, a+1, M)`: B3's `s7o_turn_M_of_lt` (`turn Q M = −χ` for `x_a < y_a`) with the determinant identity `det(d_{M−1}, d_M)·(1−p')q' = −(q−p)·det(d_a, μ_M − μ_a)` read with `q − p < 0` (proof text mirrored, 70 lines) |
| `W6CorWall` (25294-25358): `w6c_chi_P₂` | `χ_{P₂(t)}(a, a+1, M) = −s₀` (`vertex_contact_signs` on `h.1`, by `s7f_side`) |
| **`w6c_turn_firstHalf_zero`** | `turn λ₁ 0 = s₀`: `= markTurn P₂ (inr y_a)` (`s7fb_markTurn_ya`) `= crossingSign P₂ a M = −crossingSign P₂ M a = −χ_{P₂} = s₀` (`s7e_twin_va`, `crossingSign_swap`, `s7o_crossingSign_y`) |
| **`w6c_turn_secondHalf_zero`** | `turn λ₂ 0 = s₀`: `= markTurn P₂ (inr x_ℓ)` (`s7fb_markTurn_xl`) `= crossingSign P₂ (M−1) a = −χ_{P₂} = s₀` (`s7o_crossingSign_x`) |
| `w6c_interlacing_iff` | `s7f_Interlacing hn h t ↔ param(x_a) < param(y_a)` (B3's `s7o_interlaces_iff` on `s7o_sideData … (s7f_side g M a)`, `w5t_x_eq/y_eq`) |
| **`w6c_turn_M`** | `turn P₂(t) M = if s7f_Interlacing then s₀ else −s₀` (`s7o_turn_M_of_lt` / `w6c_turn_M_of_gt`, `s7fb_xa_param_ne_ya` for the trichotomy, `w6c_chi_P₂`) |
| `W6CorData` (25360-25500): **`w6c_glued_corners_wall`** (25373) | the abstract lemma instantiated on `hRT := w5t_transport …`: `ι_i := w5t_mark ∘ inl/inr` (`w5t_mark_injective`), owners `hRT.owner_inl/inr_eq_qH_iff hη hw`, `c₁ = c₂ = inl 0`, `μ = inl M`; `hnot`: `w5t_mark_inl_zero/inr_zero` + `hRT.y_not/x_not`; `hcorner`: `w5t_mark_inl_inl/inr_inl` (vertices, `Iff.rfl`) and `w5t_mark_inl_inr/inr_inr` + `s7b_firstVisitQ_fst` + `s7b_mem_pre` (visits; `S_i = s7b_pre ι_i T` definitionally); `hμ`: `w5t_M_not_mem_range`; `hoff`: the case analysis of RT's `off_first` (`w5t_inl_mem_range` for vertices `≠ M`; `s7fb_visit_cases` for visits — `x_a`, `y_ℓ` unselected, `x_ℓ`, `y_a` images of the vertex-`0` marks, others carried by `hRT.img` + `s7b_visit_of_first/secondCrossingQ`) |
| **`w6c_cornerData`** (25477) | `w5r_CornerData hn g h h₁ h₂ t T₀` from the above: `turn_ccpCornerPolygon_eq_markTurn` on `q_H` (with `hT`) and on `L₁, L₂` (with `hT₁, hT₂`), `w5t_markTurn_first/second` for the image marks, the three contact turns |
| **body of `w5r_box_corners`** (25509-25517) | radius `min δ₁ δ₂` of `s7f_exists_bigonSplit` and `s7a2_exists_intervalLocal`; `hE, hT` from `w4_mem_EligDec`; `hT₁, hT₂` from `w4_eligibleEquiv … (hsplit t ht₁) ⟨T₀, hmem⟩` (as `w5_transportData` does) |

The Prop is proved exactly as stated in `w5r_CornerData` (24544): no deviation, no corrected form (rule 3 not triggered).
The route differs from §6's sketch in ONE respect, disclosed: **no extension of RT's abstract corner transport to the glued
cycle** (no rotation/cyclic-order statement); the bijection is set-theoretic.  Size: 436 lines against the estimate 700-1,100.

## 2. Black boxes (rule 2)

**None.**  No `w6c_` Prop is left with `sorry`; no black box of another unit is consumed.  Every consumed statement is a
PROVED theorem of `W5_Assembled.lean` or the library: RT's `w5t_transport`, `w5t_hw`, `w5t_hcx/hcy`, `w5t_x_eq/y_eq`, `w5t_mark_*`
(`_injective`, `_inl_zero`, `_inr_zero`, `_inl_inl`, `_inr_inl`, `_inl_inr`, `_inr_inr`), `w5t_inl_mem_range`, `w5t_M_not_mem_range`,
`w5t_markTurn_first/second`, the structure fields `x_not y_not img` and the owner lemmas `owner_inl_eq_qH_iff`,
`owner_inr_eq_qH_iff`; B3's `s7o_turn_M_of_lt`, `s7o_crossingSign_x/y`, `s7o_chi_legs`, `s7o_interlaces_iff`, `s7o_sideData`,
`s7o_det_*`, `s7o_sign_*`; FB2's `s7fb_markTurn_ya/xl`, `s7fb_visit_cases`, `s7fb_xa_param_ne_ya`; F's `s7f_exists_bigonSplit`,
`s7f_Interlacing`, `s7f_hP₂`, `s7f_hQC`, `s7f_lift`; A2's `s7a2_exists_intervalLocal` (`VertexLocalData.chirotopes`); W4's
`w4_mem_EligDec`, `w4_eligibleEquiv`; U110-B's `s7b_mem_pre`, `s7b_first/secondVisitQ_fst`, `s7b_visit_of_first/secondCrossingQ`;
ROW's `w5r_sgn`, `w5r_qH/L₁/L₂/T₁/T₂`; library `ccpCornerMark_exists/_injective/_owner/_isTrueCorner`, `IsTrueCorner`
(`isTrueCorner_visit`), `turn_ccpCornerPolygon_eq_markTurn`, `markTurn_inl/inr`, `crossingSign_swap`, `s7e_twin_va/vl`,
`s7e_va_edge/vl_edge`, `s7e_vl_fst`, `s7e_a_ne_leg`, `chi_edge`, `turn_det`, `crossingParameter_spec/_interior`, `s7i_signType_cases`,
`WallGerm.vertex_contact_signs`.  Nothing found false as stated.

## 3. Honest state after W6-COR: the exact remaining Props

`thm_C_S7` still carries `sorryAx` through the leaf `s7_bigon_law_at` (25629, its own `sorry`; not wired — merge rule).  Wiring the
leaf (`w4_s7_bigon_law_at_of hn g h h₁ h₂ hsing (w4_box_returnedRows hn g h h₁ h₂ hF)`) would move the source to exactly
**THREE** live declarations, all BR's (statements in W5_ASSEMBLY_REPORT §5.2-5.4; entering `w4_box_returnedRows` only through
`w5_box_branch` → `w5_branchData` → `w5b_interlacingData` / `w5b_noninterlacingData`):
1. `w5b_box_interlacingTurnData` (24278; `w5b_InterlacingTurnData` 24250) — W6-ROT (rotation field) + W6-COR (pattern fields via
   U110-C's `s7c_uniform_halves_of_interlacing` from `w5r_box_corners`' data and `wt(q_H) ≠ 0`);
2. `w5b_box_noninterlacingTurnData` (24287; `w5b_NoninterlacingTurnData` 24260) — likewise with `s7c_dissent_halves_of_noninterlacing`;
3. `w5b_box_curlData` (24304; `w5b_CurlData` 24294) — W6-CURL.

Dead (sorried, on no proved path; drop at port): `w5r_box_branch` (25534), `w5b_box_returnedData` (23881), `s7q_box_ret` (4439),
`s7z_F_exists` (18055), `s7z_returned_of_FSector` (18496).

**For W6-ROT / W6-GLUE.**  Consume `w5r_box_corners hn g h h₁ h₂ : ∃ δ > 0, ∀ t < δ, ∀ T₀ ∈ w4_EligDec, w5r_CornerData …` (call it; do
not restate).  Its `e` is set-theoretic: `ccpCornerMark q_H (e x).1 = w5t_mark (inl/inr (ccpCornerMark L_i y.1))` is available
as `w6c_glued_corners_wall` (the mark-level form, stronger than the turn-level `w5r_CornerData`) if W6-ROT needs the MARKS
of corresponding corners (e.g. to compare principal turns on the centre polygon: the image marks' positions in `P₂(t)`
are the half marks' positions carried by the mark map).  The contact turns are `w6c_turn_firstHalf_zero`,
`w6c_turn_secondHalf_zero` (both `s₀`, no interlacing hypothesis) and `w6c_turn_M`.

## 4. Method audit (D-AUTH-20260919 §2, the reassessment rule)

Not triggered: every piece compiled on its first or second attempt.  Plan decided before writing (after reading the RT block):
(i) recognise that `w5r_CornerData` needs no cyclic order → an abstract set-level bijection lemma instead of extending
`w5t_ct_*`; (ii) the contact turns through the newborn-side crossing signs (`s7fb_markTurn_ya/xl` + `s7o_crossingSign_y/x`),
avoiding the centre-polygon geometry of `s7g_turn_firstHalf_zero`/`s7g_sign_det_a_M` — the sliding unit's `hetaM`
(`turn λ₂ 0 = −χ(a, a+1, M+1)`) was a warning that the halves' signs need the bigon condition `h.2`, which the crossing-sign
route encodes automatically; (iii) the non-interlacing turn at `M` as a mirrored copy of `s7o_turn_M_of_lt`.  Compile-fix
rounds: pieces 1, 2, 4 none; piece 3 one (`w6c_chi_P₂` does not take `hn`, which the section does not include).  Four scratch
pieces compiled against a prefix olean of `W5_Assembled.lean[1..25067]` + closing `end`s (`<scratchpad>/w6cor/pfx/W6Prefix.olean`,
124 s to build; 13-17 s per probe; `P1.lean`-`P4.lean`, the assembled `P4.lean` with `#print axioms` standard for
`w6c_box_corners_test`), then assembled once (`assemble` step inline, python) and compiled in place.

## 5. Verification record

```
cd work/lean && lake env lean ../drafts/corner/W6_COR.lean        # 0 errors; 9 × "declaration uses sorry" (4439 18055 18496 23881 24278 24287 24304 25534 25629); 83 s
grep -c sorry work/drafts/corner/W5_Assembled.lean work/drafts/corner/W6_COR.lean       # 22 / 21
diff work/drafts/corner/W5_Assembled.lean work/drafts/corner/W6_COR.lean | grep '^[0-9]'   # 25067a25068,25503  25073c25509,25517
python3 tools/stmt_check.py W6_COR.lean --base W3_Skeleton.lean    # 5/5 PASS ; tail -n 43 identical to W3_Skeleton.lean
python3 tools/clash_scan.py W6_COR.lean                           # duplicates_in_assembled: [], full_name_clashes: {}
<scratchpad>/w6cor/lean.sh W6_COR_axioms.lean                    # w5r_box_corners and all w6c_*: [propext, Classical.choice, Quot.sound]
```
