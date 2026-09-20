# W4_S1P_REPORT — unit S1P (prefix `s7u_`; serving `s7_sliding_law_at`), 2026-09-19 05:55 UTC / 1:55am ET (wave 4, first unit under D-AUTH-20260919)

File: **`work/drafts/corner/W4_S1P.lean`** (9,356 lines, sha256 `e389a092e6abdf8ef0de204ad66097326a0382c8e7be2035d9031336842a13ff`) =
`W3_Assembled.lean` (8,958 lines, `109050d9…`) with ONE `s7u_` block of 398 lines (lines 4841-5238) inserted immediately BEFORE the
docstring of `s7_sliding_law_at` (now line 5239; the same anchor SPLIT/RET/ROT used).  Lines 1-4840 and the whole suffix are
byte-identical to `W3_Assembled.lean` (`diff` of both ranges empty); the last 43 lines are byte-identical to `W3_Skeleton.lean`; the five
frozen declarations, every existing statement, name and docstring untouched; both leaf `sorry`s untouched.
**Compile** (`cd work/lean && lake env lean ../drafts/corner/W4_S1P.lean`, 41 s at load ≈ 1.5): **0 errors, 0 warnings other than 13
`declaration uses 'sorry'`** = the 12 of `W3_Assembled` (shifted by +398 after line 4840: 4437, 4519, 5242, 5769, 5786, 6123, 7370, 7416,
8998, 9018, 9037, 9304) + ONE new: `s7u_box_carriers'` (5161, the S3' black box).  `grep -c sorry`: 20 before → 21 after (the one new
body; no new prose mention).  Name-clash scan: `grep -rcE "\bs7u_" work/lean/SM/` → 0 hits; no duplicate top-level name in the file.

## 0. In one paragraph

**S1' is PROVED**: `s7u_box_ret'` (line 5026) is the corrected first-return box, both sides, on standard axioms only (`propext`,
`Classical.choice`, `Quot.sound`).  It replaces ROT's `s7q_box_ret` (= Prop S1 `w3_SlidingRet`), which is FALSE as stated on the leg-`M`
side (W3_RET_REPORT §2, rule 4); that declaration keeps its `sorry` (rule 3), as does `w3_SlidingRet` — nothing below consumes them.
RET is now fully consumed: `s7r_slidingTransport_side` (the `s7b_SlidingTransport` at `s7e_vl` on the side carrying `{a, M−1}`) and
`s7r_slidingTransport_side'` (the `s7r_SlidingTransport'` at `s7e_va` on the side carrying `{a, M}`) are instantiated on every row of
the contact sector below one radius, with `hSimg := s7r_img_of_decomposition` and the half supports by `s7q_pre_of_symm`.  ROT's
coefficient/row transport is copied onto the corrected structure (`s7u_coef_first'`, `s7u_coef_second'`, `s7u_rowData_of_transport'`,
`s7u_CarrierData'`, `s7u_rowData_of_carrierData'`).  **S3' is stated** as the Prop `s7u_SlidingCarriers'` (5113) with the black box
`s7u_box_carriers'` (5161) for unit S3G, and the glue is PROVED: `s7u_box_rows'_of : S3' → ⟨statement of s7q_box_rows⟩` (5168) and
`s7u_sliding_law_at_of : S3' → ⟨statement of s7_sliding_law_at⟩` (5219).  The sliding leaf therefore now waits on exactly ONE Prop: when
S3G lands, `s7_sliding_law_at … := s7u_sliding_law_at_of hn g h h₁ h₂ (s7u_box_carriers' hn g h h₁ h₂)`.  Zero failed attempts: the block
compiled on its first elaboration (against a prefix olean of lines 1-4839, 18 s), then in place.

## 1. Delivered (all inside `section VertexEdge`, `{n : ℕ} [NeZero n]`)

| line | declaration | status | axioms |
|---|---|---|---|
| 4841-4859 | block header (prose) | — | — |
| 4861 | `section S7UTransport` (the variable block of ROT's `S7QTransport`, with `{va : Visit Q}`) | | |
| 4878 | `theorem s7u_coef_first' (hT : s7r_SlidingTransport' hn hQ hsep hm hQC h₁ h₂ S S₁ S₂ va) (hsplit : s7b_PivotSplit … va.1) hS hS₁ q q₁ (hq : hT.componentEquiv q = Sum.inl q₁) (hcut : s7q_CutFirst …) : cornerCoefficient hn hQ S q hS = cornerCoefficient … q₁ hS₁` | PROVED (ROT's text on `s7r_SlidingTransport'.carrierCrossings_eq_img_first`) | std + `lit_homfly`, `lp_lm`, `lp_lm_uniqueness` |
| 4902 | `theorem s7u_coef_second'` | PROVED | same |
| 4928 | `theorem s7u_rowData_of_transport' (hT : s7r_SlidingTransport' …) hsplit hS hS₁ hS₂ a₀ m₀ τ hc₁ hc₂ hw hw₀ : s7q_RowData …` | PROVED | same |
| 4953 | `section S7UBoxes` (`variable (hn) (g : WallGerm n) {M a} (h : g.SlidingAt M a)`) | | |
| 4967 | `def s7u_CarrierData' hn g h hQ hQC h₁ h₂ (hT : s7r_SlidingTransport' hn hQ h.1.1 h.1.2.2.2.1 hQC h₁ h₂ S S₁ S₂ va) a₀ m₀ τ : Prop` | = `s7q_CarrierData` with the primed `hT` (same four clauses on `hT.componentEquiv`) | — |
| 4993 | `theorem s7u_rowData_of_carrierData' t b h₁ h₂ (hT : s7r_SlidingTransport' hn (s7a_sideGeneric g b) h.1.1 h.1.2.2.2.1 (s7e_hQC hn g h t b) h₁ h₂ S S₁ S₂ va) hsplit hS hS₁ hS₂ (hord : s7q_OrderAgrees hn g h t b) (hd : s7u_CarrierData' …) : s7q_RowData …` | PROVED (`s7u_rowData_of_transport'` + `s7q_cutFirst_of`/`s7q_cutSecond_of`) | std + the three |
| **5026** | **`theorem s7u_box_ret' h₁ h₂` — S1'** (statement §2) | **PROVED** | **standard only** |
| 5113 | `def s7u_SlidingCarriers' h₁ h₂ : Prop` — **S3'** (statement §3) | Prop | — |
| 5161 | `theorem s7u_box_carriers' h₁ h₂ : s7u_SlidingCarriers' hn g h h₁ h₂` | **BLACK BOX (`sorry`, for unit S3G)** | std + `sorryAx` |
| 5168 | `theorem s7u_box_rows'_of h₁ h₂ (hcar : s7u_SlidingCarriers' hn g h h₁ h₂) : ⟨the statement of s7q_box_rows, verbatim⟩` | PROVED (S1' + `s7q_box_order` + S3') | std + the three |
| 5219 | `theorem s7u_sliding_law_at_of h₁ h₂ (hcar : s7u_SlidingCarriers' hn g h h₁ h₂) : ⟨the statement of s7_sliding_law_at, verbatim⟩` | PROVED (`w3_s7_sliding_law_at_of`'s proof with `s7u_box_rows'_of`) | std + the three |
| 5237 | `end S7UBoxes` | | |

`#print axioms` (scratch copy `<scratchpad>/s1p/W4_S1P_axioms.lean` = the file + ten `#print axioms` lines after `end SM`, 41 s):
`s7u_box_ret'` → `[propext, Classical.choice, Quot.sound]`; `s7u_coef_first'`, `s7u_coef_second'`, `s7u_rowData_of_transport'`,
`s7u_rowData_of_carrierData'`, `s7u_box_rows'_of`, `s7u_sliding_law_at_of` → standard + `SM.lit_homfly`, `SM.lp_lm`, `SM.lp_lm_uniqueness`
(the same footprint as ROT's `s7q_rowData_of_transport` / `w3_s7_sliding_law_at_of`: it comes from `s7d_cornerCoefficient_eq_of_cut` and
`s7e_sliding_law_at_of_contact`); `s7u_box_carriers'` → standard + `sorryAx` (its own body); `s7_sliding_law_at` and `thm_C_S7`
unchanged (still `sorryAx` through both leaves; registered axioms only otherwise).

## 2. S1' — the corrected first-return box (`s7u_box_ret'`, PROVED)

```
∃ δ : ℝ, 0 < δ ∧ ∀ t : g.SideParameter, t.val < δ →
  ∀ (hsplitm : s7q_Split hn g h t false h₁ h₂ (s7e_xm hn h t)) (hsplitp : s7q_Split hn g h t true h₁ h₂ (s7e_xp hn h t))
    (q : {S₁ // IsDecomposition … h₁ S₁} × {S₂ // IsDecomposition … h₂ S₂}),
  (s7e_leg g M a = false →
    (∃ vm : Visit P₋, vm.1 = s7e_xm hn h t ∧ s7b_SlidingTransport hn h.1.1 h.1.2.2.2.1 (s7e_hQC hn g h t false) (s7a_sideGeneric g false) h₁ h₂ S₋ q.1.1 q.2.1 vm) ∧
    (∃ va : Visit P₊, va.1 = s7e_xp hn h t ∧ s7r_SlidingTransport' hn (s7a_sideGeneric g true) h.1.1 h.1.2.2.2.1 (s7e_hQC hn g h t true) h₁ h₂ S₊ q.1.1 q.2.1 va)) ∧
  (s7e_leg g M a = true →
    (∃ va : Visit P₋, va.1 = s7e_xm hn h t ∧ s7r_SlidingTransport' hn (s7a_sideGeneric g false) … S₋ q.1.1 q.2.1 va) ∧
    (∃ vm : Visit P₊, vm.1 = s7e_xp hn h t ∧ s7b_SlidingTransport … true … S₊ q.1.1 q.2.1 vm))
```
with `S₋ := ((s7b_slidingDecompositionEquiv … false … (s7e_xm hn h t) hsplitm).symm q).1`, `S₊` likewise on `true` — i.e. ROT's
`s7q_box_ret` with the leg case split and the side carrying `{a, M}` typed as `s7r_SlidingTransport'`.  Note the ARGUMENT ORDER of the
primed structure: `s7r_SlidingTransport' hn hQ hsep hm hQC h₁ h₂ S S₁ S₂ va` (RET's), versus `s7b_SlidingTransport hn hsep hm hQC hQ …`.

**Proof** (W3_RET_REPORT §3 recipe, 55 lines).  One `δ := min δ₁ δ₂` from `s7r_slidingTransport_side` / `_side'` (both are the interval
radius of `s7a2_exists_intervalLocal`, but the two theorems package it separately, so `min`).  For `t hsplitm hsplitp q`: the rows'
data `hSm := (… .symm q).2 : IsDecomposition ∧ x₋ ∈ S₋`, the half supports `⟨em₁, em₂⟩ := s7q_pre_of_symm … q` (`q.1.1 = s7b_pre … S₋`,
`q.2.1 = s7b_pre … S₋`), the image hypotheses `himgm := s7r_img_of_decomposition hn (s7a_sideGeneric g false) h.1.1 h.1.2.2.2.1
(s7e_hQC …) h₁ h₂ _ (s7e_xm hn h t) hsplitm hSm.1 hSm.2` (the `hsplit` of the box IS `s7q_Split`, which unfolds to `s7b_PivotSplit` by
defeq; accepted without `unfold`).  Case `hl : s7e_leg g M a = false`: `hcm : IsCrossing P₋ {a, contactLeg false M}` by `rwa [hl]` at
`s7e_hxm hn g h t`, `hcp : IsCrossing P₊ {a, contactLeg true M}` by `rwa [hl]` at `s7e_hxp hn g h t` (`!false` closes by defeq in
`exact`); `(s7e_va hcm).1 = s7e_xm hn h t` by `Subtype.ext (by simp only [s7e_va_fst_val, s7e_xm_val, hl])` (the `xp` twin adds
`Bool.not_false`); witnesses `s7e_vl hcm` (with `s7e_vl_fst`) and `s7e_va hcp`; the goals after `rw [em₁, em₂]` are exactly the two
germ theorems' conclusions with `hxS`/`hSimg` rewritten by the `.1`-equalities.  Case `true` symmetric (`Bool.not_true`).

## 3. S3' — the restated carriers box (`s7u_SlidingCarriers'`, BLACK BOX `s7u_box_carriers'` for unit S3G)

```
∃ (first : Bool) (τ : SignType) (δ : ℝ), τ ≠ 0 ∧ 0 < δ ∧ ∀ t < δ, ∀ hsplitm hsplitp q,
  (g.contactSign M a ∈ s7q_contactTurns hn g h h₁ h₂ q.1.1 q.2.1 first) ∧
  (-g.contactSign M a ∈ s7q_contactTurns hn g h h₁ h₂ q.1.1 q.2.1 (!first)) ∧
  (s7e_leg g M a = false →
    (∀ vm (hT : s7b_SlidingTransport … false … S₋ q.1.1 q.2.1 vm), vm.1 = s7e_xm hn h t →
      s7q_CarrierData hn g h (s7a_sideGeneric g false) (s7e_hQC hn g h t false) h₁ h₂ hT (s7q_contactPoint … first) (s7q_contactTurns … first) τ) ∧
    (∀ va (hT : s7r_SlidingTransport' hn (s7a_sideGeneric g true) h.1.1 h.1.2.2.2.1 (s7e_hQC hn g h t true) h₁ h₂ S₊ q.1.1 q.2.1 va), va.1 = s7e_xp hn h t →
      s7u_CarrierData' hn g h (s7a_sideGeneric g true) (s7e_hQC hn g h t true) h₁ h₂ hT (s7q_contactPoint … (!first)) (s7q_contactTurns … (!first)) τ)) ∧
  (s7e_leg g M a = true →
    (∀ va (hT : s7r_SlidingTransport' … false … S₋ q.1.1 q.2.1 va), va.1 = s7e_xm hn h t → s7u_CarrierData' … false … hT (… first) (… first) τ) ∧
    (∀ vm (hT : s7b_SlidingTransport … true … S₊ q.1.1 q.2.1 vm), vm.1 = s7e_xp hn h t → s7q_CarrierData … true … hT (… (!first)) (… (!first)) τ))
```
= ROT's `s7q_box_carriers` (whose `sorry` also stays: its `hT` on the leg-`M` side is the unrealisable `s7b_SlidingTransport`) with the leg
case split of §2 and the primed transport / primed carrier data on the side carrying `{a, M}`.  The memberships, `first`, `τ` and the
leg-`(M−1)` side are ROT's verbatim.  **Notes for S3G.**  (i) The theorem's type is the def `s7u_SlidingCarriers' hn g h h₁ h₂`: start with
`unfold s7u_SlidingCarriers'` (or `show`/`refine ⟨first, τ, δ, hτ, hδ, fun t ht hsplitm hsplitp q => ?_⟩` after `unfold`).  (ii) The
expected `first` is `!s7e_leg g M a` (docstring of `s7q_contactPoint`: `λ₁` carries the extra corner on `P₋` when the leg of `x₋` is `M−1`);
a single choice serves both cases (`cases hl : s7e_leg g M a` then `simp only [hl] at *`).  (iii) On the primed side the contact-carrier
identifications EXCHANGE halves (W3_RET_REPORT §1.D): `hT.componentEquiv_owner_vertexM` : `Q`'s carrier through `μ_M` ↦ `inr (owner λ₂ S₂
(inl 0))`, `hT.componentEquiv_owner_pivot` : `Q`'s carrier through `v_a` ↦ `inl (owner λ₁ S₁ (inl 0))`; the extra corner there is the leg
visit `v_ℓ` (skipped by `s7r_slidingMark'`), on the unprimed side it is `v_a`.  (iv) `s7u_CarrierData'` has the four clauses of
`s7q_CarrierData` in the same order (`hbit`+`hr` per `inl` carrier, per `inr` carrier, weights off `a₀`, refined weight).  (v) Everything the
box docstring of `s7q_box_carriers` names (`s7q_CutFirst/_Second` decoding — NOT needed here, it is supplied by the glue from
`s7q_box_order` —, `s7d_positiveOverBit_eq_of_smul`, `HalvesData.cut_segments`, `s7q_carrierRotation_eq_of_merge/_of_perturb`,
`s7q_principal_three_a/_b`, `s7q_two_turn_perturb`, `s7i_principalTurn_eq_of_edges_pos_smul`, `s7q_carrierWeight_eq_of_merge/_of_perturb`,
`s7c_carrierWeight_eq_sel`) is proved in the ROT block above the anchor; ROT §6 lists the remaining geometry ((a)-(c), 1,300-2,050 lines).

## 4. The glue (PROVED)

* `s7u_box_rows'_of` (5168): ROT's `s7q_box_rows` proof with the three inputs `s7u_box_ret'` (proved), `hcar : S3'`, `s7q_box_order`
  (proved); after the three `obtain`s and `refine ⟨hs₁, hs₂, ?_⟩`, `cases hl : s7e_leg g M a`; in each case the two row data are
  `s7q_rowData_of_carrierData … hTm (by rw [hvm]; exact hsplitm) _ q.1.2 q.2.2 (hord t ht₃ false) (hdm vm hTm hvm)` on the
  `s7b_SlidingTransport` side and `s7u_rowData_of_carrierData' … hTp (by rw [hva]; exact hsplitp) _ q.1.2 q.2.2 (hord t ht₃ true)
  (hdp va hTp hva)` on the `s7r_SlidingTransport'` side (sides swapped in the `true` case).  Conclusion = the statement of `s7q_box_rows`
  verbatim, so `s7q_hterm_of_rows` consumes it unchanged.
* `s7u_sliding_law_at_of` (5219): `w3_s7_sliding_law_at_of`'s proof with `s7u_box_rows'_of` in place of `w3_box_rows_of`
  (`s7e_sliding_law_at_of_contact` ← `s7q_box_split` + `s7q_hterm_of_rows` + `s7e_contactSector_of_pivotSplit`).  Conclusion = the frozen
  leaf statement verbatim.  **Leaf closure when S3G lands:** `s7_sliding_law_at hn g M a h h₁ h₂ := s7u_sliding_law_at_of hn g h h₁ h₂
  (s7u_box_carriers' hn g h h₁ h₂)` (the leaf's `M a` are explicit; `h : g.SlidingAt M a` fixes them).
* NOT re-typed (frozen, rule 1): `w3_box_rows_of` (4768), `w3_s7_sliding_law_at_of` (4809), `w3_s7_sliding_law_at_of₂` (4829) keep their
  `hret : w3_SlidingRet` hypothesis; they are superseded by `s7u_box_rows'_of` / `s7u_sliding_law_at_of` and can be dropped at port
  together with `w3_SlidingRet`, `w3_SlidingRet_of_box`, `s7q_box_ret`, `w3_SlidingCarriers`, `w3_SlidingCarriers_of_box`, `s7q_box_carriers`
  (the port list of W3_ASSEMBLY_REPORT §6 changes accordingly: `SM/CS7Units.lean` = lines 24-5238 minus those six + the bigon blocks).

## 5. Deviations from the brief, disclosed

1. **Anchor.** The block sits before the docstring of `s7_sliding_law_at` (the leaf this unit serves; SPLIT/RET/ROT's anchor), not before
   `s7q_box_ret`'s: the glue consumes `s7q_box_order`, `s7q_rowData_of_carrierData`, `s7q_hterm_of_rows` and `s7q_box_split`, which are
   defined AFTER `s7q_box_ret` in `section S7QBoxes`.  Nothing existing was moved.
2. **Transport copy is smaller than estimated** (170 lines, not ~380): `s7q_CutFirst`, `s7q_CutSecond`, `s7q_cutFirst_of`,
   `s7q_cutSecond_of` and the key-decoding lemmas do not mention the transport structure (they are stated on `q : Component hn hQ S`,
   `q₁`, `hord`, `hbit`, `hr`) and are reused as they stand; only `s7q_coef_first/_second`, `s7q_rowData_of_transport` (transport section),
   `s7q_CarrierData`, `s7q_rowData_of_carrierData` (S7QBoxes) mention `hT` and were copied.
3. **S3' is stated as a Prop def + a `sorry` theorem** (`s7u_SlidingCarriers'` / `s7u_box_carriers'`), so that the glue takes a
   hypothesis of the def's type and S3G replaces exactly one body (rule 1 for the next unit).  ROT's shape (verbatim theorem statement)
   would have duplicated the 45-line statement.
4. `s7q_box_ret` and `s7q_box_carriers` keep their `sorry` (rule 3 for the first: false as stated; the second is superseded, not false: on the
   leg-`M` side no `s7b_SlidingTransport` instance with `vm.1 = x` exists (the same counter-derivation), so its `∀ hT` clause there is
   VACUOUS and the box carries no usable content for that side).  `w3_SlidingRet`, `w3_SlidingCarriers` and their shape checks are
   untouched (frozen); `w3_SlidingRet_of_box` / `w3_SlidingCarriers_of_box` still carry `sorryAx` and remain off every proved path.

## 6. Method audit (reassessment discipline)

Zero failed attempts.  Method: prefix olean (`lake env lean --root=<scratch> -o S1PPrefix.olean` on lines 1-4839 + closers, 18 s), the
block compiled against `import S1PPrefix` (`LEAN_PATH=$LEAN_PATH:<scratch> lean S1PTest.lean`, 11 s, 0 errors on the first run), then the
insertion and the full compile (41 s).  No `set`/`▸` was needed: `rw [em₁, em₂]` on the goal and `exact` on the germ theorems' conclusions
unify through `s7q_Split ≡ s7b_PivotSplit` and the `.symm q` projections by defeq.  Pitfalls (v4.34.0-rc2): `lake env lean -o` requires
the input under the root — pass `--root=<dir>`; `lake env --dir` fails on toolchain resolution, run from `work/lean` instead.

## 7. Black boxes after this unit (the sliding leaf)

| box | line | status |
|---|---|---|
| `s7u_box_carriers'` (S3', NEW) | 5161 | **the one remaining input of the sliding leaf** (unit S3G; ROT (a)-(c) geometry on the corrected transports) |
| `s7q_box_ret` (S1, ROT) | 4437 | FALSE as stated on the leg-`M` side (W3_RET §2); superseded by `s7u_box_ret'`; off every proved path; drop at port |
| `s7q_box_carriers` (S3, ROT) | 4519 | superseded by `s7u_SlidingCarriers'`; off every proved path; drop at port |
| `s7_sliding_law_at` (leaf) | 5242 | closes as `s7u_sliding_law_at_of hn g h h₁ h₂ (s7u_box_carriers' hn g h h₁ h₂)` once S3G lands |

Bigon side untouched (`s7f_exists_*` 5769/5786/6123, `s7s_clear_local` 7370, `s7s_wallTriangleData_of_bigon` 7416, `s7z_*` 8998/9018/9037,
`s7_bigon_law_at` 9304).

## 8. Reproduce

`cd work/lean && lake env lean ../drafts/corner/W4_S1P.lean` → exactly 13 lines `declaration uses 'sorry'` (4437, 4519, 5161, 5242, 5769,
5786, 6123, 7370, 7416, 8998, 9018, 9037, 9304), exit 0.  `grep -c sorry ../drafts/corner/W4_S1P.lean` → 21.  Frozen text:
`diff <(sed -n 1,4840p W3_Assembled.lean) <(sed -n 1,4840p W4_S1P.lean)`, `diff <(sed -n 4841,8958p W3_Assembled.lean) <(sed -n 5239,9356p
W4_S1P.lean)`, `diff <(tail -n 43 W3_Skeleton.lean) <(tail -n 43 W4_S1P.lean)` — all empty.  Axioms: append the ten `#print axioms SM.s7u_*`
/ `SM.s7_sliding_law_at` / `SM.thm_C_S7` lines after `end SM` in a scratch copy and run it from `work/lean` (41 s; results in §1).
`python3 tools/stmt_check.py` does not exist in this package (no target-row statement is touched by this unit; the frozen-text diffs above
are the applicable check).  Timeline: 05:33Z author response received (recorded AN L6520), 05:46Z start, 05:50Z block compiles against
the prefix, 05:52Z in-place full compile clean, 05:55Z report.
