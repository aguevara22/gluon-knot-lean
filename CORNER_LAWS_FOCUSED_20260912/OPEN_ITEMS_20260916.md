# OPEN_ITEMS_20260916.md — the complete register of open items, disclosures and caveats at the close of the 2026-09-15/16 execution

Written 01:51 UTC 2026-09-16 / 9:51pm ET (2026-09-15) by the synthesizer agent (Claude Code, tmux `side`, on Mark's RunPod home pod) from 306 raw findings of six
finder agents plus a verification pass over the files named below. It is a REGISTER, not a proof: nothing here changes any accepted
row. Read it together with `work/RESUME_FOR_NEXT_AGENT.md` (the operational guide, rewritten the same day) and `FINAL_REVIEW.md`
(root, 1276 lines, regenerated 2026-09-16 00:56Z).

**Repair pass 02:24Z UTC 2026-09-16 / 10:24pm ET (2026-09-15).** Two adversarial critics reviewed this register and the RESUME; their 35 findings were each
verified against the cited source and applied in place (§A-01/02/03/10/12/15/16/18/19, §B-02/04/06, §C-03/05/14, §D-01/37/49/53/54/56, new
rows D-73..D-79, §E-08/09/11/15/23, new §E-28, §F-03/07/08/13/14, new §F-20, §G-05/10, the owner index). The "Critic items rejected" note at
the end of the file lists the findings whose own locators had to be corrected. Nothing below this line changes an accepted row.

**Conventions.** ROOT = `/workspace/repos/lean/lean_repo/LEAN_HANDOFF_20260912_RESUME/CORNER_LAWS_FOCUSED_20260912`; every
relative path below is under ROOT. `AN L…` = line numbers in `work/AUTHOR_NOTES.md` (6479 lines at closing; the 2026-09-15/16 entries are
L5144-6479, headings listed in §F-06). `FR §…` = sections of the root `FINAL_REVIEW.md`. Line numbers in Lean files and drafts are as
of 2026-09-16 (files unchanged since 00:59Z 2026-09-16). "Row numbers" are `tools/claims.py` numbers (claims.py "#" ≠ map index:
`cp:finite-contact-path` is 91 in claims.py and 95 in the map; `src:contact` is m97). "The nine registered axioms" = `propext`,
`Classical.choice`, `Quot.sound` + the six literature constants `SM.lit_homfly`, `SM.lit_homfly_descent`, `SM.lp_lm`,
`SM.lp_lm_uniqueness`, `SM.ng_finite_word`, `SM.src_contact` (six constants for FIVE literature interfaces, see §B). Every item says who
decides: **author** (the collaborator who speaks as the author, reached through Mark), **executor** (any next agent may do it inside the
package rules), or **none** (disclosure only).

**State the register describes** (verified against `work/checks/dev-check-FINAL-20260916.json`, `work/checks/stage-1.json`,
`work/checks/stage-all-check-20260916-0032.log`, `work/progress-watch.log` and `work/lean/lean-declarations.json`): claims verified
124/132 (93.9%); checklist 184/192 accepted, 0 implemented-awaiting-review, 8 pending; final targets 5/8 (`prop:C-chamber`,
`prop:C-silent`, `thm:C-S3`, `thm:C-S5`, `thm:C-soft` accepted; `thm:C-S7`, `Bridge:theorem`, `SM:corner_laws_and_soft` open);
development checker passed (184 mapped, 41 658 audited, no unregistered axiom, no `sorryAx`); `python3 tools/check_lean.py work/lean
--all` and `--stage 1` FAIL by design ("stage is incomplete; unaccepted rows: Bridge:theorem, R:cv_theorem, R:extreme_selected,
SM:corner_laws_and_soft, cor:C-inherits, lem:gauss-two-discs, thm:C-S7, thm:comparison"); `verify_bundle.py` PASS (191 files);
`work/lean` = 697 `.lean` files (648 SM, 32 CV, 11 RProof, 4 Bridge, 2 Supplemental), 295 911 lines, zero `sorry`. No construction is in
flight; both stopped branches (110 → 127/128 → 184 and 177 → 178 → 183) wait for the author (§G).

**How the eight pending rows hang together.**
```
57  lem:gauss-two-discs                     deferred by the author (D-GAP2 item 5)                          §A-01
110 thm:C-S7  ─┬─► 127 thm:comparison  ─┐   110 kernel-proved modulo 5 named Props (S1 S3 B1 B2 B3)          §A-02..A-12
               └─► 128 cor:C-inherits  ─┴─► 184 SM:corner_laws_and_soft (needs 110, 128 AND 183)             §A-13..A-14, A-20..A-21
177 R:extreme_selected ─► 178 R:cv_theorem ─► 183 Bridge:theorem ─► 184                                        §A-15..A-19
```

---

## A. Unaccepted rows and their named leaves

### A-01 — Row 57 `lem:gauss-two-discs`: deferred by the author; nothing built in this period
- **Status.** Pending, no fixed name (`work/lean/lean-declarations.json`: `declaration ""`, `module ""`). The author's instruction
  (D-GAP2 item 5, AN L5156: "Row 57 stays deferred" — L5152-5153 are items 2-3 of the quoted instruction); listed among the eight unaccepted rows by the stage check
  (`work/checks/stage-all-check-20260916-0032.log`); AN L6450, L6479 ("Open for the author … (c) row 57").
- **Proved.** Nothing new. Its non-GAP-2 consumer 104 was proved without it on 2026-09-14 (D-ER1); its other consumer 105 (i) is proved
  unconditionally by the corner lane's `corner_values_i` (FR §3 pending table, D-CM-5 at AN L5710-5711). Blueprint edges 57 → 104 and
  57 → 105 are therefore not realised by the proof routes (FR §5 item 14; the blueprint is frozen).
- **Open.** The whole row: PL Schoenflies on S² (`work/drafts/pldiscs/PLDISCS_FEASIBILITY.md` §2.4, per FR §3).
- **Size.** 12-20k lines (the 2026-09-14 feasibility study; not re-estimated in 2026-09-15/16).
- **Resume.** Only on the author's explicit acceptance of the cost: read `work/drafts/pldiscs/PLDISCS_FEASIBILITY.md`, then the lane
  pattern of `work/RESUME_FOR_NEXT_AGENT.md` §5. Search AN before L5144 for the row's history (`grep -n 'gauss-two-discs' work/AUTHOR_NOTES.md`).
- **Decision.** author (§G-09).

### A-02 — Row 110 `thm:C-S7` (fixed name `SM.thm_C_S7 : CS7Data`): kernel-proved modulo five named Props; corner construction STOPPED by audit A-110-1
- **Where.** Draft `work/drafts/corner/W3_Assembled.lean` (8958 lines, sha256 `109050d9…`, 0 errors, 12 `declaration uses sorry`);
  state file `work/drafts/corner/port/CS7_STATE.md` (20 lines); merge report `work/drafts/corner/W3_ASSEMBLY_REPORT.md` (240 lines; §3
  leaves, §4 axioms, §6 port recipe, §7 order of attack); unit reports `W3_RET_REPORT.md`, `W3_K_REPORT.md`, `W3_F_REPORT.md` (and the
  other units' reports next to them); skeleton `work/drafts/corner/W3_Skeleton.lean` (97 lines, compiles against the ported oleans);
  statement `CS7Data` in `work/lean/SM/CornerChainStatements.lean` (accepted module; the statement is frozen there); ported library
  `work/lean/SM/CornerChainUnits.lean` (11 842 lines), `work/lean/SM/CS7Sliding.lean` (2956 lines, no row mapped),
  `work/lean/SM/BigonDeletion.lean` (5374 lines). Audit A-110-1: AN L6079-6116 (20:46Z), concluded AN L6300-6319 (22:40Z); FR §3.1,
  FR §5 item 2, FR §6. `work/lean/SM/CS7.lean` and `SM/CS7Units.lean` do NOT exist (verified).
- **Proved (sorry-free, registered axioms only).** `thm_C_S7 : CS7Data := thm_C_S7_of_floor thm_floor` typechecks (W3_Assembled 8954)
  with `#print axioms` = the nine registered axioms + `sorryAx` through exactly the two branch leaves `s7_sliding_law_at` (decl 4844,
  `sorry` at 4852) and `s7_bigon_law_at` (decl 8906, `sorry` 8915). Everything else on the path is proved: `sg_daughters_products`,
  `sft_same_sign`, `sft_loop`, U110-A/B/C/D/F/G/H, A2, E (ported in `SM.CornerChainUnits`); in wave 3: SPLIT entire
  (`s7p_exists_pivotSplit` 1176; the interlacement transfer on both sides incl. `x_split`), RET entire (`s7r_slidingTransport_side` 3363,
  `_side'` 3402, the first-return law on both sides in the corrected form), ROT's angle/merge/algebra/transport sections and its boxes
  `s7q_box_split` (4367) and `s7q_box_order` (4470, = Prop S2 `w3_SlidingOrder`, `w3_SlidingOrder_of_box` 4762), F's
  `s7f_law_residual` (5895) / `s7f_law_decomposition`, SITE's `s7s_core` / `s7s_site` / `s7s_contact_sign`, BLOCK's row theorems
  (`s7k_switch_value`, `s7k_skein_on`, `s7k_extraction`, `s7k_component_value`), J's floor entries (`s7j_*_entry`), K's row algebra
  (`s7z_bigon_law_at_of`, `s7z_law_at_of_rowSector`, `s7z_bigon_law_at_of_residual`, `s7z_law_at_of_residual`). The sorry-free glue
  reduces each leaf to named Props: `w3_s7_sliding_law_at_of₂ (hret : w3_SlidingRet) (hcar : w3_SlidingCarriers)` (line 4829) and
  `w3_s7_bigon_law_at_of (hFs : w3_BigonFSector) (hR : w3_BigonReturnedRows) (hO : w3_BigonOneNewborn)` (line 8876 — `CS7_STATE.md`
  says 8854, off by 22, FR §7). Sibling rows 103/105/112 of the same lane are ACCEPTED (AN L6015-6023).
- **Open.** Five Props: S1 `w3_SlidingRet` (def 4705; must be RESTATED, §A-03), S3 `w3_SlidingCarriers` (def 4730, §A-05), B1
  `w3_BigonFSector` (def 8824, §A-06 with F's three boxes §A-07..A-09), B2 `w3_BigonReturnedRows` (def 8841, §A-10), B3
  `w3_BigonOneNewborn` (def 8859, §A-11). The 12 sorried bodies: `s7q_box_ret` 4437 (sorry 4453), `s7q_box_carriers` 4519 (4545),
  `s7_sliding_law_at` 4844 (4852), `s7f_exists_bigonSplit` 5371 (5379), `s7f_exists_twoNewbornTerm` 5388 (5405),
  `s7f_exists_ineligible_transport` 5725 (5729), `s7s_clear_local` 6972 (6981), `s7s_wallTriangleData_of_bigon` 7018 (7023),
  `s7z_F_exists` 8600 (8614), `s7z_returned_of_FSector` 8620 (8635), `s7z_oneNewborn_exists` 8639 (8642), `s7_bigon_law_at` 8906 (8915).
  Other `sorry` tokens in the file are prose — exactly 8 lines: 6 (header), 3431, 4723, 4757, 4761, 4888, 8595, 8863 (4757 and 8863 are the
  `sorryAx` mentions in the two shape-check docstrings; `grep -c sorry` = 20 = 12 terms + 8 prose; reword at port, §E-23).
  Not port-ready. Consumers 127, 128 and (through 128) 184 are INCOMPLETE for this reason alone.
- **Size.** ≈ 8-12k lines, 2-3 further waves (sliding ≈ 1.8-2.75k, bigon ≈ 6.2-9.7k; AN L6304-6312). Historical: D-CC-4 estimated
  11-15k for the whole row; the lane produced ≈ 11.8k (CornerChainUnits, shared with 103/105/112) + 3.0k (CS7Sliding) + the 9.0k draft
  and still owes the remainder (FR §7).
- **Resume (only after §G-01).** Compile check: `cd work/lean && lake env lean ../drafts/corner/W3_Assembled.lean` (expect exactly 12
  `declaration uses sorry`; 26 s idle, many minutes under load). Order of attack (W3_ASSEMBLY_REPORT §7): (1) S1'/S3 restatement on
  `s7r_SlidingTransport'` (§A-03), (2) S3 geometry (§A-05), (3) bigon via K's F-aligned route `s7z_bigon_law_at_of_residual` (§A-06),
  B2/B3 in F's vocabulary. Leaf bodies when the Props exist: `w3_s7_sliding_law_at_of₂ … S1' S3` and `w3_s7_bigon_law_at_of hn h h₁ h₂
  B1 (B2 hF) (B3 hsing)` (K's own composition line was deliberately NOT carried into the assembled file). Port recipe (§6):
  `SM/CS7Units.lean` = W3_Assembled lines 24-8804 + the two glue sections (imports `SM.CornerChainUnits SM.CS7Sliding SM.BigonDeletion
  SM.CarrierFloorRows`, all present in `work/lean/SM/`), `SM/CS7.lean` = the two leaves + `thm_C_S7_of`, `thm_C_S7_of_floor`, `theorem
  thm_C_S7 : CS7Data := thm_C_S7_of_floor thm_floor`; tools `work/drafts/corner/port/tools/{port_build.py, port_clash_scan.py,
  port_stmt_check.py}`; reword the prose `sorry` mentions first; then map `thm:C-S7` → `SM.thm_C_S7` / `SM.CS7`, checker, review (3 lenses
  + 2 refuters, disclosed readings FR-CC-1..15 at AN L5396-5472), then §A-13/A-14, then §A-20. The reproduction script `assemble.py` of
  the wave-3 merge lived in the session scratchpad and is GONE; the report's §1 ranges suffice to redo it.
- **Decision.** author: whether to fund the remainder at all (§G-01). The corner branch has consumed three waves plus one bounded wave
  without acceptance; any resumption is a new window on a branch with a stagnation history (§F-06).

### A-03 — Leaf S1 `w3_SlidingRet` (= ROT's `s7q_box_ret`): FALSE as stated on the leg-M side; must become S1' on RET's corrected `s7r_SlidingTransport'`
- **Where.** `W3_Assembled.lean`: `def w3_SlidingRet` 4705; `theorem s7q_box_ret` 4437 (sorry 4453); shape check `w3_SlidingRet_of_box`
  4758 (carries sorryAx); `structure s7r_SlidingTransport'` 2248; `s7r_slidingTransport_side'` 3402; `s7r_slidingMark'`,
  `s7r_slidingMark'_eq`; `W3_RET_REPORT.md` §2 (the defect), §3 (how to consume), §1.D (exchanged-halves API); W3_ASSEMBLY_REPORT §3.1,
  §7 item 1; AN L6304-6309.
- **Proved.** Leg-(M−1) side: `s7r_slidingTransport_side` (3363) gives `s7b_SlidingTransport … (s7e_vl hc)` for every sliding row S ∋ x
  with `hSimg`, below the radius of `s7a2_exists_intervalLocal`. Leg-M side: `s7r_slidingTransport_side'` (3402) gives the corrected
  structure `s7r_SlidingTransport'` at `s7e_va hc` with its `ret` PROVED (mark map `swap(μ_M, v_a) ∘ s7b_slidingMark … v_a`: λ₁'s vertex 0
  ↦ v_a, λ₂'s ↦ μ_M). `hSimg` supplier `s7r_img_of_decomposition`; namespace consequences `componentEquiv`,
  `carrierCrossings_eq_img_first/_second`, `carrierCrossingCount_eq_first/_second`, `componentEquiv_owner_vertexM`,
  `componentEquiv_owner_pivot` (halves EXCHANGED vs the leg-(M−1) side). Standard axioms, no sorry (the 2181-line RET block).
- **Open.** S1 demands `s7b_SlidingTransport` on BOTH sides with `vm.1 = x∓`; on the side whose contact crossing is {a, M} the accepted
  mark map sends `inl (inl 0) ↦ μ_M` and `inr (inl 0) ↦ v_ℓ` while `nextMark μ_M = v_ℓ`, so `ret` fails for every `vm` (W3_RET §2, a
  counter-derivation, see §C-05). Needed: S1' split by `s7e_leg g M a` — `s7b_SlidingTransport` at `s7e_vl` on the leg-(M−1) side,
  `s7r_SlidingTransport'` at `s7e_va` on the leg-M side; a second copy of ROT's transport section `section S7QTransport` (lines
  3968-4346, ≈ 380 lines: `s7q_cutFirst_of` 4238, `s7q_cutSecond_of` 4254, `s7q_coef_first` 4273, `s7q_coef_second` 4297,
  `s7q_rowData_of_transport` 4323) PLUS `def s7q_CarrierData` at 4484, which sits in `section S7QBoxes` (4348-4686), NOT in the transport
  section as W3_ASSEMBLY_REPORT §3.1 (L102) says — the S1' copy must take the def from S7QBoxes as well; on `s7r_SlidingTransport'` (a
  `s7q_CarrierData'` on `.componentEquiv`); glue `vm.1 = s7e_xm/xp ↔ s7e_vl/s7e_va` (~100 lines); re-type
  `w3_box_rows_of` (4768) and `w3_s7_sliding_law_at_of₂` (4829) to S1'. The frozen `s7_sliding_law_at` is unaffected (the state sums are
  symmetric in which side carries the extra corner).
- **Size.** 500-700 lines (statements ≈ 150 + transport copy ≈ 380 + glue ≈ 100), all consuming proved material.
- **Resume.** W3_RET_REPORT §3 recipe: `cases hl : s7e_leg g M a`; `hc₋ : IsCrossing P₋ {a, contactLeg false M} := hl ▸ s7e_hxm hn g h t`;
  `hc₊ … := (by simpa [hl] using s7e_hxp hn g h t)`; `(s7e_va hc₋).1 = s7e_xm hn h t` by `Subtype.ext` + `s7e_xm_val` + `hl` (likewise x₊);
  `hSimg := s7r_img_of_decomposition hn hQ hsep hm hQC h₁ h₂ S x hsplit hS hx` with `hsplit` from `s7e_contactSector_of_pivotSplit` and
  `S := (s7b_slidingDecompositionEquiv … hsplit).symm q`; one `obtain` of `s7a2_exists_intervalLocal` serves both sides, intersected with
  A2/E (`s7e_exists_spectatorSector`) and the contact sector's own radius; half supports via `s7q_pre_of_symm`.
- **Decision.** executor (inside a window the author has opened, §G-01).

### A-04 — Leaf S2 `w3_SlidingOrder` — PROVED at assembly (recorded so nobody re-does it)
- `def w3_SlidingOrder` 4726 = statement of `s7q_box_order`; `w3_SlidingOrder_of_box : w3_SlidingOrder := s7q_box_order` (4762), sorry-free
  on standard axioms (9-line proof from RET's `s7r_first_order` / `s7r_second_order` at the germ data `s7r_hord`, W3_ASSEMBLY_REPORT §3.1).
  The three-Prop form `w3_s7_sliding_law_at_of` (4809) is kept; the two-Prop form `w3_s7_sliding_law_at_of₂` (4829) is the one to use.
  **Decision.** none.

### A-05 — Leaf S3 `w3_SlidingCarriers` (= ROT's `s7q_box_carriers`): ROT's remaining geometry (a)-(c); also to be restated on `s7r_SlidingTransport'`
- **Where.** `def w3_SlidingCarriers` 4730; `theorem s7q_box_carriers` 4519 (sorry 4545): ∃ first τ δ, τ ≠ 0 ∧ 0 < δ ∧ ∀ t<δ, ∀ hsplitm hsplitp
  q, contact-sign memberships in `s7q_contactTurns` on both sides ∧ (∀ vm hT : `s7b_SlidingTransport` …, vm.1 = s7e_xm → `s7q_CarrierData` …
  hT (contactPoint first) (contactTurns first) τ) ∧ the true side with `!first`. W3_ASSEMBLY_REPORT §3.1 (S3), §7 item 3; ROT's report §6.
- **Proved.** ROT's consumers of the box are sorry-free: `w3_box_rows_of` 4768, `s7q_rowData_of_carrierData`, `s7q_hterm_of_rows`,
  `s7q_exists_contactSector`; the tools the box docstring names: `s7q_CutFirst/_Second` key decoding, `s7d_positiveOverBit_eq_of_smul` +
  `HalvesData.cut_segments`, `s7q_carrierRotation_eq_of_merge` (`s7q_principal_three_a/_b`), `s7q_carrierRotation_eq_of_perturb`
  (`s7q_two_turn_perturb`), `s7i_principalTurn_eq_of_edges_pos_smul`, `s7q_carrierWeight_eq_of_merge/_of_perturb`, `s7c_carrierWeight_eq_sel`.
- **Open.** ROT (a)-(c): ordered corner correspondences `s7q_CornerMerge` / `s7q_CornerPerturb` (U_S7B §2.3) 400-600; `hbit` 150-250;
  `hr` exact 150-250; `hr` perturbation 300-500; turn-sign constancy 200-300; contact-sign memberships + τ 100-150. Its `hT` arguments
  are `s7b_SlidingTransport`, so on the leg-M side it must be restated on `s7r_SlidingTransport'` together with S1' (§A-03).
- **Size.** 1,300-2,050 lines.
- **Resume.** Do §A-03 first (prerequisite). Then per ROT §6: ordered corner correspondence with the extra corner v_a (leg-(M−1) side) /
  v_ℓ (leg-M side; PLAN §3.3 eq. s7c:short-direction-lists), the over bits, `hr` via the merge/perturb lemmas, the turn-sign constancy
  (`s7e_sign_const` / `s7r_sign_const_center` pattern), the memberships; feed `w3_box_rows_of` → `w3_s7_sliding_law_at_of₂`.
- **Decision.** executor (inside an authorised window).

### A-06 — Leaf B1 `w3_BigonFSector` (= K's `s7z_F_exists`): F's sector data — three geometric boxes + a shape bridge, or K's F-aligned route
- **Where.** `def w3_BigonFSector` 8824; `theorem s7z_F_exists` 8600 (sorry 8614): below a radius ∃ `e₀ : Finset (Crossing P₀) ≃ {T :
  Finset (Crossing P₂) // x ∉ T ∧ y ∉ T}`, ∃ `e : {T // Elig T} ≃ Ind(λ₁) × Ind(λ₂)`, `s7z_FSector … e₀ e`; F-aligned alternative
  `s7z_bigon_law_at_of_residual` 8790 on `s7f_law_residual` 5895 / `s7f_exists_law_residual` 5933. W3_ASSEMBLY_REPORT §3.2, §7 item 4;
  `W3_K_REPORT.md` §2.1, §4(a)-(c); `W3_F_REPORT.md` §0, §2, §3.
- **Proved.** F: `s7f_law_residual` (per t, from `hsplit hterm htr`) and `s7f_exists_law_residual` (from F's three boxes): C(P₊) − C(P₋) =
  (if ε then 0 else 1)·J + δ_dir·(Σ_{eligible}(term₂(lift T₀) − term₀ T₀) + Σ_{eligible}(term₂(T₀∪{x}) + term₂(T₀∪{y})));
  `s7f_twoNewbornSum_eq_zero`, `s7f_twoNewbornEquiv`, `s7f_term_eq_zero_of_ineligible`, `s7f_triangle_data`, `s7f_s₀_eq_chi`. K:
  `s7z_law_at_of_residual` consumes exactly that identity (shape verified against W3_F.lean 1077-1115, K §4(a)); `s7z_side/x/y/pattern`
  definitionally F's; eligibility identification `s7z_Eligible ↔ s7f_Eligible` is a corollary of F's box 1 (K §4(c)); sign s₀ = χ(P₀)
  proved (`s7z_s₀_eq_chi`).
- **Open.** Route A (keep K's shape): F's three boxes (§A-07..A-09, 2,100-3,200) + the F→K bridge of K §4(b) (`e₀ := Equiv.ofBijective
  (s7f_lift …) ⟨s7f_lift_injective, s7f_lift_surj⟩` restricted by `s7f_x_not_mem_lift`/`s7f_y_not_mem_lift`, `e :=
  s7b_eligibleDecompositionEquiv ∘ lift`, clause (iii) from `s7f_exists_ineligible_transport` + `s7f_term_eq_zero_of_ineligible`, clause
  (iv) from `s7f_exists_twoNewbornTerm` (ε = 0) and `s7e_term_of_not` (ε = 1); 200-400 lines). Route B (recommended, W3_ASSEMBLY §7 item
  4): `s7z_bigon_law_at_of_residual` with K §4(a)'s instantiation — no B1 bridge; obligations = F's three boxes + `hrow`/`hone` per
  eligible T₀ in F's vocabulary + the eligible bijection restricted to `Finset.univ.filter (s7f_Eligible …)` via
  `Equiv.subtypeEquivRight` (200-400).
- **Size.** 2,300-3,600 lines (F's boxes 2,100-3,200 + bridge/restriction 200-400).
- **Resume.** Route B instantiation (K §4(a), verbatim): `s7z_law_at_of_residual hn h h₁ h₂ t (s7f_side g M a) (s7f_x hn h t) (s7f_y hn h t)
  (s7f_dirSign g M a) (s7f_dirSign_sq g M a) (s7z_s₀_eq_dirSign_mul g M a) (s7f_Interlacing hn h t) (s7f_lift hn g h t) (s7e_term hn
  (s7f_hP₀ g M a t)) (Finset.univ.filter (s7f_Eligible hn g h t)) e (s7f_law_residual hn g h h₁ h₂ t hsplit hterm htr) hrow hone`, radius
  form via `s7z_bigon_law_at_of_residual`; `hrow`/`hone` are then B2/B3's content in F's vocabulary.
- **Decision.** executor (route choice), inside an authorised window.

### A-07 — F box 1 `s7f_exists_bigonSplit`: the bigon support split (ten geometric hypotheses of `s7f_bigonSplit_of`)
- **Where.** `theorem s7f_exists_bigonSplit` 5371 (sorry 5379); `W3_F_REPORT.md` §1.F, §2 item 1, §3 last bullet.
- **Proved.** `s7f_bigonSplit_of hn g h h₁ h₂ t hrel₁ hrel₂ hcross hcross' hxfree₁ hxfree₂ hyfree₁ hyfree₂ hxsplit hysplit` builds
  `s7f_BigonSplit`; `inj₁ inj₂ disjoint` and the eight newborn exclusions come from U110-B (`s7b_firstCrossingQ_injective`,
  `s7b_secondCrossingQ_injective`, `s7b_firstCrossingQ_ne_secondCrossingQ`, `s7b_*CrossingQ_not_affected` vs `s7f_x_affected` /
  `s7f_y_affected`). The abstract split theory (`s7f_BigonSplit`, `twoNewbornEquiv`, `not_indep_of_mem_x/_y`, `indep_insert`) is proved.
- **Open.** Below a radius: `rel₁ rel₂` (the halves' interlacement is the restriction of P₂'s along the half crossing maps — U_S7B §2.2's
  open fields in bigon form), `cross cross'` (no interlacement across the two images), `x_free y_free` (newborn chords interlace no
  internal label of A or B), `x_split y_split` (an old crossing interlacing neither newborn lies in a half image, sm-4:414-416). Content:
  `Interlaces` = `traversalBetween` of visit positions; half positions are the centre's (U110-B part II), P₂'s positions are the centre's
  on persistent visits (`VertexLocalData.visit_order`) with the four newborn visits inserted adjacent to μ_M on E_{M−1}, E_M and within η
  of r on E_a (`ContactParameterWindows`).
- **Size.** 600-900 lines (shares the P₂(t)-vs-centre visit-position bookkeeping with box 3; together 1,000-1,500 as one lane).
- **Decision.** executor (inside an authorised window).

### A-08 — F box 2 `s7f_exists_twoNewbornTerm`
- **Where.** `theorem s7f_exists_twoNewbornTerm` 5388 (sorry 5405); `W3_F_REPORT.md` §2 item 2. Feeds `s7f_exists_law_residual` (5933) and,
  on Route A, clause (iv) of the F→K bridge at ε = 0 (§A-06).
- **Open.** The two-newborn term identity in F's vocabulary (the ε = 1 sector is already empty: `s7f_twoNewbornSum_eq_zero`).
- **Size.** 1,000-1,500 lines (W3_ASSEMBLY_REPORT §3.2). **Decision.** executor (inside an authorised window).

### A-09 — F box 3 `s7f_exists_ineligible_transport`
- **Where.** `theorem s7f_exists_ineligible_transport` 5725 (sorry 5729); `W3_F_REPORT.md` §2 item 3. Feeds `s7f_exists_law_residual` and
  clause (iii) of the bridge (`s7f_term_eq_zero_of_ineligible` is proved).
- **Open.** The transport of ineligible supports below a radius (the visit-position bookkeeping shared with box 1).
- **Size.** 500-800 lines. **Decision.** executor (inside an authorised window).

### A-10 — Leaf B2 `w3_BigonReturnedRows` (= K's `s7z_returned_of_FSector`): per-support instantiation of SITE/BLOCK/ROT/RET/J — the largest item
- **Where.** `def w3_BigonReturnedRows` 8841 (its hypothesis `hF : FloorTheoremData` does not occur in the conclusion); `theorem
  s7z_returned_of_FSector` 8620 (sorry 8635); SITE's open boxes `s7s_clear_local` 6972 (sorry 6981; 300-450) and
  `s7s_wallTriangleData_of_bigon` 7018 (sorry 7023; 300-500) feeding `s7s_siteData_of_wall`; the I-110 site's `hrec` (1,000-1,650) and
  clearance (600-900) — AN L6233-6247 (interim reading: "SITE leaves hrec as a Prop + two clearance/wall-data sorries"), L5948-5950 (I-110
  site "deferred until SM/BigonDeletion.lean is ported" — it was, 20:19Z), L6266-6269 (unit K composed the one-line body);
  `W3_BLOCK_REPORT.md` §2 (the 3,500-5,400 estimate).
- **Proved.** The generic RII deletion constructor `SM/BigonDeletion.lean` (`exists_rii_deletion` for general j,
  `exists_bigonData_of_triangle`, glue `s7_rii_witnesses` / `s7_switch_value_of_bigon`) is ported and sorry-free; SITE built the abstract
  and carrier-level bigon site at a bigon wall (`s7s_core`, `s7s_site`, `s7s_contact_sign`, wall-field lemmas); BLOCK's skein extraction,
  two-component and curl values, floor reads on three Prop interfaces (`s7k_ContactRowData` / `s7k_InterlacingData` /
  `s7k_NoninterlacingData`); J's floor and singleton entries (`s7j_interlacing_entry`, `s7j_noninterlacing_entry`, `s7j_below_floor_entry`);
  no RI-curl witness needed (`two_component_row_of_recordIso` + `curl_block_value`, AN L5876-5879).
- **Open.** The per-support instantiation on the actual carriers: SITE's `s7s_siteData_of_wall` (its two boxes + `hrec` + clearance),
  BLOCK's Gauss-record identifications and `R_H = R_L` through the wall, ROT's rotation ledger, RET, J's entries at the half contact
  carriers.
- **Size.** 3,500-5,400 lines (SITE's own 1,600-2,600 included).
- **Resume.** Templates: rows 174/176's site + hrec units closed the same geometry in one wave each — `work/drafts/moves/Site_174.lean`
  (2941 lines), `R174_HREC.lean` (3390), `Site_176.lean` (4143), `R176_HSUCC.lean` (4492); the curl removal `r176c_curl_removal`
  (`R176W2_CURL.lean`, 6709 lines) is "shared with 174/110" (AN L6278). **Decision.** executor (inside an authorised window).

### A-11 — Leaf B3 `w3_BigonOneNewborn` (= K's `s7z_oneNewborn_exists`)
- **Where.** `def w3_BigonOneNewborn` 8859 (`hsing` absent from the conclusion); `theorem s7z_oneNewborn_exists` 8639 (sorry 8642).
- **Open.** J's cb:singleton entry with C's one-newborn selectors on F's split vocabulary.
- **Size.** 400-700 lines. **Decision.** executor (inside an authorised window).

### A-12 — Row 110, the RET rule-4 finding (recorded under the row; the library side is §C-05)
The accepted structure `s7b_SlidingTransport` (`work/lean/SM/CornerChainUnits.lean:3934`; the U110-B docstring at :3811-3815, "vm = the visit
of x₋ on the leg edge M−1 / M", belongs to `def s7b_slidingMark` at :3816 — the mark map the structure consumes — not to the structure
itself) is usable on the leg-(M−1) side only; its `ret` field is FALSE on the leg-M side (W3_RET_REPORT §2). No accepted
declaration is wrong as a theorem — the structure is a Prop-valued record, nothing claims it is inhabited on that side — but the consumers
S1/S3 quote it on both sides and must be restated (§A-03, §A-05). No AN "FR" entry records the finding beyond the audit conclusion (AN
L6304-6309); FR §3.1 and §5 item 2 record it. **Decision.** none for the row; §G-05 for a docstring clarification inside the accepted module.

### A-13 — Row 127 `thm:comparison` (fixed name `SM.thm_comparison (hR : hyp_R) : ∀ n [NeZero n] hn P hP, cornerStateSum hn hP = amplitude P hP.1 hn`): one line away, blocked on 110
- **Where.** Design AN L5691-5799 (D-CM-2 at L5702-5705: a plain theorem with hyp:R as the EXPLICIT parameter, policy mode
  `explicit_parameter`, FR-CM-7); lane proved AN L5827-5837; PORTED AN L6025-6042; one-liner recorded in
  `work/drafts/comparison/port/PORT_REPORT.md` (lines ~130-143; placement paragraph L139-143); ported library `work/lean/SM/Comparison.lean`
  (260 lines, `thm_comparison_of`), `SM/CornerPolygon.lean`, `SM/CuspDeletionGeneric.lean`; FR §3 pending table.
- **Proved.** `thm_comparison_of (hR) (h7 : CS7Data) (hs : CSoftData)` sorry-free on standard + `lit_homfly` / `lp_lm` / `lp_lm_uniqueness`;
  the lane's only leaf `cusp_deletion_generic` PROVED on standard axioms; row 112 `thm:C-soft` accepted, so the only missing input is
  `SM.thm_C_S7`. Row 105 is no longer a dependency (D-CM-5).
- **Open.** The row theorem: `theorem thm_comparison (hR : hyp_R) : … := thm_comparison_of hR thm_C_S7 thm_C_soft`, to go in a new
  `work/lean/SM/ComparisonRows.lean` (verified ABSENT) importing `SM.CInherits`, `SM.CSoft` and the row-110 module (the pattern of
  `SM/CSoft.lean` and `SM/AnchorValuesRow.lean`; alternative: append to `SM/Comparison.lean` / `SM/CInherits.lean`, which then import the
  row-110 module — PORT_REPORT L139-143).
- **Size.** one line + map + review once `SM.thm_C_S7` exists.
- **Resume.** After §A-02 lands: create `SM/ComparisonRows.lean`, `lake build SM.ComparisonRows`, `python3 work/port/map_row.py implement
  thm:comparison SM.thm_comparison SM.ComparisonRows`, checker, review brief from `work/port/review_prompt_prop-anchor-values.md` with the
  disclosed readings FR-CM-6/7/10/11/12 (AN L5713-5799). **Decision.** executor.

### A-14 — Row 128 `cor:C-inherits` (fixed name `SM.cor_C_inherits (hR : hyp_R) : CInheritsData`): one line away, blocked on 110
- **Where.** D-CM-3 at AN L5705-5708; ported `work/lean/SM/CInherits.lean` (204 lines: `TrianglesC`, `CuspLawC`, `ReversalLawC`,
  `CInheritsData` (12 fields incl. `root_values`, `SM/CInherits.lean:52`), `cor_C_inherits_of`, the §6 `example`s = the consumer shape checks
  proving CInheritsData → hyp_R / CS7Data / CSoftData, FR-CM-15); one-liner `cor_C_inherits hR := cor_C_inherits_of hR thm_C_S7
  thm_C_soft` (PORT_REPORT L135-136).
- **Proved.** `cor_C_inherits_of` and `trianglesC` sorry-free on standard + `lit_homfly` / `lp_lm` / `lp_lm_uniqueness`;
  `cusp_deletion_generic` proved (the (G1) premise is even automatic at a simple cusp wall, FR-CM-9′). `CInheritsData` is the FINAL shape
  (D-CM-3); the CV/R tail's draft copy differs (§A-21).
- **Open / size / resume.** As §A-13, same module; readings to disclose FR-CM-8/9/9′/13/14/15/16/17. **Decision.** executor.

### A-15 — Row 177 `R:extreme_selected` (fixed name `RProof.extreme_selected : RowShape @ExtremeSelectedData`): two named leaves open in the operative chain; R construction STOPPED by audit A-177-2
- **Where.** Draft `work/drafts/moves/W3C_Assembled.lean` (16 945 lines at closing, 1428 declarations, 0 errors, 34-38 s; sha256
  `dbcd10375ac572c0…`, mtime 00:36:55Z 2026-09-16 — the closing file. The report's §0 paragraph (L12) AND its table (L32) read "16 945
  lines, 1428 declarations": the report was rewritten after its 00:26Z draft, mtime 00:36:54Z. The stale "16 774 / 1 425" figures survive
  only in FR L410, L560, L1183 — whose own note "§0 (00:26Z) says 16 774" is therefore stale — and L1223, and in AN L6421; §E-09); report
  `work/drafts/moves/W3C_ASSEMBLY_REPORT.md` (293 lines: §3 every remaining sorry, §6 honest state, §7 what the port would look like, §8
  pitfalls); Wave-3 material `W3_A1_Assembled.lean` (7827 lines, sha256 `b8c7b7d1d4b2368b…`, mtime 21:55:51Z 2026-09-15),
  `Port_GenericTransportSw_draft.lean` (119 lines), `W3B_Assembled.lean` (Wave 3b base; 11 851 lines, sha256 `cbedf6d625333202…`, mtime
  23:15:54Z 2026-09-15) — with `W3_Assembled.lean`'s `109050d9…` (§A-02) these checksums let a next agent tell whether `assemble_W3C.py` +
  `assemble_W3C_connect.py` reproduce the closing file (the connect script does contain the final `w3cx_sign_table_at` /
  `w3cx_outer_residue_data` block, its lines 643-793, so it should); ledger `work/lean/RProof/RALedgers.lean`
  (2371 lines, byte-unchanged since its 18:08Z port — `RowShape` at :29, `est_PortData` :872, `esc_MoveData` :1957, `cv_R_of_rows` :2354,
  `sm_R_of_rows` :2365 per FR); audits A-177-1 AN L6171-6204 (21:21Z), success L6216-6231 (22:00Z), A-177-2 L6330-6359 (23:20Z), concluded
  L6419-6440 (00:31Z); FR §3.4, §5 item 3, §6. `work/lean/RProof/ExtremeSelected.lean` and `RProof/GenericTransportSw.lean` do NOT
  exist (verified). `lean-declarations.json`: `R:extreme_selected` → `RProof.extreme_selected`, module "", pending.
- **Proved (registered axioms, no sorryAx).** The `esc_` ledger (RALedgers); the switched RIII core `G11_core_sw` on the trans-free copy
  `G11_ConfigSw` / `G11_ParamsSw` (905 of 908 declarations re-derived; `#print axioms` = standard + `lit_homfly`, `lp_lm`,
  `lp_lm_uniqueness`); `esc_switch_riii_of_chain` ((4) realiser); (6) `rii_after_smoothing` in the weak form
  (`w3bi_rii_after_smoothing_weak`); the interface replay `w3bi_esc_ledger : ext interface → CarrierSlotFloor → RowShape
  @ExtremeSelectedData` (RALedgers untouched, A-177-1 D2); wall data β2 `w3bi_wall_data_data`, `w3bi_hrec_general`, `w3bi_rii_sites_of`;
  site data β1′ `w3bi_site_data_data` (D4 as a determinant identity, D5 from the positive over-strand convention); the four bigon sites in
  corrected non-kink statements; SPLITA's `touching_iff` / `distinct` / `central_no_piece` / `central_rot` with explicit carriers
  `w3ca_A/B/C/Z`; SPLITC's `outer_alternative` / `uniform` (closed by the assembler from SPLITA, `w3cc_splitA_corners_data`); SPLITB's
  `writhe` / `mixed` modulo its core; the sign table (1c) `w3cx_sign_table_at`; KNOT's `w3ck_knot_after_two` and
  `w3ck_three_components_count` at every configuration; `esc_FullSplitData` at every configuration modulo ONE residue
  (`w3cx_fullSplitData_at`). Chain: `w3ck_extreme_selected := w3ck_esc_ledger w3ck_esc_interface_ext_occ_holds CV.carrierSlotFloor`
  (W3C §3 lists every link). Footprint (`W3C_AXIOMS.log:2`): `w3ck_extreme_selected : [propext, sorryAx, Classical.choice, Quot.sound,
  lit_homfly, lit_homfly_descent, lp_lm, lp_lm_uniqueness, ng_finite_word, src_contact]` — on closure `RProof.extreme_selected` will carry
  all nine registered axioms (descent + `src_contact` through `CV.carrierSlotFloor`), to be disclosed in FR §4.3 (§B-04).
- **Open.** Exactly two `sorryAx` sources of `w3ck_extreme_selected`: `w3cx_outer_residue_data` (§A-16) and `w3cs_not_kink_site_data`
  (§A-17). Outside the operative chain: the frozen Wave-3b OUTER leaf `w3bi_esc_outer_data` (decl 11689, sorry 11690; NOT provable as
  stated, superseded by `w3ck_esc_outer_occ_holds`, §C-07) and the optional `w3b_reparam_switch` (decl 4093, sorry 4095; ≈ 0.15k, no
  consumer). Two port-time statement edits (§A-18). `RProof.extreme_selected` not declared.
- **Size.** W3C §6: ≈ 1.0-1.9k lines (0.7-1.3k + 0.3-0.6k) + the two skeleton edits; AN L6437-6438 and STATUS say ≈ 1.3-2.5k; FR §3's
  pending table attributes "≈ 1.0-1.9k" to the residue alone (a slip, §E-09). Take 1.0-2.5k, one route open.
- **Resume (only after §G-02).** Read W3C_ASSEMBLY_REPORT §3, §6, §7, §8 (pitfalls). Compile: `cd work/lean && lake env lean
  ../drafts/moves/W3C_Assembled.lean` (expect 4 `declaration uses sorry` at 4093, 11689, 13745, 16425). Regenerate the merge with `python3
  assemble_W3C.py` then `python3 assemble_W3C_connect.py` (both assert unique matches) — CAUTION: both scripts hard-code RELATIVE
  filenames (`W3B_Assembled.lean`, `W3C_SPLITA/SPLITC/BIGON/SITE/SPLITB/KNOT.lean`; `assemble_W3C.py:9-11`) and OVERWRITE
  `W3C_Assembled.lean` in place (`:58`), so run them with cwd = `work/drafts/moves/` and only after copying the current file aside (then
  compare with the sha256 above); likewise `check_W3_statements.py` reads `Skeleton_W3.lean` from the cwd (`:8`, `:16`). All unit files are
  present (verified 02:20Z: `W3C_SPLITA/SPLITC/BIGON/SITE/SPLITB/KNOT.lean`, `Skeleton_W3.lean`; likewise the corner unit files
  `work/drafts/corner/W3_SPLIT/RET/ROT/F/SITE/BLOCK/J/K.lean` + `W3_Skeleton.lean` needed to redo the lost corner `assemble.py`, §A-02).
  `work/drafts/moves/port/` holds `R174/` and `R176/` only — there is NO `R177/` (W3C §0 table: port "not prepared"), so nothing there is
  to be copied for 177. On closure: declare
  `RProof.extreme_selected` in the FIXED `RowShape @ExtremeSelectedData` form (as siblings 174/175/176), port per §A-18/§C-04 (§7:
  `RProof/GenericTransportSw.lean` = lines 1-7846; `RProof/ExtremeSelectedUnits.lean` = sections Row177_6 + W3BI_REAL + W3CK_KNOT;
  `RProof/ExtremeSelected.lean` = `theorem extreme_selected : RowShape @ExtremeSelectedData := w3ck_extreme_selected`), map, review; then
  §A-19, §A-20.
- **Decision.** author (§G-02; two bounded windows + Wave 3c without acceptance — a new window is the author's call).

### A-16 — Leaf `w3cx_outer_residue_data : w3cx_outer_residue` (row 177): parity `#mixedSet = 2Λ` + KNOT's polynomial identification of the three components
- **Where.** `W3C_Assembled.lean` decl 16425 (sorry 16426), section `W3CK_Outer`; W3C §1.4, §3; AN L6427-6428. CONTENT DISCREPANCY:
  AN L6427-6428 (A-177-2 concluded), FR §3's pending table (L410) and FR §3.4 (L566) describe this residue as "the sign table (1c), the
  parity #mixedSet = 2Λ, and KNOT's identification"; the W3C report (§0 (iii) L17-18, §3 L181, §6 L245) states that the sign table (1c) is
  PROVED (`w3cx_sign_table_at`, standard axioms) and that the residue is parity + identification only (0.7-1.3k). The report and this
  item are right on content; AN and FR are wrong on content as well as on size (§E-09).
- **Proved.** Everything `esc_FullSplitData` needs except this residue (`w3cx_fullSplitData_at`); the sign table (1c) that SPLITB's core
  also needed (`w3cx_sign_table_at`); `w3cb_split_core_data` and `w3ck_split_ident_data` are proved MODULO the residue
  (`w3cx_split_ident_of_residue`).
- **Open.** Two clauses at a common Λ: (i) the parity `#w3cb_mixedSet Q' (Q'∪T') q₀' = 2Λ` (KNOT's bridge count, analogue of
  `r176m_bridge_count`: the mixed crossings of J_L are the retained crossings of q₀' between distinct outer carriers, all positive; Λ then
  fixed by (17)); (ii) KNOT's identification `twoLambda J_L = 2Λ ∧ ∃ σ : Fin 3 ≃ Fin J_L.Γ.c, homfly (knotRestrict (σ i)) = groupedPoly
  A/B/C` in record-clause form (route and API in KNOT's report §5, §8: the `r176s_smoothRestrictIso` pattern twice,
  `Stack.restrictSmoothIso`, a restrict-of-restrict lemma NOT in the library, `CV.crossKeep_liftBlock_iff`, `r176s_homfly_of_liftBlock`).
- **Size.** (i) ≈ 0.3-0.5k, (ii) ≈ 0.4-0.8k: ≈ 0.7-1.3k lines; route known.
- **Resume.** Templates: row 176's OUTER unit `work/drafts/moves/R176W2_OUTER.lean` (7984 lines) and MIXED's count argument
  `R176W2_MIXED.lean` (6835 lines) — "the same shape" (AN L6345-6347). **Decision.** executor inside an authorised window (§G-02).

### A-17 — Leaf `w3cs_not_kink_site_data : w3cs_not_kink_site` (row 177): NOT a consequence of the site data; may need a hypothesis on the event
- **Where.** `W3C_Assembled.lean` decl 13745 (sorry 13746), SITE's new box; W3C §1.2 ("SITE's non-kink box wired"), §3; SITE's report §4
  (the kink-loop example and routes (i)/(ii)); AN L6429-6431.
- **Proved.** The four bigon sites in their corrected non-kink statements; the box is wired into `w3bi_bigon_of_site_model` /
  `w3bi_bigon_of_site` / `w3bi_bigon_pair_of` → `w3bi_rii_sites_data` → both row chains.
- **Open.** That the lift crossing over `x_ef` is not a kink of the one-component lift, under the binders of `w3bi_site_data`. SITE
  exhibits a kink loop satisfying D4, D5, `clear` and `clear_vertex`, so the fact does NOT follow from `w3bi_SiteData`; it needs data from
  the 177 configuration (the carrier edges `G11_mE`, `G11_pE` of `x_ef` not at cyclic distance 2 in `geoCornerPolygon`; SITE §4 routes
  (i)/(ii)) — or a hypothesis on the RIII event, which would touch the accepted row shape / event vocabulary.
- **Size.** ≈ 0.3-0.6k lines if a route exists; route open.
- **Resume.** Author decides first whether an event-level non-kink hypothesis is admissible (it is NOT in the printed proof
  `reference/R/RA/R_EXTREME_SELECTED_COUPLE_PROOF.md`) or whether the derivation from the configuration data is required. Then prove it
  in `W3C_Assembled.lean`. **Decision.** author (§G-02b).

### A-18 — Row 177 port-time statement edits (skeleton material, not frozen row statements)
1. The four j = 2 bigon sub-leaves `w3g_bigonData_smooth_arcST/TS` and `w3bi_bigonData_smooth_arcST/TS_switch_z` were FALSE as stated
   (`BigonData.hk` fails when the smoothed crossing is a kink); Wave 3c RESTATED them with unit G's non-kink hypothesis and PROVED the
   corrected forms; consumers gained the hypothesis (W3C §1.2; AN L6338-6339, L6355-6356, L6431-6432). `check_W3_statements.py` reports
   40/42 byte-identical, the two differing being exactly these. Record the four restatements in AN/FINAL_REVIEW when 177 is ported.
2. The Wave-3b Props `w3bi_knot_after_two` / `w3bi_three_components` (and hence the frozen `w3bi_esc_outer` + leaf `w3bi_esc_outer_data`)
   quantify over every relational `IsOrientedSmoothing`; the library identifies only `smoothDiagram`'s record — NOT provable as stated
   (KNOT rule 3). Superseded by the record-clause forms `w3ck_knot_after_two_occ` / `w3ck_three_components_occ` and the `w3ck_` chain.
   Port-time: edit the two Props and the `rii_after_smoothing_weak` field of `w3bi_esc_MoveDataWeak` (KNOT §3), or adopt the `w3ck_` chain
   and delete/keep the `w3bi_` chain as documentation (W3C §7 (d)).
3. Reword the prose `sorry` mentions — exactly TWO, lines 7856 and 14706 (`grep -c sorry` = 6 = 4 terms at 4095/11690/13746/16426 + 2
   prose); the report's third mention "16561 (KNOT's chain docstring)" is stale — section `W3CK_Chain` (16545-16937) contains no `sorry`,
   so the porter must not hunt for it. The `-- (W3C assembler)` comments (STATEMENT RESTATED at 9253, 9283, 13113, 13135) name the
   RESTATEMENTS, not the word `sorry`; record them under item 1, nothing to reword for `sorry`;
   (c) of §7: drop the library copies of `SM.CBProducts`, `CV.SingletonDi`, `SM.ZeroRotationSeed` by importing them, or keep them.
**Decision.** executor (recorded edits, no frozen statement involved; `RALedgers.lean` unaffected).

### A-19 — Row 178 `R:cv_theorem` (fixed name `RProof.cv_R : CV.hyp_R`): assembly proved, one-liner STAGED, waits only on 177
- **Where.** D-CVT-5 AN L5493-5495; FR-R-178-1/2 AN L5565-5570; staged file `work/drafts/cvtail/port/R178_183/RProof/CvR.lean` (verified
  present: header carries a `<HH:MM>Z` placeholder to fill at port; imports `RProof.RALedgers`, `RProof.GenericSelected`,
  `RProof.ExtremePairZero`, `RProof.ExtremeTransport`, `RProof.ExtremeSelected` — the last does not exist yet; body `cv_R_of_rows (fun … =>
  generic_selected …) (… extreme_pair_zero …) (… extreme_transport …) (… extreme_selected …)`); library `RProof.cv_R_of_rows` in
  `work/lean/RProof/RALedgers.lean` (:2354 per FR; via `A2_cvRNear_of_rows` + `hyp_R_of_near_of_chamberinv` + `cvt_chamberInvII` — the third input of the body at :2354-2358, verified).
- **Proved.** `cv_R_of_rows` ported and sorry-free; three of the four RA inputs accepted (174 at 23:54Z, 175 at 18:39Z, 176 at 00:12Z);
  domain `E.IsSimpleRIII` as printed.
- **Open.** The declaration; blocked only on §A-15. Its footprint will be the nine registered axioms incl. `SM.lit_homfly_descent` and
  `SM.src_contact` (FR-R-178-2; §B-04) — disclose in FR §4.3 on acceptance.
- **Size.** one line (staged). **Resume.** After 177 is accepted: `cp work/drafts/cvtail/port/R178_183/RProof/CvR.lean work/lean/RProof/CvR.lean`,
  fill the header time, `lake build RProof.CvR`, `map_row.py implement R:cv_theorem RProof.cv_R RProof.CvR`, checker, review (brief from
  `review_prompt_r-extreme-transport.md`, disclosures FR-R-178-1/2). **Decision.** executor.

### A-20 — Row 183 `Bridge:theorem` (fixed name `Bridge.sm_R : SM.hyp_R`; a final TARGET): staged one-liner, waits on 178
- **Where.** D-CVT-5 AN L5495; FR-B-183 AN L5571-5574 (BRIDGE.md §3 (19)-(21) verbatim, no new mathematics); staged
  `work/drafts/cvtail/port/R178_183/Bridge/SmRRow.lean` (verified: imports `RProof.CvR`, `Bridge.SmR`; `theorem sm_R : SM.hyp_R :=
  SM.sm_R_of_cv_R RProof.cv_R`; header placeholder `<HH:MM>Z`); library `work/lean/Bridge/SmR.lean` (54 lines, 2026-09-14: `SM.sm_R_of_cv_R
  : CV.hyp_R → SM.hyp_R`, `hyp_R_of_cv_hyp_R`, `smR_shape_conclusion_is_diagonal`; its header line 1 still says "blocked by GAP-2" —
  §E-11); `Bridge.sm_R_of_rows` in RALedgers (:2365 per FR).
- **Proved.** The library implication; its conclusion IS `SM.hyp_R` in the all-side-parameters form (equivalent to the chamber form by
  `prop:C-chamber`, `hyp_R_iff_base`).
- **Open.** The row (targets would become 6/8). Blocked on §A-19 ← §A-15.
- **Resume.** After 178: copy the staged file to `work/lean/Bridge/SmRRow.lean` (NOT over `Bridge/SmR.lean`, which is the library module),
  build, map `Bridge:theorem` → `Bridge.sm_R` / `Bridge.SmRRow`, review; disclose the descent footprint. **Decision.** executor.

### A-21 — Row 184 `SM:corner_laws_and_soft` (fixed name `SM.corner_laws_and_soft : CornerLawsAndSoftData`; the FINAL target): assembly proved in a draft; three inputs missing plus one port-time re-typing
- **Where.** Design AN L5474-5597 (D-CVT-5 at L5493-5497; FR-F-184-1..4 at L5576-5595); assembly PROVED AN L5801-5815 (`corner_laws_and_soft_of
  (hR : hyp_R) (h7 : CS7Data) (hs : CSoftData) (hinh : CInheritsData) : CornerLawsAndSoftData`, `work/drafts/cvtail/Wave1_Assembled.lean:4367`
  per FR §3; 4386 lines); statements `work/drafts/cvtail/Statements_FINAL.lean` (992 lines); FR §3 pending table, §4.6 (clause table — "the
  final declaration is NOT declared"), §5 item 4.
- **Proved.** `corner_laws_and_soft_of` (a flat 11-field bundle, one field per item of TARGETS' required coverage, pre-review); genericity of
  children corrected from ∃ to ∀ (FR-F-184-2); the row is the instantiation at `Bridge.sm_R`, `thm_C_S7`, `thm_C_soft` (accepted),
  `cor_C_inherits Bridge.sm_R` — R discharged, no parameter (FR-F-184-1).
- **Open.** (a) inputs `thm_C_S7` (§A-02), `Bridge.sm_R` (§A-20), `cor_C_inherits Bridge.sm_R` (§A-14); (b) the `CInheritsData` UNIFICATION
  (§A-22). Not ported; not declared (D-F11).
- **Size.** one instantiation + the field-type edits; blocked on ≈ 9-15k lines upstream.
- **Resume.** When 110/127/128 and 177/178/183 are accepted: port from `Statements_FINAL.lean` / `Wave1_Assembled.lean` with `import
  SM.CInherits`, apply §A-22, declare `SM.corner_laws_and_soft`, map, review; recompute the axiom footprint (§B-04) and update FR §4.3/§4.6.
  **Decision.** executor (after the author's §G-01/§G-02).

### A-22 — Row 184 port-time edit: replace the cvtail draft's `CInheritsData` / `CuspLawC` / `ReversalLawC` / `TrianglesC` copies by `import SM.CInherits`
- The comparison lane's 12-field `SM.CInheritsData` with `root_values` (`work/lean/SM/CInherits.lean:52`) is FINAL (D-CM-3, AN L5705-5708);
  the cvtail draft's 11-field proposal (D-CVT-5 "a PROPOSAL to be unified", AN L5495-5497; FR-F-184-4 L5592-5595) differs. The edit changes
  the field TYPES `cusp` / `reversal` / `triangles` and the `hinh` parameter of `CornerLawsAndSoftData`; `corner_laws_and_soft_of` is
  unchanged (AN L6036-6038; `work/drafts/comparison/PLAN_FINAL.md` §6 has the exact field-type edits). The §6 `example`s in
  `SM/CInherits.lean` already prove the bundle direction the final line needs (FR-CM-15). **Size.** small. **Decision.** executor.

---

## B. Axioms and interfaces added or assumed on 2026-09-15/16

### B-01 — `axiom SM.lit_homfly_descent : SM.AmbientIsotopyDescent` — the author-authorised SECOND declaration of lit:homfly (GAP-2 closed by decision, not by proof)
- **Where.** `work/lean/SM/LitHomflyDescent.lean:37` (39-line module); the predicate `AmbientIsotopyDescent` at
  `work/lean/SM/ContactPathOfDescent.lean:176-182` (statement-reviewed 2026-09-14, `work/reviews/cp-finite-contact-path-conditional.json`);
  policy key `"lit:homfly (descent sentence)": "SM.lit_homfly_descent"` at line 9 of BOTH `lean/axiom-policy.json` and
  `work/lean/axiom-policy.json` (verified identical); the author's decision quoted verbatim AN L5146-5153 (D-GAP2, 13:39Z) with
  D-GAP2-1..4 and FR-LHD-1..4 at L5155-5176; interface review `work/reviews/lit-homfly-descent.json` (3/3 faithful, 2 refuters clean,
  14:25Z; brief `work/port/review_prompt_lit-homfly-descent.md`); FR §4.3 (the full paragraph), §5 item 1.
- **What it asserts.** Along every jointly smooth ℝ-indexed family of oriented spatial embeddings (`SpatialFamily`) whose two ends have
  `RegularGenericProjection`, `homfly` takes equal values on any polygonal `HeightMarking` readings of the two end diagrams — the last
  printed sentence of lit:homfly ("Its value depends only on the oriented link presented by D", `blueprint/AXIOM_REGISTRY.md:14-15` =
  sm-3:920-921) for the FIXED witness `SM.homfly := Classical.choose lit_homfly`. Own axiom set: `[propext, Classical.choice, Quot.sound,
  SM.lit_homfly, SM.lit_homfly_descent]`. Not derivable from `lit_homfly` alone (design D2 reads descent over `LinkEquiv`); true for the
  genuine HOMFLY-PT polynomial under the standing D2 premise (formal Reidemeister completeness) already carried by `lp_lm_uniqueness`.
- **Every accepted row carrying it (14 by FR §4.3's recount of the 00:14Z audit; AN L6457 says "13" — §E-10):** 91 `cp:finite-contact-path`
  (std + H + HD + LM + LMU) and, with the full nine, 94 `fd:contact`, 162 `CV:ax:slbound`, 99 `cf:thm-carrierfloor`, 100 `thm:floor`,
  155 `CV:thm:carrierfloor`, 165 `CV:singleton_D_i`, 175 `R:extreme_pair_zero`, 103 `cb:singleton`, 105 `lem:corner-values`, 112
  `thm:C-soft`, 122 `prop:anchor-values`, 174 `R:generic_selected`, 176 `R:extreme_transport`. When declared, 177/178/183/184 will carry it
  through `CV.carrierSlotFloor` (D-CVT-6, §B-04). No row accepted before 2026-09-15 depends on it. Row 91 itself is
  `cp_finite_contact_path := cp_finite_contact_path_of_descent lit_homfly_descent` (`SM/ContactPath.lean`, 20 lines), accepted 14:25Z.
- **Disclosed readings (permanent).** STRONGER: FR-LHD-1 — stated on a family of EMBEDDINGS, so it bundles the isotopy-extension step the
  printed proof performs by hand (sm-3:3276-3312) with the literature sentence (the literal `AmbientIsotopyDescentLit` and the proved split
  `ambientIsotopyDescent_of_lit : AmbientIsotopyDescentLit → IsotopyExtension → AmbientIsotopyDescent` are in
  `ContactPathOfDescent.lean` 146-178); FR-1/FR-LHD-3 — record-level presentation (`HeightMarking`), so it also asserts equal `homfly` for
  any two polygonal diagrams carrying the same signed O/U record of one regular generic projection (the constant-family instance is already a
  theorem of the accepted layer). WEAKER: FR-LHD-4 regular generic ends only; readings only; same labelled circles (no component
  permutation); C^∞ only; exact parametrized ends; fixed xz projection; FR-LHD-2 ℝ-indexed family; c = 0 vacuous. The refuter CS1 of the
  row-91 review requires that every record say "literature descent premise + isotopy extension (unformalised)", never "modulo the literature
  sentence alone" — FR §5 item 1 does.
- **Trust base, not a sixth interface** (the author's reading, D-GAP2-2). TARGETS.md:8 ("the five listed literature interfaces") is met
  under that reading; §B-05 and §G-07 (registry document), §G-08 (the literal alternative).
- **Decision.** none (recorded); §G-06/§G-07/§G-08 are the author's follow-ups.

### B-02 — `axiom SM.src_contact : ∃ r tb : (ℝ → E3) → ℝ, SrcContactClauses r tb` — the fifth literature interface, declared 15:10Z, accepted 16:51Z
- **Where.** `work/lean/SM/SrcContact.lean` (287 lines; the axiom at :224 per FR; `SrcContactClauses`, fixed witnesses `SM.rot`, `SM.tb :=
  Classical.choose …`, `src_contact_spec`, `src_contact_iff_consequence` — the theorem at :258, its docstring :254-257 — in the frozen statement file); design AN L5295-5368
  (D-SC-1..6, FR-SC-1..11, FR-FC-1..7); declared AN L5370-5384; accepted AN L5629-5636; review `work/reviews/src-contact.json` (3/3, 2
  clean); plan `work/drafts/contact/PLAN_FINAL.md` §3; FR §4.3 second paragraph, §3.5.
- **What it asserts.** Only the four printed formulas of sm-3:3341-3365 as fields: `rotation` r = (D − U)/2, `thurston_bennequin` tb = w −
  (D + U)/2, `pushoff_self_linking` sl(T₊(L)) = tb − r for every positive pushoff circle of every pushoff annulus (rows 84/87's
  `GenericFront.IsPositivePushoff`), `transverse_front_writhe` sl K = writhe of the front for a generic positive transverse front.
  `SM.sl K := slCircle K.circle` is the document's own fd:framed-linking number (row 88; D-SC-2), so the axiom has content relative to an
  independent definition (the 2026-09-14 memo's §3(a)(ii) objection no longer applies).
- **What is NOT constructed.** No contact-geometric r or tb (no winding of L′ in ξ, no contact-framing linking number): the ∃-form is
  PROVABLY equivalent to the substituted consequence "sl(T₊) = w − D on the Legendrian class ∧ sl = w on the transverse class"
  (`src_contact_iff_consequence`, standard axioms; FR-SC-1); no transverse-isotopy class T₊(L) is formed — field 3 quantifies over EVERY
  positive circle of EVERY accepted pushoff annulus, presupposing Etnyre's well-definedness, with the `injective` field load-bearing for
  truth (FR-SC-3; a non-embedded annulus gave a would-be counterexample sl = −1); the convention, D + U, provenance and scope sentences have
  no field (FR-SC-6/8).
- **Narrowings / neutral readings.** Legendrian formulas for KNOTS (F.c = 1) whose front lies on ng:front-domain's `SmoothFront` class
  (FR-SC-2; Etnyre's Lemma 2.22 covers links and non-generic fronts); real-valued r, tb, sl, integrality a consequence (FR-SC-10);
  `slCircle T = 0` off `IsPositiveTransverseEmbedding`, never exercised — on-class discharged by `SM.u_circle`
  (`work/lean/SM/FdContactUnits.lean:102`; FR-SC-9). Identification of the document's sl with Etnyre's/Geiges' is rem:sl-convention, a
  remark (FR-SC-4). Truth of the axiom on the accepted definitions rests on numeric probes (D-SC-6 + three refuter probes with D ≠ U) — see
  §E-13 for the inaccurate AN sentence about the eye probe.
- **Carried by (15 of 184):** `src:contact` itself, 161 `CV:ax:etnyre` (std + SC), and the thirteen nine-axiom rows of §B-01.
- **Consequences recorded elsewhere.** D-SC-4 SUPERSEDES the 2026-09-14 decision D-F10 (iii): rows 161/162 are THEOREMS on the real sl
  (`CV.ax_etnyre` from `src_contact` alone; `CV.ax_slbound := ax_slbound_of SM.fd_contact`), not axioms (AN L5312-5314; readers of notes
  before L5144 must know). Rows 84 and 87 carry textually identical `IsPositivePushoff` structures; the axiom uses row 87's (§C-12).
- **Decision.** none; §G-11 (single-representative form) and §G-12 (Etnyre citation) are optional author items.

### B-03 — D-GAP2-2b: `verify_bundle.py` line 100 relaxed; the bundle verifier no longer enforces set equality of literature keys
- **Where.** `verify_bundle.py:97-100` (verified: comment "A literature input may carry a second declaration under a key '<id> (<note>)'
  (author's decision D-GAP2, 2026-09-15); the ceiling is on the set of literature inputs (labels)…", then `require({k.split(' ')[0] for k
  in policy['literature']} == {x['id'] for x in axioms} == required_axioms, 'literature ceiling')`); AN L5186-5202; root `MANIFEST.sha256`
  lines for `lean/axiom-policy.json` and `verify_bundle.py` refreshed with `python3 work/port/refresh_manifest.py`; `tools/check_lean.py`
  untouched (`allowed = policy['standard'] + list(policy['literature'].values())` at :114; `fixed = policy['literature'] | policy['targets']
  | {'hyp:R': 'SM.hyp_R'}` at :104 already accept the key); flagged in `lit-homfly-descent.json` AR0 note (iv) as a process edit.
- **Effect.** The ceiling on literature INPUTS is unchanged (exactly five labels); a second declaration of an input is admitted under
  `'<id> (<note>)'`. `verify_bundle.py` PASS (191 files). "The one edit to a package tool of the whole execution", reversible: restore
  `set(policy['literature']) == required_axioms` and drop the key — then every row carrying `SM.lit_homfly_descent` fails the checker.
- **Decision.** author: confirm or revert (§G-06). Author sign-off is recorded only as "flagged in the report to Mark and the author".

### B-04 — Axiom-footprint disclosure owed when 178/183/184 are declared (D-CVT-6, FR-R-178-2) and the R-lane footprint through row 99
- `RProof.extreme_selected` (row 177; evidence `W3C_AXIOMS.log:2`: `w3ck_extreme_selected : [propext, sorryAx, Classical.choice,
  Quot.sound, lit_homfly, lit_homfly_descent, lp_lm, lp_lm_uniqueness, ng_finite_word, src_contact]` — all nine registered axioms plus the
  two open `sorryAx` leaves of §A-16/§A-17), `RProof.cv_R`, `Bridge.sm_R`, `SM.corner_laws_and_soft` will carry `SM.lit_homfly_descent`
  and `SM.src_contact` (path 155 (C) ← 99 (C) ← 94 ← 91; AN L5497-5499, L5568-5570) although TARGETS names "five listed literature interfaces". Already-accepted R rows 174/175/176
  inherit `lit_homfly_descent`, `src_contact`, `lp_lm`, `lp_lm_uniqueness`, `ng_finite_word` through `CV.singleton_D_i` /
  `CV.carrierSlotFloor` while the RA texts name only R-LOC/R-PAR/(D)(i) as inputs (reviews `r-extreme-pair-zero.json` CS1 cs-disc[5];
  `r-extreme-transport.json` discrepancies[6]); their leaf lemmas (e.g. `extreme_pair_zero_of_singleton`) depend only on standard +
  `lit_homfly`. FR §4.3 lists the 14/15 rows; on each new acceptance recompute the footprint from the checker audit, update FR §4.3 and
  refresh the manifest line (`python3 work/port/refresh_manifest.py FINAL_REVIEW.md`). **Decision.** executor (documentation).

### B-05 — Five registry headings, six axiom constants: `blueprint/AXIOM_REGISTRY.md` has no entry for the second declaration
- Headings verified: `## lit:homfly — AXIOM` (:5), `## lp:lm — AXIOM` (:20), `## lp:lm-uniqueness — AXIOM` (:53), `## ng:finite-word —
  AXIOM` (:78), `## src:contact — AXIOM` (:122). Policy `literature` has six keys. Several reviewers could not verify registration under
  their reading restrictions and deferred it to FINAL_REVIEW (`cv-ax-slbound.json` AR0 §7, `thm-floor.json` AR1 §6,
  `r-extreme-pair-zero.json` CS1 cs-disc[5], `r-generic-selected.json` discrepancies[8], `cb-singleton.json` AR1, `thm-C-soft.json` AR0 §10,
  `fd-contact.json` CS0 cs-disc[0](b)). The blueprint is FROZEN (package rule 8), so only the author can add a sub-entry under "## lit:homfly
  — AXIOM" naming `SM.lit_homfly_descent` (type `AmbientIsotopyDescent`, D-GAP2); otherwise FR §4.3 remains the record. **Decision.** author (§G-07).

### B-06 — CV "axiom" rows 161/162 are Lean THEOREMS; the D-F10 (iii) route is superseded (provenance note)
- `CV.ax_etnyre` (`work/lean/CV/AxEtnyre.lean`, 15 lines; `ax_etnyre_of` at `SM/FdContactStatements.lean:84`) has axiom set standard +
  `SM.src_contact`; `CV.ax_slbound` (`CV/AxSlbound.lean`, 16 lines; `ax_slbound_of` :88) has the nine. Kernel equivalence `CV.AxEtnyreData ↔
  ∀ K, sl K = ↑K.front.writhe` checked by the reviewers. Their truth rests on the SM route, not on the CV document's cited source (the CV
  `ax:*` pattern of `CV.ax_homfly`). Row 161 keeps the redundant hypothesis "no downward vertical tangency" (FR-FC-4; rendered x′ = 0 → 0 <
  z′). **Decision.** none.

---

## C. Library-interface findings — literal fields unrealisable or false as stated, closed by weak replays or corrected forms WITHOUT editing the accepted library

### C-01 — D-RM-5: accepted `est_PortData.port` (row 176) is UNREALISABLE as stated; row 176 closes through the weak port replay
- **Where.** `work/lean/RProof/RALedgers.lean:872` (`structure est_PortData …`), field `port : Relation.ReflTransGen RII ((CV.carrierDiagram
  … q').switch y) (CV.carrierDiagram … q)` at :878 (verified); weak forms `est_port_weak_of_bigon`, `fulltwist_coefficient_of_port_weak`,
  `fulltwist_skein_of_port_weak` in `work/lean/SM/BigonDeletion.lean`; `s176_PortDataWeak` (:347), `.ofPortData` (:415),
  `s176_est_ledger_weak` in `work/lean/RProof/ExtremeTransportUnits.lean`; AN L5879-5884 (moves panel: "TWO INTERFACE PROPS ARE
  UNREALISABLE AS STATED"), L6070-6074 (D-RM-5: the site's 5-line edit F-176-1 NOT applied), L6262-6265; FR §5 item 6; review
  `r-extreme-transport.json` executor_notes.
- **Finding.** An RII chain cannot cross the wall (`OutsideMatch.eval_eq`); the printed "port relation" sentence is rendered by the weak
  form ∃ D₀′, RII-chain ∧ `homfly D₀′ = homfly D₀`, which IS proved from an actual constructed RII deletion (`exists_rii_deletion`).
- **Status.** Row 176 `R:extreme_transport` ACCEPTED 00:12Z (AN L6407-6417) on exactly the nine registered axioms; the row leaf `RowShape
  @ExtremeTransportData` byte-identical to the fixed statement; RALedgers.lean byte-unchanged since its port (sha256 = the 18:11Z receipt's
  entry, FR §7). The accepted library keeps a literal Prop no object can satisfy; anyone reading `est_PortData.port` as the meaning of the
  printed sentence is misled.
- **Decision.** author: apply the F-176-1 edit inside the accepted module (forbidden to the executor) or keep + document (§G-04).

### C-02 — D-RM-6: `est_PortData.rot / alt₁ / alt₂` FALSE as stated without `wind(S) ≠ 0`; corrected forms + a `wind = 0` split
- **Where.** `RALedgers.lean:903-906` (verified: `rot : (CV.carrierR hn hG hS q : ℤ) = CV.carrierR … Λ₁ + CV.carrierR … Λ₂ + 1`, `alt₁`,
  `alt₂ : CV.UniformOrOneDissentCV …`); corrected forms `r176l_est_port_relation_uniform` / `_weak_uniform` and the split
  `r176_est_row_H_weak_uniform` (13 lines: at wind(S) = 0 both row terms vanish via `rowTerm_of_mem_Ind` + `GT_wind_eq`) in
  `RProof/ExtremeTransportUnits.lean`; AN L6255-6265 (unit LEDGER, 2102 lines), L6270-6283; FR §5 item 6.
- **Finding.** A MIXED affected carrier breaks `UniformOrOneDissentCV` and `R = R₁ + R₂ + 1`. Also recorded by the R176 assembler:
  `r176l_smooth_black_box` was stated too strongly (binders lacked `hcomp`, `habc`, `hu hv hju hjv huv`); superseded by
  `r176_outer_carriers_L` / `r176_mixed_bridge` with the full binder list (FR §5 item 6).
- **Status.** Row 176 accepted through the replay; the literal fields stay in the library unused by the composition. **Decision.** author (§G-04).

### C-03 — Row 177: `esc_MoveData.rii_after_smoothing` (∀ oriented smoothings) unrealisable as stated → `esc_rii_after_smoothing_weak`; F-177-2 handled by an extended-interface REPLAY, not an edit
- **Where.** `RALedgers.lean:1957` (`structure esc_MoveData`), field `rii_after_smoothing` :1962-1967, `def esc_rii_after_smoothing` :1904
  (verified); weak form `esc_rii_after_smoothing_of_bigons` in `SM/BigonDeletion.lean` (:5313; the module also holds `exists_rii_deletion`
  :4999, `est_port_weak_of_bigon` :5276, `fulltwist_skein_of_port_weak` :5285, `fulltwist_coefficient_of_port_weak` :5296).
  `esc_switch_riii_of_chain` is NOT in BigonDeletion — its header (line 1) and line 18 say the Wave-3 §4 material `G11_ConfigSw` /
  `G11_core_sw` / `esc_switch_riii_of_chain` "is NOT here"; the theorem exists only in the drafts (`W3_A1_Assembled.lean:7652`,
  `W3C_Assembled.lean:7837`); the replay `w3bi_esc_*` / `w3bi_esc_ledger` in `work/drafts/moves/W3C_Assembled.lean`; AN L5882-5884,
  L6199-6201 (A-177-1 D2: "NOT an edit of RALedgers — the realiser replays esc_ with an extended interface esc_interface_ext … exactly as
  D-RM-5 did for 176"), L6333-6335; FR §5 item 11, §7 ("F-177-2 wording": `W3_A1_ASSEMBLY_REPORT.md` §6 had planned an EDIT of
  RALedgers.lean:2027 — the executor's D2 governed).
- **Status.** `esc_rii_after_smoothing_of_bigons` proved (standard + `lit_homfly` / `lp_lm` / `lp_lm_uniqueness`); row 177 still open
  (§A-15) and will close, if ever, through the ext-interface replay. **Decision.** author (with §G-02/§G-04).

### C-04 — A-177-1: accepted `RProof.G11_Config.trans` is FALSE on the K3 side of row 177; the 1 056 accepted `G11_Params` declarations cannot be instantiated at a 177 site; an ADDITIVE trans-free copy exists in drafts; the author's cheaper edit option is untaken
- **Where.** `work/lean/RProof/GenericTransport.lean:111` (`structure G11_Config`), field `trans : ¬ IsAlternating (crossingSign X m p)
  (crossingSign X m q) (crossingSign X p q)` at :125 (verified; docstring "the divide over-order of the three strands is transitive");
  copies `G11_ConfigSw` / `G11_ParamsSw` in `work/drafts/moves/W3_A1_Assembled.lean` (7827 lines) and `W3C_Assembled.lean` lines 1-7846;
  `Port_GenericTransportSw_draft.lean` (119 lines: the skeleton of the port); AN L6171-6204 (options (i) edit, (ii) copy, (iii) abandon),
  L6216-6231 (the copy test SUCCEEDED: 905/908 declarations re-derived — `gu6_htrans` → hypothesis `htrans`, `riii` → `w3de_riii_param`,
  `core_of_params` → `G11_core_sw`; `G11_core_sw` and `esc_switch_riii_of_chain` = standard + `lit_homfly`, `lp_lm`, `lp_lm_uniqueness`,
  no sorryAx); FR §5 item 7, §7.
- **Finding.** No accepted proof uses `trans` except the D8 table; the configuration type OVER-SPECIFIES what its proofs use. Nothing
  accepted is false as a theorem; the accepted `RProof.generic_transport` (rows 166-173) is unaffected.
- **Open.** (a) the 6.4k-line mechanical copy is draft-only — `work/lean/RProof/GenericTransportSw*.lean` do not exist (verified); (b)
  the author may instead drop `trans` from `G11_Config` — statement-neutral for every row, ≈ 4k lines for Wave 3 instead of ≈ 12.5-13k, but
  a rewrite inside an accepted module. **Size.** copy route: ≈ 7.8k mechanical port (only worthwhile if 177 continues); edit route: ≈ 4k.
  **Decision.** author (§G-03).

### C-05 — Corner RET rule-4 defect: `s7b_SlidingTransport.ret` (accepted `SM/CornerChainUnits.lean:3934`) is FALSE on the leg-M side; corrected `s7r_SlidingTransport'` stated and PROVED in the draft
- **Where.** `work/lean/SM/CornerChainUnits.lean:3934` (structure), :3811-3815 (the U110-B docstring "vm = the visit of x₋ on the leg
  edge M−1 / M" — wrong for leg M; it is the docstring of `def s7b_slidingMark` at :3816, the mark map the structure consumes, not of the
  structure itself); `W3_RET_REPORT.md` §2 (counter-derivation), §1.B-1.D (corrected forms), §4 (docstring flag); draft
  `W3_Assembled.lean:2248` (`structure s7r_SlidingTransport'`), :3402 (`s7r_slidingTransport_side'`); FR §3.1, §5 item 2 ("rule 4 invoked
  six times", FR L1144-1149 per the finder).
- **Finding.** With Q carrying x = {a, M}, ι := `s7b_slidingMark … vm` has ι (inl (inl 0)) = μ_M and `smoothingSuccessor S (inl M) = nextMark
  (inl M) = inr v_ℓ` (`s7r_nextMark_M`); with vm = v_ℓ the step lands on an image mark of λ₂, with any other vm the chain reaches an image
  mark of λ₂ and never ι (inl (g₁ (inl 0))) — `ret` fails for every vm. Geometric reading: on that side the carrier through μ_M is the
  closed SECOND half with v_ℓ as extra corner; the FIRST half has v_a in place of λ₁'s vertex 0. The corrected mark map `s7r_slidingMark'`
  (inl (inl 0) ↦ inr v_a, inr (inl 0) ↦ inl M) has `ret` PROVED (`s7r_slidingTransport_of_leg_true`, `_side'`); one generic first-return
  engine `S7RReturn` (`s7r_reach_of_transit`, `s7r_hit_of_transit`) serves both sides. The frozen `s7_sliding_law_at` is unaffected.
- **Status.** No accepted declaration is wrong as a theorem; the accepted structure stays as stated (usable on the leg-(M−1) side only);
  the consumers S1/S3 (draft) must be restated (§A-03, §A-05). No AN "FR" entry exists for the docstring flag beyond L6304-6309.
  **Decision.** author for a comment-only clarification of the accepted docstring (§G-05); executor for the draft restatements.

### C-06 — Row 177: the four j = 2 bigon sub-leaf statements were FALSE as stated (kink case); restated and proved in the draft
- Skeleton material, not frozen row statements (AN L6338-6339, L6355-6356, L6431-6432; W3C §1.2): `w3g_bigonData_smooth_arcST/TS`,
  `w3bi_bigonData_smooth_arcST/TS_switch_z`, `BigonData.hk` fails when the smoothed crossing is a kink; corrected forms with the non-kink
  hypothesis proved; the residual obligation is §A-17. Record at port (§A-18 item 1). **Decision.** executor.

### C-07 — Row 177: relational-smoothing Props `w3bi_knot_after_two` / `w3bi_three_components` (hence the frozen `w3bi_esc_outer` and its leaf `w3bi_esc_outer_data`) are NOT provable as stated; superseded by the record-clause `w3ck_` chain
- Draft-level (W3C §0, §3 row 11689, §6 rule-3 (b); AN L6431-6434): the library identifies only `smoothDiagram`'s record. `w3bi_esc_outer_data`'s
  `esc_FullSplitData` conjunct IS proved modulo the residue (`w3cx_fullSplitData_at`). Port-time statement edit (§A-18 item 2); RALedgers
  unaffected. **Decision.** executor.

### C-08 — D-RM-7: row 176 draft Prop `r176_outer_carriers_L` FALSE in its second disjunct; corrected two-sided form proved (rule-3 repair of a draft artefact)
- AN L6377-6394 (esp. L6380-6387): y = lift v′ — the arc from v′_c to v′_b carries both occurrences of lift u′, a chord of S_full never in
  the retained block; `r176o_outer_carriers_L_corrected` proved (both halves, standard axioms) with mirrored data `r176o_OuterDataL′` and
  the mirrored bridge `r176a_mixed_bridge′_proof` (88 lines); ported in `RProof/ExtremeTransportUnits.lean` (r176o_, r176a_ blocks; header
  lines 7, 15). No accepted declaration involved; disclosed FR §5 item 6. **Decision.** none.

### C-09 — Row 174: the bare `hrec` Prop `s174_hrec_prop` is false for arbitrary q′; proved only under the ledger binding (q′ = τ qAB); the ledger's σ is orientation-dependent and NO AUTHOR_NOTES entry records it
- AN L6056-6059 (site stated hrec as a Prop), L6164-6166 (HREC's finding and proof under the binding); ported `RProof/GenericSelectedUnits.lean`
  (r174h_: `r174h_hrec_tau`); the one open Prop `r174_arc_rec_moves` was later proved TRUE as stated by two independent routes (AN
  L6361-6366; Route R kept in `work/drafts/moves/R174W2_ARCR.lean`, 7444 lines, not ported — §E-26). Row 174 accepted 23:54Z on the nine
  axioms. `R174_ASSEMBLY_REPORT.md` §8.1 / `R174W2_ASSEMBLY_REPORT.md` §0 asked for an AN entry on σ = −τ(m_AB) being orientation-dependent
  while the `gsc_Ledger` / `gsc_moves` docstrings read σ as `crossingSign ℓ₁ ℓ₂`; none was written — FR §5 item 6 records it instead
  (verified by FR at closing). **Decision.** executor (an AN entry; §E-14).

### C-10 — D-FL-4: floor-lane helper `MirrorSubstitutionData.coeff` was false for negative odd k ((-1)^k.toNat); repaired to (-1)^k.natAbs at assembly
- AN L5386-5394 (unit U-ι's machine-checked counterexample `ui_coeff_toNat_false`: f = z⁻¹, d = 0, k = −1), L5599-5609 (repair in
  `work/drafts/floor/Wave2_Skeleton.lean`), L5651-5653 (Floor_Assembled statements byte-identical "except the one intended D-FL-4 repair");
  ported `work/lean/SM/CarrierFloor.lean`; row bundles untouched (D-FR2 pattern); rows 99/100 accepted. Note: the draft
  `work/drafts/floor/Statements_FINAL.lean` and the ported module differ in this one field. **Decision.** none.

### C-11 — Moves toolkit: `BigonData.hk : j + 3 ≤ k` is stronger than needed (library interface); satisfied at every site
- AN L5937-5939 (U-M0 pre-review: "NO field must change"); `work/lean/SM/BigonDeletion.lean`. Every consumer site (110 wall, 174 m-corner,
  176 j-corner) satisfies it; `no_io` automatic for j = 1; `exists_rii_deletion` proved for general j (the R1 fallback to j ∈ {1,2} not
  needed, AN L5987-5997). Anyone reusing `BigonDeletion` at a new site with small k must check it. **Decision.** none.

### C-12 — Two textually identical `IsPushoffAnnulus` / `IsPositivePushoff` definitions (rows 84 and 87); `Iff.rfl` between them fails; `src:contact` uses row 87's
- `work/lean/SM/GenericFront.lean:74` (structure `IsPushoffAnnulus`), :88 (`def IsPositivePushoff`); `work/lean/SM/TransverseNeighborhood.lean:120`,
  :138 (verified by the finder's grep); `src-contact.json` CS1 cs-disc[3], executor_notes; AN L5631-5634. A consumer holding the
  TransverseNeighborhood form must convert by hand; optional bridging lemma `GenericFront.isPositivePushoff_iff_tn` (~10-20 lines) by
  structure eta — needed by no accepted row. **Decision.** none.

### C-13 — Library gap: existence of a polygonal `HeightMarking` reading of a transverse front / regular generic projection is not a library theorem; rows 91, 94 (`representative_bound`), 162 are conditional on `Nonempty (HeightMarking …)`
- `SM/FdContactStatements.lean:39-41` (`representative_bound`), :80-83 (`CV.AxSlboundData.bound`); `ContactPathData.endpoint_polynomial`;
  reviews `fd-contact.json` discrepancies[1], `cv-ax-slbound.json` discrepancies[3] ("No registered existence theorem for HeightMarking of a
  TransverseKnot projection … in work/lean/lean-declarations.json"), `cp-finite-contact-path-row.json` discrepancies[1]. Mathematically a
  reading always exists (PL approximation); no Lean lemma `∃ X, Nonempty (K.spatial.HeightMarking K.spatial.projLoop X)` for `K :
  TransverseKnot`; the only consumer (thm:carrierfloor (C)) supplies its own reading. Template if wanted: `U_reading` (SmoothFront case) in
  `SM/FdContactUnits.lean`. **Size.** not estimated. **Decision.** author (§G-13, optional).

### C-14 — `lem:corner-values` (i): "embedded (m_Q = 0)" rendered by the gloss `carrierCrossingCount = 0`; no library lemma `Embedded → carrierCrossingCount = 0` (or converse)
- `SM/CornerChainStatements.lean` (`CornerValuesData.embedded_value`; "168-171" are lines of the frozen reviewer input
  `work/reviews/corner-chain-statements-reviewer-input.lean.txt`, where `CornerValuesData` starts at :167 — in the live module it starts at :190); `Embedded` in `SM/EmbeddedRotation.lean:33-36`;
  `lem-corner-values.json` discrepancies[0], stronger_than_source[0]; FR-CC-4. A consumer starting from geometric embeddedness (e.g.
  sm-4:1092-1093) must supply the implication itself (lem:carriers (iii) `self_intersections`; ~20-50 lines). No accepted consumer needs
  it today. **Decision.** none (add on demand).

### C-15 — CV row 155's statement file carries library material consumed by 165/174/176/177 but reviewed under no row: `CV.CarrierSlotFloor`, `carrierSlotFloor`, `carrier_slot_floor_of_C`, `cvtS_` helpers
- `work/lean/CV/CarrierFloor.lean` (486 lines; the frozen statement file lines 298-386); `cv-thm-carrierfloor.json` CS0 cs-disc[7]; D-CVT-2.
  Kernel-checked as part of the built module; inherits the nine axioms. If an interface list is compiled for FINAL_REVIEW, add
  `CV.CarrierSlotFloor` with its consumers 165, 174, 175, 176 (and 177 when declared). **Decision.** none (documentation).

---

## D. Statement notes from the independent reviews of the rows accepted 2026-09-15/16 (every stronger / weaker / non-blocking note; NONE is blocking)

All 17 reviews (16 rows + the descent axiom; `src:contact` counted as a row) were AI-only: primary "literal" lens, countersigned
"definitions" and "strength" lenses, two adversarial refuters, proofs replaced by `sorry` (reviewer identity string
`reviewer-pod-claude-fable-5-1-20260913`, dated by first use). Files: `work/reviews/<slug>.json` with arrays `discrepancies`,
`stronger_than_source`, `weaker_than_source`, plus `*-reviewer-input-statement.lean.txt` and `*-source-excerpt-*.tex.txt`. Kinds: S =
stronger than print, W = weaker than print, N = neutral / convention, P = provenance, D = documentation, X = process. FR §5 item 10 and §2
quote one clause per row; this table is the complete list the finders extracted, plus rows D-73..D-79 added by the repair pass (three
reviewer-conduct disclosures and four non-blocking notes the finders had missed).

| id | row / declaration | note | kind | blocking? |
|---|---|---|---|---|
| D-01 | 91 `SM.cp_finite_contact_path` (`SM/ContactPath.lean`; `structure ContactPathData` at `SM/ContactPathOfDescent.lean:102`, fields :103-:124, consistent with §E-02) | FR-CP-5 / CE-R2: the supplied family is an ℝ-indexed `SpatialFamily` (jointly C^∞ on ℝ×ℝ, every slice embedded regular), the printed family lives on [0,1]; a [0,1]-family enters after the `Real.smoothTransition` clamp (row 89's pattern) | W | no |
| D-02 | 91 | FR-CP-1: S(F) and D_T enter only through polygonal `HeightMarking` readings; no polygonal carrier existence is asserted (§C-13) | W | no |
| D-03 | 91 | K-5 / D-1 (inherited from row 90): "every clean ordinary cusp smoothing" ranges over `CleanCuspSmoothing` with the unprinted convex `IsDisc` (`SM/LinkMoves.lean:100`) and the collar clause (collar IS printed, ce:smoothing-record 3175-3176; convexity is not) | W | no |
| D-04 | 91 | P S = P X asserted for ALL polygonal readings X, S rather than "the" two diagrams; equivalent because two `HeightMarking`s of one loop family are `RecordIso` (`CeSmoothingRecord` 592) and P is record-determined (`PolynomialBlock` 1177) | S | no |
| D-05 | 91 | FR-CP-9: read-back fields `link_class`, `cusped_front`, `double_points`, `supplied_family`, `smaller_y_over` are trivially provable projections of the hypotheses; `0 < c` is a hypothesis of every field except `supplied_family` and is used by nothing; `heights_distinct` and `deriv y ≠ 0` (ExactCuspGerm) are redundant; the content is `endpoint_polynomial` alone | D | no |
| D-06 | 91 | FR-CP-7 / FR-LHD-1: proved modulo `SM.lit_homfly_descent`, which bundles the isotopy-extension step with the literature sentence (§B-01); CS1: records must say "literature descent premise + isotopy extension (unformalised)" | S (axiom) | no (author-authorised) |
| D-07 | 91 | Citation nits: descent sentence at sm-3:3310-3312 (docstrings say 3313-3316), hand extension step 3276-3312 (docstrings 3264-3313), field ranges off by one (§E-02) | D | no |
| D-08 | 91 | `source_sha256` fa17a1b1… in both row/conditional JSONs is the sha of the whole `sm-3-statesum.tex`, not of the excerpt (9f9854f6…; excerpt byte-identical to lines 3210-3233) (§E-04) | D | no |
| D-09 | axiom `SM.lit_homfly_descent` | FR-LHD-1: asserts the isotopy-extension step too (stronger than registry sentence sm-3:920-921 by exactly `IsotopyExtension`) | S | no |
| D-10 | axiom `SM.lit_homfly_descent` | FR-1 / FR-LHD-3: record-level presentation — also asserts equal `homfly` for two polygonal diagrams with the same signed O/U record of one regular generic projection (constant-family instance already a theorem); a ≤2-visit crossing-connected cluster may be reversed as a whole between two readings — harmless (split, invertible, HOMFLY invariant under global reversal) | S | no |
| D-11 | axiom `SM.lit_homfly_descent` | Weaker clauses: regular generic ends (FR-LHD-4), readings only, ℝ-indexed family (FR-LHD-2), same labelled circles, C^∞ only, exact parametrized ends, fixed xz projection, c = 0 vacuous | W | no |
| D-12 | axiom `SM.lit_homfly_descent` | Consistency for the fixed witness rests on the standing D2 premise (formal moves complete for PL isotopy), the same premise `lp_lm_uniqueness` carries; not derivable from `lit_homfly` alone | P | no |
| D-13 | axiom `SM.lit_homfly_descent` | Frozen reviewer-input statement file keeps the pre-correction docstring (stmt 100-101 "exactly what the printed proof consumes at sm-3:3313-3316"); live docstring corrected; do NOT regenerate the frozen file (its sha256 is in the accepted review) (§E-03) | D | no |
| D-14 | axiom `SM.lit_homfly_descent` | Docstrings at `ContactPathOfDescent.lean:54` and :173 still say "NOT an axiom"; header comment (:2) is the only fix (§E-01) | D | no |
| D-15 | axiom `SM.src_contact` | FR-SC-3: sl = tb − r asserted for EVERY positive circle of EVERY accepted pushoff annulus (printed: one transverse-isotopy class T₊(L)); presupposes Etnyre's well-definedness; `injective` field load-bearing (a non-embedded annulus gives sl = −1) | S (form) | no |
| D-16 | axiom `SM.src_contact` | FR-SC-1: ∃-form over undefined r, tb; witnesses not identified with the literature's invariants; no invariance content; provably equivalent to the substituted consequence (`src_contact_iff_consequence`) | W | no |
| D-17 | axiom `SM.src_contact` | FR-SC-2: Legendrian clauses for KNOTS (F.c = 1) with fronts on ng:front-domain's `SmoothFront` class only | W | no |
| D-18 | axiom `SM.src_contact` (also 94, 161, 162) | FR-SC-10: r, tb, sl ℝ-valued; integrality of sl a consequence of field 4 | N | no |
| D-19 | axiom `SM.src_contact` | FR-SC-9: `slCircle` returns 0 off `IsPositiveTransverseEmbedding`; never exercised on `K.circle` (`SM.u_circle`, `FdContactUnits.lean:102`); `cv-ax-etnyre.json` (16:51Z) still records this as pending unit U0 — superseded 17:12Z | N / D | no |
| D-20 | axiom `SM.src_contact` | Docstring `SrcContact.lean:152` attributes "the positive y axis goes into the page" to Etnyre §2.2 (3): not checkable from package files (agrees with sm-3:3432-3436) (§G-12) | D | no |
| D-21 | axiom `SM.src_contact` | AN FR-SC-11 (L5346-5348) claims the judge's eye probe confirms w − D over w − U; refuters: the eye (D = U = 1) cannot discriminate; the decisive D ≠ U probes (D=3/U=1, D=2/U=0, D=4/U=0) live only in reviewer scratchpads (§E-13) | D | no |
| D-22 | axiom `SM.src_contact` | Reviewer conduct: an awk over AUTHOR_NOTES printed from the Contact-lane heading to EOF (not used); rows 84/87 duplicate structures noted (§C-12) | X | no |
| D-23 | 161 `CV.ax_etnyre` (`CV/AxEtnyre.lean`) | Printed as an axiom, a Lean THEOREM from `SM.src_contact` alone; D-F10 (iii) superseded by D-SC-4 (§B-06) | P | no |
| D-24 | 161 | FR-FC-4: the hypothesis "no downward vertical tangency" kept explicitly though redundant on `TransverseKnot` (`front_vertical_up`, `TransverseFront.lean` 767-769); rendered x′ = 0 → 0 < z′ (needs immersion); `CV.AxEtnyreData ↔ ∀ K, sl K = writhe` kernel-checked | N | no |
| D-25 | 94 `SM.fd_contact` (`SM/FdContactStatements.lean:32-41`) | FR-FC-3: sentence 1 (smaller-y over, sign = sgn det_xz) rendered only on def:transverse-front's class where it is definitional; the general Legendrian-front rule is carried by row 92's `IsOver`, not by this field | W | no |
| D-26 | 94 | FR-FC-1 / FR-1: `representative_bound` conditional on a `HeightMarking` reading; no existence theorem (§C-13); reading-independence kernel-checked | W | no |
| D-27 | 94 / 162 | `degAZ 0 = 0` convention (`AdegDefinition.lean` 11-14, 34-37, `WithBot.unbotD 0`) would read sl ≤ −1 at P X = 0 where printed max deg_a is undefined; inert since `SM.lp_core.ne_zero` / `SM.P_ne_zero` (`PolynomialBlock.lean` 793) | S / N | no |
| D-28 | 94 | `representative_bound` for EVERY polygonal reading; `over_rule_sign`'s sign clause for every ordered double pair (formal only; `crossSign` defined for any ordered pair) | S | no |
| D-29 | 94 | Docstring line refs approximate (`FdContactStatements.lean:29` "3418-3421" → 3419-3421; :35 "3409-3411"; :37 "3412-3418" → display 3416-3418); status line names only src:contact + lit:homfly while the kernel set has nine; AN 16:40Z "seven registered" (§E-05, §E-10); receipt `dev-check-fdcontact-row162-implemented.json` names row 162 for row 94's port | D | no |
| D-30 | 162 `CV.ax_slbound` (`FdContactStatements.lean:80-83`) | FR-FC-5: "a transverse knot in the standard contact ℝ³" narrowed to `SM.TransverseKnot` (generic xz-projection, C^∞, 1-periodic, positively transverse; `TransverseFront.lean` 571-596) — fd:contact's own printed domain and the sole consumer instance (d3_floor.tex 976-987); a broader form would need a genericity-by-isotopy lemma the library lacks | W | no |
| D-31 | 162 | A theorem (`ax_slbound_of SM.fd_contact`), axiom set = the nine; "seven registered literature axioms + the standard three" in its `kernel_check` is the nine-element list (§E-10) | P / D | no |
| D-32 | 99 `SM.cf_thm_carrierfloor` (`SM/CarrierFloor.lean` §4; also 155) | FR-FL-B1 / FR-CV-155-5: clause (B) asserted for the NORMALISED orientation — `(AllPosOrOneNeg C.P ∧ BClaim C D) ∨ (AllPosOrOneNeg (reversal C.P) ∧ BClaim C.reverse D.reverse)`; the literal "record of L itself" reading is FALSE for an all-negative L (refuter AR1 kernel-extracted it); follows the printed WLOG sm-3:4368-4370; `Round(−L,−D,ε) = reverse (Round(L,D,ε))` NOT proved; consumers read (C)+(D) only | W (correction of the reading) | no |
| D-33 | 99 / 155 | FR-FL-R3 / FR-CV-155-3: clause (R)'s smooth-diagram half rendered only as `rot_reverse_curve` (curve level, `ClosedC1Curve.reverse`); reversal of a CARRIED smooth diagram not defined; P_{−D} = P_D for smooth diagrams not separately rendered; polygonal case complete (`rot_reverse_polygon`) | W | no |
| D-34 | 99 / 155 | FR-FL-A1 / FR-CV-155-4: `junction_determined` fixes the PARAMETRISATION on [a j, b j] (`curveMap_on_junction`), stronger than the printed image equality; image form is `junction_local`; FR-FL-A2: `Round := CornerRounding.roundedWitness` (`Rounding.lean` 3008) is a definition, no uniqueness among smoothings claimed; `one_record` is rfl; `length_determined` closed form `juncLen`; `junctionTemplate` uses arg u vs accumulated θu (differ by 2π); `one_diagram` renders inheritance as `Nonempty Carried ∧ smoothWrithe = writhe` | S / D | no |
| D-35 | 99 / 155 | Clause (B): tangency count over PARAMETERS t ∈ [0,1) (bijection with points not a clause, FR-FL-B2); `BClaim` adds ε₁ ≤ clearance C (FR-FL-B4, makes ∀ h non-vacuous); `TangencyCount` adds explicit `Set.Finite`; `CrossesPositively` locates tangencies in open junctions | S | no |
| D-36 | 99 / 155 | Clause (C): three redundant printed hypotheses kept as fields (`turn_exists`, `turn_lt_pi`, `generic`; FR-FL-C1) so consumers must supply them (`of_diagram` derives them); floor unconditional on P X via `P_ne_zero` while `mindegAZ 0 = 0` by convention (FR-FL-C2); CV form in ℤ with `rotAbs` vs SM form in ℝ (`rotAbs_intCast_real`) | D | no |
| D-37 | 99 / 155 | Clause (R) generalisations: `sign_reverse`, `writhe_reverse` for every link diagram; `rot_reverse_curve` for every closed C¹ regular curve; `knot_reverse` over the `LinkEquiv` class; `P_reverse` restricted to knots as printed though `ur_P_reverse_all` is unconditional; CV binder `hL' : Regular (reversal L)` derivable (`regular_reversal'`, `work/lean/CV/Rotation.lean:412` — there is no `SM/Rotation.lean`; SM has `RotationNumber` / `RotationReversal` / … only) | S | no |
| D-38 | 99 / 100 | Other floor-lane readings recorded BEFORE stating (AN L5218-5293): D-FL-3 / FR-FL-C4 the printed mirror D̄ is the CROSSING SWITCH (`Diagram.switchAll` + `SwitchAllCarriesUnit`), not `Diagram.mirror`; FR-FL-C6 rotation applied to the smooth curve only; FR-FL-C7 closed-form bump replaces the printed piecewise φ-bump; FR-FL-C8 "front reads T" = `K.Reads X_R` (record isomorphism); FR-FL-C9 fd:contact enters as the sl-free composite `TransverseFrontBound`; FR-FL-R1 library lemma unconditional, row field its knot restriction | N | no |
| D-39 | 99 | Review brief locator "341-343 (def:transverse-front)" should be sm-3:3328-3339 (§E-15) | D | no |
| D-40 | 100 `SM.thm_floor` (`SM/CarrierFloorRows.lean`; statements `CarrierFloor.lean` §7) | FR-FL-F1: "exactly one turn is right" rendered as "one right AND all others left" (zero turns excluded); coincides on carriers of decompositions (`ccpCornerPolygon_turn_ne_zero`, `CarrierCornerPolygon.lean` 579-584); 4-way disjunction kernel-checked | W (coincides) | no |
| D-41 | 100 | `z_parity` stated for every subpolygon without the turn hypothesis (FR-FL-F3; uses only `lit_homfly`/`lp_lm`/`lp_lm_uniqueness`); `a_floor` stated twice (ℤ via `cornerSlot`, ℝ via `carrierRotation`); at H⁺_Q = 0 (impossible) `a_floor` would read d_Q ≤ 0 | S | no |
| D-42 | 100 | Kernel axiom set (nine) larger than the printed status line's "Literature input lit:homfly"; `thm_floor_of_bound` uses only `lit_homfly`, `lp_lm`, `lp_lm_uniqueness`; the rest enters via the row-94 discharge of `TransverseFrontBound` | D | no |
| D-43 | 155 `CV.carrierfloor` (`CV/CarrierFloor.lean`) | Clause (A): "hypotheses of lem:rounding" transcribed as `Diagrammatic L` (with the no-triple / exactly-two-preimages clause) which lem:rounding's printed list (d3:35-38) omits — same domain as accepted `CV:lem:rounding` and SM `Round`; (B)/(C) print "diagrammatic" themselves | W | no |
| D-44 | 155 | Clause (D): "so that P_{S,L} = 1 and w_{S,L} = 0 by def:X1's empty conventions" not a conjunct (accepted `X1_definition.empty_conventions`, FR-CV-155-7); extra binder `hn : 3 ≤ n` redundant given `Generic P`; `mindegAZ (groupedPoly) = 0` as equality; FR-CV-155-8 partial acceptance is not a row (D-F11) | D | no |
| D-45 | 155 | In CV's copy the reversal branch of (B) is stated on SM objects (`PolyComp.reverse` / `PolygonDiagram.reverse`) because `OverUnder.reverse` / `Diagrammatic (reversal L)` are not library material; R there is SM |rotationNumber (reversal L)| (= `rotAbs L` by `rot_eq_rotationNumber` + `rot_reversal`) | N | no |
| D-46 | 155 | Statement file carries un-reviewed library material `CarrierSlotFloor` etc. (§C-15) | X | no |
| D-47 | 165 `CV.singleton_D_i` (`CV/SingletonDi.lean` 25-43) | (D)(i) stated for EVERY CV-generic P on n ≥ 3 (not only the event's ambient polygon, N1); degree bound in support form, vacuous at f_A = 0 (FR-CV-165-1; f_A = 0 case empty by cor:groupedknot (B)); two independent fields `degree_gap` / `factor_zero`; Ω₁ = 0 derivable from the gap; f_A ≠ 0 not asserted | S / W | no |
| D-48 | 165 | FR-CV-165-3: `claims.py` / `DEPENDENCIES.json` list cb:singleton (103) as a dependency, but the CV row is proved from this lane's geo-layer split `cvt_singleton_split` (row 103 is the TEMPLATE on SM's `Component` / `SM.Generic`, not consumable on `CV.Generic`); FR-CV-165-4 algebra via `mindegAZ_mul` (§E-12) | D | no |
| D-49 | 175 `RProof.extreme_pair_zero` (`RProof/ExtremePairZero.lean` 78-84; bundle `X1Rows.lean` 1483-1522; `PRE_175_*` 1527-1600) | Bundle asserts three presupposition fields (`pair_absent_on_complete`, `pair_present_on_empty`, `third_singleton_piece` — the last promoted from the Proof section, NOTES_FINAL §7/§12 item 7); every field over ALL punctured t of either sign with sides named by local graph; no orbit-pairing hypothesis (FR-R-174..177 (frozen), AN L5560, the RowShape convention — FR §5 item 10 L964 writes "FR-R-175", a label that does not exist in AN); `pair_absent_on_complete` carries `FullAvail` though its proof is unconditional; `third_singleton_piece` does not state ownership (`cvt_exists_owner`) | S | no |
| D-50 | 175 | "For arbitrary outside support" rendered as ∀ Q over the full-availability fiber (`FullAvail` a hypothesis of `pair_row_zero`); `hef`/`heg`/`hfg` conditional rather than asserted; follows "fix a full-availability fiber" and R_ASSEMBLY_SPEC 61-64 | W | no |
| D-51 | 175 (also 174, 176) | Footprint via `CV.singleton_D_i` / `CV.carrierSlotFloor` ← row 99 (C) ← fd:contact includes the descent axiom and `src_contact` while the RA texts name only R-LOC/R-PAR/(D)(i) (§B-04) | P | no |
| D-52 | 175 | Disclosed breach of proof-withholding: a refuter read the one-line proof term at `RProof/ExtremePairZero.lean:85` (identical to the term in the statement file's header); incidental exposure of sibling one-liners and `have` lines in `PRE_175_third_singleton_piece` | X | no |
| D-53 | 103 `SM.cb_singleton` (`SM/CornerChainStatements.lean`; `CbSingletonData` 143-149 are lines of the frozen reviewer input `work/reviews/corner-chain-statements-reviewer-input.lean.txt` — live module :166) | Conventions: redundant guard c′ ≠ c (`Interlaces` irreflexive; guarded ↔ unguarded kernel-checked); `CarrierUniform`'s τ ≠ 0 vs printed "one sign" (equivalent on decompositions); `Interlaces` = G_P adjacency (def:interlace), not record interlacement (FR-CC-1); c(A) is the total coefficient (FR-CC-2); FR-CC-3 proof route bounds mindeg_a of the FULL product instead of the printed z⁰ rows (`z_parity` unused) | N | no |
| D-54 | 105 `SM.lem_corner_values` (`CornerValuesData` 168-184 of the reviewer-input file; live `SM/CornerChainStatements.lean:190`) | FR-CC-4: (i) "embedded (m_Q = 0)" rendered by the gloss `carrierCrossingCount = 0` only; geometric `Embedded` (row 104) not assumed; neither direction of `Embedded ⇔ m_Q = 0` stated (§C-14); "uniform" hypothesis kept though unused by (i) | S | no |
| D-55 | 105 | |r_Q| = 1 stated for the REAL `carrierRotation`; integer form is the companion `CornerValuesData.embedded_rotationInt` (not a bundle field); d_Q = 0 in ℤ via `cornerSlot` (FR-CC-5); guard y′ ≠ y and `hS` in (i) redundant | D | no |
| D-56 | 112 `SM.thm_C_soft` (`SM/CSoft.lean`; `CSoftData` statements 267-291 of the reviewer-input file; live `SM/CornerChainStatements.lean:289`, `CS7Data` :207 there = live :232) | FR-CC-12: genericity of P_ε quantified ∀ hQ (presupposition form; literally the consumer shape `UniquenessHypotheses.soft`, `SM/Uniqueness.lean:72`); the ∃ hQ form is the proved companion `CSoftData.exists_generic` (via accepted `SM.soft_family_generic`); CS0 could not verify the `Uniqueness.lean:72` pointer (outside its list; CS1 did) | W (companion proved) | no |
| D-57 | 112 | FR-CC-11: identity read in ℚ with `softAmplitudeMultiplier` (ℤ form = companion `doubled`; multiplier ∈ {−1,0,1} under admissibility); def:soft stated for (G1) only vs theorem's `Generic`; `softInsertion` defined for all real ε; labelling via `ZMod canonicalPosition`; proof-route deviation `sft_same_sign` (record layer) — same conclusion; FR-CC-7 the type clause of 110 is a description, not a hypothesis; FR-CC-9 genericity of the halves quantified (∀ h₁ h₂); FR-CC-14 RII/RI witnesses are new constructions | N | no |
| D-58 | 112 | Docstrings cite "proof 992-1147" while `\begin{proof}` is at sm-4:993 (`SM/CSoft.lean:11`, `SM/CornerChainStatements.lean:40,273`) (§E-06) | D | no |
| D-59 | 122 `SM.prop_anchor_values` (`SM/AnchorValuesRow.lean`; `AnchorValuesData` in `SM/AnchorValues.lean`) | FR-CM-1: F restricted to ℤ-valued functions on `GenericPolygon n` (printed proposition names no codomain; every consumer is ℤ-valued) | W | no |
| D-60 | 122 | FR-CM-3′: fields quantify over every `ZeroAnchor` / `LoopAnchor` / `LoopAnchorZero` WITHOUT def:anchors' case conditions (Admissible; MinimalAdmissible ∧ 2 ≤ |r|; (m+1,r) = (4,0)) and with any bound having the one-chamber property — a proved SUPERSET; FR-CM-3 / D-CM-1: `loopZero_turn` asserts BOTH readings of the undefined "orientation sign of the parent triangle" (common turn sign and rotation number); ∃! parent root in A_loop / A_loopZero | S | no |
| D-61 | 122 | `loop_turn` is `LoopAnchor.parent_turn` restated (tautological, as printed); `cornerPolygon n = 0` below arity 3, unreachable (FR-CM-5); `rotationNumber` ℝ-valued so (L₀) is an ℝ-equation after casting; FR-CM-9′ (premise "G1 (deleteVertex …) →" of `CuspLawC` implied by `w.CuspAt j`, premise kept) and FR-CM-13 (`root_values` an extra true clause) flagged for 127/128's future review | D | no |
| D-62 | 174 `RProof.generic_selected` (`RProof/GenericSelected.lean`; bundle `X1Rows.lean` 1434-1476) | Each couple field carries a strand-sign hypothesis (all-equal / SelectedAB / SelectedBC) ALONGSIDE the two-edge-side graph hypothesis; equivalent in the generic orbit only via accepted row 172 (`GenericTableData.selected_is_graph_selected`, `canonical_branch`) — refuter AR0 kernel-derived each from Edge* + ¬ExtremeLocal at any punctured t in the table's radius; canonical premise s_a = s_b = s_c narrower than `SelectedAC` (excluded triples = extreme orbit); sign hypotheses range over `SignType` incl. 0 (unreachable) | W (redundant) | no |
| D-63 | 174 | Printed words P/E, the E-side graph (edge ac only) and ¬EdgeAC not hypothesised (follow from ¬ExtremeLocal ∧ EdgeAB ∧ EdgeBC / R-LOC-2); `FullAvail` and generic orbit stated on side t only (R-PAR (P2)); all six generic branches explicit; identity for every opposite pair (t,t′) and every `hs`; feeds `cv_R_of_rows` as h174 | S | no |
| D-64 | 174 | Printed "opposite coorientation by multiplying by −1" not rendered (sides named by graphs, `OppositeSides` symmetric, NOTES_FINAL §6); `hef`/`heg`/`hfg`, `hs` universally quantified hypotheses (supplied by `LocalizationData.triangle_crossings` / `crossing_set_constant`); fields non-vacuous | D | no |
| D-65 | 174 | Docstring `GenericSelected.lean:28-29` says "the three branches are the fields of GenericSelectedData" but the bundle has TWO fields (`couple_relabelled` holds two branches); :36 says "the six literature interfaces" (six constants for five interfaces) (§E-07) | D | no |
| D-66 | 174 | σ orientation dependence (§C-09); `s174_hrec_prop` provable only under the ledger binding; two independent proof routes for `r174_arc_rec_moves` kept in drafts (§E-26); reviewers read `Cores.lean` definitions outside the brief and row 175's module | X | no |
| D-67 | 176 `RProof.extreme_transport` (`RProof/ExtremeTransport.lean`; bundle `X1Rows.lean` 1628-1686) | Transport fields conditional on explicit `hs` (crossing sets equal across the wall, R-LOC-2 (1)); `singleton_rows_present` stated per side (print: "on both sides"; other side by `outsideSupports_transport`, R-PAR (P2)); `sign_branch` does not restate σ ≠ 0 (`GenericTableData.nonzero`); `FullAvail` on side t only | W (formal) | no |
| D-68 | 176 | `graphs_complementary` quantified over every opposite pair of punctured parameters without the extreme-orbit hypothesis (R-LOC-2 clause 4; `LocalizationData.complement_on_triangle`; vacuously both-false on generic-orbit events); transport fields cover both orderings H→L and L→H; presupposition fields `singleton_rows_present` / `sign_branch` asserted | S | no |
| D-69 | 176 | Canonical words (1), gap strings A,B,C, Cramer identities, side vectors (4), rowwise table (5), (5a), empty-carrier convention have no Lean clause (proof data per NOTES_FINAL §8, lines 185-198); labels x = x_ef, y = x_eg, z = x_fg forced by the print's sign vector; the theorem docstring narrates the proof route (unit names) unverified by refuters; CS1 confirms the transport fields carry no uniformity / selector-nonzero hypothesis (matches the print's §4 selector-zero coverage) | D | no |
| D-70 | 176 | D-RM-5 / D-RM-6 / D-RM-7 carried in the proof route only (§C-01, C-02, C-08); the review brief pointed to NOTES_FINAL §7 where 176 is §8 | X / D | no |
| D-71 | all R rows and C rows (174, 175, 176, 103, 105, 112, 165) | `hn : 3 ≤ n` (and `[NeZero n]`) explicit binders though derivable (`three_le_of_h3` `X1Rows.lean` 146-152; Generic → Regular → 3 ≤ n) — the shared fixed-shape convention; no narrowing | N | no |
| D-72 | 91 / axiom / src:contact (reviewer conduct) | Files opened outside the permitted list (`ContactPath.lean`, `LitHomflyDescent.lean`; name-only grep on `work/lean/axiom-policy.json`; `OccOf` taken from usage); registration and AXIOM_REGISTRY.md:14-15 not checked from permitted files; no row proof body read; verdicts independent of the extra material | X | no |
| D-73 | 176 (reviewer conduct) | Proof-withholding deviation: the PRIMARY (literal) lens's grep that printed the sibling statements showed each theorem's one-line proof term (e.g. `r176a_extreme_transport_rowShape …`, a lemma name already in the statement file's header) — `r-extreme-transport.json` discrepancies[7] | X | no |
| D-74 | 176 (reviewer conduct) | Proof-withholding deviation: the strength lens (countersignatures[1]) incidentally saw the proof bodies of the accepted library lemmas `PRE_175_pair_absent_on_complete` / `PRE_175_pair_present_on_empty` while printing definition ranges with sed — `r-extreme-transport.json` countersignatures[1].discrepancies[1]. FR §5 item 9 (L958-960) names only the row-175 breach (§D-52); D-73/D-74 are not carried there (§F-13) | X | no |
| D-75 | 174 (reviewer conduct) | Sibling row 175's module was outside the permitted reading list, so its literal signature was NOT compared; its shape was checked only through the shared `RowShape` definition and `cv_R_of_rows`' binder `h175` — `r-generic-selected.json` discrepancies[1] | X | no |
| D-76 | 112 | No ε₀-anchoring: thm:A-soft gives, for every ε₀ > 0, an ε₁ ≤ ε₀; `CSoftData` gives a bare ∃ ε₁ > 0 — logically equivalent (any smaller ε₁ works), and the printed thm:C-soft has no ε₀ clause — `thm-C-soft.json` CS1 weaker_than_source[2] (AN L6019-6020 calls it "the marginal ε₁-vs-δ remark") | W (equivalent) | no |
| D-77 | 99 | `tangencies` (270-272) also records WHICH orientation is the normalised one (the `AllPosOrOneNeg` conjunct), and its `turn_ne` hypothesis is redundant with `UniformOrOneDissent` — `cf-thm-carrierfloor.json` CS0 stronger_than_source[8] | S / D | no |
| D-78 | 122 | The soft hypothesis's `∀ hQ : Generic (P_ε)` guard makes `AnchorValuesHypotheses` a (formally) weaker requirement on F than an ∃ hQ form, so the proposition applies to (formally) more F; equivalent by lem:soft-generic (i) — `prop-anchor-values.json` CS1 stronger_than_source[3] | S (formal) | no |
| D-79 | 161 | `sl K = writhe D` asserted for EVERY transverse knot K with `K.front = D` (K quantified separately) rather than for "the" knot presented by T; equivalent to the printed meaning — `cv-ax-etnyre.json` CS1 stronger_than_source[1] | S (formal) | no |

---

## E. Documentation debts and inconsistencies (nothing here changes a proof; most are comment-only edits, some inside ACCEPTED modules — see §G-05 before touching those)

### E-01 — `SM/ContactPathOfDescent.lean` docstrings still call `AmbientIsotopyDescent` "a def : Prop, NOT an axiom" (lines 54 and 173, verified); only the header (lines 1-2) was fixed 22:40Z
Literally true of the predicate (the assumption lives in `SM/LitHomflyDescent.lean:37`) but easy to misread. The 22:41Z closing pass (AN
L6321-6328) changed comment lines only and left the docstrings on purpose; `lit-homfly-descent.json` executor_notes had promised a
"closing documentation pass" for them. Fix: point both docstrings at the axiom (comment-only; accepted module → §G-05); re-run the
development checker. **Decision.** author (comment edit inside an accepted module) / executor once allowed.

### E-02 — Citation nits on row 91 / the descent axiom (tex line numbers)
Consumed descent sentence is sm-3:3310-3312 (docstrings say 3313-3316: `ContactPathOfDescent.lean:163`); the hand isotopy-extension step is
3276-3312 (docstrings say 3264-3313: `ContactPathOfDescent.lean:57, :163, :175, :205, :231, :679`; `SM/LitHomflyDescent.lean:24` — all
verified by grep); `ContactPathData` field ranges off by one (`:103` "3211-3213" → 3212-3214, `:109` "3213-3218" → 3214-3219, `:113`
"3219-3221" → 3220-3222, `:124` "3221-3225" → 3222-3225); FR §4.3 itself writes "3276-3311". The excerpt file is byte-identical to
`reference/SM/sm-3-statesum.tex` 3210-3233 (`\begin{proof}` at 3234). ~10 docstring lines. **Decision.** author/executor as §G-05.

### E-03 — Frozen reviewer-input statement file of the descent axiom keeps the pre-correction docstring
`work/reviews/cp-finite-contact-path-reviewer-input-statement.lean.txt` 100-101 ("exactly what the printed proof consumes at sm-3:3313-3316")
vs the live `ContactPathOfDescent.lean:163`; def bodies byte-identical (reviewers diffed §1). Do NOT regenerate the frozen file (its sha256
is bound in the accepted review); note it in FR §7 if FR is next regenerated. **Decision.** none.

### E-04 — `source_sha256` bookkeeping in two review JSONs
`work/reviews/cp-finite-contact-path-row.json` and `cp-finite-contact-path-conditional.json` record `fa17a1b162bd…` = sha256 of the WHOLE
`reference/SM/sm-3-statesum.tex` (verified by `sha256sum`), while the excerpt file hashes to `9f9854f62a8b…`. The excerpt is correct; the
field is mislabelled. Either patch the two fields (and refresh MANIFEST if manifested) or leave and record in FR §7 (FR already notes
it). **Decision.** executor.

### E-05 — fd:contact docstring line refs, axiom-count wording, receipt naming
`SM/FdContactStatements.lean:29` ("3418-3421" → closing sentences 3419-3421), `:35` ("3409-3411"), `:37` ("3412-3418" → display 3416-3418);
the status line names only src:contact + lit:homfly while the kernel set is the nine; AN 16:40Z (L5613-5627) says "seven registered
literature axioms + the standard three" and `cv-ax-slbound.json` `kernel_check` repeats it — it means the nine-element list; receipt
`work/checks/dev-check-fdcontact-row162-implemented.json` names row 162 for the 94+162 port. **Decision.** executor (docstring edits in an
accepted module → §G-05).

### E-06 — `thm-C-soft` proof locator "992-1147" should be "993-1147" in three places
`SM/CSoft.lean:11`, `SM/CornerChainStatements.lean:40`, `:273` (verified). Comment-only; accepted modules (§G-05). **Decision.** executor once allowed.

### E-07 — `RProof/GenericSelected.lean:28-29` "the three branches are the fields of GenericSelectedData" (the bundle has two fields); `:36` "the six literature interfaces" (six constants, five interfaces)
Verified. Comment-only; accepted module (§G-05). **Decision.** executor once allowed.

### E-08 — `SM/CornerChainUnits.lean:3811-3815` U110-B docstring of `def s7b_slidingMark` (:3816; the mark map consumed by `structure s7b_SlidingTransport` :3934) is wrong for the leg-M side
"vm = the visit of x₋ on the leg edge M−1 / M": on the leg-M side the structure built on this mark map is not inhabited (§C-05; the first
version of this register attributed the docstring to the structure itself); a one-line "see
`s7r_SlidingTransport'` for the leg-M side" would prevent the next unit from re-discovering it. Accepted module (§G-05). **Decision.** author.

### E-09 — Line-count and time slips between reports, notes and STATUS (all verified at closing, none affects a proof)
- `CS7_STATE.md`: `w3_s7_bigon_law_at_of` "line 8854" — actual 8876 (sliding glue 4829 in both).
- W3C line count: `W3C_ASSEMBLY_REPORT.md` §0 does NOT say "16 774 / 1425" — both its paragraph (L12) and its table (L32) read "16 945
  lines, 1428 declarations" (the report was rewritten after its 00:26Z draft; mtime 00:36:54Z; `W3C_Assembled.lean` mtime 00:36:55Z, not
  "00:32Z"). The stale 16 774 / 1 425 figures survive only in FR L410 (pending table), L560 (§3.4), L1183 (§7 — whose own note "§0
  (00:26Z) says 16 774" is itself stale) and L1223, and in AN L6421 (L6420 is blank). The next FR regeneration must drop or reword the
  L1183 note and fix L410 / L560 / L1223. (The first version of this register and of §A-15 repeated FR's claim without re-reading the report.)
- Row-177 remaining size: W3C §6 "≈ 1.0-1.9k" (0.7-1.3k + 0.3-0.6k); AN L6437 / STATUS "≈ 1.3-2.5k"; FR §3 pending table attributes
  "≈ 1.0-1.9k" to `w3cx_outer_residue_data` ALONE (a slip — the residue is 0.7-1.3k). CONTENT slip too: AN L6427-6428, FR L410 and FR
  §3.4 L566 include "the sign table (1c)" in the residue; the report (§0 (iii) L17-18, §3 L181, §6 L245) has it PROVED (`w3cx_sign_table_at`)
  and the residue = parity + identification only (§A-16).
- Audit A-110-1 conclusion: AN entry 22:40Z, STATUS "CONCLUDED 22:39Z".
- Row 176 acceptance / STATUS top block: STATUS's first bullet says "00:12Z" (correct). Of the pre-conclusion wording ONLY "no branch
  currently past its bound" survives (`work/STATUS.md` L11, the fifth bullet) — superseded by the "FINAL (2026-09-16)" bullet above it. The
  sentence "177 (Wave 3c assembler, bound 02:15Z), 178 -> 183 after 177" is NOT in STATUS (grep for "02:15Z", "Wave 3c", "178 -> 183"
  finds nothing): it lives in AN L6417 (the row-176 ACCEPTED entry) and in FR §7 L1190-1194, which was written against the 00:33Z STATUS
  header, before the 00:57Z rewrite. (The first version of this register copied FR §7 without re-verifying.)
- `work/STATUS.md` stacks five "# STATUS" headers (00:57Z top; 2026-09-15 18:40Z, 17:52Z, 16:52Z, 14:00Z) above the 2026-09-14 text;
  the 22:40Z block sits header-less under the top header (FR §7).
- "21 vs 20 `w3a_` sub-leaves" (AN L6194 vs L6221): 21 replaced `sorry` lines = 20 `w3a_` + `w3a_exists_params`.
- Skeleton line numbers "207 vs 199" in `work/drafts/moves/W3_SKELETON_REPORT.md` (row 177, unit U-W3-0 of the moves lane — not a
  corner file; every §2 number offset by 8; anchor on names).
- The 2026-09-14 lane-size slip "≈ 26.8k" (really ≈ 39.9k) carried over (FR §7).
- FR §7 itself is stale relative to the 00:57-00:59Z closing; the next regeneration must fix: L1155-1157 "`work/delivery/` itself has NOT
  been refreshed since 2026-09-14 18:21Z … run `refresh.sh` after this root file is final" (`refresh.sh` ran 00:56Z and 00:59Z, AN
  L6453-6479, §E-18); L107 (§0) and L1190 "STATUS.md header (last update 2026-09-16 00:33Z)" and L1192 row 176 accepted "00:05Z 09-16"
  (the header is 00:57Z and says 00:12Z); L1241 "five # STATUS headers (2026-09-16 00:33Z on top)" (the top header is 00:57Z);
  L1274-1276 "Placeholders left for the executor's stamps … FINAL-TIME and STAGE-CHECK-RESULT" and L871 (§4) "the one STAGE-CHECK-RESULT
  token of this file" — `grep -c '<<' FINAL_REVIEW.md` = 0, they were filled; both sentences are dead text. §E-22 lists other "not
  verified" items but not these.
**Decision.** executor (documentation; fix STATUS's top block at the next checkpoint).

### E-10 — Five-vs-six inputs and the axiom-count vocabulary; 13 vs 14 rows carrying the descent axiom
TARGETS.md:8 "five listed literature interfaces"; AXIOM_REGISTRY has five headings; the policy has six literature keys; `work/lean` has six
`axiom` declarations. Vocabulary in use: "the nine registered axioms" (= 3 standard + 6 constants; FR's choice), "seven registered
literature axioms + the standard three" (AN 16:40Z, means nine), "six registered literature axioms" (CS7_STATE.md, W3_ASSEMBLY §4),
"the six literature interfaces" (`GenericSelected.lean:36`, wrong: five interfaces). Rows carrying `SM.lit_homfly_descent`: AN L6457 and
STATUS say 13, FR §4.3 lists 14 (91 + the thirteen nine-axiom rows) — FR's recount from the 00:14Z audit is the one to trust; 15 for
`src_contact` agrees in both. Standardise on FR's wording when documents are next touched. **Decision.** executor.

### E-11 — Stale headers and "sorry-free" wording in accepted modules (carried over from 2026-09-14, NOT done at closing — FR §5 item 8)
`SM/LinkLaurentRing.lean:80-81` and `SM/LinkInterfaces.lean` 55-60 / 180-181 (header field names); `SM/FlatCarriersDefs.lean:6` still says the
two row theorems "are proved in SM/FlatCarriers.lean when the prover units finish" (verified; they were, 2026-09-13); 55 library modules at register time
(`grep -rliE 'sorry-free|no sorry' work/lean --include=*.lean | wc -l` = 55 = the number of `.lean` files under `work/lean` containing
the string `sorry` at all; STATUS.md 2026-09-14 item 6 counted 57, 30 of them row modules — 57 is not current) say "sorry-free"/"no
sorry" in their headers (the checker does not object — the executor's stricter practice "not even the string in a docstring of a new
port" applies to NEW ports); `Bridge/SmR.lean:1` still says
`Bridge.sm_R` is "blocked by GAP-2" (verified). All are accepted modules — comment-only edits need §G-05. **Decision.** author.

### E-12 — Dependency column out of step with the proofs: `tools/claims.py` / `blueprint/DEPENDENCIES.json`
Row 165 lists cb:singleton (103) although nothing of row 103 is consumable on 165's domain (FR-CV-165-3, AN L5553-5556); rows 127/128 no
longer depend on 105 (D-CM-5, AN L5710-5711); blueprint edges 57 → 104/105 not realised (D-ER1, `corner_values_i`). The column is used
only for `--next`; the blueprint is frozen — record, do not patch. **Decision.** none (recorded here and FR §7).

### E-13 — AN FR-SC-11 (L5346-5348) cites the wrong evidence for the w − D convention; the decisive probe scripts are not in the package
The judge's eye probe (D = U = 1, r = 0) cannot discriminate w − D from w − U; the sign convention IS established by three refuter probes
with D ≠ U (`src-contact.json` CS0/CS1/AR0/AR1; `cv-ax-etnyre.json` AR0 §6: D=3/U=1, D=2/U=0, D=4/U=0), whose Python scripts
(`probe_sl*.py`, `probe_sc*.py`, `probe161.py`) lived in reviewer scratchpads under `/workspace/scratch/claude-0/…` and are gone unless
recovered. Amend the AN sentence (a NEW dated entry, never an edit of an old one) and, if reproducibility is wanted, re-derive the probes into
`work/drafts/contact/`. **Decision.** executor.

### E-14 — Row 174: no AUTHOR_NOTES entry on the ledger σ's orientation dependence (asked for by `R174_ASSEMBLY_REPORT.md` §8.1 and `R174W2_ASSEMBLY_REPORT.md` §0)
Recorded only in FR §5 item 6 (§C-09). Write the AN entry. **Decision.** executor.

### E-15 — Review-brief locator errors (fix before re-using `work/port/review_prompt_*.md` as templates)
def:transverse-front at sm-3:3328-3340, not "341-343"; rem:curlauthor is not in sm-3 (`reference/R/CV/d3_floor.tex:704`); `R_ASSEMBLY_SPEC.md`
/ `EXECUTION.json` live at the package ROOT, not `reference/R/RA/`; `NOTES_FINAL.md` §7 → §6 (row 174, `review_prompt_r-generic-selected.md:28`) and → §8 (row 176,
`review_prompt_r-extreme-transport.md:30`) (verified: §6 = 174, §7 = 175, §8 = 176/177) — CAUTION: the grep below also hits
`review_prompt_cvtail-rows.md:36`, where "§7" is CORRECT (it is cited there for row 175); do not "fix" that one; `softInsertion` / `SoftAdmissible` live in `SM/SoftInsertionTuple.lean`, not `SoftGenericLemma` /
`SoftAmplitudeSectors`; the descent brief's header repeated the pre-correction phrase "exactly the missing sentence". `grep -n
'341-343\|reference/R/RA/R_ASSEMBLY\|NOTES_FINAL.md §7' work/port/review_prompt_*.md`. **Decision.** executor.

### E-16 — `blueprint/AXIOM_REGISTRY.md` lacks a sub-entry for the second declaration (frozen; author only) — see §B-05 / §G-07.

### E-17 — `work/delivery/tools/gen_final_review_tables.py` is stale (FR §7)
Its abbreviation table (line 22) knows H/LM/LMU/NG only (no HD/SC); `PENDING_REASONS` carries the 2026-09-14 texts for rows now accepted
(91, src:contact, 94, hyp:R, 76-80/83/93) and the 2026-09-14 reasons for 110/127/128/174-178/183/184; its `DRAFT` target is
`work/FINAL_REVIEW_DRAFT.md`, not the root file; `audit_axioms()` prefers the stale `work/delivery/receipts/declaration-audit.summary.json`
(36 079 checked). The 2026-09-16 tables were produced by a scratch copy (`…/scratchpad/fr/gen_tables_scratch.py`, GONE with the session)
whose output for the 168 rows of the 2026-09-14 table was byte-identical. Porting the patches (HD/SC, `9`, the 16 curated readings, the
eight §3 pending texts, the 00:14Z audit) into the delivered tool is an executor tool edit. **Decision.** executor.

### E-18 — `work/delivery/README.md` and `work/HANDOVER_README.md` still describe the 2026-09-14 state
Verified at register time: `work/delivery/README.md` opens with "State at delivery (2026-09-14 18:15 UTC …): claims verified 109/132 …";
`refresh.sh` (run 00:56Z and 00:59Z, 1045 → 1047 files) refreshes copies and receipts but evidently not the README prose;
`work/HANDOVER_README.md` (21:15Z 2026-09-14) says 109/132, 168/192, 4/8, "four registered literature axioms". Both need a dated 2026-09-16
paragraph (124/132, 184/192, 5/8, six constants, the eight pending rows) or a pointer to this register. **Decision.** executor.

### E-19 — `work/drafts/floor/PLAN_FINAL.md` §4 "lp_lm only" axiom expectation is stale
`cf_thm_carrierfloor_R` and `uf_z_parity` also depend on `lit_homfly` and `lp_lm_uniqueness` (AN L5602-5605; `coefficient_transport` on
`lp_lm_uniqueness`, the frozen `knot_reverse` proof on `lit_homfly`). Draft-only. **Decision.** none.

### E-20 — Staged 178/183 files carry `<HH:MM>Z` header placeholders and an import of a module that does not exist yet
`work/drafts/cvtail/port/R178_183/RProof/CvR.lean` line 1 ("Ported <HH:MM>Z 2026-09-16 …") and `…/Bridge/SmRRow.lean` line 1; `CvR.lean`
imports `RProof.ExtremeSelected` (absent until §A-15 closes) — intended, compiles only then. Fill the time at port. **Decision.** executor (at port).

### E-21 — FR §4.3 / §4.6 must be updated when 178/183/184 are declared (footprint, clause table) — see §B-04. **Decision.** executor.

### E-22 — Items explicitly "not verified at closing" or unverifiable now
Wall-clock claims (checker 4-6 min idle; unit compile 26-38 s idle vs "many minutes" under ≈ 25 agents; "two shells died" — AN L3929-3931
records one); the exact `#print axioms` facts for the unmapped library modules `SM/BigonDeletion.lean`, `SM/CS7Sliding.lean`,
`RProof/RALedgers.lean`, `SM/Comparison.lean`, `SM/CInherits.lean` come from `lake build` and scratch files, not from a checker receipt
(§F-01); `work/checks/stage-1.json` is the placeholder `{"passed": false, "stage": 1, "state": "checking"}` written by the 00:33Z `--all`
run (the FAIL text is in the `.log`); the W3C §0 line count (§E-09); the `Bridge/SmR.lean` contents were checked here only by grep of its
declarations. **Decision.** none.

### E-23 — Prose `sorry` mentions to reword at port time
`W3_Assembled.lean`: 8 prose mentions (report §4) — lines 6, 3431, 4723, 4757, 4761, 4888, 8595, 8863 (4757 and 8863 are the `sorryAx`
mentions in the two shape-check docstrings; `grep -c sorry` = 20 = 12 terms + 8 prose). `W3C_Assembled.lean`: exactly TWO, 7856 and 14706
(`grep -c sorry` = 6 = 4 terms at 4095/11690/13746/16426 + 2 prose); the W3C report's own list (§0 table L34, §3 L183, §7 L264-265: "3 prose
mentions … 16561") overstates by one — the KNOT chain docstring near 16561 (section `W3CK_Chain`, 16545-16937) contains no `sorry`, so the
porter must not hunt for it; the `-- (W3C assembler)` comments at 9253, 9283, 13113, 13135 name the RESTATEMENTS (§A-18 item 1), not the
word. The checker rejects only `sorryAx`, but the executor's practice is no `sorry` string in a ported module. **Decision.** executor (at port).

### E-24 — `cv-ax-etnyre.json` records the `slCircle`/`U_circle` identification as a pending unit U0 (16:51Z); superseded by `SM.u_circle` (`SM/FdContactUnits.lean:102`, 17:12Z)
Record in FR §7 if FR is regenerated. **Decision.** none.

### E-25 — The 2026-09-14 `work/RESUME_FOR_NEXT_AGENT.md` text (24 unaccepted rows, "GAP-2 open", "src:contact never declared", four axioms) is SUPERSEDED by the 2026-09-16 rewrite; the 2026-09-14 verification note is kept there as history. **Decision.** none.

### E-26 — Housekeeping: two independent proof routes for row 174's last obligation are both in the drafts
Route V (ported, `RProof/GenericSelectedUnits.lean`: `r174v_arc_rec_moves_proof`) and Route R (`work/drafts/moves/R174W2_ARCR.lean`, 7444 lines,
an independent check, NOT ported); AN L6361-6366. Whether to prune is not recorded. **Decision.** executor (leave as is unless space matters).

### E-27 — Unmapped conditional library modules (no content effect; never map while their premise is open — D-F11)
`SM/ContactPathOfDescent.lean` (`cp_finite_contact_path_of_descent`, now consumed by row 91), `Bridge/SmR.lean`, `RProof/X1Rows3.lean`,
`SM/LinkingCalculus.lean` (2026-09-14 list), and new: `RProof/RALedgers.lean` (the three ledgers, `cv_R_of_rows`, `sm_R_of_rows`),
`SM/Comparison.lean`, `SM/CInherits.lean`, `SM/FdContactStatements.lean` (`fd_contact_of_units`, `ax_etnyre_of`, `ax_slbound_of`),
`SM/CarrierFloor.lean` (`_of_bound` forms), `SM/CornerChainUnits.lean` (`cb_singleton_of_floor` …; NOT `thm_C_S7_of`), `SM/CS7Sliding.lean`,
`SM/BigonDeletion.lean` (FR §5 item 13). `RProof/GenericSelectedUnits.lean` and `RProof/ExtremeTransportUnits.lean` ARE inside the audited
closure (imported by mapped row modules). **Decision.** none.

### E-28 — D-GAP2 item 4 housekeeping EXECUTED 13:50Z 2026-09-15: the stray root file `'=3'` was DELETED, the FINAL_REVIEW.md MANIFEST line refreshed, `verify_bundle.py` PASS
The author's instruction (AN L5155-5156: "refresh the FINAL_REVIEW.md line in the root MANIFEST.sha256 (verify_bundle.py currently fails on
it), and delete the stray file '=3' at the package root") was carried out — AN L5180: "HOUSEKEEPING (item 4): stray file '=3' deleted;
FINAL_REVIEW.md manifest line refreshed; `python3 verify_bundle.py` PASS at 13:50Z". A package-ROOT change recorded nowhere but that AN
line (FINAL_REVIEW, STATUS, the RESUME and the first version of this register do not mention it; a fresh agent would otherwise see it only
in MANIFEST history). Verified at the repair pass: no file `=3` exists at ROOT; `verify_bundle.py` PASS (191 files) at closing. **Decision.** none (record).

---

## F. Tooling and process caveats a next agent must know

### F-01 — `audited_declarations` (41 658) covers ONLY the import closure of the MAPPED modules plus `Supplemental`
`tools/check_lean.py` builds the mapped modules + `work/lean/Supplemental.lean` (a fixed list of 70 imports, none of the 2026-09-15 library
modules) and runs `Supplemental.auditProject` over `env.constants`; a library module imported by no mapped module is built
(`project_sha256` hashes the file) but contributes nothing to the count and its axiom sets are NOT machine-checked by the checker.
Evidence (FR §7): `dev-check-cs7sliding-library.json` reports the same 39 005 audited as `dev-check-row122-accepted.json` while its
`project_sha256` has one more file. Per-declaration rows in `work/checks/declaration-audit.json` exist only for the 184 mapped
declarations (`audit.declarations` = 184, `audit.checked` = 41 658). Consequence: `#print axioms` facts for `SM/BigonDeletion.lean`,
`SM/CS7Sliding.lean`, `RProof/RALedgers.lean`, `SM/Comparison.lean`, `SM/CInherits.lean` rest on `lake build` + scratch files (AN entries),
not on a receipt. A full-library audit would mean extending `tools/check_lean.py` or a scratch `#print axioms` pass (never inside `work/lean`).

### F-02 — The review schema keys, incl. `reviewer_files_read`
REVIEW_SCHEMA = {`verdict`, `reason`, `discrepancies`, `stronger_than_source`, `weaker_than_source`, `supporting_definitions_inspected`,
`reviewer_files_read`}; REFUTE_SCHEMA = {`refuted`, `argument`, `files_read`}. `work/port/write_review_and_accept.py:23` reads
`r['reviewer_files_read']` for every review and binds the sha256 of every file named there (a review whose JSON lacks the key aborts the
acceptance); `summarize_review.py:11` prints `files=len(r['reviewer_files_read'])`. Save the workflow result as
`/workspace/scratch/lean_results/<slug>-round1.output` in the shape `{"result": {"reviews": [...], "refuters": [...]}}` (RESUME §4).

### F-03 — Heredocs and quoting when appending to `work/AUTHOR_NOTES.md` or writing Lean text from bash
Lean names in the notes are full of backticks (`` `thm_C_S7` ``) and `$`-free but `'`-rich text: an UNQUOTED bash heredoc (`<<EOF`) executes
backtick segments as command substitution and silently mangles the entry; always use a quoted delimiter (`<<'EOF'`) and append with `>>`.
(The 2026-09-14 RESUME §4 records the sibling bite: apostrophes inside the quoted texts of `write_review_and_accept.py`.) This register
and the RESUME rewrite were written that way. Not recorded as an AN incident (grep for "heredoc"/"backtick" in AN finds nothing) — a
practice note. The 2026-09-15/16 task framing "interrupted-heredoc repairs" has NO recorded incident behind it: `grep -n -i
'heredoc\|backtick\|interrupt\|mangle\|command substitution'` over AN L5144-6479 gives 0 hits, and this register, the RESUME and FR show no
EOF artefacts, duplicate headings or numbering gaps. If such a repair ever happened to an AN entry it is undocumented in AN, FR, STATUS,
this register and the RESUME alike — a fresh agent cannot learn which entry was affected and should treat every 2026-09-15/16 AN entry as
unrepaired text.

### F-04 — `pgrep`/`pkill` self-match: the pattern must not occur literally in the invoking command line
AN L3929-3931 (verbatim): "a background waiter of mine matched its own command line (pgrep -f on a literal that the same command
contained) and never returned; killing it by the same pattern killed my own shell. Rule: patterns for pgrep/pkill must not occur in the
invoking command line (use character-class tricks on the pattern itself, e.g. 'check_lea[n]')." Use `pgrep -f '^python3 tools/check_lea[n]'`.

### F-05 — ONE `lake build` or checker at a time; subagents never build
AN L3893-3894 (two concurrent checkers → the second killed within seconds; "Rule kept: one checker/build at a time"). Checker:
`nohup python3 tools/check_lean.py work/lean > work/checks/checker-run-<HHMM>.log 2>&1 &`, poll the log (4-6 min idle). Subagents compile
drafts ONLY with `cd work/lean && lake env lean ../drafts/<lane>/<file>.lean` (uses the built oleans; safe while the checker runs) and never
write under `work/lean`. `#print axioms` goes in a scratch copy compiled with `lake env lean <abs path>` from `work/lean`, never in
`work/lean` (the checker rejects `#print`/`#eval` directives). `work/lean/.lake` is a symlink to `/root/lean-lake` (local disk; rebuilt by
`setup.sh` / `lake build`; excluded from every archive).

### F-06 — The reassessment rule and how the audits were applied
Rule file: `/workspace/repos/lean/reassessment_rule.md` (61 lines; Mark, 2026-09-14) — reassess after two substantive attempts or 60 min of
active work without a NEW ACCEPTED source claim, or immediately on domain mismatch / circularity / impossible interface / repeated failure /
growing helper scope; response = a bounded audit (claim + remaining obligation, diagnosis, continue/change/abandon, ONE decisive test with
success criterion, effort bound ≤ next audit window, consequence on failure; unproved feasibility labelled CONJECTURE; accepted count
stated unchanged). Memory note: `/root/.claude/projects/-workspace-repos-lean/memory/lean-reassessment-rule.md`. Adopted AN L5019-5036.
Audits of this period, each with its consequence APPLIED: **A-110-1** (AN L6079-6116, 20:46Z; test = corner wave 3, bound 00:30Z; FAILED
→ L6300-6319, 22:40Z: no further corner construction), **A-177-1** (L6171-6204, 21:21Z; test = the trans-free copy; SUCCEEDED → L6216-6231,
22:00Z: Wave 3b as a NEW bounded window, stagnation history since 15:49Z retained), **A-177-2** (L6330-6359, 23:20Z; test = Wave 3c,
bound 02:15Z; FAILED → L6419-6440, 00:31Z: no further 177 construction). Also the reassessment note D-RM-1 (L5664-5689: the move
realisations are one shared toolkit lane) and D-CC-5 (L5839-5847: an acceptance bottleneck, not a stall). FR §6 summarises. Rule of
thumb for a next agent: any resumption of 110 or 177 is a NEW window on a branch with a stagnation history — the author, not the
executor, opens it (§G-01, §G-02); record the audit state in AN before constructing.

### F-07 — The heartbeat: what ran, what survives
CLAUDE.md rule 6 / `EXECUTION.json` `progress_interval_seconds: 900`: report `claims verified X/132` every ≤ 15 min while active. On
2026-09-15/16 two mechanisms ran (STATUS.md): `python3 tools/progress.py --watch` (log `work/progress-watch.log`; still running as pid 77461
at 01:32Z AND at 02:17Z 2026-09-16 (the repair pass; `pgrep -af 'progress.py --watc[h]'`); last claims line
"[2026-09-16T02:17:05+00:00] … claims verified 124/132 (93.9%) … 184/192 accepted; targets 5/8", trailer "Stage 1: not established by a
current checker receipt" — re-verify with `pgrep` before relying on it) and an in-session Claude Code timer "cron every 14 min" that posted the line into the executor's conversation — that timer dies
with the session (there is no system crontab on the pod: `crontab: command not found`). A next agent restarts its own reminder and either
keeps or kills the watcher deliberately (`pgrep -f 'progress.py --watc[h]'`).

### F-08 — Where the archives live and what they exclude; NO checkpoint tarball of the 2026-09-15/16 state exists
`/workspace/scratch/lean_results/RESULT_2026091{3,4}_*.tgz` — 32 checkpoints (`ls | wc -l` at the repair pass; with the handover
mirror 33 `.tgz` in the directory), the last `RESULT_20260914_1820Z_FINAL.tgz` (13 MB, 18:21Z 09-14); `LEAN_HANDOVER_20260914_2115Z.tgz` (106 MB) in `/workspace/repos/lean/` with a mirror in `/workspace/scratch/lean_results/`
(AN L5135-5142: the whole package directory minus `work/lean/.lake`, `work/checks/declaration-audit.json` and `work/checks/lean-check.log`
(~0.9 GB each, regenerable — today 197 723 and 5429 lines), plus `handover_extras/` = project CLAUDE.md, `reassessment_rule.md`, the
session's memory files; `env.sh` excluded). Verified by `ls`: nothing dated 2026-09-15 or 2026-09-16 exists, and no AN entry after L5144
mentions a checkpoint or tarball. The 2026-09-15/16 work (16 rows, six new lanes, ≈ 48k lines of new library, the two drafts) is on the
volume only. FIRST ACTION for a next agent: build `LEAN_HANDOVER_20260916_<HHMM>Z.tgz` with the same exclusions (`tar --exclude=work/lean/.lake
--exclude=work/checks/declaration-audit.json --exclude=work/checks/lean-check.log …`) into `/workspace/repos/lean/` and
`/workspace/scratch/lean_results/`. The gzipped audit is also in `work/delivery/receipts/`.

### F-09 — Compile latency under load is latency, not correctness
Under ≈ 25 concurrent agents a full compile of a 3000-line draft takes many minutes (AN L5610-5611); the hard stops given to units were
audit bounds (units 00:00Z/00:15Z/00:45Z/01:45Z, assemblers 00:30Z/01:00Z/01:15Z/02:15Z). Idle figures: W3_Assembled 26 s, W3C_Assembled
34-38 s, `W3_A1_Assembled` 36 s. Plan wall-clock bounds on the 8-vCPU pod accordingly.

### F-10 — Lean pitfalls recorded this period
RProof's global `DecidableEq (Crossing P)` instance conflicts with `open Classical`; fixed by a local high-priority instance in helper
regions, kept verbatim (redundant) in the CV modules (AN L5814-5815, L5866-5867; copy from `work/lean/CV/SingletonDi.lean` or the RALedgers
helper regions). W3C §8: `refine { f₁ := …, … }` for a Prop structure with a less-indented continuation fails — use `⟨…⟩`; a `/-! -/` module
comment directly after a `/-- -/` docstring is a parse error; `geomAt E t ht.1` vs `(genericAt E t ht.1).crossingGeometry` are defeq (use
`exact`, not `rw`); `(visitOn x v h).1 = x` by `rfl`; `SignType` is not a `SubtractionMonoid` (`decide`, not `neg_ne_zero`);
`IsAlternating sa sb sc` does not imply `sa ≠ 0`. Skeleton `variable`s are included only if the statement mentions them (`include hG in`);
no forward references; Mathlib lemmas outside the import closure must be re-proved or the import added (RESUME §5 lessons).

### F-11 — The stage check FAILS by design and the refresh sequence after any new acceptance
`python3 tools/check_lean.py work/lean --all` and `--stage 1` report the eight rows (stage 1 is the ONLY stage commissioned:
`EXECUTION.json` `acceptance_stages: [1]`, `certificates: []`; `--stage 2/3` → "outside this handoff scope"). After each acceptance
(AN L6465-6467): development checker → copy the receipt to `work/checks/dev-check-<name>-accepted.json`; then `--all`; `--stage 1`; `python3
verify_bundle.py`; `bash work/delivery/refresh.sh`; and `python3 work/port/refresh_manifest.py FINAL_REVIEW.md` after editing any manifested
root file (MANIFEST.sha256 lists 191 files). 100 receipts in `work/checks/dev-check-*.json` at register time, all `passed: true`; the
current one is `dev-check-FINAL-20260916.json`.

### F-12 — Fixed names are enforced by the checker; conditional theorems are never mapped
`tools/check_lean.py:104`: `fixed = policy['literature'] | policy['targets'] | {'hyp:R': 'SM.hyp_R'}`; `:114`: `allowed = policy['standard'] +
list(policy['literature'].values())`. `map_row.py implement <row> <Decl> <Module>` must use the fixed name where one exists (§A lists
them). D-F11: a row theorem with an undischarged premise (or a statement-only bundle) is never mapped — hence the eight pending rows have
`module ""` in `work/lean/lean-declarations.json` while their `_of` forms are ported library.

### F-13 — AI-only review; identity strings; disclosed protocol deviations
All 184 accepted rows and the two 2026-09-15 interface declarations were reviewed by Claude Code subagents of the implementer's model family;
the 16 rows accepted since 2026-09-14 had one workflow each (three lenses + two refuters, proof withheld), no second session, no
countersignature; the 39 handover rows keep their 2026-09-13 countersignatures (FR §5 item 9). The map's `reviewer` string
`reviewer-pod-claude-fable-5-1-20260913 (…)` and `author …-20260913` are the workflow's standing identities, dated by first use (FR §7).
Disclosed deviations (§D-22, D-52, D-66, D-72 and, added at the repair pass, D-73/D-74 — row 176's lenses saw one-line proof terms and
two library proof bodies incidentally — and D-75 — row 174's review did not compare sibling 175's signature) are recorded in the JSONs; FR
§5 item 9 (L958-960) and §6 name only the row-175 breach (D-52) and must be extended at the next regeneration; no re-review is required
unless the author wants a strict-protocol rerun (§G-10). No human has read any review.

### F-14 — Port tools and merge scripts (where they are; which are gone)
Corner: `work/drafts/corner/port/tools/{port_build.py (286 lines), port_clash_scan.py (56), port_stmt_check.py (179)}`; the wave-3
`assemble.py` was in the session scratchpad (GONE; W3_ASSEMBLY_REPORT §1 gives the slice ranges). Moves/177: `work/drafts/moves/assemble_W3C.py`,
`assemble_W3C_connect.py`, `check_W3_identity.py`, `check_W3_statements.py`, `clash_scan_W3.py`, `W3C_AXIOMS.log` (both `assemble_W3C*.py`
hard-code relative filenames and OVERWRITE `W3C_Assembled.lean`; `check_W3_statements.py` reads `Skeleton_W3.lean` from the cwd — run all
three from `work/drafts/moves/`, §A-15; `work/drafts/moves/port/` has `R174/` and `R176/` only, no `R177/`). Comparison:
`work/drafts/comparison/port/tools/port_build.py` (regenerates the ported modules). Accept cycle: `work/port/{map_row.py (31 lines),
strip_proofs.py (38), summarize_review.py (19), write_review_and_accept.py (75), refresh_manifest.py (21)}` and one `review_prompt_<slug>.md`
per reviewed row/group (nearest templates: `review_prompt_r-extreme-transport.md` for an R row, `review_prompt_prop-anchor-values.md` for a
comparison row, `review_prompt_lit-homfly-descent.md` for an interface). The FINAL_REVIEW table generator's patched copy is gone (§E-17).

### F-15 — Scratchpad ephemerality
Everything under `/workspace/scratch/claude-0/…/scratchpad/` (merge scripts, probe scripts, `#print axioms` scratch copies, the table
generator patch) belongs to one Claude session and is not recoverable afterwards. Anything worth keeping goes under `work/drafts/<lane>/`
(the W3C assembler did this; the corner assembler and the reviewers did not).

### F-16 — Numbering: claims.py "#" (184 units) ≠ map index (192 rows)
`cp:finite-contact-path` is 91 in claims.py, 95 in the map (index 94 zero-based); `src:contact` is m97. Notes, FR and this register use
claims.py numbers. Receipts are named by the executor (`dev-check-fdcontact-row162-implemented.json` covered the 94+162 port).

### F-17 — Reviewer input and source excerpts are frozen artefacts bound by hash
`write_review_and_accept.py` binds the sha256 of every file the reviewers read and requires the row's statement hash to be in
`work/checks/declaration-audit.json` (i.e. the checker ran after mapping). Never regenerate a `*-reviewer-input-statement.lean.txt` or a
`*-source-excerpt-*.tex.txt` of an accepted row (§E-03); create new files for new reviews.

### F-18 — `STATUS.md` and `AUTHOR_NOTES.md` conventions
AN is append-only, dated entries (`## <title> — YYYY-MM-DD HH:MMZ (pod executor)`), decisions carry ids (D-GAP2, D-SC-n, D-FL-n, D-CC-n,
D-CVT-n, D-CM-n, D-RM-n; fidelity readings FR-<lane>-n recorded BEFORE a statement is stated); STATUS.md gets a new header block per
checkpoint on TOP (hence the stack, §E-09). Never edit an old AN entry; correct with a new dated one (§E-13).

### F-19 — Discord and Mark
Nothing in tmux `side` is mirrored to Discord; use `echo "..." | discord-notify` only at milestones (an accepted target, a blocked decision,
a finished long run), never for routine progress; times in UTC and New York (`TZ=America/New_York date`). Never print a key (they are in
the environment via `/workspace/home/rc.sh`; `/workspace/envs/lean/env.sh` has no keys).

### F-20 — Index of 2026-09-15/16 decision and fidelity ids that this register otherwise reaches only as ranges (id → AN line → gist)
RESUME §1 item 4 points to the lane entries but not to the ids. The AN headings (`grep -n '^## ' work/AUTHOR_NOTES.md | awk -F: '$1>=5144'`)
list only D-RM-1..7; the other ids sit inline in the lane design entries. Gists are one-line paraphrases — the AN line is the record.
| id | AN | gist |
|---|---|---|
| D-GAP2-3 | L5163-5166 | row 91 := `cp_finite_contact_path_of_descent lit_homfly_descent` in `SM/ContactPath.lean`; statement = the reviewed `ContactPathData`; own 3+2 review, interface review of the axiom |
| D-GAP2-4 | L5167-5169 | `src:contact` designed by a panel (two architects + judge) and declared on the accepted vocabulary (fd rows 84-88, 93; `selfLinking` is the document's own fd:framed-linking, so the axiom has content); rows 94, 161/162 follow |
| D-FL-1 | L5224-5227 | floor statements: row 99 = `SM.CarrierFloorData` (four clause bundles R/A/B/C, `Round := CornerRounding.roundedWitness`, (B) on the normalised orientation); row 100 = `SM.FloorTheoremData`; row names declared/mapped only when row 94 lands |
| D-FL-2 | L5227-5229 | the row-94 interface is the sl-free composite `TransverseFrontBound : ∀ K X, K.Reads X → K.front.writhe ≤ -degAZ (P X) - 1` on `K.Reads X := Nonempty (HeightMarking …)` |
| D-SC-3 | L5311-5312 | D_T read by `HeightMarking` of `K.spatial` (row 91's endpoint reading); the gap2 memo's `SmoothKnotDiagram.Carries` dropped (never in work/lean) |
| D-SC-5 | L5314-5316 | module `SM/SrcContact.lean`, not FrontInterfaces; the CV bundles/theorems live in the ROOT namespace `CV`, not `SM.CV` (sketch corrected at port, statements unchanged) |
| D-CC-1 | L5402-5407 | the row statements 103 `CbSingletonData` / 105 `CornerValuesData` / 110 `CS7Data.vertex_edge_law` / 112 `CSoftData.soft_theorem`, field by field |
| D-CC-2 | L5407-5410 | the floor interface is the floor lane's FINAL shape verbatim (byte-identical copy of `floor/Statements_FINAL.lean` §7, checked 15:25Z; deleted when the floor module lands); only `a_floor`'s ℤ conjunct consumed |
| D-CC-3 | L5410-5411 | the C rows stay conditional (`_of_floor`) until `SM.thm_floor` is accepted; row theorems declared and mapped only then (D-F11/D-F14 pattern) |
| D-CVT-1 | L5483-5486 | row 155 = `CV.CarrierFloorData` on CV's printed binders, (R)(A)(B)(C) proved from the SM bundles through the polygon bridge, (D) proved; the row theorem declared only when all five clauses are theorems |
| D-CVT-3 | L5488-5490 | row 165 = `CV.SingletonDiData`, PROVED from this lane's geo-layer split `SingletonSplitData` + `CarrierSlotFloor` via `mindegAZ_mul` (row 103 is the TEMPLATE only, §E-12) |
| D-CM-4 | L5708-5710 | `cusp_deletion_generic` is the ONLY open leaf and mandatory — a `Generic (deletion)` hypothesis on `CuspLawC` would narrow TARGETS' cusp domain; fallback = "one lemma leaf open" (it was then proved, §A-13) |
| D-RM-2 | L5868 (heading), L5891-5893 | proceed with Wave 1 (the constructor `SM/BigonDeletion.lean`: U-M0 frozen, then M1 ∥ M2 ∥ M3 ∥ M6, M4 ∥ M5, M7) and Wave 2 (three j = 1 sites + two interface re-bases); Wave 3 = row 177 |
| D-RM-3 | L5930 (heading), L5939-5941 | the Cut interface is frozen; Wave 1 as seven parallel units on byte-identical copies with an assembler that splits the port (constructor → `SM/BigonDeletion.lean`; `G11_core_sw` → the Wave-3 draft) |
| D-RM-4 | L6007-6009 | the split port: `SM/BigonDeletion.lean` = the assembler's tested `Port_BigonDeletion_draft.lean` (5374 lines, no sorry), import `RProof.GenericTransport` kept (no cycle) |
| A-177-1 D1 | L6200 | the trans-free copy goes in NEW draft modules (later `RProof/GenericTransportSw*.lean`) |
| A-177-1 D3 | L6202-6203 | the nonzero sign is DERIVED from genericity — no hypothesis added to a frozen statement (D2 = ext-interface replay, §C-03; D4/D5 = realiser obligations) |
| D-F14 | L4412 (2026-09-14) | row 88 `fd:linking-calculus` proved modulo `RegularPoleCount`, NOT mapped — the conditional-not-mapped pattern; SUPERSEDED as a row decision by D-F16 at L4592 (row 88 restated unconditionally and mapped). The nine AN mentions of "D-F11/D-F14" (L4578, L4654, L4668, L5227, L5282, L5411, L5467, L5711, L5835) cite the PATTERN, not the superseded row decision |
| FR-CC-6/8/10/13 | L5435, L5441, L5448, L5459 | corner readings: 105 (ii) is literally 103's clause at (Q, y); `s = χ_{a,a+1,M}(P₋)` = `g.contactSign M a`; P₊/P₋ read at every pair of side parameters; C evaluated on labelled tuples, thm:comparison consumes it on the quotient |
| FR-CM-2/4 | L5720, L5734 | comparison readings: the soft hypothesis "in the form of thm:C-soft at every admissible soft insertion" with the two bounds; the A_g clause "every anchor root other than the soft edge" = `a ≠ A.softEdge` |
| FR-SC-5/7 | L5333, L5337 | contact readings: Legendrian clauses on `E3` with period 2π (rows 84/87's objects); front writhe of a transverse front = accepted row 92's over/sign rule |
| FR-FC-2/6/7 | L5352, L5360, L5362 | fd:contact readings: row 94's "individual smooth positive transverse knot whose xz projection is ordinary finite"; 162's "HOMFLY-PT of the knot it presents" = `homfly X`; rows 94/161/162 are theorems about the same fixed witness `sl` |
| FR-CP-4 | L4629 (2026-09-14; cited L5175) | = CE-R2: the printed H_s lives on [0,1], `SpatialFamily` is indexed by all of ℝ, constancy outside [0,1] not required (§D-01) |

---

## G. Decisions reserved for the author (the collaborator who speaks as the author, reached through Mark) — exact question and the recorded cost/benefit

### G-01 — Fund the remainder of row 110 `thm:C-S7`?
**Question.** Authorise 2-3 further corner waves (≈ 8-12k lines: S1' 500-700, S3 1,300-2,050, B1 2,300-3,600, B2 3,500-5,400, B3 400-700) to
close the five named Props, then the one-liners 127/128 and the assembly 184?
**For.** Every unit of four waves landed 0-error with a shrinking, named remainder; the G11 analogue (11k lines) was completed; nothing is
believed false in the row statement and no leaf restates the conclusion (AN L6093-6100); the remainder is enumerated with templates (rows
174/176's site + hrec units closed the same geometry in one wave each). Closing 110 alone raises targets 5/8 → 6/8 (`thm:C-S7`) and makes
127/128 one-liners; with §G-02 it completes 184 (8/8).
**Against.** The corner branch has consumed three waves + one bounded wave without acceptance (A-110-1's consequence: "no further corner
construction … a decision for the author, not the executor", AN L6316-6318); B2 is the lane's largest single item (3.5-5.4k) and its site
`hrec` (1.0-1.65k) is a Prop inside a Prop; at the observed rate (≈ 3.5 h per wave under load) this is a working day or more.
**If yes:** §A-02 resume, in the order of W3_ASSEMBLY_REPORT §7; record a new audit window in AN first (§F-06).

### G-02 — Fund the remainder of row 177 `R:extreme_selected` (then 178/183 are staged one-liners)?
**Question.** Authorise one more bounded window (≈ 1.0-1.9k lines per W3C §6; 1.3-2.5k per AN) for `w3cx_outer_residue_data` (route known,
0.7-1.3k) and `w3cs_not_kink_site_data` (0.3-0.6k, route OPEN), plus the two skeleton statement edits and the ≈ 7.8k mechanical port of the
trans-free copy (§C-04)?
**G-02b (part of the same question).** Is a NON-KINK HYPOTHESIS on the RIII event admissible for `w3cs_not_kink_site_data`? It is not in the
printed proof and would touch the accepted row shape / event vocabulary; the alternative is a derivation from the 177 configuration data
(`G11_mE`, `G11_pE` of `x_ef` not at cyclic distance 2 in `geoCornerPolygon`; SITE §4 routes (i)/(ii)), feasibility a CONJECTURE.
**For.** Three windows each landed 0-error and proved corrected forms; the remaining two leaves are the smallest the branch has had;
178 and 183 compile the moment `RProof.extreme_selected` exists (targets 5/8 → 6/8 by `Bridge:theorem`; with §G-01, 8/8).
**Against.** Two bounded windows + Wave 3c without acceptance (A-177-2's consequence applied, AN L6435-6438); one route open; an event
hypothesis would be a statement-level change to accepted vocabulary.
**If yes:** §A-15..A-18, then §A-19, §A-20; decide §G-03 first (it fixes the port shape).

### G-03 — `RProof.G11_Config.trans`: port the trans-free copy, or drop the field from the accepted module?
**Question.** (i) Edit `work/lean/RProof/GenericTransport.lean:125` to drop `trans : ¬ IsAlternating …` (statement-neutral for every accepted
row — no accepted proof uses it except the D8 table; ≈ 4k lines of Wave-3 work instead of ≈ 12.5-13k; but a rewrite inside an accepted module,
which the package forbids to the executor and which would need re-review of rows 166-173's statements only if their bundles mention
`G11_Config` — to be checked), or (ii) port the ADDITIVE copy `G11_ConfigSw` / `G11_ParamsSw` (≈ 7.8k mechanical lines, already proved in
`W3_A1_Assembled.lean`; the library then carries two near-identical namespaces), or (iii) leave both undone (only if §G-02 is "no").
Recorded AN L6189-6195 as "the author's option … not taken"; FR §5 item 7.

### G-04 — The false-as-stated fields of accepted `est_PortData` (D-RM-5/6) and the unrealisable `esc_MoveData.rii_after_smoothing` (F-177-2)
**Question.** Apply the site report's 5-line edit F-176-1 to `est_PortData.port` (`RALedgers.lean:878`) and add `wind(S) ≠ 0` to `rot`/`alt₁`/`alt₂`
(`:903-906`), and weaken `rii_after_smoothing` (`:1962-1967`) — three rewrites inside an accepted module — or keep the literal fields and the
weak replays (`s176_`, `r176l_`, `w3bi_esc_*`) with FR §5 item 6 / item 11 as the record?
**Cost/benefit.** The edits make the library honest to a reader and shrink 177's replay; they touch an accepted module whose sha256 is bound in
receipts (RALedgers.lean byte-unchanged since 18:08Z, FR §7) and would need a re-build + checker run + (if any accepted row's statement
unfolds them — the RA rows read `RowShape` bundles, not `est_PortData` — probably none) re-review. Keeping them costs nothing mathematically.

### G-05 — Comment-only edits inside ACCEPTED modules
**Question.** May the executor make comment/docstring-only edits in accepted modules (no declaration, statement or body changed), re-running the
checker afterwards? Items waiting: §E-01 (`ContactPathOfDescent.lean:54,173`), §E-02 (citation lines), §E-05, §E-06, §E-07, §E-08
(`CornerChainUnits.lean:3811-3815`, the `s7b_slidingMark` docstring), §E-11 (`LinkLaurentRing.lean:80-81`, `LinkInterfaces.lean` 55-60/180-181, `FlatCarriersDefs.lean:6`,
`Bridge/SmR.lean:1`, the 55 "sorry-free" headers). Precedent: the 22:40Z header fix in `ContactPathOfDescent.lean` was done by the executor as
"comment lines only" and confirmed by the closing checker; the 2026-09-14 practice allowed docstring-only edits of UNACCEPTED modules.
**Cost.** ~30 lines of comments, one checker run (receipts re-bind `project_sha256`). **Benefit.** No next agent re-discovers §C-05 or reads
"NOT an axiom" wrongly.

### G-06 — Confirm or revert the `verify_bundle.py` relaxation (D-GAP2-2b, §B-03)
**Question.** Is the label-part comparison at `verify_bundle.py:100` acceptable as the package's permanent data model (one label, possibly
several declarations), or should the author prescribe another registration of the second declaration (e.g. a separate policy section)?
Reverting alone breaks every row carrying `SM.lit_homfly_descent`.

### G-07 — Registry document: add a sub-entry for `SM.lit_homfly_descent` under "## lit:homfly — AXIOM" in the FROZEN `blueprint/AXIOM_REGISTRY.md`?
(§B-05.) Only the author can touch the blueprint; otherwise FR §4.3 stays the sole record and TARGETS.md:8's "five" is met only under the
D-GAP2 reading.

### G-08 — Keep the bundled descent axiom or switch to the literal form?
**Question.** Keep `axiom SM.lit_homfly_descent : AmbientIsotopyDescent` (bundles `IsotopyExtension`, FR-LHD-1), or replace it by `axiom :
AmbientIsotopyDescentLit` and PROVE `IsotopyExtension` (`ContactPathOfDescent.lean` 146-178 already has `AmbientIsotopy`,
`AmbientIsotopyDescentLit`, `IsotopyExtension`, `ambientIsotopyDescent_of_lit`)? **Cost.** The 2026-09-14 estimate for route (α') was ~3-5k
lines of analysis (`work/drafts/gap2/CPRow91_PLAN.md` §7); every row carrying the axiom would then need its footprint re-recorded (statements
unchanged). **Benefit.** The axiom would be exactly the registry sentence.

### G-09 — Row 57 `lem:gauss-two-discs`: stays deferred (12-20k lines; no accepted row depends on it)? (§A-01.)

### G-10 — Human review of the AI-only verdicts
**Question.** Does the author want a human spot-check (start with FR §4-§5 and, per row, `work/reviews/<slug>.json` `reason` + `discrepancies`,
the excerpt file and the reviewer-input statement file), or a strict-protocol re-run for the rows with disclosed reading deviations (§D-22,
D-52, D-66, D-72, D-73..D-75)? No human has read any review.

### G-11 — `src:contact` field 3 in a single-representative form? (FR-SC-3, §B-02.) Would need a definition of T₊(L) the document lacks; optional.

### G-12 — Confirm or soften the Etnyre §2.2 (3) attribution in `SM/SrcContact.lean:152` (§D-20). Optional; comment-only (§G-05).

### G-13 — Add the library lemma "a transverse front / regular generic projection has a polygonal `HeightMarking` reading" (§C-13)? Optional;
size not estimated; no accepted row needs it.

### G-14 — Salvage the literal clause (B) of rows 99/155 for all-negative L by proving `Round(−L,−D,ε) = reverse (Round(L,D,ε))` (§D-32)? Optional; no
consumer reads (B).

### G-15 — Archive / prune: build the missing 2026-09-15/16 tarball now (executor can, §F-08 — no decision needed); prune Route R of row 174
(§E-26) or keep both routes? Optional.

---

## Index by decision owner
- **author:** A-01, A-02 (window), A-12/C-05 docstring, A-15 (window), A-17, B-03, B-05, C-01, C-02, C-03, C-04, C-13, E-01, E-02, E-08, E-11,
  E-16, G-01..G-14.
- **executor (inside the package rules; some only after an authorised window):** A-03..A-11, A-13, A-14, A-16, A-18..A-22, B-04, C-06, C-07, C-09,
  E-04, E-05, E-06, E-07, E-09, E-10, E-13, E-14, E-15, E-17, E-18, E-20, E-21, E-23, E-26, F-08 (build the tarball).
- **none (disclosure / record only):** A-04, B-01, B-02, B-06, C-08, C-10, C-11, C-12, C-14, C-15, every D row, E-03, E-12, E-19, E-22,
  E-24, E-25, E-27, E-28, F-01..F-07, F-09..F-20.

## Critic items rejected (repair pass 02:24Z UTC 2026-09-16 / 10:24pm ET (2026-09-15))
None of the 35 critic findings was rejected: every one checked out against its cited source and was applied above. Five were applied with
CORRECTED locators because the critic's own pointer was off: (i) the `'=3'` housekeeping line is AN L5180 (the critic said L5177-5178; the
instruction itself is L5155-5156); (ii) FR §7's stale sentences are at FR L1155-1157, L1190-1194, L1241, L1274-1276 (plus L107 in §0 and
L871 in §4), not at "L158-162 / L194-198 / L245 / L278-280", which are §0 text and §2 table rows; (iii) D-CC-1 starts at AN L5402 and
D-CC-2 at L5407 (the critic said L5405-5410 / L5410); (iv) FR-CP-4 is DEFINED in a 2026-09-14 entry (AN L4629) and only cited at L5175,
and "D-F11/D-F14" has nine AN mentions, not six; (v) RESUME §1 item 3 never contained the "Wave 3c … 02:15Z" sentence — it wrongly said
"fourth/fifth bullets", now "fifth bullet only". One critic phrasing was tightened rather than adopted: the `-- (W3C assembler)` comments
at 9253/9283/13113/13135 do not contain the word `sorry` (no W3C comment does — `grep -c sorry` = 6), so they are recorded as naming the
restatements, not as prose mentions to reword. Sources re-read for this pass: the two drafts and their reports, `W3C_AXIOMS.log`,
`assemble_W3C*.py`, `check_W3_statements.py`, AN L4412-6479 (selected), FR (selected lines), STATUS L1-12, the seven review JSONs named
in §D-73..79, `lean-declarations.json`, the live modules named in each item, `ls` of the archive directory and `pgrep`.

*End of register. Item count and category counts are in the synthesizer's JSON return; the counts can be re-derived with*
`grep -c '^### [A-G]-[0-9]' OPEN_ITEMS_20260916.md` *and* `grep -c '^| D-[0-9]' OPEN_ITEMS_20260916.md`.
