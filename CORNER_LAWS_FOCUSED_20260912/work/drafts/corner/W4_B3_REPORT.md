# W4_B3_REPORT — wave 4, unit B3 (prefix `s7o_`; closing K's box `s7z_oneNewborn_exists` = Prop B3 `w3_BigonOneNewborn`), 2026-09-19 06:45 UTC / 2:45am ET (under D-AUTH-20260919)

File: `work/drafts/corner/W4_B3.lean` (9807 lines, sha256 `51213ea3436deb76543945ac6afed834bcd1438d17e61de135bcb6e122b867a5`) =
`W3_Assembled.lean` (8958 lines, sha256 `109050d918ecd537…`) + ONE inserted block + ONE replaced body.
`diff W3_Assembled.lean W4_B3.lean` = `8636a8637,9485` (849 lines inserted immediately BEFORE the docstring of
`s7z_oneNewborn_exists`, inside `section S7ZBigon` after K's §E boxes `s7z_F_exists` / `s7z_returned_of_FSector`) and
`8642c9491` (the single line `  sorry` → `  exact s7o_oneNewborn_exists hsing hn h`).  Nothing else changed: the deleted side of the
diff is exactly `  sorry`; the five frozen declarations and every existing statement/name/docstring are byte-identical (the last 43
lines are byte-identical to `W3_Skeleton.lean` 55-97; the ±12-line contexts of `s7_sliding_law_at` 4844, `s7_bigon_law_at` 8906→9755,
`thm_C_S7_of` 8924→9773, `thm_C_S7_of_floor` 8949→9798, `thm_C_S7` 8954→9803 are identical); every existing line after 8636 moved by
+849.  **45 declarations**, all `theorem`, all `s7o_`-prefixed (no `def`, no structure, no instance); no import, no `open`, no new
`variable` outside the block's own nested sections (`S7OOneNewborn` ⊃ `S7OSide`, `S7OSigns`, `S7OTerms`, `S7OWall`).

Check (official): `cd work/lean && lake env lean ../drafts/corner/W4_B3.lean` — **0 errors, exit 0, 36 s** (load ≈ 8 lean
processes of the sibling units); **exactly 11 `declaration uses sorry`** (was 12): lines 4437 `s7q_box_ret`, 4519 `s7q_box_carriers`,
4844 `s7_sliding_law_at`, 5371 `s7f_exists_bigonSplit`, 5388 `s7f_exists_twoNewbornTerm`, 5725 `s7f_exists_ineligible_transport`, 6972
`s7s_clear_local`, 7018 `s7s_wallTriangleData_of_bigon`, 8600 `s7z_F_exists`, 8620 `s7z_returned_of_FSector`, 9755 `s7_bigon_law_at`;
**0 other warnings**.  `grep -c sorry`: 20 → **19** (the closed body; no new prose mention).
`python3 work/drafts/corner/tools/stmt_check.py work/drafts/corner/W4_B3.lean`: **4/49, the same four rows as on `W3_Assembled.lean`
and on the skeleton itself** (`s7_sliding_law_at`, `s7_bigon_law_at`, `thm_C_S7_of`, `thm_C_S7_of_floor` byte-identical and unique;
`thm_C_S7`'s row is the checker's known mismatch, W3_K_REPORT header) — unchanged by this unit.
Clash scan: `grep -rcE "\bs7o_" work/lean/SM/` → 0 hits; `grep -lE "\bs7o_" work/drafts/corner/*.lean` → only `W4_B3.lean`; no duplicate
top-level name in the file (`sort | uniq -d` empty).
Axioms (`#print axioms` on a scratch copy of the FULL file, `lake env lean` from `work/lean`):
`s7o_oneNewborn_exists`, **`s7z_oneNewborn_exists`**, **`w3_BigonOneNewborn_of_box`**, `w3_s7_bigon_law_at_of`,
`s7o_oneNewborn_side`, `s7o_term_insert_x/_y` = `[propext, Classical.choice, Quot.sound, SM.lit_homfly]` (the literature axiom enters
through `cornerCoefficient`, as for the whole corner chain); the pure geometry/combinatorics (`s7o_interlaces_iff`,
`s7o_interlaces_x_iff_y`, `s7o_turn_M_of_lt`, `s7o_nextMark_xl`, `s7o_sideData`) = `[propext, Classical.choice, Quot.sound]`;
`s7z_exists_rowSector` and `s7_bigon_law_at` still carry `sorryAx` — now through `s7z_F_exists` and `s7z_returned_of_FSector` ONLY;
`thm_C_S7` = the registered set + `sorryAx` (unchanged list).  **No `sorryAx` anywhere in the `s7o_` block.**

**Box closed: YES — `s7z_oneNewborn_exists` is proved, sorry-free; Prop B3 `w3_BigonOneNewborn hn h` is now delivered by
`w3_BigonOneNewborn_of_box hsing hn h` without `sorryAx`.**  Nothing believed false; no frozen statement needs a change; no new
black box (rule (3) unused).  Reassessment rule: NOT triggered (no lemma needed a second method; one design change before the first
attempt, §3).

## 0. What the block renders (sm-4:693-706 and 777-783), in one paragraph

On the newborn side `Q = P₂(t)` — a generic side polygon carrying BOTH contact crossings `x = {a, M−1}` and `y = {a, M}`
(`s7p_x false _`, `s7p_x true _`; definitionally K's `s7z_x hn h t`, `s7z_y hn h t`) — SPLIT's side data `hd : s7p_SideData M a
g.center Q r η` (`ContactParameterWindows`, `ContactOrderAgrees`, the κ-coordinate `s7p_kappa v = (edge v − M).val + param v`)
turn the bigon word eq. s7c:bigon-words-eq into three MARK-ADJACENCY facts: `nextMark x_ℓ = μ_M` (the leg visit of `x` is the last
mark of `E_{M−1}`: parameter `> 1 − η`, persistent visits `< 1 − 3η`), `nextMark μ_M = y_ℓ` (first mark of `E_M`), and on `E_a` the
earlier newborn `a`-visit is followed by the other (both within `η` of `r`, persistent `a`-visits `> 3η` away).  `ε = 1` iff `x_a`
comes first (`s7o_interlaces_iff`: the chords interlace iff `y_a` is outside the arc from `x_ℓ` (κ ≈ n⁻) to `x_a`), and an old label
interlaces `x` iff it interlaces `y` (`s7o_interlaces_x_iff_y`: one visit at `κ < D + r`, the other at `κ > D + r`, the same condition
for both newborns — the common old neighbourhood `N` of sm-4:414-415).  Hence for an eligible newborn-free `T` (`s7z_Eligible`: a
decomposition, no selected crossing interlacing both newborns): no selected crossing interlaces either newborn
(`s7o_free_of_elig`), `T ∪ {x}`, `T ∪ {y}` are decompositions (`s7o_insert_decomposition`, sm-4:777 "`T ∪ {x}` is a support since `x` is
adjacent to neither `T` nor `y`"), and by the smoothing successor (`smoothingSuccessor = selectedMarkPerm ≫ markSuccessor`) the marks
`x_a` (selected) → `μ_M` → `y_ℓ` → (`ε = 0`: `y_a` → `x_a`) lie on ONE carrier `q = owner μ_M` of `T ∪ {x}`, and symmetrically for
`T ∪ {y}`.  **`ε = 1`** (sm-4:693-706): `q` has the vertex corner `M` with `turn Q M = −σ` (`s7o_turn_M_of_lt`, `σ := χ_{a,a+1,M}(Q)`)
and the smoothing corner at the selected newborn with turn `σ` (`s7o_crossingSign_x : crossingSign Q a (M−1) = σ`, `s7o_crossingSign_y :
crossingSign Q M a = σ` — eq. s7c:one-newborn-turns' three determinants without coordinates: both legs cross `E_a`, `crossing_test`),
so `q` is mixed and `wind = 0` (`turn_ccpCornerPolygon_eq_markTurn`, `ccpCornerMark_exists`, `s7c_carrierWeight_eq_zero_of_ne`).
**`ε = 0`** (sm-4:777-783): the unselected newborn is a self-crossing of `q` (both its visits owned by `q`), every old neighbour of it
interlaces the selected newborn (`N` common), and cb:singleton closes the term through unit J's
`s7j_one_newborn_term_zero_insert` (which does the selector split itself).  The wall level instantiates `hd` at `P₂(t)` below the
radius of `s7a2_exists_intervalLocal` (`s7o_sideData`, FB1's restatement of SPLIT's `s7p_sideData` on `VertexEdgeAt`) and reads
`s7z_OneNewbornRows` off `s7o_oneNewborn_side`.

| printed (sm-4) | block lemmas | status |
|---|---|---|
| 409-411 the word `x₀y₀ A … B`: `x_ℓ`, `μ_M`, `y_ℓ` consecutive | §A `s7o_nextMark_xl`, `s7o_nextMark_M` (via `s7e_nextMark_inr_eq_inl` / `_inl_eq_inr`, the windows `s7e_vl_param_false/_true`, `s7e_persist_M_sub_one/_M`) | PROVED |
| 411 the a-side letters `y₁x₁` / `x₁y₁` | §A `s7o_nextMark_va`, `s7o_nextMark_xa`, `s7o_nextMark_ya`, `s7o_param_ne` | PROVED |
| 409 `ε` | §A `s7o_interlaces_iff` (`ε = 1 ↔ param x_a < param y_a`, by `s7p_interlaces_iff` on κ) | PROVED |
| 414-415 `N` the common old neighbourhood | §A `s7o_interlaces_contact_iff`, **`s7o_interlaces_x_iff_y`** | PROVED |
| 693-706 eq. s7c:one-newborn-turns (`hv − uk > 0`, `−h < 0`, `−k < 0`) | §B `s7o_chi_legs`, `s7o_crossingSign_x`, `s7o_crossingSign_y`, **`s7o_turn_M_of_lt`** | PROVED (coordinate-free) |
| 703-706 "the opposite turns lie on the same daughter carrier and make it mixed" | §C `s7o_owner_xa_M_of_mem`, `s7o_owner_M_yl`, the `ε = 1` branches of `s7o_term_insert_x/_y` | PROVED |
| 777 "`T ∪ {x}` is a support" | §C `s7o_free_of_elig`, `s7o_insert_decomposition` | PROVED |
| 777-783 "`{y}` is an isolated block … cb:singleton" | §C the `ε = 0` branches (owners `s7o_owner_xl_M_of_not_mem`, `s7o_owner_eq_of_succ`; J's `s7j_one_newborn_term_zero_insert`) | PROVED |
| "the statement with `x, y` exchanged is identical" | §C `s7o_term_insert_y`, **`s7o_oneNewborn_side`** | PROVED |
| the box below a radius | §D `s7o_side_of_r`, `s7o_sideData`, **`s7o_oneNewborn_exists`**; body of `s7z_oneNewborn_exists` | **CLOSED** |

## 1. Proved (45 theorems; all `s7o_`, inside `section S7ZBigon`'s `variable {g : WallGerm n} {M a : ZMod n}`)

§A `section S7OSide` (`variable (hn) {P Q} {r η} (hd : s7p_SideData M a P Q r η) (hcx : IsCrossing Q {a, contactLeg false M})
(hcy : IsCrossing Q {a, contactLeg true M})`): `s7o_leg_ne`, `s7o_persistent_of_ne`, `s7o_visit_persistent`, `s7o_visit_cases`,
`s7o_nextMark_xl`, `s7o_nextMark_M`, `s7o_nextMark_va`, `s7o_a_visit_cases`, `s7o_nextMark_xa`, `s7o_nextMark_ya`, `s7o_param_ne`,
`s7o_bounds`, `s7o_kappa_va`, `s7o_kappa_xl_bounds`, `s7o_kappa_yl_bounds`, `s7o_kappa_persistent`, `s7o_before_of_lt`,
`s7o_after_of_gt`, `s7o_va_eq`, `s7o_interlaces_iff`, `s7o_interlaces_contact_iff`, `s7o_interlaces_x_iff_y`;
§B `section S7OSigns` (`variable (hn) {Q} (hQ : Generic Q) (hsep) (hcx) (hcy)`): `s7o_det_sub_right`, `s7o_det_smul_right`,
`s7o_det_smul_left`, `s7o_det_self`, `s7o_sign_of_mul_neg_one`, `s7o_sign_cases`, `s7o_chi_legs`, `s7o_crossingSign_x`,
`s7o_crossingSign_y`, `s7o_turn_M_of_lt`;
§C `section S7OTerms` (same variables as §A): `s7o_x_ne_y`, `s7o_free_of_elig`, `s7o_insert_decomposition`, `s7o_owner_eq_of_succ`,
`s7o_owner_M_yl`, `s7o_owner_xa_M_of_mem`, `s7o_owner_xl_M_of_not_mem`, **`s7o_term_insert_x`**, **`s7o_term_insert_y`**,
**`s7o_oneNewborn_side`**;
§D `section S7OWall` (`variable (hn) (h : g.BigonAt M a) {r η δ} (hloc : s7a2_IntervalLocal hn g M a r η δ) (t) (ht)`):
`s7o_side_of_r`, `s7o_sideData`; then **`s7o_oneNewborn_exists`** (the box statement verbatim).

Inputs used (all PROVED / accepted; no sibling sorry on the path).  From the same file: SPLIT's `s7p_SideData`, `s7p_x`,
`s7p_x_affected`, `s7p_x_visits`, `s7p_xl_eq`, `s7p_kappa`, `s7p_kappa_eq`, `s7p_cyc`,
`s7p_interlaces_iff`, `s7p_D_bounds`, `s7p_n5`, `s7p_kappa_persistent_bounds`, `s7p_kappa_va_bounds`, `s7p_kappa_vl_false/_true`;
F's `s7f_hQC`; J's `s7j_one_newborn_term_zero_insert`; K's `s7z_pattern`, `s7z_OneNewbornRows`, `s7z_Eligible`.  From
`SM.CS7Sliding`: `s7e_va/vl` + `_edge`, `_fst_val`, `_fst`, `s7e_twin_va/vl`, `s7e_visit_of_fst`, `s7e_a_ne_leg`, `s7e_visit_eq_of_param`,
`s7e_nextMark_inr_eq_inl/_inl_eq_inr/_inr_eq_inr`, `s7e_persist_a/_M/_M_sub_one`, `s7e_va_param_near`, `s7e_vl_param_false/_true`,
`s7e_term_of_decomposition`, `s7e_hw`, `s7e_hL`, `s7a2_IntervalLocal`, `s7a2_exists_intervalLocal`, `s7a2_crossing_iff`,
`s7a2_continuousAt_edgeParameter`, `s7a2_pos_of_ne_zero`.  From `SM.CornerChainUnits`: `s7a_sideGeneric`, `s7i_signType_cases`,
`s7c_carrierWeight_eq_zero_of_ne`, `s7c_sign_ne_neg_self`.  Accepted library: `contactSeparated_size`, `contact_pairs_distinct`,
`contactLeg_remote`, `crossing_test`, `crossingParameter_spec`, `crossingParameter_interior`, `chi_edge`, `turn_det`, `det_swap`,
`visitPosition_interior`, `mem_independentSupports_iff`, `interlaces_symm`, `smoothingSuccessor_vertex/_visit_of_mem/_visit_of_not_mem`,
`markSuccessor_apply`, `owner_successor`, `mem_carrierCrossings`, `ccpCornerMark_exists`, `turn_ccpCornerPolygon_eq_markTurn`,
`markTurn_inl/_inr`, `WallGerm.sideTime_val_abs`, `VertexLocalData.windows`; Mathlib `sign_pos/neg`, `sign_eq_one_iff/_neg_one_iff`,
`Left.sign_neg`, `lt_abs`, `abs_lt`, `ZMod.val_lt`, `ZMod.val_injective`, `ZMod.one_eq_zero_iff`, `Finset.prod_eq_zero`.

## 2. Unproved / black boxes

None.  This unit consumes no sorried declaration (rule (3) unused) and adds none.  Off this unit's path, the bigon leaf still waits on
B1 (`s7z_F_exists` — or F's route through `s7f_exists_twoNewbornTerm` / `s7f_exists_ineligible_transport`, since FB1 closed
`s7f_exists_bigonSplit`) and B2 (`s7z_returned_of_FSector`); the sliding leaf on S1'/S3.

## 3. Method audit (reassessment discipline, D-AUTH-20260919 §2)

No lemma failed twice; the audit trigger was not reached (five compile rounds on the whole block, each error a Lean idiom: section
`include`, `rw … at c1 c2` over hypotheses lacking the pattern, an `omit` of a referenced instance, C's pitfall 6 on `{i j}`, and a
`subst` re-introducing a shadowed name — §5).  ONE method decision before the first attempt, recorded here because the plan said
"on F's split vocabulary": the fields of `s7f_BigonSplit` (`x_free`, `y_free`, `x_split`, `y_split`) do NOT contain the fact B3 needs —
that the newborns' old neighbourhoods COINCIDE (`x_split`/`y_split` say an old label interlacing neither newborn is a half image;
`x_free`/`y_free` say half images interlace neither; together they give `z ∉ images ↔ (z ~ x ∨ z ~ y)`, never `z ~ x → z ~ y`) — nor the
mark-adjacency facts the owner computation needs.  So the block is built on SPLIT's κ-coordinate side data `s7p_SideData` instead (the
same data FB1 used to close F's box 1), where both facts are `linarith` over the window bounds.  Consequence: B3 is independent of F's
boxes 1-3 and of the `s7f_BigonSplit` structure.

## 4. Defects / observations (nothing false; nothing narrowed)

* The printed proof's "Both one-newborn sectors vanish by their selectors" (`ε = 1`) and the cb:singleton argument (`ε = 0`) are
  rendered exactly; in Lean both branches are needed: for `ε = 1` the unselected newborn is a MIXED crossing of `T ∪ {x}` (its two
  visits lie on different carriers: `y₀ → A → x₁ → y₀` vs `y₁ → B → x₀ → y₁`), so cb:singleton cannot apply and the selector argument
  is the only route; for `ε = 0` the carrier through `μ_M` may be uniform, so the selector argument cannot apply.  `hsing` enters only
  in the `ε = 0` branch (through J's entry).
* `s7o_turn_M_of_lt` proves the paper's "Interlacing means `hv − uk > 0`" (sm-4:695) coordinate-free: `(1−p') q' · det(d_{M−1}, d_M) =
  −(q − p) · det(d_a, μ_M − μ_a)` with `p < q` the two `a`-parameters and `p', q'` the leg parameters of the crossing points.  Only the
  direction `ε = 1 ⇒ turn Q M = −σ` is stated (the converse holds by the same identity but is not needed).
* Duplication with unit FB1 (`W4_FB1.lean`, same wave): `s7o_side_of_r` / `s7o_sideData` are textually FB1's `s7fa_side_of_r` /
  `s7fa_sideData` (SPLIT's `s7p_side_of_r` / `s7p_sideData` restated on `h.1 : g.VertexEdgeAt M a`) under this unit's prefix, because
  each wave-4 unit works on its own copy of `W3_Assembled.lean`.  The assembler may keep one copy and rename (no other dependency on the
  names; both are `theorem`s of identical statements).
* `s7o_persistent_of_ne` duplicates FB1's `s7fa_not_affected_of_ne` (three lines) for the same reason.
* K's docstring of `s7z_OneNewbornRows` cites "`s7k_one_newborn_term_zero`"; the J theorem actually used is
  `s7j_one_newborn_term_zero_insert` (prose only; frozen docstrings untouched here).

## 5. Mathlib / Lean pitfalls met (v4.34.0-rc2 pin)

1. Section variables used only in a proof body are not included: `include hn hd hcy in` was needed for `s7o_nextMark_xl` (its
   statement mentions `hcx` only, its proof `hcy` through `s7o_visit_cases`); `omit [NeZero n] in` fails on any statement mentioning
   `s7p_kappa` / `nextMark` ("cannot omit referenced section variable").
2. `rw [e0, e1, f0, f1] at c1 c2` fails when one hypothesis lacks one pattern; rewrite the two cyclic conditions separately
   (`rw [e0, f0, e1] at c1 <;> rw [e1, f1, e0] at c2`).
3. C's pitfall 6 again: `s7c_carrierWeight_eq_zero_of_ne … (by rw [hti, htj]; …)` unifies both implicit corners `{i j}` with the same
   one; state `turn … i ≠ turn … j` in a `have` first.
4. `rcases Finset.mem_insert.mp hu with rfl | hu <;> rcases … with rfl | hv`: the second `subst` reverts and re-introduces the OLD `hu`
   (which depends on the substituted variable) AFTER the new one, so `hu` again names `u ∈ insert w T`.  Use named equations and `rw`.
5. A `have` type `owner hn hd.hQ _ (Sum.inr v) = owner hn hd.hQ _ (Sum.inl M)` cannot infer the support `_`; write it out.
6. `le_or_lt` / `lt_or_le` do not exist in this Mathlib; `le_or_gt` does.  `- -1 = 1` in `SignType` closes by `decide`.
7. In a `by`-block with `set p' := …`, a `show` mentioning `M - 1` fails against a target still spelled `contactLeg false M`; rewrite with
   `hleg : contactLeg false M = M - 1 := rfl` first (the two are definitionally equal, `rfl`-checked in scratch, but `rw`/`show` match
   syntactically).
8. Fast iteration: `W3_Assembled.lean` compiled ONCE to an olean (`lean --root=<dir> -o W3Base.olean`, 25 s) and imported by the
   scratch files via an extended `LEAN_PATH` under `lake env` (12-18 s per round instead of 36 s).

## 6. Notes for the assembler

* Position: the block starts at line 8637 `/-! ### Wave 4, unit B3 (prefix `s7o_` …` and ends at line 9484 `end S7OOneNewborn` (line 9485 blank), inside
  `section S7ZBigon` (K's `variable {g : WallGerm n} {M a : ZMod n}`), immediately before the docstring of `s7z_oneNewborn_exists`
  (now line 9486; `theorem` at 9488, body line 9491 `exact s7o_oneNewborn_exists hsing hn h`).  The block references SPLIT (`s7p_*`), F (`s7f_hQC`), J
  (`s7j_one_newborn_term_zero_insert`) and K (`s7z_pattern`, `s7z_OneNewbornRows`) — all earlier in the file — so its anchor must stay
  after J and after K's §B/§C definitions; it references no `w3_` glue.
* Consumption: nothing else to do for B3.  `w3_BigonOneNewborn_of_box hsing hn h : w3_BigonOneNewborn hn h` is now sorry-free, so the
  leaf body, once B1 and B2 exist, is `w3_s7_bigon_law_at_of hn h h₁ h₂ B1 (B2 hF) (w3_BigonOneNewborn_of_box hsing hn h)` (or, on K's
  F-aligned route, `hone` per eligible `T₀` is `s7o_oneNewborn_side` at `hd := s7o_sideData …`, `T := s7f_lift … T₀`, with
  `s7f_x_not_mem_lift` / `s7f_y_not_mem_lift` and the eligibility identification of W3_K_REPORT §4(c)).
* Merging with FB1: `s7o_side_of_r` / `s7o_sideData` / `s7o_persistent_of_ne` duplicate `s7fa_side_of_r` / `s7fa_sideData` /
  `s7fa_not_affected_of_ne` (identical statements, different prefixes); keep either.
* Diff summary: `+` 849 lines, `−` 1 line (the box's `sorry`), `~` 0.  Reproduce: `cp W3_Assembled.lean W4_B3.lean`, insert the block
  before line 8637, replace line 8642, `cd work/lean && lake env lean ../drafts/corner/W4_B3.lean`.  Timeline: 06:09 UTC reading done,
  06:16 first scratch compile, 06:37 whole block compiles in scratch, 06:39 `W4_B3.lean` compiles (11 sorries), 06:45 report.
