# W4_FB1_REPORT — wave 4, unit FB1 (prefix `s7fa_`, closing F box 1 `s7f_exists_bigonSplit`), 2026-09-19 05:55 UTC / 1:55am ET

File: `work/drafts/corner/W4_FB1.lean` (9293 lines, sha256 `3c47c9bb7bbdbab5845d…`) = `W3_Assembled.lean` (8958 lines, sha256
`109050d918ecd5371c8a…`) + ONE inserted block + ONE replaced body.  `diff W3_Assembled.lean W4_FB1.lean` = `5362a5363,5697`
(335 lines inserted immediately BEFORE the docstring of `s7f_exists_bigonSplit`, inside `section S7FSectorSplit` after its
`variable` line) and `5379c5714` (the single line `  sorry` → `  exact s7fa_exists_bigonSplit hn g h h₁ h₂`).  Nothing else
changed: the five frozen declarations and every existing statement/name/docstring are byte-identical (the deleted-line side
of the diff is exactly `  sorry`); every existing line after 5362 moved by +335.  **6 declarations**, all `theorem`, all
`s7fa_`-prefixed; no import, no `open`, no new `variable` outside two nested sections.
Check (official): `cd work/lean && lake env lean ../drafts/corner/W4_FB1.lean` — **0 errors, exit 0, 40 s** (idle pod);
**exactly 11 `declaration uses sorry`** (was 12): lines 4437 `s7q_box_ret`, 4519 `s7q_box_carriers`, 4844 `s7_sliding_law_at`,
5723 `s7f_exists_twoNewbornTerm`, 6060 `s7f_exists_ineligible_transport`, 7307 `s7s_clear_local`, 7353
`s7s_wallTriangleData_of_bigon`, 8935 `s7z_F_exists`, 8955 `s7z_returned_of_FSector`, 8974 `s7z_oneNewborn_exists`, 9241
`s7_bigon_law_at`; **0 other warnings**.  `grep -c sorry`: 20 → **19** (= 11 declaration bodies + the same 8 prose mentions as
before, now at lines 6, 3431, 4723, 4757, 4761, 4888, 8930, 9198).
`python3 tools/stmt_check.py W4_FB1.lean`: **4/49, PASS lines identical to `W3_Assembled.lean`'s** (the draft carries only the
four row-110 declarations of the 49 frozen ones; `thm_C_S7`'s base text differs in both files exactly as before — pre-existing).
Clash scan: `grep -rln s7fa_ work/lean/{SM,CV,Bridge}` empty.
Axioms (`#print axioms` on a scratch copy of the whole file, `W4_FB1_axioms.lean`):
**`s7f_exists_bigonSplit` (the closed box) = `[propext, Classical.choice, Quot.sound]`** — no `sorryAx`, not even a registered
axiom; the same for all six `s7fa_` theorems.  Consumers unchanged in kind: `s7f_sector_split`, `s7f_exists_law_residual` =
`[propext, sorryAx, Classical.choice, Quot.sound, lit_homfly]` (the `sorryAx` now enters ONLY through boxes 2 and 3);
`thm_C_S7` = `[propext, sorryAx, Classical.choice, Quot.sound, lit_homfly, lit_homfly_descent, lp_lm, lp_lm_uniqueness,
ng_finite_word, src_contact]`.
Black boxes consumed: **none**.  New `s7fa_` Props with `sorry`: **none**.  Nothing believed false.

## 0. What was closed, in one paragraph

**BLACK BOX 1 of unit F (OPEN_ITEMS_20260916 §A-07) is PROVED**: below the radius of `s7a2_exists_intervalLocal`, the interlacement
relation of the newborn side `P₂(t) = g.curve (g.sideTime (s7f_side g M a) t)` splits along the two half crossing maps with the
two newborns `x = {a, M−1}`, `y = {a, M}` as in `s7f_BigonSplit` — all ten geometric hypotheses of `s7f_bigonSplit_of` (`rel₁ rel₂
cross cross' x_free₁ x_free₂ y_free₁ y_free₂ x_split y_split`).  The method is SPLIT's κ-coordinate transfer (W3_SPLIT_REPORT §0)
applied to `P₂` instead of a sliding side: `s7p_rel_first/_second`, `s7p_cross/_cross'` and `s7p_x_free_first/_second` take only
`hd : s7p_SideData` and a contact crossing `{a, contactLeg f M}`, so they apply verbatim at BOTH legs (`x = s7p_x false _`,
`y = s7p_x true _` **definitionally**, since `contactLeg false M = M − 1` and `contactLeg true M = M` reduce by `rfl`); the ONLY
sliding-specific input in SPLIT was `huniq` ("the affected crossing is unique"), used in `s7p_x_split` solely to conclude that a
crossing `z ≠ x` is persistent — on the bigon side that is `z ≠ x → z ≠ y → ¬ ContactAffected M a z.val` (`ContactAffected`
IS `s = {a, M−1} ∨ s = {a, M}`), so `s7p_x_split`'s argument is restated with the persistence hypothesis in its place
(`s7fa_x_split_of_persistent`, the body of `s7p_x_split` minus its first line).  The side data `s7p_SideData` for `P₂(t)` is
`s7p_sideData` restated on `g.VertexEdgeAt M a` (SPLIT stated it for `SlidingAt` but consumed only `h.1`); the bigon side
carries both parameter windows because `ContactParameterWindows`' third clause quantifies over both legs, and the persistent
agreement is `s7f_hQC`.  The radius theorem `s7fa_exists_bigonSplit` has the frozen statement verbatim and the frozen
declaration's body is now `exact s7fa_exists_bigonSplit hn g h h₁ h₂`.

## 1. Proved (all `s7fa_`; `{n} [NeZero n]` and `hn g {M a} h h₁ h₂` from the enclosing sections)

### 1.A On one side polygon `Q` with `hd : s7p_SideData M a P Q r η` (section `S7FASplitSide`, lines 5383-5600)
| declaration | content |
|---|---|
| **`s7fa_x_split_of_persistent hn hd f hc y hy hyx hxy`** | `y` persistent, `y ≠ s7p_x f hc`, `¬ Interlaces (s7p_x f hc) y` ⇒ `y ∈ range ι₁ ∪ range ι₂` (SPLIT's `s7p_x_split` with `hy : ¬ ContactAffected M a y.val` in place of `huniq`; both visit orders and both legs, `κ(v_ℓ)` extremal, `s7p_mem_range_first/_second`) |
| `s7fa_not_affected_of_ne hcx hcy z hzx hzy` | a crossing distinct from both `s7p_x false hcx` and `s7p_x true hcy` is persistent (`ContactAffected` unfolded; definitional `contactLeg`) |
| **`s7fa_bigonSplit_side hn hd hcx hcy hg₁ hg₂`** | `s7f_BigonSplit (Interlaces hn hd.hQ) (Interlaces hn₁ hg₁) (Interlaces hn₂ hg₂) ι₁ ι₂ (s7p_x false hcx) (s7p_x true hcy)` — `split` from U110-B's `inj₁ inj₂ disjoint` + `s7p_rel_first/_second`, `s7p_cross/_cross'`; `x_not/y_not` from `s7b_*CrossingQ_not_affected` + `s7p_x_affected`; `x_free/y_free` from `s7p_x_free_first/_second` at `f = false` / `f = true` with `interlaces_symm`; `x_split/y_split` from `s7fa_x_split_of_persistent` at each leg |

### 1.B At a vertex–edge wall (section `S7FASplitWall`, lines 5602-5677; `hloc : s7a2_IntervalLocal hn g M a r η δ`, `t`, `ht : t.val < δ`)
| declaration | content |
|---|---|
| **`s7fa_side_of_r hn g h hloc t ht hη b`** | side-of-`r` agreement between `g.curve (g.sideTime b t)` and the centre for persistent `a`-visits (SPLIT's `s7p_side_of_r` on `h.1 : g.VertexEdgeAt M a`; `s7a2_continuousAt_edgeParameter`, `s7a2_pos_of_ne_zero`) |
| **`s7fa_sideData hn g h hloc t ht hr0 hr1 hr hη hηr hηr1 b : s7p_SideData M a g.center (g.curve (g.sideTime b t)) r η`** | for EITHER side `b` (so also `P₀` with `b := !s7f_side g M a`): `hQC := s7f_hQC hn h.1 t b`, `hw := s7e_hw`, `hord := (s7e_hL …).parameter_order`, `hside := s7fa_side_of_r` |

### 1.C The radius theorem (line 5683)
**`s7fa_exists_bigonSplit hn g h h₁ h₂`** — the frozen statement of `s7f_exists_bigonSplit` verbatim; `δ` = the radius of
`s7a2_exists_intervalLocal hn g M a h.1`; body `s7fa_bigonSplit_side hn (s7fa_sideData … (s7f_side g M a)) (s7f_pattern hn h t).1
(s7f_pattern hn h t).2.1 h₁ h₂` (the target's `s7f_x hn h t`, `s7f_y hn h t`, `s7f_hP₂ g M a t` and `s7f_hQC …` unify with
`s7p_x false _`, `s7p_x true _`, `hd.hQ`, `hd.hQC` by `rfl` / proof irrelevance — no `convert`, no `show`).

**Closed: `s7f_exists_bigonSplit` (W4_FB1 line 5706, body 5714).**

## 2. Not proved

Nothing in this unit.  No black box consumed, no `s7fa_` Prop stated with `sorry`.  Nothing believed false; no missing
hypothesis in the frozen statement (the ten hypotheses of `s7f_bigonSplit_of` are all literally true below the radius, and the
frozen statement needs no more than `h : g.BigonAt M a` — in fact `h.1 : g.VertexEdgeAt M a` plus the pattern `s7f_pattern`
suffice; the bigon-vs-sliding distinction enters only through `s7f_side`/`s7f_pattern`, i.e. through WHICH side carries the two
newborns).

## 3. Method audit (reassessment discipline)

Attempts on the box: **one**; it compiled with 0 errors and 0 warnings on the first probe (16 s on a 1394-line scratch prelude =
header + SPLIT block + F's `S7FBigonSides` + the `s7f_BigonSplit` structure).  No audit was triggered.  Estimate check: OPEN_ITEMS
§A-07 / W3_F_REPORT §2 estimated **600-900 lines** for "U_S7B §2.2's 500-800 for the sliding `PivotSplit` plus the two-newborn
bookkeeping"; actual **335 lines** (of which 150 are the verbatim `s7p_x_split` body).  The overrun is negative because the
estimate predated W3_SPLIT_REPORT §3's observation that "§1.C-1.G apply to the bigon side polygons `P₀`, `P₂` as well once a
`s7p_SideData` is supplied" — the two-newborn bookkeeping the estimate feared (the four newborn visits' positions) is already
inside `s7p_kappa_va_bounds` / `s7p_kappa_vl_false` / `s7p_kappa_vl_true`, which are stated for an arbitrary leg `f` and read
the windows of `ContactParameterWindows` that a bigon side carries for both legs at once.  Nothing in the frozen statement
needed the `VertexLocalData.visit_order` route sketched in §A-07 ("`P₂`'s positions are the centre's on persistent visits …
with the four newborn visits inserted"): the κ-bounds do that job directly.

## 4. How to consume (F boxes 2-3, K, B2)

* `s7f_sector_split` and `s7f_exists_law_residual` now take their `hsplit` from a proved theorem; their remaining `sorryAx`
  is boxes 2 (`s7f_exists_twoNewbornTerm`, W4_FB1 line 5723) and 3 (`s7f_exists_ineligible_transport`, line 6060).
* **Box 3 / B2 reuse.** `s7fa_sideData hn g h hloc t ht hr0 hr1 hr hη hηr hηr1 (!s7f_side g M a)` is the `s7p_SideData` of
  `P₀(t)` on the same radius; with it SPLIT's `s7p_kappa_*_bounds`, `s7p_mem_range_first/_second`, `s7p_first_params/_second_params`
  read the persistent visit positions of `P₀` against the centre exactly as for `P₂` — the "visit-position bookkeeping shared
  with box 3" of §A-07/§A-09.  For the separation lemma box 3 needs (a chord `z ∈ N` with one visit in `A = (3η, D+r−3η)` and one
  in `B = (D+r+3η, n−3η)` separates the two visits of `x` and of `y`): the κ-coordinates of `x`'s visits are
  `s7p_kappa_va_bounds` (`D + r ± η`) and `s7p_kappa_vl_false` (`> n − η`), those of `y` are the `va` bound and
  `s7p_kappa_vl_true` (`< η`), so "`z` separates `x`'s visits" is `linarith` on `κ`, as in `s7p_x_free_*`.
* **Eligibility identification (K §4(c)).** `s7f_Eligible` ↔ `s7z_Eligible` is a corollary of this box through
  `hsplit.x_split`/`y_split` (an old crossing interlacing neither newborn lies in a half image) — now available below the radius.
* `s7fa_bigonSplit_side` is generic: any polygon `Q` with a `s7p_SideData` and both contact crossings gets the split; nothing in
  it is tied to `WallGerm`.

## 5. Mathlib / Lean pitfalls hit (v4.34.0-rc2 pin)

None new.  Two facts worth recording for the remaining F boxes: (i) `s7f_x hn h t = s7p_x false hc` and `s7f_y hn h t = s7p_x
true hc` are `rfl` (through `noncomputable def s7f_x`, `def s7p_x`, and `contactLeg`'s `if` on a Bool literal), so SPLIT's lemmas
about `s7p_x f hc` apply to the newborns by `exact`, no `Subtype.ext`/`convert`; (ii) redeclaring no outer section variable
(reusing `hn g {M a} h h₁ h₂` of `section S7FSectorSplit` and adding only `{P Q} {r η} (hd …)` resp. `{r η δ} (hloc) (t) (ht)` in
nested sections, with `include hd in` / `include h hloc ht in` per theorem) produced zero unused-variable or unused-instance
warnings without any `omit` beyond the one on `s7fa_not_affected_of_ne`.

## 6. Left

Of the F lane: boxes 2 (`s7f_exists_twoNewbornTerm`, 1,000-1,500 est.) and 3 (`s7f_exists_ineligible_transport`, 500-800 est.,
reduced by §4's reuse).  Not this unit's: the other ten sorried bodies listed in the header; the leaves `s7_sliding_law_at`,
`s7_bigon_law_at`; the row theorems `thm_C_S7_of`, `thm_C_S7_of_floor`, `thm_C_S7` (untouched, byte-identical).
