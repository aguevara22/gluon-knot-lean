# W3_K_REPORT — wave 3 unit K (prefix `s7z_`; U110-K, PLAN_FINAL §3.3 bigon (6): the ASSEMBLY of the bigon leaf `s7_bigon_law_at`), 2026-09-15 22:12 UTC / 6:12pm ET

File: `work/drafts/corner/W3_K.lean` = `W3_Skeleton.lean` (97 lines) + ONE inserted block (lines 37-608, 572 lines,
**29 `s7z_` declarations**: 18 theorems, 11 defs incl. the six Prop-definitions), placed inside `section VertexEdge`
immediately BEFORE the docstring of the leaf `s7_bigon_law_at` (now line 609), after the sliding leaf, **plus the leaf's
`sorry` body replaced** (rule (2)): `diff W3_Skeleton.lean W3_K.lean` = `36a37,608` + `54c626` (`sorry` →
`exact s7z_bigon_law_at_of hn h h₁ h₂ (s7z_exists_rowSector hF hsing hn h h₁ h₂)`); 0 other changes.  669 lines,
sha256 `5ba907578fd2d66e…`.  Statements, names and docstrings of the five frozen declarations untouched
(`python3 tools/stmt_check.py W3_K.lean`: 4/49 OK — `s7_sliding_law_at`, `s7_bigon_law_at`, `thm_C_S7_of`,
`thm_C_S7_of_floor` — identical to the skeleton's own 4/49; `thm_C_S7`'s row is the checker's known mismatch on the
skeleton itself).  No import added, no `open` added.
Check (official): `cd work/lean && lake env lean ../drafts/corner/W3_K.lean` — **0 errors, exit 0**, ~20 s warm;
**exactly 4 `declaration uses sorry`** = the frozen sliding leaf (line 26) + this unit's THREE black boxes
(`s7z_F_exists` 403, `s7z_returned_of_FSector` 423, `s7z_oneNewborn_exists` 442); **0 other warnings** (the two
`unusedSectionVars` hits silenced with `omit [NeZero n] in`).  `grep -c sorry`: 3 (skeleton) → **6** (= 4 sorry bodies at
lines 34, 417, 438, 445 + 2 prose mentions: the skeleton header line 4 and the §E heading line 398).
Clash scan `grep -rln s7z_ work/lean/SM work/lean/CV work/lean/Bridge work/drafts/corner/*.lean`: only W3_K.lean.
Axioms (`#print axioms` on a scratch copy): pure algebra and wall vocabulary (`s7z_sum_insert_split`, `s7z_law_of_rows`,
`s7z_residual_sum`, `s7z_pattern`, `s7z_x_ne_y`, `s7z_s₀_eq_chi`, `s7z_dirSign_sq`, `s7z_s₀_eq_dirSign_mul`) =
`[propext, Classical.choice, Quot.sound]`; every theorem mentioning `cornerStateSum`/`s7e_term`
(`s7z_undirected_of_rowSector`, `s7z_law_at_of_rowSector`, `s7z_bigon_law_at_of`, `s7z_law_at_of_residual`,
`s7z_bigon_law_at_of_residual`) `+ SM.lit_homfly` (through `cornerCoefficient`, as for the whole corner chain);
`s7z_exists_rowSector`, `s7_bigon_law_at`, `thm_C_S7_of`, `thm_C_S7` carry `sorryAx` through the three black boxes ONLY
(the registered set is unchanged: `thm_C_S7` = `[propext, sorryAx, Classical.choice, Quot.sound, lit_homfly,
lit_homfly_descent, lp_lm, lp_lm_uniqueness, ng_finite_word, src_contact]`).
Reassessment rule: not triggered (one compile error in five rounds — a swapped contradiction in `s7z_pattern`).

**Leaf closed: YES, MODULO THREE EXPLICIT BLACK BOXES** — the body of `s7_bigon_law_at` is the one-line composition
and typechecks; `#print axioms s7_bigon_law_at` shows `sorryAx` exactly through `s7z_F_exists`,
`s7z_returned_of_FSector`, `s7z_oneNewborn_exists` (§3).  Nothing believed false; no frozen statement needs a change.

## 0. What the block renders (sm-4:396-455 bookkeeping, 874-908 total), in one paragraph

The bigon law is `Σ_{P₂} − Σ_{P₀} = s₀ C(λ₁) C(λ₂)` on the two sides `P₂` (newborn side, `s7z_side`) and `P₀`, where every
support of `P₂` is uniquely `T`, `T∪{x}`, `T∪{y}` or `T∪{x,y}` with `T` newborn-free (`s7z_sum_insert_split`, a pure
`Finset.powerset` fact), the newborn-free supports are the persistent images of `P₀`'s supports (a bijection `e₀`), and the
eligible ones (`s7z_Eligible`: a decomposition meeting the common neighbourhood `N` of `x, y` in no crossing) correspond to
`Ind(λ₁) × Ind(λ₂)` (a bijection `e`).  Per newborn-free `T` the ROW `row T = (f_H T − f_L (e₀⁻¹ T)) + f_H (T∪{x}) +
f_H (T∪{y}) + f_H (T∪{x,y})` is `0` for ineligible `T` and `s₀ · term(T₁) term(T₂)` for eligible `T` — the latter as
`ε s₀ G` (returned newborn-free row) `+ 0 + 0` (one-newborn rows) `+ (1−ε) s₀ G` (two-newborn row), i.e. eq. s7c:bigon-total
`B + R_ret = (1−ε)J + εJ = J`; `s7z_law_of_rows` sums this to `Σ f_H − Σ f_L = s₀ (Σ g₁)(Σ g₂)` (`Fintype.sum_equiv`,
`Fintype.sum_prod_type`, `Finset.sum_mul_sum`, the half terms vanishing off the decompositions).  The direction
(eq. s7c:bigon-signs) is absorbed by `s7z_s₀ g M a b := if b then s else −s` with `s = g.contactSign M a` (PROVED `= χ(P₀)`,
`s7z_s₀_eq_chi`, from `vertex_contact_signs`), so `C(P₊) − C(P₋) = s C(λ₁) C(λ₂)` follows by `cases` on the newborn side
(`s7z_law_at_of_rowSector`).  The three geometric inputs — F's data (`e₀`, `e`, ineligible cancellation, two-newborn row),
the returned newborn-free row (SITE + BLOCK + ROT + RET + J's floor entries), the one-newborn rows (J's cb:singleton entry
+ C's selectors) — are the Props `s7z_FSector`, `s7z_NewbornFreeRow`, `s7z_OneNewbornRows` (§3), bundled per `t` in
`s7z_RowSector`; the leaf is `s7z_bigon_law_at_of : (∃ δ > 0, ∀ t < δ, s7z_RowSector …) → <leaf statement>` applied to
`s7z_exists_rowSector hF hsing …`, itself PROVED from the three sorried per-unit existence theorems (radii intersected).
Section F re-does the assembly on **unit F's ACTUAL output shape** (W3_F_REPORT §0, read after this unit started):
`s7z_law_at_of_residual` takes `s7f_exists_law_residual`'s identity as a hypothesis (F's data abstracted) and reduces the
law at `t` to K's residual obligation "the second summand is `εJ`" — `hrow` + `hone` — so the assembler can close the
leaf from W3_F's proved theorems without touching §C-E.

| printed (sm-4) | block section / lemmas | status |
|---|---|---|
| 409-418 the four sectors of `P₂` (`T`, `T∪{x}`, `T∪{y}`, `T∪{x,y}`) | §A `s7z_sum_insert_split` | PROVED (pure) |
| 874-908 `B + R_ret = J`, `Finset.sum_bij` + distributivity | §A `s7z_law_of_rows` (abstract rows), §F `s7z_residual_sum` (filter-sum form) | PROVED (pure) |
| 396-399 `P₀`, `P₂` (the side with the two newborns) | §B `s7z_side`, `s7z_pattern` (from `vertex_sides`' `BigonCrossingPattern` at `(t, t)` and `(base, t)`) | PROVED |
| 398 the newborns `x = x_{M−1,a}`, `y = x_{a,M}` | §B `s7z_x`, `s7z_y`, `s7z_x_ne_y` (`contact_pairs_distinct`) | PROVED |
| 400-406 eq. s7c:bigon-signs `s₀`, `δ_dir`, `s = δ_dir s₀` | §B `s7z_s₀`, **`s7z_s₀_eq_chi`** (`s₀ = χ_{a,a+1,M}(P₀)` at every `t`), §F `s7z_dirSign`, `s7z_dirSign_sq`, `s7z_s₀_eq_dirSign_mul` | PROVED |
| 409 `ε` | §B `s7z_eps` (`if Interlaces hn hP₂ x y then 1 else 0`) | defined |
| 419-421 eligible `T` (`T ∩ N = ∅`) | §B `s7z_Eligible` (decomposition, no selected crossing interlaces both newborns) | defined |
| 421-425 ineligible rows zero; 428-431 eligible bijection; 434-455 two-newborn row `B = (1−ε)J` | §C `s7z_FSector` (Prop), §E `s7z_F_exists` | STATED (black box, unit F) |
| 456-770, 785-825 returned newborn-free row `= εJ` (skein, two-component row, ledger, floor) | §C `s7z_NewbornFreeRow` (Prop), §E `s7z_returned_of_FSector` | STATED (black box, SITE+BLOCK+ROT+RET+J) |
| 693-723, 777-788 one-newborn rows zero (selectors / cb:singleton) | §C `s7z_OneNewbornRows` (Prop), §E `s7z_oneNewborn_exists` | STATED (black box, J+C) |
| the law at `t` (undirected, then directed) | §D `s7z_undirected_of_rowSector`, `s7z_law_at_of_rowSector` | PROVED from the sector |
| the leaf modulo the sector; the sector from the boxes | §D `s7z_bigon_law_at_of`, §E `s7z_exists_rowSector` | PROVED |
| the law at `t` on F's output shape; the leaf modulo F-shaped data | §F `s7z_law_at_of_residual`, `s7z_ResidualData`, `s7z_bigon_law_at_of_residual` | PROVED |
| **`s7_bigon_law_at`** | body `s7z_bigon_law_at_of … (s7z_exists_rowSector …)` | CLOSED modulo the three boxes |

## 1. Proved (18 theorems, 11 defs; all `s7z_`, inside `section VertexEdge`, sub-`section S7ZBigon` with
`variable {g : WallGerm n} {M a : ZMod n}`)

§A `s7z_sum_insert_split`, `s7z_law_of_rows`; §B `s7z_side` (def), `s7z_pattern`, `s7z_x` (def), `s7z_y` (def), `s7z_x_ne_y`,
`s7z_s₀` (def), `s7z_s₀_eq_chi`, `s7z_eps` (def), `s7z_Eligible` (def); §C `s7z_FSector`, `s7z_NewbornFreeRow`,
`s7z_OneNewbornRows`, `s7z_RowSector` (Prop defs); §D `s7z_undirected_of_rowSector`, `s7z_law_at_of_rowSector`,
`s7z_bigon_law_at_of`; §E `s7z_exists_rowSector` (proved FROM the three boxes); §F `s7z_residual_sum`, `s7z_dirSign` (def),
`s7z_dirSign_sq`, `s7z_s₀_eq_dirSign_mul`, `s7z_law_at_of_residual`, `s7z_ResidualData` (Prop def),
`s7z_bigon_law_at_of_residual`.

Accepted / ported inputs used: `vertex_sides` (`VertexSidesData … .2.2.2.1 s t : VertexCrossingData`, `.2.1 h.2 :
BigonCrossingPattern`), `vertex_contact_signs`, `contact_pairs_distinct`, `contactSign`, `s7a_sideGeneric`, `Interlaces`,
`IsDecomposition`, `firstHalfIndex`, `secondHalfEdgeIndex` (SM.CornerChainUnits / the accepted wall library); the wave-2b
algebra `s7e_term`, `s7e_term_of_not`, `s7e_cornerStateSum_eq_sum_term`, `s7e_sum_full_eq_of_zero` (SM.CS7Sliding — the
sliding unit's completion-by-zeros form of lem:C-X1 is reused verbatim); Mathlib `Finset.sum_powerset_insert`,
`Finset.sum_subtype`, `Finset.sum_coe_sort`, `Fintype.sum_equiv`, `Fintype.sum_prod_type`, `Finset.mul_sum`,
`Finset.sum_mul_sum`, `Finset.sum_sub_distrib`, `Finset.notMem_erase`.

## 2. Unproved — the three black boxes, exact shapes and estimates

The leaf `s7_bigon_law_at` is closed modulo §3's three sorried theorems.  What each needs, with the supplier's own report:

1. **`s7z_F_exists`** (unit F).  W3_F_REPORT §2 shows F itself is PROVED down to three geometric black boxes:
   `s7f_exists_bigonSplit` (B's split fields, 600-900 lines), `s7f_exists_twoNewbornTerm` (the bigon mark map + triangle,
   1,000-1,500), `s7f_exists_ineligible_transport` (500-800, incl. the new "dominated newborn is mixed" separation lemma).
   **Remaining: 2,100-3,200 lines** of geometry (F's numbers), plus the ≤ 300-line bridge of §4(b) if the §C shape is kept.
2. **`s7z_returned_of_FSector`** (SITE + BLOCK + ROT + RET + J).  The polynomial/row content is PROVED in the sibling units on
   explicit hypotheses: SITE `s7s_cornerHomfly_skein` (skein with the R-II site done, modulo `s7s_carrier_data_of_wall` 400-700,
   `s7s_wallTriangleData_of_bigon` 300-500, and `hrec` 1,000-1,650, W3_SITE_REPORT §2-3); BLOCK `s7k_interlacing_row` /
   `s7k_noninterlacing_row` / `s7k_different_block_row` + the term laws `s7k_interlacing_term` / `s7k_noninterlacing_term`
   (W3_BLOCK_REPORT §H, §J); J `s7j_interlacing_entry_at_halves` / `s7j_noninterlacing_entry_at_halves` /
   `s7j_different_block_entry_at_halves` (the floor at the half contact carriers as `Component` of `Tᵢ` of `λᵢ` — literal
   discharge of sm-4:800-835).  What no unit has: the per-eligible-support INSTANTIATION of their hypotheses on the actual
   carriers of `lift T₀` vs `T₀` — the full contact carrier pair `q_H, q_L` and the half carriers `q₁, q₂` (U110-A/B: the
   component isos in Gauss form, `s7k_component_iso_of_gauss`, `s7k_reduced_iso_of_gauss`), the rotation through the wall
   (`R_H = R_L`, U110-A2's family excludes the contact carrier: 400-600), the selector patterns (C), the spectator
   bookkeeping `wind`/`cornerProduct` over the other carriers, and the ε ⟺ turn-sign link (`s7i_contact_dichotomy`).
   **Remaining: 3,500-5,400 lines** (W3_BLOCK_REPORT §2's total for the bigon leaf, which is exactly this box).
3. **`s7z_oneNewborn_exists`** (J + C).  J's `s7j_one_newborn_term_zero_insert` PROVES `term(insert x T) = 0` from
   "owner uniform ⇒ `{y}` isolated block" hypotheses; C's `carrierWeight_eq_zero_of_not_uniform` covers `ε = 1` (the
   daughter carrying the turn at `m` is mixed, eq. s7c:one-newborn-turns).  What remains is the geometry per eligible `T₀`:
   at `ε = 0` that every old neighbour of `y` is a neighbour of the selected `x` on `P₂(t)` (sm-4:777-781, an interlacement
   statement on the side polygon from the words eq. s7c:bigon-words-eq), at `ε = 1` the mixed owner.  **Remaining: 400-700
   lines** (on F's `s7f_BigonSplit` vocabulary, whose `x_free/y_free/x_split/y_split` fields carry the words).

Total for the bigon leaf beyond this unit: **≈ 6,000-9,300 lines**, all geometry/instantiation; no algebra, skein, record,
floor or singleton content is left open (this unit + F + SITE + BLOCK + J).  Not attempted here: everything in 1-3 (out of
K's scope by PLAN §4; the 2-hour bounded wave allowed no geometric lane).

## 3. Black boxes — what this unit consumes (rule (3)), stated exactly

All three are `∃ δ > 0, ∀ t : g.SideParameter, t.val < δ → …` at the newborn side `b := s7z_side g M a`, newborns
`x := s7z_x hn h t`, `y := s7z_y hn h t`, sides `P₂ := g.curve (g.sideTime b t)` (generic `s7a_sideGeneric g b`),
`P₀ := g.curve (g.sideTime (!b) t)`, terms `f_H := s7e_term hn hP₂`, `f_L := s7e_term hn hP₀`,
`g₁ := s7e_term (contactHalfSizes_bounds hn h.1.1).1.1 h₁`, `g₂ := … .2.1 h₂`, `ε := s7z_eps hn hP₂ x y`,
`s₀ := s7z_s₀ g M a b`, `Elig T := s7z_Eligible hn hP₂ x y T` (`IsDecomposition ∧ ∀ c ∈ T, ¬(Interlaces x c ∧ Interlaces y c)`):

* **`s7z_F_exists hn h h₁ h₂`** [unit F]: `∃ e₀ : Finset (Crossing P₀) ≃ {T : Finset (Crossing P₂) // x ∉ T ∧ y ∉ T}`,
  `∃ e : {T : {T // x ∉ T ∧ y ∉ T} // Elig T.1} ≃ {S₁ // IsDecomposition … h₁ S₁} × {S₂ // IsDecomposition … h₂ S₂}` with
  `s7z_FSector … e₀ e` = (i) `∀ S c, c ∈ S ↔ ∃ c' ∈ (e₀ S).1, c'.val = c.val` (persistent = label-preserving; `s7a_cross` is
  `⟨x.val, _⟩`, so this pins `e₀` down); (ii) `∀ T c₁, c₁ ∈ (e T).1.1 ↔ ∃ c ∈ T.1.1, c.val = c₁.val.image (firstHalfIndex M a)`
  and the same for `(e T).2.1` with `secondHalfEdgeIndex` (= `s7b_firstCrossingQ_val` / `s7b_secondCrossingQ_val`, checked in
  the library: these ARE B's crossing maps, so `e` is `s7b_eligibleDecompositionEquiv` up to the lift); (iii) `∀ T, ¬ Elig T →
  f_H T = f_L (e₀.symm T) ∧ f_H (insert x T) = 0 ∧ f_H (insert y T) = 0 ∧ f_H (insert x (insert y T)) = 0`; (iv) `∀ T, Elig T →
  f_H (insert x (insert y T)) = (1 − ε) * s₀ * (g₁ (e T).1.1 * g₂ (e T).2.1)`.
* **`s7z_returned_of_FSector hF hn h h₁ h₂`** [SITE + BLOCK + ROT + RET + J-floor]: `∀ e₀ e, s7z_FSector … e₀ e →
  s7z_NewbornFreeRow … e₀ e` = `∀ T, Elig T → f_H T − f_L (e₀.symm T) = ε * s₀ * (g₁ (e T).1.1 * g₂ (e T).2.1)`.  (Conditional
  on F's data, which (i)-(ii) determine.)  The floor `hF` is a parameter; `hsing` is not needed here.
* **`s7z_oneNewborn_exists hsing hn h`** [J-singleton + C]: `s7z_OneNewbornRows hn t b x y` = `∀ T, x ∉ T → y ∉ T → Elig T →
  f_H (insert x T) = 0 ∧ f_H (insert y T) = 0`.
* No other unit's declaration is referenced (rule (3)): `s7f_*`, `s7s_*`, `s7k_*`, `s7j_*`, `s7r_*`, `s7q_*`, `s7p_*` never
  appear in W3_K.lean.

## 4. Coordination with the sibling reports (read at the start and re-read at the end) — and two shape observations

(a) **F's shape vs K's §C shape.**  W3_F_REPORT (21:57Z) appeared after this block's §A-E were written.  F organises the sum
over the supports `T₀` of `P₀` with the persistent LIFT `s7f_lift` and `Finset.filter` sums (its pitfall 1: subtype
`Fintype`/`Decidable` instance terms differ between files), delivering `s7f_exists_law_residual` = `C(P₊) − C(P₋) =
(if ε then 0 else 1)·J + δ_dir·(Σ_{T₀ eligible}(term₂(lift T₀) − term₀ T₀) + Σ_{T₀ eligible}(term₂(T₀∪{x}) + term₂(T₀∪{y})))`.
K's §C shape instead indexes by the newborn-free supports of `P₂` with an abstract `e₀`.  Both are faithful; to avoid forcing a
bridge, **§F restates the assembly on F's exact shape**: `s7z_law_at_of_residual` consumes that identity as `hres` with F's
data abstracted (`α`, `lift`, `term₀`, `Elig`, `ε : Prop`, `d = δ_dir` with `d² = 1` and `s₀ = d·s`), and needs only K's
residual obligation `hrow` (`term₂(lift T₀) − term₀ T₀ = (if ε then 1 else 0) * s₀ * (g₁ (e T₀).1.1 * g₂ (e T₀).2.1)`) and
`hone` (`term₂(T₀∪{x}) = 0 ∧ term₂(T₀∪{y}) = 0`) per eligible `T₀`, with `e` the eligible bijection on `P₀`
(`s7b_eligibleDecompositionEquiv hn h.1.1 h.1.2.2.2.1 (hQC on P₀) hP₀ h₁ h₂ hsplit.split`, restricted to `Elig` —
F's `s7f_Eligible` is "every crossing lifts into a half image", i.e. the library's `∀ y ∈ T, y ∈ range ι₁ ∪ range ι₂` read
through the label-preserving lift).  `s7z_side`, `s7z_x`, `s7z_y`, `s7z_pattern` are DEFINITIONALLY F's `s7f_side`, `s7f_x`,
`s7f_y`, `s7f_pattern` (same `decide (IsCrossing P₊(base) {a, M})`, same `vertex_sides` reads), and `s7z_s₀_eq_chi` /
`s7z_s₀_eq_dirSign_mul` are F's `s7f_s₀_eq_chi` (`δ_dir · s = χ(P₀)`); the assembler may identify them by `rfl` or keep
both.  **Recipe for the assembler once W3_F is in the same file (VERIFIED against W3_F.lean lines 1077-1115 at 22:15Z: F's
`s7f_law_residual` / `s7f_exists_law_residual` conclusion is LITERALLY the `hres` hypothesis of `s7z_law_at_of_residual` with
`b := s7f_side g M a`, `x y := s7f_x hn h t, s7f_y hn h t`, `d := s7f_dirSign g M a`, `ε := s7f_Interlacing hn h t`,
`α := Finset (Crossing (g.curve (g.sideTime (!s7f_side g M a) t)))`, `lift := s7f_lift hn g h t`,
`term₀ := s7e_term hn (s7f_hP₀ g M a t)`, `Elig := (Finset.univ).filter (s7f_Eligible hn g h t)` — same `J` spelling
`(g.contactSign M a : ℤ) * (C₁ * C₂)`, same `(if ε then 0 else 1) * J + δ_dir * (Σ … + Σ …)`, same summand bodies; F's
`s7f_hP₂ g M a t` and K's `s7a_sideGeneric g b` are both proofs of the same `Generic`, hence interchangeable):**
```
s7z_law_at_of_residual hn h h₁ h₂ t (s7f_side g M a) (s7f_x hn h t) (s7f_y hn h t) (s7f_dirSign g M a)
  (s7f_dirSign_sq g M a) (s7z_s₀_eq_dirSign_mul g M a)   -- s7f_side/s7f_dirSign are definitionally s7z_side/s7z_dirSign
  (s7f_Interlacing hn h t) (s7f_lift hn g h t) (s7e_term hn (s7f_hP₀ g M a t))
  (Finset.univ.filter (s7f_Eligible hn g h t)) e (s7f_law_residual hn g h h₁ h₂ t hsplit hterm htr) hrow hone
```
with `e` the eligible bijection on `P₀` restricted to the filter (`s7b_eligibleDecompositionEquiv` composed with
`Equiv.subtypeEquivRight` on `Finset.mem_filter` and the lift/eligibility identification of §4(c)), and `hrow`/`hone` the
residual obligations of boxes 2-3 in F's vocabulary; `s7z_bigon_law_at_of_residual` gives the radius form from
`s7f_exists_law_residual`.  The `if` on the atomic Prop `s7f_Interlacing hn h t` elaborates with the section's
`Classical.propDecidable` in both files.

(b) **If the §C shape is kept**, the bridge from F to `s7z_FSector` is: `e₀ := Equiv.ofBijective (s7f_lift …) ⟨s7f_lift_injective,
s7f_lift_surj⟩` restricted to the target subtype by `s7f_x_not_mem_lift`/`s7f_y_not_mem_lift` (clause (i) from
`s7f_liftCross_val`), `e := s7b_eligibleDecompositionEquiv` composed with the lift (clause (ii) is `s7b_*CrossingQ_val`),
clause (iii) from `s7f_exists_ineligible_transport` + `s7f_term_eq_zero_of_ineligible`, clause (iv) from
`s7f_exists_twoNewbornTerm` (`ε = 0`) and `s7f_twoNewbornSum_eq_zero`'s argument (`ε = 1`: two interlacing crossings are never
in one decomposition, so the term is `s7e_term_of_not`).  Est. 200-400 lines.  Not attempted (F's file is a black box here).

(c) **Eligibility.**  K's `s7z_Eligible` is the paper's `T ∩ N = ∅` with `N` = the common old neighbourhood (sm-4:419-420),
i.e. "no selected crossing interlaces both newborns"; F's `s7f_Eligible` is "every selected crossing lifts into a half image".
They agree under F's split fields `x_split`/`y_split` (an old crossing interlacing neither newborn lies in an image) and
`x_free`/`y_free` (an image crossing interlaces neither newborn) — exactly the fields F lists as its black box 1, so the
identification is a corollary of F's box, not an extra obligation.  §F is agnostic (it takes `Elig` as data).

(d) **ε.**  Both units render `ε` as `Interlaces hn hP₂(t) x y` on the side polygon (a `t`-dependent Prop).  The link to the
turn-sign dichotomy of the full contact corner (`s7i_contact_dichotomy`, U_S7I) is needed only INSIDE box 2 (choosing the
interlacing/noninterlacing row); K never splits on `ε` except algebraically (`by_cases` in `s7z_law_at_of_residual`).

(e) **Sign convention check (fidelity).**  `s7z_s₀ g M a (s7z_side g M a) = χ_{a,a+1,M}(P₀)` is PROVED (`s7z_s₀_eq_chi` at
`!b`), so the black boxes' `s₀` is literally the paper's `s₀ = sgn det(r, m − a)|_{P₀}` (eq. s7c:bigon-signs), and the frozen
`contactSign` is `δ_dir s₀` with `δ_dir = s7z_dirSign` (`+1` iff `P₋ = P₀`).  No sign is left to convention.

## 5. Mathlib / Lean pitfalls met (v4.34.0-rc2 pin)

1. `Finset.sum_subtype` has an IMPLICIT `Fintype (Subtype p)` argument: forward `rw` leaves it as a metavariable; rewrite
   RIGHT-TO-LEFT (`rw [← Finset.sum_subtype s hmem f]` with `f` explicit) so the instance is read off the goal — used in
   `s7z_sum_insert_split` after `Finset.sum_powerset_insert` ×3 (`univ = insert x (insert y ((univ.erase x).erase y))`,
   `Finset.powerset` of `univ` is `univ` by `ext; simp`).
2. `Fintype.sum_equiv e f g h` with `g` a `set`-bound local (`row`) accepts `h` stated on the unfolded body (zeta-defeq).
3. `Finset.sum_coe_sort Elig r` (`∑ i : Elig, r i = ∑ i ∈ Elig, r i`) turns a filter sum into the subtype sum that
   `Fintype.sum_equiv` needs; no instance mismatch arose (F's pitfall 1 is about subtype sums with compound predicates).
4. The bigon pattern from `vertex_sides` is `((vertex_sides hn g h.1).2.2.2.1 s t).2.1 h.2 : BigonCrossingPattern P₊(s) P₋(t)`
   — first parameter `P₊`, second `P₋`; the side-constancy argument needs the pattern at `(t, t)` AND at `(g.sideBase, t)`
   (mirror of `s7e_pattern`, which used `(t, g.sideBase)`).
5. `cases hb : s7z_side g M a` followed by `rw [hb] at key` handles a `Bool` that occurs inside `g.sideTime b t` and
   `(g.sideTuple b t).property` (the motive is type-correct because all occurrences are abstracted at once); then
   `simp only [Bool.not_false, s7z_s₀, Bool.false_eq_true, ↓reduceIte] at key` and `linear_combination ±key`.
6. `(g.sideTuple b t).property` and `s7a_sideGeneric g b` are interchangeable in `exact`/`refine` (proof irrelevance +
   `sideTuple` unfolding), as in `s7e_law_at_of_sectors`.
7. `omit [NeZero n] in` is required (linter) for theorems whose statement mentions only `WallGerm n`/`ZMod n` without any
   `NeZero`-needing constant (`s7z_dirSign_sq`, `s7z_s₀_eq_dirSign_mul`); it is NOT possible when `cornerStateSum` appears.

## 6. Notes for the assembler

* Position: the block starts at line 37 `/-! ### Unit K (wave 3, prefix `s7z_` …` and ends at line 607 `end S7ZBigon`, inside
  `section VertexEdge`, immediately before the bigon leaf's docstring (line 609); it opens `section S7ZBigon` with
  `variable {g : WallGerm n} {M a : ZMod n}` (closed before the leaf).  All names `s7z_`-prefixed.
* The leaf body (line 626) is `exact s7z_bigon_law_at_of hn h h₁ h₂ (s7z_exists_rowSector hF hsing hn h h₁ h₂)`; if the
  assembler prefers the F-aligned route, replace it by `s7z_bigon_law_at_of_residual hn h h₁ h₂ ⟨δ, hδ, fun t ht => ⟨…⟩⟩` with
  the instantiation of §4(a) and delete §E's three boxes (or keep them as documentation of the §C shapes).
* Both sibling units placed their blocks at the same anchor (before the bigon docstring): concatenation order there is free
  (K references none of them); K must come AFTER F if the assembler wants to instantiate §F with `s7f_*` inside K's file.
* Diff summary: `+` 572 lines, `−` 1 line (the leaf's `sorry`), `~` 0.  Reproduce: `cp W3_Skeleton.lean W3_K.lean`, insert
  the block before line 37, replace the leaf's `sorry`, `cd work/lean && lake env lean ../drafts/corner/W3_K.lean`.
