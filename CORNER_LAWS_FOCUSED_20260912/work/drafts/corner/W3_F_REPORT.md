# W3_F_REPORT — unit F (U110-F, prefix `s7f_`: the two-newborn sector `B = (1−ε)J` of the bigon branch), 2026-09-15 21:57 UTC / 5:57pm ET

File: `work/drafts/corner/W3_F.lean` (1201 lines) = `W3_Skeleton.lean` + ONE inserted block (`36a37,1140`,
1104 lines, 0 deleted lines), placed inside `section VertexEdge` immediately before the docstring of
`s7_bigon_law_at`.
Check: `cd work/lean && lake env lean ../drafts/corner/W3_F.lean` — **0 errors, 0 non-sorry warnings**, 5
`declaration uses sorry` warnings = the two frozen leaves (`s7_sliding_law_at` line 26, `s7_bigon_law_at` line
1149) + this unit's three black boxes (lines 553, 570, 907); 13-22 s warm.  `grep -c sorry`: 2 (skeleton) → 7
(= 5 declaration bodies at lines 34, 561, 587, 911, 1158 + 2 prose mentions: the skeleton header line 4 and this
block's docstring).  Statements, names, docstrings of the five frozen declarations untouched (pure insertion);
no import added; 74 declarations (`s7f_` and the namespace `s7f_BigonSplit`); clash scan
`grep s7f_ work/lean/SM/*.lean` empty.
Axioms (`#print axioms` on a scratch copy): every proved `s7f_` theorem that mentions `s7e_term`/`cornerStateSum`
depends on `[propext, Classical.choice, Quot.sound, SM.lit_homfly]` (the literature axiom enters through
`cornerCoefficient`, as for the whole corner chain); the pure combinatorics (`s7f_twoNewbornDecompositionEquiv`,
`s7f_bigonSplit_of`, `s7f_s₀_eq_chi`) is standard-axiom only; `s7f_triangle_data` adds `SM.lp_lm,
SM.lp_lm_uniqueness` through row 105's `corner_values_of_floor` (the registered set); the two radius theorems
that consume the black boxes (`s7f_sector_split`, `s7f_exists_law_residual`) carry `sorryAx`, nothing else.

**The leaf `s7_bigon_law_at` is NOT closed** (this unit never owned it: PLAN §4 makes U110-F a helper unit
for U110-K).  Its `sorry` is untouched.

## 0. What U110-K gets, in one paragraph

With `P₂ := g.curve (g.sideTime (s7f_side g M a) t)` the side carrying the two newborn crossings
`x = {a, M−1}`, `y = {a, M}` (`s7f_x`, `s7f_y`; `s7f_pattern` from `vertex_sides`' `BigonCrossingPattern`),
`P₀` the other side, `δ_dir = s7f_dirSign g M a` (eq. s7c:bigon-signs, `+1` iff `P₋ = P₀`),
`ε := Interlaces hn hP₂ x y` (`s7f_Interlacing`), `J = s · C(λ₁) · C(λ₂)` with `s = g.contactSign M a`,
`lift` the reading of a support of `P₀` on `P₂` (`s7f_lift`) and `Eligible T₀` = "`T₀ ∩ N = ∅`"
(`s7f_Eligible`: every crossing lifts into a half image), the block proves, from three geometric black
boxes stated in §2, **the assembled shape**

```
s7f_exists_law_residual hn g h h₁ h₂ :
  ∃ δ > 0, ∀ t < δ,
    C(P₊) − C(P₋) = (if ε then 0 else 1) · J
      + δ_dir · ( Σ_{T₀ eligible} (term₂(lift T₀) − term₀(T₀))
                + Σ_{T₀ eligible} (term₂(T₀ ∪ {x}) + term₂(T₀ ∪ {y})) )
```
(`term = s7e_term`, lem:C-X1's summand completed by zeros).  The first summand is `B = (1−ε)J`
(eq. s7c:sector-split, `s7f_sector_split`).  **U110-K's whole remaining obligation is sm-4:448 onward: the
second summand equals `ε · J`** — the eligible persistent rows by the skein extraction (G: `s7_universal_extraction`,
`s7g_*`), the two-component row (H), the rotation ledger (I), the floor reads (J) and cb:singleton for the
eligible one-newborn rows.  The per-`t` version `s7f_law_residual` takes the three geometric inputs as
hypotheses (no radius) so K can also assemble radii itself.

## 1. Proved (all `s7f_`; `{n} [NeZero n]` from `section VertexEdge`)

### 1.A Sides, newborns, signs (section `S7FBigonSides`)
| declaration | content |
|---|---|
| `s7f_side g M a : Bool` | the newborn side (`decide (IsCrossing P₊(base) {a, M})`), constant along the side by `s7f_pattern` |
| `s7f_dirSign g M a : ℤ`, `s7f_dirSign_sq` | eq. s7c:bigon-signs `δ_dir`, `δ_dir² = 1` |
| `s7f_pattern hn h t` | `P₂(t)` has both contact crossings, `P₀(t)` neither, at EVERY `t` (`vertex_sides … .2.2.2.1 t t / g.sideBase t`, `.2.1 h.2`) |
| `s7f_hP₂`, `s7f_hP₀` | genericity of the two sides (`s7a_sideGeneric`) |
| `s7f_x`, `s7f_y`, `_val`, `s7f_x_ne_y`, `s7f_x_affected`, `s7f_y_affected` | the newborns as `Crossing P₂(t)` |
| `s7f_eq_x_or_y_of_affected`, `s7f_P₀_not_affected` | `x, y` are the only affected crossings of `P₂`; every crossing of `P₀` is persistent |
| `s7f_hQC hn h t b` | `VertexCrossingData`'s persistence clause for either side (U110-B's `hQC`; `h : VertexEdgeAt`) |
| `s7f_s₀_eq_chi` | `δ_dir · s = χ_{a,a+1,M}(P₀)` = the paper's `s₀` (from `vertex_contact_signs`) |

### 1.B The three sectors of `P₂` and the directed difference (section `S7FSectors`)
| declaration | content |
|---|---|
| `s7f_Interlacing hn h t` | `ε` as `Interlaces hn hP₂ x y` |
| `s7f_twoNewbornSum`, `s7f_oneNewbornSum`, `s7f_persistentSum` | `Σ term` over the supports of `P₂` with both / exactly one / neither newborn (`Finset.filter` sums) |
| `s7f_sum_split3` | instance-free three-way split of a finite sum by two predicates |
| `s7f_cornerStateSum_P₂` | `C(P₂) = Σ_pers + Σ_one + Σ_two` (`s7e_cornerStateSum_eq_sum_term`) |
| `s7f_directed_difference` (+ `_aux`) | `C(P₊) − C(P₋) = δ_dir (C(P₂) − C(P₀))` (sm-4:399-406) |
| **`s7f_law_decomposition`** | `C(P₊) − C(P₋) = δ_dir · ((Σ_pers − C(P₀)) + Σ_one + Σ_two)` at every `t`, no black box |
| **`s7f_twoNewbornSum_eq_zero`** | **`ε = 1`: the two-newborn sector is empty** (sm-4:445) — two interlacing crossings are never in one decomposition |

### 1.C The bigon support split, abstractly (section `S7FSplit`, namespace `s7f_BigonSplit`; U110-B part IV's pattern)
`structure s7f_BigonSplit R R₁ R₂ ι₁ ι₂ x y : Prop` = `split : s7b_SupportSplit` + `x_not₁ x_not₂ y_not₁ y_not₂`
(newborns outside the images) + `x_free₁ x_free₂ y_free₁ y_free₂` (newborns interlace nothing in the images)
+ `x_split`, `y_split` (an old crossing interlacing neither newborn lies in an image: the complement is `N`,
sm-4:414-416).  Proved on it: `not_indep_of_mem_x/_y` (sm-4:418-420: a support meeting `N` and containing a
newborn is not independent), `indep_insert` (`{x,y} ∪ ι₁S₁ ∪ ι₂S₂` independent when `¬R x y ∧ ¬R y x`),
`pre₁_insert`, `pre₂_insert`, `insert_join_pre`, **`twoNewbornEquiv (hxy) : {S // Indep R S ∧ x ∈ S ∧ y ∈ S} ≃
{S₁ // Indep R₁ S₁} × {S₂ // Indep R₂ S₂}`** (eq. s7c:eligible-bijection on the two-newborn rows, sm-4:434-441),
`twoNewbornEquiv_apply` (`rfl`), `twoNewbornEquiv_symm_apply` (`rfl`).  `[DecidableEq γ]` is a section
variable (so the concrete `RProof.instDecidableEqCrossing` is passed through — see §4).

### 1.D On the actual decompositions (section `S7FDecompositions`)
`s7f_twoNewbornDecompositionEquiv hn hsep hm hQC hQ h₁ h₂ x y hsplit hxy : {S // IsDecomposition hn hQ S ∧ x ∈ S ∧
y ∈ S} ≃ Ind(λ₁) × Ind(λ₂)` (a direct `where`-definition, so `s7f_twoNewbornDecompositionEquiv_symm_apply :
(e.symm q).1 = insert x (insert y (hsplit.split.joinSupport q.1.1 q.2.1))` is `rfl`).

### 1.D' The contact triangle (section `S7FTriangle`)
**`s7f_triangle_data hF hn hP S hS q hs₀ h3 hturn hfree`** — eq. s7c:triangle-data on a carrier (sm-4:437-441):
three corners of turn `−s₀` and `carrierCrossingCount = 0` give `carrierWeight = s₀ ∧ |carrierRotation| = 1 ∧
cornerSlot = 0 ∧ cornerCoefficient = 1` (`s7c_carrierWeight_triangle`, `s7c_carrierUniform_of_weight_ne_zero`,
`(corner_values_of_floor hF).embedded_value`).  This is the triangle factor of BLACK BOX 2; what that box still
needs is the geometry (the triangle IS a carrier of `T ∪ {x, y}` with these three corners and no crossing) and
the successor correspondence for the other carriers.

### 1.E The sector identity (section `S7FSectorSplit`)
| declaration | content |
|---|---|
| **`s7f_term_eq_zero_of_ineligible`** | sm-4:418-420 on `P₂(t)`: a one- or two-newborn support containing an ineligible old crossing has term `0` (from the split) |
| **`s7f_twoNewbornSum_of_split`** | `ε = 0`: `δ_dir · Σ_two = s · C(λ₁) C(λ₂)` from the split, `¬ε`, and the termwise identity along the equiv (sm-4:441-445: `Finset.sum_subset`, `Finset.sum_subtype`, `Fintype.sum_equiv`, `Fintype.sum_prod_type`, `Finset.sum_mul_sum`, `s7f_dirSign_sq`) |
| **`s7f_sector_split_at`** | **eq. s7c:sector-split `δ_dir · Σ_two = (1−ε) J` at one `t`** from the split and the (conditional) termwise identity |
| **`s7f_sector_split`** | the same below a radius, from black boxes 1-2 |

### 1.F The split from its open fields (section `S7FSplitOf`)
`s7f_bigonSplit_of hn g h h₁ h₂ t hrel₁ hrel₂ hcross hcross' hxfree₁ hxfree₂ hyfree₁ hyfree₂ hxsplit hysplit` —
`inj₁ inj₂ disjoint` and the eight newborn exclusions are U110-B's (`s7b_firstCrossingQ_injective`,
`s7b_secondCrossingQ_injective`, `s7b_firstCrossingQ_ne_secondCrossingQ`, `s7b_*CrossingQ_not_affected` against
`s7f_x_affected`/`s7f_y_affected`), so BLACK BOX 1 is exactly the ten geometric hypotheses of this constructor.

### 1.G The persistent sector over `P₀` (section `S7FPersistent`)
| declaration | content |
|---|---|
| `s7f_hs` | persistent crossings agree between `P₂(t)` and `P₀(t)` (through the centre) |
| `s7f_liftCross`, `_val`, `_injective`, `_ne_x`, `_ne_y`, `s7f_exists_liftCross` | `Crossing P₀ → Crossing P₂` (same crossing set), bijective onto the non-newborns |
| `s7f_lift`, `s7f_mem_lift`, `s7f_liftCross_mem_lift`, `s7f_x_not_mem_lift`, `s7f_y_not_mem_lift`, `s7f_lift_injective`, `s7f_lift_surj` | `Finset (Crossing P₀) → Finset (Crossing P₂)`, bijective onto the newborn-free supports |
| **`s7f_persistentSum_eq_sum_lift`** | `Σ_pers(P₂) = Σ_{T₀} term₂(lift T₀)` (`Finset.sum_image`) |
| `s7f_Eligible hn g h t T₀` | `∀ z ∈ T₀, liftCross z ∈ range ι₁ ∪ range ι₂` (sm-4:416-417 `T ∩ N = ∅`) |
| **`s7f_persistent_difference_of_transport (htr)`** | `Σ_pers − C(P₀) = Σ_{T₀ eligible} (term₂(lift T₀) − term₀ T₀)` given the ineligible transport at `t` (sm-4:420-421) |
| **`s7f_law_decomposition_eligible (htr)`** | `C(P₊) − C(P₋) = δ_dir · (Σ_{eligible}(…) + Σ_one + Σ_two)` |

### 1.H The one-newborn sector over `P₀` (section `S7FOneNewborn`)
`s7f_insert_x_lift_injective`, `s7f_insert_y_lift_injective`, `s7f_oneNewborn_filter_eq` (the one-newborn
supports are exactly the `T₀ ∪ {x}` and `T₀ ∪ {y}`), `s7f_oneNewborn_images_disjoint`,
**`s7f_oneNewbornSum_eq_sum_lift`** (`Σ_one = Σ_{T₀} (term₂(T₀∪{x}) + term₂(T₀∪{y}))`),
**`s7f_oneNewbornSum_of_split (hsplit)`** (restricted to the eligible `T₀`: the ineligible rows vanish by
`s7f_term_eq_zero_of_ineligible`, sm-4:418-420 — the printed "neither extension by a newborn is a support").

### 1.I The assembled residual (section `S7FResidual`)
**`s7f_law_residual hn g h h₁ h₂ t hsplit hterm htr`** and **`s7f_exists_law_residual hn g h h₁ h₂`** — §0's
formula, at one `t` from the three geometric inputs, resp. below a radius from the three black boxes
(`min δ₁ (min δ₂ δ₃)`).

## 2. Not proved — the three black boxes (`sorry`), stated exactly as consumed

All three are of the form `∃ δ > 0, ∀ t < δ, …`; their bodies are the only `sorry`s of this unit.

1. **`s7f_exists_bigonSplit hn g h h₁ h₂`** — `s7f_BigonSplit (Interlaces hn hP₂(t)) (Interlaces hn₁ h₁)
   (Interlaces hn₂ h₂) (s7b_firstCrossingQ hn h.1.1 h.1.2.2.2.1 (s7f_hQC hn h.1 t (s7f_side g M a)))
   (s7b_secondCrossingQ …) (s7f_x hn h t) (s7f_y hn h t)`.  By `s7f_bigonSplit_of` this is exactly:
   `rel₁ rel₂` (the halves' interlacement is the restriction of `P₂`'s along the half crossing maps — U_S7B_REPORT
   §2.2's open fields, bigon form), `cross cross'` (no interlacement across the two images), `x_free y_free`
   (the newborn chords interlace no internal label of `A` or `B`), `x_split y_split` (an old crossing
   interlacing neither newborn lies in a half image — the converse of `s7b_isCrossing_firstHalf_image`,
   sm-4:414-416).  Content: `Interlaces` is `traversalBetween` of visit positions (Interlacement.lean); the
   half visit positions are the centre's (U110-B part II parameter laws) and `P₂`'s positions are the
   centre's on persistent visits (`VertexLocalData.visit_order`), with the four newborn visits inserted
   adjacent to `μ_M` on `E_{M−1}, E_M` and within `η` of `r` on `E_a` (`ContactParameterWindows`).
   **Estimate 600-900 lines** (U_S7B §2.2's 500-800 for the sliding `PivotSplit` plus the two-newborn
   bookkeeping; `s7e_nextMark_*`, `s7e_sign_const`, `s7e_side_a*` of CS7Sliding are reusable for the
   `E_a` side-of-`r` classification).
2. **`s7f_exists_twoNewbornTerm hn g h h₁ h₂`** — for every `hsplit` (as in 1), `¬ s7f_Interlacing hn h t`,
   and decompositions `S₁ S₂` of the halves:
   `s7e_term hn hP₂ (insert x (insert y (hsplit.split.joinSupport S₁ S₂))) = (δ_dir · s) · (s7e_term hn₁ h₁ S₁ ·
   s7e_term hn₂ h₂ S₂)`.  This is sm-4:434-447 verbatim: the four newborn visits smooth to the contact
   triangle — three corners of turn `−s₀`, no carrier crossing (`s7f_triangle_data` PROVES `wt = s₀`,
   `|rot| = 1`, `d = 0`, `c = 1` from exactly these two facts) — and otherwise exactly the
   successors of `T₁, T₂` with equal weights and coefficients (U110-B §2.4's bigon mark map
   `Mark λ₁ ⊕ Mark λ₂ → Mark P₂` with the two `μ_M`-vertices identified and the two smoothing corners
   `inr x`, `inr y` added; carriers ↔ `Component λ₁ T₁ ⊕ Component λ₂ T₂ ⊕ {triangle}` by the
   `s7b_ReturnTransport` cycle machinery; coefficients by U110-D's `s7d_cornerCoefficient_eq_of_cut` with
   `hr` from the ledger `s7i_*` or a family through the wall; `wind` by `Fintype.prod_sum_type` +
   `s7c_carrierWeight_triangle`).  **Estimate 1,000-1,500 lines** — the "bigon mark map … Not started,
   700-1000" of U_S7B §2.4 plus the triangle's carrier data and the product bookkeeping.  Note the sign:
   the paper's `s₀ = sgn det(r, m − a)|_{P₀}` is `δ_dir · s` here (`s7f_s₀_eq_chi`: `= χ_{a,a+1,M}(P₀)`).
3. **`s7f_exists_ineligible_transport hn g h`** — for every `T₀ : Finset (Crossing P₀(t))` with
   `¬ s7f_Eligible hn g h t T₀`: `s7e_term hn hP₂ (s7f_lift T₀) = s7e_term hn hP₀ T₀`.  This is sm-4:418-421
   "Deleting their four visits identifies the complete smoothing successor, owners, corners, rotations,
   carrier diagrams and coefficient reads": `lift T₀` is a PERSISTENT support of `P₂` (`s7f_x_not_mem_lift`,
   `s7f_y_not_mem_lift`), so U110-A's `s7a_sideComponentEquiv` (carriers, decompositions `s7a_side_isDecomposition_iff`,
   uniformity `s7a_side_carrierUniform_iff`), U110-A2's `s7a2_carrierRotation_eq` (`hr`) and U110-D's
   `s7d_cornerCoefficient_eq_of_strictMono` apply exactly as in CS7Sliding's `s7e_term_eq` — with ONE new
   fact for `hmem`: the newborns are not carrier crossings of any carrier of `lift T₀`.  Reason (the paper's
   "both newborns are dominated"): a chord `z ∈ T₀ ∩ N` has one visit in `A` and one in `B`, so it separates the
   two visits of `x` (and of `y`) on the circle; for a NON-CROSSING chord family, two boundary points lie on the
   same smoothing cycle iff no chord separates them — hence `x`'s two visits have different owners, `x` is a
   MIXED crossing and enters no carrier diagram, and `carrierCrossings` on `P₂` equal the transported ones
   (`s7a_side_mem_carrierCrossings` covers the persistent crossings).  This separation lemma is not in the
   library (the sliding analogue `s7e_xm_mem_iff` uses the adjacency of the leg visit and `μ_M` instead).
   **Estimate 500-800 lines** (the `s7e_term_eq` pattern ≈ 250 lines of CS7Sliding §1.H-1.J to re-instantiate
   with `x, y` in place of `x₋`, plus the separation lemma on the successor permutation ≈ 300-500).

Nothing believed false.  No missing hypothesis found in the frozen statement.  Two shape decisions to
record (FR for the executor): (i) `ε` is rendered as `Interlaces hn hP₂ x y` on the side polygon `P₂(t)`
(a Prop depending on `t`); U110-K/I must connect it to the turn-sign dichotomy of the full contact corner
(`s7i_contact_dichotomy`, U_S7I_REPORT interface notes: interlacing ⟺ full contact turn `s₀`) — by
`VertexLocalData.visit_order` it is constant in `t`, which K may or may not need; (ii) the sectors are
`Finset.filter` sums (not subtype sums) to stay independent of the `Decidable` instance terms — see §4.

## 3. How to consume (U110-K)

* `obtain ⟨δ, hδ, hres⟩ := s7f_exists_law_residual hn g h h₁ h₂`; for `t < δ`, `hres t ht` is §0's identity.
  K then proves `δ_dir · (Σ_{eligible}(term₂(lift T₀) − term₀ T₀) + Σ_{eligible}(term₂(T₀∪{x}) + term₂(T₀∪{y})))
  = ε · J` and finishes with `by_cases` on `s7f_Interlacing`, `ite_eq_left/right`, `ring`.  The frozen leaf's
  goal has `h.1.1` for `hsep` and `(g.sideTuple b t).property` for the side genericities — the latter are
  `s7a_sideGeneric g b` up to proof irrelevance (the block's `s7f_directed_difference_aux` uses exactly this).
* For the eligible persistent rows K needs, per `T₀` with `s7f_Eligible`, the carrier data of `lift T₀` on `P₂`
  vs `T₀` on `P₀`: the full contact carrier `L*` through `μ_M` has `x, y` as self-crossings on `P₂`
  (`D_H` = `D_L` plus the bigon) — the skein branch.  `s7f_Eligible` unfolds to the half-image membership, which
  is what `s7b_eligibleDecompositionEquiv` (U110-B, on `P₀` with `hQC := s7f_hQC hn h.1 t (!s7f_side g M a)`)
  needs to produce `(T₁, T₂)` and the floor reads at the half contact carriers.
* For the eligible one-newborn rows: `s7f_oneNewbornSum_of_split` already presents them as
  `term₂(T₀ ∪ {x}) + term₂(T₀ ∪ {y})`; cb:singleton (`hsing.isolated_zero`) applies at `T₀ ∪ {x}` with the
  isolated block `{y}` (sm-4:777-783).
* The three black boxes are independent lanes; 1 and 3 share the visit-position bookkeeping of `P₂(t)`
  against the centre and could be one lane ("bigon side positions", est. 1,000-1,500 lines together).

## 4. Mathlib / Lean pitfalls hit (v4.34.0-rc2 pin)

1. **`Decidable` instance terms inside subtype `Fintype`s differ between files.**  The library's
   `s7e_sum_split`/`s7e_sum_subtype_eq_of_zero` carry `Classical.propDecidable (P a)` with `P` a variable; the
   same statement elaborated here with `P S := p S ∧ q S` gets `instDecidableAnd …`, and for `x ∉ T` the concrete
   `Finset.decidableMem…` — so `rw`/`exact` against the library lemmas fail ("did not find pattern", or a
   200000-heartbeat `isDefEq` timeout).  Cure adopted: state the sector sums as `Finset.filter` sums, prove the
   three-way split instance-free (`s7f_sum_split3` over arbitrary finsets with membership characterisations,
   `Finset.sum_union`), and pass to subtype sums only through `Finset.sum_subtype` (implicit `Fintype`) and
   `Fintype.sum_equiv`.
2. `insert` on `Finset (Crossing Q)` resolves `DecidableEq` to `RProof.instDecidableEqCrossing`, while an
   abstract section without `[DecidableEq γ]` bakes in the classical one — the concrete `where`-definition then
   failed with "argument has type … `fun a b => Classical.propDecidable (a = b)` … expected
   `RProof.instDecidableEqCrossing`".  Cure: `variable [DecidableEq γ]` in the abstract section (and
   `omit [DecidableEq γ] in` for the lemmas that do not mention `insert`).
3. `theorem … : (e.symm q).1 = … := rfl` FAILS for an `Equiv` built with `.trans`/`Equiv.subtypeEquivRight`/
   `Equiv.prodCongr` ("Not a definitional equality") but succeeds for a direct `where`-structure definition —
   `s7f_twoNewbornDecompositionEquiv` is therefore defined by `where` (its `_symm_apply` is `rfl`), unlike
   `s7b_slidingDecompositionEquiv`.
4. `rw [← s7e_sum_full_eq_of_zero _ _ hz]` with the function and predicate left as `_` re-matched the sum it had
   just produced (giving `↑↑i`); pass `F` and `D` explicitly.
5. Section variables used only in a proof body are not auto-included (`unknown identifier hn`): `include hn h in`.
   `omit [NeZero n] in` errors when the statement mentions `cornerStateSum` ("cannot omit referenced section
   variable").  Subscript `₊`/`₋` are not identifier characters (`e₊` → "unexpected token").
6. `if_pos`/`if_neg` are deprecated → `ite_eq_left (h : c)`, `ite_eq_right (h : ¬c)`; `push_neg` → `push Not`;
   `Finset.notMem_erase`, `Finset.card_insert_of_notMem` (new `notMem` spelling).
7. `linear_combination (c) * s7f_dirSign_sq g M a` closes `d * (d * s * P) = s * P` cleanly where a chain of
   `← mul_assoc` rewrites hits the wrong association.
8. `cases b` on a `Bool` term followed by `simp only [Bool.not_false, Bool.false_eq_true, ↓reduceIte]` handles
   `if b then 1 else -1` and `!b`; when `simp` already closes the goal a trailing `ring` errors ("no goals").

## 5. Left

* Of this unit: the three black boxes of §2 (est. 600-900 + 1,000-1,500 + 500-800 lines).  Nothing else of
  PLAN §3.3 bigon (1) is open: the ineligible domination, the eligible bijection on two-newborn rows, `ε = 1`
  emptiness, the directed/sector bookkeeping and the row decomposition for K are proved.
* Not this unit's: `s7_bigon_law_at` (U110-K: `R_ret = εJ` from G/H/I/J + cb:singleton), `s7_sliding_law_at`
  (U110-E's remainder, W2_S7E_REPORT §2).
