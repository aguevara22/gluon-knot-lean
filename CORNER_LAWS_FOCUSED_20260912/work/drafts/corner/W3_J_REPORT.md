# W3_J_REPORT — wave 3 unit J (prefix `s7j_`; PLAN_FINAL §3.3 bigon (5): where thm:floor and cb:singleton ENTER; serves U110-K `s7_bigon_law_at`), 2026-09-15 21:50Z

File: `work/drafts/corner/W3_J.lean` = `W3_Skeleton.lean` (97 lines) + ONE inserted block (lines 37-509, 473 lines;
`diff W3_Skeleton.lean W3_J.lean` = `36a37,509`, 0 removed lines), placed inside `section VertexEdge` immediately BEFORE the
docstring of `s7_bigon_law_at` (line 510), after the sliding leaf.  No frozen statement, name or docstring touched; no
import added; both leaf `sorry`s untouched (lines 34, 527).  sha256 `b8bb91e110aac303…4435fd`, 570 lines.
Check: `cd work/lean && lake env lean ../drafts/corner/W3_J.lean` — **0 errors, 0 non-sorry warnings**, exactly 2
`declaration uses sorry` (lines 26 `s7_sliding_law_at`, 518 `s7_bigon_law_at`), 14-15 s warm.  `grep -c sorry`: 3 before
(skeleton: 2 leaves + 1 header prose) → 3 after (**this unit adds NO sorry** — no sorried black box, see §3).
Clash scan `grep -rln s7j_ work/lean/SM work/lean/CV work/drafts/corner/*.lean`: only W3_J.lean.
Axioms (`#print axioms` on a scratch copy, all 29 declarations): standard `[propext, Classical.choice, Quot.sound]` for the
pure-ℤ / Laurent-ring entries; `+ lit_homfly` where `hF.slot_le_of_signed` / `hsing.isolated_zero` / `cornerCoefficient` enter;
`+ lit_homfly, lp_lm, lp_lm_uniqueness` where `P_eq_homfly` / `P_knot_support` enter (`s7j_z_nonneg` and everything built on
the interlacing read) — the plan's policy set; the row assembly's expected list is unaffected.

**Leaf closed: NO** (`s7_bigon_law_at` still `sorry`; this unit is the floor/singleton ENTRY supplier, never the closer).
**Nothing believed false; no frozen statement needs a change.**

## 0. What the block renders (PLAN §3.3 bigon (5); sm-4:655-668, 680-690, 745-748, 758-769, 777-783, 785-813, 800-835)

Design decision.  Every entry is a theorem taking the EXTRACTED ROW as an explicit hypothesis — in three vocabularies, from
the most abstract to the leaf's own: (§B) the Laurent ring `R` (`f₁ f₂ : R`, `k₁ k₂ K : ℤ`, `ΩH ΩL : ℤ`), (§C) def:C at two
half contact carriers `q₁ : Component hn₁ hP₁ S₁`, `q₂` (`cornerHomfly`, `cornerSlot`, `cornerCoefficient`), and (§D) the
WALL's halves `firstHalf g.center M a`, `secondHalf g.center M a` with the leaf's `h₁ h₂ : Generic` and sizes
`(contactHalfSizes_bounds hn h.1.1).1.1 / .2.1` — the printed hypothesis discharge 800-835 LITERALLY: the half contact carrier
`Lᵢ` is a `Component hn'ᵢ hᵢ Tᵢ` of a decomposition `Tᵢ` of the generic half `λᵢ` (U110-B's output), the floor's domain.  The
floor `hF` enters ONLY through `FloorTheoremData.slot_le_of_signed` (§A, four wrappers); cb:singleton `hsing` ONLY through
`CbSingletonData.isolated_zero` (§E).  The printed case "if either `fᵢ = 0`" is vacuous in Lean (`cornerHomfly_ne_zero`) and is
never split on.  BLOCK's `s7k_*` names are NOT referenced (rule (3)); its outputs are consumed as the hypotheses `hrow`/`hext`
(`Ω_H − Ω_L = [a^{k_L+2ℓ−2}](f₁f₂) − [a^{k_L+2ℓ}](f₁f₂)`, the shape of `s7k_coefficient_difference` with `tl = twoLinking D_A i j`),
`hw` (writhe counts), `hR` (rotation identities), `hfH hfL` (mp:blocks products), `hu` (turn patterns).

| printed (sm-4) | block section / lemmas | status |
|---|---|---|
| 680-684 thm:floor at the two UNIFORM half contact carriers (`ε = 1`) | §A `s7j_floor_of_uniform` (via `signedUniformOrOneDissent_of_uniform`) | PROVED |
| 745-748 thm:floor at the two ONE-DISSENT half contact carriers (`ε = 0`): old turns `τ`, one contact turn `−τ` | §A `s7j_floor_of_dissent` (turn-pattern form), `s7j_floor_of_signed` (units C/I's shape) | PROVED |
| lp:core `knot_support`: no negative `z`-exponent (the `hz` inputs of `s7_corner_product`) | §A `s7j_z_nonneg` | PROVED |
| eq. s7c:interlacing-slot `k_L + 2ℓ = K`; s7c:noninterlacing-slot `K − k_L = 2ℓ + 2`; s7c:different-low/high-slot `k_L = K−2, k_H = K−4` | §B pure ℤ `s7j_interlacing_slot_int`, `s7j_noninterlacing_slot_int`, `s7j_different_slot_int`; §C at carriers `s7j_interlacing_slot`, `s7j_noninterlacing_slot`, `s7j_different_block_slots` | PROVED (omega) |
| **eq. s7c:interlacing-coefficient-result `Ω_H − Ω_L = −ω₁ω₂`** from the extracted row at `K−2, K` | §B `s7j_interlacing_entry` (Laurent), §C `s7j_interlacing_read` (carriers, `CarrierUniform`), `s7j_interlacing_row` (printed order: extraction at `k_L + 2ℓ` + writhe count + `\|R_L\| = \|R₁\|+\|R₂\|`), §D `s7j_interlacing_entry_at_halves` | PROVED |
| **eq. s7c:noninterlacing-extraction, `Ω_H − Ω_L = 0`** (reads `K−4, K−2` below the floor `K`) | §B `s7j_noninterlacing_entry`, `s7j_below_floor_entry`; §C `s7j_noninterlacing_read`, `s7j_below_floor_read`, `s7j_noninterlacing_row` (printed order); §D `s7j_noninterlacing_entry_at_halves` | PROVED |
| 785-813 different-block alternative `f_H = f_L = f₁f₂`, slots `K−4, K−2`, `Ω_H = Ω_L = 0` | §B `s7j_different_block_entry`; §C `s7j_different_block_read` (+ `s7j_different_block_slots` from `m_H = m₁+m₂+2`, `m_L = m₁+m₂`, `R₁+R₂−R_L = −1`, `R_H = R_L`); §D `s7j_different_block_entry_at_halves` | PROVED |
| 800-835 hypothesis discharge: `Lᵢ` a carrier of a decomposition of the generic half | §D `s7j_half₁_floor`, `s7j_half₂_floor` (thm:floor at `Component (contactHalfSizes_bounds hn h.1.1).i.1 hᵢ Tᵢ`) | PROVED (literal instances) |
| 777-781 "every old neighbour of `y` is a neighbour of selected `x`, hence dominated; `{y}` is an isolated block" | §E `s7j_isolated_of_neighbours_dominated` (via `neighbor_visit_owners_ne`: a neighbour of a selected crossing has its visits on different carriers) | PROVED |
| 781-783 cb:singleton at `T ∪ {x}`, owner uniform ⇒ `c(q) = 0`; "every one-newborn term is zero" | §E `s7j_singleton_entry`, `s7j_one_newborn_term_zero` (`wind S * cornerProduct S = 0`, selector-zero case by `carrierWeight_eq_zero_of_not_uniform`), `s7j_one_newborn_term_zero_insert` (at `insert x T` literally) | PROVED |

## 1. Proved (29 theorems; all inside `section VertexEdge`, sub-`section S7JFloor` with `variable {n₁ n₂ : ℕ} [NeZero n₁] [NeZero n₂]`)

§A `s7j_z_nonneg`, `s7j_floor_of_uniform`, `s7j_floor_of_dissent`, `s7j_floor_of_signed`;
§B `s7j_interlacing_slot_int`, `s7j_noninterlacing_slot_int`, `s7j_different_slot_int`, `s7j_interlacing_entry`,
`s7j_below_floor_entry`, `s7j_noninterlacing_entry`, `s7j_different_block_entry`;
§C `s7j_interlacing_read`, `s7j_noninterlacing_read`, `s7j_below_floor_read`, `s7j_different_block_read`,
`s7j_different_block_slots`, `s7j_interlacing_slot`, `s7j_noninterlacing_slot`, **`s7j_interlacing_row`**,
**`s7j_noninterlacing_row`**;
§D `s7j_half₁_floor`, `s7j_half₂_floor`, **`s7j_interlacing_entry_at_halves`**, **`s7j_noninterlacing_entry_at_halves`**,
**`s7j_different_block_entry_at_halves`**;
§E `s7j_isolated_of_neighbours_dominated`, **`s7j_singleton_entry`**, `s7j_one_newborn_term_zero`, `s7j_one_newborn_term_zero_insert`.

Accepted / ported inputs used: `FloorTheoremData.slot_le_of_signed`, `signedUniformOrOneDissent_of_uniform`,
`cornerHomfly_ne_zero`, `coeffAt_mul_eq_zero_of_lt_floor`, `CbSingletonData.isolated_zero` (SM.CornerChainStatements);
`s7_corner_product`, `s7c_signedUniformOrOneDissent_of_dissent` (SM.CornerChainUnits); `P_eq_homfly`, `P_knot_support`
(PolynomialBlock); `positiveLift_componentCount` (LinkPositiveLift); `cornerCoefficient_eq_coeffAt`, `cornerSlot`,
`cornerProduct` (CornerStateSum); `wind`, `carrierWeight_eq_zero_of_not_uniform` (CX1); `mem_carrierCrossings`
(CarrierCrossings); `mem_supportNeighbors` (InterlaceSupports); `neighbor_visit_owners_ne` (CarrierNeighborSeparation);
`crossing_visits_exist`, `visitTwin`; `contactHalfSizes_bounds`, `firstHalf`, `secondHalf` with the `NeZero` half-size
instances (ContactHalfSizes/Tuples/Indices); `WallGerm.BigonAt` (`h.1.1 : ContactSeparated M a`).

## 2. Unproved — the leaf, and what J does NOT do (exact estimates)

`s7_bigon_law_at` stays `sorry` (U110-K).  J delivers every floor/singleton ENTRY of bigon (5) as a theorem on explicit
hypotheses; the hypotheses themselves are the outputs of the other units and remain to be produced per eligible support:

1. **The extracted rows `hext`** (bigon (2)-(3), unit BLOCK): `c(L_H) − c(L_L) = [a^{k_L+tl−2}](H⁺_{L₁}H⁺_{L₂}) − [a^{k_L+tl}](…)`
   with `tl = twoLinking D_A i j`, from the skein triple, the R-II site and the two-component row — BLOCK's
   `s7k_coefficient_difference` has exactly this shape (its `ΩH, ΩL` are the `cornerCoefficient`s, its `Q₁ Q₂` the half
   lifts' values); the gluing is a one-line `exact` in K once both blocks sit in one file.  Its own inputs (the `BigonData`
   site with the reduced-record identification, the component record isos) are U110-A/B/F geometry: 3,500-5,400 lines per
   W3_BLOCK_REPORT §2.
2. **The counts and rotations `hw`, `hR`**: `m_L = m₁ + m₂ + tl − 1` / `+ tl` (crossing partition + `twoLinking`, U110-H
   `s7h_writhe_two_component` + BLOCK's `s7k_count_of_site`), `|R_L| = |R₁| + |R₂|` / `|R₁| + |R₂| − |R_L| = −1`
   (U110-I `s7i_carrierRotationInt_interlacing/_noninterlacing` on U110-C's live patterns) — available at the carrier level;
   the instantiation at the wall's contact carriers needs the family through the wall (W2_S7A2 §4(ii), est. 400-600 lines).
3. **The turn patterns `hu₁ hu₂`**: `CarrierUniform` of both half contact carriers in the interlacing branch
   (U110-C `s7c_uniform_halves_of_interlacing`), `SignedUniformOrOneDissent` in the noninterlacing branch
   (`s7c_dissent_halves_of_noninterlacing`, or `s7j_floor_of_dissent`'s turn-pattern form) — C's outputs, to be read at
   `Lᵢ` once B's corner correspondence exists (U_S7B §2.3, est. 400-600 lines).
4. **The domain data `T₁ hT₁ L₁ T₂ hT₂ L₂`** at the wall's halves (§D's parameters): U110-B's half ↔ interval transport
   ("closing the interval at the cut closes the boundary successor of `T` into the carrier of the decomposition `Tᵢ` of
   `λᵢ`", sm-4:817-828) — U_S7B §2 "not started" for the bigon eligible bijection; est. 1,500-2,200 lines (W3_BLOCK §2.1).
5. **The singleton entry's `hy`, `hdom`** at `insert x T` on the side polygon: `y ∈ carrierCrossings (insert x T) q` and
   "every unselected old neighbour of `y` interlaces `x`" — F's eligible-support combinatorics (sm-4:777-779: `x` adjacent
   to neither `T` nor `y`; eq. s7c:bigon-words-eq for the common-neighbour property); est. 200-400 lines.
6. **The different-block products `hfH hfL`**: `H⁺_{L_H} = H⁺_{L_L} = H⁺_{L₁}H⁺_{L₂}` from mp:blocks with the two singleton
   newborn blocks (`SM.blocks.product`, `curl_block_value`) — U110-H/B, est. 300-500 lines.

Total remaining for the bigon leaf (unchanged from W3_BLOCK §2): **3,500-5,400 lines**, all geometry/bookkeeping (A/B/F/K);
no floor, singleton, skein or record content is left.  Not attempted here (out of scope, not blocked): everything in 1-6.

## 3. Black boxes — what this unit consumes from other units (rule (3))

No `s7j_` declaration is `sorry`: every consumed output is a HYPOTHESIS of the theorem that uses it, in the printed proof's own
vocabulary, each with its supplier:

* `hrow` / `hext` — the extracted rows eq. s7c:interlacing-extraction / s7c:noninterlacing-extraction (Laurent form with
  `K = k₁ + k₂`, or the raw form at `k_L + tl` with `tl = 2ℓ`) [unit BLOCK `s7k_coefficient_difference` +
  `s7k_high_slot`; U110-G/H].
* `hw` — the writhe counts eq. s7c:interlacing-writhe-row / s7c:noninterlacing-writhe / s7c:different-polynomials
  [U110-H + crossing partition]; `hR`, `hRH` — eqs. s7c:interlacing-absolute / s7c:noninterlacing-rotation /
  s7c:full-rotation [U110-I/A2].
* `hu₁ hu₂` — `CarrierUniform` (interlacing) / `SignedUniformOrOneDissent` (noninterlacing, different-block) of the half
  contact carriers [U110-C].
* `T₁ hT₁ L₁ T₂ hT₂ L₂` — the half contact carriers as carriers of decompositions of the generic halves [U110-B].
* `hfH hfL` — the mp:blocks products of the different-block alternative [U110-H/B].
* `hS` (the support `insert x T`), `hy`, `hdom` — the one-newborn support data [U110-F].
* WALL-LEVEL existence of these data for the eligible supports of `g.sideTuple b t` is NOT stated (it needs U110-F's
  eligible-bijection vocabulary, which does not exist yet); the §D theorems are the target shapes at the leaf's halves.

## 4. Defects / observations

* None of the printed intermediates used here is false as stated.  Two printed case splits are vacuous in Lean and were
  dropped without loss: "if either `fᵢ = 0`" (`cornerHomfly_ne_zero`) and "including the zero-polynomial case" of
  cb:singleton (the field `isolated_zero` has no such case).
* The printed "test `W_T` and `U_sp`" (sm-4:654-660) — the rotation identity `R_L = R₁ + R₂` is only available when the full
  selector is nonzero — is NOT a case split inside the entries: `hR` is a hypothesis, and K performs the selector split at
  the term level (BLOCK's `s7k_interlacing_term` / `s7k_noninterlacing_term`, pure ℤ).  J's `s7j_one_newborn_term_zero`
  does contain its own selector split (uniform ⇒ cb:singleton; not uniform ⇒ `wt = 0`), as printed at 781-783.
* `s7j_isolated_of_neighbours_dominated` exempts `c' = y` in `hdom` (the printed "old neighbour" excludes the newborn); the
  proof needs only `c' ≠ y` from the isolation goal, so nothing is lost and K need not prove `¬ Interlaces y y`.
* The `ε = 0` one-dissent floor is offered in two shapes: `s7j_floor_of_dissent` (explicit `τ`, contact corner `j₀`, the
  printed 745-748 sentence) and `s7j_floor_of_signed` (the `SignedUniformOrOneDissent` shape units C/I return); both are
  one-line wrappers of `slot_le_of_signed`, kept so K can use whichever C delivers.

## 5. Mathlib / Lean pitfalls met (v4.34.0-rc2 pin)

1. `turn (ccpCornerPolygon hn hP S q) j` indexes `ZMod (ccpCornerCount hn hP S q)`, not `ZMod 3` (first compile error;
   the corner polygon has as many corners as the carrier has marks).
2. `omega` closes every slot identity after `unfold cornerSlot` with `|carrierRotationInt …|` and the ℕ-cast counts as
   atoms; `push_cast` is needed only when a hypothesis rewrites a `carrierCrossingCount` sum under the cast
   (`s7j_different_block_slots`), not when the count identity is already stated in ℤ (`s7j_interlacing_slot`).
3. `rw [hK] at hext` rewrites both `cornerSlot qL + tl - 2` and `cornerSlot qL + tl` at once (the former is
   `HSub.hSub (cornerSlot qL + tl) 2` syntactically), so the composite rows need no auxiliary equations.
4. `mem_supportNeighbors hn hP S y : y ∈ supportNeighbors ↔ ∃ x ∈ S, Interlaces hn hP y x` takes `hP` explicitly and builds
   its own `NeZero` — usable under the frozen `variable {n} [NeZero n]` without adjustment.
5. `(visitTwin v).1 = v.1` is `rfl` (`visitTwin v := ⟨v.1, …⟩`), so the two owner equalities from `mem_carrierCrossings`
   compose by `.trans … .symm` exactly as in `sg_isolated_undominated`.

## 6. Notes for the assembler

* Position: the block starts with `/-! ### Unit J (wave 3, prefix `s7j_` …` (line 37) and ends with `end S7JFloor` (line 507),
  inside `section VertexEdge`, immediately before the bigon leaf's docstring; it opens its own `section S7JFloor` with
  `variable {n₁ n₂ : ℕ} [NeZero n₁] [NeZero n₂]` (closed before the leaf, so the frozen statements see no extra variables).
  All names `s7j_`-prefixed; no `def`, no structure, no instance.
* Consumption by K, per eligible support of the bigon sector: interlacing — `s7j_interlacing_row hF hn hPH hPL hSH hSL qH qL
  hn₁ hn₂ hP₁ hP₂ hS₁ hS₂ q₁ q₂ hu₁ hu₂ (twoLinking DA i j) hext hw hR` (or `s7j_interlacing_entry_at_halves` when `q₁ q₂` are
  literally `L₁ L₂` at `firstHalf/secondHalf g.center M a`); noninterlacing — `s7j_noninterlacing_row … hu₁ hu₂ tl hext hw hR`;
  one-newborn — `s7j_one_newborn_term_zero_insert hsing hn hP T x y hS q hy hdom`; different-block —
  `s7j_different_block_entry_at_halves … hfH hfL hmH hmL hR hRH hu₁ hu₂`.  Merging with BLOCK: BLOCK's
  `s7k_coefficient_difference` output is J's `hext` with `tl := twoLinking DA i j` (one `exact`); BLOCK's own `s7k_*_row`s
  and J's `s7j_*_row`s prove the same conclusions from different hypothesis shapes — keep both or either; no clash.
* Diff summary: `+` 473 lines, `−` 0 lines.  Reproduce: `cp W3_Skeleton.lean W3_J.lean`, insert the block after line 36,
  `cd work/lean && lake env lean ../drafts/corner/W3_J.lean`.
