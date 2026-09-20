# U_S7I_REPORT — unit U110-I (helper unit: the contact rotation ledger; prefix `s7i_`), 2026-09-15

File: `work/drafts/corner/U_S7I.lean` = byte-identical copy of `Statements_FINAL.lean` plus ONE inserted block
(lines 468-1299, 832 lines), placed inside `section VertexEdge` immediately before the docstring of
`s7_bigon_law_at` — the first leaf that consumes these helpers (U110-K's assembly; U110-J's slot bookkeeping).
`diff Statements_FINAL.lean U_S7I.lean` = `467a468,1299`: a pure insertion, 0 deleted lines; no definition, structure,
statement, name or docstring of the frozen file touched; no import added.
Check: `cd work/lean && lake env lean ../drafts/corner/U_S7I.lean`: **0 errors, 0 non-sorry warnings**, 14
`declaration uses sorry` warnings = exactly the other units' 10 leaves and the 4 §6 row theorems (lines 208, 223, 243,
458, 1308, 1323, 1331, 1452, 1462, 1473, 1568, 1573, 1578, 1583); 13 s warm. `grep -c sorry`: 16 before, 16 after
(this unit owns no leaf; 16 = 14 declarations + 2 prose mentions).
Axioms (`#print axioms` on a scratch copy with identical statements): every `s7i_` declaration checked
(`s7i_rotationNumber_constant_Icc`, `s7i_full_rotation_germ`, `s7i_carrierRotation_sides_of_family`, `s7i_contact_ledger`,
`s7i_ledger_of_int`, `s7i_rotation_ledger_interlacing/_noninterlacing`, `s7i_interlacing_absolute`,
`s7i_noninterlacing_absolute`, `s7i_carrierRotationInt_interlacing/_noninterlacing`, `s7i_different_slot`,
`s7i_principalTurn_eq_of_edges_pos_smul`) depends on `[propext, Classical.choice, Quot.sound]` only — no `lit_homfly`,
`lp_lm`, `lp_lm_uniqueness`; the row assembly's expected axiom list is unaffected.
Clash scan: `grep -rn s7i_ work/lean/SM` empty; no other `U_*.lean` uses the prefix.

## Content (PLAN_FINAL §3.3 bigon item (4); §4 row U110-I: eq. s7c:full-rotation, eq. s7c:rotation-ledger, the
`R`-identities), sm-4:483-503, 540-551, 587-598, 655-670, 748-762, 827-832

Design decision (load-bearing for the consumers).  The ledger is stated on REGULAR LABELLED POLYGONS of three
different sizes (the corner polygons of the full contact carrier `L*` and the halves `L₁`, `L₂`), with the SAME corner
correspondence U110-C uses (`e : {i // i ≠ j₁} ⊕ {i // i ≠ j₂} ≃ {i // i ≠ j}`, `he` in `Sum.elim` form) — but `he` is
required to preserve the PRINCIPAL turn (`principalTurn`, the real angle), not only the sign.  With that, NO explicit
angle computation is needed: the three rotation numbers are integers (`rotationNumber_integer`), so the signed
combination of the three contact turns `ϑ_{j₁} + ϑ_{j₂} − ϑ_j` is a multiple of `2π`; each contact turn lies in `(−π, π)`
(`principalAngle_bounds`) and has the sign of its `turn` (`principalTurn_sign`); the two half contact turns have sign
`s₀`, the full one `s₀` (interlacing) or `−s₀` (noninterlacing); the multiple is then forced to `0`, resp. `s₀`
(`s7i_ledger_of_int`).  This is exactly the printed argument's content ("Dividing by 2π gives the signed identity …
unsigned angles would not give this formula") with the explicit `β`, `π − α`, `β − α ∓ π` replaced by their signs and
bounds; the explicit vector-level version is ALSO proved (`s7i_contact_ledger`) for the consumer who identifies the
contact turns geometrically.  `principalTurn`-preservation implies U110-C's `turn`-preservation
(`s7i_turn_elim_of_principalTurn_elim`, `s7i_carrier_turn_elim`), so ONE hypothesis `he` serves both units.

All 49 declarations PROVED (1 def + 48 theorems; 832 lines with docstrings, the plan's ~900 budget):

| group | declarations | printed source |
|---|---|---|
| **eq. s7c:full-rotation** (lem:rot (ii) through the wall) | `s7i_rotationNumber_constant_Icc` (a `k`-gon family continuous on `[a,b]`, regular at every parameter INCLUDING the wall ⇒ one rotation number); `s7i_germIcc` (+ `_continuous`, `_left`, `_right`: the inclusion `[−t, t] ↪ g.Parameter` hitting `g.sideTime false/true t`); `s7i_full_rotation_germ` (`f : g.Parameter → LabelledTuple k`, `ContinuousOn f {u ∣ ∣u.val∣ ≤ t.val}`, regular there ⇒ `rot (f (sideTime false t)) = rot (f (sideTime true t))`); `s7i_full_rotation_germ_centre` (either side value = the centre value `f g.zeroParameter`, i.e. `rot(L_L) = rot(L_H) = rot(L*)`); `s7i_carrierRotation_sides_of_family` (read on `carrierRotation` of the two side carriers `q₋`, `q₊` whose corner polygons are, up to `recastTuple`, the side values of the family) | sm-4:493-503 |
| contact geometry (vector level) | `s7i_det_neg_left/_right`, `s7i_det_zero_left/_right`, `s7i_regularPair_of_det_ne_zero`; `s7i_contact_angle_sum` (the three contact turns `r → w₂`, `−w₁ → r`, `−w₁ → w₂` sum to `0` in `Real.Angle`), `s7i_contact_angle_sum_int`; `s7i_contact_sign_half₁/₂` (both half contact turns have the sign of `det(r, w₂)`, `det(r, w₁)` = `s₀`), `s7i_contact_sign_full` (the full contact turn has sign `−sgn det(w₁, w₂)`); **`s7i_contact_ledger`** (both neighbours on side `s₀` of the remote line, `det(w₁,w₂) ≠ 0`: if `sgn det(w₁,w₂) = −s₀` [interlacing, `β < α`] the full sign is `s₀` and `θ₁ + θ₂ − θ* = 0`; if `= s₀` [noninterlacing] the full sign is `−s₀` and `θ₁ + θ₂ − θ* = 2π s₀`); `s7i_contact_dichotomy`, `s7i_sign_cases_of_ne_zero` (eq. s7c:angle-orders as a dichotomy) | sm-4:540-551 |
| the ledger as arithmetic | `s7i_signType_cases`, `s7i_neg_signType_ne_zero`; **`s7i_ledger_of_int`** (three angles in `(−π,π)`, combination a multiple of `2π`, first two of sign `s₀`: sign `s₀` of the third ⇒ `0`; sign `−s₀` ⇒ `2π s₀`) | sm-4:587-598 |
| edges → turns (bridge for `he` and for the contact turns) | `s7i_principalTurn_eq_of_pos_smul` (edges `c•u`, `d•v`, `c,d>0` ⇒ `ϑ = principalAngle u v`, via `principalAngle_smul`), `s7i_turn_eq_of_pos_smul` (`turn = sgn det(u,v)`), `s7i_principalTurn_eq_of_edges_pos_smul` (two corners of two polygons with edges equal up to positive rescaling have equal principal turns — `he` corner by corner), `s7i_principalTurn_eq_of_edges_eq` | lem:carriers (ii), `corner_polygons.2.1` |
| **eq. s7c:rotation-ledger** on polygons | `s7i_principalTurn_bounds`, `s7i_sum_principalTurn_split` (`Σϑ = Σ_{i≠j} ϑ + ϑ_j`), `s7i_ledger_sum` (`Σϑ(Q₁)+Σϑ(Q₂)−Σϑ(Q) = ϑ_{j₁}+ϑ_{j₂}−ϑ_j` through `e`), `s7i_rotation_ledger_sum` (`rot Q₁ + rot Q₂ − rot Q = (ϑ_{j₁}+ϑ_{j₂}−ϑ_j)/2π`), `s7i_ledger_int` (∃ m : ℤ with both forms), `s7i_turn_elim_of_principalTurn_elim`; **`s7i_rotation_ledger_interlacing`** (contact turns `s₀, s₀, s₀` ⇒ `rot Q₁ + rot Q₂ − rot Q = 0`), **`s7i_rotation_ledger_noninterlacing`** (`s₀, s₀, −s₀` ⇒ `= (s₀ : ℝ)`) | sm-4:587-598 |
| **`R`-identities** (lem:uniformrot) | `s7i_rotation_on_ray_of_uniform` (all turns `τ` ⇒ `1 ≤ τ·rot ∧ ∣rot∣ = τ·rot`), `s7i_rotation_on_ray_of_dissent` (one turn `−τ`, rest `τ` ⇒ same); **`s7i_interlacing_absolute`** (three uniform carriers of sign `s₀`, `3 ≤ k`'s ⇒ `∣rot Q∣ = ∣rot Q₁∣ + ∣rot Q₂∣`, eq. s7c:interlacing-absolute `R_L = R₁ + R₂`); **`s7i_noninterlacing_absolute`** (full carrier uniform of sign `−s₀`, halves one-dissent at their contact corners ⇒ `∣rot Q₁∣ + ∣rot Q₂∣ − ∣rot Q∣ = −1`, eq. s7c:noninterlacing-rotation) | sm-4:655-663, 748-757 |
| on carriers (def:uniform / def:C) | `s7i_carrier_turn_elim` (U110-C's `he` from the principal one on `ccpCornerPolygon`s of carriers of decompositions), `s7i_carrierRotation_ledger_interlacing/_noninterlacing` (`carrierRotation`, real), **`s7i_carrierRotationInt_interlacing`** (`∣rInt q∣ = ∣rInt q₁∣ + ∣rInt q₂∣` in ℤ, from `hall` patterns — the output shape of `s7c_uniform_halves_of_interlacing`), **`s7i_carrierRotationInt_noninterlacing`** (`∣rInt q₁∣ + ∣rInt q₂∣ − ∣rInt q∣ = −1`, from the patterns `s7c_dissent_halves_of_noninterlacing` returns); regularity and `3 ≤ ccpCornerCount` from `hS : IsDecomposition` via `ccpCornerPolygon_regular`, `ccpCornerCount_ge_three`, casts by `carrierRotationInt_cast` | sm-4:655-663, 748-757 |
| slot identities (pure ℤ, `omega`) | `s7i_high_slot` (`k_H = k_L − 2`), `s7i_interlacing_slot` (`k_L = K − 2ℓ`), `s7i_noninterlacing_slot` (`K − k_L = 2ℓ + 2`), `s7i_different_slot` (`k_L = K − 2 ∧ k_H = K − 4`) | sm-4:629-632, 665-670, 758-762, 827-832 |

## Interface notes for the consumers (U110-A/B geometry, U110-J floor rows, U110-K assembly) and the assembler

- Sign conventions, verified against the printed normalisation (`r = (1,0)`, both neighbours above, `s₀ = +1`): `w₁ =
  μ_{M−1} − μ_M`, `w₂ = μ_{M+1} − μ_M`; `s₀ = sgn det(r, w₁) = sgn det(r, w₂)`; half 1's contact corner turns `r → w₂`
  (`β`), half 2's `−w₁ → r` (`π − α`), the full carrier's `−w₁ → w₂` (the polygon's own corner at `M`, `β − α ∓ π`).
  INTERLACING (`ε = 1`) ⟺ `sgn det(w₁, w₂) = −s₀` ⟺ the full contact turn has the sign `s₀` of the half contact turns
  (this matches sm-4:679-682, "Interlacing means `hv − uk > 0`" with `(u,h) = w₁`, `(v,k) = w₂`).  NONINTERLACING ⟺
  `sgn det(w₁, w₂) = s₀` ⟺ full contact sign `−s₀`.  Consumers may take the dichotomy from the turn sign of the full
  carrier's contact corner alone (`s7i_rotation_ledger_*` take `hj : turn Q j = ±s₀`), never from the explicit angles.
- The ledger lemmas need `Regular` for all three polygons (lem:carriers (ii), `ccpCornerPolygon_regular` on
  decompositions; the carrier versions take `hS hS₁ hS₂ : IsDecomposition`) and the PRINCIPAL-turn-preserving `he`.
  U110-B produces `he` from "inherited corner edges are positive multiples of the same original edges" via
  `s7i_principalTurn_eq_of_edges_pos_smul` (or `_of_edges_eq` when the corner polygons literally share the edges at the
  centre), one corner at a time (`rintro (y | y)` on `x`, then `Sum.elim_inl/inr` are `rfl`).  The SignType `he` U110-C's
  selector laws want is `s7i_carrier_turn_elim … e he`, so the two units share one `e`/`he`.
- eq. s7c:full-rotation: `s7i_full_rotation_germ` expects the consumer's family `f : g.Parameter → LabelledTuple k` of
  corner polygons of the full contact carrier (built by U110-A's persistent-crossing transport), continuous and regular
  on `|u| ≤ t` — the corner polygon at the centre `u = 0` is regular by the printed argument (positive edge lengths,
  nonzero turn determinants at `M`, sm-4:495-500); the two side values are `recastTuple`s of `ccpCornerPolygon`s
  (`s7i_carrierRotation_sides_of_family` does the recast bookkeeping, `rotationNumber_recastTuple`).  If the consumer
  prefers a `unitInterval` path (CSilent's `silentPath` pattern), the accepted `rotationNumber_family_constant` applies
  directly and nothing here is needed.
- The `R`-identities on `carrierRotationInt` (`s7i_carrierRotationInt_*`) plug into the slot identities: `cornerSlot =
  1 − m − |rInt|` (def:C) with `m = w` of the positive lift (`positiveLift_writhe_eq_carrierCrossingCount`,
  LinkPositiveLift.lean:820) and the writhe counts of U110-H give `hkL hk₁ hk₂ hw`; `s7i_interlacing_slot` then yields
  `k_L = K − 2ℓ`, `s7i_noninterlacing_slot` `K − k_L = 2ℓ + 2`, `s7i_different_slot` `k_L = K − 2 ∧ k_H = K − 4`.
- Nothing believed false; no missing hypothesis found.  The only hypothesis the printed text leaves implicit and these
  statements make explicit is `3 ≤ k` for each carrier in the `R`-identities (lem:uniformrot's domain; the printed
  "Every carrier used here has at least three corners", sm-4:586-591; on carriers it is `ccpCornerCount_ge_three`).
- U110-G GO/NO-GO: not this unit's content (no RI/RII witnesses touched); see U_S7G_REPORT.md.

## Mathlib / Lean pitfalls hit (v4.34.0-rc2 pin)

1. `rw [← Fintype.sum_sum_type]` fails on a target `∑ x, f x.1 + ∑ x, g x.1` (higher-order pattern `?f (Sum.inl a)` does
   not unify); go forward instead: `Fintype.sum_equiv e _ _ (fun x => (he x).symm)` on the `Sum.elim` sum, then
   `rw [Fintype.sum_sum_type]` and close by `rfl` (`Sum.elim f g (Sum.inl a) = f a` is definitional).
2. `neg_ne_zero` / `neg_eq_zero` do NOT apply to `SignType` (no `SubtractionMonoid`); prove `-σ ≠ 0` by
   `rcases s7i_signType_cases h with rfl | rfl <;> decide`.  `neg_neg` and `Left.sign_neg` DO work on `SignType`.
3. `omit [NeZero n] in` must precede the DOCSTRING, not sit between docstring and `theorem` (parse error "expected
   'lemma'").  Needed for the germ helpers that mention `g : WallGerm n` but not `NeZero n` (unusedSectionVars linter).
4. `push_neg` is deprecated → `push Not`; `haveI` for a `Prop` triggers the `haveILetI` linter → `have`.
5. `PreconnectedSpace (Set.Icc a b)` is not found by instance search; get it with
   `isPreconnected_iff_preconnectedSpace.mp isPreconnected_Icc`, then `ContinuousOn.comp_continuous` with
   `continuous_subtype_val` turns a `ContinuousOn` family into the `Continuous` one `rotationNumber_family_constant` wants.
6. `Finset.sum_subtype (Finset.univ.erase j) (fun i => by simp) f` produces the `{i // i ≠ j}` sum with the ambient
   `Fintype` instance and unifies with the statement's `∑ x : {i : ZMod k // i ≠ j}` without `convert`.
7. `linear_combination` coefficient signs: check the residual goal it prints (`2 − s₀² · 2 = 0` meant `+ hsq` should be
   `− hsq`).

## Left

Nothing of this unit.  Not touched (other units): `sg_isolated_undominated` (U103-A), `sg_daughters_products` (U103-D),
`sg_daughters_rotation` (U103-E), `s7_sliding_law_at` (U110-E), `s7_bigon_law_at` (U110-K), `s7_universal_extraction`
(U110-G), `s7_corner_product` 2nd conjunct (U110-J), `sft_same_sign`/`sft_mixed`/`sft_loop` (U112), the §6 row theorems.
