# U_S7C_REPORT — unit U110-C (helper unit, prefix `s7c_`), 2026-09-15

File: `work/drafts/corner/U_S7C.lean` (byte-identical copy of `Statements_FINAL.lean` plus ONE inserted block, lines
455-1120, immediately before the docstring of `s7_sliding_law_at`, the first leaf that consumes these helpers;
`diff Statements_FINAL.lean U_S7C.lean` = `454a455,1120`, a pure insertion of 666 lines — no frozen definition,
statement, name or docstring touched, no import added).
Check: `cd work/lean && lake env lean ../drafts/corner/U_S7C.lean`: **0 errors, 0 non-sorry warnings**, 14
`declaration uses sorry` warnings = exactly the other units' leaves and the §6 row theorems (lines 208, 223, 243, 1124,
1142, 1157, 1165, 1286, 1296, 1307, 1402, 1407, 1412, 1417); 15.3 s warm. `grep -c sorry`: 16 before, 16 after (this
unit owns no leaf; 16 = 14 declarations + 2 mentions in comments).
Axioms (`#print axioms` on a scratch copy with the same statements): every one of the 49 `s7c_` declarations depends on
[propext, Classical.choice, Quot.sound] only (`s7c_forall_add_singleton`: [propext, Quot.sound]) — no `SM.lit_homfly`,
`SM.lp_lm`, `SM.lp_lm_uniqueness`; the row assembly's expected list is unaffected.

## Content (PLAN_FINAL §3.3: sliding item (3), bigon items (1) triangle and (5) selectors; §4 row U110-C)

Design. lem:C-X1's `wt(L) = carrierWeight hn hP S q` (CX1.lean:24) equals the accepted `cornerSelector` of the corner
polygon (cor:flat-carriers (iii), FlatCarriersDefs.lean:466 — available; CS3's `carrierWeight_eq_cornerSelector` is not
imported, so re-proved as `s7c_carrierWeight_eq_cornerSelector`) and depends on the polygon only through the MULTISET of
its turns and the corner count. So the algebra is proved ONCE on `Multiset SignType` (`s7c_sel`), and read back on carriers
of DIFFERENT polygons (a side polygon and the two halves, three different `n`) through corner bijections. Nothing is
divided; every identity holds "including all zero cases" as printed.

All 49 declarations PROVED (2 defs + 47 theorems; ~600 lines with docstrings, the plan's budget):

| group | declarations | printed source |
|---|---|---|
| multiset selector | `s7c_turns Q := univ.val.map (turn Q)`, `s7c_sel m := if ∀ x ∈ m, x = -1 then 1 else if ∀ x ∈ m, x = 1 then (-1)^card m else 0`; `s7c_sel_of_forall_neg/_pos`, `s7c_sel_of_forall` (`= (-σ)^card` for uniform sign `σ ≠ 0`), `s7c_sel_eq_zero_of_ne`, `s7c_sel_eq_zero_of_zero_mem`, `s7c_sel_ne_zero_iff` (`≠ 0 ↔ ∃ σ ≠ 0, ∀ x ∈ m, x = σ`), `s7c_sel_add_singleton_ne_zero` (`sel (m + {σ}) ≠ 0 → ∀ x ∈ m, x = σ`), `s7c_forall_add_singleton`, sign trivia `s7c_neg_sign_ne_zero`, `s7c_sign_ne_neg_self`, `s7c_neg_sign_pow_ne_zero`, `s7c_exists_ne_of_not_forall` | lem:C-X1 |
| **eq. s7c:short-selector** | `s7c_sel_refine (hη : η ≠ 0) (hmem : η ∈ m) : s7c_sel (m + {τ}) = if τ = η then -(η:ℤ) * s7c_sel m else 0` | sm-4:365-381 |
| **eq. s7c:sliding-selector-difference** | `s7c_sliding_difference_of_table` (pure ℤ: from the two table rows, `Q h_s c_{−s} − Q c_s h_{−s} = s (Q h_s h_{−s})`; needs `s ≠ 0`, `τ ≠ 0`); `s7c_sliding_selector_difference (Qsp) (m₁ m₂) (hs) (hτ) (h₁ : s ∈ m₁) (h₂ : -s ∈ m₂) : Qsp * sel m₁ * sel (m₂ + {τ}) - Qsp * sel (m₁ + {τ}) * sel m₂ = s * (Qsp * sel m₁ * sel m₂)` = `W₊ − W₋ = s W₁W₂` with eq. s7c:sliding-selector-factors | sm-4:382-393 |
| **eq. s7c:interlacing-selector** | `s7c_sel_interlacing (hs₀ : s₀ ≠ 0) : s7c_sel (m₁ + m₂ + {s₀}) = -(s₀:ℤ) * (s7c_sel (m₁ + {s₀}) * s7c_sel (m₂ + {s₀}))`; live row `s7c_uniform_of_interlacing` (`≠ 0 →` all of `m₁`, `m₂` are `s₀`) | sm-4:556-575 |
| **eq. s7c:noninterlacing-selector** | `s7c_sel_noninterlacing (hs₀) (hne : m₁ ≠ 0 ∨ m₂ ≠ 0) : s7c_sel (m₁ + m₂ + {-s₀}) * (s7c_sel (m₁ + {s₀}) * s7c_sel (m₂ + {s₀})) = 0`; live row `s7c_dissent_of_noninterlacing` (`≠ 0 →` all of `m₁`, `m₂` are `−s₀`: the halves are one-dissent) | sm-4:576-585, 742-747 |
| **eq. s7c:triangle-data** `wt = s₀` | `s7c_sel_triangle : s7c_sel (replicate 3 (-s₀)) = s₀`; on a carrier `s7c_carrierWeight_triangle (h3 : ccpCornerCount = 3) (h : ∀ j, turn … = -s₀) : carrierWeight = s₀` | sm-4:437-447 |
| bridge to carriers | `s7c_card_turns`, `s7c_mem_turns`, `s7c_forall_turns`, `s7c_cornerSelector_eq_sel`, `s7c_carrierWeight_eq_cornerSelector`, `s7c_carrierWeight_eq_sel`, `s7c_carrierWeight_of_uniform_sign` (`= (-σ)^k(L)`), `s7c_carrierWeight_eq_zero_of_ne` / `_of_opposite` (eq. s7c:one-newborn-turns: two corners of different turns ⇒ `wt = 0`), `s7c_carrierUniform_of_weight_ne_zero`, `s7c_turn_eq_of_weight_ne_zero`, `s7c_forall_turn_of_weight_ne_zero` (live selector + one corner of turn `σ` ⇒ all turns `σ`) | lem:C-X1, sm-4:695-706 |
| floor patterns (§0) | `s7c_signedUniformOrOneDissent_of_forall`, `s7c_signedUniformOrOneDissent_of_dissent (j₀) (h0 : turn Q j₀ = -τ) (h : ∀ j ≠ j₀, turn Q j = τ)` | sm-4:765-769 |
| multiset transport | `s7c_turns_eq_erase_add Q j : s7c_turns Q = (univ.erase j).val.map (turn Q) + {turn Q j}`; `s7c_map_univ_eq_of_equiv (t t') (e : α ≃ β) (h : ∀ x, t' (e x) = t x)`; `s7c_map_erase_eq_map_subtype` (`univ.erase j` as `{i // i ≠ j}`); `s7c_map_univ_sum` (`Sum.elim` over `α ⊕ β`); `s7c_exists_ne (2 ≤ k) j`; `s7c_map_subtype_ne_zero` | — |
| **carrier-level laws through corner bijections** | `s7c_carrierWeight_refine`: `q` has a corner `j` of turn `τ`, `e : {i // i ≠ j} ≃ ZMod k₁` turn-preserving onto ALL corners of the half carrier `q₁`, which has a corner `jη` of sign `η ≠ 0` ⇒ `carrierWeight q = if τ = η then -(η:ℤ) * carrierWeight q₁ else 0` (the sliding refinement, eq. s7c:short-direction-lists); `s7c_turns_of_halves`: `e : {i // i ≠ j₁} ⊕ {i // i ≠ j₂} ≃ {i // i ≠ j}` turn-preserving ⇒ `s7c_turns Q = (univ.erase j₁).map turn Q₁ + (univ.erase j₂).map turn Q₂ + {turn Q j}`; `s7c_carrierWeight_interlacing` (contact turns `s₀, s₀, s₀` ⇒ `wt(q) = -s₀ (wt q₁ wt q₂)`); `s7c_carrierWeight_noninterlacing` (contact turns `-s₀, s₀, s₀`, a half with `≥ 2` corners ⇒ `wt(q) (wt q₁ wt q₂) = 0`); `s7c_uniform_halves_of_interlacing` (`wt q ≠ 0` ⇒ all three carriers have every turn `s₀`); `s7c_dissent_halves_of_noninterlacing` (`wt q ≠ 0` ⇒ `q` uniform of sign `−s₀`, each half has turns `−s₀` off its contact corner, and BOTH `SignedUniformOrOneDissent (ccpCornerPolygon … qᵢ)` — the floor's input at the half contact carriers) | sm-4:540-585, 655-660, 742-750 |

## Interface notes for the consumers (U110-E sliding, U110-F triangle, U110-J/K bigon) and the assembler

- Geometry the wrappers expect (all from sm-4:343-357 and 540-551). Sliding: on the side polygon the carrier through the
  short edge has direction list `(r, u_in, u_out)` vs the half's `(r, u_out)`: its corner at `μ_M` has turn `τ`, its
  smoothing corner at `x₋` has turn `sgn det(r, u_in) = η` (eq. s7c:sliding-signs), all other corners are the half's —
  so `e` sends the `x₋`-corner to the half's contact corner (both turn `η`) and is the identity elsewhere; the multiset of
  turns is `turns(half) + {τ}` exactly. Bigon: the full contact carrier `L*` has one contact corner (turn `s₀`
  interlacing / `−s₀` noninterlacing); each half `Lᵢ` has one contact corner of turn `s₀`; the noncontact corners of
  `L*` are the disjoint union of the halves' noncontact corners — `e` is that bijection.
- The multiset level is available if a consumer's correspondence is not an `Equiv` of subtypes: rewrite with
  `s7c_carrierWeight_eq_sel`, split contact corners off with `s7c_turns_eq_erase_add`, transport with
  `Multiset.map_eq_map_of_bij_of_nodup` (Mathlib) or `s7c_map_univ_eq_of_equiv`, then apply the `s7c_sel_*` law.
- `s7c_sel_refine` / `s7c_carrierWeight_refine` do NOT need `τ ≠ 0` (for `τ = 0` both sides are `0`); the ℤ table
  lemma `s7c_sliding_difference_of_table` does need `s ≠ 0`, `τ ≠ 0` (both are given: `vertex_contact_signs`, lem:carriers
  (ii) turns nonzero).
- `s7c_carrierWeight_noninterlacing` needs a half with `≥ 2` corners: `(carriers_lemma hnᵢ hPᵢ hSᵢ).corner_polygons.2.2.1 qᵢ`
  gives `3 ≤ ccpCornerCount` (or `ccpCornerCount_ge_three hn hP hS q`, `IsDecomposition` unfolds to
  `S ∈ independentSupports`).
- Spectator products: `wind hn hP S = ∏ q, carrierWeight …` (`C_X1.wind_eq`, `rfl`); the split `W = Q_sp · wt(L*)` /
  `Q_sp · wt(L₁) wt(L₂)` of eq. s7c:selector-owners is product bookkeeping over the carrier bijections of U110-A/B
  (`Finset.prod_erase_mul`, `Fintype.prod_equiv`) — not this unit's; `s7c_sliding_selector_difference` takes `Q_sp : ℤ`
  abstractly, as printed ("without assuming it nonzero").
- Assembler: `s7c_carrierWeight_eq_cornerSelector` duplicates SM/CS3.lean:1453 (`carrierWeight_eq_cornerSelector`) under
  a different name because CS3 is not among the frozen imports; if CS3 is imported at port time it can be replaced by
  the accepted one (no clash).
- Nothing believed false; no missing hypothesis found. The two printed selector tables and both bigon selector
  identities are literally true as stated once "turns of `L*` = noncontact turns of the halves + one contact turn" is
  the hypothesis (the printed sentence "All noncontact turns partition between the halves").
- U110-G GO/NO-GO: not this unit's content (no RI/RII witnesses touched); see U_S7G_REPORT.md.

## Mathlib / Lean pitfalls hit (v4.34.0-rc2 pin)

1. `if_pos` / `if_neg` are deprecated → use `ite_eq_left h` / `ite_eq_right hn` (as CX1.lean does); `push_neg` is
   deprecated (→ `push Not`); avoided with the 5-line `s7c_exists_ne_of_not_forall`.
2. **Deterministic `whnf` timeout (200000 heartbeats)** when passing an UN-annotated lambda `fun x => turn Q x.1` over
   `{i : ZMod (ccpCornerCount hn hP S q) // i ≠ j}` to a lemma with an explicit function argument: Lean tries to
   reduce `ZMod (ccpCornerCount …)` (a Nat that does not reduce) to resolve the projection. Fix: annotate the binder
   `fun x : {i : ZMod (ccpCornerCount hn hP S q) // i ≠ j} => …`. Consumers constructing `e`/`he` should do the same.
3. `s7c_map_univ_eq_of_equiv _ _ e he` cannot infer `t'` from `he : ∀ x, t' (e x) = …` (`?t' (e x)` is not a
   higher-order pattern) — pass `t'` explicitly.
4. `Finset.mem_val` is stated as a Prop EQUALITY `(a ∈ s.val) = (a ∈ s)` (no `.mp`); use `Finset.mem_def : a ∈ s ↔ a ∈ s.val`.
5. `rw [Multiset.card_add, Multiset.card_add, …]` rewrites one instance family per step and can leave a `card (m + {σ})`
   behind; use `simp only [Multiset.card_add, Multiset.card_singleton]`.
6. In `rw [h]` inside a `by` block whose expected type still has metavariables (`{i j}` implicit in
   `s7c_carrierWeight_eq_zero_of_ne`), the rewrite unifies BOTH metavariables with the same corner — state the
   inequality in a `have` first.
7. `Multiset.map_eq_map_of_bij_of_nodup` (MapFold.lean:472) is the right tool to transport multisets along bijections
   between DIFFERENT index types; `Multiset.map_disjSum`/`Finset.val_disjSum`/`Finset.univ_disjSum_univ` (rfl) handle
   `α ⊕ β`; `Multiset.map_univ_val_equiv` exists in namespace `Multiset` (not `Finset`).
8. `rfl` closing `univ.val.map (turn Q) + {τ} = s7c_turns Q + {τ}` is fine (unfolds the def, no reduction of `ZMod`).

## Left

Nothing of this unit. Not touched (other units): `sg_isolated_undominated` (U103-A), `sg_daughters_products` (U103-D),
`sg_daughters_rotation` (U103-E), `s7_sliding_law_at` (U110-E), `s7_bigon_law_at` (U110-K), `s7_universal_extraction`
(U110-G), `s7_corner_product` 2nd conjunct (U110-J), `sft_same_sign`/`sft_mixed`/`sft_loop` (U112), the §6 row theorems.
