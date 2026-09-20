# R176_SMOOTH_REPORT — row 176 (R:extreme_transport), the SMOOTH unit: `s176_PortDataRest` items (T1) and (9)/(9a)

R176 SMOOTH prover (subagent), 2026-09-15.  Inputs: Site_176_REPORT.md (§3, §5, §6), U_R176_REPORT.md §5 (items 2–5),
RProof/RALedgers.lean 860–960 (`est_PortData`, the `est_` wall lemmas), RProof/GenericTransport.lean (`GT_carrierEquiv`,
`GT_tri_cases`), RProof/X1Rows3.lean (`GT_groupedPoly_eq_homfly`, `GT_homfly_wall_gen`, `GT_transportSupport_S`,
`GT_outsideSupports_transport`, `GT_fullAvail_transport`), CV/GroupedKnot.lean (`liftBlock`, `restrictTransfer`,
**`liftRestrictRecordIso`**, `arcBetween_iff_key`, `carrierDiagram`), CV/PieceIntrinsic.lean (`liftVisit`, `liftVisit_twin`,
`visitBetween_iff_key`), CV/RecordHomfly.lean (`recordIsoOfData`), CV/HomflyRows.lean (`exists_linkingNumber`),
SM/Smoothing.lean (`smoothDiagram`, `isOrientedSmoothing_smoothDiagram`, `smoothDiagram_record`, `eps`, `eps_small`),
SM/LinkRecord.lean (`Record.smooth`, `reconnect`, `SmoothKeep`, `smoothPairIso`, `firstReturn` API), SM/LinkRecordExtras.lean
(`componentCount_smooth_of_self`, `not_reconnect_sameCycle_pair_of_self`, `smooth_comps_ne_of_self`, **`RecordIso.restrict`**),
SM/LinkDiagramRecord.lean (**`restrictRecordIso`**, `record_componentCount`), SM/MarkedProducts.lean (`restrictCrossings`,
`CrossKeep`, `knotRestrict`, `steps`, `ArcBetween`, `steps_pow`, `pow_steps`, `steps_lt_card`, `pow_mod_card_apply`,
`pow_card_apply`, `arcBetween_or_arcBetween`, `arcBetween_rotate`, **`Record.firstReturn_mul_swap_apply_of_avoid`**),
SM/Stack.lean (`firstReturn_val_eq_of_pow`, `firstReturn_congr_pred`, `mul_swap_pow_apply_of_forall_ne`,
**`firstReturn_firstReturn`**), SM/PolynomialBlock.lean (`presentations`, `P_eq_homfly`), RProof/X1Rows.lean
(`PRE_union_mem_Ind_of_fullAvail`), RProof/Cores.lean (`LocalizationData.complement_on_triangle`).

## 0. Deliverables and checks

| item | result |
|---|---|
| `work/drafts/moves/R176_SMOOTH.lean` | 5053 lines = `Site_176.lean` (4143 lines, **byte-identical prefix**, checked with `cmp`) + an APPENDIX of 910 lines (module comment + §R1–§R5, 65 declarations, all names `r176s_`, namespace `RProof`) |
| compile `cd work/lean && lake env lean ../drafts/moves/R176_SMOOTH.lean` | exit 0, **0 errors**, ≈ 19 s; warnings: exactly the skeleton's **33** `declaration uses sorry` (the 4 frozen leaves + 29 `m*_` sub-leaves) and its own `<;>` style warning at line 566; **no warning from the appendix** |
| `grep -c sorry` | **34 before / 34 after** (the 33 skeleton leaves + the FINAL's docstring); the appendix contains no `sorry` — its black boxes are `def … : Prop` consumed as HYPOTHESES |
| statement identity `python3 check_W1_identity.py Statements_FINAL.lean R176_SMOOTH.lean` | "declarations in Statements_FINAL: 37; changed/missing: **0**" (checks 1 and 3 report `False` mechanically, as for Site_176: the added import line and the appendix) |
| `#print axioms` | `r176s_firstReturn_reconnect`, `r176s_smoothRestrictIso`, `r176s_smoothRestrictIso'`, `r176s_DA_componentCount`, `r176s_knotRestrictIso_i/j`, `r176s_Sfull_ind`, `r176s_arcA_iff_key`: `[propext, Classical.choice, Quot.sound]`; `r176s_homfly_of_liftBlock`, **`r176s_portDataRest_of`**: `[propext, Classical.choice, Quot.sound, SM.lit_homfly, SM.lp_lm, SM.lp_lm_uniqueness]` (the accepted `est_ledger` footprint, **no `sorryAx`** — the black boxes are hypotheses); `r176s_homfly_of_liftBlock_curl`: standard + `SM.lit_homfly`; `r176s_est_port_relation_weak_of''`: additionally `sorryAx` THROUGH THE FROZEN LEAF `exists_bigonData_of_triangle` only (via `s176_port_weak_of_event`, as in Site_176_REPORT) |
| written under `work/lean` | nothing |

## 1. What is PROVED (exact names; statements in the file)

### §R1. The record core (a one-circle record `ρ`, `h1 : ρ.componentCount = 1`, an occurrence `x`, `y = τ x`)
* `r176s_ArcA ρ x v := ρ.ArcBetween x v (ρ.pair x)` — the open arc `A = (x → τ x)` (the word `A` of `(x A y B)`);
  `r176s_arcA_iff`, `r176s_steps_pair_pos`, `r176s_arcA_ne_self`, `r176s_arcA_ne_pair`, `r176s_arcA_smoothKeep`,
  `r176s_pow_x_eq_iff`, `r176s_pow_x_ne_self`, `r176s_pow_x_ne_pair` (positions from `x` via `steps_pow`).
* `r176s_reconnect_pow_succ_x`, **`r176s_reconnect_sameCycle_pair : ArcA v → (reconnect x).SameCycle (τ x) v`**
  (the `s₁`-cycle of `τ x` is `(τ x, A)`), `r176s_reconnect_sameCycle_self` (the `s₁`-cycle of `x` is `(x, B)`, by the
  pair symmetry `reconnect_pair`), `r176s_arc_dichotomy` (every retained occurrence is on `A` or on `B`),
  `r176s_isSelfCrossing`.
* **`r176s_smooth_comp_eq_pair_iff : (ρ.smooth x).comp w = Sum.inl ⟦τ x⟧ ↔ ArcA w.1`**,
  **`r176s_smooth_comp_eq_self_iff : (ρ.smooth x).comp w = Sum.inl ⟦x⟧ ↔ ArcBetween (τ x) w.1 x`** — the two
  components of the smoothing of a self crossing are exactly the two arcs.
* `r176s_reconnect_pow_of_arcA` (the reconnected walk from a point of `A` follows `succ` while on `A`).
* **`r176s_firstReturn_reconnect (p) (hp : ∀ v, p v → ArcA v) (u) : (firstReturn (reconnect x) p u).1 =
  (firstReturn succ p u).1`** — the first return to any set of occurrences of one arc is the same along `s₁ = s ∘ swap x y`
  and along `s`.  Case (i) the return happens before `τ x`: `Record.firstReturn_mul_swap_apply_of_avoid`; case (ii) the
  `s`-walk passes `τ x, B, x` (none of which is a `p`-point) and the first `p`-point sits at position `a + r − N` on `A`;
  the `s₁`-walk jumps from `τ x` to `s x` and reaches it at step `r − (N − m)`; `firstReturn_val_eq_of_pow` with the
  explicit index bookkeeping (`steps_pow`, `pow_mod_card_apply`, `pow_card_apply`).
* `r176s_KA ρ x := {c | ∀ v ∈ c.1, ArcA v}` (the self crossings of the `A`-component), `r176s_crossKeep_KA_iff`;
  `r176s_smoothB := {Sum.inl ⟦τ x⟧}`, `r176s_mem_smoothB`, `r176s_restrictKeep_iff`; `r176s_ΦA` (the identity on
  occurrences), `r176s_ΦA_val`, **`r176s_ΦA_succ`** (the successor clause: `firstReturn_congr_pred` +
  `firstReturn_firstReturn` + `r176s_firstReturn_reconnect`).
* **`r176s_smoothRestrictIso : RecordIso ((ρ.smooth x).restrict {⟦τ x⟧}) (ρ.restrictCrossings (r176s_KA ρ x))`** —
  the restriction of the smoothed record to its `A`-component IS `ρ` restricted to the crossings of `A`.
* `r176s_KB ρ x := r176s_KA ρ (τ x)`, `r176s_crossKeep_KB_iff`, `r176s_smoothB' := {Sum.inl ⟦x⟧}`, `r176s_mem_smoothB'`,
  `r176s_smoothPairIso_e`, **`r176s_smoothRestrictIso' : RecordIso ((ρ.smooth x).restrict {⟦x⟧})
  (ρ.restrictCrossings (r176s_KB ρ x))`** (by the pair symmetry through `smoothPairIso` and `RecordIso.restrict`).

### §R2. The oriented smoothing `D_A` (any diagram `D`, crossing `x`; `hD : D.componentCount = 1` where stated)
* **`r176s_DA D x := Smoothing.smoothDiagram D x (eps D x) (eps_small D x)`** — the library construction, the SAME one
  `exists_smoothing_record_visit` returns (PLAN §4.2's recommendation for 174).
* **`r176s_DA_smooth : IsOrientedSmoothing D x (r176s_DA D x)`** (item (T1)).
* `r176s_DA_record_nonempty`, **`r176s_DA_record_visit (v) (hv : v.1 = x) : Nonempty (RecordIso (r176s_DA D x).record
  (D.record.smooth v))`** (either occurrence, via `smoothPairIso`), `r176s_DA_iso` (chosen).
* `r176s_isSelfCrossing_of_one` (on one component every occurrence is a self-crossing occurrence),
  `r176s_record_componentCount_one`, **`r176s_DA_componentCount (hD) : (r176s_DA D x).componentCount = 2`**
  ("Smoothing `q` splits `D_+` into two components").
* **`r176s_DA_i D x v hv := ι.e.symm (Sum.inl ⟦v⟧)`** (the `B`-arc class of `v`), **`r176s_DA_j := ι.e.symm (Sum.inl ⟦τ v⟧)`**
  (the `A`-arc class), **`r176s_DA_ij (hD) : i ≠ j`** (`smooth_comps_ne_of_self`); `r176s_DA_e_mem_i`, `r176s_DA_e_mem_j`.
* **`r176s_knotRestrictIso_j (hD) (v) (hv) : RecordIso ((r176s_DA D x).knotRestrict (r176s_DA_j …)).record
  (D.record.restrictCrossings (r176s_KA D.record v))`** and **`r176s_knotRestrictIso_i … (r176s_KB D.record v)`** —
  the knot restrictions of `D_A` are the record of `D_+` restricted to the arc crossings
  (`Diagram.restrictRecordIso` ∘ `RecordIso.restrict` along `ι` ∘ `r176s_smoothRestrictIso`/`'`).

### §R3. The exact owner map (9)/(9a), record level
* `r176s_homfly_eq_groupedPoly : Nonempty (RecordIso X.record (carrierDiagram hn hG hSf Λ).record) → homfly X =
  groupedPoly hn hG hSf Λ` (`GT_groupedPoly_eq_homfly`, `P_eq_homfly`, `presentations`).
* **`r176s_homfly_of_liftBlock (hsub : retained Λ ⊆ retained q) (hK : K = liftBlock q (retained Λ)) (hX : Nonempty
  (RecordIso X.record ((lift q).record.restrictCrossings K))) : homfly X = homfly (lift Λ)`** — the clean component,
  through `CV.liftRestrictRecordIso` (the lift of an inner carrier is the lift of `q` restricted to its chords).
* `r176s_curl_removal : Prop` — the record-level R-I (BLACK BOX, §2 below).
* **`r176s_homfly_of_liftBlock_curl (hcurl) … (hK : K = liftBlock q (retained Λ) ∪ {r}) (hr : r ∉ …) (hcurlK : the two
  occurrences of r are consecutive in ρ|K) (hX) : homfly X = homfly (lift Λ)`** — the kinked component.
* `r176s_arcA_iff_key`, `r176s_crossKeep_KA_iff_key` — the arcs of a lift read on the parent visits
  (`cycBetween` of `geometricVisitKey` of `liftVisit`, through `CV.arcBetween_iff_key`, `liftVisit_twin`): the
  bridge the geometric black box needs to state/prove `KA_eq`, `KB_eq`.

### §R4. `S_full`
* `r176s_triangle_ind_L` (on `L` no two triangle crossings interlace: `complement_on_triangle` against
  `est_interlaces_of_complete`), `r176s_Sfull_eq` (`transportSupport hs (Q ∪ {j,u,v}) = Q' ∪ {j',u',v'}`),
  **`r176s_Sfull_ind : transportSupport hs (Q ∪ {j, u, v}) ∈ CV.Ind (geomAt E t' ht'.1)`** (U_R176_REPORT §5 item 3's
  "easy" part: full availability + `EmptyLocal`, the `est_S'_ind` pattern).  NOTE: it needs `hcomp : CompleteLocal` on
  `H` (equivalently the empty graph on `L`), which the frozen `hrest` binders of `s176_est_port_relation_weak_of` do
  NOT carry — see §4.

### §R5. Event level
* `r176s_third` (the third triangle crossing from two distinct ones), `r176s_cgL` (the `CarrierGeometry` of `L` as
  `carrierDiagram` reads it).
* `structure r176s_OuterData` (DATA, §2 below), `r176s_outer_carriers : Prop`, `r176s_ledger : Prop` (BLACK BOXES).
* **`r176s_portDataRest_of (hcurl : r176s_curl_removal) (hout : r176s_outer_carriers) (hled : r176s_ledger) … :
  Nonempty (s176_PortDataRest hn (genericAt E t ht.1) (genericAt E t' ht'.1) (est_S_ind …) (est_S'_ind …) q
  (GT_carrierEquiv (est_wall …) q) (est_liftCrossing … hu'))`** — in the binders of `est_port_relation` plus
  `hu : u.val ∈ triangleSupports`, `hju : j ≠ u`.  Fields: `DA := r176s_DA D₊ y`, `smooth`, `two`, `i`, `j`, `ij`
  (§R2, PROVED), `Sf := Q' ∪ {j',u',v'}`, `hSf` (§R4, PROVED), `Λ₁ := Λ_B` (kinked), `Λ₂ := Λ_A` (clean) from
  `r176s_OuterData`, **`poly₁`** (`r176s_homfly_of_liftBlock_curl` + `r176s_knotRestrictIso_i` + `GT_groupedPoly_eq_homfly`),
  **`poly₂`** (`r176s_homfly_of_liftBlock` + `r176s_knotRestrictIso_j`), `ℓ`, `link` (`CV.exists_linkingNumber`, PROVED),
  `writhe`, `rot`, `alt₁`, `alt₂` from `r176s_ledger`.
* **`r176s_est_port_relation_weak_of'' (hcurl) (hout) (hled) (hrec : the frozen hrec binders) :
  s176_est_port_relation_weak`** — the frozen `s176_est_port_relation_weak_of` with `hrest` discharged.

## 2. Black boxes (stated as `Prop`s, consumed as hypotheses; exact shapes in the file)

1. **`r176s_curl_removal`** (record-level R-I, lc:single-crossing for the kink `r`):
   `∀ ρ, ρ.componentCount = 1 → ∀ K r, r ∈ K → (∃ w hw, ρ.crossingOf w = r ∧ ((ρ.restrictCrossings K).succ ⟨w, hw⟩).1 =
   ρ.pair w) → ∀ X X', Nonempty (RecordIso X.record (ρ.restrictCrossings K)) → Nonempty (RecordIso X'.record
   (ρ.restrictCrossings (K \ {r}))) → homfly X = homfly X'`.  TRUE (the kink is an interlacement block of value one:
   mp:blocks `SM.blocks.product` + `single_crossing.one_crossing`, or an R-I move + rp:record-polynomial).  Route sketch
   for a prover: `BlockSupply` for `ρ|K` (blocks = the curl `{r}` + the blocks of `ρ|(K∖{r})`), `curl_block_value`
   (Statements_FINAL) for `X`, `SM.blocks.product` for `X'` with the same supplied family; needs an actual one-crossing
   one-circle diagram with the curl's record and the block bijection `blocks(ρ|K) ∖ {r} ≃ blocks(ρ|(K∖{r}))`.
   Estimate ≈ 600–900 lines.  Shared with rows 174/110 (their kinks).
2. **`r176s_outer_carriers`** (the geometric identification, THIS unit's remaining obligation): in the binders of
   `est_port_relation` + `hu hju` + the third crossing `v (hv hjv huv)`, `Nonempty (r176s_OuterData …)`, where
   `r176s_OuterData` bundles: `v₀ : D₊.Γ.Visit` with `v₀.1 = y`; `Λ_A Λ_B : GeoComponent (geomAt E t' ht'.1) S_full`;
   `subA/subB : retained Λ ⊆ retained q₀'`; **`KA_eq : r176s_KA D₊.record v₀ = liftBlock q₀' (retained Λ_A)`**;
   `r : D₊.record.Crossing`; **`KB_eq : r176s_KB D₊.record v₀ = liftBlock q₀' (retained Λ_B) ∪ {r}`**; `r_not : r ∉ liftBlock …`;
   `r_curl : ∃ w hw, crossingOf w = r ∧ ((D₊.record.restrictCrossings (r176s_KB …)).succ ⟨w, hw⟩).1 = pair w`.
   Geometric content (from the site): the record of `D₊ = carrierDiagram q₀'` has, in the parent's cyclic order
   (`visitBetween_iff_key`), the occurrences `u'_a, v'_b, [B], v'_c, u'_c, [C]` — the order `v' <_c u'` is FORCED by the
   empty local graph on `L` (with `u <_a j`, `j <_b v` from `s176_corner_case1`; the acyclic order would make `u', v'`
   interlace on `P'`), and the edge order `(a, b, c)` on `P'` likewise.  Selecting `u', v'` too (`S_full`), `q₀'` splits
   into the central triangle `(v'_b → u'_c → v'_b)` and the two outer carriers `Λ_B = (v'_c → B)`, `Λ_C = Λ_A = (u'_a → C)`
   (`geoSmoothingSuccessor` of `S_full`: at a selected crossing the successor of a visit is the successor of its twin).
   With `v₀ := u'_a` (or `u'_c`, whichever makes `A` the `C`-side — `r176s_DA_record_visit` accepts either occurrence):
   `A = (v₀ → τ v₀)` carries `[C]`, `B` carries `v'_b, [B], v'_c`, so `K_A = liftBlock(retained Λ_A)` and
   `K_B = liftBlock(retained Λ_B) ∪ {lift v'}` with the kink `lift v'` adjacent in `ρ|B` (`v'_b, v'_c` are consecutive
   among the `B`-occurrences since `[B]` = the self crossings of `Λ_B` lie strictly between them… precisely: the
   `B`-restricted successor of `v'_c` is `v'_b` — the `B`-arc wraps).  `r176s_arcA_iff_key` /
   `r176s_crossKeep_KA_iff_key` express `K_A, K_B` on the parent keys.  Estimate ≈ 1.5–2.5k lines (the carrier
   structure of `S_full` vs `S'` on `geoSmoothingSuccessor`, plus the retained-set identities).  NOT on any other unit's
   path except the ledger (below), which consumes `Λ_A, Λ_B`.
3. **`r176s_ledger`** (U_R176_REPORT §5 items 4–5, OTHER units): for `O : r176s_OuterData` and `ℓ` with
   `IsLinkingNumber (r176s_DA D₊ y) i j ℓ`: `w(q) = w(Λ_B) + w(Λ_A) + 2ℓ` (14), `R(q) = R(Λ_B) + R(Λ_A) + 1` (13),
   `UniformOrOneDissentCV` at `Λ_B`, `Λ_A` (12).

## 3. Verification notes

* `r176s_portDataRest_of` has NO `sorryAx`: every field of `s176_PortDataRest` is built from the three black boxes as
  hypotheses; `DA, smooth, two, i, j, ij, Sf, hSf, ℓ, link` need none of them; `poly₂` needs only `r176s_outer_carriers`;
  `poly₁` needs `r176s_outer_carriers` + `r176s_curl_removal`; `writhe, rot, alt₁, alt₂` need `r176s_ledger`.
* The frozen `s176_PortDataRest` field order is `Λ₁ ↔ poly₁ ↔ i`: the file sets `Λ₁ := Λ_B` (kinked, the `B`-arc class
  `i` of `v₀`) and `Λ₂ := Λ_A` (clean, the `A`-arc class `j` of `τ v₀`); `r176s_ledger` is stated in that order so its
  conjuncts are the fields verbatim.
* `r176s_DA_componentCount` is `2` for ANY crossing of a one-component diagram (every crossing is a self crossing); no
  site data enters (T1)/(two)/(i ≠ j).

## 4. Defect in the frozen interface (rule (4)) — reported, not edited

The frozen `hrest` hypothesis of `s176_est_port_relation_weak_of` / `_of'` (Site_176.lean 3497–3507, 4120–4130)
quantifies `Nonempty (s176_PortDataRest …)` over binders that carry **no `hcomp : CompleteLocal`, no
`hu : u.val ∈ triangleSupports`, no `hju : j ≠ u`**.  `s176_PortDataRest.hSf` (and everything geometric) needs the empty
local graph on `L`, i.e. `hcomp`; the retention `hu'` alone does not give it.  So the frozen `hrest` is (very likely)
NOT realisable as stated, while the enriched form is.  Fix (5 lines, in the frozen theorem's binder list): add
`(hef' heg' hfg') (hcomp : CompleteLocal (geomAt E t ht.1) hef' heg' hfg') (hu : u.val ∈ triangleSupports e f g)
(hju : j ≠ u)` to `hrest` (they are available at the call site).  This file does not edit the frozen theorem; it
appends **`r176s_est_port_relation_weak_of''`**, the same theorem with `hrest` discharged by `r176s_portDataRest_of`
(whose binders carry `hcomp`, `hu`, `hju`), keeping the frozen `hrec` binders.

## 5. What remains (with estimates)

| obligation | consumer | estimate |
|---|---|---|
| `r176s_outer_carriers` (the carrier structure of `S_full` and the arc identification, §2.2) | `r176s_portDataRest_of` | ≈ 1.5–2.5k lines |
| `r176s_curl_removal` (record-level R-I) | `poly₁` | ≈ 600–900 lines; shared with 174/110 |
| `r176s_ledger` ((14), (13), (12)) | `writhe, rot, alt₁, alt₂` | other units (U_R176 §5 items 4–5) |
| `hsucc` / `s176_hrec_of_site` | `r176s_est_port_relation_weak_of''`'s `hrec` | the HSUCC unit (R176_HSUCC.lean) |
| F-176-1 acceptance, the frozen leaf `exists_bigonData_of_triangle` | — | as in Site_176_REPORT §4–5 |

## 6. Pitfalls met

1. `set x := …` (let-bound locals) breaks both `rw` matching and `omega` atom identification when later hypotheses
   are stated in the unfolded form — the first-return arithmetic is written fully explicitly (`ρ.steps x u.1`,
   `Fintype.card ρ.M`, `returnTime ρ.succ p u.1 u.2`).
2. `pow_add` gives `f^(a+b) v = f^a (f^b v)`; to iterate from `u = f^a x` use `add_comm` first.
3. `← ρ.pow_mod_card_apply h1 x` WITHOUT the exponent rewrites the FIRST `(succ ^ ?n) x` it finds (possibly the wrong
   side); pass the exponent explicitly.
4. `unfold` of a `Finset` singleton over `(ρ.smooth x).comps` exposes the `Sum`/`Quotient` type and then
   `Finset.mem_singleton` fails ("target not type-correct under implicit transparency"); keep the singleton's type by
   proving membership lemmas at type `(ρ.smooth x).comps` (`r176s_mem_smoothB`) and never unfolding.
5. Rewriting `(Equiv).injective.eq_iff` after `rw [← he]` fails for the same typing reason; prove the iff by hand.
6. `firstReturn_mul_swap_apply_of_avoid` lives in `SM.Link.Record` (MarkedProducts opens `namespace Record` at line 541).
7. Stating the poly lemmas with `CV.Generic`/`Ind` binders and `carrierDiagram` on one side and `liftBlock` with
   `CarrierGeometry.ofDiagrammatic` on the other hit the `whnf` heartbeat limit; state them in the `geoPositiveLift hn hG
   hT q` binders (`CarrierGeometry`) and bridge at the event level, where `carrierDiagram` is a reducible `abbrev` and
   `(ofDiagrammatic …).cg = geomAt …` is `rfl`.
8. `Set.insert_diff_of_mem` / `Set.diff_singleton_eq_self` are deprecated: `Set.insert_sdiff_of_mem`,
   `Set.sdiff_singleton_eq_self`.
9. `lt_or_le` is not available; `Nat.lt_or_ge`.
10. `firstReturn_firstReturn` needs the outer predicate in the form `fun m => q m.1` with `q` on the base type; the
    `RestrictKeep` predicate of `(ρ.smooth x).restrict B` is definitionally of that form (`smooth_comp`, `smooth_pair_val`),
    moved across with `firstReturn_congr_pred` (which also absorbs `DecidablePred` instance mismatches).
