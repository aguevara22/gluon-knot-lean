# R174_SMOOTH_REPORT — unit SMOOTH (Wave 2, row 174): the oriented smoothing `D₀` of the `E`-side lift and the ledger fields `D₀, qx, fulltwist, i, j, ℓ, smoothing, writhe_count` (U_R174_REPORT §4 items 5–6, `gsc_smoothing_split`)

Prover (subagent), 2026-09-15 21:18 UTC / 5:18pm ET.  File: `work/drafts/moves/R174_SMOOTH.lean`
(= `Site_174.lean` byte-identical in lines 1–2941 + 1006 appended lines 2942–3947, prefix `r174s_`).
Inputs read: Site_174_REPORT.md (§1 `s174_site`, §3 `s174_hrec_prop`, §4 `s174_fulltwist_of_hrec`, §5),
U_R174_REPORT.md §4 items 1–6, RProof/RALedgers.lean (`gsc_fulltwist_triple`, `gsc_smoothing_split`,
`gsc_Ledger` fields `D₀ qx fulltwist i j ℓ smoothing writhe_count`, `gsc_carrierDiagram_*`),
PLAN_FINAL.md §4.2, RProof/GenericTransport.lean / X1Rows3.lean (`GT_homfly_wall_gen`, `GT_Endpoint`),
SM/LinkRecord.lean (`Record.smooth`, `reconnect`, `firstReturn`, `restrict`), SM/MarkedProducts.lean
(`restrictCrossings`, the `steps`/`ArcBetween`/first-return toolbox R3(a), `RecordIso.ofOccOfCard`),
SM/LinkRecordExtras.lean (`RecordIso.restrict`, `componentCount_smooth_of_self`, `smooth_comps_ne_of_self`),
SM/Stack.lean (`firstReturn_firstReturn`, `firstReturn_mul_swap`, `firstReturn_val_congr`), SM/Smoothing.lean
(`smoothDiagram`, `smoothDiagram_record`, `exists_smoothing`), SM/LinkDiagramRecord.lean (`restrict_record`,
`record_succ_no_between`, `cycNext_unique`), CV/PieceIntrinsic.lean + CV/GroupedKnot.lean (`liftVisit`,
`liftVisitEquiv`, `arcBetween_iff_key`, `visitBetween_iff_key`, `overBit_eq_true_iff_parent`), CV/HomflyRows.lean
(`IsLinkingNumber`, `exists_linkingNumber`), CV/Axioms.lean (`gausscode_polynomial`), SM/CornerChainUnits.lean
(the U110-H counting lemmas `s7h_*`, reproduced — not in the import chain).

## 0. Deliverables and checks

| item | result |
|---|---|
| `R174_SMOOTH.lean` | 3947 lines: `Site_174.lean` (2941 lines, `diff` of the prefix: IDENTICAL) + the appended block "Unit SMOOTH" (lines 2944–3947, 42 declarations) |
| compile `cd work/lean && lake env lean ../drafts/moves/R174_SMOOTH.lean` | exit 0, **0 errors**, ≈ 17 s; warnings: exactly the skeleton's **33** `declaration uses sorry` (all at lines ≤ 1819) + its one cosmetic `<;>` note (line 566).  **No new `sorry`**: `grep -c sorry` = 34 before and 34 after |
| `python3 check_W1_identity.py Statements_FINAL.lean R174_SMOOTH.lean` | check 2 (all 37 declarations of Statements_FINAL): **0 changed/missing**; checks 1 and 3 `False` for the prescribed reasons (the site's import line shifts the prefix; appended material) — same as Site_174_REPORT §0 |
| frozen material | nothing above line 2942 touched; no Prop of RALedgers edited or asserted; nothing under `work/lean` written; scratch in the session scratchpad only |
| `#print axioms` | every record-level and lift-level lemma (`r174s_restrict_smooth_iso`, `r174s_firstReturn_reconnect_eq`, `r174s_firstReturn_mul_swap_of_apply_eq`, `r174s_knotRestrict_record_iso`, `r174s_D₀_record`, `r174s_D₀_componentCount`, `r174s_D₀_writhe`, `r174s_writhe_two_component`, `r174s_recordIso_of_arcVisitData`, `r174s_arc_rec_of_visitData`): `propext, Classical.choice, Quot.sound` only.  `r174s_split_of_arc_prop`, `r174s_smoothing_split_of_arc`: + `SM.lit_homfly, SM.lp_lm, SM.lp_lm_uniqueness` (ax:gausscode through `CV.gausscode_polynomial`), the accepted footprint, **no `sorryAx`**.  `r174s_fulltwist_triple_of_bigon`, `r174s_fulltwist_of_hrec`, `r174s_ledger_fields`: + `sorryAx`, entering ONLY through the frozen skeleton leaves `exists_rii_deletion` / `exists_bigonData_of_triangle` (exactly as `s174_fulltwist_of_hrec`) |
| reassessment rule | never triggered (no lemma took two failed attempts; the largest iteration was one compile round on the record core) |

## 1. What is PROVED (all `r174s_`, namespace `SM.Link`, `open SM SM.GeoCarrier SM.Carrier RProof`)

### 1A. The smoothing `D₀` (§A, lines 3514–3574)

`r174s_D₀ D_H qx := Smoothing.smoothDiagram D_H qx (eps D_H qx) (eps_small D_H qx)` — the library oriented
smoothing, i.e. **the same `D₀` that `exists_smoothing` / `gsc_fulltwist_of_bigon` / `s174_fulltwist_of_hrec`
produce** (PLAN §4.2 "the realiser should take the SAME `D₀ := smoothDiagram …` in both fields").
`r174s_D₀_isOrientedSmoothing`, `r174s_D₀_record : D₀.record ≅ D_H.record.smooth (overVisit qx)`
(`smoothDiagram_record`), `r174s_D₀_componentCount` (`= 2` for one-component `D_H`), `r174s_D₀_writhe`
(`w(D₀) = w(D_H) − 1` at a positive `qx`).

### 1B. Record level: the two arcs of a self crossing on a one-circle record (§B, lines 2977–3256; the core)

For `ρ` a one-circle record and `u : ρ.M` (a self crossing since one circle, `r174s_isSelfCrossing`):
* `r174s_KeepArc ρ u : Set ρ.Crossing` — the crossings both of whose occurrences lie strictly inside the
  forward arc `(u, τ u)` (`ArcBetween u · (pair u)`); `r174s_crossKeep_keepArc_iff`.
* `r174s_arcComp ρ u a := Sum.inl ⟦τ a⟧ : (ρ.smooth u).comps` for `a ∈ {u, τ u}` — the two circles of the
  smoothing (`r174s_arcComp_ne`); **`r174s_smooth_comp_eq_iff`: a retained occurrence lies on the circle of `a`
  iff it lies strictly inside the arc `(a, τ a)`** (via `r174s_reconnect_sameCycle_pair_iff`: the
  `s₁ = s ∘ swap(u, τ u)`-cycle of `τ u` is the arc `(u, τ u)`, by `mul_swap_pow_apply_of_forall_ne` and the
  `steps` arithmetic of R3(a), plus `not_reconnect_sameCycle_pair_of_self`).
* **`r174s_firstReturn_mul_swap_of_apply_eq`** (general permutations): if `g b = a` with `a` non-retained,
  `firstReturn (g * swap a b) p = firstReturn g p` — the first returns to `(· ≠ a)` agree pointwise and the
  first return to `p` factors through it (`firstReturn_firstReturn`, `firstReturn_val_congr`).
* **`r174s_firstReturn_reconnect_eq`**: for `P ↔ CrossKeep (KeepArc u)`, `firstReturn (reconnect u) P = firstReturn succ P`
  (values) — through `P⁺ = P ∪ {u, τ u}`: `firstReturn s₁ P⁺ = firstReturn s P⁺ * swap u (τ u)`
  (`firstReturn_mul_swap`), the `P⁺`-first return of `τ u` along `s` is `u` (no `P`-point on the other arc,
  `firstReturn_val_eq_iff` + `steps_eq_of_base`), so the swap is harmless by the previous lemma, and both first
  returns to `P` factor through `P⁺`.
* **`r174s_restrict_smooth_iso`**: `(ρ.smooth u).restrict {arcComp u a} ≅ ρ.restrictCrossings (KeepArc a)`
  for `a ∈ {u, τ u}` — occurrences by `r174s_smooth_comp_eq_iff`, successor by `firstReturn_firstReturn` +
  the previous lemma, pairing/bits/signs verbatim, one circle on both sides (`RecordIso.ofOccOfCard`).

### 1C. Diagram level (§C, lines 3258–3512)

`r174s_componentCount_of_smooth_iso`, `r174s_writhe_of_smooth_iso` (`w(D₀) = w(D) − σ(v)`), the counting
lemmas `r174s_writhe_restrict / self_iff / writhe_knotRestrict / mixedSignSum_eq / comp_eq_or /
writhe_two_component` (`w(D) = w(D|ᵢ) + w(D|ⱼ) + 2ℓ_ij` for a two-component diagram) and
`r174s_record_writhe_smooth` — the U110-H lemmas `s7h_*` of SM/CornerChainUnits.lean reproduced verbatim
(that module is not in the import chain).
**`r174s_knotRestrict_record_iso`**: `(D₀.knotRestrict i).record ≅ D.record.restrictCrossings (KeepArc a)`
when `ι.e i = arcComp v a` (`restrict_record` → `RecordIso.restrict` along the smoothing clause →
`r174s_restrict_smooth_iso`).  `r174s_smoothing_split_swap` (`mixedSignSum_comm`).
**`r174s_split_of_arc_isos`** / **`r174s_split_of_arc_prop`**: if the two arc records of one occurrence `u`
of `qx` are the records of one-component diagrams `K₁, K₂`, then `D₀ = r174s_D₀ D_H qx` has components
`i ≠ j` with `gsc_smoothing_split D₀ i j (homfly K₁) (homfly K₂) ℓ` (ax:gausscode, `exists_linkingNumber`)
and `w(D_H) = w(K₁) + w(K₂) + 2ℓ + 1` (both orientations of `u` handled: `visit_eq_over_or_under`).

### 1D. The ledger fields on the `GT_Endpoint` configuration (§D, lines 3576–3717)

* `r174s_fulltwist_triple_of_bigon` — `gsc_fulltwist_of_bigon` with `D₀` pinned to `r174s_D₀` (same proof);
  `r174s_qx` := the lifted `x'` (`s174_lift`, as in `s174_site`);
  **`r174s_fulltwist_of_hrec`** — `s174_fulltwist_of_hrec` without the existential:
  `gsc_fulltwist_triple (carrierDiagram qAB) (carrierDiagram q') (r174s_D₀ _ qx) qx` from `s174_site` + `s174_hrec_prop`.
* **`r174s_smoothing_split_of_arc`** (items 5–6): from the black box `r174s_arc_rec_prop` (§2),
  `∃ i j ℓ, gsc_smoothing_split (r174s_D₀ D_H qx) i j (groupedPoly hn hG hSxw qA) (groupedPoly hn hG hSxw qB) ℓ ∧
  groupedWrithe hG' q' = groupedWrithe hG qA + groupedWrithe hG qB + 2ℓ + 1` (`GT_groupedPoly_eq_homfly`,
  `gsc_carrierDiagram_componentCount/writhe`, `geoPositiveLift_isPositive`).
* **`r174s_ledger_fields`**: with `hrec : s174_hrec_prop`, `hsplit : r174s_arc_rec_prop` and
  `hwall : groupedWrithe hG' q' = groupedWrithe hG qAB + 2` (the ledger's `writhe_wall`, item 2),
  `∃ D₀ qx i j ℓ, fulltwist ∧ smoothing ∧ (groupedWrithe hG qAB = groupedWrithe hG qA + groupedWrithe hG qB + 2ℓ − 1)`
  — exactly the fields `D₀, qx, fulltwist, i, j, ℓ, smoothing, writhe_count` of `gsc_Ledger` at `q' := W.τ qAB`
  (no interface edit; (10) is `w_H − 1 = w_A + w_B + 2ℓ` read through (9)).

### 1E. The arc record from visit-level transport data (§E, lines 3719–3943; reduction of the black box)

`r174s_InArc hP' u₀ v := cycBetween (key u₀) (key v) (key (twin u₀))`; **`r174s_ArcVisitData hG hG' q q' u₀`**:
a bijection `ψ` from the retained visits of the carrier `q` (on `P`) onto the retained visits of `q'` (on `P'`)
lying with their twins strictly inside the arc `(u₀, twin u₀)`, compatible with twins, with the cyclic key
order and with the divide signs — the hypothesis shape of `GT_homfly_wall_gen`.
**`r174s_recordIso_of_arcVisitData`**: such a datum at `u₀ = liftVisit u` gives
`(lift q').record.restrictCrossings (KeepArc u) ≅ (lift q).record` — occurrences by `liftVisitEquiv` on both
sides, twins by `liftVisit_twin`, bits by `overBit_eq_true_iff_parent`, signs `+1` on both positive lifts, and
the first-return successor by `cycNext_unique`: no retained occurrence lies inside a gap
(`not_arcBetween_firstReturn` read through `arcBetween_iff_key` and `ψ.cyc`), no occurrence lies between a
visit and its successor on the lift of `q` (`record_succ_no_between`, `visitBetween_iff_key`).
**`r174s_arc_rec_of_visitData`**: two such data (arcs `(u, τ u)` for `qA`, `(τ u, u)` for `qB`) on the
carrier diagrams give the black box `r174s_arc_rec_prop`.

## 2. The BLACK BOX — `r174s_arc_rec_prop` (STATED as a `def … : Prop`, consumed as a hypothesis; no `sorry`)

```
def r174s_arc_rec_prop hn hG hG' hSxw hSm' q' hx' qA qB : Prop :=
  ∃ u : (carrierDiagram hn hG' hSm' q').Γ.Visit, u.1 = r174s_qx hn hG' hSm' q' hx' ∧
    Nonempty (RecordIso (D_H.record.restrictCrossings (D_H.record.r174s_KeepArc u)) (carrierDiagram hn hG hSxw qA).record) ∧
    Nonempty (RecordIso (D_H.record.restrictCrossings (D_H.record.r174s_KeepArc (D_H.record.pair u))) (carrierDiagram hn hG hSxw qB).record)
```
(`D_H := carrierDiagram hn hG' hSm' q'`).  This is the wall/ownership transport of **U_R174_REPORT §4 items 1–2**
in arc form: `E = b a A c a B c b C`, the carrier `AB'` of `E-b` reads `x'(ℓ₁) [A] w'(ℓ₂) x'(ℓ₂) [B] w'(ℓ₃)`
(order inherited from `P'` on the independent support, `arcBetween_iff_key`), the `P-ac` carriers are
`A = (m(ℓ₁) [A])`, `B = ([B] m(ℓ₃))` (the `Q`-loops excised on both sides), the strings agree across the wall
(A7 exactness `D.gauss` on the non-triangle visits), the bits by `D.sign_eq`, both lifts positive.  By §1E it is
**reduced to two visit bijections `ψ_A, ψ_B` with the twin / key-order / divide-sign compatibilities**, i.e. to
the ownership facts "`qA` owns the `ℓ₁`-visit of `m` and the residual `A`-string visits, `qB` the `ℓ₃`-visit of
`m` and the `B`-string, `AB'` owns `x', w'` and both strings" (`GT_owner_transport` / `GT_owner_arc`,
`GT_Endpoint.adj1..3`, `Q_out`, `Q_avail`) — no record combinatorics remains.  Estimate for the realiser:
0.8–1.5k lines (below the 1.5–2.5k of Site_174_REPORT §3, since steps 3–5 of that route are now §1B/§1E).
I checked the statement against the GSC words on both sides (including the mirror label order
`(ℓ₁ ℓ₃ ℓ₂)`, where the within-edge orders and the arcs swap consistently): **it is TRUE as stated**; no
defect of the RALedgers material was found (rule 4 not triggered).

## 3. Other consumer obligations touched only as hypotheses (black boxes of other units)

| obligation | where it enters | unit |
|---|---|---|
| `s174_hrec_prop` (the `hrec` of the bigon site) | `r174s_fulltwist_of_hrec`, `r174s_ledger_fields` | Site_174_REPORT §3 (1.5–2.5k) |
| `writhe_wall` `w_H = w_L + 2` | `hwall` of `r174s_ledger_fields` | U_R174 §4 item 2 |
| `hx'`, `hw'` (ownership of the `x', w'` visits by `q' = τ qAB`) | inherited from `s174_site` | Site_174_REPORT §5 |
| `exists_rii_deletion`, `exists_bigonData_of_triangle` | through `s174_site` / `r174s_fulltwist_triple_of_bigon` | Wave 1 leaves (skeleton `sorry`) |

Items 5–6 themselves (`componentCount = 2`, `i ≠ j`, the two `homfly` identities, `IsLinkingNumber`, the writhe
count) are fully PROVED from the arc black box; the interlacing of `x'` and `w'` on `D_H` (which makes `w'` a
mixed crossing of `D₀`) is NOT needed for any ledger field and was not formalised (it follows from
`D.compl x w` + `D.hxw` and `arcBetween_iff_key` if a later unit wants it).

## 4. Design decisions and fidelity

* **`D₀` is named, not existential.**  `s174_fulltwist_of_hrec` gives `∃ D₀`; the ledger needs the SAME `D₀` in
  `fulltwist` and `smoothing`, so `r174s_D₀` fixes it to `smoothDiagram` and `r174s_fulltwist_of_hrec` re-proves
  the triple for it (the proof of `gsc_fulltwist_of_bigon`, which uses exactly `exists_smoothing`'s witness).
* **The record clause is the only property of `D₀` used** (`smoothDiagram_record`), as PLAN §4.2 and U_R174 §4
  item 5 prescribe ("reads `D₀` through `exists_smoothing_record_visit`'s record clause"); `IsOrientedSmoothing`
  alone carries no record information.
* **Arc records instead of "masks".**  GSC (9a) speaks of mask-zero / mask-`xw` survivors; at the record level
  the self-crossings of the two smoothing circles are the crossings internal to the two arcs of `x'`, which is
  what `r174s_KeepArc` states — no mask bookkeeping.
* **Both orientations.**  Which occurrence of `x'` (over/under) starts the `A`-arc depends on the corner
  orientation (`s174_order`); the black box is stated with `∃ u`, and `r174s_split_of_arc_prop` case-splits
  (`visit_eq_over_or_under`, `r174s_smoothing_split_swap`).
* **`writhe_count` through `writhe_wall`.**  The unconditional identity proved is
  `w_H = w_A + w_B + 2ℓ + 1` (`r174s_smoothing_split_of_arc`); (10) `w_L = w_A + w_B + 2ℓ − 1` needs (9),
  which is item 2's `writhe_wall`, taken as a hypothesis in `r174s_ledger_fields`.

## 5. Pitfalls met (for the realiser of items 1–2 / the assembler)

1. `set P := ρ.CrossKeep …` inside a proof whose variable's type mentions the set produced a fresh `w✝`
   and broke the final `rw`; passing the predicate as an explicit argument with `hP : ∀ m, P m ↔ CrossKeep … m`
   (`r174s_firstReturn_reconnect_eq`) is clean.
2. `show (firstReturn (firstReturn (ρ.reconnect u) (ρ.SmoothKeep u)) ((ρ.smooth u).RestrictKeep B) w).1.1 = _`
   fails with "failed to synthesize `DecidablePred (RestrictKeep …)`" (the predicate is elaborated at the
   `Perm`'s subtype type, not at `(ρ.smooth u).M`); `exact`/`refine Eq.trans ?_ (firstReturn_firstReturn …)`
   with the goal's own instances works.
3. `firstReturn_val_congr`'s decidability arguments are implicit `{_ : DecidablePred p}`: use it only where
   the expected type is known (`have h : … := firstReturn_val_congr …`, or inside `Eq.trans`).
4. `rw [← hwk]` with `hwk : (succ ^ steps u w) u = w` rewrites the `w` inside `steps u w` too; use a `calc`
   step that rewrites `hwk` left-to-right instead.
5. Identifiers with combining diacritics (`v̂`, `ẑ`) are not Lean identifiers ("expected token").
6. A `structure` inside a `variable` section takes only the variables it mentions (`r174s_ArcVisitData hG hG' q q' u₀`
   — `hT hT'` are not parameters).
7. `Decidable (D.Γ.MixedPair …)`: `mixedSignSum` is defined under `open Classical`; start such proofs with
   `classical`.
8. The `GeoComponent hG.crossingGeometry S` of `CV.carrierDiagram` is accepted for
   `GeoComponent (s174_cg hn hG).cg S` by proof irrelevance (Site_174_REPORT §6.10) — used in
   `r174s_arc_rec_of_visitData`.
