# R174_HREC_REPORT — unit HREC (Wave 2, I-174 (b)): the wall record transport `hrec` of row 174, PROVED

Prover (subagent), 2026-09-15 ≈ 21:15 UTC / 5:15pm ET.  File: `work/drafts/moves/R174_HREC.lean`
(= `Site_174.lean`, byte-identical on its 2941 lines, + 449 appended lines, prefix `r174h_`).
Inputs read: Site_174_REPORT.md (§3 the stated Prop and its route), U_R174_REPORT.md §4, PLAN_FINAL.md §4.2,
RProof/RALedgers.lean (`gsc_WallData`, `gsc_wallData_of_endpoint`, `gsc_Ledger`, `gsc_fulltwist_triple`),
RProof/X1Rows3.lean (`GT_Wall`, `GT_Good`, `GT_carrierEquiv`, `GT_owner_transport`, `GT_homfly_wall_gen`,
`GT_Endpoint`, `GT_cyc_congr_of_lt`, `GT_det_pos_iff_of_sign`), CV/GroupedKnot.lean (§1–§2:
`arcBetween_iff_visitBetween`, `arcBetween_iff_key`, `liftRestrictRecordIso` — the template),
CV/PieceIntrinsic.lean (`liftVisit`, `liftVisitEquiv`, `liftVisit_twin`, `overBit_eq_true_iff_parent`,
`visitBetween_iff_key`), SM/MarkedProducts.lean (`restrictCrossings`, `restrictCrossings_succ_val_eq_iff`,
`not_arcBetween_firstReturn`), SM/LinkDiagramRecord.lean (`record`, `cycNext_unique_on`, `switchRecordIso`,
`mem_pair_twin_iff`), SM/LinkRecord.lean (`Record`, `RecordIso`, `crossingOf_eq_iff`), SM/LinkDiagram.lean
(`switch`, `switch_overStrand_of_ne`, `switch_sign_of_ne`), SM/GeoCarrierCrossings.lean
(`mem_geoCarrierCrossings`, `geoCarrierCrossings_subset_U`, `mem_geoSupportUnselected_iff`).

## 0. Deliverables and checks

| item | result |
|---|---|
| `R174_HREC.lean` | 3390 lines = `Site_174.lean` (2941, `cmp` byte-identical) + the appended section "HREC" (2942–3390, 449 lines).  Nothing above line 2941 changed: no statement, name or docstring of the skeleton or of `s174_` was touched; the Prop `s174_hrec_prop` is NOT edited |
| compile `cd work/lean && lake env lean ../drafts/moves/R174_HREC.lean` | exit 0, **0 errors**, ≈ 23 s; warnings: exactly the skeleton's **33** `declaration uses sorry` + its one cosmetic `<;>` linter note (line 566).  `grep -c sorry`: **34 before, 34 after** (no new `sorry`, no black box added) |
| `#print axioms` | `r174h__s174_hrec_prop_proof`, `r174h_recordIso`, `r174h_transfer`, `r174h_transfer_succ`, `r174h_hrec_tau`, `r174h_retained_of_mem'`, `r174h_keep`: **`propext, Classical.choice, Quot.sound` only** — standard axioms, no `sorryAx` (the whole `hrec` is sorry-free).  `r174h_fulltwist` (the consumer corollary through `s174_fulltwist_of_hrec`): `+ sorryAx` (the frozen leaf `exists_bigonData_of_triangle` inside `s174_site`) `+ SM.lit_homfly, SM.lp_lm, SM.lp_lm_uniqueness` (through `gsc_fulltwist_of_bigon` → `CV.gausscode_polynomial`), i.e. exactly the footprint of `s174_fulltwist_of_hrec` |
| reassessment rule | not triggered: no lemma took two failed attempts (the failures met were elaboration-level — §4 — each fixed on the next compile) |
| size | 449 lines against the §3 estimate of 1.5–2.5k: the CV:cor:groupedknot §2 template (`liftRestrictRecordIso`, `restrictTransfer_succ` with `cycNext_unique_on`) already handles the first-return successor of `restrictCrossings`; the wall only adds ownership and key-order transport (≈ 100 lines) and the switch bookkeeping (≈ 30 lines) |

Nothing under `work/lean` was written.  Scratch probes live in the session scratchpad only.

## 1. What is PROVED (all `r174h_`, namespace `SM.Link`, `open SM SM.GeoCarrier SM.Carrier RProof`)

### 1a. The main theorem

```
theorem r174h__s174_hrec_prop_proof
    (hn) (hG : CV.Generic P) (hG' : CV.Generic P')
    (D : GT_Endpoint hG.crossingGeometry hG'.crossingGeometry hs e f g Q x w m ℓ₁ ℓ₂ ℓ₃)
    (hSm : Q ∪ {m} ∈ CV.Ind hG.crossingGeometry)
    (hSm' : transportSupport hs (Q ∪ {m}) ∈ CV.Ind hG'.crossingGeometry)
    (qAB : GeoComponent hG.crossingGeometry (Q ∪ {m}))
    (q' : GeoComponent hG'.crossingGeometry (transportSupport hs (Q ∪ {m})))
    (hq' : q' = GT_carrierEquiv (gsc_wall_of_endpoint hG hG' D hSm hSm') qAB)
    (hx' : crossingTransport hs x ∈ geoCarrierCrossings hG'.crossingGeometry (transportSupport hs (Q ∪ {m})) q')
    (hw' : crossingTransport hs w ∈ geoCarrierCrossings hG'.crossingGeometry (transportSupport hs (Q ∪ {m})) q') :
    s174_hrec_prop hn hG hG' hSm hSm' qAB q' hx' hw'
```
i.e. `Nonempty (RecordIso (s174_reducedRecordOf ((carrierDiagram hn hG' hSm' q').switch (lift x')) (lift w') (lift x'))
(carrierDiagram hn hG hSm qAB).record)` — exactly the `hrec` that `s174_fulltwist_of_hrec` consumes.  The proof is
`Nonempty.intro (r174h_recordIso …).symm` where

```
noncomputable def r174h_recordIso : RecordIso 𝓓L.record (𝓓sw.record.restrictCrossings 𝓚)
```
with `𝓓L := geoPositiveLift hn (s174_cg hn hG) hSg qAB` (= `carrierDiagram hn hG hSm qAB`, `rfl`),
`𝓓H := geoPositiveLift hn (s174_cg hn hG') hSg' q'`, `𝓓sw := 𝓓H.switch (lift x')`, and
`𝓚 := r174h_keep … = {c | c ≠ crossingOf (overVisit (lift w')) ∧ c ≠ crossingOf (overVisit (lift x'))}` (the keep-set of
`s174_reducedRecordOf`; `r174h_reducedRecordOf_eq` is `rfl`).

Two corollaries in the ledger's binding (`gsc_wallData_of_endpoint … .τ qAB` is `GT_carrierEquiv (gsc_wall_of_endpoint …) qAB`
by `rfl`, so `hq' := rfl`):
* `r174h_hrec_tau … hx' hw' : s174_hrec_prop hn hG hG' hSm hSm' qAB ((gsc_wallData_of_endpoint hn hG hG' D hSm hSm').τ qAB) hx' hw'`;
* `r174h_fulltwist (hsgn : crossingSign P ℓ₁ ℓ₂ = crossingSign P ℓ₁ ℓ₃) … : ∃ D₀, gsc_fulltwist_triple (carrierDiagram hn hG hSm qAB)
  (carrierDiagram hn hG' hSm' q') D₀ (lift x')` (for `q'` with `hq'`) = `s174_fulltwist_of_hrec` + the main theorem: the
  `fulltwist` field of `gsc_Ledger` (F-174) now rests on the site inputs `hx', hw'` alone (§3).

### 1b. The route (CV:cor:groupedknot §2 across the wall)

`Φ := r174h_transfer : 𝓓L.Γ.Visit ≃ {v : 𝓓sw.Γ.Visit // 𝓓sw.record.CrossKeep 𝓚 v}` is the identity on parent visits transported
by `visitTransport hs`: `v' ↦ liftVisitEquiv_H.symm ⟨visitTransport hs (liftVisit_L v'), _⟩`, inverse
`v ↦ liftVisitEquiv_L.symm ⟨(visitTransport hs).symm (liftVisit_H v.1), _⟩` (`r174h_liftVisit_transfer : liftVisit_H (Φ v').1 =
visitTransport hs (liftVisit_L v')`).  The RecordIso clauses:

| clause | lemma | content |
|---|---|---|
| `e`, `comp_eq` | — | both lifts are one-circle (`geoPositiveLift_componentCount`), `finCongr` / `Subsingleton (Fin 1)` |
| `succ_eq` | `r174h_transfer_succ` | `cycNext_unique_on` on the `P'`-keys of parent visits, as `restrictTransfer_succ`: (i) `Φ (next v') ≠ Φ v'` (`nextVisit_ne_self`, the twin is another occurrence); (ii) `succ (Φ v') ≠ Φ v'` (`restrictCrossings_succ_val_eq_iff`); (iii) no kept `u` strictly between `Φ v'` and `Φ (next v')`: the three parent visits are visits of retained crossings of `AB`, their cyclic key order is carried across the wall (`r174h_cyc`), so `visitBetween_iff_key` on `𝓓L` and `not_visitBetween_nextVisit` apply; (iv) no kept `u` strictly between `Φ v'` and the first return: `arcBetween_iff_key` on `𝓓H` (the arc order of `𝓓sw.record` is that of `𝓓H.record`, `r174h_switch_arcBetween : Iff.rfl`) and `not_arcBetween_firstReturn` |
| `pair_eq` | — | `liftVisit_twin` on both lifts and `visitTransport_visitTwin` |
| `bit_eq` | — | `r174h_switch_overBit_of_ne` (a kept occurrence is not at `x'`), `overBit_eq_true_iff_parent` on both lifts, the divide sign `0 < det (edge ℓ) (edge ℓ')` carried by `GT_Endpoint.sign_eq` through `GT_det_pos_iff_of_sign` (`crossingSign P' i j = crossingSign P i j` at the crossing `{i, j} = c.val`, `visit_crossing_val_eq_pair`) |
| `sgn_eq` | — | `switch_sign_of_ne` + `geoPositiveLift_sign` (all `+1`) |

### 1c. The retained-crossing correspondence (the ownership transport of U_R174 §4 item 2, `writhe_wall`'s content)

Setting: `𝑾 := gsc_wall_of_endpoint hG hG' D hSm hSm' : GT_Wall … (triangleCrossings P e f g) (Q ∪ {m})`,
`τ qAB := GT_carrierEquiv 𝑾 qAB`.
* `r174h_not_tri_of_retained : c ∈ geoCarrierCrossings … (Q ∪ {m}) qAB → c.val ∉ triangleSupports e f g` — a retained
  crossing lies in `U(S)` (`geoCarrierCrossings_subset_U`, `mem_geoSupportUnselected_iff`), `m` is selected, and `x, w`
  interlace `m` (`D.hxm`, `D.hwm`; `D.tri_cases`).  Hence its visits are good marks: `r174h_good` (`GT_good_of_not_mem`).
* `r174h_owner' : geoOwner … (visitTransport hs v) = τ qAB` for a visit `v` of a retained crossing (`GT_owner_transport`).
* `r174h_mem_retained' : c ∈ retained(AB) → crossingTransport hs c ∈ retained(τ AB)`; `r174h_ne_x'`, `r174h_ne_w'` (the transport
  of a retained crossing is neither `x'` nor `w'`).
* `r174h_retained_of_mem' / ''` (converse): `c' ∈ retained(τ AB)`, `c' ≠ x', w'` → `(crossingTransport hs).symm c' ∈ retained(AB)`:
  `c'` is not `m'` (selected), so its preimage is outside the triangle, its visits are good, and `GT_owner_transport` +
  injectivity of `GT_carrierEquiv` give the owner `qAB`.
  Together: **`retained(τ AB) = transport(retained(AB)) ∪ {x', w'}`** given `hx', hw'` — the set identity behind `writhe_wall`
  ((9) `w_H = w_L + 2`) is available to the ledger realiser from these two lemmas (not stated as a `Finset` equation here).
* `r174h_key_lt`, `r174h_cyc`: the key order / cyclic order of visits of retained crossings of `AB` is carried by `𝑾.key_lt`
  (no reversed pair: `GT_not_rev_of_not_mem_left`; `GT_cyc_congr_of_lt`).
* `r174h_mem_retained_q`, `r174h_retained_of_mem_q`: the same at the variable `q'` through `hq'`.

### 1d. Record/diagram helpers (general, section `R174HRecord`)
`r174h_switch_record_succ`, `r174h_switch_record_pair` (`rfl`), `r174h_switch_arcBetween` (`Iff.rfl`),
`r174h_switch_overBit_of_ne`, `r174h_crossingOf_overVisit_eq_iff` (`record.crossingOf v = record.crossingOf (overVisit y₀) ↔ v.1 = y₀`,
by `crossingOf_eq_iff` + `mem_pair_twin_iff`); in the lift section `r174h_crossKeep_iff` (kept ↔ `v.1 ≠ lift w' ∧ v.1 ≠ lift x'`),
`r174h_lift_eq_iff` (`v.1 = s174_lift c hc ↔ (liftVisit v).1 = c`, `Equiv.eq_symm_apply`), `r174h_crossKeep_iff'` (kept ↔ the parent
crossing is neither `w'` nor `x'`), `r174h_record_componentCount`.

## 2. The stated Prop is provable only in a corrected (hypothesised) form — no ledger edit

`s174_hrec_prop hn hG hG' hSm hSm' qAB q' hx' hw'` binds an ARBITRARY carrier `q'` of the transported centre row, with no
`GT_Endpoint` configuration and no relation between `q'` and `qAB`.  As a universally quantified statement it is FALSE
(take `q'` a different carrier of `Q ∪ {m}` on `P'` owning `x', w'` — the two records have different crossing sets in general;
even for `q' = τ q` with `q ≠ qAB` the retained crossings differ).  It is exactly what `gsc_fulltwist_of_bigon` needs at the
binding `q' := W.τ qAB` of `gsc_Ledger.fulltwist`, and that is what is proved: the theorem adds the hypotheses
`D : GT_Endpoint …` (the configuration the whole site lives on — `s174_site` and `s174_fulltwist_of_hrec` already take it) and
`hq' : q' = GT_carrierEquiv (gsc_wall_of_endpoint hG hG' D hSm hSm') qAB`.  Nothing in `RALedgers` or in `Site_174`'s frozen
material is touched (rule (4)/(1)); the name follows rule (1) (`r174h__s174_hrec_prop_proof`, naming linter silenced locally).
The sign condition `hsgn` of the site is NOT needed for `hrec` (only for `s174_site`, hence for `r174h_fulltwist`).

## 3. What remains for row 174 (unchanged obligations, none of this unit)

| obligation | content | status |
|---|---|---|
| `hx'`, `hw'` (site inputs) | `x', w' ∈ geoCarrierCrossings hG'.cg S' (τ qAB)`: the four `ℓ₁/ℓ₂/ℓ₃`-visits of `x', w'` on `P'` are owned by `τ qAB` — the arc `[m'(ℓ₁) → … → m'(ℓ₃)]` (`GT_owner_arc`, `AV_nextCorner`), given the ledger's choice of `qAB` as the owner of `x(ℓ₂), w(ℓ₂)` on `P` (U_R174 §4 items 1–2).  Both `r174h__s174_hrec_prop_proof` and `r174h_fulltwist` take them as hypotheses | open, Site_174_REPORT §5 estimate 0.4–0.8k |
| `gsc_Ledger.qx`, `.fulltwist` | discharged by `r174h_fulltwist` once `hx', hw'` are supplied: `qx := lift x'`, `D₀` from the existential | done modulo `hx', hw'` |
| the rest of `gsc_Ledger` | items 1, 2 (`omega_wall`; `writhe_wall` — its set identity is §1c), 3, 5, 6 of U_R174 §4 | open (other units) |
| `exists_bigonData_of_triangle` (U-M7) | black box inside `s174_site` | Wave 1 |

## 4. Pitfalls met (for the 176 prover — the `j`-corner `hrec` is this construction with `(Q ∪ {m}, qAB, x', w') := (Q ∪ {j}, q₀, u', v')`)

1. **Never put the compound carrier `GT_carrierEquiv 𝑾 qAB` (or `W.τ qAB`) inside a lifted term.**  `geoCarrierShadow` is an
   `abbrev`; with a compound carrier the unifier unfolds it (through `GT_carrierEquiv`, `Quotient.lift`, …) on every type
   ascription `(geoPositiveLift … q).Γ.Crossing =?= (geoCarrierShadow … q).Crossing` and hits `maxHeartbeats` (200k, even 400k)
   — `example : (𝓓H).Γ.Crossing := 𝓵x` alone times out.  With a *variable* `q'` (as `s174_hrec_prop` binds it) plus
   `hq' : q' = τ qAB` everything is instantaneous; use `hq'` only in the ownership lemmas (`rw [hq']`, no shadows there).
   The same applies to any consumer statement: `r174h_fulltwist` is stated at `q'`, `hq'`, not at `W.τ qAB`.
2. **`rw`/`simp` cannot instantiate lemma metavariables at a `𝓓sw`-typed visit** (`(D.switch x₀).Γ.Visit` vs `D.Γ.Visit` is
   invisible at implicit transparency: "target expression is not type-correct under the `implicit` transparency level").
   Supply the lemma as a closed term first (`have h2 := overBit_eq_true_iff_parent … (Φ v').1`, `Diagram.switch_sign_of_ne (𝓓H) hne`,
   `CV.liftVisit_twin … _`) and `rw` with it, or use `exact`/`.trans`.  Note `Diagram.switch_sign_of_ne _ hne` infers `E := 𝓓sw`
   from `hne`'s type and produces a DOUBLE switch — pass `(𝓓H)` explicitly.
3. **`include` applies to theorems, a `def` gets only the variables its type mentions**: `r174h_keep` takes `hn hG' hSm' q' hx' hw'`
   while every theorem of the section takes the eleven `hn hG hG' D hSm hSm' qAB q' hq' hx' hw'` (`include` + `set_option
   linter.unusedSectionVars false`).  `rw [thm]` with an `include`d theorem whose extra arguments are not in the statement
   leaves goals `⊢ CV.Generic P`, `⊢ ZMod n`… — pass all arguments.
4. `{m}` inside `local notation` is ambiguous (structure instance vs singleton) at quotation precheck: write
   `Q ∪ (Singleton.singleton m : Finset (Crossing P))` (elaborates to the same term as `Q ∪ {m}`).  Notations used inside
   `variable` binders then re-elaborated in a nested section produced `Unknown constant hs✝` — write binder types without notations.
5. `rw [Diagram.overBit_eq_true_iff]` fails on `(E.switch x₀).overBit v` (same as 2); and after `unfold Diagram.isOver; rw [switch_overStrand_of_ne]`
   the goal `↑v.snd = E.overStrand v.fst ↔ ↑v.snd = E.overStrand v.fst` is not closed by `rw`'s `rfl` (coercion instances differ
   at reducible transparency) — finish with `exact Iff.rfl`.
6. `set_option … in` must precede the docstring, not sit between docstring and declaration.
7. The proofs `hG.crossingGeometry` vs `(s174_cg hn hG).cg` (and `GeoIndependent` at either) are accepted everywhere by proof
   irrelevance (Site_174_REPORT §6.10 confirmed); `Record.ArcBetween` of `(D.switch x₀).record` and of `D.record` are `Iff.rfl`.
