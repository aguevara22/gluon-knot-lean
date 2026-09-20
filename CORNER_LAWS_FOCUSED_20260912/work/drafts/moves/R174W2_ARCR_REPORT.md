# R174W2_ARCR_REPORT — unit ARCR (row 174, Wave 2, ROUTE R): the arc records of `x'` — `r174_arc_rec_moves` PROVED, row 174 CLOSED

Prover (subagent), 2026-09-15 23:05 UTC / 7:05pm ET (window 22:37–00:45 UTC; finished at 23:03 UTC).
File: **`work/drafts/moves/R174W2_ARCR.lean`** = `R174_Port_GenericSelectedUnits_draft.lean` (6847 lines, byte-identical:
`head -n 6847 R174W2_ARCR.lean | cmp - R174_Port_GenericSelectedUnits_draft.lean` prints nothing) + **597 appended lines
(6848–7444), 36 declarations, prefix `r174r_`**, one self-contained `namespace SM.Link … end SM.Link` block after the frozen
material (as SITEIN/WALL/SMOOTH did).  Inputs read: R174_ASSEMBLY_REPORT.md §3/§5, R174_SMOOTH_REPORT.md §1E/§2,
R174_HREC_REPORT.md §1b–1c/§4, R174_CARRIERS_REPORT.md §3, R174_WALL_REPORT.md §1b/§6, U_R174_REPORT.md §4 (via the
SMOOTH docstring), RProof/X1Rows3.lean (`GT_Endpoint`, `GT_Wall`, `GT_Rev`, `GT_not_rev_of_*`, `GT_cyc_congr_of_lt`,
`GT_det_pos_iff_of_sign`), SM/GeometricInterlacement.lean, SM/CrossingTransport.lean, SM/CarrierVisitTwin.lean,
SM/GeoCarrierCrossings.lean, CV/PieceIntrinsic.lean (`liftVisit*`).

## 0. Deliverables and checks

| item | result |
|---|---|
| compile `cd work/lean && lake env lean ../drafts/moves/R174W2_ARCR.lean` | **exit 0, 0 errors, 0 warnings** (no `sorry` warning, no linter note), 36 s |
| `grep -c sorry` | **2 before, 2 after** — both hits are the frozen header PROSE of the port draft (lines 8–9: "0 `sorry` warnings … (no sorryAx)"); **no `sorry` term anywhere**, none added |
| frozen material | nothing above line 6847 changed (byte-identical); no Prop of RALedgers / SMOOTH / the composition edited; the Prop `r174s_arc_rec_prop` / `r174_arc_rec` / `r174_arc_rec_moves` is PROVED as stated (rule (2) never needed); nothing under `work/lean` written; scratch in the session scratchpad only |
| **`#print axioms`** (scratch copy) | `r174r_arc_rec_moves_proof`, `r174r_arc_rec_at`, `r174r_w'_not_inArc`: **`propext, Classical.choice, Quot.sound`** only.  `r174r_gsc_moves`: `+ SM.lit_homfly, SM.lp_lm, SM.lp_lm_uniqueness` (the ledger's `Ω₁` reads, as the assembly report predicted for `r174_gsc_moves_of_arc_rec`).  `r174r_generic_selected`: `+ SM.lit_homfly_descent, SM.ng_finite_word, SM.src_contact` (through `CV.carrierSlotFloor`, exactly as `r174_generic_selected_of_arc_rec`).  **No `sorryAx`.**  All non-standard axioms are the registered literature axioms of `work/lean/axiom-policy.json` |
| reassessment rule | never triggered: three compile rounds in total (round 1: two `visitTwin_unique` orientation slips + a lemma name; round 2: `local notation` cannot carry `by`/projection syntax; round 3: clean) |
| black boxes consumed | **none**; nothing stated with `sorry`; the ARCV prover's material is NOT used (this file was built from the port draft alone) |

## 1. What is PROVED — the row closes

```
theorem r174r_arc_rec_moves_proof : r174_arc_rec_moves                              -- the ONE open Prop of row 174
theorem r174r_gsc_moves : gsc_moves := r174_gsc_moves_of_arc_rec r174r_arc_rec_moves_proof   -- unconditional
theorem r174r_generic_selected (hn) (E : CV.Event n) (e f g) (h3) (h4e) (h4f) (h4g) (hE : E.IsSimpleRIII e f g h3 h4e h4f h4g) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ E.radius ∧ GenericSelectedData hn E e f g δ                -- the FIXED signature of RProof.generic_selected
  := r174_generic_selected_of_arc_rec r174r_arc_rec_moves_proof hn E e f g h3 h4e h4f h4g hE
```
So `RProof.generic_selected := SM.Link.r174r_generic_selected` (or `r174_generic_selected_of_arc_rec r174r_arc_rec_moves_proof`)
closes the row-174 leaf with no interface edit.  The composition consumes exactly the applied form
`r174r_arc_rec hn hG hG' D hsgn hSm hSxw hSm' : r174_arc_rec hn hG hG' D hSm hSxw hSm'` (§1e).

### 1a. The `x`-arcs of `A`, `B` on `P` (section `R174RArcs`, WALL's world: `insert w (insert x Q)`, classical `insert`)
On the fixed Split `sp : r174w_Split D` (WALL's orientation case analysis; `xA` = the visit of `x` carried by `A`):
* `r174r_xA_ne_w₂`: the `Q ∪ {x}`-carrier of `xA` is not that of `w₂` — otherwise (`r174w_part_w`) `A` would carry a visit
  of `w`, but `wB ∈ B ≠ A` and `twin wB ∈ C' ≠ A` (both `sp.hcase` orientations; `r174w_sep_x_Sxw`, `r174w_qA_ne_qB`).
* **`r174r_arcA`**: `owner_{Q∪{x,w}} z = A ↔ z = xA ∨ (cycBetween (key (twin xA)) (key z) (key xA) ∧ z ∈ q₀)` — `A` is the
  unsplit `x`-child of `q₀` (`r174w_unaffected_w` + `r174w_split_x`).
* **`r174r_arcB`**: a visit of `B` other than `twin xA` lies in `(xA, twin xA)` — trichotomy of the keys
  (`cycBetween_or_of_ne`, `geometricVisitKey_injective`) and `r174r_arcA` for the other arc.
* `r174r_arcA_export`, `r174r_arcB_export`: the same at a support variable (`Sxw = insert w (insert x Q)` supplied inline
  by `ext … tauto`, WALL pitfall 6.2); `r174r_cyc_rotate`, `r174r_markKey_inj` helpers.

### 1b. Across the wall (section `R174RWall`)
* `r174r_twin_edge_ne : v.2.val ≠ (visitTwin v).2.val`; `r174r_not_mem_tri` (a retained visit of `AB` is not a triangle
  crossing, from HREC's `r174h_not_tri_of_retained`).
* **`r174r_cyc_x`**: for a retained visit `v` of `AB` and two visits `a, b` on different edges,
  `cycBetween (key a) (key v) (key b) ↔ cycBetween (key' a') (key' v') (key' b')` — `GT_cyc_congr_of_lt` with `GT_Wall.key_lt`
  on the three pairs (`GT_not_rev_of_not_mem_right/left` for `v`, `GT_not_rev_of_edge_ne` for `(b, a)`).  This is the only
  new key-order fact beyond HREC's `r174h_key_lt`/`r174h_cyc` (which need all three visits retained).
* `r174r_interlaces'`: `x'`, `w'` interlace on `P'` (`GT_Endpoint.compl` + `hxw`).
* **`r174r_w'_not_inArc`**: no visit of `w'` lies with its twin strictly inside an arc `(u₀, twin u₀)` of `x'` — the
  interlacing unfolds (`traversalBetween_iff_cycBetween`, `Iff.rfl`) to `cycBetween a₀ b₀ a₁ ∧ cycBetween a₁ b₁ a₀` on the
  keys; four cases `u₀ ∈ {a₀, a₁}`, `v' ∈ {b₀, b₁}` (`visitTwin_unique`), each killed by `cycBetween_asymm'`.  (SMOOTH §3
  had noted this fact "not formalised"; it is needed here for the converse direction of the occurrence bijection.)

### 1c. Route R core (section `R174RData`, variable `q'` with `hq' : q' = GT_carrierEquiv 𝑾 (r174c_qAB D)`)
* **`r174r_mem_iff`**: for a pair-row carrier `qX` with `hfwd` (retained visit of `qX` ⟹ retained visit of `AB` in the
  arc) and `hbwd` (retained visit of `AB` with both transported visits in the arc ⟹ retained by `qX`):
  `v ∈ retained(qX) ↔ (v' ∈ retained'(q') ∧ InArc u₀ v' ∧ InArc u₀ (twin v'))`.  (⇒) `r174h_mem_retained'`; (⇐) `v` is not a
  visit of `x` (`v'` would be `u₀` or `twin u₀`: `not_cycBetween_self_left`, `CV.cycBetween_ne`), not of `w`
  (`r174r_w'_not_inArc`), so `r174h_retained_of_mem'` gives `v ∈ retained(AB)` and `hbwd` applies.
* **`r174r_arcVisitData`**: `Nonempty (r174s_ArcVisitData (s174_cg hn hG) (s174_cg hn hG') qX q' u₀)` — `ψ := Equiv.subtypeEquiv
  (visitTransport hs) r174r_mem_iff` (the identity on parent visits, HREC's template restricted to the arc), `twin` by
  `visitTransport_visitTwin`, `cyc` by `r174h_cyc` (via `hfwd`), `det` by `GT_Endpoint.sign_eq` through
  `GT_det_pos_iff_of_sign` (HREC's `bit_eq` argument).

### 1d. The two arcs of the ledger (section `R174RMain`; all theorems take `hn hG hG' D hsgn hSm hSxw hSm'` in this order)
`qA = r174c_qA D = L_xw(m₁)`, `qB = r174c_qB D = L_xw(m₃)`, `qAB = r174c_qAB D = L_m(x₂)`; the `A`-arc starts at
`u₀A := (twin xA)'` (its twin is `xA'`, `r174r_twin_u₀A`), the `B`-arc at `xA'`.
* `r174r_qA_ne`, `r174r_qB_ne`, `r174r_qAB_ne`: retained visits are non-local (`m` is split between `A`, `B`: `r174c_hAB`;
  retained visits of `AB` are outside the triangle); `r174r_nonLocal` (CARRIERS' predicate).
* `r174r_qAB_of_qA`, `r174r_qAB_of_qB`: `retained(A), retained(B) ⊆ retained(AB)` — `r174c_owner_qAB_iff` (`AB ↔ A ∪ B` on
  non-local marks) + `r174c_mem_iff_of_outside`.
* `r174r_inArcA_iff`, `r174r_inArcB_iff`: the `P'`-arc condition read on `P` (`r174r_cyc_x`).
* `r174r_arcA_of_qA`, `r174r_arcB_of_qB`: retained visits of `A` (`B`) lie in `(twin xA, xA)` (`(xA, twin xA)`).
* **`r174r_qA_of_arcA`, `r174r_qB_of_arcB`** (the converses): a retained visit of `AB` in the `A`-arc is owned by `A` — it is
  owned by `A` or `B` (`r174c_owner_qAB_iff`), and `B`'s visits lie in the other arc (`cycBetween_asymm'`).
* `r174r_fwdA/B`, `r174r_bwdA/B`: the `hfwd`/`hbwd` of §1c for `qA`, `qB` (both visits of a retained crossing handled by
  `visitTwin_unique`).

### 1e. The Prop
* **`r174r_arc_rec_at (q') (hq') (hx') (hw') : r174s_arc_rec_prop hn hG hG' hSxw hSm' q' hx' (r174c_qA D) (r174c_qB D)`**:
  `u := (liftVisitEquiv).symm ⟨u₀A, _⟩` (the occurrence of `x'` on `D_H` at the parent visit `(twin xA)'`; `hu : u.1 = r174s_qx …`
  by HREC's `r174h_lift_eq_iff`), `liftVisit (pair u) = xA'` (`Diagram.record_pair_apply`, `liftVisit_twin`), then
  `r174s_arc_rec_of_visitData … u hu (Classical.choice A) (Classical.choice B)`.
* **`r174r_arc_rec : r174_arc_rec hn hG hG' D hSm hSxw hSm'`** at the binding `q' := W.τ (r174c_qAB D)` (`hq' := rfl`,
  `hx' hw' := r174x_hx'_tau / r174x_hw'_tau`), then `r174r_arc_rec_moves_proof`, `r174r_gsc_moves`, `r174r_generic_selected`.

## 2. On the route (why the record layer is SMOOTH's `r174s_recordIso_of_arcVisitData`)

The task asked for Route R "directly by the HREC template … do NOT go through `r174s_ArcVisitData` unless it is strictly
shorter".  It is strictly shorter, and it IS the HREC template: `r174s_recordIso_of_arcVisitData` (SMOOTH §1E, PROVED, frozen)
builds `RecordIso.ofOccOfCard` from an occurrence bijection with `succ_eq` by `cycNext_unique` / `not_arcBetween_firstReturn`,
`pair_eq` by `liftVisit_twin`, `bit_eq` by `overBit_eq_true_iff_parent`, `sgn_eq` by positivity — exactly the clauses of
`r174h_recordIso`, with the keep-set `KeepArc u` in place of HREC's `{≠ x', ≠ w'}`.  Re-deriving it here would have copied
≈150 lines verbatim.  What Route R contributes, and what is independent of the ARCV prover, is everything that FEEDS that
template: the occurrence bijection as `visitTransport` restricted to the retained visits of `A`/`B` (`r174r_mem_iff`,
`r174r_arcVisitData`), and the ownership/arc facts §1a, §1b, §1d.  Nothing from any ARCV file was read or used.

## 3. Findings / fidelity

1. **The Prop is TRUE as stated in every binder configuration** (both orientations of `r174w_sp`, both label orders);
   no corrected form was needed.  The occurrence `u` of `x'` that starts the `A`-arc is the one at `(twin xA)'`, i.e.
   `x'(ℓ₁)` in WALL's case B (`xA = x₂`) and `x'(ℓ₂)` in case A (`xA = x₁`) — consistent with SMOOTH's `∃ u`.
2. **`w'` is a mixed crossing of `D₀`** (its two visits lie in different arcs of `x'`): `r174r_w'_not_inArc` is the
   formalisation SMOOTH §3 left open; it is essential (without it the converse of the occurrence bijection fails).
3. `r174c_mem_iff_of_outside` takes no `D` argument; `r174h_mem_retained'`/`r174h_retained_of_mem'` (section `R174H`) are
   usable at a variable `q'` via `rw [hq']` without HREC's lift-section arguments `hx' hw'`.

## 4. Pitfalls met (for the port)

1. `local notation` cannot carry `by …` terms or projections `(t).field` (quot precheck fails: "no macro or
   `[quot_precheck]` instance for syntax kind `Lean.Parser.Term.byTactic` / `Term.proj`"); write `r174w_Split.xA (r174w_sp …)`
   and inline the `ext … tauto` proof at each use site (`set_option quotPrecheck false` was not needed).
2. `visitTwin_unique v w hc hne : w = visitTwin v` (the equation is oriented `w = twin v`, not `twin v = w`).
3. With `include hn hG hG' D hsgn hSm hSxw hSm'` every theorem of `R174RMain` takes the eight arguments in this order even
   when unused (`set_option linter.unusedSectionVars false`); the R174RWall section takes `hG hG' D hSm hSm'`, the R174RData
   section `hn hG hG' D hSm hSm' q' hq'`.
4. The classical `insert` of WALL's Config section must be bridged through a support variable with an inline `ext` proof,
   exactly as R174_WALL_REPORT §6.2 says; `r174r_arcA_export`/`r174r_arcB_export` are the bridge.
5. `traversalBetween_iff_cycBetween` is `Iff.rfl`, so `GeometricInterlaces`' witnesses are accepted directly as
   `cycBetween` facts on `geometricVisitKey` (`have c0 : cycBetween … := h0`).

## 5. Port notes

Library material (keep): `r174r_cyc_x` (key-order transport of a good visit relative to any two visits on different
edges — general `GT_Wall` fact), `r174r_w'_not_inArc` (interlacing ⟹ the two visits of one crossing separate the two of the
other, on keys), `r174r_mem_iff`/`r174r_arcVisitData` (the visit datum of an arc from `hfwd`/`hbwd`; re-usable for row 176's
arc identifications).  Row-specific: `R174RArcs` (the `x`-arcs of `A`, `B` on the Split), `R174RMain`, `R174RMoves`.  At port
time `RProof.generic_selected := SM.Link.r174r_generic_selected`; `r174r_gsc_moves` can replace the conditional
`r174_gsc_moves_of_arc_rec` in `RProof/GenericSelectedUnits.lean`.  Sizes: §1a 130 lines, §1b 95, §1c 100, §1d 200, §1e 70.
