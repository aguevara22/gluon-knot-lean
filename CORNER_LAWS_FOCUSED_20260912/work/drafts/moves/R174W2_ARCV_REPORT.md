# R174W2_ARCV_REPORT — unit ARCV (Route V, visit data): the open Prop `r174_arc_rec_moves` of row 174 is PROVED

Prover (subagent), 2026-09-15 23:10 UTC / 7:10pm ET.  File: `work/drafts/moves/R174W2_ARCV.lean`
(= `R174_Port_GenericSelectedUnits_draft.lean` byte-identical on its 6843 body lines + 483 appended lines,
prefix `r174v_`; 7326 lines).  Inputs read: R174_ASSEMBLY_REPORT.md (§3 the composition, §5 #1 the open Prop),
R174_SMOOTH_REPORT.md (§1E `r174s_ArcVisitData`, `r174s_arc_rec_of_visitData`, §2), R174_HREC_REPORT.md (§1b–1c
the transfer and the retained-crossing correspondence, §4 pitfalls), R174_CARRIERS_REPORT.md (§3
`r174c_owner_qAB_iff`), R174_WALL_REPORT.md (§1a `r174w_retained_qAB`, Part C `r174w_split_x`, `r174w_Split`,
§6.2 instance hygiene), RProof/X1Rows3.lean (`GT_Endpoint`, `GT_Wall.key_lt`, `GT_Rev`, `GT_cyc_congr_of_lt`,
`GT_det_pos_iff_of_sign`), SM/GeometricInterlacement.lean (`GeometricInterlaces`), SM/CrossingTransport.lean,
SM/CarrierVisitTwin.lean, CV/PieceIntrinsic.lean (`liftVisit*`), CV/GroupedKnot.lean (`arcBetween_iff_key`).

## 0. Deliverables and checks

| item | result |
|---|---|
| `R174W2_ARCV.lean` | 7326 lines = the port draft (lines 1–6843, `cmp` **byte-identical**) + the appended block "R174 ARCV" (15 declarations, all `r174v_`-prefixed; inside `namespace SM.Link` / `noncomputable section`, before the final `end` lines) |
| compile `cd work/lean && lake env lean ../drafts/moves/R174W2_ARCV.lean` | **exit 0, 0 errors, 0 warnings**, 33 s |
| `grep -c sorry` | **2 before, 2 after** — both hits are the draft's header comment (lines 8–9, "0 `sorry` warnings … no sorryAx"); no `sorry` anywhere in code |
| frozen material | nothing above line 6843 touched; the Prop `r174_arc_rec_moves` / `r174s_arc_rec_prop` NOT edited (rule 1); no Prop found false (rule 2 not needed); nothing under `work/lean` written; scratch in the session scratchpad only |
| **closed?** | **YES.** `r174v_arc_rec_moves_proof : r174_arc_rec_moves` is PROVED; hence `r174v_gsc_moves : gsc_moves` and `r174v_generic_selected` (the FIXED signature of `RProof.generic_selected`) are unconditional theorems |
| `#print axioms` (scratch copy) | `r174v_arc_rec_moves_proof`, `r174v_arcData`, `r174v_arcA_of_owner`, `r174v_not_both_inArc`: **`propext, Classical.choice, Quot.sound`** only.  `r174v_gsc_moves`: + `SM.lit_homfly, SM.lp_lm, SM.lp_lm_uniqueness` (the ledger's `Ω₁` reads, as predicted by R174_ASSEMBLY_REPORT §4).  `r174v_generic_selected`: + `SM.lit_homfly_descent, SM.ng_finite_word, SM.src_contact` (from `CV.carrierSlotFloor`, as predicted).  **No `sorryAx`.**  All non-standard axioms are the registered literature axioms of `work/lean/axiom-policy.json` |
| reassessment rule (3) | never triggered: three compile rounds in total (19 → 2 → 0 errors), every error an elaboration detail (§4); no lemma took two failed attempts |
| size | 483 lines against the assembly's estimate of 0.6–1.5k |

## 1. What is PROVED (all `r174v_`, namespace `SM.Link`, `open SM SM.GeoCarrier SM.Carrier RProof`)

### V0. Interlacing on the visit keys (section `R174VCyc`, no configuration)
* `r174v_interlaces_keys (hP) (h : GeometricInterlaces hP x y) : ∃ a b₀ b₁ : Visit P, a.1 = x ∧ b₀.1 = y ∧ b₁.1 = y ∧
  cycBetween (key a) (key b₀) (key (twin a)) ∧ cycBetween (key (twin a)) (key b₁) (key a)` —
  `GeometricInterlaces` unfolded (`geometricCrossingVisitBetween` = `traversalBetween` of the visit positions,
  `traversalBetween_iff_cycBetween`, `geometricVisitKey = traversalKey ∘ geometricVisitPosition` by `rfl`), the
  second `x`-visit identified with `visitTwin` of the first (`visit_eq_or_twin`).
* `r174v_not_both_inArc (h : GeometricInterlaces hP x y) (a) (ha : a.1 = x) (hall : ∀ b, b.1 = y → cycBetween (key a) (key b) (key (twin a))) : False`
  (`cycBetween_asymm'` in both placements of `a`).

### V1. The pair-row arcs on `P` (section `R174VArcP`; `hP : CrossingGeometry P`, `D : GT_Endpoint`, `sp : r174w_Split D`)
With WALL's instance hygiene activated locally (`attribute [local instance] Classical.propDecidable`,
`attribute [local instance high] r174w_decEqCrossing` — Part C's `insert` terms carry that instance, §4.1):
* `r174v_xA_not_w : L_x (inr sp.xA) ≠ L_x (inr D.w₂)` — `A` is the child of the `x`-split untouched by the
  `w`-split: otherwise `xA` lands on `L_xw w₂` or `L_xw w₃` (`r174w_part_w`), i.e. on `B` or `C'`
  (`sp.oB`, `sp.oC'`, `sp.hcase`; contradiction with `r174w_sep_m_Sxw` / `r174w_sep_x_Sxw`), four one-line cases.
* **`r174v_arcA_of_owner (T) (hT : T = insert w (insert x Q)) (z) (hz : z ≠ inr sp.xA) (h : L_T z = L_T (inr D.m₁)) :
  cycBetween (geoMarkKey (inr (twin sp.xA))) (geoMarkKey z) (geoMarkKey (inr sp.xA))`** — `L_xw z = L_xw xA`
  (`sp.oA`), so `L_x z = L_x xA` (`r174w_unaffected_w` with `r174v_xA_not_w`), so `z` lies in the `x`-child
  of `xA` = `{xA} ∪ (twin xA, xA)` (`r174w_split_x`, the component chosen by `sp.hcase`, `D.twin_x₁/x₂`).
* **`r174v_arcB_of_owner (T) (hT) (z) (hz : z ≠ inr (twin sp.xA)) (h : L_T z = L_T (inr D.m₃)) :
  cycBetween (geoMarkKey (inr sp.xA)) (geoMarkKey z) (geoMarkKey (inr (twin sp.xA)))`** — `z ∈ q₀`
  (`sp.onZ_B`), so `z` is in one of the two `x`-children (`r174w_part_x`); not `xA`'s (else `L_xw z = L_xw xA = qA ≠ qB`,
  `r174w_unaffected_w`, `r174w_sep_m_Sxw`), hence in `{twin xA} ∪ (xA, twin xA)`.

(The `T`/`hT` form is WALL's own bridge between `Q ∪ {x, w}` and `insert w (insert x Q)`: callers pass
`(Q ∪ {x, w}) (by ext c; simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]; tauto)`.)

### V2. Across the wall (section `R174VData`: `hn hG hG' D hSm hSm'`; nested `R174VArcData`: `hsgn hSxw q' hq' hx' hw'`)
* `r174v_nonLocal_of_not_tri (hv : v.1.val ∉ triangleSupports e f g) : r174c_NonLocal (inr v)` (`D.xT wT mT`).
* **`r174v_cyc_transport {a v} (hv : v.1.val ∉ triangleSupports) : cycBetween (key a) (key v) (key (twin a)) ↔
  cycBetween (key' (τ a)) (key' (τ v)) (key' (τ (twin a)))`** — `GT_cyc_congr_of_lt` with `𝑾.key_lt` on the
  three pairs: `(a, v)`, `(v, twin a)` have the non-triangle member `v` (`GT_not_rev_of_not_mem_right/left`),
  `(twin a, a)` lie on different edges (`GT_not_rev_of_edge_ne (visitTwin_edge_ne a)`).  No goodness of `a`
  needed: this is why the arc test at the visits of `x` transports although `x` is a triangle crossing.
* `r174v_retained_qAB_of_xw (hm : m ∉ retained_xw q₀) (hown : ∀ v, NonLocal (inr v) → L_xw v = q₀ → L_m v = qAB)
  (hc : c ∈ retained_xw q₀) : c ∈ retained_m (r174c_qAB D)` (`mem_geoCarrierCrossings` both sides; `c ≠ m` from `hm`).
* **`r174v_arcData (q₀) (hm) (hown) (a) (ha : a.1 = x) (H1) (H2) (u₀) (hu₀ : u₀ = τ a) :
  r174s_ArcVisitData (s174_cg hn hG) (s174_cg hn hG') q₀ q' u₀`** — the generic datum, `ψ := visitTransport hs`
  restricted, with
  `H1 : ∀ v, v.1.val ∉ tri → L_xw v = q₀ → cycBetween (key a) (key v) (key (twin a))` and
  `H2 : ∀ v, v.1.val ∉ tri → L_m v = qAB → cycBetween (key a) (key v) (key (twin a)) → L_xw v = q₀`:
  - forward: `c ∈ retained_xw q₀ ⊆ retained_m AB` (`r174v_retained_qAB_of_xw`), so `τ c ∈ retained' q'`
    (`r174h_mem_retained_q`); `τ v` and `τ (twin v)` lie in `(τ a, τ (twin a))` by `H1` + `r174v_cyc_transport`
    (`r174s_InArc` unfolded; `visitTransport_visitTwin`);
  - backward: for `v'` retained by `q'` with `v', twin v'` in the arc, `v := τ⁻¹ v'`; `v.1 ≠ x` since the arc is
    open at `τ a`, `τ (twin a)` (`visit_eq_or_twin`, `r174w_cyc_ne_left/right`); `v.1 ≠ w` since `x', w'`
    interlace on `P'` (`(D.compl x w D.xT D.wT D.xw).mpr D.hxw`) and every visit of `w'` would be in the arc
    (`r174v_not_both_inArc`); hence `v.1 ∈ retained_m AB` (`r174h_retained_of_mem_q`), its visits are `AB`-visits
    in the arc (transport back by `r174v_cyc_transport`), so `q₀`-visits by `H2`; `v.1 ∉ Q ∪ {x, w}`;
  - `twin`: `visitTransport_visitTwin`; `cyc`: `r174h_cyc` (the three visits are retained visits of `AB`);
    `det`: `visitTransport_edge`, `GT_det_pos_iff_of_sign (D.sign_eq _ _ _)` with `visit_crossing_val_eq_pair`
    (HREC's `bit_eq` pattern).
* **`r174v_dataA (sp) (u₀) (hu₀ : u₀ = τ (twin sp.xA)) : r174s_ArcVisitData … (r174c_qA D) q' u₀`** —
  `q₀ := qA = L_xw(m₁)`, `a := twin xA`: `hm` from `L_xw m₃ = qB ≠ qA` (`r174c_hAB`), `hown` from
  `r174c_owner_qAB_iff … |>.mpr (Or.inl _)`, `H1 := r174v_arcA_of_owner`, `H2`: `L_xw v ∈ {qA, qB}`
  (`r174c_owner_qAB_iff`), and `qB` is excluded by `r174v_arcB_of_owner` + `r174w_cyc_asymm`
  (`visitTwin_involutive` for `twin (twin xA)`).
* **`r174v_dataB (sp) (u₀) (hu₀ : u₀ = τ sp.xA) : r174s_ArcVisitData … (r174c_qB D) q' u₀`** — symmetric
  (`a := xA`, `H1 := r174v_arcB_of_owner`, `qA` excluded by `r174v_arcA_of_owner`).

### V3. The open Prop
* **`r174v_arc_rec_at (sp : r174w_Split D) : r174s_arc_rec_prop hn hG hG' hSxw hSm' q' hx' (r174c_qA D) (r174c_qB D)`**
  (at a variable `q'` with `hq' : q' = GT_carrierEquiv (gsc_wall_of_endpoint …) (r174c_qAB D)`, HREC pitfall 1):
  `u := liftVisitEquiv.symm ⟨τ (twin xA), _⟩` (an occurrence of `x'` on `D_H`: `u.1 = r174s_qx …` by
  `r174h_lift_eq_iff`), `liftVisit u = τ (twin xA)` (`liftVisit_symm`), `liftVisit (pair u) = τ xA`
  (`Diagram.record_pair_apply`, `liftVisit_twin`, `visitTransport_visitTwin`, `visitTwin_involutive`);
  then `r174s_arc_rec_of_visitData … u hu (r174v_dataA … sp _ hu1) (r174v_dataB … sp _ hu2)`.
* **`r174v_arc_rec_moves_proof : r174_arc_rec_moves`** — `intro` the binders of `gsc_moves`, then
  `r174v_arc_rec_at hn hG hG' D hSm hSm' hsgn hSxw _ rfl (r174x_hx'_tau …) (r174x_hw'_tau …) (r174w_sp hG hG' D)`
  (`W.τ (r174c_qAB D)` is `GT_carrierEquiv (gsc_wall_of_endpoint …) (r174c_qAB D)` by `rfl`).
* **`r174v_gsc_moves : gsc_moves := r174_gsc_moves_of_arc_rec r174v_arc_rec_moves_proof`.**
* **`r174v_generic_selected (hn) (E) (e f g) (h3 h4e h4f h4g) (hE : E.IsSimpleRIII …) : ∃ δ, 0 < δ ∧ δ ≤ E.radius ∧ GenericSelectedData hn E e f g δ`**
  `:= r174_generic_selected_of_arc_rec r174v_arc_rec_moves_proof …` — the FIXED statement of
  `RProof.generic_selected` (work/drafts/cvtail/Statements_FINAL.lean:738), now with NO extra hypothesis.

## 2. The mathematics, in one paragraph (why the arcs are what they are)

On `P`, the geo layer's insertion child data (`r174w_split_x`) says: inserting `x` into `Q` splits the carrier
`q₀` of the six local visits into `{x₂} ∪ (x₁, x₂)` and `{x₁} ∪ (x₂, x₁)` in the mark-key order.  Inserting `w`
afterwards splits only the child containing `w₂, w₃`; the other child is `A` (`r174v_xA_not_w`: it carries `xA`
and `m₁`, while `B` carries `wB` and `C'` carries `twin wB`, `r174w_Split`).  So `A ∖ {xA} ⊂ (twin xA, xA)` and
`B ∪ C' ∖ {twin xA} ⊂ (xA, twin xA)`, in particular `B ⊂ (xA, twin xA)` — in BOTH orientations of `r174w_Split.hcase`
(case `xA = x₂`: `A = m₁ α₁ x₂`, `B = m₃ w₃ α₂`; case `xA = x₁`: `A = m₁ x₁ α₂`, `B = w₂ m₃ α₃`).  Across the wall the
key order of a non-triangle visit relative to ANY visit is carried (`𝑾.key_lt`, reversed pairs need two
triangle crossings on one edge), and the two visits of `x` lie on different edges, so the arc test `v ∈ (a, twin a)`
at a visit `a` of `x` is carried verbatim (`r174v_cyc_transport`).  Hence on `D_H = carrierDiagram (τ AB)`, whose
arc order is the `P'`-key order (`arcBetween_iff_key`), the retained crossings of `τ AB` strictly inside the arc
`(τ (twin xA), τ xA)` with both occurrences are exactly the transports of `retained(A)` (a mixed `A`–`B` crossing has
one visit on each side; `w'` has one visit on each side because `x', w'` interlace on `P'`, `D.compl`; `x'` bounds
the arc), and likewise `(τ xA, τ (twin xA))` for `B`.  This is U_R174 §4 items 1–2 (`x'(ℓ₁) [A] w'(ℓ₂) x'(ℓ₂) [B] w'(ℓ₃)`)
in arc form, exactly as SMOOTH §2 stated it; the Prop is TRUE as stated and needed no correction.

## 3. Composition — what closes now (no interface edit)

```
theorem RProof.generic_selected … := SM.Link.r174v_generic_selected hn E e f g h3 h4e h4f h4g hE   -- FIXED signature
theorem gsc_moves_holds : gsc_moves := SM.Link.r174v_gsc_moves
```
`RALedgers.lean` is untouched by this unit (as by every unit and the assembler).  For the port of
`RProof/GenericSelectedUnits.lean` the assembly report's §7 applies unchanged; the ARCV block is row-specific
material except V0 (`r174v_interlaces_keys`, `r174v_not_both_inArc`: `GeometricInterlaces` on visit keys,
SM/GeometricInterlacement material) and `r174v_cyc_transport` (a `GT_Wall` lemma: arc tests at a same-crossing
pair transport for every non-triangle visit; RProof/X1Rows3 material, reusable by row 176's `j`-corner arcs).

## 4. Pitfalls met (three compile rounds; for the 176 prover)

1. **Instance hygiene of WALL Part C** (R174_WALL_REPORT §6.2): `r174w_split_x`, `r174w_part_x/w`,
   `r174w_unaffected_w`, `r174w_sep_*` and the fields of `r174w_Split` elaborate `insert x Q` with the local
   `r174w_decEqCrossing` (priority `high`), while a plain section elaborates it with `instDecidableEqCrossing`;
   the terms are then not syntactically equal ("Application type mismatch … `@Finset.instInsert _ r174w_decEqCrossing`"
   vs `instDecidableEqCrossing`, 11 errors in round 1).  Fix: activate the same two local instances in the section
   that consumes Part C (V1), and export its results through a support variable `T` with `hT : T = insert w (insert x Q)`
   (`subst hT` inside), so that ledger-facing sections (default instances) call them at `(Q ∪ {x, w})` with the
   `ext/simp only/tauto` equation — WALL's own bridge.  Do NOT activate the instance in ledger-facing sections.
2. **`include` does not add unused variables to a `def`.**  With `include hsgn hSxw q' hq' hx' hw'` in force,
   the structure-valued `def r174v_arcData` still took only the variables its type or body uses
   (`hn hG hG' D hSm hSm' q' hq' hx' hw'`, not `hsgn hSxw`), while every `theorem` took all of them; a call with the
   theorem-style argument list misaligned by two and produced cascading "No goals" / "Or.casesOn can only
   eliminate into Prop" errors in the lambda arguments (their expected types were metavariables).  Rule: for a `def`
   in an `include` section, list its arguments by usage; a failing body also shrinks its argument list
   (round 1 showed `r174v_dataA` without `hSm`), so fix the innermost error first.
3. **`visitTwin (visitTwin xA)`**: the datum for `A` is at `a := twin xA`, so `H1`'s conclusion reads
   `key (twin (twin xA))` where the `P`-side lemma gives `key xA`; `rw [visitTwin_involutive]` at the goal (or at
   `hcyc`), plus `simp only [geoMarkKey_visit]` to align `geoMarkKey (Sum.inr v)` with `geometricVisitKey v`
   (the latter is `rfl` but not syntactic).
4. `absurd (Subtype.ext (congrArg … h)).symm hx` left the middle type as `Sigma.snd ?m = Sigma.snd ?m`
   (postponed elaboration of `h`); an explicit `have h' : x₁ = x₀ := …` fixes it.
5. The `[NeZero n]` section instance is unused by the pure key lemmas of V0 → `omit [NeZero n] in` (else a linter
   warning; the file is warning-free).
6. Confirmed from HREC: keep `q'` a variable with `hq'` and instantiate `q' := W.τ (r174c_qAB D)`, `hq' := rfl`
   only in the final theorem; `CV.carrierDiagram hn hG' hSm' q'` and `geoPositiveLift hn (s174_cg hn hG') … q'`
   unify silently at the variable.

## 5. Nothing remains open for row 174 on the library base

| obligation (R174_ASSEMBLY_REPORT §5) | status |
|---|---|
| #1 `r174s_arc_rec_prop` at the ledger's binding, quantified as `r174_arc_rec_moves` | **PROVED** (`r174v_arc_rec_moves_proof`, standard axioms) |
| #2 the skeleton leaves behind `s174_site` / `gsc_fulltwist_of_bigon` | in the library (`SM/BigonDeletion.lean`); this file imports it — no `sorryAx` |
| #3 `G11_core_sw` | not reached by row 174 |

Black boxes consumed: **none** (no `def : Prop` stated, no hypothesis left unproved).
