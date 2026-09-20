# W4_SITEH_REPORT — wave 4, unit SITEH (prefix `s7sh_`; the I-110 record identification `hrec`), 2026-09-19 06:25 UTC / 2:25am ET

File: `work/drafts/corner/W4_SITEH.lean` (9379 lines, sha256 `0fe7557007b538c6f1f77d58c3618877205bc812f7eaacaab8ab07a2558e4895`)
= `W3_Assembled.lean` (8958 lines, sha256 `109050d918ecd5371c8a…`) + ONE inserted block.  `diff W3_Assembled.lean W4_SITEH.lean`
= `8615a8616,9036` — 421 lines (the 420-line block + one blank) inserted immediately BEFORE the docstring of the sorried black box
`s7z_returned_of_FSector` (B2; its docstring names "units SITE + BLOCK + ROT + RET" as suppliers — the sorried declaration this
unit serves), inside K's `section S7ZBigon`; **0 deleted lines**, so every existing statement/name/docstring and the five frozen
declarations are byte-identical; every existing line after 8615 moved by +421.  **No sorry body replaced**: the unit's content is
SITE's STATED Prop `s7s_hrec_prop` (a `def … : Prop`, not a sorried theorem), which is now PROVED in the applied form
(`s7sh_hrec_prop_side`) and at the carrier level (`s7sh_hrec_prop_carrier`).  **23 declarations** (19 theorems, 3 defs,
1 Prop-structure), all `s7sh_`-prefixed, in two nested sections `S7SHCarrier` / `S7SHGerm`; no import, no `open` at the
`VertexEdge` level (`open GeoCarrier RProof` inside the two sections, as SITE does), no `variable` outside the sections.
Check (official): `cd work/lean && lake env lean ../drafts/corner/W4_SITEH.lean` — **0 errors, exit 0, 32 s** (load ≈ 2.4);
**exactly 12 `declaration uses sorry`** (unchanged set): 4437 `s7q_box_ret`, 4519 `s7q_box_carriers`, 4844 `s7_sliding_law_at`,
5371 `s7f_exists_bigonSplit`, 5388 `s7f_exists_twoNewbornTerm`, 5725 `s7f_exists_ineligible_transport`, 6972 `s7s_clear_local`,
7018 `s7s_wallTriangleData_of_bigon`, 8600 `s7z_F_exists`, 9041 `s7z_returned_of_FSector`, 9060 `s7z_oneNewborn_exists`,
9327 `s7_bigon_law_at`; **0 other warnings** (no linter output).  `grep -c sorry`: **20 → 20** (12 bodies + the same 8 prose
mentions; the block contains no `sorry`).
`python3 tools/stmt_check.py W4_SITEH.lean`: output **identical** to `W3_Assembled.lean`'s (4/49 PASS; the draft carries only
the four row-110 declarations of the 49 frozen ones and `thm_C_S7`'s base text differs in both files exactly as before — pre-existing,
as W4_FB1_REPORT notes).  Clash scan: `grep -rln s7sh_ work/lean/{SM,CV,Bridge,RProof,Supplemental}` empty; no other draft in
`work/drafts/corner` uses the prefix.
Axioms (`#print axioms` on a scratch copy of the WHOLE file with the print lines after `end SM`): **every `s7sh_` declaration =
`[propext, Classical.choice, Quot.sound]`** — `s7sh_hrec_prop_side`, `s7sh_hrec_prop_carrier`, `s7sh_hrec_unswitched`,
`s7sh_recordIso`, `s7sh_succ`, `s7sh_Φ`, `s7sh_wallData_side`, `s7sh_other_side_free`, `s7sh_cycBetween_iff`, `s7sh_key_lt`,
`s7sh_crossKeep_iff` printed; no `sorryAx`, no literature axiom.  Unchanged: `thm_C_S7` = `[propext, sorryAx, Classical.choice,
Quot.sound, lit_homfly, lit_homfly_descent, lp_lm, lp_lm_uniqueness, ng_finite_word, src_contact]`; `s7z_returned_of_FSector` =
`[propext, sorryAx, Classical.choice, Quot.sound, lit_homfly]` (its own sorry).
Black boxes consumed: **none**.  New `s7sh_` Props with `sorry`: **none**.  Nothing believed false.
Reassessment rule: **not triggered** — no lemma took two failed attempts; three compile rounds on the scratch harness (§3).
Nothing written under `work/lean`; scratch files in the session scratchpad (`siteh/SiteMini*.lean`, `W4_SITEH_axioms.lean`).

## 0. What was closed, in one paragraph

**The record identification `hrec` of PLAN_FINAL §3.3 bigon (2) — SITE's stated Prop `s7s_hrec_prop` (W3_SITE_REPORT §3, estimated
1,000-1,650 lines) — is PROVED in 420 lines.**  In SITE's reduction the switch is already gone (`s7s_hrec_prop_of_unswitched`), so
what remained was the persistent-visit transport `D_H.record − {x, y} ≅ D_L.record` between the positive lifts of the full contact
carrier `q` on the bigon side `P` and of its U110-A transport `q' = s7a_sideComponentEquiv … q` on the far side `Q`.  The proof is the
R-lane wall-record pattern (`s176_hrec_unswitched_of_succ` / `r176h_succ`, `r174h_transfer`) with the bigon-wall crossing map in
place of `crossingTransport`: the kept occurrences of `D_H` are exactly those whose parent crossing is persistent
(`s7sh_crossKeep_iff`: the keep set `s7s_keepOf D_H (lift x) (lift y)` deletes `x, y`, and `x, y` are the ONLY affected crossings of
`P`, `s7sh_affected_iff`); the occurrence bijection `s7sh_Φ` is `CV.liftVisit` followed by `s7a_visit` (inverse through
`contactVisitTransport`, `s7sh_back`), with `CV.liftVisit (Φ v) = s7a_visit hs (CV.liftVisit v)` (`s7sh_Φ_liftVisit`).  The five
clauses: `comp` (one circle each), `pair` (`CV.liftVisit_twin` + `s7a_visit_twin`), `bit` (both lifts positive; the over bit is the
divide convention on the parent's two edges, `CV.overBit_eq_true_iff_parent`, and `s7a_side_sgn` carries `crossingSign`, read by
SITE's `s7s_pos_iff_of_sign_eq`), `sgn` (all `+1`, `geoPositiveLift_sign`), and `succ` (`s7sh_succ`): `cycNext_unique` on the
`D_L` traversal coordinate — the two candidates for the successor of `Φ v` both differ from `Φ v` (`restrictCrossings_succ_val_eq_iff`,
`record_succ_eq_self_iff` with the twin) and neither has an occurrence strictly between: for the `D_L` successor by
`record_succ_no_between`; for the transported first return by reading the cyclic order of three occurrences of a positive lift as the
cyclic order of their PARENT visits' traversal keys on the polygon (`CV.visitBetween_iff_key`, lem:carrierword — an independent
support's carrier traverses its blocks in the polygon's order), carrying it across the wall with U110-A's `s7a_markKey_lt`
(`s7sh_key_lt`, `s7sh_cycBetween_iff`: `geometricVisitKey` IS `markKey` on visit marks, `rfl`), and then reading it back as
`Record.ArcBetween` (`CV.arcBetween_iff_key`) against the distance characterisation of the restricted successor
(`Record.arcBetween_restrictCrossings_succ_iff`).  At the germ, the transport data are U110-A's side lemmas verbatim
(`s7a_side_hs`, `s7a_side_hpar`, `s7a_side_sgn`), the far side is contact-free by the bigon crossing pattern of `vertex_sides`
(`s7sh_other_side_free`), and the carrier correspondence is `s7a_side_mem_carrierCrossings` read through
`s7s_mem_geoCarrierCrossings_iff`; `positiveLift` of `e q` is `geoPositiveLift` of `s7s_geoComp (e q)` by `s7s_geoPositiveLift_eq`.

## 1. Proved (all `s7sh_`; inside `section VertexEdge` → K's `section S7ZBigon` → nested `S7SHCarrier` / `S7SHGerm`)

### 1.1 `section S7SHCarrier` (lines 8639-8944; `variable {P Q : LabelledTuple n} {M a : ZMod n}`, then in order
`(hx : IsCrossing P {M - 1, a}) (hy : IsCrossing P {a, M}) (hn) (hG : CarrierGeometry P) {S} (hS : GeoIndependent hG.cg S)
(q : GeoComponent hG.cg S) (hxq) (hyq) (hP : Generic P) (hQ : Generic Q) (hG' : CarrierGeometry Q) (hs) {S'} (hS') (q')
(W : s7sh_WallData hG q hG' hs q')`; each declaration takes the variables its statement mentions plus the `include`d ones, in this order)

| line | declaration | content |
|---|---|---|
| 8647 | `s7sh_visit_congr hs (h : v = w) hv hw : s7a_visit hs v hv = s7a_visit hs w hw` | proof-irrelevant congruence (`subst; rfl`) |
| 8656 | `def s7sh_back hs hQa (w : Visit Q) : Visit P` | `((contactVisitTransport hs).symm ⟨w, hQa w.1⟩).1` |
| 8661-8673 | `s7sh_back_not_affected`, `s7sh_visit_back` (`s7a_visit hs (back w) _ = w`), `s7sh_back_visit` (`back (s7a_visit hs v hv) = v`) | the `Equiv` laws of `contactVisitTransport` |
| 8682 | `s7sh_affected_iff hx hy c : ContactAffected M a c.val ↔ c = xPair hx ∨ c = xPair hy` | `Finset.pair_comm`, `Subtype.ext` |
| 8697 | `s7sh_fst_eq_lift_iff hn hG hS q v hc : v.1 = s7s_lift hn hG hS q c hc ↔ (CV.liftVisit hn hG hS q v).1 = c` | the `s176_fst_eq_lift_iff` pattern (`CV.liftVisit_fst`, `geoCarrierCrossingEquiv`) |
| 8714 | **`s7sh_crossKeep_iff hx hy hn hG hS q hxq hyq v : D_H.record.CrossKeep (s7s_keepOf D_H (lift x) (lift y)) v ↔ ¬ ContactAffected M a (CV.liftVisit hn hG hS q v).1.val`** | via SITE's `s7s_crossingOf_eq_iff_fst` |
| 8735 | **`structure s7sh_WallData hG q hG' hs q' : Prop`** — fields `par` (= the `hpar` of `s7a_markKey_lt`), `sgn` (= `s7a_side_sgn`'s conclusion), `free : ∀ c : Crossing Q, ¬ ContactAffected M a c.val`, `cross : ∀ c hc, c ∈ geoCarrierCrossings hG.cg S q ↔ s7a_cross hs c hc ∈ geoCarrierCrossings hG'.cg S' q'` | U110-A's transport data in the form the record identification consumes |
| 8751 | `s7sh_key_lt hn hG q hP hQ hG' hs q' W w₁ w₂ h₁ h₂ : geometricVisitKey hG'.cg (s7a_visit hs w₁ h₁) < … (s7a_visit hs w₂ h₂) ↔ geometricVisitKey hG.cg w₁ < geometricVisitKey hG.cg w₂` | `s7a_markKey_lt` at `Sum.inr`; `geometricVisitKey = markKey ∘ inr` by `rfl` |
| 8761 | **`s7sh_cycBetween_iff … w₁ w₂ w₃ h₁ h₂ h₃`** | the three-key transport (`unfold cycBetween; rw` ×3) |
| 8772, 8782 | `s7sh_mem_of_keep`, `s7sh_back_mem` | the two membership proofs of `s7sh_Φ` from `W.cross` |
| 8793 | **`def s7sh_Φ hx hy hn hG hS q hxq hyq hG' hs hS' q' W : {v // D_H.record.CrossKeep 𝓚 v} ≃ D_L.Γ.Visit`** | `toFun v := (CV.liftVisitEquiv q').symm ⟨s7a_visit hs (CV.liftVisit q v.1) _, _⟩`; `invFun w := ⟨(CV.liftVisitEquiv q).symm ⟨s7sh_back hs W.free (CV.liftVisit q' w), _⟩, _⟩`; inverses by `CV.liftVisit_injective` + `CV.liftVisit_symm` |
| 8824 | **`s7sh_Φ_liftVisit … v : CV.liftVisit hn hG' hS' q' (s7sh_Φ … v) = s7a_visit hs (CV.liftVisit hn hG hS q v.1) _`** | `CV.liftVisit_symm` |
| 8838 | **`s7sh_succ hx hy hn hG hS q hxq hyq hP hQ hG' hs hS' q' W v : s7sh_Φ … ((D_H.record.restrictCrossings 𝓚).succ v) = D_L.record.succ (s7sh_Φ … v)`** | `cycNext_unique` on `D_L.visitCoord` (§0) |
| 8886 | **`def s7sh_recordIso … : RecordIso (D_H.record.restrictCrossings 𝓚) D_L.record`** | `e := Equiv.refl (Fin 1)`, `Φ := s7sh_Φ`, the five clauses |
| 8931 | **`s7sh_hrec_unswitched … : Nonempty (RecordIso (D_H.record.restrictCrossings (s7s_keepOf D_H (s7s_lift … hxq) (s7s_lift … hyq))) D_L.record)`** | exactly the hypothesis of `s7s_hrec_prop_of_unswitched` |
| 8939 | **`s7sh_hrec_prop_carrier hx hy hn hG hS q hxq hyq hP hQ hG' hs hS' q' W : s7s_hrec_prop hn hG hS q hx hy hxq hyq (geoPositiveLift hn hG' hS' q')`** | `s7s_hrec_prop_of_unswitched` |

Here `D_H := geoPositiveLift hn hG hS q`, `D_L := geoPositiveLift hn hG' hS' q'`, `𝓚 := s7s_keepOf D_H (s7s_lift hn hG hS q _ hxq)
(s7s_lift hn hG hS q _ hyq)` (written out in the file; no notation is used).

### 1.2 `section S7SHGerm` (lines 8946-9035; `variable (hn) (g : WallGerm n) {M a} (h : g.BigonAt M a) {r η} {t : g.SideParameter} (b : Bool)`)

| line | declaration | content |
|---|---|---|
| 8956 | `s7sh_other_side_free hn g h b hx hy : ¬ IsCrossing (side (!b)) {a, M - 1} ∧ ¬ IsCrossing (side (!b)) {a, M}` | `BigonCrossingPattern` from `((vertex_sides hn g h.1).2.2.2.1 t t).2.1 h.2`, `cases b` |
| 8976 | `s7sh_other_side_not_affected hn g h b hx hy c : ¬ ContactAffected M a c.val` (`c : Crossing (side (!b))`) | = `free` |
| 8987 | **`s7sh_wallData_side hn g h b hL hx hy S S' hSS' hSp hSp' q : s7sh_WallData (s7s_cg hn (s7a_sideGeneric g b)) (s7s_geoComp … q) (s7s_cg hn (s7a_sideGeneric g (!b))) (s7a_side_hs hn g hL b (!b)) (s7s_geoComp … (s7a_sideComponentEquiv hn g hL b (!b) S S' hSS' hSp hSp' q))`** | `par := s7a_side_hpar`, `sgn := s7a_side_sgn hn g h.1 hL b (!b)`, `free` as above, `cross` := `s7a_side_mem_carrierCrossings` through `s7s_mem_geoCarrierCrossings_iff` ×2 |
| 9010 | **`s7sh_hrec_prop_side hn g h b hL hx hy S S' hSS' hSp hSp' hS hS' q hxq hyq : s7s_hrec_prop hn (s7s_cg hn (s7a_sideGeneric g b)) (s7s_geoIndependent hn _ S hS) (s7s_geoComp hn _ S q) hx hy hxq hyq (positiveLift hn (s7a_sideGeneric g (!b)) S' (s7a_sideComponentEquiv hn g hL b (!b) S S' hSS' hSp hSp' q) hS')`** | `rw [← s7s_geoPositiveLift_eq]`, then `s7sh_hrec_prop_carrier` with `s7sh_wallData_side` |

Exact signature of the applied form (from `#check`):
```
s7sh_hrec_prop_side (hn : 3 ≤ n) (g : WallGerm n) {M a : ZMod n} (h : g.BigonAt M a) {r η : ℝ} {t : g.SideParameter} (b : Bool)
    (hL : s7a_SideLocal hn g M a r η t)
    (hx : IsCrossing (g.curve (g.sideTime b t)) {M - 1, a}) (hy : IsCrossing (g.curve (g.sideTime b t)) {a, M})
    (S : Finset (Crossing (g.curve (g.sideTime b t)))) (S' : Finset (Crossing (g.curve (g.sideTime (!b) t))))
    (hSS' : ∀ (v : Visit (g.curve (g.sideTime b t))) (hv : ¬ ContactAffected M a v.1.val),
      (s7a_visit (s7a_side_hs hn g hL b (!b)) v hv).1 ∈ S' ↔ v.1 ∈ S)
    (hSp : ∀ x ∈ S, ¬ ContactAffected M a x.val) (hSp' : ∀ x ∈ S', ¬ ContactAffected M a x.val)
    (hS : IsDecomposition hn (s7a_sideGeneric g b) S) (hS' : IsDecomposition hn (s7a_sideGeneric g (!b)) S')
    (q : Component hn (s7a_sideGeneric g b) S)
    (hxq : xPair hx ∈ geoCarrierCrossings (s7s_cg hn (s7a_sideGeneric g b)).cg S (s7s_geoComp hn (s7a_sideGeneric g b) S q))
    (hyq : xPair hy ∈ geoCarrierCrossings (s7s_cg hn (s7a_sideGeneric g b)).cg S (s7s_geoComp hn (s7a_sideGeneric g b) S q)) :
    s7s_hrec_prop hn (s7s_cg hn (s7a_sideGeneric g b)) (s7s_geoIndependent hn (s7a_sideGeneric g b) S hS)
      (s7s_geoComp hn (s7a_sideGeneric g b) S q) hx hy hxq hyq
      (positiveLift hn (s7a_sideGeneric g (!b)) S' (s7a_sideComponentEquiv hn g hL b (!b) S S' hSS' hSp hSp' q) hS')
```
(`s7a_sideGeneric g b` is a proof of `Generic (g.curve (g.sideTime b t))`; any other proof — `(g.sideTuple b t).2`, `s7f_hP₂ g M a t` —
is accepted by proof irrelevance, and `(g.sideTuple b t).1` is `g.curve (g.sideTime b t)` by `rfl`.)

## 2. Not proved

Nothing of this unit's content is open.  The two SITE black boxes `s7s_clear_local` (6972) and `s7s_wallTriangleData_of_bigon`
(7018) are NOT this unit's (SITEC / U110-A-B); the twelve pre-existing sorries are untouched.  The bare `s7s_hrec_prop … DL` for an
ARBITRARY `DL` is of course not provable (as with row 174's `s174_hrec_prop`, OPEN_ITEMS §C-09); the proved instance is the one the
plan names — `DL = positiveLift` of U110-A's transported carrier — and the carrier-level form covers any `q'` satisfying `s7sh_WallData`.

## 3. Method audit (reassessment discipline)

Not triggered (no lemma failed twice).  Three compile rounds on a scratch harness (`SiteMini.lean` = the skeleton header + the SITE
block + this block, 14 s per round; the unit depends on SITE and the library only):
1. Missing `include hn/hP/hQ/W in` on lemmas that use them only in proofs, and two call-site signature slips (`hS`/`hS'` are not
   included when the statement mentions no lift of that side).
2. The `rw` motive failure of W3_SITE_REPORT §6 item 1 in a new guise: after a `change`/`rw` that unfolds `Diagram.record` etc., the
   target is "not type-correct at implicit transparency" because `s7s_keepOf (geoPositiveLift …) (s7s_lift …)` mixes
   `(geoCarrierShadow …).Crossing` with `(geoPositiveLift …).Γ.Crossing`, and `rw [s7sh_Φ_liftVisit]` with a metavariable `?v` then
   fails to find its pattern.  Fix (applied uniformly in `s7sh_succ`, `pair_eq`, `bit_eq`): instantiate the equation first
   (`have e := s7sh_Φ_liftVisit … v`) and rewrite INSIDE freshly stated hypotheses (`rw [e1, e2, e3] at hb2`, `rw [e] at h1`),
   finishing with `exact` up to defeq — never `rw` on a target that a `change` has already unfolded.
3. A wrong-direction `.mp` in `right_inv` (the persistence proof of `CV.liftVisit (symm …)` is `by rw [CV.liftVisit_symm]; exact
   s7sh_back_not_affected …`, not an instance of `s7sh_crossKeep_iff`).
Estimate vs actual: W3_SITE_REPORT §3 put `hrec` at 1,000-1,650 lines (crossing correspondence 200-350, cyclic order 300-500, bits 100,
assembly 400-700); it took 420 lines because (i) the cyclic-order step is 30 lines — `CV.visitBetween_iff_key` already reads the
cyclic order of a positive lift's occurrences on the PARENT visits' traversal keys, and `geometricVisitKey` is `markKey` on visit
marks by `rfl`, so U110-A's `s7a_markKey_lt` applies verbatim; (ii) the assembly is the accepted `s176_hrec_unswitched_of_succ` /
`r176h_succ` shape with `Record.arcBetween_restrictCrossings_succ_iff` in place of `firstReturn_no_between` (no `firstReturn` term, hence
no `DecidablePred` instance to match); (iii) the crossing correspondence is `s7a_side_mem_carrierCrossings` + `s7s_mem_geoCarrierCrossings_iff`.

## 4. How to consume (B2 `s7z_returned_of_FSector`, or SITE's `s7s_cornerHomfly_skein` at a support)

On the bigon side `b := s7z_side g M a` (= `s7f_side`; `s7f_pattern hn h t` gives `IsCrossing … {a, M-1}` and `… {a, M}`; SITE's `hx`
wants `{M - 1, a}`: `hx := Finset.pair_comm a (M - 1) ▸ (s7f_pattern hn h t).1`, `hy := (s7f_pattern hn h t).2.1`; then
`xPair hx = s7z_x hn h t` and `xPair hy = s7z_y hn h t` by `Subtype.ext (Finset.pair_comm _ _)` / `rfl`):
1. `obtain ⟨r, η, -, -, -, -, -, -, δ, hδ, -, hloc⟩ := s7a_exists_sideLocal hn g M a h.1`; for `t.val < δ`, `hL := hloc t ht`.
2. For a newborn-free support `S` (`x, y ∉ S`, so `hSp` from `s7f_eq_x_or_y_of_affected`) take `S'` its transport — e.g. `e₀.symm ⟨S, …⟩`
   of `s7z_FSector`'s persistent bijection, or `S.image (fun c => s7a_cross (s7a_side_hs hn g hL b (!b)) c _)` — with
   `hSS'`; `hSp'` is `s7sh_other_side_not_affected hn g h b hx hy`; `hS' := (s7a_side_isDecomposition_iff hn g hL b (!b) S S' hSS' hSp hSp').mpr hS`.
3. `hxq hyq` from `x, y ∈ carrierCrossings hn hP S q` through `(s7s_mem_geoCarrierCrossings_iff hn hP S q _).mpr`.
4. `hrec := s7sh_hrec_prop_side hn g h b hL hx hy S S' hSS' hSp hSp' hS hS' q hxq hyq`, then W3_SITE_REPORT §5 item 4:
   `s7s_cornerHomfly_skein hn hP S hS q hx hy hxq hyq W D_L hrec v hv` with `W := s7s_siteData_of_wall …` (SITEC / U110-A-B) and
   `D_L := positiveLift hn (s7a_sideGeneric g (!b)) S' (s7a_sideComponentEquiv hn g hL b (!b) S S' hSS' hSp hSp' q) hS'`.
5. If the consumer holds its own `q'` and geometry data instead, `s7sh_hrec_prop_carrier` needs only `s7sh_WallData hG q hG' hs q'`
   (four Props) besides `Generic P`, `Generic Q`.

## 5. Mathlib / Lean pitfalls hit (v4.34.0-rc2 pin)

1. The implicit-transparency `rw` failure (§3 item 2) — rewrite in hypotheses, not in unfolded targets; instantiate `?v` before `rw`.
2. `exact s7sh_back_visit hs W.free _ _` cannot infer the persistence-proof placeholder from a goal whose visit sits under
   `Subtype.val ⟨…, …⟩` ("don't know how to synthesize placeholder"): pass the proof explicitly (`(s7sh_crossKeep_iff …).mp v.2`).
3. Section-variable inclusion: a `structure … : Prop` whose fields mention `hG q hG' hs q'` takes exactly those as parameters
   (`s7sh_WallData hG q hG' hs q'`); a theorem whose statement mentions `geoCarrierCrossings hG'.cg S' q'` but no lift of `q'` does NOT
   take `hS'` — read the `#check` before writing call sites.
4. `include hn h in` is needed for the germ lemmas (`hn`, `h` enter only through `vertex_sides` in the proof).
5. `Finset.pair_comm` bridges `{M - 1, a}` (SITE's `hx`, `xPair hx`) and `{a, M - 1}` (`ContactAffected`, `BigonCrossingPattern`,
   `s7f_x`); `Subtype.ext` after it identifies the crossings.

## 6. Notes for the assembler

* Pure insertion at `8615a8616,9036`; the block is self-contained on the library + SITE's `s7s_lift`, `s7s_keepOf`,
  `s7s_crossingOf_eq_iff_fst`, `s7s_pos_iff_of_sign_eq`, `s7s_hrec_prop`, `s7s_hrec_prop_of_unswitched`, `s7s_cg`, `s7s_geoIndependent`,
  `s7s_geoComp`, `s7s_geoPositiveLift_eq`, `s7s_mem_geoCarrierCrossings_iff` (it references no `s7f_`/`s7k_`/`s7j_`/`s7z_` name), so it
  may be moved to any position after `end S7Site` (line 7025) if the merge prefers producer order — e.g. directly after the SITE block,
  before BLOCK — without change; inside K's `section S7ZBigon` its own `variable (g : WallGerm n) {M a : ZMod n}` shadow K's `{g} {M a}`
  (line 8345), which is harmless (verified by the full compile).
* The unit name `s7sh_Φ` contains `Φ` (as `s176_wallΦ`, `r174h_transfer`'s `𝚽` notation do); `s7sh_recordIso` is a `def` (data), the rest
  theorems.  No notation, no `set_option`.
* Timeline: 05:58 UTC start (reading), 06:07 first scratch compile, 06:14 clean scratch compile, 06:17 full compile of `W4_SITEH.lean`
  (0 errors), 06:20 axioms, 06:25 report.
