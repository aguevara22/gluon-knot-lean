# R174_SITEIN_REPORT — unit SITEIN (row 174): the two site inputs `hx'`, `hw'` of Site 174, PROVED

Prover (subagent), 2026-09-15 ≈ 22:40 UTC / 6:40pm ET.  File: `work/drafts/moves/R174_SITEIN.lean`
(= `R174_CARRIERS.lean`, byte-identical on its 4439 lines (`cmp`), + 191 appended lines, prefix `r174x_`,
17 declarations).  Inputs read: Site_174_REPORT.md §1/§5, R174_CARRIERS_REPORT.md, R174_HREC_REPORT.md,
U_R174_REPORT.md §4 items 1–2, RProof/RALedgers.lean (`gsc_wall_of_endpoint`, `gsc_wallData_of_endpoint`),
RProof/X1Rows3.lean (`GT_Endpoint` and its namespace, `GT_Wall`, `GT_Good`, `GT_good_of_not_mem`, `GT_carrierEquiv`,
`GT_owner_transport`, `GT_owner_arc`, `GT_owner_eq_of_adjacent`), SM/FlatCarriersDefs.lean (`markTransport`,
`transportSupport`), SM/FlatCarriers.lean (`mem_transportSupport_iff`, `markTransport_visit`),
SM/CrossingTransport.lean, SM/GeoCarrierCrossings.lean (`mem_geoCarrierCrossings`), CV/CarrierBridges.lean
(`CV.mem_U_iff`), CV/CarriersLemma.lean (`CV.owner_eq_of_mem_U`), RProof/Cores.lean (`visitOn`, `F1.mem_triangleCrossings`).

## 0. Deliverables and checks

| item | result |
|---|---|
| `R174_SITEIN.lean` | 4630 lines = `R174_CARRIERS.lean` (4439, byte-identical: `cp` then append only) + 191 appended lines (section "Unit SITEIN", two subsections `R174XLocal`, `R174XMain`) |
| compile `cd work/lean && lake env lean ../drafts/moves/R174_SITEIN.lean` | exit 0, **0 errors**, ≈ 17 s; warnings: exactly the skeleton's **33** `declaration uses sorry` + its one cosmetic `<;>` linter note (line 566).  No new warning of any kind |
| `grep -c sorry` | **34 before / 34 after** (no new `sorry`; no black box stated — nothing from another unit was needed beyond the `r174c_` material already in the file) |
| `python3 check_W1_identity.py Statements_FINAL.lean R174_SITEIN.lean` | check 2 (all **37** declarations of Statements_FINAL byte-identical): **PASS, 0 changed/missing**; checks 1 and 3 report `False` for the two reasons Site_174_REPORT §0 records (the skeleton's added import line; appended material after the FINAL's suffix) |
| `#print axioms` (scratch copy) | `r174x_hx'`, `r174x_hw'`, `r174x_site_inputs`, `r174x_hx'_tau`, `r174x_hw'_tau`, `r174x_hx'_of_owner`, `r174x_hw'_of_owner`, `r174x_owner'_x₂`, `r174x_good_of_edge₂`, `r174x_x'_mem_U`: **`propext, Classical.choice, Quot.sound`** (standard; no `sorryAx`).  `r174x_carrierData_qAB` (a `rfl`) lists in addition `SM.lit_homfly, SM.lp_lm, SM.lp_lm_uniqueness` only because its STATEMENT mentions `r174c_carrierData`, whose body carries them (the `Ω₁` spectator read) |
| integration (scratch, not part of the file) | `R174_SITEIN.lean` + the appended `r174h_` section of `R174_HREC.lean` (lines 2942–3390) compile together with 0 errors, and `r174h_fulltwist hn hG hG' D hSm hSm' (r174c_qAB D) q' hq' (r174x_hx' …) (r174x_hw' …) hsgn` and `r174h_hrec_tau … (r174x_hx'_tau …) (r174x_hw'_tau …)` typecheck — i.e. the assembler's discharge of `hx', hw'` is verified.  Axioms of the instantiated `fulltwist`: exactly the footprint of `r174h_fulltwist` (`sorryAx` from the frozen leaf `exists_bigonData_of_triangle` inside `s174_site`, plus the homfly triple); the instantiated `hrec`: standard axioms only |
| reassessment rule | not triggered: the section compiled at the first attempt (one linter note fixed by `omit hSm' in`) |
| size | 191 lines against Site_174_REPORT §5's estimate of 0.4–0.8k: the arc route (`GT_owner_arc`, `AV_nextCorner`) is not needed — see §2 |

Nothing under `work/lean` was written.  Scratch files (`R174_SITEIN_axioms.lean`, `R174_SITEIN_integ.lean`) live in the
session scratchpad only.

## 1. What is PROVED (all `r174x_`, namespace `SM.Link`, `open SM SM.GeoCarrier SM.Carrier RProof`)

### 1a. The site inputs on the consumers' binders — `r174x_hx'`, `r174x_hw'`, `r174x_site_inputs` (section `R174XMain`)

Binders of the section: `hG : CV.Generic P`, `hG' : CV.Generic P'`,
`D : GT_Endpoint hG.crossingGeometry hG'.crossingGeometry hs e f g Q x w m ℓ₁ ℓ₂ ℓ₃`,
`hSm : Q ∪ {m} ∈ CV.Ind hG.crossingGeometry`, `hSm' : transportSupport hs (Q ∪ {m}) ∈ CV.Ind hG'.crossingGeometry`
(`𝑺' := transportSupport hs (Q ∪ {m})`, `𝑾 := gsc_wall_of_endpoint hG hG' D hSm hSm'`).

```
theorem r174x_hx' (qAB : GeoComponent hG.crossingGeometry (Q ∪ {m})) (hqAB : qAB = r174c_qAB D)
    (q' : GeoComponent hG'.crossingGeometry 𝑺') (hq' : q' = GT_carrierEquiv 𝑾 qAB) :
    crossingTransport hs x ∈ geoCarrierCrossings hG'.crossingGeometry 𝑺' q'
theorem r174x_hw' (same binders) :
    crossingTransport hs w ∈ geoCarrierCrossings hG'.crossingGeometry 𝑺' q'
theorem r174x_site_inputs (same binders) : (hx' statement) ∧ (hw' statement)
```
These are exactly the hypotheses `hx'`, `hw'` of `r174h__s174_hrec_prop_proof` / `r174h_fulltwist` (binders
`hn hG hG' D hSm hSm' qAB q' hq' hx' hw'`, R174_HREC_REPORT §1a) at the ledger's carrier `qAB = r174c_qAB D`
(R174_CARRIERS_REPORT §1a: `r174c_carrierData … .qAB`), with the same `hq'`.  `hn` is not needed here (no lift).
Assembler's call, verified in the integration scratch:
```
r174h_fulltwist hn hG hG' D hSm hSm' (r174c_qAB D) q' hq'
  (r174x_hx' hG hG' D hSm hSm' (r174c_qAB D) rfl q' hq') (r174x_hw' hG hG' D hSm hSm' (r174c_qAB D) rfl q' hq') hsgn
```
If the realiser reads `qAB` off the bundle, `hqAB := r174x_carrierData_qAB hG hG' D hSm hn hsgn hSxw`
(`(r174c_carrierData hn hG D hsgn hSm hSxw).qAB = r174c_qAB D`, `rfl`).

Two further forms:
* `r174x_hx'_tau (hn) : crossingTransport hs x ∈ geoCarrierCrossings hG'.crossingGeometry 𝑺' ((gsc_wallData_of_endpoint hn hG hG' D hSm hSm').τ (r174c_qAB D))`
  and `r174x_hw'_tau` — the ledger's binding `q' := W.τ qAB` (`τ` is `GT_carrierEquiv (gsc_wall_of_endpoint …)` by
  `rfl`), the form `r174h_hrec_tau` consumes.
* `r174x_hx'_of_owner (qAB) (hqAB : geoOwner hG.crossingGeometry (Q ∪ {m}) (Sum.inr D.x₂) = qAB) : x' ∈ retained(GT_carrierEquiv 𝑾 qAB)`
  and `r174x_hw'_of_owner (hqAB : geoOwner … (Sum.inr D.w₂) = qAB)` — the general statement: ANY carrier of `Q ∪ {m}`
  owning `x₂` (resp. `w₂`) has `x'` (resp. `w'`) retained on its wall copy.  `r174c_qAB` owns both (`r174c_qAB_x₂ : rfl`,
  `r174c_qAB_w₂`), which is all the specialisations use.

### 1b. The ownership transport — `r174x_owner'_x₂`, `r174x_owner'_w₂`

```
theorem r174x_owner'_x₂ (qAB) (hqAB : geoOwner hG.crossingGeometry (Q ∪ {m}) (Sum.inr D.x₂) = qAB) :
    geoOwner hG'.crossingGeometry 𝑺' (Sum.inr (visitTransport hs D.x₂)) = GT_carrierEquiv 𝑾 qAB
```
(`rw [← markTransport_visit, GT_owner_transport 𝑾 (r174x_good_x₂ D), hqAB]`), and the same for `w₂`.

### 1c. The `CrossingGeometry`-level facts (section `R174XLocal`, binders `D : GT_Endpoint hP hP' hs …` only)

| lemma | content |
|---|---|
| `r174x_x'_not_mem_Sm'`, `r174x_w'_not_mem_Sm'` | `x', w' ∉ transportSupport hs (Q ∪ {m})` (`mem_transportSupport_iff` + `r174c_x_not_mem_Sm`, `r174c_w_not_mem_Sm`) |
| `r174x_x'_mem_U`, `r174x_w'_mem_U` | `x', w' ∈ CV.U hP' 𝑺'`: for `s ∈ Q`, `D.toggle` (neither `x` nor `s` … `s` is outside by `Q_out`) reduces to `¬ GeometricInterlaces hP x s`, which is `D.Q_avail s _ x D.xT` up to symmetry; for `s = m`, `D.compl x m` turns `GeometricInterlaces hP' x' m'` into `¬ GeometricInterlaces hP x m`, contradicting `D.hxm` (resp. `D.hwm`) |
| `r174x_good_of_edge₂ (hv : v.2.val = ℓ₂) : GT_Good (triangleCrossings P e f g) (Q ∪ {m}) (Sum.inr v)` | a reversed partner `u` of `v` is a triangle crossing on `ℓ₂`; `u.1 ∈ Q` contradicts `Q_out`; `u.1 = m` gives `ℓ₂ ∈ m.val`, contradicting `D.l2_not_mem_m` |
| `r174x_good_x₂`, `r174x_good_w₂` | the instances `v := D.x₂`, `D.w₂` (`x₂_edge`, `w₂_edge` are `rfl`) |

Then `r174x_hx'_of_owner` is `mem_geoCarrierCrossings` + `CV.owner_eq_of_mem_U hG'.crossingGeometry hSm' (r174x_x'_mem_U D) v' (visitTransport hs D.x₂)`
(every visit of `x'` has the owner of `x₂'`) + `r174x_owner'_x₂`.

## 2. Why 191 lines and not 400–800: the good-mark route instead of the arc route

Site_174_REPORT §5 / U_R174 §4 item 2 sketch `hx', hw'` through the `E`-side arc `[m'(ℓ₁) → … → m'(ℓ₃)]`
(`GT_owner_arc`, `AV_nextCorner`): "the four `ℓ₁/ℓ₂/ℓ₃`-visits of `x', w'` are owned by `AB'`".  That route is
not needed.  The wall of the centre row (`gsc_wall_of_endpoint`) has `T = {x, w, m}` and `S = Q ∪ {m}`; a mark is
good (`GT_Good`) when none of its reversed partners (same-edge visits of another triangle crossing) is a corner of
`S`.  The only corner among `x, w, m` is `m`, on `ℓ₁, ℓ₃`.  So the bad visits are exactly `x₁` (partner `m₁`) and
`w₃` (partner `m₃`); the `ℓ₂`-visits `x₂, w₂` are good, and `GT_owner_transport` carries their ownership across the
wall verbatim: `L'(x₂') = τ L(x₂) = τ qAB`, `L'(w₂') = τ L(w₂) = τ qAB`.  The other two visits `x₁', w₃'` need no
arc argument either: `x', w' ∈ U(S')` (they do not interlace `m'` — that is precisely the RIII toggle `compl` — nor
any `Q'`-crossing), so both visits of `x'` (resp. `w'`) lie on one carrier (`CV.owner_eq_of_mem_U`).  The
`AV_nextCorner` / `GT_owner_arc` machinery, the traversal direction (`s174_order`) and the case split A/B of
R174_CARRIERS are all unnecessary for the site inputs.

## 3. Fidelity: `hx'`, `hw'` are TRUE as stated for the ledger's binding — no defect, no corrected form needed

* As bound by `r174h__s174_hrec_prop_proof` (`q' = GT_carrierEquiv (gsc_wall_of_endpoint …) qAB`, `qAB` the
  ledger's `r174c_qAB D`) both statements hold on every `GT_Endpoint` configuration, with no sign condition
  (`hsgn` is not used), no `hn`, and for either traversal direction (case A / case B of R174_CARRIERS are not
  distinguished).
* For an ARBITRARY `q'` (as `s174_site` binds it) `hx'` is of course not a theorem — it is a hypothesis about
  which carrier is meant; the consumer theorems already pin `q'` by `hq'`, and that is the form proved here.
  The slightly more general `r174x_hx'_of_owner` shows the true content: "`τ` of the carrier of `x₂` retains `x'`".
* Both `x'` and `w'` lie on the SAME carrier `τ qAB` (this is what makes the bigon of `s174_site` a bigon of one
  carrier diagram); the ledger's choice `qAB = L_m(x₂) = L_m(w₂)` is what makes it `τ qAB` rather than `τ qC`.

## 4. What remains for row 174 (none of this unit)

| obligation | status |
|---|---|
| `hx'`, `hw'` (site inputs) | **done** (this unit) — `gsc_Ledger.qx`, `.fulltwist` are now discharged by `r174h_fulltwist` + `r174x_hx'`/`r174x_hw'` with `qx := lift x'`; `hrec` by `r174h_hrec_tau` + `r174x_hx'_tau`/`r174x_hw'_tau` |
| items 2 (`omega_wall`, `writhe_wall`), 3, 5, 6 of `gsc_Ledger` | open (other units).  For `writhe_wall`'s set identity `retained(τ AB) = transport(retained(AB)) ∪ {x', w'}` the `∪ {x', w'}` half is now `r174x_hx'_tau`, `r174x_hw'_tau` (the rest is R174_HREC §1c) |
| `exists_bigonData_of_triangle` (U-M7) | black box inside `s174_site` (Wave 1) |

## 5. Pitfalls met (none serious)

1. `include hG hG' D hSm hSm'` in `R174XMain`: the `rfl` lemma `r174x_carrierData_qAB` does not use `hSm'` — the
   linter asks for `omit hSm' in` (placed BEFORE the docstring, as R174_CARRIERS_REPORT §6.3 says).
2. `r174x_good_of_edge₂ D (v := D.x₂) rfl`: `v` must be given by name — with `rfl` alone the visit is not
   determined before `GT_owner_transport`'s pattern is elaborated inside `rw`.
3. `obtain rfl := Finset.mem_singleton.mp hsm` (with `s = m`, `m` in `D`'s type) was avoided: `rw [Finset.mem_singleton.mp hsm]`
   in the goal is simpler and leaves `D` alone.
4. In `r174x_good_of_edge₂` the target `ℓ₂ ∈ m.val` is reached by `rw [← hv, hrev.2.2.2, ← hum]; exact u.2.property`
   (rewriting the GOAL with `u.1 = m` backwards, never the hypothesis `u.2.property`, whose implicit type mentions `u.1`
   — the pattern of `GT_Endpoint.good_of_edge`).
