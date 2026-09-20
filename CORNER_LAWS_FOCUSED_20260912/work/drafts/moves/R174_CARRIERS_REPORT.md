# R174_CARRIERS_REPORT — unit CARRIERS (row 174, `gsc_Ledger` item 1): the carrier structure of the two rows `Q ∪ {m}` / `Q ∪ {x, w}` on `P` and the bijection `ρ`

Prover (subagent), 2026-09-15 ≈ 21:15 UTC / 5:15pm ET.  File: `work/drafts/moves/R174_CARRIERS.lean`
(= `Site_174.lean` byte-identical, 2941 lines, + 1498 appended lines, prefix `r174c_`, 149 declarations).
Inputs read: Site_174_REPORT.md (§1–§5), U_R174_REPORT.md §4 item 1 / §5, RProof/RALedgers.lean (`gsc_WallData`,
`gsc_Ledger`, `gsc_moves`, `gsc_wallData_of_endpoint`, the `est_` spectator transport `est_groupedPoly_eq_of_ne` /
`est_omega1_eq_of_ne` as the model for the `Ω₁` read), PLAN_FINAL.md §4.2, RProof/X1Rows3.lean (`GT_Endpoint` and its
namespace: `x₁ x₂ w₂ w₃ m₁ m₃`, `twin_*`, `xval/wval/mval`, `not_mem_Q_of_mem_T`; `GT_Wall`, `GT_carrierEquiv`,
`GT_owner_transport`, `GT_owner_eq_of_adjacent`, `GT_succ_of_adjacent`, `GT_cornerList_eq` … `GT_selector_eq`,
`GT_carrierR_eq`, `GT_groupedPoly_eq_homfly`), RProof/X1Rows2.lean (`AV_nextCorner`, `EXT_homfly_wall`),
RProof/GenericTransport.lean (`gu1_markSuccessor_eq_of_adjacent`), SM/FlatCarriersDefs.lean (the geo carrier layer:
`geoSmoothingSuccessor`, `GeoComponent`, `geoOwner`, `geoComponentCornerList`, `geoCornerPolygon`,
`geoCarrierCrossings`, `geoCarrierSelector`), SM/FlatCarriers.lean (`geoMarkSuccessor_position_cases`),
SM/GeoMarkTransport.lean (`geoRecast` toolkit), SM/GeoCarrierCrossings.lean (`mem_geoCarrierCrossings`),
CV/CarriersLemma.lean (`visits_separated_iff`, `owner_eq_of_mem_U`), CV/X1.lean (`Omega1`, `slot`, `carrierR`,
`groupedWrithe_eq_card_geoCarrierCrossings`), CV/Carriers.lean (`weight`), CV/Events.lean (`Ind`, `N`, `U`),
SM/CrossingTransport.lean, RProof/Cores.lean (`AdjacentVisits`, `visitOn`).

## 0. Deliverables and checks

| item | result |
|---|---|
| `R174_CARRIERS.lean` | 4439 lines = `Site_174.lean` (2941, byte-identical: `cp` then append only) + 1498 appended lines (sections "Unit CARRIERS" §1–§6) |
| compile `cd work/lean && lake env lean ../drafts/moves/R174_CARRIERS.lean` | exit 0, **0 errors**, ≈ 19 s; warnings: exactly the skeleton's **33** `declaration uses sorry` + its one cosmetic `<;>` linter note (line 566).  No new warning of any kind |
| `grep -c sorry` | **34 before / 34 after** (no new `sorry`; the 34th hit is the header prose) |
| `python3 check_W1_identity.py Statements_FINAL.lean R174_CARRIERS.lean` | check 2 (all **37** declarations of Statements_FINAL byte-identical): **PASS, 0 changed/missing**; checks 1 and 3 report `False` for the two reasons Site_174_REPORT §0 records (the skeleton's added import line; appended material after the FINAL's suffix) |
| `#print axioms` | `r174c_ρ`, `r174c_local_Sm`, `r174c_local_Sxw`, `r174c_owner_iff_of_avoid`, `r174c_spectator_weight`, `r174c_retained_spectator`, `r174c_first_local`, `r174c_owner_qC_iff`, `r174c_owner_qAB_iff`: `propext, Classical.choice, Quot.sound` (standard).  `r174c_spectator_omega`, `r174c_homfly_spectator`, `r174c_carrierData`: + `SM.lit_homfly, SM.lp_lm, SM.lp_lm_uniqueness` (through `EXT_homfly_wall` → `CV.gausscode_polynomial`, the accepted footprint of every `Ω₁` transport in the library, e.g. `est_omega1_eq_of_ne`).  **No `sorryAx` anywhere in the `r174c_` material** |
| black boxes consumed | **none** — no other unit's obligation was needed; nothing stated with `sorry` |
| reassessment rule | never triggered (no lemma took two failed attempts; four compile rounds in total, each fixing elaboration details) |

Nothing under `work/lean` was written.  Scratch files live in the session scratchpad only.

## 1. What is PROVED — item 1 of `gsc_Ledger`, field by field

Setting (the binders of `gsc_moves`): `hG : CV.Generic P`, `D : GT_Endpoint hG.crossingGeometry hP' hs e f g Q x w m ℓ₁ ℓ₂ ℓ₃`,
`hsgn : crossingSign P ℓ₁ ℓ₂ = crossingSign P ℓ₁ ℓ₃`, `hSm : Q ∪ {m} ∈ Ind`, `hSxw : Q ∪ {x, w} ∈ Ind`, `hn : 3 ≤ n`.
Everything is on the ONE polygon `P` (the `E`-side polygon `P'` is not involved: the wall part `τ, weight_wall,
carrierR_wall` is already realised by `gsc_wallData_of_endpoint`).  Notation: `L_m := geoOwner hP (Q ∪ {m})`,
`L_xw := geoOwner hP (Q ∪ {x, w})`; the six local visits are `D.x₁ D.x₂ D.w₂ D.w₃ D.m₁ D.m₃` (`x₁ = x` on `ℓ₁`, etc.).

### 1a. The bundle `r174c_CarrierData` and its constructor

```
structure r174c_CarrierData hn hG Q m x w hSm hSxw where
  qC qAB : GeoComponent hG.cg (Q ∪ {m});  hCAB : qC ≠ qAB
  qC' qA qB : GeoComponent hG.cg (Q ∪ {x, w});  hC'A : qC' ≠ qA;  hC'B : qC' ≠ qB;  hAB : qA ≠ qB
  ρ : GeoComponent hG.cg (Q ∪ {m}) ≃ {q' // q' ≠ qB};  ρ_AB : (ρ qAB).1 = qA;  ρ_C : (ρ qC).1 = qC'
  spectator_weight : ∀ q, q ≠ qAB → q ≠ qC → CV.weight hG.cg (Q ∪ {x, w}) (ρ q).1 = CV.weight hG.cg (Q ∪ {m}) q
  spectator_omega  : ∀ q, q ≠ qAB → q ≠ qC → CV.Omega1 hn hG hSxw (ρ q).1 = CV.Omega1 hn hG hSm q
def r174c_carrierData hn hG D hsgn hSm hSxw : r174c_CarrierData hn hG Q m x w hSm hSxw
```
The fourteen fields are, statement for statement and in the same order, the item-1 fields
`qC qAB hCAB qC' qA qB hC'A hC'B hAB ρ ρ_AB ρ_C spectator_weight spectator_omega` of `gsc_Ledger` (RALedgers.lean
350–376), on `gsc_Ledger`'s own binders — a realiser of `gsc_moves` fills them with `(r174c_carrierData hn hG D hsgn hSm hSxw).qC`, …
(RALedgers is not touched; the remaining fields `σ hσ omega_wall writhe_wall omega_C weight_C weight_AB carrierR_add
D₀ qx fulltwist i j ℓ smoothing writhe_count` belong to items 2–6 / Site 174 and are not consumed here).

| ledger field | realisation | content |
|---|---|---|
| `qC` | `r174c_qC D := L_m (inr D.x₁)` | `C` owns `x₁` and (`r174c_qC_w₃`) `w₃`, and one visit of `m`: `m₁` in case A (`r174c_qC_m₁_A`), `m₃` in case B (`r174c_qC_m₃_B`) |
| `qAB` | `r174c_qAB D := L_m (inr D.x₂)` | `AB` owns `x₂`, `w₂` (`r174c_qAB_w₂`) and the other visit of `m`: `m₃` in case A (`r174c_qAB_m₃_A`), `m₁` in case B (`r174c_qAB_m₁_B`) |
| `hCAB` | `r174c_hCAB D hSm` | `x` is dominated in `Q ∪ {m}` (`x ∈ N`, `D.hxm`): `CV.visits_separated_iff` |
| `qA` | `r174c_qA D := L_xw (inr D.m₁)` | owns `x₂` (case A, `r174c_qA_x₂_A`) / `x₁` (case B, `r174c_qA_x₁_B`) |
| `qB` | `r174c_qB D := L_xw (inr D.m₃)` | owns `w₃` (case A, `r174c_qB_w₃_A`) / `w₂` (case B, `r174c_qB_w₂_B`) |
| `qC'` | `r174c_qC' D := if param x₁ < param m₁ then L_xw (inr D.x₁) else L_xw (inr D.x₂)` | the third local carrier: owns `x₁, w₂` (case A: `r174c_qC'_A`, `r174c_qC'_w₂_A`) / `x₂, w₃` (case B: `r174c_qC'_B`, `r174c_qC'_w₃_B`) |
| `hAB` | `r174c_hAB D hSxw` | `m` is dominated in `Q ∪ {x, w}` |
| `hC'A`, `hC'B` | `r174c_hC'A D hn hSxw`, `r174c_hC'B D hn hSxw hsgn` | `x` resp. `w` selected in `Q ∪ {x, w}`: their two visits are separated, and `C'` vs `A` (resp. `B`) own the two visits of `x` (resp. `w`) |
| `ρ` | `r174c_ρ D hn hSm hSxw hsgn` | §2 below |
| `ρ_AB`, `ρ_C` | `r174c_ρ_AB`, `r174c_ρ_C` | by construction (`r174c_fwdMark_of_qAB/of_qC`) |
| `spectator_weight` | `r174c_spectator_weight hn hG D hSm hSxw hsgn` | a spectator is the same cycle of marks in both rows, hence has the same corner list (`r174c_cornerList_spectator`), the same corner polygon up to `geoRecast` (`r174c_cornerPolygon_spectator`), the same selector (`r174c_selector_spectator`) |
| `spectator_omega` | `r174c_spectator_omega hn hG D hSm hSxw hsgn` | same retained crossings (`r174c_retained_spectator`), same `R(L)` (`r174c_carrierR_spectator`), same grouped polynomial (`r174c_groupedPoly_spectator`, via `GT_groupedPoly_eq_homfly` and `r174c_homfly_spectator` = `EXT_homfly_wall` with the identity transport `crossingTransport (fun _ => Iff.rfl)`, `r174c_map_refl`) |

**Case A / case B.** `r174c_order₃ D hsgn : param x₁ < param m₁ ↔ param m₃ < param w₃` (Site 174's `s174_order` read on `P`,
with `D.sgn` as the second sign equation), so exactly two traversal pictures occur, decided by the order of `x, m` on
`ℓ₁`; `r174c_order₂_A/_B` derive the `ℓ₂`-order (`x` before `w` in case A, `w` before `x` in case B) not from the
algebra but from the carrier structure (the other order would put `m₁, m₃` on one carrier of `Q ∪ {x, w}`,
contradicting `hAB`).  The successors at the local visits (`r174c_succ_*`, `r174c_succSm_*`, `r174c_succSxw_*`) come
from `D.adj1..3` through `GT_succ_of_adjacent`, oriented by the parameter order (`r174c_param_lt_of_succ`, from
`geoMarkSuccessor_position_cases`).  All case-split theorems have case-free wrappers where the ledger needs them
(`r174c_qC_w₃`, `r174c_hC'A`, `r174c_hC'B`, `r174c_local_Sm`, `r174c_local_Sxw`, and everything about `ρ`).

### 1b. The one non-local fact: the other visit of `m` lies on `AB` — `r174c_m_visit_qAB`

Every local step above is a `ρ_S`-successor computation, except `m₃ ∈ AB` (case A) / `m₁ ∈ AB` (case B), which is
NOT reachable by local steps (`ρ_{Q∪{m}}(m₃) = ρ(m₁)` leaves the bundle).  Proof: the reconnections `ρ_{Q∪{m}}` and `ρ_Q`
agree except at the two visits of `m`; if the `Q ∪ {m}`-carrier of `x₂` avoided both, it would be a carrier of `Q` as
well (`r174c_owner_iff_of_avoid`), but on `Q` the visits `x₂, x₁, m₁` lie on one carrier (`x ∈ U(Q)` by `Q_out`/`Q_avail`,
`CV.owner_eq_of_mem_U`; `x₁ ~ m₁` adjacent unselected, `GT_owner_eq_of_adjacent`) — so `AB` contains `m₁` or `m₃`, and
the one on `C` is excluded by `hCAB`.  Consequences: `r174c_local_Sm` (every local visit lies on `C` or `AB`) and
`r174c_local_Sxw` (every local visit lies on `C'`, `A` or `B`).

## 2. The bijection `ρ` — `r174c_ρ` (§3–§4 of the appended material)

Tool (§1, general, any finite type): two permutations `σ, σ'` that agree outside a predicate `L` have the same
orbits away from `L` — `r174c_pow_eq_of_agree`, `r174c_sameCycle_iff_of_agree`; on the polygon (§2)
`r174c_succ_eq_of_not_local` (`ρ_S a = ρ_T a` for a vertex or a visit of a crossing in neither or both of `S, T`) and

```
r174c_owner_iff_of_avoid hP S T (hL : ∀ v, L_S (inr v) = L_S a → (v.1 ∈ S ↔ v.1 ∈ T)) (b) :
    L_S b = L_S a ↔ L_T b = L_T a
```
— a carrier avoiding the visits of `S ∆ T` is literally the same set of marks for both supports.  Applied to
`S, T = Q ∪ {m}, Q ∪ {x, w}` (`S ∆ T = {x, w, m}`): a carrier of `Q ∪ {m}` other than `C, AB` avoids every local visit
(`r174c_local_Sm`), so `r174c_owner_iff_m`; a carrier of `Q ∪ {x, w}` other than `C', A, B` likewise (`r174c_owner_iff_xw`).

Construction: on marks, `r174c_fwdMark a := if L_m a = qAB then qA else if L_m a = qC then qC' else L_xw a` and
`r174c_bwdMark a := if L_xw a ∈ {qA, qB} then qAB else if L_xw a = qC' then qC else L_m a`; both are constant on cycles
(`r174c_fwdMark_congr`, `r174c_bwdMark_congr`, the third branch by `r174c_owner_iff_m/xw`), so they descend to
`r174c_fwd`, `r174c_bwd` by `Quotient.lift` (`GeoComponent` is the cycle quotient).  `r174c_fwd_ne_qB` (a spectator's
image is not `B`, since `B` owns the local visit `m₃`), `r174c_bwd_fwd`, `r174c_fwd_bwd` give the `Equiv` onto
`{q' // q' ≠ qB}`; `r174c_ρ_apply`, `r174c_ρ_AB`, `r174c_ρ_C`, `r174c_ρ_spectator` ((ρ (L_m a)).1 = L_xw a for a spectator).

## 3. Beyond item 1 (for items 2–3): the local carriers mark by mark — §6

Items 2–3 (`omega_C`, `weight_C`, `weight_AB`, `carrierR_add`, `writhe_count`) must compare the corner lists and retained
crossings of `C, AB` with those of `C', A, B`.  The mark-level correspondence is PROVED here:

```
r174c_owner_qC_iff  (hb : r174c_NonLocal b) : L_m b = qC  ↔ L_xw b = qC'
r174c_owner_qAB_iff (hb : r174c_NonLocal b) : L_m b = qAB ↔ (L_xw b = qA ∨ L_xw b = qB)
```
(`r174c_NonLocal b`: `b` is a vertex or a visit of a crossing other than `x, w, m`.)  Method: `r174c_exists_first` /
`r174c_first_local` — following `ρ_S` from a non-local mark `b` of a local carrier, the FIRST local mark `ℓ` reached is
entered from a non-local mark `p` (`ρ_S p = ℓ`), and `ρ_T` agrees with `ρ_S` up to `ℓ`, so `L_T b = L_T ℓ`; the local
visits of `C` (resp. `AB`, `C'`, `A ∪ B`) that can be entered from a non-local mark are exactly `x₁` (case A) / `w₃`
(case B) for `C` and `C'`, `x₂, m₃` / `w₂, m₁` for `AB`, `x₂` / `m₁` for `A`, `m₃` / `w₂` for `B` (`r174c_entry_qC`,
`r174c_entry_qAB`, `r174c_entry_qC'`, `r174c_entry_qA_qB`: the other local visits have a LOCAL `ρ_S`-predecessor,
`r174c_not_entry`).  Hence the picture of GSC §1 (2), in both cases, with `α₁ α₂ α₃` the three outside arcs:
`C = {x₁, m₁, w₃} ∪ α₃`, `AB = {x₂, w₂} ∪ α₂ ∪ {m₃} ∪ α₁`; `C' = {x₁, w₂} ∪ α₃`, `A = {x₂, m₁} ∪ α₁`, `B = {m₃, w₃} ∪ α₂`
(case A; case B: `C = {w₃, m₃, x₁} ∪ α₁`, `AB = {w₂, x₂} ∪ α₂ ∪ {m₁} ∪ α₃`, `C' = {w₃, x₂} ∪ α₁`, `A = {m₁, x₁} ∪ α₂`,
`B = {w₂, m₃} ∪ α₃`).  So: the corners of `C'` are those of `C` with the selected corner `m₁`/`m₃` replaced by the two
selected corners `x₁, w₂` / `w₃, x₂` (→ `weight_C = −σ · weight_C_b`, `omega_C`: the retained crossings of `C` and `C'`
coincide, both being the unselected crossings with both visits in the common outside arc — `r174c_owner_qC_iff` on the
two visits), and the corners of `A` and `B` together are those of `AB` with its selected corner `m₃`/`m₁` replaced by the
four selected corners `x₁ x₂ w₂ w₃` minus the two on `C'` — the corner bookkeeping GSC (5), (8), (10) read
(`weight_AB`, `carrierR_add`, `writhe_count`).  These lemmas are stated at the `hP : CrossingGeometry P` level (no
`CV.Generic` needed).

## 4. Fidelity: the ledger's item-1 statements are satisfiable AS STATED — no defect found

* All fourteen fields are met verbatim (no re-basing, no F-174 edit; RALedgers.lean untouched).
* The only choice the ledger leaves open is WHICH carrier `qC'` is (the fields constrain it only through `hC'A, hC'B,
  ρ_C` and, in items 2–3, `omega_C, weight_C`).  It is necessarily case-dependent: in case A the third local carrier
  of `Q ∪ {x, w}` owns `x₁, w₂`, in case B it owns `x₂, w₃` (`r174c_qC'_A/_B`); no case-free visit description exists,
  which is why `r174c_qC'` is defined by the `ℓ₁`-order.  Items 2–3 should consume it through `r174c_qC'_A/_B`,
  `r174c_qC'_w₂_A`, `r174c_qC'_w₃_B` and `r174c_owner_qC_iff`.
* `spectator_weight`/`spectator_omega` are stated for `q ≠ qAB ∧ q ≠ qC`, exactly the carriers on which `ρ` is the
  identity on marks; `ρ`'s two special values are pinned by `ρ_AB, ρ_C`.  Nothing about `C` vs `C'` is claimed by
  item 1 — correct, since their reads differ (`weight_C`).

## 5. What the realiser of `gsc_moves` still needs (unchanged from U_R174 §4, minus item 1)

| obligation | unit | note from this unit |
|---|---|---|
| `omega_wall`, `writhe_wall` (item 2) | wall reads | for the spectators of the wall the pattern is `est_groupedPoly_eq_of_ne`; for `C` use `r174c_qC_w₃`, `r174c_qC_m₁_A/_m₃_B` (its local marks) |
| `omega_C`, `weight_C`, `weight_AB`, `carrierR_add` (item 3) | corner ledger | §3 above supplies the mark-level `C ↔ C'`, `AB ↔ A ∪ B` correspondence; the corner lists follow by `List.filter_congr` on `geoMarkList` as in `r174c_cornerList_spectator`, with the six local corners handled by `r174c_local_cases` |
| `hx'`, `hw'` (site inputs), `hrec` | Site 174 §5 | on `P'`, not touched here |
| `smoothing`, `writhe_count` (items 5–6) | smoothing | `qA = L_xw m₁`, `qB = L_xw m₃` are now concrete; the retained crossings of `A`, `B` vs `AB` follow from `r174c_owner_qAB_iff` |

## 6. Pitfalls met (all resolved)

1. `include D` is needed for theorems whose statement does not mention `D` (`D.foo` in a proof is otherwise
   "unknown identifier"); with it, lemmas that do not use `D` must say `omit [NeZero n] D in` (the linter reports
   included-but-unused variables).  Same for `hn`.
2. `geoSmoothingSuccessor_visit_of_mem hP _ D.m₁ r174c_m_mem_Sm` unifies the support as `?Q ∪ {D.m₁.fst}` — a
   syntactically different (defeq) term that `rw` then cannot find; pass the support explicitly (`hP (Q ∪ {m})`).
3. A docstring must be immediately followed by the declaration: `omit … in` goes BEFORE the docstring.
4. `⟨j, proof⟩.symm` does not elaborate (no expected type for the anonymous constructor); write `Eq.symm (… ⟨(j : ℤ), …⟩)`,
   and coerce the `ℕ`-exponent (`SameCycle` is `∃ i : ℤ`; `zpow_natCast`).
5. `if_pos/if_neg` are deprecated in this toolchain → `ite_eq_left/ite_eq_right` (same shape); `push_neg` is deprecated →
   `simp only [not_or]`.
6. `EXT_homfly_wall` with `P' = P`, `hs := fun _ => Iff.rfl`: `crossingTransport hs c = c` and `visitTransport hs v = v`
   hold by structure eta (`rfl`), so `hkey`/`hdet` are `Iff.rfl` and `Finset.map … = X` is `Finset.mem_map_equiv` + `Iff.rfl`
   (`r174c_map_refl`).
7. Dependent corner polygons: prove the LIST equality first (`r174c_cornerList_spectator`, `List.filter_filter` +
   `List.filter_congr` + `Bool.eq_iff_iff`), then the count, then `geoCornerPolygon … = geoRecast h …` by
   `geo_getElem_congr` / `geo_zmod_val_cast`; `cornerSelector_geoRecast`, `rotationNumber_geoRecast` finish `wt` and `R`
   (after `CV.rot_eq_rotationNumber` has removed the regularity proof, as in `GT_carrierR_eq`).
