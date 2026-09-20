# R176_HSUCC_REPORT — unit HSUCC of row 176: the successor clause `hsucc` of `hrec`, PROVED, and the chain discharged

HSUCC prover (subagent), 2026-09-15.  Inputs: `Site_176_REPORT.md` §3/§5/§6, `Site_176.lean` §G–§H (`s176_wallKeep`,
`s176_wallΦ`, `s176_wallΦ_liftVisit`, `s176_hrec_unswitched_of_succ`, `s176_hX_event`, `s176_not_mem_map_event`,
`s176_hrec_wall`, `s176_hrec_wall_of_succ`, `s176_port_weak_of_event'`, `s176_est_port_relation_weak_of'`,
`s176_est_ledger_weak`), `U_R176_REPORT.md` §5, `RProof/RALedgers.lean` (`est_wall`, `est_not_retained_H`,
`est_S_ind`, `est_S'_ind`, `est_liftCrossing`, `est_PortData`), `RProof/X1Rows3.lean` (`GT_Wall.key_lt`,
`GT_not_rev_of_not_mem_left`), `RProof/X1Rows2.lean` (`EXT_homfly_wall`, the `cyclic_order` pattern),
`CV/PieceIntrinsic.lean` (`visitBetween_iff_key`, `liftVisit_mem`), `SM/LinkDiagramRecord.lean` (`cycNext_unique`,
`nextVisit_no_between`, `record_succ_no_between`, `record_succ_eq_self_iff`, `visitCoord_injOn`, `twin_ne`),
`SM/Smoothing.lean` (`firstReturn_no_between`), `SM/MarkedProducts.lean` (`Record.firstReturn_val_ne`,
`Record.crossKeep_exists_ne`, `Record.restrictCrossings_succ_val`), `SM/LinkRecord.lean` (`Record.sameCycle_iff_comp_eq`),
`W1_M6.lean` / `W1_M6_REPORT.md` (`m6_succ`, the one-deleted-crossing shape).

## 0. Deliverables and checks

| item | result |
|---|---|
| `work/drafts/moves/R176_HSUCC.lean` | 4492 lines = `Site_176.lean` (4143 lines, **byte-identical**, `head -4143 \| cmp` = equal) + an APPENDIX of 349 lines (§I–§K, all names `r176h_`, namespace `RProof`) |
| compile `cd work/lean && lake env lean ../drafts/moves/R176_HSUCC.lean` | exit 0, **0 errors**, ≈ 18–25 s; warnings: exactly the skeleton's **33** `declaration uses sorry` + the skeleton's `<;>` style warning at line 566; **no new warnings** |
| `grep -c sorry` before / after | **34 / 34** (unchanged; the appendix contains no `sorry`, no black box was needed) |
| statement identity `python3 check_W1_identity.py Statements_FINAL.lean R176_HSUCC.lean` | "declarations in Statements_FINAL: 37; changed/missing: **0**"; its checks 1 and 3 report `False` MECHANICALLY exactly as for `Site_176.lean` (check 1 compares lines 1–136 shifted by Site_176's added import line; check 3 requires the file to END with the Statements_FINAL suffix, impossible for any appendix) |
| every frozen declaration | untouched (no statement, name, docstring or body edited; only appended material) |
| `#print axioms` | `r176h_compOf_eq`, `r176h_visitCoord_injective`, `r176h_record_componentCount`, `r176h_key_lt_iff`, `r176h_cycBetween_iff`, `r176h_succ_firstReturn`, **`r176h_succ`**, **`r176h_hrec_unswitched`**, `r176h_hkey_event`, **`r176h_hrec_wall_proof`**, `r176h_hrec_wall`: `[propext, Classical.choice, Quot.sound]` — standard only.  `r176h_est_port_weak`, `r176h_est_port_relation_weak_of_rest`, `r176h_est_ledger_weak_of_rest`: `[propext, sorryAx, Classical.choice, Quot.sound, SM.lit_homfly, SM.lp_lm, SM.lp_lm_uniqueness]` — **identical to the footprint of the frozen `s176_port_weak_of_event'` and of the frozen glue `est_port_weak_of_bigon`** (probed): the `sorryAx` is the frozen leaf `exists_bigonData_of_triangle` (black box of U-M7), the three `SM.*` are the accepted literature axioms of the moves glue / the ledger.  Nothing new is introduced |
| written under `work/lean` | nothing |
| black boxes consumed | **none** (no `sorry` Prop stated) |

## 1. What is PROVED (exact statements in the file)

### §I. One-component bookkeeping of a positive lift (3 lemmas)
* `r176h_compOf_eq : (geoPositiveLift hn hG hT q).compOf v = (geoPositiveLift hn hG hT q).compOf w` (`Fin.ext` + `omega`
  on `.isLt` after `change _ < 1`, the Site_176 §G idiom).
* `r176h_visitCoord_injective : Function.Injective (geoPositiveLift hn hG hT q).visitCoord` (`visitCoord_injOn`).
* `r176h_record_componentCount : (geoPositiveLift hn hG hT q).record.componentCount = 1`
  (`record_componentCount` + `geoPositiveLift_componentCount`).

### §J. The successor clause at the carrier level (section `R176HWall`, the §G variables + `hkey`)
Hypothesis (the same shape as `EXT_homfly_wall`'s `hkey`, restricted to retained parent visits of `q`):
`hkey : ∀ v w : Visit P, v.1 ∈ geoCarrierCrossings hG.cg T q → w.1 ∈ geoCarrierCrossings hG.cg T q →
(geometricVisitKey hG.cg v < geometricVisitKey hG.cg w ↔ geometricVisitKey hG'.cg (visitTransport hs v) <
geometricVisitKey hG'.cg (visitTransport hs w))`.
* `r176h_key_lt_iff (v u : retained) : key_H (liftVisit₀ (Φ v)) < key_H (liftVisit₀ (Φ u)) ↔ key_L (liftVisit₊ v.1) <
  key_L (liftVisit₊ u.1)` — `hkey` at the transported-back parents (`s176_wallΦ_liftVisit`, `Equiv.apply_symm_apply`).
* `r176h_cycBetween_iff (v u x : retained) : cycBetween (coord₀ (Φ v)) (coord₀ (Φ u)) (coord₀ (Φ x)) ↔
  cycBetween (coord₊ v.1) (coord₊ u.1) (coord₊ x.1)` — `CV.visitBetween_iff_key` on both lifts, `unfold cycBetween`,
  `r176h_key_lt_iff` on the three pairs `(v,u), (u,x), (x,v)`.
* `r176h_succ_firstReturn (w : retained) : Φ (firstReturn D₊.record.succ (D₊.record.CrossKeep keep) w) =
  D₀.record.succ (Φ w)` — **the content of `hsucc`**, by `cycNext_unique` on `D₀.visitCoord` (`r176h_visitCoord_injective`):
  - `Φ (fr w) ≠ Φ w`: `Record.firstReturn_val_ne` (one component, `r176h_record_componentCount`) with the retained
    second point from `Record.crossKeep_exists_ne` (the twin), and `Φ.injective`;
  - `D₀.record.succ (Φ w) ≠ Φ w`: `record_succ_eq_self_iff` applied to `twin (Φ w)` contradicts `twin_ne`;
  - no `u` strictly between `Φ w` and `Φ (fr w)`: `u = Φ (Φ.symm u)`, the cyclic order is carried back to the L side by
    `r176h_cycBetween_iff`, and `firstReturn_no_between D₊.record.succ (CrossKeep keep) D₊.visitCoord` (with
    `visitCoord_injOn` and `record_succ_no_between` as its two hypotheses, `Record.sameCycle_iff_comp_eq` for the
    same-cycle side condition) refutes it;
  - no `u` strictly between `Φ w` and `D₀.record.succ (Φ w)`: `record_succ_no_between`.
* **`r176h_succ (w) : Φ ((D₊.record.restrictCrossings (s176_wallKeep u' v')).succ w) = D₀.record.succ (Φ w)`** — the
  exact hypothesis shape of `s176_hrec_unswitched_of_succ`, from `r176h_succ_firstReturn` through the `rfl` lemma
  `Record.restrictCrossings_succ_val` + `Subtype.ext` (see §3, pitfall 1).
* **`r176h_hrec_unswitched (hdet) : Nonempty (RecordIso (D₊.record.restrictCrossings (s176_wallKeep u' v')) D₀.record)`**
  — `hrec` at the carrier level, CLOSED (`s176_hrec_unswitched_of_succ` + `r176h_succ`).

### §K. The event level (section `R176HEvent` and after)
* `r176h_hkey_event (… hcomp hQ hfull hj q) (v w) (hv : v.1 ∈ geoCarrierCrossings (geomAt E t ht.1) (Q ∪ {j}) q) :
  key_t v < key_t w ↔ key_t' (visitTransport hs v) < key_t' (visitTransport hs w)` — `(est_wall …).key_lt v w` with
  `GT_not_rev_of_not_mem_left`: a retained crossing of `q₀` is not a triangle crossing (`est_not_retained_H`,
  `F1.mem_triangleCrossings`).  Only the FIRST visit needs to be retained (the reversed-pair predicate is one-sided).
* **`r176h_hrec_wall_proof (hn hL hR hef heg hfg ht ht' hop hs hcomp hQ hfull hj q hu hju hu') :
  s176_hrec_wall hn hL hR hef heg hfg ht ht' hop hs hQ hfull hj q hu'`** — the stated Prop `s176_hrec_wall` PROVED
  (rule (1) naming), via `s176_hrec_wall_of_succ` with `hsucc := r176h_succ` instantiated at `hG = hG' = ofDiagrammatic …`,
  `hX := s176_hX_event`, `hu_not/hv_not := s176_not_mem_map_event`, `hkey := r176h_hkey_event` (all `rfl`-compatible with
  the event-level binders, Site_176_REPORT §6 pitfall 10).  `r176h_hrec_wall` is the same theorem under the unit's name.
* **`r176h_est_port_weak … : est_port_weak (carrierDiagram hn (genericAt E t' ht'.1) (est_S'_ind …) (GT_carrierEquiv
  (est_wall …) q)) (carrierDiagram hn (genericAt E t ht.1) (est_S_ind …) q) (est_liftCrossing hn (genericAt E t' ht'.1)
  (est_S'_ind …) _ hu')`** — the weak RII port of row 176, `s176_port_weak_of_event'` + `r176h_hrec_wall_proof`.  Its
  only non-standard axioms are those of the frozen glue (`exists_bigonData_of_triangle` = `sorryAx`, `SM.lit_homfly`,
  `SM.lp_lm`, `SM.lp_lm_uniqueness`), exactly as `s176_port_weak_of_event'` (probed, §0).
* **`r176h_est_port_relation_weak_of_rest (hrest) : s176_est_port_relation_weak`** — the weak interface of row 176 from
  the non-move port data ALONE (`hrest` byte-identical to the `hrest` binder of `s176_est_port_relation_weak_of'`).
* **`r176h_est_ledger_weak_of_rest (hF : CV.CarrierSlotFloor) (hrest) : RowShape @ExtremeTransportData`** — the weak RA
  ledger of row 176 from `hrest` alone (`s176_est_ledger_weak`).

## 2. Status of the row-176 chain after this unit

Site_176_REPORT §3 chain: `hsucc` → `s176_hrec_wall_of_succ` → `s176_hrec_wall` → `s176_port_weak_of_event'` →
`est_port_weak D₊ D₀ y` → interface → `s176_est_ledger_weak`.  **Every arrow is now a theorem**; the ledger
`r176h_est_ledger_weak_of_rest` depends on exactly:
1. `hrest` — `Nonempty (s176_PortDataRest …)` for every event configuration (U_R176_REPORT §5 items 2–5: the oriented
   smoothing `D_A` with `componentCount = 2`, the exact owner map (9)/(9a) `poly₁ poly₂` via `S_full = Q' ∪ {j', u', v'}`
   and its outer carriers `Λ₁ Λ₂`, the linking number `ℓ`, the writhe ledger (14), the rotation ledger (13), `alt₁ alt₂`) —
   the ONLY open obligation of row 176 besides F-176-1; ≈ 3–4k lines per Site_176_REPORT §5;
2. the frozen leaf `exists_bigonData_of_triangle` (U-M7, Wave 1) through `s176_port_weak_of_event'`;
3. `CV.CarrierSlotFloor` (`hF`, the assembler's, as for `est_ledger`);
4. F-176-1 acceptance (the 5-line RALedgers edit, Site_176_REPORT §4) to turn `s176_est_*_weak` back into `est_*`.
No obligation of another unit was consumed as a black box here.

## 3. Pitfalls met (and how they were avoided)

1. **`restrictCrossings … .succ w` versus `firstReturn`.**  Stating the successor clause directly on
   `((D₊.record.restrictCrossings keep).succ w)` and closing it with `firstReturn_no_between`/`firstReturn_val_ne` makes the
   unifier identify `((restrictCrossings ρ S).succ w).1` with `(firstReturn f p w).1` by unfolding `firstReturn`/`returnTime`
   (`Nat.find`) instead of `restrictCrossings` — a `(deterministic) timeout at whnf` (200000 heartbeats), twice (once as
   `rw`, once as `exact`).  Also `rw [r176h_cycBetween_iff]` fails to find the pattern because the argument has type
   `(restrictCrossings keep).M`, not the subtype, and `rw` matches at reducible transparency.  Fix (the `m6_succ` shape):
   prove the clause for the literal `firstReturn D₊.record.succ (D₊.record.CrossKeep keep) w` (a genuine element of the
   retained subtype, every step syntactic), then transfer once with `Subtype.ext (Record.restrictCrossings_succ_val …)`
   (`rfl`) and `rw`.  Use `D.record.succ` (not `D.visitSucc`) throughout so the `firstReturn` terms match those of
   `restrictCrossings` letter for letter, with `record_succ_no_between` / `record_succ_eq_self_iff` /
   `Record.sameCycle_iff_comp_eq` supplying the record-level side conditions.
2. **`nextVisit_ne_self _ …` with the visit left as `_`** against a goal `D.record.succ (Φ w) ≠ Φ w`: the unifier must solve
   `D.nextVisit ?v =?= D.record.succ (Φ w)` before `?v` is known and times out (whnf through `compList`/`sort`).  Use the
   record-level `record_succ_eq_self_iff (Φ w)` with every argument explicit (or `rw [record_succ_apply]` first).
3. **`include` lists.**  A theorem whose statement mentions `s176_wallΦ …` automatically includes `hX hu_not hv_not hs`;
   one whose statement only mentions `s176_wallKeep` and `geoPositiveLift` (e.g. `r176h_hrec_unswitched`) does not —
   `hX hu_not hv_not` were "unknown identifiers" in its body until `include hX hu_not hv_not hkey in` (Site_176 §6.5).
4. The `hkey` of the wall only needs the FIRST visit of the pair to be at a retained (hence non-triangle) crossing
   (`GT_Rev T v w` starts with `v.1 ∈ T`); the carrier-level `hkey` binder keeps both memberships to match
   `EXT_homfly_wall`'s shape, the event-level lemma drops the second.
5. `s176_est_port_relation_weak_of'` (frozen) quantifies its `hrec` hypothesis without `hcomp`, `hu`, `hju`, which
   `s176_hrec_wall_of_succ` needs (through `s176_hX_event` and `est_not_retained_H`); so it cannot be fed
   `r176h_hrec_wall_proof` directly.  Not a defect of a stated Prop (the hypothesis is merely too strong to discharge from
   here): `r176h_est_port_relation_weak_of_rest` replays its 5-line body with `r176h_est_port_weak` in place of the `hrec`
   call (the `intro` has `hcomp`, `hu`, `hju` in scope) and takes only `hrest`.
6. Unused-variable lint: the third crossing `v` of the `hsucc` lambda is used only implicitly — name it `_v`.

## 4. Statistics

Appendix 349 lines (estimate was 500–700): 3 bookkeeping lemmas (§I), 6 carrier-level theorems (§J), 6 event-level theorems
(§K); 4 compile iterations to 0 errors; no `sorry`, no `set_option maxHeartbeats`, no `set_option` at all.
