# U2 — the record core (infrastructure for U3 and U6): report

2026-09-14, prover for unit U2 (PLAN_FINAL.md §4 "L-rec", §5 "U2 record core").  File:
`work/drafts/frontrows/U_U2.lean` = `Skeleton_FINAL.lean` + one inserted block (lines 219–1972, a single `diff`
hunk `218a219,1972`, zero lines removed or changed), the section
`/-! ### U2 infrastructure — the record core -/` … `namespace U2 … end U2`, placed immediately before the L-rec
docstring (the first consumer, `comm_recordIso`).  No leaf touched: `grep -c sorry` 26 before, 26 after; the
compile `cd work/lean && lake env lean ../drafts/frontrows/U_U2.lean` gives **0 errors**, 26 `declaration uses
sorry` warnings (the other units' leaves), no other warning.  `#print axioms` on `U2.slotRecord`,
`U2.realizeRecordIso`, `U2.diagramRecordIso`, `U2.extRecordIso`, `U2.extRecordIsoAddFree`,
`U2.vertexMovedRecordIso'`, `U2.realize_recordIso_of_ext`, `U2.realize_recordIso_addFree_of_ext`,
`U2.slotRecordIsoOfSlotEquiv`: `[propext, Classical.choice, Quot.sound]` only.  1,754 lines (estimate 2.5–3.5k).
Naming: the plan's rule "helpers prefixed `<unit>_`" is realised as the namespace `SM.FrontRows.U2`, so the
plan's names are `U2.slotRecord`, `U2.realizeRecordIso`, …; nothing else in the file was changed.

## 1. What the record core is

**The abstract named record of a closed word.**  For `W : Word`, `hW : W.Closed` and an *active set*
`S : Slot W → Prop` (`[DecidablePred S]`, `hS : U2.ActiveSet hW S` = every active slot is a `σ` slot and the set
is closed under the twin):

```
U2.slotRecord hW S hS : Record
  comps := Fin (numComp hW)                      -- the components (cycles of `next`), free ones included
  M     := {u : Slot W // S u}                   -- one occurrence per active crossing strand
  comp  := U2.slotComp hW ∘ val                  -- component of the slot's strand  (= Fintype.equivFin (orbitOf u))
  succ  := firstReturn (nextPerm hW) S           -- the next active slot along the slot cycle `next`
  pair  := U2.σtwin hW                           -- the other crossing strand of the column
  isOver:= U2.isDesc                             -- descending pass `pass m (m+1)` = over (the printed rule)
  sgn   := U2.σsgn                               -- +1 iff the two bits of the column agree (β1's `signBit`)
```
`σ` slots: `U2.IsσSlot u` (decidable; `U2.isσSlot_iff`: `u = σSlotA hW hk hℓ ∨ u = σSlotB hW hk hℓ`),
`U2.σtwin_σSlotA = σSlotB`, `σtwin_σSlotB = σSlotA`, `σtwin_σtwin`, `σtwin_ne`, `colOf_σtwin`, `isDesc_σtwin`,
`isDesc_σSlotA = true`, `isDesc_σSlotB = false`, `coe_σsgn_eq_signBit`, `coe_σsgn_σSlotA` (= the geometric sign of
`crossingOf`).  Simp/rfl lemmas `slotRecord_comps/M/comp/succ/succ_val/pair_val/isOver/sgn`;
`slotRecordCongr` for pointwise-equivalent active sets; `slotComp_eq_iff` (same component ↔ `SameCycle`),
`slotComp_eq_equivFin`.  Two ready-made active sets: all `σ` slots (`IsσSlot`, `U2.allActive hW`) and the `σ`
slots of a set of columns `K` (`U2.colActive K u := IsσSlot u ∧ K (colOf u)`, `U2.colActive_activeSet`).

**Realizations.**  `U2.realizeAtRecordIso pl hW hne : RecordIso (realizeAt pl hW hne).diagram.record
(slotRecord hW IsσSlot (allActive hW))` and `U2.realizeRecordIso (W : OWord) (h : W.letters ≠ []) :
RecordIso (realize W).diagram.record (slotRecord W.closed IsσSlot (allActive W.closed))` — THE plan's
`realizeRecordIso` for `S` = all `σ` slots.

**Any diagram on the strands of a realization** (the vertex-moved `D` of U6; `V := (shadowOf …).vertices` is the
realization itself): `U2.mkDiagram pl hW hne V hgen ov hov : Diagram := ⟨(shadowOf pl hW hne).withVertices V, hgen,
ov, hov⟩`; `U2.SlotDiagramData pl hW hne V hgen ov hov K : Prop` (three fields) says its crossings are exactly
the `σ` pairs `U2.σpair … hk hℓ = {stStrand (σSlotA hW hk hℓ), stStrand (σSlotB hW hk hℓ)}` of the columns in
`K`, the over strand of each is the descending one, and the sign is `if bit W k m = bit W k (m+1) then 1 else -1`.
Then **`U2.diagramRecordIso … K data : RecordIso (mkDiagram …).record (slotRecord hW (colActive K) _)`**.  Its
heart is `U2.nextVisit_eq`: the forward successor of a visit is the first return of `next` to the active slots
(each strand carries at most one visit; the traversal order of the visits on a component is the cyclic order of
their strand labels; proved with `cycNext_unique_on`, `nextVisit_no_between`, `cycIdx_iff`).
`U2.realizeAt_data` is the instance for the realization (`crossing_char`/`eq_crossingOf`, `overStrand_crossingOf`,
`sign_crossingOf`).

## 2. The exterior correspondence (β2's `shiftIdx` / `extSlot` / `next_ext`)

Setting `X P Y P' : Word`, `hP : P ≠ []`, `hE : SameEffect X P P'`, `hW : (X ++ P ++ Y).Closed`,
`hW' : (X ++ P' ++ Y).Closed`; **`P' = []` is allowed everywhere** (the deletions with an empty factor).

* `U2.ExtPiece X P Y u := ExtCol X P (colOf u)` — slots whose piece lies in an exterior column (decidable).
* `U2.φE X P Y P' hP hE hW : {u // ExtPiece X P Y u} ≃ {u' // ExtPiece X P' Y u'}` — THE exterior slot
  correspondence, `(φE u).1 = extSlot X P Y P' hP hE ⟨u.1, _⟩`, `(φE u).1.1 = extPair X P P' u.1.1` (`φE_val`),
  `colOf (φE u).1 = shiftIdx X P P' (colOf u.1)` (`colOf_φE`), `shapeOf_φE`, `letterAt_colOf_φE`, `bit_colOf_φE`,
  `isσSlot_φE_iff`, `isDesc_φE`, `σsgn_φE`, `φE_σtwin`.  Bijectivity is proved directly (`extF_injective`,
  `extF_surjective` with the inverse column shift `U2.unshiftCol`), so no `P' ≠ []` is needed.
* **The hypothesis the rows verify — `U2.Passage X P Y P' hW hW'`** (one field `pass`): for every *entry slot*
  `b` (`IsExtSlot X P b.1 ∧ ¬ ExtCol X P (colOf b)`; concretely, `U2.entry_iff`: `b.1 = (|X|, p)` with
  `bit W |X| p = true`, or `b.1 = (|X|+|P|, p)` with `bit W (|X|+|P|) p = false`), there are `m`, `c` with
  `(next hW)^[m] b = c`, `ExtCol X P (colOf c)`, all `(next hW)^[i] b` (`i < m`) in the block, and `m'`, `b'` with
  `b'.1 = extPair X P P' b.1`, `((next hW')^[m'] b').1 = extPair X P P' c.1`, all `(next hW')^[i] b'` (`i < m'`) in
  the block of `W'` (`m' = 0` when `P' = []`).  This is what U3 (zigzag, circle) and U6 (types I, II, crossed
  cusp) compute on their concrete factors with `nextPair_*`/`next_cases`.
* `U2.conj_of_passage hpass : ∀ u, firstReturn (nextPerm hW') (ExtPiece X P' Y) (φE u) = φE (firstReturn
  (nextPerm hW) (ExtPiece X P Y) u)` — the passage makes the first returns to the exterior *conjugate*; from
  the conjugation alone (no reverse hypothesis) both the successor law on the active slots
  (`U2.firstReturn_conj_of_factor`, via `U2.firstReturn_factor`: the first return to `p ⊆ E` factors through
  the first return to `E`) and the bijection of components (`U2.cycleEquiv`, `U2.cycleEquivOption`) follow.
* **`U2.extRecordIso hpass hexit hexit' : RecordIso (slotRecord hW (colActive (ExtCol X P)) _)
  (slotRecord hW' (colActive (ExtCol X P')) _)`** with `hexit : ∀ u, ∃ n, ExtPiece X P Y ((next hW)^[n] u)`
  (every component meets the exterior; this is β2's `ExitsBlock` in slot form) and `hexit'` likewise for `W'`
  (trivial when `P' = []`).
* **`U2.extRecordIsoAddFree hpass hexit' c₀ hc₀ : RecordIso (slotRecord hW …) (slotRecord hW' …).addFree`**
  for the circle deletion: `c₀ : Orbit hW`, `hc₀ : ∀ u, (¬ ∃ n, ExtPiece X P Y ((next hW)^[n] u)) ↔ orbitOf hW u
  = c₀` (exactly the circle misses the exterior).  `U2.addFreeCongr` transports a `RecordIso` through `addFree`.

## 3. Composed statements for U3 / U6 (what to `exact`)

* U6 (`typeII_move`, `typeI_move`, `crossedCusp_move`): with `W = X ++ P ++ Y`, the vertex-moved diagram built as
  `U2.mkDiagram .std hW hne V hgen ov hov` (or anything definitionally of that form), `data : SlotDiagramData … V
  hgen ov hov (ExtCol X P)` (crossings = the exterior `σ` pairs; U4 supplies genericity and the crossing set,
  the over/sign fields are `overStrand_crossingOf`-style facts on unchanged strands), `hpass`, `hexit`, `hexit'`,
  `hnoσ : ∀ k, |X| ≤ k → k < |X| + |P'| → (letterAt (X ++ P' ++ Y) k).isCrossing = false`:
  **`U2.vertexMovedRecordIso' X P Y P' hP hE hW hW' .std hne V hgen ov hov data hpass hexit hexit' hnoσ W' hW'eq hne'
  : RecordIso (mkDiagram …).record (realize W').diagram.record`** (`hW'eq : W'.letters = X ++ P' ++ Y`; `hE`
  from `sameEffect_of_replace` and β1's `run_*` lemmas).  `U2.vertexMovedRecordIso` is the `realizeAt pl'` form.
* U3 `zigzag_recordIso` (and any deletion with `P' = []`): **`U2.realize_recordIso_of_ext … hpass hexit hexit'
  hnoσ hnoσ' W W' hWeq hW'eq : Nonempty (RecordIso (realize W).diagram.record (realize W').diagram.record)`**
  (`hnoσ`: no `σ` in `P`, `hnoσ'`: none in `P'`; with `P' = []` write `W'.letters = X ++ [] ++ Y`, i.e.
  `by simpa using hW'eq`).
* U3 `circle_recordIso_addFree`: **`U2.realize_recordIso_addFree_of_ext … hpass hexit' c₀ hc₀ hnoσ hnoσ' W W'
  hWeq hW'eq : Nonempty (RecordIso (realize W).diagram.record (realize W').diagram.record.addFree)`**.
* U3 `comm_recordIso` and the switch half of `skein_site` (`|P| = |P'|`, a bijection of ALL slots): 
  **`U2.slotRecordIsoOfSlotEquiv hW hW' S S' hS hS' ψ hnext hact htwin hdesc hsgn`** for `ψ : Slot W ≃ Slot W'`
  with `ψ (next hW u) = next hW' (ψ u)`, `S' (ψ u) ↔ S u`, and twin/`isDesc`/`σsgn` preserved on `S`; compose with
  `realizeRecordIso` on both sides.  For the switch record, build `RecordIso (slotRecord A' all)
  ((slotRecord A all).switch x)` from the `slotRecord_*` rfl-lemmas (bits and signs flipped at `x`, `pair x`)
  and transport `(realize A).diagram.switch x` with the library's `switch_record`; the smoothing half uses the
  library's `Record.smooth` API (`smooth_succ_val_of_*`) on `slotRecord A IsσSlot`.
* `U2.colActive_extCol_iff` (no `σ` in the block ⇒ exterior `σ` slots = all `σ` slots), `U2.realizeAtRecordIsoOfExt`.

## 4. Generic tools (reusable beyond U2)

`U2.firstReturn_pow_of_pow_strong`, `U2.firstReturn_factor`, `U2.firstReturn_conj`, `U2.firstReturn_eq_of_path`
(`(firstReturn f E a).1 = (f^m) a.1` from a path: `E ((f^m) a)`, none before), `U2.returnTime_le_of_pow_eq`;
`U2.pow_conj`, `U2.sameCycle_of_conj`, `U2.sameCycle_iff_of_conj`, `U2.sameCycle_φ_iff`, `U2.repE`,
`U2.cycleMap`, `U2.cycleEquiv` (+ `_mk`), `U2.cycleEquivOption` (+ `_mk`), `U2.orbitEquivOfSlotEquiv`;
`U2.visit_ext`, `U2.signType_ext_int`, `U2.cycBetween_nat_add`; `U2.idxEquiv_add`, `U2.nextPerm_pow_apply`.

## 5. Gotchas recorded for the consumers

1. **Strand types.** `((shadowOf pl hW hne).withVertices V).Strand` and `Idx hW` are definitionally but not
   syntactically equal (`(shadowOf …).c` vs `numComp hW`, `((… ).comp i).k` vs `period hW (rep hW i)`).  A sigma
   literal `⟨i, a⟩` elaborates at whichever type is expected, `rw` then fails and `exact` across the two can
   time out (it unfolds `ZMod.val`/`period`).  Use the identity maps `U2.stStrand` (slot → strand of the
   re-vertexed shadow) and `U2.strIdx` (strand → `Idx hW`), state equations through them, and finish with
   `exact` of a `congrArg`; see `U2.visitCoord_eq_of`, `U2.compOf_eq_of`.  The `Finset` literal in `σpair` is
   built from `stStrand` for the same reason (`Finset.mem_insert` would not fire otherwise).
2. **Section variables.** Lean includes only header-mentioned variables; the β2 lemmas under `include hP hE`
   take `X P Y P' hP hE` (e.g. `isExtSlot_of_extCol X P Y P' hP hE u h`); `length_W' X Y P'`.
3. `Passage` is stated with the total `extPair` (no `P' ≠ []`); `entry_iff` needs `hP` and closedness.
4. The empty word: all statements are for nonempty words (`realize_eq_realizeAt`); no row hypothesis produces `[]`.

## 6. Appendix — declarations of `namespace SM.FrontRows.U2` (in file order)
- L246: theorem firstReturn_pow_of_pow_strong (E 
- L278: theorem firstReturn_factor (E 
- L303: theorem firstReturn_conj (p 
- L322: theorem firstReturn_eq_of_path (E 
- L330: theorem returnTime_le_of_pow_eq (E 
- L343: theorem pow_conj {φ 
- L350: theorem sameCycle_of_conj {φ 
- L356: theorem conj_symm {φ 
- L360: theorem sameCycle_iff_of_conj {φ 
- L369: theorem sameCycle_φ_iff (conj 
- L374: theorem conj_symm' (conj 
- L380: theorem firstReturn_conj_of_factor (conj 
- L395: theorem sameCycle_pow (n 
- L399: noncomputable def repE (hE 
- L403: theorem repE_sameCycle (hE 
- L407: noncomputable def cycleMap (conj 
- L417: theorem cycleMap_mk (conj 
- L424: theorem cycleMap_mk' (conj 
- L430: noncomputable def cycleEquiv (conj 
- L450: theorem cycleEquiv_mk (conj 
- L459: noncomputable def cycleEquivOption (conj 
- L522: theorem cycleEquivOption_mk (conj 
- L545: theorem letterAt_σ_of_isCrossing {k 
- L554: def isDesc (u 
- L561: def IsσSlot (u 
- L566: instance 
- L570: def σsgnCol (W 
- L574: def σsgn (u 
- L576: theorem σsgnCol_ne_zero (k 
- L579: theorem σsgn_ne_zero (u 
- L581: theorem coe_σsgnCol (k 
- L589: theorem isσSlot_σSlotA {k m 
- L596: theorem isσSlot_σSlotB {k m 
- L603: theorem isDesc_σSlotA {k m 
- L607: theorem isDesc_σSlotB {k m 
- L612: theorem colOf_lt (u 
- L615: theorem eq_σSlotA_or_σSlotB {u 
- L624: theorem isσSlot_iff (u 
- L635: theorem σslot_ext {u v 
- L644: theorem isDesc_eq_true_iff {u 
- L650: noncomputable def σtwin (u 
- L656: theorem σtwin_spec {u 
- L666: theorem colOf_σtwin {u 
- L668: theorem isσSlot_σtwin {u 
- L670: theorem isDesc_σtwin {u 
- L673: theorem σtwin_σtwin {u 
- L679: theorem σtwin_ne {u 
- L685: theorem σsgn_σtwin {u 
- L688: theorem σtwin_σSlotA {k m 
- L695: theorem σtwin_σSlotB {k m 
- L700: theorem coe_σsgn_eq_signBit {u 
- L709: theorem coe_σsgn_σSlotA (pl 
- L723: noncomputable def slotComp (u 
- L725: theorem slotComp_eq_iff (u v 
- L731: theorem slotComp_idxEquiv (s 
- L736: theorem slotComp_eq_equivFin (u 
- L746: structure ActiveSet (S 
- L753: noncomputable def slotPair 
- L768: noncomputable def slotRecord 
- L786: theorem slotRecord_comp (u 
- L787: theorem slotRecord_succ 
- L788: theorem slotRecord_succ_val (u 
- L790: theorem slotRecord_pair_val (u 
- L792: theorem slotRecord_isOver (u 
- L793: theorem slotRecord_sgn (u 
- L796: noncomputable def slotRecordCongr (S' 
- L815: theorem visit_ext {Γ 
- L822: theorem signType_ext_int {a b 
- L827: theorem cycBetween_nat_add {A B C 
- L844: def colActive (K 
- L846: instance (K 
- L849: theorem colActive_activeSet (K 
- L853: theorem colActive_σSlotA {K 
- L856: theorem colActive_σSlotB {K 
- L862: noncomputable def stStrand (u 
- L870: theorem stStrand_injective 
- L873: def strIdx (s 
- L875: theorem idxEquiv_strIdx (s 
- L878: theorem strIdx_stStrand (u 
- L880: theorem eq_stStrand_iff (s 
- L889: noncomputable abbrev mkDiagram 
- L895: noncomputable abbrev σpair {k m 
- L899: theorem mem_σpair_A {k m 
- L902: theorem mem_σpair_B {k m 
- L906: theorem mem_σpair_iff {k m 
- L911: theorem colOf_of_mem_σpair {k m 
- L923: structure SlotDiagramData 
- L937: noncomputable def σcross {k m 
- L941: theorem σcross_val {k m 
- L945: theorem visit_active (v 
- L954: theorem crossing_eq_of_mem {x y 
- L966: noncomputable def toVisit (u 
- L972: theorem toVisit_strand (u 
- L976: noncomputable def visitEquiv 
- L990: theorem visitEquiv_apply_val (v 
- L993: theorem visitEquiv_symm_apply (u 
- L997: theorem slot_other {x 
- L1017: theorem overBit_eq (v 
- L1033: theorem sign_eq (v 
- L1041: theorem visit_eq_of_strand_eq {w w' 
- L1047: theorem idxEquiv_add (i 
- L1056: theorem nextPerm_pow_apply (n 
- L1061: theorem visitCoord_eq (w 
- L1067: theorem visitCoord_eq_of (w 
- L1077: theorem compOf_eq_of (w 
- L1085: theorem nextVisit_eq [DecidablePred K] (v 
- L1213: noncomputable def diagramRecordIso [DecidablePred K] 
- L1240: theorem allActive 
- L1245: theorem realizeAt_data 
- L1267: noncomputable def realizeAtRecordIso 
- L1284: instance instDecidableExtCol (k 
- L1285: instance instDecidablePredExtCol 
- L1288: def ExtPiece (u 
- L1290: instance 
- L1292: theorem extPiece_σtwin (hW 
- L1296: theorem shiftIdx_injOn (hP 
- L1304: def unshiftCol (k' 
- L1306: theorem unshiftCol_spec (hP 
- L1313: theorem colOf_mk {V 
- L1320: noncomputable def extF (u 
- L1327: theorem extF_val (u 
- L1330: theorem extF_eq (u 
- L1333: theorem extF_injective 
- L1380: theorem length_W' 
- L1383: theorem length_W 
- L1386: theorem extF_surjective 
- L1469: noncomputable def φE 
- L1472: theorem φE_apply (u 
- L1475: theorem φE_val (u 
- L1478: theorem colOf_φE (u 
- L1487: structure Passage 
- L1496: theorem conj_of_passage (hpass 
- L1550: theorem entry_iff (b 
- L1596: theorem shapeOf_φE (u 
- L1629: theorem letterAt_colOf_φE (u 
- L1633: theorem bit_colOf_φE (u 
- L1638: theorem isσSlot_φE_iff (u 
- L1643: theorem isDesc_φE (u 
- L1647: theorem σsgn_φE (u 
- L1652: theorem φE_σtwin (u 
- L1664: theorem colActive_φE_iff (u 
- L1671: noncomputable def extActiveEquiv 
- L1687: theorem extActiveEquiv_val (u 
- L1692: noncomputable def extRecordIso (hpass 
- L1745: noncomputable def realizeRecordIso (W 
- L1751: theorem colActive_extCol_iff (X P Y 
- L1768: noncomputable def orbitEquivOfSlotEquiv (ψ 
- L1775: noncomputable def slotRecordIsoOfSlotEquiv (ψ 
- L1807: noncomputable def vertexMovedRecordIso (pl 
- L1823: noncomputable def vertexMovedRecordIso' (pl 
- L1842: noncomputable def realizeAtRecordIsoOfExt (hne 
- L1858: theorem realize_recordIso_of_ext (hne 
- L1881: noncomputable def addFreeCongr {ρ ρ' 
- L1897: noncomputable def extRecordIsoAddFree (hpass 
- L1947: theorem realize_recordIso_addFree_of_ext (hne 
