# MERGE1_REPORT — front certificate rows, wave 1 merge (U1 + U2 + U7)

Written 2026-09-14 08:50 UTC / 4:50am ET by the wave-1 merger.  Output file:
`work/drafts/frontrows/Skeleton_W1.lean` (4009 lines).  Toolchain: Lean 4.34.0-rc2, project Mathlib pin;
compiled with `cd work/lean && lake env lean ../drafts/frontrows/Skeleton_W1.lean`.

## 1. Result

| item | value |
|---|---|
| compile | **0 errors**; exactly 13 `declaration uses sorry` warnings; no other warning |
| `grep -c sorry Skeleton_W1.lean` | **13** (Skeleton_FINAL.lean: 26; U1 removed 12, U7 removed 1) |
| remaining sorries | the 13 leaves of U3 (5), U5/U6 (4), U8 (4) — list in §3; no wave-1 leaf is unproved |
| `diff Skeleton_FINAL.lean Skeleton_W1.lean` | removes exactly the 15 lines that are `sorry` bodies of the 13 proved leaves (12 `:= sorry` / `:=`+`sorry` bodies of U1, 1 of U7); every other skeleton line (definitions, the eight bundles, all leaf statements, docstrings, glue, rows) is present verbatim and in order |
| `#print axioms` (scratch probe `/workspace/scratch/lean_merge1/W1_ax.lean`) | the 13 proved leaves and the key U2 declarations: `[propext, Classical.choice, Quot.sound]` only.  `PLFront.IsStandardCircles.defect_eq_zero` (row 81 sentences 2-3) is now sorry-free: `[propext, Classical.choice, Quot.sound, SM.lp_lm]` (the accepted axiom, through `P`).  The eight row theorems still reach `sorryAx` through the wave-2 leaves, as planned |

Scripts (not deliverables): `/workspace/scratch/lean_merge1/verify_merge.py` (verification + merge),
`extract_u2.py` (the appendix), `compile_W1.log`.

## 2. Verification of the units (task step 1)

Method: `difflib.SequenceMatcher` of each unit against `Skeleton_FINAL.lean`, line-exact.  Allowed edits are
(a) a skeleton line ending in `:= sorry` replaced by lines whose first is the same text with `sorry` removed
(the header verbatim, `:=` or `:= by`), (b) a lone `sorry` line (multi-line leaf) dropped and its header line
given a trailing ` by`, (c) inserted lines.  Anything else fails.  All three units pass; U3, U4, U5, U6, U8 are
byte-identical copies of the skeleton (`cmp`), i.e. nothing to merge.

| unit | hunks vs skeleton | removed lines | inserted | `grep -c sorry` |
|---|---|---|---|---|
| U_U1.lean | 14, all inside skeleton lines 149-217 (the L-deg and L-cnt leaves) | the 12 sorry bodies of `delta_ne_zero`, `degAZ_delta`, `degAZ_le_of_eq_pos`, `degAZ_le_of_eq_neg`, `comm_counts`, `typeI_counts`, `typeII_counts`, `typeIII_counts`, `zigzag_counts`, `crossedCusp_counts`, `circleDeletion_counts`, `skein_counts` | 51 `u1_*` helpers (12 inline before their leaf, 39 in `section U1Infra`) + 12 proofs | 26 → 14 |
| U_U2.lean | 1, pure insertion after skeleton line 218 (before the L-rec docstring) | none | `/-! ### U2 infrastructure … -/` + `namespace U2 … end U2` (1754 lines, 159 declarations) | 26 → 26 |
| U_U7.lean | 2: insertion after skeleton line 317, replacement of line 323 | the `:= sorry` of `PLFront.IsStandardCircles.downCount_eq_c_general` | `section u7_helpers … end u7_helpers` (25 `u7_*` helpers) + 6-line proof | 26 → 25 |

Skeleton ranges touched: U1 ⊂ [149, 217], U2 = {after 218}, U7 ⊂ [318, 323] — pairwise disjoint, so the merge is
the union of the hunks applied to the skeleton (no conflict resolution needed).  Name clashes: none — U1 uses the
prefix `u1_`, U7 `u7_`, U2 the namespace `SM.FrontRows.U2`; a scan of every `theorem/def/abbrev/structure` name in the
merged file finds no duplicate.  Nothing was renamed or de-duplicated.

## 3. Layout of Skeleton_W1.lean

| lines | content |
|---|---|
| 1-148 | skeleton header, `Statements` (verbatim), nonemptiness helpers (unchanged) |
| 149-234 | L-deg: `delta_ne_zero`, `degAZ_delta`, `degAZ_le_of_eq_pos`, `degAZ_le_of_eq_neg` PROVED, with 12 inline `u1_*` helpers |
| 240-937 | `/-! ### U1 infrastructure -/`, `section U1Infra` (245) … `end U1Infra` (936): word-layer count lemmas |
| 941-1159 | L-cnt: the 8 count leaves PROVED |
| 1161-2913 | `/-! ### U2 infrastructure — the record core -/` docstring, `namespace U2` (1175) … `end U2` (2913) |
| 2914-3008 | L-rec docstring and leaves (U3): `comm_recordIso` 2924, `zigzag_recordIso` 2930, `circle_recordIso_addFree` 2936, `def SkeinSite`, `skein_site` 2958, `skein_unique` 2964 — `sorry` |
| 2966-3008 | L-geo leaves (U5/U6): `typeIII_site` 2982, `typeII_move` 2991, `typeI_move` 2999, `crossedCusp_move` 3008 — `sorry` |
| 3014-3653 | `section u7_helpers` … `end u7_helpers` (25 `u7_*` helpers) |
| 3660-3665 | `PLFront.IsStandardCircles.downCount_eq_c_general` PROVED |
| 3667-3692 | L-smooth leaves (U8): `deform_downCount` 3673, `deform_writhe` 3678, `deform_P` 3683, `represent` 3689 — `sorry` |
| 3694-4009 | `end Leaves`, glue, assembly of the eight rows, row 83 (unchanged) |

Remaining `sorry` (13): `comm_recordIso`, `zigzag_recordIso`, `circle_recordIso_addFree`, `skein_site`,
`skein_unique` (U3); `typeIII_site` (U5); `typeII_move`, `typeI_move`, `crossedCusp_move` (U6); `deform_downCount`,
`deform_writhe`, `deform_P`, `represent` (U8).

## 4. What U3 (and U4/U6) may now consume from U2 (task step 3)

Everything below lives in `namespace SM.FrontRows.U2` (the file is inside `namespace SM … namespace FrontRows`, so
consumers write `U2.name`).  The block opens `SM.FrontRealize SM.FrontWord.Letter Equiv`.  Section variables are
listed with each group; Lean includes a section variable only if the statement mentions it, except under
`include` (noted).  Exact signatures of all 159 declarations, in file order with their section context, are in the
Appendix; the statements below are copied from the merged file.

### 4.1 The abstract named record of a closed word (section `SlotRecord`; `variable {W : Word} (hW : W.Closed)`, then `(S : Slot W → Prop) [DecidablePred S] (hS : ActiveSet hW S)`)

```lean
structure ActiveSet (S : Slot W → Prop) : Prop where
  isσ : ∀ u, S u → IsσSlot u
  twin : ∀ u, S u → S (σtwin hW u)

noncomputable def slotRecord : Record      -- U2.slotRecord hW S hS
@[simp] theorem slotRecord_comps : (slotRecord hW S hS).comps = Fin (numComp hW)
@[simp] theorem slotRecord_M : (slotRecord hW S hS).M = {u : Slot W // S u}
theorem slotRecord_comp (u : {u : Slot W // S u}) : (slotRecord hW S hS).comp u = slotComp hW u.1
theorem slotRecord_succ : (slotRecord hW S hS).succ = firstReturn (nextPerm hW) S
theorem slotRecord_succ_val (u : {u : Slot W // S u}) :
    ((slotRecord hW S hS).succ u).1 = ((nextPerm hW) ^ returnTime (nextPerm hW) S u.1 u.2) u.1
theorem slotRecord_pair_val (u : {u : Slot W // S u}) : ((slotRecord hW S hS).pair u).1 = σtwin hW u.1
theorem slotRecord_isOver (u : {u : Slot W // S u}) : (slotRecord hW S hS).isOver u = isDesc u.1
theorem slotRecord_sgn (u : {u : Slot W // S u}) : (slotRecord hW S hS).sgn u = σsgn u.1
noncomputable def slotRecordCongr (S' : Slot W → Prop) [DecidablePred S'] (hS' : ActiveSet hW S')
    (h : ∀ u, S u ↔ S' u) : RecordIso (slotRecord hW S hS) (slotRecord hW S' hS')

noncomputable def slotComp (u : Slot W) : Fin (numComp hW)
theorem slotComp_eq_iff (u v : Slot W) : slotComp hW u = slotComp hW v ↔ (nextPerm hW).SameCycle u v
theorem slotComp_idxEquiv (s : Idx hW) : slotComp hW (idxEquiv hW s) = s.1
theorem slotComp_eq_equivFin (u : Slot W) : slotComp hW u = Fintype.equivFin (Orbit hW) (orbitOf hW u)
```
(`slotRecord_comps`/`_M` are `rfl`; `pair`, `isOver`, `sgn` are given on the subtype, `succ` is literally
`firstReturn (nextPerm hW) S`.)  For the **switch record** needed by `skein_site` (U3): build
`RecordIso (slotRecord A' IsσSlot _) ((slotRecord A IsσSlot _).switch x)` from these rfl-lemmas (bits and sign
flipped at `x` and `pair x`, everything else equal), then transport with the library's `switch_record` and
`realizeRecordIso` on both sides; the smoothing half uses the library's `Record.smooth` API on
`slotRecord A IsσSlot _`.

### 4.2 `σ` slots, twin, over bit, sign (section `SigmaSlots`; `variable {W : Word}`, later `(hW : W.Closed)` with `include hW`)

```lean
def IsσSlot (u : Slot W) : Prop                    -- decidable
def isDesc (u : Slot W) : Bool                     -- descending pass = over strand
def σsgnCol (W : Word) (k : ℕ) : SignType
def σsgn (u : Slot W) : SignType
noncomputable def σtwin (u : Slot W) : Slot W       -- U2.σtwin hW u (hW explicit)
theorem letterAt_σ_of_isCrossing {k : ℕ} (h : (letterAt W k).isCrossing = true) : letterAt W k = .σ (letterAt W k).idx
theorem σsgn_ne_zero (u : Slot W) : σsgn u ≠ 0
theorem coe_σsgnCol (k : ℕ) : ((σsgnCol W k : SignType) : ℤ) =
    if bit W k (letterAt W k).idx = bit W k ((letterAt W k).idx + 1) then 1 else -1
theorem isσSlot_σSlotA {k m : ℕ} (hk : k < W.length) (hℓ : letterAt W k = .σ m) : IsσSlot (σSlotA hW hk hℓ)
theorem isσSlot_σSlotB … : IsσSlot (σSlotB hW hk hℓ)
theorem isDesc_σSlotA … : isDesc (σSlotA hW hk hℓ) = true
theorem isDesc_σSlotB … : isDesc (σSlotB hW hk hℓ) = false
theorem colOf_lt (u : Slot W) : colOf u < W.length
theorem eq_σSlotA_or_σSlotB {u : Slot W} (hu : IsσSlot u) :
    u = σSlotA hW (colOf_lt hW u) (letterAt_σ_of_isCrossing hu.1) ∨ u = σSlotB hW (colOf_lt hW u) (letterAt_σ_of_isCrossing hu.1)
theorem isσSlot_iff (u : Slot W) : IsσSlot u ↔ ∃ (k m : ℕ) (hk : k < W.length) (hℓ : letterAt W k = .σ m),
      u = σSlotA hW hk hℓ ∨ u = σSlotB hW hk hℓ
theorem σslot_ext {u v : Slot W} (hu : IsσSlot u) (hv : IsσSlot v) (hc : colOf u = colOf v) (hd : isDesc u = isDesc v) : u = v
theorem isDesc_eq_true_iff {u : Slot W} (hu : IsσSlot u) :
    isDesc u = true ↔ shapeOf u = .pass (letterAt W (colOf u)).idx ((letterAt W (colOf u)).idx + 1)
theorem σtwin_spec {u : Slot W} (hu : IsσSlot u) :
    colOf (σtwin hW u) = colOf u ∧ IsσSlot (σtwin hW u) ∧ isDesc (σtwin hW u) = !isDesc u
theorem colOf_σtwin / isσSlot_σtwin / isDesc_σtwin        -- the three conjuncts separately
theorem σtwin_σtwin {u : Slot W} (hu : IsσSlot u) : σtwin hW (σtwin hW u) = u
theorem σtwin_ne {u : Slot W} (hu : IsσSlot u) : σtwin hW u ≠ u
theorem σsgn_σtwin {u : Slot W} (hu : IsσSlot u) : σsgn (σtwin hW u) = σsgn u
theorem σtwin_σSlotA … : σtwin hW (σSlotA hW hk hℓ) = σSlotB hW hk hℓ
theorem σtwin_σSlotB … : σtwin hW (σSlotB hW hk hℓ) = σSlotA hW hk hℓ
theorem coe_σsgn_eq_signBit {u : Slot W} (hu : IsσSlot u) :
    ((σsgn u : SignType) : ℤ) = (letterAt W (colOf u)).signBit (cut W (colOf u))
theorem coe_σsgn_σSlotA (pl : Placement) (hne : W ≠ []) {k m : ℕ} (hk : k < W.length) (hℓ : letterAt W k = .σ m) :
    ((σsgn (σSlotA hW hk hℓ) : SignType) : ℤ) = ((realizeAt pl hW hne).diagram.sign (crossingOf pl hW hne hk hℓ) : ℤ)
```
`coe_σsgn_eq_signBit` is the bridge to U1's word-layer sign (`signBit`), i.e. to `writheFrom`; `skein_site`'s
sign clause (`sign x = w_A − w_C`) can be read through it together with U1's `u1_writheFrom_append₃`.

### 4.3 Active sets and the records of realizations (sections `DiagramIso`, `Realize`; `variable (pl : Placement) {W : Word} (hW : W.Closed) (hne : W ≠ [])`)

```lean
def colActive (K : ℕ → Prop) (u : Slot W) : Prop            -- IsσSlot u ∧ K (colOf u); decidable for [DecidablePred K]
theorem colActive_activeSet (K : ℕ → Prop) : ActiveSet hW (colActive K)
theorem colActive_σSlotA {K : ℕ → Prop} {k m : ℕ} (hk : k < W.length) (hℓ : letterAt W k = .σ m) (hK : K k) : colActive K (σSlotA hW hk hℓ)
theorem colActive_σSlotB … : colActive K (σSlotB hW hk hℓ)
theorem allActive : ActiveSet hW (IsσSlot (W := W))            -- U2.allActive hW

noncomputable def realizeAtRecordIso :
    RecordIso (realizeAt pl hW hne).diagram.record (slotRecord hW IsσSlot (allActive hW))   -- U2.realizeAtRecordIso pl hW hne
noncomputable def realizeRecordIso (W : OWord) (h : W.letters ≠ []) :
    RecordIso (realize W).diagram.record (slotRecord W.closed IsσSlot (allActive W.closed))  -- THE plan's realizeRecordIso
theorem colActive_extCol_iff (X P Y : Word)
    (hnoσ : ∀ k, X.length ≤ k → k < X.length + P.length → (letterAt (X ++ P ++ Y) k).isCrossing = false)
    (u : Slot (X ++ P ++ Y)) : colActive (ExtCol X P) u ↔ IsσSlot u
```

Any diagram on the strands of a realization (for U6's vertex-moved `D`; U4 supplies `V`, `hgen`, and the crossing
set), with `variable (V : (shadowOf pl hW hne).Vertices) (hgen : ((shadowOf pl hW hne).withVertices V).Generic)
(ov : … .Crossing → … .Strand) (hov : ∀ x, ov x ∈ x.val) (K : ℕ → Prop)`:
```lean
noncomputable abbrev mkDiagram : Diagram                       -- ⟨(shadowOf pl hW hne).withVertices V, hgen, ov, hov⟩
noncomputable def stStrand (u : Slot W) : ((shadowOf pl hW hne).withVertices V).Strand     -- identity map slot → strand
def strIdx (s : ((shadowOf pl hW hne).withVertices V).Strand) : Idx hW                      -- identity map strand → Idx
@[simp] theorem idxEquiv_stStrand (u : Slot W) : idxEquiv hW (stStrand pl hW hne V u) = u
@[simp] theorem stStrand_idxEquiv (s) : stStrand pl hW hne V (idxEquiv hW s) = s
theorem eq_stStrand_iff (s) (u : Slot W) : s = stStrand pl hW hne V u ↔ idxEquiv hW s = u
noncomputable abbrev σpair {k m : ℕ} (hk : k < W.length) (hℓ : letterAt W k = .σ m) : Finset (… .Strand)
theorem mem_σpair_iff … (s) : s ∈ σpair pl hW hne V hk hℓ ↔ idxEquiv hW s = σSlotA hW hk hℓ ∨ idxEquiv hW s = σSlotB hW hk hℓ
structure SlotDiagramData : Prop where
  cross : ∀ x : Finset (… .Strand), (… .withVertices V).IsCrossing x ↔
      ∃ (k m : ℕ) (hk : k < W.length) (hℓ : letterAt W k = .σ m), K k ∧ x = σpair pl hW hne V hk hℓ
  overStrand : ∀ (x : … .Crossing) (k m : ℕ) (hk) (hℓ), x.val = σpair pl hW hne V hk hℓ → ov x = stStrand pl hW hne V (σSlotA hW hk hℓ)
  sgn : ∀ (x : … .Crossing) (k m : ℕ) (hk) (hℓ), x.val = σpair pl hW hne V hk hℓ →
    ((mkDiagram pl hW hne V hgen ov hov).sign x : ℤ) = if bit W k m = bit W k (m + 1) then 1 else -1
noncomputable def diagramRecordIso [DecidablePred K] (data : SlotDiagramData pl hW hne V hgen ov hov K) :
    RecordIso (mkDiagram pl hW hne V hgen ov hov).record (slotRecord hW (colActive K) (colActive_activeSet hW K))
theorem realizeAt_data : SlotDiagramData pl hW hne (shadowOf pl hW hne).vertices (realizeAt pl hW hne).generic
      (realizeAt pl hW hne).overStrand (realizeAt pl hW hne).overStrand_mem (fun _ => True)
```
(`data` is a section variable under `include data` from `σcross` to `diagramRecordIso`, so it is an explicit
argument after `K`: `U2.diagramRecordIso pl hW hne V hgen ov hov K data`.)  Sub-lemmas usable on their own:
`toVisit`, `visitEquiv` (+ `_apply_val`, `_symm_apply`), `slot_other`, `overBit_eq`, `sign_eq`, `nextVisit_eq`,
`visitCoord_eq(_of)`, `compOf_eq_of`, `idxEquiv_add`, `nextPerm_pow_apply` (Appendix).

### 4.4 The exterior correspondence of two words agreeing outside a block (section `Exterior`; `variable (X P Y P' : Word)`, then `(hP : P ≠ []) (hE : SameEffect X P P') (hW : (X ++ P ++ Y).Closed) (hW' : (X ++ P' ++ Y).Closed)` with `include hP hE hW`)

`P' = []` is allowed everywhere (deletions with an empty factor).
```lean
def ExtPiece (u : Slot (X ++ P ++ Y)) : Prop                  -- ExtCol X P (colOf u); decidable
theorem extPiece_σtwin (hW) {u} (hu : IsσSlot u) (h : ExtPiece X P Y u) : ExtPiece X P Y (σtwin hW u)
theorem colOf_mk {V : Word} (k p : ℕ) (hs : IsSlot V (k, p)) :
    colOf (⟨(k, p), hs⟩ : Slot V) = if p = 0 then k else if bit V k p then k else k - 1
theorem shiftIdx_injOn (hP : P ≠ []) {k k'} (hk : ExtCol X P k) (hk' : ExtCol X P k') (h : shiftIdx X P P' k = shiftIdx X P P' k') : k = k'
def unshiftCol (k' : ℕ) : ℕ
theorem unshiftCol_spec (hP : P ≠ []) {k'} (h : ExtCol X P' k') : ExtCol X P (unshiftCol X P P' k') ∧ shiftIdx X P P' (unshiftCol X P P' k') = k'

noncomputable def φE : {u : Slot (X ++ P ++ Y) // ExtPiece X P Y u} ≃ {u' : Slot (X ++ P' ++ Y) // ExtPiece X P' Y u'}
    -- U2.φE X P Y P' hP hE hW
theorem φE_val (u) : (φE X P Y P' hP hE hW u).1.1 = extPair X P P' u.1.1
theorem φE_apply (u) : φE X P Y P' hP hE hW u = extF X P Y P' hP hE hW u
theorem extF_eq (u) : (extF X P Y P' hP hE hW u).1 = extSlot X P Y P' hP hE ⟨u.1, isExtSlot_of_extCol X P Y P' hP hE u.1 u.2⟩
theorem colOf_φE (u) : colOf (φE X P Y P' hP hE hW u).1 = shiftIdx X P P' (colOf u.1)
theorem shapeOf_φE (u) : shapeOf (φE X P Y P' hP hE hW u).1 = shapeOf u.1
theorem letterAt_colOf_φE (u) : letterAt (X ++ P' ++ Y) (colOf (φE … u).1) = letterAt (X ++ P ++ Y) (colOf u.1)
theorem bit_colOf_φE (u) (p : ℕ) : bit (X ++ P' ++ Y) (colOf (φE … u).1) p = bit (X ++ P ++ Y) (colOf u.1) p
theorem isσSlot_φE_iff (u) : IsσSlot (φE … u).1 ↔ IsσSlot u.1
theorem isDesc_φE (u) : isDesc (φE … u).1 = isDesc u.1
theorem σsgn_φE (u) : σsgn (φE … u).1 = σsgn u.1
theorem φE_σtwin (u) (hu : IsσSlot u.1) : (φE … ⟨σtwin hW u.1, extPiece_σtwin X P Y hW hu u.2⟩).1 = σtwin hW' (φE … u).1
theorem colActive_φE_iff (u) : colActive (ExtCol X P') (φE … u).1 ↔ colActive (ExtCol X P) u.1
theorem length_W : (X ++ P ++ Y).length = X.length + P.length + Y.length ;  theorem length_W' : (X ++ P' ++ Y).length = …

structure Passage : Prop where                                -- U2.Passage X P Y P' hW hW'  (the hypothesis U3/U6 verify)
  pass : ∀ b : Slot (X ++ P ++ Y), IsExtSlot X P b.1 → ¬ ExtCol X P (colOf b) →
    ∃ (m : ℕ) (c : Slot (X ++ P ++ Y)), (next hW)^[m] b = c ∧ ExtCol X P (colOf c) ∧
      (∀ i < m, ¬ ExtCol X P (colOf ((next hW)^[i] b))) ∧
      ∃ (m' : ℕ) (b' : Slot (X ++ P' ++ Y)), b'.1 = extPair X P P' b.1 ∧
        ((next hW')^[m'] b').1 = extPair X P P' c.1 ∧
        ∀ i < m', ¬ ExtCol X P' (colOf ((next hW')^[i] b'))
theorem entry_iff (b : Slot (X ++ P ++ Y)) :                  -- the entry slots, concretely
    IsExtSlot X P b.1 ∧ ¬ ExtCol X P (colOf b) ↔
      (∃ p, b.1 = (X.length, p) ∧ p ≠ 0 ∧ bit (X ++ P ++ Y) X.length p = true) ∨
      (∃ p, b.1 = (X.length + P.length, p) ∧ p ≠ 0 ∧ bit (X ++ P ++ Y) (X.length + P.length) p = false)
theorem conj_of_passage (hpass : Passage X P Y P' hW hW') (u) :
    firstReturn (nextPerm hW') (ExtPiece X P' Y) (φE X P Y P' hP hE hW u) = φE X P Y P' hP hE hW (firstReturn (nextPerm hW) (ExtPiece X P Y) u)

noncomputable def extRecordIso (hpass : Passage X P Y P' hW hW')
    (hexit : ∀ u : Slot (X ++ P ++ Y), ∃ n : ℕ, ExtPiece X P Y ((next hW)^[n] u))
    (hexit' : ∀ u' : Slot (X ++ P' ++ Y), ∃ n : ℕ, ExtPiece X P' Y ((next hW')^[n] u')) :
    RecordIso (slotRecord hW (colActive (ExtCol X P)) (colActive_activeSet hW _))
      (slotRecord hW' (colActive (ExtCol X P')) (colActive_activeSet hW' _))
```
(section `AddFree`; `variable (X P Y P' : Word) (hP : P ≠ []) (hE : SameEffect X P P') (hW …) (hW' …)`, `include hP hE`)
```lean
noncomputable def addFreeCongr {ρ ρ' : Record} (ι : RecordIso ρ ρ') : RecordIso ρ.addFree ρ'.addFree
noncomputable def extRecordIsoAddFree (hpass : Passage X P Y P' hW hW')
    (hexit' : ∀ u' : Slot (X ++ P' ++ Y), ∃ n : ℕ, ExtPiece X P' Y ((next hW')^[n] u'))
    (c₀ : Orbit hW)
    (hc₀ : ∀ u : Slot (X ++ P ++ Y), (¬ ∃ n : ℕ, ExtPiece X P Y ((next hW)^[n] u)) ↔ orbitOf hW u = c₀) :
    RecordIso (slotRecord hW (colActive (ExtCol X P)) (colActive_activeSet hW _))
      (slotRecord hW' (colActive (ExtCol X P')) (colActive_activeSet hW' _)).addFree
```

### 4.5 The composed statements — what U3 / U6 `exact` (sections `Composed`, `AddFree`; `variable (X P Y P' : Word) (hP : P ≠ []) (hE : SameEffect X P P') (hW : (X ++ P ++ Y).Closed) (hW' : (X ++ P' ++ Y).Closed)`, `include hP hE`)

**U3 `zigzag_recordIso`** (and any deletion with `P' = []`, no `σ` in either factor):
```lean
theorem realize_recordIso_of_ext (hne : X ++ P ++ Y ≠ []) (hne' : X ++ P' ++ Y ≠ [])
    (hpass : Passage X P Y P' hW hW')
    (hexit : ∀ u : Slot (X ++ P ++ Y), ∃ n : ℕ, ExtPiece X P Y ((next hW)^[n] u))
    (hexit' : ∀ u' : Slot (X ++ P' ++ Y), ∃ n : ℕ, ExtPiece X P' Y ((next hW')^[n] u'))
    (hnoσ : ∀ k, X.length ≤ k → k < X.length + P.length → (letterAt (X ++ P ++ Y) k).isCrossing = false)
    (hnoσ' : ∀ k, X.length ≤ k → k < X.length + P'.length → (letterAt (X ++ P' ++ Y) k).isCrossing = false)
    (W W' : OWord) (hWeq : W.letters = X ++ P ++ Y) (hW'eq : W'.letters = X ++ P' ++ Y) :
    Nonempty (RecordIso (realize W).diagram.record (realize W').diagram.record)
-- call: U2.realize_recordIso_of_ext X P Y P' hP hE hW hW' hne hne' hpass hexit hexit' hnoσ hnoσ' W W' hWeq hW'eq
```
**U3 `circle_recordIso_addFree`** (`P = [l m d, r m]`-type factor, `P' = []`, the circle is the one orbit `c₀` missing the exterior):
```lean
theorem realize_recordIso_addFree_of_ext (hne : X ++ P ++ Y ≠ []) (hne' : X ++ P' ++ Y ≠ [])
    (hpass : Passage X P Y P' hW hW')
    (hexit' : ∀ u' : Slot (X ++ P' ++ Y), ∃ n : ℕ, ExtPiece X P' Y ((next hW')^[n] u'))
    (c₀ : Orbit hW)
    (hc₀ : ∀ u : Slot (X ++ P ++ Y), (¬ ∃ n : ℕ, ExtPiece X P Y ((next hW)^[n] u)) ↔ orbitOf hW u = c₀)
    (hnoσ : ∀ k, X.length ≤ k → k < X.length + P.length → (letterAt (X ++ P ++ Y) k).isCrossing = false)
    (hnoσ' : ∀ k, X.length ≤ k → k < X.length + P'.length → (letterAt (X ++ P' ++ Y) k).isCrossing = false)
    (W W' : OWord) (hWeq : W.letters = X ++ P ++ Y) (hW'eq : W'.letters = X ++ P' ++ Y) :
    Nonempty (RecordIso (realize W).diagram.record (realize W').diagram.record.addFree)
```
**U3 `comm_recordIso` and the switch half of `skein_site`** (same length, a bijection of ALL slots; section
`Consequences`; `variable {W W' : Word} (hW : W.Closed) (hW' : W'.Closed) (S : Slot W → Prop) (S' : Slot W' → Prop)
[DecidablePred S] [DecidablePred S'] (hS : ActiveSet hW S) (hS' : ActiveSet hW' S')`):
```lean
noncomputable def orbitEquivOfSlotEquiv (ψ : Slot W ≃ Slot W') (hnext : ∀ u, ψ (next hW u) = next hW' (ψ u)) : Orbit hW ≃ Orbit hW'
noncomputable def slotRecordIsoOfSlotEquiv (ψ : Slot W ≃ Slot W') (hnext : ∀ u, ψ (next hW u) = next hW' (ψ u))
    (hact : ∀ u, S' (ψ u) ↔ S u) (htwin : ∀ u, S u → ψ (σtwin hW u) = σtwin hW' (ψ u))
    (hdesc : ∀ u, S u → isDesc (ψ u) = isDesc u) (hsgn : ∀ u, S u → σsgn (ψ u) = σsgn u) :
    RecordIso (slotRecord hW S hS) (slotRecord hW' S' hS')
-- call: U2.slotRecordIsoOfSlotEquiv hW hW' S S' hS hS' ψ hnext hact htwin hdesc hsgn ; compose with U2.realizeRecordIso on both sides
```
**U6 `typeII_move`, `typeI_move`, `crossedCusp_move`** (vertex-moved diagram; U4 supplies `V`, `hgen`, `data`):
```lean
noncomputable def vertexMovedRecordIso' (pl : Placement) (hne : X ++ P ++ Y ≠ [])
    (V : (shadowOf pl hW hne).Vertices) (hgen : ((shadowOf pl hW hne).withVertices V).Generic)
    (ov : ((shadowOf pl hW hne).withVertices V).Crossing → ((shadowOf pl hW hne).withVertices V).Strand)
    (hov : ∀ x, ov x ∈ x.val) (data : SlotDiagramData pl hW hne V hgen ov hov (ExtCol X P))
    (hpass : Passage X P Y P' hW hW')
    (hexit : ∀ u : Slot (X ++ P ++ Y), ∃ n : ℕ, ExtPiece X P Y ((next hW)^[n] u))
    (hexit' : ∀ u' : Slot (X ++ P' ++ Y), ∃ n : ℕ, ExtPiece X P' Y ((next hW')^[n] u'))
    (hnoσ : ∀ k, X.length ≤ k → k < X.length + P'.length → (letterAt (X ++ P' ++ Y) k).isCrossing = false)
    (W' : OWord) (hW'eq : W'.letters = X ++ P' ++ Y) (hne' : X ++ P' ++ Y ≠ []) :
    RecordIso (mkDiagram pl hW hne V hgen ov hov).record (realize W').diagram.record
noncomputable def vertexMovedRecordIso (pl : Placement) (hne) (hne') (V) (hgen) (ov) (hov) (data) (hpass) (hexit) (hexit') (hnoσ) (pl' : Placement) :
    RecordIso (mkDiagram pl hW hne V hgen ov hov).record (realizeAt pl' hW' hne').diagram.record
noncomputable def realizeAtRecordIsoOfExt (hne) (hne') (hpass) (hexit) (hexit') (hnoσ) (hnoσ') (pl pl' : Placement) :
    RecordIso (realizeAt pl hW hne).diagram.record (realizeAt pl' hW' hne').diagram.record
```

### 4.6 Generic permutation tools (sections `FirstReturnExtra`, `ConjExtra`; `variable {α β : Type*} [Fintype α] [Fintype β] (f : Perm α) (g : Perm β)`, later `(E : α → Prop) (E' : β → Prop) [DecidablePred E] [DecidablePred E'] (φ : {a // E a} ≃ {b // E' b})`)

```lean
theorem firstReturn_factor (E : α → Prop) [DecidablePred E] (p : α → Prop) [DecidablePred p] (hpE : ∀ a, p a → E a) (a : {a // p a}) :
    (firstReturn f p a).1 = (firstReturn (firstReturn f E) (fun b => p b.1) ⟨⟨a.1, hpE _ a.2⟩, a.2⟩).1.1
theorem firstReturn_conj (p : α → Prop) (q : β → Prop) [DecidablePred p] [DecidablePred q] (φ : α ≃ β)
    (hφ : ∀ a, φ (f a) = g (φ a)) (hpq : ∀ a, q (φ a) ↔ p a) (a : {a // p a}) : (firstReturn g q ⟨φ a.1, (hpq _).2 a.2⟩).1 = φ (firstReturn f p a).1
theorem firstReturn_eq_of_path (E : α → Prop) [DecidablePred E] (a : {a // E a}) {m : ℕ} (hm : 0 < m)
    (hE : E ((f ^ m) a.1)) (hmin : ∀ i, 0 < i → i < m → ¬ E ((f ^ i) a.1)) : (firstReturn f E a).1 = (f ^ m) a.1
theorem returnTime_le_of_pow_eq (E) [DecidablePred E] (a : α) (ha : E a) {k : ℕ} (hk : 0 < k) (h : (f ^ k) a = a) : returnTime f E a ha ≤ k
theorem firstReturn_pow_of_pow_strong (E) [DecidablePred E] (n : ℕ) : ∀ (m : {m // E m}), E ((f ^ n) m.1) →
      ∃ i : ℕ, ((firstReturn f E ^ i) m).1 = (f ^ n) m.1 ∧ (0 < n → 0 < i) ∧ ∀ j, 0 < j → j < i → ∃ t, 0 < t ∧ t < n ∧ ((firstReturn f E ^ j) m).1 = (f ^ t) m.1
theorem pow_conj {φ : α ≃ β} (hφ : ∀ a, φ (f a) = g (φ a)) (n : ℕ) (x : α) : φ ((f ^ n) x) = (g ^ n) (φ x)
theorem sameCycle_iff_of_conj {φ : α ≃ β} (hφ : ∀ a, φ (f a) = g (φ a)) (x y : α) : g.SameCycle (φ x) (φ y) ↔ f.SameCycle x y
theorem sameCycle_φ_iff (conj : ∀ a, firstReturn g E' (φ a) = φ (firstReturn f E a)) (a b : {a // E a}) : g.SameCycle (φ a).1 (φ b).1 ↔ f.SameCycle a.1 b.1
theorem firstReturn_conj_of_factor (conj : …) (p : α → Prop) (p' : β → Prop) [DecidablePred p] [DecidablePred p']
    (hpE : ∀ a, p a → E a) (hp'E' : ∀ b, p' b → E' b) (hpq : ∀ a : {a // E a}, p' (φ a).1 ↔ p a.1) (a : {a // p a}) :
    (firstReturn g p' ⟨(φ ⟨a.1, hpE _ a.2⟩).1, (hpq _).2 a.2⟩).1 = (φ ⟨(firstReturn f p a).1, hpE _ (firstReturn f p a).2⟩).1
noncomputable def cycleEquiv (conj : …) (hE : ∀ a : α, ∃ n : ℕ, E ((f ^ n) a)) (hE' : ∀ b : β, ∃ n : ℕ, E' ((g ^ n) b)) :
    Quotient (Perm.SameCycle.setoid f) ≃ Quotient (Perm.SameCycle.setoid g)          -- + cycleEquiv_mk
noncomputable def cycleEquivOption (conj : …) (hE' : …) (c₀ : Quotient (Perm.SameCycle.setoid f))
    (hc₀ : ∀ a : α, (¬ ∃ n : ℕ, E ((f ^ n) a)) ↔ Quotient.mk (Perm.SameCycle.setoid f) a = c₀) :
    Quotient (Perm.SameCycle.setoid f) ≃ Option (Quotient (Perm.SameCycle.setoid g))  -- + cycleEquivOption_mk
theorem visit_ext {Γ : Shadow} {v w : Γ.Visit} (h1 : v.1 = w.1) (h2 : v.2.val = w.2.val) : v = w
theorem signType_ext_int {a b : SignType} (h : ((a : SignType) : ℤ) = b) : a = b
theorem cycBetween_nat_add {A B C : ℕ} (hAB : A ≠ B) (hBC : B ≠ C) (hAC : A ≠ C) {α β γ : ℝ} (0 ≤ α < 1) (0 ≤ β < 1) (0 ≤ γ < 1) :
    cycBetween (A + α) (B + β) (C + γ) ↔ ((A < B ∧ B < C) ∨ (B < C ∧ C < A) ∨ (C < A ∧ A < B))
```

### 4.7 Gotchas (from U_U2_REPORT.md §5, still valid in the merged file)

1. `((shadowOf pl hW hne).withVertices V).Strand` and `Idx hW` are definitionally but not syntactically equal; go
   through `U2.stStrand` / `U2.strIdx` and finish with `exact` of a `congrArg` (`visitCoord_eq_of`, `compOf_eq_of`).
2. Section variables are included only when mentioned, except under `include`: in `Exterior` the lemmas take
   `X P Y P' hP hE hW` explicitly (e.g. `U2.φE X P Y P' hP hE hW`); in `Composed`/`AddFree` `hP hE` are included,
   `hW hW'` only when mentioned (they always are); `length_W' X Y P'`.
3. `Passage` uses the total `extPair` (no `P' ≠ []`); `entry_iff` needs `hP` and closedness.
4. All statements are for nonempty words (`realize_eq_realizeAt`); no row hypothesis produces `[]`.
5. `local notation "𝔇" => mkDiagram pl hW hne V hgen ov hov` is used inside section `DiagramIso` only
   (`visitCoord_eq_of`, `compOf_eq_of`); it does not leak.

### 4.8 Also available from U1 (word layer, `SM.FrontRows`, section `U1Infra`) — useful for `skein_site`'s sign clause and `skein_unique`

```lean
theorem u1_downCountFrom_nil (c : Cuts) : Word.downCountFrom [] c = 0
theorem u1_writheFrom_nil (c : Cuts) : Word.writheFrom [] c = 0
theorem u1_downCountFrom_cons {a : Letter} {V : Word} {c c' : Cuts} (h : a.step c = some c') : Word.downCountFrom (a :: V) c = a.downBit c + V.downCountFrom c'
theorem u1_writheFrom_cons {a : Letter} {V : Word} {c c' : Cuts} (h : a.step c = some c') : Word.writheFrom (a :: V) c = a.signBit c + V.writheFrom c'
theorem u1_downCountFrom_append {V W : Word} {c c' : Cuts} (h : Word.run V c = some c') : (V ++ W).downCountFrom c = V.downCountFrom c + W.downCountFrom c'
theorem u1_writheFrom_append {V W : Word} {c c' : Cuts} (h : Word.run V c = some c') : (V ++ W).writheFrom c = V.writheFrom c + W.writheFrom c'
theorem u1_run_append_some {X P : Word} {c₀ c₁ : Cuts} (hX : Word.run X [] = some c₀) (hP : Word.run P c₀ = some c₁) : Word.run (X ++ P) [] = some c₁
theorem u1_downCountFrom_append₃ (X P Y : Word) {c₀ c₁ : Cuts} (hX : Word.run X [] = some c₀) (hP : Word.run P c₀ = some c₁) :
    (X ++ P ++ Y).downCountFrom [] = X.downCountFrom [] + P.downCountFrom c₀ + Y.downCountFrom c₁
theorem u1_writheFrom_append₃ (X P Y : Word) {c₀ c₁ : Cuts} (hX : Word.run X [] = some c₀) (hP : Word.run P c₀ = some c₁) :
    (X ++ P ++ Y).writheFrom [] = X.writheFrom [] + P.writheFrom c₀ + Y.writheFrom c₁
theorem u1_downBit_window {ℓ : Letter} {n : ℕ} {A A' w R R' : Cuts} (hA : A.length = ℓ.idx - 1) (hA' : A'.length = n - 1) (hw : w.length = ℓ.arity) :
    (ℓ.reindex n).downBit (A' ++ (w ++ R')) = ℓ.downBit (A ++ (w ++ R))
theorem u1_signBit_window … : (ℓ.reindex n).signBit (A' ++ (w ++ R')) = ℓ.signBit (A ++ (w ++ R))
theorem u1_downBit_window' / u1_signBit_window'   -- the n = ℓ.idx case
theorem u1_typeI_target_ne_nil {W X Y : Word} {m : ℕ} {d : Bool}
    (hpat : (2 ≤ m ∧ W = X ++ [.l m d, .σ (m - 1), .r m] ++ Y) ∨ (1 ≤ m ∧ W = X ++ [.l m d, .σ (m + 1), .r m] ++ Y)) (hW : W.Closed) : X ++ Y ≠ []
```
Also the per-pattern local values `u1_*_local` (e.g. `u1_skein_local`: the factor's `D`, `w` on the symbolic cut for
`A`, `A'`, `C_top`, `C_bottom`) — see U_U1_REPORT.md §2 and lines 245-936 of the merged file.

## 5. Appendix — every declaration of `namespace SM.FrontRows.U2` in Skeleton_W1.lean (file order, with section context)

Generated from the merged file by `/workspace/scratch/lean_merge1/extract_u2.py`.  `omit … in` prefixes are shown
where a declaration drops a section variable.  Proof bodies and `where` fields of `def`s are omitted; `structure`
fields are shown.

#### section `FirstReturnExtra`

Section variables (in scope, included only when mentioned unless `include`d):

```lean
variable {α β : Type*} [Fintype α] [Fintype β] (f : Perm α) (g : Perm β)
```

**`U2.firstReturn_pow_of_pow_strong`** (L1188, theorem)

```lean
theorem firstReturn_pow_of_pow_strong (E : α → Prop) [DecidablePred E] (n : ℕ) :
    ∀ (m : {m // E m}), E ((f ^ n) m.1) →
      ∃ i : ℕ, ((firstReturn f E ^ i) m).1 = (f ^ n) m.1 ∧ (0 < n → 0 < i) ∧
        ∀ j, 0 < j → j < i → ∃ t, 0 < t ∧ t < n ∧ ((firstReturn f E ^ j) m).1 = (f ^ t) m.1 :=
```

**`U2.firstReturn_factor`** (L1220, theorem)

```lean
theorem firstReturn_factor (E : α → Prop) [DecidablePred E] (p : α → Prop) [DecidablePred p]
    (hpE : ∀ a, p a → E a) (a : {a // p a}) :
    (firstReturn f p a).1 =
      (firstReturn (firstReturn f E) (fun b => p b.1) ⟨⟨a.1, hpE _ a.2⟩, a.2⟩).1.1 :=
```

**`U2.firstReturn_conj`** (L1245, theorem)

```lean
theorem firstReturn_conj (p : α → Prop) (q : β → Prop) [DecidablePred p] [DecidablePred q]
    (φ : α ≃ β) (hφ : ∀ a, φ (f a) = g (φ a)) (hpq : ∀ a, q (φ a) ↔ p a) (a : {a // p a}) :
    (firstReturn g q ⟨φ a.1, (hpq _).2 a.2⟩).1 = φ (firstReturn f p a).1 :=
```

**`U2.firstReturn_eq_of_path`** (L1264, theorem)

```lean
theorem firstReturn_eq_of_path (E : α → Prop) [DecidablePred E] (a : {a // E a}) {m : ℕ} (hm : 0 < m)
    (hE : E ((f ^ m) a.1)) (hmin : ∀ i, 0 < i → i < m → ¬ E ((f ^ i) a.1)) :
    (firstReturn f E a).1 = (f ^ m) a.1 :=
```

**`U2.returnTime_le_of_pow_eq`** (L1272, theorem)

```lean
theorem returnTime_le_of_pow_eq (E : α → Prop) [DecidablePred E] (a : α) (ha : E a) {k : ℕ} (hk : 0 < k)
    (h : (f ^ k) a = a) : returnTime f E a ha ≤ k :=
```

#### section `ConjExtra`

Section variables (in scope, included only when mentioned unless `include`d):

```lean
variable {α β : Type*} [Fintype α] [Fintype β] (f : Perm α) (g : Perm β)
```

**`U2.pow_conj`** (L1285, theorem; `omit [Fintype α] [Fintype β] in`)

```lean
theorem pow_conj {φ : α ≃ β} (hφ : ∀ a, φ (f a) = g (φ a)) (n : ℕ) (x : α) :
    φ ((f ^ n) x) = (g ^ n) (φ x) :=
```

**`U2.sameCycle_of_conj`** (L1292, theorem; `omit [Fintype β] in`)

```lean
theorem sameCycle_of_conj {φ : α ≃ β} (hφ : ∀ a, φ (f a) = g (φ a)) {x y : α} (h : f.SameCycle x y) :
    g.SameCycle (φ x) (φ y) :=
```

**`U2.conj_symm`** (L1298, theorem; `omit [Fintype α] [Fintype β] in`)

```lean
theorem conj_symm {φ : α ≃ β} (hφ : ∀ a, φ (f a) = g (φ a)) (b : β) : φ.symm (g b) = f (φ.symm b) :=
```

**`U2.sameCycle_iff_of_conj`** (L1302, theorem)

```lean
theorem sameCycle_iff_of_conj {φ : α ≃ β} (hφ : ∀ a, φ (f a) = g (φ a)) (x y : α) :
    g.SameCycle (φ x) (φ y) ↔ f.SameCycle x y :=
```

**`U2.sameCycle_φ_iff`** (L1311, theorem)

```lean
theorem sameCycle_φ_iff (conj : ∀ a, firstReturn g E' (φ a) = φ (firstReturn f E a)) (a b : {a // E a}) :
    g.SameCycle (φ a).1 (φ b).1 ↔ f.SameCycle a.1 b.1 :=
```

**`U2.conj_symm'`** (L1316, theorem)

```lean
theorem conj_symm' (conj : ∀ a, firstReturn g E' (φ a) = φ (firstReturn f E a)) (b : {b // E' b}) :
    firstReturn f E (φ.symm b) = φ.symm (firstReturn g E' b) :=
```

**`U2.firstReturn_conj_of_factor`** (L1322, theorem)

```lean
theorem firstReturn_conj_of_factor (conj : ∀ a, firstReturn g E' (φ a) = φ (firstReturn f E a))
    (p : α → Prop) (p' : β → Prop) [DecidablePred p] [DecidablePred p']
    (hpE : ∀ a, p a → E a) (hp'E' : ∀ b, p' b → E' b) (hpq : ∀ a : {a // E a}, p' (φ a).1 ↔ p a.1)
    (a : {a // p a}) :
    (firstReturn g p' ⟨(φ ⟨a.1, hpE _ a.2⟩).1, (hpq _).2 a.2⟩).1 =
      (φ ⟨(firstReturn f p a).1, hpE _ (firstReturn f p a).2⟩).1 :=
```

**`U2.sameCycle_pow`** (L1337, theorem; `omit [Fintype α] [Fintype β] in`)

```lean
theorem sameCycle_pow (n : ℕ) (a : α) : f.SameCycle a ((f ^ n) a) :=
```

**`U2.repE`** (L1341, def; `omit [Fintype α] [Fintype β] [DecidablePred E] in`)

```lean
noncomputable def repE (hE : ∀ a : α, ∃ n : ℕ, E ((f ^ n) a)) (a : α) : {a // E a} :=
```

**`U2.repE_sameCycle`** (L1345, theorem; `omit [Fintype α] [Fintype β] [DecidablePred E] in`)

```lean
theorem repE_sameCycle (hE : ∀ a : α, ∃ n : ℕ, E ((f ^ n) a)) (a : α) : f.SameCycle a (repE f E hE a).1 :=
```

**`U2.cycleMap`** (L1349, def)

```lean
noncomputable def cycleMap (conj : ∀ a, firstReturn g E' (φ a) = φ (firstReturn f E a))
    (hE : ∀ a : α, ∃ n : ℕ, E ((f ^ n) a)) :
    Quotient (Perm.SameCycle.setoid f) → Quotient (Perm.SameCycle.setoid g) :=
```

**`U2.cycleMap_mk`** (L1359, theorem)

```lean
theorem cycleMap_mk (conj : ∀ a, firstReturn g E' (φ a) = φ (firstReturn f E a))
    (hE : ∀ a : α, ∃ n : ℕ, E ((f ^ n) a)) (a : {a // E a}) :
    cycleMap f g E E' φ conj hE (Quotient.mk (Perm.SameCycle.setoid f) a.1) =
      Quotient.mk (Perm.SameCycle.setoid g) (φ a).1 :=
```

**`U2.cycleMap_mk'`** (L1366, theorem)

```lean
theorem cycleMap_mk' (conj : ∀ a, firstReturn g E' (φ a) = φ (firstReturn f E a))
    (hE : ∀ a : α, ∃ n : ℕ, E ((f ^ n) a)) (a : α) :
    cycleMap f g E E' φ conj hE (Quotient.mk (Perm.SameCycle.setoid f) a) =
      Quotient.mk (Perm.SameCycle.setoid g) (φ (repE f E hE a)).1 :=
```

**`U2.cycleEquiv`** (L1372, def)

```lean
noncomputable def cycleEquiv (conj : ∀ a, firstReturn g E' (φ a) = φ (firstReturn f E a))
    (hE : ∀ a : α, ∃ n : ℕ, E ((f ^ n) a)) (hE' : ∀ b : β, ∃ n : ℕ, E' ((g ^ n) b)) :
    Quotient (Perm.SameCycle.setoid f) ≃ Quotient (Perm.SameCycle.setoid g) where
```

**`U2.cycleEquiv_mk`** (L1392, theorem)

```lean
theorem cycleEquiv_mk (conj : ∀ a, firstReturn g E' (φ a) = φ (firstReturn f E a))
    (hE : ∀ a : α, ∃ n : ℕ, E ((f ^ n) a)) (hE' : ∀ b : β, ∃ n : ℕ, E' ((g ^ n) b)) (a : {a // E a}) :
    cycleEquiv f g E E' φ conj hE hE' (Quotient.mk (Perm.SameCycle.setoid f) a.1) =
      Quotient.mk (Perm.SameCycle.setoid g) (φ a).1 :=
```

**`U2.cycleEquivOption`** (L1401, def)

```lean
noncomputable def cycleEquivOption (conj : ∀ a, firstReturn g E' (φ a) = φ (firstReturn f E a))
    (hE' : ∀ b : β, ∃ n : ℕ, E' ((g ^ n) b)) (c₀ : Quotient (Perm.SameCycle.setoid f))
    (hc₀ : ∀ a : α, (¬ ∃ n : ℕ, E ((f ^ n) a)) ↔ Quotient.mk (Perm.SameCycle.setoid f) a = c₀) :
    Quotient (Perm.SameCycle.setoid f) ≃ Option (Quotient (Perm.SameCycle.setoid g)) where
```

**`U2.cycleEquivOption_mk`** (L1464, theorem)

```lean
theorem cycleEquivOption_mk (conj : ∀ a, firstReturn g E' (φ a) = φ (firstReturn f E a))
    (hE' : ∀ b : β, ∃ n : ℕ, E' ((g ^ n) b)) (c₀ : Quotient (Perm.SameCycle.setoid f))
    (hc₀ : ∀ a : α, (¬ ∃ n : ℕ, E ((f ^ n) a)) ↔ Quotient.mk (Perm.SameCycle.setoid f) a = c₀)
    (a : {a // E a}) :
    cycleEquivOption f g E E' φ conj hE' c₀ hc₀ (Quotient.mk (Perm.SameCycle.setoid f) a.1) =
      some (Quotient.mk (Perm.SameCycle.setoid g) (φ a).1) :=
```

#### section `SigmaSlots`

Section variables (in scope, included only when mentioned unless `include`d):

```lean
variable {W : Word}
```

**`U2.letterAt_σ_of_isCrossing`** (L1487, theorem)

```lean
theorem letterAt_σ_of_isCrossing {k : ℕ} (h : (letterAt W k).isCrossing = true) :
    letterAt W k = .σ (letterAt W k).idx :=
```

**`U2.isDesc`** (L1496, def)

```lean
def isDesc (u : Slot W) : Bool :=
```

**`U2.IsσSlot`** (L1503, def)

```lean
def IsσSlot (u : Slot W) : Prop :=
```

**`U2.(anonymous)`** (L1508, instance)

```lean
instance : DecidablePred (IsσSlot (W := W)) :=
```

**`U2.σsgnCol`** (L1512, def)

```lean
def σsgnCol (W : Word) (k : ℕ) : SignType :=
```

**`U2.σsgn`** (L1516, def)

```lean
def σsgn (u : Slot W) : SignType :=
```

**`U2.σsgnCol_ne_zero`** (L1518, theorem)

```lean
theorem σsgnCol_ne_zero (k : ℕ) : σsgnCol W k ≠ 0 :=
```

**`U2.σsgn_ne_zero`** (L1521, theorem)

```lean
theorem σsgn_ne_zero (u : Slot W) : σsgn u ≠ 0 :=
```

**`U2.coe_σsgnCol`** (L1523, theorem)

```lean
theorem coe_σsgnCol (k : ℕ) :
    ((σsgnCol W k : SignType) : ℤ) =
      if bit W k (letterAt W k).idx = bit W k ((letterAt W k).idx + 1) then 1 else -1 :=
```

**`U2.isσSlot_σSlotA`** (L1531, theorem)

```lean
theorem isσSlot_σSlotA {k m : ℕ} (hk : k < W.length) (hℓ : letterAt W k = .σ m) :
    IsσSlot (σSlotA hW hk hℓ) :=
```

**`U2.isσSlot_σSlotB`** (L1538, theorem)

```lean
theorem isσSlot_σSlotB {k m : ℕ} (hk : k < W.length) (hℓ : letterAt W k = .σ m) :
    IsσSlot (σSlotB hW hk hℓ) :=
```

**`U2.isDesc_σSlotA`** (L1545, theorem)

```lean
theorem isDesc_σSlotA {k m : ℕ} (hk : k < W.length) (hℓ : letterAt W k = .σ m) :
    isDesc (σSlotA hW hk hℓ) = true :=
```

**`U2.isDesc_σSlotB`** (L1549, theorem)

```lean
theorem isDesc_σSlotB {k m : ℕ} (hk : k < W.length) (hℓ : letterAt W k = .σ m) :
    isDesc (σSlotB hW hk hℓ) = false :=
```

**`U2.colOf_lt`** (L1554, theorem)

```lean
theorem colOf_lt (u : Slot W) : colOf u < W.length :=
```

**`U2.eq_σSlotA_or_σSlotB`** (L1557, theorem)

```lean
theorem eq_σSlotA_or_σSlotB {u : Slot W} (hu : IsσSlot u) :
    u = σSlotA hW (colOf_lt hW u) (letterAt_σ_of_isCrossing hu.1) ∨
    u = σSlotB hW (colOf_lt hW u) (letterAt_σ_of_isCrossing hu.1) :=
```

**`U2.isσSlot_iff`** (L1566, theorem)

```lean
theorem isσSlot_iff (u : Slot W) :
    IsσSlot u ↔ ∃ (k m : ℕ) (hk : k < W.length) (hℓ : letterAt W k = .σ m),
      u = σSlotA hW hk hℓ ∨ u = σSlotB hW hk hℓ :=
```

**`U2.σslot_ext`** (L1577, theorem)

```lean
theorem σslot_ext {u v : Slot W} (hu : IsσSlot u) (hv : IsσSlot v) (hc : colOf u = colOf v)
    (hd : isDesc u = isDesc v) : u = v :=
```

**`U2.isDesc_eq_true_iff`** (L1586, theorem; `omit hW in`)

```lean
theorem isDesc_eq_true_iff {u : Slot W} (hu : IsσSlot u) :
    isDesc u = true ↔ shapeOf u = .pass (letterAt W (colOf u)).idx ((letterAt W (colOf u)).idx + 1) :=
```

**`U2.σtwin`** (L1592, def)

```lean
noncomputable def σtwin (u : Slot W) : Slot W :=
```

**`U2.σtwin_spec`** (L1598, theorem)

```lean
theorem σtwin_spec {u : Slot W} (hu : IsσSlot u) :
    colOf (σtwin hW u) = colOf u ∧ IsσSlot (σtwin hW u) ∧ isDesc (σtwin hW u) = !isDesc u :=
```

**`U2.colOf_σtwin`** (L1608, theorem)

```lean
theorem colOf_σtwin {u : Slot W} (hu : IsσSlot u) : colOf (σtwin hW u) = colOf u :=
```

**`U2.isσSlot_σtwin`** (L1610, theorem)

```lean
theorem isσSlot_σtwin {u : Slot W} (hu : IsσSlot u) : IsσSlot (σtwin hW u) :=
```

**`U2.isDesc_σtwin`** (L1612, theorem)

```lean
theorem isDesc_σtwin {u : Slot W} (hu : IsσSlot u) : isDesc (σtwin hW u) = !isDesc u :=
```

**`U2.σtwin_σtwin`** (L1615, theorem)

```lean
theorem σtwin_σtwin {u : Slot W} (hu : IsσSlot u) : σtwin hW (σtwin hW u) = u :=
```

**`U2.σtwin_ne`** (L1621, theorem)

```lean
theorem σtwin_ne {u : Slot W} (hu : IsσSlot u) : σtwin hW u ≠ u :=
```

**`U2.σsgn_σtwin`** (L1627, theorem)

```lean
theorem σsgn_σtwin {u : Slot W} (hu : IsσSlot u) : σsgn (σtwin hW u) = σsgn u :=
```

**`U2.σtwin_σSlotA`** (L1630, theorem)

```lean
theorem σtwin_σSlotA {k m : ℕ} (hk : k < W.length) (hℓ : letterAt W k = .σ m) :
    σtwin hW (σSlotA hW hk hℓ) = σSlotB hW hk hℓ :=
```

**`U2.σtwin_σSlotB`** (L1637, theorem)

```lean
theorem σtwin_σSlotB {k m : ℕ} (hk : k < W.length) (hℓ : letterAt W k = .σ m) :
    σtwin hW (σSlotB hW hk hℓ) = σSlotA hW hk hℓ :=
```

**`U2.coe_σsgn_eq_signBit`** (L1642, theorem)

```lean
theorem coe_σsgn_eq_signBit {u : Slot W} (hu : IsσSlot u) :
    ((σsgn u : SignType) : ℤ) = (letterAt W (colOf u)).signBit (cut W (colOf u)) :=
```

**`U2.coe_σsgn_σSlotA`** (L1651, theorem)

```lean
theorem coe_σsgn_σSlotA (pl : Placement) (hne : W ≠ []) {k m : ℕ} (hk : k < W.length) (hℓ : letterAt W k = .σ m) :
    ((σsgn (σSlotA hW hk hℓ) : SignType) : ℤ) =
      ((realizeAt pl hW hne).diagram.sign (crossingOf pl hW hne hk hℓ) : ℤ) :=
```

#### section `SlotRecord`

Section variables (in scope, included only when mentioned unless `include`d):

```lean
variable {W : Word} (hW : W.Closed)
```

**`U2.slotComp`** (L1665, def)

```lean
noncomputable def slotComp (u : Slot W) : Fin (numComp hW) :=
```

**`U2.slotComp_eq_iff`** (L1667, theorem)

```lean
theorem slotComp_eq_iff (u v : Slot W) :
    slotComp hW u = slotComp hW v ↔ (nextPerm hW).SameCycle u v :=
```

**`U2.slotComp_idxEquiv`** (L1673, theorem)

```lean
theorem slotComp_idxEquiv (s : Idx hW) : slotComp hW (idxEquiv hW s) = s.1 :=
```

**`U2.slotComp_eq_equivFin`** (L1678, theorem)

```lean
theorem slotComp_eq_equivFin (u : Slot W) :
    slotComp hW u = Fintype.equivFin (Orbit hW) (orbitOf hW u) :=
```

**`U2.ActiveSet`** (L1688, structure)

```lean
structure ActiveSet (S : Slot W → Prop) : Prop where
  isσ : ∀ u, S u → IsσSlot u
  twin : ∀ u, S u → S (σtwin hW u)
```

**`U2.slotPair`** (L1695, def)

```lean
noncomputable def slotPair : Perm {u : Slot W // S u} where
```

**`U2.slotRecord`** (L1710, def)

```lean
noncomputable def slotRecord : Record where
```

**`U2.slotRecord_comps`** (L1726, theorem)

```lean
@[simp] theorem slotRecord_comps : (slotRecord hW S hS).comps = Fin (numComp hW) :=
```

**`U2.slotRecord_M`** (L1727, theorem)

```lean
@[simp] theorem slotRecord_M : (slotRecord hW S hS).M = {u : Slot W // S u} :=
```

**`U2.slotRecord_comp`** (L1728, theorem)

```lean
theorem slotRecord_comp (u : {u : Slot W // S u}) : (slotRecord hW S hS).comp u = slotComp hW u.1 :=
```

**`U2.slotRecord_succ`** (L1729, theorem)

```lean
theorem slotRecord_succ : (slotRecord hW S hS).succ = firstReturn (nextPerm hW) S :=
```

**`U2.slotRecord_succ_val`** (L1730, theorem)

```lean
theorem slotRecord_succ_val (u : {u : Slot W // S u}) :
    ((slotRecord hW S hS).succ u).1 = ((nextPerm hW) ^ returnTime (nextPerm hW) S u.1 u.2) u.1 :=
```

**`U2.slotRecord_pair_val`** (L1732, theorem)

```lean
theorem slotRecord_pair_val (u : {u : Slot W // S u}) :
    ((slotRecord hW S hS).pair u).1 = σtwin hW u.1 :=
```

**`U2.slotRecord_isOver`** (L1734, theorem)

```lean
theorem slotRecord_isOver (u : {u : Slot W // S u}) : (slotRecord hW S hS).isOver u = isDesc u.1 :=
```

**`U2.slotRecord_sgn`** (L1735, theorem)

```lean
theorem slotRecord_sgn (u : {u : Slot W // S u}) : (slotRecord hW S hS).sgn u = σsgn u.1 :=
```

**`U2.slotRecordCongr`** (L1738, def)

```lean
noncomputable def slotRecordCongr (S' : Slot W → Prop) [DecidablePred S'] (hS' : ActiveSet hW S')
    (h : ∀ u, S u ↔ S' u) : RecordIso (slotRecord hW S hS) (slotRecord hW S' hS') where
```

#### section `DiagramIso`


**`U2.visit_ext`** (L1757, theorem)

```lean
theorem visit_ext {Γ : Shadow} {v w : Γ.Visit} (h1 : v.1 = w.1) (h2 : v.2.val = w.2.val) : v = w :=
```

**`U2.signType_ext_int`** (L1764, theorem)

```lean
theorem signType_ext_int {a b : SignType} (h : ((a : SignType) : ℤ) = b) : a = b :=
```

**`U2.cycBetween_nat_add`** (L1769, theorem)

```lean
theorem cycBetween_nat_add {A B C : ℕ} (hAB : A ≠ B) (hBC : B ≠ C) (hAC : A ≠ C) {α β γ : ℝ}
    (hα0 : 0 ≤ α) (hα1 : α < 1) (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) :
    cycBetween (A + α) (B + β) (C + γ) ↔ ((A < B ∧ B < C) ∨ (B < C ∧ C < A) ∨ (C < A ∧ A < B)) :=
```

**`U2.colActive`** (L1786, def)

```lean
def colActive (K : ℕ → Prop) (u : Slot W) : Prop :=
```

**`U2.(anonymous)`** (L1788, instance)

```lean
instance (K : ℕ → Prop) [DecidablePred K] : DecidablePred (colActive (W := W) K) :=
```

**`U2.colActive_activeSet`** (L1791, theorem)

```lean
theorem colActive_activeSet (K : ℕ → Prop) : ActiveSet hW (colActive K) where
```

**`U2.colActive_σSlotA`** (L1795, theorem)

```lean
theorem colActive_σSlotA {K : ℕ → Prop} {k m : ℕ} (hk : k < W.length) (hℓ : letterAt W k = .σ m) (hK : K k) :
    colActive K (σSlotA hW hk hℓ) :=
```

**`U2.colActive_σSlotB`** (L1798, theorem)

```lean
theorem colActive_σSlotB {K : ℕ → Prop} {k m : ℕ} (hk : k < W.length) (hℓ : letterAt W k = .σ m) (hK : K k) :
    colActive K (σSlotB hW hk hℓ) :=
```

**`U2.stStrand`** (L1804, def)

```lean
noncomputable def stStrand (u : Slot W) : ((shadowOf pl hW hne).withVertices V).Strand :=
```

**`U2.idxEquiv_stStrand`** (L1806, theorem)

```lean
@[simp] theorem idxEquiv_stStrand (u : Slot W) : idxEquiv hW (stStrand pl hW hne V u) = u :=
```

**`U2.stStrand_idxEquiv`** (L1809, theorem)

```lean
@[simp] theorem stStrand_idxEquiv (s : ((shadowOf pl hW hne).withVertices V).Strand) :
    stStrand pl hW hne V (idxEquiv hW s) = s :=
```

**`U2.stStrand_injective`** (L1812, theorem)

```lean
theorem stStrand_injective : Function.Injective (stStrand pl hW hne V) :=
```

**`U2.strIdx`** (L1815, def)

```lean
def strIdx (s : ((shadowOf pl hW hne).withVertices V).Strand) : Idx hW :=
```

**`U2.idxEquiv_strIdx`** (L1817, theorem)

```lean
theorem idxEquiv_strIdx (s : ((shadowOf pl hW hne).withVertices V).Strand) :
    idxEquiv hW (strIdx pl hW hne V s) = idxEquiv hW s :=
```

**`U2.strIdx_stStrand`** (L1820, theorem)

```lean
theorem strIdx_stStrand (u : Slot W) : strIdx pl hW hne V (stStrand pl hW hne V u) = (idxEquiv hW).symm u :=
```

**`U2.eq_stStrand_iff`** (L1822, theorem)

```lean
theorem eq_stStrand_iff (s : ((shadowOf pl hW hne).withVertices V).Strand) (u : Slot W) :
    s = stStrand pl hW hne V u ↔ idxEquiv hW s = u :=
```

**`U2.mkDiagram`** (L1831, abbrev)

```lean
noncomputable abbrev mkDiagram : Diagram :=
```

**`U2.σpair`** (L1837, abbrev)

```lean
noncomputable abbrev σpair {k m : ℕ} (hk : k < W.length) (hℓ : letterAt W k = .σ m) :
    Finset ((shadowOf pl hW hne).withVertices V).Strand :=
```

**`U2.mem_σpair_A`** (L1841, theorem)

```lean
theorem mem_σpair_A {k m : ℕ} (hk : k < W.length) (hℓ : letterAt W k = .σ m) :
    stStrand pl hW hne V (σSlotA hW hk hℓ) ∈ σpair pl hW hne V hk hℓ :=
```

**`U2.mem_σpair_B`** (L1844, theorem)

```lean
theorem mem_σpair_B {k m : ℕ} (hk : k < W.length) (hℓ : letterAt W k = .σ m) :
    stStrand pl hW hne V (σSlotB hW hk hℓ) ∈ σpair pl hW hne V hk hℓ :=
```

**`U2.mem_σpair_iff`** (L1848, theorem)

```lean
theorem mem_σpair_iff {k m : ℕ} (hk : k < W.length) (hℓ : letterAt W k = .σ m)
    (s : ((shadowOf pl hW hne).withVertices V).Strand) :
    s ∈ σpair pl hW hne V hk hℓ ↔ idxEquiv hW s = σSlotA hW hk hℓ ∨ idxEquiv hW s = σSlotB hW hk hℓ :=
```

**`U2.colOf_of_mem_σpair`** (L1853, theorem)

```lean
theorem colOf_of_mem_σpair {k m : ℕ} (hk : k < W.length) (hℓ : letterAt W k = .σ m)
    {s : ((shadowOf pl hW hne).withVertices V).Strand} (hs : s ∈ σpair pl hW hne V hk hℓ) :
    colOf (idxEquiv hW s) = k :=
```

**`U2.SlotDiagramData`** (L1865, structure)

```lean
structure SlotDiagramData : Prop where
  cross : ∀ x : Finset ((shadowOf pl hW hne).withVertices V).Strand,
    ((shadowOf pl hW hne).withVertices V).IsCrossing x ↔
      ∃ (k m : ℕ) (hk : k < W.length) (hℓ : letterAt W k = .σ m), K k ∧ x = σpair pl hW hne V hk hℓ
  overStrand : ∀ (x : ((shadowOf pl hW hne).withVertices V).Crossing) (k m : ℕ) (hk : k < W.length)
    (hℓ : letterAt W k = .σ m), x.val = σpair pl hW hne V hk hℓ → ov x = stStrand pl hW hne V (σSlotA hW hk hℓ)
  sgn : ∀ (x : ((shadowOf pl hW hne).withVertices V).Crossing) (k m : ℕ) (hk : k < W.length)
    (hℓ : letterAt W k = .σ m), x.val = σpair pl hW hne V hk hℓ →
    ((mkDiagram pl hW hne V hgen ov hov).sign x : ℤ) = if bit W k m = bit W k (m + 1) then 1 else -1
```

**`U2.σcross`** (L1879, def)

```lean
noncomputable def σcross {k m : ℕ} (hk : k < W.length) (hℓ : letterAt W k = .σ m) (hK : K k) :
    (mkDiagram pl hW hne V hgen ov hov).Γ.Crossing :=
```

**`U2.σcross_val`** (L1883, theorem)

```lean
theorem σcross_val {k m : ℕ} (hk : k < W.length) (hℓ : letterAt W k = .σ m) (hK : K k) :
    (σcross pl hW hne V hgen ov hov K data hk hℓ hK).val = σpair pl hW hne V hk hℓ :=
```

**`U2.visit_active`** (L1887, theorem)

```lean
theorem visit_active (v : (mkDiagram pl hW hne V hgen ov hov).Γ.Visit) :
    colActive K (idxEquiv hW v.2.val) :=
```

**`U2.crossing_eq_of_mem`** (L1896, theorem)

```lean
theorem crossing_eq_of_mem {x y : (mkDiagram pl hW hne V hgen ov hov).Γ.Crossing}
    {s : (mkDiagram pl hW hne V hgen ov hov).Γ.Strand} (hx : s ∈ x.val) (hy : s ∈ y.val) : x = y :=
```

**`U2.toVisit`** (L1908, def)

```lean
noncomputable def toVisit (u : {u : Slot W // colActive K u}) : (mkDiagram pl hW hne V hgen ov hov).Γ.Visit :=
```

**`U2.toVisit_strand`** (L1914, theorem)

```lean
theorem toVisit_strand (u : {u : Slot W // colActive K u}) :
    (toVisit pl hW hne V hgen ov hov K data u).2.val = stStrand pl hW hne V u.1 :=
```

**`U2.visitEquiv`** (L1918, def)

```lean
noncomputable def visitEquiv : (mkDiagram pl hW hne V hgen ov hov).Γ.Visit ≃ {u : Slot W // colActive K u} where
```

**`U2.visitEquiv_apply_val`** (L1932, theorem)

```lean
theorem visitEquiv_apply_val (v : (mkDiagram pl hW hne V hgen ov hov).Γ.Visit) :
    (visitEquiv pl hW hne V hgen ov hov K data v).1 = idxEquiv hW v.2.val :=
```

**`U2.visitEquiv_symm_apply`** (L1935, theorem)

```lean
theorem visitEquiv_symm_apply (u : {u : Slot W // colActive K u}) :
    (visitEquiv pl hW hne V hgen ov hov K data).symm u = toVisit pl hW hne V hgen ov hov K data u :=
```

**`U2.slot_other`** (L1939, theorem)

```lean
theorem slot_other {x : (mkDiagram pl hW hne V hgen ov hov).Γ.Crossing}
    {s : (mkDiagram pl hW hne V hgen ov hov).Γ.Strand} (hs : s ∈ x.val) :
    idxEquiv hW (((shadowOf pl hW hne).withVertices V).other x hs) = σtwin hW (idxEquiv hW s) :=
```

**`U2.overBit_eq`** (L1959, theorem)

```lean
theorem overBit_eq (v : (mkDiagram pl hW hne V hgen ov hov).Γ.Visit) :
    (mkDiagram pl hW hne V hgen ov hov).overBit v = isDesc (idxEquiv hW v.2.val) :=
```

**`U2.sign_eq`** (L1975, theorem)

```lean
theorem sign_eq (v : (mkDiagram pl hW hne V hgen ov hov).Γ.Visit) :
    (mkDiagram pl hW hne V hgen ov hov).sign v.1 = σsgn (idxEquiv hW v.2.val) :=
```

**`U2.visit_eq_of_strand_eq`** (L1983, theorem)

```lean
theorem visit_eq_of_strand_eq {w w' : (mkDiagram pl hW hne V hgen ov hov).Γ.Visit}
    (h : w.2.val = w'.2.val) : w = w' :=
```

**`U2.idxEquiv_add`** (L1989, theorem; `omit data in`)

```lean
theorem idxEquiv_add (i : Fin (numComp hW)) (a : ZMod (period hW (rep hW i))) (n : ℕ) :
    idxEquiv hW ⟨i, a + n⟩ = (next hW)^[n] (idxEquiv hW ⟨i, a⟩) :=
```

**`U2.nextPerm_pow_apply`** (L1998, theorem; `omit data in`)

```lean
theorem nextPerm_pow_apply (n : ℕ) (u : Slot W) : ((nextPerm hW) ^ n) u = (next hW)^[n] u :=
```

**`U2.visitCoord_eq`** (L2003, theorem; `omit data in`)

```lean
theorem visitCoord_eq (w : (mkDiagram pl hW hne V hgen ov hov).Γ.Visit) :
    (mkDiagram pl hW hne V hgen ov hov).visitCoord w =
      ((w.2.val.2.val : ℕ) : ℝ) + ((mkDiagram pl hW hne V hgen ov hov).visitPt w).2.2.val :=
```

**`U2.visitCoord_eq_of`** (L2009, theorem; `omit data in`)

```lean
theorem visitCoord_eq_of (w : (𝔇).Γ.Visit) {i : Fin (numComp hW)} {b : ZMod (period hW (rep hW i))}
    (h : strIdx pl hW hne V w.2.val = ⟨i, b⟩) :
    (𝔇).visitCoord w = ((b.val : ℕ) : ℝ) + ((𝔇).visitPt w).2.2.val :=
```

**`U2.compOf_eq_of`** (L2019, theorem; `omit data in`)

```lean
theorem compOf_eq_of (w : (𝔇).Γ.Visit) {i : Fin (numComp hW)} {b : ZMod (period hW (rep hW i))}
    (h : strIdx pl hW hne V w.2.val = ⟨i, b⟩) : (𝔇).compOf w = i :=
```

**`U2.nextVisit_eq`** (L2027, theorem)

```lean
theorem nextVisit_eq [DecidablePred K] (v : (mkDiagram pl hW hne V hgen ov hov).Γ.Visit) :
    (mkDiagram pl hW hne V hgen ov hov).nextVisit v =
      toVisit pl hW hne V hgen ov hov K data
        (firstReturn (nextPerm hW) (colActive K) (visitEquiv pl hW hne V hgen ov hov K data v)) :=
```

**`U2.diagramRecordIso`** (L2155, def)

```lean
noncomputable def diagramRecordIso [DecidablePred K] :
    RecordIso (mkDiagram pl hW hne V hgen ov hov).record (slotRecord hW (colActive K) (colActive_activeSet hW K)) where
```

#### section `Realize`

Section variables (in scope, included only when mentioned unless `include`d):

```lean
variable (pl : Placement) {W : Word} (hW : W.Closed) (hne : W ≠ [])
```

**`U2.allActive`** (L2182, theorem)

```lean
theorem allActive : ActiveSet hW (IsσSlot (W := W)) where
```

**`U2.realizeAt_data`** (L2187, theorem)

```lean
theorem realizeAt_data :
    SlotDiagramData pl hW hne (shadowOf pl hW hne).vertices (realizeAt pl hW hne).generic
      (realizeAt pl hW hne).overStrand (realizeAt pl hW hne).overStrand_mem (fun _ => True) where
```

**`U2.realizeAtRecordIso`** (L2209, def)

```lean
noncomputable def realizeAtRecordIso :
    RecordIso (realizeAt pl hW hne).diagram.record (slotRecord hW IsσSlot (allActive hW)) :=
```

#### section `Exterior`

Section variables (in scope, included only when mentioned unless `include`d):

```lean
variable (X P Y P' : Word)
```

**`U2.instDecidableExtCol`** (L2226, instance)

```lean
instance instDecidableExtCol (k : ℕ) : Decidable (ExtCol X P k) :=
```

**`U2.instDecidablePredExtCol`** (L2227, instance)

```lean
instance instDecidablePredExtCol : DecidablePred (ExtCol X P) :=
```

**`U2.ExtPiece`** (L2230, def)

```lean
def ExtPiece (u : Slot (X ++ P ++ Y)) : Prop :=
```

**`U2.(anonymous)`** (L2232, instance)

```lean
instance : DecidablePred (ExtPiece X P Y) :=
```

**`U2.extPiece_σtwin`** (L2234, theorem)

```lean
theorem extPiece_σtwin (hW : (X ++ P ++ Y).Closed) {u : Slot (X ++ P ++ Y)} (hu : IsσSlot u)
    (h : ExtPiece X P Y u) : ExtPiece X P Y (σtwin hW u) :=
```

**`U2.shiftIdx_injOn`** (L2238, theorem)

```lean
theorem shiftIdx_injOn (hP : P ≠ []) {k k' : ℕ} (hk : ExtCol X P k) (hk' : ExtCol X P k')
    (h : shiftIdx X P P' k = shiftIdx X P P' k') : k = k' :=
```

**`U2.unshiftCol`** (L2246, def)

```lean
def unshiftCol (k' : ℕ) : ℕ :=
```

**`U2.unshiftCol_spec`** (L2248, theorem)

```lean
theorem unshiftCol_spec (hP : P ≠ []) {k' : ℕ} (h : ExtCol X P' k') :
    ExtCol X P (unshiftCol X P P' k') ∧ shiftIdx X P P' (unshiftCol X P P' k') = k' :=
```

**`U2.colOf_mk`** (L2255, theorem)

```lean
theorem colOf_mk {V : Word} (k p : ℕ) (hs : IsSlot V (k, p)) :
    colOf (⟨(k, p), hs⟩ : Slot V) = if p = 0 then k else if bit V k p then k else k - 1 :=
```

**`U2.extF`** (L2262, def)

```lean
noncomputable def extF (u : {u : Slot (X ++ P ++ Y) // ExtPiece X P Y u}) :
    {u' : Slot (X ++ P' ++ Y) // ExtPiece X P' Y u'} :=
```

**`U2.extF_val`** (L2269, theorem)

```lean
theorem extF_val (u : {u : Slot (X ++ P ++ Y) // ExtPiece X P Y u}) :
    (extF X P Y P' hP hE hW u).1.1 = extPair X P P' u.1.1 :=
```

**`U2.extF_eq`** (L2272, theorem)

```lean
theorem extF_eq (u : {u : Slot (X ++ P ++ Y) // ExtPiece X P Y u}) :
    (extF X P Y P' hP hE hW u).1 = extSlot X P Y P' hP hE ⟨u.1, isExtSlot_of_extCol X P Y P' hP hE u.1 u.2⟩ :=
```

**`U2.extF_injective`** (L2275, theorem)

```lean
theorem extF_injective : Function.Injective (extF X P Y P' hP hE hW) :=
```

**`U2.length_W'`** (L2322, theorem; `omit hP hE hW in`)

```lean
theorem length_W' : (X ++ P' ++ Y).length = X.length + P'.length + Y.length :=
```

**`U2.length_W`** (L2325, theorem; `omit hP hE hW in`)

```lean
theorem length_W : (X ++ P ++ Y).length = X.length + P.length + Y.length :=
```

**`U2.extF_surjective`** (L2328, theorem)

```lean
theorem extF_surjective : Function.Surjective (extF X P Y P' hP hE hW) :=
```

**`U2.φE`** (L2411, def)

```lean
noncomputable def φE : {u : Slot (X ++ P ++ Y) // ExtPiece X P Y u} ≃ {u' : Slot (X ++ P' ++ Y) // ExtPiece X P' Y u'} :=
```

**`U2.φE_apply`** (L2414, theorem)

```lean
theorem φE_apply (u : {u : Slot (X ++ P ++ Y) // ExtPiece X P Y u}) :
    φE X P Y P' hP hE hW u = extF X P Y P' hP hE hW u :=
```

**`U2.φE_val`** (L2417, theorem)

```lean
theorem φE_val (u : {u : Slot (X ++ P ++ Y) // ExtPiece X P Y u}) :
    (φE X P Y P' hP hE hW u).1.1 = extPair X P P' u.1.1 :=
```

**`U2.colOf_φE`** (L2420, theorem)

```lean
theorem colOf_φE (u : {u : Slot (X ++ P ++ Y) // ExtPiece X P Y u}) :
    colOf (φE X P Y P' hP hE hW u).1 = shiftIdx X P P' (colOf u.1) :=
```

**`U2.Passage`** (L2429, structure)

```lean
structure Passage : Prop where
  pass : ∀ b : Slot (X ++ P ++ Y), IsExtSlot X P b.1 → ¬ ExtCol X P (colOf b) →
    ∃ (m : ℕ) (c : Slot (X ++ P ++ Y)), (next hW)^[m] b = c ∧ ExtCol X P (colOf c) ∧
      (∀ i < m, ¬ ExtCol X P (colOf ((next hW)^[i] b))) ∧
      ∃ (m' : ℕ) (b' : Slot (X ++ P' ++ Y)), b'.1 = extPair X P P' b.1 ∧
        ((next hW')^[m'] b').1 = extPair X P P' c.1 ∧
        ∀ i < m', ¬ ExtCol X P' (colOf ((next hW')^[i] b'))
```

**`U2.conj_of_passage`** (L2438, theorem)

```lean
theorem conj_of_passage (hpass : Passage X P Y P' hW hW') (u : {u : Slot (X ++ P ++ Y) // ExtPiece X P Y u}) :
    firstReturn (nextPerm hW') (ExtPiece X P' Y) (φE X P Y P' hP hE hW u) =
      φE X P Y P' hP hE hW (firstReturn (nextPerm hW) (ExtPiece X P Y) u) :=
```

**`U2.entry_iff`** (L2492, theorem; `omit hE in`)

```lean
theorem entry_iff (b : Slot (X ++ P ++ Y)) :
    IsExtSlot X P b.1 ∧ ¬ ExtCol X P (colOf b) ↔
      (∃ p, b.1 = (X.length, p) ∧ p ≠ 0 ∧ bit (X ++ P ++ Y) X.length p = true) ∨
      (∃ p, b.1 = (X.length + P.length, p) ∧ p ≠ 0 ∧ bit (X ++ P ++ Y) (X.length + P.length) p = false) :=
```

**`U2.shapeOf_φE`** (L2538, theorem)

```lean
theorem shapeOf_φE (u : {u : Slot (X ++ P ++ Y) // ExtPiece X P Y u}) :
    shapeOf (φE X P Y P' hP hE hW u).1 = shapeOf u.1 :=
```

**`U2.letterAt_colOf_φE`** (L2571, theorem)

```lean
theorem letterAt_colOf_φE (u : {u : Slot (X ++ P ++ Y) // ExtPiece X P Y u}) :
    letterAt (X ++ P' ++ Y) (colOf (φE X P Y P' hP hE hW u).1) = letterAt (X ++ P ++ Y) (colOf u.1) :=
```

**`U2.bit_colOf_φE`** (L2575, theorem)

```lean
theorem bit_colOf_φE (u : {u : Slot (X ++ P ++ Y) // ExtPiece X P Y u}) (p : ℕ) :
    bit (X ++ P' ++ Y) (colOf (φE X P Y P' hP hE hW u).1) p = bit (X ++ P ++ Y) (colOf u.1) p :=
```

**`U2.isσSlot_φE_iff`** (L2580, theorem)

```lean
theorem isσSlot_φE_iff (u : {u : Slot (X ++ P ++ Y) // ExtPiece X P Y u}) :
    IsσSlot (φE X P Y P' hP hE hW u).1 ↔ IsσSlot u.1 :=
```

**`U2.isDesc_φE`** (L2585, theorem)

```lean
theorem isDesc_φE (u : {u : Slot (X ++ P ++ Y) // ExtPiece X P Y u}) :
    isDesc (φE X P Y P' hP hE hW u).1 = isDesc u.1 :=
```

**`U2.σsgn_φE`** (L2589, theorem)

```lean
theorem σsgn_φE (u : {u : Slot (X ++ P ++ Y) // ExtPiece X P Y u}) :
    σsgn (φE X P Y P' hP hE hW u).1 = σsgn u.1 :=
```

**`U2.φE_σtwin`** (L2594, theorem)

```lean
theorem φE_σtwin (u : {u : Slot (X ++ P ++ Y) // ExtPiece X P Y u}) (hu : IsσSlot u.1) :
    (φE X P Y P' hP hE hW ⟨σtwin hW u.1, extPiece_σtwin X P Y hW hu u.2⟩).1 = σtwin hW' (φE X P Y P' hP hE hW u).1 :=
```

**`U2.colActive_φE_iff`** (L2606, theorem)

```lean
theorem colActive_φE_iff (u : {u : Slot (X ++ P ++ Y) // ExtPiece X P Y u}) :
    colActive (ExtCol X P') (φE X P Y P' hP hE hW u).1 ↔ colActive (ExtCol X P) u.1 :=
```

**`U2.extActiveEquiv`** (L2613, def)

```lean
noncomputable def extActiveEquiv :
    {u : Slot (X ++ P ++ Y) // colActive (ExtCol X P) u} ≃ {u' : Slot (X ++ P' ++ Y) // colActive (ExtCol X P') u'} where
```

**`U2.extActiveEquiv_val`** (L2629, theorem)

```lean
theorem extActiveEquiv_val (u : {u : Slot (X ++ P ++ Y) // colActive (ExtCol X P) u}) :
    (extActiveEquiv X P Y P' hP hE hW u).1 = (φE X P Y P' hP hE hW ⟨u.1, u.2.2⟩).1 :=
```

**`U2.extRecordIso`** (L2634, def)

```lean
noncomputable def extRecordIso (hpass : Passage X P Y P' hW hW')
    (hexit : ∀ u : Slot (X ++ P ++ Y), ∃ n : ℕ, ExtPiece X P Y ((next hW)^[n] u))
    (hexit' : ∀ u' : Slot (X ++ P' ++ Y), ∃ n : ℕ, ExtPiece X P' Y ((next hW')^[n] u')) :
    RecordIso (slotRecord hW (colActive (ExtCol X P)) (colActive_activeSet hW _))
      (slotRecord hW' (colActive (ExtCol X P')) (colActive_activeSet hW' _)) :=
```

#### section `Consequences`


**`U2.realizeRecordIso`** (L2687, def)

```lean
noncomputable def realizeRecordIso (W : OWord) (h : W.letters ≠ []) :
    RecordIso (realize W).diagram.record (slotRecord W.closed IsσSlot (allActive W.closed)) :=
```

**`U2.colActive_extCol_iff`** (L2693, theorem)

```lean
theorem colActive_extCol_iff (X P Y : Word)
    (hnoσ : ∀ k, X.length ≤ k → k < X.length + P.length → (letterAt (X ++ P ++ Y) k).isCrossing = false)
    (u : Slot (X ++ P ++ Y)) : colActive (ExtCol X P) u ↔ IsσSlot u :=
```

**`U2.orbitEquivOfSlotEquiv`** (L2710, def)

```lean
noncomputable def orbitEquivOfSlotEquiv (ψ : Slot W ≃ Slot W') (hnext : ∀ u, ψ (next hW u) = next hW' (ψ u)) :
    Orbit hW ≃ Orbit hW' :=
```

**`U2.slotRecordIsoOfSlotEquiv`** (L2717, def)

```lean
noncomputable def slotRecordIsoOfSlotEquiv (ψ : Slot W ≃ Slot W') (hnext : ∀ u, ψ (next hW u) = next hW' (ψ u))
    (hact : ∀ u, S' (ψ u) ↔ S u) (htwin : ∀ u, S u → ψ (σtwin hW u) = σtwin hW' (ψ u))
    (hdesc : ∀ u, S u → isDesc (ψ u) = isDesc u) (hsgn : ∀ u, S u → σsgn (ψ u) = σsgn u) :
    RecordIso (slotRecord hW S hS) (slotRecord hW' S' hS') where
```

#### section `Composed`

Section variables (in scope, included only when mentioned unless `include`d):

```lean
variable (X P Y P' : Word) (hP : P ≠ []) (hE : SameEffect X P P') (hW : (X ++ P ++ Y).Closed) (hW' : (X ++ P' ++ Y).Closed)
include hP hE
```

**`U2.vertexMovedRecordIso`** (L2749, def)

```lean
noncomputable def vertexMovedRecordIso (pl : Placement) (hne : X ++ P ++ Y ≠ []) (hne' : X ++ P' ++ Y ≠ [])
    (V : (shadowOf pl hW hne).Vertices) (hgen : ((shadowOf pl hW hne).withVertices V).Generic)
    (ov : ((shadowOf pl hW hne).withVertices V).Crossing → ((shadowOf pl hW hne).withVertices V).Strand)
    (hov : ∀ x, ov x ∈ x.val) (data : SlotDiagramData pl hW hne V hgen ov hov (ExtCol X P))
    (hpass : Passage X P Y P' hW hW')
    (hexit : ∀ u : Slot (X ++ P ++ Y), ∃ n : ℕ, ExtPiece X P Y ((next hW)^[n] u))
    (hexit' : ∀ u' : Slot (X ++ P' ++ Y), ∃ n : ℕ, ExtPiece X P' Y ((next hW')^[n] u'))
    (hnoσ : ∀ k, X.length ≤ k → k < X.length + P'.length → (letterAt (X ++ P' ++ Y) k).isCrossing = false)
    (pl' : Placement) :
    RecordIso (mkDiagram pl hW hne V hgen ov hov).record (realizeAt pl' hW' hne').diagram.record :=
```

**`U2.vertexMovedRecordIso'`** (L2765, def)

```lean
noncomputable def vertexMovedRecordIso' (pl : Placement) (hne : X ++ P ++ Y ≠ [])
    (V : (shadowOf pl hW hne).Vertices) (hgen : ((shadowOf pl hW hne).withVertices V).Generic)
    (ov : ((shadowOf pl hW hne).withVertices V).Crossing → ((shadowOf pl hW hne).withVertices V).Strand)
    (hov : ∀ x, ov x ∈ x.val) (data : SlotDiagramData pl hW hne V hgen ov hov (ExtCol X P))
    (hpass : Passage X P Y P' hW hW')
    (hexit : ∀ u : Slot (X ++ P ++ Y), ∃ n : ℕ, ExtPiece X P Y ((next hW)^[n] u))
    (hexit' : ∀ u' : Slot (X ++ P' ++ Y), ∃ n : ℕ, ExtPiece X P' Y ((next hW')^[n] u'))
    (hnoσ : ∀ k, X.length ≤ k → k < X.length + P'.length → (letterAt (X ++ P' ++ Y) k).isCrossing = false)
    (W' : OWord) (hW'eq : W'.letters = X ++ P' ++ Y) (hne' : X ++ P' ++ Y ≠ []) :
    RecordIso (mkDiagram pl hW hne V hgen ov hov).record (realize W').diagram.record :=
```

**`U2.realizeAtRecordIsoOfExt`** (L2784, def)

```lean
noncomputable def realizeAtRecordIsoOfExt (hne : X ++ P ++ Y ≠ []) (hne' : X ++ P' ++ Y ≠ [])
    (hpass : Passage X P Y P' hW hW')
    (hexit : ∀ u : Slot (X ++ P ++ Y), ∃ n : ℕ, ExtPiece X P Y ((next hW)^[n] u))
    (hexit' : ∀ u' : Slot (X ++ P' ++ Y), ∃ n : ℕ, ExtPiece X P' Y ((next hW')^[n] u'))
    (hnoσ : ∀ k, X.length ≤ k → k < X.length + P.length → (letterAt (X ++ P ++ Y) k).isCrossing = false)
    (hnoσ' : ∀ k, X.length ≤ k → k < X.length + P'.length → (letterAt (X ++ P' ++ Y) k).isCrossing = false)
    (pl pl' : Placement) :
    RecordIso (realizeAt pl hW hne).diagram.record (realizeAt pl' hW' hne').diagram.record :=
```

**`U2.realize_recordIso_of_ext`** (L2800, theorem)

```lean
theorem realize_recordIso_of_ext (hne : X ++ P ++ Y ≠ []) (hne' : X ++ P' ++ Y ≠ [])
    (hpass : Passage X P Y P' hW hW')
    (hexit : ∀ u : Slot (X ++ P ++ Y), ∃ n : ℕ, ExtPiece X P Y ((next hW)^[n] u))
    (hexit' : ∀ u' : Slot (X ++ P' ++ Y), ∃ n : ℕ, ExtPiece X P' Y ((next hW')^[n] u'))
    (hnoσ : ∀ k, X.length ≤ k → k < X.length + P.length → (letterAt (X ++ P ++ Y) k).isCrossing = false)
    (hnoσ' : ∀ k, X.length ≤ k → k < X.length + P'.length → (letterAt (X ++ P' ++ Y) k).isCrossing = false)
    (W W' : OWord) (hWeq : W.letters = X ++ P ++ Y) (hW'eq : W'.letters = X ++ P' ++ Y) :
    Nonempty (RecordIso (realize W).diagram.record (realize W').diagram.record) :=
```

#### section `AddFree`


**`U2.addFreeCongr`** (L2823, def)

```lean
noncomputable def addFreeCongr {ρ ρ' : Record} (ι : RecordIso ρ ρ') : RecordIso ρ.addFree ρ'.addFree where
```

**`U2.extRecordIsoAddFree`** (L2839, def)

```lean
noncomputable def extRecordIsoAddFree (hpass : Passage X P Y P' hW hW')
    (hexit' : ∀ u' : Slot (X ++ P' ++ Y), ∃ n : ℕ, ExtPiece X P' Y ((next hW')^[n] u'))
    (c₀ : Orbit hW)
    (hc₀ : ∀ u : Slot (X ++ P ++ Y), (¬ ∃ n : ℕ, ExtPiece X P Y ((next hW)^[n] u)) ↔ orbitOf hW u = c₀) :
    RecordIso (slotRecord hW (colActive (ExtCol X P)) (colActive_activeSet hW _))
      (slotRecord hW' (colActive (ExtCol X P')) (colActive_activeSet hW' _)).addFree :=
```

**`U2.realize_recordIso_addFree_of_ext`** (L2889, theorem)

```lean
theorem realize_recordIso_addFree_of_ext (hne : X ++ P ++ Y ≠ []) (hne' : X ++ P' ++ Y ≠ [])
    (hpass : Passage X P Y P' hW hW')
    (hexit' : ∀ u' : Slot (X ++ P' ++ Y), ∃ n : ℕ, ExtPiece X P' Y ((next hW')^[n] u'))
    (c₀ : Orbit hW)
    (hc₀ : ∀ u : Slot (X ++ P ++ Y), (¬ ∃ n : ℕ, ExtPiece X P Y ((next hW)^[n] u)) ↔ orbitOf hW u = c₀)
    (hnoσ : ∀ k, X.length ≤ k → k < X.length + P.length → (letterAt (X ++ P ++ Y) k).isCrossing = false)
    (hnoσ' : ∀ k, X.length ≤ k → k < X.length + P'.length → (letterAt (X ++ P' ++ Y) k).isCrossing = false)
    (W W' : OWord) (hWeq : W.letters = X ++ P ++ Y) (hW'eq : W'.letters = X ++ P' ++ Y) :
    Nonempty (RecordIso (realize W).diagram.record (realize W').diagram.record.addFree) :=
```