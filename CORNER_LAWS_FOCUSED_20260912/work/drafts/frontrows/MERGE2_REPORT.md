# MERGE2_REPORT — front certificate rows, wave 2 merge (U3 + U4 + U8D + U8R)

2026-09-14 12:16 UTC / 8:16am ET, merger for the frontrows lane, wave 2.  Inputs: `Skeleton_W1.lean` (4,009 lines,
13 sorries: the wave-2 leaves) and the four unit files `W2_U3.lean`, `W2_U4.lean`, `W2_U8D.lean`, `W2_U8R.lean`
with their reports.  Output: **`work/drafts/frontrows/Skeleton_W2.lean`** (14,891 lines), produced by the script
`work/drafts/frontrows/merge2.py` (rerunnable; it re-derives every hunk from `diff Skeleton_W1.lean W2_Ux.lean`).

## 1. Result

| item | value |
|---|---|
| file | `work/drafts/frontrows/Skeleton_W2.lean`, 14,891 lines (W1: 4,009) |
| `grep -c sorry` | **5** (W1: 13; U3 closed 5, U8D closed 3, U8R closed 0, U4 has no leaves) |
| compile (`cd work/lean && lake env lean ../drafts/frontrows/Skeleton_W2.lean`) | **0 errors**, exit 0, 41 s wall (log `/workspace/scratch/merge2_compile.log`) |
| warnings | 5 × `declaration uses sorry` (the five open leaves below); 2 × unused section variable (`U8R.lexKey_injective` L13451, `U8R.mem_fib` L13472); 2 × "Variable name not explicitly referenced" (L14137 `q`, L14256 `t`, both in U8R).  All four non-sorry warnings were already in `W2_U8R.lean`; nothing new from the merge |
| remaining leaves | `typeIII_site` (L11100), `typeII_move` (L11109), `typeI_move` (L11117), `crossedCusp_move` (L11126) — all four of L-geo, units U5/U6 — and `represent` (L14571, U8R) |
| rows sorry-free (`#print axioms`) | **row 81 `SM.ng_circle`** and **row 82 `SM.ng_cusp_skein`**: `[propext, Classical.choice, Quot.sound, SM.lp_lm]` (`lp_lm` is the accepted literature interface reached through `P`).  Rows 76, 77, 78, 79, 80, 83 still reach `sorryAx` (§5) |
| clashes / renames | none needed: every unit's helpers live in their own namespace (`SM.FrontRows.U3`, `.U4`, `.U8D`, `.U8R`); Lean would have rejected a duplicate name and the compile is clean |

## 2. Verification of the units (task step 1)

`diff Skeleton_W1.lean W2_Ux.lean` for each unit, hunk by hunk (W1 line numbers):

| unit | hunks | kind |
|---|---|---|
| U3 | `2914a` (+5,687 lines: `/-! ### U3 infrastructure … -/ namespace U3 … end U3`); `2925c`, `2931c`, `2937c`, `2958,2959c`, `2964,2965c` | one insertion + the five leaf bodies `comm_recordIso`, `zigzag_recordIso`, `circle_recordIso_addFree`, `skein_site`, `skein_unique` |
| U4 | `2966a` (+2,329 lines: `/-! ### U4 infrastructure … -/ namespace U4 … end U4`) | one insertion, no leaf touched |
| U8D | `7a` (+6 `import Mathlib.…` lines after `import SM.PolynomialBlock`); `3668a` (+1,612 lines: `namespace U8D … end U8D`); `3674c`, `3679c`, `3684c` | imports + one insertion + the three leaf bodies `deform_downCount`, `deform_writhe`, `deform_P` |
| U8R | `3685a` (+1,151 lines: `section U8RInfra namespace U8R … end U8R end U8RInfra`) | one insertion, `represent` left as `sorry` |

Checks performed by `merge2.py` and by hand:
- **No deletion hunk** in any unit (only `a` and `c`).
- **Every `c` hunk replaces exactly one `sorry`**, and the replacement text starts with the *verbatim* old line up to
  `:=` (statement, name, binders, docstring untouched); the new body contains no `sorry`.  Verified
  programmatically for all 8 `c` hunks (`statement-prefix identical=True`).
- **Scoping.** Each inserted block is closed: `namespace U3 … end U3`, `namespace U4 … noncomputable section … end … end U4`,
  `namespace U8D … noncomputable section … end … end U8D`, `section U8RInfra namespace U8R … end U8R end U8RInfra`.
  All `open`, `local notation`, `noncomputable section` inside them are scoped; no top-level `set_option`/`attribute`.
- **Non-overlap.** The hunks of different units touch disjoint W1 ranges (insertion points 7, 2914, 2966, 3668,
  3685; replaced lines 2925-2965 and 3674-3684), so the merge is order-independent.
- **Containment (after the merge).** `diff Skeleton_W2.lean W2_Ux.lean`: the only lines present in a unit file and
  absent from `Skeleton_W2.lean` are the *other* units' leaf `sorry` lines (listed and checked for all four).
  Every unit hunk occurs verbatim and contiguously in `Skeleton_W2.lean`.
- **Imports.** The six Mathlib imports added by U8D (`InverseFunctionTheorem.ApproximatesLinearOn`, `MeanValue`,
  `Deriv.MeanValue`, `Topology.LocallyConstant.Basic`, `Normed.Operator.Banach`, `TangentCone.Prod`) did not break
  any other unit's proofs (0 errors in the merged compile).

## 3. Layout of `Skeleton_W2.lean`

| lines | content |
|---|---|
| 1-13 | imports (7 `SM.*` + the 6 Mathlib imports of U8D) |
| 15-41 | header docstring (unchanged from W1) |
| 42-149 | `namespace SM`, definitions, the eight bundles, nonemptiness helpers, `namespace FrontRows` (L146), `section Leaves` (L150) |
| 152-942 | L-deg, L-cnt, U1 infrastructure (wave 1) |
| 1167-2919 | U2 record core (wave 1) |
| **2921-8605** | **U3 infrastructure** (`namespace U3`, 5,675 lines, sections A-G: word combinatorics, `recordIsoOfConj`, letter-local passes, zigzag/circle/commutation/cusp-skein passages) |
| 8608-8755 | L-rec leaves, all five **proved** (`comm_recordIso` L8617, `zigzag_recordIso` L8641, `circle_recordIso_addFree` L8652, `SkeinSite`, `skein_site` L8676, `skein_unique` L8749) |
| **8756-11083** | **U4 infrastructure** (`namespace U4`, 2,316 lines, sections A-I; API in §6) |
| 11085-11128 | L-geo leaves, **open**: `typeIII_site` L11100, `typeII_move` L11109, `typeI_move` L11117, `crossedCusp_move` L11126 |
| 11130-11784 | L-PL (U7, wave 1) |
| **11787-13397** | **U8D infrastructure** (`namespace U8D`, 1,609 lines) |
| 13403-13413 | `deform_downCount`, `deform_writhe`, `deform_P` — **proved** (`h.elim fun d => U8D.…_of_deformation d …`) |
| **13417-14566** | **U8R infrastructure** (`section U8RInfra namespace U8R`, 1,150 lines) |
| 14571 | `represent` — **open** (reduced to `U8R.SweepStatement`, see §7) |
| 14575-14891 | `end Leaves`, glue, assembly of the eight rows, row 83, `end SM` (unchanged) |

## 4. Remaining leaves (5)

| leaf | line | unit | consumed by |
|---|---|---|---|
| `typeIII_site` | 11100 | U5 | `P_typeIII` → row 79 (`ng_front_III`), row 83 via `certificate_laws.pres_B` |
| `typeII_move` | 11109 | U6 | `P_typeII` → row 78 (`ng_front_II`), row 83 |
| `typeI_move` | 11117 | U6 | `P_typeI` → row 77 (`ng_front_I`), row 83 |
| `crossedCusp_move` | 11126 | U6 | `P_crossedCusp` → row 80 field `crossedCusp_B`, row 83 via `del_B` |
| `represent` | 14571 | U8R | row 76 field `represent`, row 83 (`ng_local_front_bound` opens with `ng_commutation.represent`) |

## 5. Rows 76-83: `#print axioms` in the merged file (probe copies `/tmp/lean_merge2/W2_ax.lean`, `W2_ax2.lean` = `Skeleton_W2.lean` + `#print axioms` lines; logs `/workspace/scratch/merge2_axioms.log`, `merge2_axioms2.log`)

| row | theorem | axioms | status |
|---|---|---|---|
| 76 ng:commutation | `SM.ng_commutation` | `[propext, sorryAx, Classical.choice, Quot.sound, SM.lp_lm]` | **open** — only through the field `represent`.  The other 8 fields are sorry-free: `comm_D/w/d/B` via `comm_counts` `[propext, Classical.choice, Quot.sound]` and `P_comm` `[…, SM.lp_lm]`; `deform_D/w/d/B` via `deform_downCount`, `deform_writhe` `[propext, Classical.choice, Quot.sound]` and `deform_P` `[…, SM.lp_lm]` |
| 77 ng:front-I | `SM.ng_front_I` | `[…, sorryAx, …, SM.lp_lm]` | open — `P_typeI` (← `typeI_move`); `typeI_counts` is sorry-free |
| 78 ng:front-II | `SM.ng_front_II` | `[…, sorryAx, …, SM.lp_lm]` | open — `P_typeII` (← `typeII_move`); `typeII_counts` sorry-free |
| 79 ng:front-III | `SM.ng_front_III` | `[…, sorryAx, …, SM.lp_lm]` | open — `P_typeIII` (← `typeIII_site`); `typeIII_counts` sorry-free |
| 80 ng:deletions | `SM.ng_deletions` | `[…, sorryAx, …, SM.lp_lm]` | open — only the field `crossedCusp_B` (`P_crossedCusp` ← `crossedCusp_move`).  `zigzag_s`, `zigzag_B` (`zigzag_counts`, `P_zigzag` `[propext, Classical.choice, Quot.sound, SM.lp_lm]`) and `crossedCusp_s` are sorry-free |
| **81 ng:circle** | `SM.ng_circle` | **`[propext, Classical.choice, Quot.sound, SM.lp_lm]`** | **CLOSED** (wave 2: `circle_recordIso_addFree` → `P_circleDeletion`; wave 1: `circleDeletion_counts`, `PLFront.IsStandardCircles.defect_eq_zero`) |
| **82 ng:cusp-skein** | `SM.ng_cusp_skein` (and `SM.ng_cusp_skein_both`) | **`[propext, Classical.choice, Quot.sound, SM.lp_lm]`** | **CLOSED** (wave 2: `skein_site` → `skein_ineq_forward/backward`, `skein_unique`; wave 1: `skein_counts`, the degree leaves) |
| 83 ng:local-front-bound | `SM.ng_local_front_bound` | `[propext, sorryAx, Classical.choice, Quot.sound, SM.lp_lm, SM.ng_finite_word]` | open — `represent` and, through `certificate_laws` (`[…, sorryAx, …, SM.lp_lm]`), the four L-geo leaves.  `SM.ng_finite_word` is the accepted literature interface consumed by `word_bound` |

Glue theorems, for reference: `P_comm`, `P_zigzag`, `P_circleDeletion`, `base_defect_nonneg`, `skein_ineq_forward`,
`skein_ineq_backward` = `[propext, Classical.choice, Quot.sound, SM.lp_lm]`; `P_typeI`, `P_typeII`, `P_typeIII`,
`P_crossedCusp` additionally `sorryAx`.  All 26 leaves: the 21 proved ones are `[propext, Classical.choice, Quot.sound]`
(`skein_unique`: `[propext, Quot.sound]`; `deform_P`: `+ SM.lp_lm`); the 5 open ones carry `sorryAx`.  Key new
declarations checked: `U3.cm_recordIso_above`, `U3.sk_switchIso`, `U3.sk_smoothIso`, `U8D.downCount_eq_of_deformation`,
`U8D.writhe_eq_of_deformation`, `U8R.represent_of_sweepStatement`, `U8R.markingRecordIso`, `U4.arcCover_of`,
`U4.generic_of`, `U4.slotDiagramData_of`, `U4.MatchData.moveMatch`, `U4.isDisc_polygon`, `U4.clean_mv`:
`[propext, Classical.choice, Quot.sound]` (`U8D.P_eq_of_deformation`: `+ SM.lp_lm`).

**What closes what next.** `typeIII_site` (U5) closes row 79.  `typeI_move` closes 77, `typeII_move` closes 78,
`crossedCusp_move` closes 80 (U6).  `represent` (U8R, the sweep) closes 76; with all five, `certificate_laws` and row 83.

## 6. The U4 API that U5 (`typeIII_site`) and U6 (`typeII_move`, `typeI_move`, `crossedCusp_move`) must consume

Namespace **`SM.FrontRows.U4`** (Skeleton_W2.lean L8768-11083; `open SM.FrontRealize SM.FrontWord.Letter Equiv`,
`noncomputable section`).  Statements below are copied from the merged file (line numbers are Skeleton_W2.lean).
Section `variable`s are listed first for each section; Lean includes a section variable in a declaration only when
the statement mentions it, so e.g. `PieceIn L hW mv u` (no `pl`, no `hne`) but `clean_mv pl hW hne mv …`.
The full list of the 190 declarations is W2_U4_REPORT.md §6; §2-§5 there give the intended calling patterns.

### 6.1 A. The disc: `polygon L` (section `Polygon`, L8779-8960)

```lean
structure HalfPlane where a : Plane; b : ℝ; ha : a ≠ 0                           -- L8779
-- namespace HalfPlane, variable (h : HalfPlane)
def HalfPlane.f (q : Plane) : ℝ := h.a.1 * q.1 + h.a.2 * q.2                      -- L8789
def HalfPlane.cl : Set Plane := {q | h.f q ≤ h.b}                                  -- L8792
def HalfPlane.op : Set Plane := {q | h.f q < h.b}                                  -- L8795
def polygon : List HalfPlane → Set Plane | [] => Set.univ | h :: L => h.cl ∩ polygon L   -- L8859
theorem mem_polygon_iff (L : List HalfPlane) (q : Plane) : q ∈ polygon L ↔ ∀ h ∈ L, h.f q ≤ h.b            -- L8863
theorem mem_interior_polygon_iff (L : List HalfPlane) (q : Plane) :
    q ∈ interior (polygon L) ↔ ∀ h ∈ L, h.f q < h.b                                                          -- L8879
theorem mem_frontier_polygon_iff (L : List HalfPlane) (q : Plane) :
    q ∈ frontier (polygon L) ↔ q ∈ polygon L ∧ ∃ h ∈ L, h.f q = h.b                                          -- L8895
theorem isDisc_polygon (L : List HalfPlane) {a b c d : ℝ}
    (hbox : ∀ q ∈ polygon L, a ≤ q.1 ∧ q.1 ≤ b ∧ c ≤ q.2 ∧ q.2 ≤ d)
    (hint : ∃ q : Plane, ∀ h ∈ L, h.f q < h.b) : IsDisc (polygon L)                                          -- L8920
def HalfPlane.xle (b : ℝ) : HalfPlane      -- {x ≤ b}
def HalfPlane.xge (a : ℝ) : HalfPlane      -- {a ≤ x}
def HalfPlane.yle (d : ℝ) : HalfPlane      -- {y ≤ d}
def HalfPlane.yge (c : ℝ) : HalfPlane      -- {c ≤ y}
def HalfPlane.below (c s : ℝ) : HalfPlane  -- {y ≤ c + s x}
def HalfPlane.above (c s : ℝ) : HalfPlane  -- {c + s x ≤ y}                                                -- L8935-8945
@[simp] theorem HalfPlane.f_xle (b : ℝ) (q : Plane) : (HalfPlane.xle b).f q = q.1;   @[simp] theorem HalfPlane.b_xle (b : ℝ) : (HalfPlane.xle b).b = b
@[simp] theorem HalfPlane.f_xge (a : ℝ) (q : Plane) : (HalfPlane.xge a).f q = -q.1;  @[simp] theorem HalfPlane.b_xge (a : ℝ) : (HalfPlane.xge a).b = -a
@[simp] theorem HalfPlane.f_yle (d : ℝ) (q : Plane) : (HalfPlane.yle d).f q = q.2;   @[simp] theorem HalfPlane.b_yle (d : ℝ) : (HalfPlane.yle d).b = d
@[simp] theorem HalfPlane.f_yge (c : ℝ) (q : Plane) : (HalfPlane.yge c).f q = -q.2;  @[simp] theorem HalfPlane.b_yge (c : ℝ) : (HalfPlane.yge c).b = -c
@[simp] theorem HalfPlane.f_below (c s : ℝ) (q : Plane) : (HalfPlane.below c s).f q = -s * q.1 + q.2;  @[simp] theorem HalfPlane.b_below (c s : ℝ) : (HalfPlane.below c s).b = c
@[simp] theorem HalfPlane.f_above (c s : ℝ) (q : Plane) : (HalfPlane.above c s).f q = s * q.1 - q.2;   @[simp] theorem HalfPlane.b_above (c s : ℝ) : (HalfPlane.above c s).b = -c   -- L8947-8960
```
Also: `interior_polygon`, `isClosed_polygon`, `convex_polygon`, `interior_polygon_subset`, `mem_frontier_polygon_of`,
`notMem_interior_of_mem_frontier`, `mem_of_mem_frontier`, `HalfPlane.interior_cl`, `HalfPlane.mem_interior_cl_iff`.
Recipe (U4 report §2.1): `U := polygon [xge (pl.x k), xle (pl.x (k+3)), yge …, yle …, above …]`; concrete
membership = `simp [mem_polygon_iff, mem_interior_polygon_iff, List.mem_cons, forall_eq_or_imp]` + `linarith`.

### 6.2 B. Segments (section `Segments`, L8969-9095; `variable (L : List HalfPlane)`, then `{L}`)

```lean
abbrev segPt (p₀ p₁ : Plane) (t : ℝ) : Plane := p₀ + t • (p₁ - p₀)                                          -- L8969
@[simp] segPt_zero : segPt p₀ p₁ 0 = p₀;  @[simp] segPt_one : segPt p₀ p₁ 1 = p₁;  segPt_fst; segPt_snd; segPt_reverse
theorem segPt_fst_injective {p₀ p₁ : Plane} (h : p₀.1 ≠ p₁.1) {t t' : ℝ}
    (he : (segPt p₀ p₁ t).1 = (segPt p₀ p₁ t').1) : t = t'                                                   -- L8979
theorem segPt_injective {p₀ p₁ : Plane} (h : p₀ ≠ p₁) : Function.Injective (segPt p₀ p₁)                   -- L8987
def SegIn (p₀ p₁ : Plane) : Prop := ∀ h ∈ L, h.f p₀ ≤ h.b ∧ h.f p₁ ≤ h.b ∧ (h.f p₀ < h.b ∨ h.f p₁ < h.b)   -- L9006
def SegOut (p₀ p₁ : Plane) : Prop := ∃ h ∈ L, h.b ≤ h.f p₀ ∧ h.b ≤ h.f p₁ ∧ (h.b < h.f p₀ ∨ h.b < h.f p₁)  -- L9010
theorem SegIn.symm (h : SegIn L p₀ p₁) : SegIn L p₁ p₀;   theorem SegOut.symm (h : SegOut L p₀ p₁) : SegOut L p₁ p₀
theorem SegIn.mem_interior {p₀ p₁ : Plane} (h : SegIn L p₀ p₁) {t : ℝ} (h0 : 0 < t) (h1 : t < 1) :
    segPt p₀ p₁ t ∈ interior (polygon L)                                                                     -- L9021
theorem SegIn.left_mem {p₀ p₁ : Plane} (h : SegIn L p₀ p₁) : p₀ ∈ polygon L                                 -- L9029
theorem SegIn.right_mem {p₀ p₁ : Plane} (h : SegIn L p₀ p₁) : p₁ ∈ polygon L                                -- L9032
theorem SegIn.mem {p₀ p₁ : Plane} (h : SegIn L p₀ p₁) {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) : segPt p₀ p₁ t ∈ polygon L   -- L9035
theorem SegOut.notMem {p₀ p₁ : Plane} (h : SegOut L p₀ p₁) {t : ℝ} (h0 : 0 < t) (h1 : t < 1) : segPt p₀ p₁ t ∉ polygon L   -- L9043
theorem SegOut.left_notMem_interior {p₀ p₁ : Plane} (h : SegOut L p₀ p₁) : p₀ ∉ interior (polygon L)       -- L9052
theorem SegOut.right_notMem_interior {p₀ p₁ : Plane} (h : SegOut L p₀ p₁) : p₁ ∉ interior (polygon L)      -- L9058
theorem SegOut.notMem_interior {p₀ p₁ : Plane} (h : SegOut L p₀ p₁) {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    segPt p₀ p₁ t ∉ interior (polygon L)                                                                     -- L9061
theorem SegOut.eq_end_of_mem {p₀ p₁ : Plane} (h : SegOut L p₀ p₁) {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1)
    (hm : segPt p₀ p₁ t ∈ polygon L) : t = 0 ∨ t = 1                                                        -- L9070
theorem not_segIn_of_segOut {p₀ p₁ : Plane} (h : SegOut L p₀ p₁) : ¬ SegIn L p₀ p₁                          -- L9077
theorem segIn_of_interior_left {p₀ p₁ : Plane} (h0 : p₀ ∈ interior (polygon L)) (h1 : p₁ ∈ polygon L) : SegIn L p₀ p₁    -- L9081
theorem segIn_of_interior_right {p₀ p₁ : Plane} (h0 : p₀ ∈ polygon L) (h1 : p₁ ∈ interior (polygon L)) : SegIn L p₀ p₁   -- L9087
theorem segOut_of {p₀ p₁ : Plane} (h : HalfPlane) (hh : h ∈ L) (h0 : h.b ≤ h.f p₀) (h1 : h.b ≤ h.f p₁)
    (hs : h.b < h.f p₀ ∨ h.b < h.f p₁) : SegOut L p₀ p₁                                                     -- L9091
theorem segOut_of_lt {p₀ p₁ : Plane} (h : HalfPlane) (hh : h ∈ L) (h0 : h.b < h.f p₀) (h1 : h.b < h.f p₁) : SegOut L p₀ p₁   -- L9095
```

### 6.3 C. The moved slot diagram (section `SlotDiagram`, L9107-9273; `variable (pl : Placement) {W : Word} (hW : W.Closed) (hne : W ≠ [])`, then `(mv : Slot W → Plane)`)

```lean
def vertsOf (mv : Slot W → Plane) : (shadowOf pl hW hne).Vertices := fun i j => mv (idxEquiv hW ⟨i, j⟩)     -- L9107
abbrev shadowMv (mv : Slot W → Plane) : Shadow := (shadowOf pl hW hne).withVertices (vertsOf pl hW hne mv)  -- L9111
theorem vertsOf_pt : vertsOf pl hW hne (fun u => pt pl W u.1) = (shadowOf pl hW hne).vertices              -- L9114 (rfl)
abbrev slotMv (s : (shadowMv pl hW hne mv).Strand) : Slot W                                                 -- L9121  (= idxEquiv hW s)
theorem tail_mv (s) : (shadowMv pl hW hne mv).tail s = mv (slotMv pl hW hne mv s)                           -- L9132
theorem head_mv (s) : (shadowMv pl hW hne mv).head s = mv (next hW (slotMv pl hW hne mv s))                 -- L9135
theorem dir_mv (s) : (shadowMv pl hW hne mv).dir s = mv (next hW (slotMv pl hW hne mv s)) - mv (slotMv pl hW hne mv s)   -- L9141
theorem eval_mv (p : (shadowMv pl hW hne mv).Pt) :
    (shadowMv pl hW hne mv).eval p = segPt (mv (slotPtMv pl hW hne mv p)) (mv (next hW (slotPtMv pl hW hne mv p))) p.2.2.val   -- L9156
theorem mem_seg_mv_iff (s) (q : Plane) : q ∈ (shadowMv pl hW hne mv).seg s ↔
      ∃ t, 0 ≤ t ∧ t ≤ 1 ∧ q = segPt (mv (slotMv pl hW hne mv s)) (mv (next hW (slotMv pl hW hne mv s))) t  -- L9161
theorem mem_interior_mv_iff (s) (q : Plane) : q ∈ (shadowMv pl hW hne mv).interior s ↔
      ∃ t, 0 < t ∧ t < 1 ∧ q = segPt (mv (slotMv pl hW hne mv s)) (mv (next hW (slotMv pl hW hne mv s))) t  -- L9170
theorem adjacent_mv_iff (s t) : (shadowMv pl hW hne mv).Adjacent s t ↔
      slotMv pl hW hne mv t = slotMv pl hW hne mv s ∨ slotMv pl hW hne mv t = next hW (slotMv pl hW hne mv s) ∨
        slotMv pl hW hne mv t = prev hW (slotMv pl hW hne mv s)                                              -- L9180
abbrev strandMv (u : Slot W) : (shadowMv pl hW hne mv).Strand                                              -- L9192  (= U2.stStrand pl hW hne (vertsOf …) u)
abbrev travMv (u : Slot W) (t : Set.Ico (0 : ℝ) 1) : (shadowMv pl hW hne mv).Pt                             -- L9195
theorem eval_travMv (u : Slot W) (t : Set.Ico (0 : ℝ) 1) :
    (shadowMv pl hW hne mv).eval (travMv pl hW hne mv u t) = segPt (mv u) (mv (next hW u)) t.val           -- L9201
abbrev vertexPt (u : Slot W) : (shadowMv pl hW hne mv).Pt                                                   -- L9213  (= travMv … u 0)
theorem eval_vertexPt (u : Slot W) : (shadowMv pl hW hne mv).eval (vertexPt pl hW hne mv u) = mv u          -- L9215
def Unch (u : Slot W) : Prop := mv u = pt pl W u.1 ∧ mv (next hW u) = pt pl W (next hW u).1                 -- L9219
theorem unch_pt (u : Slot W) : Unch pl hW (fun u => pt pl W u.1) u
theorem segPt_pt (u : Slot W) (t : ℝ) :
    segPt (pt pl W u.1) (pt pl W (next hW u).1) t = piecePt pl u (if xsign u then t else 1 - t)             -- L9233
theorem segPt_unch {u : Slot W} (hu : Unch pl hW mv u) (t : ℝ) :
    segPt (mv u) (mv (next hW u)) t = piecePt pl u (if xsign u then t else 1 - t)                           -- L9241
theorem pt_fst_ne_pt_next_fst (u : Slot W) : (pt pl W u.1).1 ≠ (pt pl W (next hW u).1).1                    -- L9247
theorem realizeAt_diagram_eq : (realizeAt pl hW hne).diagram =
      U2.mkDiagram pl hW hne (vertsOf pl hW hne (fun u => pt pl W u.1)) (generic pl hW hne)
        (realizeAt pl hW hne).overStrand (realizeAt pl hW hne).overStrand_mem                               -- L9267 (rfl)
theorem realizeAt_data' : U2.SlotDiagramData pl hW hne (vertsOf pl hW hne (fun u => pt pl W u.1)) (generic pl hW hne)
      (realizeAt pl hW hne).overStrand (realizeAt pl hW hne).overStrand_mem (fun _ => True)                 -- L9273
```
Also: `slotMv_stStrand`, `stStrand_slotMv`, `slotMv_injective`, `edgePoint_mv`, `slotPtMv`, `slotPtMv_travMv`,
`travMv_slotPtMv`, `incidentTail_mv_of`, `shadowMv_pt`, `segPt_piecePt`, `pt_fst_mem`, `pt_next_fst_mem`.

### 6.4 D. Classification and `Clean` (section `Classify`, L9287-9367; `variable (L : List HalfPlane) (pl : Placement) {W : Word} (hW : W.Closed) (hne : W ≠ []) (mv : Slot W → Plane)`)

```lean
def PieceIn (u : Slot W) : Prop := SegIn L (mv u) (mv (next hW u))                                           -- L9287   (PieceIn L hW mv u)
def PieceOut (u : Slot W) : Prop := SegOut L (mv u) (mv (next hW u))                                         -- L9290   (PieceOut L hW mv u)
theorem not_pieceIn_of_pieceOut {u : Slot W} (h : PieceOut L hW mv u) : ¬ PieceIn L hW mv u
theorem frontier_injOn_mv (hinj : Function.Injective mv) (hcl : ∀ u, PieceIn L hW mv u ∨ PieceOut L hW mv u) :
    Set.InjOn (shadowMv pl hW hne mv).eval {p | (shadowMv pl hW hne mv).eval p ∈ frontier (polygon L)}       -- L9310
def ExitsMv : Prop := ∀ i : Fin (numComp hW), ∃ (j : ZMod (period hW (rep hW i))) (t : Set.Ico (0 : ℝ) 1),
    segPt (mv (idxEquiv hW ⟨i, j⟩)) (mv (next hW (idxEquiv hW ⟨i, j⟩))) t.val ∉ polygon L                    -- L9323   (ExitsMv L hW mv)
theorem exitsMv_of_sameCycle (hex : ∀ u : Slot W, ∃ v : Slot W, (nextPerm hW).SameCycle u v ∧ PieceOut L hW mv v) :
    ExitsMv L hW mv                                                                                          -- L9328
theorem clean_mv (hinj : Function.Injective mv) (hcl : ∀ u, PieceIn L hW mv u ∨ PieceOut L hW mv u)
    (hex : ExitsMv L hW mv) (hgen : (shadowMv pl hW hne mv).Generic)
    (ov : (shadowMv pl hW hne mv).Crossing → (shadowMv pl hW hne mv).Strand) (hov : ∀ x, ov x ∈ x.val) :
    Clean (polygon L) (U2.mkDiagram pl hW hne (vertsOf pl hW hne mv) hgen ov hov)                           -- L9359
theorem pieceOut_of_extCol {a b : ℕ} (ha : HalfPlane.xge (pl.x a) ∈ L) (hb : HalfPlane.xle (pl.x b) ∈ L)
    {u : Slot W} (hu : Unch pl hW mv u) (hcol : colOf u + 1 ≤ a ∨ b ≤ colOf u) : PieceOut L hW mv u        -- L9367
```

### 6.5 E. Genericity and the crossing set (section `Generic`, L9401-9828; `variable (pl : Placement) {W : Word} (hW : W.Closed) (hne : W ≠ []) (mv : Slot W → Plane) (K : ℕ → Prop)`)

```lean
def SigmaMeet (u v : Slot W) : Prop :=
  Unch pl hW mv u ∧ Unch pl hW mv v ∧ colOf u = colOf v ∧ K (colOf u) ∧
    ∃ m, letterAt W (colOf u) = .σ m ∧
      ((shapeOf u = .pass m (m + 1) ∧ shapeOf v = .pass (m + 1) m) ∨
       (shapeOf u = .pass (m + 1) m ∧ shapeOf v = .pass m (m + 1)))                                          -- L9401
def MeetSpec (u v : Slot W) : Prop :=
  ∀ τ τ' : ℝ, 0 ≤ τ → τ ≤ 1 → 0 ≤ τ' → τ' ≤ 1 →
    segPt (mv u) (mv (next hW u)) τ = segPt (mv v) (mv (next hW v)) τ' →
    (u = v ∧ τ = τ') ∨ (v = next hW u ∧ τ = 1 ∧ τ' = 0) ∨ (u = next hW v ∧ τ = 0 ∧ τ' = 1) ∨
    (τ = 1 / 2 ∧ τ' = 1 / 2 ∧ SigmaMeet pl hW mv K u v)                                                      -- L9417   (MeetSpec pl hW mv K u v)
theorem SigmaMeet.symm; theorem MeetSpec.symm
theorem meetSpec_of_col_ne (hinj : Function.Injective mv) (hx : ∀ u, (mv u).1 = (pt pl W u.1).1)
    {u v : Slot W} (hne' : colOf u ≠ colOf v) : MeetSpec pl hW mv K u v                                     -- L9494
theorem meetSpec_of_unch {u v : Slot W} (hu : Unch pl hW mv u) (hv : Unch pl hW mv v)
    (hK : ∀ (k m : ℕ) (hk : k < W.length) (hℓ : letterAt W k = .σ m),
      Unch pl hW mv (σSlotA hW hk hℓ) → Unch pl hW mv (σSlotB hW hk hℓ) → K k) :
    MeetSpec pl hW mv K u v                                                                                  -- L9522
structure GenericData : Prop where                                                                           -- L9562   (GenericData pl hW mv K)
  inj : Function.Injective mv
  xcoord : ∀ u, (mv u).1 = (pt pl W u.1).1
  meet : ∀ u v, u ≠ v → colOf u = colOf v → MeetSpec pl hW mv K u v
theorem GenericData.meetSpec (d : GenericData pl hW mv K) {u v : Slot W} (huv : u ≠ v) : MeetSpec pl hW mv K u v
theorem generic_of (d : GenericData pl hW mv K) : (shadowMv pl hW hne mv).Generic                           -- L9598
def ovMv (x : (shadowMv pl hW hne mv).Crossing) : (shadowMv pl hW hne mv).Strand                            -- L9728   (the descending strand)
theorem ovMv_mem (x : (shadowMv pl hW hne mv).Crossing) : ovMv pl hW hne mv x ∈ x.val                        -- L9732
theorem isCrossing_mv_iff (d : GenericData pl hW mv K)
    (hK : ∀ (k m : ℕ) (hk : k < W.length) (hℓ : letterAt W k = .σ m),
      K k ↔ Unch pl hW mv (σSlotA hW hk hℓ) ∧ Unch pl hW mv (σSlotB hW hk hℓ))
    (x : Finset (shadowMv pl hW hne mv).Strand) :
    (shadowMv pl hW hne mv).IsCrossing x ↔
      ∃ (k m : ℕ) (hk : k < W.length) (hℓ : letterAt W k = .σ m), K k ∧ x = U2.σpair pl hW hne (vertsOf pl hW hne mv) hk hℓ   -- L9756
theorem slotDiagramData_of (d : GenericData pl hW mv K)
    (hK : ∀ (k m : ℕ) (hk : k < W.length) (hℓ : letterAt W k = .σ m),
      K k ↔ Unch pl hW mv (σSlotA hW hk hℓ) ∧ Unch pl hW mv (σSlotB hW hk hℓ)) :
    U2.SlotDiagramData pl hW hne (vertsOf pl hW hne mv) (generic_of pl hW hne mv K d) (ovMv pl hW hne mv)
      (ovMv_mem pl hW hne mv) K                                                                              -- L9828
```
Also: `affine_eq_max/min`, `meetSpec_of_col_lt`, `piecePt_param_injective`, `segPt_unch_eq_pt`,
`pt_prev_fst_eq_pt_next_fst_of_cusp`, `ovMv_eq_of_σpair`, `K_of_σpair`.
U6's moved diagram: `D := U2.mkDiagram .std hW hne (vertsOf .std hW hne mv) (generic_of … d) (ovMv …) (ovMv_mem …)`;
its record isomorphism with `realize W'` is U2's `vertexMovedRecordIso' … (slotDiagramData_of … d hK) …` with
`K := ExtCol X P` (MERGE1_REPORT §4.5).

### 6.6 F. The move match (section `Match`, L9884-10373; `variable (L : List HalfPlane) (pl : Placement) {W W' : Word} (hW : W.Closed) (hW' : W'.Closed) (hne : W ≠ []) (hne' : W' ≠ []) (mv : Slot W → Plane) (mv' : Slot W' → Plane) (ψ : Slot W ≃ Slot W')`; from L10001 `variable {L hW hW' mv mv' ψ} (M : MatchData L hW hW' mv mv' ψ)`)

```lean
structure MatchData : Prop where                                                                             -- L9884   (MatchData L hW hW' mv mv' ψ)
  cl : ∀ u, PieceIn L hW mv u ∨ PieceOut L hW mv u
  cl' : ∀ u', PieceIn L hW' mv' u' ∨ PieceOut L hW' mv' u'
  out_iff : ∀ u, PieceOut L hW mv u ↔ PieceOut L hW' mv' (ψ u)
  pt_eq : ∀ u, mv u ∉ interior (polygon L) → mv' (ψ u) = mv u
  int_iff : ∀ u, mv u ∈ interior (polygon L) ↔ mv' (ψ u) ∈ interior (polygon L)
  next_eq : ∀ u, PieceOut L hW mv u → ψ (next hW u) = next hW' (ψ u)
def ψStr (s : (shadowMv pl hW hne mv).Strand) : (shadowMv pl hW' hne' mv').Strand                           -- L9893
def ψPt (p : (shadowMv pl hW hne mv).Pt) : (shadowMv pl hW' hne' mv').Pt                                    -- L9915   (ψPt pl hW hW' hne hne' mv mv' ψ p)
def ψFin (x : Finset (shadowMv pl hW hne mv).Strand) : Finset (shadowMv pl hW' hne' mv').Strand             -- L9942
theorem crossingPoint_notMem_interior_iff (hcl : ∀ u, PieceIn L hW mv u ∨ PieceOut L hW mv u)
    (hgen : (shadowMv pl hW hne mv).Generic) (x : (shadowMv pl hW hne mv).Crossing)
    {s : (shadowMv pl hW hne mv).Strand} (hs : s ∈ x.val) :
    (shadowMv pl hW hne mv).crossingPoint x ∉ interior (polygon L) ↔ PieceOut L hW mv (slotMv pl hW hne mv s)   -- L9977
def SigmaCorr (K K' : ℕ → Prop) : Prop :=                                                                    -- L9995   (SigmaCorr L hW hW' mv ψ K K')
  ∀ (k m : ℕ) (hk : k < W.length) (hℓ : letterAt W k = .σ m), K k → PieceOut L hW mv (σSlotA hW hk hℓ) →
    ∃ (k' m' : ℕ) (hk' : k' < W'.length) (hℓ' : letterAt W' k' = .σ m'), K' k' ∧
      ψ (σSlotA hW hk hℓ) = σSlotA hW' hk' hℓ' ∧ ψ (σSlotB hW hk hℓ) = σSlotB hW' hk' hℓ'
theorem MatchData.eval_ψPt_of_outside (p : (shadowMv pl hW hne mv).Pt)
    (hp : (shadowMv pl hW hne mv).eval p ∉ interior (polygon L)) :
    (shadowMv pl hW' hne' mv').eval (ψPt pl hW hW' hne hne' mv mv' ψ p) = (shadowMv pl hW hne mv).eval p    -- L10058
def MatchData.outEquiv : (shadowMv pl hW hne mv).Outside (polygon L) ≃ (shadowMv pl hW' hne' mv').Outside (polygon L)   -- L10074  (M.outEquiv pl hne hne')
theorem MatchData.outEquiv_apply (p) : (M.outEquiv pl hne hne' p).1 = ψPt pl hW hW' hne hne' mv mv' ψ p.1   -- L10083
theorem MatchData.dir_ψPt (p) (hp : (shadowMv pl hW hne mv).eval p ∉ polygon L) :
    (shadowMv pl hW' hne' mv').dir ((shadowMv pl hW' hne' mv').strandOf (ψPt pl hW hW' hne hne' mv mv' ψ p)) =
      (shadowMv pl hW hne mv).dir ((shadowMv pl hW hne mv).strandOf p)                                       -- L10093
theorem MatchData.dir_before_ψPt (p) (hp : (shadowMv pl hW hne mv).eval p ∉ polygon L) :
    (shadowMv pl hW' hne' mv').dir ((shadowMv pl hW' hne' mv').strandBefore (ψPt pl hW hW' hne hne' mv mv' ψ p)) =
      (shadowMv pl hW hne mv).dir ((shadowMv pl hW hne mv).strandBefore p)                                   -- L10106
-- variable (hgen : (shadowMv pl hW hne mv).Generic) (ov : … .Crossing → … .Strand) (hov : ∀ x, ov x ∈ x.val) (K : ℕ → Prop)
--   (data : U2.SlotDiagramData pl hW hne (vertsOf pl hW hne mv) hgen ov hov K) (hgen') (ov') (hov') (K')
--   (data' : U2.SlotDiagramData pl hW' hne' (vertsOf pl hW' hne' mv') hgen' ov' hov' K') (hσ : SigmaCorr L hW hW' mv ψ K K')
def MatchData.crossMap : (mkDiagram …).OuterCrossing (polygon L) → (mkDiagram' …).OuterCrossing (polygon L)  -- (M.crossMap pl hne hne' hgen ov hov K data hgen' ov' hov' K' data' hσ)
theorem MatchData.crossingPoint_crossMap (x : (U2.mkDiagram pl hW hne (vertsOf pl hW hne mv) hgen ov hov).OuterCrossing (polygon L)) :
    (shadowMv pl hW' hne' mv').crossingPoint (M.crossMap pl hne hne' hgen ov hov K data hgen' ov' hov' K' data' hσ x).1 =
      (shadowMv pl hW hne mv).crossingPoint x.1                                                              -- L10216
theorem MatchData.crossingParam_crossMap (x) {u : Slot W} (hu : PieceOut L hW mv u) (hs : strandMv pl hW hne mv u ∈ x.1.val)
    (hs' : strandMv pl hW' hne' mv' (ψ u) ∈ (M.crossMap … x).1.val) :
    (U2.mkDiagram pl hW' hne' (vertsOf pl hW' hne' mv') hgen' ov' hov').crossingParam _ hs' =
      (U2.mkDiagram pl hW hne (vertsOf pl hW hne mv) hgen ov hov).crossingParam x.1 hs                       -- L10234
theorem MatchData.ψPt_over (x) : ψPt pl hW hW' hne hne' mv mv' ψ ((mkDiagram …).visitPt ((mkDiagram …).overVisit x.1)) =
      (mkDiagram' …).visitPt ((mkDiagram' …).overVisit (M.crossMap … x).1)                                    -- L10269
theorem MatchData.ψPt_under (x) : … underVisit …                                                             -- L10300
-- variable (hσ' : SigmaCorr L hW' hW mv' ψ.symm K' K)
def MatchData.crossEquiv : (mkDiagram …).OuterCrossing (polygon L) ≃ (mkDiagram' …).OuterCrossing (polygon L)  -- L10351
-- variable (e : Fin (numComp hW) ≃ Fin (numComp hW')) (he : ∀ u : Slot W, mv u ∉ interior (polygon L) → U2.slotComp hW' (ψ u) = e (U2.slotComp hW u))
def MatchData.moveMatch :
    MoveMatch (polygon L) (U2.mkDiagram pl hW hne (vertsOf pl hW hne mv) hgen ov hov)
      (U2.mkDiagram pl hW' hne' (vertsOf pl hW' hne' mv') hgen' ov' hov')                                     -- L10373
-- call: M.moveMatch pl hne hne' hgen ov hov K data hgen' ov' hov' K' data' hσ hσ' e he
```
Also: `slotMv_ψStr`, `ψStr_symm_ψStr`, `ψStr_injective`, `ψStr_strandMv`, `ψPt_travMv`, `slotPtMv_ψPt`, `ψPt_param`,
`ψPt_symm_ψPt`, `eval_ψPt`, `ψFin_pair`, `ψFin_symm_ψFin`, `ψFin_σpair`, `slotMv_pred`, `pieceOut_of_notMem`,
`MatchData.symm/mv_eq_of_out/mv_next_eq_of_out/segPt_eq_of_out/pieceIn_of_not_out/pieceIn'_of_not_out/outside_iff/
pieceOut_of_eval_notMem/crossMap_val/seg_eq_of_out/outer_spec`, `pt_ext'`.
Instantiations (U4 report §2.5): **U6** — `W' = W`, `ψ = Equiv.refl _`, `mv' = fun u => pt pl W u.1`, `e = Equiv.refl _`,
`he := fun _ _ => rfl`, `data' := realizeAt_data' …` with `K' := fun _ => True`; the result is
`MoveMatch U D (realizeAt pl hW hne).diagram` by `realizeAt_diagram_eq` (rfl) after `rw [realize_eq_realizeAt]`.
**U5** — `mv = pt`, `mv' = pt'`, `ψ := sameSlotEquiv W W' h` (§6.9), `K = K' = fun _ => True`, `data = data' = realizeAt_data'`;
U5 must build the component bijection `e` itself (U4 report §4.3).

### 6.7 G. The arcs (section `Arcs`, L10500-10777; `variable (L : List HalfPlane) (pl : Placement) {W : Word} (hW : W.Closed) (hne : W ≠ []) (mv : Slot W → Plane)`; in `namespace Chain`: `variable (c : Chain W)`, then `{c} {L hW mv}` for the `IsChain.*` lemmas)

```lean
structure Chain (W : Word) where u₀ : Slot W; n : ℕ; hn : 0 < n                                            -- L10500
def Chain.slot (j : ℕ) : Slot W                                                                              -- L10510  (c.slot hW j = (next hW)^[j] c.u₀)
@[simp] theorem Chain.slot_zero : c.slot hW 0 = c.u₀                                                         -- L10512
theorem Chain.slot_succ (j : ℕ) : c.slot hW (j + 1) = next hW (c.slot hW j)                                  -- L10514
def Chain.toArc : (shadowMv pl hW hne mv).Arc                                                                -- L10530  (c.toArc pl hW hne mv)
theorem Chain.startPt_eq : (c.toArc pl hW hne mv).startPt = vertexPt pl hW hne mv c.u₀                       -- L10536
theorem Chain.stopPt_eq : (c.toArc pl hW hne mv).stopPt = vertexPt pl hW hne mv (c.slot hW c.n)              -- L10538
theorem Chain.eval_startPt : (shadowMv pl hW hne mv).eval (c.toArc pl hW hne mv).startPt = mv c.u₀           -- L10542
theorem Chain.eval_stopPt : (shadowMv pl hW hne mv).eval (c.toArc pl hW hne mv).stopPt = mv (c.slot hW c.n)  -- L10545
theorem Chain.toArc_ne {c c' : Chain W} (h : c.u₀ ≠ c'.u₀) : c.toArc pl hW hne mv ≠ c'.toArc pl hW hne mv    -- L10549
structure Chain.IsChain : Prop where                                                                         -- L10557  (c.IsChain L hW mv)
  pieceIn : ∀ j, j < c.n → PieceIn L hW mv (c.slot hW j)
  vertex_interior : ∀ j, 0 < j → j < c.n → mv (c.slot hW j) ∈ interior (polygon L)
  out_prev : PieceOut L hW mv (prev hW c.u₀)
  out_stop : PieceOut L hW mv (c.slot hW c.n)
theorem Chain.travMv_slot_eq (c : Chain W) (j : ℕ) (t : Set.Ico (0 : ℝ) 1) :
    travMv pl hW hne mv (c.slot hW j) t = ⟨(c.toArc pl hW hne mv).i, ((c.toArc pl hW hne mv).start.1 + (j : ZMod _), t)⟩   -- L10597
theorem Chain.IsChain.n_lt_period (h : c.IsChain L hW mv) : c.n < period hW c.u₀                             -- L10627
theorem Chain.IsChain.inner_iff (h : c.IsChain L hW mv) (p : (shadowMv pl hW hne mv).Pt) :
    (c.toArc pl hW hne mv).Inner p ↔
      ∃ j, j < c.n ∧ ∃ t : Set.Ico (0 : ℝ) 1, p = travMv pl hW hne mv (c.slot hW j) t ∧ (0 < j ∨ 0 < t.val)  -- L10646  (h.inner_iff pl hne p)
theorem Chain.IsChain.mem_iff (h : c.IsChain L hW mv) (p : (shadowMv pl hW hne mv).Pt) :
    (c.toArc pl hW hne mv).Mem p ↔
      (∃ j, j < c.n ∧ ∃ t : Set.Ico (0 : ℝ) 1, p = travMv pl hW hne mv (c.slot hW j) t) ∨
        p = vertexPt pl hW hne mv (c.slot hW c.n)                                                            -- L10671
theorem Chain.IsChain.mem_of_slot (h : c.IsChain L hW mv) {j : ℕ} (hj : j < c.n) (t : Set.Ico (0 : ℝ) 1) :
    (c.toArc pl hW hne mv).Mem (travMv pl hW hne mv (c.slot hW j) t)                                         -- L10694
theorem Chain.IsChain.inner_of_slot (h : c.IsChain L hW mv) {j : ℕ} (hj : j < c.n) (t : Set.Ico (0 : ℝ) 1)
    (ht : 0 < t.val) : (c.toArc pl hW hne mv).Inner (travMv pl hW hne mv (c.slot hW j) t)                   -- L10699
theorem Chain.IsChain.before_iff (h : c.IsChain L hW mv) {j j' : ℕ} (hj : j < c.n) (hj' : j' < c.n)
    (t t' : Set.Ico (0 : ℝ) 1) (hp : 0 < j ∨ 0 < t.val) (hq : 0 < j' ∨ 0 < t'.val) :
    (c.toArc pl hW hne mv).Before (travMv pl hW hne mv (c.slot hW j) t) (travMv pl hW hne mv (c.slot hW j') t') ↔
      (j < j' ∨ (j = j' ∧ t.val < t'.val))                                                                   -- L10704
theorem Chain.IsChain.isArc (h : c.IsChain L hW mv) : (shadowMv pl hW hne mv).IsArc (polygon L) (c.toArc pl hW hne mv)   -- L10739  (h.isArc pl hne)
def arcsOf (cs : List (Chain W)) : Set (shadowMv pl hW hne mv).Arc                                          -- L10768  ({a | ∃ c ∈ cs, a = c.toArc pl hW hne mv})
theorem mem_arcsOf (cs : List (Chain W)) (c : Chain W) (hc : c ∈ cs) : c.toArc pl hW hne mv ∈ arcsOf pl hW hne mv cs   -- L10771
theorem arcCover_of (cs : List (Chain W)) (hall : ∀ c ∈ cs, c.IsChain L hW mv)
    (hcl : ∀ u, PieceIn L hW mv u ∨ PieceOut L hW mv u)
    (hcover : ∀ u, PieceIn L hW mv u → ∃ c ∈ cs, ∃ j, j < c.n ∧ c.slot hW j = u)
    (hdisj : ∀ c ∈ cs, ∀ c' ∈ cs, c ≠ c' → ∀ j, j < c.n → ∀ j', j' < c'.n → c.slot hW j ≠ c'.slot hW j')
    (htouch : ∀ u, PieceOut L hW mv u → mv u ∈ polygon L → PieceIn L hW mv (prev hW u)) :
    (shadowMv pl hW hne mv).ArcCover (polygon L) (arcsOf pl hW hne mv cs)                                    -- L10777
```
Also: `Chain.strandMv_slot`, `Chain.toArc_i`, `Chain.period_eq`, `Chain.k_eq`, `Chain.key_start/key_stop/key_pt`,
`IsChain.entry_notMem_interior/stop_notMem_interior/entry_mem/stop_mem/entry_frontier/stop_frontier/slot_mem`,
`nat_lt_add_iff`, `nat_add_lt_iff`, `nat_add_lt_add_iff`, `cycBetween_key(')`, `cycBetween_key2(')`.
Site fields (U4 report §2.6): `cover := arcCover_of [a, b, c] …` after rewriting `{a.toArc, b.toArc, c.toArc}` as
`arcsOf … [a, b, c]`; `ab := Chain.toArc_ne …`; `OverOn`/`BeforeOn` via `IsChain.mem_of_slot`/`before_iff`
(crossing parameters are in `(0,1)`: `Diagram.crossingParam_pos/lt_one`; `1/2` on the realization,
`crossingParam_eq_half`); `inner_iff`/`no_inner` via `crossingPoint_notMem_interior_iff` + `isCrossing_mv_iff`.

### 6.8 H. Exits (section `Exits`, L10870-10962; `variable {W : Word} (hW : W.Closed)`)

```lean
theorem exists_cusps_of_no_ext (a b : ℕ) (u : Slot W)
    (h : ∀ v, (nextPerm hW).SameCycle u v → a ≤ colOf v ∧ colOf v < b) :
    (∃ v, (nextPerm hW).SameCycle u v ∧ v.1.2 = 0 ∧ (∃ m, letterAt W v.1.1 = .r m) ∧ a ≤ v.1.1 ∧ v.1.1 < b) ∧
    (∃ v, (nextPerm hW).SameCycle u v ∧ v.1.2 = 0 ∧ (∃ m d, letterAt W v.1.1 = .l m d) ∧ a ≤ v.1.1 ∧ v.1.1 < b)   -- L10870
theorem exists_ext_of_no_r (a b : ℕ) (hno : ∀ k, a ≤ k → k < b → ∀ m, letterAt W k ≠ .r m) (u : Slot W) :
    ∃ v, (nextPerm hW).SameCycle u v ∧ (colOf v + 1 ≤ a ∨ b ≤ colOf v)                                       -- L10939
theorem exists_ext_of_no_l (a b : ℕ) (hno : ∀ k, a ≤ k → k < b → ∀ m d, letterAt W k ≠ .l m d) (u : Slot W) :
    ∃ v, (nextPerm hW).SameCycle u v ∧ (colOf v + 1 ≤ a ∨ b ≤ colOf v)                                       -- L10950
theorem exitsMv_of_ext (L : List HalfPlane) (pl : Placement) (mv : Slot W → Plane) {a b : ℕ}
    (ha : HalfPlane.xge (pl.x a) ∈ L) (hb : HalfPlane.xle (pl.x b) ∈ L)
    (hunch : ∀ v, (colOf v + 1 ≤ a ∨ b ≤ colOf v) → Unch pl hW mv v)
    (hex : ∀ u : Slot W, ∃ v, (nextPerm hW).SameCycle u v ∧ (colOf v + 1 ≤ a ∨ b ≤ colOf v)) :
    ExitsMv L hW mv                                                                                          -- L10962
```
Also `colOf_of_cusp`.  Type III / II / crossed cusp: `exists_ext_of_no_r` or `_no_l` on the block `[|X|, |X|+|P|)`
gives `hex`; type I (`l σ r`) uses `exists_cusps_of_no_ext` (U4 report §2.4).

### 6.9 I. Equal-length congruences, for U5 (section `Congr`, L10982-11069; `variable (W W' : Word)`)

```lean
theorem nextPair_congr (k p : ℕ) (h0 : p = 0 → letterAt W k = letterAt W' k) (h0b : p = 0 → ∀ q, bit W k q = bit W' k q)
    (hb : p ≠ 0 → bit W k p = bit W' k p)
    (hR : p ≠ 0 → bit W k p = true → (letterAt W k).posR p = (letterAt W' k).posR p)
    (hL : p ≠ 0 → bit W k p = false → (letterAt W (k - 1)).posL p = (letterAt W' (k - 1)).posL p) :
    nextPair W (k, p) = nextPair W' (k, p)                                                                   -- L10982
theorem prevPair_congr (k p : ℕ) (h0 : …) (h0b : …) (hb : …)
    (hR : p ≠ 0 → bit W k p = false → (letterAt W k).posR p = (letterAt W' k).posR p)
    (hL : p ≠ 0 → bit W k p = true → (letterAt W (k - 1)).posL p = (letterAt W' (k - 1)).posL p) :
    prevPair W (k, p) = prevPair W' (k, p)                                                                   -- L11003
theorem pt_congr (pl : Placement) (k p : ℕ) (h0 : p = 0 → (letterAt W k).idx = (letterAt W' k).idx) :
    pt pl W (k, p) = pt pl W' (k, p)                                                                         -- L11025
theorem isSlot_congr (k p : ℕ) (hlen : W.length = W'.length) (hcut : (cut W k).length = (cut W' k).length)
    (h0 : (letterAt W k).isCrossing = (letterAt W' k).isCrossing) : IsSlot W (k, p) ↔ IsSlot W' (k, p)      -- L11034
def sameSlotEquiv (h : ∀ s, IsSlot W s ↔ IsSlot W' s) : Slot W ≃ Slot W'                                     -- L11041  (identity on the pairs)
@[simp] theorem sameSlotEquiv_val (h) (u : Slot W) : (sameSlotEquiv W W' h u).1 = u.1                         -- L11047
@[simp] theorem sameSlotEquiv_symm_val (h) (u : Slot W') : ((sameSlotEquiv W W' h).symm u).1 = u.1            -- L11049
theorem sameSlotEquiv_next (hW : W.Closed) (hW' : W'.Closed) (h : ∀ s, IsSlot W s ↔ IsSlot W' s) (u : Slot W)
    (hn : nextPair W u.1 = nextPair W' u.1) :
    sameSlotEquiv W W' h (next hW u) = next hW' (sameSlotEquiv W W' h u)                                     -- L11053
theorem colOf_congr (k p : ℕ) (hu : IsSlot W (k, p)) (hu' : IsSlot W' (k, p)) (hb : p ≠ 0 → bit W k p = bit W' k p) :
    colOf (⟨(k, p), hu⟩ : Slot W) = colOf (⟨(k, p), hu'⟩ : Slot W')                                          -- L11060
theorem xsign_congr (k p : ℕ) (hu : IsSlot W (k, p)) (hu' : IsSlot W' (k, p)) (hb : p ≠ 0 → bit W k p = bit W' k p)
    (h0 : p = 0 → letterAt W k = letterAt W' k) :
    xsign (⟨(k, p), hu⟩ : Slot W) = xsign (⟨(k, p), hu'⟩ : Slot W')                                          -- L11069
```

### 6.10 Gotchas for U5/U6 (from W2_U4_REPORT.md §5, still valid in the merged file)

1. `(shadowMv pl hW hne mv).Strand`, `(shadowOf pl hW hne).Strand`, `(realizeAt pl hW hne).Γ.Strand` and `Idx hW` are
   definitionally but not syntactically equal; stay in the `shadowMv` vocabulary (`slotMv`, `strandMv`, `travMv`,
   `vertexPt`, `dir_mv`, `mem_seg_mv_iff`) and convert realization facts with `have … := …`/`show` (defeq), not `rw`.
   `realizeAt_diagram_eq` is `rfl`; `realize W = realizeAt .std W.closed h` by `realize_eq_realizeAt`.
2. Argument order: `PieceIn L hW mv u`, `PieceOut L hW mv u`, `Unch pl hW mv u`, `MeetSpec pl hW mv K u v`,
   `GenericData pl hW mv K`, `MatchData L hW hW' mv mv' ψ`, `SigmaCorr L hW hW' mv ψ K K'`, `ExitsMv L hW mv`,
   `c.IsChain L hW mv`; the `MatchData.*` and `IsChain.*` lemmas take `pl hne (hne')` explicitly.
3. `Chain` is over `W` only: `c.slot hW j`, `c.toArc pl hW hne mv`.
4. `MeetSpec`'s `σ` clause has `τ = τ' = 1/2`; it only arises through `meetSpec_of_unch`.
5. `hK` in `slotDiagramData_of`/`isCrossing_mv_iff` is an `↔`.
6. This Mathlib: `Set.mem_setOf_eq` deprecated (`Set.mem_ofPred_eq`), `push_neg` → `push Not`, `if_pos` → `ite_eq_left`.

What U4 does **not** supply (U4 report §4): the concrete half-plane lists, moved vertices and per-slot classification
for each pattern; `MeetSpec` for pairs with a moved piece (U6, same column only); the component bijection `e` for two
different words (U5); the assembly of the `RIData`/`RIIData`/`RIIIData` fields.

## 7. Notes for the next wave

- **U8R (`represent`)** is reduced to one statement, `SM.FrontRows.U8R.SweepStatement F` (L13966):
  `∃ W : OWord, W.letters ≠ [] ∧ F.downCount = W.downCountSyn ∧ F.cuspSet.card = W.letters.cuspCount ∧
  Nonempty (RecordIso (frontRecord F) (U2.slotRecord W.closed U2.IsσSlot (U2.allActive W.closed)))`, with
  `U8R.represent_of_sweepStatement (h : SweepStatement F) : ∃ W : OWord, …` (L13971) closing the leaf.  Its analytic
  groundwork (x-velocity signs, cusp arcs, finite fibres) is in sections F-H of the U8R block; see W2_U8R_REPORT.md.
- **U3's proved leaves** call only `U3.zb_recordIso`, `U3.za_recordIso`, `U3.ci_recordIso`, `U3.cm_recordIso_above`,
  `U3.sk_switchIso`, `U3.sk_smoothIso`, `U3.siteX(_sgn)`, `U3.smoothCongr`, `U3.sk_writhe_factor`, `U3.skeinStep_unique`,
  `U3.skeinStep_not_both` plus U1/U2 glue (`U2.realizeRecordIso`, `realize_writhe`, `u1_writheFrom_*`).
- **U8D's** three leaf bodies are one-liners over `U8D.downCount_eq_of_deformation`, `U8D.writhe_eq_of_deformation`,
  `U8D.P_eq_of_deformation (d : F.NonsingularDeformation F') (S S') (hS) (hS') : P S = P S'`.
- The U2 API (MERGE1_REPORT.md §4) is unchanged; U6's record isomorphism for the vertex-moved `D` is
  `U2.vertexMovedRecordIso'` fed by `U4.slotDiagramData_of`.
- Scratch: `/tmp/lean_merge2/` (probe copies), `/workspace/scratch/merge2_*.log`.  Nothing under `work/lean` was touched.
