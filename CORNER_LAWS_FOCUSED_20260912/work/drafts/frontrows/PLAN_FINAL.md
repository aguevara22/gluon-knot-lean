# PLAN_FINAL — the eight front certificate rows (tools/claims.py rows 76-83), judge's decision

2026-09-14 (judge; inputs PLAN_A.md / Statements_A.lean / Skeleton_A.lean and PLAN_B.md / Statements_B.lean /
Skeleton_B.lean, all four Lean files re-checked with `cd work/lean && lake env lean` — 0 errors each, A: 8/36
placeholders, B: 8/26; the printed statements sm-3:1921-2169 and 2305-2348; the design of record
work/reports/front-block-design-FINAL-20260913.md; AUTHOR_NOTES FR-1..FR-7, D-F1..D-F6; BETA2_REPORT §4, §6, §7;
the accepted layer `SM/LinkMoves`, `SM/PolynomialBlock`, `SM/FrontWords`, `SM/FrontRealize*`, `SM/FrontInterfaces`,
`SM/FrontSmooth`, `SM/Smoothing`).

Deliverables (this directory; checked with `lake env lean`, Lean v4.34.0-rc2, the project's Mathlib pin):
**Statements_FINAL.lean** — 0 errors, exactly eight placeholders = the row theorems `SM.ng_commutation`,
`SM.ng_front_I`, `SM.ng_front_II`, `SM.ng_front_III`, `SM.ng_deletions`, `SM.ng_circle`, `SM.ng_cusp_skein`,
`SM.ng_local_front_bound`; **Skeleton_FINAL.lean** — 0 errors, bundles verbatim from the Statements, 26 leaves,
all glue proved, the eight rows assembled; `#print axioms`: rows 76-82 reach `sorryAx` + the standard three +
`SM.lp_lm` (through `P`), row 83 and `SM.FrontRows.word_bound` additionally `SM.ng_finite_word`; no new axiom.

## 0. Verdict

**Winner: TAG B (literal fidelity), adopted with three refinements from the judge (leaf shapes, unit split,
risk list).**  A is not adoptable: eleven of its 36 leaves are false statements (section 3, finding F1).

| design | fidelity | feasibility | reuse | sum | weighted (fidelity ×2) |
|---|---|---|---|---|---|
| A — maximal reuse of β2's block rectangles | 6 | 3 | 7 | 16 | 22 |
| B — literal fidelity, records + hugging discs | 8 | 6 | 7 | 21 | 29 |
| FINAL — B + refinements (section 2) | 8 | 7 | 8 | 23 | 31 |

Scoring notes.
- **A fidelity 6.** Rows 77-80, 82 agree with B.  Row 76's deformation clause is moved to the PL class
  (`PLFront.Deform`) — a disclosed class change on a printed clause whose subject is the smooth class of row 73;
  the design of record (FINAL §5, §7 "76a smooth deformations: statement now") asked for the smooth clause.  Row
  81 sentence 2 is on realizations only.  Row 83 carries a non-printed field `on_words` inside the bundle (the
  rule is one field per printed clause).  Row 82 drops "unique".
- **A feasibility 3.** `Skeleton_A` compiles, but its site leaves `typeI_site_left/right`, `typeII_site_ll/lr/rl/rr`,
  `typeIII_site`, `crossedCusp_site_l/r` and the smoothing half of `skein_site`/`skein_site_refl` assert
  `RIData`/`RIIData`/`RIIIData`/`OrientedSmoothingData` on `BlockSetup.U`, which is the full-height block rectangle
  (`FrontRealizeGeometry.lean`, `U_eq : B.U = blockRect B.pl |X| (|X|+|P|) (blockH …)`).  `ArcCover U A`
  (`LinkMoves.lean:208`, field `mem_iff : ∀ p, Γ.eval p ∈ U ↔ ∃ a ∈ A, a.Mem p`) puts EVERY traversal point inside
  `U` on one of the listed arcs (one arc for RI, two for RII and the smoothing, three for RIII).  Any spectator
  strand running through the block columns lies in `U` and on no listed arc, so the leaves are false whenever the
  cut before the factor has a strand the pattern does not touch — e.g. `[l 1 d] ++ [l 2 d', σ 1, r 2] ++ [r 1]` for
  `typeI_site_left` (through-strand at position 1, spectator at position 2).  No prover can close them; the plan's
  cost model (700-1300 lines per move row) is built on them.  A's counts/degree/record leaves are true and its
  `blockPlacement`/`BlockSetup.ofReplace` helpers are correct but unused by the FINAL route.
- **B fidelity 8.** Clause by clause on the printed text: row 76 all three sentences on their printed subjects
  (commutations on words, deformations on the smooth class, the representation sentence); rows 77-82 on realized
  words with the narrowing disclosed and closed by `represent`; row 81 sentence 2 on `PLFront` (the smallest
  accepted class carrying the geometric predicate; still not the smooth class — FR-11); row 82 with "unique";
  row 83 exactly the printed clause on the smooth class.  Not 9: the deformation reading imposes joint `C^∞`
  smoothness on `[0,1] × ℝ` (FR-9), and 81(2) is on `PLFront`, not on fronts of ng:front-domain.
- **B feasibility 6.** Every leaf audited true (section 4); the estimates are the realistic ones (B found F1); but
  the route is heavy (20-24k lines for 76(1)+77-83 on words) with the new record core on the critical path of six
  rows, and 76(2-3) are analysis (10-15k) with the block's rock inside.
- **Reuse 7/7/8.** Both reuse `realize_downCount/writhe/sCount`, `presentations`, `P_addFree`, `P_reidemeister_*`,
  `P_recursion_pos/neg`, `degAZ_mul`, the accepted `wordMoves_*_s`, `realize_isStandardCircles_of_base`,
  `ng_finite_word_bound`.  A's reuse of `BlockSetup.outsideMatch` for the move discs is illusory (F1); its exterior
  half (`shiftIdx`, `next_ext`, `extSlot`) IS reused by the FINAL's record core.  FINAL 8: it also reuses the
  accepted `exists_smoothing_record_visit` (no geometric smoothing construction) and B's algebraic trick for the
  reflected skein direction (one site leaf, not two).

Judge's refinements over B: (i) polynomial leaves stated at the RECORD level (`Nonempty (RecordIso …)`), the
`P` equalities being glue through `presentations`/`P_addFree` — pins the printed argument ("the full named records
are identical") and keeps every leaf a true statement; (ii) the geometric leaves pin the route without fixing a
disc: `typeIII_site : ∃ U, Nonempty (RIIIData U (realize W).diagram (realize W').diagram)` (true between the two
standard realizations) and `typeII_move/typeI_move/crossedCusp_move : ∃ D, RII/RI D (realize W).diagram ∧ Nonempty
(RecordIso D.record (realize W').diagram.record)` (true with the vertex-moved diagram); (iii) `skein_counts` states
the syntactic `w_A + w_{A'} = 2 w_C` and the site carries `sign x = w_A − w_C`, so one site leaf serves both
principal directions; (iv) the unit split of section 5 (8 units).

## 1. Readings (recorded once in Statements_FINAL.lean; every row docstring cites them)

| id | reading | AUTHOR_NOTES entry |
|---|---|---|
| R-front | rows 77-82 (and 76 sentence 1, 81 sentence 1) on closed oriented words through `SM.realize`; the moves are the accepted word patterns (`IsComm`, `IsTypeI/II/III`, `IsZigzagDeletion`, `IsCrossedCuspShortcut`, `IsCircleDeletion`, `IsCuspSkein`) | FR-5 (accepted), FR-8 (new: the class narrowing and how `represent` closes it) |
| R-quantities | `D = PLFront.downCount`, `w = PLFront.writhe`, `s = sCount`, `d = degAZ (P F.diagram)` on the identity rounding, `B = PLFront.defect` | FR-1 (accepted) |
| R-smooth | rows 76 (2-3), 83 on `SmoothFront` with `d`, `B` on a rounding `S`, `F.IsRounding S` | FR-1 (accepted), row 74 |
| R-circle | row 81 sentence 2 on `PLFront.IsStandardCircles` | FR-11 (new) |
| R76-2 | "deformations through fronts without a singular event" = `SmoothFront.NonsingularDeformation` (jointly `C^∞` family in the class on `[0,1]`, constant `c`) | FR-9 (new) |
| R76-3 | "represented by a finite elementary front word" = equal `D`, `w`, `s` + `RecordIso` of every rounding with the realization's diagram | FR-10 (new) |
| FR-6 | deletion directions only for types I/II; equalities, so the creation direction is the same statement | FR-6 (accepted) |
| FR-12 | "the unique compatible smoothing" = field `unique_smoothing` | FR-12 (new) |

## 2. Clause maps (printed clause → field; tex lines; Statements_FINAL.lean)

| row | printed clause (sm-3) | field(s) | binder |
|---|---|---|---|
| 76 | 1922-1923 "Disjoint-gadget commutations ... preserve D, w, d, and hence B" | `comm_D`, `comm_w`, `comm_d`, `comm_B` | `IsComm` on `OWord` |
| 76 | 1922-1923 "deformations through fronts without a singular event preserve D, w, d, and hence B" | `deform_D`, `deform_w`, `deform_d`, `deform_B` | `SmoothFront`, `NonsingularDeformation`, roundings `S`, `S'` |
| 76 | 1924-1925 "Every supplied finite front can be represented by a finite elementary front word." | `represent` | `∀ F : SmoothFront, ∃ W : OWord, …` |
| 77 | 1951 "The front type-I moves preserve B." | `typeI_B` | `IsTypeI` (deletion direction) |
| 78 | 1973 "The front type-II moves preserve D, w, d, and hence B." | `typeII_D/w/d/B` | `IsTypeII` (four variants incl. right cusps 1988-1989) |
| 79 | 1991 "The front type-III moves preserve D, w, d, and hence B." | `typeIII_D/w/d/B` | `IsTypeIII` (either direction) |
| 80 | 2009-2010 "Deleting an empty zigzag lowers s by two and cannot increase B" | `zigzag_s` (`s' + 2 = s`), `zigzag_B` (`B' ≤ B`) | `IsZigzagDeletion` |
| 80 | 2010-2011 "applying the crossed-cusp shortcut lowers s by one and cannot increase B" | `crossedCusp_s`, `crossedCusp_B` | `IsCrossedCuspShortcut` (bit flip built in) |
| 81 | 2047-2048 "Deleting a separated standard front circle with nonempty remainder preserves B." | `circleDeletion_B` | `IsCircleDeletion` (nonempty remainder built in) |
| 81 | 2048-2049 "A single standard front circle ... has B = 0" / "and any union of such circles" | `single_B` (`c = 1`), `union_B` | `PLFront`, `IsStandardCircles` |
| 82 | 2077-2080 "For either principal direction ..., B of the earlier branch ≥ min{B other branch, B compatible smoothing}" | `earlier_branch` | `IsCuspSkein A A' C` (symmetric: both lines of ng:skein-defect 2158-2163) |
| 82 | 2080 "the unique compatible smoothing" | `unique_smoothing` | theorem about `IsCuspSkein` |
| 82 | 2080-2082 "The smoothing has one fewer singularity; the principal branches have the same singularity count." | `smoothing_s`, `principal_s` | |
| 83 | 2306-2311 "For every front F on the domain of Definition ng:front-domain, with the same polynomial evaluated on its actual ordinary cusp rounding, w(F) − D(F) ≤ −deg_a P_{S(F)} − 1" | `front_inequality` | `∀ F : SmoothFront, ∀ S, F.IsRounding S → …` |

Proof displays that are leaves, not fields: ng:type-I-counts 1964-1966 (`typeI_counts`), ng:zigzag-counts
2020-2022 (`zigzag_counts`), ng:crossed-cusp-counts 2034-2036 (`crossedCusp_counts`), ng:circle-counts 2064-2067
(`circleDeletion_counts` + `degAZ_delta`), the (t,u) table 2107-2118 (`skein_counts`, the sign of `skein_site`),
ng:skein-plus/minus and degree-plus/minus 2137-2148 (`degAZ_le_of_eq_pos/neg`, `switch_of_recursion_pos/neg`).
Row 83 on words (the strong induction, 2313-2343) is the named companion `SM.FrontRows.word_bound`, not a field.

## 3. Findings that fix the route (verified against the accepted layer)

- **F1 — the move disc must be spectator-free (B, confirmed).** `ArcCover` (LinkMoves.lean:208) and the singleton/
  pair/triple arc sets of `RIData`/`RIIData`/`RIIIData`/`OrientedSmoothingData` (:569-740) make the full-height block
  rectangle `BlockSetup.U` inadmissible whenever a spectator strand crosses the block.  β2's `outsideMatch`/
  `clean_blockRect` do not deliver the move data (BETA2_REPORT §6 (ii)-(iii) already listed `MoveMatch` and arcs as
  not started).  The disc must be a convex polygon hugging the active strands.  Checked against `realize`'s piece
  geometry (FrontRealize.lean: `Shape.pass p q` is the segment `(0,−p)–(1,−q)` of its column, `armL/armR` meet at the
  cusp vertex `(1/2, −m − 1/2)`): a spectator below a cusp column runs parallel to the pushed-down active strand one
  unit lower, so a convex `U` with lower boundary half a unit below the active diagonal, then horizontal, exists
  (lower boundary = convex function; spectators above are horizontal one unit up).
- **F2 — length-changing moves change spectator traces (B, confirmed).** For `|P| ≠ |P'|` a spectator is a broken
  line in one realization and a straight segment in the other (blockPlacement or not), so no `OutsideMatch` relative
  to a hugging disc exists between the two realizations; `Deform` keeps vertex counts, no accepted `Reparam`
  subdivision exists.  Route: a vertex-moved diagram `D` with the shadow structure of `realize W` (only the active
  strand's interior block vertices moved, inside `U`; `MoveMatch` = identity), `RI`/`RII` between `D` and `realize W`,
  and `RecordIso D.record (realize W').diagram.record` (the record core with an "active set" of `σ` slots).
- **F3 — no record-level kink or bigon lemma exists** (`PolynomialBlock.lean` theorem index: `P_planar`,
  `P_reidemeister_I/II/III`, `P_circle`, `P_skein`, `P_crossingFree`, `P_recursion_pos/neg`, `P_addFree`,
  `P_split_circle`, `presentations`, …), so rows 77, 78, 79 and the crossed cusp of 80 need the geometric data; the
  skein relation alone cannot replace RI (one equation, two unknowns).
- **F4 — records carry four rows.** Commutation (76), zigzag (80), circle deletion (81, `P_addFree`), cusp-skein
  (82: the switch record and the accepted `exists_smoothing_record_visit`, Smoothing.lean:8185).  All need one tool:
  the named record of a realization (unit U2).
- **F5 — counts are syntactic and cheap** (`realize_downCount/writhe/sCount`, FrontRealizeCorrespondence.lean:901-915).
- **F6 — the descent is done**: `wordMoves_pres_s/del_s/skein_s` (:1000-1028), `realize_isStandardCircles_of_base`,
  `realize_downCount_eq_c_of_base` (FrontRealizeBase.lean:566, 573), `ng_finite_word_bound` (FrontInterfaces.lean:499).
  `certificate_laws`, `word_bound`, `base_defect_nonneg` are proved in the skeleton from the row theorems.

## 4. Leaf audit (every placeholder of Skeleton_FINAL.lean is a true statement; route and tools)

**L-deg (4).** `delta_ne_zero` (`R.delta = (a − a⁻¹) z⁻¹`, distinct monomials, units, `IsDomain R`);
`degAZ_delta = 1` (`degA_mul` with `degA (a − a⁻¹) = 1`, `degA zInv = 0`); `degAZ_le_of_eq_pos/neg` (`degA_add_le`,
`degA_sub_le`, `degA_mul`, `degA_aInv = −1`, `degA_a = 1`, `degA_z = 0`, `degA_eq_degAZ`).  ~250 lines.

**L-cnt (8).** `comm_counts`, `typeI_counts` (`D = D' + 1`, `w = w' + 1`), `typeII_counts`, `typeIII_counts`,
`zigzag_counts` (`w = w'`, `D = D' ∨ D = D' + 2`), `crossedCusp_counts` (`w' = w + 1`, `D' + 1 = D ∨ D' = D + 1`),
`circleDeletion_counts` (`w = w'`, `D = D' + 1`), `skein_counts` (`D_A = D_{A'} = D_C`, `w_A + w_{A'} = 2 w_C`).
Truth: each is the printed display read on the realization; the pattern's factor contributes the display's local
value at the typed cut (β1's `run_*` lemmas and `decide` checks), the exterior letters see the same cuts.  Proof:
`downCountFrom_append`/`writheFrom_append` (run of the prefix), then the factor's contribution on the symbolic cut
`A ++ w ++ R` (`Letter.step_eq_some_iff`, `act_*`), then `realize_downCount`/`realize_writhe` (words nonempty by the
pattern).  ~900 lines.

**L-rec (5; on the record core U2).** `comm_recordIso` (slot bijection: identity outside the two columns, the
exchanged gadgets' slots by the index shift, commutes with `next` — `run_comm_above/below`); `zigzag_recordIso`
(no `σ` in the factor; exterior slots by the column shift, `shiftIdx`/`extSlot`/`next_ext`, `next` commutes; the
block connects its boundary slots as the straight strand does — β2 §6 (i): an empty factor has no literal outside
match, the record does not need one); `circle_recordIso_addFree` (the circle is a free component:
`Record.addFree`); `skein_site` (x := `crossingOf … (σ m)`; switch record by the slot bijection
`(k+1,m) ↦ (k+1,m+2)`, `(k+1,m+1) ↦ (k+1,m)`, `(k+1,m+2) ↦ (k+1,m+1)`, identity elsewhere; smoothing:
`exists_smoothing_record_visit` gives `D₀` with `RecordIso D₀.record ((realize A).record.smooth v)` and the
reconnection `T ↦ arm` is the record of `C` by the (t,u) table; sign by `sign_crossingOf` = `w_A − w_C` since the
exterior writhe is `w_C`); `skein_unique` (the first differing index of `A`, `A'` is `|X|`; `m`, `d`, `Y` and the
through-strand bit `a` (from `run X []`) follow; the reverse-direction case gives `l (m+1) = l m'` and
`l m = l (m'+1)`, contradiction).  Truth of `skein_site`: printed 2091-2099 and 2119-2126.  ~2.7k lines + U2.

**L-geo (4; on the geometry core U4).** `typeIII_site` — between the two STANDARD realizations (same length, only
`σ` letters, so exterior and spectators are literally the same pieces; the band `[x_k, x_{k+3}] × [−(m+2)−ε, −m+ε]`
excludes every spectator; arcs = the three strands, height order `a` over `b` over `c` on both sides by
`overStrand_crossingOf`, visit order reversed; `MoveMatch` by the conjugating slot bijection with the component
bijection of the equal `next`-cycles; both directions of `IsTypeIII` since `RIIIData` is symmetric).  `typeII_move`
— `D` := `realize W` with the through-strand's vertices at `x_{k+1}, x_{k+2}` lifted to `−(m−1) + 1/2` (variant
`l_{m−1} σ_m σ_{m−1}`; mirror for the others), `RIIData U D (realize W)` in the convex hexagon of F1 (arcs: the
through-strand and the cusp arc entering/exiting on the right; `same_over`: through-strand under at both, or over
at both), `RecordIso D.record (realize W').record` (no crossing left in the block, exterior `σ` slots by
`shiftIdx`, the block connects position `m−1` straight and the arms via the cusp in both).  `typeI_move` — `D` :=
`realize W` with the curl's block vertices moved onto an embedded shallow zigzag from `(x_k, −(m−1))` to
`(x_{k+3}, −(m−1))` (the spectator below runs a trough `−2/0/+2` slopes, one unit lower; `U` a convex hexagon),
`RIData U D (realize W)` (one arc, the kink on the `realize W` side), record of `realize (X ++ Y)`.
`crossedCusp_move` — `D` := `realize W` with the arms' vertices at `x_{k+1}` exchanged (`−(i+1)+δ`, `−i−δ`), `RIData`
with the kink of sign −1 on the `realize W` side, record of `realize (X ++ [l i (!d)] ++ Y)`.  Truth: each `∃ D` is
witnessed by the described diagram; the existence of the convex disc is F1.  Estimates §5.

**L-PL (1).** `PLFront.IsStandardCircles.downCount_eq_c_general`: per component the two x-monotone PL arcs between
the left and right cusp never meet (no crossing), so one lies above the other (IVT on the difference of the two PL
graph functions), and `isDownCusp_iff_armIn_above` (FrontPL.lean:292) gives exactly one downward cusp.  True
(planar fact; accepted for realizations by β2 on the grid).  1.5-2.5k; fallback FR-11.

**L-smooth (4).** `deform_downCount`: along a jointly `C^∞` family inside the class, `Z = {(t,u) : x'(t,u) = 0}` is a
smooth 1-manifold (at its points `x'' ≠ 0`: a zero of `x'` with `γ' ≠ 0` would be a vertical tangency, excluded; a
cusp has `x'' ≠ 0` by `cusp_nonvertical`), transverse to the fibres, hence a covering of `[0,1]` — the cusp count is
locally constant — and `x''·det(γ'', γ''')` is continuous and nonzero on `Z`, so `D` is constant.  `deform_writhe`:
the transverse double points form a covering likewise (IFT on `γ(t,u) = γ(t,v)`; no accumulation at a semicubical
cusp, which is locally injective), `crossSign` continuous nonzero.  `deform_P`: the `Marking` of `F` transports to
`F'` along the family (`isRounding_iff_geomModel`, FrontGeomModel.lean:332), then `presentations`.  `represent`:
PL model of a smooth front carrying its record (5-7k) + PL vertical sweep reading the word (2.5-4k) — FINAL §8 risk 1.
All true (the printed lemma; standard transversality); 10-15k in total; only `represent` is on row 83's path.

**Glue audited (proved in the skeleton):** `P_comm/P_zigzag` (`presentations`), `P_circleDeletion` (`P_addFree`),
`P_typeIII` (`P_reidemeister_III ⟨U, Or.inl _⟩`), `P_typeII/P_typeI/P_crossedCusp` (`P_reidemeister_II/I` then
`presentations`), `degAZ_delta_pow`, `switch_of_recursion_pos/neg` (`linear_combination` with `R.a_mul_aInv`),
`skein_ineq_forward/backward` (`P_recursion_pos/neg`, the degree leaves, `omega`), `base_defect_nonneg`
(`realize_isStandardCircles_of_base`, `realize_downCount_eq_c_of_base`, `P_crossingFree`), `IsStandardCircles.defect_eq_zero`,
the `s` clauses (`realize_sCount` + β1's `*.sCount`), `certificate_laws`, `word_bound`, the eight assemblies.

## 5. Unit split (8 units; Lean lines; calibration: β2 landed at 6.7k against 2.5-5k, the smoothing gate at 8.2k
against 1.2-1.8k — geometric construction units carry a ×1.5-2 tail)

| unit | leaves (Skeleton_FINAL.lean) | est. lines | depends on | closes |
|---|---|---|---|---|
| **U1 cnt+deg** | `delta_ne_zero`, `degAZ_delta`, `degAZ_le_of_eq_pos`, `degAZ_le_of_eq_neg`, `comm_counts`, `typeI_counts`, `typeII_counts`, `typeIII_counts`, `zigzag_counts`, `crossedCusp_counts`, `circleDeletion_counts`, `skein_counts` (12) | 1.1-1.4k | — (start now) | fields `comm_D/w` (76), `typeII_D/w` (78), `typeIII_D/w` (79); needed by every `B` field and by `base_defect_nonneg` |
| **U2 record core** | none (infrastructure: `slotRecord W S` for an active set `S` of `σ` slots and a vertex-moved shadow; `realizeRecordIso : RecordIso D.record (slotRecord W S)` for `D = realize W` (`S` = all) and for the vertex-moved `D` of U6; exterior correspondence via `shiftIdx`/`extSlot`/`next_ext`) | 2.5-3.5k | — (start now; the critical path of 76(1), 77, 78, 80, 81, 82) | nothing by itself |
| **U3 record rows** | `comm_recordIso`, `zigzag_recordIso`, `circle_recordIso_addFree`, `skein_site`, `skein_unique` (5) | 2.5-3.5k | U2 (+ accepted `exists_smoothing_record_visit`, `switch`) | 76(1) `comm_d/comm_B` (with U1); 80 `zigzag_B` (with U1); 81(1); 82 (with U1) |
| **U4 geometry core** | none (infrastructure: convex polygon `U` as an intersection of half-planes with the parallel-offset spectator argument; `Clean` on its frontier; `ArcCover` for the active arcs; the vertex-moved diagram `D` — genericity of `withVertices V`, crossing set = the kept `σ` slots — and the identity `MoveMatch`; the band `OutsideMatch` for equal-length patterns) | 2-3k | U2 (record of the vertex-moved `D`) | nothing by itself |
| **U5 geo III** | `typeIII_site` (1) | 1.5-2.5k | U4 | 79 (with U1) — **first row to accept** |
| **U6 geo I/II/X** | `typeII_move`, `typeI_move`, `crossedCusp_move` (3) | 6-8k (2-2.7k each) | U4 | 78 (with U1), 77 (with U1), 80 (with U1, U3) |
| **U7 PL circles** | `PLFront.IsStandardCircles.downCount_eq_c_general` (1) | 1.5-2.5k (0.1k under the FR-11 fallback) | — | 81(2-3) → row 81 with U1, U3 |
| **U8 smooth** | `deform_downCount`, `deform_writhe`, `deform_P`, `represent` (4) | 10-15k (`represent` 7.5-11k; deformations 2.5-4k) | — (`represent` last) | 76 (all fields, with U1, U3); 83 (with all rows) |
| **rows 77-82 + 76(1) + 83 on words** (U1-U7) | 22 leaves | **≈ 17-23k** (B: 20-24k; A's 9.7k rested on false leaves) | | |
| **all of 76-83** (U1-U8) | 26 leaves | **≈ 27-38k** | | |

Order: U1, U2, U7 in parallel (three lanes); U3 and U4 when U2 lands; U5 then U6 when U4 lands (U6's three
leaves are independent of each other — three provers); U8's deformation leaves whenever a lane is free;
`represent` last.  Row acceptance order: 79, 78, 81, 80, 77, 82 (each independent of U8), then 76 and 83 together.
Each `D`/`w`/`s` field can be reported early; row-level acceptance needs all fields.

## 6. Row 83: the chain (exact statements in Skeleton_FINAL.lean)

1. `certificate_laws : (wordMovesOf (fun W => (realize W).sCount) (fun W => (realize W).defect)
   OWord.IsStandardCircleBase).Laws` — `pres_B` from `comm_B`, `typeI_B`, `typeII_B`, `typeIII_B`; `del_B` from
   `zigzag_B`, `crossedCusp_B`, `circleDeletion_B`; `skein_B` from `earlier_branch`; `pres_s/del_s/skein_s` =
   `wordMoves_pres_s/del_s/skein_s` (same fields definitionally); `base_B` = `base_defect_nonneg` (accepted forward
   base bridge; the open converse, β2 §7 item 1, is NOT needed).  This is the axiom's own shape
   (`ng_finite_word_bound`), so neither `finiteWordStatement_wordMoves_of` nor `SM.wordMoves` is needed.
2. `word_bound : ∀ W : OWord, 0 ≤ (realize W).defect := ng_finite_word_bound _ _ certificate_laws`
   (consumes `SM.ng_finite_word`, accepted 04:56Z).
3. `front_inequality`: `represent F` gives `W`; `presentations S _ (hrec S hS) : P S = P (realize W).diagram`;
   `F.defect S = (realize W).defect`; `defect_nonneg_iff` (FrontSmooth.lean:1524).
The empty word never enters: no row hypothesis produces `[]` (`Pres.two_le_of_target_nil`, `IsZigzagDeletion.ne_nil`,
type I from `[]`-closed words is untypable), the `s` clauses are on realizations, and `realize ⟨[], _⟩` is the
standard circle (β2 convention), covered by `realize_isStandardCircles_of_base`.

## 7. Fidelity risks the executor must write into AUTHOR_NOTES BEFORE the rows are stated (FR-1..FR-7 remain)

- **FR-8 (class narrowing of the certificate rows).** Rows 77-82, 76 sentence 1 and 81 sentence 1 are stated on
  realizations of closed oriented words; the printed rows are on fronts.  Justified by the printed text (the
  section computes on Rutherford's words; the moves exist only as word patterns) and CLOSED by the printed second
  sentence of ng:commutation, kept as the field `represent` (row 76) on the smooth class; row 83 is derived from it.
  Consequence: rows 76 and 83 cannot be accepted before `represent` (U8) lands; reviewers of 77-82 must be told the
  `OWord` binder is by design (D-F1/FR-5).  Fallback (Mark's decision, FINAL §10 item 2): drop `represent` and
  disclose a class change on 76/83/93.
- **FR-9 (deformation clause).** "Deformations through fronts without a singular event" = a jointly `C^∞` family of
  fronts of the class on `[0,1] × ℝ` with constant `c` (`SmoothFront.NonsingularDeformation`).  A reviewer may prefer
  `C^k`, or smoothness on a neighbourhood of `[0,1]`; the chosen hypothesis is stronger, so the clause is (slightly)
  weaker than the most liberal reading.  Its proof (U8, analysis) is not on row 83's path.
- **FR-10 ("represented by").** Equal `D`, `w`, `s` and a named-record isomorphism of every rounding `S(F)` with the
  realization's diagram.  A reviewer may ask for "the same front up to deformation"; across the smooth/PL boundary
  only the invariants and the record can be stated, and the record reading is exactly what every consumer uses
  (row 83, fd:ng-bound).  The printed proof (vertical cuts of a perturbed front) produces such a word.
- **FR-11 (row 81 sentence 2).** Stated on `PLFront` (`IsStandardCircles`), not on the smooth class; the descent uses
  only the realization instance.  If U7 stalls, the word reading `∀ W, (realize W).IsStandardCircles → …` is a 100-line
  fallback and a recorded narrowing.
- **FR-12 ("unique").** `unique_smoothing` renders the definite article as a theorem about `IsCuspSkein`; "or its
  reflected pattern" (ng:finite-word) = the other principal direction (`IsCuspSkein` symmetric); right-cusp templates
  (sm-3:2164-2166 "by relabeling") are outside the row, as in the accepted interface.
- **FR-13 (P through `lp_lm`).** Every polynomial clause reaches the literature interface `SM.lp_lm` through `P`, as
  `PLFront.defect` itself does; row 83 additionally `SM.ng_finite_word`; no new axiom.
- **FR-14 (the base of the axiom).** `SM.ng_finite_word` has the syntactic base `IsStandardCircleBase`; `base_B` is
  proved on it directly through the accepted forward bridge; the converse (β2 open item 1) is not on the path.
- **FR-15 (F1/F2: no block-rectangle move discs).** The geometric rows use β2's block tools only for the exterior
  index shift (`shiftIdx`, `next_ext`, `extSlot`); the move discs are convex polygons hugging the active strands, and
  the length-changing moves compare `realize W` with a vertex-moved diagram whose record is that of `realize W'`.
  Recorded so that reviewers do not expect `BlockSetup.outsideMatch` in the proofs, and so that nobody re-attempts
  A's route.
- **FR-16 (identity rounding on PL fronts).** `d(F) = degAZ (P F.diagram)` on realizations (FR-1's polygonal reading:
  a PL front is its own ordinary diagram); the choice of rounding is immaterial on the smooth side by row 74, which is
  where `front_inequality` lives.
- **FR-17 (route disclosure for 77).** The printed proof deletes the monogon directly; the Lean chain compares
  `realize W` with a vertex-moved diagram (RI) and transports by the record — a proof device, not a statement change.
  Likewise 82: `realize A'` is identified with `(realize A).switch x` by a `RecordIso` (printed 2093-2097), not by a
  `Deform` (impossible: the cusp vertex must cross the through-strand).

## 8. Accepted declarations used (file:line)

FrontPL.lean: `PLFront.downCount` 436, `writhe` 452, `sCount` 458, `defect` 462, `IsStandardCircles` 513,
`.writhe_eq_zero` 518, `.defect_eq` 554, `isDownCusp_iff_armIn_above` 292.  FrontWords.lean: `IsCommStep/IsComm`
412/418, `IsTypeI/II/III` 425/433/441, `IsZigzagDeletion` 450, `IsCrossedCuspShortcut` 456, `IsCircleDeletion` 463,
`IsCuspSkeinStep/IsCuspSkein` 475/483, `run_*` 500-935, `*.sCount` 1035-1090, `Pres/Del/Skein` 1017-1027,
`Moves.Chain` 1149, `Moves.Laws` 1156, `defect_nonneg` 1180, `wordMovesOf` 1201, `word_bound_of` 1237.
FrontInterfaces.lean: `NgFiniteWordClauses` 450, `ng_finite_word` 480, `ng_finite_word_bound` 499.
FrontRealize.lean: `Placement` 49, `Shape` 239, `piecePt` 779, `realizeAt` 1221, `realize` 1243.
FrontRealizeSlots.lean: `idxEquiv` 1282, `toSlot_succ` 1291.  FrontRealizeCorrespondence.lean:
`realize_sCount/downCount/writhe` 901/911/915, `wordMoves_pres_s/del_s/skein_s` 1000/1010/1028,
`IsZigzagDeletion.ne_nil` 951, `Pres.two_le_of_target_nil` 985.  FrontRealizeBase.lean:
`realize_isStandardCircles_of_base` 566, `realize_downCount_eq_c_of_base` 573.  FrontRealizeDeform.lean:
`deformData` 182, `P_realizeAt_eq_realize` 234.  FrontRealizeGeometry.lean: `blockRect` 86, `clean_blockRect` 414,
`SameEffect` 479, `shiftIdx`/`extSlot`/`next_ext` 479-778, `BlockSetup` 1034, `U_eq` 1069, `crossingParam_eq_half`
1403, `outsideMatch` 1624.  FrontSmooth.lean: `SmoothFront` 305, `downCount/writhe/sCount` 724-730, `IsRounding`
1479, `defect` 1506, `defect_nonneg_iff` 1524.  FrontGeomModel.lean: `isRounding_iff_geomModel` 332.
LinkMoves.lean: `IsDisc` 100, `Arc` 145, `IsArc` 198, `ArcCover` 208, `OutsideMatch` 316, `Clean` 342, `LocalFrame`
348, `MoveMatch` 356, `DeformData/Deform` 462/478, `RIData/RI` 569/590, `RIIData/RII` 599/629, `RIIIData/RIII`
639/700, `OrientedSmoothingData` 713, `IsOrientedSmoothing` 743, `IsSkeinTriple` 751.  PolynomialBlock.lean:
`P_planar` 604, `P_reidemeister_I/II/III` 605-607, `P_crossingFree` 688, `P_recursion_pos/neg` 693/697, `P_ne_zero`
793, `Record.addFree` 911, `P_addFree` 1036, `presentations` 1177.  LinkLaurentRing.lean: `R.a_mul_aInv` 177,
`R.delta` 193, `degA_add_le` 431, `degA_aInv/z/one` 440-443, `degAZ` 446, `degA_eq_degAZ` 449, `degAZ_mul` 733,
`degA_mul` 753.  LinkDiagram.lean: `IsPositive` 547, `sign` 552 (`SignType`), `isPositive_iff_sign_eq_one` 559,
`sign_eq_one_or_neg_one` 570, `switch` 650.  LinkRecord.lean: `RecordIso` 539, `switch` 655, `smooth` 895.
Smoothing.lean: `exists_smoothing_record` 8178, `exists_smoothing_record_visit` 8185.

## 9. Decisions needed from Mark (none blocks rows 77-82)

1. Whether to invest U8's `represent` (7.5-11k, ~40% in horizon) for rows 76/83 on the smooth class, or accept the
   FR-8 fallback (a recorded class change on 76/83/93) if it stalls.
2. Whether row 81 sentence 2 stays on `PLFront` (U7, 1.5-2.5k) or takes the FR-11 word-reading fallback now.
3. The total for the certificate rows is 17-23k lines, not the 6-8k of the design of record (F1); confirm the lanes.
