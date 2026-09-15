# Front certificate rows 76-83 — statements and proof plan, TAG B (literal fidelity)

2026-09-14. Files: `Statements_B.lean` (compiles; 8 `sorry` = the row theorems), `Skeleton_B.lean`
(compiles; 26 `sorry` = leaves; the eight rows are assembled from them; `#print axioms`: rows 76-82 reach
`sorryAx` + standard + `SM.lp_lm` (through `P`); row 83 and `word_bound` additionally `SM.ng_finite_word`).
Fixed names used: `SM.ng_commutation`, `SM.ng_front_I`, `SM.ng_front_II`, `SM.ng_front_III`, `SM.ng_deletions`,
`SM.ng_circle`, `SM.ng_cusp_skein`, `SM.ng_local_front_bound`; none is in axiom-policy.json's target list, so
they are the convention of the brief.  Source lines are reference/SM/sm-3-statesum.tex.

## 0. Verdict in five sentences

1. Rows 77-82 are stated on closed oriented words through the realization (`SM.realize`), rows 76(2-3) and 83
   on the printed smooth class; this is the FINAL/FR-5 reading and, for the moves, the ONLY possible one (the
   printed moves are defined by word patterns), while for the class of fronts it is a narrowing that the printed
   text itself closes with ng:commutation's second sentence (the representation clause, field `represent`).
2. The counts (`D`, `w`, `s`) of every row are cheap: letter tracing is accepted (`realize_downCount`,
   `realize_writhe`, `realize_sCount`), so `ΔD`, `Δw` are list computations.
3. The polynomial clauses are where the cost is, and the accepted geometric move data is HARDER to instantiate
   than the FINAL design assumed: `ArcCover U {a}` (LinkMoves.lean:208) forces the move disc to contain NO
   spectator strand, so the geometry lane's full-height `blockRect`/`BlockSetup.outsideMatch` cannot be the disc
   of an `RIData`/`RIIData`/`OrientedSmoothingData` when any strand passes the block (finding F1).
4. Consequently four rows go through RECORDS (commutation, zigzag, circle deletion, cusp-skein: `presentations`,
   `P_addFree`, `exists_smoothing_record`), and four through geometry on a VERTEX-MOVED realization (type I, II,
   III, crossed cusp) with a convex disc hugging the active strands; the shared prerequisite is one new tool,
   the record of a realization (unit R1).
5. Realistic cost for 76(1)+77-83(words): ≈ 20-24k lines (FINAL §7 assumed ≈ 6-8k for 77-82); plus 76(2)
   2.5-4k and 76(3) 7.5-11k (the rock).  Row 83 on the smooth class is `represent` + `presentations` +
   `word_bound` (8 lines, done in the skeleton).

## 1. Readings (recorded once; every row docstring cites them)

* **R-front (FR-4/FR-5).** "the front type-I moves", "an oriented cusp-skein interchange", "deleting an empty
  zigzag": operations on Rutherford words (sm-3:1906-1908 "Use Rutherford's elementary front words"; the patterns
  1955-1956, 1977-1978, 1988-1989, 1995-1996, 2014-2015, 2027-2029, 2046-2049, 2087-2089).  A front acted on is
  `realize W : PLFront`; `B(front) = (realize W).defect`.  Cost of the alternative (stating 77-82 on arbitrary
  fronts of ng:front-domain): one would first have to DEFINE a type-I move on a smooth front, which the source
  does not do — not a faithful option.  What IS narrowed: the class of fronts; closed by `represent`.
* **R-quantities.** `D = PLFront.downCount`, `w = PLFront.writhe = diagram.writhe`, `s = sCount`,
  `d = degAZ (P F.diagram)`; a PL front is its own rounding (FINAL §2 G1 (ii)); `B = defect`
  (FrontPL.lean:462 = ng:defect sm-3:1896-1899).
* **R-smooth (FR-1).** Rows 76(2,3), 83 on `SmoothFront` (row 73 accepted); `d`, `B` on a rounding `S` with
  `F.IsRounding S` (FrontSmooth.lean:1479, 1506); independence of `S` is row 74 (accepted).
* **R-circle.** Row 81's second sentence on `PLFront` with `IsStandardCircles` (FrontPL.lean:513): the smallest
  accepted class carrying "simple crossing-free component with exactly one left and one right cusp"
  (sm-3:2053-2054).  Every realization is a `PLFront`, so the descent's base is an instance.  Cost: the
  planarity fact `D = c` is accepted only for realizations (FrontRealizeStandard.lean:603, FrontRealizeBase
  :573); the general PL version is leaf L-PL (1.5-2.5k).  Fallback (word reading, ~100 lines): if the reviewers
  or the horizon demand it, replace the two fields by `∀ W, (realize W).IsStandardCircles → ...`.
* **R76-2 ("deformations through fronts without a singular event").** `SmoothFront.NonsingularDeformation F F'`:
  a family `path : ℝ → SmoothFront`, `path 0 = F`, `path 1 = F'`, same `c`, jointly `C^∞` on `[0,1] × ℝ`.
  "Without a singular event" = every `path t` is in the class of ng:front-domain (the class forbids exactly the
  singular events).  Joint smoothness is needed (a `C^0` family does not control the cusp set).  Mild
  strengthening of the hypothesis: smoothness on `[0,1] × ℝ` rather than on a neighbourhood.
* **R76-3 ("represented by a finite elementary front word").** `∃ W, D, w, s equal ∧ ∀ S, IsRounding S →
  RecordIso S.record (realize W).diagram.record`.  A smooth front and a PL front can only be "the same" through
  their invariants and named records (rp:record-polynomial); this is exactly what row 83 consumes.  The printed
  proof ("separate singularities by small local x translations ... read successive vertical cuts") produces such
  a `W`; the record clause is its content.
* **Deletion directions only (FR-6).** `IsTypeI`/`IsTypeII` are the deletion directions; the row clauses are
  equalities, so the creation direction is the same statement.
* **Empty word.** `realize ⟨[], _⟩` is the standard circle (β2 convention); no row hypothesis produces `[]`
  (`Pres.two_le_of_target_nil`, `IsZigzagDeletion.ne_nil`; type I from `[]`-closed words is untypable), and the
  `s` clauses are stated on realizations, so the convention never enters (checked in the skeleton: the
  nonemptiness helpers `IsZigzagDeletion.source_ne_nil`, `IsCrossedCuspShortcut.ne_nil`, `IsCuspSkein.ne_nil`).

## 2. Clause maps (printed clause → field; tex lines)

| row | printed clause | field (Statements_B.lean) |
|---|---|---|
| 76 :1922-1924 | "Disjoint-gadget commutations ... preserve D, w, d, and hence B" | `comm_D`, `comm_w`, `comm_d`, `comm_B` on `IsComm` (FrontWords.lean:412-418; index shift built in) |
| 76 :1923-1924 | "deformations through fronts without a singular event preserve D, w, d, and hence B" | `deform_D`, `deform_w`, `deform_d`, `deform_B` (R76-2; `d`, `B` on roundings) |
| 76 :1925-1926 | "Every supplied finite front can be represented by a finite elementary front word." | `represent` (R76-3) |
| 77 :1951 | "The front type-I moves preserve B." | `typeI_B` on `IsTypeI` (:425) |
| 78 :1973 | "The front type-II moves preserve D, w, d, and hence B." | `typeII_D/w/d/B` on `IsTypeII` (:433) |
| 79 :1991 | "The front type-III moves preserve D, w, d, and hence B." | `typeIII_D/w/d/B` on `IsTypeIII` (:441) |
| 80 :2010-2011 | "Deleting an empty zigzag lowers s by two and cannot increase B" | `zigzag_s` (`s' + 2 = s`), `zigzag_B` (`B' ≤ B`) on `IsZigzagDeletion` (:450) |
| 80 :2011-2012 | "applying the crossed-cusp shortcut lowers s by one and cannot increase B" | `crossedCusp_s`, `crossedCusp_B` on `IsCrossedCuspShortcut` (:456) |
| 81 :2047-2048 | "Deleting a separated standard front circle with nonempty remainder preserves B." | `circleDeletion_B` on `IsCircleDeletion` (:463; nonempty remainder built in) |
| 81 :2048-2049 | "A single standard front circle ... has B = 0" | `single_B : ∀ F : PLFront, IsStandardCircles → Γ.c = 1 → defect = 0` |
| 81 :2048-2049 | "and any union of such circles, has B = 0" | `union_B` |
| 82 :2077-2080 | "For either principal direction ..., B of the earlier branch ≥ min(B other branch, B compatible smoothing)" | `earlier_branch` on `IsCuspSkein` (:483, symmetric = "either direction") |
| 82 :2080 | "the unique compatible smoothing" | `unique_smoothing` (`C.letters = C'.letters`) |
| 82 :2080-2081 | "The smoothing has one fewer singularity" | `smoothing_s` |
| 82 :2081-2082 | "the principal branches have the same singularity count" | `principal_s` |
| 83 :2307-2311 | "For every front F on the domain of Definition ng:front-domain, with the same polynomial evaluated on its actual ordinary cusp rounding, w(F) − D(F) ≤ −deg_a P_{S(F)} − 1" | `front_inequality : ∀ F S, F.IsRounding S → F.writhe − D ≤ −degAZ (P S) − 1` |

Proof displays that are NOT clauses but skeleton leaves: ng:type-I-counts (`typeI_counts`), ng:zigzag-counts
(`zigzag_counts`), ng:crossed-cusp-counts (`crossedCusp_counts`), ng:circle-counts (`circleDeletion_counts`,
`degAZ_delta`), the (t,u) table (`skein_downCount`, `skein_site`'s sign disjunction), ng:skein-plus/minus and
degree-plus/minus (`degAZ_le_of_eq_pos/neg`, `switch_of_recursion_pos/neg`), ng:skein-defect's second line
(`ng_cusp_skein_both`).

## 3. Findings that change the FINAL cost model (read before estimating)

* **F1 — the move disc must be spectator-free.** `ArcCover U A` (LinkMoves.lean:208) says "a traversal point
  evaluates into U iff it lies on one of the arcs A"; `RIData.cover : ArcCover U {a}` (:576), `RIIData` `{a, b}`,
  `RIIIData` `{a, b, c}`, `OrientedSmoothingData` `{a, b}`.  A full-height block rectangle (`blockRect`,
  FrontRealizeGeometry.lean:86; `clean_blockRect` :414; `BlockSetup.outsideMatch` :1624) contains every
  spectator strand crossing the block, so it is NOT admissible as `U` unless the word has no spectator.  The
  β2 report's "what rows 77-82 can consume" (§4, §6) therefore does not deliver the move data; the disc has to be
  a convex polygon hugging the active strands (a spectator below a cusp column slopes parallel to the active
  strand, one unit lower, so a convex `U` between them exists; the entry/exit cut points must be vertices of
  `∂U`, the interior active points strictly inside).
* **F2 — length-changing moves change the spectators' traces.** For `X P Y` vs `X P' Y` with `|P| ≠ |P'|`, a
  spectator below the letters is a broken line in one realization and a straight segment in the other, so the
  two realizations never agree outside a small disc; and `Deform` cannot change vertex counts, `Reparam` needs a
  subdivision construction (none accepted).  Resolution (P5'): compare `realize (X P Y)` with the diagram
  `D := ⟨(shadowOf …).withVertices V, …⟩` obtained by moving only the interior vertices of the ACTIVE strands
  (same slots, same `next`, same components: `MoveMatch` with `e := Equiv.refl`, `φ := Equiv.refl` up to
  `Outside`), build the `RI/RII/RIII` data in a hugging disc, and transport `P D = P (realize (X P' Y))` by a
  RECORD isomorphism (R1 below, with the removed crossings deleted).  The smoothing of row 82 reconnects strands
  and so cannot be a vertex-moved realization: use the accepted `exists_smoothing_record` (Smoothing.lean:8178)
  and compare records.
* **F3 — the record of a realization is the central new tool (R1).**  Needed by 76(1) (the printed proof:
  "equivalently, the full named records are the same"), 80a (no crossing touched), 81(1) (`P_addFree`,
  PolynomialBlock.lean:1036, the record form of lp:split-circle — no `Reparam` for `IsSplitCircleAddition`), 82
  (`A'` vs the switch of `A`; the smoothing record), and F2's transport.
* **F4 — counts are syntactic.**  `realize_downCount : (realize W).downCount = W.downCountSyn`,
  `realize_writhe`, `realize_sCount` (FrontRealizeCorrespondence.lean:901-915) reduce every `ΔD`, `Δw`, `Δs` to
  list lemmas (`downCountFrom`/`writheFrom` over `X ++ P ++ Y` with the typed cut before `P`); the printed
  displays are the local values (already `decide`-checked in FrontWords.lean for the patterns).
* **F5 — the three `s` laws, `base_B` and the descent are done.**  `wordMoves_pres_s/del_s/skein_s`
  (:1000-1028), `realize_isStandardCircles_of_base`/`realize_downCount_eq_c_of_base` (FrontRealizeBase.lean:566,
  573), `ng_finite_word_bound` (FrontInterfaces.lean:499).  The skeleton's `certificate_laws`, `word_bound`,
  `base_defect_nonneg` compile from the row theorems alone.

## 4. Proof plan per leaf group (statements are in Skeleton_B.lean; here the route and the tools)

**L-deg (4 leaves; ~250 lines).** `delta_ne_zero`: `R.delta = (a − a⁻¹) z⁻¹`, `a − a⁻¹ ≠ 0` (distinct
monomials), units, `IsDomain R` (LinkLaurentRing.lean:103).  `degAZ_delta = 1`: `degA_mul` (:753) with
`degA (a − a⁻¹) = 1` (`degA_single`, :436) and `degA zInv = 0`.  `degAZ_le_of_eq_pos/neg`: `degA_add_le` (:431),
`degA_sub_le`, `degA_mul` with `degA_aInv = −1`, `degA_a = 1`, `degA_z = 0` (:439-441), then `degA_eq_degAZ` (:449)
to descend from `WithBot ℤ`.  `switch_of_recursion_pos/neg` are PROVED (`linear_combination` with `R.a_mul_aInv`,
:177).  `degAZ_delta_pow` is PROVED from the two leaves.

**L-cnt (8 leaves; ~900 lines).** Prove `Word.downCountFrom_append`, `writheFrom_append` (run of the prefix),
then for each pattern the local value at the typed cut (the `decide` checks of FrontWords.lean become lemmas
with `A ++ L` cuts: `step_prefix`, `act_*`).  `comm_counts` uses `run_comm_above/below` (FrontWords.lean:889-935)
and that `downBit`/`signBit` of a letter depend only on the bits at its own positions.  `skein_downCount` is
the (t,u) table's last column (`run_skein_A/A'/Ctop/Cbottom`, :840-870).  Then `realize_downCount`/`realize_writhe`
(words nonempty by the pattern).

**R1 — the record of a realization (new module, ~2.5-3.5k lines; prerequisite of L-rec and L-geo).**
`slotRecord W spec : Record` (LinkRecord.lean:309) with `M` = the σ-visit slots `(k, p)`, `letterAt W k = σ m`,
`p ∈ {m, m+1}` (or a given `spec` of active slots for the vertex-moved case), `comps` = cycles of `next`
(`Orbit`/`numComp`, FrontRealizeSlots.lean), `succ` = first visit slot along `next`, `pair` = the other slot of
the letter, `isOver` = the descending strand (`overStrand_crossingOf`), `sgn` = `signBit` (`sign_crossingOf`).
Theorem `realizeRecordIso : RecordIso (realizeAt pl hW hne).diagram.record (slotRecord W σspec)`: components
via `idxEquiv`/`toSlot_succ` (FrontRealizeSlots.lean:1282, 1291) and `slotOf_succ` (FrontRealize.lean:747);
`nextVisit` (LinkDiagramRecord.lean:258, the cyclic successor in the sorted `compList`) = the next visit slot
because every piece carries at most one crossing point, at parameter 1/2 (`crossingParam_eq_half`,
FrontRealizeGeometry.lean:1403), so the visit order along a component is the edge order.  Variant R1b for
`D := ⟨(shadowOf …).withVertices V, gen, over⟩` whose crossings are exactly a subset of the σ-slots on the same
edges (hypothesis supplied by the geometric row).

**L-rec (5 leaves).** `P_comm` (~700): `slotRecord (X[a,b]Y) ≅ slotRecord (X[b',a']Y)` by the slot bijection
"identity outside the two columns, the exchanged gadgets' slots by the index shift" commuting with `next`
(`run_comm_*` give the cuts); then `presentations` (PolynomialBlock.lean:1177).  `P_zigzag` (~500): no σ in the
factor, visit slots correspond by the column shift (the geometry lane's `shiftIdx`/`extSlot` machinery,
FrontRealizeGeometry.lean:479-778, is reusable for the exterior), `next` commutes.  `P_circleDeletion` (~600):
`slotRecord (X l_m r_m Y) ≅ (slotRecord (XY)).addFree` (`Record.addFree`, PolynomialBlock.lean:911), then
`P_addFree`.  `skein_site` (~1.2k): `x := crossingOf … (σ m)`; switch record: `slotRecord A' ≅ (slotRecord
A).switch v` (LinkRecord.lean:655) by the slot bijection `(k+1,m) ↦ (k+1,m+2)`, `(k+1,m+1) ↦ (k+1,m)`,
`(k+1,m+2) ↦ (k+1,m+1)`, identity elsewhere (commutes with `next` for both orientations), visits `through ↦
through`, `arm ↦ arm`; smoothing: `exists_smoothing_record_visit` (Smoothing.lean:8185) gives `D₀` with
`RecordIso D₀.record ((realize A).record.smooth v)`, and `slotRecord (A).smooth v ≅ slotRecord C` is the
reconnection `T ↦ arm` (`run_skein_*`, the (t,u) table fixes which arm); signs from `sign_crossingOf` and
`realize_writhe`.  `skein_unique` (~150): the first differing index of `A`, `A'` is `|X|`; the reverse-direction
case is contradictory (`l (m+1) = l m'`, `l m = l (m'+1)`).

**L-geo (4 leaves; the expensive ones).** Shared infrastructure (~2k): a convex polygon `U` as an intersection
of half-planes with the parallel-offset spectator argument, `Clean` (frontier injectivity on the cut points),
`ArcCover` for the active arcs, the vertex-moved diagram `D` (genericity of `withVertices V`, crossing
characterization), the trivial `MoveMatch` (`Equiv.refl`), R1b.  Then per row: `P_typeIII` — directly between
the two realizations (same length, same cut sequence): `U` = the band `[x_k, x_{k+3}] × [−(m+2)−ε, −m+ε]`
(no spectator slopes: only σ letters), `OutsideMatch` by the conjugating slot bijection (~1k), `RIIIData`
(LinkMoves.lean:639: three arcs, one strict height order = "the three over/under choices give one strict height
order", opposite visit order along each arc) (~1.2k), `P_reidemeister_III` (PolynomialBlock.lean:607).
`P_typeII` (~3k): `D` = `realize (X l_{m−1} σ_m σ_{m−1} Y)` with the through strand's two interior vertices
lifted above the arms; `RIIData` (:599; "the through-strand is under at both crossings"); `P_reidemeister_II`;
`P D = P (realize (X l_m Y))` by R1b + the column-shift slot bijection.  `P_typeI` (~2.5k): `D` = the curl
realization with the through strand straightened past the cusp pair; `RIData` (:569) with the kink in
`realize`; then R1b to `realize (X Y)`.  `P_crossedCusp` (~2.5k): `D` = `realize (X l_i σ_i Y)` with the arms'
interior vertices uncrossed; `RIData` with a kink of sign −1; R1b to `realize (X l_i (!d) Y)` (the bit flip is
the arms' exchange of exits).  Mirror/reverse carriers (`mirrorCarries_RI`, `reverseCarries_RI`, LinkMoves.lean
:1676, 3071) may halve the right-cusp cases.

**L-PL (1 leaf; 1.5-2.5k, or 0.1k under the word fallback).** For a `PLFront` union of standard circles, each
component is two x-monotone PL arcs between its left and right cusp; embedded ⇒ one arc lies above the other
(IVT on the difference of the two graph functions, which never vanishes because there is no crossing); the arm
order at a cusp (`isDownCusp_iff_armIn_above`, FrontPL.lean:292) then gives exactly one downward cusp.

**L-smooth (4 leaves).** `deform_downCount`, `deform_writhe`, `deform_P` (2.5-4k together): along a jointly
smooth family the cusp set and the double-point set vary continuously and finitely (transversality is open;
`cusp_alone`, `no_triple` are open conditions), so `IsDownCusp`, `crossSign` are locally constant in `t`
(sign of a nonvanishing continuous function on `[0,1]`), and the `Marking`/`GeomRounding` of `F` transports to
`F'` (FrontGeomModel.lean:332 `isRounding_iff_geomModel`); `P` by `presentations`.  `represent` (7.5-11k, FINAL
§8 risk 1, ~40 % in horizon): a PL model of a smooth front carrying its record + a vertical sweep reading the
word; the skeleton keeps it as ONE named leaf so that everything else can close first.

## 5. Unit split and effort (Lean lines; calibration: β2 landed at 6.7k against 2.5-5k)

| unit | leaves | est. | depends on |
|---|---|---|---|
| U-deg | L-deg (4) | 0.25k | — (start now) |
| U-cnt | L-cnt (8) | 0.9k | — (start now; closes every count field of 76-82 and row 80's `s`) |
| U-R1 | `slotRecord`, `realizeRecordIso`, R1b | 2.5-3.5k | — (start now; the critical path) |
| U-rec1 | `P_comm`, `P_zigzag`, `P_circleDeletion` | 1.8k | U-R1 |
| U-rec2 | `skein_site`, `skein_unique` | 1.4k | U-R1 (+ accepted `exists_smoothing_record_visit`) |
| U-geo0 | hugging disc, vertex-moved diagram, trivial `MoveMatch` | 2k | U-R1 (for R1b) |
| U-geoIII | `P_typeIII` | 2.5k | U-geo0 (band disc; no vertex move) |
| U-geoII | `P_typeII` | 3k | U-geo0 |
| U-geoI | `P_typeI` | 2.5k | U-geo0 |
| U-geoX | `P_crossedCusp` | 2.5k | U-geo0 |
| U-PL | L-PL | 1.5-2.5k (0.1k fallback) | — |
| U-smooth1 | `deform_*` | 2.5-4k | — (row 76 fields only; not on row 83's path) |
| U-smooth2 | `represent` | 7.5-11k | — (row 83's only remaining obligation once the words close) |
| **rows 77-82 + 76(1) + 83 on words** | | **≈ 20-24k** | |
| **all of 76-83** | | **≈ 30-39k** | |

Order: U-deg, U-cnt, U-R1 in parallel; then U-rec1/U-rec2 and U-geo0; then the four geometric rows in parallel;
U-PL and U-smooth1 whenever a lane is free; U-smooth2 last.  Rows 80(s), 82(s), and every `D`/`w` field can be
accepted early (row-level acceptance needs all fields, so 80 and 82 wait for their polynomial leaves).

## 6. Row 83: the chain, with exact statements (all compile in Skeleton_B.lean)

1. `certificate_laws : (wordMovesOf (fun W => (realize W).sCount) (fun W => (realize W).defect)
   OWord.IsStandardCircleBase).Laws` — `pres_B` from `comm_B`, `typeI_B`, `typeII_B`, `typeIII_B`; `del_B` from
   `zigzag_B`, `crossedCusp_B`, `circleDeletion_B`; `skein_B` from `earlier_branch`; `pres_s/del_s/skein_s` =
   `wordMoves_pres_s/del_s/skein_s` (definitional transfer: same `s`, same relations); `base_B` =
   `base_defect_nonneg` (accepted `realize_isStandardCircles_of_base`, `realize_downCount_eq_c_of_base`,
   `P_crossingFree`, `degAZ_delta_pow`).
2. `word_bound : ∀ W : OWord, 0 ≤ (realize W).defect := ng_finite_word_bound _ _ certificate_laws`
   (FrontInterfaces.lean:499; consumes `SM.ng_finite_word`, accepted 04:56Z).
3. `front_inequality`: `represent F` gives `W`; `presentations S _ (hrec S hS) : P S = P (realize W).diagram`;
   `F.defect S = (realize W).defect`; `defect_nonneg_iff` (FrontSmooth.lean:1524).
   The alternative geometric-base route (`finiteWordStatement_wordMoves_of` + `word_bound_of` on `SM.wordMoves`)
   is equivalent and not needed.

## 7. Fidelity risks to record (new; FR-1..FR-7 remain)

* **FR-8 (class narrowing of 77-82).** Stated on realizations of closed oriented words; closed by `represent`
  (76), which is unproved for now.  Until then rows 77-82 are faithful statements about word fronts and row 83
  is a faithful statement whose proof has exactly one open named obligation.
* **FR-9 (R76-2).** "Deformation ... without a singular event" read as a jointly `C^∞` family inside the class
  on `[0,1] × ℝ`, constant `c`.  Reviewers may ask whether `C^k` or a neighbourhood of `[0,1]` was meant; the
  chosen hypothesis is stronger, so the clause is (slightly) weaker than the most liberal reading.
* **FR-10 (R76-3).** "Represented by" = equal `D`, `w`, `s` and a record isomorphism of every rounding with the
  realization's diagram.  Alternative readings (a nonsingular deformation to a front "read off" as the word)
  cannot be stated across the smooth/PL boundary without exactly these invariants.
* **FR-11 (R-circle).** Row 81 sentence 2 on `PLFront`; the descent uses only the realization instance.  If
  L-PL stalls, the word reading is a 100-line fallback and a recorded narrowing.
* **FR-12 ("unique").** `unique_smoothing` renders the definite article; it is a theorem about `IsCuspSkein`, not
  a hypothesis.  "or its reflected pattern" (ng:finite-word) = the other principal direction (R4 of the accepted
  interface); right-cusp templates are outside the row (sm-3:2162-2164, "by relabeling").
* **FR-13 (P through `lp_lm`).** Every polynomial clause reaches the literature interface `SM.lp_lm` through
  `P` (as `PLFront.defect` itself does); expected and unchanged.
* **FR-14 (the base of the axiom).** `SM.ng_finite_word` has the syntactic base `IsStandardCircleBase`; the
  descent's `base_B` is proved on it directly (no converse of the base bridge needed; β2 open item 1 stays open
  and is not on the path).
* **FR-15 (F1/F2 above).** The geometric rows do not use the geometry lane's block-rectangle tools for the move
  discs; they use them only for the exterior index shift.  Recorded so that reviewers do not expect
  `BlockSetup.outsideMatch` in the proofs.

## 8. Accepted declarations used (file:line)

FrontPL.lean: `PLFront.defect` 462, `IsStandardCircles` 513, `.writhe_eq_zero` 518, `.defect_eq` 554,
`isDownCusp_iff_armIn_above` 292.  FrontWords.lean: `IsCommStep/IsComm` 412/418, `IsTypeI/II/III` 425/433/441,
`IsZigzagDeletion` 450, `IsCrossedCuspShortcut` 456, `IsCircleDeletion` 463, `IsCuspSkeinStep/IsCuspSkein`
475/483, `run_*` 500-935, `*.sCount` 1035-1090, `Moves.Chain` 1149, `Moves.Laws` 1156, `defect_nonneg` 1180,
`wordMovesOf` 1201, `word_bound_of` 1237.  FrontInterfaces.lean: `NgFiniteWordClauses` 450, `ng_finite_word` 480,
`ng_finite_word_bound` 499.  FrontRealize.lean: `realizeAt` 1221, `realize` 1243, `slotOf_succ` 747.
FrontRealizeSlots.lean: `idxEquiv` 1282, `toSlot_succ` 1291.  FrontRealizeCorrespondence.lean: `realize_sCount/
downCount/writhe` 901/911/915, `wordMoves` 928, `wordMoves_pres_s/del_s/skein_s` 1000/1010/1028,
`IsZigzagDeletion.ne_nil` 951.  FrontRealizeBase.lean: `realize_isStandardCircles_of_base` 566,
`realize_downCount_eq_c_of_base` 573, `finiteWordStatement_wordMoves_of` 592.  FrontRealizeDeform.lean:
`P_realizeAt_eq_realize` 234.  FrontRealizeGeometry.lean: `blockRect` 86, `clean_blockRect` 414, `SameEffect` 479,
`shiftIdx`/`extSlot`/`next_ext` 479-778, `BlockSetup` 1034, `outsideMatch` 1624, `crossingParam_eq_half` 1403.
FrontRealizeStandard.lean: `IsStandardCircles.downCount_eq_c` 603.  FrontSmooth.lean: `SmoothLoop` 166,
`SmoothFront` 305, `downCount/writhe/sCount` 724-730, `IsRounding` 1479, `defect` 1506, `defect_nonneg_iff` 1524.
FrontGeomModel.lean: `isRounding_iff_geomModel` 332.  FrontWordsBase.lean: `isStandardCircleBase_comm_invariant`
441.  LinkMoves.lean: `IsDisc` 100, `Arc` 145, `ArcCover` 208, `OutsideMatch` 316, `Clean` 342, `LocalFrame` 348,
`MoveMatch` 356, `ReparamData` 372, `DeformData/Deform` 462/478, `PlanarIsotopic` 516, `RIData/RI` 569/590,
`RIIData/RII` 599/629, `RIIIData/RIII` 639/700, `OrientedSmoothingData` 713, `IsOrientedSmoothing` 743,
`IsSkeinTriple` 751, `IsSplitCircleAddition` 1088, `IsOrientedSmoothing.switch` 1988.  PolynomialBlock.lean:
`P_planar` 604, `P_reidemeister_I/II/III` 605-607, `P_circle` 609, `P_skein` 638, `P_crossingFree` 688,
`P_recursion_pos/neg` 693/697, `P_ne_zero` 793, `Record.addFree` 911, `P_addFree` 1036, `P_split_circle` 1085,
`presentations` 1177.  LinkLaurentRing.lean: `R` 76, `a_mul_aInv` 177, `R.delta` 193, `degA` 392,
`degA_add_le` 431, `degA_single` 436, `degA_a/aInv/z/one` 439-443, `degAZ` 446, `degA_eq_degAZ` 449,
`degAZ_mul` 733, `degA_mul` 753.  LinkRecord.lean: `Record` 309, `RecordIso` 539, `switch` 655, `smooth` 895.
LinkDiagram.lean: `Diagram` 490, `IsPositive` 547, `sign` 552, `writhe` 577, `componentCount` 580, `switch` 650,
`switch_switch` 710.  LinkDiagramRecord.lean: `nextVisit` 258.  Smoothing.lean: `exists_smoothing_record` 8178,
`exists_smoothing_record_visit` 8185.
