# Front block design — FINAL (judge), 2026-09-14 02:35 UTC / 10:35pm ET

Inputs judged: `work/reports/front-block-design-A-20260913.md` (+ sketch, 331 lines, two units) and
`work/reports/front-block-design-B-20260913.md` (+ sketch, 519 lines), the printed def ng:front-domain
(sm-3:1825-1841) and the block sm-3:1843-2400, 3328-3520, the accepted layer (`SM/LinkDiagram`, `LinkMoves`,
`LinkDiagramRecord`, `PolynomialBlock`, `Smoothing`, `LinkInterfaces`), `tools/claims.py` rows 73-94,
`work/lean/axiom-policy.json`. Every Lean claim below was re-checked with `lake env lean` (Lean v4.34.0-rc2,
Mathlib 85e3a25e): both panel sketches elaborate as their authors say (A: `sorry` only in the word-pattern
placeholders and `realize`; B: one `sorry`, the ng:smoothing-record body). The FINAL definitions of section 4
are in `work/reports/front-block-design-FINAL-20260913-sketch.lean.txt` (695 lines; the only `sorry` is
`realize`, the grid realization to build). Nothing was written under `work/lean`.

## 0. Verdict

**Winner: TAG B (the printed smooth class with a record bridge), with three grafts from TAG A.**

| design | fidelity | feasibility | reuse | sum | weighted (fidelity x2) |
|---|---|---|---|---|---|
| A — PL fronts on the accepted polygonal layer | 5 | 8 | 10 | 23 | 28 |
| B — printed smooth class + named-record marking | 8 | 6 | 7 | 21 | 29 |
| FINAL — B + grafts (section 3) | 9 | 7 | 9 | 25 | 34 |

Why fidelity is weighted double: the brief's own acceptance test is clause-by-clause comparison with the printed
text, and a class change on the *defined object* of row 73 is a review-blocking event for the whole block (rows 74,
83, 93, 94 all quantify over "fronts on the domain of Definition ng:front-domain"). A's class is not the printed
class and A says so honestly ("divergent", "class changed smooth -> PL", "no germ, no vanishing tangent"); the
printed sanction A cites (sm-3:337-343, corners in *diagrams* away from crossings) covers polygonal diagrams, not
fronts whose cusps are the whole point of the definition ("ordinary semicubical cusps ... in a semicubical
parameter u ... x''(0) != 0"). I put the probability that A's row 73 survives independent review at well under
one half; B's row 73 is faithful field by field, and its one weak clause (S(F) as a bare record marking) is
repaired by graft G2 below at a cost of ~100 statement lines.

Scoring notes (what moved each number):
- A fidelity 5: every *derived* datum (cusp side, up/down, over rule, D, w, s, the rounding relation) is faithful
  and A's `RoundingData` is the most literal rendering of sm-3:1838-1841 in either report; but the primary class is
  different, and the consumer fd:contact needs the smooth class (A: "fd:contact would need an unprinted smooth-to-PL
  front model lemma"). A feasibility 8, not 9: A's row 74 ("disc-local crossing-free replacement preserves the
  record, 800-1200 lines, shared with the smoothing gate") is not shared with anything that exists — the smoothing
  gate proved the record only for the *constructed* smoothing (`Smoothing.lean:8178 exists_smoothing_record`,
  8.2k lines for one constructive instance, against a 1.2-1.8k estimate in the design record); a relational
  `OutsideMatch`-based record lemma is a new order-transport theorem, realistically 3-5k lines. A's gate table is
  also stale: `P_ne_zero`, `P_skein`, `P_split_circle`, `P_circle`, `lmF_eq_of_recordIso` are accepted and depend
  only on `lp_lm` (checked with `#print axioms`), so 81, 82 and 74's polynomial clause are not gated.
- B fidelity 8, not 9: `IsRounding := Nonempty (Marking S)` drops the disc/arc clause of S(F) (B records this as
  risk 3 and says "must be documented, not hidden"); the derivative-form cusp criterion is standard but unproved
  against the normal form (risk 4). B feasibility 6: statements are cheap and typecheck, the word program is the
  same as A's, but 83/93 on the smooth class hinge on the analytic representation theorem (6-10k lines, B's own 40%
  in-horizon estimate) and the statement `forall F S, IsRounding F S -> ...` is non-vacuous only once that theorem
  supplies an S. B reuse 7: `Diagram.record`/`RecordIso`/`P`/`degAZ`/the move predicates are reused; the front
  class itself is new smooth infrastructure and B's word layer recomputes D, w by letter tracing.
- What both got right and the FINAL keeps: certificates 77-82 must be proved on grid realizations (B's section 4
  argument that records cannot carry disc-local moves is correct: `RII` needs planar adjacency that a record does
  not know); ng:finite-word stated on words; the abstract descent induction (B's `Calculus.defect_nonneg`, proved);
  the GAP-1/GAP-2 diagnosis for rows 89-91, 94 (confirmed: `HomflyClauses.descent` is over `LinkEquiv`,
  `LinkInterfaces.lean:118`, and Reidemeister's theorem is outside scope by design decision D2).

## 1. The two designs against the printed clauses of ng:front-domain (sm-3:1825-1841)

| printed clause | A (PL) | B (smooth) | FINAL |
|---|---|---|---|
| actual map of a nonempty finite union of parameter circles to the oriented (x,z) plane | `Shadow` (polygons) — class changed | `c >= 1`, `comp : Fin c -> SmoothLoop` (`C^inf`, 1-periodic) — faithful | B |
| finitely many transverse double points, no other singularities | `Γ.Generic` — faithful in PL | `doubles_finite`, `transverse`, `no_triple`; zeros of `γ'` are all cusps — faithful | B |
| ordinary semicubical cusps | x-reversal vertex — divergent (no germ) | `deriv = 0 -> det(γ'', γ''') != 0` — derivative form of the (u², u³) normal form (FR-2) | B |
| limiting tangent nonvertical, `x''(0) != 0` | built into the class | `(γ'' t).1 != 0` at cusps — faithful, parametrization-free | B |
| no vertical tangencies on regular arcs | every edge `dir.1 != 0` | `deriv != 0 -> (deriv).1 != 0` — faithful | B |
| cusps meet no other strand or singularity | `tail_off` | `cusp_alone` — faithful | B |
| over = smaller dz/dx | `overStrand` by slope | `IsOverUnder` by slope — faithful; `det_pos_iff_of_slope_lt` proved in both | B |
| downward cusp: upper arm -> lower arm | `0 < det eIn eOut` (checked correct) | `x''·det(γ'',γ''') < 0` (checked correct on both cusp sides; FR-2) | B |
| D, w, s | `Nat.card`, accepted writhe | finite sets, `crossSign` sum — faithful | B |
| S(F): disjoint clean cusp discs, simple regular arc, same oriented attachments, no crossing; "the resulting ordinary diagram" | `RoundingData` (discs, `OutsideMatch`, one arc) — faithful; identity rounding | `Marking` only — discs and arcs dropped (widened) | **graft G2**: `GeomRounding` (discs, intervals, agree/inside/regular/simple/no_crossing) then `Marking` of the cusp-free result (FR-1) |

## 2. What is adopted from where

**From B (the skeleton).** `SmoothLoop`, `Param`, `SameParam`, `SmoothFront` with one field per printed clause;
the derived `IsCusp`/`cuspDisc`/`IsDownCusp`/`IsUpCusp`/`IsLeftCusp`/`IsRightCusp` with the two proved xor lemmas;
`slope`, `IsOverUnder`, `crossSign`, `cuspSet`, `crossingPairs`, `downCount`, `upCount`, `writhe`, `sCount`, `slNg`;
the exact-germ certificate (`germFront_semicubical`: det = 8A², x'' = 2A; `germFront_cuspDisc` = 16A³, proved);
`occSet`/`Occ`/`Marking`; 1-based `Letter.step` typing; the list-rewrite move patterns; the abstract descent
induction (`defect_nonneg`, proved); the contact vocabulary of rows 84-92, 94 (`SmoothKnot`,
`GenericTransverseFront`, `vertical_tangent_up` proved, `gaussLinking`, `HasSl`, `ContactBoundStatement`).

**Graft G1 (from A): the PL front as the realization class.** A's `Front` becomes `PLFront` (generic polygonal
shadow, all edges nonvertical; cusps = x-reversal vertices; `cusp_det_ne_zero`, `isDownCusp_or_isUpCusp` proved).
`realize : OWord -> PLFront`, and the word-level `D`, `w`, `s`, `B` are read *geometrically* from the realization
(`PLFront.downCount`, `.writhe := diagram.writhe`, `.defect := D - w - degAZ (P diagram) - 1`) instead of by
letter tracing. Reasons: (i) `ΔD = 1`, `Δw = 1` in the certificates are then facts about geometry, as printed
(A's argument against a structural class); (ii) a PL front is itself a `Diagram` (wedge cusps are legal corners of
`Shadow.Generic`: `RegularPair` forbids only antiparallel edges), so no rounding relation is needed at word level
and the RI/RII/RIII/`OrientedSmoothingData` instances are built on `(realize W).diagram` directly; (iii) the
standard-circle base is a geometric predicate (`PLFront.IsStandardCircles`: no crossing, one left and one right
cusp per component), which avoids a syntactic characterisation that would wrongly admit the crossing-free zigzag
word `l_1 l_2 r_1 r_2` (s = 4, D = 3) as a base.

**Graft G2 (from A, transposed to the smooth class): the geometric rounding.** A's `RoundingData` clauses become
`SmoothFront.GeomRounding F G` on smooth loops `G` over the *same* parameter circles: disjoint clean discs `U c`
about each cusp, parameter intervals `I c`, `G = F` outside the intervals (hence literally the same oriented
attachments), the new arc inside its disc, regular, injective, creating no crossing. `Rounding F S` packs a
cusp-free `SmoothFront G`, `GeomRounding F G`, and `Marking G S`; `IsRounding F S := Nonempty (Rounding F S)`.
This restores the printed S(F) clause; the only non-literal step is the polygonal reading `Marking G S` of "the
resulting ordinary diagram", which is the accepted layer's reading of every diagram (def:positive-lift row,
sm-3:337-343, lem:gauss-pl-model) and is recorded as FR-1.

**Graft G3 (judge): split B's `Calculus` into `Moves` (definitions) and `Laws` (the seven B/s clauses).** The
literature axiom `SM.ng_finite_word` must be statable before rows 76-82 are proved; with B's bundled `Calculus` it
could not be (the instance needs the row proofs). Now `wordMoves : Moves` is a definition,
`ng_finite_word_statement := forall W : OWord, wordMoves.Chain W`, `certificate_laws_statement := wordMoves.Laws`
collects rows 76a-82 one field each, and `word_bound_of : Laws -> (forall W, Chain W) -> forall W, 0 <= B W` and
`localFrontBound_of : word_bound -> ng_commutation_word -> LocalFrontBoundStatement` are proved in the sketch
(the second is 8 lines: `P_eq_of_recordIso` + `omega`).

**Judge's additions.** Direction bits on the letters (`l m d`: the upper new arm travels rightward iff `d`; `r m`
requires opposite directions; `σ m` transports them), so that a local rewrite keeps the exterior cuts and the
typing forces the printed orientation facts (sanity: `[l 2 true, σ 1, r 2]` is typed on `[true]`, `[l 2 false, σ 1,
r 2]` on `[false]`, and `[l 2 true, σ 1, r 2]` on `[false]` is *rejected* — "both crossing arrows are rightward, or
both leftward when the entire strand is reversed", sm-3:1958-1960; all three by `decide`). `IsCrossedCuspShortcut`
flips the bit (`l i d σ i -> l i (!d)`: "flips the cusp direction because the boundary arms exchange places").
`IsCircleDeletion` requires a nonempty remainder. `IsComm` and the bits of `IsCuspSkein` are marked placeholders.

## 3. The chosen representation in one paragraph

Row 73 is the printed smooth class: a front is `c >= 1` `C^inf` 1-periodic maps `R -> Plane` with finitely many
cusps (zeros of `γ'` with `det(γ'', γ''') != 0` and `x'' != 0`), no vertical tangency on regular arcs, finitely
many transverse double points, no triple point, cusps alone; over = smaller `dz/dx`; downward iff
`x''·det(γ'',γ''') < 0`; `D`, `w`, `s` from the finite sets. `S(F)` is any polygonal `Diagram` carrying the named
record of a cusp-free smooth front obtained from `F` by the printed clean-disc cusp replacement (`GeomRounding`,
then `Marking`). Rows 77-82 and ng:finite-word live on closed *oriented* Rutherford words realized as PL fronts
(A's class), whose diagrams are their own roundings; row 83 on words is the abstract descent `defect_nonneg`;
row 83 on the smooth class is `localFrontBound_of` applied to the representation theorem (ng:commutation's second
sentence, the block's single analytic bridge, attacked last). Rows 84-92, 94 are stated with the smooth vocabulary.

## 4. Exact Lean definitions to write first (all typecheck; file `front-block-design-FINAL-20260913-sketch.lean.txt`)

Module `SM/FrontSmooth.lean` (row 73), abridged — every field name is a printed clause:

```lean
structure SmoothLoop where (γ : ℝ → Plane) (smooth : ContDiff ℝ ∞ γ) (periodic : Function.Periodic γ 1)
abbrev Param (c : ℕ) := Fin c × ℝ
def SameParam {c} (p q : Param c) : Prop := p.1 = q.1 ∧ ∃ n : ℤ, q.2 = p.2 + n

structure SmoothFront where
  c : ℕ;  hc : 0 < c;  comp : Fin c → SmoothLoop
  cusps_finite : {p : Param c | p.2 ∈ Set.Ico 0 1 ∧ deriv (comp p.1).γ p.2 = 0}.Finite
  cusp_semicubical : ∀ i t, deriv (comp i).γ t = 0 →
    det (iteratedDeriv 2 (comp i).γ t) (iteratedDeriv 3 (comp i).γ t) ≠ 0
  cusp_nonvertical : ∀ i t, deriv (comp i).γ t = 0 → (iteratedDeriv 2 (comp i).γ t).1 ≠ 0
  no_vertical : ∀ i t, deriv (comp i).γ t ≠ 0 → (deriv (comp i).γ t).1 ≠ 0
  doubles_finite : {q : Param c × Param c | … q.1 ≠ q.2 ∧ eval q.1 = eval q.2}.Finite
  transverse : ∀ p q, ¬ SameParam p q → eval p = eval q → det (vel p) (vel q) ≠ 0
  no_triple : …
  cusp_alone : ∀ p q, ¬ SameParam p q → vel p = 0 → eval p ≠ eval q

def cuspDisc (p) : ℝ := (F.acc p).1 * det (F.acc p) (F.jerk p)
def IsDownCusp (p) : Prop := F.IsCusp p ∧ F.cuspDisc p < 0      -- upper arm → lower arm
def IsLeftCusp (p) : Prop := F.IsCusp p ∧ 0 < (F.acc p).1
def slope (p) : ℝ := (F.vel p).2 / (F.vel p).1                 -- over = smaller slope
def crossSign (p q) : ℤ := if 0 < det (F.vel p) (F.vel q) then 1 else -1
def downCount : ℕ := (F.cuspSet.filter F.IsDownCusp).card
def writhe : ℤ := ∑ q ∈ F.crossingPairs, F.crossSign q.1 q.2
def sCount : ℕ := F.crossingPairs.card + F.cuspSet.card
def CuspFree : Prop := ∀ i t, deriv (F.comp i).γ t ≠ 0

structure Marking (S : Diagram) where                      -- the named record (ng:smoothing-record's list)
  e : Fin F.c ≃ Fin S.Γ.c;  Φ : F.Occ ≃ S.Γ.Visit;  comp_eq : …;  between_iff : … (cycBetween ↔ cycBetween)
  pair_eq : … Φ q = S.twin (Φ p);  over_iff : … (S.overBit (Φ p) = true ↔ F.slope p.1 < F.slope q.1)
  sgn_eq : … (S.sign (Φ p).1 : ℤ) = F.crossSign p.1 q.1

structure GeomRounding (G : Fin F.c → SmoothLoop) where     -- sm-3:1838-1840, literal
  U : F.Cusp → Set Plane;  I : F.Cusp → Set ℝ
  disc : ∀ c, IsDisc (U c);  center : ∀ c, F.eval c.1 ∈ interior (U c)
  interval : ∀ c, ∃ a b, a < c.1.2 ∧ c.1.2 < b ∧ b - a < 1 ∧ I c = Set.Ioo a b
  disjoint : ∀ c c', c ≠ c' → Disjoint (U c) (U c')
  clean : ∀ c q, F.eval q ∈ U c → q.1 = c.1.1 ∧ ∃ n : ℤ, q.2 + n ∈ I c
  agree : ∀ i t, (∀ c, c.1.1 = i → ∀ n : ℤ, t + n ∉ I c) → (G i).γ t = (F.comp i).γ t
  inside : ∀ c, ∀ t ∈ I c, (G c.1.1).γ t ∈ U c;  regular : ∀ c, ∀ t ∈ I c, deriv (G c.1.1).γ t ≠ 0
  simple : ∀ c, Set.InjOn (G c.1.1).γ (I c)
  no_crossing : ∀ c, ∀ t ∈ I c, ∀ q, ¬ SameParam (c.1.1, t) q → (G q.1).γ q.2 ≠ (G c.1.1).γ t

structure Rounding (S : Diagram) where
  G : SmoothFront;  hc : G.c = F.c;  cuspFree : G.CuspFree
  geom : F.GeomRounding (fun i => G.comp (Fin.cast hc.symm i));  mark : G.Marking S
def IsRounding (S : Diagram) : Prop := Nonempty (F.Rounding S)
def defect (S : Diagram) : ℤ := (F.downCount : ℤ) - F.writhe - degAZ (P S) - 1     -- B(F)

def ng_smoothing_record_statement : Prop := ∀ F S S', F.IsRounding S → F.IsRounding S' →
    Nonempty (RecordIso S.record S'.record) ∧ P S = P S'
def LocalFrontBoundStatement : Prop := ∀ (F : SmoothFront) (S : Diagram), F.IsRounding S →
    F.writhe - (F.downCount : ℤ) ≤ -degAZ (P S) - 1                                   -- rows 83 and 93
```

Module `SM/FrontPL.lean` (graft G1; A's code verbatim under the name `PLFront`), `SM/FrontWords.lean`:

```lean
structure PLFront where (Γ : Shadow) (generic : Γ.Generic) (nonvertical : ∀ s, (Γ.dir s).1 ≠ 0)
def IsCusp (s) : Prop := (F.eIn s).1 * (F.eOut s).1 < 0;   def IsDownCusp (s) := F.IsCusp s ∧ 0 < det (F.eIn s) (F.eOut s)
def diagram : Diagram := ⟨F.Γ, F.generic, F.overStrand, F.overStrand_mem⟩   -- over = smaller slope
def defect : ℤ := (F.downCount : ℤ) - F.writhe - degAZ (P F.diagram) - 1
def IsStandardCircles : Prop := IsEmpty F.Γ.Crossing ∧ ∀ i, Nat.card {s // s.1 = i ∧ F.IsLeftCusp s} = 1 ∧ …

inductive Letter | l (m : ℕ) (d : Bool) | r (m : ℕ) | σ (m : ℕ)
abbrev Cuts := List Bool                                   -- strand directions at a cut, top to bottom
def Letter.step : Letter → Cuts → Option Cuts             -- 1-based; r needs opposite bits; σ transports them
def Word.Closed (W : Word) : Prop := Word.run W [] = some []
structure OWord where (letters : Word) (closed : letters.Closed)
def realize (W : OWord) : PLFront := sorry                -- TO BUILD
def IsTypeI (W W' : Word) : Prop := ∃ X Y m d, 2 ≤ m ∧ (W = X ++ [.l m d, .σ (m-1), .r m] ++ Y ∨ …) ∧ W' = X ++ Y
-- IsTypeII, IsTypeIII, IsComm, IsZigzagDeletion, IsCrossedCuspShortcut, IsCircleDeletion, IsCuspSkein likewise

structure Moves where (α : Type) (s : α → ℕ) (B : α → ℤ) (Pres Del : α → α → Prop) (Skein : α → α → α → Prop) (Base : α → Prop)
inductive Moves.Chain : K.α → Prop | base | del | pres | skein            -- the principal chain of ng:finite-word
structure Moves.Laws : Prop where pres_B pres_s del_B del_s skein_B skein_s base_B   -- rows 76a-82
theorem Moves.defect_nonneg (L : K.Laws) (hfw : ∀ F, K.Chain F) : ∀ F, 0 ≤ K.B F   -- PROVED
def wordMoves : Moves := ⟨OWord, OWord.sCount, OWord.defect, Pres := comm ∨ typeI ∨ typeII ∨ typeIII, Del := zigzag ∨ crossedCusp ∨ circle, Skein := IsCuspSkein, Base := (realize ·).IsStandardCircles⟩
def ng_finite_word_statement : Prop := ∀ W : OWord, wordMoves.Chain W         -- shape of SM.ng_finite_word
def ng_commutation_word_statement : Prop := ∀ F : SmoothFront, ∃ W : OWord,
    F.downCount = (realize W).downCount ∧ F.writhe = (realize W).writhe ∧
    ∀ S, F.IsRounding S → Nonempty (RecordIso S.record (realize W).diagram.record)  -- 76b, THE ROCK
theorem localFrontBound_of (hw : word_bound_statement) (hrep : ng_commutation_word_statement) : LocalFrontBoundStatement  -- PROVED
```

## 5. Row order and the statements of the first rows

Order (gate-free items first; lp:core, rp:record-polynomial, lp:split-circle are accepted, so nothing in 73-83 is
gated by the polynomial block):

1. **ng:front-domain (73)** — `SM.front_domain_definition : FrontDomainDefinitionData`, a Prop bundle with one
   field per printed clause: `SmoothFront` fields ↔ clauses (docstring notation map), `isDownCusp_xor_isUpCusp`,
   `isLeftCusp_xor_isRightCusp`, `det_pos_iff_of_slope_lt`, `germFront_semicubical` + `germFront_cuspDisc` (the
   printed germ is in the class, x''(0) = 2A), `IsRounding` as `GeomRounding` + `Marking`, `sCount = crossings +
   cusps`, `defect = D - w - degAZ (P S) - 1`. 900-1200 lines. Reviewer lenses to pre-empt: FR-1, FR-2 below.
2. **ng:smoothing-record (74)** — `∀ F S S', F.IsRounding S → F.IsRounding S' → Nonempty (RecordIso S.record
   S'.record) ∧ P S = P S'`. Proof: (i) `GeomRounding F G → (G.Marking S → F.Marking S)` and back — the
   occurrences of `G` and `F` coincide as parameter sets (double points of `F` lie outside the discs by `clean` and
   `cusp_alone`; the new arcs create none by `no_crossing`), `G = F` on an open set around each occurrence so
   `slope`/`crossSign` agree (`Filter.EventuallyEq.deriv_eq`), the cyclic order is the same parameters — the
   printed proof sentence for sentence; (ii) two markings of `F` compose to a `RecordIso` (successor from the
   cyclic order via `cycNext_unique`, as in `Diagram.nextVisit_no_between`); (iii) `P_eq_of_recordIso`.
   1000-1400 lines.
3. **word layer + ng:front-III (79)** — `∀ W W' : OWord, IsTypeIII W.letters W'.letters → W.defect = W'.defect ∧
   W.sCount = W'.sCount`, via a concrete `RIIIData` on `(realize W).diagram`/`(realize W').diagram` in the letter's
   column and `P_reidemeister_III`; `D` unchanged (no cusp letter), `w` unchanged (same strands, bits transported).
4. **ng:front-II (78)** — same shape with `RIIData`, `P_reidemeister_II`; `ΔD = 0` (the cusp arms persist), `Δw = 0`
   (the two crossings have opposite signs: `det_pos_iff_of_slope_lt` with the arms' opposite x-directions).
5. **ng:front-I (77)** — `RIData` + `P_reidemeister_I`; in the deletion direction `Δw = -1`, `ΔD = -1` (one down and
   one up cusp among the two, `isDownCusp_or_isUpCusp`; the crossing is positive by the typed bits).
6. Then **ng:deletions (80)** (zigzag: `Deform` of the realization inside the rectangle + `P_planar`; crossed cusp:
   `RIData` with old sign -1 and the bit flip), **ng:circle (81)** (`IsSplitCircleAddition`, `P_split_circle`,
   `degAZ_mul` in a domain, `P_circle`/`P_crossingFree`), **ng:cusp-skein (82)** (`(realize A).diagram.switch x`,
   concrete `OrientedSmoothingData`, `P_skein`, the (t,u) table with the bits fixed, `degA_add_le` in ℤ form),
   **76a on words** (commutations = `PlanarIsotopic` realizations), the **ng:finite-word** statement (independent
   review), **83 on words** (`word_bound_of`), **93** (`ng_bound_form`, `Iff.rfl`), **92 + src:contact vocabulary**,
   statements of **84-88**; **76b** last (section 7); 89-91, 94 after the GAP decisions.

## 6. Dependency graph

```
73 SmoothFront + GeomRounding + Marking ──► 74 smoothing-record (marking transfer, compose, P_eq)
73 ──► 92 def:transverse-front / src:contact vocabulary ──► 94 statement (GAP-1, GAP-2)
PLFront (G1) ──► oriented words + typing ──► realize (grid) ──┬─► 79 III  ─┐
                                                              ├─► 78 II    │
                                                              ├─► 77 I     ├─► certificate_laws_statement (Laws)
                                                              ├─► 80 del   │
                                                              ├─► 81 circle│
                                                              ├─► 82 skein │
                                                              └─► 76a comm ┘
ng:finite-word (axiom on OWord; Chain) + Laws ──► 83 on words (defect_nonneg) ──► 76b ──► 83 on SmoothFront ──► 93
76a smooth (deformations of SmoothFront preserve D, w, record): statement now, proof deferred
84, 85, 86, 88 independent; 87 ◄ 85, 86; 89 ◄ smooth spatial class (GAP-1); 90 ◄ 89, rp; 91 ◄ 89, 90, 88, GAP-2
```

## 7. Effort (Lean lines; one prover lane; calibration: the smoothing gate's record bridge was estimated 1.2-1.8k in
the design record and landed at 8.2k, so every *geometric construction* row below carries a x1.5-2 tail risk)

| unit | estimate | notes |
|---|---|---|
| 73 | 900-1200 | 60% is in the sketch |
| 74 | 1000-1400 | marking transfer 400-600; composition 500-700; no geometry |
| PLFront layer (G1) | 500-700 | A's code, plus `IsStandardCircles`, letters ↔ cusps/crossings lemmas |
| oriented words, typing, counts | 600-900 | `Letter.step` is written; closedness preserved by each rewrite is a lemma |
| `realize` + `Generic` + nonvertical + letter/singularity correspondence | 2500-3500 (tail: 5k) | the volume is in `ArcCover`/`Clean`/`OutsideMatch` on grid coordinates |
| 79 / 78 / 77 | 700-1000 each | concrete `RIIIData`/`RIIData`/`RIData` in one grid column with arbitrary exterior |
| 80 | 900-1300 | `Deform` for the zigzag; RI with sign -1 for the crossed cusp |
| 81 | 400-600 | `degAZ (δ f) = degAZ f + 1` from `degAZ_mul`; last-component case |
| 82 | 1000-1500 | (t,u) table; `switch` + `OrientedSmoothingData`; `degAZ (f+g) ≤ max` in ℤ (~30 lines) |
| 76a words | 600-900 | commutations as `PlanarIsotopic` realizations |
| ng:finite-word statement | 300-400 | + the two index corrections (sm-3:2284-2290), `IsComm`, skein bits; independent review |
| 83 words + 93 | 400-600 | `Laws` instance = the row theorems; `word_bound_of`; `ng_bound_form` |
| 92, src:contact vocabulary | 500-800 | `sl` declared in ∃-form with its properties, per the CV lane's expectation |
| 84-88 statements | 1000-1500 total | proofs (Moser, ODE flows, Gauss integral, transversality) ≥ 30k, not planned |
| **plannable core** (73, 74, G1, words, realize, 77-82, 76a-words, axiom, 83w, 93) | **≈ 13,200 (11.4k-16.2k)** | ≈ 95-110 prover agent-hours at the observed 7-8 h/kloc; 3 lanes: (α) 73+74, (β) G1+words+realize then 79/78/77, (γ) 80-82 after realize |
| 76b representation (PL model of a smooth front 5-7k + PL vertical sweep to a word 2.5-4k) | 7,500-11,000 | the block's rock; ~40% in horizon |
| 76a smooth deformations | 2,500-4,000 | statement now |
| statements 89-91, 94 | 700-1100 | after the GAP decisions |
| **total planned** | **≈ 28,000 (25k-34k)** | A: 14.5k (PL-only, 74 underestimated); B: 29k |

## 8. Risks

1. **76b** (smooth front → oriented word whose realization carries every rounding's record): the only analytic
   theorem the ng rows need; 7.5-11k lines, ~40% in horizon. Without it: 83/93 are *stated* on the printed class
   and *proved* on words; `localFrontBound_of` makes the remaining obligation exactly one named statement. Fallback
   (only with Mark's OK, recorded as a class change on 83/93): state them on `PLFront` via the PL sweep alone.
2. **Non-vacuity of `IsRounding`**: existence of an `S` with `F.IsRounding S` for a smooth `F` is part of 76b
   (it needs a smooth cusp replacement — a bump-function construction, ~1-2k — and a polygonal model). Until then
   `LocalFrontBoundStatement` is a faithful but existentially unwitnessed statement; say so in the row docstring.
3. **`realize` and the certificate instances are mechanical but voluminous** (calibration above). Mitigation: one
   shared grid-geometry module (column rectangles as `IsDisc`, `Clean`, `OutsideMatch` between two words agreeing
   outside a column) built once and reused by 77-82.
4. **ng:finite-word fidelity** (FR-6): 1-based indices, deletion directions only in `Pres` ("Only deletion
   directions of types I and II occur here"), the (t,u) bits of the skein interchange, `IsComm`'s two-strand index
   shift, the two Rutherford corrections; no global chain-length bound may be added; independent review before any
   consumer.
5. **GAP-1** (rows 89-91, 94 evaluate `P` on a smooth spatial projection; only polygonal `Diagram`s exist) and
   **GAP-2** (cp:finite-contact-path derives `H_{D_ε} = H_{D_T}` from an *ambient isotopy*; `HomflyClauses.descent`
   is over `LinkEquiv`; ambient isotopy ⇒ `LinkEquiv` is Reidemeister's theorem, excluded by D2). Both need a policy
   decision from Mark (new documented interface, statement-only rows, or consuming CV:ax:slbound in the CV lane);
   no effort on 89-91, 94 before that.
6. **Rows 84-88**: statable now; proofs are multi-thousand-line analysis projects each; do not let them block the
   ng rows.

## 9. Fidelity risks to record in AUTHOR_NOTES before row 73 is stated

- **FR-1 (polygonal reading of S(F)).** Printed: "The resulting ordinary diagram is denoted S(F)" — a smooth
  cusp-free curve. Lean: `S` is a polygonal `Diagram` carrying the named record (`Marking`) of the cusp-free smooth
  front `G` produced by the literal clean-disc replacement (`GeomRounding`). This is the accepted layer's reading of
  every diagram (def:positive-lift row; sm-3:337-343 "a diagram here is a finite polygonal immersion, or a regular
  smooth immersion ..."; lem:gauss-pl-model "the crossing names, the four-ray orders, the traversal direction and
  the over/under designations are retained"). Consumers see only `P S`, which depends on the record alone
  (rp:record-polynomial, accepted). Must be cited in the row docstring and in each review of 73, 74, 83, 93.
- **FR-2 (cusp criterion in derivative form).** "Ordinary semicubical cusp ... in a semicubical parameter u ...
  x''(0) ≠ 0" is rendered as `deriv = 0 → det(γ'', γ''') ≠ 0 ∧ (γ'').1 ≠ 0` at the cusp parameter, and "traversed
  from its locally upper arm to its locally lower arm" as `x''·det(γ'', γ''') < 0`. Both are the standard unpacking
  (Bruce–Giblin) and are checked on the printed exact germ (`8A²`, `2A`, `16A³`, proved), but the equivalence with
  the (u², u³) normal form and the geometric upper/lower reading are not proved in Lean (an optional ~500-line Taylor
  lemma can supply the latter).
- **FR-3 (smoothness and parametrization).** "smooth" = `C^∞`; a parameter circle = a 1-periodic map of `ℝ`; "an
  actual map" is a parametrized map, and the record (occurrences, cyclic order) is read on the parameters.
- **FR-4 (parametrized rounding).** `GeomRounding` keeps the parameter circles of `F` and replaces `F` only on open
  intervals `I c` around the cusp parameters; "same oriented attachments" is thereby literal. A rounding in a
  different parametrization is covered because `Marking` is parametrization-free — the two readings agree on
  `P S`.
- **FR-5 (the PL/word layer is a proof device).** Rows 77-82 and ng:finite-word are stated on oriented Rutherford
  words and their grid PL realizations, as the printed certificate section is ("Use Rutherford's elementary front
  words"; "For an actual finite front word"). Rows 73, 74, 83, 93 are on the smooth class. The transfer is one named
  statement (`ng_commutation_word_statement`, the second sentence of ng:commutation). Rutherford's letters are
  unoriented; the direction bits quantify over *all* consistent orientations ("The permitted orientations need not
  produce a single component"), and the typing forces the printed orientation facts rather than assuming them.
- **FR-6 (ng:finite-word transcription).** Listed in risk 4. Plus: the axiom quantifies over closed oriented words
  only (no words with free ends), the base is `IsStandardCircles` of the realization (unions allowed, nesting
  allowed), and `Chain` encodes "stop at the first strict decrease of s or at the base" with `s` non-increasing
  before it as a *consequence* of the `Laws` (pres_s, skein_s), not as an axiom clause.
- **FR-7 (scope gaps, for rows 89-91, 94).** GAP-1 and GAP-2 of section 8, with the D2 citation
  (`LinkInterfaces.lean` header; `HomflyClauses.descent` over `LinkEquiv`).

## 10. Decisions needed from Mark (none blocks rows 73-83)

1. Approve the FINAL (B + grafts) and the AUTHOR_NOTES entry FR-1..FR-7 before row 73 is stated.
2. Whether to invest ~7.5-11k lines in 76b for a smooth-class 83/93 (recommended: yes, but last), or accept a
   recorded PL-class fallback for 83/93 if it stalls.
3. GAP-1/GAP-2 policy for 89-91, 94 (new documented interface / statement-only / CV:ax:slbound route).

## 11. Module plan

`SM/FrontSmooth.lean` (73: class, derived data, `Marking`, `GeomRounding`, `Rounding`, definition bundle),
`SM/FrontRecordBridge.lean` (74), `SM/FrontPL.lean` (G1), `SM/FrontWords.lean` (letters, typing, rewrites,
`Moves`/`Chain`/`Laws`, `wordMoves`), `SM/FrontRealize.lean` (grid realization + shared grid geometry),
`SM/FrontMoves{I,II,III}.lean`, `SM/FrontDeletions.lean`, `SM/FrontCircle.lean`, `SM/FrontCuspSkein.lean`,
`SM/FrontInterfaces.lean` (`SM.ng_finite_word`, `SM.src_contact` — policy names fixed), `SM/FrontBound.lean`
(83 words, 93, `localFrontBound_of`), `SM/FrontRepresentation.lean` (76b), `SM/ContactVocabulary.lean` (84-92, 94
statements). Names free: the existing `Cusp*`/`Contact*` modules are Chapter-1/2 corner geometry.
