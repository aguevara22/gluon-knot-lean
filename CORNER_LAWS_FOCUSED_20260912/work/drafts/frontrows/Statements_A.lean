import SM.FrontRealizeGeometry
import SM.FrontRealizeDeform
import SM.FrontRealizeBase
import SM.FrontWordsBase
import SM.FrontGeomModel

/-! # Statements_A — the eight front certificate rows (tools/claims.py rows 76-83)

Architect A (maximal reuse), 2026-09-14.  Source: reference/SM/sm-3-statesum.tex — ng:commutation 1921-1925
(proof 1926-1948), ng:front-I 1950-1952 (proof 1953-1970, display ng:type-I-counts 1964-1966), ng:front-II
1972-1974, ng:front-III 1990-1992, ng:deletions 2008-2011 (displays ng:zigzag-counts 2020-2022,
ng:crossed-cusp-counts 2034-2036), ng:circle 2046-2049 (display ng:circle-counts 2064-2067), ng:cusp-skein
2076-2082 (eq. ng:cusp-words 2087-2090, the (t,u) table 2107-2118, displays ng:skein-plus/minus 2137-2142,
ng:skein-defect 2158-2163), ng:local-front-bound 2305-2312 (display ng:front-inequality 2309-2311; proof
2313-2348 consumes the axiom `SM.ng_finite_word`).  Design of record: work/reports/front-block-design-FINAL-20260913.md
(§2 G1, §3, §5 items 3-6, §9 FR-5/FR-6); accepted layer: SM/FrontPL, FrontWords, FrontInterfaces,
FrontRealize*, FrontWordsBase, LinkMoves, PolynomialBlock, LinkLaurentRing, FrontSmooth, FrontRecordBridge.

## The reading (FR-5) — every certificate row is stated on closed oriented words through the realization

A front word `W : OWord` (β1) stands for the front `realize W : PLFront` (β2, `SM.realize`, the grid
realization, standard placement).  Every printed phrase "a front" in rows 76-82 is read on such realizations:

* `D(F)` = `(realize W).downCount`, `w(F)` = `(realize W).writhe`, `s(F)` = `(realize W).sCount`
  (`SM/FrontPL.lean`, geometric counts on the PL front; β2's `realize_downCount`/`realize_writhe`/`realize_sCount`
  identify them with β1's letter tracing);
* `d(F) = deg_a P_{S(F)}` (display ng:defect, sm-3:1896-1898) = `degAZ (P (realize W).diagram)`: a PL front is its
  own ordinary diagram (its cusps are legal corners), so the identity is its rounding `S(F) = F.diagram`
  (FINAL §2 G1 (ii)), and `P` is the accepted local polynomial (lp:core);
* `B(F)` = `(realize W).defect = D − w − degAZ (P ·) − 1` (`PLFront.defect`, display ng:defect);
* the moves are the word patterns of `SM/FrontWords.lean` (`IsComm`, `IsTypeI/II/III`, `IsZigzagDeletion`,
  `IsCrossedCuspShortcut`, `IsCircleDeletion`, `IsCuspSkein`; the certificate section itself is printed on
  Rutherford's words, sm-3:1904-1919), and "deformations through fronts without a singular event" are the PL
  deformations `PLFront.Deform` below (a generic `Deform` of the diagrams all of whose intermediate polygons
  are nonvertical).

**Narrowing disclosed.** The printed rows quantify over arbitrary fronts of Definition ng:front-domain (the
smooth class `SmoothFront`, row 73).  Here rows 76 (first sentence), 77-82 and the field `on_words` of 83 are
stated for fronts represented by finite elementary front words — exactly the fronts on which the printed
certificates are computed and the only ones the word procedure (ng:finite-word) ever visits.  The printed
justification is the SECOND sentence of ng:commutation, "Every supplied finite front can be represented by a
finite elementary front word" (sm-3:1924-1925): it is kept as a printed clause of row 76 (`representation`,
stated on the smooth class, FINAL's `ng_commutation_word_statement`, the block's single analytic bridge, unit
76b) and row 83's printed clause `on_fronts` is derived from `on_words` and it.  Two further readings:
(i) the deformation clause of row 76 is stated on the PL class (`PLFront.Deform`), not on smooth families —
the smooth-class deformation invariance is not stated (it is used by no consumer; see PLAN_A.md risk R-3);
(ii) "represented by" is read as: same `s`, same `D`, same `w`, and the realization's diagram carries the named
record of every rounding `S(F)` (hence the same `d` and `B` by rp:record-polynomial, accepted `presentations`).

Exactly eight `sorry`: the eight row theorems (fixed names `SM.ng_commutation`, `SM.ng_front_I`,
`SM.ng_front_II`, `SM.ng_front_III`, `SM.ng_deletions`, `SM.ng_circle`, `SM.ng_cusp_skein`,
`SM.ng_local_front_bound`).  Checked with `cd work/lean && lake env lean` on this file. -/

namespace SM

open SM.Link SM.FrontWord SM.FrontRealize

noncomputable section

/-! ## 0. Deformations of PL fronts without a singular event (for row 76) -/

namespace PLFront

/-- A deformation of PL fronts "through fronts without a singular event" (ng:commutation, sm-3:1922-1923),
in the PL reading: a generic deformation of the two diagrams (the accepted `DeformData`: a continuous path of
vertex tuples, every intermediate polygon generic with literally the same crossing pairs — no crossing is
created, destroyed or has its strands exchanged) all of whose intermediate polygons are nonvertical.  In the PL
class a cusp is an x-reversal vertex; the x-sign of an edge cannot change along a continuous path without
passing through a vertical edge, so no cusp is born, dies or changes side, and "signs, cusp directions and
cyclic attachments cannot change" (sm-3:1934-1936) is the content of the invariance clause. -/
structure DeformData (F F' : PLFront) extends SM.Link.DeformData F.diagram F'.diagram where
  /-- every intermediate polygon is nonvertical (no vertical tangency: no cusp event) -/
  nonvertical : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s : F.Γ.Strand,
    ((F.Γ.withVertices (γ t)).dir s).1 ≠ 0

/-- `F'` is obtained from `F` by a deformation through PL fronts without a singular event. -/
def Deform (F F' : PLFront) : Prop := Nonempty (DeformData F F')

end PLFront

/-! ## 1. ng:commutation (row 76, sm-3:1921-1925) -/

/-- **ng:commutation** (sm-3:1921-1925), one field per printed clause.  "Disjoint-gadget commutations and
deformations through fronts without a singular event preserve D, w, d, and hence B.  Every supplied finite
front can be represented by a finite elementary front word."  Reading: FR-5 (module docstring); a
disjoint-gadget commutation is `IsComm` (the two-strand index shift of sm-3:1929-1931 is in its definition);
a deformation without singular event is `PLFront.Deform`; `d(F) = deg_a P_{S(F)}` on the identity rounding. -/
structure NgCommutationData : Prop where
  /-- "Disjoint-gadget commutations ... preserve D, w, d": for closed oriented words `W`, `W'` related by a
  disjoint-gadget commutation, the fronts `realize W`, `realize W'` have the same `D`, `w` and `d`. -/
  commutation : ∀ W W' : OWord, IsComm W.letters W'.letters →
    (realize W).downCount = (realize W').downCount ∧ (realize W).writhe = (realize W').writhe ∧
      degAZ (P (realize W).diagram) = degAZ (P (realize W').diagram)
  /-- "... and hence B" (commutations): `B(realize W) = B(realize W')`. -/
  commutation_B : ∀ W W' : OWord, IsComm W.letters W'.letters →
    (realize W).defect = (realize W').defect
  /-- "deformations through fronts without a singular event preserve D, w, d": for PL fronts `F`, `F'`
  joined by a deformation through nonvertical generic polygons, `D`, `w` and `d` agree. -/
  deformation : ∀ F F' : PLFront, PLFront.Deform F F' →
    F.downCount = F'.downCount ∧ F.writhe = F'.writhe ∧ degAZ (P F.diagram) = degAZ (P F'.diagram)
  /-- "... and hence B" (deformations): `B(F) = B(F')`. -/
  deformation_B : ∀ F F' : PLFront, PLFront.Deform F F' → F.defect = F'.defect
  /-- "Every supplied finite front can be represented by a finite elementary front word." (sm-3:1924-1925):
  every front `F` of Definition ng:front-domain (the smooth class, row 73) is represented by a closed oriented
  word `W` — the front `realize W` has the same `s`, `D`, `w`, and its diagram carries the named record of every
  rounding `S(F)` of `F` (so `P_{S(F)} = P_{realize W}` by rp:record-polynomial, and `d`, `B` agree).  This is
  the block's single analytic bridge (FINAL §3, §8 risk 1: unit 76b, attacked last). -/
  representation : ∀ F : SmoothFront, ∃ W : OWord,
    F.sCount = (realize W).sCount ∧ F.downCount = (realize W).downCount ∧ F.writhe = (realize W).writhe ∧
      ∀ S : Diagram, F.IsRounding S → Nonempty (RecordIso S.record (realize W).diagram.record)

/-- **ng:commutation** (row 76). -/
theorem ng_commutation : NgCommutationData := sorry

/-! ## 2. ng:front-I (row 77, sm-3:1950-1952) -/

/-- **ng:front-I** (sm-3:1950-1952): "The front type-I moves preserve B."  The type-I move is the deletion of
the curl `l_m σ_{m−1} r_m` or `l_m σ_{m+1} r_m` on one through-strand (`IsTypeI W W'`, `W` the side with the
curl; FR-6: deletion direction, as the word procedure uses it).  Display ng:type-I-counts (`Δw = 1`, `ΔD = 1`,
`Δd = 0` in the direction creating the curl) is proof content: companion lemmas of the skeleton. -/
structure NgFrontIData : Prop where
  /-- "The front type-I moves preserve B." -/
  typeI_B : ∀ W W' : OWord, IsTypeI W.letters W'.letters → (realize W).defect = (realize W').defect

/-- **ng:front-I** (row 77). -/
theorem ng_front_I : NgFrontIData := sorry

/-! ## 3. ng:front-II (row 78, sm-3:1972-1974) -/

/-- **ng:front-II** (sm-3:1972-1974): "The front type-II moves preserve D, w, d, and hence B."  The type-II
move replaces `l_{m−1} σ_m σ_{m−1}` or `l_{m+1} σ_m σ_{m+1}` by `l_m` (and, "for right-cusp versions, follow
these same local strands backwards", sm-3:1988-1989: `σ_{m−1} σ_m r_{m−1}`, `σ_{m+1} σ_m r_{m+1}` by `r_m`);
`IsTypeII W W'`, `W` the side with the two crossings. -/
structure NgFrontIIData : Prop where
  /-- "The front type-II moves preserve D, w, d" -/
  typeII : ∀ W W' : OWord, IsTypeII W.letters W'.letters →
    (realize W).downCount = (realize W').downCount ∧ (realize W).writhe = (realize W').writhe ∧
      degAZ (P (realize W).diagram) = degAZ (P (realize W').diagram)
  /-- "... and hence B." -/
  typeII_B : ∀ W W' : OWord, IsTypeII W.letters W'.letters → (realize W).defect = (realize W').defect

/-- **ng:front-II** (row 78). -/
theorem ng_front_II : NgFrontIIData := sorry

/-! ## 4. ng:front-III (row 79, sm-3:1990-1992) -/

/-- **ng:front-III** (sm-3:1990-1992): "The front type-III moves preserve D, w, d, and hence B."  The type-III
move is `σ_{m+1} σ_m σ_{m+1} ↔ σ_m σ_{m+1} σ_m` (`IsTypeIII`, either direction). -/
structure NgFrontIIIData : Prop where
  /-- "The front type-III moves preserve D, w, d" -/
  typeIII : ∀ W W' : OWord, IsTypeIII W.letters W'.letters →
    (realize W).downCount = (realize W').downCount ∧ (realize W).writhe = (realize W').writhe ∧
      degAZ (P (realize W).diagram) = degAZ (P (realize W').diagram)
  /-- "... and hence B." -/
  typeIII_B : ∀ W W' : OWord, IsTypeIII W.letters W'.letters → (realize W).defect = (realize W').defect

/-- **ng:front-III** (row 79). -/
theorem ng_front_III : NgFrontIIIData := sorry

/-! ## 5. ng:deletions (row 80, sm-3:2008-2011) -/

/-- **ng:deletions** (sm-3:2008-2011): "Deleting an empty zigzag lowers s by two and cannot increase B;
applying the crossed-cusp shortcut lowers s by one and cannot increase B."  The empty zigzag is
`l_m r_{m+1}` or `l_{m+1} r_m` deleted (`IsZigzagDeletion W W'`); the crossed-cusp shortcut replaces
`l_i σ_i` by the uncrossed cusp `l_i` with flipped direction bit ("the boundary arms exchange places",
sm-3:2031-2032) and `σ_i r_i` by `r_i` (`IsCrossedCuspShortcut W W'`).  The displays ng:zigzag-counts and
ng:crossed-cusp-counts are proof content (companion lemmas). -/
structure NgDeletionsData : Prop where
  /-- "Deleting an empty zigzag lowers s by two" -/
  zigzag_s : ∀ W W' : OWord, IsZigzagDeletion W.letters W'.letters →
    (realize W').sCount + 2 = (realize W).sCount
  /-- "[Deleting an empty zigzag] cannot increase B" -/
  zigzag_B : ∀ W W' : OWord, IsZigzagDeletion W.letters W'.letters →
    (realize W').defect ≤ (realize W).defect
  /-- "applying the crossed-cusp shortcut lowers s by one" -/
  crossedCusp_s : ∀ W W' : OWord, IsCrossedCuspShortcut W.letters W'.letters →
    (realize W').sCount + 1 = (realize W).sCount
  /-- "[applying the crossed-cusp shortcut] cannot increase B" -/
  crossedCusp_B : ∀ W W' : OWord, IsCrossedCuspShortcut W.letters W'.letters →
    (realize W').defect ≤ (realize W).defect

/-- **ng:deletions** (row 80). -/
theorem ng_deletions : NgDeletionsData := sorry

/-! ## 6. ng:circle (row 81, sm-3:2046-2049) -/

/-- **ng:circle** (sm-3:2046-2049): "Deleting a separated standard front circle with nonempty remainder
preserves B.  A single standard front circle, and any union of such circles, has B = 0."  A separated
standard front circle is the factor `l_m r_m` (no letter acts between its cusps: crossing-free, nesting
allowed) and `IsCircleDeletion W W'` requires the nonempty remainder `W' ≠ []`; "a single standard front
circle, and any union of such circles" is the geometric base predicate `PLFront.IsStandardCircles` on the
realization (no crossing, exactly one left and one right cusp per component; FINAL §2 G1 (iii)).  Display
ng:circle-counts (`d`, `D` drop by one, `w` unchanged) is proof content. -/
structure NgCircleData : Prop where
  /-- "Deleting a separated standard front circle with nonempty remainder preserves B." -/
  circle_deletion_B : ∀ W W' : OWord, IsCircleDeletion W.letters W'.letters →
    (realize W).defect = (realize W').defect
  /-- "A single standard front circle, and any union of such circles, has B = 0." -/
  standard_circles_B : ∀ W : OWord, (realize W).IsStandardCircles → (realize W).defect = 0

/-- **ng:circle** (row 81). -/
theorem ng_circle : NgCircleData := sorry

/-! ## 7. ng:cusp-skein (row 82, sm-3:2076-2082) -/

/-- **ng:cusp-skein** (sm-3:2076-2082): "For either principal direction of an oriented cusp-skein
interchange, B of the earlier branch is at least the minimum of B of the other principal branch and B of the
unique compatible smoothing.  The smoothing has one fewer singularity; the principal branches have the same
singularity count."  The interchange is eq. ng:cusp-words `A = l₂σ₁`, `A' = l₁σ₂` with the compatible
smoothing `C_top = l₁` or `C_bottom = l₂` fixed by the (t,u) table (`IsCuspSkeinStep`, spectator offset
`m − 1`, direction bits as in `SM/FrontWords.lean`); "either principal direction" is the symmetric relation
`IsCuspSkein A A' C := IsCuspSkeinStep A A' C ∨ IsCuspSkeinStep A' A C` (`Skein` on closed words), so the
field `skein_B` for all triples is both lines of display ng:skein-defect. -/
structure NgCuspSkeinData : Prop where
  /-- "For either principal direction of an oriented cusp-skein interchange, B of the earlier branch is at
  least the minimum of B of the other principal branch and B of the unique compatible smoothing." -/
  skein_B : ∀ A A' C : OWord, Skein A A' C →
    min (realize A').defect (realize C).defect ≤ (realize A).defect
  /-- "The smoothing has one fewer singularity" -/
  smoothing_s : ∀ A A' C : OWord, Skein A A' C → (realize C).sCount + 1 = (realize A).sCount
  /-- "the principal branches have the same singularity count." -/
  principal_s : ∀ A A' C : OWord, Skein A A' C → (realize A').sCount = (realize A).sCount

/-- **ng:cusp-skein** (row 82). -/
theorem ng_cusp_skein : NgCuspSkeinData := sorry

/-! ## 8. ng:local-front-bound (row 83, sm-3:2305-2312) -/

/-- **ng:local-front-bound** (sm-3:2305-2312): "For every front F on the domain of Definition
ng:front-domain, with the same polynomial evaluated on its actual ordinary cusp rounding,
`w(F) − D(F) ≤ −deg_a P_{S(F)} − 1`" (display ng:front-inequality), i.e. `B(F) ≥ 0` (display ng:defect,
sm-3:1899-1900 "We will prove B(F) ≥ 0 for each front").  Two fields: the inequality on every front
represented by a closed oriented word (`realize W` with its identity rounding — the statement the word
procedure proves: strong induction on `s` along the principal chains of `SM.ng_finite_word`, rows 76-82 as
the laws, `SM.ng_finite_word_bound`), and the printed clause on the smooth class for every rounding `S(F)`
(derived from the first through row 76's `representation` and rp:record-polynomial; the dependence of
`deg_a P_{S(F)}` on the rounding is settled by ng:smoothing-record, row 74).  The consumer fd:ng-bound (row 93)
reads `on_fronts`. -/
structure NgLocalFrontBoundData : Prop where
  /-- the printed inequality `w(F) − D(F) ≤ −deg_a P_{S(F)} − 1` for every front `F = realize W`
  represented by a closed oriented word, `S(F) = F.diagram` (FR-5 reading) -/
  on_words : ∀ W : OWord,
    (realize W).writhe - ((realize W).downCount : ℤ) ≤ -degAZ (P (realize W).diagram) - 1
  /-- "For every front F on the domain of Definition ng:front-domain, with the same polynomial evaluated on
  its actual ordinary cusp rounding, `w(F) − D(F) ≤ −deg_a P_{S(F)} − 1`." -/
  on_fronts : ∀ (F : SmoothFront) (S : Diagram), F.IsRounding S →
    F.writhe - (F.downCount : ℤ) ≤ -degAZ (P S) - 1

/-- **ng:local-front-bound** (row 83). -/
theorem ng_local_front_bound : NgLocalFrontBoundData := sorry

end

end SM
