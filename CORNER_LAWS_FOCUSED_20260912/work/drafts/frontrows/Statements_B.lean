import SM.FrontRealizeGeometry
import SM.FrontRealizeBase
import SM.FrontRealizeDeform
import SM.FrontInterfaces
import SM.FrontWordsBase
import SM.FrontGeomModel
import SM.PolynomialBlock

/-! # Front certificate rows 76-83 — STATEMENTS (TAG B, literal-fidelity variant)

Draft 2026-09-14, work/drafts/frontrows/Statements_B.lean.  Plan: PLAN_B.md next to this file.  Nothing
here is proved: exactly eight `sorry`, one per row theorem.  Design of record:
work/reports/front-block-design-FINAL-20260913.md (§2 G1, §3, §5 items 3-6, §9 FR-4/FR-5) and the
AUTHOR_NOTES entries FR-1..FR-7, D-F1..D-F5, "ng:finite-word ACCEPTED", "hinv obligation closed",
"CV:lem:piececurve ACCEPTED (round 2); β2 ported".

## The reading (recorded here once; each row docstring cites it)

* **R-front (FR-5).**  The certificate section opens "Use Rutherford's elementary front words"
  (sm-3:1906) and every move of rows 77-82 is *defined* by a word pattern (sm-3:1955-1956, 1977-1978,
  1995-1996, 2014-2015, 2027-2028, 2087-2089).  So a "front" acted on by a move is the realization of a
  closed oriented word, `SM.realize W : PLFront` (β2), and "the front type-I moves preserve B" reads
  `∀ W W' : OWord, IsTypeI W.letters W'.letters → (realize W).defect = (realize W').defect`.  This is the
  FINAL design's reading; it is NOT a narrowing of the moves (they exist only on words) but it IS a
  narrowing of the class of fronts (realizations of words instead of arbitrary fronts of Definition
  ng:front-domain).  The narrowing is closed by the second sentence of ng:commutation ("Every supplied
  finite front can be represented by a finite elementary front word", sm-3:1925-1926), rendered as the
  field `represent` of row 76 on the printed smooth class: the representation theorem, the block's rock.
* **R-quantities.**  On a realization `F = realize W`: `D(F) = F.downCount`, `w(F) = F.writhe`
  (`= F.diagram.writhe`), `s(F) = F.sCount`, `d(F) = degAZ (P F.diagram)` (a PL front is its own rounding:
  wedge cusps are legal corners of `Shadow.Generic`; FINAL §2 G1 (ii)), `B(F) = F.defect`
  (`SM/FrontPL.lean:462`, `= D − w − degAZ (P F.diagram) − 1`, display ng:defect sm-3:1896-1899).
* **R-smooth.**  Rows 76 (clauses 2, 3) and 83 are on the printed class `SmoothFront` (row 73, accepted)
  with `D`, `w`, `s` its finite-set counts and `d`, `B` read on a rounding `S` with `F.IsRounding S`
  (`F.defect S`, FR-1).
* **R-circle.**  Row 81's second sentence is about fronts that are standard circles; the smallest
  accepted class carrying the geometric predicate "simple crossing-free component with exactly one left
  and one right cusp" (sm-3:2053-2054) is `PLFront` with `PLFront.IsStandardCircles`
  (`SM/FrontPL.lean:513`); the clause is stated there (every realization is a `PLFront`).
* **Deletion directions only** (FR-6): `IsTypeI`, `IsTypeII` are the deletion directions; "the front
  type-I moves preserve B" is an equality, so the creation direction is the same statement read backwards.

Checked with `lake env lean` (Lean v4.34.0-rc2, the project's Mathlib pin). -/

namespace SM

open SM.FrontWord SM.Link
open scoped ContDiff

/-! ## Vocabulary for row 76, clause 2: a deformation through fronts without a singular event -/

/-- A *deformation through fronts without a singular event* from `F` to `F'` (ng:commutation,
sm-3:1923-1924): a family `path t` of fronts of Definition ng:front-domain, `t ∈ [0,1]`, from `F` to `F'`,
on a fixed set of parameter circles, jointly `C^∞` in `(t, u)`.  Reading R76-2: "without a singular
event" is membership of every `path t` in the printed class (`SmoothFront` forbids exactly the singular
events — a vanishing derivative that is not a semicubical cusp, a non-transverse or triple double point,
a cusp on another strand, a vertical tangency); the joint smoothness is the meaning of "deformation"
(a smooth one-parameter family).  The parameter circles are kept (`c_eq`), as in FR-3/FR-4. -/
structure SmoothFront.NonsingularDeformation (F F' : SmoothFront) where
  /-- the family of fronts -/
  path : ℝ → SmoothFront
  /-- it starts at `F` -/
  start : path 0 = F
  /-- and ends at `F'` -/
  stop : path 1 = F'
  /-- the same parameter circles throughout -/
  c_eq : ∀ t, (path t).c = F.c
  /-- jointly smooth in the deformation parameter and the curve parameter, on `[0,1] × ℝ` -/
  smooth : ∀ i : Fin F.c, ContDiffOn ℝ ∞
    (fun p : ℝ × ℝ => ((path p.1).comp (Fin.cast (c_eq p.1).symm i)).γ p.2) (Set.Icc 0 1 ×ˢ Set.univ)

/-! ## Row 76 — ng:commutation (sm-3:1921-1926) -/

/-- Lemma ng:commutation [Commutations and nonsingular deformation] (sm-3:1921-1926), one field per
printed assertion.  Sentence 1: "Disjoint-gadget commutations and deformations through fronts without
a singular event preserve D, w, d, and hence B" — two subjects × four quantities = eight fields;
commutations on closed oriented words (`IsComm`, `SM/FrontWords.lean:415`: the two-strand index shift
of sm-3:1929-1931 is built in; reading R-front), deformations on the printed smooth class
(`NonsingularDeformation`, reading R76-2; `d` and `B` on roundings, FR-1).  Sentence 2: "Every supplied
finite front can be represented by a finite elementary front word" — field `represent`, reading R76-3:
"represented by" = the word's realization carries the front's `D`, `w`, `s` and the named record of
every rounding of the front (hence its polynomial, rp:record-polynomial).  This field is the block's
analytic bridge (FINAL §8 risk 1); it is a printed clause of the row, not a narrowing. -/
structure NgCommutationClauses : Prop where
  /-- "Disjoint-gadget commutations ... preserve D" -/
  comm_D : ∀ W W' : OWord, IsComm W.letters W'.letters →
    (realize W).downCount = (realize W').downCount
  /-- "Disjoint-gadget commutations ... preserve ... w" -/
  comm_w : ∀ W W' : OWord, IsComm W.letters W'.letters → (realize W).writhe = (realize W').writhe
  /-- "Disjoint-gadget commutations ... preserve ... d" -/
  comm_d : ∀ W W' : OWord, IsComm W.letters W'.letters →
    degAZ (P (realize W).diagram) = degAZ (P (realize W').diagram)
  /-- "Disjoint-gadget commutations ... preserve ..., and hence B" -/
  comm_B : ∀ W W' : OWord, IsComm W.letters W'.letters → (realize W).defect = (realize W').defect
  /-- "deformations through fronts without a singular event preserve D" -/
  deform_D : ∀ F F' : SmoothFront, Nonempty (F.NonsingularDeformation F') → F.downCount = F'.downCount
  /-- "deformations through fronts without a singular event preserve ... w" -/
  deform_w : ∀ F F' : SmoothFront, Nonempty (F.NonsingularDeformation F') → F.writhe = F'.writhe
  /-- "deformations through fronts without a singular event preserve ... d" (on roundings of the two
  fronts) -/
  deform_d : ∀ F F' : SmoothFront, Nonempty (F.NonsingularDeformation F') →
    ∀ S S' : Diagram, F.IsRounding S → F'.IsRounding S' → degAZ (P S) = degAZ (P S')
  /-- "deformations through fronts without a singular event preserve ..., and hence B" -/
  deform_B : ∀ F F' : SmoothFront, Nonempty (F.NonsingularDeformation F') →
    ∀ S S' : Diagram, F.IsRounding S → F'.IsRounding S' → F.defect S = F'.defect S'
  /-- "Every supplied finite front can be represented by a finite elementary front word." -/
  represent : ∀ F : SmoothFront, ∃ W : OWord,
    F.downCount = (realize W).downCount ∧ F.writhe = (realize W).writhe ∧ F.sCount = (realize W).sCount ∧
    ∀ S : Diagram, F.IsRounding S → Nonempty (RecordIso S.record (realize W).diagram.record)

/-- **ng:commutation** (sm-3:1921-1926). -/
theorem ng_commutation : NgCommutationClauses := sorry

/-! ## Row 77 — ng:front-I (sm-3:1950-1953) -/

/-- Lemma ng:front-I [Front type I] (sm-3:1950-1953): "The front type-I moves preserve B."  The move is
the word rewrite `IsTypeI` (sm-3:1955-1956: "Each word l_m σ_{m−1} r_m or l_m σ_{m+1} r_m replaces one
through-strand"; deletion direction, FR-6), read on realizations (R-front).  The proof's display
ng:type-I-counts (Δw = 1, ΔD = 1, Δd = 0) is a proof step, not a clause. -/
structure NgFrontIClauses : Prop where
  /-- "The front type-I moves preserve B." -/
  typeI_B : ∀ W W' : OWord, IsTypeI W.letters W'.letters → (realize W).defect = (realize W').defect

/-- **ng:front-I** (sm-3:1950-1953). -/
theorem ng_front_I : NgFrontIClauses := sorry

/-! ## Row 78 — ng:front-II (sm-3:1972-1975) -/

/-- Lemma ng:front-II [Front type II] (sm-3:1972-1975): "The front type-II moves preserve D, w, d, and
hence B."  The move is `IsTypeII` (sm-3:1977-1978 and the right-cusp versions of 1988-1989), read on
realizations (R-front); four fields for the four quantities. -/
structure NgFrontIIClauses : Prop where
  /-- "The front type-II moves preserve D" -/
  typeII_D : ∀ W W' : OWord, IsTypeII W.letters W'.letters →
    (realize W).downCount = (realize W').downCount
  /-- "... w" -/
  typeII_w : ∀ W W' : OWord, IsTypeII W.letters W'.letters → (realize W).writhe = (realize W').writhe
  /-- "... d" -/
  typeII_d : ∀ W W' : OWord, IsTypeII W.letters W'.letters →
    degAZ (P (realize W).diagram) = degAZ (P (realize W').diagram)
  /-- "..., and hence B" -/
  typeII_B : ∀ W W' : OWord, IsTypeII W.letters W'.letters → (realize W).defect = (realize W').defect

/-- **ng:front-II** (sm-3:1972-1975). -/
theorem ng_front_II : NgFrontIIClauses := sorry

/-! ## Row 79 — ng:front-III (sm-3:1990-1993) -/

/-- Lemma ng:front-III [Front type III] (sm-3:1990-1993): "The front type-III moves preserve D, w, d,
and hence B."  The move is `IsTypeIII` (sm-3:1995-1996, either direction), read on realizations
(R-front). -/
structure NgFrontIIIClauses : Prop where
  /-- "The front type-III moves preserve D" -/
  typeIII_D : ∀ W W' : OWord, IsTypeIII W.letters W'.letters →
    (realize W).downCount = (realize W').downCount
  /-- "... w" -/
  typeIII_w : ∀ W W' : OWord, IsTypeIII W.letters W'.letters → (realize W).writhe = (realize W').writhe
  /-- "... d" -/
  typeIII_d : ∀ W W' : OWord, IsTypeIII W.letters W'.letters →
    degAZ (P (realize W).diagram) = degAZ (P (realize W').diagram)
  /-- "..., and hence B" -/
  typeIII_B : ∀ W W' : OWord, IsTypeIII W.letters W'.letters → (realize W).defect = (realize W').defect

/-- **ng:front-III** (sm-3:1990-1993). -/
theorem ng_front_III : NgFrontIIIClauses := sorry

/-! ## Row 80 — ng:deletions (sm-3:2008-2012) -/

/-- Lemma ng:deletions [Zigzag and crossed-cusp deletion] (sm-3:2008-2012): "Deleting an empty zigzag
lowers s by two and cannot increase B; applying the crossed-cusp shortcut lowers s by one and cannot
increase B."  Four assertions; the operations are `IsZigzagDeletion` (sm-3:2014-2015) and
`IsCrossedCuspShortcut` (sm-3:2027-2029, with the printed direction flip), read on realizations
(R-front).  "cannot increase B": `B_after ≤ B_before`. -/
structure NgDeletionsClauses : Prop where
  /-- "Deleting an empty zigzag lowers s by two" -/
  zigzag_s : ∀ W W' : OWord, IsZigzagDeletion W.letters W'.letters →
    (realize W').sCount + 2 = (realize W).sCount
  /-- "Deleting an empty zigzag ... cannot increase B" -/
  zigzag_B : ∀ W W' : OWord, IsZigzagDeletion W.letters W'.letters →
    (realize W').defect ≤ (realize W).defect
  /-- "applying the crossed-cusp shortcut lowers s by one" -/
  crossedCusp_s : ∀ W W' : OWord, IsCrossedCuspShortcut W.letters W'.letters →
    (realize W').sCount + 1 = (realize W).sCount
  /-- "applying the crossed-cusp shortcut ... cannot increase B" -/
  crossedCusp_B : ∀ W W' : OWord, IsCrossedCuspShortcut W.letters W'.letters →
    (realize W').defect ≤ (realize W).defect

/-- **ng:deletions** (sm-3:2008-2012). -/
theorem ng_deletions : NgDeletionsClauses := sorry

/-! ## Row 81 — ng:circle (sm-3:2046-2050) -/

/-- Lemma ng:circle [Standard front circles] (sm-3:2046-2050): "Deleting a separated standard front
circle with nonempty remainder preserves B.  A single standard front circle, and any union of such
circles, has B = 0."  Sentence 1 on words (`IsCircleDeletion`, sm-3:2046-2049 read through the word
procedure: `l_m r_m` with nothing acting between, nonempty remainder built in; R-front).  Sentence 2 on
`PLFront` with the geometric predicate `IsStandardCircles` (reading R-circle; "in either orientation",
sm-3:2054, is covered because the predicate is orientation-free; nesting allowed, sm-3:2057-2058). -/
structure NgCircleClauses : Prop where
  /-- "Deleting a separated standard front circle with nonempty remainder preserves B." -/
  circleDeletion_B : ∀ W W' : OWord, IsCircleDeletion W.letters W'.letters →
    (realize W).defect = (realize W').defect
  /-- "A single standard front circle ... has B = 0." -/
  single_B : ∀ F : PLFront, F.IsStandardCircles → F.Γ.c = 1 → F.defect = 0
  /-- "and any union of such circles, has B = 0." -/
  union_B : ∀ F : PLFront, F.IsStandardCircles → F.defect = 0

/-- **ng:circle** (sm-3:2046-2050). -/
theorem ng_circle : NgCircleClauses := sorry

/-! ## Row 82 — ng:cusp-skein (sm-3:2076-2083) -/

/-- Lemma ng:cusp-skein [Cusp-skein inequality] (sm-3:2076-2083): "For either principal direction of an
oriented cusp-skein interchange, B of the earlier branch is at least the minimum of B of the other
principal branch and B of the unique compatible smoothing.  The smoothing has one fewer singularity;
the principal branches have the same singularity count."  The interchange is `IsCuspSkein A A' C`
(eq. ng:cusp-words sm-3:2087-2089 with spectator offset, direction bits fixed from the printed (t,u)
table, `SM/FrontWords.lean:479-496`; `IsCuspSkein` is symmetric in `A`, `A'`, so quantifying over it is
"either principal direction": the earlier branch is `A`, the other principal branch `A'`, the compatible
smoothing `C`).  "unique": the field `unique_smoothing`.  Read on realizations (R-front). -/
structure NgCuspSkeinClauses : Prop where
  /-- "For either principal direction of an oriented cusp-skein interchange, B of the earlier branch is
  at least the minimum of B of the other principal branch and B of the unique compatible smoothing." -/
  earlier_branch : ∀ A A' C : OWord, IsCuspSkein A.letters A'.letters C.letters →
    min (realize A').defect (realize C).defect ≤ (realize A).defect
  /-- "the unique compatible smoothing": the interchange determines it -/
  unique_smoothing : ∀ A A' C C' : OWord, IsCuspSkein A.letters A'.letters C.letters →
    IsCuspSkein A.letters A'.letters C'.letters → C.letters = C'.letters
  /-- "The smoothing has one fewer singularity" -/
  smoothing_s : ∀ A A' C : OWord, IsCuspSkein A.letters A'.letters C.letters →
    (realize C).sCount + 1 = (realize A).sCount
  /-- "the principal branches have the same singularity count." -/
  principal_s : ∀ A A' C : OWord, IsCuspSkein A.letters A'.letters C.letters →
    (realize A').sCount = (realize A).sCount

/-- **ng:cusp-skein** (sm-3:2076-2083). -/
theorem ng_cusp_skein : NgCuspSkeinClauses := sorry

/-! ## Row 83 — ng:local-front-bound (sm-3:2305-2312) -/

/-- Theorem ng:local-front-bound [Individual-front polynomial bound] (sm-3:2305-2312): "For every front
F on the domain of Definition ng:front-domain, with the same polynomial evaluated on its actual ordinary
cusp rounding, w(F) − D(F) ≤ −deg_a P_{S(F)} − 1" (display ng:front-inequality).  On the printed class
(`SmoothFront`, row 73) with `S` any rounding (`F.IsRounding S`, FR-1; the value does not depend on the
choice by ng:smoothing-record, row 74).  Equivalent to `0 ≤ F.defect S`
(`SmoothFront.defect_nonneg_iff`, `SM/FrontSmooth.lean:1524`). -/
structure NgLocalFrontBoundClauses : Prop where
  /-- "For every front F on the domain of Definition ng:front-domain, with the same polynomial evaluated
  on its actual ordinary cusp rounding, w(F) − D(F) ≤ −deg_a P_{S(F)} − 1." -/
  front_inequality : ∀ (F : SmoothFront) (S : Diagram), F.IsRounding S →
    F.writhe - (F.downCount : ℤ) ≤ -degAZ (P S) - 1

/-- **ng:local-front-bound** (sm-3:2305-2312; consumes Literature input ng:finite-word through the word
bound, and rows 76-82). -/
theorem ng_local_front_bound : NgLocalFrontBoundClauses := sorry

end SM
