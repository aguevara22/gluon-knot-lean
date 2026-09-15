import SM.PolynomialBlock
import SM.TurningNumber
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Shift

/-! # Finite oriented fronts (Definition ng:front-domain)

Source: reference/SM/sm-3-statesum.tex:1825-1841 (row 73 of tools/claims.py, the DEFINE row that
opens the front block, rows 73-94).  Design: work/reports/front-block-design-FINAL-20260913.md
(§0-§5, §9 FR-1..FR-7, §11; winner TAG B, the printed smooth class, with the judge's graft G2, the
geometric rounding) and its typechecked sketch front-block-design-FINAL-20260913-sketch.lean.txt
§1-§5.  Intended home: `work/lean/SM/FrontSmooth.lean`.  Main declaration:
`SM.front_domain_definition : FrontDomainDefinitionData`.

## The printed text (sm-3:1825-1841, verbatim)

"A front F is an actual map of a nonempty finite union of parameter circles to the oriented
(x,z) plane, with finitely many transverse double points and ordinary semicubical cusps, no other
singularities, and no vertical tangencies on regular arcs. The limiting tangent at every cusp is
also nonvertical: in a semicubical parameter u with cusp at u=0, require x''(0)≠0. Cusps meet no
other strand or singularity. At a crossing the branch with smaller dz/dx is over. A downward cusp
is traversed from its locally upper arm to its locally lower arm. Write D(F) for the number of
downward cusps, w(F) for the sum of the over-first tangent-determinant crossing signs, and s(F)
for the number of crossings plus cusps.

In disjoint clean cusp discs replace each cusp by a simple regular arc with the same oriented
attachments and no crossing. The resulting ordinary diagram is denoted S(F)."

Used with it: display ng:defect (sm-3:1896-1899) `d(F) = deg_a P_{S(F)}`, `B(F) = D(F) − w(F) −
d(F) − 1`; the printed exact cusp germ `x = x₀ + Au², z = z₀ + Ay₀u² + ⅔Au³` (sm-3:2747, the
front of fd:generic-exact-germ; the page coordinates `X = (x−x₀)/A`, `Z = 3(z−z₀−y₀(x−x₀))/(2A)`
give `(X, Z) = (u², u³)`, sm-3:2749-2750); the standard crossing of sm-3:1908-1912 ("With both
arrows pointing right, the over-first tangent representatives (1,−1),(1,1) have determinant 2, so
this crossing is positive"); the words "left cusp", "right cusp" of sm-3:1906-1907.

## Printed notion → Lean

| printed | Lean |
|---|---|
| a parameter circle, smooth map to the plane | `SmoothLoop`: `γ : ℝ → Plane`, `ContDiff ℝ ∞ γ`, `Function.Periodic γ 1` (FR-3) |
| nonempty finite union of parameter circles | `SmoothFront.c : ℕ`, `hc : 0 < c`, `comp : Fin c → SmoothLoop`; a parameter is `Param c = Fin c × ℝ`, read modulo `SameParam` (same circle, parameters differing by an integer) |
| the oriented (x,z) plane | the accepted `Plane = ℝ × ℝ` with `.1 = x`, `.2 = z` and the accepted `det` (positive = counterclockwise) |
| finitely many transverse double points | `doubles_finite` (the ordered pairs of distinct parameters in `[0,1)` with equal image form a finite set, `doubleSet`), `transverse` (`det` of the two velocities `≠ 0`) |
| ordinary semicubical cusps | `cusps_finite`, `cusp_semicubical`: at every zero of `γ'`, `det(γ'', γ''') ≠ 0` (FR-2) |
| no other singularities | every non-immersive parameter is such a cusp (definitional: `IsCusp p ↔ vel p = 0`), every multiple point is a transverse double point: `no_triple` |
| no vertical tangencies on regular arcs | `no_vertical`: `γ' t ≠ 0 → (γ' t).1 ≠ 0` |
| limiting tangent at a cusp nonvertical, `x''(0) ≠ 0` | `cusp_nonvertical`: `γ' t = 0 → (γ'' t).1 ≠ 0` (FR-2) |
| cusps meet no other strand or singularity | `cusp_alone` |
| over = smaller dz/dx | `slope p = (vel p).2 / (vel p).1`; `IsOverUnder p q := IsDouble p q ∧ slope p < slope q` |
| over-first tangent-determinant crossing sign | `crossSign p q = if 0 < det (vel p) (vel q) then 1 else −1` on the over-first pair |
| downward cusp: upper arm → lower arm | `IsDownCusp p := IsCusp p ∧ cuspDisc p < 0`, `cuspDisc p = x''·det(γ'', γ''')` (FR-2); `IsUpCusp` with `0 <` |
| left / right cusp | `IsLeftCusp` (`0 < x''`, the cusp opens to the right), `IsRightCusp` (`x'' < 0`) |
| `D(F)` | `downCount` |
| `w(F)` | `writhe = ∑ q ∈ crossingPairs, crossSign q.1 q.2`, `crossingPairs` = the double points ordered over-first, one entry per double point (`crossingPairs_xor_swap`) |
| `s(F)` | `sCount = crossingPairs.card + cuspSet.card` |
| disjoint clean cusp discs; simple regular arc; same oriented attachments; no crossing | `GeomRounding F G` (fields `disc`, `center`, `disjoint`, `clean`; `inside`, `regular`, `simple`, `no_crossing`; `agree`) (FR-4) |
| the resulting ordinary diagram `S(F)` | `Rounding F S`: a cusp-free `SmoothFront G` with `GeomRounding F G`, read polygonally by `Marking G S`; `IsRounding F S := Nonempty (Rounding F S)` (FR-1) |
| the named record of a front on a polygonal diagram | `Marking F S`: component bijection (crossing-free circles included), occurrence bijection, cyclic orders, pairing, over/under bits, signs |
| `d(F)`, `B(F)` (display ng:defect) | `dOf F S = degAZ (P S)`, `defect F S = D − w − dOf − 1` |

## Fidelity readings recorded (FINAL §9, verbatim where relevant)

* **FR-1 (polygonal reading of S(F)).** Printed: "The resulting ordinary diagram is denoted S(F)" —
  a smooth cusp-free curve. Lean: `S` is a polygonal `Diagram` carrying the named record (`Marking`)
  of the cusp-free smooth front `G` produced by the literal clean-disc replacement (`GeomRounding`).
  This is the accepted layer's reading of every diagram (def:positive-lift row; sm-3:337-343 "a
  diagram here is a finite polygonal immersion, or a regular smooth immersion ..."; lem:gauss-pl-model
  "the crossing names, the four-ray orders, the traversal direction and the over/under designations
  are retained"). Consumers see only `P S`, which depends on the record alone (rp:record-polynomial,
  accepted; here `defect_eq_of_recordIso`). Must be cited in each review of 73, 74, 83, 93.
* **FR-2 (cusp criterion in derivative form).** "Ordinary semicubical cusp ... in a semicubical
  parameter u ... x''(0) ≠ 0" is rendered as `deriv = 0 → det(γ'', γ''') ≠ 0 ∧ (γ'').1 ≠ 0` at the
  cusp parameter, and "traversed from its locally upper arm to its locally lower arm" as
  `x''·det(γ'', γ''') < 0`. Both are the standard unpacking (Bruce–Giblin) and are checked on the
  printed exact germ (`8A²`, `2A`, `16A³`, proved: `germFront_semicubical`, `germFront_cuspDisc`;
  the arm comparison `germFront_later_arm_higher_iff`), but the equivalence with the (u², u³)
  normal form and the geometric upper/lower reading are not proved in Lean (an optional ~500-line
  Taylor lemma can supply the latter).  Why the sign is right: near a cusp `γ(t) − γ(0) = ½γ''t² +
  ⅙γ'''t³ + …`, the arm after the cusp (`t > 0`) lies on the side of the tangent line `ℝγ''` where
  `det(γ'', ·)` has the sign of `det(γ'', γ''')`, and for a nonvertical `γ''` that side is the upper
  one iff `x'' > 0`; so the later arm is the upper one iff `x''·det > 0`, i.e. the cusp is traversed
  upper → lower iff `x''·det < 0`.
* **FR-3 (smoothness and parametrization).** "smooth" = `C^∞`; a parameter circle = a 1-periodic
  map of `ℝ`; "an actual map" is a parametrized map, and the record (occurrences, cyclic order) is
  read on the parameters.
* **FR-4 (parametrized rounding).** `GeomRounding` keeps the parameter circles of `F` and replaces
  `F` only on open intervals `I c` around the cusp parameters; "same oriented attachments" is
  thereby literal. A rounding in a different parametrization is covered because `Marking` is
  parametrization-free — the two readings agree on `P S`.

Further readings made in this file (printed text over sketch where they differ):
* "finitely many transverse double points and ordinary semicubical cusps" is read as finitely
  many of each (`doubles_finite`, `cusps_finite`); for a `C^∞` map with the semicubical criterion
  the finiteness of cusps is in fact automatic (isolated zeros of `γ'` on a compact circle), so the
  field adds no strength.
* The printed germ is taken with its base point `(x₀, z₀)` (sm-3:2747), not translated to the
  origin as in the sketch.
* `IsCusp`, `IsDownCusp`, `slope`, `crossSign`, `eval` are invariant under `SameParam`
  (`eval_of_sameParam`, `vel_of_sameParam`, …), so the counts read on the fundamental period
  `[0,1)` (`cuspSet`, `doubleSet`) are the counts on the circles.

## Reuse of the accepted layer

`Plane`, `det` (SM/Polygon.lean); `IsDisc` (SM/LinkMoves.lean, the clean-disc vocabulary);
`Diagram`, `componentCount`, `sign`, `Shadow.Visit` (SM/LinkDiagram.lean); `Diagram.compOf`,
`visitCoord`, `twin`, `overBit`, `cycBetween`, `Diagram.record` (SM/LinkDiagramRecord.lean);
`RecordIso` (SM/LinkRecord.lean); `degAZ` (SM/LinkLaurentRing.lean); `P` (SM/LocalPolynomial.lean);
`presentations` = `P` depends only on the record (SM/PolynomialBlock.lean).  The accepted smooth
model `ClosedC1Curve` (SM/TurningNumber.lean) is *regular* by definition, so a front component
cannot be one; the bridge `SmoothLoop.toClosedC1Curve` / `SmoothFront.toClosedC1Curve` shows that
every cusp-free component is one (no duplication of the turning-number notions).

## Main declarations

`SmoothLoop`, `Param`, `SameParam`, `SmoothFront` (with `eval`, `vel`, `acc`, `jerk`, `IsCusp`,
`cuspDisc`, `IsDownCusp`, `IsUpCusp`, `IsLeftCusp`, `IsRightCusp`, `slope`, `IsDouble`,
`IsOverUnder`, `crossSign`, `cuspSet`, `doubleSet`, `crossingPairs`, `downCount`, `upCount`,
`writhe`, `sCount`, `slNg`, `CuspFree`, `occSet`, `Occ`, `Marking`, `Cusp`, `GeomRounding`,
`Rounding`, `IsRounding`, `dOf`, `defect`), `det_pos_iff_of_slope_lt`, `germFront` with
`germFront_semicubical`, `germFront_cuspDisc`, and the row bundle `FrontDomainDefinitionData` /
`front_domain_definition`.  Sorry-free; checked with `lake env lean`. -/

namespace SM

open Link
open scoped ContDiff

noncomputable section
open Classical

/-! ## 1. One parameter circle -/

/-- One parameter circle of a front: a `C^∞` map `γ : ℝ → Plane` of period `1` ("an actual map of
a ... parameter circle to the oriented (x,z) plane"; FR-3: smooth = `C^∞`, a parameter circle = a
1-periodic map of `ℝ`).  Not a `ClosedC1Curve`: that accepted class is regular by definition, a
front component has cusps. -/
structure SmoothLoop where
  /-- the map, `γ t = (x t, z t)` -/
  γ : ℝ → Plane
  /-- smooth -/
  smooth : ContDiff ℝ ∞ γ
  /-- the parameter circle `ℝ / ℤ` -/
  periodic : Function.Periodic γ 1

namespace SmoothLoop

variable (L : SmoothLoop)

theorem continuous : Continuous L.γ := L.smooth.continuous

theorem differentiable : Differentiable ℝ L.γ := L.smooth.differentiable (by decide)

theorem hasDerivAt (t : ℝ) : HasDerivAt L.γ (deriv L.γ t) t := (L.differentiable t).hasDerivAt

theorem continuous_deriv : Continuous (deriv L.γ) :=
  L.smooth.continuous_deriv (by exact_mod_cast le_top)

theorem contDiff_iteratedDeriv (n : ℕ) : ContDiff ℝ ∞ (iteratedDeriv n L.γ) := by
  rw [iteratedDeriv_eq_iterate]
  exact L.smooth.iterate_deriv n

theorem continuous_iteratedDeriv (n : ℕ) : Continuous (iteratedDeriv n L.γ) :=
  (L.contDiff_iteratedDeriv n).continuous

theorem eq_add_one (t : ℝ) : L.γ (t + 1) = L.γ t := L.periodic t

theorem eq_add_int (n : ℤ) (t : ℝ) : L.γ (t + n) = L.γ t := by
  have h := L.periodic.int_mul n t
  simpa using h

theorem comp_add_one : (fun t => L.γ (t + 1)) = L.γ := funext L.periodic

/-- The velocity of a parameter circle is 1-periodic. -/
theorem deriv_periodic : Function.Periodic (deriv L.γ) 1 := by
  intro t
  have h := deriv_comp_add_const L.γ 1 t
  rw [L.comp_add_one] at h
  exact h.symm

/-- Every iterated derivative of a parameter circle is 1-periodic. -/
theorem iteratedDeriv_periodic (n : ℕ) : Function.Periodic (iteratedDeriv n L.γ) 1 := by
  intro t
  have h := congrFun (iteratedDeriv_comp_add_const n L.γ 1) t
  rw [L.comp_add_one] at h
  exact h.symm

theorem deriv_eq_add_int (n : ℤ) (t : ℝ) : deriv L.γ (t + n) = deriv L.γ t := by
  have h := L.deriv_periodic.int_mul n t
  simpa using h

theorem iteratedDeriv_eq_add_int (k : ℕ) (n : ℤ) (t : ℝ) :
    iteratedDeriv k L.γ (t + n) = iteratedDeriv k L.γ t := by
  have h := (L.iteratedDeriv_periodic k).int_mul n t
  simpa using h

/-- Reuse of the accepted smooth model: a *regular* parameter circle is a `ClosedC1Curve`
(SM/TurningNumber.lean). -/
def toClosedC1Curve (h : ∀ t, deriv L.γ t ≠ 0) : ClosedC1Curve where
  γ := L.γ
  γ' := deriv L.γ
  hasDerivAt := L.hasDerivAt
  continuous_deriv := L.continuous_deriv
  regular := h
  periodic := L.periodic

@[simp] theorem toClosedC1Curve_γ (h : ∀ t, deriv L.γ t ≠ 0) : (L.toClosedC1Curve h).γ = L.γ := rfl

end SmoothLoop

/-! ## 2. Parameters of a finite union of circles -/

/-- A parameter of a front with `c` parameter circles: the circle index and a real parameter. -/
abbrev Param (c : ℕ) := Fin c × ℝ

/-- Two parameters name the same point of the same parameter circle: equal circle index and
parameters differing by an integer. -/
def SameParam {c : ℕ} (p q : Param c) : Prop := p.1 = q.1 ∧ ∃ n : ℤ, q.2 = p.2 + n

namespace SameParam

variable {c : ℕ}

theorem refl (p : Param c) : SameParam p p := ⟨rfl, 0, by simp⟩

theorem symm {p q : Param c} (h : SameParam p q) : SameParam q p := by
  obtain ⟨h1, n, hn⟩ := h
  refine ⟨h1.symm, -n, ?_⟩
  rw [hn]; push_cast; ring

theorem trans {p q r : Param c} (h : SameParam p q) (h' : SameParam q r) : SameParam p r := by
  obtain ⟨h1, n, hn⟩ := h
  obtain ⟨h2, m, hm⟩ := h'
  refine ⟨h1.trans h2, n + m, ?_⟩
  rw [hm, hn]; push_cast; ring

theorem fst_eq {p q : Param c} (h : SameParam p q) : p.1 = q.1 := h.1

/-- On the fundamental period `[0,1)` the relation is equality. -/
theorem eq_of_mem_Ico {p q : Param c} (hp : p.2 ∈ Set.Ico (0 : ℝ) 1) (hq : q.2 ∈ Set.Ico (0 : ℝ) 1)
    (h : SameParam p q) : p = q := by
  obtain ⟨h1, n, hn⟩ := h
  obtain ⟨hp0, hp1⟩ := hp
  obtain ⟨hq0, hq1⟩ := hq
  have h1' : (n : ℝ) < 1 := by linarith
  have h2' : (-1 : ℝ) < n := by linarith
  have h3 : n < 1 := by exact_mod_cast h1'
  have h4 : -1 < n := by exact_mod_cast h2'
  have hn0 : n = 0 := by omega
  subst hn0
  simp only [Int.cast_zero, add_zero] at hn
  exact Prod.ext h1 hn.symm

theorem iff_eq_of_mem_Ico {p q : Param c} (hp : p.2 ∈ Set.Ico (0 : ℝ) 1)
    (hq : q.2 ∈ Set.Ico (0 : ℝ) 1) : SameParam p q ↔ p = q :=
  ⟨eq_of_mem_Ico hp hq, fun h => h ▸ refl p⟩

/-- The representative of a parameter on the fundamental period `[0,1)`. -/
def rep (p : Param c) : Param c := (p.1, Int.fract p.2)

theorem rep_mem_Ico (p : Param c) : (rep p).2 ∈ Set.Ico (0 : ℝ) 1 :=
  ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩

theorem sameParam_rep (p : Param c) : SameParam p (rep p) := by
  refine ⟨rfl, -⌊p.2⌋, ?_⟩
  show Int.fract p.2 = p.2 + ((-⌊p.2⌋ : ℤ) : ℝ)
  rw [← Int.self_sub_floor]; push_cast; ring

end SameParam

/-! ## 3. The front class (sm-3:1825-1833), one field per printed clause -/

/-- Definition ng:front-domain, the class of finite oriented fronts (sm-3:1825-1833), one field per
printed clause.  Derivatives are those of the parametrization; the printed "semicubical parameter
u" is not needed because `γ' = 0 → det(γ'', γ''') ≠ 0` and `(γ'').1 ≠ 0` are parametrization-free
(FR-2). -/
structure SmoothFront where
  /-- number of parameter circles -/
  c : ℕ
  /-- "a nonempty finite union of parameter circles" -/
  hc : 0 < c
  /-- "an actual map of a ... finite union of parameter circles to the oriented (x,z) plane" -/
  comp : Fin c → SmoothLoop
  /-- finitely many cusps ("finitely many ... ordinary semicubical cusps"): the zeros of `γ'` with
  parameter in the fundamental period form a finite set -/
  cusps_finite :
    {p : Param c | p.2 ∈ Set.Ico (0 : ℝ) 1 ∧ deriv (comp p.1).γ p.2 = 0}.Finite
  /-- "ordinary semicubical cusps" (and "no other singularities": every zero of `γ'` is one):
  `det(γ'', γ''') ≠ 0` at every zero of `γ'` (FR-2) -/
  cusp_semicubical : ∀ (i : Fin c) (t : ℝ), deriv (comp i).γ t = 0 →
    det (iteratedDeriv 2 (comp i).γ t) (iteratedDeriv 3 (comp i).γ t) ≠ 0
  /-- "The limiting tangent at every cusp is also nonvertical: in a semicubical parameter u with
  cusp at u=0, require x''(0)≠0" (FR-2: `γ''` spans the limiting tangent in every parametrization) -/
  cusp_nonvertical : ∀ (i : Fin c) (t : ℝ), deriv (comp i).γ t = 0 →
    (iteratedDeriv 2 (comp i).γ t).1 ≠ 0
  /-- "no vertical tangencies on regular arcs" -/
  no_vertical : ∀ (i : Fin c) (t : ℝ), deriv (comp i).γ t ≠ 0 → (deriv (comp i).γ t).1 ≠ 0
  /-- "finitely many ... double points": the ordered pairs of distinct parameters in the
  fundamental period with equal image form a finite set -/
  doubles_finite :
    {q : Param c × Param c | q.1.2 ∈ Set.Ico (0 : ℝ) 1 ∧ q.2.2 ∈ Set.Ico (0 : ℝ) 1 ∧ q.1 ≠ q.2 ∧
      (comp q.1.1).γ q.1.2 = (comp q.2.1).γ q.2.2}.Finite
  /-- "transverse double points": at a double point the two velocities are independent -/
  transverse : ∀ p q : Param c, ¬ SameParam p q → (comp p.1).γ p.2 = (comp q.1).γ q.2 →
    det (deriv (comp p.1).γ p.2) (deriv (comp q.1).γ q.2) ≠ 0
  /-- "no other singularities": no triple point (every multiple point is a double point) -/
  no_triple : ∀ p q r : Param c, ¬ SameParam p q → ¬ SameParam q r → ¬ SameParam p r →
    (comp p.1).γ p.2 = (comp q.1).γ q.2 → (comp q.1).γ q.2 = (comp r.1).γ r.2 → False
  /-- "Cusps meet no other strand or singularity." -/
  cusp_alone : ∀ p q : Param c, ¬ SameParam p q → deriv (comp p.1).γ p.2 = 0 →
    (comp p.1).γ p.2 ≠ (comp q.1).γ q.2

/-! ## 4. The over/under rule against the sign convention -/

/-- Sanity for the over rule (sm-3:1908-1912): with over = smaller slope, the over-first
determinant is positive iff the two x-velocities agree in sign ("With both arrows pointing right,
the over-first tangent representatives (1,−1),(1,1) have determinant 2, so this crossing is
positive"). -/
theorem det_pos_iff_of_slope_lt {u v : Plane} (hu : u.1 ≠ 0) (hv : v.1 ≠ 0)
    (h : u.2 / u.1 < v.2 / v.1) : 0 < det u v ↔ 0 < u.1 * v.1 := by
  have key : det u v = u.1 * v.1 * (v.2 / v.1 - u.2 / u.1) := by
    unfold det; field_simp
  rw [key]
  have hpos : 0 < v.2 / v.1 - u.2 / u.1 := sub_pos.mpr h
  exact mul_pos_iff_of_pos_right hpos

/-- The printed standard crossing (sm-3:1910-1912): over-first representatives `(1,−1)`, `(1,1)`,
determinant `2`. -/
theorem det_standard_crossing : det ((1 : ℝ), (-1 : ℝ)) ((1 : ℝ), (1 : ℝ)) = 2 := by
  unfold det; norm_num

theorem slope_standard_crossing :
    ((1 : ℝ), (-1 : ℝ)).2 / ((1 : ℝ), (-1 : ℝ)).1 < ((1 : ℝ), (1 : ℝ)).2 / ((1 : ℝ), (1 : ℝ)).1 := by
  norm_num

/-! ## 5. Derived data of a front -/

namespace SmoothFront

variable (F : SmoothFront)

/-- the point of the plane at a parameter -/
def eval (p : Param F.c) : Plane := (F.comp p.1).γ p.2
/-- the velocity `γ'` -/
def vel (p : Param F.c) : Plane := deriv (F.comp p.1).γ p.2
/-- the acceleration `γ''` -/
def acc (p : Param F.c) : Plane := iteratedDeriv 2 (F.comp p.1).γ p.2
/-- the third derivative `γ'''` -/
def jerk (p : Param F.c) : Plane := iteratedDeriv 3 (F.comp p.1).γ p.2

theorem eval_def (p : Param F.c) : F.eval p = (F.comp p.1).γ p.2 := rfl
theorem vel_def (p : Param F.c) : F.vel p = deriv (F.comp p.1).γ p.2 := rfl
theorem acc_def (p : Param F.c) : F.acc p = iteratedDeriv 2 (F.comp p.1).γ p.2 := rfl
theorem jerk_def (p : Param F.c) : F.jerk p = iteratedDeriv 3 (F.comp p.1).γ p.2 := rfl

section periodicity

variable {F}

theorem eval_of_sameParam {p q : Param F.c} (h : SameParam p q) : F.eval q = F.eval p := by
  obtain ⟨i, t⟩ := p
  obtain ⟨j, s⟩ := q
  obtain ⟨h1, n, hn⟩ := h
  simp only at h1 hn
  subst h1; subst hn
  exact (F.comp i).eq_add_int n t

theorem vel_of_sameParam {p q : Param F.c} (h : SameParam p q) : F.vel q = F.vel p := by
  obtain ⟨i, t⟩ := p
  obtain ⟨j, s⟩ := q
  obtain ⟨h1, n, hn⟩ := h
  simp only at h1 hn
  subst h1; subst hn
  exact (F.comp i).deriv_eq_add_int n t

theorem acc_of_sameParam {p q : Param F.c} (h : SameParam p q) : F.acc q = F.acc p := by
  obtain ⟨i, t⟩ := p
  obtain ⟨j, s⟩ := q
  obtain ⟨h1, n, hn⟩ := h
  simp only at h1 hn
  subst h1; subst hn
  exact (F.comp i).iteratedDeriv_eq_add_int 2 n t

theorem jerk_of_sameParam {p q : Param F.c} (h : SameParam p q) : F.jerk q = F.jerk p := by
  obtain ⟨i, t⟩ := p
  obtain ⟨j, s⟩ := q
  obtain ⟨h1, n, hn⟩ := h
  simp only at h1 hn
  subst h1; subst hn
  exact (F.comp i).iteratedDeriv_eq_add_int 3 n t

end periodicity

/-! ### Cusps -/

/-- a cusp: a zero of the velocity (by `cusp_semicubical` every such zero is an ordinary
semicubical cusp) -/
def IsCusp (p : Param F.c) : Prop := F.vel p = 0

theorem isCusp_def (p : Param F.c) : F.IsCusp p ↔ deriv (F.comp p.1).γ p.2 = 0 := Iff.rfl

theorem isCusp_iff_of_sameParam {p q : Param F.c} (h : SameParam p q) :
    F.IsCusp q ↔ F.IsCusp p := by
  unfold IsCusp; rw [vel_of_sameParam h]

theorem det_acc_jerk_ne_zero_of_isCusp {p : Param F.c} (hp : F.IsCusp p) :
    det (F.acc p) (F.jerk p) ≠ 0 :=
  F.cusp_semicubical p.1 p.2 hp

theorem acc_fst_ne_zero_of_isCusp {p : Param F.c} (hp : F.IsCusp p) : (F.acc p).1 ≠ 0 :=
  F.cusp_nonvertical p.1 p.2 hp

theorem acc_ne_zero_of_isCusp {p : Param F.c} (hp : F.IsCusp p) : F.acc p ≠ 0 := fun h =>
  F.acc_fst_ne_zero_of_isCusp hp (by rw [h]; rfl)

/-- The cusp discriminant `x''·det(γ'', γ''')`: the later arm is the locally upper one iff it is
positive (FR-2). -/
def cuspDisc (p : Param F.c) : ℝ := (F.acc p).1 * det (F.acc p) (F.jerk p)

theorem cuspDisc_of_sameParam {p q : Param F.c} (h : SameParam p q) :
    F.cuspDisc q = F.cuspDisc p := by
  unfold cuspDisc; rw [acc_of_sameParam h, jerk_of_sameParam h]

theorem cuspDisc_ne_zero_of_isCusp {p : Param F.c} (hp : F.IsCusp p) : F.cuspDisc p ≠ 0 :=
  mul_ne_zero (F.acc_fst_ne_zero_of_isCusp hp) (F.det_acc_jerk_ne_zero_of_isCusp hp)

/-- "A downward cusp is traversed from its locally upper arm to its locally lower arm": the cusp
discriminant is negative (FR-2). -/
def IsDownCusp (p : Param F.c) : Prop := F.IsCusp p ∧ F.cuspDisc p < 0
/-- an upward cusp: traversed from its locally lower arm to its locally upper arm -/
def IsUpCusp (p : Param F.c) : Prop := F.IsCusp p ∧ 0 < F.cuspDisc p
/-- a left cusp (sm-3:1906): the limiting tangent points to the right, the cusp opens rightward -/
def IsLeftCusp (p : Param F.c) : Prop := F.IsCusp p ∧ 0 < (F.acc p).1
/-- a right cusp (sm-3:1907): the limiting tangent points to the left -/
def IsRightCusp (p : Param F.c) : Prop := F.IsCusp p ∧ (F.acc p).1 < 0

theorem IsDownCusp.isCusp {p : Param F.c} (h : F.IsDownCusp p) : F.IsCusp p := h.1
theorem IsUpCusp.isCusp {p : Param F.c} (h : F.IsUpCusp p) : F.IsCusp p := h.1
theorem IsLeftCusp.isCusp {p : Param F.c} (h : F.IsLeftCusp p) : F.IsCusp p := h.1
theorem IsRightCusp.isCusp {p : Param F.c} (h : F.IsRightCusp p) : F.IsCusp p := h.1

/-- Every cusp is downward or upward, not both. -/
theorem isDownCusp_xor_isUpCusp {p : Param F.c} (hp : F.IsCusp p) :
    Xor (F.IsDownCusp p) (F.IsUpCusp p) := by
  rcases lt_or_gt_of_ne (F.cuspDisc_ne_zero_of_isCusp hp) with h | h
  · exact Or.inl ⟨⟨hp, h⟩, fun h' => lt_asymm h h'.2⟩
  · exact Or.inr ⟨⟨hp, h⟩, fun h' => lt_asymm h h'.2⟩

theorem isDownCusp_or_isUpCusp {p : Param F.c} (hp : F.IsCusp p) :
    F.IsDownCusp p ∨ F.IsUpCusp p := by
  rcases F.isDownCusp_xor_isUpCusp hp with h | h
  · exact Or.inl h.1
  · exact Or.inr h.1

theorem not_isDownCusp_and_isUpCusp (p : Param F.c) : ¬ (F.IsDownCusp p ∧ F.IsUpCusp p) :=
  fun h => lt_asymm h.1.2 h.2.2

theorem isUpCusp_iff_not_isDownCusp {p : Param F.c} (hp : F.IsCusp p) :
    F.IsUpCusp p ↔ ¬ F.IsDownCusp p := by
  rcases F.isDownCusp_xor_isUpCusp hp with h | h
  · exact ⟨fun h' => absurd h' h.2, fun h' => absurd h.1 h'⟩
  · exact ⟨fun _ => h.2, fun _ => h.1⟩

/-- Every cusp is a left cusp or a right cusp, not both. -/
theorem isLeftCusp_xor_isRightCusp {p : Param F.c} (hp : F.IsCusp p) :
    Xor (F.IsLeftCusp p) (F.IsRightCusp p) := by
  rcases lt_or_gt_of_ne (F.acc_fst_ne_zero_of_isCusp hp) with h | h
  · exact Or.inr ⟨⟨hp, h⟩, fun h' => lt_asymm h h'.2⟩
  · exact Or.inl ⟨⟨hp, h⟩, fun h' => lt_asymm h h'.2⟩

theorem isLeftCusp_or_isRightCusp {p : Param F.c} (hp : F.IsCusp p) :
    F.IsLeftCusp p ∨ F.IsRightCusp p := by
  rcases F.isLeftCusp_xor_isRightCusp hp with h | h
  · exact Or.inl h.1
  · exact Or.inr h.1

theorem isDownCusp_iff_of_sameParam {p q : Param F.c} (h : SameParam p q) :
    F.IsDownCusp q ↔ F.IsDownCusp p := by
  unfold IsDownCusp; rw [F.isCusp_iff_of_sameParam h, F.cuspDisc_of_sameParam h]

theorem isUpCusp_iff_of_sameParam {p q : Param F.c} (h : SameParam p q) :
    F.IsUpCusp q ↔ F.IsUpCusp p := by
  unfold IsUpCusp; rw [F.isCusp_iff_of_sameParam h, F.cuspDisc_of_sameParam h]

/-! ### Double points, the over/under rule, crossing signs -/

/-- `dz/dx` at a parameter (meaningful on regular arcs, where `x' ≠ 0` by `no_vertical`) -/
def slope (p : Param F.c) : ℝ := (F.vel p).2 / (F.vel p).1

theorem slope_of_sameParam {p q : Param F.c} (h : SameParam p q) : F.slope q = F.slope p := by
  unfold slope; rw [vel_of_sameParam h]

/-- a double point, as an ordered pair of parameters of distinct points of the circles -/
def IsDouble (p q : Param F.c) : Prop := ¬ SameParam p q ∧ F.eval p = F.eval q

/-- "At a crossing the branch with smaller dz/dx is over": `p` is the over branch, `q` the under
branch of the double point. -/
def IsOverUnder (p q : Param F.c) : Prop := F.IsDouble p q ∧ F.slope p < F.slope q

/-- the over-first tangent-determinant crossing sign of the pair `(over, under)` -/
def crossSign (p q : Param F.c) : ℤ := if 0 < det (F.vel p) (F.vel q) then 1 else -1

theorem IsDouble.symm {p q : Param F.c} (h : F.IsDouble p q) : F.IsDouble q p :=
  ⟨fun h' => h.1 h'.symm, h.2.symm⟩

theorem IsDouble.eval_eq {p q : Param F.c} (h : F.IsDouble p q) : F.eval p = F.eval q := h.2

theorem det_vel_ne_zero_of_isDouble {p q : Param F.c} (h : F.IsDouble p q) :
    det (F.vel p) (F.vel q) ≠ 0 :=
  F.transverse p q h.1 h.2

/-- a double point is not a cusp (`cusp_alone`) -/
theorem vel_ne_zero_of_isDouble {p q : Param F.c} (h : F.IsDouble p q) : F.vel p ≠ 0 := fun hv =>
  F.cusp_alone p q h.1 hv h.2

theorem not_isCusp_of_isDouble {p q : Param F.c} (h : F.IsDouble p q) : ¬ F.IsCusp p :=
  F.vel_ne_zero_of_isDouble h

/-- at a double point both branches are regular arcs, hence nonvertical (`no_vertical`) -/
theorem vel_fst_ne_zero_of_isDouble {p q : Param F.c} (h : F.IsDouble p q) : (F.vel p).1 ≠ 0 :=
  F.no_vertical p.1 p.2 (F.vel_ne_zero_of_isDouble h)

/-- The two branches of a double point have distinct slopes (transversality with nonvertical
branches), so "the branch with smaller dz/dx" is well defined. -/
theorem slope_ne_of_isDouble {p q : Param F.c} (h : F.IsDouble p q) : F.slope p ≠ F.slope q := by
  intro heq
  apply F.det_vel_ne_zero_of_isDouble h
  unfold slope at heq
  rw [div_eq_div_iff (F.vel_fst_ne_zero_of_isDouble h) (F.vel_fst_ne_zero_of_isDouble h.symm)]
    at heq
  unfold det; linarith

theorem IsOverUnder.isDouble {p q : Param F.c} (h : F.IsOverUnder p q) : F.IsDouble p q := h.1

theorem isOverUnder_or_isOverUnder {p q : Param F.c} (h : F.IsDouble p q) :
    F.IsOverUnder p q ∨ F.IsOverUnder q p := by
  rcases lt_or_gt_of_ne (F.slope_ne_of_isDouble h) with hlt | hgt
  · exact Or.inl ⟨h, hlt⟩
  · exact Or.inr ⟨h.symm, hgt⟩

theorem not_isOverUnder_and_isOverUnder (p q : Param F.c) :
    ¬ (F.IsOverUnder p q ∧ F.IsOverUnder q p) :=
  fun h => lt_asymm h.1.2 h.2.2

/-- At every double point exactly one branch is over. -/
theorem isOverUnder_xor {p q : Param F.c} (h : F.IsDouble p q) :
    Xor (F.IsOverUnder p q) (F.IsOverUnder q p) := by
  rcases F.isOverUnder_or_isOverUnder h with h' | h'
  · exact Or.inl ⟨h', fun h'' => F.not_isOverUnder_and_isOverUnder p q ⟨h', h''⟩⟩
  · exact Or.inr ⟨h', fun h'' => F.not_isOverUnder_and_isOverUnder p q ⟨h'', h'⟩⟩

theorem isOverUnder_iff_of_sameParam {p p' q q' : Param F.c} (hp : SameParam p p')
    (hq : SameParam q q') : F.IsOverUnder p' q' ↔ F.IsOverUnder p q := by
  unfold IsOverUnder IsDouble
  rw [eval_of_sameParam hp, eval_of_sameParam hq, F.slope_of_sameParam hp, F.slope_of_sameParam hq]
  constructor
  · rintro ⟨⟨hne, he⟩, hs⟩
    exact ⟨⟨fun h => hne (hp.symm.trans (h.trans hq)), he⟩, hs⟩
  · rintro ⟨⟨hne, he⟩, hs⟩
    exact ⟨⟨fun h => hne (hp.trans (h.trans hq.symm)), he⟩, hs⟩

theorem crossSign_eq_one_or_neg_one (p q : Param F.c) :
    F.crossSign p q = 1 ∨ F.crossSign p q = -1 := by
  unfold crossSign; split_ifs <;> simp

theorem crossSign_eq_one_iff (p q : Param F.c) :
    F.crossSign p q = 1 ↔ 0 < det (F.vel p) (F.vel q) := by
  unfold crossSign
  split_ifs with hd
  · exact ⟨fun _ => hd, fun _ => rfl⟩
  · exact ⟨fun h => absurd h (by norm_num), fun h => absurd h hd⟩

theorem crossSign_eq_neg_one_iff {p q : Param F.c} (h : F.IsDouble p q) :
    F.crossSign p q = -1 ↔ det (F.vel p) (F.vel q) < 0 := by
  have hne := F.det_vel_ne_zero_of_isDouble h
  unfold crossSign
  split_ifs with hd
  · exact ⟨fun h1 => absurd h1 (by norm_num), fun h1 => absurd (lt_trans h1 hd) (lt_irrefl _)⟩
  · exact ⟨fun _ => lt_of_le_of_ne (not_lt.mp hd) hne, fun _ => rfl⟩

/-- The crossing sign is the accepted `SignType.sign (det u_o u_u)` of def:positive-lift
(sm-3:328-331), read in `ℤ`. -/
theorem crossSign_eq_sign {p q : Param F.c} (h : F.IsDouble p q) :
    F.crossSign p q = ((SignType.sign (det (F.vel p) (F.vel q)) : SignType) : ℤ) := by
  have hne := F.det_vel_ne_zero_of_isDouble h
  unfold crossSign
  split_ifs with hd
  · rw [sign_pos hd]; simp
  · rw [sign_neg (lt_of_le_of_ne (not_lt.mp hd) hne)]; simp

/-- Reversing the order of the branches reverses the sign (the sign is "over-first"). -/
theorem crossSign_swap {p q : Param F.c} (h : F.IsDouble p q) :
    F.crossSign q p = - F.crossSign p q := by
  have hne := F.det_vel_ne_zero_of_isDouble h
  unfold crossSign
  rw [det_swap]
  split_ifs with h1 h2 h2
  · exact absurd (lt_trans h2 (neg_pos.mp h1)) (lt_irrefl _)
  · norm_num
  · norm_num
  · exact absurd (lt_of_le_of_ne (not_lt.mp h2) hne) (fun h3 => h1 (neg_pos.mpr h3))

/-- The over rule agrees with the sign convention: the over-first sign of a crossing is `+1` iff
the two branches travel in the same x-direction (sm-3:1908-1912). -/
theorem crossSign_eq_one_iff_of_isOverUnder {p q : Param F.c} (h : F.IsOverUnder p q) :
    F.crossSign p q = 1 ↔ 0 < (F.vel p).1 * (F.vel q).1 := by
  rw [F.crossSign_eq_one_iff]
  exact det_pos_iff_of_slope_lt (F.vel_fst_ne_zero_of_isDouble h.1)
    (F.vel_fst_ne_zero_of_isDouble h.1.symm) h.2

theorem crossSign_of_sameParam {p p' q q' : Param F.c} (hp : SameParam p p') (hq : SameParam q q') :
    F.crossSign p' q' = F.crossSign p q := by
  unfold crossSign; rw [vel_of_sameParam hp, vel_of_sameParam hq]

/-! ### The finite sets of cusps and double points, and the counts `D`, `w`, `s` -/

/-- the cusps, one parameter each (in the fundamental period) -/
def cuspSet : Finset (Param F.c) := F.cusps_finite.toFinset

theorem mem_cuspSet {p : Param F.c} : p ∈ F.cuspSet ↔ p.2 ∈ Set.Ico (0 : ℝ) 1 ∧ F.IsCusp p := by
  unfold cuspSet; rw [Set.Finite.mem_toFinset]; exact Iff.rfl

theorem isCusp_of_mem_cuspSet {p : Param F.c} (hp : p ∈ F.cuspSet) : F.IsCusp p :=
  (F.mem_cuspSet.mp hp).2

/-- every cusp has exactly one representative in `cuspSet` -/
theorem rep_mem_cuspSet {p : Param F.c} (hp : F.IsCusp p) : SameParam.rep p ∈ F.cuspSet :=
  F.mem_cuspSet.mpr ⟨SameParam.rep_mem_Ico p,
    (F.isCusp_iff_of_sameParam (SameParam.sameParam_rep p)).mpr hp⟩

/-- the double points as ordered pairs of parameters in the fundamental period -/
def doubleSet : Finset (Param F.c × Param F.c) := F.doubles_finite.toFinset

theorem mem_doubleSet {q : Param F.c × Param F.c} :
    q ∈ F.doubleSet ↔ q.1.2 ∈ Set.Ico (0 : ℝ) 1 ∧ q.2.2 ∈ Set.Ico (0 : ℝ) 1 ∧ q.1 ≠ q.2 ∧
      F.eval q.1 = F.eval q.2 := by
  unfold doubleSet; rw [Set.Finite.mem_toFinset]; exact Iff.rfl

theorem isDouble_of_mem_doubleSet {q : Param F.c × Param F.c} (hq : q ∈ F.doubleSet) :
    F.IsDouble q.1 q.2 := by
  rw [mem_doubleSet] at hq
  obtain ⟨h1, h2, hne, he⟩ := hq
  exact ⟨fun hs => hne (SameParam.eq_of_mem_Ico h1 h2 hs), he⟩

theorem swap_mem_doubleSet_iff {q : Param F.c × Param F.c} :
    q.swap ∈ F.doubleSet ↔ q ∈ F.doubleSet := by
  simp only [mem_doubleSet, Prod.fst_swap, Prod.snd_swap]
  constructor
  · rintro ⟨h1, h2, hne, he⟩; exact ⟨h2, h1, hne.symm, he.symm⟩
  · rintro ⟨h1, h2, hne, he⟩; exact ⟨h2, h1, hne.symm, he.symm⟩

/-- the crossings: each double point once, as its over-first pair `(over, under)` -/
def crossingPairs : Finset (Param F.c × Param F.c) :=
  F.doubleSet.filter fun q => F.slope q.1 < F.slope q.2

theorem mem_crossingPairs {q : Param F.c × Param F.c} :
    q ∈ F.crossingPairs ↔ q ∈ F.doubleSet ∧ F.slope q.1 < F.slope q.2 := by
  unfold crossingPairs; rw [Finset.mem_filter]

theorem mem_crossingPairs' {q : Param F.c × Param F.c} :
    q ∈ F.crossingPairs ↔ (q.1.2 ∈ Set.Ico (0 : ℝ) 1 ∧ q.2.2 ∈ Set.Ico (0 : ℝ) 1 ∧ q.1 ≠ q.2 ∧
      F.eval q.1 = F.eval q.2) ∧ F.slope q.1 < F.slope q.2 := by
  rw [mem_crossingPairs, mem_doubleSet]

theorem isOverUnder_of_mem_crossingPairs {q : Param F.c × Param F.c} (hq : q ∈ F.crossingPairs) :
    F.IsOverUnder q.1 q.2 := by
  rw [mem_crossingPairs] at hq
  exact ⟨F.isDouble_of_mem_doubleSet hq.1, hq.2⟩

theorem mem_crossingPairs_or_swap {q : Param F.c × Param F.c} (hq : q ∈ F.doubleSet) :
    q ∈ F.crossingPairs ∨ q.swap ∈ F.crossingPairs := by
  have hd := F.isDouble_of_mem_doubleSet hq
  rcases F.isOverUnder_or_isOverUnder hd with h | h
  · exact Or.inl (F.mem_crossingPairs.mpr ⟨hq, h.2⟩)
  · exact Or.inr (F.mem_crossingPairs.mpr ⟨F.swap_mem_doubleSet_iff.mpr hq, h.2⟩)

theorem not_swap_mem_crossingPairs {q : Param F.c × Param F.c} (hq : q ∈ F.crossingPairs) :
    q.swap ∉ F.crossingPairs := by
  intro h'
  have h1 := (F.mem_crossingPairs.mp hq).2
  have h2 := (F.mem_crossingPairs.mp h').2
  simp only [Prod.fst_swap, Prod.snd_swap] at h2
  exact lt_asymm h1 h2

/-- Each double point enters `crossingPairs` exactly once: in exactly one of its two orders. -/
theorem crossingPairs_xor_swap {q : Param F.c × Param F.c} (hq : q ∈ F.doubleSet) :
    Xor (q ∈ F.crossingPairs) (q.swap ∈ F.crossingPairs) := by
  rcases F.mem_crossingPairs_or_swap hq with h | h
  · exact Or.inl ⟨h, F.not_swap_mem_crossingPairs h⟩
  · exact Or.inr ⟨h, fun h' => F.not_swap_mem_crossingPairs h' h⟩

theorem crossingPairs_subset_doubleSet : F.crossingPairs ⊆ F.doubleSet :=
  Finset.filter_subset _ _

/-- "Write D(F) for the number of downward cusps" -/
def downCount : ℕ := (F.cuspSet.filter fun p => F.IsDownCusp p).card
/-- the number of upward cusps -/
def upCount : ℕ := (F.cuspSet.filter fun p => F.IsUpCusp p).card
/-- "w(F) for the sum of the over-first tangent-determinant crossing signs" -/
def writhe : ℤ := ∑ q ∈ F.crossingPairs, F.crossSign q.1 q.2
/-- "s(F) for the number of crossings plus cusps" -/
def sCount : ℕ := F.crossingPairs.card + F.cuspSet.card
/-- `w(F) − D(F)`, the quantity bounded in ng:local-front-bound / fd:ng-bound (`sl_Ng`) -/
def slNg : ℤ := F.writhe - F.downCount

theorem downCount_def : F.downCount = (F.cuspSet.filter fun p => F.IsDownCusp p).card := rfl
theorem writhe_def : F.writhe = ∑ q ∈ F.crossingPairs, F.crossSign q.1 q.2 := rfl
theorem sCount_def : F.sCount = F.crossingPairs.card + F.cuspSet.card := rfl
theorem slNg_def : F.slNg = F.writhe - F.downCount := rfl

/-- Every cusp is downward or upward: `D + U = #cusps`. -/
theorem downCount_add_upCount : F.downCount + F.upCount = F.cuspSet.card := by
  unfold downCount upCount
  rw [← Finset.card_filter_add_card_filter_not (s := F.cuspSet) (p := fun p => F.IsDownCusp p)]
  congr 2
  ext p
  simp only [Finset.mem_filter, mem_cuspSet]
  constructor
  · rintro ⟨hp, hup⟩
    exact ⟨hp, fun hdown => F.not_isDownCusp_and_isUpCusp p ⟨hdown, hup⟩⟩
  · rintro ⟨hp, hnd⟩
    exact ⟨hp, (F.isUpCusp_iff_not_isDownCusp hp.2).mpr hnd⟩

theorem downCount_le_card_cuspSet : F.downCount ≤ F.cuspSet.card :=
  Finset.card_filter_le _ _

theorem downCount_le_sCount : F.downCount ≤ F.sCount :=
  le_trans F.downCount_le_card_cuspSet (Nat.le_add_left _ _)

theorem card_crossingPairs_le_sCount : F.crossingPairs.card ≤ F.sCount := Nat.le_add_right _ _

/-- the writhe is bounded by the number of crossings -/
theorem abs_writhe_le : |F.writhe| ≤ F.crossingPairs.card := by
  unfold writhe
  calc |∑ q ∈ F.crossingPairs, F.crossSign q.1 q.2|
      ≤ ∑ q ∈ F.crossingPairs, |F.crossSign q.1 q.2| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ q ∈ F.crossingPairs, (1 : ℤ) := by
        refine Finset.sum_congr rfl fun q _ => ?_
        rcases F.crossSign_eq_one_or_neg_one q.1 q.2 with h | h <;> rw [h] <;> norm_num
    _ = F.crossingPairs.card := by simp

/-! ### Cusp-free fronts (ordinary diagrams in the smooth sense) -/

/-- a cusp-free front: every parameter is regular ("ordinary diagram", the class of `S(F)`) -/
def CuspFree : Prop := ∀ (i : Fin F.c) (t : ℝ), deriv (F.comp i).γ t ≠ 0

theorem CuspFree.not_isCusp {F : SmoothFront} (h : F.CuspFree) (p : Param F.c) : ¬ F.IsCusp p :=
  h p.1 p.2

theorem CuspFree.vel_ne_zero {F : SmoothFront} (h : F.CuspFree) (p : Param F.c) : F.vel p ≠ 0 :=
  h p.1 p.2

theorem CuspFree.vel_fst_ne_zero {F : SmoothFront} (h : F.CuspFree) (p : Param F.c) :
    (F.vel p).1 ≠ 0 :=
  F.no_vertical p.1 p.2 (h p.1 p.2)

theorem cuspSet_eq_empty_of_cuspFree (h : F.CuspFree) : F.cuspSet = ∅ := by
  ext p
  simp only [mem_cuspSet, Finset.notMem_empty, iff_false, not_and]
  exact fun _ hp => h.not_isCusp p hp

theorem downCount_eq_zero_of_cuspFree (h : F.CuspFree) : F.downCount = 0 := by
  unfold downCount; rw [F.cuspSet_eq_empty_of_cuspFree h, Finset.filter_empty, Finset.card_empty]

theorem sCount_eq_of_cuspFree (h : F.CuspFree) : F.sCount = F.crossingPairs.card := by
  unfold sCount; rw [F.cuspSet_eq_empty_of_cuspFree h, Finset.card_empty, add_zero]

theorem cuspFree_iff_cuspSet_eq_empty : F.CuspFree ↔ F.cuspSet = ∅ := by
  constructor
  · exact F.cuspSet_eq_empty_of_cuspFree
  · intro h i t ht
    have hmem := F.rep_mem_cuspSet (p := (i, t)) ht
    rw [h] at hmem
    exact Finset.notMem_empty _ hmem

/-- Reuse of the accepted smooth model: each component of a cusp-free front is a `ClosedC1Curve`
(SM/TurningNumber.lean). -/
def toClosedC1Curve (h : F.CuspFree) (i : Fin F.c) : ClosedC1Curve :=
  (F.comp i).toClosedC1Curve (h i)

end SmoothFront

/-! ## 6. The printed exact germ passes the cusp clauses -/

/-- The front of the printed exact cusp germ (sm-3:2747; fd:generic-exact-germ):
`x = x₀ + Au², z = z₀ + Ay₀u² + ⅔Au³`, in the parameter `u` with the cusp at `u = 0`. -/
def germFront (A y₀ x₀ z₀ : ℝ) : ℝ → Plane :=
  fun u => (x₀ + A * u ^ 2, z₀ + A * y₀ * u ^ 2 + 2 * A / 3 * u ^ 3)

theorem germFront_smooth (A y₀ x₀ z₀ : ℝ) : ContDiff ℝ ∞ (germFront A y₀ x₀ z₀) := by
  unfold germFront; fun_prop

theorem hasDerivAt_germFront (A y₀ x₀ z₀ u : ℝ) :
    HasDerivAt (germFront A y₀ x₀ z₀) (2 * A * u, 2 * A * y₀ * u + 2 * A * u ^ 2) u := by
  have h1 : HasDerivAt (fun u : ℝ => x₀ + A * u ^ 2) (2 * A * u) u := by
    refine ((hasDerivAt_const u x₀).add ((hasDerivAt_pow 2 u).const_mul A)).congr_deriv ?_
    push_cast; ring
  have h2 : HasDerivAt (fun u : ℝ => z₀ + A * y₀ * u ^ 2 + 2 * A / 3 * u ^ 3)
      (2 * A * y₀ * u + 2 * A * u ^ 2) u := by
    have a := (hasDerivAt_pow 2 u).const_mul (A * y₀)
    have b := (hasDerivAt_pow 3 u).const_mul (2 * A / 3)
    refine (((hasDerivAt_const u z₀).add a).add b).congr_deriv ?_
    push_cast; ring
  exact h1.prodMk h2

theorem deriv_germFront (A y₀ x₀ z₀ : ℝ) :
    deriv (germFront A y₀ x₀ z₀) = fun u => (2 * A * u, 2 * A * y₀ * u + 2 * A * u ^ 2) :=
  funext fun u => (hasDerivAt_germFront A y₀ x₀ z₀ u).deriv

theorem hasDerivAt_germFront' (A y₀ u : ℝ) :
    HasDerivAt (fun u : ℝ => ((2 * A * u, 2 * A * y₀ * u + 2 * A * u ^ 2) : Plane))
      (2 * A, 2 * A * y₀ + 4 * A * u) u := by
  have h1 : HasDerivAt (fun u : ℝ => 2 * A * u) (2 * A) u := by
    refine ((hasDerivAt_id u).const_mul (2 * A)).congr_deriv ?_
    simp
  have h2 : HasDerivAt (fun u : ℝ => 2 * A * y₀ * u + 2 * A * u ^ 2)
      (2 * A * y₀ + 4 * A * u) u := by
    have a := (hasDerivAt_id u).const_mul (2 * A * y₀)
    have b := (hasDerivAt_pow 2 u).const_mul (2 * A)
    refine (a.add b).congr_deriv ?_
    push_cast; simp; ring
  exact h1.prodMk h2

theorem hasDerivAt_germFront'' (A y₀ u : ℝ) :
    HasDerivAt (fun u : ℝ => ((2 * A, 2 * A * y₀ + 4 * A * u) : Plane)) (0, 4 * A) u := by
  have h1 : HasDerivAt (fun _ : ℝ => 2 * A) 0 u := hasDerivAt_const u _
  have h2 : HasDerivAt (fun u : ℝ => 2 * A * y₀ + 4 * A * u) (4 * A) u := by
    have b := (hasDerivAt_id u).const_mul (4 * A)
    refine ((hasDerivAt_const u (2 * A * y₀)).add b).congr_deriv ?_
    simp
  exact h1.prodMk h2

theorem iteratedDeriv_two_germFront (A y₀ x₀ z₀ : ℝ) :
    iteratedDeriv 2 (germFront A y₀ x₀ z₀) = fun u => (2 * A, 2 * A * y₀ + 4 * A * u) := by
  rw [iteratedDeriv_succ, iteratedDeriv_one, deriv_germFront]
  exact funext fun u => (hasDerivAt_germFront' A y₀ u).deriv

theorem iteratedDeriv_three_germFront (A y₀ x₀ z₀ : ℝ) :
    iteratedDeriv 3 (germFront A y₀ x₀ z₀) = fun _ => (0, 4 * A) := by
  rw [iteratedDeriv_succ, iteratedDeriv_two_germFront]
  exact funext fun u => (hasDerivAt_germFront'' A y₀ u).deriv

/-- The printed germ has a cusp at `u = 0` satisfying the class clauses `cusp_semicubical`
(`det(γ'', γ''') = 8A² ≠ 0`) and `cusp_nonvertical` (`x''(0) = 2A ≠ 0`) for every `A ≠ 0`
(FR-2). -/
theorem germFront_semicubical (A y₀ x₀ z₀ : ℝ) (hA : A ≠ 0) :
    deriv (germFront A y₀ x₀ z₀) 0 = 0 ∧
    det (iteratedDeriv 2 (germFront A y₀ x₀ z₀) 0) (iteratedDeriv 3 (germFront A y₀ x₀ z₀) 0) =
      8 * A ^ 2 ∧
    (iteratedDeriv 2 (germFront A y₀ x₀ z₀) 0).1 = 2 * A ∧ 8 * A ^ 2 ≠ 0 ∧ 2 * A ≠ 0 := by
  rw [deriv_germFront, iteratedDeriv_two_germFront, iteratedDeriv_three_germFront]
  refine ⟨by simp, ?_, by simp, by positivity, by simpa using hA⟩
  simp [det]; ring

/-- The cusp discriminant of the printed germ is `16A³`: the cusp is upward iff `A > 0`. -/
theorem germFront_cuspDisc (A y₀ x₀ z₀ : ℝ) :
    (iteratedDeriv 2 (germFront A y₀ x₀ z₀) 0).1 *
      det (iteratedDeriv 2 (germFront A y₀ x₀ z₀) 0) (iteratedDeriv 3 (germFront A y₀ x₀ z₀) 0) =
      16 * A ^ 3 := by
  rw [iteratedDeriv_two_germFront, iteratedDeriv_three_germFront]
  simp [det]; ring

/-- The two arms of the germ at `±u` have the same `x`. -/
theorem germFront_fst_neg (A y₀ x₀ z₀ u : ℝ) :
    (germFront A y₀ x₀ z₀ (-u)).1 = (germFront A y₀ x₀ z₀ u).1 := by
  simp [germFront]

/-- The height difference between the later arm (`u`) and the earlier arm (`−u`) is `⁴⁄₃Au³`. -/
theorem germFront_snd_sub (A y₀ x₀ z₀ u : ℝ) :
    (germFront A y₀ x₀ z₀ u).2 - (germFront A y₀ x₀ z₀ (-u)).2 = 4 * A / 3 * u ^ 3 := by
  simp only [germFront]; ring

/-- Geometric check of the down/up rule on the printed germ: for `u > 0` the later arm is the
locally upper one (so the cusp is traversed lower → upper, upward) iff `A > 0`, i.e. iff the
discriminant `16A³` is positive (FR-2). -/
theorem germFront_later_arm_higher_iff (A y₀ x₀ z₀ u : ℝ) (hu : 0 < u) :
    (germFront A y₀ x₀ z₀ (-u)).2 < (germFront A y₀ x₀ z₀ u).2 ↔ 0 < 16 * A ^ 3 := by
  rw [← sub_pos, germFront_snd_sub]
  have hu3 : 0 < u ^ 3 := pow_pos hu 3
  constructor
  · intro h
    have hA : 0 < A := by
      by_contra hA
      have hA' : A ≤ 0 := not_lt.mp hA
      have : 4 * A / 3 * u ^ 3 ≤ 0 := by
        apply mul_nonpos_of_nonpos_of_nonneg _ hu3.le
        linarith
      linarith
    positivity
  · intro h
    have hA : 0 < A := by
      by_contra hA
      have hA' : A ≤ 0 := not_lt.mp hA
      have : A ^ 3 ≤ 0 := Odd.pow_nonpos (by decide) hA'
      linarith
    positivity

/-! ## 7. The named record of a front on a polygonal diagram (FR-1) -/

namespace SmoothFront

variable (F : SmoothFront)

/-- the crossing occurrences of `F`: the parameters (in the fundamental period) of the double
points, one per branch -/
def occSet : Set (Param F.c) :=
  {p | p.2 ∈ Set.Ico (0 : ℝ) 1 ∧ ∃ q : Param F.c, q.2 ∈ Set.Ico (0 : ℝ) 1 ∧ p ≠ q ∧ F.eval p = F.eval q}

theorem mem_occSet {p : Param F.c} :
    p ∈ F.occSet ↔ p.2 ∈ Set.Ico (0 : ℝ) 1 ∧
      ∃ q : Param F.c, q.2 ∈ Set.Ico (0 : ℝ) 1 ∧ p ≠ q ∧ F.eval p = F.eval q := Iff.rfl

theorem occSet_finite : F.occSet.Finite :=
  (F.doubles_finite.image Prod.fst).subset fun p ⟨hp, q, hq, hne, he⟩ =>
    ⟨(p, q), ⟨hp, hq, hne, he⟩, rfl⟩

/-- the occurrence type (finite) -/
abbrev Occ : Type := F.occSet

instance : Fintype F.Occ := F.occSet_finite.fintype

theorem Occ.mem_Ico (p : F.Occ) : p.1.2 ∈ Set.Ico (0 : ℝ) 1 := p.2.1

/-- two distinct occurrences with the same image form a double point -/
theorem Occ.isDouble_of_ne {p q : F.Occ} (hne : p ≠ q) (he : F.eval p = F.eval q) :
    F.IsDouble p.1 q.1 :=
  ⟨fun hs => hne (Subtype.ext (SameParam.eq_of_mem_Ico p.2.1 q.2.1 hs)), he⟩

theorem fst_mem_occSet_of_mem_doubleSet {q : Param F.c × Param F.c} (hq : q ∈ F.doubleSet) :
    q.1 ∈ F.occSet := by
  rw [mem_doubleSet] at hq
  exact ⟨hq.1, q.2, hq.2.1, hq.2.2.1, hq.2.2.2⟩

theorem snd_mem_occSet_of_mem_doubleSet {q : Param F.c × Param F.c} (hq : q ∈ F.doubleSet) :
    q.2 ∈ F.occSet :=
  F.fst_mem_occSet_of_mem_doubleSet (F.swap_mem_doubleSet_iff.mpr hq)

/-- The polygonal reading of a smooth ordinary diagram (FR-1; sm-3:337-343, lem:gauss-pl-model:
"the crossing names, the four-ray orders, the traversal direction and the over/under designations
are retained"): the polygonal `Diagram S` carries the front's full named record — the items listed
in ng:smoothing-record (sm-3:1846-1848): "the same component circles, including crossing-free
ones, and the same crossing occurrences, cyclic orders, over/under bits and signs". -/
structure Marking (S : Diagram) where
  /-- the component circles, crossing-free ones included -/
  e : Fin F.c ≃ Fin S.Γ.c
  /-- the crossing occurrences -/
  Φ : F.Occ ≃ S.Γ.Visit
  /-- an occurrence keeps its circle -/
  comp_eq : ∀ p : F.Occ, S.compOf (Φ p) = e p.1.1
  /-- the cyclic order of the occurrences along each oriented circle -/
  between_iff : ∀ p q r : F.Occ, p.1.1 = q.1.1 → q.1.1 = r.1.1 →
    (cycBetween p.1.2 q.1.2 r.1.2 ↔
      cycBetween (S.visitCoord (Φ p)) (S.visitCoord (Φ q)) (S.visitCoord (Φ r)))
  /-- the pairing of the two occurrences of each double point -/
  pair_eq : ∀ p q : F.Occ, p ≠ q → F.eval p = F.eval q → Φ q = S.twin (Φ p)
  /-- the over/under bits: over = smaller slope -/
  over_iff : ∀ p q : F.Occ, p ≠ q → F.eval p = F.eval q →
    (S.overBit (Φ p) = true ↔ F.slope p.1 < F.slope q.1)
  /-- the signs: the over-first tangent-determinant sign -/
  sgn_eq : ∀ p q : F.Occ, p ≠ q → F.eval p = F.eval q → F.slope p.1 < F.slope q.1 →
    ((S.sign (Φ p).1 : ℤ)) = F.crossSign p.1 q.1

namespace Marking

variable {F} {S : Diagram}

/-- a marked diagram has the front's number of component circles -/
theorem c_eq (m : F.Marking S) : S.Γ.c = F.c := (Fin.equiv_iff_eq.mp ⟨m.e⟩).symm

theorem componentCount_eq (m : F.Marking S) : S.componentCount = F.c := m.c_eq

theorem card_visit_eq (m : F.Marking S) : Fintype.card S.Γ.Visit = Fintype.card F.Occ :=
  (Fintype.card_congr m.Φ).symm

/-- the under branch of a marked double point carries bit `false` -/
theorem under_bit (m : F.Marking S) {p q : F.Occ} (hne : p ≠ q) (he : F.eval p = F.eval q)
    (hs : F.slope p.1 < F.slope q.1) : S.overBit (m.Φ q) = false := by
  have h := m.over_iff q p hne.symm he.symm
  rcases Bool.eq_false_or_eq_true (S.overBit (m.Φ q)) with hb | hb
  · exact absurd (h.mp hb) (lt_asymm hs)
  · exact hb

end Marking

/-! ## 8. The printed rounding (sm-3:1838-1841): clean-disc cusp replacement, then S(F) -/

/-- the cusps of `F`, one parameter each -/
abbrev Cusp : Type := {p : Param F.c // p ∈ F.cuspSet}

theorem Cusp.isCusp (c : F.Cusp) : F.IsCusp c.1 := F.isCusp_of_mem_cuspSet c.2

theorem Cusp.mem_Ico (c : F.Cusp) : c.1.2 ∈ Set.Ico (0 : ℝ) 1 := (F.mem_cuspSet.mp c.2).1

instance : Fintype F.Cusp := inferInstance

theorem card_cusp : Fintype.card F.Cusp = F.cuspSet.card := Fintype.card_coe _

/-- "In disjoint clean cusp discs replace each cusp by a simple regular arc with the same oriented
attachments and no crossing" (sm-3:1838-1840), for `G : Fin F.c → SmoothLoop` on the SAME
parameter circles as `F` (FR-4):
* `U c` a disc (`disc`, the accepted `IsDisc`) about the cusp point (`center`), the discs pairwise
  `disjoint`, each *clean*: `F` meets `U c` only along the cusp's own arc, the parameter interval
  `I c` (`clean`);
* `G = F` outside the intervals (`agree`) — hence the same oriented attachments: the parameter
  circles, their orientation and the end points of each arc are literally shared;
* on `I c` the new arc lies in the disc (`inside`), is regular (`regular`), simple (`simple`) and
  creates no crossing (`no_crossing`). -/
structure GeomRounding (G : Fin F.c → SmoothLoop) where
  /-- the cusp discs -/
  U : F.Cusp → Set Plane
  /-- the parameter interval of each cusp's arc -/
  I : F.Cusp → Set ℝ
  /-- "cusp discs" -/
  disc : ∀ c, IsDisc (U c)
  /-- the disc is about its cusp -/
  center : ∀ c, F.eval c.1 ∈ interior (U c)
  /-- the arc replaced is an open parameter interval around the cusp parameter, shorter than the
  circle -/
  interval : ∀ c, ∃ a b : ℝ, a < c.1.2 ∧ c.1.2 < b ∧ b - a < 1 ∧ I c = Set.Ioo a b
  /-- "disjoint" -/
  disjoint : ∀ c c', c ≠ c' → Disjoint (U c) (U c')
  /-- "clean": the front meets a cusp disc only along that cusp's arc -/
  clean : ∀ c (q : Param F.c), F.eval q ∈ U c → q.1 = c.1.1 ∧ ∃ n : ℤ, q.2 + n ∈ I c
  /-- "with the same oriented attachments": unchanged outside the arcs -/
  agree : ∀ (i : Fin F.c) (t : ℝ), (∀ c : F.Cusp, c.1.1 = i → ∀ n : ℤ, t + n ∉ I c) →
    (G i).γ t = (F.comp i).γ t
  /-- the replacing arc stays in the disc -/
  inside : ∀ c, ∀ t ∈ I c, (G c.1.1).γ t ∈ U c
  /-- "regular arc" -/
  regular : ∀ c, ∀ t ∈ I c, deriv (G c.1.1).γ t ≠ 0
  /-- "simple" -/
  simple : ∀ c, Set.InjOn (G c.1.1).γ (I c)
  /-- "and no crossing" -/
  no_crossing : ∀ c, ∀ t ∈ I c, ∀ q : Param F.c, ¬ SameParam (c.1.1, t) q →
    (G q.1).γ q.2 ≠ (G c.1.1).γ t

namespace GeomRounding

variable {F} {G : Fin F.c → SmoothLoop} (r : F.GeomRounding G)

theorem cusp_mem_I (c : F.Cusp) : c.1.2 ∈ r.I c := by
  obtain ⟨a, b, ha, hb, -, hI⟩ := r.interval c
  rw [hI]; exact ⟨ha, hb⟩

theorem isOpen_I (c : F.Cusp) : IsOpen (r.I c) := by
  obtain ⟨a, b, -, -, -, hI⟩ := r.interval c
  rw [hI]; exact isOpen_Ioo

theorem cusp_mem_U (c : F.Cusp) : F.eval c.1 ∈ r.U c := interior_subset (r.center c)

/-- the cusp point of another cusp is outside this cusp's disc -/
theorem cusp_notMem_U_of_ne {c c' : F.Cusp} (h : c ≠ c') : F.eval c'.1 ∉ r.U c := fun hm =>
  Set.disjoint_left.mp (r.disjoint c c' h) hm (r.cusp_mem_U c')

/-- an arc interval is shorter than the circle: it contains at most one representative of each
parameter -/
theorem eq_of_mem_I_of_sameParam {c : F.Cusp} {t t' : ℝ} (ht : t ∈ r.I c) (ht' : t' ∈ r.I c)
    (h : SameParam (c.1.1, t) (c.1.1, t')) : t = t' := by
  obtain ⟨a, b, -, -, hlen, hI⟩ := r.interval c
  rw [hI] at ht ht'
  obtain ⟨-, n, hn⟩ := h
  simp only at hn
  have h1 : (n : ℝ) < 1 := by linarith [ht.1, ht.2, ht'.1, ht'.2]
  have h2 : (-1 : ℝ) < n := by linarith [ht.1, ht.2, ht'.1, ht'.2]
  have h3 : n < 1 := by exact_mod_cast h1
  have h4 : -1 < n := by exact_mod_cast h2
  have hn0 : n = 0 := by omega
  subst hn0
  simp only [Int.cast_zero, add_zero] at hn
  exact hn.symm

/-- the new arc is injective as a map of the circle on its interval -/
theorem inj_arc {c : F.Cusp} {t t' : ℝ} (ht : t ∈ r.I c) (ht' : t' ∈ r.I c)
    (h : (G c.1.1).γ t = (G c.1.1).γ t') : t = t' :=
  r.simple c ht ht' h

/-- the rounding agrees with the front at every parameter whose whole orbit avoids the arcs of
its circle -/
theorem eval_eq {i : Fin F.c} {t : ℝ}
    (h : ∀ c : F.Cusp, c.1.1 = i → ∀ n : ℤ, t + n ∉ r.I c) : (G i).γ t = F.eval (i, t) :=
  r.agree i t h

end GeomRounding

/-- `S` is a rounding `S(F)` of `F`: a cusp-free smooth front `G` on the same parameter circles
obtained from `F` by the printed cusp replacement (`geom`), read polygonally by a marking of its
named record (`mark`) — "The resulting ordinary diagram is denoted S(F)" (sm-3:1840-1841; FR-1). -/
structure Rounding (S : Diagram) where
  /-- the rounded front -/
  G : SmoothFront
  /-- on the same parameter circles -/
  hc : G.c = F.c
  /-- "ordinary": no cusps -/
  cuspFree : G.CuspFree
  /-- the printed clean-disc cusp replacement -/
  geom : F.GeomRounding (fun i => G.comp (Fin.cast hc.symm i))
  /-- the polygonal reading (FR-1) -/
  mark : G.Marking S

/-- `S` is an `S(F)`. -/
def IsRounding (S : Diagram) : Prop := Nonempty (F.Rounding S)

theorem isRounding_iff (S : Diagram) :
    F.IsRounding S ↔ ∃ (G : SmoothFront) (hc : G.c = F.c), G.CuspFree ∧
      Nonempty (F.GeomRounding (fun i => G.comp (Fin.cast hc.symm i))) ∧ Nonempty (G.Marking S) := by
  constructor
  · rintro ⟨ρ⟩
    exact ⟨ρ.G, ρ.hc, ρ.cuspFree, ⟨ρ.geom⟩, ⟨ρ.mark⟩⟩
  · rintro ⟨G, hc, hcf, ⟨geom⟩, ⟨mark⟩⟩
    exact ⟨⟨G, hc, hcf, geom, mark⟩⟩

theorem Rounding.componentCount_eq {S : Diagram} (ρ : F.Rounding S) : S.componentCount = F.c :=
  ρ.mark.componentCount_eq.trans ρ.hc

theorem IsRounding.componentCount_eq {F : SmoothFront} {S : Diagram} (h : F.IsRounding S) :
    S.componentCount = F.c :=
  h.elim fun ρ => ρ.componentCount_eq

/-- `d(F) = deg_a P_{S(F)}` on a rounding `S` (display ng:defect, sm-3:1896-1898) -/
def dOf (_F : SmoothFront) (S : Diagram) : ℤ := degAZ (P S)

/-- `B(F) = D(F) − w(F) − d(F) − 1` (display ng:defect, sm-3:1896-1899), the *defect* -/
def defect (S : Diagram) : ℤ := (F.downCount : ℤ) - F.writhe - F.dOf S - 1

theorem dOf_def (S : Diagram) : F.dOf S = degAZ (P S) := rfl

theorem defect_def (S : Diagram) :
    F.defect S = (F.downCount : ℤ) - F.writhe - degAZ (P S) - 1 := rfl

theorem defect_eq_of_P_eq {S S' : Diagram} (h : P S = P S') : F.defect S = F.defect S' := by
  unfold defect dOf; rw [h]

/-- `d(F)` and `B(F)` depend on `S` only through its named record (rp:record-polynomial via the
accepted `presentations`). -/
theorem defect_eq_of_recordIso {S S' : Diagram} (h : Nonempty (RecordIso S.record S'.record)) :
    F.defect S = F.defect S' :=
  F.defect_eq_of_P_eq (presentations S S' h)

/-- `B(F) ≥ 0` is the inequality `w(F) − D(F) ≤ −deg_a P_{S(F)} − 1` of ng:local-front-bound
(sm-3:2343 "Substituting ng:defect gives ng:front-inequality"). -/
theorem defect_nonneg_iff (S : Diagram) :
    0 ≤ F.defect S ↔ F.writhe - (F.downCount : ℤ) ≤ -degAZ (P S) - 1 := by
  unfold defect dOf; omega

theorem defect_nonneg_iff_slNg (S : Diagram) : 0 ≤ F.defect S ↔ F.slNg ≤ -degAZ (P S) - 1 :=
  F.defect_nonneg_iff S

end SmoothFront

/-! ## 9. The DEFINE-row bundle -/

/-- Definition ng:front-domain (sm-3:1825-1841) as printed, one field per printed clause, with
display ng:defect (sm-3:1896-1899) and the printed exact germ (sm-3:2747) as the certificates of
the class.  Readings: FR-1 (polygonal `S(F)`), FR-2 (derivative-form cusp criterion), FR-3
(`C^∞`, 1-periodic parametrizations), FR-4 (parametrized rounding); see the module docstring. -/
structure FrontDomainDefinitionData : Prop where
  /-- "A front F is an actual map of a nonempty finite union of parameter circles to the oriented
  (x,z) plane": `c ≥ 1` parameter circles, each a smooth 1-periodic map to `Plane` (FR-3). -/
  map : ∀ F : SmoothFront, 0 < F.c ∧
    ∀ i : Fin F.c, ContDiff ℝ ∞ (F.comp i).γ ∧ Function.Periodic (F.comp i).γ 1
  /-- "with finitely many transverse double points": the double points (distinct parameters of the
  fundamental period with equal image) form the finite set `doubleSet`, and at each of them the
  velocities are independent. -/
  double_points : ∀ F : SmoothFront,
    (∀ q : Param F.c × Param F.c, q ∈ F.doubleSet ↔
      q.1.2 ∈ Set.Ico (0 : ℝ) 1 ∧ q.2.2 ∈ Set.Ico (0 : ℝ) 1 ∧ q.1 ≠ q.2 ∧ F.eval q.1 = F.eval q.2) ∧
    ∀ p q : Param F.c, F.IsDouble p q → det (F.vel p) (F.vel q) ≠ 0
  /-- "and ordinary semicubical cusps": the cusps (zeros of `γ'` in the fundamental period) form the
  finite set `cuspSet`, and at every zero of `γ'` one has `det(γ'', γ''') ≠ 0` (FR-2). -/
  cusps : ∀ F : SmoothFront,
    (∀ p : Param F.c, p ∈ F.cuspSet ↔ p.2 ∈ Set.Ico (0 : ℝ) 1 ∧ F.IsCusp p) ∧
    ∀ p : Param F.c, F.IsCusp p → det (F.acc p) (F.jerk p) ≠ 0
  /-- "no other singularities": every non-immersive parameter is a cusp of the previous clause,
  and every multiple point is a double point (no triple points). -/
  no_other_singularities : ∀ F : SmoothFront,
    (∀ p : Param F.c, F.vel p = 0 ↔ F.IsCusp p) ∧
    ∀ p q r : Param F.c, ¬ SameParam p q → ¬ SameParam q r → ¬ SameParam p r →
      F.eval p = F.eval q → F.eval q = F.eval r → False
  /-- "and no vertical tangencies on regular arcs" -/
  no_vertical : ∀ (F : SmoothFront) (p : Param F.c), F.vel p ≠ 0 → (F.vel p).1 ≠ 0
  /-- "The limiting tangent at every cusp is also nonvertical: in a semicubical parameter u with
  cusp at u=0, require x''(0)≠0": `(γ'').1 ≠ 0` at every cusp (FR-2). -/
  cusp_nonvertical : ∀ (F : SmoothFront) (p : Param F.c), F.IsCusp p → (F.acc p).1 ≠ 0
  /-- "Cusps meet no other strand or singularity." -/
  cusp_alone : ∀ (F : SmoothFront) (p q : Param F.c), ¬ SameParam p q → F.IsCusp p →
    F.eval p ≠ F.eval q
  /-- "At a crossing the branch with smaller dz/dx is over": `slope = dz/dx`, `IsOverUnder p q`
  says `p` is the over branch; at every double point exactly one branch is over. -/
  over_rule : ∀ F : SmoothFront,
    (∀ p : Param F.c, F.slope p = (F.vel p).2 / (F.vel p).1) ∧
    (∀ p q : Param F.c, F.IsOverUnder p q ↔ F.IsDouble p q ∧ F.slope p < F.slope q) ∧
    ∀ p q : Param F.c, F.IsDouble p q → Xor (F.IsOverUnder p q) (F.IsOverUnder q p)
  /-- The over rule agrees with the sign convention of def:positive-lift / sm-3:1908-1912: for
  nonvertical `u`, `v` with `u` of smaller slope, `det u v > 0` iff `u.1 v.1 > 0`; the printed
  standard crossing `(1,−1), (1,1)` has determinant `2`; on a front the over-first sign is `+1` iff
  the branches travel in the same x-direction. -/
  over_first_sign :
    (∀ u v : Plane, u.1 ≠ 0 → v.1 ≠ 0 → u.2 / u.1 < v.2 / v.1 → (0 < det u v ↔ 0 < u.1 * v.1)) ∧
    det ((1 : ℝ), (-1 : ℝ)) ((1 : ℝ), (1 : ℝ)) = 2 ∧
    ∀ (F : SmoothFront) (p q : Param F.c), F.IsOverUnder p q →
      (F.crossSign p q = 1 ↔ 0 < (F.vel p).1 * (F.vel q).1)
  /-- "A downward cusp is traversed from its locally upper arm to its locally lower arm":
  `IsDownCusp p ↔ IsCusp p ∧ x''·det(γ'', γ''') < 0` (FR-2), and every cusp is downward or upward,
  not both. -/
  downward_cusp : ∀ F : SmoothFront,
    (∀ p : Param F.c, F.IsDownCusp p ↔ F.IsCusp p ∧ (F.acc p).1 * det (F.acc p) (F.jerk p) < 0) ∧
    (∀ p : Param F.c, F.IsUpCusp p ↔ F.IsCusp p ∧ 0 < (F.acc p).1 * det (F.acc p) (F.jerk p)) ∧
    ∀ p : Param F.c, F.IsCusp p → Xor (F.IsDownCusp p) (F.IsUpCusp p)
  /-- The left/right cusp vocabulary of the certificate section (sm-3:1906-1907): a cusp is left
  iff its limiting tangent `γ''` points right (`x'' > 0`), right iff `x'' < 0`; every cusp is one
  or the other, not both. -/
  left_right_cusp : ∀ F : SmoothFront,
    (∀ p : Param F.c, F.IsLeftCusp p ↔ F.IsCusp p ∧ 0 < (F.acc p).1) ∧
    (∀ p : Param F.c, F.IsRightCusp p ↔ F.IsCusp p ∧ (F.acc p).1 < 0) ∧
    ∀ p : Param F.c, F.IsCusp p → Xor (F.IsLeftCusp p) (F.IsRightCusp p)
  /-- "Write D(F) for the number of downward cusps" (and `D + U = #cusps`). -/
  D_count : ∀ F : SmoothFront,
    F.downCount = (F.cuspSet.filter fun p => F.IsDownCusp p).card ∧
    F.downCount + F.upCount = F.cuspSet.card
  /-- "w(F) for the sum of the over-first tangent-determinant crossing signs": the sum over the
  double points, each taken once in its over-first order `(over, under)`, of
  `sgn det(velocity_over, velocity_under)`. -/
  w_sum : ∀ F : SmoothFront,
    F.writhe = ∑ q ∈ F.crossingPairs, F.crossSign q.1 q.2 ∧
    (∀ q : Param F.c × Param F.c, q ∈ F.crossingPairs ↔ q ∈ F.doubleSet ∧ F.slope q.1 < F.slope q.2) ∧
    (∀ q : Param F.c × Param F.c, q ∈ F.doubleSet →
      Xor (q ∈ F.crossingPairs) (q.swap ∈ F.crossingPairs)) ∧
    ∀ p q : Param F.c, F.IsDouble p q →
      F.crossSign p q = ((SignType.sign (det (F.vel p) (F.vel q)) : SignType) : ℤ)
  /-- "and s(F) for the number of crossings plus cusps." -/
  s_count : ∀ F : SmoothFront, F.sCount = F.crossingPairs.card + F.cuspSet.card
  /-- "In disjoint clean cusp discs": each cusp has a disc (`IsDisc`) about it, the discs are
  pairwise disjoint, and each is clean (the front meets it only along the cusp's own arc). -/
  rounding_discs : ∀ (F : SmoothFront) (G : Fin F.c → SmoothLoop) (r : F.GeomRounding G)
      (c : F.Cusp),
    IsDisc (r.U c) ∧ F.eval c.1 ∈ interior (r.U c) ∧
    (∀ c', c ≠ c' → Disjoint (r.U c) (r.U c')) ∧
    ∀ q : Param F.c, F.eval q ∈ r.U c → q.1 = c.1.1 ∧ ∃ n : ℤ, q.2 + n ∈ r.I c
  /-- "replace each cusp by a simple regular arc ... and no crossing": on the cusp's parameter
  interval (an open interval around the cusp parameter, shorter than the circle) the new arc stays
  in the disc, is regular, simple and meets no other point of the rounded curves. -/
  rounding_arc : ∀ (F : SmoothFront) (G : Fin F.c → SmoothLoop) (r : F.GeomRounding G)
      (c : F.Cusp),
    (∃ a b : ℝ, a < c.1.2 ∧ c.1.2 < b ∧ b - a < 1 ∧ r.I c = Set.Ioo a b) ∧
    (∀ t ∈ r.I c, (G c.1.1).γ t ∈ r.U c) ∧
    (∀ t ∈ r.I c, deriv (G c.1.1).γ t ≠ 0) ∧
    Set.InjOn (G c.1.1).γ (r.I c) ∧
    ∀ t ∈ r.I c, ∀ q : Param F.c, ¬ SameParam (c.1.1, t) q → (G q.1).γ q.2 ≠ (G c.1.1).γ t
  /-- "with the same oriented attachments": the rounded curves are the same parameter circles,
  equal to the front outside the arcs (FR-4). -/
  rounding_attachments : ∀ (F : SmoothFront) (G : Fin F.c → SmoothLoop) (r : F.GeomRounding G)
      (i : Fin F.c) (t : ℝ),
    (∀ c : F.Cusp, c.1.1 = i → ∀ n : ℤ, t + n ∉ r.I c) → (G i).γ t = (F.comp i).γ t
  /-- "The resulting ordinary diagram is denoted S(F)": `S` is an `S(F)` iff it carries the named
  record of a cusp-free front on the same circles obtained from `F` by the cusp replacement
  (FR-1). -/
  resulting_diagram : ∀ (F : SmoothFront) (S : Diagram),
    F.IsRounding S ↔ ∃ (G : SmoothFront) (hc : G.c = F.c), G.CuspFree ∧
      Nonempty (F.GeomRounding (fun i => G.comp (Fin.cast hc.symm i))) ∧ Nonempty (G.Marking S)
  /-- The named record carried by a marking (FR-1; the items of ng:smoothing-record): component
  circles (crossing-free ones included, so `S` has `c` components), crossing occurrences, cyclic
  orders, pairing, over/under bits and signs. -/
  named_record : ∀ (F : SmoothFront) (S : Diagram) (m : F.Marking S),
    S.componentCount = F.c ∧
    (∀ p : F.Occ, S.compOf (m.Φ p) = m.e p.1.1) ∧
    (∀ p q r : F.Occ, p.1.1 = q.1.1 → q.1.1 = r.1.1 →
      (cycBetween p.1.2 q.1.2 r.1.2 ↔
        cycBetween (S.visitCoord (m.Φ p)) (S.visitCoord (m.Φ q)) (S.visitCoord (m.Φ r)))) ∧
    (∀ p q : F.Occ, p ≠ q → F.eval p = F.eval q → m.Φ q = S.twin (m.Φ p)) ∧
    (∀ p q : F.Occ, p ≠ q → F.eval p = F.eval q →
      (S.overBit (m.Φ p) = true ↔ F.slope p.1 < F.slope q.1)) ∧
    ∀ p q : F.Occ, p ≠ q → F.eval p = F.eval q → F.slope p.1 < F.slope q.1 →
      ((S.sign (m.Φ p).1 : ℤ)) = F.crossSign p.1 q.1
  /-- The printed exact cusp germ `x = x₀ + Au², z = z₀ + Ay₀u² + ⅔Au³` (sm-3:2747) is smooth and
  passes the cusp clauses at `u = 0` for every `A ≠ 0`: `γ' = 0`, `det(γ'', γ''') = 8A² ≠ 0`,
  `x''(0) = 2A ≠ 0`; its discriminant is `16A³`, and for `u > 0` its later arm is the higher one
  iff `16A³ > 0` (the down/up rule checked on the germ, FR-2). -/
  germ : ∀ A y₀ x₀ z₀ : ℝ, ContDiff ℝ ∞ (germFront A y₀ x₀ z₀) ∧
    (A ≠ 0 → deriv (germFront A y₀ x₀ z₀) 0 = 0 ∧
      det (iteratedDeriv 2 (germFront A y₀ x₀ z₀) 0) (iteratedDeriv 3 (germFront A y₀ x₀ z₀) 0) =
        8 * A ^ 2 ∧
      (iteratedDeriv 2 (germFront A y₀ x₀ z₀) 0).1 = 2 * A ∧ 8 * A ^ 2 ≠ 0 ∧ 2 * A ≠ 0) ∧
    (iteratedDeriv 2 (germFront A y₀ x₀ z₀) 0).1 *
      det (iteratedDeriv 2 (germFront A y₀ x₀ z₀) 0) (iteratedDeriv 3 (germFront A y₀ x₀ z₀) 0) =
      16 * A ^ 3 ∧
    ∀ u : ℝ, 0 < u →
      ((germFront A y₀ x₀ z₀ (-u)).2 < (germFront A y₀ x₀ z₀ u).2 ↔ 0 < 16 * A ^ 3)
  /-- Display ng:defect (sm-3:1896-1899): `d(F) = deg_a P_{S(F)}`, `B(F) = D(F) − w(F) − d(F) − 1`
  on a rounding `S`; `B(F)` depends on `S` only through its named record. -/
  defect : ∀ (F : SmoothFront) (S : Diagram),
    F.dOf S = degAZ (P S) ∧ F.defect S = (F.downCount : ℤ) - F.writhe - degAZ (P S) - 1 ∧
    ∀ S' : Diagram, Nonempty (RecordIso S.record S'.record) → F.defect S = F.defect S'

/-- Definition ng:front-domain (sm-3:1825-1841). -/
theorem front_domain_definition : FrontDomainDefinitionData where
  map := fun F => ⟨F.hc, fun i => ⟨(F.comp i).smooth, (F.comp i).periodic⟩⟩
  double_points := fun F =>
    ⟨fun _ => F.mem_doubleSet, fun _ _ h => F.det_vel_ne_zero_of_isDouble h⟩
  cusps := fun F => ⟨fun _ => F.mem_cuspSet, fun _ h => F.det_acc_jerk_ne_zero_of_isCusp h⟩
  no_other_singularities := fun F =>
    ⟨fun _ => Iff.rfl, fun p q r hpq hqr hpr hpq' hqr' => F.no_triple p q r hpq hqr hpr hpq' hqr'⟩
  no_vertical := fun F p h => F.no_vertical p.1 p.2 h
  cusp_nonvertical := fun F _ h => F.acc_fst_ne_zero_of_isCusp h
  cusp_alone := fun F p q hne h => F.cusp_alone p q hne h
  over_rule := fun F => ⟨fun _ => rfl, fun _ _ => Iff.rfl, fun _ _ h => F.isOverUnder_xor h⟩
  over_first_sign :=
    ⟨fun _ _ hu hv h => det_pos_iff_of_slope_lt hu hv h, det_standard_crossing,
      fun F _ _ h => F.crossSign_eq_one_iff_of_isOverUnder h⟩
  downward_cusp := fun F =>
    ⟨fun _ => Iff.rfl, fun _ => Iff.rfl, fun _ h => F.isDownCusp_xor_isUpCusp h⟩
  left_right_cusp := fun F =>
    ⟨fun _ => Iff.rfl, fun _ => Iff.rfl, fun _ h => F.isLeftCusp_xor_isRightCusp h⟩
  D_count := fun F => ⟨rfl, F.downCount_add_upCount⟩
  w_sum := fun F =>
    ⟨rfl, fun _ => F.mem_crossingPairs, fun _ h => F.crossingPairs_xor_swap h,
      fun _ _ h => F.crossSign_eq_sign h⟩
  s_count := fun _ => rfl
  rounding_discs := fun _ _ r c =>
    ⟨r.disc c, r.center c, fun c' h => r.disjoint c c' h, fun q h => r.clean c q h⟩
  rounding_arc := fun _ _ r c =>
    ⟨r.interval c, fun t ht => r.inside c t ht, fun t ht => r.regular c t ht, r.simple c,
      fun t ht q h => r.no_crossing c t ht q h⟩
  rounding_attachments := fun _ _ r i t h => r.agree i t h
  resulting_diagram := fun F S => F.isRounding_iff S
  named_record := fun _ _ m =>
    ⟨m.componentCount_eq, m.comp_eq, m.between_iff, m.pair_eq, m.over_iff, m.sgn_eq⟩
  germ := fun A y₀ x₀ z₀ =>
    ⟨germFront_smooth A y₀ x₀ z₀, fun hA => germFront_semicubical A y₀ x₀ z₀ hA,
      germFront_cuspDisc A y₀ x₀ z₀, fun u hu => germFront_later_arm_higher_iff A y₀ x₀ z₀ u hu⟩
  defect := fun F _ => ⟨rfl, rfl, fun _ h => F.defect_eq_of_recordIso h⟩

end

end SM
