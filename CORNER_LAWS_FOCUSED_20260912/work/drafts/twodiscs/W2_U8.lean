import SM.EmbeddedRotation
import SM.LinkMoves
import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Analysis.Convex.Hull
import Mathlib.SetTheory.Cardinal.Finite
import SM.DeletedTuple
import Mathlib.Analysis.Convex.Gauge
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Analysis.Convex.Join
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Topology.Baire.CompleteMetrizable

/-! ### W1 assembly note (2026-09-19)

`W1_Assembled.lean` = `Skeleton_FINAL.lean` + the wave-1 unit files `W1_U1, W1_U2, W1_U3, W1_U4, W1_U10,
W1_U11` merged by alignment against the skeleton (each unit's `u<k>h_` helpers sit where that unit put them,
immediately before the leaf that uses them; every closed leaf carries the body of the unit that closed it;
imports are the union).  Three leaf statements were corrected under rule 3 (marked `W1 ASSEMBLY (rule 3)` in
their docstrings): `U3_isPositivePLFromPlane_inv` (+ `hL : 0 < L`, false for `L ≤ 0`), `U4_polygonImage_ear`
(+ `hP`, `hac`, `hstrict`, false without them) and `U5_exists_ear_homeo` (+ `hcut`, false for a reflex ear);
the only wave-1 call site affected (`U10_pl_extension`) was patched.  Report: W1_ASSEMBLY_REPORT.md. -/

/-! ### Skeleton note (U0, 2026-09-19)

`Skeleton_FINAL.lean` = `Statements_FINAL.lean` (frozen; the definitions block, the bundle
`GaussTwoDiscsData` and the row-theorem header are byte-identical, enforced by
`check_57_identity.py`) + the LEAF statements of units U1-U11 (all `sorry`, names prefixed `U<k>_`)
+ the assembly of `lem_gauss_two_discs` and of the three consumer bridges from the leaves.  When
every leaf is closed the row closes with no further glue.  Plan: PLAN_FINAL.md §3.3; report:
SKELETON_REPORT.md. -/

/-! # Row 57 lem:gauss-two-discs — statement draft A (architect A, fidelity first)

Written 2026-09-19 (D-AUTH-20260919 G-09: row 57 un-deferred).  Source:
reference/SM/sm-3-statesum.tex:428-436 (statement), 437-542 (proof).  Plan: PLAN_A.md (same
directory), which records the fidelity risks FR-TD-1..6 of PLDISCS_FEASIBILITY.md §2.5 and the new
ones FR-TD-7..12 with the reading chosen here.  Not a module of work/lean; every leaf is `sorry`.
Check: `cd work/lean && lake env lean ../drafts/twodiscs/Statements_A.lean`.

Printed statement, clause by clause (memo §2.1 numbering):
* 57a "A simple polygonal circle in the oriented sphere has exactly two complementary regions"
* 57b "and both closures are PL discs."
* 57c "Finite prescribed positive PL boundary maps between such discs extend to positive PL disc maps."
* 57d "A continuous positive boundary map also extends to a topological disc map."
* 57e "The statement includes the exterior region."

Readings fixed here (details in PLAN_A.md §2):
* circle = `Embedded P` (accepted, SM/EmbeddedRotation.lean), its image `embeddedPolygonImage P = ⋃ edgeSegment`;
* sphere = `OnePoint Plane`, oriented by the plane's `det`; the point at infinity is the printed
  "one point off the curve" (sm-3:439);
* regions = connected components of the complement in the sphere (`ConnectedComponents`,
  `connectedComponentIn`); the exterior region is the component of `∞`;
* PL structure of the sphere = the printed two-disc model (sm-3:440-456): the square `Q_L` with the
  plane's straight structure, capped by a second square `Q_1` carried to the exterior of `Q_L` by the
  sup-norm radial inversion `capInvFun L` (orientation-preserving, affine on the seam);
* PL disc = image of a convex compact set with nonempty interior (`Link.IsDisc`, LinkMoves.lean:100) under
  a homeomorphism affine with positive determinant on every triangle of a finite straight
  triangulation (`Triangulation`, `IsPositivePLOn`);
* boundary maps are given in traversal coordinates by a lift `φ : ℝ → ℝ` (`traversal`, accepted);
  "positive" = orientation-preserving for the induced boundary orientations of the two discs, which
  for the traversal of `P` around region `s` is `traversalPositiveFor P s` (left turn = bounded region
  on the left, as in the accepted `EmbeddedRotationData.orientation`); "finite PL" = affine between
  finitely many marks of one period (`IsFinitePL`, the `rexB_pl` pattern). -/

namespace SM

open Set OnePoint

variable {n : ℕ}

/-! ## §1 The circle and its two complementary regions in the sphere -/

/-- The polygonal circle `C` in the plane: the union of the edge segments (def:polygon vocabulary;
for `Embedded P` it is the simple closed curve `range (traversal P)`). -/
def embeddedPolygonImage (P : LabelledTuple n) : Set Plane := ⋃ i, edgeSegment P i

/-- The oriented sphere (sm-3:430 "in the oriented sphere"): the one-point compactification of the
plane, oriented by the plane's `det`. -/
abbrev Sphere : Type := OnePoint Plane

/-- The circle as a subset of the sphere. -/
def sphereCircle (P : LabelledTuple n) : Set Sphere := ((↑) : Plane → Sphere) '' embeddedPolygonImage P

/-- The complement of the circle in the sphere (its connected components are the printed
"complementary regions"). -/
def sphereComplement (P : LabelledTuple n) : Set Sphere := (sphereCircle P)ᶜ

/-- The exterior region: the complementary region containing the point at infinity
(sm-3:434 "the exterior region"; sm-3:448-456 "the actual one-point-compactified exterior"). -/
def exteriorRegion (P : LabelledTuple n) : Set Sphere :=
  connectedComponentIn (sphereComplement P) ∞

/-- The interior (bounded) region: the rest of the complement; by 57a it is one connected region. -/
def interiorRegion (P : LabelledTuple n) : Set Sphere := sphereComplement P \ exteriorRegion P

/-- Which of the two complementary regions. -/
inductive Side
  | inner
  | outer

/-- The two regions by side. -/
def regionOf (P : LabelledTuple n) : Side → Set Sphere
  | .inner => interiorRegion P
  | .outer => exteriorRegion P

/-! ## §2 Straight triangulations and positive PL maps in the plane (new vocabulary) -/

/-- A straight, positively oriented, nondegenerate triangle of the plane. -/
structure Triangle where
  /-- the three vertices, in positive (counterclockwise) order -/
  v : Fin 3 → Plane
  pos : 0 < det (v 1 - v 0) (v 2 - v 0)

/-- The closed triangle spanned by the vertices. -/
def Triangle.carrier (T : Triangle) : Set Plane := convexHull ℝ (range T.v)

/-- A finite straight triangulation of a plane set `X`: finitely many straight triangles covering
exactly `X`, any two of which meet in a common face (the convex hull of their common vertices:
empty, a vertex, an edge, or the whole triangle). -/
structure Triangulation (X : Set Plane) where
  faces : Set Triangle
  finite : faces.Finite
  cover : (⋃ T ∈ faces, T.carrier) = X
  inter : ∀ T ∈ faces, ∀ T' ∈ faces,
    T.carrier ∩ T'.carrier = convexHull ℝ (range T.v ∩ range T'.v)

/-- `f` agrees with an affine map of the plane on `S`. -/
def AffineOn (f : Plane → Plane) (S : Set Plane) : Prop :=
  ∃ (M : Plane →ₗ[ℝ] Plane) (b : Plane), ∀ x ∈ S, f x = M x + b

/-- `f` is affine on the triangle `T` with positive determinant (orientation-preserving). -/
def IsPositiveAffineOn (f : Plane → Plane) (T : Triangle) : Prop :=
  AffineOn f T.carrier ∧ 0 < det (f (T.v 1) - f (T.v 0)) (f (T.v 2) - f (T.v 0))

/-- `f` is positive PL with respect to the triangulation `K`: affine with positive determinant on
each of its triangles. -/
def IsPositivePLOn (f : Plane → Plane) {X : Set Plane} (K : Triangulation X) : Prop :=
  ∀ T ∈ K.faces, IsPositiveAffineOn f T

/-- `f` restricts to a homeomorphism of `S` onto `S'`. -/
def IsHomeoOnto {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    (S : Set α) (S' : Set β) (f : α → β) : Prop :=
  ∃ e : S ≃ₜ S', ∀ z : S, (e z : β) = f z

/-- **PL disc in the plane** (sm-3:431 "PL discs"): the image of a convex compact set with nonempty
interior (`Link.IsDisc`, LinkMoves.lean:100, the accepted convex model disc) under a homeomorphism that is affine with
positive determinant on each triangle of a finite straight triangulation of the model. -/
def IsPLDisc (S : Set Plane) : Prop :=
  ∃ (D : Set Plane) (K : Triangulation D) (g : Plane → Plane),
    Link.IsDisc D ∧ IsPositivePLOn g K ∧ IsHomeoOnto D S g

/-! ## §3 The PL structure of the sphere: the printed two-disc model (sm-3:440-456)

The rectangle is the square `Q_L = {|x₁|, |x₂| ≤ L}` with the plane's straight structure (chart
`false`, the coercion `Plane → Sphere`).  The cap is the square `Q_1`, carried onto the closed
exterior of `Q_L` together with `∞` by the sup-norm radial inversion
`capInvFun L y = (L / ‖y‖_∞²) • (y₁, −y₂)` (chart `true`; `0 ↦ ∞`).  It is a homeomorphism of
`Q_1 \ {0}` onto `{‖x‖_∞ ≥ L}`, self-inverse up to the scale, direction-preserving up to the
reflection `y₂ ↦ −y₂` (which makes it orientation-preserving, so that "positive" means `det > 0`
in either chart), and on the seam `‖y‖_∞ = 1` it is the affine map `y ↦ L • (y₁, −y₂)`.  The
printed version uses the Euclidean radial map `ru ↦ (R(u)/r)u` onto the unit disc (sm-3:449-452);
the sup-norm version is the same construction in the square's own gauge and glues affinely
(FR-TD-7). -/

/-- The sup norm `‖x‖_∞ = max |x₁| |x₂|` of the plane (written out, instance-free). -/
def supNorm (x : Plane) : ℝ := max |x.1| |x.2|

/-- The closed square of half-width `L` about the origin. -/
def square (L : ℝ) : Set Plane := {x | supNorm x ≤ L}

/-- The polygon lies strictly inside the model square `Q_L` (sm-3:439 "inside a large rectangle"). -/
def InsideModel (L : ℝ) (P : LabelledTuple n) : Prop := ∀ i, supNorm (P i) < L

/-- Sup-norm radial inversion across `∂Q_L`, composed with the reflection `y₂ ↦ −y₂`. -/
noncomputable def capInvFun (L : ℝ) (y : Plane) : Plane := (L / supNorm y ^ 2) • (y.1, -y.2)

/-- The cap chart of the two-disc model at scale `L`: `Q_1 → Sphere`, `0 ↦ ∞`. -/
noncomputable def capChart (L : ℝ) (y : Plane) : Sphere :=
  if y = 0 then ∞ else ((capInvFun L y : Plane) : Sphere)

/-- The two charts of the model: `false` = the plane chart on `Q_L`, `true` = the cap chart on `Q_1`. -/
noncomputable def modelChart (L : ℝ) : Bool → Plane → Sphere
  | false => fun x => (x : Sphere)
  | true => capChart L

/-- The chart domains. -/
def modelDomain (L : ℝ) : Bool → Set Plane
  | false => square L
  | true => square 1

/-- Plane coordinates of a finite point of the sphere (junk value `0` at `∞`). -/
def planeOf : Sphere → Plane
  | ∞ => 0
  | (x : Plane) => x

/-- The inverse charts (junk outside the chart images). -/
noncomputable def modelChartInv (L : ℝ) : Bool → Sphere → Plane
  | false => planeOf
  | true => fun z => match z with
    | ∞ => 0
    | (x : Plane) => capInvFun L x

/-- The part of `S ⊆ Sphere` seen in chart `b`, in chart coordinates. -/
def chartPart (L : ℝ) (b : Bool) (S : Set Sphere) : Set Plane :=
  modelDomain L b ∩ modelChart L b ⁻¹' S

/-- `f : Sphere → Plane` is positive PL on `S` (model at scale `L`): in each chart, `S` carries a
finite straight triangulation on whose triangles `f ∘ chart` is affine with positive determinant. -/
def IsPositivePLToPlane (L : ℝ) (S : Set Sphere) (f : Sphere → Plane) : Prop :=
  ∀ b : Bool, ∃ K : Triangulation (chartPart L b S), IsPositivePLOn (f ∘ modelChart L b) K

/-- **PL disc in the sphere with boundary `B`** (model at scale `L`): `S` is carried onto a convex
compact plane set with nonempty interior by a homeomorphism that is positive PL in the model
charts and carries `B` onto the frontier of the model; the circle `B` lies in the closed region `S`
(`B ⊆ S`).  For `S` inside the plane chart this is `IsPLDisc` of its plane trace (bridge
`isPLDisc_of_isPLDiscSphere` below). -/
def IsPLDiscSphere (L : ℝ) (S B : Set Sphere) : Prop :=
  ∃ (D : Set Plane) (f : Sphere → Plane),
    Link.IsDisc D ∧ B ⊆ S ∧ IsHomeoOnto S D f ∧ f '' B = frontier D ∧ IsPositivePLToPlane L S f

/-- `F : Sphere → Sphere` is positive PL from `S` (model `L`) to the sphere with model `L'`: in
each source chart, `S` carries a finite straight triangulation each of whose triangles is sent by
`F` into the image of a single target chart, where `F` read in the two charts is affine with
positive determinant. -/
def IsPositivePLSphereMap (L L' : ℝ) (S : Set Sphere) (F : Sphere → Sphere) : Prop :=
  ∀ b : Bool, ∃ K : Triangulation (chartPart L b S), ∀ T ∈ K.faces, ∃ b' : Bool,
    (∀ x ∈ T.carrier, F (modelChart L b x) ∈ modelChart L' b' '' modelDomain L' b') ∧
    IsPositiveAffineOn (modelChartInv L' b' ∘ F ∘ modelChart L b) T

/-! ## §4 Boundary maps in traversal coordinates (sm-3:431-434) -/

/-- `φ` is piecewise affine with finitely many pieces on one period `[0, n]`
(sm-3:431 "finite prescribed ... PL": marks `0 = a 0 < a 1 < ⋯ < a m = n`, affine between them; the
accepted `rexB_pl` pattern of def:gauss-record). -/
def IsFinitePL (n : ℕ) (φ : ℝ → ℝ) : Prop :=
  ∃ (m : ℕ) (a : ℕ → ℝ), a 0 = 0 ∧ a m = n ∧ (∀ j < m, a j < a (j + 1)) ∧
    ∀ j < m, ∃ c d : ℝ, ∀ x ∈ Icc (a j) (a (j + 1)), φ x = c * x + d

/-- The traversal of `P` runs positively around the region `s` (the region on its left): for the
interior region iff `rotationNumber P > 0` (counterclockwise traversal, the accepted reading "left
turn = bounded region on the left" of `EmbeddedRotationData.orientation`), for the exterior region
iff `rotationNumber P < 0`.  This is the *induced-boundary-orientation* convention: the boundary of
an oriented disc is oriented so that the disc lies on its left, and for the sphere oriented by the
plane's `det` the two regions induce opposite orientations on the common circle.  The definition
is meaningful because the accepted `cb_embedded_rotation.pm_one` gives `rotationNumber P = ±1` for
`Embedded P`, so `0 < rotationNumber P` (counterclockwise) and `rotationNumber P < 0` (clockwise)
are the only two cases and exactly one of them holds. -/
def traversalPositiveFor [NeZero n] (P : LabelledTuple n) (s : Side) : Prop :=
  (0 < rotationNumber P ↔ s = Side.inner)

/-- A **positive boundary map** from `∂(region s of P)` to `∂(region s' of P')`, given in traversal
coordinates by its lift `φ : ℝ → ℝ` (`β (traversal P x) = traversal P' (φ x)`): continuous, strictly
monotone, of degree one, and orientation-preserving for the induced boundary orientations — `φ`
increases when the two traversals run positively around their regions together or negatively
together, and decreases otherwise (sm-3:431-434 "positive"). -/
structure IsPositiveBoundaryLift [NeZero n] {n' : ℕ} [NeZero n'] (P : LabelledTuple n) (s : Side)
    (P' : LabelledTuple n') (s' : Side) (φ : ℝ → ℝ) : Prop where
  continuous : Continuous φ
  same : (traversalPositiveFor P s ↔ traversalPositiveFor P' s') →
    StrictMono φ ∧ ∀ x, φ (x + n) = φ x + n'
  opposite : ¬ (traversalPositiveFor P s ↔ traversalPositiveFor P' s') →
    StrictAnti φ ∧ ∀ x, φ (x + n) = φ x - n'


/-! ## §L Leaves of the proof units (skeleton; every leaf is `sorry`)

Naming: `U<k>_<name>` for unit `U<k>` of PLAN_FINAL §3.3 (lanes: A = U1-U3, B = U4, C = U10/U11
convex models, then the sequential chain U5 → U6 → U7 → U9 → U8 → U10/U11).  Each docstring names
the printed step of sm-3:437-542 it renders. -/

/-! ### U1 (lane A) — convex/affine toolkit -/

/-- The triangle with vertices `f (T.v i)` for a positive affine `f` (its determinant clause is the
positivity field). -/
def Triangle.map (f : Plane → Plane) (T : Triangle) (h : IsPositiveAffineOn f T) : Triangle :=
  ⟨f ∘ T.v, h.2⟩

/-- `K'` refines `K`: every face of `K'` lies in a face of `K`. -/
def Triangulation.Refines {X : Set Plane} (K' K : Triangulation X) : Prop :=
  ∀ T' ∈ K'.faces, ∃ T ∈ K.faces, T'.carrier ⊆ T.carrier

/-- U1 (sm-3:440 "straight structure"): a triangle is compact. -/
theorem U1_triangle_isCompact (T : Triangle) : IsCompact T.carrier :=
  (finite_range T.v).isCompact_convexHull (𝕜 := ℝ)

/-- U1: a triangle is convex. -/
theorem U1_triangle_convex (T : Triangle) : Convex ℝ T.carrier := convex_convexHull ℝ _

/-- Barycentric coordinate `a` of `x` (weight of `T.v 1`), by Cramer's rule. -/
noncomputable def u1h_baryA (T : Triangle) (x : Plane) : ℝ :=
  det (x - T.v 0) (T.v 2 - T.v 0) / det (T.v 1 - T.v 0) (T.v 2 - T.v 0)

/-- Barycentric coordinate `b` of `x` (weight of `T.v 2`). -/
noncomputable def u1h_baryB (T : Triangle) (x : Plane) : ℝ :=
  det (T.v 1 - T.v 0) (x - T.v 0) / det (T.v 1 - T.v 0) (T.v 2 - T.v 0)

theorem u1h_bary_eq (T : Triangle) (x : Plane) :
    x = (1 - u1h_baryA T x - u1h_baryB T x) • T.v 0 + u1h_baryA T x • T.v 1 +
      u1h_baryB T x • T.v 2 := by
  simp only [u1h_baryA, u1h_baryB]
  set D := det (T.v 1 - T.v 0) (T.v 2 - T.v 0) with hDdef
  have hD : D ≠ 0 := T.pos.ne'
  ext <;> simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;>
    field_simp <;> simp only [hDdef, det, Prod.fst_sub, Prod.snd_sub] <;> ring

theorem u1h_det0 (T : Triangle) (x : Plane) :
    det (T.v 1 - T.v 0) (x - T.v 0) = det (T.v 1 - T.v 0) (T.v 2 - T.v 0) * u1h_baryB T x := by
  simp only [u1h_baryB]
  set D := det (T.v 1 - T.v 0) (T.v 2 - T.v 0) with hDdef
  have hD : D ≠ 0 := T.pos.ne'
  field_simp

theorem u1h_det2 (T : Triangle) (x : Plane) :
    det (T.v 0 - T.v 2) (x - T.v 2) = det (T.v 1 - T.v 0) (T.v 2 - T.v 0) * u1h_baryA T x := by
  simp only [u1h_baryA]
  set D := det (T.v 1 - T.v 0) (T.v 2 - T.v 0) with hDdef
  have hD : D ≠ 0 := T.pos.ne'
  field_simp
  simp only [det, Prod.fst_sub, Prod.snd_sub]; ring

theorem u1h_det1 (T : Triangle) (x : Plane) :
    det (T.v 2 - T.v 1) (x - T.v 1) =
      det (T.v 1 - T.v 0) (T.v 2 - T.v 0) * (1 - u1h_baryA T x - u1h_baryB T x) := by
  simp only [u1h_baryA, u1h_baryB]
  set D := det (T.v 1 - T.v 0) (T.v 2 - T.v 0) with hDdef
  have hD : D ≠ 0 := T.pos.ne'
  field_simp
  simp only [hDdef, det, Prod.fst_sub, Prod.snd_sub]; ring

/-- A closed half-plane `{x | 0 ≤ det u (x - p)}` is convex. -/
theorem u1h_convex_det_nonneg (u p : Plane) : Convex ℝ {x : Plane | 0 ≤ det u (x - p)} := by
  intro x hx y hy a b ha hb hab
  simp only [mem_ofPred_eq, det, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add,
    Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at hx hy ⊢
  obtain rfl : b = 1 - a := by linarith
  nlinarith [mul_nonneg ha hx, mul_nonneg hb hy]

/-- Membership in a triangle by the three `det` signs (proved here; `U1_mem_carrier_iff_det` below is
this statement). -/
theorem u1h_mem_carrier_iff_det (T : Triangle) (x : Plane) :
    x ∈ T.carrier ↔ 0 ≤ det (T.v 1 - T.v 0) (x - T.v 0) ∧ 0 ≤ det (T.v 2 - T.v 1) (x - T.v 1) ∧
      0 ≤ det (T.v 0 - T.v 2) (x - T.v 2) := by
  have hD := T.pos
  constructor
  · intro hx
    have hsub : T.carrier ⊆ {x | 0 ≤ det (T.v 1 - T.v 0) (x - T.v 0)} ∩
        ({x | 0 ≤ det (T.v 2 - T.v 1) (x - T.v 1)} ∩ {x | 0 ≤ det (T.v 0 - T.v 2) (x - T.v 2)}) := by
      refine convexHull_min ?_ ((u1h_convex_det_nonneg _ _).inter
        ((u1h_convex_det_nonneg _ _).inter (u1h_convex_det_nonneg _ _)))
      rintro _ ⟨i, rfl⟩
      simp only [mem_inter_iff, mem_ofPred_eq, det, Prod.fst_sub, Prod.snd_sub] at hD ⊢
      fin_cases i <;> simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, Fin.reduceFinMk] <;>
        refine ⟨?_, ?_, ?_⟩ <;> nlinarith [hD]
    exact hsub hx
  · rintro ⟨h0, h1, h2⟩
    rw [u1h_det0] at h0; rw [u1h_det1] at h1; rw [u1h_det2] at h2
    have hx := u1h_bary_eq T x
    set a := u1h_baryA T x
    set b := u1h_baryB T x
    clear_value a b
    have ha : 0 ≤ a := (mul_nonneg_iff_of_pos_left hD).1 h2
    have hb : 0 ≤ b := (mul_nonneg_iff_of_pos_left hD).1 h0
    have hab : 0 ≤ 1 - a - b := (mul_nonneg_iff_of_pos_left hD).1 h1
    rw [hx]
    have := (convex_convexHull ℝ (range T.v)).sum_mem (t := Finset.univ) (w := ![1 - a - b, a, b])
      (z := T.v) ?_ ?_ ?_
    · show _ ∈ convexHull ℝ (range T.v)
      simpa [Fin.sum_univ_three] using this
    · intro i _; fin_cases i <;> simp <;> linarith
    · simp [Fin.sum_univ_three]; ring
    · exact fun i _ => subset_convexHull ℝ _ (mem_range_self i)

theorem u1h_continuous_det (u p : Plane) : Continuous fun x : Plane => det u (x - p) := by
  unfold det; fun_prop

theorem u1h_isOpen_det_pos (u p : Plane) : IsOpen {x : Plane | 0 < det u (x - p)} :=
  isOpen_lt continuous_const (u1h_continuous_det u p)

/-- A set inside a closed half-plane has its interior inside the open half-plane. -/
theorem u1h_interior_subset_pos {S : Set Plane} {u p : Plane} (hu : u ≠ 0)
    (hS : ∀ x ∈ S, 0 ≤ det u (x - p)) : ∀ x ∈ interior S, 0 < det u (x - p) := by
  intro x hx
  by_contra hle
  have hzero : det u (x - p) = 0 := le_antisymm (not_lt.1 hle) (hS x (interior_subset hx))
  set w : Plane := (u.2, -u.1) with hw
  have hw' : det u w < 0 := by
    have : u.1 ≠ 0 ∨ u.2 ≠ 0 := by
      by_contra h
      rcases not_or.1 h with ⟨h1, h2⟩
      exact hu (Prod.ext (not_not.1 h1) (not_not.1 h2))
    simp only [det, hw]
    rcases this with h | h
    · nlinarith [sq_pos_of_ne_zero h, sq_nonneg u.2]
    · nlinarith [sq_pos_of_ne_zero h, sq_nonneg u.1]
  have ht : Filter.Tendsto (fun t : ℝ => x + t • w) (nhdsWithin 0 (Ioi 0)) (nhds x) := by
    have : Filter.Tendsto (fun t : ℝ => x + t • w) (nhds 0) (nhds (x + (0:ℝ) • w)) :=
      ((continuous_const.add (continuous_id.smul continuous_const)).tendsto 0)
    rw [zero_smul, add_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  have h1 : ∀ᶠ t in nhdsWithin (0:ℝ) (Ioi 0), x + t • w ∈ S :=
    ht.eventually (mem_interior_iff_mem_nhds.1 hx)
  obtain ⟨t, htS, ht0⟩ := (h1.and eventually_mem_nhdsWithin).exists
  have := hS _ htS
  have hcalc : det u (x + t • w - p) = det u (x - p) + t * det u w := by
    simp only [det, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst,
      Prod.smul_snd, smul_eq_mul]; ring
  rw [hcalc, hzero, zero_add] at this
  exact absurd this (not_le.2 (mul_neg_of_pos_of_neg ht0 hw'))

theorem u1h_edge01_ne (T : Triangle) : T.v 1 - T.v 0 ≠ 0 := by
  intro h; have := T.pos; rw [h] at this; simp [det] at this

theorem u1h_edge12_ne (T : Triangle) : T.v 2 - T.v 1 ≠ 0 := by
  intro h; have := T.pos
  have h' : det (T.v 2 - T.v 1) (T.v 0 - T.v 1) = det (T.v 1 - T.v 0) (T.v 2 - T.v 0) := by
    simp only [det, Prod.fst_sub, Prod.snd_sub]; ring
  rw [h] at h'; simp only [det, Prod.fst_sub, Prod.snd_sub] at this
  simp [det] at h'; linarith

theorem u1h_edge20_ne (T : Triangle) : T.v 0 - T.v 2 ≠ 0 := by
  intro h; have := T.pos
  have h' : det (T.v 0 - T.v 2) (T.v 1 - T.v 2) = det (T.v 1 - T.v 0) (T.v 2 - T.v 0) := by
    simp only [det, Prod.fst_sub, Prod.snd_sub]; ring
  rw [h] at h'; simp only [det, Prod.fst_sub, Prod.snd_sub] at this
  simp [det] at h'; linarith

/-- The interior of a triangle is the open triangle (three strict `det` inequalities). -/
theorem u1h_interior_triangle (T : Triangle) :
    interior T.carrier = {x | 0 < det (T.v 1 - T.v 0) (x - T.v 0) ∧
      0 < det (T.v 2 - T.v 1) (x - T.v 1) ∧ 0 < det (T.v 0 - T.v 2) (x - T.v 2)} := by
  have hc : ∀ y ∈ T.carrier, 0 ≤ det (T.v 1 - T.v 0) (y - T.v 0) ∧
      0 ≤ det (T.v 2 - T.v 1) (y - T.v 1) ∧ 0 ≤ det (T.v 0 - T.v 2) (y - T.v 2) :=
    fun y hy => (u1h_mem_carrier_iff_det T y).1 hy
  apply Subset.antisymm
  · intro x hx
    exact ⟨u1h_interior_subset_pos (u1h_edge01_ne T) (fun y hy => (hc y hy).1) x hx,
      u1h_interior_subset_pos (u1h_edge12_ne T) (fun y hy => (hc y hy).2.1) x hx,
      u1h_interior_subset_pos (u1h_edge20_ne T) (fun y hy => (hc y hy).2.2) x hx⟩
  · apply interior_maximal
    · intro x hx; exact (u1h_mem_carrier_iff_det T x).2 ⟨hx.1.le, hx.2.1.le, hx.2.2.le⟩
    · exact (u1h_isOpen_det_pos _ _).and ((u1h_isOpen_det_pos _ _).and (u1h_isOpen_det_pos _ _))

/-- U1: a nondegenerate triangle has nonempty interior. -/
theorem U1_triangle_interior_nonempty (T : Triangle) : (interior T.carrier).Nonempty := by
  refine ⟨(1 / 3 : ℝ) • (T.v 0 + T.v 1 + T.v 2), ?_⟩
  rw [u1h_interior_triangle]
  have hD := T.pos
  simp only [mem_ofPred_eq, det, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add,
    Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at hD ⊢
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith [hD]

/-- U1 (sm-3:431 "PL discs", model disc): a triangle is a `Link.IsDisc`. -/
theorem U1_triangle_isDisc (T : Triangle) : Link.IsDisc T.carrier :=
  ⟨U1_triangle_convex T, U1_triangle_isCompact T, U1_triangle_interior_nonempty T⟩

/-- U1 (sm-3:439 "large rectangle"): the square `Q_L` is a `Link.IsDisc`. -/
theorem U1_square_isDisc {L : ℝ} (hL : 0 < L) : Link.IsDisc (square L) := by
  have h : square L = Metric.closedBall (0 : Plane) L := by
    ext x
    simp only [square, supNorm, mem_ofPred_eq, Metric.mem_closedBall, dist_zero_right,
      Prod.norm_def, Real.norm_eq_abs]
  rw [h]; exact Link.isDisc_closedBall 0 hL

/-- U1: membership in a positively oriented triangle by the three `det` signs. -/
theorem U1_mem_carrier_iff_det (T : Triangle) (x : Plane) :
    x ∈ T.carrier ↔ 0 ≤ det (T.v 1 - T.v 0) (x - T.v 0) ∧ 0 ≤ det (T.v 2 - T.v 1) (x - T.v 1) ∧
      0 ≤ det (T.v 0 - T.v 2) (x - T.v 2) :=
  u1h_mem_carrier_iff_det T x

theorem u1h_det_segment (p q x : Plane) (h : x ∈ segment ℝ p q) : det (q - p) (x - p) = 0 := by
  obtain ⟨α, β, -, -, hαβ, rfl⟩ := h
  obtain rfl : β = 1 - α := by linarith
  simp only [det, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
    Prod.smul_snd, smul_eq_mul]; ring

theorem u1h_seg0 (T : Triangle) (x : Plane) (h0 : det (T.v 1 - T.v 0) (x - T.v 0) = 0)
    (h1 : 0 ≤ det (T.v 2 - T.v 1) (x - T.v 1)) (h2 : 0 ≤ det (T.v 0 - T.v 2) (x - T.v 2)) :
    x ∈ segment ℝ (T.v 0) (T.v 1) := by
  have hD := T.pos
  rw [u1h_det0] at h0; rw [u1h_det1] at h1; rw [u1h_det2] at h2
  have hx := u1h_bary_eq T x
  set a := u1h_baryA T x
  set b := u1h_baryB T x
  clear_value a b
  have hb : b = 0 := by
    rcases mul_eq_zero.1 h0 with h | h
    · exact absurd h hD.ne'
    · exact h
  have ha : 0 ≤ a := (mul_nonneg_iff_of_pos_left hD).1 h2
  have hab : 0 ≤ 1 - a - b := (mul_nonneg_iff_of_pos_left hD).1 h1
  subst hb
  refine ⟨1 - a, a, by linarith, ha, by ring, ?_⟩
  rw [hx]; simp

theorem u1h_seg1 (T : Triangle) (x : Plane) (h0 : 0 ≤ det (T.v 1 - T.v 0) (x - T.v 0))
    (h1 : det (T.v 2 - T.v 1) (x - T.v 1) = 0) (h2 : 0 ≤ det (T.v 0 - T.v 2) (x - T.v 2)) :
    x ∈ segment ℝ (T.v 1) (T.v 2) := by
  have hD := T.pos
  rw [u1h_det0] at h0; rw [u1h_det1] at h1; rw [u1h_det2] at h2
  have hx := u1h_bary_eq T x
  set a := u1h_baryA T x
  set b := u1h_baryB T x
  clear_value a b
  have hab : 1 - a - b = 0 := by
    rcases mul_eq_zero.1 h1 with h | h
    · exact absurd h hD.ne'
    · exact h
  have ha : 0 ≤ a := (mul_nonneg_iff_of_pos_left hD).1 h2
  have hb : 0 ≤ b := (mul_nonneg_iff_of_pos_left hD).1 h0
  refine ⟨a, b, ha, hb, by linarith, ?_⟩
  rw [hx, hab]; simp

theorem u1h_seg2 (T : Triangle) (x : Plane) (h0 : 0 ≤ det (T.v 1 - T.v 0) (x - T.v 0))
    (h1 : 0 ≤ det (T.v 2 - T.v 1) (x - T.v 1)) (h2 : det (T.v 0 - T.v 2) (x - T.v 2) = 0) :
    x ∈ segment ℝ (T.v 2) (T.v 0) := by
  have hD := T.pos
  rw [u1h_det0] at h0; rw [u1h_det1] at h1; rw [u1h_det2] at h2
  have hx := u1h_bary_eq T x
  set a := u1h_baryA T x
  set b := u1h_baryB T x
  clear_value a b
  have ha : a = 0 := by
    rcases mul_eq_zero.1 h2 with h | h
    · exact absurd h hD.ne'
    · exact h
  have hb : 0 ≤ b := (mul_nonneg_iff_of_pos_left hD).1 h0
  have hab : 0 ≤ 1 - a - b := (mul_nonneg_iff_of_pos_left hD).1 h1
  subst ha
  refine ⟨b, 1 - b, hb, by linarith, by ring, ?_⟩
  rw [hx]; simp [add_comm]

/-- U1: the frontier of a triangle is the union of its three edges. -/
theorem U1_frontier_triangle (T : Triangle) :
    frontier T.carrier = ⋃ i : Fin 3, segment ℝ (T.v i) (T.v (i + 1)) := by
  rw [(U1_triangle_isCompact T).isClosed.frontier_eq, u1h_interior_triangle]
  ext x
  simp only [mem_sdiff, U1_mem_carrier_iff_det, mem_ofPred_eq, mem_iUnion, not_and_or, not_lt]
  constructor
  · rintro ⟨⟨h0, h1, h2⟩, hn⟩
    rcases hn with h | h | h
    · exact ⟨0, u1h_seg0 T x (le_antisymm h h0) h1 h2⟩
    · exact ⟨1, u1h_seg1 T x h0 (le_antisymm h h1) h2⟩
    · exact ⟨2, u1h_seg2 T x h0 h1 (le_antisymm h h2)⟩
  · rintro ⟨i, hi⟩
    fin_cases i <;> simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, Fin.reduceFinMk,
      Fin.reduceAdd, zero_add] at hi
    · have hmem : x ∈ T.carrier :=
        segment_subset_convexHull (mem_range_self 0) (mem_range_self 1) hi
      exact ⟨(U1_mem_carrier_iff_det T x).1 hmem, Or.inl (u1h_det_segment _ _ _ hi).le⟩
    · have hmem : x ∈ T.carrier :=
        segment_subset_convexHull (mem_range_self 1) (mem_range_self 2) hi
      exact ⟨(U1_mem_carrier_iff_det T x).1 hmem, Or.inr (Or.inl (u1h_det_segment _ _ _ hi).le)⟩
    · have hmem : x ∈ T.carrier :=
        segment_subset_convexHull (mem_range_self 2) (mem_range_self 0) hi
      exact ⟨(U1_mem_carrier_iff_det T x).1 hmem, Or.inr (Or.inr (u1h_det_segment _ _ _ hi).le)⟩

/-- U1 (sm-3:486-489 "regions"): the interior of a convex set with nonempty interior is connected. -/
theorem U1_interior_convex_isConnected {S : Set Plane} (hS : Convex ℝ S)
    (hne : (interior S).Nonempty) : IsConnected (interior S) :=
  ⟨hne, hS.interior.isPreconnected⟩

/-- The exterior `{y | R < ‖y‖}` of a closed ball in the plane is preconnected. -/
theorem u1h_isPreconnected_exterior (R : ℝ) (hR : 0 ≤ R) :
    IsPreconnected {y : Plane | R < ‖y‖} := by
  have hrank : 1 < Module.rank ℝ Plane := by
    rw [rank_prod', Module.rank_self]; exact_mod_cast (by norm_num : (1:ℕ) < 1 + 1)
  have hset : {y : Plane | R < ‖y‖} =
      (fun p : Plane × ℝ => p.2 • p.1) '' (Metric.sphere (0 : Plane) 1 ×ˢ Ioi R) := by
    ext y; constructor
    · intro hy
      have hy0 : y ≠ 0 := by rintro rfl; simp at hy; linarith
      refine ⟨(‖y‖⁻¹ • y, ‖y‖), ⟨?_, hy⟩, ?_⟩
      · simp only [mem_sphere_zero_iff_norm]
        rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 hy0)]
      · simp [smul_smul, hy0]
    · rintro ⟨⟨u, r⟩, ⟨hu, hr⟩, rfl⟩
      simp only [mem_sphere_zero_iff_norm] at hu
      simp only [mem_Ioi] at hr
      simp only [mem_ofPred_eq, norm_smul, hu, mul_one, Real.norm_eq_abs,
        abs_of_pos (hR.trans_lt hr)]
      exact hr
  rw [hset]
  exact ((isPreconnected_sphere hrank 0 1).prod isPreconnected_Ioi).image _
    (continuous_snd.smul continuous_fst).continuousOn

theorem u1h_isPreconnected_ray (y d : Plane) :
    IsPreconnected ((fun t : ℝ => y + t • d) '' Ici 0) :=
  isPreconnected_Ici.image _ (continuous_const.add (continuous_id.smul continuous_const)).continuousOn

/-- U1 (sm-3:486-489, the exterior): the complement of a compact convex set in the plane is
connected. -/
theorem U1_compl_compact_convex_isConnected {S : Set Plane} (hS : Convex ℝ S) (hc : IsCompact S) :
    IsConnected Sᶜ := by
  obtain ⟨R, hR0, hSR⟩ := hc.isBounded.subset_closedBall_lt 0 0
  have hfar : ∀ y : Plane, R < ‖y‖ → y ∈ Sᶜ := fun y hy hyS => by
    have := hSR hyS; rw [Metric.mem_closedBall, dist_zero_right] at this; linarith
  set x₀ : Plane := (R + 1, 0) with hx₀
  have hx₀R : R < ‖x₀‖ := by
    have : ‖x₀‖ = R + 1 := by
      rw [hx₀, Prod.norm_def]; simp only [norm_zero, Real.norm_eq_abs]
      rw [abs_of_pos (by linarith), max_eq_left (by linarith)]
    linarith
  refine ⟨⟨x₀, hfar x₀ hx₀R⟩, ?_⟩
  rcases S.eq_empty_or_nonempty with hS0 | ⟨a, ha⟩
  · rw [hS0, compl_empty]; exact convex_univ.isPreconnected
  apply isPreconnected_of_forall x₀
  intro y hy
  obtain ⟨f, u, hfu, huf⟩ := geometric_hahn_banach_closed_point hS hc.isClosed hy
  set d := y - a with hd
  have hfd : 0 < f d := by rw [hd, map_sub]; linarith [hfu a ha]
  have hd0 : d ≠ 0 := by rintro h; rw [h, map_zero] at hfd; exact lt_irrefl _ hfd
  have hnd : 0 < ‖d‖ := norm_pos_iff.2 hd0
  refine ⟨(fun t : ℝ => y + t • d) '' Ici 0 ∪ {z : Plane | R < ‖z‖}, ?_, Or.inr hx₀R,
    Or.inl ⟨0, mem_Ici.2 le_rfl, by simp⟩, ?_⟩
  · rintro z (⟨t, ht, rfl⟩ | hz)
    · intro hzS
      have := hfu _ hzS
      simp only [map_add, map_smul, smul_eq_mul] at this
      nlinarith [mul_nonneg (mem_Ici.1 ht) hfd.le]
    · exact hfar z hz
  · refine (u1h_isPreconnected_ray y d).union' ?_ (u1h_isPreconnected_exterior R hR0.le)
    have hpos : 0 < (R + ‖y‖ + 1) / ‖d‖ := div_pos (by linarith [norm_nonneg y]) hnd
    refine ⟨y + ((R + ‖y‖ + 1) / ‖d‖) • d, ⟨_, mem_Ici.2 hpos.le, rfl⟩, ?_⟩
    show R < ‖y + ((R + ‖y‖ + 1) / ‖d‖) • d‖
    have h1 : ‖((R + ‖y‖ + 1) / ‖d‖) • d‖ = R + ‖y‖ + 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hpos, div_mul_cancel₀ _ hnd.ne']
    have h2 := norm_sub_le (y + ((R + ‖y‖ + 1) / ‖d‖) • d) y
    rw [add_sub_cancel_left, h1] at h2
    linarith

/-- U1: `AffineOn` is stable under composition. -/
theorem U1_affineOn_comp {f g : Plane → Plane} {S S' : Set Plane} (hf : AffineOn f S)
    (hg : AffineOn g S') (h : f '' S ⊆ S') : AffineOn (g ∘ f) S := by
  obtain ⟨M, b, hM⟩ := hf
  obtain ⟨M', b', hM'⟩ := hg
  refine ⟨M'.comp M, M' b + b', fun x hx => ?_⟩
  simp only [Function.comp, LinearMap.comp_apply]
  rw [hM' (f x) (h ⟨x, hx, rfl⟩), hM x hx, map_add, add_assoc]

/-- U1: `AffineOn` restricts to subsets. -/
theorem U1_affineOn_mono {f : Plane → Plane} {S S' : Set Plane} (hf : AffineOn f S) (h : S' ⊆ S) :
    AffineOn f S' := by
  obtain ⟨M, b, hM⟩ := hf
  exact ⟨M, b, fun x hx => hM x (h hx)⟩

/-- A linear map of the plane scales `det` by its determinant `det (M (1,0)) (M (0,1))`. -/
theorem u1h_det_linear (M : Plane →ₗ[ℝ] Plane) (u v : Plane) :
    det (M u) (M v) = det (M (1, 0)) (M (0, 1)) * det u v := by
  have hu : M u = u.1 • M (1, 0) + u.2 • M (0, 1) := by
    rw [← map_smul, ← map_smul, ← map_add]; congr 1; ext <;> simp
  have hv : M v = v.1 • M (1, 0) + v.2 • M (0, 1) := by
    rw [← map_smul, ← map_smul, ← map_add]; congr 1; ext <;> simp
  rw [hu, hv]; simp only [det, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
    smul_eq_mul]; ring

/-- The vertices of a triangle lie in its carrier. -/
theorem u1h_vertex_mem_carrier (T : Triangle) (i : Fin 3) : T.v i ∈ T.carrier :=
  subset_convexHull ℝ _ (mem_range_self i)

/-- On a set where `f` is affine, differences are carried by the linear part. -/
theorem u1h_affineOn_sub {f : Plane → Plane} {S : Set Plane} {M : Plane →ₗ[ℝ] Plane} {b : Plane}
    (hM : ∀ x ∈ S, f x = M x + b) {x y : Plane} (hx : x ∈ S) (hy : y ∈ S) :
    f x - f y = M (x - y) := by
  rw [hM x hx, hM y hy, map_sub]; abel

/-- U1: an affine map on a triangle with positive determinant is positive on every sub-triangle. -/
theorem U1_isPositiveAffineOn_mono {f : Plane → Plane} {T T' : Triangle}
    (hf : IsPositiveAffineOn f T) (h : T'.carrier ⊆ T.carrier) : IsPositiveAffineOn f T' := by
  obtain ⟨⟨M, b, hM⟩, hpos⟩ := hf
  refine ⟨⟨M, b, fun x hx => hM x (h hx)⟩, ?_⟩
  have hv : ∀ i, T.v i ∈ T.carrier := u1h_vertex_mem_carrier T
  have hv' : ∀ i, T'.v i ∈ T.carrier := fun i => h (u1h_vertex_mem_carrier T' i)
  rw [u1h_affineOn_sub hM (hv 1) (hv 0), u1h_affineOn_sub hM (hv 2) (hv 0), u1h_det_linear] at hpos
  rw [u1h_affineOn_sub hM (hv' 1) (hv' 0), u1h_affineOn_sub hM (hv' 2) (hv' 0), u1h_det_linear]
  exact mul_pos (pos_of_mul_pos_left hpos T.pos.le) T'.pos

/-- The affine map `x ↦ M x + b` as a bundled `AffineMap`. -/
noncomputable def u1h_affineMap (M : Plane →ₗ[ℝ] Plane) (b : Plane) : Plane →ᵃ[ℝ] Plane :=
  (AffineEquiv.vaddConst ℝ b).toAffineMap.comp M.toAffineMap

theorem u1h_affineMap_apply (M : Plane →ₗ[ℝ] Plane) (b : Plane) (x : Plane) :
    u1h_affineMap M b x = M x + b := by
  simp [u1h_affineMap, vadd_eq_add]

/-- An affine map carries the convex hull of `s` onto the convex hull of its image. -/
theorem u1h_affineOn_image_convexHull {f : Plane → Plane} {s : Set Plane}
    (hf : AffineOn f (convexHull ℝ s)) : f '' convexHull ℝ s = convexHull ℝ (f '' s) := by
  obtain ⟨M, b, hM⟩ := hf
  have h1 : f '' convexHull ℝ s = u1h_affineMap M b '' convexHull ℝ s :=
    image_congr fun x hx => by rw [hM x hx, u1h_affineMap_apply]
  have h2 : f '' s = u1h_affineMap M b '' s :=
    image_congr fun x hx => by rw [hM x (subset_convexHull ℝ s hx), u1h_affineMap_apply]
  rw [h1, h2, AffineMap.image_convexHull]

theorem u1h_image_carrier {f : Plane → Plane} {T : Triangle} (hf : IsPositiveAffineOn f T) :
    f '' T.carrier = (T.map f hf).carrier := by
  show f '' convexHull ℝ (range T.v) = convexHull ℝ (range (f ∘ T.v))
  rw [u1h_affineOn_image_convexHull hf.1, range_comp]

/-- U1 (sm-3:535-537, positivity multiplicative): composition of positive affine maps is positive. -/
theorem U1_isPositiveAffineOn_comp {f g : Plane → Plane} {T : Triangle}
    (hf : IsPositiveAffineOn f T) (hg : IsPositiveAffineOn g (T.map f hf)) :
    IsPositiveAffineOn (g ∘ f) T :=
  ⟨U1_affineOn_comp hf.1 hg.1 (u1h_image_carrier hf).le, hg.2⟩

/-- The linear map with prescribed values on the basis `e₁ = v 1 - v 0`, `e₂ = v 2 - v 0` of a
triangle (Cramer's rule). -/
noncomputable def u1h_solveLinear (e₁ e₂ w₁ w₂ : Plane) : Plane →ₗ[ℝ] Plane where
  toFun q := (det q e₂ / det e₁ e₂) • w₁ + (det e₁ q / det e₁ e₂) • w₂
  map_add' q q' := by
    simp only [det, Prod.fst_add, Prod.snd_add]
    ext <;> simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;> ring
  map_smul' c q := by
    simp only [det, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, RingHom.id_apply]
    ext <;> simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;> ring

theorem u1h_solveLinear_apply (e₁ e₂ w₁ w₂ q : Plane) :
    u1h_solveLinear e₁ e₂ w₁ w₂ q = (det q e₂ / det e₁ e₂) • w₁ + (det e₁ q / det e₁ e₂) • w₂ := rfl

theorem u1h_det_self (u : Plane) : det u u = 0 := by simp [det, mul_comm]

/-- U1: the affine map of the plane sending the vertices of `T` to three prescribed points. -/
theorem U1_exists_affine_of_triangle (T : Triangle) (w : Fin 3 → Plane) :
    ∃ f : Plane → Plane, AffineOn f univ ∧ ∀ i, f (T.v i) = w i := by
  set M := u1h_solveLinear (T.v 1 - T.v 0) (T.v 2 - T.v 0) (w 1 - w 0) (w 2 - w 0) with hMdef
  have hD : det (T.v 1 - T.v 0) (T.v 2 - T.v 0) ≠ 0 := T.pos.ne'
  refine ⟨fun x => M (x - T.v 0) + w 0, ⟨M, w 0 - M (T.v 0), fun x _ => ?_⟩, fun i => ?_⟩
  · simp only [map_sub]; abel
  · fin_cases i
    · simp [hMdef, u1h_solveLinear_apply, det]
    · simp only [Fin.mk_one, Fin.isValue, hMdef, u1h_solveLinear_apply, u1h_det_self, zero_div,
        zero_smul, add_zero, div_self hD, one_smul]; abel
    · simp only [Fin.reduceFinMk, Fin.isValue, hMdef, u1h_solveLinear_apply, u1h_det_self,
        zero_div, zero_smul, zero_add, div_self hD, one_smul]; abel

/-- U1: the affine map of `U1_exists_affine_of_triangle` is positive on `T` iff the image triple is
positively oriented. -/
theorem U1_isPositiveAffineOn_of_det {f : Plane → Plane} (T : Triangle) (hf : AffineOn f univ)
    (hpos : 0 < det (f (T.v 1) - f (T.v 0)) (f (T.v 2) - f (T.v 0))) : IsPositiveAffineOn f T :=
  ⟨U1_affineOn_mono hf (subset_univ _), hpos⟩

/-- U1 (pasting lemma): a map continuous on each of finitely many closed sets is continuous on
their union. -/
theorem U1_continuousOn_iUnion_of_finite {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    {ι : Type*} [Finite ι] {C : ι → Set α} {f : α → β} (hC : ∀ i, IsClosed (C i))
    (hf : ∀ i, ContinuousOn f (C i)) : ContinuousOn f (⋃ i, C i) :=
  (locallyFinite_of_finite C).continuousOn_iUnion hC hf

/-- U1: `IsHomeoOnto` composes. -/
theorem U1_isHomeoOnto_comp {α β γ : Type*} [TopologicalSpace α] [TopologicalSpace β]
    [TopologicalSpace γ] {S : Set α} {S' : Set β} {S'' : Set γ} {f : α → β} {g : β → γ}
    (hf : IsHomeoOnto S S' f) (hg : IsHomeoOnto S' S'' g) : IsHomeoOnto S S'' (g ∘ f) := by
  obtain ⟨e, he⟩ := hf
  obtain ⟨e', he'⟩ := hg
  refine ⟨e.trans e', fun z => ?_⟩
  simp only [Homeomorph.trans_apply, Function.comp]
  rw [he', he]

/-- U1: `IsHomeoOnto` inverts (any left inverse on `S` is a homeomorphism `S' → S`). -/
theorem U1_isHomeoOnto_inv {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    {S : Set α} {S' : Set β} {f : α → β} {g : β → α} (hf : IsHomeoOnto S S' f)
    (hg : ∀ x ∈ S, g (f x) = x) : IsHomeoOnto S' S g := by
  obtain ⟨e, he⟩ := hf
  refine ⟨e.symm, fun z => ?_⟩
  have h1 : (z : β) = f (e.symm z) := by rw [← he]; simp
  rw [h1, hg _ (e.symm z).2]

theorem u1h_isHomeoOnto_image {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    {S : Set α} {S' : Set β} {f : α → β} (hf : IsHomeoOnto S S' f) : f '' S = S' := by
  obtain ⟨e, he⟩ := hf
  apply Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩; rw [← he ⟨x, hx⟩]; exact (e ⟨x, hx⟩).2
  · intro y hy
    refine ⟨e.symm ⟨y, hy⟩, (e.symm ⟨y, hy⟩).2, ?_⟩
    rw [← he]; simp

/-- U1: `IsHomeoOnto` restricts to a subset and its image. -/
theorem U1_isHomeoOnto_restrict {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    {S : Set α} {S' : Set β} {f : α → β} (hf : IsHomeoOnto S S' f) {A : Set α} (hA : A ⊆ S) :
    IsHomeoOnto A (f '' A) f := by
  have himg : f '' A ⊆ S' := (image_mono hA).trans (u1h_isHomeoOnto_image hf).le
  obtain ⟨e, he⟩ := hf
  have hmem : ∀ y : f '' A, ((e.symm ⟨y, himg y.2⟩ : S) : α) ∈ A := by
    rintro ⟨_, x, hx, rfl⟩
    have : e ⟨x, hA hx⟩ = ⟨f x, himg ⟨x, hx, rfl⟩⟩ := Subtype.ext (he _)
    show ((e.symm ⟨f x, _⟩ : S) : α) ∈ A
    rw [← this, e.symm_apply_apply]; exact hx
  refine ⟨{ toFun := fun x => ⟨f x, ⟨x, x.2, rfl⟩⟩
            invFun := fun y => ⟨_, hmem y⟩
            left_inv := fun x => ?_
            right_inv := fun y => ?_
            continuous_toFun := ?_
            continuous_invFun := ?_ }, fun z => rfl⟩
  · apply Subtype.ext
    show ((e.symm ⟨f x, _⟩ : S) : α) = x
    have : e ⟨x, hA x.2⟩ = ⟨f x, himg ⟨x, x.2, rfl⟩⟩ := Subtype.ext (he _)
    rw [← this, e.symm_apply_apply]
  · apply Subtype.ext
    show f ((e.symm ⟨y, himg y.2⟩ : S) : α) = y
    rw [← he, e.apply_symm_apply]
  · have hc : Continuous (S.domRestrict f) := by
      have h1 : S.domRestrict f = fun x : S => ((e x : S') : β) := by
        funext x; exact (he x).symm
      rw [h1]; exact continuous_subtype_val.comp e.continuous
    have : Continuous (fun x : A => f x) := by
      have h2 : (fun x : A => f x) = S.domRestrict f ∘ (fun x : A => (⟨x, hA x.2⟩ : S)) := rfl
      rw [h2]; exact hc.comp (continuous_subtype_val.subtype_mk _)
    exact this.subtype_mk _
  · exact ((continuous_subtype_val.comp e.symm.continuous).comp
      (continuous_subtype_val.subtype_mk _)).subtype_mk _

/-- U1: a plane homeomorphism is `IsHomeoOnto` any set onto its image. -/
theorem U1_isHomeoOnto_of_homeomorph (H : Plane ≃ₜ Plane) (A : Set Plane) :
    IsHomeoOnto A (H '' A) H :=
  ⟨H.image A, fun _ => rfl⟩

/-- Builder: a continuous bijection with continuous inverse between `S` and `S'` is `IsHomeoOnto`. -/
theorem u1h_isHomeoOnto_of_inv {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    {S : Set α} {S' : Set β} {f : α → β} {g : β → α} (hf : ContinuousOn f S) (hg : ContinuousOn g S')
    (hfS : MapsTo f S S') (hgS : MapsTo g S' S) (hgf : ∀ x ∈ S, g (f x) = x)
    (hfg : ∀ y ∈ S', f (g y) = y) : IsHomeoOnto S S' f := by
  refine ⟨{ toFun := fun x => ⟨f x, hfS x.2⟩
            invFun := fun y => ⟨g y, hgS y.2⟩
            left_inv := fun x => Subtype.ext (hgf x x.2)
            right_inv := fun y => Subtype.ext (hfg y y.2)
            continuous_toFun := ?_
            continuous_invFun := ?_ }, fun z => rfl⟩
  · exact (hf.comp_continuous continuous_subtype_val (fun x => x.2)).subtype_mk _
  · exact (hg.comp_continuous continuous_subtype_val (fun y => y.2)).subtype_mk _

/-- U1: a set is `IsHomeoOnto` its coercion image in the sphere. -/
theorem U1_isHomeoOnto_coe (A : Set Plane) :
    IsHomeoOnto A (((↑) : Plane → Sphere) '' A) ((↑) : Plane → Sphere) := by
  refine u1h_isHomeoOnto_of_inv (g := planeOf) OnePoint.continuous_coe.continuousOn ?_
    (mapsTo_image _ _) ?_ (fun x _ => rfl) ?_
  · rintro _ ⟨x, -, rfl⟩
    apply ContinuousAt.continuousWithinAt
    exact (OnePoint.isOpenEmbedding_coe.continuousAt_iff (g := planeOf)).1 continuousAt_id
  · rintro _ ⟨x, hx, rfl⟩; exact hx
  · rintro _ ⟨x, -, rfl⟩; rfl

/-! ### U2 (lane A) — triangulation basics -/

/-- U2: the edge `i` of `T` (from `T.v i` to `T.v (i+1)`). -/
def Triangle.edgeSeg (T : Triangle) (i : Fin 3) : Set Plane := segment ℝ (T.v i) (T.v (i + 1))

/-- U2 helper: every face lies in `X`. -/
theorem u2h_carrier_subset {X : Set Plane} (K : Triangulation X) {T : Triangle} (hT : T ∈ K.faces) :
    T.carrier ⊆ X := by
  rw [← K.cover]; exact subset_biUnion_of_mem (u := fun T => T.carrier) hT

/-- U2: the set `X` of a triangulation is compact. -/
theorem U2_isCompact_of_triangulation {X : Set Plane} (K : Triangulation X) : IsCompact X := by
  rw [← K.cover]; exact K.finite.isCompact_biUnion fun T _ => U1_triangle_isCompact T

/-- U2 (sm-3:440-443, the empty part of a chart): the empty set has a triangulation. -/
theorem U2_triangulation_empty : Nonempty (Triangulation (∅ : Set Plane)) := by
  exact ⟨{ faces := ∅, finite := finite_empty, cover := by simp, inter := by simp }⟩

/-- U2 helper: the `inter` clause for a face against itself. -/
theorem u2h_carrier_inter_self (T : Triangle) :
    T.carrier ∩ T.carrier = convexHull ℝ (range T.v ∩ range T.v) := by
  simp [Triangle.carrier]

/-- U2: a triangle is triangulated by itself. -/
theorem U2_triangulation_triangle (T : Triangle) : Nonempty (Triangulation T.carrier) := by
  refine ⟨{ faces := {T}, finite := finite_singleton T, cover := by simp, inter := ?_ }⟩
  intro T₁ h₁ T₂ h₂
  rw [mem_singleton_iff] at h₁ h₂; subst h₁; subst h₂; exact u2h_carrier_inter_self _

/-! U2 helper toolbox: `det` algebra, barycentric coordinates, interior criteria. -/
theorem u2h_det_def (u v : Plane) : det u v = u.1 * v.2 - u.2 * v.1 := rfl

/-- cyclic positivity of a triangle -/
theorem u2h_pos_cyc (T : Triangle) (j : Fin 3) :
    0 < det (T.v (j + 1) - T.v j) (T.v (j + 2) - T.v j) := by
  have h := T.pos
  fin_cases j <;> simp only [u2h_det_def, Prod.fst_sub, Prod.snd_sub] at h ⊢ <;>
    simp [Fin.isValue] <;> nlinarith [h]

/-- cyclic membership criterion -/
theorem u2h_mem_iff (T : Triangle) (x : Plane) :
    x ∈ T.carrier ↔ ∀ j : Fin 3, 0 ≤ det (T.v (j + 1) - T.v j) (x - T.v j) := by
  rw [U1_mem_carrier_iff_det]
  constructor
  · rintro ⟨h0, h1, h2⟩ j
    fin_cases j <;> simpa
  · intro h
    exact ⟨h 0, h 1, by simpa using h 2⟩

theorem u2h_range_v (T : Triangle) : range T.v = {T.v 0, T.v 1, T.v 2} := by
  ext x; simp only [mem_range, mem_insert_iff, mem_singleton_iff]
  constructor
  · rintro ⟨j, rfl⟩; fin_cases j <;> simp
  · rintro (rfl | rfl | rfl) <;> exact ⟨_, rfl⟩

theorem u2h_range_vec (a b c : Plane) : range ![a, b, c] = {a, b, c} := by
  ext x; simp only [mem_range, mem_insert_iff, mem_singleton_iff]
  constructor
  · rintro ⟨j, rfl⟩; fin_cases j <;> simp
  · rintro (rfl | rfl | rfl)
    exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩]

theorem u2h_v_ne (T : Triangle) {i j : Fin 3} (h : i ≠ j) : T.v i ≠ T.v j := by
  intro heq
  have hp := T.pos
  fin_cases i <;> fin_cases j <;> simp at h <;>
    simp only [Fin.isValue, u2h_det_def, Prod.fst_sub, Prod.snd_sub] at hp <;>
    simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, Fin.reduceFinMk] at heq <;>
    rw [heq] at hp <;> linarith [hp]

/-- the affine functional `det a (· - q)` on a convex combination -/
theorem u2h_det_affine (a q : Plane) (μ0 μ1 μ2 : ℝ) (u0 u1 u2 : Plane)
    (h1 : μ0 + μ1 + μ2 = 1) :
    det a (μ0 • u0 + μ1 • u1 + μ2 • u2 - q) =
      μ0 * det a (u0 - q) + μ1 * det a (u1 - q) + μ2 * det a (u2 - q) := by
  simp only [u2h_det_def, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
    Prod.smul_snd, smul_eq_mul]
  have : μ2 = 1 - μ0 - μ1 := by linarith
  rw [this]; ring

/-- barycentric coordinates from the `det` criterion -/
theorem u2h_bary (T : Triangle) {x : Plane} (hx : x ∈ T.carrier) :
    ∃ μ0 μ1 μ2 : ℝ, 0 ≤ μ0 ∧ 0 ≤ μ1 ∧ 0 ≤ μ2 ∧ μ0 + μ1 + μ2 = 1 ∧
      x = μ0 • T.v 0 + μ1 • T.v 1 + μ2 • T.v 2 := by
  obtain ⟨h0, h1, h2⟩ := (U1_mem_carrier_iff_det T x).mp hx
  have hD := T.pos
  set D := det (T.v 1 - T.v 0) (T.v 2 - T.v 0) with hDdef
  have hD' : D ≠ 0 := hD.ne'
  refine ⟨det (T.v 2 - T.v 1) (x - T.v 1) / D, det (T.v 0 - T.v 2) (x - T.v 2) / D,
    det (T.v 1 - T.v 0) (x - T.v 0) / D, by positivity, by positivity, by positivity, ?_, ?_⟩
  · rw [← add_div, ← add_div, div_eq_one_iff_eq hD']
    simp only [hDdef, u2h_det_def, Prod.fst_sub, Prod.snd_sub]; ring
  · ext <;> simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;>
      field_simp <;> simp only [hDdef, u2h_det_def, Prod.fst_sub, Prod.snd_sub] <;> ring

theorem u2h_mem_of_bary (T : Triangle) {μ0 μ1 μ2 : ℝ} (h0 : 0 ≤ μ0) (h1 : 0 ≤ μ1) (h2 : 0 ≤ μ2)
    (hs : μ0 + μ1 + μ2 = 1) : μ0 • T.v 0 + μ1 • T.v 1 + μ2 • T.v 2 ∈ T.carrier := by
  have hc := U1_triangle_convex T
  have hv : ∀ k, T.v k ∈ T.carrier := fun k => subset_convexHull ℝ _ (mem_range_self k)
  have := hc.sum_mem (t := Finset.univ) (w := ![μ0, μ1, μ2]) (z := T.v)
    (fun i _ => by fin_cases i <;> simpa) (by simp [Fin.sum_univ_three]; linarith)
    (fun i _ => hv i)
  simpa [Fin.sum_univ_three] using this

/-- the strict half-plane is open -/
theorem u2h_isOpen_det_pos (a q : Plane) : IsOpen {x : Plane | 0 < det a (x - q)} := by
  have : Continuous fun x : Plane => det a (x - q) := by unfold det; fun_prop
  exact isOpen_lt continuous_const this

theorem u2h_isClosed_det_nonneg (a q : Plane) : IsClosed {x : Plane | 0 ≤ det a (x - q)} := by
  have : Continuous fun x : Plane => det a (x - q) := by unfold det; fun_prop
  exact isClosed_le continuous_const this

/-- strict `det` conditions give an interior point -/
theorem u2h_mem_interior_of_det_pos (T : Triangle) {o : Plane}
    (h : ∀ j : Fin 3, 0 < det (T.v (j + 1) - T.v j) (o - T.v j)) : o ∈ interior T.carrier := by
  have hopen : IsOpen {x : Plane | ∀ j : Fin 3, 0 < det (T.v (j + 1) - T.v j) (x - T.v j)} := by
    rw [ofPred_forall]; exact isOpen_iInter_of_finite fun j => u2h_isOpen_det_pos _ _
  apply interior_mono (s := {x : Plane | ∀ j : Fin 3, 0 < det (T.v (j + 1) - T.v j) (x - T.v j)})
  · intro x hx; exact (u2h_mem_iff T x).mpr fun j => (hx j).le
  · rw [hopen.interior_eq]; exact h

/-- an interior point satisfies the strict `det` conditions -/
theorem u2h_det_pos_of_mem_interior (T : Triangle) {o : Plane} (ho : o ∈ interior T.carrier)
    (j : Fin 3) : 0 < det (T.v (j + 1) - T.v j) (o - T.v j) := by
  have hmem : o ∈ T.carrier := interior_subset ho
  have h0 := (u2h_mem_iff T o).mp hmem j
  rcases h0.lt_or_eq with hlt | heq
  · exact hlt
  exfalso
  set a := T.v (j + 1) - T.v j with ha
  have hane : a ≠ 0 := sub_ne_zero.mpr (u2h_v_ne T (by simp))
  set w : Plane := (-a.2, a.1) with hw
  have hdw : 0 < det a w := by
    simp only [u2h_det_def, hw]
    have : a.1 ≠ 0 ∨ a.2 ≠ 0 := by
      by_contra hc; push Not at hc; exact hane (Prod.ext hc.1 hc.2)
    rcases this with h | h <;> nlinarith [sq_pos_of_ne_zero h, sq_nonneg a.1, sq_nonneg a.2]
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp ho)
  set t : ℝ := ε / (2 * (‖w‖ + 1)) with ht
  have htpos : 0 < t := by positivity
  have hmem' : o - t • w ∈ Metric.ball o ε := by
    rw [Metric.mem_ball, dist_eq_norm, sub_sub_cancel_left, norm_neg, norm_smul,
      Real.norm_eq_abs, abs_of_pos htpos, ht]
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith [norm_nonneg w]
  have hin := (u2h_mem_iff T _).mp (hball hmem') j
  have hlin : det a (o - t • w - T.v j) = det a (o - T.v j) - t * det a w := by
    simp only [u2h_det_def, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    ring
  rw [← ha, hlin, ← heq] at hin
  nlinarith [mul_pos htpos hdw]

/-- the two triangles of the square -/
def u2h_sqT1 {L : ℝ} (hL : 0 < L) : Triangle :=
  ⟨![((-L, -L) : Plane), (L, -L), (L, L)], by
    simp [u2h_det_def]
    nlinarith⟩

def u2h_sqT2 {L : ℝ} (hL : 0 < L) : Triangle :=
  ⟨![((-L, -L) : Plane), (L, L), (-L, L)], by
    simp [u2h_det_def]
    nlinarith⟩

theorem u2h_mem_sqT1 {L : ℝ} (hL : 0 < L) (x : Plane) :
    x ∈ (u2h_sqT1 hL).carrier ↔ -L ≤ x.2 ∧ x.1 ≤ L ∧ x.2 ≤ x.1 := by
  rw [U1_mem_carrier_iff_det]
  simp [u2h_sqT1, u2h_det_def]
  constructor
  · rintro ⟨h0, h1, h2⟩
    refine ⟨?_, ?_, ?_⟩ <;> nlinarith
  · rintro ⟨h0, h1, h2⟩
    refine ⟨?_, ?_, ?_⟩ <;> nlinarith

theorem u2h_mem_sqT2 {L : ℝ} (hL : 0 < L) (x : Plane) :
    x ∈ (u2h_sqT2 hL).carrier ↔ x.1 ≤ x.2 ∧ x.2 ≤ L ∧ -L ≤ x.1 := by
  rw [U1_mem_carrier_iff_det]
  simp [u2h_sqT2, u2h_det_def]
  constructor
  · rintro ⟨h0, h1, h2⟩
    refine ⟨?_, ?_, ?_⟩ <;> nlinarith
  · rintro ⟨h0, h1, h2⟩
    refine ⟨?_, ?_, ?_⟩ <;> nlinarith

theorem u2h_mem_square {L : ℝ} (x : Plane) :
    x ∈ square L ↔ -L ≤ x.1 ∧ x.1 ≤ L ∧ -L ≤ x.2 ∧ x.2 ≤ L := by
  simp only [square, supNorm, mem_setOf_eq, max_le_iff, abs_le]
  tauto

theorem u2h_sq_inter {L : ℝ} (hL : 0 < L) :
    (u2h_sqT1 hL).carrier ∩ (u2h_sqT2 hL).carrier =
      convexHull ℝ (range (u2h_sqT1 hL).v ∩ range (u2h_sqT2 hL).v) := by
  have hr : range (u2h_sqT1 hL).v ∩ range (u2h_sqT2 hL).v = {((-L, -L) : Plane), (L, L)} := by
    simp only [u2h_sqT1, u2h_sqT2, u2h_range_vec]
    ext ⟨a, b⟩
    simp only [mem_inter_iff, mem_insert_iff, mem_singleton_iff, Prod.mk.injEq]
    constructor
    · rintro ⟨h1 | h1 | h1, h2 | h2 | h2⟩ <;> first | (left; exact h1) | (right; exact h1) |
        (exfalso; obtain ⟨rfl, rfl⟩ := h1; linarith [h2.1, h2.2])
    · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> simp
  rw [hr, convexHull_pair]
  ext x
  rw [mem_inter_iff, u2h_mem_sqT1, u2h_mem_sqT2, segment_eq_image]
  constructor
  · rintro ⟨⟨h1, h2, h3⟩, ⟨h4, h5, h6⟩⟩
    have hx : x.2 = x.1 := le_antisymm h3 h4
    refine ⟨(x.1 + L) / (2 * L), ⟨div_nonneg (by linarith) (by positivity), ?_⟩, ?_⟩
    · rw [div_le_one (by positivity)]; linarith
    · ext <;> simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;>
        field_simp <;> ring_nf <;> linarith
  · rintro ⟨θ, ⟨h0, h1⟩, rfl⟩
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩ <;> nlinarith

/-- U2 (sm-3:440 "triangulate the rectangle"): the square `Q_L` has a triangulation. -/
theorem U2_triangulation_square {L : ℝ} (hL : 0 < L) : Nonempty (Triangulation (square L)) := by
  refine ⟨{ faces := {u2h_sqT1 hL, u2h_sqT2 hL}, finite := toFinite _, cover := ?_, inter := ?_ }⟩
  · ext x
    simp only [mem_iUnion, mem_insert_iff, mem_singleton_iff, exists_prop, exists_eq_or_imp,
      exists_eq_left, u2h_mem_sqT1, u2h_mem_sqT2, u2h_mem_square]
    constructor
    · rintro (⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩) <;> refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith
    · rintro ⟨h1, h2, h3, h4⟩
      rcases le_total x.2 x.1 with h | h
      · left; exact ⟨h3, h2, h⟩
      · right; exact ⟨h, h4, h1⟩
  · intro T hT T' hT'
    simp only [mem_insert_iff, mem_singleton_iff] at hT hT'
    rcases hT with rfl | rfl <;> rcases hT' with rfl | rfl
    · exact u2h_carrier_inter_self _
    · exact u2h_sq_inter hL
    · rw [inter_comm, u2h_sq_inter hL, inter_comm]
    · exact u2h_carrier_inter_self _

/-- U2: a refinement carries positive PL maps (positivity is inherited by sub-triangles). -/
theorem U2_isPositivePLOn_of_refines {X : Set Plane} {K K' : Triangulation X} {f : Plane → Plane}
    (hf : IsPositivePLOn f K) (h : K'.Refines K) : IsPositivePLOn f K' := by
  intro T' hT'
  obtain ⟨T, hT, hsub⟩ := h T' hT'
  exact U1_isPositiveAffineOn_mono (hf T hT) hsub

/-! U2 helper toolbox, part 2: `Fin 3` arithmetic, face lemmas of a triangle (A, B, D, E1, F1-F3),
the sub-triangle `inter` lemma, and the fan triangles. -/
theorem u2h_fin3_cases (i m : Fin 3) : m = i ∨ m = i + 1 ∨ m = i + 2 := by
  revert i m; decide

theorem u2h_fin3_add_one_two (i : Fin 3) : i + 1 + 2 = i := by revert i; decide
theorem u2h_fin3_add_two_one (i : Fin 3) : i + 2 + 1 = i := by revert i; decide
theorem u2h_fin3_add_one_one (i : Fin 3) : i + 1 + 1 = i + 2 := by revert i; decide
theorem u2h_fin3_add_two_two (i : Fin 3) : i + 2 + 2 = i + 1 := by revert i; decide

/-- E1: a segment point lies on the line of the segment. -/
theorem u2h_det_eq_zero_of_mem_segment {p q x : Plane} (hx : x ∈ segment ℝ p q) :
    det (q - p) (x - p) = 0 := by
  rw [segment_eq_image] at hx
  obtain ⟨θ, _, rfl⟩ := hx
  simp only [u2h_det_def, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
    Prod.smul_snd, smul_eq_mul]
  ring

/-- the injectivity of the vertex map -/
theorem u2h_v_injective (T : Triangle) : Function.Injective T.v := fun i j h => by
  by_contra hne; exact u2h_v_ne T hne h

/-- D: a triangle whose vertices all belong to another has the same carrier. -/
theorem u2h_carrier_eq_of_range_subset {T T' : Triangle} (h : range T.v ⊆ range T'.v) :
    T.carrier = T'.carrier := by
  have heq : range T.v = range T'.v := by
    apply eq_of_subset_of_ncard_le h _ (finite_range _)
    rw [ncard_range_of_injective (u2h_v_injective T'), ncard_range_of_injective (u2h_v_injective T)]
  simp only [Triangle.carrier, heq]

theorem u2h_exists_vertex_notMem {T T' : Triangle} (h : T'.carrier ≠ T.carrier) :
    ∃ k, T.v k ∉ range T'.v := by
  by_contra hc
  push Not at hc
  exact h (u2h_carrier_eq_of_range_subset (range_subset_iff.mpr hc)).symm

/-- B: a set of vertices missing `T.v k` spans within the opposite edge. -/
theorem u2h_subset_edge_of_notMem {T : Triangle} {S : Set Plane} (hS : S ⊆ range T.v) {k : Fin 3}
    (hk : T.v k ∉ S) : S ⊆ {T.v (k + 1), T.v (k + 2)} := by
  intro y hy
  obtain ⟨m, rfl⟩ := hS hy
  rcases u2h_fin3_cases k m with rfl | rfl | rfl
  · exact absurd hy hk
  · exact mem_insert _ _
  · exact mem_insert_of_mem _ (mem_singleton _)

theorem u2h_convexHull_subset_edge_of_notMem {T : Triangle} {S : Set Plane} (hS : S ⊆ range T.v)
    {k : Fin 3} (hk : T.v k ∉ S) : convexHull ℝ S ⊆ segment ℝ (T.v (k + 1)) (T.v (k + 2)) := by
  rw [← convexHull_pair]
  exact convexHull_mono (u2h_subset_edge_of_notMem hS hk)

/-- A: a vertex of `T` in the hull of some vertices of `T` is one of them. -/
theorem u2h_vertex_mem_of_mem_convexHull {T : Triangle} {S : Set Plane} (hS : S ⊆ range T.v)
    {k : Fin 3} (hk : T.v k ∈ convexHull ℝ S) : T.v k ∈ S := by
  by_contra hc
  have h1 := u2h_det_eq_zero_of_mem_segment (u2h_convexHull_subset_edge_of_notMem hS hc hk)
  have h2 := u2h_pos_cyc T (k + 1)
  rw [u2h_fin3_add_one_one, u2h_fin3_add_one_two] at h2
  linarith

/-- F3: a `det` functional nonpositive at the vertices is nonpositive on the triangle. -/
theorem u2h_det_nonpos_on_carrier (U : Triangle) (a q : Plane)
    (h : ∀ k, det a (U.v k - q) ≤ 0) {x : Plane} (hx : x ∈ U.carrier) : det a (x - q) ≤ 0 := by
  obtain ⟨μ0, μ1, μ2, h0, h1, h2, hs, rfl⟩ := u2h_bary U hx
  rw [u2h_det_affine _ _ _ _ _ _ _ _ hs]
  nlinarith [h 0, h 1, h 2, mul_nonneg h0 (neg_nonneg.mpr (h 0)),
    mul_nonneg h1 (neg_nonneg.mpr (h 1)), mul_nonneg h2 (neg_nonneg.mpr (h 2))]

theorem u2h_det_nonneg_on_carrier (U : Triangle) (a q : Plane)
    (h : ∀ k, 0 ≤ det a (U.v k - q)) {x : Plane} (hx : x ∈ U.carrier) : 0 ≤ det a (x - q) := by
  obtain ⟨μ0, μ1, μ2, h0, h1, h2, hs, rfl⟩ := u2h_bary U hx
  rw [u2h_det_affine _ _ _ _ _ _ _ _ hs]
  nlinarith [h 0, h 1, h 2, mul_nonneg h0 (h 0), mul_nonneg h1 (h 1), mul_nonneg h2 (h 2)]

/-- F1: a functional vanishing at one vertex and positive at the other two vanishes on the
triangle only at that vertex. -/
theorem u2h_eq_vertex_of_det_eq_zero (U : Triangle) (a q : Plane) (m : Fin 3)
    (h0 : det a (U.v m - q) = 0) (h1 : 0 < det a (U.v (m + 1) - q)) (h2 : 0 < det a (U.v (m + 2) - q))
    {x : Plane} (hx : x ∈ U.carrier) (hxz : det a (x - q) = 0) : x = U.v m := by
  obtain ⟨μ0, μ1, μ2, hμ0, hμ1, hμ2, hs, rfl⟩ := u2h_bary U hx
  rw [u2h_det_affine _ _ _ _ _ _ _ _ hs] at hxz
  fin_cases m <;> simp only [Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] at h0 h1 h2 <;>
    simp only [Fin.isValue, zero_add, Fin.reduceAdd] at h1 h2 ⊢
  · have hb : μ1 = 0 := by nlinarith [mul_nonneg hμ1 h1.le, mul_nonneg hμ2 h2.le]
    have hc : μ2 = 0 := by nlinarith [mul_nonneg hμ1 h1.le, mul_nonneg hμ2 h2.le]
    have ha : μ0 = 1 := by linarith
    simp [ha, hb, hc]
  · have hb : μ2 = 0 := by nlinarith [mul_nonneg hμ2 h1.le, mul_nonneg hμ0 h2.le]
    have hc : μ0 = 0 := by nlinarith [mul_nonneg hμ2 h1.le, mul_nonneg hμ0 h2.le]
    have ha : μ1 = 1 := by linarith
    simp [ha, hb, hc]
  · have hb : μ0 = 0 := by nlinarith [mul_nonneg hμ0 h1.le, mul_nonneg hμ1 h2.le]
    have hc : μ1 = 0 := by nlinarith [mul_nonneg hμ0 h1.le, mul_nonneg hμ1 h2.le]
    have ha : μ2 = 1 := by linarith
    simp [ha, hb, hc]

/-- F2: a functional vanishing at two vertices and positive at the third vanishes on the
triangle exactly on the edge between them. -/
theorem u2h_mem_segment_of_det_eq_zero (U : Triangle) (a q : Plane) (m : Fin 3)
    (h0 : det a (U.v m - q) = 0) (h1 : det a (U.v (m + 1) - q) = 0) (h2 : 0 < det a (U.v (m + 2) - q))
    {x : Plane} (hx : x ∈ U.carrier) (hxz : det a (x - q) = 0) :
    x ∈ segment ℝ (U.v m) (U.v (m + 1)) := by
  obtain ⟨μ0, μ1, μ2, hμ0, hμ1, hμ2, hs, rfl⟩ := u2h_bary U hx
  rw [u2h_det_affine _ _ _ _ _ _ _ _ hs] at hxz
  fin_cases m <;> simp only [Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] at h0 h1 h2 <;>
    simp only [Fin.isValue, zero_add, Fin.reduceAdd] at h1 h2 ⊢
  · have hc : μ2 = 0 := by nlinarith [mul_nonneg hμ2 h2.le]
    refine ⟨μ0, μ1, hμ0, hμ1, by linarith, ?_⟩
    simp [hc]
  · have hc : μ0 = 0 := by nlinarith [mul_nonneg hμ0 h2.le]
    refine ⟨μ1, μ2, hμ1, hμ2, by linarith, ?_⟩
    simp [hc]
  · have hc : μ1 = 0 := by nlinarith [mul_nonneg hμ1 h2.le]
    refine ⟨μ2, μ0, hμ2, hμ0, by linarith, ?_⟩
    simp [hc]; abel

/-- the vertices of a triangle lie in its carrier -/
theorem u2h_v_mem (U : Triangle) (k : Fin 3) : U.v k ∈ U.carrier :=
  subset_convexHull ℝ _ (mem_range_self k)

/-- the `inter` clause for a sub-triangle `U ⊆ T` against a face `T''` meeting `T` in a common face:
`U`'s vertices inside `T''` are vertices of `T`, and `U` meets any edge of `T` it does not span only
in its own vertices. -/
theorem u2h_inter_sub {T U T'' : Triangle} (hUT : U.carrier ⊆ T.carrier)
    (hne : T''.carrier ≠ T.carrier)
    (hTT'' : T.carrier ∩ T''.carrier = convexHull ℝ (range T.v ∩ range T''.v))
    (hi : ∀ y ∈ range U.v, y ∈ T''.carrier → y ∈ range T.v)
    (hii : ∀ m : Fin 3, ¬ ({T.v (m + 1), T.v (m + 2)} ⊆ range U.v) →
      U.carrier ∩ segment ℝ (T.v (m + 1)) (T.v (m + 2)) ⊆ range U.v) :
    U.carrier ∩ T''.carrier = convexHull ℝ (range U.v ∩ range T''.v) := by
  apply Subset.antisymm
  · intro x ⟨hxU, hxT''⟩
    have hxS : x ∈ convexHull ℝ (range T.v ∩ range T''.v) := hTT'' ▸ ⟨hUT hxU, hxT''⟩
    obtain ⟨m, hm⟩ := u2h_exists_vertex_notMem hne
    have hmS : T.v m ∉ range T.v ∩ range T''.v := fun h => hm h.2
    by_cases hsp : {T.v (m + 1), T.v (m + 2)} ⊆ range U.v
    · apply convexHull_mono _ hxS
      intro y ⟨hy1, hy2⟩
      exact ⟨hsp (u2h_subset_edge_of_notMem inter_subset_left hmS ⟨hy1, hy2⟩), hy2⟩
    · have hseg := u2h_convexHull_subset_edge_of_notMem inter_subset_left hmS hxS
      have hxV : x ∈ range U.v := hii m hsp ⟨hxU, hseg⟩
      obtain ⟨k, hk⟩ := hi x hxV hxT''
      have : T.v k ∈ range T.v ∩ range T''.v :=
        u2h_vertex_mem_of_mem_convexHull inter_subset_left (hk ▸ hxS)
      exact subset_convexHull ℝ _ ⟨hxV, hk ▸ this.2⟩
  · apply convexHull_min
    · intro y ⟨hy1, hy2⟩
      obtain ⟨k, rfl⟩ := hy1
      obtain ⟨k', hk'⟩ := hy2
      exact ⟨u2h_v_mem U k, hk' ▸ u2h_v_mem T'' k'⟩
    · exact (U1_triangle_convex U).inter (U1_triangle_convex T'')

theorem u2h_det_sub_sub (a b c : Plane) : det (a - c) (b - c) = det (b - a) (c - a) := by
  simp only [u2h_det_def, Prod.fst_sub, Prod.snd_sub]; ring

@[simp] theorem u2h_det_self (a : Plane) : det a a = 0 := by simp only [u2h_det_def]; ring
@[simp] theorem u2h_det_zero_right (a : Plane) : det a 0 = 0 := by simp [u2h_det_def]
@[simp] theorem u2h_det_zero_left (a : Plane) : det 0 a = 0 := by simp [u2h_det_def]

theorem u2h_det_swap' (u v : Plane) : det v u = -det u v := by
  simp only [u2h_det_def]; ring

theorem u2h_det_sub_swap (a b x : Plane) : det (a - b) (x - b) = -det (b - a) (x - a) := by
  simp only [u2h_det_def, Prod.fst_sub, Prod.snd_sub]; ring

/-- the fan triangle `(T.v i, T.v (i+1), o)` from an interior point `o` -/
def u2h_fanT (T : Triangle) {o : Plane} (ho : o ∈ interior T.carrier) (i : Fin 3) : Triangle :=
  ⟨![T.v i, T.v (i + 1), o], by simpa using u2h_det_pos_of_mem_interior T ho i⟩

theorem u2h_fanT_v (T : Triangle) {o : Plane} (ho : o ∈ interior T.carrier) (i : Fin 3) :
    (u2h_fanT T ho i).v 0 = T.v i ∧ (u2h_fanT T ho i).v 1 = T.v (i + 1) ∧
      (u2h_fanT T ho i).v 2 = o := by
  simp [u2h_fanT]

theorem u2h_fanT_range (T : Triangle) {o : Plane} (ho : o ∈ interior T.carrier) (i : Fin 3) :
    range (u2h_fanT T ho i).v = {T.v i, T.v (i + 1), o} :=
  u2h_range_vec _ _ _

theorem u2h_fanT_carrier (T : Triangle) {o : Plane} (ho : o ∈ interior T.carrier) (i : Fin 3) :
    (u2h_fanT T ho i).carrier = convexHull ℝ {o, T.v i, T.v (i + 1)} := by
  rw [Triangle.carrier, u2h_fanT_range, Set.pair_comm (T.v (i + 1)) o, Set.insert_comm (T.v i) o]

theorem u2h_fanT_subset (T : Triangle) {o : Plane} (ho : o ∈ interior T.carrier) (i : Fin 3) :
    (u2h_fanT T ho i).carrier ⊆ T.carrier := by
  rw [Triangle.carrier, u2h_fanT_range]
  apply convexHull_min _ (U1_triangle_convex T)
  intro y hy
  simp only [mem_insert_iff, mem_singleton_iff] at hy
  rcases hy with rfl | rfl | rfl
  · exact u2h_v_mem T i
  · exact u2h_v_mem T (i + 1)
  · exact interior_subset ho

theorem u2h_mem_fanT (T : Triangle) {o : Plane} (ho : o ∈ interior T.carrier) (i : Fin 3)
    (x : Plane) : x ∈ (u2h_fanT T ho i).carrier ↔
      0 ≤ det (T.v (i + 1) - T.v i) (x - T.v i) ∧ 0 ≤ det (o - T.v (i + 1)) (x - T.v (i + 1)) ∧
        0 ≤ det (T.v i - o) (x - o) := by
  rw [U1_mem_carrier_iff_det]; simp [u2h_fanT]

theorem u2h_o_ne_v (T : Triangle) {o : Plane} (ho : o ∈ interior T.carrier) (k : Fin 3) :
    o ≠ T.v k := by
  intro h
  have := u2h_det_pos_of_mem_interior T ho k
  rw [h, sub_self] at this
  simp [u2h_det_def] at this

theorem u2h_o_notMem_edge (T : Triangle) {o : Plane} (ho : o ∈ interior T.carrier) (k : Fin 3) :
    o ∉ segment ℝ (T.v (k + 1)) (T.v (k + 2)) := by
  intro h
  have h1 := u2h_det_eq_zero_of_mem_segment h
  have h2 := u2h_det_pos_of_mem_interior T ho (k + 1)
  rw [u2h_fin3_add_one_one] at h2
  linarith

/-- the fan covers the triangle -/
theorem u2h_fan_cover (T : Triangle) {o : Plane} (ho : o ∈ interior T.carrier) {x : Plane}
    (hx : x ∈ T.carrier) : ∃ i, x ∈ (u2h_fanT T ho i).carrier := by
  have hl := (u2h_mem_iff T x).mp hx
  have hc : ∀ i, 0 < det (T.v i - o) (T.v (i + 1) - o) := fun i => by
    rw [u2h_det_sub_sub]; exact u2h_det_pos_of_mem_interior T ho i
  have key : det (T.v 0 - o) (T.v 1 - o) * det (T.v 2 - o) (x - o) +
      det (T.v 2 - o) (T.v 0 - o) * det (T.v 1 - o) (x - o) +
      det (T.v 1 - o) (T.v 2 - o) * det (T.v 0 - o) (x - o) = 0 := by
    simp only [u2h_det_def, Prod.fst_sub, Prod.snd_sub]; ring
  have c01 := hc 0
  have c12 := hc 1
  have c20 := hc 2
  simp only [Fin.isValue, zero_add, Fin.reduceAdd] at c01 c12 c20
  simp only [u2h_mem_fanT, u2h_det_sub_swap o]
  have l0 := hl 0
  have l1 := hl 1
  have l2 := hl 2
  simp only [Fin.isValue, zero_add, Fin.reduceAdd] at l0 l1 l2
  by_cases h0 : 0 ≤ det (T.v 0 - o) (x - o) ∧ det (T.v 1 - o) (x - o) ≤ 0
  · exact ⟨0, by simpa using l0, by simpa using h0.2, by simpa using h0.1⟩
  by_cases h1 : 0 ≤ det (T.v 1 - o) (x - o) ∧ det (T.v 2 - o) (x - o) ≤ 0
  · exact ⟨1, by simpa using l1, by simpa using h1.2, by simpa using h1.1⟩
  by_cases h2 : 0 ≤ det (T.v 2 - o) (x - o) ∧ det (T.v 0 - o) (x - o) ≤ 0
  · exact ⟨2, by simpa using l2, by simpa using h2.2, by simpa using h2.1⟩
  exfalso
  rw [not_and_or, not_le, not_le] at h0 h1 h2
  rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;>
    nlinarith [key, c01, c12, c20]

theorem u2h_fanT_mem_v (T : Triangle) {o : Plane} (ho : o ∈ interior T.carrier) (i : Fin 3) :
    T.v i ∈ (u2h_fanT T ho i).carrier ∧ T.v (i + 1) ∈ (u2h_fanT T ho i).carrier ∧
      o ∈ (u2h_fanT T ho i).carrier := by
  refine ⟨?_, ?_, ?_⟩
  · simpa [u2h_fanT] using u2h_v_mem (u2h_fanT T ho i) 0
  · simpa [u2h_fanT] using u2h_v_mem (u2h_fanT T ho i) 1
  · simpa [u2h_fanT] using u2h_v_mem (u2h_fanT T ho i) 2

/-- two consecutive fan triangles meet in the common spoke -/
theorem u2h_fan_inter_succ (T : Triangle) {o : Plane} (ho : o ∈ interior T.carrier) (i : Fin 3) :
    (u2h_fanT T ho i).carrier ∩ (u2h_fanT T ho (i + 1)).carrier =
      convexHull ℝ (range (u2h_fanT T ho i).v ∩ range (u2h_fanT T ho (i + 1)).v) := by
  have hc : ∀ i, 0 < det (T.v i - o) (T.v (i + 1) - o) := fun i => by
    rw [u2h_det_sub_sub]; exact u2h_det_pos_of_mem_interior T ho i
  have hr : range (u2h_fanT T ho i).v ∩ range (u2h_fanT T ho (i + 1)).v = {T.v (i + 1), o} := by
    rw [u2h_fanT_range, u2h_fanT_range, u2h_fin3_add_one_one]
    ext y
    simp only [mem_inter_iff, mem_insert_iff, mem_singleton_iff]
    constructor
    · rintro ⟨h1 | h1 | h1, h2 | h2 | h2⟩ <;> subst h1
      · exact absurd h2 (u2h_v_ne T (by simp))
      · exact absurd h2 (u2h_v_ne T (by simp))
      · exact absurd h2.symm (u2h_o_ne_v T ho i)
      all_goals simp
    · rintro (rfl | rfl) <;> simp
  rw [hr, convexHull_pair]
  apply Subset.antisymm
  · intro x ⟨hx1, hx2⟩
    have hneg : det (T.v (i + 1) - o) (x - o) ≤ 0 := by
      apply u2h_det_nonpos_on_carrier (u2h_fanT T ho i) _ _ _ hx1
      intro k; fin_cases k <;> simp [u2h_fanT]
      rw [u2h_det_swap']; linarith [hc i]
    have hpos : 0 ≤ det (T.v (i + 1) - o) (x - o) := by
      apply u2h_det_nonneg_on_carrier (u2h_fanT T ho (i + 1)) _ _ _ hx2
      intro k; fin_cases k <;> simp [u2h_fanT]
      exact (hc (i + 1)).le
    have hz : det (T.v (i + 1) - o) (x - o) = 0 := le_antisymm hneg hpos
    have := u2h_mem_segment_of_det_eq_zero (u2h_fanT T ho (i + 1)) (T.v (i + 1) - o) o 2
      (by simp [u2h_fanT]) (by simp [u2h_fanT]) (by simpa [u2h_fanT] using hc (i + 1)) hx2 hz
    rw [segment_symm]; simpa [u2h_fanT] using this
  · exact ((U1_triangle_convex _).inter (U1_triangle_convex _)).segment_subset
      ⟨(u2h_fanT_mem_v T ho i).2.1, (u2h_fanT_mem_v T ho (i + 1)).1⟩
      ⟨(u2h_fanT_mem_v T ho i).2.2, (u2h_fanT_mem_v T ho (i + 1)).2.2⟩

/-- a fan triangle against an old face of different carrier -/
theorem u2h_fan_inter_old (T : Triangle) {o : Plane} (ho : o ∈ interior T.carrier) (i : Fin 3)
    {T'' : Triangle} (hne : T''.carrier ≠ T.carrier)
    (hTT'' : T.carrier ∩ T''.carrier = convexHull ℝ (range T.v ∩ range T''.v)) :
    (u2h_fanT T ho i).carrier ∩ T''.carrier =
      convexHull ℝ (range (u2h_fanT T ho i).v ∩ range T''.v) := by
  have ho'' : o ∉ T''.carrier := by
    intro h
    obtain ⟨m, hm⟩ := u2h_exists_vertex_notMem hne
    have hmS : T.v m ∉ range T.v ∩ range T''.v := fun h' => hm h'.2
    have : o ∈ convexHull ℝ (range T.v ∩ range T''.v) := hTT'' ▸ ⟨interior_subset ho, h⟩
    exact u2h_o_notMem_edge T ho m (u2h_convexHull_subset_edge_of_notMem inter_subset_left hmS this)
  apply u2h_inter_sub (u2h_fanT_subset T ho i) hne hTT''
  · intro y hy hyT''
    rw [u2h_fanT_range] at hy
    rcases hy with rfl | rfl | rfl
    · exact mem_range_self _
    · exact mem_range_self _
    · exact absurd hyT'' ho''
  · intro m hm
    rw [u2h_fanT_range] at hm ⊢
    rcases u2h_fin3_cases i m with rfl | rfl | rfl
    · intro x ⟨hx1, hx2⟩
      have hz := u2h_det_eq_zero_of_mem_segment hx2
      have := u2h_eq_vertex_of_det_eq_zero (u2h_fanT T ho m) (T.v (m + 2) - T.v (m + 1))
        (T.v (m + 1)) 1 (by simp [u2h_fanT]) ?_ ?_ hx1 hz
      · rw [this]; simp [u2h_fanT]
      · have := u2h_det_pos_of_mem_interior T ho (m + 1)
        rw [u2h_fin3_add_one_one] at this
        simpa [u2h_fanT] using this
      · have := u2h_pos_cyc T (m + 1)
        rw [u2h_fin3_add_one_one, u2h_fin3_add_one_two] at this
        simpa [u2h_fanT] using this
    · rw [u2h_fin3_add_one_one, u2h_fin3_add_one_two]
      intro x ⟨hx1, hx2⟩
      have hz := u2h_det_eq_zero_of_mem_segment hx2
      have := u2h_eq_vertex_of_det_eq_zero (u2h_fanT T ho i) (T.v i - T.v (i + 2))
        (T.v (i + 2)) 0 (by simp [u2h_fanT]) ?_ ?_ hx1 hz
      · rw [this]; simp [u2h_fanT]
      · have := u2h_pos_cyc T (i + 2)
        rw [u2h_fin3_add_two_one, u2h_fin3_add_two_two] at this
        simpa [u2h_fanT] using this
      · have := u2h_det_pos_of_mem_interior T ho (i + 2)
        rw [u2h_fin3_add_two_one] at this
        simpa [u2h_fanT] using this
    · exfalso; apply hm
      rw [u2h_fin3_add_two_one, u2h_fin3_add_two_two]
      intro y hy; rcases hy with rfl | rfl <;> simp

/-- U2 (fan refinement): a face may be replaced by its fan from an interior point. -/
theorem U2_refine_fan {X : Set Plane} (K : Triangulation X) {T : Triangle} (hT : T ∈ K.faces)
    {o : Plane} (ho : o ∈ interior T.carrier) :
    ∃ K' : Triangulation X, K'.Refines K ∧
      (∀ T' ∈ K.faces, T'.carrier ≠ T.carrier → T' ∈ K'.faces) ∧
      (∀ i : Fin 3, ∃ T' ∈ K'.faces, T'.carrier = convexHull ℝ {o, T.v i, T.v (i + 1)}) := by
  set F : Set Triangle := {T' ∈ K.faces | T'.carrier ≠ T.carrier} ∪ range (u2h_fanT T ho) with hF
  have hfin : F.Finite := (K.finite.subset (sep_subset _ _)).union (finite_range _)
  have hcover : (⋃ T' ∈ F, T'.carrier) = X := by
    apply Subset.antisymm
    · intro x hx
      obtain ⟨T', hT', hx⟩ := mem_iUnion₂.mp hx
      rcases hT' with ⟨hT'K, _⟩ | ⟨i, rfl⟩
      · exact u2h_carrier_subset K hT'K hx
      · exact u2h_carrier_subset K hT (u2h_fanT_subset T ho i hx)
    · intro x hx
      rw [← K.cover] at hx
      obtain ⟨T', hT', hx⟩ := mem_iUnion₂.mp hx
      by_cases hc : T'.carrier = T.carrier
      · obtain ⟨i, hi⟩ := u2h_fan_cover T ho (hc ▸ hx)
        exact mem_iUnion₂.mpr ⟨_, Or.inr (mem_range_self i), hi⟩
      · exact mem_iUnion₂.mpr ⟨T', Or.inl ⟨hT', hc⟩, hx⟩
  have hinter : ∀ T₁ ∈ F, ∀ T₂ ∈ F,
      T₁.carrier ∩ T₂.carrier = convexHull ℝ (range T₁.v ∩ range T₂.v) := by
    intro T₁ h₁ T₂ h₂
    rcases h₁ with ⟨h₁, hc₁⟩ | ⟨i, rfl⟩ <;> rcases h₂ with ⟨h₂, hc₂⟩ | ⟨j, rfl⟩
    · exact K.inter T₁ h₁ T₂ h₂
    · rw [inter_comm, u2h_fan_inter_old T ho j hc₁ (K.inter T hT T₁ h₁), inter_comm]
    · exact u2h_fan_inter_old T ho i hc₂ (K.inter T hT T₂ h₂)
    · rcases u2h_fin3_cases i j with rfl | rfl | rfl
      · exact u2h_carrier_inter_self _
      · exact u2h_fan_inter_succ T ho i
      · have := u2h_fan_inter_succ T ho (i + 2)
        rw [u2h_fin3_add_two_one] at this
        rw [inter_comm, this, inter_comm]
  refine ⟨⟨F, hfin, hcover, hinter⟩, ?_, ?_, ?_⟩
  · intro T' hT'
    rcases hT' with ⟨h, _⟩ | ⟨i, rfl⟩
    · exact ⟨T', h, subset_rfl⟩
    · exact ⟨T, hT, u2h_fanT_subset T ho i⟩
  · intro T' hT' hne; exact Or.inl ⟨hT', hne⟩
  · intro i; exact ⟨u2h_fanT T ho i, Or.inr (mem_range_self i), u2h_fanT_carrier T ho i⟩

/-! U2 helpers: the edge split. -/
/-- variant of `u2h_inter_sub`: the case analysis on the common face is left to the caller. -/
theorem u2h_inter_sub' {T U T'' : Triangle} (hUT : U.carrier ⊆ T.carrier)
    (hTT'' : T.carrier ∩ T''.carrier = convexHull ℝ (range T.v ∩ range T''.v))
    (hi : ∀ y ∈ range U.v, y ∈ T''.carrier → y ∈ range T.v)
    (hii : ∀ x ∈ U.carrier, x ∈ convexHull ℝ (range T.v ∩ range T''.v) →
      x ∈ range U.v ∨ range T.v ∩ range T''.v ⊆ range U.v) :
    U.carrier ∩ T''.carrier = convexHull ℝ (range U.v ∩ range T''.v) := by
  apply Subset.antisymm
  · intro x ⟨hxU, hxT''⟩
    have hxS : x ∈ convexHull ℝ (range T.v ∩ range T''.v) := hTT'' ▸ ⟨hUT hxU, hxT''⟩
    rcases hii x hxU hxS with hxV | hsp
    · obtain ⟨k, hk⟩ := hi x hxV hxT''
      have : T.v k ∈ range T.v ∩ range T''.v :=
        u2h_vertex_mem_of_mem_convexHull inter_subset_left (hk ▸ hxS)
      exact subset_convexHull ℝ _ ⟨hxV, hk ▸ this.2⟩
    · refine convexHull_mono ?_ hxS
      intro y hy; exact ⟨hsp hy, hy.2⟩
  · apply convexHull_min
    · intro y ⟨hy1, hy2⟩
      obtain ⟨k, rfl⟩ := hy1
      obtain ⟨k', hk'⟩ := hy2
      exact ⟨u2h_v_mem U k, hk' ▸ u2h_v_mem T'' k'⟩
    · exact (U1_triangle_convex U).inter (U1_triangle_convex T'')

/-- the three `det` values of a point of the open edge `i` -/
theorem u2h_openSegment_dets (T : Triangle) (i : Fin 3) {p : Plane}
    (hp : p ∈ openSegment ℝ (T.v i) (T.v (i + 1))) :
    det (T.v (i + 1) - T.v i) (p - T.v i) = 0 ∧
      0 < det (T.v (i + 2) - T.v (i + 1)) (p - T.v (i + 1)) ∧
      0 < det (T.v i - T.v (i + 2)) (p - T.v (i + 2)) := by
  rw [openSegment_eq_image] at hp
  obtain ⟨θ, ⟨hθ0, hθ1⟩, rfl⟩ := hp
  have c1 := u2h_pos_cyc T (i + 1)
  rw [u2h_fin3_add_one_one, u2h_fin3_add_one_two] at c1
  have c2 := u2h_pos_cyc T (i + 2)
  rw [u2h_fin3_add_two_one, u2h_fin3_add_two_two] at c2
  refine ⟨?_, ?_, ?_⟩
  · simp only [u2h_det_def, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
      Prod.smul_snd, smul_eq_mul]; ring
  · have e : det (T.v (i + 2) - T.v (i + 1)) ((1 - θ) • T.v i + θ • T.v (i + 1) - T.v (i + 1)) =
        (1 - θ) * det (T.v (i + 2) - T.v (i + 1)) (T.v i - T.v (i + 1)) := by
      simp only [u2h_det_def, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
        Prod.smul_snd, smul_eq_mul]; ring
    rw [e]; exact mul_pos (by linarith) c1
  · have e : det (T.v i - T.v (i + 2)) ((1 - θ) • T.v i + θ • T.v (i + 1) - T.v (i + 2)) =
        θ * det (T.v i - T.v (i + 2)) (T.v (i + 1) - T.v (i + 2)) := by
      simp only [u2h_det_def, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
        Prod.smul_snd, smul_eq_mul]; ring
    rw [e]; exact mul_pos hθ0 c2

/-- a point of the open edge `i` lies in `T` -/
theorem u2h_openSegment_mem (T : Triangle) (i : Fin 3) {p : Plane}
    (hp : p ∈ openSegment ℝ (T.v i) (T.v (i + 1))) : p ∈ T.carrier :=
  (U1_triangle_convex T).openSegment_subset (u2h_v_mem T i) (u2h_v_mem T (i + 1)) hp

/-- a point of the open edge `i` of `T` in a face `T''` meeting `T` in a common face forces the
whole edge into `T''`. -/
theorem u2h_edge_subset_of_openSegment_mem {T T'' : Triangle}
    (hTT'' : T.carrier ∩ T''.carrier = convexHull ℝ (range T.v ∩ range T''.v)) (i : Fin 3)
    {p : Plane} (hp : p ∈ openSegment ℝ (T.v i) (T.v (i + 1))) (hpT'' : p ∈ T''.carrier) :
    T.edgeSeg i ⊆ T''.carrier := by
  obtain ⟨_, hp2, hp3⟩ := u2h_openSegment_dets T i hp
  have hpS : p ∈ convexHull ℝ (range T.v ∩ range T''.v) :=
    hTT'' ▸ ⟨u2h_openSegment_mem T i hp, hpT''⟩
  have hvi : T.v i ∈ range T.v ∩ range T''.v := by
    by_contra h
    have := u2h_det_eq_zero_of_mem_segment
      (u2h_convexHull_subset_edge_of_notMem inter_subset_left h hpS)
    linarith
  have hvi1 : T.v (i + 1) ∈ range T.v ∩ range T''.v := by
    by_contra h
    have := u2h_det_eq_zero_of_mem_segment
      (u2h_convexHull_subset_edge_of_notMem inter_subset_left h hpS)
    rw [u2h_fin3_add_one_one, u2h_fin3_add_one_two] at this
    linarith
  calc T.edgeSeg i = convexHull ℝ {T.v i, T.v (i + 1)} := (convexHull_pair _ _).symm
    _ ⊆ convexHull ℝ (range T.v ∩ range T''.v) := by
        apply convexHull_mono; intro y hy
        rcases hy with rfl | rfl
        · exact hvi
        · exact hvi1
    _ = T.carrier ∩ T''.carrier := hTT''.symm
    _ ⊆ T''.carrier := inter_subset_right

/-- the two halves of the edge split: `(T.v i, p, T.v (i+2))` and `(p, T.v (i+1), T.v (i+2))` -/
def u2h_spT1 (T : Triangle) (i : Fin 3) {p : Plane} (hp : p ∈ openSegment ℝ (T.v i) (T.v (i + 1))) :
    Triangle :=
  ⟨![T.v i, p, T.v (i + 2)], by
    have h := (u2h_openSegment_dets T i hp).2.2
    have e : det (p - T.v i) (T.v (i + 2) - T.v i) = det (T.v i - T.v (i + 2)) (p - T.v (i + 2)) := by
      simp only [u2h_det_def, Prod.fst_sub, Prod.snd_sub]; ring
    simpa [e] using h⟩

def u2h_spT2 (T : Triangle) (i : Fin 3) {p : Plane} (hp : p ∈ openSegment ℝ (T.v i) (T.v (i + 1))) :
    Triangle :=
  ⟨![p, T.v (i + 1), T.v (i + 2)], by
    have h := (u2h_openSegment_dets T i hp).2.1
    have e : det (T.v (i + 1) - p) (T.v (i + 2) - p) =
        det (T.v (i + 2) - T.v (i + 1)) (p - T.v (i + 1)) := by
      simp only [u2h_det_def, Prod.fst_sub, Prod.snd_sub]; ring
    simpa [e] using h⟩

section split
variable (T : Triangle) (i : Fin 3) {p : Plane} (hp : p ∈ openSegment ℝ (T.v i) (T.v (i + 1)))
include hp

theorem u2h_spT1_range : range (u2h_spT1 T i hp).v = {T.v i, p, T.v (i + 2)} := u2h_range_vec _ _ _
theorem u2h_spT2_range : range (u2h_spT2 T i hp).v = {p, T.v (i + 1), T.v (i + 2)} :=
  u2h_range_vec _ _ _

theorem u2h_spT1_carrier : (u2h_spT1 T i hp).carrier = convexHull ℝ {T.v i, p, T.v (i + 2)} := by
  rw [Triangle.carrier, u2h_spT1_range]
theorem u2h_spT2_carrier : (u2h_spT2 T i hp).carrier = convexHull ℝ {p, T.v (i + 1), T.v (i + 2)} := by
  rw [Triangle.carrier, u2h_spT2_range]

theorem u2h_spT1_subset : (u2h_spT1 T i hp).carrier ⊆ T.carrier := by
  rw [u2h_spT1_carrier]
  apply convexHull_min _ (U1_triangle_convex T)
  intro y hy
  rcases hy with rfl | rfl | rfl
  · exact u2h_v_mem T i
  · exact u2h_openSegment_mem T i hp
  · exact u2h_v_mem T (i + 2)

theorem u2h_spT2_subset : (u2h_spT2 T i hp).carrier ⊆ T.carrier := by
  rw [u2h_spT2_carrier]
  apply convexHull_min _ (U1_triangle_convex T)
  intro y hy
  rcases hy with rfl | rfl | rfl
  · exact u2h_openSegment_mem T i hp
  · exact u2h_v_mem T (i + 1)
  · exact u2h_v_mem T (i + 2)

theorem u2h_mem_spT1 (x : Plane) : x ∈ (u2h_spT1 T i hp).carrier ↔
    0 ≤ det (p - T.v i) (x - T.v i) ∧ 0 ≤ det (T.v (i + 2) - p) (x - p) ∧
      0 ≤ det (T.v i - T.v (i + 2)) (x - T.v (i + 2)) := by
  rw [U1_mem_carrier_iff_det]; simp [u2h_spT1]

theorem u2h_mem_spT2 (x : Plane) : x ∈ (u2h_spT2 T i hp).carrier ↔
    0 ≤ det (T.v (i + 1) - p) (x - p) ∧ 0 ≤ det (T.v (i + 2) - T.v (i + 1)) (x - T.v (i + 1)) ∧
      0 ≤ det (p - T.v (i + 2)) (x - T.v (i + 2)) := by
  rw [U1_mem_carrier_iff_det]; simp [u2h_spT2]

/-- the two halves cover `T` -/
theorem u2h_sp_cover {x : Plane} (hx : x ∈ T.carrier) :
    x ∈ (u2h_spT1 T i hp).carrier ∨ x ∈ (u2h_spT2 T i hp).carrier := by
  have hp' := hp
  rw [openSegment_eq_image] at hp'
  obtain ⟨θ, ⟨hθ0, hθ1⟩, hpθ⟩ := hp'
  have hl := (u2h_mem_iff T x).mp hx
  have l0 := hl i
  have l1 := hl (i + 1)
  have l2 := hl (i + 2)
  rw [u2h_fin3_add_one_one] at l1
  rw [u2h_fin3_add_two_one] at l2
  have e1 : det (p - T.v i) (x - T.v i) = θ * det (T.v (i + 1) - T.v i) (x - T.v i) := by
    rw [← hpθ]
    simp only [u2h_det_def, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
      Prod.smul_snd, smul_eq_mul]; ring
  have e2 : det (T.v (i + 1) - p) (x - p) = (1 - θ) * det (T.v (i + 1) - T.v i) (x - T.v i) := by
    rw [← hpθ]
    simp only [u2h_det_def, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
      Prod.smul_snd, smul_eq_mul]; ring
  have e3 : det (p - T.v (i + 2)) (x - T.v (i + 2)) = -det (T.v (i + 2) - p) (x - p) := by
    simp only [u2h_det_def, Prod.fst_sub, Prod.snd_sub]; ring
  rw [u2h_mem_spT1, u2h_mem_spT2, e1, e2, e3]
  rcases le_total 0 (det (T.v (i + 2) - p) (x - p)) with h | h
  · left; exact ⟨mul_nonneg hθ0.le l0, h, l2⟩
  · right; exact ⟨mul_nonneg (by linarith) l0, l1, by linarith⟩

/-- the splitting functional is `≥ 0` on the first half and `≤ 0` on the second -/
theorem u2h_sp_lam_nonneg {x : Plane} (hx : x ∈ (u2h_spT1 T i hp).carrier) :
    0 ≤ det (T.v (i + 2) - p) (x - p) := ((u2h_mem_spT1 T i hp x).mp hx).2.1

theorem u2h_sp_lam_nonpos {x : Plane} (hx : x ∈ (u2h_spT2 T i hp).carrier) :
    det (T.v (i + 2) - p) (x - p) ≤ 0 := by
  have h := ((u2h_mem_spT2 T i hp x).mp hx).2.2
  have e3 : det (p - T.v (i + 2)) (x - T.v (i + 2)) = -det (T.v (i + 2) - p) (x - p) := by
    simp only [u2h_det_def, Prod.fst_sub, Prod.snd_sub]; ring
  linarith

theorem u2h_sp_lam_vi : 0 < det (T.v (i + 2) - p) (T.v i - p) := by
  have hp' := hp
  rw [openSegment_eq_image] at hp'
  obtain ⟨θ, ⟨hθ0, hθ1⟩, hpθ⟩ := hp'
  have e : det (T.v (i + 2) - p) (T.v i - p) = θ * det (T.v (i + 1) - T.v i) (T.v (i + 2) - T.v i) := by
    rw [← hpθ]
    simp only [u2h_det_def, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
      Prod.smul_snd, smul_eq_mul]; ring
  rw [e]; exact mul_pos hθ0 (u2h_pos_cyc T i)

theorem u2h_sp_lam_vi1 : det (T.v (i + 2) - p) (T.v (i + 1) - p) < 0 := by
  have hp' := hp
  rw [openSegment_eq_image] at hp'
  obtain ⟨θ, ⟨hθ0, hθ1⟩, hpθ⟩ := hp'
  have e : det (T.v (i + 2) - p) (T.v (i + 1) - p) =
      -((1 - θ) * det (T.v (i + 1) - T.v i) (T.v (i + 2) - T.v i)) := by
    rw [← hpθ]
    simp only [u2h_det_def, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
      Prod.smul_snd, smul_eq_mul]; ring
  rw [e, neg_lt_zero]; exact mul_pos (by linarith) (u2h_pos_cyc T i)

theorem u2h_sp_vi1_notMem : T.v (i + 1) ∉ (u2h_spT1 T i hp).carrier := fun h =>
  absurd (u2h_sp_lam_nonneg T i hp h) (not_le.mpr (u2h_sp_lam_vi1 T i hp))

theorem u2h_sp_vi_notMem : T.v i ∉ (u2h_spT2 T i hp).carrier := fun h =>
  absurd (u2h_sp_lam_nonpos T i hp h) (not_le.mpr (u2h_sp_lam_vi T i hp))

theorem u2h_p_ne_v : p ≠ T.v i ∧ p ≠ T.v (i + 1) ∧ p ≠ T.v (i + 2) := by
  obtain ⟨_, hp2, hp3⟩ := u2h_openSegment_dets T i hp
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · rw [h] at hp3; simp at hp3
  · rw [h] at hp2; simp at hp2
  · rw [h] at hp3; simp at hp3

end split

section split2
variable (T : Triangle) (i : Fin 3) {p : Plane} (hp : p ∈ openSegment ℝ (T.v i) (T.v (i + 1)))
include hp

theorem u2h_spT1_mem_v : T.v i ∈ (u2h_spT1 T i hp).carrier ∧ p ∈ (u2h_spT1 T i hp).carrier ∧
    T.v (i + 2) ∈ (u2h_spT1 T i hp).carrier := by
  refine ⟨?_, ?_, ?_⟩
  · simpa [u2h_spT1] using u2h_v_mem (u2h_spT1 T i hp) 0
  · simpa [u2h_spT1] using u2h_v_mem (u2h_spT1 T i hp) 1
  · simpa [u2h_spT1] using u2h_v_mem (u2h_spT1 T i hp) 2

theorem u2h_spT2_mem_v : p ∈ (u2h_spT2 T i hp).carrier ∧ T.v (i + 1) ∈ (u2h_spT2 T i hp).carrier ∧
    T.v (i + 2) ∈ (u2h_spT2 T i hp).carrier := by
  refine ⟨?_, ?_, ?_⟩
  · simpa [u2h_spT2] using u2h_v_mem (u2h_spT2 T i hp) 0
  · simpa [u2h_spT2] using u2h_v_mem (u2h_spT2 T i hp) 1
  · simpa [u2h_spT2] using u2h_v_mem (u2h_spT2 T i hp) 2

/-- the two halves meet in the splitting segment -/
theorem u2h_sp_inter : (u2h_spT1 T i hp).carrier ∩ (u2h_spT2 T i hp).carrier =
    convexHull ℝ (range (u2h_spT1 T i hp).v ∩ range (u2h_spT2 T i hp).v) := by
  obtain ⟨hpi, hpi1, hpi2⟩ := u2h_p_ne_v T i hp
  have hr : range (u2h_spT1 T i hp).v ∩ range (u2h_spT2 T i hp).v = {p, T.v (i + 2)} := by
    rw [u2h_spT1_range, u2h_spT2_range]
    ext y
    simp only [mem_inter_iff, mem_insert_iff, mem_singleton_iff]
    constructor
    · rintro ⟨h1 | h1 | h1, h2 | h2 | h2⟩ <;> subst h1
      · exact absurd h2.symm hpi
      · exact absurd h2 (u2h_v_ne T (by simp))
      · exact absurd h2 (u2h_v_ne T (by simp))
      all_goals simp
    · rintro (rfl | rfl) <;> simp
  rw [hr, convexHull_pair]
  apply Subset.antisymm
  · intro x ⟨hx1, hx2⟩
    have hz : det (T.v (i + 2) - p) (x - p) = 0 :=
      le_antisymm (u2h_sp_lam_nonpos T i hp hx2) (u2h_sp_lam_nonneg T i hp hx1)
    have := u2h_mem_segment_of_det_eq_zero (u2h_spT1 T i hp) (T.v (i + 2) - p) p 1
      (by simp [u2h_spT1]) (by simp [u2h_spT1]) (by simpa [u2h_spT1] using u2h_sp_lam_vi T i hp) hx1 hz
    simpa [u2h_spT1] using this
  · exact ((U1_triangle_convex _).inter (U1_triangle_convex _)).segment_subset
      ⟨(u2h_spT1_mem_v T i hp).2.1, (u2h_spT2_mem_v T i hp).1⟩
      ⟨(u2h_spT1_mem_v T i hp).2.2, (u2h_spT2_mem_v T i hp).2.2⟩

/-- both halves against an old face not containing the split edge -/
theorem u2h_sp_inter_old {T'' : Triangle} (hne : T''.carrier ≠ T.carrier)
    (hTT'' : T.carrier ∩ T''.carrier = convexHull ℝ (range T.v ∩ range T''.v))
    (hnot : ¬ T.edgeSeg i ⊆ T''.carrier) :
    (u2h_spT1 T i hp).carrier ∩ T''.carrier =
        convexHull ℝ (range (u2h_spT1 T i hp).v ∩ range T''.v) ∧
      (u2h_spT2 T i hp).carrier ∩ T''.carrier =
        convexHull ℝ (range (u2h_spT2 T i hp).v ∩ range T''.v) := by
  obtain ⟨_, hp2, hp3⟩ := u2h_openSegment_dets T i hp
  have hpT'' : p ∉ T''.carrier := fun h => hnot (u2h_edge_subset_of_openSegment_mem hTT'' i hp h)
  set S := range T.v ∩ range T''.v with hS
  have hSsub : S ⊆ range T.v := inter_subset_left
  obtain ⟨m, hm⟩ := u2h_exists_vertex_notMem hne
  have hmS : T.v m ∉ S := fun h => hm h.2
  have hboth : ¬ (T.v i ∈ S ∧ T.v (i + 1) ∈ S) := by
    rintro ⟨h1, h2⟩
    apply hnot
    calc T.edgeSeg i = convexHull ℝ {T.v i, T.v (i + 1)} := (convexHull_pair _ _).symm
      _ ⊆ convexHull ℝ S := by
          apply convexHull_mono; intro y hy
          rcases hy with rfl | rfl
          · exact h1
          · exact h2
      _ = T.carrier ∩ T''.carrier := hTT''.symm
      _ ⊆ T''.carrier := inter_subset_right
  have hSedge := u2h_subset_edge_of_notMem hSsub hmS
  have hShull := u2h_convexHull_subset_edge_of_notMem hSsub hmS
  constructor
  · apply u2h_inter_sub' (u2h_spT1_subset T i hp) hTT''
    · intro y hy hyT''
      rw [u2h_spT1_range] at hy
      rcases hy with rfl | rfl | rfl
      · exact mem_range_self _
      · exact absurd hyT'' hpT''
      · exact mem_range_self _
    · intro x hx hxS
      rw [u2h_spT1_range]
      rcases u2h_fin3_cases i m with rfl | rfl | rfl
      · left
        have hz := u2h_det_eq_zero_of_mem_segment (hShull hxS)
        have := u2h_eq_vertex_of_det_eq_zero (u2h_spT1 T m hp) (T.v (m + 2) - T.v (m + 1))
          (T.v (m + 1)) 2 (by simp [u2h_spT1]) ?_ ?_ hx hz
        · rw [this]; simp [u2h_spT1]
        · have := u2h_pos_cyc T (m + 1)
          rw [u2h_fin3_add_one_one, u2h_fin3_add_one_two] at this
          simpa [u2h_spT1] using this
        · simpa [u2h_spT1] using hp2
      · right
        rw [u2h_fin3_add_one_one, u2h_fin3_add_one_two] at hSedge
        intro y hy
        rcases hSedge hy with rfl | rfl <;> simp
      · rw [u2h_fin3_add_two_one, u2h_fin3_add_two_two] at hSedge hShull
        by_cases h1 : T.v (i + 1) ∈ S
        · exfalso
          have h0 : T.v i ∉ S := fun h0 => hboth ⟨h0, h1⟩
          have hS1 : S ⊆ {T.v (i + 1)} := by
            intro y hy
            rcases hSedge hy with rfl | rfl
            · exact absurd hy h0
            · exact mem_singleton _
          have := convexHull_mono hS1 hxS
          rw [convexHull_singleton, mem_singleton_iff] at this
          exact u2h_sp_vi1_notMem T i hp (this ▸ hx)
        · right
          intro y hy
          rcases hSedge hy with rfl | rfl
          · simp
          · exact absurd hy h1
  · apply u2h_inter_sub' (u2h_spT2_subset T i hp) hTT''
    · intro y hy hyT''
      rw [u2h_spT2_range] at hy
      rcases hy with rfl | rfl | rfl
      · exact absurd hyT'' hpT''
      · exact mem_range_self _
      · exact mem_range_self _
    · intro x hx hxS
      rw [u2h_spT2_range]
      rcases u2h_fin3_cases i m with rfl | rfl | rfl
      · right
        intro y hy
        rcases hSedge hy with rfl | rfl <;> simp
      · left
        rw [u2h_fin3_add_one_one, u2h_fin3_add_one_two] at hShull
        have hz := u2h_det_eq_zero_of_mem_segment (hShull hxS)
        have := u2h_eq_vertex_of_det_eq_zero (u2h_spT2 T i hp) (T.v i - T.v (i + 2))
          (T.v (i + 2)) 2 (by simp [u2h_spT2]) ?_ ?_ hx hz
        · rw [this]; simp [u2h_spT2]
        · simpa [u2h_spT2] using hp3
        · have := u2h_pos_cyc T (i + 2)
          rw [u2h_fin3_add_two_one, u2h_fin3_add_two_two] at this
          simpa [u2h_spT2] using this
      · rw [u2h_fin3_add_two_one, u2h_fin3_add_two_two] at hSedge hShull
        by_cases h0 : T.v i ∈ S
        · exfalso
          have h1 : T.v (i + 1) ∉ S := fun h1 => hboth ⟨h0, h1⟩
          have hS0 : S ⊆ {T.v i} := by
            intro y hy
            rcases hSedge hy with rfl | rfl
            · exact mem_singleton _
            · exact absurd hy h1
          have := convexHull_mono hS0 hxS
          rw [convexHull_singleton, mem_singleton_iff] at this
          exact u2h_sp_vi_notMem T i hp (this ▸ hx)
        · right
          intro y hy
          rcases hSedge hy with rfl | rfl
          · exact absurd hy h0
          · simp

end split2

/-- U2 (edge split): an edge lying in exactly one face may be subdivided at an interior point. -/
theorem U2_refine_edge_split {X : Set Plane} (K : Triangulation X) {T : Triangle} (hT : T ∈ K.faces)
    (i : Fin 3) (huniq : ∀ T' ∈ K.faces, T.edgeSeg i ⊆ T'.carrier → T'.carrier = T.carrier)
    {p : Plane} (hp : p ∈ openSegment ℝ (T.v i) (T.v (i + 1))) :
    ∃ K' : Triangulation X, K'.Refines K ∧
      (∀ T' ∈ K.faces, T'.carrier ≠ T.carrier → T' ∈ K'.faces) ∧
      (∃ T₁ ∈ K'.faces, T₁.carrier = convexHull ℝ {T.v i, p, T.v (i + 2)}) ∧
      (∃ T₂ ∈ K'.faces, T₂.carrier = convexHull ℝ {p, T.v (i + 1), T.v (i + 2)}) := by
  set F : Set Triangle := {T' ∈ K.faces | T'.carrier ≠ T.carrier} ∪ {u2h_spT1 T i hp, u2h_spT2 T i hp}
    with hF
  have hfin : F.Finite := (K.finite.subset (sep_subset _ _)).union (toFinite _)
  have hold : ∀ T'' ∈ K.faces, T''.carrier ≠ T.carrier →
      (u2h_spT1 T i hp).carrier ∩ T''.carrier =
          convexHull ℝ (range (u2h_spT1 T i hp).v ∩ range T''.v) ∧
        (u2h_spT2 T i hp).carrier ∩ T''.carrier =
          convexHull ℝ (range (u2h_spT2 T i hp).v ∩ range T''.v) := fun T'' hT'' hne =>
    u2h_sp_inter_old T i hp hne (K.inter T hT T'' hT'') fun h => hne (huniq T'' hT'' h)
  have hcover : (⋃ T' ∈ F, T'.carrier) = X := by
    apply Subset.antisymm
    · intro x hx
      obtain ⟨T', hT', hx⟩ := mem_iUnion₂.mp hx
      rcases hT' with ⟨hT'K, _⟩ | (rfl | rfl)
      · exact u2h_carrier_subset K hT'K hx
      · exact u2h_carrier_subset K hT (u2h_spT1_subset T i hp hx)
      · exact u2h_carrier_subset K hT (u2h_spT2_subset T i hp hx)
    · intro x hx
      rw [← K.cover] at hx
      obtain ⟨T', hT', hx⟩ := mem_iUnion₂.mp hx
      by_cases hc : T'.carrier = T.carrier
      · rcases u2h_sp_cover T i hp (hc ▸ hx) with h | h
        · exact mem_iUnion₂.mpr ⟨_, Or.inr (Or.inl rfl), h⟩
        · exact mem_iUnion₂.mpr ⟨_, Or.inr (Or.inr rfl), h⟩
      · exact mem_iUnion₂.mpr ⟨T', Or.inl ⟨hT', hc⟩, hx⟩
  have hinter : ∀ T₁ ∈ F, ∀ T₂ ∈ F,
      T₁.carrier ∩ T₂.carrier = convexHull ℝ (range T₁.v ∩ range T₂.v) := by
    intro T₁ h₁ T₂ h₂
    rcases h₁ with ⟨h₁, hc₁⟩ | (rfl | rfl) <;> rcases h₂ with ⟨h₂, hc₂⟩ | (rfl | rfl)
    · exact K.inter T₁ h₁ T₂ h₂
    · rw [inter_comm, (hold T₁ h₁ hc₁).1, inter_comm]
    · rw [inter_comm, (hold T₁ h₁ hc₁).2, inter_comm]
    · exact (hold T₂ h₂ hc₂).1
    · exact u2h_carrier_inter_self _
    · exact u2h_sp_inter T i hp
    · exact (hold T₂ h₂ hc₂).2
    · rw [inter_comm, u2h_sp_inter T i hp, inter_comm]
    · exact u2h_carrier_inter_self _
  refine ⟨⟨F, hfin, hcover, hinter⟩, ?_, ?_, ?_, ?_⟩
  · intro T' hT'
    rcases hT' with ⟨h, _⟩ | (rfl | rfl)
    · exact ⟨T', h, subset_rfl⟩
    · exact ⟨T, hT, u2h_spT1_subset T i hp⟩
    · exact ⟨T, hT, u2h_spT2_subset T i hp⟩
  · intro T' hT' hne; exact Or.inl ⟨hT', hne⟩
  · exact ⟨u2h_spT1 T i hp, Or.inr (Or.inl rfl), u2h_spT1_carrier T i hp⟩
  · exact ⟨u2h_spT2 T i hp, Or.inr (Or.inr rfl), u2h_spT2_carrier T i hp⟩

/-- U2 (positive distance): the faces not containing `x` stay at positive distance from `x`. -/
theorem U2_exists_ball_disjoint_faces {X : Set Plane} (K : Triangulation X) (x : Plane) :
    ∃ ε > 0, ∀ T ∈ K.faces, x ∉ T.carrier → Disjoint (Metric.ball x ε) T.carrier := by
  set U : Set Plane := ⋃ T ∈ {T ∈ K.faces | x ∉ T.carrier}, T.carrier with hU
  have hUc : IsClosed U :=
    (K.finite.subset (sep_subset _ _)).isClosed_biUnion fun T _ => (U1_triangle_isCompact T).isClosed
  have hx : x ∈ Uᶜ := by
    simp only [hU, mem_compl_iff, mem_iUnion, mem_ofPred_eq, not_exists]
    intro T hT hxT; exact hT.2 hxT
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hUc.isOpen_compl x hx
  refine ⟨ε, hε, fun T hT hxT => ?_⟩
  refine Set.disjoint_left.mpr fun y hy hyT => hball hy ?_
  exact mem_biUnion (x := T) ⟨hT, hxT⟩ hyT

/-- U2 (local structure): near `x ∈ X` the set `X` is the union of the faces containing `x`. -/
theorem U2_local_structure {X : Set Plane} (K : Triangulation X) {x : Plane} (hx : x ∈ X) :
    ∃ ε > 0, Metric.ball x ε ∩ X = Metric.ball x ε ∩ ⋃ T ∈ {T ∈ K.faces | x ∈ T.carrier}, T.carrier := by
  obtain ⟨ε, hε, hdisj⟩ := U2_exists_ball_disjoint_faces K x
  refine ⟨ε, hε, ?_⟩
  ext y
  simp only [mem_inter_iff, mem_iUnion, mem_ofPred_eq, exists_prop]
  constructor
  · rintro ⟨hy, hyX⟩
    rw [← K.cover] at hyX
    obtain ⟨T, hT, hyT⟩ := mem_iUnion₂.mp hyX
    refine ⟨hy, T, ⟨hT, ?_⟩, hyT⟩
    by_contra hxT
    exact Set.disjoint_left.mp (hdisj T hT hxT) hy hyT
  · rintro ⟨hy, T, ⟨hT, _⟩, hyT⟩
    exact ⟨hy, u2h_carrier_subset K hT hyT⟩

/-! U2 helpers: the reversed-edge lemma and the local two-face cover. -/
theorem u2h_det_affine2 (a q m w : Plane) (t : ℝ) :
    det a ((1 - t) • m + t • w - q) = (1 - t) * det a (m - q) + t * det a (w - q) := by
  simp only [u2h_det_def, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
    Prod.smul_snd, smul_eq_mul]; ring

theorem u2h_eventually_det_pos (a q m w : Plane) (h : 0 < det a (m - q)) :
    ∀ᶠ t in nhdsWithin (0 : ℝ) (Ioi 0), 0 < det a ((1 - t) • m + t • w - q) := by
  have hc : Continuous fun t : ℝ => det a ((1 - t) • m + t • w - q) := by unfold det; fun_prop
  have : ∀ᶠ t in nhds (0 : ℝ), (fun _ : ℝ => (0 : ℝ)) t < det a ((1 - t) • m + t • w - q) :=
    continuousAt_const.eventually_lt hc.continuousAt (by simpa using h)
  exact this.filter_mono nhdsWithin_le_nhds

/-- membership from the three edge functionals indexed from `i` -/
theorem u2h_mem_of_three (T : Triangle) (i : Fin 3) {y : Plane}
    (h0 : 0 ≤ det (T.v (i + 1) - T.v i) (y - T.v i))
    (h1 : 0 ≤ det (T.v (i + 2) - T.v (i + 1)) (y - T.v (i + 1)))
    (h2 : 0 ≤ det (T.v i - T.v (i + 2)) (y - T.v (i + 2))) : y ∈ T.carrier := by
  rw [u2h_mem_iff]
  intro j
  rcases u2h_fin3_cases i j with rfl | rfl | rfl
  · exact h0
  · rw [u2h_fin3_add_one_one]; exact h1
  · rw [u2h_fin3_add_two_one]; exact h2

/-- the midpoint of an edge lies on the open edge -/
theorem u2h_midpoint_mem_openSegment (p q : Plane) :
    (1 / 2 : ℝ) • p + (1 / 2 : ℝ) • q ∈ openSegment ℝ p q :=
  ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, rfl⟩

/-- L2: a face containing an edge of `T` and different from `T` carries that edge reversed. -/
theorem u2h_reversed_edge {T T'' : Triangle}
    (hTT'' : T.carrier ∩ T''.carrier = convexHull ℝ (range T.v ∩ range T''.v))
    (hne : T''.carrier ≠ T.carrier) (i : Fin 3) (hsub : T.edgeSeg i ⊆ T''.carrier) :
    ∃ a : Fin 3, T''.v a = T.v (i + 1) ∧ T''.v (a + 1) = T.v i := by
  set S := range T.v ∩ range T''.v with hS
  have hvi : T.v i ∈ S := by
    apply u2h_vertex_mem_of_mem_convexHull inter_subset_left
    rw [← hTT'']
    exact ⟨u2h_v_mem T i, hsub (left_mem_segment ℝ _ _)⟩
  have hvi1 : T.v (i + 1) ∈ S := by
    apply u2h_vertex_mem_of_mem_convexHull inter_subset_left
    rw [← hTT'']
    exact ⟨u2h_v_mem T (i + 1), hsub (right_mem_segment ℝ _ _)⟩
  obtain ⟨a₀, ha₀⟩ := hvi.2
  obtain ⟨b₀, hb₀⟩ := hvi1.2
  have hab : a₀ ≠ b₀ := by
    rintro rfl; exact u2h_v_ne T (by simp : i ≠ i + 1) (ha₀.symm.trans hb₀)
  rcases u2h_fin3_cases a₀ b₀ with rfl | rfl | rfl
  · exact absurd rfl hab
  · exfalso
    -- same orientation: contradiction
    have hw := u2h_pos_cyc T'' a₀
    rw [hb₀, ha₀] at hw
    obtain ⟨m, hm⟩ := u2h_exists_vertex_notMem hne
    have hmS : T.v m ∉ S := fun h => hm h.2
    have hm2 : m = i + 2 := by
      rcases u2h_fin3_cases i m with rfl | rfl | rfl
      · exact absurd hvi hmS
      · exact absurd hvi1 hmS
      · rfl
    subst hm2
    have hline : ∀ z ∈ T.carrier ∩ T''.carrier, det (T.v (i + 1) - T.v i) (z - T.v i) = 0 := by
      intro z hz
      rw [hTT''] at hz
      have := u2h_convexHull_subset_edge_of_notMem inter_subset_left hmS hz
      rw [u2h_fin3_add_two_one, u2h_fin3_add_two_two] at this
      exact u2h_det_eq_zero_of_mem_segment this
    set m₀ : Plane := (1 / 2 : ℝ) • T.v i + (1 / 2 : ℝ) • T.v (i + 1) with hm₀
    have hm₀o := u2h_midpoint_mem_openSegment (T.v i) (T.v (i + 1))
    obtain ⟨hd0, hd1, hd2⟩ := u2h_openSegment_dets T i hm₀o
    set w := T''.v (a₀ + 2) with hw'
    have E1 := u2h_eventually_det_pos _ _ m₀ w hd1
    have E2 := u2h_eventually_det_pos _ _ m₀ w hd2
    obtain ⟨t, ⟨⟨h1, h2⟩, ht0, ht1⟩⟩ := ((E1.and E2).and (Ioo_mem_nhdsGT zero_lt_one)).exists
    set z : Plane := (1 - t) • m₀ + t • w with hz
    have hzT : z ∈ T.carrier := by
      apply u2h_mem_of_three T i _ h1.le h2.le
      rw [u2h_det_affine2, hd0]
      have : 0 < t * det (T.v (i + 1) - T.v i) (w - T.v i) := mul_pos ht0 hw
      linarith
    have hzT'' : z ∈ T''.carrier := by
      apply (U1_triangle_convex T'').segment_subset (hsub (openSegment_subset_segment ℝ _ _ hm₀o))
        (u2h_v_mem T'' (a₀ + 2))
      exact ⟨1 - t, t, by linarith, ht0.le, by ring, rfl⟩
    have := hline z ⟨hzT, hzT''⟩
    rw [u2h_det_affine2, hd0] at this
    have : 0 < t * det (T.v (i + 1) - T.v i) (w - T.v i) := mul_pos ht0 hw
    linarith
  · refine ⟨a₀ + 2, hb₀, ?_⟩
    rw [u2h_fin3_add_two_one]; exact ha₀

/-- L3: near a point of an open edge shared (reversed) by two faces, the plane is covered by the
two faces. -/
theorem u2h_ball_subset_two_faces {T T'' : Triangle} (i : Fin 3) {a : Fin 3}
    (ha0 : T''.v a = T.v (i + 1)) (ha1 : T''.v (a + 1) = T.v i) {x : Plane}
    (hx : x ∈ openSegment ℝ (T.v i) (T.v (i + 1))) :
    ∃ ε > 0, Metric.ball x ε ⊆ T.carrier ∪ T''.carrier := by
  obtain ⟨_, hd1, hd2⟩ := u2h_openSegment_dets T i hx
  have hx'' : x ∈ openSegment ℝ (T''.v a) (T''.v (a + 1)) := by
    rw [ha0, ha1, openSegment_symm]; exact hx
  obtain ⟨_, he1, he2⟩ := u2h_openSegment_dets T'' a hx''
  set O : Set Plane := {y | 0 < det (T.v (i + 2) - T.v (i + 1)) (y - T.v (i + 1))} ∩
    {y | 0 < det (T.v i - T.v (i + 2)) (y - T.v (i + 2))} ∩
    ({y | 0 < det (T''.v (a + 2) - T''.v (a + 1)) (y - T''.v (a + 1))} ∩
    {y | 0 < det (T''.v a - T''.v (a + 2)) (y - T''.v (a + 2))}) with hO
  have hOopen : IsOpen O :=
    ((u2h_isOpen_det_pos _ _).inter (u2h_isOpen_det_pos _ _)).inter
      ((u2h_isOpen_det_pos _ _).inter (u2h_isOpen_det_pos _ _))
  have hxO : x ∈ O := ⟨⟨hd1, hd2⟩, ⟨he1, he2⟩⟩
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hOopen x hxO
  refine ⟨ε, hε, fun y hy => ?_⟩
  obtain ⟨⟨hy1, hy2⟩, ⟨hy3, hy4⟩⟩ := hball hy
  rcases le_or_gt 0 (det (T.v (i + 1) - T.v i) (y - T.v i)) with h | h
  · exact Or.inl (u2h_mem_of_three T i h hy1.le hy2.le)
  · right
    apply u2h_mem_of_three T'' a _ hy3.le hy4.le
    rw [ha0, ha1, u2h_det_sub_swap]
    linarith

theorem u2h_exists_det_neg_in_ball {a : Plane} (hane : a ≠ 0) (q x : Plane)
    (hx : det a (x - q) = 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ y ∈ Metric.ball x ε, det a (y - q) < 0 := by
  set w : Plane := (-a.2, a.1) with hw
  have hdw : 0 < det a w := by
    simp only [u2h_det_def, hw]
    have : a.1 ≠ 0 ∨ a.2 ≠ 0 := by
      by_contra hc; push Not at hc; exact hane (Prod.ext hc.1 hc.2)
    rcases this with h | h <;> nlinarith [sq_pos_of_ne_zero h, sq_nonneg a.1, sq_nonneg a.2]
  set t : ℝ := ε / (2 * (‖w‖ + 1)) with ht
  have htpos : 0 < t := by positivity
  refine ⟨x - t • w, ?_, ?_⟩
  · rw [Metric.mem_ball, dist_eq_norm, sub_sub_cancel_left, norm_neg, norm_smul,
      Real.norm_eq_abs, abs_of_pos htpos, ht]
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith [norm_nonneg w]
  · have hlin : det a (x - t • w - q) = det a (x - q) - t * det a w := by
      simp only [u2h_det_def, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
      ring
    rw [hlin, hx]
    nlinarith [mul_pos htpos hdw]

/-- U2 (sm-3:490-491 "single boundary"): an edge lying in exactly one face is in the frontier. -/
theorem U2_edgeSeg_subset_frontier {X : Set Plane} (K : Triangulation X) {T : Triangle}
    (hT : T ∈ K.faces) (i : Fin 3)
    (huniq : ∀ T' ∈ K.faces, T.edgeSeg i ⊆ T'.carrier → T'.carrier = T.carrier) :
    T.edgeSeg i ⊆ frontier X := by
  have hopen : openSegment ℝ (T.v i) (T.v (i + 1)) ⊆ frontier X := by
    intro x hx
    have hxX : x ∈ X := u2h_carrier_subset K hT (u2h_openSegment_mem T i hx)
    refine ⟨subset_closure hxX, fun hint => ?_⟩
    obtain ⟨ε₁, hε₁, hball₁⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hint)
    obtain ⟨ε₂, hε₂, hloc⟩ := U2_local_structure K hxX
    obtain ⟨hp1, _, _⟩ := u2h_openSegment_dets T i hx
    have hane : T.v (i + 1) - T.v i ≠ 0 := sub_ne_zero.mpr (u2h_v_ne T (by simp))
    obtain ⟨y, hy, hyneg⟩ := u2h_exists_det_neg_in_ball hane (T.v i) x hp1 (lt_min hε₁ hε₂)
    have hyX : y ∈ X := hball₁ (Metric.ball_subset_ball (min_le_left _ _) hy)
    have hy2 : y ∈ Metric.ball x ε₂ ∩ X := ⟨Metric.ball_subset_ball (min_le_right _ _) hy, hyX⟩
    rw [hloc] at hy2
    obtain ⟨T', ⟨hT', hxT'⟩, hyT'⟩ := mem_iUnion₂.mp hy2.2
    have hedge : T.edgeSeg i ⊆ T'.carrier :=
      u2h_edge_subset_of_openSegment_mem (K.inter T hT T' hT') i hx hxT'
    rw [huniq T' hT' hedge] at hyT'
    have := (u2h_mem_iff T y).mp hyT' i
    linarith
  have : T.edgeSeg i = closure (openSegment ℝ (T.v i) (T.v (i + 1))) :=
    (closure_openSegment _ _).symm
  rw [this]
  exact closure_minimal hopen isClosed_frontier

/-- U2: the open faces lie in the interior of `X`. -/
theorem U2_interior_face_subset_interior {X : Set Plane} (K : Triangulation X) {T : Triangle}
    (hT : T ∈ K.faces) : interior T.carrier ⊆ interior X := by
  exact interior_mono (u2h_carrier_subset K hT)

/-- U2: an open edge shared by two distinct faces lies in the interior of `X`. -/
theorem U2_openSegment_subset_interior_of_two_faces {X : Set Plane} (K : Triangulation X)
    {T T' : Triangle} (hT : T ∈ K.faces) (hT' : T' ∈ K.faces) (hne : T.carrier ≠ T'.carrier)
    (i : Fin 3) (h : T.edgeSeg i ⊆ T'.carrier) : openSegment ℝ (T.v i) (T.v (i + 1)) ⊆ interior X := by
  intro x hx
  obtain ⟨a, ha0, ha1⟩ := u2h_reversed_edge (K.inter T hT T' hT') hne.symm i h
  obtain ⟨ε, hε, hball⟩ := u2h_ball_subset_two_faces i ha0 ha1 hx
  rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff]
  exact ⟨ε, hε, hball.trans (union_subset (u2h_carrier_subset K hT) (u2h_carrier_subset K hT'))⟩

/-! U2 helpers: tangent cones at a vertex and the vertex-star lemma (a vertex all of whose edges are
doubly covered is interior: the covered directions form a clopen nonempty subset of the circle). -/
theorem u2h_parallel_of_det_eq_zero {u d : Plane} (hu : u ≠ 0) (h : det u d = 0) :
    ∃ c : ℝ, d = c • u := by
  simp only [u2h_det_def] at h
  by_cases h1 : u.1 = 0
  · have h2 : u.2 ≠ 0 := fun h2 => hu (Prod.ext h1 h2)
    have hd1 : d.1 = 0 := by
      rw [h1] at h
      have : u.2 * d.1 = 0 := by linarith
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h h2
      · exact h
    refine ⟨d.2 / u.2, ?_⟩
    ext
    · simp [hd1, h1]
    · simp; field_simp
  · refine ⟨d.1 / u.1, ?_⟩
    ext
    · simp; field_simp
    · simp; field_simp; linarith

/-- the tangent cone of `T` at its vertex `T.v j` -/
def u2h_cone (T : Triangle) (j : Fin 3) : Set Plane :=
  {y | 0 ≤ det (T.v (j + 1) - T.v j) (y - T.v j) ∧ 0 ≤ det (T.v j - T.v (j + 2)) (y - T.v j)}

theorem u2h_isClosed_cone (T : Triangle) (j : Fin 3) : IsClosed (u2h_cone T j) :=
  (u2h_isClosed_det_nonneg _ _).inter (u2h_isClosed_det_nonneg _ _)

theorem u2h_det_sub_vertex (u c y : Plane) : det (u - c) (y - c) = det (u - c) (y - u) := by
  simp only [u2h_det_def, Prod.fst_sub, Prod.snd_sub]; ring

theorem u2h_mem_of_mem_cone (T : Triangle) (j : Fin 3) {y : Plane} (hy : y ∈ u2h_cone T j)
    (h1 : 0 < det (T.v (j + 2) - T.v (j + 1)) (y - T.v (j + 1))) : y ∈ T.carrier := by
  apply u2h_mem_of_three T j hy.1 h1.le
  rw [u2h_det_sub_vertex]; exact hy.2

theorem u2h_vertex_mem_cone (T : Triangle) (j : Fin 3) : T.v j ∈ u2h_cone T j := by
  simp [u2h_cone]

theorem u2h_cone_smul (T : Triangle) (j : Fin 3) {d : Plane} (hd : T.v j + d ∈ u2h_cone T j) {c : ℝ}
    (hc : 0 ≤ c) : T.v j + c • d ∈ u2h_cone T j := by
  obtain ⟨h1, h2⟩ := hd
  simp only [add_sub_cancel_left] at h1 h2
  have e : ∀ a : Plane, det a (c • d) = c * det a d := fun a => by
    simp only [u2h_det_def, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring
  exact ⟨by rw [add_sub_cancel_left, e]; exact mul_nonneg hc h1,
    by rw [add_sub_cancel_left, e]; exact mul_nonneg hc h2⟩

theorem u2h_isOpen_det_pos' (a : Plane) : IsOpen {d : Plane | 0 < det a d} := by
  simpa using u2h_isOpen_det_pos a 0

/-- the `det` of the two edge vectors at a vertex -/
theorem u2h_det_edges_at_vertex (T : Triangle) (j : Fin 3) :
    0 < det (T.v j - T.v (j + 2)) (T.v (j + 1) - T.v j) := by
  have := u2h_pos_cyc T (j + 2)
  rw [u2h_fin3_add_two_one, u2h_fin3_add_two_two] at this
  rw [u2h_det_sub_vertex] at this
  exact this

theorem u2h_det_sub_left_swap (a b d : Plane) : det (a - b) d = -det (b - a) d := by
  simp only [u2h_det_def, Prod.fst_sub, Prod.snd_sub]; ring

theorem u2h_det_smul_right (a d : Plane) (c : ℝ) : det a (c • d) = c * det a d := by
  simp only [u2h_det_def, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring

/-- (3) around a nonzero direction of a cone at `x`, every direction lies in a cone at `x`, when
every edge at `x` is doubly covered. -/
theorem u2h_star_open_at {X : Set Plane} (K : Triangulation X) {x : Plane}
    (hdouble : ∀ T ∈ K.faces, ∀ i, x ∈ T.edgeSeg i →
      ∃ T' ∈ K.faces, T.edgeSeg i ⊆ T'.carrier ∧ T'.carrier ≠ T.carrier)
    {d : Plane} (hd : d ≠ 0) {T : Triangle} (hT : T ∈ K.faces) {j : Fin 3} (hj : T.v j = x)
    (hcone : x + d ∈ u2h_cone T j) :
    ∃ N : Set Plane, IsOpen N ∧ d ∈ N ∧
      ∀ d' ∈ N, ∃ T' ∈ K.faces, ∃ j', T'.v j' = x ∧ x + d' ∈ u2h_cone T' j' := by
  obtain ⟨hA, hB⟩ := hcone
  rw [hj, add_sub_cancel_left] at hA hB
  have hE := u2h_det_edges_at_vertex T j
  rw [hj] at hE
  have hmemT : ∀ d' : Plane, 0 ≤ det (T.v (j + 1) - x) d' → 0 ≤ det (x - T.v (j + 2)) d' →
      x + d' ∈ u2h_cone T j := fun d' h1 h2 =>
    ⟨by rw [hj, add_sub_cancel_left]; exact h1, by rw [hj, add_sub_cancel_left]; exact h2⟩
  rcases hA.lt_or_eq with hA | hA
  · rcases hB.lt_or_eq with hB | hB
    · refine ⟨{d' | 0 < det (T.v (j + 1) - x) d'} ∩ {d' | 0 < det (x - T.v (j + 2)) d'},
        (u2h_isOpen_det_pos' _).inter (u2h_isOpen_det_pos' _), ⟨hA, hB⟩, ?_⟩
      intro d' ⟨h1, h2⟩
      exact ⟨T, hT, j, hj, hmemT d' h1.le h2.le⟩
    · -- `d` points along the edge `j+2` (towards `T.v (j+2)`)
      have hu : x - T.v (j + 2) ≠ 0 :=
        sub_ne_zero.mpr (by rw [← hj]; exact u2h_v_ne T (by simp))
      obtain ⟨c', hc'⟩ := u2h_parallel_of_det_eq_zero hu hB.symm
      have hc'neg : c' < 0 := by
        have e : det (T.v (j + 1) - x) d = -(c' * det (x - T.v (j + 2)) (T.v (j + 1) - x)) := by
          rw [hc', u2h_det_smul_right, u2h_det_swap']; ring
        rw [e] at hA
        by_contra hc; push Not at hc
        nlinarith [mul_nonneg hc hE.le]
      have hxedge : x ∈ T.edgeSeg (j + 2) := by
        show x ∈ segment ℝ (T.v (j + 2)) (T.v (j + 2 + 1))
        rw [u2h_fin3_add_two_one, hj]; exact right_mem_segment ℝ _ _
      obtain ⟨T', hT', hsub, hne⟩ := hdouble T hT (j + 2) hxedge
      obtain ⟨a, ha0, ha1⟩ := u2h_reversed_edge (K.inter T hT T' hT') hne (j + 2) hsub
      rw [u2h_fin3_add_two_one, hj] at ha0
      have hP := u2h_pos_cyc T' a
      rw [ha0, ha1] at hP
      refine ⟨{d' | 0 < det (T.v (j + 1) - x) d'} ∩ {d' | 0 < det (x - T'.v (a + 2)) d'},
        (u2h_isOpen_det_pos' _).inter (u2h_isOpen_det_pos' _), ⟨hA, ?_⟩, ?_⟩
      · have e : det (x - T'.v (a + 2)) d = -(c' * det (T.v (j + 2) - x) (T'.v (a + 2) - x)) := by
          rw [hc', u2h_det_smul_right]
          simp only [u2h_det_def, Prod.fst_sub, Prod.snd_sub]; ring
        show 0 < det (x - T'.v (a + 2)) d
        rw [e]; exact neg_pos.mpr (mul_neg_of_neg_of_pos hc'neg hP)
      · intro d' ⟨h1, h2⟩
        by_cases hB' : 0 ≤ det (x - T.v (j + 2)) d'
        · exact ⟨T, hT, j, hj, hmemT d' h1.le hB'⟩
        · refine ⟨T', hT', a, ha0, ?_, ?_⟩
          · rw [ha0, ha1, add_sub_cancel_left, u2h_det_sub_left_swap]; linarith
          · rw [ha0, add_sub_cancel_left]; exact h2.le
  · -- `d` points along the edge `j` (towards `T.v (j+1)`)
    have hu : T.v (j + 1) - x ≠ 0 :=
      sub_ne_zero.mpr (by rw [← hj]; exact u2h_v_ne T (by simp))
    obtain ⟨c, hc⟩ := u2h_parallel_of_det_eq_zero hu hA.symm
    have eB : det (x - T.v (j + 2)) d = c * det (x - T.v (j + 2)) (T.v (j + 1) - x) := by
      rw [hc, u2h_det_smul_right]
    have hcpos : 0 < c := by
      have hc0 : c ≠ 0 := fun h => hd (by rw [hc, h, zero_smul])
      rw [eB] at hB
      rcases lt_or_gt_of_ne hc0 with h | h
      · nlinarith [mul_neg_of_neg_of_pos h hE]
      · exact h
    have hxedge : x ∈ T.edgeSeg j := by
      show x ∈ segment ℝ (T.v j) (T.v (j + 1))
      rw [hj]; exact left_mem_segment ℝ _ _
    obtain ⟨T', hT', hsub, hne⟩ := hdouble T hT j hxedge
    obtain ⟨a, ha0, ha1⟩ := u2h_reversed_edge (K.inter T hT T' hT') hne j hsub
    rw [hj] at ha1
    have hP := u2h_pos_cyc T' (a + 1)
    rw [u2h_fin3_add_one_one, u2h_fin3_add_one_two, ha1, ha0] at hP
    refine ⟨{d' | 0 < det (x - T.v (j + 2)) d'} ∩ {d' | 0 < det (T'.v (a + 2) - x) d'},
      (u2h_isOpen_det_pos' _).inter (u2h_isOpen_det_pos' _), ⟨?_, ?_⟩, ?_⟩
    · show 0 < det (x - T.v (j + 2)) d
      rw [eB]; exact mul_pos hcpos hE
    · show 0 < det (T'.v (a + 2) - x) d
      rw [hc, u2h_det_smul_right]; exact mul_pos hcpos hP
    · intro d' ⟨h1, h2⟩
      by_cases hA' : 0 ≤ det (T.v (j + 1) - x) d'
      · exact ⟨T, hT, j, hj, hmemT d' hA' h1.le⟩
      · refine ⟨T', hT', a + 1, ha1, ?_, ?_⟩
        · rw [u2h_fin3_add_one_one, ha1, add_sub_cancel_left]; exact h2.le
        · rw [u2h_fin3_add_one_two, ha1, ha0, add_sub_cancel_left, u2h_det_sub_left_swap]; linarith

/-- the vertex-star lemma: if every face through `x` has `x` as a vertex and every edge at `x` is
doubly covered, then `x` is an interior point of `X`. -/
theorem u2h_mem_interior_of_vertex_star {X : Set Plane} (K : Triangulation X) {x : Plane}
    (hx : x ∈ X) (hvert : ∀ T ∈ K.faces, x ∈ T.carrier → ∃ j, T.v j = x)
    (hdouble : ∀ T ∈ K.faces, ∀ i, x ∈ T.edgeSeg i →
      ∃ T' ∈ K.faces, T.edgeSeg i ⊆ T'.carrier ∧ T'.carrier ≠ T.carrier) :
    x ∈ interior X := by
  set D : Set Plane := {d | ∃ T ∈ K.faces, ∃ j, T.v j = x ∧ x + d ∈ u2h_cone T j} with hD
  have hDclosed : IsClosed D := by
    have : D = ⋃ T ∈ K.faces, ⋃ j : Fin 3, {d | T.v j = x ∧ x + d ∈ u2h_cone T j} := by
      ext d; simp only [hD, mem_setOf_eq, mem_iUnion, exists_prop]
    rw [this]
    refine K.finite.isClosed_biUnion fun T _ => isClosed_iUnion_of_finite fun j => ?_
    by_cases h : T.v j = x
    · have : {d | T.v j = x ∧ x + d ∈ u2h_cone T j} = (fun d => x + d) ⁻¹' u2h_cone T j := by
        ext d; simp [h]
      rw [this]; exact (u2h_isClosed_cone T j).preimage (continuous_const.add continuous_id)
    · have : {d | T.v j = x ∧ x + d ∈ u2h_cone T j} = ∅ := by ext d; simp [h]
      rw [this]; exact isClosed_empty
  have hx' := hx
  rw [← K.cover] at hx'
  obtain ⟨T₀, hT₀, hxT₀⟩ := mem_iUnion₂.mp hx'
  obtain ⟨j₀, hj₀⟩ := hvert T₀ hT₀ hxT₀
  have hsphere : ∀ d ∈ Metric.sphere (0 : Plane) 1, d ∈ D := by
    have hconn : IsConnected (Metric.sphere (0 : Plane) 1) :=
      isConnected_sphere (by rw [← Module.finrank_eq_rank]; simp [Module.finrank_prod]) 0 zero_le_one
    have : ConnectedSpace (Metric.sphere (0 : Plane) 1) := isConnected_iff_connectedSpace.mp hconn
    set A : Set (Metric.sphere (0 : Plane) 1) := {d | (d : Plane) ∈ D} with hA
    have hAclosed : IsClosed A := hDclosed.preimage continuous_subtype_val
    have hAopen : IsOpen A := by
      rw [isOpen_iff_forall_mem_open]
      intro d hd
      have hd0 : (d : Plane) ≠ 0 := by
        intro h0
        have := d.2
        rw [mem_sphere_zero_iff_norm, h0, norm_zero] at this
        exact zero_ne_one this
      obtain ⟨T, hT, j, hj, hcone⟩ := hd
      obtain ⟨N, hNopen, hdN, hN⟩ := u2h_star_open_at K hdouble hd0 hT hj hcone
      exact ⟨Subtype.val ⁻¹' N, fun d' hd' => hN d' hd', hNopen.preimage continuous_subtype_val, hdN⟩
    have hAne : A.Nonempty := by
      set u := T₀.v (j₀ + 1) - x with hu
      have hu0 : u ≠ 0 := sub_ne_zero.mpr (by rw [← hj₀]; exact u2h_v_ne T₀ (by simp))
      have hnu : 0 < ‖u‖ := norm_pos_iff.mpr hu0
      refine ⟨⟨‖u‖⁻¹ • u, ?_⟩, T₀, hT₀, j₀, hj₀, ?_, ?_⟩
      · rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hnu.ne']
      · rw [hj₀, add_sub_cancel_left, u2h_det_smul_right, hu, u2h_det_self, mul_zero]
      · have hE := u2h_det_edges_at_vertex T₀ j₀
        rw [hj₀] at hE
        rw [hj₀, add_sub_cancel_left, u2h_det_smul_right]
        exact (mul_pos (inv_pos.mpr hnu) hE).le
    rcases isClopen_iff.mp ⟨hAclosed, hAopen⟩ with h | h
    · exact absurd h hAne.ne_empty
    · intro d hd
      have : (⟨d, hd⟩ : Metric.sphere (0 : Plane) 1) ∈ A := by rw [h]; exact mem_univ _
      exact this
  have hcover : ∀ y : Plane, ∃ T ∈ K.faces, ∃ j, T.v j = x ∧ y ∈ u2h_cone T j := by
    intro y
    by_cases hyx : y = x
    · exact ⟨T₀, hT₀, j₀, hj₀, by rw [hyx, ← hj₀]; exact u2h_vertex_mem_cone T₀ j₀⟩
    · have hn : 0 < ‖y - x‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hyx)
      have hd : ‖y - x‖⁻¹ • (y - x) ∈ Metric.sphere (0 : Plane) 1 := by
        rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
      obtain ⟨T, hT, j, hj, hcone⟩ := hsphere _ hd
      refine ⟨T, hT, j, hj, ?_⟩
      have := u2h_cone_smul T j (d := ‖y - x‖⁻¹ • (y - x)) (by rw [hj]; exact hcone) hn.le
      rwa [smul_smul, mul_inv_cancel₀ hn.ne', one_smul, hj, add_sub_cancel] at this
  set O : Set Plane := {y | ∀ T ∈ K.faces, ∀ j : Fin 3, T.v j = x →
    0 < det (T.v (j + 2) - T.v (j + 1)) (y - T.v (j + 1))} with hO
  have hOopen : IsOpen O := by
    have : O = ⋂ T ∈ K.faces, ⋂ j : Fin 3,
        {y | T.v j = x → 0 < det (T.v (j + 2) - T.v (j + 1)) (y - T.v (j + 1))} := by
      ext y; simp only [hO, mem_setOf_eq, mem_iInter]
    rw [this]
    refine K.finite.isOpen_biInter fun T _ => isOpen_iInter_of_finite fun j => ?_
    by_cases h : T.v j = x
    · simp only [h, true_implies]; exact u2h_isOpen_det_pos _ _
    · simp only [h, false_implies, setOf_true]; exact isOpen_univ
  have hxO : x ∈ O := by
    intro T hT j hj
    have := u2h_pos_cyc T (j + 1)
    rw [u2h_fin3_add_one_one, u2h_fin3_add_one_two, hj] at this
    exact this
  have hOX : O ⊆ X := by
    intro y hy
    obtain ⟨T, hT, j, hj, hcone⟩ := hcover y
    exact u2h_carrier_subset K hT (u2h_mem_of_mem_cone T j hcone (hy T hT j hj))
  exact interior_mono hOX (by rw [hOopen.interior_eq]; exact hxO)

/-- U2: the frontier of `X` is the union of the edges lying in exactly one face. -/
theorem U2_frontier_eq_iUnion_boundary_edges {X : Set Plane} (K : Triangulation X) :
    frontier X = ⋃ T ∈ K.faces, ⋃ i : Fin 3,
      ⋃ (_ : ∀ T' ∈ K.faces, T.edgeSeg i ⊆ T'.carrier → T'.carrier = T.carrier), T.edgeSeg i := by
  apply Subset.antisymm
  · intro x hx
    have hxX : x ∈ X := by
      have := hx.1
      rwa [(U2_isCompact_of_triangulation K).isClosed.closure_eq] at this
    have hxint : x ∉ interior X := hx.2
    by_contra hnot
    simp only [mem_iUnion, exists_prop, not_exists, not_and] at hnot
    apply hxint
    have hdouble : ∀ T ∈ K.faces, ∀ i, x ∈ T.edgeSeg i →
        ∃ T' ∈ K.faces, T.edgeSeg i ⊆ T'.carrier ∧ T'.carrier ≠ T.carrier := by
      intro T hT i hxi
      by_contra hc
      push Not at hc
      exact hnot T hT i (fun T' hT' h => hc T' hT' h) hxi
    have hvert : ∀ T ∈ K.faces, x ∈ T.carrier → ∃ j, T.v j = x := by
      intro T hT hxT
      by_cases hint : x ∈ interior T.carrier
      · exact absurd (U2_interior_face_subset_interior K hT hint) hxint
      have hfr : x ∈ frontier T.carrier :=
        ⟨by rw [(U1_triangle_isCompact T).isClosed.closure_eq]; exact hxT, hint⟩
      rw [U1_frontier_triangle, mem_iUnion] at hfr
      obtain ⟨i, hi⟩ := hfr
      rw [← insert_endpoints_openSegment] at hi
      rcases hi with rfl | rfl | hi
      · exact ⟨i, rfl⟩
      · exact ⟨i + 1, rfl⟩
      · exfalso
        obtain ⟨T', hT', hsub, hne⟩ := hdouble T hT i (openSegment_subset_segment ℝ _ _ hi)
        exact hxint (U2_openSegment_subset_interior_of_two_faces K hT hT' hne.symm i hsub hi)
    exact u2h_mem_interior_of_vertex_star K hxX hvert hdouble
  · intro x hx
    simp only [mem_iUnion, exists_prop] at hx
    obtain ⟨T, hT, i, huniq, hxi⟩ := hx
    exact U2_edgeSeg_subset_frontier K hT i huniq hxi

/-! U2 helpers: images of convex hulls under affine maps, the pushforward triangulation. -/
/-- the affine map `x ↦ M x + b` as an `AffineMap` -/
theorem u2h_image_convexHull_of_affineOn {f : Plane → Plane} {C S : Set Plane} (hf : AffineOn f C)
    (hC : Convex ℝ C) (hS : S ⊆ C) : f '' convexHull ℝ S = convexHull ℝ (f '' S) := by
  obtain ⟨M, b, hM⟩ := hf
  set A : Plane →ᵃ[ℝ] Plane := M.toAffineMap + AffineMap.const ℝ Plane b with hA
  have hAx : ∀ x, A x = M x + b := fun x => by simp [hA]
  have h1 : f '' convexHull ℝ S = A '' convexHull ℝ S := by
    apply image_congr
    intro x hx
    rw [hM x (convexHull_min hS hC hx), hAx]
  have h2 : f '' S = A '' S := by
    apply image_congr
    intro x hx
    rw [hM x (hS hx), hAx]
  rw [h1, h2, AffineMap.image_convexHull]

theorem u2h_image_carrier {f : Plane → Plane} {T : Triangle} (hf : AffineOn f T.carrier) :
    f '' T.carrier = convexHull ℝ (range (f ∘ T.v)) := by
  rw [Triangle.carrier, u2h_image_convexHull_of_affineOn hf (U1_triangle_convex T)
    (subset_convexHull ℝ _), range_comp]

theorem u2h_map_carrier {f : Plane → Plane} {T : Triangle} (hf : IsPositiveAffineOn f T) :
    (T.map f hf).carrier = f '' T.carrier := by
  rw [u2h_image_carrier hf.1]; rfl

/-- the pushforward triangulation, with the faces identified as `T.map H` -/
theorem u2h_pushforward {X : Set Plane} (K : Triangulation X) (H : Plane ≃ₜ Plane)
    (hH : IsPositivePLOn H K) :
    ∃ K' : Triangulation (H '' X), (∀ T ∈ K.faces, ∃ hT : IsPositiveAffineOn H T, T.map H hT ∈ K'.faces) ∧
      ∀ T' ∈ K'.faces, ∃ T ∈ K.faces, ∃ hT : IsPositiveAffineOn H T, T' = T.map H hT := by
  have : Finite K.faces := K.finite.to_subtype
  set F : Set Triangle := range (fun T : K.faces => T.1.map H (hH T.1 T.2)) with hF
  have hcover : (⋃ T' ∈ F, T'.carrier) = H '' X := by
    rw [← K.cover, image_iUnion₂]
    apply Subset.antisymm
    · intro y hy
      obtain ⟨T', ⟨T, rfl⟩, hy⟩ := mem_iUnion₂.mp hy
      rw [u2h_map_carrier] at hy
      exact mem_iUnion₂.mpr ⟨T.1, T.2, hy⟩
    · intro y hy
      obtain ⟨T, hT, hy⟩ := mem_iUnion₂.mp hy
      refine mem_iUnion₂.mpr ⟨T.map H (hH T hT), ⟨⟨T, hT⟩, rfl⟩, ?_⟩
      rw [u2h_map_carrier]; exact hy
  have hinter : ∀ T₁ ∈ F, ∀ T₂ ∈ F,
      T₁.carrier ∩ T₂.carrier = convexHull ℝ (range T₁.v ∩ range T₂.v) := by
    rintro _ ⟨T₁, rfl⟩ _ ⟨T₂, rfl⟩
    rw [u2h_map_carrier, u2h_map_carrier, ← image_inter H.injective, K.inter T₁.1 T₁.2 T₂.1 T₂.2]
    have hS : range T₁.1.v ∩ range T₂.1.v ⊆ T₁.1.carrier :=
      inter_subset_left.trans (subset_convexHull ℝ _)
    rw [u2h_image_convexHull_of_affineOn (hH T₁.1 T₁.2).1 (U1_triangle_convex _) hS,
      image_inter H.injective]
    show _ = convexHull ℝ (range (H ∘ T₁.1.v) ∩ range (H ∘ T₂.1.v))
    rw [range_comp, range_comp]
  refine ⟨⟨F, finite_range _, hcover, hinter⟩, ?_, ?_⟩
  · intro T hT; exact ⟨hH T hT, ⟨⟨T, hT⟩, rfl⟩⟩
  · rintro _ ⟨T, rfl⟩; exact ⟨T.1, T.2, hH T.1 T.2, rfl⟩

/-- U2 (pushforward): the image triangulation under a positive PL homeomorphism of the plane. -/
theorem U2_pushforward {X : Set Plane} (K : Triangulation X) (H : Plane ≃ₜ Plane)
    (hH : IsPositivePLOn H K) :
    ∃ K' : Triangulation (H '' X), (∀ T ∈ K.faces, ∃ hT : IsPositiveAffineOn H T, T.map H hT ∈ K'.faces) ∧
      ∀ T' ∈ K'.faces, ∃ T ∈ K.faces, T'.carrier = H '' T.carrier := by
  obtain ⟨K', h1, h2⟩ := u2h_pushforward K H hH
  refine ⟨K', h1, fun T' hT' => ?_⟩
  obtain ⟨T, hT, hTa, rfl⟩ := h2 T' hT'
  exact ⟨T, hT, u2h_map_carrier hTa⟩

/-- an affine map on a triangle is determined by its vertex values -/
theorem u2h_affineOn_apply_bary {f : Plane → Plane} {S : Set Plane} (hf : AffineOn f S) {T : Triangle}
    (hv : ∀ k, T.v k ∈ S) {x : Plane} (hx : x ∈ S) {μ0 μ1 μ2 : ℝ}
    (hμ : x = μ0 • T.v 0 + μ1 • T.v 1 + μ2 • T.v 2) (hs : μ0 + μ1 + μ2 = 1) :
    f x = μ0 • f (T.v 0) + μ1 • f (T.v 1) + μ2 • f (T.v 2) := by
  obtain ⟨M, b, hM⟩ := hf
  rw [hM x hx, hM _ (hv 0), hM _ (hv 1), hM _ (hv 2), hμ]
  simp only [map_add, map_smul, smul_add]
  have : μ2 = 1 - μ0 - μ1 := by linarith
  subst this
  module

theorem u2h_affineOn_eq_of_vertices {f g : Plane → Plane} {T : Triangle} (hf : AffineOn f T.carrier)
    (hg : AffineOn g T.carrier) (h : ∀ k, f (T.v k) = g (T.v k)) {x : Plane} (hx : x ∈ T.carrier) :
    f x = g x := by
  obtain ⟨μ0, μ1, μ2, _, _, _, hs, hμ⟩ := u2h_bary T hx
  rw [u2h_affineOn_apply_bary hf (u2h_v_mem T) hx hμ hs,
    u2h_affineOn_apply_bary hg (u2h_v_mem T) hx hμ hs, h 0, h 1, h 2]

/-- U2 (inverse): the inverse of a positive PL homeomorphism is positive PL on the pushforward. -/
theorem U2_inverse_isPositivePLOn {X : Set Plane} (K : Triangulation X) (H : Plane ≃ₜ Plane)
    (hH : IsPositivePLOn H K) :
    ∃ K' : Triangulation (H '' X), IsPositivePLOn H.symm K' := by
  obtain ⟨K', _, hK'2⟩ := u2h_pushforward K H hH
  refine ⟨K', fun T' hT' => ?_⟩
  obtain ⟨T, hT, hTa, rfl⟩ := hK'2 T' hT'
  obtain ⟨g, hg, hgv⟩ := U1_exists_affine_of_triangle (T.map H hTa) T.v
  have hgH : ∀ x ∈ T.carrier, g (H x) = x := by
    intro x hx
    have hcomp : AffineOn (g ∘ H) T.carrier :=
      U1_affineOn_comp hTa.1 (U1_affineOn_mono hg (subset_univ _)) (subset_univ _)
    have hid : AffineOn (fun x : Plane => x) T.carrier := ⟨LinearMap.id, 0, fun x _ => by simp⟩
    exact u2h_affineOn_eq_of_vertices hcomp hid (fun k => hgv k) hx
  constructor
  · obtain ⟨M, b, hM⟩ := hg
    refine ⟨M, b, fun y hy => ?_⟩
    rw [u2h_map_carrier] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    rw [H.symm_apply_apply, ← hM _ (mem_univ _), hgH x hx]
  · simp only [Triangle.map, Function.comp_apply, Homeomorph.symm_apply_apply]
    exact T.pos

/-- U2 helper: an affine map is continuous. -/
theorem u2h_continuousOn_of_affineOn {f : Plane → Plane} {S : Set Plane} (hf : AffineOn f S) :
    ContinuousOn f S := by
  obtain ⟨M, b, hM⟩ := hf
  have : ContinuousOn (fun x => M x + b) S :=
    (M.continuous_of_finiteDimensional.add continuous_const).continuousOn
  exact this.congr hM

/-- U2 helper: a positive PL map is continuous on `X` (pasting lemma over the faces). -/
theorem u2h_continuousOn_of_isPositivePLOn {X : Set Plane} (K : Triangulation X) {f : Plane → Plane}
    (hf : IsPositivePLOn f K) : ContinuousOn f X := by
  rw [← K.cover, biUnion_eq_iUnion]
  have : Finite K.faces := K.finite.to_subtype
  exact U1_continuousOn_iUnion_of_finite (fun T => U1_triangle_isCompact T.1 |>.isClosed)
    (fun T => u2h_continuousOn_of_affineOn (hf T.1 T.2).1)

/-- U2 (sm-3:520-523, the disc parametrisation is a homeomorphism): a face-wise positive affine map
that is injective on `X` is a homeomorphism of `X` onto its image (compactness). -/
theorem U2_isHomeoOnto_of_isPositivePLOn {X : Set Plane} (K : Triangulation X) {f : Plane → Plane}
    (hf : IsPositivePLOn f K) (hinj : InjOn f X) : IsHomeoOnto X (f '' X) f := by
  have : CompactSpace X := isCompact_iff_compactSpace.mp (U2_isCompact_of_triangulation K)
  have hc : Continuous (Equiv.Set.imageOfInjOn f X hinj) := by
    apply Continuous.subtype_mk
    exact (u2h_continuousOn_of_isPositivePLOn K hf).domRestrict
  exact ⟨hc.homeoOfEquivCompactToT2, fun z => rfl⟩

/-- U2: a positive PL map is continuous on `X`. -/
theorem U2_continuousOn_of_isPositivePLOn {X : Set Plane} (K : Triangulation X) {f : Plane → Plane}
    (hf : IsPositivePLOn f K) : ContinuousOn f X := by
  exact u2h_continuousOn_of_isPositivePLOn K hf

/-! ### U3 (lane A) — overlay / common refinement -/

/-- U3: `g : Plane → Sphere` is positive PL from the plane set `D` into the sphere with model `L'`:
`D` carries a triangulation each of whose faces is sent into one target chart image, where `g` read
in that chart is positive affine (the inverse-parametrisation side of `IsPositivePLSphereMap`). -/
def IsPositivePLFromPlane (L' : ℝ) (D : Set Plane) (g : Plane → Sphere) : Prop :=
  ∃ K : Triangulation D, ∀ T ∈ K.faces, ∃ b' : Bool,
    (∀ x ∈ T.carrier, g x ∈ modelChart L' b' '' modelDomain L' b') ∧
    IsPositiveAffineOn (modelChartInv L' b' ∘ g) T


/-! ### U3 helpers (u3h_): plane algebra and barycentric coordinates -/

theorem u3h_planeDot_add (p x y : Plane) : planeDot p (x + y) = planeDot p x + planeDot p y := by
  simp [planeDot]; ring

theorem u3h_planeDot_smul (p : Plane) (a : ℝ) (x : Plane) : planeDot p (a • x) = a * planeDot p x := by
  simp [planeDot]; ring

theorem u3h_planeDot_sub (p x y : Plane) : planeDot p (x - y) = planeDot p x - planeDot p y := by
  simp [planeDot]; ring

theorem u3h_planeDot_neg_left (p x : Plane) : planeDot (-p) x = -planeDot p x := by
  simp [planeDot]; ring

theorem u3h_planeDot_zero_left (x : Plane) : planeDot 0 x = 0 := by
  simp [planeDot]

theorem u3h_planeDot_combo (p x y : Plane) (a b : ℝ) :
    planeDot p (a • x + b • y) = a * planeDot p x + b * planeDot p y := by
  rw [u3h_planeDot_add, u3h_planeDot_smul, u3h_planeDot_smul]

theorem u3h_convex_le (p : Plane) (r : ℝ) : Convex ℝ {x : Plane | planeDot p x ≤ r} := by
  intro x hx y hy a b ha hb hab
  simp only [mem_ofPred_eq] at *
  rw [u3h_planeDot_combo]
  have h1 : a * r + b * r = r := by rw [← add_mul, hab, one_mul]
  nlinarith [mul_le_mul_of_nonneg_left hx ha, mul_le_mul_of_nonneg_left hy hb]

theorem u3h_convex_ge (p : Plane) (r : ℝ) : Convex ℝ {x : Plane | r ≤ planeDot p x} := by
  intro x hx y hy a b ha hb hab
  simp only [mem_ofPred_eq] at *
  rw [u3h_planeDot_combo]
  have h1 : a * r + b * r = r := by rw [← add_mul, hab, one_mul]
  nlinarith [mul_le_mul_of_nonneg_left hx ha, mul_le_mul_of_nonneg_left hy hb]

theorem u3h_convex_eq (p : Plane) (r : ℝ) : Convex ℝ {x : Plane | planeDot p x = r} := by
  intro x hx y hy a b ha hb hab
  simp only [mem_ofPred_eq] at *
  rw [u3h_planeDot_combo, hx, hy]; linear_combination r * hab

theorem u3h_range_v (T : Triangle) : range T.v = {T.v 0, T.v 1, T.v 2} := by
  ext y; constructor
  · rintro ⟨i, rfl⟩; fin_cases i <;> simp
  · rintro (rfl | rfl | rfl) <;> exact ⟨_, rfl⟩

/-- Membership in a triangle by three weights. -/
theorem u3h_mem_carrier_iff (T : Triangle) (x : Plane) :
    x ∈ T.carrier ↔ ∃ a b c : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ a + b + c = 1 ∧
      a • T.v 0 + b • T.v 1 + c • T.v 2 = x := by
  constructor
  · intro hx
    unfold Triangle.carrier at hx
    rw [u3h_range_v, convexHull_insert (by simp), convexHull_pair, mem_convexJoin] at hx
    obtain ⟨a₀, ha₀, y, hy, hxy⟩ := hx
    rw [mem_singleton_iff] at ha₀; subst ha₀
    obtain ⟨γ, δ, hγ, hδ, hγδ, rfl⟩ := hy
    obtain ⟨α, β, hα, hβ, hαβ, rfl⟩ := hxy
    refine ⟨α, β * γ, β * δ, hα, mul_nonneg hβ hγ, mul_nonneg hβ hδ, ?_, ?_⟩
    · linear_combination hαβ + β * hγδ
    · simp only [smul_add, mul_smul]; abel
  · rintro ⟨a, b, c, ha, hb, hc, habc, rfl⟩
    refine mem_convexHull_of_exists_fintype (ι := Fin 3) ![a, b, c] T.v ?_ ?_ (fun i => ⟨i, rfl⟩) ?_
    · intro i; fin_cases i <;> simpa
    · simp [Fin.sum_univ_three]; linarith
    · simp [Fin.sum_univ_three]

/-- Barycentric coordinates are unique (nondegeneracy). -/
theorem u3h_bary_unique (T : Triangle) {a b c a' b' c' : ℝ}
    (h : a • T.v 0 + b • T.v 1 + c • T.v 2 = a' • T.v 0 + b' • T.v 1 + c' • T.v 2)
    (hs : a + b + c = a' + b' + c') : a = a' ∧ b = b' ∧ c = c' := by
  have hD := T.pos
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at h1 h2
  unfold det at hD
  simp only [Prod.fst_sub, Prod.snd_sub] at hD
  have E1 : (b - b') * ((T.v 1).1 - (T.v 0).1) + (c - c') * ((T.v 2).1 - (T.v 0).1) = 0 := by
    linear_combination h1 - (T.v 0).1 * hs
  have E2 : (b - b') * ((T.v 1).2 - (T.v 0).2) + (c - c') * ((T.v 2).2 - (T.v 0).2) = 0 := by
    linear_combination h2 - (T.v 0).2 * hs
  have hb : (b - b') * (((T.v 1).1 - (T.v 0).1) * ((T.v 2).2 - (T.v 0).2)
      - ((T.v 1).2 - (T.v 0).2) * ((T.v 2).1 - (T.v 0).1)) = 0 := by
    linear_combination ((T.v 2).2 - (T.v 0).2) * E1 - ((T.v 2).1 - (T.v 0).1) * E2
  have hc : (c - c') * (((T.v 1).1 - (T.v 0).1) * ((T.v 2).2 - (T.v 0).2)
      - ((T.v 1).2 - (T.v 0).2) * ((T.v 2).1 - (T.v 0).1)) = 0 := by
    linear_combination ((T.v 1).1 - (T.v 0).1) * E2 - ((T.v 1).2 - (T.v 0).2) * E1
  rcases mul_eq_zero.1 hb with hb | hb
  · rcases mul_eq_zero.1 hc with hc | hc
    · refine ⟨by linarith, by linarith, by linarith⟩
    · linarith
  · linarith

theorem u3h_pos_cyc (T : Triangle) (i : Fin 3) :
    0 < det (T.v (i + 1) - T.v i) (T.v (i + 2) - T.v i) := by
  have h := T.pos
  fin_cases i
  · simpa using h
  · have : det (T.v 2 - T.v 1) (T.v 0 - T.v 1) = det (T.v 1 - T.v 0) (T.v 2 - T.v 0) := by
      simp [det]; ring
    simpa [this] using h
  · have : det (T.v 0 - T.v 2) (T.v 1 - T.v 2) = det (T.v 1 - T.v 0) (T.v 2 - T.v 0) := by
      simp [det]; ring
    simpa [this] using h

theorem u3h_v01 (T : Triangle) : T.v 0 ≠ T.v 1 := by
  intro h
  have := u3h_bary_unique T (a := 1) (b := 0) (c := 0) (a' := 0) (b' := 1) (c' := 0)
    (by simp [h]) (by norm_num)
  norm_num at this

theorem u3h_v02 (T : Triangle) : T.v 0 ≠ T.v 2 := by
  intro h
  have := u3h_bary_unique T (a := 1) (b := 0) (c := 0) (a' := 0) (b' := 0) (c' := 1)
    (by simp [h]) (by norm_num)
  norm_num at this

theorem u3h_v12 (T : Triangle) : T.v 1 ≠ T.v 2 := by
  intro h
  have := u3h_bary_unique T (a := 0) (b := 1) (c := 0) (a' := 0) (b' := 0) (c' := 1)
    (by simp [h]) (by norm_num)
  norm_num at this

theorem u3h_v_injective (T : Triangle) : Function.Injective T.v := by
  have h01 := u3h_v01 T; have h02 := u3h_v02 T; have h12 := u3h_v12 T
  intro i j h
  fin_cases i <;> fin_cases j <;> simp at h ⊢
  all_goals first | exact (h01 h).elim | exact (h02 h).elim | exact (h12 h).elim | exact (h01 h.symm).elim | exact (h02 h.symm).elim | exact (h12 h.symm).elim

/-- A vertex different from `T.v i` is `T.v (i+1)` or `T.v (i+2)`. -/
theorem u3h_other (T : Triangle) (i j : Fin 3) (h : T.v j ≠ T.v i) :
    T.v j = T.v (i + 1) ∨ T.v j = T.v (i + 2) := by
  fin_cases i <;> fin_cases j <;> simp_all

/-- No vertex lies on the segment of the other two. -/
theorem u3h_v_not_mem_segment (T : Triangle) (i : Fin 3) :
    T.v i ∉ segment ℝ (T.v (i + 1)) (T.v (i + 2)) := by
  fin_cases i <;> simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, Fin.reduceFinMk] <;>
    rintro ⟨α, β, hα, hβ, hαβ, h⟩
  · have := u3h_bary_unique T (a := 0) (b := α) (c := β) (a' := 1) (b' := 0) (c' := 0)
      (by simpa using h) (by linarith)
    norm_num at this
  · have := u3h_bary_unique T (a := β) (b := 0) (c := α) (a' := 0) (b' := 1) (c' := 0)
      (by simpa [add_comm] using h) (by linarith)
    norm_num at this
  · have := u3h_bary_unique T (a := α) (b := β) (c := 0) (a' := 0) (b' := 0) (c' := 1)
      (by simpa using h) (by linarith)
    norm_num at this

/-- Two edges meet only in their common vertex. -/
theorem u3h_segment_inter (T : Triangle) (i : Fin 3) {x : Plane}
    (h1 : x ∈ segment ℝ (T.v i) (T.v (i + 1))) (h2 : x ∈ segment ℝ (T.v (i + 1)) (T.v (i + 2))) :
    x = T.v (i + 1) := by
  fin_cases i <;> simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, Fin.reduceFinMk] at h1 h2 ⊢ <;>
    obtain ⟨α, β, hα, hβ, hαβ, rfl⟩ := h1 <;> obtain ⟨γ, δ, hγ, hδ, hγδ, h⟩ := h2
  · have := u3h_bary_unique T (a := 0) (b := γ) (c := δ) (a' := α) (b' := β) (c' := 0)
      (by simpa using h) (by linarith)
    obtain ⟨rfl, rfl, rfl⟩ := this
    have hγ1 : γ = 1 := by linarith
    simp [hγ1]
  · have := u3h_bary_unique T (a := δ) (b := 0) (c := γ) (a' := 0) (b' := α) (c' := β)
      (by simpa [add_comm] using h) (by linarith)
    obtain ⟨rfl, rfl, rfl⟩ := this
    have hγ1 : γ = 1 := by linarith
    simp [hγ1]
  · have := u3h_bary_unique T (a := γ) (b := δ) (c := 0) (a' := β) (b' := 0) (c' := α)
      (by simpa [add_comm] using h) (by linarith)
    obtain ⟨rfl, rfl, rfl⟩ := this
    have hγ1 : γ = 1 := by linarith
    simp [hγ1]

/-- A vertex in the convex hull of a set of vertices is one of them. -/
theorem u3h_v_mem_convexHull (T : Triangle) {S : Set Plane} (hS : S ⊆ range T.v) (i : Fin 3)
    (h : T.v i ∈ convexHull ℝ S) : T.v i ∈ S := by
  by_contra hn
  have hsub : S ⊆ {T.v (i + 1), T.v (i + 2)} := by
    intro y hy
    obtain ⟨j, rfl⟩ := hS hy
    have hne : T.v j ≠ T.v i := fun e => hn (e ▸ hy)
    rcases u3h_other T i j hne with e | e <;> simp [e]
  have := convexHull_mono hsub h
  rw [convexHull_pair] at this
  exact u3h_v_not_mem_segment T i this

/-- The three vertices are not all on one line (for a genuine line). -/
theorem u3h_not_all_on_line (T : Triangle) {p : Plane} {r : ℝ} (hp : p ≠ 0)
    (h : ∀ i, planeDot p (T.v i) = r) : False := by
  have hD := T.pos
  have h0 := h 0; have h1 := h 1; have h2 := h 2
  unfold det at hD; unfold planeDot at h0 h1 h2
  simp only [Prod.fst_sub, Prod.snd_sub] at hD
  have e1 : p.1 * (((T.v 1).1 - (T.v 0).1) * ((T.v 2).2 - (T.v 0).2)
      - ((T.v 1).2 - (T.v 0).2) * ((T.v 2).1 - (T.v 0).1)) = 0 := by
    linear_combination ((T.v 2).2 - (T.v 0).2) * (h1 - h0) - ((T.v 1).2 - (T.v 0).2) * (h2 - h0)
  have e2 : p.2 * (((T.v 1).1 - (T.v 0).1) * ((T.v 2).2 - (T.v 0).2)
      - ((T.v 1).2 - (T.v 0).2) * ((T.v 2).1 - (T.v 0).1)) = 0 := by
    linear_combination ((T.v 1).1 - (T.v 0).1) * (h2 - h0) - ((T.v 2).1 - (T.v 0).1) * (h1 - h0)
  rcases mul_eq_zero.1 e1 with e1 | e1
  · rcases mul_eq_zero.1 e2 with e2 | e2
    · exact hp (Prod.ext e1 e2)
    · linarith
  · linarith

theorem u3h_carrier_subset_le (T : Triangle) {p : Plane} {r : ℝ}
    (h : ∀ i, planeDot p (T.v i) ≤ r) : T.carrier ⊆ {x | planeDot p x ≤ r} :=
  convexHull_min (by rintro _ ⟨i, rfl⟩; exact h i) (u3h_convex_le p r)

theorem u3h_carrier_subset_ge (T : Triangle) {p : Plane} {r : ℝ}
    (h : ∀ i, r ≤ planeDot p (T.v i)) : T.carrier ⊆ {x | r ≤ planeDot p x} :=
  convexHull_min (by rintro _ ⟨i, rfl⟩; exact h i) (u3h_convex_ge p r)

/-- The face of a triangle on a supporting line is the hull of the vertices on the line. -/
theorem u3h_carrier_inter_line (T : Triangle) {p : Plane} {r : ℝ}
    (h : ∀ i, planeDot p (T.v i) ≤ r) :
    T.carrier ∩ {x | planeDot p x = r} = convexHull ℝ (range T.v ∩ {x | planeDot p x = r}) := by
  apply Subset.antisymm
  · rintro x ⟨hx, hxr⟩
    simp only [mem_ofPred_eq] at hxr
    obtain ⟨a, b, c, ha, hb, hc, habc, rfl⟩ := (u3h_mem_carrier_iff T x).1 hx
    have hsum : a * (r - planeDot p (T.v 0)) + b * (r - planeDot p (T.v 1))
        + c * (r - planeDot p (T.v 2)) = 0 := by
      rw [u3h_planeDot_add, u3h_planeDot_combo, u3h_planeDot_smul] at hxr
      linear_combination r * habc - hxr
    have t0 : 0 ≤ a * (r - planeDot p (T.v 0)) := mul_nonneg ha (by linarith [h 0])
    have t1 : 0 ≤ b * (r - planeDot p (T.v 1)) := mul_nonneg hb (by linarith [h 1])
    have t2 : 0 ≤ c * (r - planeDot p (T.v 2)) := mul_nonneg hc (by linarith [h 2])
    have z0 : a = 0 ∨ planeDot p (T.v 0) = r := by
      rcases mul_eq_zero.1 (show a * (r - planeDot p (T.v 0)) = 0 by linarith) with e | e
      · exact Or.inl e
      · exact Or.inr (by linarith)
    have z1 : b = 0 ∨ planeDot p (T.v 1) = r := by
      rcases mul_eq_zero.1 (show b * (r - planeDot p (T.v 1)) = 0 by linarith) with e | e
      · exact Or.inl e
      · exact Or.inr (by linarith)
    have z2 : c = 0 ∨ planeDot p (T.v 2) = r := by
      rcases mul_eq_zero.1 (show c * (r - planeDot p (T.v 2)) = 0 by linarith) with e | e
      · exact Or.inl e
      · exact Or.inr (by linarith)
    -- some vertex is on the line
    have hex : ∃ i₀, planeDot p (T.v i₀) = r := by
      by_contra hno
      push Not at hno
      have a0 : a = 0 := z0.resolve_right (hno 0)
      have b0 : b = 0 := z1.resolve_right (hno 1)
      have c0 : c = 0 := z2.resolve_right (hno 2)
      linarith
    obtain ⟨i₀, hi₀⟩ := hex
    classical
    let z : Fin 3 → Plane := fun i => if planeDot p (T.v i) = r then T.v i else T.v i₀
    have hz : ∀ i, z i ∈ range T.v ∩ {x | planeDot p x = r} := by
      intro i
      simp only [z]
      split_ifs with hi
      · exact ⟨⟨i, rfl⟩, hi⟩
      · exact ⟨⟨i₀, rfl⟩, hi₀⟩
    have hw : ∀ i, (![a, b, c] : Fin 3 → ℝ) i • z i = (![a, b, c] : Fin 3 → ℝ) i • T.v i := by
      intro i
      simp only [z]
      split_ifs with hi
      · rfl
      · fin_cases i
        · simp [z0.resolve_right hi]
        · simp [z1.resolve_right hi]
        · simp [z2.resolve_right hi]
    refine mem_convexHull_of_exists_fintype (ι := Fin 3) ![a, b, c] z ?_ ?_ hz ?_
    · intro i; fin_cases i <;> simpa
    · simp [Fin.sum_univ_three]; linarith
    · simp only [Fin.sum_univ_three, hw]; simp
  · apply convexHull_min
    · rintro x ⟨hx, hxr⟩
      exact ⟨subset_convexHull ℝ _ hx, hxr⟩
    · exact (convex_convexHull ℝ _).inter (u3h_convex_eq p r)

theorem u3h_line_neg (p : Plane) (r : ℝ) :
    {x : Plane | planeDot (-p) x = -r} = {x | planeDot p x = r} := by
  ext x; simp only [mem_ofPred_eq, u3h_planeDot_neg_left]; constructor <;> intro h <;> linarith

theorem u3h_carrier_inter_line' (T : Triangle) {p : Plane} {r : ℝ}
    (h : ∀ i, r ≤ planeDot p (T.v i)) :
    T.carrier ∩ {x | planeDot p x = r} = convexHull ℝ (range T.v ∩ {x | planeDot p x = r}) := by
  rw [← u3h_line_neg p r]
  exact u3h_carrier_inter_line T (p := -p) (r := -r) (fun i => by
    rw [u3h_planeDot_neg_left]; linarith [h i])

/-! ### U3 helpers: separation of faces -/

theorem u3h_dual_eq (f : StrongDual ℝ Plane) (x : Plane) :
    f x = planeDot (f ((1 : ℝ), (0 : ℝ)), f ((0 : ℝ), (1 : ℝ))) x := by
  have hx : x = x.1 • ((1 : ℝ), (0 : ℝ)) + x.2 • ((0 : ℝ), (1 : ℝ)) := by ext <;> simp
  conv_lhs => rw [hx]
  rw [map_add, map_smul, map_smul]
  simp [planeDot, mul_comm]

/-- Hahn–Banach for a compact convex body and a convex set missing its interior. -/
theorem u3h_separate_of_disjoint {A B : Set Plane} (hA : Convex ℝ A) (hAc : IsCompact A)
    (hAi : (interior A).Nonempty) (hB : Convex ℝ B) (hBne : B.Nonempty)
    (hdisj : Disjoint (interior A) B) :
    ∃ (p : Plane) (r : ℝ), p ≠ 0 ∧ (∀ x ∈ A, planeDot p x ≤ r) ∧ ∀ x ∈ B, r ≤ planeDot p x := by
  obtain ⟨f, u, hf1, hf2⟩ := geometric_hahn_banach_open hA.interior isOpen_interior hB hdisj
  refine ⟨(f ((1 : ℝ), (0 : ℝ)), f ((0 : ℝ), (1 : ℝ))), u, ?_, ?_, ?_⟩
  · intro hp
    obtain ⟨a, ha⟩ := hAi
    obtain ⟨b, hb⟩ := hBne
    have h1 := hf1 a ha
    have h2 := hf2 b hb
    rw [u3h_dual_eq, hp, u3h_planeDot_zero_left] at h1 h2
    linarith
  · intro x hx
    rw [← u3h_dual_eq]
    have hcl : closure (interior A) = A := by
      rw [hA.closure_interior_eq_closure_of_nonempty_interior hAi, hAc.isClosed.closure_eq]
    have hx' : x ∈ closure (interior A) := by rw [hcl]; exact hx
    exact closure_minimal (fun y hy => (hf1 y hy).le) (isClosed_le f.continuous continuous_const) hx'
  · intro x hx
    rw [← u3h_dual_eq]
    exact hf2 x hx

/-- If a vertex of `T` is not a vertex of `T'`, the interior of `T` misses `T'`. -/
theorem u3h_interior_disjoint_of_vertex {X : Set Plane} (K : Triangulation X) {T T' : Triangle}
    (hT : T ∈ K.faces) (hT' : T' ∈ K.faces) (i : Fin 3) (hi : T.v i ∉ range T'.v) :
    Disjoint (interior T.carrier) T'.carrier := by
  have hinter := K.inter T hT T' hT'
  have hsub : range T.v ∩ range T'.v ⊆ {T.v (i + 1), T.v (i + 2)} := by
    rintro y ⟨⟨j, rfl⟩, hy'⟩
    have hne : T.v j ≠ T.v i := fun e => hi (e ▸ hy')
    rcases u3h_other T i j hne with e | e <;> simp [e]
  have hfr : T.carrier ∩ T'.carrier ⊆ frontier T.carrier := by
    rw [hinter, U1_frontier_triangle]
    intro y hy
    have := convexHull_mono hsub hy
    rw [convexHull_pair] at this
    refine mem_iUnion.2 ⟨i + 1, ?_⟩
    have e : i + 1 + 1 = i + 2 := by fin_cases i <;> rfl
    rw [e]; exact this
  rw [Set.disjoint_left]
  intro y hy hy'
  have hyT : y ∈ T.carrier := interior_subset hy
  exact (Set.disjoint_left.1 disjoint_interior_frontier) hy (hfr ⟨hyT, hy'⟩)

/-- Two faces of a triangulation with distinct carriers are separated by a line. -/
theorem u3h_faces_separated {X : Set Plane} (K : Triangulation X) {T T' : Triangle}
    (hT : T ∈ K.faces) (hT' : T' ∈ K.faces) (hne : T.carrier ≠ T'.carrier) :
    ∃ (p : Plane) (r : ℝ), p ≠ 0 ∧ (∀ i, planeDot p (T.v i) ≤ r) ∧ ∀ i, r ≤ planeDot p (T'.v i) := by
  have key : ∀ (S S' : Triangle), S ∈ K.faces → S' ∈ K.faces → (∃ i, S.v i ∉ range S'.v) →
      ∃ (p : Plane) (r : ℝ), p ≠ 0 ∧ (∀ i, planeDot p (S.v i) ≤ r) ∧ ∀ i, r ≤ planeDot p (S'.v i) := by
    intro S S' hS hS' ⟨i, hi⟩
    obtain ⟨p, r, hp, h1, h2⟩ := u3h_separate_of_disjoint (U1_triangle_convex S)
      (U1_triangle_isCompact S) (U1_triangle_interior_nonempty S) (U1_triangle_convex S')
      ⟨S'.v 0, subset_convexHull ℝ _ ⟨0, rfl⟩⟩ (u3h_interior_disjoint_of_vertex K hS hS' i hi)
    exact ⟨p, r, hp, fun j => h1 _ (subset_convexHull ℝ _ ⟨j, rfl⟩),
      fun j => h2 _ (subset_convexHull ℝ _ ⟨j, rfl⟩)⟩
  by_cases h : ∃ i, T.v i ∉ range T'.v
  · exact key T T' hT hT' h
  · push Not at h
    have h' : ∃ i, T'.v i ∉ range T.v := by
      by_contra h'
      push Not at h'
      apply hne
      have : range T.v = range T'.v := by
        apply Subset.antisymm
        · rintro _ ⟨i, rfl⟩; exact h i
        · rintro _ ⟨i, rfl⟩; exact h' i
      unfold Triangle.carrier; rw [this]
    obtain ⟨p, r, hp, h1, h2⟩ := key T' T hT' hT h'
    refine ⟨-p, -r, neg_ne_zero.2 hp, fun i => ?_, fun i => ?_⟩
    · rw [u3h_planeDot_neg_left]; linarith [h2 i]
    · rw [u3h_planeDot_neg_left]; linarith [h1 i]

/-- Separated triangles meet inside their faces on the separating line. -/
theorem u3h_inter_of_separated (Δ Δ' : Triangle) {p : Plane} {r : ℝ}
    (h : ∀ i, planeDot p (Δ.v i) ≤ r) (h' : ∀ i, r ≤ planeDot p (Δ'.v i)) :
    Δ.carrier ∩ Δ'.carrier = convexHull ℝ (range Δ.v ∩ {x | planeDot p x = r}) ∩
      convexHull ℝ (range Δ'.v ∩ {x | planeDot p x = r}) := by
  rw [← u3h_carrier_inter_line Δ h, ← u3h_carrier_inter_line' Δ' h']
  ext x
  simp only [mem_inter_iff, mem_ofPred_eq]
  constructor
  · rintro ⟨hx, hx'⟩
    have h1 := u3h_carrier_subset_le Δ h hx
    have h2 := u3h_carrier_subset_ge Δ' h' hx'
    simp only [mem_ofPred_eq] at h1 h2
    exact ⟨⟨hx, le_antisymm h1 h2⟩, hx', le_antisymm h1 h2⟩
  · rintro ⟨⟨hx, _⟩, hx', _⟩
    exact ⟨hx, hx'⟩

/-- The vertices of a triangle on a genuine line: none, or a pair (possibly repeated). -/
theorem u3h_vertices_on_line (Δ : Triangle) {p : Plane} {r : ℝ} (hp : p ≠ 0) :
    range Δ.v ∩ {x | planeDot p x = r} = ∅ ∨
      ∃ a b : Plane, a ∈ range Δ.v ∧ b ∈ range Δ.v ∧ planeDot p a = r ∧ planeDot p b = r ∧
        range Δ.v ∩ {x | planeDot p x = r} = {a, b} := by
  have hnot : ¬ (planeDot p (Δ.v 0) = r ∧ planeDot p (Δ.v 1) = r ∧ planeDot p (Δ.v 2) = r) := by
    rintro ⟨h0, h1, h2⟩
    exact u3h_not_all_on_line Δ hp (fun i => by fin_cases i <;> assumption)
  by_cases h0 : planeDot p (Δ.v 0) = r <;> by_cases h1 : planeDot p (Δ.v 1) = r <;>
    by_cases h2 : planeDot p (Δ.v 2) = r
  · exact absurd ⟨h0, h1, h2⟩ hnot
  · refine Or.inr ⟨Δ.v 0, Δ.v 1, ⟨0, rfl⟩, ⟨1, rfl⟩, h0, h1, ?_⟩
    ext x; simp only [u3h_range_v, mem_inter_iff, mem_insert_iff, mem_singleton_iff, mem_ofPred_eq]
    constructor
    · rintro ⟨(rfl | rfl | rfl), hx⟩ <;> simp_all
    · rintro (rfl | rfl) <;> simp_all
  · refine Or.inr ⟨Δ.v 0, Δ.v 2, ⟨0, rfl⟩, ⟨2, rfl⟩, h0, h2, ?_⟩
    ext x; simp only [u3h_range_v, mem_inter_iff, mem_insert_iff, mem_singleton_iff, mem_ofPred_eq]
    constructor
    · rintro ⟨(rfl | rfl | rfl), hx⟩ <;> simp_all
    · rintro (rfl | rfl) <;> simp_all
  · refine Or.inr ⟨Δ.v 0, Δ.v 0, ⟨0, rfl⟩, ⟨0, rfl⟩, h0, h0, ?_⟩
    ext x; simp only [u3h_range_v, mem_inter_iff, mem_insert_iff, mem_singleton_iff, mem_ofPred_eq]
    constructor
    · rintro ⟨(rfl | rfl | rfl), hx⟩ <;> simp_all
    · rintro (rfl | rfl) <;> simp_all
  · refine Or.inr ⟨Δ.v 1, Δ.v 2, ⟨1, rfl⟩, ⟨2, rfl⟩, h1, h2, ?_⟩
    ext x; simp only [u3h_range_v, mem_inter_iff, mem_insert_iff, mem_singleton_iff, mem_ofPred_eq]
    constructor
    · rintro ⟨(rfl | rfl | rfl), hx⟩ <;> simp_all
    · rintro (rfl | rfl) <;> simp_all
  · refine Or.inr ⟨Δ.v 1, Δ.v 1, ⟨1, rfl⟩, ⟨1, rfl⟩, h1, h1, ?_⟩
    ext x; simp only [u3h_range_v, mem_inter_iff, mem_insert_iff, mem_singleton_iff, mem_ofPred_eq]
    constructor
    · rintro ⟨(rfl | rfl | rfl), hx⟩ <;> simp_all
    · rintro (rfl | rfl) <;> simp_all
  · refine Or.inr ⟨Δ.v 2, Δ.v 2, ⟨2, rfl⟩, ⟨2, rfl⟩, h2, h2, ?_⟩
    ext x; simp only [u3h_range_v, mem_inter_iff, mem_insert_iff, mem_singleton_iff, mem_ofPred_eq]
    constructor
    · rintro ⟨(rfl | rfl | rfl), hx⟩ <;> simp_all
    · rintro (rfl | rfl) <;> simp_all
  · left
    ext x; simp only [u3h_range_v, mem_inter_iff, mem_insert_iff, mem_singleton_iff, mem_ofPred_eq,
      mem_empty_iff_false, iff_false, not_and]
    rintro (rfl | rfl | rfl) <;> assumption

/-! ### U3 helpers: coordinates on a line and segment combinatorics -/

/-- A direction vector of the lines `planeDot p x = r`. -/
def u3h_dir (p : Plane) : Plane := (-p.2, p.1)

theorem u3h_planeDot_dir_self (p : Plane) :
    planeDot (u3h_dir p) (u3h_dir p) = p.1 ^ 2 + p.2 ^ 2 := by
  simp [u3h_dir, planeDot]; ring

theorem u3h_dir_pos {p : Plane} (hp : p ≠ 0) : 0 < planeDot (u3h_dir p) (u3h_dir p) := by
  rw [u3h_planeDot_dir_self]
  have : p.1 ≠ 0 ∨ p.2 ≠ 0 := by
    by_contra h; push Not at h; exact hp (Prod.ext h.1 h.2)
  rcases this with h | h
  · have := mul_self_pos.2 h; nlinarith [sq_nonneg p.2]
  · have := mul_self_pos.2 h; nlinarith [sq_nonneg p.1]

/-- Two points of a line differ by a multiple of the direction. -/
theorem u3h_on_line_eq {p : Plane} (hp : p ≠ 0) {r : ℝ} {x y : Plane} (hx : planeDot p x = r)
    (hy : planeDot p y = r) :
    x = y + (planeDot (u3h_dir p) (x - y) / planeDot (u3h_dir p) (u3h_dir p)) • u3h_dir p := by
  have hN := u3h_dir_pos hp
  have hw : p.1 * (x.1 - y.1) + p.2 * (x.2 - y.2) = 0 := by
    unfold planeDot at hx hy; linarith
  have key : x - y = (planeDot (u3h_dir p) (x - y) / planeDot (u3h_dir p) (u3h_dir p)) • u3h_dir p := by
    rw [u3h_planeDot_dir_self] at hN ⊢
    ext
    · simp only [Prod.smul_fst, smul_eq_mul, u3h_dir, planeDot, Prod.fst_sub, Prod.snd_sub]
      rw [div_mul_eq_mul_div, eq_div_iff hN.ne']
      linear_combination p.1 * hw
    · simp only [Prod.smul_snd, smul_eq_mul, u3h_dir, planeDot, Prod.fst_sub, Prod.snd_sub]
      rw [div_mul_eq_mul_div, eq_div_iff hN.ne']
      linear_combination p.2 * hw
  rw [← key]; abel

theorem u3h_coord_injOn {p : Plane} (hp : p ≠ 0) {r : ℝ} {x y : Plane} (hx : planeDot p x = r)
    (hy : planeDot p y = r) (h : planeDot (u3h_dir p) x = planeDot (u3h_dir p) y) : x = y := by
  have := u3h_on_line_eq hp hx hy
  rw [u3h_planeDot_sub, h, sub_self, zero_div, zero_smul, add_zero] at this
  exact this

theorem u3h_mem_segment_iff_coord {p : Plane} (hp : p ≠ 0) {r : ℝ} {a b x : Plane}
    (ha : planeDot p a = r) (hb : planeDot p b = r) (hx : planeDot p x = r) :
    x ∈ segment ℝ a b ↔
      planeDot (u3h_dir p) x ∈ segment ℝ (planeDot (u3h_dir p) a) (planeDot (u3h_dir p) b) := by
  constructor
  · rintro ⟨α, β, hα, hβ, hαβ, rfl⟩
    exact ⟨α, β, hα, hβ, hαβ, by rw [u3h_planeDot_combo, smul_eq_mul, smul_eq_mul]⟩
  · rintro ⟨α, β, hα, hβ, hαβ, h⟩
    have hy : planeDot p (α • a + β • b) = r := by
      rw [u3h_planeDot_combo, ha, hb]; linear_combination r * hαβ
    have : α • a + β • b = x :=
      u3h_coord_injOn hp hy hx (by rw [u3h_planeDot_combo]; exact h)
    exact ⟨α, β, hα, hβ, hαβ, this⟩

theorem u3h_real_comb_ordered {a1 a2 b1 b2 ξ : ℝ} (_ha : a1 ≤ a2) (_hb : b1 ≤ b2)
    (hξa : ξ ∈ Icc a1 a2) (hξb : ξ ∈ Icc b1 b2)
    (hA : ∀ y, (y = b1 ∨ y = b2) → y ∈ Icc a1 a2 → (y = a1 ∨ y = a2))
    (hB : ∀ y, (y = a1 ∨ y = a2) → y ∈ Icc b1 b2 → (y = b1 ∨ y = b2)) :
    ∃ u v : ℝ, ((u = a1 ∨ u = a2) ∧ (u = b1 ∨ u = b2)) ∧ ((v = a1 ∨ v = a2) ∧ (v = b1 ∨ v = b2)) ∧
      u ≤ ξ ∧ ξ ≤ v := by
  obtain ⟨h1, h2⟩ := hξa; obtain ⟨h3, h4⟩ := hξb
  rcases le_total a1 b1 with hab | hab <;> rcases le_total a2 b2 with hcd | hcd
  · exact ⟨b1, a2, ⟨hA b1 (Or.inl rfl) ⟨hab, by linarith⟩, Or.inl rfl⟩,
      ⟨Or.inr rfl, hB a2 (Or.inr rfl) ⟨by linarith, hcd⟩⟩, h3, h2⟩
  · exact ⟨b1, b2, ⟨hA b1 (Or.inl rfl) ⟨hab, by linarith⟩, Or.inl rfl⟩,
      ⟨hA b2 (Or.inr rfl) ⟨by linarith, hcd⟩, Or.inr rfl⟩, h3, h4⟩
  · exact ⟨a1, a2, ⟨Or.inl rfl, hB a1 (Or.inl rfl) ⟨hab, by linarith⟩⟩,
      ⟨Or.inr rfl, hB a2 (Or.inr rfl) ⟨by linarith, hcd⟩⟩, h1, h2⟩
  · exact ⟨a1, b2, ⟨Or.inl rfl, hB a1 (Or.inl rfl) ⟨hab, by linarith⟩⟩,
      ⟨hA b2 (Or.inr rfl) ⟨by linarith, hcd⟩, Or.inr rfl⟩, h1, h4⟩

theorem u3h_real_comb {a1 a2 b1 b2 ξ : ℝ} (hξa : ξ ∈ segment ℝ a1 a2) (hξb : ξ ∈ segment ℝ b1 b2)
    (hA : ∀ y, (y = b1 ∨ y = b2) → y ∈ segment ℝ a1 a2 → (y = a1 ∨ y = a2))
    (hB : ∀ y, (y = a1 ∨ y = a2) → y ∈ segment ℝ b1 b2 → (y = b1 ∨ y = b2)) :
    ∃ u v : ℝ, ((u = a1 ∨ u = a2) ∧ (u = b1 ∨ u = b2)) ∧ ((v = a1 ∨ v = a2) ∧ (v = b1 ∨ v = b2)) ∧
      ξ ∈ segment ℝ u v := by
  rcases le_total a1 a2 with h12 | h12 <;> rcases le_total b1 b2 with h34 | h34
  · have ea : segment ℝ a1 a2 = Icc a1 a2 := segment_eq_Icc h12
    have eb : segment ℝ b1 b2 = Icc b1 b2 := segment_eq_Icc h34
    rw [ea] at hξa hA; rw [eb] at hξb hB
    obtain ⟨u, v, hu, hv, huξ, hξv⟩ := u3h_real_comb_ordered h12 h34 hξa hξb hA hB
    exact ⟨u, v, hu, hv, by rw [segment_eq_Icc (huξ.trans hξv)]; exact ⟨huξ, hξv⟩⟩
  · have ea : segment ℝ a1 a2 = Icc a1 a2 := segment_eq_Icc h12
    have eb : segment ℝ b1 b2 = Icc b2 b1 := by rw [segment_symm]; exact segment_eq_Icc h34
    rw [ea] at hξa hA; rw [eb] at hξb hB
    obtain ⟨u, v, hu, hv, huξ, hξv⟩ := u3h_real_comb_ordered h12 h34 hξa hξb
      (fun y hy => hA y hy.symm) (fun y hy hyI => (hB y hy hyI).symm)
    exact ⟨u, v, ⟨hu.1, hu.2.symm⟩, ⟨hv.1, hv.2.symm⟩,
      by rw [segment_eq_Icc (huξ.trans hξv)]; exact ⟨huξ, hξv⟩⟩
  · have ea : segment ℝ a1 a2 = Icc a2 a1 := by rw [segment_symm]; exact segment_eq_Icc h12
    have eb : segment ℝ b1 b2 = Icc b1 b2 := segment_eq_Icc h34
    rw [ea] at hξa hA; rw [eb] at hξb hB
    obtain ⟨u, v, hu, hv, huξ, hξv⟩ := u3h_real_comb_ordered h12 h34 hξa hξb
      (fun y hy hyI => (hA y hy hyI).symm) (fun y hy => hB y hy.symm)
    exact ⟨u, v, ⟨hu.1.symm, hu.2⟩, ⟨hv.1.symm, hv.2⟩,
      by rw [segment_eq_Icc (huξ.trans hξv)]; exact ⟨huξ, hξv⟩⟩
  · have ea : segment ℝ a1 a2 = Icc a2 a1 := by rw [segment_symm]; exact segment_eq_Icc h12
    have eb : segment ℝ b1 b2 = Icc b2 b1 := by rw [segment_symm]; exact segment_eq_Icc h34
    rw [ea] at hξa hA; rw [eb] at hξb hB
    obtain ⟨u, v, hu, hv, huξ, hξv⟩ := u3h_real_comb_ordered h12 h34 hξa hξb
      (fun y hy hyI => (hA y hy.symm hyI).symm) (fun y hy hyI => (hB y hy.symm hyI).symm)
    exact ⟨u, v, ⟨hu.1.symm, hu.2.symm⟩, ⟨hv.1.symm, hv.2.symm⟩,
      by rw [segment_eq_Icc (huξ.trans hξv)]; exact ⟨huξ, hξv⟩⟩

/-- Two segments on a line whose endpoints are compatible meet in the hull of the common endpoints. -/
theorem u3h_segment_inter_segment {p : Plane} {r : ℝ} (hp : p ≠ 0) {a1 a2 b1 b2 : Plane}
    (ha1 : planeDot p a1 = r) (ha2 : planeDot p a2 = r) (hb1 : planeDot p b1 = r)
    (hb2 : planeDot p b2 = r)
    (hA : ∀ y, (y = b1 ∨ y = b2) → y ∈ segment ℝ a1 a2 → (y = a1 ∨ y = a2))
    (hB : ∀ y, (y = a1 ∨ y = a2) → y ∈ segment ℝ b1 b2 → (y = b1 ∨ y = b2)) :
    segment ℝ a1 a2 ∩ segment ℝ b1 b2 = convexHull ℝ ({a1, a2} ∩ {b1, b2} : Set Plane) := by
  apply Subset.antisymm
  · rintro x ⟨hxa, hxb⟩
    have hx : planeDot p x = r := (u3h_convex_eq p r).segment_subset ha1 ha2 hxa
    have hxa' := (u3h_mem_segment_iff_coord hp ha1 ha2 hx).1 hxa
    have hxb' := (u3h_mem_segment_iff_coord hp hb1 hb2 hx).1 hxb
    have hA' : ∀ y, (y = planeDot (u3h_dir p) b1 ∨ y = planeDot (u3h_dir p) b2) →
        y ∈ segment ℝ (planeDot (u3h_dir p) a1) (planeDot (u3h_dir p) a2) →
        (y = planeDot (u3h_dir p) a1 ∨ y = planeDot (u3h_dir p) a2) := by
      rintro y (rfl | rfl) hy
      · rcases hA b1 (Or.inl rfl) ((u3h_mem_segment_iff_coord hp ha1 ha2 hb1).2 hy) with e | e <;>
          simp [e]
      · rcases hA b2 (Or.inr rfl) ((u3h_mem_segment_iff_coord hp ha1 ha2 hb2).2 hy) with e | e <;>
          simp [e]
    have hB' : ∀ y, (y = planeDot (u3h_dir p) a1 ∨ y = planeDot (u3h_dir p) a2) →
        y ∈ segment ℝ (planeDot (u3h_dir p) b1) (planeDot (u3h_dir p) b2) →
        (y = planeDot (u3h_dir p) b1 ∨ y = planeDot (u3h_dir p) b2) := by
      rintro y (rfl | rfl) hy
      · rcases hB a1 (Or.inl rfl) ((u3h_mem_segment_iff_coord hp hb1 hb2 ha1).2 hy) with e | e <;>
          simp [e]
      · rcases hB a2 (Or.inr rfl) ((u3h_mem_segment_iff_coord hp hb1 hb2 ha2).2 hy) with e | e <;>
          simp [e]
    obtain ⟨u, v, ⟨hu1, hu2⟩, ⟨hv1, hv2⟩, hξ⟩ := u3h_real_comb hxa' hxb' hA' hB'
    have pick : ∀ w : ℝ, (w = planeDot (u3h_dir p) a1 ∨ w = planeDot (u3h_dir p) a2) →
        (w = planeDot (u3h_dir p) b1 ∨ w = planeDot (u3h_dir p) b2) →
        ∃ W : Plane, W ∈ ({a1, a2} ∩ {b1, b2} : Set Plane) ∧ planeDot p W = r ∧
          planeDot (u3h_dir p) W = w := by
      rintro w (rfl | rfl) h2
      · refine ⟨a1, ⟨by simp, ?_⟩, ha1, rfl⟩
        rcases h2 with h | h
        · simp [u3h_coord_injOn hp ha1 hb1 h]
        · simp [u3h_coord_injOn hp ha1 hb2 h]
      · refine ⟨a2, ⟨by simp, ?_⟩, ha2, rfl⟩
        rcases h2 with h | h
        · simp [u3h_coord_injOn hp ha2 hb1 h]
        · simp [u3h_coord_injOn hp ha2 hb2 h]
    obtain ⟨U, hU, hUr, hUκ⟩ := pick u hu1 hu2
    obtain ⟨V, hV, hVr, hVκ⟩ := pick v hv1 hv2
    have : x ∈ segment ℝ U V :=
      (u3h_mem_segment_iff_coord hp hUr hVr hx).2 (by rw [hUκ, hVκ]; exact hξ)
    exact segment_subset_convexHull hU hV this
  · apply convexHull_min
    · rintro y ⟨hy1, hy2⟩
      simp only [mem_insert_iff, mem_singleton_iff] at hy1 hy2
      refine ⟨?_, ?_⟩
      · rcases hy1 with rfl | rfl
        · exact left_mem_segment ℝ _ _
        · exact right_mem_segment ℝ _ _
      · rcases hy2 with rfl | rfl
        · exact left_mem_segment ℝ _ _
        · exact right_mem_segment ℝ _ _
    · exact (convex_segment _ _).inter (convex_segment _ _)

/-- **Gluing criterion**: a family of triangles, pairwise separated when distinct, in which every
vertex of one triangle lying in another is a vertex of it, has face-to-face intersections. -/
theorem u3h_inter_of_family {F : Set Triangle}
    (hsep : ∀ Δ ∈ F, ∀ Δ' ∈ F, Δ.carrier ≠ Δ'.carrier → ∃ (p : Plane) (r : ℝ), p ≠ 0 ∧
      (∀ i, planeDot p (Δ.v i) ≤ r) ∧ ∀ i, r ≤ planeDot p (Δ'.v i))
    (hvert : ∀ Δ ∈ F, ∀ Δ' ∈ F, ∀ j, Δ'.v j ∈ Δ.carrier → Δ'.v j ∈ range Δ.v) :
    ∀ Δ ∈ F, ∀ Δ' ∈ F, Δ.carrier ∩ Δ'.carrier = convexHull ℝ (range Δ.v ∩ range Δ'.v) := by
  intro Δ hΔ Δ' hΔ'
  by_cases hc : Δ.carrier = Δ'.carrier
  · have hr : range Δ.v = range Δ'.v := by
      apply Subset.antisymm
      · rintro _ ⟨j, rfl⟩
        exact hvert Δ' hΔ' Δ hΔ j (hc ▸ subset_convexHull ℝ _ ⟨j, rfl⟩)
      · rintro _ ⟨j, rfl⟩
        exact hvert Δ hΔ Δ' hΔ' j (hc.symm ▸ subset_convexHull ℝ _ ⟨j, rfl⟩)
    rw [← hc, inter_self, hr, inter_self]; exact hc
  obtain ⟨p, r, hp, h1, h2⟩ := hsep Δ hΔ Δ' hΔ' hc
  rw [u3h_inter_of_separated Δ Δ' h1 h2]
  have hcommon : ∀ w, w ∈ range Δ.v → w ∈ range Δ'.v → planeDot p w = r := by
    rintro w ⟨i, rfl⟩ hw'
    obtain ⟨j, hj⟩ := hw'
    have := h2 j; rw [hj] at this
    exact le_antisymm (h1 i) this
  rcases u3h_vertices_on_line Δ (r := r) hp with hA | ⟨a1, a2, ha1, ha2, ha1r, ha2r, hA⟩
  · rw [hA, convexHull_empty, empty_inter]
    have : range Δ.v ∩ range Δ'.v = ∅ := by
      rw [eq_empty_iff_forall_notMem]
      rintro w ⟨hw, hw'⟩
      have : w ∈ range Δ.v ∩ {x | planeDot p x = r} := ⟨hw, hcommon w hw hw'⟩
      rw [hA] at this; exact this
    rw [this, convexHull_empty]
  rcases u3h_vertices_on_line Δ' (r := r) hp with hB | ⟨b1, b2, hb1, hb2, hb1r, hb2r, hB⟩
  · rw [hB, convexHull_empty, inter_empty]
    have : range Δ.v ∩ range Δ'.v = ∅ := by
      rw [eq_empty_iff_forall_notMem]
      rintro w ⟨hw, hw'⟩
      have : w ∈ range Δ'.v ∩ {x | planeDot p x = r} := ⟨hw', hcommon w hw hw'⟩
      rw [hB] at this; exact this
    rw [this, convexHull_empty]
  rw [hA, hB, convexHull_pair, convexHull_pair]
  have hA' : ∀ y, (y = b1 ∨ y = b2) → y ∈ segment ℝ a1 a2 → (y = a1 ∨ y = a2) := by
    intro y hy hys
    have hyΔ : y ∈ Δ.carrier :=
      segment_subset_convexHull ha1 ha2 hys
    have hy' : y ∈ range Δ'.v := by rcases hy with rfl | rfl <;> assumption
    have hyr : planeDot p y = r := by rcases hy with rfl | rfl <;> assumption
    obtain ⟨j, rfl⟩ := hy'
    have := hvert Δ hΔ Δ' hΔ' j hyΔ
    have hmem : Δ'.v j ∈ range Δ.v ∩ {x | planeDot p x = r} := ⟨this, hyr⟩
    rw [hA] at hmem
    simpa using hmem
  have hB' : ∀ y, (y = a1 ∨ y = a2) → y ∈ segment ℝ b1 b2 → (y = b1 ∨ y = b2) := by
    intro y hy hys
    have hyΔ : y ∈ Δ'.carrier :=
      segment_subset_convexHull hb1 hb2 hys
    have hy' : y ∈ range Δ.v := by rcases hy with rfl | rfl <;> assumption
    have hyr : planeDot p y = r := by rcases hy with rfl | rfl <;> assumption
    obtain ⟨j, rfl⟩ := hy'
    have := hvert Δ' hΔ' Δ hΔ j hyΔ
    have hmem : Δ.v j ∈ range Δ'.v ∩ {x | planeDot p x = r} := ⟨this, hyr⟩
    rw [hB] at hmem
    simpa using hmem
  rw [u3h_segment_inter_segment hp ha1r ha2r hb1r hb2r hA' hB']
  congr 1
  apply Subset.antisymm
  · rintro w ⟨hw1, hw2⟩
    simp only [mem_insert_iff, mem_singleton_iff] at hw1 hw2
    refine ⟨?_, ?_⟩
    · rcases hw1 with rfl | rfl <;> assumption
    · rcases hw2 with rfl | rfl <;> assumption
  · rintro w ⟨hw, hw'⟩
    have hr := hcommon w hw hw'
    have m1 : w ∈ range Δ.v ∩ {x | planeDot p x = r} := ⟨hw, hr⟩
    have m2 : w ∈ range Δ'.v ∩ {x | planeDot p x = r} := ⟨hw', hr⟩
    rw [hA] at m1; rw [hB] at m2
    exact ⟨m1, m2⟩

/-! ### U3 helpers: splitting one triangle along one line -/

theorem u3h_mem_carrier_of_homog (T : Triangle) {a b c s : ℝ} {x : Plane} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : 0 ≤ c) (hs : 0 < s) (hsum : a + b + c = s)
    (h : a • T.v 0 + b • T.v 1 + c • T.v 2 = s • x) : x ∈ T.carrier := by
  rw [u3h_mem_carrier_iff]
  refine ⟨a / s, b / s, c / s, div_nonneg ha hs.le, div_nonneg hb hs.le, div_nonneg hc hs.le, ?_, ?_⟩
  · rw [← add_div, ← add_div, hsum, div_self hs.ne']
  · have : (a / s) • T.v 0 + (b / s) • T.v 1 + (c / s) • T.v 2 =
        s⁻¹ • (a • T.v 0 + b • T.v 1 + c • T.v 2) := by
      simp only [smul_add, smul_smul, div_eq_inv_mul]
    rw [this, h, smul_smul, inv_mul_cancel₀ hs.ne', one_smul]

theorem u3h_not_mem_of_lt (Δ : Triangle) {p : Plane} {r : ℝ} (h : ∀ i, planeDot p (Δ.v i) ≤ r)
    {w : Plane} (hw : r < planeDot p w) : w ∉ Δ.carrier :=
  fun hm => absurd (u3h_carrier_subset_le Δ h hm) (not_le.2 hw)

theorem u3h_not_mem_of_gt (Δ : Triangle) {p : Plane} {r : ℝ} (h : ∀ i, r ≤ planeDot p (Δ.v i))
    {w : Plane} (hw : planeDot p w < r) : w ∉ Δ.carrier :=
  fun hm => absurd (u3h_carrier_subset_ge Δ h hm) (not_le.2 hw)

theorem u3h_det_eq_planeDot (u w : Plane) : det u w = planeDot (u3h_dir u) w := by
  simp [det, planeDot, u3h_dir]; ring

theorem u3h_dir_ne_zero {u : Plane} (hu : u ≠ 0) : u3h_dir u ≠ 0 := by
  intro h
  apply hu
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  simp [u3h_dir] at h1 h2
  exact Prod.ext h2 h1

theorem u3h_inter_self_face (Δ : Triangle) :
    Δ.carrier ∩ Δ.carrier = convexHull ℝ (range Δ.v ∩ range Δ.v) := by
  rw [inter_self, inter_self]; rfl

/-- The crossing point of the line `planeDot p x = r` with the segment `[A, B]`. -/
noncomputable def u3h_cross (p : Plane) (r : ℝ) (A B : Plane) : Plane :=
  (1 - (r - planeDot p A) / (planeDot p B - planeDot p A)) • A +
    ((r - planeDot p A) / (planeDot p B - planeDot p A)) • B

theorem u3h_cross_spec (p : Plane) (r : ℝ) {A B : Plane} (hAB : planeDot p A ≠ planeDot p B) :
    ∃ α : ℝ, u3h_cross p r A B = (1 - α) • A + α • B ∧
      α * (planeDot p B - planeDot p A) = r - planeDot p A :=
  ⟨_, rfl, div_mul_cancel₀ _ (sub_ne_zero.2 hAB.symm)⟩

theorem u3h_cross_param_pos {hA hB r α : ℝ} (hopp : (hA < r ∧ r < hB) ∨ (hB < r ∧ r < hA))
    (hα : α * (hB - hA) = r - hA) : 0 < α ∧ α < 1 := by
  rcases hopp with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have hd : 0 < hB - hA := by linarith
    constructor
    · by_contra h; push Not at h; nlinarith
    · by_contra h; push Not at h; nlinarith
  · have hd : hB - hA < 0 := by linarith
    constructor
    · by_contra h; push Not at h; nlinarith
    · by_contra h; push Not at h; nlinarith

theorem u3h_mem_openSegment_of_param {A B : Plane} {α : ℝ} (h0 : 0 < α) (h1 : α < 1) :
    (1 - α) • A + α • B ∈ openSegment ℝ A B :=
  ⟨1 - α, α, by linarith, h0, by ring, rfl⟩

theorem u3h_mem_segment_of_param {A B : Plane} {α : ℝ} (h0 : 0 ≤ α) (h1 : α ≤ 1) :
    (1 - α) • A + α • B ∈ segment ℝ A B :=
  ⟨1 - α, α, by linarith, h0, by ring, rfl⟩

theorem u3h_planeDot_param (p A B : Plane) (α : ℝ) :
    planeDot p ((1 - α) • A + α • B) = planeDot p A + α * (planeDot p B - planeDot p A) := by
  rw [u3h_planeDot_combo]; ring

theorem u3h_cross_unique {p : Plane} {r : ℝ} {A B : Plane} (hAB : planeDot p A ≠ planeDot p B)
    {α : ℝ} (hα : α * (planeDot p B - planeDot p A) = r - planeDot p A) {x : Plane}
    (hx : x ∈ openSegment ℝ A B) (hxr : planeDot p x = r) : x = (1 - α) • A + α • B := by
  obtain ⟨a, b, _, _, hab, rfl⟩ := hx
  have hab' : a = 1 - b := by linarith
  subst hab'
  rw [u3h_planeDot_param] at hxr
  have : (b - α) * (planeDot p B - planeDot p A) = 0 := by linear_combination hxr - hα
  rcases mul_eq_zero.1 this with h | h
  · have : b = α := by linarith
    rw [this]
  · exact absurd (sub_eq_zero.1 h) hAB.symm

/-- Opposite strict signs at the two ends of edge `i`. -/
def u3h_Opp (T : Triangle) (p : Plane) (r : ℝ) (i : Fin 3) : Prop :=
  (planeDot p (T.v i) < r ∧ r < planeDot p (T.v (i + 1))) ∨
    (r < planeDot p (T.v i) ∧ planeDot p (T.v (i + 1)) < r)

/-- Specification of the pieces of `T` cut by the line `planeDot p x = r`. -/
structure u3h_SplitSpec (T : Triangle) (p : Plane) (r : ℝ) (F : Set Triangle) : Prop where
  finite : F.Finite
  cover : (⋃ Δ ∈ F, Δ.carrier) = T.carrier
  inter : ∀ Δ ∈ F, ∀ Δ' ∈ F, Δ.carrier ∩ Δ'.carrier = convexHull ℝ (range Δ.v ∩ range Δ'.v)
  side : ∀ Δ ∈ F, (∀ j, planeDot p (Δ.v j) ≤ r) ∨ (∀ j, r ≤ planeDot p (Δ.v j))
  vert : ∀ Δ ∈ F, ∀ j, (∃ i, Δ.v j = T.v i) ∨
    (∃ i, Δ.v j ∈ openSegment ℝ (T.v i) (T.v (i + 1)) ∧ planeDot p (Δ.v j) = r ∧ u3h_Opp T p r i)
  old : ∀ i, ∃ Δ ∈ F, ∃ j, Δ.v j = T.v i
  cross : ∀ i, u3h_Opp T p r i → ∀ x ∈ openSegment ℝ (T.v i) (T.v (i + 1)), planeDot p x = r →
    ∃ Δ ∈ F, ∃ j, Δ.v j = x

theorem u3h_split_one_sided (T : Triangle) (p : Plane) (r : ℝ)
    (h : (∀ j, planeDot p (T.v j) ≤ r) ∨ (∀ j, r ≤ planeDot p (T.v j))) :
    u3h_SplitSpec T p r {T} where
  finite := finite_singleton T
  cover := by simp
  inter := by
    intro Δ hΔ Δ' hΔ'
    rw [mem_singleton_iff] at hΔ hΔ'; subst hΔ; subst hΔ'
    exact u3h_inter_self_face _
  side := by intro Δ hΔ; rw [mem_singleton_iff] at hΔ; subst hΔ; exact h
  vert := by intro Δ hΔ j; rw [mem_singleton_iff] at hΔ; subst hΔ; exact Or.inl ⟨j, rfl⟩
  old := fun i => ⟨T, mem_singleton T, i, rfl⟩
  cross := by
    intro i hi
    exfalso
    rcases h with h | h <;> rcases hi with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · linarith [h (i + 1)]
    · linarith [h i]
    · linarith [h i]
    · linarith [h (i + 1)]

theorem u3h_Opp_neg (T : Triangle) (p : Plane) (r : ℝ) (i : Fin 3) :
    u3h_Opp T (-p) (-r) i ↔ u3h_Opp T p r i := by
  unfold u3h_Opp
  simp only [u3h_planeDot_neg_left]
  constructor
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · right; constructor <;> linarith
    · left; constructor <;> linarith
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · right; constructor <;> linarith
    · left; constructor <;> linarith

theorem u3h_SplitSpec_neg {T : Triangle} {p : Plane} {r : ℝ} {F : Set Triangle}
    (h : u3h_SplitSpec T (-p) (-r) F) : u3h_SplitSpec T p r F where
  finite := h.finite
  cover := h.cover
  inter := h.inter
  side := by
    intro Δ hΔ
    rcases h.side Δ hΔ with hs | hs
    · right; intro j; have := hs j; rw [u3h_planeDot_neg_left] at this; linarith
    · left; intro j; have := hs j; rw [u3h_planeDot_neg_left] at this; linarith
  vert := by
    intro Δ hΔ j
    rcases h.vert Δ hΔ j with hv | ⟨i, h1, h2, h3⟩
    · exact Or.inl hv
    · refine Or.inr ⟨i, h1, ?_, (u3h_Opp_neg T p r i).1 h3⟩
      rw [u3h_planeDot_neg_left] at h2; linarith
  old := h.old
  cross := by
    intro i hi x hx hxr
    exact h.cross i ((u3h_Opp_neg T p r i).2 hi) x hx (by rw [u3h_planeDot_neg_left, hxr])

/-- Cyclic rotation of the vertex list. -/
def u3h_rot (T : Triangle) (k : Fin 3) : Triangle where
  v := fun j => T.v (j + k)
  pos := by
    show 0 < det (T.v (1 + k) - T.v (0 + k)) (T.v (2 + k) - T.v (0 + k))
    rw [zero_add, add_comm (1 : Fin 3) k, add_comm (2 : Fin 3) k]
    exact u3h_pos_cyc T k

@[simp] theorem u3h_rot_v (T : Triangle) (k j : Fin 3) : (u3h_rot T k).v j = T.v (j + k) := rfl

theorem u3h_fin3_a : ∀ i k : Fin 3, i - k + k = i := by decide
theorem u3h_fin3_b : ∀ i k : Fin 3, i + 1 + k = i + k + 1 := by decide
theorem u3h_fin3_c : ∀ i k : Fin 3, i - k + 1 + k = i + 1 := by decide

theorem u3h_rot_range (T : Triangle) (k : Fin 3) : range (u3h_rot T k).v = range T.v := by
  ext y; constructor
  · rintro ⟨j, rfl⟩; exact ⟨j + k, rfl⟩
  · rintro ⟨j, rfl⟩; exact ⟨j - k, by rw [u3h_rot_v, u3h_fin3_a]⟩

theorem u3h_rot_carrier (T : Triangle) (k : Fin 3) : (u3h_rot T k).carrier = T.carrier := by
  unfold Triangle.carrier; rw [u3h_rot_range]

theorem u3h_Opp_rot (T : Triangle) (p : Plane) (r : ℝ) (k i : Fin 3) :
    u3h_Opp (u3h_rot T k) p r i ↔ u3h_Opp T p r (i + k) := by
  unfold u3h_Opp; simp only [u3h_rot_v]; rw [u3h_fin3_b]

theorem u3h_SplitSpec_rot {T : Triangle} {p : Plane} {r : ℝ} {F : Set Triangle} (k : Fin 3)
    (h : u3h_SplitSpec (u3h_rot T k) p r F) : u3h_SplitSpec T p r F where
  finite := h.finite
  cover := by rw [h.cover, u3h_rot_carrier]
  inter := h.inter
  side := h.side
  vert := by
    intro Δ hΔ j
    rcases h.vert Δ hΔ j with ⟨i, hi⟩ | ⟨i, h1, h2, h3⟩
    · exact Or.inl ⟨i + k, hi⟩
    · refine Or.inr ⟨i + k, ?_, h2, (u3h_Opp_rot T p r k i).1 h3⟩
      rw [u3h_rot_v, u3h_rot_v, u3h_fin3_b] at h1; exact h1
  old := by
    intro i
    obtain ⟨Δ, hΔ, j, hj⟩ := h.old (i - k)
    exact ⟨Δ, hΔ, j, by rw [hj, u3h_rot_v, u3h_fin3_a]⟩
  cross := by
    intro i hi x hx hxr
    have hi' : u3h_Opp (u3h_rot T k) p r (i - k) := by rw [u3h_Opp_rot, u3h_fin3_a]; exact hi
    refine h.cross (i - k) hi' x ?_ hxr
    rw [u3h_rot_v, u3h_rot_v, u3h_fin3_a, u3h_fin3_c]; exact hx

theorem u3h_exists_param (p : Plane) (r : ℝ) {A B : Plane} (hAB : planeDot p A ≠ planeDot p B) :
    ∃ α : ℝ, α * (planeDot p B - planeDot p A) = r - planeDot p A :=
  ⟨_, div_mul_cancel₀ _ (sub_ne_zero.2 hAB.symm)⟩

/-- Vector identities used for the pieces (all by `ring`). -/
theorem u3h_det_split1 (v0 v1 v2 : Plane) (α : ℝ) :
    det (v1 - v0) (((1 - α) • v1 + α • v2) - v0) = α * det (v1 - v0) (v2 - v0) := by
  simp [det]; ring

theorem u3h_det_split2 (v0 v1 v2 : Plane) (α : ℝ) :
    det (((1 - α) • v1 + α • v2) - v0) (v2 - v0) = (1 - α) * det (v1 - v0) (v2 - v0) := by
  simp [det]; ring

theorem u3h_det_split3 (v0 v1 v2 : Plane) (α : ℝ) :
    det (((1 - α) • v1 + α • v2) - v0) (v1 - v0) = -(α * det (v1 - v0) (v2 - v0)) := by
  simp [det]; ring

/-- Pattern B at index 0: `v 0` on the line, `v 1` strictly above, `v 2` strictly below. -/
theorem u3h_splitB0 (T : Triangle) (p : Plane) (r : ℝ) (h0 : planeDot p (T.v 0) = r)
    (h1 : r < planeDot p (T.v 1)) (h2 : planeDot p (T.v 2) < r) :
    ∃ F : Set Triangle, u3h_SplitSpec T p r F := by
  have hAB : planeDot p (T.v 1) ≠ planeDot p (T.v 2) := by linarith
  obtain ⟨α, hα⟩ := u3h_exists_param p r hAB
  obtain ⟨hα0, hα1⟩ := u3h_cross_param_pos (Or.inr ⟨h2, h1⟩) hα
  set P : Plane := (1 - α) • T.v 1 + α • T.v 2 with hPdef
  have hPr : planeDot p P = r := by rw [hPdef, u3h_planeDot_param]; linear_combination hα
  have hPmem : P ∈ openSegment ℝ (T.v 1) (T.v 2) := u3h_mem_openSegment_of_param hα0 hα1
  have hPT : P ∈ T.carrier :=
    segment_subset_convexHull (mem_range_self 1) (mem_range_self 2) (openSegment_subset_segment ℝ _ _ hPmem)
  have hD := T.pos
  have pos1 : 0 < det (T.v 1 - T.v 0) (P - T.v 0) := by
    rw [hPdef, u3h_det_split1]; exact mul_pos hα0 hD
  have pos2 : 0 < det (P - T.v 0) (T.v 2 - T.v 0) := by
    rw [hPdef, u3h_det_split2]; exact mul_pos (by linarith) hD
  have neg3 : det (P - T.v 0) (T.v 1 - T.v 0) < 0 := by
    rw [hPdef, u3h_det_split3]; linarith [mul_pos hα0 hD]
  obtain ⟨Δ1, e1⟩ : ∃ Δ : Triangle, Δ.v = ![T.v 0, T.v 1, P] :=
    ⟨Triangle.mk ![T.v 0, T.v 1, P] pos1, rfl⟩
  obtain ⟨Δ2, e2⟩ : ∃ Δ : Triangle, Δ.v = ![T.v 0, P, T.v 2] :=
    ⟨Triangle.mk ![T.v 0, P, T.v 2] pos2, rfl⟩
  have d10 : Δ1.v 0 = T.v 0 := by rw [e1]; rfl
  have d11 : Δ1.v 1 = T.v 1 := by rw [e1]; rfl
  have d12 : Δ1.v 2 = P := by rw [e1]; rfl
  have d20 : Δ2.v 0 = T.v 0 := by rw [e2]; rfl
  have d21 : Δ2.v 1 = P := by rw [e2]; rfl
  have d22 : Δ2.v 2 = T.v 2 := by rw [e2]; rfl
  -- the separating line through `v 0` and `P`
  have hP0 : P - T.v 0 ≠ 0 := by
    intro h
    have : P = T.v 0 := sub_eq_zero.1 h
    apply u3h_v_not_mem_segment T 0
    rw [← this]
    simpa using openSegment_subset_segment ℝ _ _ hPmem
  set p' := u3h_dir (P - T.v 0) with hp'def
  set r' := planeDot p' (T.v 0) with hr'def
  have hp' : p' ≠ 0 := u3h_dir_ne_zero hP0
  have hq : ∀ w, planeDot p' w - r' = det (P - T.v 0) (w - T.v 0) := fun w => by
    rw [u3h_det_eq_planeDot, u3h_planeDot_sub]
  have hq0 : planeDot p' (T.v 0) = r' := rfl
  have hqP : planeDot p' P = r' := by
    have := hq P
    rw [show det (P - T.v 0) (P - T.v 0) = 0 by simp [det]; ring] at this
    linarith
  have hv2 : r' < planeDot p' (T.v 2) := by linarith [hq (T.v 2)]
  have hv1 : planeDot p' (T.v 1) < r' := by linarith [hq (T.v 1)]
  have s1 : ∀ i, planeDot p' (Δ1.v i) ≤ r' := by
    intro i; fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue, d10]; linarith
    · simp only [Fin.mk_one, Fin.isValue, d11]; linarith
    · simp only [Fin.reduceFinMk, d12]; linarith
  have s2 : ∀ i, r' ≤ planeDot p' (Δ2.v i) := by
    intro i; fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue, d20]; linarith
    · simp only [Fin.mk_one, Fin.isValue, d21]; linarith
    · simp only [Fin.reduceFinMk, Fin.isValue, d22]; linarith
  have hΔ1T : Δ1.carrier ⊆ T.carrier := by
    apply convexHull_min _ (convex_convexHull ℝ _)
    rintro _ ⟨j, rfl⟩; fin_cases j
    · simp only [Fin.zero_eta, Fin.isValue, d10]; exact subset_convexHull ℝ _ ⟨0, rfl⟩
    · simp only [Fin.mk_one, Fin.isValue, d11]; exact subset_convexHull ℝ _ ⟨1, rfl⟩
    · simp only [Fin.reduceFinMk, d12]; exact hPT
  have hΔ2T : Δ2.carrier ⊆ T.carrier := by
    apply convexHull_min _ (convex_convexHull ℝ _)
    rintro _ ⟨j, rfl⟩; fin_cases j
    · simp only [Fin.zero_eta, Fin.isValue, d20]; exact subset_convexHull ℝ _ ⟨0, rfl⟩
    · simp only [Fin.mk_one, Fin.isValue, d21]; exact hPT
    · simp only [Fin.reduceFinMk, Fin.isValue, d22]; exact subset_convexHull ℝ _ ⟨2, rfl⟩
  refine ⟨{Δ1, Δ2}, ?_⟩
  refine
    { finite := toFinite _
      cover := ?_
      inter := ?_
      side := ?_
      vert := ?_
      old := ?_
      cross := ?_ }
  · rw [biUnion_pair]
    apply Subset.antisymm (union_subset hΔ1T hΔ2T)
    intro x hx
    obtain ⟨a, b, c, ha, hb, hc, habc, rfl⟩ := (u3h_mem_carrier_iff T x).1 hx
    rcases le_total (c * (1 - α)) (b * α) with hcb | hcb
    · left
      refine u3h_mem_carrier_of_homog Δ1 (a := a * α) (b := b * α - c * (1 - α)) (c := c) (s := α)
        (mul_nonneg ha hα0.le) (by linarith) hc hα0 (by linear_combination α * habc) ?_
      rw [d10, d11, d12, hPdef]
      ext <;> simp <;> ring
    · right
      refine u3h_mem_carrier_of_homog Δ2 (a := a * (1 - α)) (b := b) (c := c * (1 - α) - b * α)
        (s := 1 - α) (mul_nonneg ha (by linarith)) hb (by linarith) (by linarith)
        (by linear_combination (1 - α) * habc) ?_
      rw [d20, d21, d22, hPdef]
      ext <;> simp <;> ring
  · apply u3h_inter_of_family
    · rintro Δ (rfl | rfl) Δ' (rfl | rfl) hne
      · exact absurd rfl hne
      · exact ⟨p', r', hp', s1, s2⟩
      · refine ⟨-p', -r', neg_ne_zero.2 hp', fun i => ?_, fun i => ?_⟩
        · rw [u3h_planeDot_neg_left]; linarith [s2 i]
        · rw [u3h_planeDot_neg_left]; linarith [s1 i]
      · exact absurd rfl hne
    · rintro Δ (rfl | rfl) Δ' (rfl | rfl) j hj
      · exact ⟨j, rfl⟩
      · fin_cases j
        · simp only [Fin.zero_eta, Fin.isValue, d20] at hj ⊢; exact ⟨0, d10⟩
        · simp only [Fin.mk_one, Fin.isValue, d21] at hj ⊢; exact ⟨2, d12⟩
        · simp only [Fin.reduceFinMk, Fin.isValue, d22] at hj ⊢
          exact absurd hj (u3h_not_mem_of_lt Δ s1 hv2)
      · fin_cases j
        · simp only [Fin.zero_eta, Fin.isValue, d10] at hj ⊢; exact ⟨0, d20⟩
        · simp only [Fin.mk_one, Fin.isValue, d11] at hj ⊢
          exact absurd hj (u3h_not_mem_of_gt Δ s2 hv1)
        · simp only [Fin.reduceFinMk, d12] at hj ⊢; exact ⟨1, d21⟩
      · exact ⟨j, rfl⟩
  · rintro Δ (rfl | rfl)
    · right; intro j; fin_cases j
      · simp only [Fin.zero_eta, Fin.isValue, d10]; linarith
      · simp only [Fin.mk_one, Fin.isValue, d11]; linarith
      · simp only [Fin.reduceFinMk, d12]; linarith
    · left; intro j; fin_cases j
      · simp only [Fin.zero_eta, Fin.isValue, d20]; linarith
      · simp only [Fin.mk_one, Fin.isValue, d21]; linarith
      · simp only [Fin.reduceFinMk, Fin.isValue, d22]; linarith
  · have hOpp1 : u3h_Opp T p r 1 := Or.inr ⟨h1, by simpa using h2⟩
    rintro Δ (rfl | rfl) j
    · fin_cases j
      · exact Or.inl ⟨0, d10⟩
      · exact Or.inl ⟨1, d11⟩
      · refine Or.inr ⟨1, ?_, by simpa [d12] using hPr, hOpp1⟩
        simp only [Fin.reduceFinMk, d12]; simpa using hPmem
    · fin_cases j
      · exact Or.inl ⟨0, d20⟩
      · refine Or.inr ⟨1, ?_, by simpa [d21] using hPr, hOpp1⟩
        simp only [Fin.mk_one, Fin.isValue, d21]; simpa using hPmem
      · exact Or.inl ⟨2, d22⟩
  · intro i; fin_cases i
    · exact ⟨Δ1, by simp, 0, d10⟩
    · exact ⟨Δ1, by simp, 1, d11⟩
    · exact ⟨Δ2, by simp, 2, d22⟩
  · intro i hi x hx hxr
    fin_cases i
    · exfalso; rcases hi with ⟨a1, _⟩ | ⟨a1, _⟩ <;> simp at a1 <;> linarith
    · refine ⟨Δ1, by simp, 2, ?_⟩
      rw [d12, hPdef]
      exact (u3h_cross_unique hAB hα (by simpa using hx) hxr).symm
    · exfalso; rcases hi with ⟨_, a2⟩ | ⟨_, a2⟩ <;> simp at a2 <;> linarith

theorem u3h_det_A1 (v0 v1 v2 : Plane) (α β : ℝ) :
    det (((1 - α) • v0 + α • v1) - v0) (((1 - β) • v2 + β • v0) - v0) =
      (α * (1 - β)) * det (v1 - v0) (v2 - v0) := by
  simp [det]; ring

theorem u3h_det_A2 (v0 v1 v2 : Plane) (α : ℝ) :
    det (v1 - ((1 - α) • v0 + α • v1)) (v2 - ((1 - α) • v0 + α • v1)) =
      (1 - α) * det (v1 - v0) (v2 - v0) := by
  simp [det]; ring

theorem u3h_det_A3 (v0 v1 v2 : Plane) (α β : ℝ) :
    det (v2 - ((1 - α) • v0 + α • v1)) (((1 - β) • v2 + β • v0) - ((1 - α) • v0 + α • v1)) =
      (α * β) * det (v1 - v0) (v2 - v0) := by
  simp [det]; ring

theorem u3h_det_A4 (v0 v1 v2 : Plane) (α : ℝ) :
    det (v2 - ((1 - α) • v0 + α • v1)) (v1 - ((1 - α) • v0 + α • v1)) =
      -((1 - α) * det (v1 - v0) (v2 - v0)) := by
  simp [det]; ring

/-- Pattern A at index 0: `v 0` strictly above the line, `v 1`, `v 2` strictly below. -/
theorem u3h_splitA0 (T : Triangle) (p : Plane) (r : ℝ) (h0 : r < planeDot p (T.v 0))
    (h1 : planeDot p (T.v 1) < r) (h2 : planeDot p (T.v 2) < r) :
    ∃ F : Set Triangle, u3h_SplitSpec T p r F := by
  have hAB1 : planeDot p (T.v 0) ≠ planeDot p (T.v 1) := by linarith
  have hp0 : p ≠ 0 := by
    rintro rfl; rw [u3h_planeDot_zero_left] at h0 h1; linarith
  have hAB2 : planeDot p (T.v 2) ≠ planeDot p (T.v 0) := by linarith
  obtain ⟨α, hα⟩ := u3h_exists_param p r hAB1
  obtain ⟨β, hβ⟩ := u3h_exists_param p r hAB2
  obtain ⟨hα0, hα1⟩ := u3h_cross_param_pos (Or.inr ⟨h1, h0⟩) hα
  obtain ⟨hβ0, hβ1⟩ := u3h_cross_param_pos (Or.inl ⟨h2, h0⟩) hβ
  have hγ : (1 - β) * (planeDot p (T.v 2) - planeDot p (T.v 0)) = r - planeDot p (T.v 0) := by
    linear_combination hβ
  set P : Plane := (1 - α) • T.v 0 + α • T.v 1 with hPdef
  set Q : Plane := (1 - β) • T.v 2 + β • T.v 0 with hQdef
  have hPr : planeDot p P = r := by rw [hPdef, u3h_planeDot_param]; linear_combination hα
  have hQr : planeDot p Q = r := by rw [hQdef, u3h_planeDot_param]; linear_combination hβ
  have hPmem : P ∈ openSegment ℝ (T.v 0) (T.v 1) := u3h_mem_openSegment_of_param hα0 hα1
  have hQmem : Q ∈ openSegment ℝ (T.v 2) (T.v 0) := u3h_mem_openSegment_of_param hβ0 hβ1
  have hPT : P ∈ T.carrier :=
    segment_subset_convexHull (mem_range_self 0) (mem_range_self 1)
      (openSegment_subset_segment ℝ _ _ hPmem)
  have hQT : Q ∈ T.carrier :=
    segment_subset_convexHull (mem_range_self 2) (mem_range_self 0)
      (openSegment_subset_segment ℝ _ _ hQmem)
  have hD := T.pos
  have pos1 : 0 < det (P - T.v 0) (Q - T.v 0) := by
    rw [hPdef, hQdef, u3h_det_A1]; exact mul_pos (mul_pos hα0 (by linarith)) hD
  have pos2 : 0 < det (T.v 1 - P) (T.v 2 - P) := by
    rw [hPdef, u3h_det_A2]; exact mul_pos (by linarith) hD
  have pos3 : 0 < det (T.v 2 - P) (Q - P) := by
    rw [hPdef, hQdef, u3h_det_A3]; exact mul_pos (mul_pos hα0 hβ0) hD
  have neg4 : det (T.v 2 - P) (T.v 1 - P) < 0 := by
    rw [hPdef, u3h_det_A4]; linarith [mul_pos (show (0:ℝ) < 1 - α by linarith) hD]
  obtain ⟨Δ1, e1⟩ : ∃ Δ : Triangle, Δ.v = ![T.v 0, P, Q] := ⟨Triangle.mk ![T.v 0, P, Q] pos1, rfl⟩
  obtain ⟨Δ2, e2⟩ : ∃ Δ : Triangle, Δ.v = ![P, T.v 1, T.v 2] :=
    ⟨Triangle.mk ![P, T.v 1, T.v 2] pos2, rfl⟩
  obtain ⟨Δ3, e3⟩ : ∃ Δ : Triangle, Δ.v = ![P, T.v 2, Q] := ⟨Triangle.mk ![P, T.v 2, Q] pos3, rfl⟩
  have d10 : Δ1.v 0 = T.v 0 := by rw [e1]; rfl
  have d11 : Δ1.v 1 = P := by rw [e1]; rfl
  have d12 : Δ1.v 2 = Q := by rw [e1]; rfl
  have d20 : Δ2.v 0 = P := by rw [e2]; rfl
  have d21 : Δ2.v 1 = T.v 1 := by rw [e2]; rfl
  have d22 : Δ2.v 2 = T.v 2 := by rw [e2]; rfl
  have d30 : Δ3.v 0 = P := by rw [e3]; rfl
  have d31 : Δ3.v 1 = T.v 2 := by rw [e3]; rfl
  have d32 : Δ3.v 2 = Q := by rw [e3]; rfl
  -- signs with respect to the cutting line
  have s1 : ∀ i, r ≤ planeDot p (Δ1.v i) := by
    intro i; fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue, d10]; linarith
    · simp only [Fin.mk_one, Fin.isValue, d11]; linarith
    · simp only [Fin.reduceFinMk, d12]; linarith
  have s2 : ∀ i, planeDot p (Δ2.v i) ≤ r := by
    intro i; fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue, d20]; linarith
    · simp only [Fin.mk_one, Fin.isValue, d21]; linarith
    · simp only [Fin.reduceFinMk, d22]; linarith
  have s3 : ∀ i, planeDot p (Δ3.v i) ≤ r := by
    intro i; fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue, d30]; linarith
    · simp only [Fin.mk_one, Fin.isValue, d31]; linarith
    · simp only [Fin.reduceFinMk, d32]; linarith
  -- the diagonal line through `P` and `v 2`
  have hP2 : T.v 2 - P ≠ 0 := by
    intro h
    have : T.v 2 = P := sub_eq_zero.1 h
    apply u3h_v_not_mem_segment T 2
    rw [this]
    simpa using openSegment_subset_segment ℝ _ _ hPmem
  set p'' := u3h_dir (T.v 2 - P) with hp''def
  set r'' := planeDot p'' P with hr''def
  have hp'' : p'' ≠ 0 := u3h_dir_ne_zero hP2
  have hq : ∀ w, planeDot p'' w - r'' = det (T.v 2 - P) (w - P) := fun w => by
    rw [u3h_det_eq_planeDot, u3h_planeDot_sub]
  have hqP : planeDot p'' P = r'' := rfl
  have hq2 : planeDot p'' (T.v 2) = r'' := by
    have := hq (T.v 2)
    rw [show det (T.v 2 - P) (T.v 2 - P) = 0 by simp [det]; ring] at this
    linarith
  have hqQ : r'' < planeDot p'' Q := by linarith [hq Q]
  have hq1 : planeDot p'' (T.v 1) < r'' := by linarith [hq (T.v 1)]
  have t2 : ∀ i, planeDot p'' (Δ2.v i) ≤ r'' := by
    intro i; fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue, d20]; linarith
    · simp only [Fin.mk_one, Fin.isValue, d21]; linarith
    · simp only [Fin.reduceFinMk, d22]; linarith
  have t3 : ∀ i, r'' ≤ planeDot p'' (Δ3.v i) := by
    intro i; fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue, d30]; linarith
    · simp only [Fin.mk_one, Fin.isValue, d31]; linarith
    · simp only [Fin.reduceFinMk, d32]; linarith
  have hΔ1T : Δ1.carrier ⊆ T.carrier := by
    apply convexHull_min _ (convex_convexHull ℝ _)
    rintro _ ⟨j, rfl⟩; fin_cases j
    · simp only [Fin.zero_eta, Fin.isValue, d10]; exact subset_convexHull ℝ _ ⟨0, rfl⟩
    · simp only [Fin.mk_one, Fin.isValue, d11]; exact hPT
    · simp only [Fin.reduceFinMk, d12]; exact hQT
  have hΔ2T : Δ2.carrier ⊆ T.carrier := by
    apply convexHull_min _ (convex_convexHull ℝ _)
    rintro _ ⟨j, rfl⟩; fin_cases j
    · simp only [Fin.zero_eta, Fin.isValue, d20]; exact hPT
    · simp only [Fin.mk_one, Fin.isValue, d21]; exact subset_convexHull ℝ _ ⟨1, rfl⟩
    · simp only [Fin.reduceFinMk, d22]; exact subset_convexHull ℝ _ ⟨2, rfl⟩
  have hΔ3T : Δ3.carrier ⊆ T.carrier := by
    apply convexHull_min _ (convex_convexHull ℝ _)
    rintro _ ⟨j, rfl⟩; fin_cases j
    · simp only [Fin.zero_eta, Fin.isValue, d30]; exact hPT
    · simp only [Fin.mk_one, Fin.isValue, d31]; exact subset_convexHull ℝ _ ⟨2, rfl⟩
    · simp only [Fin.reduceFinMk, d32]; exact hQT
  refine ⟨{Δ1, Δ2, Δ3}, ?_⟩
  refine
    { finite := toFinite _
      cover := ?_
      inter := ?_
      side := ?_
      vert := ?_
      old := ?_
      cross := ?_ }
  · rw [biUnion_insert, biUnion_pair]
    apply Subset.antisymm (union_subset hΔ1T (union_subset hΔ2T hΔ3T))
    intro x hx
    obtain ⟨a, b, c, ha, hb, hc, habc, rfl⟩ := (u3h_mem_carrier_iff T x).1 hx
    have habc' : a = 1 - b - c := by linarith
    subst habc'
    have hx' : planeDot p ((1 - b - c) • T.v 0 + b • T.v 1 + c • T.v 2) =
        (1 - b - c) * planeDot p (T.v 0) + b * planeDot p (T.v 1) + c * planeDot p (T.v 2) := by
      rw [u3h_planeDot_add, u3h_planeDot_combo, u3h_planeDot_smul]
    have key : (planeDot p ((1 - b - c) • T.v 0 + b • T.v 1 + c • T.v 2) - r) * (α * (1 - β)) =
        (r - planeDot p (T.v 0)) * (b * (1 - β) + c * α - α * (1 - β)) := by
      rw [hx']
      linear_combination (b * (1 - β)) * hα + (c * α) * hγ
    have hpos : 0 < α * (1 - β) := mul_pos hα0 (by linarith)
    rcases le_total r (planeDot p ((1 - b - c) • T.v 0 + b • T.v 1 + c • T.v 2)) with hxr | hxr
    · left
      have hS : b * (1 - β) + c * α - α * (1 - β) ≤ 0 := by
        by_contra hS; push Not at hS
        have := mul_nonneg (sub_nonneg.2 hxr) hpos.le
        nlinarith
      refine u3h_mem_carrier_of_homog Δ1 (a := α * (1 - β) - b * (1 - β) - c * α)
        (b := b * (1 - β)) (c := c * α) (s := α * (1 - β)) (by linarith)
        (mul_nonneg hb (by linarith)) (mul_nonneg hc hα0.le) hpos (by ring) ?_
      rw [d10, d11, d12, hPdef, hQdef]
      ext <;> simp <;> ring
    · have hS : 0 ≤ b * (1 - β) + c * α - α * (1 - β) := by
        by_contra hS; push Not at hS
        have := mul_nonneg (sub_nonneg.2 hxr) hpos.le
        nlinarith
      rcases le_total ((1 - b - c) * α) (b * (1 - α)) with hab | hab
      · right; left
        refine u3h_mem_carrier_of_homog Δ2 (a := 1 - b - c) (b := b * (1 - α) - (1 - b - c) * α)
          (c := c * (1 - α)) (s := 1 - α) ha (by linarith) (mul_nonneg hc (by linarith)) (by linarith)
          (by ring) ?_
        rw [d20, d21, d22, hPdef]
        ext <;> simp <;> ring
      · right; right
        refine u3h_mem_carrier_of_homog Δ3 (a := b * β) (b := b * (1 - β) + c * α - α * (1 - β))
          (c := (1 - b - c) * α - b * (1 - α)) (s := α * β) (mul_nonneg hb hβ0.le) hS (by linarith)
          (mul_pos hα0 hβ0) (by ring) ?_
        rw [d30, d31, d32, hPdef, hQdef]
        ext <;> simp <;> ring
  · apply u3h_inter_of_family
    · rintro Δ (rfl | rfl | rfl) Δ' (rfl | rfl | rfl) hne
      · exact absurd rfl hne
      · refine ⟨-p, -r, ?_, fun i => ?_, fun i => ?_⟩
        · exact neg_ne_zero.2 hp0
        · rw [u3h_planeDot_neg_left]; linarith [s1 i]
        · rw [u3h_planeDot_neg_left]; linarith [s2 i]
      · refine ⟨-p, -r, ?_, fun i => ?_, fun i => ?_⟩
        · exact neg_ne_zero.2 hp0
        · rw [u3h_planeDot_neg_left]; linarith [s1 i]
        · rw [u3h_planeDot_neg_left]; linarith [s3 i]
      · exact ⟨p, r, hp0, s2, s1⟩
      · exact absurd rfl hne
      · exact ⟨p'', r'', hp'', t2, t3⟩
      · exact ⟨p, r, hp0, s3, s1⟩
      · refine ⟨-p'', -r'', neg_ne_zero.2 hp'', fun i => ?_, fun i => ?_⟩
        · rw [u3h_planeDot_neg_left]; linarith [t3 i]
        · rw [u3h_planeDot_neg_left]; linarith [t2 i]
      · exact absurd rfl hne
    · rintro Δ (rfl | rfl | rfl) Δ' (rfl | rfl | rfl) j hj
      · exact ⟨j, rfl⟩
      · fin_cases j
        · simp only [Fin.zero_eta, Fin.isValue, d20] at hj ⊢; exact ⟨1, d11⟩
        · simp only [Fin.mk_one, Fin.isValue, d21] at hj ⊢
          exact absurd hj (u3h_not_mem_of_gt Δ s1 h1)
        · simp only [Fin.reduceFinMk, d22] at hj ⊢
          exact absurd hj (u3h_not_mem_of_gt Δ s1 h2)
      · fin_cases j
        · simp only [Fin.zero_eta, Fin.isValue, d30] at hj ⊢; exact ⟨1, d11⟩
        · simp only [Fin.mk_one, Fin.isValue, d31] at hj ⊢
          exact absurd hj (u3h_not_mem_of_gt Δ s1 h2)
        · simp only [Fin.reduceFinMk, d32] at hj ⊢; exact ⟨2, d12⟩
      · fin_cases j
        · simp only [Fin.zero_eta, Fin.isValue, d10] at hj ⊢
          exact absurd hj (u3h_not_mem_of_lt Δ s2 h0)
        · simp only [Fin.mk_one, Fin.isValue, d11] at hj ⊢; exact ⟨0, d20⟩
        · simp only [Fin.reduceFinMk, d12] at hj ⊢
          exact absurd hj (u3h_not_mem_of_lt Δ t2 hqQ)
      · exact ⟨j, rfl⟩
      · fin_cases j
        · simp only [Fin.zero_eta, Fin.isValue, d30] at hj ⊢; exact ⟨0, d20⟩
        · simp only [Fin.mk_one, Fin.isValue, d31] at hj ⊢; exact ⟨2, d22⟩
        · simp only [Fin.reduceFinMk, d32] at hj ⊢
          exact absurd hj (u3h_not_mem_of_lt Δ t2 hqQ)
      · fin_cases j
        · simp only [Fin.zero_eta, Fin.isValue, d10] at hj ⊢
          exact absurd hj (u3h_not_mem_of_lt Δ s3 h0)
        · simp only [Fin.mk_one, Fin.isValue, d11] at hj ⊢; exact ⟨0, d30⟩
        · simp only [Fin.reduceFinMk, d12] at hj ⊢; exact ⟨2, d32⟩
      · fin_cases j
        · simp only [Fin.zero_eta, Fin.isValue, d20] at hj ⊢; exact ⟨0, d30⟩
        · simp only [Fin.mk_one, Fin.isValue, d21] at hj ⊢
          exact absurd hj (u3h_not_mem_of_gt Δ t3 hq1)
        · simp only [Fin.reduceFinMk, d22] at hj ⊢; exact ⟨1, d31⟩
      · exact ⟨j, rfl⟩
  · rintro Δ (rfl | rfl | rfl)
    · exact Or.inr s1
    · exact Or.inl s2
    · exact Or.inl s3
  · have hOpp0 : u3h_Opp T p r 0 := Or.inr ⟨h0, by simpa using h1⟩
    have hOpp2 : u3h_Opp T p r 2 := Or.inl ⟨h2, by simpa using h0⟩
    have hPv : ∀ (Δ : Triangle) (j : Fin 3), Δ.v j = P → (∃ i, Δ.v j = T.v i) ∨
        (∃ i, Δ.v j ∈ openSegment ℝ (T.v i) (T.v (i + 1)) ∧ planeDot p (Δ.v j) = r ∧ u3h_Opp T p r i) := by
      intro Δ j hj
      refine Or.inr ⟨0, ?_, by rw [hj]; exact hPr, hOpp0⟩
      rw [hj]; simpa using hPmem
    have hQv : ∀ (Δ : Triangle) (j : Fin 3), Δ.v j = Q → (∃ i, Δ.v j = T.v i) ∨
        (∃ i, Δ.v j ∈ openSegment ℝ (T.v i) (T.v (i + 1)) ∧ planeDot p (Δ.v j) = r ∧ u3h_Opp T p r i) := by
      intro Δ j hj
      refine Or.inr ⟨2, ?_, by rw [hj]; exact hQr, hOpp2⟩
      rw [hj]; simpa using hQmem
    rintro Δ (rfl | rfl | rfl) j
    · fin_cases j
      · exact Or.inl ⟨0, d10⟩
      · exact hPv _ _ d11
      · exact hQv _ _ d12
    · fin_cases j
      · exact hPv _ _ d20
      · exact Or.inl ⟨1, d21⟩
      · exact Or.inl ⟨2, d22⟩
    · fin_cases j
      · exact hPv _ _ d30
      · exact Or.inl ⟨2, d31⟩
      · exact hQv _ _ d32
  · intro i; fin_cases i
    · exact ⟨Δ1, by simp, 0, d10⟩
    · exact ⟨Δ2, by simp, 1, d21⟩
    · exact ⟨Δ2, by simp, 2, d22⟩
  · intro i hi x hx hxr
    fin_cases i
    · refine ⟨Δ1, by simp, 1, ?_⟩
      rw [d11, hPdef]
      exact (u3h_cross_unique hAB1 hα (by simpa using hx) hxr).symm
    · exfalso; rcases hi with ⟨a1, a2⟩ | ⟨a1, a2⟩ <;> simp at a1 a2 <;> linarith
    · refine ⟨Δ1, by simp, 2, ?_⟩
      rw [d12, hQdef]
      exact (u3h_cross_unique hAB2 hβ (by simpa using hx) hxr).symm

/-- Every triangle splits along every line. -/
theorem u3h_split_exists (T : Triangle) (p : Plane) (r : ℝ) :
    ∃ F : Set Triangle, u3h_SplitSpec T p r F := by
  by_cases hone : (∀ j, planeDot p (T.v j) ≤ r) ∨ (∀ j, r ≤ planeDot p (T.v j))
  · exact ⟨{T}, u3h_split_one_sided T p r hone⟩
  have key : ∀ (S : Triangle),
      (r < planeDot p (S.v 0) ∧ planeDot p (S.v 1) < r ∧ planeDot p (S.v 2) < r) ∨
      (planeDot p (S.v 0) < r ∧ r < planeDot p (S.v 1) ∧ r < planeDot p (S.v 2)) ∨
      (planeDot p (S.v 0) = r ∧ r < planeDot p (S.v 1) ∧ planeDot p (S.v 2) < r) ∨
      (planeDot p (S.v 0) = r ∧ planeDot p (S.v 1) < r ∧ r < planeDot p (S.v 2)) →
      ∃ F, u3h_SplitSpec S p r F := by
    rintro S (⟨a, b, c⟩ | ⟨a, b, c⟩ | ⟨a, b, c⟩ | ⟨a, b, c⟩)
    · exact u3h_splitA0 S p r a b c
    · obtain ⟨F, hF⟩ := u3h_splitA0 S (-p) (-r) (by rw [u3h_planeDot_neg_left]; linarith)
        (by rw [u3h_planeDot_neg_left]; linarith) (by rw [u3h_planeDot_neg_left]; linarith)
      exact ⟨F, u3h_SplitSpec_neg hF⟩
    · exact u3h_splitB0 S p r a b c
    · obtain ⟨F, hF⟩ := u3h_splitB0 S (-p) (-r) (by rw [u3h_planeDot_neg_left]; linarith)
        (by rw [u3h_planeDot_neg_left]; linarith) (by rw [u3h_planeDot_neg_left]; linarith)
      exact ⟨F, u3h_SplitSpec_neg hF⟩
  suffices ∃ k : Fin 3, ∃ F, u3h_SplitSpec (u3h_rot T k) p r F by
    obtain ⟨k, F, hF⟩ := this; exact ⟨F, u3h_SplitSpec_rot k hF⟩
  rcases lt_trichotomy (planeDot p (T.v 0)) r with h0 | h0 | h0 <;>
    rcases lt_trichotomy (planeDot p (T.v 1)) r with h1 | h1 | h1 <;>
    rcases lt_trichotomy (planeDot p (T.v 2)) r with h2 | h2 | h2
  all_goals first
    | (refine absurd (Or.inl fun j => ?_) hone
       fin_cases j <;> simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, Fin.reduceFinMk] <;> linarith)
    | (refine absurd (Or.inr fun j => ?_) hone
       fin_cases j <;> simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, Fin.reduceFinMk] <;> linarith)
    | (refine ⟨0, key _ (Or.inl ⟨?_, ?_, ?_⟩)⟩ <;> [simpa using h0; simpa using h1; simpa using h2])
    | (refine ⟨0, key _ (Or.inr (Or.inl ⟨?_, ?_, ?_⟩))⟩ <;>
        [simpa using h0; simpa using h1; simpa using h2])
    | (refine ⟨0, key _ (Or.inr (Or.inr (Or.inl ⟨?_, ?_, ?_⟩)))⟩ <;>
        [simpa using h0; simpa using h1; simpa using h2])
    | (refine ⟨0, key _ (Or.inr (Or.inr (Or.inr ⟨?_, ?_, ?_⟩)))⟩ <;>
        [simpa using h0; simpa using h1; simpa using h2])
    | (refine ⟨1, key _ (Or.inl ⟨?_, ?_, ?_⟩)⟩ <;> [simpa using h1; simpa using h2; simpa using h0])
    | (refine ⟨1, key _ (Or.inr (Or.inl ⟨?_, ?_, ?_⟩))⟩ <;>
        [simpa using h1; simpa using h2; simpa using h0])
    | (refine ⟨1, key _ (Or.inr (Or.inr (Or.inl ⟨?_, ?_, ?_⟩)))⟩ <;>
        [simpa using h1; simpa using h2; simpa using h0])
    | (refine ⟨1, key _ (Or.inr (Or.inr (Or.inr ⟨?_, ?_, ?_⟩)))⟩ <;>
        [simpa using h1; simpa using h2; simpa using h0])
    | (refine ⟨2, key _ (Or.inl ⟨?_, ?_, ?_⟩)⟩ <;> [simpa using h2; simpa using h0; simpa using h1])
    | (refine ⟨2, key _ (Or.inr (Or.inl ⟨?_, ?_, ?_⟩))⟩ <;>
        [simpa using h2; simpa using h0; simpa using h1])
    | (refine ⟨2, key _ (Or.inr (Or.inr (Or.inl ⟨?_, ?_, ?_⟩)))⟩ <;>
        [simpa using h2; simpa using h0; simpa using h1])
    | (refine ⟨2, key _ (Or.inr (Or.inr (Or.inr ⟨?_, ?_, ?_⟩)))⟩ <;>
        [simpa using h2; simpa using h0; simpa using h1])

/-! ### U3 helpers: canonical pieces and the one-line refinement -/

/-- A vertex is an extreme point of the triangle. -/
theorem u3h_v_extreme (T : Triangle) (i : Fin 3) : T.v i ∈ Set.extremePoints ℝ T.carrier := by
  refine ⟨subset_convexHull ℝ _ ⟨i, rfl⟩, ?_⟩
  intro x₁ hx₁ x₂ hx₂ hmem
  obtain ⟨a1, b1, c1, ha1, hb1, hc1, s1, rfl⟩ := (u3h_mem_carrier_iff T x₁).1 hx₁
  obtain ⟨a2, b2, c2, ha2, hb2, hc2, s2, rfl⟩ := (u3h_mem_carrier_iff T x₂).1 hx₂
  obtain ⟨t1, t2, ht1, ht2, ht, hx⟩ := hmem
  have hx' : (t1 * a1 + t2 * a2) • T.v 0 + (t1 * b1 + t2 * b2) • T.v 1 + (t1 * c1 + t2 * c2) • T.v 2
      = T.v i := by
    rw [← hx]; simp only [smul_add, add_smul, mul_smul]; abel
  fin_cases i
  · have hu := u3h_bary_unique T (a' := 1) (b' := 0) (c' := 0) (by simpa using hx') (by nlinarith)
    obtain ⟨_, e2, e3⟩ := hu
    have : b1 = 0 ∧ b2 = 0 ∧ c1 = 0 ∧ c2 = 0 := by
      refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith [mul_nonneg ht1.le hb1, mul_nonneg ht2.le hb2,
        mul_nonneg ht1.le hc1, mul_nonneg ht2.le hc2]
    obtain ⟨rfl, rfl, rfl, rfl⟩ := this
    have e1 : a1 = 1 := by linarith
    have e1' : a2 = 1 := by linarith
    subst e1 e1'; simp
  · have hu := u3h_bary_unique T (a' := 0) (b' := 1) (c' := 0) (by simpa using hx') (by nlinarith)
    obtain ⟨e1, _, e3⟩ := hu
    have : a1 = 0 ∧ a2 = 0 ∧ c1 = 0 ∧ c2 = 0 := by
      refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith [mul_nonneg ht1.le ha1, mul_nonneg ht2.le ha2,
        mul_nonneg ht1.le hc1, mul_nonneg ht2.le hc2]
    obtain ⟨rfl, rfl, rfl, rfl⟩ := this
    have e1 : b1 = 1 := by linarith
    have e1' : b2 = 1 := by linarith
    subst e1 e1'; simp
  · have hu := u3h_bary_unique T (a' := 0) (b' := 0) (c' := 1) (by simpa using hx') (by nlinarith)
    obtain ⟨e1, e2, _⟩ := hu
    have : a1 = 0 ∧ a2 = 0 ∧ b1 = 0 ∧ b2 = 0 := by
      refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith [mul_nonneg ht1.le ha1, mul_nonneg ht2.le ha2,
        mul_nonneg ht1.le hb1, mul_nonneg ht2.le hb2]
    obtain ⟨rfl, rfl, rfl, rfl⟩ := this
    have e1 : c1 = 1 := by linarith
    have e1' : c2 = 1 := by linarith
    subst e1 e1'; simp

/-- Triangles with the same carrier have the same vertex set. -/
theorem u3h_range_eq_of_carrier_eq {T T' : Triangle} (h : T.carrier = T'.carrier) :
    range T.v = range T'.v := by
  have key : ∀ (S S' : Triangle), S.carrier = S'.carrier → range S.v ⊆ range S'.v := by
    rintro S S' hSS' _ ⟨i, rfl⟩
    have := u3h_v_extreme S i
    rw [hSS'] at this
    exact extremePoints_convexHull_subset this
  exact Subset.antisymm (key T T' h) (key T' T h.symm)

def u3h_defaultTri : Triangle where
  v := ![((0 : ℝ), (0 : ℝ)), ((1 : ℝ), (0 : ℝ)), ((0 : ℝ), (1 : ℝ))]
  pos := by
    show (0 : ℝ) < det (((1 : ℝ), (0 : ℝ)) - ((0 : ℝ), (0 : ℝ))) (((0 : ℝ), (1 : ℝ)) - ((0 : ℝ), (0 : ℝ)))
    simp [det]

/-- A canonical triangle with a given carrier (when one exists). -/
noncomputable def u3h_canonTri (S : Set Plane) : Triangle := by
  classical exact if h : ∃ T : Triangle, T.carrier = S then h.choose else u3h_defaultTri

theorem u3h_canonTri_carrier (T : Triangle) : (u3h_canonTri T.carrier).carrier = T.carrier := by
  unfold u3h_canonTri
  rw [dif_pos ⟨T, rfl⟩]
  exact Exists.choose_spec (⟨T, rfl⟩ : ∃ T' : Triangle, T'.carrier = T.carrier)

theorem u3h_canonTri_range (T : Triangle) : range (u3h_canonTri T.carrier).v = range T.v :=
  u3h_range_eq_of_carrier_eq (u3h_canonTri_carrier T)

/-- The pieces of a triangle along a line; they depend only on the carrier. -/
noncomputable def u3h_pieces (S : Set Plane) (p : Plane) (r : ℝ) : Set Triangle :=
  (u3h_split_exists (u3h_canonTri S) p r).choose

theorem u3h_pieces_spec (S : Set Plane) (p : Plane) (r : ℝ) :
    u3h_SplitSpec (u3h_canonTri S) p r (u3h_pieces S p r) :=
  (u3h_split_exists (u3h_canonTri S) p r).choose_spec

/-- The pieces form a triangulation of the triangle. -/
def u3h_SplitSpec.toTriangulation {T : Triangle} {p : Plane} {r : ℝ} {F : Set Triangle}
    (h : u3h_SplitSpec T p r F) : Triangulation T.carrier :=
  ⟨F, h.finite, h.cover, h.inter⟩

theorem u3h_SplitSpec.subset {T : Triangle} {p : Plane} {r : ℝ} {F : Set Triangle}
    (h : u3h_SplitSpec T p r F) {Δ : Triangle} (hΔ : Δ ∈ F) : Δ.carrier ⊆ T.carrier := by
  rw [← h.cover]; exact subset_biUnion_of_mem (u := fun Δ => Δ.carrier) hΔ

theorem u3h_fin3_d : ∀ i : Fin 3, i + 2 + 1 = i := by decide
theorem u3h_fin3_e : ∀ i : Fin 3, i + 2 + 2 = i + 1 := by decide
theorem u3h_fin3_adj : ∀ a b : Fin 3, a ≠ b → b = a + 1 ∨ a = b + 1 := by decide
theorem u3h_fin3_ne : ∀ i : Fin 3, i ≠ i + 1 := by decide
theorem u3h_fin3_f : ∀ i : Fin 3, i + 1 + 1 = i + 2 := by decide
theorem u3h_fin3_g : ∀ i : Fin 3, i + 1 + 2 = i := by decide

/-- A point of an open edge in the hull of a set of vertices forces both ends into the set. -/
theorem u3h_endpoints_mem (C : Triangle) {S : Set Plane} (hS : S ⊆ range C.v) (i : Fin 3) {w : Plane}
    (hw : w ∈ openSegment ℝ (C.v i) (C.v (i + 1))) (hwS : w ∈ convexHull ℝ S) :
    C.v i ∈ S ∧ C.v (i + 1) ∈ S := by
  have hne : C.v i ≠ C.v (i + 1) := fun e => u3h_fin3_ne i (u3h_v_injective C e)
  have hws : w ∈ segment ℝ (C.v i) (C.v (i + 1)) := openSegment_subset_segment ℝ _ _ hw
  constructor
  · by_contra hn
    have hsub : S ⊆ {C.v (i + 1), C.v (i + 2)} := by
      intro y hy
      obtain ⟨j, rfl⟩ := hS hy
      have hne' : C.v j ≠ C.v i := fun e => hn (e ▸ hy)
      rcases u3h_other C i j hne' with e | e <;> simp [e]
    have := convexHull_mono hsub hwS
    rw [convexHull_pair] at this
    have hw' := u3h_segment_inter C i hws this
    rw [hw'] at hw
    exact hne ((right_mem_openSegment_iff).1 hw)
  · by_contra hn
    have hsub : S ⊆ {C.v (i + 2), C.v (i + 2 + 1)} := by
      intro y hy
      obtain ⟨j, rfl⟩ := hS hy
      have hne' : C.v j ≠ C.v (i + 1) := fun e => hn (e ▸ hy)
      rcases u3h_other C (i + 1) j hne' with e | e
      · rw [u3h_fin3_d]; simp [e, u3h_fin3_f]
      · rw [u3h_fin3_d]; simp [e, u3h_fin3_g]
    have := convexHull_mono hsub hwS
    rw [convexHull_pair] at this
    have hw' := u3h_segment_inter C (i + 2) this (by rw [u3h_fin3_d, u3h_fin3_e]; exact hws)
    rw [u3h_fin3_d] at hw'
    rw [hw'] at hw
    exact hne ((left_mem_openSegment_iff).1 hw)

/-- Compatibility: a vertex of a piece of `T'` lying in `T` is a vertex of a piece of `T`. -/
theorem u3h_compat {X : Set Plane} (K : Triangulation X) (p : Plane) (r : ℝ) {T T' : Triangle}
    (hT : T ∈ K.faces) (hT' : T' ∈ K.faces) {Δ' : Triangle} (hΔ' : Δ' ∈ u3h_pieces T'.carrier p r)
    (j : Fin 3) (hw : Δ'.v j ∈ T.carrier) :
    ∃ Δ₂ ∈ u3h_pieces T.carrier p r, Δ'.v j ∈ range Δ₂.v := by
  by_cases hc : T.carrier = T'.carrier
  · rw [hc]; exact ⟨Δ', hΔ', j, rfl⟩
  set w := Δ'.v j with hwdef
  have spec := u3h_pieces_spec T.carrier p r
  have spec' := u3h_pieces_spec T'.carrier p r
  set C := u3h_canonTri T.carrier with hCdef
  set C' := u3h_canonTri T'.carrier with hC'def
  have hCr : range C.v = range T.v := u3h_canonTri_range T
  have hC'r : range C'.v = range T'.v := u3h_canonTri_range T'
  have hwT' : w ∈ T'.carrier := by
    rw [← u3h_canonTri_carrier T']
    exact spec'.subset hΔ' (subset_convexHull ℝ _ ⟨j, rfl⟩)
  have hwF : w ∈ convexHull ℝ (range T.v ∩ range T'.v) := by
    rw [← K.inter T hT T' hT']; exact ⟨hw, hwT'⟩
  have hS0 : range T.v ∩ range T'.v ⊆ range T'.v := inter_subset_right
  rcases spec'.vert Δ' hΔ' j with ⟨i, hi⟩ | ⟨i, hi1, hi2, hi3⟩
  · have hw' : w ∈ range T'.v := by rw [← hC'r]; exact ⟨i, hi.symm⟩
    obtain ⟨i', hi'⟩ := hw'
    have hmem := u3h_v_mem_convexHull T' hS0 i' (by rw [hi']; exact hwF)
    have hwT : w ∈ range C.v := by rw [hCr, ← hi']; exact hmem.1
    obtain ⟨i'', hi''⟩ := hwT
    obtain ⟨Δ₂, hΔ₂, j₂, hj₂⟩ := spec.old i''
    exact ⟨Δ₂, hΔ₂, j₂, by rw [hj₂, hi'']⟩
  · have hS0' : range T.v ∩ range T'.v ⊆ range C'.v := by rw [hC'r]; exact inter_subset_right
    obtain ⟨hA, hB⟩ := u3h_endpoints_mem C' hS0' i hi1 hwF
    have hA' : C'.v i ∈ range C.v := by rw [hCr]; exact hA.1
    have hB' : C'.v (i + 1) ∈ range C.v := by rw [hCr]; exact hB.1
    obtain ⟨a, ha⟩ := hA'
    obtain ⟨b, hb⟩ := hB'
    have hab : a ≠ b := by
      intro e; subst e
      exact u3h_fin3_ne i (u3h_v_injective C' (ha.symm.trans hb))
    rcases u3h_fin3_adj a b hab with e | e
    · subst e
      have hOpp : u3h_Opp C p r a := by
        unfold u3h_Opp at hi3 ⊢; rw [ha, hb]; exact hi3
      refine spec.cross a hOpp w ?_ hi2
      rw [ha, hb]; exact hi1
    · subst e
      have hOpp : u3h_Opp C p r b := by
        unfold u3h_Opp at hi3 ⊢; rw [ha, hb]
        rcases hi3 with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Or.inr ⟨h2, h1⟩
        · exact Or.inl ⟨h2, h1⟩
      refine spec.cross b hOpp w ?_ hi2
      rw [ha, hb, openSegment_symm]; exact hi1

/-- Refinement along one line. -/
theorem u3h_refine_one_line {X : Set Plane} (K : Triangulation X) (p : Plane) (r : ℝ) :
    ∃ K' : Triangulation X, K'.Refines K ∧ (∀ Δ ∈ K'.faces,
      Δ.carrier ⊆ {x | planeDot p x ≤ r} ∨ Δ.carrier ⊆ {x | r ≤ planeDot p x}) ∧
      ∀ Δ ∈ K'.faces, ∀ j, (∃ T ∈ K.faces, Δ.v j ∈ range T.v) ∨ planeDot p (Δ.v j) = r := by
  set F : Set Triangle := ⋃ T ∈ K.faces, u3h_pieces T.carrier p r with hFdef
  have hmem : ∀ Δ, Δ ∈ F ↔ ∃ T : Triangle, T ∈ K.faces ∧ Δ ∈ u3h_pieces T.carrier p r := by
    intro Δ; simp only [hFdef, mem_iUnion, exists_prop]
  have hsubT : ∀ T : Triangle, ∀ Δ ∈ u3h_pieces T.carrier p r, Δ.carrier ⊆ T.carrier := by
    intro T Δ hΔ
    have := (u3h_pieces_spec T.carrier p r).subset hΔ
    rwa [u3h_canonTri_carrier] at this
  have hfin : F.Finite := K.finite.biUnion (fun T _ => (u3h_pieces_spec T.carrier p r).finite)
  have hcover : (⋃ Δ ∈ F, Δ.carrier) = X := by
    apply Subset.antisymm
    · intro x hx
      obtain ⟨Δ, hΔ, hx⟩ := mem_iUnion₂.1 hx
      obtain ⟨T, hT, hΔT⟩ := (hmem Δ).1 hΔ
      rw [← K.cover]
      exact mem_iUnion₂.2 ⟨T, hT, hsubT T Δ hΔT hx⟩
    · intro x hx
      rw [← K.cover] at hx
      obtain ⟨T, hT, hxT⟩ := mem_iUnion₂.1 hx
      have spec := u3h_pieces_spec T.carrier p r
      have hxT' : x ∈ (u3h_canonTri T.carrier).carrier := by rwa [u3h_canonTri_carrier]
      rw [← spec.cover] at hxT'
      obtain ⟨Δ, hΔ, hxΔ⟩ := mem_iUnion₂.1 hxT'
      exact mem_iUnion₂.2 ⟨Δ, (hmem Δ).2 ⟨T, hT, hΔ⟩, hxΔ⟩
  have hinter : ∀ Δ ∈ F, ∀ Δ' ∈ F,
      Δ.carrier ∩ Δ'.carrier = convexHull ℝ (range Δ.v ∩ range Δ'.v) := by
    apply u3h_inter_of_family
    · intro Δ hΔ Δ' hΔ' hne
      obtain ⟨T, hT, hΔT⟩ := (hmem Δ).1 hΔ
      obtain ⟨T', hT', hΔT'⟩ := (hmem Δ').1 hΔ'
      by_cases hc : T.carrier = T'.carrier
      · rw [← hc] at hΔT'
        exact u3h_faces_separated (u3h_pieces_spec T.carrier p r).toTriangulation hΔT hΔT' hne
      · obtain ⟨q, s, hq, h1, h2⟩ := u3h_faces_separated K hT hT' hc
        refine ⟨q, s, hq, fun i => ?_, fun i => ?_⟩
        · exact u3h_carrier_subset_le T h1 (hsubT T Δ hΔT (subset_convexHull ℝ _ ⟨i, rfl⟩))
        · exact u3h_carrier_subset_ge T' h2 (hsubT T' Δ' hΔT' (subset_convexHull ℝ _ ⟨i, rfl⟩))
    · intro Δ hΔ Δ' hΔ' j hj
      obtain ⟨T, hT, hΔT⟩ := (hmem Δ).1 hΔ
      obtain ⟨T', hT', hΔT'⟩ := (hmem Δ').1 hΔ'
      have hwT : Δ'.v j ∈ T.carrier := hsubT T Δ hΔT hj
      obtain ⟨Δ₂, hΔ₂, j₂, hj₂⟩ := u3h_compat K p r hT hT' hΔT' j hwT
      have spec := u3h_pieces_spec T.carrier p r
      have hmem2 : Δ'.v j ∈ convexHull ℝ (range Δ.v ∩ range Δ₂.v) := by
        rw [← spec.inter Δ hΔT Δ₂ hΔ₂]
        exact ⟨hj, by rw [← hj₂]; exact subset_convexHull ℝ _ ⟨j₂, rfl⟩⟩
      have := u3h_v_mem_convexHull Δ₂ (S := range Δ.v ∩ range Δ₂.v) inter_subset_right j₂
        (by rw [hj₂]; exact hmem2)
      rw [hj₂] at this
      exact this.1
  refine ⟨⟨F, hfin, hcover, hinter⟩, ?_, ?_, ?_⟩
  · intro Δ hΔ
    obtain ⟨T, hT, hΔT⟩ := (hmem Δ).1 hΔ
    exact ⟨T, hT, hsubT T Δ hΔT⟩
  · intro Δ hΔ
    obtain ⟨T, hT, hΔT⟩ := (hmem Δ).1 hΔ
    rcases (u3h_pieces_spec T.carrier p r).side Δ hΔT with h | h
    · exact Or.inl (u3h_carrier_subset_le Δ h)
    · exact Or.inr (u3h_carrier_subset_ge Δ h)
  · intro Δ hΔ j
    obtain ⟨T, hT, hΔT⟩ := (hmem Δ).1 hΔ
    rcases (u3h_pieces_spec T.carrier p r).vert Δ hΔT j with ⟨i, hi⟩ | ⟨i, _, h2, _⟩
    · left; refine ⟨T, hT, ?_⟩; rw [← u3h_canonTri_range T]; exact ⟨i, hi.symm⟩
    · right; exact h2

theorem u3h_refines_trans {X : Set Plane} {K K' K'' : Triangulation X} (h1 : K''.Refines K')
    (h2 : K'.Refines K) : K''.Refines K := by
  intro T hT
  obtain ⟨T₁, hT₁, hsub⟩ := h1 T hT
  obtain ⟨T₀, hT₀, hsub'⟩ := h2 T₁ hT₁
  exact ⟨T₀, hT₀, hsub.trans hsub'⟩

theorem u3h_refine_along_lines {X : Set Plane} (K : Triangulation X) {m : ℕ} (a : Fin m → Plane)
    (c : Fin m → ℝ) :
    ∃ K' : Triangulation X, K'.Refines K ∧ (∀ T' ∈ K'.faces, ∀ j,
      T'.carrier ⊆ {x | planeDot (a j) x ≤ c j} ∨ T'.carrier ⊆ {x | c j ≤ planeDot (a j) x}) ∧
      ∀ T' ∈ K'.faces, ∀ i, (∃ T ∈ K.faces, T'.v i ∈ range T.v) ∨
        ∃ j, planeDot (a j) (T'.v i) = c j := by
  induction m generalizing K with
  | zero =>
    exact ⟨K, fun T hT => ⟨T, hT, subset_rfl⟩, fun T' _ j => j.elim0,
      fun T' hT' i => Or.inl ⟨T', hT', i, rfl⟩⟩
  | succ m ih =>
    obtain ⟨K₁, hK₁, h₁, v₁⟩ := ih K (fun j => a j.castSucc) (fun j => c j.castSucc)
    obtain ⟨K₂, hK₂, h₂, v₂⟩ := u3h_refine_one_line K₁ (a (Fin.last m)) (c (Fin.last m))
    refine ⟨K₂, u3h_refines_trans hK₂ hK₁, ?_, ?_⟩
    · intro T hT j
      obtain ⟨T₁, hT₁, hsub⟩ := hK₂ T hT
      refine Fin.lastCases ?_ (fun j => ?_) j
      · exact h₂ T hT
      · rcases h₁ T₁ hT₁ j with h | h
        · exact Or.inl (hsub.trans h)
        · exact Or.inr (hsub.trans h)
    · intro T hT i
      rcases v₂ T hT i with ⟨T₁, hT₁, ⟨k, hk⟩⟩ | h
      · rcases v₁ T₁ hT₁ k with ⟨T₀, hT₀, hk'⟩ | ⟨j, hj⟩
        · exact Or.inl ⟨T₀, hT₀, hk ▸ hk'⟩
        · exact Or.inr ⟨j.castSucc, hk ▸ hj⟩
      · exact Or.inr ⟨Fin.last m, h⟩

/-! ### U3 helpers: edge lines of a face, and refining so that faces map into faces -/

/-- Normal vector of edge `l` of `T` (inward side is `≥ u3h_edgeC`). -/
def u3h_edgeN (T : Triangle) (l : Fin 3) : Plane := u3h_dir (T.v (l + 1) - T.v l)

def u3h_edgeC (T : Triangle) (l : Fin 3) : ℝ := planeDot (u3h_edgeN T l) (T.v l)

theorem u3h_edge_eval (T : Triangle) (l : Fin 3) (x : Plane) :
    planeDot (u3h_edgeN T l) x - u3h_edgeC T l = det (T.v (l + 1) - T.v l) (x - T.v l) := by
  rw [u3h_edgeC, u3h_edgeN, u3h_det_eq_planeDot, u3h_planeDot_sub]

theorem u3h_edge_v0 (T : Triangle) (l : Fin 3) : planeDot (u3h_edgeN T l) (T.v l) = u3h_edgeC T l := rfl

theorem u3h_edge_v1 (T : Triangle) (l : Fin 3) :
    planeDot (u3h_edgeN T l) (T.v (l + 1)) = u3h_edgeC T l := by
  have := u3h_edge_eval T l (T.v (l + 1))
  rw [show det (T.v (l + 1) - T.v l) (T.v (l + 1) - T.v l) = 0 by simp [det]; ring] at this
  linarith

theorem u3h_edge_v2 (T : Triangle) (l : Fin 3) :
    u3h_edgeC T l < planeDot (u3h_edgeN T l) (T.v (l + 2)) := by
  have := u3h_edge_eval T l (T.v (l + 2))
  linarith [u3h_pos_cyc T l]

theorem u3h_edge_vertices (T : Triangle) (l i : Fin 3) :
    u3h_edgeC T l ≤ planeDot (u3h_edgeN T l) (T.v i) := by
  rcases u3h_fin3_cases l i with e | e | e
  · rw [e, u3h_edge_v0]
  · rw [e, u3h_edge_v1]
  · rw [e]; exact (u3h_edge_v2 T l).le
where
  u3h_fin3_cases : ∀ l i : Fin 3, i = l ∨ i = l + 1 ∨ i = l + 2 := by decide

theorem u3h_mem_iff_edges (T : Triangle) (x : Plane) :
    x ∈ T.carrier ↔ ∀ l, u3h_edgeC T l ≤ planeDot (u3h_edgeN T l) x := by
  rw [U1_mem_carrier_iff_det]
  have e0 : planeDot (u3h_edgeN T 0) x - u3h_edgeC T 0 = det (T.v 1 - T.v 0) (x - T.v 0) :=
    u3h_edge_eval T 0 x
  have e1 : planeDot (u3h_edgeN T 1) x - u3h_edgeC T 1 = det (T.v 2 - T.v 1) (x - T.v 1) :=
    u3h_edge_eval T 1 x
  have e2 : planeDot (u3h_edgeN T 2) x - u3h_edgeC T 2 = det (T.v 0 - T.v 2) (x - T.v 2) :=
    u3h_edge_eval T 2 x
  constructor
  · rintro ⟨h0, h1, h2⟩ l
    fin_cases l
    · simp only [Fin.zero_eta, Fin.isValue]; linarith
    · simp only [Fin.mk_one, Fin.isValue]; linarith
    · simp only [Fin.reduceFinMk]; linarith
  · intro h
    have h0 := h 0; have h1 := h 1; have h2 := h 2
    exact ⟨by linarith, by linarith, by linarith⟩

/-- The edge `l` is the face of `T` on its edge line. -/
theorem u3h_carrier_inter_edgeLine (T : Triangle) (l : Fin 3) :
    T.carrier ∩ {x | planeDot (u3h_edgeN T l) x = u3h_edgeC T l} ⊆ segment ℝ (T.v l) (T.v (l + 1)) := by
  rw [u3h_carrier_inter_line' T (u3h_edge_vertices T l)]
  have hsub : range T.v ∩ {x | planeDot (u3h_edgeN T l) x = u3h_edgeC T l} ⊆ {T.v l, T.v (l + 1)} := by
    rintro _ ⟨⟨i, rfl⟩, hi⟩
    simp only [mem_ofPred_eq] at hi
    rcases u3h_edge_vertices.u3h_fin3_cases l i with e | e | e
    · simp [e]
    · simp [e]
    · exfalso; rw [e] at hi; linarith [u3h_edge_v2 T l]
  intro x hx
  have := convexHull_mono hsub hx
  rwa [convexHull_pair] at this

/-- An interior point of a face is strictly inside every edge line. -/
theorem u3h_interior_strict (T : Triangle) {y : Plane} (hy : y ∈ T.carrier)
    (hfr : y ∉ frontier T.carrier) (l : Fin 3) : u3h_edgeC T l < planeDot (u3h_edgeN T l) y := by
  have hle := (u3h_mem_iff_edges T y).1 hy l
  rcases hle.lt_or_eq with h | h
  · exact h
  · exfalso
    apply hfr
    rw [U1_frontier_triangle]
    exact mem_iUnion.2 ⟨l, u3h_carrier_inter_edgeLine T l ⟨hy, h.symm⟩⟩

/-- **P15**: a triangle inside `Y`, on one side of every edge line of every face of a triangulation
of `Y`, lies in a single face. -/
theorem u3h_subset_face_of_sides {Y : Set Plane} (K' : Triangulation Y) (S : Triangle)
    (hSY : S.carrier ⊆ Y)
    (hside : ∀ T' ∈ K'.faces, ∀ l, (∀ i, planeDot (u3h_edgeN T' l) (S.v i) ≤ u3h_edgeC T' l) ∨
      (∀ i, u3h_edgeC T' l ≤ planeDot (u3h_edgeN T' l) (S.v i))) :
    ∃ T' ∈ K'.faces, S.carrier ⊆ T'.carrier := by
  haveI : Finite ↥K'.faces := K'.finite.to_subtype
  have hd : Dense (⋂ T' : ↥K'.faces, (frontier (T' : Triangle).carrier)ᶜ) := by
    apply dense_iInter_of_isOpen
    · intro T'; exact isClosed_frontier.isOpen_compl
    · intro T'
      rw [← interior_eq_empty_iff_dense_compl]
      exact interior_frontier (U1_triangle_isCompact _).isClosed
  obtain ⟨y, hyS, hyI⟩ := hd.inter_open_nonempty (interior S.carrier) isOpen_interior
    (U1_triangle_interior_nonempty S)
  have hyY : y ∈ Y := hSY (interior_subset hyS)
  rw [← K'.cover] at hyY
  obtain ⟨T', hT', hyT'⟩ := mem_iUnion₂.1 hyY
  have hyfr : y ∉ frontier T'.carrier := by
    have := mem_iInter.1 hyI ⟨T', hT'⟩
    exact this
  refine ⟨T', hT', fun x hx => ?_⟩
  rw [u3h_mem_iff_edges]
  intro l
  rcases hside T' hT' l with h | h
  · exfalso
    have h1 := u3h_carrier_subset_le S h (interior_subset hyS)
    have h2 := u3h_interior_strict T' hyT' hyfr l
    simp only [mem_ofPred_eq] at h1
    linarith
  · exact u3h_carrier_subset_ge S h hx

/-- The image of a face under a map affine on it. -/
theorem u3h_image_carrier (T : Triangle) {f : Plane → Plane} (h : IsPositiveAffineOn f T) :
    f '' T.carrier = (T.map f h).carrier := by
  obtain ⟨M, b, hMb⟩ := h.1
  have hv : ∀ i, (T.map f h).v i = f (T.v i) := fun i => rfl
  have h0 := hMb _ (subset_convexHull ℝ _ ⟨0, rfl⟩)
  have h1 := hMb _ (subset_convexHull ℝ _ ⟨1, rfl⟩)
  have h2 := hMb _ (subset_convexHull ℝ _ ⟨2, rfl⟩)
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨a, b', c, ha, hb, hc, habc, rfl⟩ := (u3h_mem_carrier_iff T x).1 hx
    rw [u3h_mem_carrier_iff]
    refine ⟨a, b', c, ha, hb, hc, habc, ?_⟩
    have hmem : a • T.v 0 + b' • T.v 1 + c • T.v 2 ∈ T.carrier := hx
    have hb3 : a • b + b' • b + c • b = b := by rw [← add_smul, ← add_smul, habc, one_smul]
    simp only [hv]
    rw [hMb _ hmem, h0, h1, h2]
    simp only [map_add, map_smul, smul_add]
    conv_rhs => rw [← hb3]
    abel
  · intro hy
    obtain ⟨a, b', c, ha, hb, hc, habc, rfl⟩ := (u3h_mem_carrier_iff (T.map f h) y).1 hy
    have hmem : a • T.v 0 + b' • T.v 1 + c • T.v 2 ∈ T.carrier :=
      (u3h_mem_carrier_iff T _).2 ⟨a, b', c, ha, hb, hc, habc, rfl⟩
    have hb3 : a • b + b' • b + c • b = b := by rw [← add_smul, ← add_smul, habc, one_smul]
    refine ⟨_, hmem, ?_⟩
    simp only [hv]
    rw [hMb _ hmem, h0, h1, h2]
    simp only [map_add, map_smul, smul_add]
    conv_lhs => rw [← hb3]
    abel

theorem u3h_isPositiveAffineOn_congr {f g : Plane → Plane} {T : Triangle}
    (h : ∀ x ∈ T.carrier, f x = g x) (hf : IsPositiveAffineOn f T) : IsPositiveAffineOn g T := by
  obtain ⟨⟨M, b, hMb⟩, hpos⟩ := hf
  refine ⟨⟨M, b, fun x hx => by rw [← h x hx]; exact hMb x hx⟩, ?_⟩
  rw [← h _ (subset_convexHull ℝ _ ⟨0, rfl⟩), ← h _ (subset_convexHull ℝ _ ⟨1, rfl⟩),
    ← h _ (subset_convexHull ℝ _ ⟨2, rfl⟩)]
  exact hpos

/-- The pulled-back normal: `planeDot (u3h_pull M q) x = planeDot q (M x)`. -/
def u3h_pull (M : Plane →ₗ[ℝ] Plane) (q : Plane) : Plane :=
  (planeDot q (M ((1 : ℝ), (0 : ℝ))), planeDot q (M ((0 : ℝ), (1 : ℝ))))

theorem u3h_pull_eval (M : Plane →ₗ[ℝ] Plane) (q x : Plane) :
    planeDot (u3h_pull M q) x = planeDot q (M x) := by
  have hx : x = x.1 • ((1 : ℝ), (0 : ℝ)) + x.2 • ((0 : ℝ), (1 : ℝ)) := by ext <;> simp
  conv_rhs => rw [hx]
  rw [map_add, map_smul, map_smul, u3h_planeDot_combo]
  simp [u3h_pull, planeDot]; ring

theorem u3h_refine_along_lines_finite {X : Set Plane} (K : Triangulation X) {ι : Type}
    [Finite ι] (a : ι → Plane) (c : ι → ℝ) :
    ∃ K' : Triangulation X, K'.Refines K ∧ (∀ T' ∈ K'.faces, ∀ j,
      T'.carrier ⊆ {x | planeDot (a j) x ≤ c j} ∨ T'.carrier ⊆ {x | c j ≤ planeDot (a j) x}) ∧
      ∀ T' ∈ K'.faces, ∀ i, (∃ T ∈ K.faces, T'.v i ∈ range T.v) ∨
        ∃ j, planeDot (a j) (T'.v i) = c j := by
  obtain ⟨m, ⟨e⟩⟩ := Finite.exists_equiv_fin ι
  obtain ⟨K', h1, h2, h3⟩ := u3h_refine_along_lines K (a ∘ e.symm) (c ∘ e.symm)
  refine ⟨K', h1, fun T' hT' j => ?_, fun T' hT' i => ?_⟩
  · have := h2 T' hT' (e j)
    simpa using this
  · rcases h3 T' hT' i with h | ⟨j, hj⟩
    · exact Or.inl h
    · exact Or.inr ⟨e.symm j, hj⟩

/-- Refine `K` so that every new face `T'' ⊆ T` is carried by `φ T` into one face of `K' T`. -/
theorem u3h_refine_map_into_dep {X : Set Plane} (K : Triangulation X) (φ : ↥K.faces → Plane → Plane)
    (Y : ↥K.faces → Set Plane) (K' : ∀ T : ↥K.faces, Triangulation (Y T))
    (hφ : ∀ T : ↥K.faces, IsPositiveAffineOn (φ T) T.1)
    (hY : ∀ T : ↥K.faces, φ T '' T.1.carrier ⊆ Y T) :
    ∃ K'' : Triangulation X, K''.Refines K ∧ ∀ T'' ∈ K''.faces, ∃ T : ↥K.faces,
      T''.carrier ⊆ T.1.carrier ∧ ∃ T' ∈ (K' T).faces, φ T '' T''.carrier ⊆ T'.carrier := by
  classical
  haveI : Finite ↥K.faces := K.finite.to_subtype
  have hMb : ∀ T : ↥K.faces, ∃ (M : Plane →ₗ[ℝ] Plane) (b : Plane),
      ∀ x ∈ T.1.carrier, φ T x = M x + b := fun T => (hφ T).1
  choose M b hMb using hMb
  haveI : ∀ T : ↥K.faces, Finite ↥(K' T).faces := fun T => (K' T).finite.to_subtype
  let ι := Σ T : ↥K.faces, ↥(K' T).faces × Fin 3
  let a : ι → Plane := fun i => u3h_pull (M i.1) (u3h_edgeN i.2.1.1 i.2.2)
  let c : ι → ℝ := fun i => u3h_edgeC i.2.1.1 i.2.2 - planeDot (u3h_edgeN i.2.1.1 i.2.2) (b i.1)
  obtain ⟨K'', hK'', hside, -⟩ := u3h_refine_along_lines_finite K a c
  refine ⟨K'', hK'', fun T'' hT'' => ?_⟩
  obtain ⟨T₀, hT₀, hsub⟩ := hK'' T'' hT''
  let T : ↥K.faces := ⟨T₀, hT₀⟩
  refine ⟨T, hsub, ?_⟩
  have hφ'' : IsPositiveAffineOn (φ T) T'' := U1_isPositiveAffineOn_mono (hφ T) hsub
  have hSc : (T''.map (φ T) hφ'').carrier = φ T '' T''.carrier := (u3h_image_carrier T'' hφ'').symm
  have hSY : (T''.map (φ T) hφ'').carrier ⊆ Y T := by
    rw [hSc]; exact (image_mono hsub).trans (hY T)
  have hsides : ∀ T' ∈ (K' T).faces, ∀ l,
      (∀ i, planeDot (u3h_edgeN T' l) ((T''.map (φ T) hφ'').v i) ≤ u3h_edgeC T' l) ∨
      (∀ i, u3h_edgeC T' l ≤ planeDot (u3h_edgeN T' l) ((T''.map (φ T) hφ'').v i)) := by
    intro T' hT' l
    have key : ∀ i, planeDot (u3h_edgeN T' l) ((T''.map (φ T) hφ'').v i) - u3h_edgeC T' l =
        planeDot (a ⟨T, ⟨T', hT'⟩, l⟩) (T''.v i) - c ⟨T, ⟨T', hT'⟩, l⟩ := by
      intro i
      have hvi : T''.v i ∈ T₀.carrier := hsub (subset_convexHull ℝ _ ⟨i, rfl⟩)
      show planeDot (u3h_edgeN T' l) (φ T (T''.v i)) - u3h_edgeC T' l = _
      rw [hMb T _ hvi]
      simp only [a, c]
      rw [u3h_planeDot_add, u3h_pull_eval]; ring
    rcases hside T'' hT'' ⟨T, ⟨T', hT'⟩, l⟩ with h | h
    · left; intro i
      have := h (subset_convexHull ℝ _ ⟨i, rfl⟩)
      simp only [mem_ofPred_eq] at this
      linarith [key i]
    · right; intro i
      have := h (subset_convexHull ℝ _ ⟨i, rfl⟩)
      simp only [mem_ofPred_eq] at this
      linarith [key i]
  obtain ⟨T', hT', hST'⟩ := u3h_subset_face_of_sides (K' T) _ hSY hsides
  exact ⟨T', hT', by rw [← hSc]; exact hST'⟩

theorem u3h_refine_map_into {X Y : Set Plane} (K : Triangulation X) (K' : Triangulation Y)
    {f : Plane → Plane} (hf : ∀ T ∈ K.faces, IsPositiveAffineOn f T) (h : f '' X ⊆ Y) :
    ∃ K'' : Triangulation X, K''.Refines K ∧ ∀ T'' ∈ K''.faces, ∃ T ∈ K.faces,
      T''.carrier ⊆ T.carrier ∧ ∃ T' ∈ K'.faces, f '' T''.carrier ⊆ T'.carrier := by
  have hX : ∀ T : ↥K.faces, T.1.carrier ⊆ X := fun T => by
    have := subset_biUnion_of_mem (u := fun T : Triangle => T.carrier) T.2
    rwa [K.cover] at this
  obtain ⟨K'', h1, h2⟩ := u3h_refine_map_into_dep K (fun _ => f) (fun _ => Y) (fun _ => K')
    (fun T => hf T.1 T.2) (fun T => (image_mono (hX T)).trans h)
  refine ⟨K'', h1, fun T'' hT'' => ?_⟩
  obtain ⟨T, hsub, T', hT', himg⟩ := h2 T'' hT''
  exact ⟨T.1, T.2, hsub, T', hT', himg⟩

theorem u3h_chartPart_image {L : ℝ} {S : Set Sphere} {D : Set Plane} {f : Sphere → Plane}
    (hfD : f '' S ⊆ D) (b : Bool) : (f ∘ modelChart L b) '' chartPart L b S ⊆ D := by
  rintro _ ⟨x, ⟨_, hx⟩, rfl⟩
  exact hfD ⟨modelChart L b x, hx, rfl⟩

/-- U3 (sm-3:462-466 "subdivide"): a triangulation can be refined so that every face lies on one
side of each of finitely many lines `{x | ⟪a j, x⟫ = c j}`. -/
theorem U3_refine_along_lines {X : Set Plane} (K : Triangulation X) {m : ℕ} (a : Fin m → Plane)
    (c : Fin m → ℝ) :
    ∃ K' : Triangulation X, K'.Refines K ∧ ∀ T' ∈ K'.faces, ∀ j,
      T'.carrier ⊆ {x | planeDot (a j) x ≤ c j} ∨ T'.carrier ⊆ {x | c j ≤ planeDot (a j) x} := by
  obtain ⟨K', h1, h2, -⟩ := u3h_refine_along_lines K a c
  exact ⟨K', h1, h2⟩

/-- U3: a triangulation can be refined so that every face lies in one face of a second
triangulation of a superset. -/
theorem U3_refine_into {X Y : Set Plane} (K : Triangulation X) (K' : Triangulation Y) (h : X ⊆ Y) :
    ∃ K'' : Triangulation X, K''.Refines K ∧ ∀ T'' ∈ K''.faces, ∃ T' ∈ K'.faces, T''.carrier ⊆ T'.carrier := by
  have hid : ∀ T ∈ K.faces, IsPositiveAffineOn id T :=
    fun T _ => ⟨⟨LinearMap.id, 0, fun x _ => by simp⟩, T.pos⟩
  obtain ⟨K'', h1, h2⟩ := u3h_refine_map_into K K' hid (by rw [image_id]; exact h)
  refine ⟨K'', h1, fun T'' hT'' => ?_⟩
  obtain ⟨T, _, _, T', hT', himg⟩ := h2 T'' hT''
  exact ⟨T', hT', by rw [image_id] at himg; exact himg⟩

/-- U3 (common refinement): two triangulations of the same set have a common refinement. -/
theorem U3_common_refinement {X : Set Plane} (K K' : Triangulation X) :
    ∃ K'' : Triangulation X, K''.Refines K ∧ K''.Refines K' := by
  obtain ⟨K'', h1, h2⟩ := U3_refine_into K K' subset_rfl
  exact ⟨K'', h1, h2⟩

/-- U3 (sm-3:535-537, composition): the composite of positive PL maps is positive PL on a
refinement of the source triangulation. -/
theorem U3_isPositivePLOn_comp {X Y : Set Plane} (K : Triangulation X) (K' : Triangulation Y)
    {f g : Plane → Plane} (hf : IsPositivePLOn f K) (hg : IsPositivePLOn g K') (h : f '' X ⊆ Y) :
    ∃ K'' : Triangulation X, K''.Refines K ∧ IsPositivePLOn (g ∘ f) K'' := by
  obtain ⟨K'', h1, h2⟩ := u3h_refine_map_into K K' hf h
  refine ⟨K'', h1, fun T'' hT'' => ?_⟩
  obtain ⟨T, hT, hsub, T', hT', himg⟩ := h2 T'' hT''
  have hf'' : IsPositiveAffineOn f T'' := U1_isPositiveAffineOn_mono (hf T hT) hsub
  have hg' : IsPositiveAffineOn g (T''.map f hf'') :=
    U1_isPositiveAffineOn_mono (hg T' hT') (by rw [← u3h_image_carrier T'' hf'']; exact himg)
  exact U1_isPositiveAffineOn_comp hf'' hg'

/-- U3 (chart bookkeeping, FR-TD-14): a positive PL map to the plane followed by a positive PL map
from the plane into the sphere is a positive PL sphere map. -/
theorem U3_isPositivePLSphereMap_comp {L L' : ℝ} {S : Set Sphere} {D : Set Plane}
    {f : Sphere → Plane} {g : Plane → Sphere} (hf : IsPositivePLToPlane L S f) (hfD : f '' S ⊆ D)
    (hg : IsPositivePLFromPlane L' D g) : IsPositivePLSphereMap L L' S (g ∘ f) := by
  intro b
  obtain ⟨Kb, hKb⟩ := hf b
  obtain ⟨Kg, hKg⟩ := hg
  obtain ⟨K'', _, h2⟩ := u3h_refine_map_into Kb Kg hKb (u3h_chartPart_image hfD b)
  refine ⟨K'', fun T'' hT'' => ?_⟩
  obtain ⟨T, hT, hsub, Tg, hTg, himg'⟩ := h2 T'' hT''
  obtain ⟨b', hmem, hpos⟩ := hKg Tg hTg
  refine ⟨b', fun x hx => hmem _ (himg' ⟨x, hx, rfl⟩), ?_⟩
  have hf'' : IsPositiveAffineOn (f ∘ modelChart L b) T'' :=
    U1_isPositiveAffineOn_mono (hKb T hT) hsub
  have hg' : IsPositiveAffineOn (modelChartInv L' b' ∘ g) (T''.map _ hf'') :=
    U1_isPositiveAffineOn_mono hpos (by rw [← u3h_image_carrier T'' hf'']; exact himg')
  exact u3h_isPositiveAffineOn_congr (fun x _ => rfl) (U1_isPositiveAffineOn_comp hf'' hg')


/-! ### U3 helpers: chart algebra for the model (any `L ≠ 0`) -/

theorem u3h_supNorm_nonneg (y : Plane) : 0 ≤ supNorm y := le_max_of_le_left (abs_nonneg _)

theorem u3h_supNorm_eq_zero {y : Plane} (h : supNorm y = 0) : y = 0 := by
  unfold supNorm at h
  have h1 : |y.1| ≤ 0 := by rw [← h]; exact le_max_left _ _
  have h2 : |y.2| ≤ 0 := by rw [← h]; exact le_max_right _ _
  exact Prod.ext (abs_nonpos_iff.1 h1) (abs_nonpos_iff.1 h2)

theorem u3h_supNorm_pos {y : Plane} (h : y ≠ 0) : 0 < supNorm y :=
  lt_of_le_of_ne (u3h_supNorm_nonneg y) (fun e => h (u3h_supNorm_eq_zero e.symm))

theorem u3h_supNorm_smul (c : ℝ) (y : Plane) : supNorm (c • y) = |c| * supNorm y := by
  unfold supNorm
  simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, abs_mul]
  rcases le_total |y.1| |y.2| with h | h
  · rw [max_eq_right h, max_eq_right (mul_le_mul_of_nonneg_left h (abs_nonneg c))]
  · rw [max_eq_left h, max_eq_left (mul_le_mul_of_nonneg_left h (abs_nonneg c))]

theorem u3h_supNorm_swap (y : Plane) : supNorm (y.1, -y.2) = supNorm y := by
  unfold supNorm; simp [abs_neg]

theorem u3h_capInvFun_capInvFun {L : ℝ} (hL : L ≠ 0) {y : Plane} (hy : y ≠ 0) :
    capInvFun L (capInvFun L y) = y := by
  have hN := u3h_supNorm_pos hy
  have hw : supNorm (capInvFun L y) = |L / supNorm y ^ 2| * supNorm y := by
    rw [capInvFun, u3h_supNorm_smul, u3h_supNorm_swap]
  rw [capInvFun, hw]
  simp only [capInvFun]
  ext
  · simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, mul_pow, sq_abs]
    field_simp
  · simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, mul_pow, sq_abs]
    field_simp

theorem u3h_chartInv_chart {L : ℝ} (hL : L ≠ 0) (b : Bool) (y : Plane) :
    modelChartInv L b (modelChart L b y) = y := by
  cases b
  · rfl
  · show modelChartInv L true (capChart L y) = y
    unfold capChart
    split_ifs with h
    · subst h; rfl
    · show capInvFun L (capInvFun L y) = y
      exact u3h_capInvFun_capInvFun hL h

theorem u3h_chart_chartInv {L : ℝ} (hL : L ≠ 0) (b : Bool) {z : Sphere}
    (hz : z ∈ modelChart L b '' modelDomain L b) : modelChart L b (modelChartInv L b z) = z := by
  obtain ⟨y, _, rfl⟩ := hz
  rw [u3h_chartInv_chart hL]

theorem u3h_chartInv_mem {L : ℝ} (hL : L ≠ 0) (b : Bool) {z : Sphere}
    (hz : z ∈ modelChart L b '' modelDomain L b) : modelChartInv L b z ∈ modelDomain L b := by
  obtain ⟨y, hy, rfl⟩ := hz
  rw [u3h_chartInv_chart hL]; exact hy

/-- At `L = 0` both chart inverses vanish on the chart images. -/
theorem u3h_chartInv_zero (b : Bool) {z : Sphere} (hz : z ∈ modelChart 0 b '' modelDomain 0 b) :
    modelChartInv 0 b z = 0 := by
  obtain ⟨y, hy, rfl⟩ := hz
  cases b
  · have : y = 0 := u3h_supNorm_eq_zero (le_antisymm hy (u3h_supNorm_nonneg y))
    subst this; rfl
  · show modelChartInv 0 true (capChart 0 y) = 0
    unfold capChart
    split_ifs with h
    · rfl
    · show capInvFun 0 (capInvFun 0 y) = 0
      simp [capInvFun]

theorem u3h_face_subset_chartPart {L : ℝ} {b : Bool} {S : Set Sphere}
    (K : Triangulation (chartPart L b S)) {T : Triangle} (hT : T ∈ K.faces) :
    T.carrier ⊆ chartPart L b S := by
  have := subset_biUnion_of_mem (u := fun T : Triangle => T.carrier) hT
  rwa [K.cover] at this


/-- U3: a positive PL sphere map followed by a positive PL map to the plane is positive PL to the
plane. -/
theorem U3_isPositivePLToPlane_comp {L L' : ℝ} {S S' : Set Sphere} {F : Sphere → Sphere}
    {f : Sphere → Plane} (hF : IsPositivePLSphereMap L L' S F) (hFS : F '' S ⊆ S')
    (hf : IsPositivePLToPlane L' S' f) : IsPositivePLToPlane L S (f ∘ F) := by
  intro b
  obtain ⟨Kb, hKb⟩ := hF b
  by_cases hL' : L' = 0
  · refine ⟨Kb, fun T hT => ?_⟩
    exfalso
    obtain ⟨b', hmem, hpos⟩ := hKb T hT
    subst hL'
    have h0 : ∀ i, (modelChartInv 0 b' ∘ F ∘ modelChart L b) (T.v i) = 0 := fun i =>
      u3h_chartInv_zero b' (hmem _ (subset_convexHull ℝ _ ⟨i, rfl⟩))
    have := hpos.2
    rw [h0 0, h0 1, h0 2] at this
    simp [det] at this
  choose b' hmem hpos using hKb
  choose Kf hKf using hf
  have hsubS : ∀ T : ↥Kb.faces, ∀ x ∈ T.1.carrier, modelChart L b x ∈ S := fun T x hx =>
    (u3h_face_subset_chartPart Kb T.2 hx).2
  obtain ⟨K'', _, h2⟩ := u3h_refine_map_into_dep Kb
    (fun T => modelChartInv L' (b' T.1 T.2) ∘ F ∘ modelChart L b)
    (fun T => chartPart L' (b' T.1 T.2) S') (fun T => Kf (b' T.1 T.2)) (fun T => hpos T.1 T.2)
    (by
      rintro T _ ⟨x, hx, rfl⟩
      have hz := hmem T.1 T.2 x hx
      refine ⟨u3h_chartInv_mem hL' _ hz, ?_⟩
      show modelChart L' (b' T.1 T.2) (modelChartInv L' (b' T.1 T.2) (F (modelChart L b x))) ∈ S'
      rw [u3h_chart_chartInv hL' _ hz]
      exact hFS ⟨_, hsubS T x hx, rfl⟩)
  refine ⟨K'', fun T'' hT'' => ?_⟩
  obtain ⟨T, hsub, T', hT', himg⟩ := h2 T'' hT''
  have hφ'' : IsPositiveAffineOn (modelChartInv L' (b' T.1 T.2) ∘ F ∘ modelChart L b) T'' :=
    U1_isPositiveAffineOn_mono (hpos T.1 T.2) hsub
  have hψ : IsPositiveAffineOn (f ∘ modelChart L' (b' T.1 T.2)) (T''.map _ hφ'') :=
    U1_isPositiveAffineOn_mono (hKf (b' T.1 T.2) T' hT')
      (by rw [← u3h_image_carrier T'' hφ'']; exact himg)
  refine u3h_isPositiveAffineOn_congr (fun x hx => ?_) (U1_isPositiveAffineOn_comp hφ'' hψ)
  show f (modelChart L' (b' T.1 T.2) (modelChartInv L' (b' T.1 T.2) (F (modelChart L b x)))) =
    f (F (modelChart L b x))
  rw [u3h_chart_chartInv hL' _ (hmem T.1 T.2 x (hsub hx))]

/-- U3: a positive PL map to the plane followed by a positive PL plane map is positive PL to the
plane. -/
theorem U3_isPositivePLToPlane_comp_plane {L : ℝ} {S : Set Sphere} {D : Set Plane}
    (K : Triangulation D) {f : Sphere → Plane} {g : Plane → Plane} (hf : IsPositivePLToPlane L S f)
    (hfD : f '' S ⊆ D) (hg : IsPositivePLOn g K) : IsPositivePLToPlane L S (g ∘ f) := by
  intro b
  obtain ⟨Kb, hKb⟩ := hf b
  obtain ⟨K'', _, hK''⟩ := U3_isPositivePLOn_comp Kb K hKb hg (u3h_chartPart_image hfD b)
  exact ⟨K'', hK''⟩


/-! ### U3 helpers: the model square, its seam, and inverses of affine maps -/

theorem u3h_norm_eq_supNorm (x : Plane) : ‖x‖ = supNorm x := by
  rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]; rfl

theorem u3h_interior_square_subset (q : ℝ) : interior (square q) ⊆ {x | supNorm x < q} := by
  intro x hx
  rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff] at hx
  obtain ⟨δ, hδ, hball⟩ := hx
  simp only [mem_ofPred_eq]
  by_cases hx0 : x = 0
  · subst hx0
    have hmem : ((δ / 2, 0) : Plane) ∈ square q := by
      apply hball
      rw [Metric.mem_ball, dist_eq_norm, sub_zero, u3h_norm_eq_supNorm]
      rw [show supNorm ((δ / 2, 0) : Plane) = δ / 2 by
        simp [supNorm, abs_of_pos (half_pos hδ), (half_pos hδ).le]]
      linarith
    have : supNorm ((δ / 2, 0) : Plane) ≤ q := hmem
    have h2 : supNorm ((δ / 2, 0) : Plane) = δ / 2 := by
      simp [supNorm, abs_of_pos (half_pos hδ), (half_pos hδ).le]
    rw [h2] at this
    simp [supNorm]; linarith
  · have hN := u3h_supNorm_pos hx0
    set N := supNorm x with hN'
    have hmem : (1 + δ / (2 * N)) • x ∈ square q := by
      apply hball
      rw [Metric.mem_ball, dist_eq_norm, u3h_norm_eq_supNorm]
      have : (1 + δ / (2 * N)) • x - x = (δ / (2 * N)) • x := by
        rw [add_smul, one_smul, add_sub_cancel_left]
      rw [this, u3h_supNorm_smul, abs_of_pos (by positivity), ← hN']
      field_simp
      try norm_num
    have : supNorm ((1 + δ / (2 * N)) • x) ≤ q := hmem
    rw [u3h_supNorm_smul, abs_of_pos (by positivity), ← hN'] at this
    have : N + δ / 2 ≤ q := by
      have e : (1 + δ / (2 * N)) * N = N + δ / 2 := by field_simp; try ring
      linarith
    linarith

theorem u3h_face_interior_supNorm_lt {L : ℝ} {b : Bool} {S : Set Sphere}
    (K : Triangulation (chartPart L b S)) {T : Triangle} (hT : T ∈ K.faces) {x : Plane}
    (hx : x ∈ interior T.carrier) : supNorm x < (if b then 1 else L) := by
  have h1 := U2_interior_face_subset_interior K hT hx
  have h2 : chartPart L b S ⊆ square (if b then 1 else L) := by
    intro y hy; cases b <;> exact hy.1
  exact u3h_interior_square_subset _ (interior_mono h2 h1)

theorem u3h_extreme_coord {a b s q t : ℝ} (ha : |a| ≤ q) (hb : |b| ≤ q) (ht0 : 0 < t) (ht1 : t < 1)
    (hs : s = (1 - t) * a + t * b) (hsq : |s| = q) : a = s ∧ b = s := by
  rw [abs_le] at ha hb
  rcases abs_eq (by linarith [abs_nonneg s] : (0 : ℝ) ≤ q) |>.1 hsq with h | h
  · constructor <;> nlinarith
  · constructor <;> nlinarith

theorem u3h_between_neg {a b s t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (hs : s = (1 - t) * a + t * b)
    (hab : a ≠ b) : (a - s) * (b - s) < 0 := by
  have e : (a - s) * (b - s) = -(t * (1 - t) * (a - b) ^ 2) := by rw [hs]; ring
  rw [e]
  have : 0 < (a - b) ^ 2 := by
    have : a - b ≠ 0 := sub_ne_zero.2 hab
    positivity
  have : 0 < t * (1 - t) := mul_pos ht0 (by linarith)
  nlinarith

/-- **Claim V**: a point of a face on the boundary of the square, with the face on one side of a
line through it that is transversal to the sides, is a vertex. -/
theorem u3h_seam_vertex {q : ℝ} (T : Triangle) (hT : T.carrier ⊆ square q) {s : Plane}
    (hs : s ∈ T.carrier) (hsq : supNorm s = q) {p : Plane} (hp1 : p.1 ≠ 0) (hp2 : p.2 ≠ 0)
    (hside : (∀ i, planeDot p (T.v i) ≤ planeDot p s) ∨ (∀ i, planeDot p s ≤ planeDot p (T.v i))) :
    s ∈ range T.v := by
  have hnot : s ∉ interior T.carrier := fun h => by
    have := u3h_interior_square_subset q (interior_mono hT h)
    simp only [mem_ofPred_eq] at this; linarith
  have hfr : s ∈ frontier T.carrier := ⟨subset_closure hs, hnot⟩
  rw [U1_frontier_triangle] at hfr
  obtain ⟨i, hi⟩ := mem_iUnion.1 hfr
  obtain ⟨α, β, hα, hβ, hαβ, hsab⟩ := hi
  by_cases hβ0 : β = 0
  · subst hβ0
    have : α = 1 := by linarith
    subst this; exact ⟨i, by simpa using hsab⟩
  by_cases hα0 : α = 0
  · subst hα0
    have : β = 1 := by linarith
    subst this; exact ⟨i + 1, by simpa using hsab⟩
  exfalso
  have ht0 : 0 < β := lt_of_le_of_ne hβ (Ne.symm hβ0)
  have ht1 : β < 1 := by
    have : 0 < α := lt_of_le_of_ne hα (Ne.symm hα0)
    linarith
  have hα' : α = 1 - β := by linarith
  subst hα'
  set a := T.v i with ha
  set b := T.v (i + 1) with hb
  have haQ : a ∈ square q := hT (subset_convexHull ℝ _ ⟨i, rfl⟩)
  have hbQ : b ∈ square q := hT (subset_convexHull ℝ _ ⟨i + 1, rfl⟩)
  have hab : a ≠ b := fun e => u3h_fin3_ne i (u3h_v_injective T e)
  have hs1 : s.1 = (1 - β) * a.1 + β * b.1 := by rw [← hsab]; simp
  have hs2 : s.2 = (1 - β) * a.2 + β * b.2 := by rw [← hsab]; simp
  have haQ' : |a.1| ≤ q ∧ |a.2| ≤ q := ⟨le_trans (le_max_left _ _) haQ, le_trans (le_max_right _ _) haQ⟩
  have hbQ' : |b.1| ≤ q ∧ |b.2| ≤ q := ⟨le_trans (le_max_left _ _) hbQ, le_trans (le_max_right _ _) hbQ⟩
  have hsi : planeDot p a - planeDot p s = p.1 * (a.1 - s.1) + p.2 * (a.2 - s.2) := by
    simp [planeDot]; ring
  have hsj : planeDot p b - planeDot p s = p.1 * (b.1 - s.1) + p.2 * (b.2 - s.2) := by
    simp [planeDot]; ring
  have hopp : (planeDot p a - planeDot p s) * (planeDot p b - planeDot p s) < 0 := by
    rcases max_choice |s.1| |s.2| with h | h
    · have hq1 : |s.1| = q := by rw [← h]; exact hsq
      obtain ⟨e1, e2⟩ := u3h_extreme_coord haQ'.1 hbQ'.1 ht0 ht1 hs1 hq1
      have hne : a.2 ≠ b.2 := fun e => hab (Prod.ext (e1.trans e2.symm) e)
      have := u3h_between_neg ht0 ht1 hs2 hne
      rw [hsi, hsj, e1, e2, sub_self, mul_zero, zero_add, zero_add]
      have hp := mul_self_pos.2 hp2
      nlinarith
    · have hq2 : |s.2| = q := by rw [← h]; exact hsq
      obtain ⟨e1, e2⟩ := u3h_extreme_coord haQ'.2 hbQ'.2 ht0 ht1 hs2 hq2
      have hne : a.1 ≠ b.1 := fun e => hab (Prod.ext e (e1.trans e2.symm))
      have := u3h_between_neg ht0 ht1 hs1 hne
      rw [hsi, hsj, e1, e2, sub_self, mul_zero, add_zero, add_zero]
      have hp := mul_self_pos.2 hp1
      nlinarith
  rcases hside with h | h
  · have h1 := h i; have h2 := h (i + 1)
    rw [← ha] at h1; rw [← hb] at h2
    nlinarith
  · have h1 := h i; have h2 := h (i + 1)
    rw [← ha] at h1; rw [← hb] at h2
    nlinarith

theorem u3h_supNorm_capInvFun {L : ℝ} (hL : 0 < L) {x : Plane} (hx : x ≠ 0) :
    supNorm (capInvFun L x) = L / supNorm x := by
  have hN := u3h_supNorm_pos hx
  rw [capInvFun, u3h_supNorm_smul, u3h_supNorm_swap, abs_of_pos (by positivity)]
  field_simp

theorem u3h_capInvFun_ne_zero {L : ℝ} (hL : 0 < L) {x : Plane} (hx : x ≠ 0) : capInvFun L x ≠ 0 := by
  intro h
  have := u3h_supNorm_capInvFun hL hx
  rw [h] at this
  have hN := u3h_supNorm_pos hx
  have : (0 : ℝ) = L / supNorm x := by simpa [supNorm] using this
  have : 0 < L / supNorm x := by positivity
  linarith

/-- The two charts cover the sphere. -/
theorem u3h_sphere_cover {L : ℝ} (hL : 0 < L) (z : Sphere) :
    ∃ b : Bool, z ∈ modelChart L b '' modelDomain L b := by
  induction z using OnePoint.rec with
  | infty =>
    refine ⟨true, 0, ?_, ?_⟩
    · show supNorm 0 ≤ 1; simp [supNorm]
    · show capChart L 0 = ∞; simp [capChart]
  | coe x =>
    by_cases hx : supNorm x ≤ L
    · exact ⟨false, x, hx, rfl⟩
    · push Not at hx
      have hx0 : x ≠ 0 := by
        rintro rfl; simp [supNorm] at hx; linarith
      refine ⟨true, capInvFun L x, ?_, ?_⟩
      · show supNorm (capInvFun L x) ≤ 1
        rw [u3h_supNorm_capInvFun hL hx0]
        have := u3h_supNorm_pos hx0
        rw [div_le_one this]; exact hx.le
      · show capChart L (capInvFun L x) = (x : Sphere)
        unfold capChart
        rw [if_neg (u3h_capInvFun_ne_zero hL hx0), u3h_capInvFun_capInvFun hL.ne' hx0]

/-- The seam: a point in both chart images. -/
theorem u3h_seam {L : ℝ} (hL : 0 < L) {x y : Plane} (hx : x ∈ square L) (hy1 : y ∈ square 1)
    (h : ((x : Plane) : Sphere) = capChart L y) :
    y ≠ 0 ∧ x = capInvFun L y ∧ supNorm x = L ∧ supNorm y = 1 := by
  unfold capChart at h
  split_ifs at h with hy
  · exact absurd h (by simp)
  · have hxy : x = capInvFun L y := OnePoint.coe_eq_coe.1 h
    have hNy := u3h_supNorm_pos hy
    have hsx : supNorm x = L / supNorm y := by rw [hxy]; exact u3h_supNorm_capInvFun hL hy
    have hxL : supNorm x ≤ L := hx
    have hy1' : supNorm y ≤ 1 := hy1
    have hge : L ≤ L / supNorm y := by
      rw [le_div_iff₀ hNy]; nlinarith
    have hxL' : supNorm x = L := by linarith
    refine ⟨hy, hxy, hxL', ?_⟩
    have : L / supNorm y = L := by linarith
    field_simp at this
    nlinarith

theorem u3h_linear_decomp (M : Plane →ₗ[ℝ] Plane) (u : Plane) :
    M u = u.1 • M ((1 : ℝ), (0 : ℝ)) + u.2 • M ((0 : ℝ), (1 : ℝ)) := by
  conv_lhs => rw [show u = u.1 • ((1 : ℝ), (0 : ℝ)) + u.2 • ((0 : ℝ), (1 : ℝ)) by ext <;> simp]
  rw [map_add, map_smul, map_smul]

theorem u3h_det_map (M : Plane →ₗ[ℝ] Plane) (u w : Plane) :
    det (M u) (M w) = det (M ((1 : ℝ), (0 : ℝ))) (M ((0 : ℝ), (1 : ℝ))) * det u w := by
  rw [u3h_linear_decomp M u, u3h_linear_decomp M w]
  simp [det]; ring

/-- A linear map of the plane with nonzero determinant has a linear left inverse. -/
theorem u3h_exists_linear_inverse (M : Plane →ₗ[ℝ] Plane)
    (hM : det (M ((1 : ℝ), (0 : ℝ))) (M ((0 : ℝ), (1 : ℝ))) ≠ 0) :
    ∃ N : Plane →ₗ[ℝ] Plane, ∀ x, N (M x) = x := by
  set a := (M ((1 : ℝ), (0 : ℝ))).1 with ha
  set c := (M ((1 : ℝ), (0 : ℝ))).2 with hc
  set b := (M ((0 : ℝ), (1 : ℝ))).1 with hb
  set d := (M ((0 : ℝ), (1 : ℝ))).2 with hd
  have hdet : a * d - c * b ≠ 0 := by simpa [det] using hM
  let N : Plane →ₗ[ℝ] Plane :=
    { toFun := fun y => ((d * y.1 - b * y.2) / (a * d - c * b), (-c * y.1 + a * y.2) / (a * d - c * b))
      map_add' := by intro y z; ext <;> simp <;> ring
      map_smul' := by intro r y; ext <;> simp <;> ring }
  refine ⟨N, fun x => ?_⟩
  have hx : M x = (a * x.1 + b * x.2, c * x.1 + d * x.2) := by
    rw [u3h_linear_decomp M x]; ext <;> simp [ha, hb, hc, hd] <;> ring
  ext
  · simp only [N, hx, LinearMap.coe_mk, AddHom.coe_mk]
    rw [div_eq_iff hdet]; ring
  · simp only [N, hx, LinearMap.coe_mk, AddHom.coe_mk]
    rw [div_eq_iff hdet]; ring

/-- The inverse of a positive affine map on a face is affine on the image face. -/
theorem u3h_affine_inverse (T : Triangle) {f : Plane → Plane} (h : IsPositiveAffineOn f T)
    {g : Plane → Plane} (hg : ∀ x ∈ T.carrier, g (f x) = x) :
    IsPositiveAffineOn g (T.map f h) := by
  obtain ⟨⟨M, b, hMb⟩, hpos⟩ := id h
  have hv : ∀ i, (T.map f h).v i = f (T.v i) := fun i => rfl
  have hdetM : det (M ((1 : ℝ), (0 : ℝ))) (M ((0 : ℝ), (1 : ℝ))) ≠ 0 := by
    intro h0
    have e : f (T.v 1) - f (T.v 0) = M (T.v 1 - T.v 0) := by
      rw [hMb _ (subset_convexHull ℝ _ ⟨1, rfl⟩), hMb _ (subset_convexHull ℝ _ ⟨0, rfl⟩), map_sub]
      abel
    have e' : f (T.v 2) - f (T.v 0) = M (T.v 2 - T.v 0) := by
      rw [hMb _ (subset_convexHull ℝ _ ⟨2, rfl⟩), hMb _ (subset_convexHull ℝ _ ⟨0, rfl⟩), map_sub]
      abel
    rw [e, e', u3h_det_map, h0, zero_mul] at hpos
    exact lt_irrefl _ hpos
  obtain ⟨N, hN⟩ := u3h_exists_linear_inverse M hdetM
  refine ⟨⟨N, -N b, ?_⟩, ?_⟩
  · intro y hy
    rw [← u3h_image_carrier T h] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    rw [hg x hx, hMb x hx, map_add, hN]; abel
  · simp only [hv]
    rw [hg _ (subset_convexHull ℝ _ ⟨0, rfl⟩), hg _ (subset_convexHull ℝ _ ⟨1, rfl⟩),
      hg _ (subset_convexHull ℝ _ ⟨2, rfl⟩)]
    exact T.pos

theorem u3h_continuous_planeDot (p : Plane) : Continuous (planeDot p) := by
  unfold planeDot; fun_prop

theorem u3h_mem_interior_iff (Δ : Triangle) (y : Plane) :
    y ∈ interior Δ.carrier ↔ ∀ l, u3h_edgeC Δ l < planeDot (u3h_edgeN Δ l) y := by
  constructor
  · intro hy l
    exact u3h_interior_strict Δ (interior_subset hy)
      (fun h => (Set.disjoint_left.1 disjoint_interior_frontier) hy h) l
  · intro h
    have hopen : IsOpen {y : Plane | ∀ l, u3h_edgeC Δ l < planeDot (u3h_edgeN Δ l) y} := by
      have : {y : Plane | ∀ l, u3h_edgeC Δ l < planeDot (u3h_edgeN Δ l) y} =
          ⋂ l, {y | u3h_edgeC Δ l < planeDot (u3h_edgeN Δ l) y} := by ext; simp
      rw [this]
      exact isOpen_iInter_of_finite fun l => isOpen_lt continuous_const (u3h_continuous_planeDot _)
    exact interior_maximal (fun y hy => (u3h_mem_iff_edges Δ y).2 fun l => (hy l).le) hopen h

theorem u3h_detM_pos (T : Triangle) {φ : Plane → Plane} (h : IsPositiveAffineOn φ T)
    {M : Plane →ₗ[ℝ] Plane} {c : Plane} (hMc : ∀ x ∈ T.carrier, φ x = M x + c) :
    0 < det (M ((1 : ℝ), (0 : ℝ))) (M ((0 : ℝ), (1 : ℝ))) := by
  have hpos := h.2
  have e : ∀ i, φ (T.v i) - φ (T.v 0) = M (T.v i - T.v 0) := fun i => by
    rw [hMc _ (subset_convexHull ℝ _ ⟨i, rfl⟩), hMc _ (subset_convexHull ℝ _ ⟨0, rfl⟩), map_sub]
    abel
  rw [e 1, e 2, u3h_det_map] at hpos
  by_contra hn; push Not at hn
  nlinarith [T.pos, mul_nonpos_of_nonpos_of_nonneg hn T.pos.le]

/-- An affine map on a face carries interior points to interior points of the image, and only them. -/
theorem u3h_interior_map (T : Triangle) {φ : Plane → Plane} (h : IsPositiveAffineOn φ T) {t : Plane}
    (ht : t ∈ T.carrier) : φ t ∈ interior (T.map φ h).carrier ↔ t ∈ interior T.carrier := by
  obtain ⟨M, c, hMc⟩ := id h.1
  have hv : ∀ i, (T.map φ h).v i = φ (T.v i) := fun i => rfl
  have hdetM := u3h_detM_pos T h hMc
  have key : ∀ l, planeDot (u3h_edgeN (T.map φ h) l) (φ t) - u3h_edgeC (T.map φ h) l =
      det (M ((1 : ℝ), (0 : ℝ))) (M ((0 : ℝ), (1 : ℝ))) *
        (planeDot (u3h_edgeN T l) t - u3h_edgeC T l) := by
    intro l
    rw [u3h_edge_eval, u3h_edge_eval, hv, hv]
    have hvl : ∀ k, T.v k ∈ T.carrier := fun k => subset_convexHull ℝ (range T.v) (mem_range_self k)
    have e1 : φ (T.v (l + 1)) - φ (T.v l) = M (T.v (l + 1) - T.v l) := by
      rw [hMc _ (hvl (l + 1)), hMc _ (hvl l), map_sub]
      abel
    have e2 : φ t - φ (T.v l) = M (t - T.v l) := by
      rw [hMc _ ht, hMc _ (hvl l), map_sub]; abel
    rw [e1, e2, u3h_det_map]
  rw [u3h_mem_interior_iff, u3h_mem_interior_iff]
  constructor
  · intro H l
    have k := key l
    have := H l
    by_contra hn; push Not at hn
    have := mul_nonpos_of_nonneg_of_nonpos hdetM.le (sub_nonpos.2 hn)
    linarith
  · intro H l
    have k := key l
    have := mul_pos hdetM (sub_pos.2 (H l))
    linarith

theorem u3h_triangulation_vertex {X : Set Plane} (K : Triangulation X) {T T' : Triangle}
    (hT : T ∈ K.faces) (hT' : T' ∈ K.faces) (j : Fin 3) (h : T'.v j ∈ T.carrier) :
    T'.v j ∈ range T.v := by
  have hmem : T'.v j ∈ convexHull ℝ (range T.v ∩ range T'.v) := by
    rw [← K.inter T hT T' hT']; exact ⟨h, subset_convexHull ℝ _ ⟨j, rfl⟩⟩
  exact (u3h_v_mem_convexHull T' inter_subset_right j hmem).1

theorem u3h_interior_disjoint_or {X : Set Plane} (K : Triangulation X) {T T' : Triangle}
    (hT : T ∈ K.faces) (hT' : T' ∈ K.faces) (hne : T.carrier ≠ T'.carrier) :
    Disjoint (interior T.carrier) T'.carrier ∨ Disjoint (interior T'.carrier) T.carrier := by
  by_cases h : ∃ i, T.v i ∉ range T'.v
  · obtain ⟨i, hi⟩ := h; exact Or.inl (u3h_interior_disjoint_of_vertex K hT hT' i hi)
  · push Not at h
    have h' : ∃ i, T'.v i ∉ range T.v := by
      by_contra h'; push Not at h'
      apply hne
      have : range T.v = range T'.v := Subset.antisymm (by rintro _ ⟨i, rfl⟩; exact h i)
        (by rintro _ ⟨i, rfl⟩; exact h' i)
      unfold Triangle.carrier; rw [this]
    obtain ⟨i, hi⟩ := h'
    exact Or.inr (u3h_interior_disjoint_of_vertex K hT' hT i hi)

theorem u3h_sep_of_disj (Δ Δ' : Triangle) (h : Disjoint (interior Δ.carrier) Δ'.carrier) :
    ∃ (p : Plane) (r : ℝ), p ≠ 0 ∧ (∀ i, planeDot p (Δ.v i) ≤ r) ∧ ∀ i, r ≤ planeDot p (Δ'.v i) := by
  obtain ⟨p, r, hp, h1, h2⟩ := u3h_separate_of_disjoint (convex_convexHull ℝ _)
    (U1_triangle_isCompact Δ) (U1_triangle_interior_nonempty Δ) (convex_convexHull ℝ _)
    ⟨Δ'.v 0, subset_convexHull ℝ (range Δ'.v) (mem_range_self 0)⟩ h
  exact ⟨p, r, hp, fun j => h1 _ (subset_convexHull ℝ _ ⟨j, rfl⟩),
    fun j => h2 _ (subset_convexHull ℝ _ ⟨j, rfl⟩)⟩

theorem u3h_sep_of_disj_or (Δ Δ' : Triangle)
    (h : Disjoint (interior Δ.carrier) Δ'.carrier ∨ Disjoint (interior Δ'.carrier) Δ.carrier) :
    ∃ (p : Plane) (r : ℝ), p ≠ 0 ∧ (∀ i, planeDot p (Δ.v i) ≤ r) ∧ ∀ i, r ≤ planeDot p (Δ'.v i) := by
  rcases h with h | h
  · exact u3h_sep_of_disj Δ Δ' h
  · obtain ⟨p, r, hp, h1, h2⟩ := u3h_sep_of_disj Δ' Δ h
    refine ⟨-p, -r, neg_ne_zero.2 hp, fun i => ?_, fun i => ?_⟩
    · rw [u3h_planeDot_neg_left]; linarith [h2 i]
    · rw [u3h_planeDot_neg_left]; linarith [h1 i]

theorem u3h_capInvFun_seam {L : ℝ} {y : Plane} (hy : supNorm y = 1) :
    capInvFun L y = L • (y.1, -y.2) := by
  simp [capInvFun, hy]

theorem u3h_planeDot_11 (x : Plane) : planeDot ((1 : ℝ), (1 : ℝ)) x = x.1 + x.2 := by
  simp [planeDot]

theorem u3h_planeDot_1m1 (x : Plane) : planeDot ((1 : ℝ), (-1 : ℝ)) x = x.1 - x.2 := by
  simp [planeDot]; ring

/-- **Corrected inverse leaf** (rule 3): `U3_isPositivePLFromPlane_inv` with the hypothesis `0 < L`
added.  The leaf as stated is false at `L ≤ 0` (see the report). -/
theorem u3h_isPositivePLFromPlane_inv {L : ℝ} (hL : 0 < L) {S : Set Sphere} {D : Set Plane}
    {f : Sphere → Plane} (_hD : Link.IsDisc D) (hf : IsHomeoOnto S D f)
    (hpl : IsPositivePLToPlane L S f) :
    ∃ g : Plane → Sphere, IsPositivePLFromPlane L D g ∧ (∀ z ∈ S, g (f z) = z) ∧
      ∀ x ∈ D, f (g x) = x := by
  classical
  obtain ⟨e, he⟩ := hf
  let g : Plane → Sphere := fun x => if h : x ∈ D then ((e.symm ⟨x, h⟩ : S) : Sphere) else ∞
  have hfD : ∀ z ∈ S, f z ∈ D := fun z hz => by rw [← he ⟨z, hz⟩]; exact (e ⟨z, hz⟩).2
  have hgf : ∀ z ∈ S, g (f z) = z := by
    intro z hz
    simp only [g, dif_pos (hfD z hz)]
    have : (⟨f z, hfD z hz⟩ : D) = e ⟨z, hz⟩ := Subtype.ext (he ⟨z, hz⟩).symm
    rw [this, Homeomorph.symm_apply_apply]
  have hgS : ∀ x ∈ D, g x ∈ S := fun x hx => by
    simp only [g, dif_pos hx]; exact (e.symm ⟨x, hx⟩).2
  have hfg : ∀ x ∈ D, f (g x) = x := by
    intro x hx
    simp only [g, dif_pos hx]
    rw [← he, Homeomorph.apply_symm_apply]
  have hinj : ∀ z ∈ S, ∀ z' ∈ S, f z = f z' → z = z' := fun z hz z' hz' h => by
    rw [← hgf z hz, ← hgf z' hz', h]
  refine ⟨g, ?_, hgf, hfg⟩
  choose K hK using hpl
  -- the set of "sums" of all vertices (false chart: x₁ + x₂; true chart: L (y₁ - y₂))
  let V : Set ℝ := (⋃ T ∈ (K false).faces, range (fun i => (T.v i).1 + (T.v i).2)) ∪
    (⋃ T ∈ (K true).faces, range (fun i => L * ((T.v i).1 - (T.v i).2)))
  have hVfin : V.Finite :=
    ((K false).finite.biUnion fun T _ => finite_range _).union
      ((K true).finite.biUnion fun T _ => finite_range _)
  haveI : Finite ↥V := hVfin.to_subtype
  obtain ⟨Kf, hKf1, hKf2, hKf3⟩ := u3h_refine_along_lines_finite (K false)
    (fun _ : ↥V => ((1 : ℝ), (1 : ℝ))) (fun c => c.1)
  obtain ⟨Kt, hKt1, hKt2, hKt3⟩ := u3h_refine_along_lines_finite (K true)
    (fun _ : ↥V => ((1 : ℝ), (-1 : ℝ))) (fun c => c.1 / L)
  have hPLf : IsPositivePLOn (f ∘ modelChart L false) Kf :=
    U2_isPositivePLOn_of_refines (hK false) hKf1
  have hPLt : IsPositivePLOn (f ∘ modelChart L true) Kt :=
    U2_isPositivePLOn_of_refines (hK true) hKt1
  have hVf : ∀ T ∈ Kf.faces, ∀ i, (T.v i).1 + (T.v i).2 ∈ V := by
    intro T hT i
    rcases hKf3 T hT i with ⟨T₀, hT₀, ⟨k, hk⟩⟩ | ⟨c, hc⟩
    · left; exact mem_iUnion₂.2 ⟨T₀, hT₀, k, by show (T₀.v k).1 + (T₀.v k).2 = _; rw [hk]⟩
    · rw [u3h_planeDot_11] at hc; rw [hc]; exact c.2
  have hVt : ∀ T ∈ Kt.faces, ∀ i, L * ((T.v i).1 - (T.v i).2) ∈ V := by
    intro T hT i
    rcases hKt3 T hT i with ⟨T₀, hT₀, ⟨k, hk⟩⟩ | ⟨c, hc⟩
    · right; exact mem_iUnion₂.2 ⟨T₀, hT₀, k, by show L * ((T₀.v k).1 - (T₀.v k).2) = _; rw [hk]⟩
    · rw [u3h_planeDot_1m1] at hc; rw [hc, mul_div_cancel₀ _ hL.ne']; exact c.2
  have hsidef : ∀ T ∈ Kf.faces, ∀ c ∈ V, (∀ i, planeDot ((1 : ℝ), (1 : ℝ)) (T.v i) ≤ c) ∨
      (∀ i, c ≤ planeDot ((1 : ℝ), (1 : ℝ)) (T.v i)) := by
    intro T hT c hc
    rcases hKf2 T hT ⟨c, hc⟩ with h | h
    · left; intro i; exact h (subset_convexHull ℝ _ ⟨i, rfl⟩)
    · right; intro i; exact h (subset_convexHull ℝ _ ⟨i, rfl⟩)
  have hsidet : ∀ T ∈ Kt.faces, ∀ c ∈ V, (∀ i, planeDot ((1 : ℝ), (-1 : ℝ)) (T.v i) ≤ c / L) ∨
      (∀ i, c / L ≤ planeDot ((1 : ℝ), (-1 : ℝ)) (T.v i)) := by
    intro T hT c hc
    rcases hKt2 T hT ⟨c, hc⟩ with h | h
    · left; intro i; exact h (subset_convexHull ℝ _ ⟨i, rfl⟩)
    · right; intro i; exact h (subset_convexHull ℝ _ ⟨i, rfl⟩)
  -- the two refined chart triangulations, indexed by the chart
  let K' : ∀ b : Bool, Triangulation (chartPart L b S) := fun b =>
    Bool.casesOn (motive := fun b => Triangulation (chartPart L b S)) b Kf Kt
  have hK' : ∀ b, IsPositivePLOn (f ∘ modelChart L b) (K' b) := fun b => by
    cases b
    · exact hPLf
    · exact hPLt
  haveI : ∀ b, Finite ↥(K' b).faces := fun b => (K' b).finite.to_subtype
  let F : Set Triangle := ⋃ b : Bool,
    range (fun T : ↥(K' b).faces => T.1.map (f ∘ modelChart L b) (hK' b T.1 T.2))
  have hFmem : ∀ Δ, Δ ∈ F ↔ ∃ b, ∃ T : ↥(K' b).faces,
      T.1.map (f ∘ modelChart L b) (hK' b T.1 T.2) = Δ := by
    intro Δ; simp only [F, mem_iUnion, mem_range]
  have hFfin : F.Finite := finite_iUnion fun b => finite_range _
  have hcar : ∀ b (T : ↥(K' b).faces),
      (T.1.map (f ∘ modelChart L b) (hK' b T.1 T.2)).carrier = (f ∘ modelChart L b) '' T.1.carrier :=
    fun b T => (u3h_image_carrier T.1 (hK' b T.1 T.2)).symm
  have hsubC : ∀ b (T : ↥(K' b).faces), T.1.carrier ⊆ chartPart L b S :=
    fun b T => u3h_face_subset_chartPart (K' b) T.2
  have hchartS : ∀ b (T : ↥(K' b).faces), ∀ t ∈ T.1.carrier, modelChart L b t ∈ S :=
    fun b T t ht => (hsubC b T ht).2
  have hchartinj : ∀ b (t t' : Plane), modelChart L b t = modelChart L b t' → t = t' := by
    intro b t t' h
    rw [← u3h_chartInv_chart hL.ne' b t, h, u3h_chartInv_chart hL.ne']
  -- a point of the interior of one image face lying in another: chart coordinates agree
  have hmeet : ∀ (b b' : Bool) (T : ↥(K' b).faces) (T' : ↥(K' b').faces) (y : Plane),
      y ∈ interior (T.1.map (f ∘ modelChart L b) (hK' b T.1 T.2)).carrier →
      y ∈ (T'.1.map (f ∘ modelChart L b') (hK' b' T'.1 T'.2)).carrier →
      ∃ t ∈ interior T.1.carrier, ∃ t' ∈ T'.1.carrier, modelChart L b t = modelChart L b' t' := by
    intro b b' T T' y hy hy'
    have hy0 := interior_subset hy
    rw [hcar] at hy0 hy'
    obtain ⟨t, ht, rfl⟩ := hy0
    obtain ⟨t', ht', hft'⟩ := hy'
    refine ⟨t, (u3h_interior_map T.1 (hK' b T.1 T.2) ht).1 hy, t', ht', ?_⟩
    exact hinj _ (hchartS b T t ht) _ (hchartS b' T' t' ht') hft'.symm
  have hcover : (⋃ Δ ∈ F, Δ.carrier) = D := by
    apply Subset.antisymm
    · intro x hx
      obtain ⟨Δ, hΔ, hxΔ⟩ := mem_iUnion₂.1 hx
      obtain ⟨b, T, rfl⟩ := (hFmem Δ).1 hΔ
      rw [hcar] at hxΔ
      obtain ⟨t, ht, rfl⟩ := hxΔ
      exact hfD _ (hchartS b T t ht)
    · intro x hx
      obtain ⟨b, y, hy, hyz⟩ := u3h_sphere_cover hL (g x)
      have hyS : y ∈ chartPart L b S := ⟨hy, by show modelChart L b y ∈ S; rw [hyz]; exact hgS x hx⟩
      rw [← (K' b).cover] at hyS
      obtain ⟨T, hT, hyT⟩ := mem_iUnion₂.1 hyS
      refine mem_iUnion₂.2 ⟨_, (hFmem _).2 ⟨b, ⟨T, hT⟩, rfl⟩, ?_⟩
      rw [hcar b ⟨T, hT⟩]
      refine ⟨y, hyT, ?_⟩
      show f (modelChart L b y) = x
      rw [hyz, hfg x hx]
  have hsupf : ∀ (T : ↥(K' false).faces) {t : Plane}, t ∈ interior T.1.carrier → supNorm t < L :=
    fun T t ht => by simpa using u3h_face_interior_supNorm_lt (K' false) T.2 ht
  have hsupt : ∀ (T : ↥(K' true).faces) {t : Plane}, t ∈ interior T.1.carrier → supNorm t < 1 :=
    fun T t ht => by simpa using u3h_face_interior_supNorm_lt (K' true) T.2 ht
  have hsqf : ∀ (T : ↥(K' false).faces), T.1.carrier ⊆ square L := fun T t ht => (hsubC false T ht).1
  have hsqt : ∀ (T : ↥(K' true).faces), T.1.carrier ⊆ square 1 := fun T t ht => (hsubC true T ht).1
  -- separation of distinct image faces
  have hsep : ∀ Δ ∈ F, ∀ Δ' ∈ F, Δ.carrier ≠ Δ'.carrier → ∃ (p : Plane) (r : ℝ), p ≠ 0 ∧
      (∀ i, planeDot p (Δ.v i) ≤ r) ∧ ∀ i, r ≤ planeDot p (Δ'.v i) := by
    intro Δ hΔ Δ' hΔ' hne
    obtain ⟨b, T, rfl⟩ := (hFmem Δ).1 hΔ
    obtain ⟨b', T', rfl⟩ := (hFmem Δ').1 hΔ'
    apply u3h_sep_of_disj_or
    by_cases hb : b = b'
    · subst hb
      have hne' : T.1.carrier ≠ T'.1.carrier := by
        intro h; apply hne; rw [hcar, hcar, h]
      rcases u3h_interior_disjoint_or (K' b) T.2 T'.2 hne' with h | h
      · left
        rw [Set.disjoint_left]
        intro y hy hy'
        obtain ⟨t, ht, t', ht', hc⟩ := hmeet b b T T' y hy hy'
        have := hchartinj b t t' hc
        subst this
        exact (Set.disjoint_left.1 h) ht ht'
      · right
        rw [Set.disjoint_left]
        intro y hy hy'
        obtain ⟨t, ht, t', ht', hc⟩ := hmeet b b T' T y hy hy'
        have := hchartinj b t t' hc
        subst this
        exact (Set.disjoint_left.1 h) ht ht'
    · left
      rw [Set.disjoint_left]
      intro y hy hy'
      obtain ⟨t, ht, t', ht', hc⟩ := hmeet b b' T T' y hy hy'
      cases b <;> cases b'
      · exact hb rfl
      · have hs := u3h_seam hL (hsqf T (interior_subset ht)) (hsqt T' ht') hc
        have := hsupf T ht
        linarith [hs.2.2.1]
      · have hs := u3h_seam hL (hsqf T' ht') (hsqt T (interior_subset ht)) hc.symm
        have := hsupt T ht
        linarith [hs.2.2.2]
      · exact hb rfl
  -- vertices of one image face lying in another are vertices of it
  have hvert : ∀ Δ ∈ F, ∀ Δ' ∈ F, ∀ j, Δ'.v j ∈ Δ.carrier → Δ'.v j ∈ range Δ.v := by
    intro Δ hΔ Δ' hΔ' j hj
    obtain ⟨b, T, rfl⟩ := (hFmem Δ).1 hΔ
    obtain ⟨b', T', rfl⟩ := (hFmem Δ').1 hΔ'
    rw [hcar] at hj
    obtain ⟨t, ht, hft⟩ := hj
    have hc : modelChart L b t = modelChart L b' (T'.1.v j) :=
      hinj _ (hchartS b T t ht) _ (hchartS b' T' _ (subset_convexHull ℝ _ ⟨j, rfl⟩)) hft
    suffices hrange : t ∈ range T.1.v by
      obtain ⟨i, rfl⟩ := hrange
      exact ⟨i, hft⟩
    cases b <;> cases b'
    · have := hchartinj false _ _ hc
      rw [this]
      exact u3h_triangulation_vertex (K' false) T.2 T'.2 j (this ▸ ht)
    · -- false / true: `t` is the seam image of the vertex `T'.v j`
      set y := T'.1.v j with hy
      have hyQ : y ∈ square 1 := hsqt T' (subset_convexHull ℝ _ ⟨j, rfl⟩)
      obtain ⟨_, hty, htL, hy1⟩ := u3h_seam hL (hsqf T ht) hyQ hc
      have ht' : t = L • (y.1, -y.2) := by rw [hty, u3h_capInvFun_seam hy1]
      have hsum : t.1 + t.2 = L * (y.1 - y.2) := by rw [ht']; simp; ring
      have hcV : t.1 + t.2 ∈ V := by rw [hsum]; exact hVt T'.1 T'.2 j
      refine u3h_seam_vertex T.1 (hsqf T) ht htL (p := ((1 : ℝ), (1 : ℝ))) one_ne_zero one_ne_zero ?_
      rw [u3h_planeDot_11]
      exact hsidef T.1 T.2 _ hcV
    · -- true / false
      set x := T'.1.v j with hx
      have hxQ : x ∈ square L := hsqf T' (subset_convexHull ℝ _ ⟨j, rfl⟩)
      obtain ⟨_, hxt, hxL, ht1⟩ := u3h_seam hL hxQ (hsqt T ht) hc.symm
      have hx' : x = L • (t.1, -t.2) := by rw [hxt, u3h_capInvFun_seam ht1]
      have hsum : x.1 + x.2 = L * (t.1 - t.2) := by rw [hx']; simp; ring
      have hcV : x.1 + x.2 ∈ V := hVf T'.1 T'.2 j
      refine u3h_seam_vertex T.1 (hsqt T) ht ht1 (p := ((1 : ℝ), (-1 : ℝ))) one_ne_zero
        (by norm_num) ?_
      rw [u3h_planeDot_1m1]
      have := hsidet T.1 T.2 _ hcV
      rw [hsum, mul_div_cancel_left₀ _ hL.ne'] at this
      exact this
    · have := hchartinj true _ _ hc
      rw [this]
      exact u3h_triangulation_vertex (K' true) T.2 T'.2 j (this ▸ ht)
  refine ⟨⟨F, hFfin, hcover, u3h_inter_of_family hsep hvert⟩, ?_⟩
  intro Δ hΔ
  obtain ⟨b, T, rfl⟩ := (hFmem Δ).1 hΔ
  refine ⟨b, ?_, ?_⟩
  · intro x hx
    rw [hcar] at hx
    obtain ⟨t, ht, rfl⟩ := hx
    show g (f (modelChart L b t)) ∈ _
    rw [hgf _ (hchartS b T t ht)]
    exact ⟨t, (hsubC b T ht).1, rfl⟩
  · refine u3h_affine_inverse T.1 (hK' b T.1 T.2) (fun t ht => ?_)
    show modelChartInv L b (g (f (modelChart L b t))) = t
    rw [hgf _ (hchartS b T t ht), u3h_chartInv_chart hL.ne']

/-- U3 (inverse chart bookkeeping): the inverse of a positive PL parametrisation `f : S → D` (a
homeomorphism, positive PL in charts) is positive PL from the plane.

W1 ASSEMBLY (rule 3): hypothesis `hL : 0 < L` added.  The skeleton form (no hypothesis on `L`) is false
for every `L ≤ 0` (W1_U3_REPORT.md §3: at `L ≤ 0` both chart parts of `S` are empty, so
`IsPositivePLToPlane L S f` holds vacuously while the conclusion fails).  The only consumer,
`U10_pl_extension`, has `InsideModel L' P'`, whence `0 < L'`. -/
theorem U3_isPositivePLFromPlane_inv {L : ℝ} (hL : 0 < L) {S : Set Sphere} {D : Set Plane}
    {f : Sphere → Plane} (hD : Link.IsDisc D) (hf : IsHomeoOnto S D f)
    (hpl : IsPositivePLToPlane L S f) :
    ∃ g : Plane → Sphere, IsPositivePLFromPlane L D g ∧ (∀ z ∈ S, g (f z) = z) ∧
      ∀ x ∈ D, f (g x) = x :=
  u3h_isPositivePLFromPlane_inv hL hD hf hpl

/-! ### U4 (lane B) — ear triangulation of an embedded polygon (Meisters) -/

/-- U4: the ear triangle at vertex `j` (vertices `P (j-1), P j, P (j+1)`). -/
def earHull (P : LabelledTuple n) (j : ZMod n) : Set Plane :=
  convexHull ℝ {P (j - 1), P j, P (j + 1)}

/-! ### U4 helpers (`u4h_`), 2026-09-19: the ear triangulation development.  Every helper is
placed here, immediately before the U4 leaves that use them.  See W1_U4_REPORT.md. -/

section U4A_block

/-- U4 helper: an edge segment is the Mathlib segment between consecutive vertices. -/
theorem u4h_edgeSegment_eq_segment (P : LabelledTuple n) (i : ZMod n) :
    edgeSegment P i = segment ℝ (P i) (P (i + 1)) := by
  rw [segment_eq_image]
  ext x
  simp only [edgeSegment, edgePoint, edge, Set.mem_ofPred_eq, Set.mem_image, Set.mem_Icc]
  constructor
  · rintro ⟨t, ht0, ht1, rfl⟩
    exact ⟨t, ⟨ht0, ht1⟩, by module⟩
  · rintro ⟨t, ⟨ht0, ht1⟩, rfl⟩
    exact ⟨t, ht0, ht1, by module⟩

theorem u4h_isCompact_segment (x y : Plane) : IsCompact (segment ℝ x y) := by
  rw [segment_eq_image]
  exact isCompact_Icc.image (by fun_prop)

theorem u4h_isClosed_segment (x y : Plane) : IsClosed (segment ℝ x y) :=
  (u4h_isCompact_segment x y).isClosed

theorem u4h_polygonImage_isCompact [NeZero n] (P : LabelledTuple n) :
    IsCompact (embeddedPolygonImage P) := by
  unfold embeddedPolygonImage
  refine isCompact_iUnion fun i => ?_
  rw [u4h_edgeSegment_eq_segment]
  exact u4h_isCompact_segment _ _

theorem u4h_polygonImage_isClosed [NeZero n] (P : LabelledTuple n) :
    IsClosed (embeddedPolygonImage P) := (u4h_polygonImage_isCompact P).isClosed

theorem u4h_edgePoint_mem_range_traversal [NeZero n] (P : LabelledTuple n) (i : ZMod n) {t : ℝ}
    (h0 : 0 ≤ t) (h1 : t < 1) : edgePoint P i t ∈ range (traversal P) := by
  refine ⟨(i.val : ℝ) + t, ?_⟩
  have hfl : ⌊(i.val : ℝ) + t⌋ = (i.val : ℤ) := by
    rw [Int.floor_eq_iff]
    push_cast
    constructor <;> linarith
  have hfr : Int.fract ((i.val : ℝ) + t) = t := by
    rw [Int.fract, hfl]
    push_cast
    ring
  simp only [traversal, hfl, hfr, Int.cast_natCast, ZMod.natCast_zmod_val]

theorem u4h_range_traversal [NeZero n] (P : LabelledTuple n) :
    range (traversal P) = embeddedPolygonImage P := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact Set.mem_iUnion.mpr ⟨_, Int.fract y, Int.fract_nonneg y, (Int.fract_lt_one y).le, rfl⟩
  · intro hx
    obtain ⟨i, t, ht0, ht1, rfl⟩ := Set.mem_iUnion.mp hx
    rcases ht1.lt_or_eq with ht1 | rfl
    · exact u4h_edgePoint_mem_range_traversal P i ht0 ht1
    · rw [edgePoint_one, ← edgePoint_zero P (i + 1)]
      exact u4h_edgePoint_mem_range_traversal P (i + 1) le_rfl zero_lt_one

theorem u4h_supNorm_eq_norm (x : Plane) : supNorm x = ‖x‖ := by
  simp [supNorm, Prod.norm_def, Real.norm_eq_abs]

theorem u4h_supNorm_nonneg (x : Plane) : 0 ≤ supNorm x := by
  rw [u4h_supNorm_eq_norm]; exact norm_nonneg x

theorem u4h_square_eq_closedBall (L : ℝ) : square L = Metric.closedBall 0 L := by
  ext x
  simp [square, u4h_supNorm_eq_norm, Metric.mem_closedBall, dist_zero_right]

theorem u4h_ball_subset_interior_square (L : ℝ) :
    Metric.ball (0 : Plane) L ⊆ interior (square L) := by
  rw [u4h_square_eq_closedBall]
  exact Metric.ball_subset_interior_closedBall

theorem u4h_mem_ball_of_supNorm_lt {L : ℝ} {x : Plane} (h : supNorm x < L) :
    x ∈ Metric.ball (0 : Plane) L := by
  rw [Metric.mem_ball, dist_zero_right, ← u4h_supNorm_eq_norm]; exact h

theorem u4h_exists_insideModel [NeZero n] (P : LabelledTuple n) :
    ∃ L : ℝ, 0 < L ∧ InsideModel L P := by
  obtain ⟨M, hM⟩ := (Set.finite_range fun i => supNorm (P i)).bddAbove
  refine ⟨M + 1, ?_, fun i => ?_⟩
  · have := hM ⟨0, rfl⟩
    have := u4h_supNorm_nonneg (P 0)
    linarith
  · have := hM ⟨i, rfl⟩
    linarith

theorem u4h_polygonImage_subset_ball [NeZero n] {L : ℝ} (P : LabelledTuple n)
    (hL : InsideModel L P) : embeddedPolygonImage P ⊆ Metric.ball 0 L := by
  intro x hx
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
  rw [u4h_edgeSegment_eq_segment] at hi
  exact (convex_ball (0 : Plane) L).segment_subset (u4h_mem_ball_of_supNorm_lt (hL i))
    (u4h_mem_ball_of_supNorm_lt (hL (i + 1))) hi

theorem u4h_polygonImage_subset_interior_square [NeZero n] {L : ℝ} (P : LabelledTuple n)
    (hL : InsideModel L P) : embeddedPolygonImage P ⊆ interior (square L) ∧ 0 < L := by
  refine ⟨(u4h_polygonImage_subset_ball P hL).trans (u4h_ball_subset_interior_square L), ?_⟩
  exact lt_of_le_of_lt (u4h_supNorm_nonneg (P 0)) (hL 0)

theorem u4h_three_le_of_embedded [NeZero n] (P : LabelledTuple n) (hP : Embedded P) : 3 ≤ n := by
  rcases n with _ | _ | _ | n
  · exact absurd rfl (NeZero.ne 0)
  · exfalso
    apply hP.edge_ne_zero 0
    have h : (0 : ZMod 1) + 1 = 0 := Subsingleton.elim _ _
    simp [edge, h]
  · exfalso
    have h01 : (0 : ZMod 2) + 1 = 1 := by decide
    have h11 : (1 : ZMod 2) + 1 = 0 := by decide
    have hc := hP.consecutive 0
    rw [h01, u4h_edgeSegment_eq_segment, u4h_edgeSegment_eq_segment, h01, h11,
      segment_symm ℝ (P 1) (P 0), Set.inter_self] at hc
    have hmem : P 0 ∈ segment ℝ (P 0) (P 1) := left_mem_segment ℝ _ _
    rw [hc] at hmem
    have h0 : P 0 = P 1 := hmem
    exact hP.edge_ne_zero 0 (by simp [edge, h01, h0])
  · omega

theorem u4h_start_mem_edgeSegment (P : LabelledTuple n) (i : ZMod n) : P i ∈ edgeSegment P i :=
  ⟨0, le_rfl, zero_le_one, (edgePoint_zero P i).symm⟩

theorem u4h_end_mem_edgeSegment (P : LabelledTuple n) (i : ZMod n) :
    P (i + 1) ∈ edgeSegment P i :=
  ⟨1, zero_le_one, le_rfl, (edgePoint_one P i).symm⟩

theorem u4h_edgeSegment_subset_polygonImage (P : LabelledTuple n) (i : ZMod n) :
    edgeSegment P i ⊆ embeddedPolygonImage P := Set.subset_iUnion (fun i => edgeSegment P i) i

theorem u4h_vertex_mem_polygonImage (P : LabelledTuple n) (i : ZMod n) : P i ∈ embeddedPolygonImage P :=
  u4h_edgeSegment_subset_polygonImage P i (u4h_start_mem_edgeSegment P i)

/-- U4 helper: an embedded polygon has pairwise distinct vertices. -/
theorem u4h_vertex_injective {P : LabelledTuple n} (hP : Embedded P) : Function.Injective P := by
  intro i j hij
  by_contra hne
  by_cases hadj : adjacent i j
  · rcases adjacent_distinct_cases hne hadj with h | h
    · apply hP.edge_ne_zero i
      rw [edge, ← h, hij, sub_self]
    · apply hP.edge_ne_zero j
      rw [edge, ← h, ← hij, sub_self]
  · have hi : P i ∈ edgeSegment P i := u4h_start_mem_edgeSegment P i
    have hj : P i ∈ edgeSegment P j := hij ▸ u4h_start_mem_edgeSegment P j
    exact Set.disjoint_left.mp (hP.remote_disjoint i j hadj) hi hj

/-- U4 helper: a vertex lying on an edge segment is one of its endpoints. -/
theorem u4h_incident_of_vertex_mem {P : LabelledTuple n} (hP : Embedded P) {k i : ZMod n}
    (hk : P k ∈ edgeSegment P i) : k = i ∨ k = i + 1 := by
  by_contra hne
  simp only [not_or] at hne
  by_cases hadj : adjacent k i
  · rcases adjacent_distinct_cases hne.1 hadj with h | h
    · -- `i = k + 1`: `P k ∈ E_k ∩ E_{k+1} = {P (k+1)}`.
      have hc := hP.consecutive k
      have hmem : P k ∈ edgeSegment P k ∩ edgeSegment P (k + 1) :=
        ⟨u4h_start_mem_edgeSegment P k, by rw [← h]; exact hk⟩
      rw [hc] at hmem
      have h0 : P k = P (k + 1) := hmem
      exact hP.edge_ne_zero k (by rw [edge, ← h0, sub_self])
    · exact hne.2 h
  · exact Set.disjoint_left.mp (hP.remote_disjoint k i hadj) (u4h_start_mem_edgeSegment P k) hk

end U4A_block

section U4B_block

/-! Barycentric / determinant toolkit for triangles `convexHull ℝ {a, b, c}` (U4 helpers). -/

theorem u4h_det_sub_right (u v w : Plane) : det u (v - w) = det u v - det u w := by
  simp only [det, Prod.fst_sub, Prod.snd_sub]; ring

theorem u4h_det_add_right (u v w : Plane) : det u (v + w) = det u v + det u w := by
  simp only [det, Prod.fst_add, Prod.snd_add]; ring

theorem u4h_det_smul_right (u v : Plane) (t : ℝ) : det u (t • v) = t * det u v := by
  simp only [det, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring

theorem u4h_det_swap' (u v : Plane) : det u v = -det v u := by
  simp only [det]; ring

theorem u4h_det_self (u : Plane) : det u u = 0 := by simp only [det]; ring

theorem u4h_hull3_comm (a b c : Plane) :
    convexHull ℝ {a, b, c} = convexHull ℝ {a, c, b} := by
  rw [Set.pair_comm]

/-- Barycentric membership in the hull of three points. -/
theorem u4h_mem_hull3_iff (a b c x : Plane) :
    x ∈ convexHull ℝ {a, b, c} ↔
      ∃ α β γ : ℝ, 0 ≤ α ∧ 0 ≤ β ∧ 0 ≤ γ ∧ α + β + γ = 1 ∧ x = α • a + β • b + γ • c := by
  rw [convexHull_insert (Set.insert_nonempty b {c}), convexHull_pair, mem_convexJoin]
  constructor
  · rintro ⟨a', ha', y, ⟨s, t, hs, ht, hst, rfl⟩, ⟨p, q, hp, hq, hpq, rfl⟩⟩
    rw [Set.mem_singleton_iff] at ha'
    subst ha'
    refine ⟨p, q * s, q * t, hp, mul_nonneg hq hs, mul_nonneg hq ht, ?_, ?_⟩
    · linear_combination hpq + q * hst
    · simp only [smul_add, smul_smul]; abel
  · rintro ⟨α, β, γ, hα, hβ, hγ, hsum, rfl⟩
    refine ⟨a, Set.mem_singleton a, ?_⟩
    by_cases h0 : β + γ = 0
    · have hβ0 : β = 0 := by linarith
      have hγ0 : γ = 0 := by linarith
      refine ⟨b, left_mem_segment ℝ b c, α, 0, hα, le_rfl, by linarith, ?_⟩
      simp [hβ0, hγ0]
    · have hpos : 0 < β + γ := lt_of_le_of_ne (by linarith) (Ne.symm h0)
      refine ⟨(β / (β + γ)) • b + (γ / (β + γ)) • c,
        ⟨β / (β + γ), γ / (β + γ), div_nonneg hβ hpos.le, div_nonneg hγ hpos.le, ?_, rfl⟩,
        α, β + γ, hα, hpos.le, by linarith, ?_⟩
      · rw [← add_div, div_self h0]
      · rw [smul_add, smul_smul, smul_smul, mul_div_cancel₀ _ h0, mul_div_cancel₀ _ h0, add_assoc]

/-- The three sub-determinants sum to the full determinant. -/
theorem u4h_det_sum3 (a b c x : Plane) :
    det (b - a) (x - a) + det (c - b) (x - b) + det (a - c) (x - c) = det (b - a) (c - a) := by
  simp only [det, Prod.fst_sub, Prod.snd_sub]; ring

/-- Membership in a positively oriented triangle by the three `det` signs. -/
theorem u4h_mem_hull3_iff_det {a b c : Plane} (hD : 0 < det (b - a) (c - a)) (x : Plane) :
    x ∈ convexHull ℝ {a, b, c} ↔
      0 ≤ det (b - a) (x - a) ∧ 0 ≤ det (c - b) (x - b) ∧ 0 ≤ det (a - c) (x - c) := by
  rw [u4h_mem_hull3_iff]
  constructor
  · rintro ⟨α, β, γ, hα, hβ, hγ, hsum, rfl⟩
    have hα' : α = 1 - β - γ := by linarith
    subst hα'
    refine ⟨?_, ?_, ?_⟩
    · have e : det (b - a) ((1 - β - γ) • a + β • b + γ • c - a) = γ * det (b - a) (c - a) := by
        simp only [det, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
          Prod.smul_snd, smul_eq_mul]; ring
      rw [e]; exact mul_nonneg hγ hD.le
    · have e : det (c - b) ((1 - β - γ) • a + β • b + γ • c - b) =
          (1 - β - γ) * det (b - a) (c - a) := by
        simp only [det, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
          Prod.smul_snd, smul_eq_mul]; ring
      rw [e]; exact mul_nonneg hα hD.le
    · have e : det (a - c) ((1 - β - γ) • a + β • b + γ • c - c) = β * det (b - a) (c - a) := by
        simp only [det, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
          Prod.smul_snd, smul_eq_mul]; ring
      rw [e]; exact mul_nonneg hβ hD.le
  · rintro ⟨h1, h2, h3⟩
    have hD' : det (b - a) (c - a) ≠ 0 := hD.ne'
    refine ⟨det (c - b) (x - b) / det (b - a) (c - a), det (a - c) (x - c) / det (b - a) (c - a),
      det (b - a) (x - a) / det (b - a) (c - a), div_nonneg h2 hD.le, div_nonneg h3 hD.le,
      div_nonneg h1 hD.le, ?_, ?_⟩
    · rw [← add_div, ← add_div, div_eq_one_iff_eq hD']
      linear_combination u4h_det_sum3 a b c x
    · apply Prod.ext
      · have key : x.1 * det (b - a) (c - a) = det (c - b) (x - b) * a.1 +
            det (a - c) (x - c) * b.1 + det (b - a) (x - a) * c.1 := by
          simp only [det, Prod.fst_sub, Prod.snd_sub]; ring
        simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
        rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, ← add_div,
          eq_div_iff hD']
        exact key
      · have key : x.2 * det (b - a) (c - a) = det (c - b) (x - b) * a.2 +
            det (a - c) (x - c) * b.2 + det (b - a) (x - a) * c.2 := by
          simp only [det, Prod.fst_sub, Prod.snd_sub]; ring
        simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
        rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, ← add_div,
          eq_div_iff hD']
        exact key

/-- A point of the triangle with vanishing first sub-determinant lies on the edge `[a, b]`. -/
theorem u4h_mem_segment_of_det_eq_zero {a b c x : Plane} (hD : 0 < det (b - a) (c - a))
    (hx : x ∈ convexHull ℝ {a, b, c}) (h0 : det (b - a) (x - a) = 0) : x ∈ segment ℝ a b := by
  rw [u4h_mem_hull3_iff] at hx
  obtain ⟨α, β, γ, hα, hβ, hγ, hsum, rfl⟩ := hx
  have hα' : α = 1 - β - γ := by linarith
  subst hα'
  have e : det (b - a) ((1 - β - γ) • a + β • b + γ • c - a) = γ * det (b - a) (c - a) := by
    simp only [det, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
      Prod.smul_snd, smul_eq_mul]; ring
  rw [e] at h0
  have hγ0 : γ = 0 := by
    rcases mul_eq_zero.mp h0 with h | h
    · exact h
    · exact absurd h hD.ne'
  subst hγ0
  exact ⟨1 - β - 0, β, by linarith, hβ, by ring, by simp⟩

theorem u4h_det_segment_zero {a b x : Plane} (hx : x ∈ segment ℝ a b) : det (b - a) (x - a) = 0 := by
  rw [segment_eq_image] at hx
  obtain ⟨t, -, rfl⟩ := hx
  simp only [det, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
    Prod.smul_snd, smul_eq_mul]; ring

/-- Two edges from a common vertex of a nondegenerate triangle meet only at that vertex. -/
theorem u4h_segment_inter_same_start {a b c : Plane} (hD : det (b - a) (c - a) ≠ 0) :
    segment ℝ a b ∩ segment ℝ a c = {a} := by
  ext x
  constructor
  · rintro ⟨hb, hc⟩
    rw [segment_eq_image] at hb hc
    obtain ⟨s, -, hs⟩ := hb
    obtain ⟨t, -, ht⟩ := hc
    simp only at hs ht
    have h1 : det (b - a) (x - a) = 0 := by
      rw [← hs]
      simp only [det, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
        Prod.smul_snd, smul_eq_mul]; ring
    have h2 : det (b - a) (x - a) = t * det (b - a) (c - a) := by
      rw [← ht]
      simp only [det, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
        Prod.smul_snd, smul_eq_mul]; ring
    rw [h2] at h1
    have ht0 : t = 0 := by
      rcases mul_eq_zero.mp h1 with h | h
      · exact h
      · exact absurd h hD
    rw [ht0] at ht
    simp only [sub_zero, one_smul, zero_smul, add_zero] at ht
    exact ht.symm
  · intro hx
    have hx' : x = a := hx
    rw [hx']
    exact ⟨left_mem_segment ℝ a b, left_mem_segment ℝ a c⟩

theorem u4h_hull3_isCompact (a b c : Plane) : IsCompact (convexHull ℝ {a, b, c}) :=
  (Set.toFinite _).isCompact_convexHull ℝ

theorem u4h_hull3_isClosed (a b c : Plane) : IsClosed (convexHull ℝ {a, b, c}) :=
  (u4h_hull3_isCompact a b c).isClosed

theorem u4h_segment_subset_hull3 (a b c : Plane) : segment ℝ a b ⊆ convexHull ℝ {a, b, c} :=
  segment_subset_convexHull (by simp) (by simp)

theorem u4h_isLinearMap_det (u : Plane) : IsLinearMap ℝ (fun y : Plane => det u y) :=
  ⟨fun x y => u4h_det_add_right u x y, fun t x => by
    simp only [smul_eq_mul]; exact u4h_det_smul_right u x t⟩

theorem u4h_continuous_det (u : Plane) : Continuous (fun y : Plane => det u y) := by
  simp only [det]; fun_prop

end U4B_block

section U4C_block

/-! Topology of a nondegenerate triangle `convexHull ℝ {a, b, c}` (U4 helpers). -/

theorem u4h_hull3_rot (a b c : Plane) : convexHull ℝ {a, b, c} = convexHull ℝ {b, c, a} := by
  rw [Set.insert_comm, Set.pair_comm]

theorem u4h_det_rot1 (a b c : Plane) : det (c - b) (a - b) = det (b - a) (c - a) := by
  simp only [det, Prod.fst_sub, Prod.snd_sub]; ring

theorem u4h_det_rot2 (a b c : Plane) : det (a - c) (b - c) = det (b - a) (c - a) := by
  simp only [det, Prod.fst_sub, Prod.snd_sub]; ring

theorem u4h_continuous_det_sub (u p : Plane) : Continuous (fun y : Plane => det u (y - p)) :=
  (u4h_continuous_det u).comp (continuous_id.sub continuous_const)

theorem u4h_isOpen_det_pos (u p : Plane) : IsOpen {y : Plane | 0 < det u (y - p)} :=
  isOpen_lt continuous_const (u4h_continuous_det_sub u p)

theorem u4h_isClosed_det_nonneg (u p : Plane) : IsClosed {y : Plane | 0 ≤ det u (y - p)} :=
  isClosed_le continuous_const (u4h_continuous_det_sub u p)

theorem u4h_convex_det_pos (u p : Plane) : Convex ℝ {y : Plane | 0 < det u (y - p)} := by
  intro x hx y hy s t hs ht hst
  simp only [Set.mem_ofPred_eq] at hx hy ⊢
  have hp : s • p + t • p = p := by rw [← add_smul, hst, one_smul]
  have e : s • x + t • y - p = s • (x - p) + t • (y - p) := by
    calc s • x + t • y - p = s • x + t • y - (s • p + t • p) := by rw [hp]
      _ = s • (x - p) + t • (y - p) := by rw [smul_sub, smul_sub]; abel
  rw [e, u4h_det_add_right, u4h_det_smul_right, u4h_det_smul_right]
  rcases hs.lt_or_eq with hs | hs
  · exact add_pos_of_pos_of_nonneg (mul_pos hs hx) (mul_nonneg ht hy.le)
  · subst hs
    have ht1 : t = 1 := by linarith
    subst ht1
    simpa using hy

theorem u4h_isOpen_strict3 (a b c : Plane) :
    IsOpen {x : Plane | 0 < det (b - a) (x - a) ∧ 0 < det (c - b) (x - b) ∧
      0 < det (a - c) (x - c)} :=
  (u4h_isOpen_det_pos _ _).and ((u4h_isOpen_det_pos _ _).and (u4h_isOpen_det_pos _ _))

/-- A point with a nonpositive supporting determinant is not interior to a set on which that
determinant is nonnegative. -/
theorem u4h_not_mem_interior_of_det_nonpos {u w p x : Plane} {S : Set Plane}
    (hS : ∀ y ∈ S, 0 ≤ det u (y - p)) (hw : 0 < det u w) (hx : det u (x - p) ≤ 0) :
    x ∉ interior S := by
  intro hint
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hint)
  set δ : ℝ := ε / (2 * (‖w‖ + 1)) with hδ
  have hw1 : 0 < ‖w‖ + 1 := by positivity
  have hδpos : 0 < δ := by positivity
  have hy : x - δ • w ∈ Metric.ball x ε := by
    rw [Metric.mem_ball, dist_eq_norm, sub_sub_cancel_left, norm_neg, norm_smul,
      Real.norm_eq_abs, abs_of_pos hδpos, hδ]
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith [norm_nonneg w]
  have h1 := hS _ (hball hy)
  rw [sub_right_comm, u4h_det_sub_right, u4h_det_smul_right] at h1
  nlinarith [mul_pos hδpos hw]

theorem u4h_interior_hull3 {a b c : Plane} (hD : 0 < det (b - a) (c - a)) :
    interior (convexHull ℝ {a, b, c}) =
      {x : Plane | 0 < det (b - a) (x - a) ∧ 0 < det (c - b) (x - b) ∧
        0 < det (a - c) (x - c)} := by
  apply Set.Subset.antisymm
  · intro x hx
    have hxm := interior_subset hx
    rw [u4h_mem_hull3_iff_det hD] at hxm
    obtain ⟨h1, h2, h3⟩ := hxm
    refine ⟨lt_of_le_of_ne h1 fun h => ?_, lt_of_le_of_ne h2 fun h => ?_,
      lt_of_le_of_ne h3 fun h => ?_⟩
    · exact u4h_not_mem_interior_of_det_nonpos (w := c - a)
        (fun y hy => ((u4h_mem_hull3_iff_det hD y).mp hy).1) hD h.symm.le hx
    · refine u4h_not_mem_interior_of_det_nonpos (w := a - b)
        (fun y hy => ((u4h_mem_hull3_iff_det hD y).mp hy).2.1) ?_ h.symm.le hx
      rw [u4h_det_rot1]; exact hD
    · refine u4h_not_mem_interior_of_det_nonpos (w := b - c)
        (fun y hy => ((u4h_mem_hull3_iff_det hD y).mp hy).2.2) ?_ h.symm.le hx
      rw [u4h_det_rot2]; exact hD
  · apply interior_maximal _ (u4h_isOpen_strict3 a b c)
    intro x hx
    rw [u4h_mem_hull3_iff_det hD]
    exact ⟨hx.1.le, hx.2.1.le, hx.2.2.le⟩

/-- On the closed triangle, `det (c - b) (x - b) = 0` means `x ∈ [b, c]`, and
`det (a - c) (x - c) = 0` means `x ∈ [c, a]` (rotations of `u4h_mem_segment_of_det_eq_zero`). -/
theorem u4h_mem_segment_of_det2_eq_zero {a b c x : Plane} (hD : 0 < det (b - a) (c - a))
    (hx : x ∈ convexHull ℝ {a, b, c}) (h0 : det (c - b) (x - b) = 0) : x ∈ segment ℝ b c := by
  rw [u4h_hull3_rot] at hx
  exact u4h_mem_segment_of_det_eq_zero (by rw [u4h_det_rot1]; exact hD) hx h0

theorem u4h_mem_segment_of_det3_eq_zero {a b c x : Plane} (hD : 0 < det (b - a) (c - a))
    (hx : x ∈ convexHull ℝ {a, b, c}) (h0 : det (a - c) (x - c) = 0) : x ∈ segment ℝ c a := by
  rw [u4h_hull3_rot, u4h_hull3_rot] at hx
  exact u4h_mem_segment_of_det_eq_zero (by rw [u4h_det_rot2]; exact hD) hx h0

theorem u4h_frontier_hull3 {a b c : Plane} (hD : 0 < det (b - a) (c - a)) :
    frontier (convexHull ℝ {a, b, c}) = segment ℝ a b ∪ segment ℝ b c ∪ segment ℝ c a := by
  rw [(u4h_hull3_isClosed a b c).frontier_eq, u4h_interior_hull3 hD]
  ext x
  constructor
  · rintro ⟨hx, hnot⟩
    have hx' := hx
    rw [u4h_mem_hull3_iff_det hD] at hx'
    obtain ⟨h1, h2, h3⟩ := hx'
    simp only [Set.mem_ofPred_eq, not_and_or, not_lt] at hnot
    rcases hnot with h | h | h
    · exact Or.inl (Or.inl (u4h_mem_segment_of_det_eq_zero hD hx (le_antisymm h h1)))
    · exact Or.inl (Or.inr (u4h_mem_segment_of_det2_eq_zero hD hx (le_antisymm h h2)))
    · exact Or.inr (u4h_mem_segment_of_det3_eq_zero hD hx (le_antisymm h h3))
  · intro hx
    have hmem : x ∈ convexHull ℝ {a, b, c} := by
      rcases hx with (h | h) | h
      · exact u4h_segment_subset_hull3 a b c h
      · rw [u4h_hull3_rot]; exact u4h_segment_subset_hull3 b c a h
      · rw [u4h_hull3_rot, u4h_hull3_rot]; exact u4h_segment_subset_hull3 c a b h
    refine ⟨hmem, ?_⟩
    simp only [Set.mem_ofPred_eq, not_and_or, not_lt]
    rcases hx with (h | h) | h
    · exact Or.inl (u4h_det_segment_zero h).le
    · exact Or.inr (Or.inl (u4h_det_segment_zero h).le)
    · exact Or.inr (Or.inr (u4h_det_segment_zero h).le)

/-- Half-disc lemma at an interior point of the edge `[c, a]`: nearby points lie in the triangle
iff they lie on the closed side of the edge line containing `b`. -/
theorem u4h_halfdisc {a b c x : Plane} (hD : 0 < det (b - a) (c - a))
    (hx : x ∈ openSegment ℝ c a) :
    ∃ ε > 0, ∀ y, dist y x < ε →
      (y ∈ convexHull ℝ {a, b, c} ↔ 0 ≤ det (a - c) (y - c)) := by
  rw [openSegment_eq_image] at hx
  obtain ⟨t, ⟨ht0, ht1⟩, rfl⟩ := hx
  have h1 : 0 < det (b - a) ((1 - t) • c + t • a - a) := by
    have e : det (b - a) ((1 - t) • c + t • a - a) = (1 - t) * det (b - a) (c - a) := by
      simp only [det, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
        Prod.smul_snd, smul_eq_mul]; ring
    rw [e]; exact mul_pos (by linarith) hD
  have h2 : 0 < det (c - b) ((1 - t) • c + t • a - b) := by
    have e : det (c - b) ((1 - t) • c + t • a - b) = t * det (b - a) (c - a) := by
      simp only [det, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
        Prod.smul_snd, smul_eq_mul]; ring
    rw [e]; exact mul_pos ht0 hD
  have hopen : IsOpen {y : Plane | 0 < det (b - a) (y - a) ∧ 0 < det (c - b) (y - b)} :=
    (u4h_isOpen_det_pos _ _).and (u4h_isOpen_det_pos _ _)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hopen.mem_nhds ⟨h1, h2⟩)
  refine ⟨ε, hε, fun y hy => ?_⟩
  have hy' := hball (Metric.mem_ball.mpr hy)
  rw [u4h_mem_hull3_iff_det hD]
  exact ⟨fun h => h.2.2, fun h => ⟨hy'.1.le, hy'.2.le, h⟩⟩

/-- The triangle minus the closed edge `[c, a]` is the convex set `T ∩ {det (a - c) (· - c) > 0}`. -/
theorem u4h_hull3_diff_edge {a b c : Plane} (hD : 0 < det (b - a) (c - a)) :
    convexHull ℝ {a, b, c} \ segment ℝ c a =
      convexHull ℝ {a, b, c} ∩ {y : Plane | 0 < det (a - c) (y - c)} := by
  ext y
  constructor
  · rintro ⟨hy, hns⟩
    refine ⟨hy, ?_⟩
    have h3 := ((u4h_mem_hull3_iff_det hD y).mp hy).2.2
    exact lt_of_le_of_ne h3 fun h => hns (u4h_mem_segment_of_det3_eq_zero hD hy h.symm)
  · rintro ⟨hy, hpos⟩
    refine ⟨hy, fun hs => ?_⟩
    have := u4h_det_segment_zero hs
    simp only [Set.mem_ofPred_eq] at hpos
    linarith

theorem u4h_convex_hull3_diff_edge {a b c : Plane} (hD : 0 < det (b - a) (c - a)) :
    Convex ℝ (convexHull ℝ {a, b, c} \ segment ℝ c a) := by
  rw [u4h_hull3_diff_edge hD]
  exact (convex_convexHull ℝ _).inter (u4h_convex_det_pos _ _)

/-! ### `Triangle` from a positively oriented triple -/

theorem u4h_range_fin3 {α : Type*} (f : Fin 3 → α) : Set.range f = {f 0, f 1, f 2} := by
  ext x
  simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp
  · rintro (rfl | rfl | rfl) <;> exact ⟨_, rfl⟩

theorem u4h_carrier_eq (T : Triangle) : T.carrier = convexHull ℝ {T.v 0, T.v 1, T.v 2} := by
  rw [Triangle.carrier, u4h_range_fin3]

/-- The positively oriented triangle on `a, b, c`. -/
def u4h_mkTri (a b c : Plane) (h : 0 < det (b - a) (c - a)) : Triangle :=
  ⟨![a, b, c], by simpa using h⟩

@[simp] theorem u4h_mkTri_v0 (a b c : Plane) (h : 0 < det (b - a) (c - a)) :
    (u4h_mkTri a b c h).v 0 = a := rfl

@[simp] theorem u4h_mkTri_v1 (a b c : Plane) (h : 0 < det (b - a) (c - a)) :
    (u4h_mkTri a b c h).v 1 = b := rfl

@[simp] theorem u4h_mkTri_v2 (a b c : Plane) (h : 0 < det (b - a) (c - a)) :
    (u4h_mkTri a b c h).v 2 = c := rfl

theorem u4h_mkTri_carrier (a b c : Plane) (h : 0 < det (b - a) (c - a)) :
    (u4h_mkTri a b c h).carrier = convexHull ℝ {a, b, c} := by
  rw [u4h_carrier_eq]; rfl

theorem u4h_mkTri_range (a b c : Plane) (h : 0 < det (b - a) (c - a)) :
    Set.range (u4h_mkTri a b c h).v = {a, b, c} := by
  rw [u4h_range_fin3]; rfl

theorem u4h_mkTri_edgeSeg0 (a b c : Plane) (h : 0 < det (b - a) (c - a)) :
    (u4h_mkTri a b c h).edgeSeg 0 = segment ℝ a b := rfl

theorem u4h_mkTri_edgeSeg1 (a b c : Plane) (h : 0 < det (b - a) (c - a)) :
    (u4h_mkTri a b c h).edgeSeg 1 = segment ℝ b c := rfl

theorem u4h_mkTri_edgeSeg2 (a b c : Plane) (h : 0 < det (b - a) (c - a)) :
    (u4h_mkTri a b c h).edgeSeg 2 = segment ℝ c a := rfl

end U4C_block

section U4D_block

/-! Segment against a triangle, part 1 (U4 helpers): a segment whose points on the two
"polygon" edges are only the base vertices, and whose endpoints inside the triangle are only the
base vertices, has no point in the open triangle. -/

/-- A preconnected set meeting both `t` and `tᶜ` meets `frontier t`. -/
theorem u4h_preconnected_inter_frontier {α : Type*} [TopologicalSpace α] {s t : Set α}
    (hs : IsPreconnected s) (h1 : (s ∩ t).Nonempty) (h2 : (s \ t).Nonempty) :
    (s ∩ frontier t).Nonempty := by
  by_contra hne
  rw [Set.not_nonempty_iff_eq_empty] at hne
  have hsub : s ⊆ interior t ∪ interior tᶜ := by
    intro x hx
    by_cases hxt : x ∈ closure t
    · by_cases hxi : x ∈ interior t
      · exact Or.inl hxi
      · have hmem : x ∈ s ∩ frontier t := ⟨hx, hxt, hxi⟩
        rw [hne] at hmem
        exact hmem.elim
    · right
      rw [interior_compl]
      exact hxt
  rcases IsPreconnected.subset_or_subset isOpen_interior isOpen_interior
      ((disjoint_compl_right : Disjoint t tᶜ).mono interior_subset interior_subset) hsub hs
      with h | h
  · obtain ⟨x, hx, hxt⟩ := h2
    exact hxt (interior_subset (h hx))
  · obtain ⟨x, hx, hxt⟩ := h1
    exact (interior_subset (h hx) : x ∈ tᶜ) hxt

theorem u4h_mem_segment_iff_lin (s t x : Plane) :
    x ∈ segment ℝ s t ↔ ∃ l : ℝ, 0 ≤ l ∧ l ≤ 1 ∧ x = s + l • (t - s) := by
  rw [segment_eq_image]
  constructor
  · rintro ⟨l, ⟨h0, h1⟩, rfl⟩
    exact ⟨l, h0, h1, by module⟩
  · rintro ⟨l, h0, h1, rfl⟩
    exact ⟨l, ⟨h0, h1⟩, by module⟩

theorem u4h_lin_mem_segment (s t : Plane) {l : ℝ} (h0 : 0 ≤ l) (h1 : l ≤ 1) :
    s + l • (t - s) ∈ segment ℝ s t :=
  (u4h_mem_segment_iff_lin s t _).mpr ⟨l, h0, h1, rfl⟩

theorem u4h_det_lin (u r s t : Plane) (l : ℝ) :
    det u (s + l • (t - s) - r) = det u (s - r) + l * det u (t - s) := by
  simp only [det, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
    Prod.smul_snd, smul_eq_mul]; ring

/-- The base vertices `p, r` are frontier points and have vanishing base determinant. -/
theorem u4h_det_base_zero (p r x : Plane) (hx : x = p ∨ x = r) : det (p - r) (x - r) = 0 := by
  rcases hx with rfl | rfl
  · exact u4h_det_self _
  · simp [det]

theorem u4h_base_mem_frontier {p q r : Plane} (hD : 0 < det (q - p) (r - p)) {x : Plane}
    (hx : x = p ∨ x = r) : x ∈ frontier (convexHull ℝ {p, q, r}) := by
  rw [u4h_frontier_hull3 hD]
  rcases hx with rfl | rfl
  · exact Or.inl (Or.inl (left_mem_segment ℝ _ _))
  · exact Or.inl (Or.inr (right_mem_segment ℝ _ _))

/-- Points of the segment on the frontier of the triangle have vanishing base determinant,
under the hypothesis that its points on the two side edges are base vertices. -/
theorem u4h_det_zero_of_frontier {p q r s t : Plane} (hD : 0 < det (q - p) (r - p))
    (H1 : segment ℝ s t ∩ (segment ℝ p q ∪ segment ℝ q r) ⊆ {p, r}) {z : Plane}
    (hz : z ∈ segment ℝ s t) (hzf : z ∈ frontier (convexHull ℝ {p, q, r})) :
    det (p - r) (z - r) = 0 := by
  rw [u4h_frontier_hull3 hD] at hzf
  rcases hzf with h | h
  · exact u4h_det_base_zero p r z (H1 ⟨hz, h⟩)
  · exact u4h_det_segment_zero h

/-- One-sided step: from an interior point `x` of the triangle on the segment, the sub-segment
towards an endpoint `e` contains a point `z ≠ x` of the segment with vanishing base determinant. -/
theorem u4h_exists_zero_towards {p q r s t x e : Plane} (hD : 0 < det (q - p) (r - p))
    (H1 : segment ℝ s t ∩ (segment ℝ p q ∪ segment ℝ q r) ⊆ {p, r})
    (He : e ∈ convexHull ℝ {p, q, r} → e = p ∨ e = r)
    (hes : e ∈ segment ℝ s t) (hx : x ∈ segment ℝ s t)
    (hxi : x ∈ interior (convexHull ℝ {p, q, r})) :
    ∃ z ∈ segment ℝ x e, z ≠ x ∧ det (p - r) (z - r) = 0 := by
  by_cases heT : e ∈ convexHull ℝ {p, q, r}
  · refine ⟨e, right_mem_segment ℝ x e, fun hex => ?_, u4h_det_base_zero p r e (He heT)⟩
    have := u4h_base_mem_frontier hD (He heT)
    rw [hex] at this
    exact (disjoint_interior_frontier.notMem_of_mem_left hxi) this
  · obtain ⟨z, hz, hzf⟩ := u4h_preconnected_inter_frontier (convex_segment x e).isPreconnected
      ⟨x, left_mem_segment ℝ x e, interior_subset hxi⟩ ⟨e, right_mem_segment ℝ x e, heT⟩
    have hzS : z ∈ segment ℝ s t := (convex_segment s t).segment_subset hx hes hz
    refine ⟨z, hz, fun hzx => ?_, u4h_det_zero_of_frontier hD H1 hzS hzf⟩
    rw [hzx] at hzf
    exact disjoint_interior_frontier.notMem_of_mem_left hxi hzf

/-- Claim A: no point of the segment lies in the open triangle. -/
theorem u4h_no_interior_point {p q r s t : Plane} (hD : 0 < det (q - p) (r - p))
    (H1 : segment ℝ s t ∩ (segment ℝ p q ∪ segment ℝ q r) ⊆ {p, r})
    (H2 : s ∈ convexHull ℝ {p, q, r} → s = p ∨ s = r)
    (H3 : t ∈ convexHull ℝ {p, q, r} → t = p ∨ t = r) (x : Plane) (hx : x ∈ segment ℝ s t) :
    x ∉ interior (convexHull ℝ {p, q, r}) := by
  intro hxi
  have hxpos : 0 < det (p - r) (x - r) := by
    rw [u4h_interior_hull3 hD] at hxi
    exact hxi.2.2
  obtain ⟨z1, hz1, hz1x, hg1⟩ :=
    u4h_exists_zero_towards hD H1 H2 (left_mem_segment ℝ s t) hx hxi
  obtain ⟨z2, hz2, hz2x, hg2⟩ :=
    u4h_exists_zero_towards hD H1 H3 (right_mem_segment ℝ s t) hx hxi
  obtain ⟨l, hl0, hl1, rfl⟩ := (u4h_mem_segment_iff_lin s t x).mp hx
  obtain ⟨α, hα0, -, hz1e⟩ := (u4h_mem_segment_iff_lin _ s z1).mp hz1
  obtain ⟨β, hβ0, -, hz2e⟩ := (u4h_mem_segment_iff_lin _ t z2).mp hz2
  have hαpos : 0 < α := by
    rcases hα0.lt_or_eq with h | h
    · exact h
    · subst h; exact absurd (by rw [hz1e]; simp) hz1x
  have hβpos : 0 < β := by
    rcases hβ0.lt_or_eq with h | h
    · exact h
    · subst h; exact absurd (by rw [hz2e]; simp) hz2x
  -- the base determinant along the line is affine in the parameter
  have e1 : det (p - r) (z1 - r) = det (p - r) (s + l • (t - s) - r) - α * l * det (p - r) (t - s) := by
    rw [hz1e]
    simp only [det, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
      Prod.smul_snd, smul_eq_mul]; ring
  have e2 : det (p - r) (z2 - r) = det (p - r) (s + l • (t - s) - r) + β * (1 - l) * det (p - r) (t - s) := by
    rw [hz2e]
    simp only [det, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
      Prod.smul_snd, smul_eq_mul]; ring
  rw [e1] at hg1
  rw [e2] at hg2
  -- `g x = α l D' = -β (1-l) D'` forces `D' = 0`, hence `g x = 0`
  have hl0' : 0 < l := by
    rcases hl0.lt_or_eq with h | h
    · exact h
    · exfalso
      subst h
      have hsT : s ∈ convexHull ℝ {p, q, r} := by simpa using interior_subset hxi
      have := u4h_base_mem_frontier hD (H2 hsT)
      exact disjoint_interior_frontier.notMem_of_mem_left hxi (by simpa using this)
  have hl1' : l < 1 := by
    rcases hl1.lt_or_eq with h | h
    · exact h
    · exfalso
      subst h
      have htT : t ∈ convexHull ℝ {p, q, r} := by simpa using interior_subset hxi
      have := u4h_base_mem_frontier hD (H3 htT)
      exact disjoint_interior_frontier.notMem_of_mem_left hxi (by simpa using this)
  have hsum : (α * l + β * (1 - l)) * det (p - r) (t - s) = 0 := by
    linear_combination hg2 - hg1
  have hcoef : 0 < α * l + β * (1 - l) := by
    have := mul_pos hαpos hl0'
    have := mul_pos hβpos (sub_pos.mpr hl1')
    linarith
  have hD0 : det (p - r) (t - s) = 0 := by
    rcases mul_eq_zero.mp hsum with h | h
    · exact absurd h hcoef.ne'
    · exact h
  rw [hD0] at hg1
  linarith

end U4D_block

section U4E_block

/-! Segment against a triangle, part 2 (U4 helpers): Claim B and the conclusion
`segment ∩ triangle ⊆ {p, r}`. -/

/-- Near an interior point of the edge `[c, a]` the two other sub-determinants are positive. -/
theorem u4h_near_open_edge {a b c x : Plane} (hD : 0 < det (b - a) (c - a))
    (hx : x ∈ openSegment ℝ c a) :
    ∃ ε > 0, ∀ y, dist y x < ε → 0 < det (b - a) (y - a) ∧ 0 < det (c - b) (y - b) := by
  rw [openSegment_eq_image] at hx
  obtain ⟨t, ⟨ht0, ht1⟩, rfl⟩ := hx
  have h1 : 0 < det (b - a) ((1 - t) • c + t • a - a) := by
    have e : det (b - a) ((1 - t) • c + t • a - a) = (1 - t) * det (b - a) (c - a) := by
      simp only [det, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
        Prod.smul_snd, smul_eq_mul]; ring
    rw [e]; exact mul_pos (by linarith) hD
  have h2 : 0 < det (c - b) ((1 - t) • c + t • a - b) := by
    have e : det (c - b) ((1 - t) • c + t • a - b) = t * det (b - a) (c - a) := by
      simp only [det, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
        Prod.smul_snd, smul_eq_mul]; ring
    rw [e]; exact mul_pos ht0 hD
  have hopen : IsOpen {y : Plane | 0 < det (b - a) (y - a) ∧ 0 < det (c - b) (y - b)} :=
    (u4h_isOpen_det_pos _ _).and (u4h_isOpen_det_pos _ _)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hopen.mem_nhds ⟨h1, h2⟩)
  exact ⟨ε, hε, fun y hy => hball (Metric.mem_ball.mpr hy)⟩

/-- A point of the line `r + κ • u` between two of its points lies on their segment. -/
theorem u4h_line_point_mem_segment {r u s t : Plane} {σs σt κ : ℝ} (hs : s = r + σs • u)
    (ht : t = r + σt • u) (hκ : (σs ≤ κ ∧ κ ≤ σt) ∨ (σt ≤ κ ∧ κ ≤ σs)) :
    r + κ • u ∈ segment ℝ s t := by
  by_cases hst : σt = σs
  · have hκs : κ = σs := by rcases hκ with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> linarith
    rw [hκs, ← hs]
    exact left_mem_segment ℝ s t
  · have hne : σt - σs ≠ 0 := sub_ne_zero.mpr hst
    rw [u4h_mem_segment_iff_lin]
    refine ⟨(κ - σs) / (σt - σs), ?_, ?_, ?_⟩
    · rcases hκ with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have hlt : σs < σt := lt_of_le_of_ne (h1.trans h2) (Ne.symm hst)
        exact div_nonneg (by linarith) (by linarith)
      · have hlt : σt < σs := lt_of_le_of_ne (h1.trans h2) hst
        exact div_nonneg_of_nonpos (by linarith) (by linarith)
    · rcases hκ with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have hlt : σs < σt := lt_of_le_of_ne (h1.trans h2) (Ne.symm hst)
        rw [div_le_one (by linarith)]; linarith
      · have hlt : σt < σs := lt_of_le_of_ne (h1.trans h2) hst
        rw [div_le_one_of_neg (by linarith)]; linarith
    · rw [hs, ht]
      have e : r + σs • u + ((κ - σs) / (σt - σs)) • (r + σt • u - (r + σs • u)) =
          r + (σs + (κ - σs) / (σt - σs) * (σt - σs)) • u := by
        simp only [add_sub_add_left_eq_sub, ← sub_smul, smul_smul, add_smul]; abel
      rw [e, div_mul_cancel₀ _ hne]
      congr 2; ring

/-- Claim B, collinear sub-case: if the base determinant vanishes identically on the segment and
the segment meets the open base edge, both base vertices lie on the segment. -/
theorem u4h_collinear_case {p q r s t : Plane} (hD : 0 < det (q - p) (r - p))
    (H2 : s ∈ convexHull ℝ {p, q, r} → s = p ∨ s = r)
    (H3 : t ∈ convexHull ℝ {p, q, r} → t = p ∨ t = r)
    {l : ℝ} (hl0 : 0 < l) (hl1 : l < 1) (hs0 : det (p - r) (s - r) = 0)
    (ht0 : det (p - r) (t - r) = 0) (hxo : s + l • (t - s) ∈ openSegment ℝ r p) :
    p ∈ segment ℝ s t ∧ r ∈ segment ℝ s t := by
  have hpr : p - r ≠ 0 := by
    intro h
    have : r = p := (sub_eq_zero.mp h).symm
    rw [this] at hD
    simp [det] at hD
  obtain ⟨σs, hs⟩ : ∃ σ : ℝ, s = r + σ • (p - r) :=
    ⟨_, by rw [← scalar_of_det_zero hpr hs0]; abel⟩
  obtain ⟨σt, ht⟩ : ∃ σ : ℝ, t = r + σ • (p - r) :=
    ⟨_, by rw [← scalar_of_det_zero hpr ht0]; abel⟩
  -- the parameter of `x` on the base line
  rw [openSegment_eq_image] at hxo
  obtain ⟨θ, ⟨hθ0, hθ1⟩, hθ⟩ := hxo
  simp only at hθ
  have hθ' : θ = σs + l * (σt - σs) := by
    have e1 : (1 - θ) • r + θ • p = r + θ • (p - r) := by module
    have e2 : s + l • (t - s) = r + (σs + l * (σt - σs)) • (p - r) := by
      rw [hs, ht]; module
    rw [e1, e2] at hθ
    have := smul_left_injective ℝ hpr (add_left_cancel hθ)
    exact this
  -- a point `r + σ • (p - r)` with `0 ≤ σ ≤ 1` lies in the triangle
  have hmemT : ∀ σ : ℝ, 0 ≤ σ → σ ≤ 1 → r + σ • (p - r) ∈ convexHull ℝ {p, q, r} := by
    intro σ h0 h1
    rw [u4h_hull3_rot, u4h_hull3_rot]
    exact u4h_segment_subset_hull3 r p q (u4h_lin_mem_segment r p h0 h1)
  have hσ : ∀ σ : ℝ, r + σ • (p - r) = p ∨ r + σ • (p - r) = r → σ = 1 ∨ σ = 0 := by
    intro σ h
    rcases h with h | h
    · left
      have : σ • (p - r) = (1 : ℝ) • (p - r) := by rw [one_smul]; exact eq_sub_of_add_eq' h
      exact smul_left_injective ℝ hpr this
    · right
      have : σ • (p - r) = (0 : ℝ) • (p - r) := by rw [zero_smul]; exact add_eq_left.mp h
      exact smul_left_injective ℝ hpr this
  have hs' : σs ≤ 0 ∨ 1 ≤ σs := by
    by_contra hc
    simp only [not_or, not_le] at hc
    rcases hσ σs (by rw [← hs]; exact H2 (by rw [hs]; exact hmemT σs hc.1.le hc.2.le)) with h | h
    · linarith
    · linarith
  have ht' : σt ≤ 0 ∨ 1 ≤ σt := by
    by_contra hc
    simp only [not_or, not_le] at hc
    rcases hσ σt (by rw [← ht]; exact H3 (by rw [ht]; exact hmemT σt hc.1.le hc.2.le)) with h | h
    · linarith
    · linarith
  have hcase : (σs ≤ 0 ∧ 1 ≤ σt) ∨ (σt ≤ 0 ∧ 1 ≤ σs) := by
    rcases hs' with h1 | h1 <;> rcases ht' with h2 | h2
    · exfalso; nlinarith
    · exact Or.inl ⟨h1, h2⟩
    · exact Or.inr ⟨h2, h1⟩
    · exfalso; nlinarith
  have hp : p = r + (1 : ℝ) • (p - r) := by simp
  have hr : r = r + (0 : ℝ) • (p - r) := by simp
  constructor
  · rw [hp]
    apply u4h_line_point_mem_segment hs ht
    rcases hcase with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨by linarith, h2⟩
    · exact Or.inr ⟨by linarith, h2⟩
  · rw [hr]
    apply u4h_line_point_mem_segment hs ht
    rcases hcase with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨h1, by linarith⟩
    · exact Or.inr ⟨h1, by linarith⟩

end U4E_block

section U4F_block

/-! Segment against a triangle, part 3 (U4 helpers): the conclusion. -/

theorem u4h_segment_inter_tri {p q r s t : Plane} (hD : 0 < det (q - p) (r - p))
    (H1 : segment ℝ s t ∩ (segment ℝ p q ∪ segment ℝ q r) ⊆ {p, r})
    (H2 : s ∈ convexHull ℝ {p, q, r} → s = p ∨ s = r)
    (H3 : t ∈ convexHull ℝ {p, q, r} → t = p ∨ t = r)
    (H5 : ¬ (p ∈ segment ℝ s t ∧ r ∈ segment ℝ s t)) :
    segment ℝ s t ∩ convexHull ℝ {p, q, r} ⊆ {p, r} := by
  rintro x ⟨hxS, hxT⟩
  by_contra hxpr
  have hxp : x ≠ p := by rintro rfl; exact hxpr (Set.mem_insert _ _)
  have hxr : x ≠ r := by rintro rfl; exact hxpr (Set.mem_insert_of_mem _ rfl)
  have hxni := u4h_no_interior_point hD H1 H2 H3 x hxS
  have hxf : x ∈ frontier (convexHull ℝ {p, q, r}) := ⟨subset_closure hxT, hxni⟩
  have hxrp : x ∈ segment ℝ r p := by
    rw [u4h_frontier_hull3 hD] at hxf
    rcases hxf with h | h
    · exact absurd (H1 ⟨hxS, h⟩) hxpr
    · exact h
  have hxo : x ∈ openSegment ℝ r p := mem_openSegment_of_ne_left_right hxr.symm hxp.symm hxrp
  have hg0 : det (p - r) (x - r) = 0 := u4h_det_segment_zero hxrp
  obtain ⟨l, hl0, hl1, hxl⟩ := (u4h_mem_segment_iff_lin s t x).mp hxS
  have hl0' : 0 < l := by
    rcases hl0.lt_or_eq with h | h
    · exact h
    · exfalso
      rw [← h, zero_smul, add_zero] at hxl
      subst hxl
      exact hxpr (H2 hxT)
  have hl1' : l < 1 := by
    rcases hl1.lt_or_eq with h | h
    · exact h
    · exfalso
      rw [h, one_smul, add_sub_cancel] at hxl
      subst hxl
      exact hxpr (H3 hxT)
  have hlin := u4h_det_lin (p - r) r s t l
  rw [← hxl, hg0] at hlin
  by_cases hDl : det (p - r) (t - s) = 0
  · have hs0 : det (p - r) (s - r) = 0 := by rw [hDl] at hlin; linarith
    have ht0 : det (p - r) (t - r) = 0 := by
      have e : t - r = (s - r) + (t - s) := by abel
      rw [e, u4h_det_add_right, hs0, hDl, add_zero]
    exact H5 (u4h_collinear_case hD H2 H3 hl0' hl1' hs0 ht0 (hxl ▸ hxo))
  · obtain ⟨ε, hε, hnear⟩ := u4h_near_open_edge hD hxo
    have hts1 : 0 < ‖t - s‖ + 1 := by positivity
    set δ : ℝ := min (ε / (2 * (‖t - s‖ + 1))) (min l (1 - l)) with hδdef
    have hδ : 0 < δ := by
      apply lt_min (by positivity) (lt_min hl0' (by linarith))
    have hδl : δ ≤ l := (min_le_right _ _).trans (min_le_left _ _)
    have hδ1 : δ ≤ 1 - l := (min_le_right _ _).trans (min_le_right _ _)
    have hδε : δ * ‖t - s‖ < ε := by
      have h1 : δ ≤ ε / (2 * (‖t - s‖ + 1)) := min_le_left _ _
      have h2 : δ * ‖t - s‖ ≤ ε / (2 * (‖t - s‖ + 1)) * ‖t - s‖ :=
        mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
      have h3 : ε / (2 * (‖t - s‖ + 1)) * ‖t - s‖ < ε := by
        rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
        nlinarith [norm_nonneg (t - s)]
      linarith
    obtain ⟨η, hηabs, hηD⟩ : ∃ η : ℝ, |η| = δ ∧ 0 < η * det (p - r) (t - s) := by
      rcases lt_or_gt_of_ne hDl with h | h
      · exact ⟨-δ, by rw [abs_neg, abs_of_pos hδ], by nlinarith⟩
      · exact ⟨δ, abs_of_pos hδ, mul_pos hδ h⟩
    have hηle : -δ ≤ η ∧ η ≤ δ := abs_le.mp (le_of_eq hηabs)
    have hy0 : 0 ≤ l + η := by linarith [hηle.1]
    have hy1 : l + η ≤ 1 := by linarith [hηle.2]
    have hdist : dist (s + (l + η) • (t - s)) x < ε := by
      rw [hxl, dist_eq_norm]
      have e : s + (l + η) • (t - s) - (s + l • (t - s)) = η • (t - s) := by module
      rw [e, norm_smul, Real.norm_eq_abs, hηabs]
      exact hδε
    have hgy : 0 < det (p - r) (s + (l + η) • (t - s) - r) := by
      rw [u4h_det_lin]
      linear_combination hηD + hlin
    have hy' := hnear _ hdist
    have hyi : s + (l + η) • (t - s) ∈ interior (convexHull ℝ {p, q, r}) := by
      rw [u4h_interior_hull3 hD]
      exact ⟨hy'.1, hy'.2, hgy⟩
    exact u4h_no_interior_point hD H1 H2 H3 _ (u4h_lin_mem_segment s t hy0 hy1) hyi

/-! ### `ZMod` index facts for `4 ≤ n` -/


theorem u4h_natCast_ne_zero {k : ℕ} (hk0 : 0 < k) (hk : k < n) : (k : ZMod n) ≠ 0 := by
  intro h
  rw [ZMod.natCast_eq_zero_iff] at h
  exact absurd (Nat.le_of_dvd hk0 h) (not_le.mpr hk)

theorem u4h_one_ne_zero (hn : 4 ≤ n) : (1 : ZMod n) ≠ 0 := by
  have := u4h_natCast_ne_zero (n := n) (k := 1) (by norm_num) (by omega)
  simpa using this

theorem u4h_two_ne_zero (hn : 4 ≤ n) : (2 : ZMod n) ≠ 0 := by
  have := u4h_natCast_ne_zero (n := n) (k := 2) (by norm_num) (by omega)
  simpa using this

theorem u4h_three_ne_zero (hn : 4 ≤ n) : (3 : ZMod n) ≠ 0 := by
  have := u4h_natCast_ne_zero (n := n) (k := 3) (by norm_num) (by omega)
  simpa using this

theorem u4h_adjacent_iff (i k : ZMod n) : adjacent i k ↔ k = i - 1 ∨ k = i ∨ k = i + 1 := by
  unfold adjacent
  constructor
  · rintro (h | h | h)
    · exact Or.inl (by linear_combination h)
    · exact Or.inr (Or.inl (by linear_combination h))
    · exact Or.inr (Or.inr (by linear_combination h))
  · rintro (h | h | h)
    · exact Or.inl (by linear_combination h)
    · exact Or.inr (Or.inl (by linear_combination h))
    · exact Or.inr (Or.inr (by linear_combination h))

/-- `i` and `i + 2` are remote when `4 ≤ n`. -/
theorem u4h_remote_add_two (hn : 4 ≤ n) (i : ZMod n) : remote i (i + 2) := by
  rw [remote, u4h_adjacent_iff]
  rintro (h | h | h)
  · exact u4h_three_ne_zero hn (by linear_combination h)
  · exact u4h_two_ne_zero hn (by linear_combination h)
  · exact u4h_one_ne_zero hn (by linear_combination h)

theorem u4h_remote_sub_two (hn : 4 ≤ n) (i : ZMod n) : remote i (i - 2) := by
  have := u4h_remote_add_two hn (i - 2)
  rw [sub_add_cancel] at this
  exact remote_symm this

end U4F_block

section U4G_block

/-! The ear criterion for an embedded polygon (U4 helpers): a vertex `j` whose closed ear
triangle contains no vertex other than `j-1, j, j+1` is a strict ear. -/

/-- No vertex of `P` other than `j - 1, j, j + 1` lies in the closed ear triangle at `j`. -/
def u4h_VertexEmpty (P : LabelledTuple n) (j : ZMod n) : Prop :=
  ∀ k, P k ∈ earHull P j → k = j - 1 ∨ k = j ∨ k = j + 1

theorem u4h_edgeSegment_prev (P : LabelledTuple n) (j : ZMod n) :
    edgeSegment P (j - 1) = segment ℝ (P (j - 1)) (P j) := by
  rw [u4h_edgeSegment_eq_segment, sub_add_cancel]

/-- (F1) a non-ear edge meets the two ear edges only in the base vertices. -/
theorem u4h_edge_inter_ears {P : LabelledTuple n} (hP : Embedded P) {j k : ZMod n}
    (hk1 : k ≠ j - 1) (hk2 : k ≠ j) :
    edgeSegment P k ∩ (edgeSegment P (j - 1) ∪ edgeSegment P j) ⊆ {P (j - 1), P (j + 1)} := by
  rintro x ⟨hxk, hx⟩
  rcases hx with hx | hx
  · by_cases hadj : adjacent k (j - 1)
    · rcases adjacent_distinct_cases hk1 hadj with h | h
      · have hmem : x ∈ edgeSegment P k ∩ edgeSegment P (k + 1) := ⟨hxk, by rw [← h]; exact hx⟩
        rw [hP.consecutive k] at hmem
        have hx' : x = P (k + 1) := hmem
        rw [hx', ← h]
        exact Set.mem_insert _ _
      · exact absurd (by rw [h, sub_add_cancel]) hk2
    · exact (Set.disjoint_left.mp (hP.remote_disjoint k (j - 1) hadj) hxk hx).elim
  · by_cases hadj : adjacent k j
    · rcases adjacent_distinct_cases hk2 hadj with h | h
      · exact absurd (by rw [h, add_sub_cancel_right]) hk1
      · have hmem : x ∈ edgeSegment P j ∩ edgeSegment P (j + 1) := ⟨hx, by rw [← h]; exact hxk⟩
        rw [hP.consecutive j] at hmem
        exact Set.mem_insert_of_mem _ hmem
    · exact (Set.disjoint_left.mp (hP.remote_disjoint k j hadj) hxk hx).elim

/-- (F4) a non-ear edge does not contain both base vertices. -/
theorem u4h_not_both_ends {P : LabelledTuple n} (hP : Embedded P) (hn : 4 ≤ n) {j k : ZMod n}
    (hk1 : k ≠ j - 1) (hk2 : k ≠ j) :
    ¬ (P (j - 1) ∈ edgeSegment P k ∧ P (j + 1) ∈ edgeSegment P k) := by
  rintro ⟨ha, hc⟩
  rcases u4h_incident_of_vertex_mem hP ha with h | h
  · exact hk1 h.symm
  · rcases u4h_incident_of_vertex_mem hP hc with h' | h'
    · exact u4h_three_ne_zero hn (by linear_combination h' - h)
    · exact hk2 (add_right_cancel h'.symm)

/-- The ear criterion, edge form: a non-ear edge meets the (vertex-empty, nondegenerate) ear
triangle only in the base vertices. -/
theorem u4h_edge_inter_earHull {P : LabelledTuple n} (hP : Embedded P) (hn : 4 ≤ n) {j : ZMod n}
    (hdet : det (P j - P (j - 1)) (P (j + 1) - P (j - 1)) ≠ 0) (hV : u4h_VertexEmpty P j)
    {k : ZMod n} (hk1 : k ≠ j - 1) (hk2 : k ≠ j) :
    edgeSegment P k ∩ earHull P j ⊆ {P (j - 1), P (j + 1)} := by
  have hE1 := u4h_edgeSegment_prev P j
  have hE2 := u4h_edgeSegment_eq_segment P j
  have hEk := u4h_edgeSegment_eq_segment P k
  have H1 := u4h_edge_inter_ears hP hk1 hk2
  have H5 := u4h_not_both_ends hP hn hk1 hk2
  have H2 : P k ∈ earHull P j → P k = P (j + 1) := fun h => by
    rcases hV k h with h1 | h1 | h1
    · exact absurd h1 hk1
    · exact absurd h1 hk2
    · rw [h1]
  have H3 : P (k + 1) ∈ earHull P j → P (k + 1) = P (j - 1) := fun h => by
    rcases hV (k + 1) h with h1 | h1 | h1
    · rw [h1]
    · exact absurd (by linear_combination h1) hk1
    · exact absurd (add_right_cancel h1) hk2
  rcases lt_or_gt_of_ne hdet with hneg | hpos
  · -- negative orientation: the positive triple is `(c, b, a)`
    have hD : 0 < det (P j - P (j + 1)) (P (j - 1) - P (j + 1)) := by
      have e : det (P j - P (j + 1)) (P (j - 1) - P (j + 1)) =
          -det (P j - P (j - 1)) (P (j + 1) - P (j - 1)) := by
        simp only [det, Prod.fst_sub, Prod.snd_sub]; ring
      rw [e]; linarith
    have hset : earHull P j = convexHull ℝ {P (j + 1), P j, P (j - 1)} := by
      unfold earHull
      congr 1
      ext x
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto
    intro x hx
    rw [hset] at hx
    rw [hEk] at hx
    have hres := u4h_segment_inter_tri hD ?_ ?_ ?_ ?_ hx
    · rcases hres with h | h
      · exact Set.mem_insert_of_mem _ h
      · exact h ▸ Set.mem_insert _ _
    · intro y hy
      have hy' : y ∈ edgeSegment P k ∩ (edgeSegment P (j - 1) ∪ edgeSegment P j) := by
        rw [hEk, hE1, hE2, segment_symm ℝ (P (j - 1)) (P j), segment_symm ℝ (P j) (P (j + 1))]
        exact ⟨hy.1, hy.2.symm⟩
      rcases H1 hy' with h | h
      · exact Set.mem_insert_of_mem _ h
      · exact h ▸ Set.mem_insert _ _
    · intro h
      exact Or.inl (H2 (by rw [hset]; exact h))
    · intro h
      exact Or.inr (H3 (by rw [hset]; exact h))
    · rintro ⟨h1, h2⟩
      exact H5 ⟨by rw [hEk]; exact h2, by rw [hEk]; exact h1⟩
  · -- positive orientation: the positive triple is `(a, b, c)`
    intro x hx
    unfold earHull at hx
    rw [hEk] at hx
    have hres := u4h_segment_inter_tri hpos ?_ ?_ ?_ ?_ hx
    · exact hres
    · intro y hy
      have hy' : y ∈ edgeSegment P k ∩ (edgeSegment P (j - 1) ∪ edgeSegment P j) := by
        rw [hEk, hE1, hE2]
        exact hy
      exact H1 hy'
    · intro h
      exact Or.inr (H2 h)
    · intro h
      exact Or.inl (H3 h)
    · rintro ⟨h1, h2⟩
      exact H5 ⟨by rw [hEk]; exact h1, by rw [hEk]; exact h2⟩

/-- Ear edges lie in the ear triangle. -/
theorem u4h_ear_edges_subset (P : LabelledTuple n) (j : ZMod n) :
    edgeSegment P (j - 1) ∪ edgeSegment P j ⊆ earHull P j := by
  rintro x (h | h)
  · rw [u4h_edgeSegment_prev] at h
    exact u4h_segment_subset_hull3 _ _ _ h
  · rw [u4h_edgeSegment_eq_segment] at h
    unfold earHull
    rw [u4h_hull3_rot]
    exact u4h_segment_subset_hull3 _ _ _ h

/-- **Ear criterion**: a vertex-empty nondegenerate ear triangle meets the polygon exactly in the
two ear edges. -/
theorem u4h_strict_ear_of_vertex_empty {P : LabelledTuple n} (hP : Embedded P) (hn : 4 ≤ n)
    {j : ZMod n} (hdet : det (P j - P (j - 1)) (P (j + 1) - P (j - 1)) ≠ 0)
    (hV : u4h_VertexEmpty P j) :
    earHull P j ∩ embeddedPolygonImage P = edgeSegment P (j - 1) ∪ edgeSegment P j := by
  apply Set.Subset.antisymm
  · rintro x ⟨hxT, hxC⟩
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hxC
    by_cases hk1 : k = j - 1
    · exact Or.inl (hk1 ▸ hk)
    by_cases hk2 : k = j
    · exact Or.inr (hk2 ▸ hk)
    rcases u4h_edge_inter_earHull hP hn hdet hV hk1 hk2 ⟨hk, hxT⟩ with h | h
    · rw [h]; exact Or.inl (u4h_start_mem_edgeSegment P (j - 1))
    · rw [h]; exact Or.inr (u4h_end_mem_edgeSegment P j)
  · intro x hx
    refine ⟨u4h_ear_edges_subset P j hx, ?_⟩
    rcases hx with h | h
    · exact u4h_edgeSegment_subset_polygonImage P _ h
    · exact u4h_edgeSegment_subset_polygonImage P _ h

end U4G_block

section U4H_block

variable [NeZero n]

/-! Edges and polygon image of `deleteVertex` (U4 helpers). -/

theorem u4h_edgeSegment_deleteVertex (P : LabelledTuple (n + 1)) (j : ZMod (n + 1)) {i : ZMod n}
    (hi : i ≠ -1) : edgeSegment (deleteVertex P j) i = edgeSegment P (deletionIndex j i) := by
  simp only [edgeSegment, edgePoint_deleteVertex P j hi]

theorem u4h_edgeSegment_deleteVertex_last (P : LabelledTuple (n + 1)) (j : ZMod (n + 1)) :
    edgeSegment (deleteVertex P j) (-1) = segment ℝ (P (j - 1)) (P (j + 1)) := by
  rw [u4h_edgeSegment_eq_segment, neg_add_cancel, deleteVertex_last, deleteVertex_zero]

theorem u4h_deletionIndex_ne_prev_or_last (j : ZMod (n + 1)) (i : ZMod n) :
    deletionIndex j i ≠ j ∧ (i ≠ -1 → deletionIndex j i ≠ j - 1) :=
  ⟨deletionIndex_ne_deleted j i, fun hi => deletionIndex_ne_prev j hi⟩

/-- Membership in the polygon image of the cut polygon. -/
theorem u4h_mem_polygonImage_deleteVertex (P : LabelledTuple (n + 1)) (j : ZMod (n + 1))
    (x : Plane) :
    x ∈ embeddedPolygonImage (deleteVertex P j) ↔
      (∃ k, k ≠ j - 1 ∧ k ≠ j ∧ x ∈ edgeSegment P k) ∨ x ∈ segment ℝ (P (j - 1)) (P (j + 1)) := by
  constructor
  · intro hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    by_cases hi1 : i = -1
    · subst hi1
      rw [u4h_edgeSegment_deleteVertex_last] at hi
      exact Or.inr hi
    · rw [u4h_edgeSegment_deleteVertex P j hi1] at hi
      exact Or.inl ⟨_, deletionIndex_ne_prev j hi1, deletionIndex_ne_deleted j i, hi⟩
  · rintro (⟨k, hk1, hk2, hk⟩ | hx)
    · obtain ⟨i, rfl⟩ := deletionIndex_exhaust j hk2
      have hi1 : i ≠ -1 := by
        rintro rfl
        exact hk1 (deletionIndex_last j)
      exact Set.mem_iUnion.mpr ⟨i, by rw [u4h_edgeSegment_deleteVertex P j hi1]; exact hk⟩
    · exact Set.mem_iUnion.mpr ⟨-1, by rw [u4h_edgeSegment_deleteVertex_last]; exact hx⟩

omit [NeZero n] in
theorem u4h_diag_subset_earHull (P : LabelledTuple n) (j : ZMod n) :
    segment ℝ (P (j - 1)) (P (j + 1)) ⊆ earHull P j := by
  unfold earHull
  rw [u4h_hull3_rot, u4h_hull3_rot, segment_symm]
  exact u4h_segment_subset_hull3 _ _ _

/-- A strict ear meets the cut polygon exactly in the diagonal. -/
theorem u4h_earHull_inter_polygonImage_delete {P : LabelledTuple (n + 1)} (hP : Embedded P)
    {j : ZMod (n + 1)}
    (hstrict : earHull P j ∩ embeddedPolygonImage P = edgeSegment P (j - 1) ∪ edgeSegment P j) :
    earHull P j ∩ embeddedPolygonImage (deleteVertex P j) = segment ℝ (P (j - 1)) (P (j + 1)) := by
  apply Set.Subset.antisymm
  · rintro x ⟨hxT, hxC⟩
    rcases (u4h_mem_polygonImage_deleteVertex P j x).mp hxC with ⟨k, hk1, hk2, hk⟩ | hx
    · have hx' : x ∈ edgeSegment P (j - 1) ∪ edgeSegment P j := by
        rw [← hstrict]
        exact ⟨hxT, u4h_edgeSegment_subset_polygonImage P k hk⟩
      rcases u4h_edge_inter_ears hP hk1 hk2 ⟨hk, hx'⟩ with h | h
      · rw [h]; exact left_mem_segment ℝ _ _
      · rw [h]; exact right_mem_segment ℝ _ _
    · exact hx
  · intro x hx
    exact ⟨u4h_diag_subset_earHull P j hx,
      (u4h_mem_polygonImage_deleteVertex P j x).mpr (Or.inr hx)⟩

omit [NeZero n] in
/-- Points of a non-ear edge are not on the open diagonal (strict ear, `a ≠ c`). -/
theorem u4h_edge_disjoint_openDiag {P : LabelledTuple (n + 1)} (hP : Embedded P)
    {j : ZMod (n + 1)} (hac : P (j - 1) ≠ P (j + 1))
    (hstrict : earHull P j ∩ embeddedPolygonImage P = edgeSegment P (j - 1) ∪ edgeSegment P j)
    {k : ZMod (n + 1)} (hk1 : k ≠ j - 1) (hk2 : k ≠ j) {x : Plane} (hk : x ∈ edgeSegment P k) :
    x ∉ openSegment ℝ (P (j - 1)) (P (j + 1)) := by
  intro hxo
  have hxT : x ∈ earHull P j :=
    u4h_diag_subset_earHull P j (openSegment_subset_segment ℝ _ _ hxo)
  have hx' : x ∈ edgeSegment P (j - 1) ∪ edgeSegment P j := by
    rw [← hstrict]
    exact ⟨hxT, u4h_edgeSegment_subset_polygonImage P k hk⟩
  rcases u4h_edge_inter_ears hP hk1 hk2 ⟨hk, hx'⟩ with h | h
  · rw [h] at hxo
    exact hac (left_mem_openSegment_iff.mp hxo)
  · rw [h] at hxo
    exact hac (right_mem_openSegment_iff.mp hxo)

/-- The ear-cut identity for the polygon image (the corrected form of `U4_polygonImage_ear`:
it needs `P` embedded, `j` a strict ear and `P (j-1) ≠ P (j+1)`). -/
theorem u4h_polygonImage_ear {P : LabelledTuple (n + 1)} (hP : Embedded P) {j : ZMod (n + 1)}
    (hac : P (j - 1) ≠ P (j + 1))
    (hstrict : earHull P j ∩ embeddedPolygonImage P = edgeSegment P (j - 1) ∪ edgeSegment P j) :
    embeddedPolygonImage P = (embeddedPolygonImage (deleteVertex P j) \ openSegment ℝ (P (j - 1)) (P (j + 1))) ∪
      edgeSegment P (j - 1) ∪ edgeSegment P j := by
  apply Set.Subset.antisymm
  · intro x hx
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hx
    by_cases hk1 : k = j - 1
    · exact Or.inl (Or.inr (hk1 ▸ hk))
    by_cases hk2 : k = j
    · exact Or.inr (hk2 ▸ hk)
    refine Or.inl (Or.inl ⟨?_, u4h_edge_disjoint_openDiag hP hac hstrict hk1 hk2 hk⟩)
    exact (u4h_mem_polygonImage_deleteVertex P j x).mpr (Or.inl ⟨k, hk1, hk2, hk⟩)
  · rintro x ((⟨hxC, hxo⟩ | hx) | hx)
    · rcases (u4h_mem_polygonImage_deleteVertex P j x).mp hxC with ⟨k, -, -, hk⟩ | hxD
      · exact u4h_edgeSegment_subset_polygonImage P k hk
      · -- on the closed diagonal but not the open one: an endpoint
        rw [← insert_endpoints_openSegment] at hxD
        rcases hxD with h | h | h
        · rw [h]; exact u4h_vertex_mem_polygonImage P _
        · rw [h]; exact u4h_vertex_mem_polygonImage P _
        · exact absurd h hxo
    · exact u4h_edgeSegment_subset_polygonImage P _ hx
    · exact u4h_edgeSegment_subset_polygonImage P _ hx

end U4H_block

section U4I_block

/-! `deleteVertex` at a strict ear is embedded (U4 helpers). -/

theorem u4h_one_ne_zero' (hn : 2 ≤ n) : (1 : ZMod n) ≠ 0 := by
  have := u4h_natCast_ne_zero (n := n) (k := 1) (by norm_num) (by omega)
  simpa using this

theorem u4h_two_ne_zero' (hn : 3 ≤ n) : (2 : ZMod n) ≠ 0 := by
  have := u4h_natCast_ne_zero (n := n) (k := 2) (by norm_num) (by omega)
  simpa using this

theorem u4h_deletionIndex_neg_two [NeZero n] (hn : 2 ≤ n) (j : ZMod (n + 1)) :
    deletionIndex j (-2) = j - 2 := by
  have h2 : (-2 : ZMod n) ≠ -1 := fun h => u4h_one_ne_zero' hn (by linear_combination -h)
  have h := deletionIndex_next j h2
  rw [show (-2 : ZMod n) + 1 = -1 by ring, deletionIndex_last] at h
  linear_combination -h

/-- A non-ear edge meets the diagonal only in the base vertices (strict ear). -/
theorem u4h_edge_inter_diag {P : LabelledTuple n} (hP : Embedded P) {j : ZMod n}
    (hstrict : earHull P j ∩ embeddedPolygonImage P = edgeSegment P (j - 1) ∪ edgeSegment P j)
    {k : ZMod n} (hk1 : k ≠ j - 1) (hk2 : k ≠ j) :
    edgeSegment P k ∩ segment ℝ (P (j - 1)) (P (j + 1)) ⊆ {P (j - 1), P (j + 1)} := by
  rintro x ⟨hk, hD⟩
  have hx' : x ∈ edgeSegment P (j - 1) ∪ edgeSegment P j := by
    rw [← hstrict]
    exact ⟨u4h_diag_subset_earHull P j hD, u4h_edgeSegment_subset_polygonImage P k hk⟩
  exact u4h_edge_inter_ears hP hk1 hk2 ⟨hk, hx'⟩

theorem u4h_eq_sub_two_of_mem {P : LabelledTuple n} (hP : Embedded P) {j k : ZMod n}
    (hk1 : k ≠ j - 1) (h : P (j - 1) ∈ edgeSegment P k) : k = j - 2 := by
  rcases u4h_incident_of_vertex_mem hP h with h' | h'
  · exact absurd h'.symm hk1
  · linear_combination -h'

theorem u4h_eq_add_one_of_mem {P : LabelledTuple n} (hP : Embedded P) {j k : ZMod n}
    (hk2 : k ≠ j) (h : P (j + 1) ∈ edgeSegment P k) : k = j + 1 := by
  rcases u4h_incident_of_vertex_mem hP h with h' | h'
  · exact h'.symm
  · exact absurd (add_right_cancel h').symm hk2

/-- **Cutting a strict ear keeps the polygon embedded.** -/
theorem u4h_embedded_deleteVertex [NeZero n] (hn : 3 ≤ n) {P : LabelledTuple (n + 1)}
    (hP : Embedded P) {j : ZMod (n + 1)} (hac : P (j - 1) ≠ P (j + 1))
    (hstrict : earHull P j ∩ embeddedPolygonImage P = edgeSegment P (j - 1) ∪ edgeSegment P j) :
    Embedded (deleteVertex P j) := by
  have hn4 : 4 ≤ n + 1 := by omega
  have h1n : (1 : ZMod n) ≠ 0 := u4h_one_ne_zero' (by omega)
  have h2n1 : (2 : ZMod (n + 1)) ≠ 0 := u4h_two_ne_zero hn4
  have h3n1 : (3 : ZMod (n + 1)) ≠ 0 := u4h_three_ne_zero hn4
  -- the two non-ear edges at the base vertices
  have hj2_1 : j - 2 ≠ j - 1 := fun h => u4h_one_ne_zero hn4 (by linear_combination -h)
  have hj2_2 : j - 2 ≠ j := fun h => h2n1 (by linear_combination -h)
  have hj1_1 : j + 1 ≠ j - 1 := fun h => h2n1 (by linear_combination h)
  have hj1_2 : j + 1 ≠ j := fun h => u4h_one_ne_zero hn4 (by linear_combination h)
  -- a non-ear edge of `P` is disjoint from the diagonal unless it ends at `a` or starts at `c`
  have hdisj : ∀ k, k ≠ j - 1 → k ≠ j → k ≠ j - 2 → k ≠ j + 1 →
      Disjoint (edgeSegment P k) (segment ℝ (P (j - 1)) (P (j + 1))) := by
    intro k hk1 hk2 hk3 hk4
    rw [Set.disjoint_left]
    intro x hxk hxD
    rcases u4h_edge_inter_diag hP hstrict hk1 hk2 ⟨hxk, hxD⟩ with h | h
    · exact hk3 (u4h_eq_sub_two_of_mem hP hk1 (h ▸ hxk))
    · exact hk4 (u4h_eq_add_one_of_mem hP hk2 (h ▸ hxk))
  refine ⟨fun i => ?_, fun i i' hr => ?_, fun i => ?_⟩
  · by_cases hi : i = -1
    · subst hi
      rw [edge_deleteVertex_last]
      exact sub_ne_zero.mpr (Ne.symm hac)
    · rw [edge_deleteVertex P j hi]
      exact hP.edge_ne_zero _
  · -- remote pairs
    have hadj_self : ∀ i : ZMod n, adjacent i i := fun i => Or.inr (Or.inl (sub_self i))
    by_cases hi : i = -1
    · subst hi
      have hi' : i' ≠ -1 := fun h => hr (h ▸ hadj_self _)
      rw [u4h_edgeSegment_deleteVertex_last, u4h_edgeSegment_deleteVertex P j hi']
      refine (hdisj _ (deletionIndex_ne_prev j hi') (deletionIndex_ne_deleted j i') ?_ ?_).symm
      · intro h
        rw [← u4h_deletionIndex_neg_two (by omega) j] at h
        have := deletionIndex_injective j h
        exact hr (by rw [u4h_adjacent_iff]; exact Or.inl (by rw [this]; ring))
      · intro h
        rw [← deletionIndex_zero j] at h
        have := deletionIndex_injective j h
        exact hr (by rw [this]; exact Or.inr (Or.inr (by ring)))
    · by_cases hi' : i' = -1
      · subst hi'
        rw [u4h_edgeSegment_deleteVertex_last, u4h_edgeSegment_deleteVertex P j hi]
        refine hdisj _ (deletionIndex_ne_prev j hi) (deletionIndex_ne_deleted j i) ?_ ?_
        · intro h
          rw [← u4h_deletionIndex_neg_two (by omega) j] at h
          have := deletionIndex_injective j h
          exact hr (by rw [this]; exact Or.inr (Or.inr (by ring)))
        · intro h
          rw [← deletionIndex_zero j] at h
          have := deletionIndex_injective j h
          exact hr (by rw [this]; exact Or.inl (by ring))
      · rw [u4h_edgeSegment_deleteVertex P j hi, u4h_edgeSegment_deleteVertex P j hi']
        apply hP.remote_disjoint
        rw [remote, u4h_adjacent_iff]
        rintro (h | h | h)
        · rw [eq_sub_iff_add_eq, ← deletionIndex_next j hi'] at h
          have := deletionIndex_injective j h
          exact hr (Or.inl (by linear_combination this))
        · exact hr (deletionIndex_injective j h ▸ hadj_self i)
        · rw [← deletionIndex_next j hi] at h
          have := deletionIndex_injective j h
          exact hr (Or.inr (Or.inr (by linear_combination this)))
  · -- consecutive pairs
    by_cases hi : i = -1
    · subst hi
      have h0 : (0 : ZMod n) ≠ -1 := fun h => h1n (by linear_combination h)
      rw [neg_add_cancel, u4h_edgeSegment_deleteVertex_last, u4h_edgeSegment_deleteVertex P j h0,
        deletionIndex_zero, deleteVertex_zero]
      ext x
      constructor
      · rintro ⟨hxD, hxk⟩
        rcases u4h_edge_inter_diag hP hstrict hj1_1 hj1_2 ⟨hxk, hxD⟩ with h | h
        · exfalso
          have := u4h_eq_sub_two_of_mem hP hj1_1 (h ▸ hxk)
          exact h3n1 (by linear_combination this)
        · exact h
      · intro hx
        have hx' : x = P (j + 1) := hx
        rw [hx']
        exact ⟨right_mem_segment ℝ _ _, u4h_start_mem_edgeSegment P (j + 1)⟩
    · by_cases hi1 : i + 1 = -1
      · have hi2 : i = -2 := by linear_combination hi1
        rw [hi1, u4h_edgeSegment_deleteVertex_last, u4h_edgeSegment_deleteVertex P j hi,
          deleteVertex_last, hi2, u4h_deletionIndex_neg_two (by omega) j]
        ext x
        constructor
        · rintro ⟨hxk, hxD⟩
          rcases u4h_edge_inter_diag hP hstrict hj2_1 hj2_2 ⟨hxk, hxD⟩ with h | h
          · exact h
          · exfalso
            have := u4h_eq_add_one_of_mem hP hj2_2 (h ▸ hxk)
            exact h3n1 (by linear_combination -this)
        · intro hx
          have hx' : x = P (j - 1) := hx
          rw [hx']
          refine ⟨?_, left_mem_segment ℝ _ _⟩
          have := u4h_end_mem_edgeSegment P (j - 2)
          rwa [show j - 2 + 1 = j - 1 by ring] at this
      · rw [u4h_edgeSegment_deleteVertex P j hi, u4h_edgeSegment_deleteVertex P j hi1,
          deletionIndex_next j hi, deleteVertex_apply, deletionIndex_next j hi]
        exact hP.consecutive _

end U4I_block

section U4J_block

/-! `Triangle` vertex facts and sub-face intersections (U4 helpers). -/

theorem u4h_tri_pos (T : Triangle) (k : Fin 3) :
    0 < det (T.v (k + 1) - T.v k) (T.v (k + 2) - T.v k) := by
  have h := T.pos
  fin_cases k
  · simpa using h
  · show 0 < det (T.v 2 - T.v 1) (T.v 0 - T.v 1)
    rw [u4h_det_rot1]; exact h
  · show 0 < det (T.v 0 - T.v 2) (T.v 1 - T.v 2)
    rw [u4h_det_rot2]; exact h

theorem u4h_tri_range_rot (T : Triangle) (k : Fin 3) :
    Set.range T.v = {T.v k, T.v (k + 1), T.v (k + 2)} := by
  rw [u4h_range_fin3]
  fin_cases k
  · rfl
  · show ({T.v 0, T.v 1, T.v 2} : Set Plane) = {T.v 1, T.v 2, T.v 0}
    exact u4h_hull3_rot_set _ _ _
  · show ({T.v 0, T.v 1, T.v 2} : Set Plane) = {T.v 2, T.v 0, T.v 1}
    rw [u4h_hull3_rot_set, u4h_hull3_rot_set]
where
  u4h_hull3_rot_set (a b c : Plane) : ({a, b, c} : Set Plane) = {b, c, a} := by
    rw [Set.insert_comm, Set.pair_comm]

theorem u4h_tri_carrier_rot (T : Triangle) (k : Fin 3) :
    T.carrier = convexHull ℝ {T.v k, T.v (k + 1), T.v (k + 2)} := by
  rw [Triangle.carrier, u4h_tri_range_rot T k]

theorem u4h_tri_edgeSeg_subset (T : Triangle) (k : Fin 3) : T.edgeSeg k ⊆ T.carrier := by
  rw [u4h_tri_carrier_rot T k]
  exact u4h_segment_subset_hull3 _ _ _

theorem u4h_tri_ne (T : Triangle) (k : Fin 3) : T.v k ≠ T.v (k + 1) := by
  intro h
  have := u4h_tri_pos T k
  rw [← h, sub_self] at this
  simp [det] at this

theorem u4h_tri_ne' (T : Triangle) (k : Fin 3) : T.v k ≠ T.v (k + 2) := by
  intro h
  have := u4h_tri_pos T k
  rw [← h, sub_self] at this
  simp [det] at this

theorem u4h_tri_injective (T : Triangle) : Function.Injective T.v := by
  intro i j hij
  by_contra hne
  fin_cases i <;> fin_cases j
  all_goals first
    | exact hne rfl
    | exact u4h_tri_ne T _ hij
    | exact u4h_tri_ne' T _ hij

/-- The apex `T.v (k+2)` is not on the line of the edge `k`. -/
theorem u4h_tri_apex_not_mem_edge (T : Triangle) (k : Fin 3) :
    T.v (k + 2) ∉ segment ℝ (T.v k) (T.v (k + 1)) := by
  intro h
  have := u4h_det_segment_zero h
  have hp := u4h_tri_pos T k
  rw [this] at hp
  exact lt_irrefl _ hp

/-- Sub-face lemma: for `W` a set of vertices of `T`, `hull W ∩ edge k = hull (W ∩ {ends of edge k})`. -/
theorem u4h_hull_inter_edge (T : Triangle) (k : Fin 3) {W : Set Plane}
    (hW : W ⊆ {T.v k, T.v (k + 1), T.v (k + 2)}) :
    convexHull ℝ W ∩ segment ℝ (T.v k) (T.v (k + 1)) =
      convexHull ℝ (W ∩ {T.v k, T.v (k + 1)}) := by
  set a := T.v k
  set b := T.v (k + 1)
  set c := T.v (k + 2)
  have hcab : c ∉ segment ℝ a b := u4h_tri_apex_not_mem_edge T k
  by_cases hc : c ∈ W
  · -- `W = insert c W0` with `W0 ⊆ {a, b}`
    set W0 := W ∩ {a, b} with hW0
    have hWeq : W = insert c W0 := by
      ext x
      constructor
      · intro hx
        rcases hW hx with h | h | h
        · exact Or.inr ⟨hx, Or.inl h⟩
        · exact Or.inr ⟨hx, Or.inr h⟩
        · exact Or.inl h
      · rintro (h | h)
        · rw [h]; exact hc
        · exact h.1
    apply Set.Subset.antisymm
    · rintro x ⟨hxW, hxe⟩
      by_cases hW0e : W0.Nonempty
      · rw [hWeq, convexHull_insert hW0e, mem_convexJoin] at hxW
        obtain ⟨c', hc', y, hy, hxy⟩ := hxW
        rw [Set.mem_singleton_iff] at hc'
        subst hc'
        rw [u4h_mem_segment_iff_lin] at hxy
        obtain ⟨l, hl0, hl1, rfl⟩ := hxy
        -- the edge determinant vanishes at `x` and at `y`, so `x = y` unless `l = 1`
        have hyW : y ∈ segment ℝ a b := by
          have : convexHull ℝ W0 ⊆ segment ℝ a b := by
            rw [← convexHull_pair]
            exact convexHull_mono Set.inter_subset_right
          exact this hy
        have hgx := u4h_det_segment_zero hxe
        have hgy := u4h_det_segment_zero hyW
        have hgc : det (b - a) (c - a) ≠ 0 := (u4h_tri_pos T k).ne'
        rw [u4h_det_lin] at hgx
        have hl : l = 1 := by
          have e : det (b - a) (y - c) = det (b - a) (y - a) - det (b - a) (c - a) := by
            simp only [det, Prod.fst_sub, Prod.snd_sub]; ring
          rw [e, hgy] at hgx
          have h1 : (1 - l) * det (b - a) (c - a) = 0 := by linear_combination hgx
          rcases mul_eq_zero.mp h1 with h | h
          · linarith
          · exact absurd h hgc
        rw [hl, one_smul, add_sub_cancel]
        exact hy
      · rw [Set.not_nonempty_iff_eq_empty] at hW0e
        have hW1 : convexHull ℝ W = {c} := by
          rw [hWeq, hW0e]
          have : (insert c (∅ : Set Plane)) = {c} := by ext; simp
          rw [this]
          exact convexHull_singleton (𝕜 := ℝ) c
        rw [hW1, Set.mem_singleton_iff] at hxW
        rw [hxW] at hxe
        exact absurd hxe hcab
    · intro x hx
      refine ⟨convexHull_mono Set.inter_subset_left hx, ?_⟩
      rw [← convexHull_pair]
      exact convexHull_mono Set.inter_subset_right hx
  · have hWeq : W = W ∩ {a, b} := by
      ext x
      constructor
      · intro hx
        rcases hW hx with h | h | h
        · exact ⟨hx, Or.inl h⟩
        · exact ⟨hx, Or.inr h⟩
        · exact absurd (h ▸ hx) hc
      · exact fun h => h.1
    rw [← hWeq]
    apply Set.Subset.antisymm
    · exact Set.inter_subset_left
    · intro x hx
      refine ⟨hx, ?_⟩
      rw [← convexHull_pair]
      exact convexHull_mono (by rw [hWeq]; exact Set.inter_subset_right) hx

/-- A vertex of `T` lying in the hull of a set of vertices belongs to that set. -/
theorem u4h_vertex_mem_hull_iff (T : Triangle) {W : Set Plane} (hW : W ⊆ Set.range T.v)
    (j : Fin 3) : T.v j ∈ convexHull ℝ W ↔ T.v j ∈ W := by
  refine ⟨fun h => ?_, fun h => subset_convexHull ℝ W h⟩
  by_contra hj
  -- `W ⊆ {T.v (j+1), T.v (j+2)}`, so `T.v j` would lie on the opposite edge
  have hW' : W ⊆ {T.v (j + 1), T.v (j + 1 + 1)} := by
    intro x hx
    rw [u4h_tri_range_rot T (j + 1)] at hW
    rcases hW hx with h1 | h1 | h1
    · exact Or.inl h1
    · exact Or.inr h1
    · exfalso
      rw [show j + 1 + 2 = j by fin_cases j <;> rfl] at h1
      exact hj (h1 ▸ hx)
  have hsub : convexHull ℝ W ⊆ segment ℝ (T.v (j + 1)) (T.v (j + 1 + 1)) := by
    rw [← convexHull_pair]; exact convexHull_mono hW'
  have := u4h_tri_apex_not_mem_edge T (j + 1)
  rw [show j + 1 + 2 = j by fin_cases j <;> rfl] at this
  exact this (hsub h)

end U4J_block

section U4K_block

/-! Gluing two triangulations along a common face-edge (U4 helpers). -/

theorem u4h_carrier_subset {X : Set Plane} (K : Triangulation X) {T : Triangle}
    (hT : T ∈ K.faces) : T.carrier ⊆ X := by
  rw [← K.cover]
  exact Set.subset_biUnion_of_mem (u := fun T : Triangle => T.carrier) hT

/-- The endpoints of a nondegenerate segment are determined by the segment. -/
theorem u4h_segment_endpoints {a b c d : Plane} (hab : a ≠ b)
    (h : segment ℝ a b = segment ℝ c d) : ({a, b} : Set Plane) = {c, d} := by
  have hc : c ∈ segment ℝ a b := h ▸ left_mem_segment ℝ c d
  have hd : d ∈ segment ℝ a b := h ▸ right_mem_segment ℝ c d
  have ha : a ∈ segment ℝ c d := h ▸ left_mem_segment ℝ a b
  have hb : b ∈ segment ℝ c d := h ▸ right_mem_segment ℝ a b
  obtain ⟨u, hu0, hu1, rfl⟩ := (u4h_mem_segment_iff_lin a b c).mp hc
  obtain ⟨w, hw0, hw1, rfl⟩ := (u4h_mem_segment_iff_lin a b d).mp hd
  obtain ⟨s, hs0, hs1, has⟩ := (u4h_mem_segment_iff_lin _ _ a).mp ha
  obtain ⟨t, ht0, ht1, hbt⟩ := (u4h_mem_segment_iff_lin _ _ b).mp hb
  have hba : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  -- `a = a + (u + s (w - u)) • (b - a)` forces `u + s (w - u) = 0`
  have e1 : (u + s * (w - u)) • (b - a) = 0 := by
    have : a + (u + s * (w - u)) • (b - a) = a := by
      conv_rhs => rw [has]
      module
    exact add_eq_left.mp this
  have e2 : (u + t * (w - u)) • (b - a) = (1 : ℝ) • (b - a) := by
    have : a + (u + t * (w - u)) • (b - a) = a + (1 : ℝ) • (b - a) := by
      rw [one_smul, add_sub_cancel]
      conv_rhs => rw [hbt]
      module
    exact add_left_cancel this
  have k1 : u + s * (w - u) = 0 := by
    rcases smul_eq_zero.mp e1 with h | h
    · exact h
    · exact absurd h hba
  have k2 : u + t * (w - u) = 1 := smul_left_injective ℝ hba e2
  -- from `k1`, `k2`: `u = 0 ∧ w = 1` or `u = 1 ∧ w = 0`
  have hcases : (u = 0 ∧ w = 1) ∨ (u = 1 ∧ w = 0) := by
    by_cases hu : u = 0
    · subst hu
      left
      refine ⟨rfl, ?_⟩
      have k2' : t * w = 1 := by linarith
      nlinarith [mul_le_of_le_one_left hw0 ht1]
    · right
      have hwu : w < u := by
        by_contra hc
        have hc' : u ≤ w := not_lt.mp hc
        have : 0 ≤ s * (w - u) := mul_nonneg hs0 (by linarith)
        have : u ≤ 0 := by linarith
        exact hu (le_antisymm this hu0)
      have hu1' : u = 1 := by
        have : t * (w - u) ≤ 0 := by nlinarith
        linarith
      subst hu1'
      refine ⟨rfl, ?_⟩
      have h1 : s * (1 - w) = 1 := by linarith
      nlinarith [mul_le_of_le_one_left (by linarith : (0 : ℝ) ≤ 1 - w) hs1]
  rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · simp
  · simp only [one_smul, add_sub_cancel, zero_smul, add_zero]
    exact Set.pair_comm a b

/-- Intersection of hulls of subsets of a two-point set `{e1, e2}` lying among the vertices of a
triangle `F` (edge `k`). -/
theorem u4h_hull_inter_pair (F : Triangle) (k : Fin 3) {A A' : Set Plane}
    (hA : A ⊆ {F.v k, F.v (k + 1)}) (hA' : A' ⊆ {F.v k, F.v (k + 1)}) :
    convexHull ℝ A ∩ convexHull ℝ A' = convexHull ℝ (A ∩ A') := by
  have hpair3 : ({F.v k, F.v (k + 1)} : Set Plane) ⊆ {F.v k, F.v (k + 1), F.v (k + 2)} := by
    rintro x (h | h)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  have hAr : A ⊆ Set.range F.v := hA.trans (by rw [u4h_tri_range_rot F k]; exact hpair3)
  have hA3 : A ⊆ {F.v k, F.v (k + 1), F.v (k + 2)} := hA.trans hpair3
  have hne : F.v k ≠ F.v (k + 1) := u4h_tri_ne F k
  -- describe `A'` by which endpoints it contains
  have key : ∀ x, x ∈ A' → x = F.v k ∨ x = F.v (k + 1) := fun x hx => hA' hx
  by_cases h1 : F.v k ∈ A' <;> by_cases h2 : F.v (k + 1) ∈ A'
  · -- `A' = {F.v k, F.v (k+1)}`
    have hA'eq : A' = {F.v k, F.v (k + 1)} := by
      apply Set.Subset.antisymm hA'
      rintro x (rfl | rfl)
      · exact h1
      · exact h2
    rw [hA'eq, convexHull_pair, u4h_hull_inter_edge F k hA3]
  · have hA'eq : A' = {F.v k} := by
      apply Set.Subset.antisymm
      · intro x hx
        rcases key x hx with h | h
        · exact h
        · exact absurd (h ▸ hx) h2
      · rintro x rfl; exact h1
    rw [hA'eq, convexHull_singleton]
    ext x
    constructor
    · rintro ⟨hx, hx'⟩
      rw [Set.mem_singleton_iff] at hx'
      subst hx'
      have := (u4h_vertex_mem_hull_iff F hAr k).mp hx
      exact subset_convexHull ℝ _ ⟨this, rfl⟩
    · intro hx
      have := convexHull_mono (Set.inter_subset_right (s := A)) hx
      rw [convexHull_singleton] at this
      exact ⟨convexHull_mono Set.inter_subset_left hx, this⟩
  · have hA'eq : A' = {F.v (k + 1)} := by
      apply Set.Subset.antisymm
      · intro x hx
        rcases key x hx with h | h
        · exact absurd (h ▸ hx) h1
        · exact h
      · rintro x rfl; exact h2
    rw [hA'eq, convexHull_singleton]
    ext x
    constructor
    · rintro ⟨hx, hx'⟩
      rw [Set.mem_singleton_iff] at hx'
      subst hx'
      have := (u4h_vertex_mem_hull_iff F hAr (k + 1)).mp hx
      exact subset_convexHull ℝ _ ⟨this, rfl⟩
    · intro hx
      have := convexHull_mono (Set.inter_subset_right (s := A)) hx
      rw [convexHull_singleton] at this
      exact ⟨convexHull_mono Set.inter_subset_left hx, this⟩
  · have hA'eq : A' = ∅ := by
      apply Set.eq_empty_of_forall_notMem
      intro x hx
      rcases key x hx with h | h
      · exact h1 (h ▸ hx)
      · exact h2 (h ▸ hx)
    rw [hA'eq, Set.inter_empty, convexHull_empty, Set.inter_empty]

/-- Sub-lemma A: a face `T` of `K` meets the edge `k` of another face `F` of `K` in the hull of
the vertices of `T` among that edge's endpoints. -/
theorem u4h_face_inter_edge {X : Set Plane} (K : Triangulation X) {T F : Triangle}
    (hT : T ∈ K.faces) (hF : F ∈ K.faces) (k : Fin 3) :
    T.carrier ∩ F.edgeSeg k = convexHull ℝ (Set.range T.v ∩ {F.v k, F.v (k + 1)}) := by
  have hW : Set.range T.v ∩ Set.range F.v ⊆ {F.v k, F.v (k + 1), F.v (k + 2)} := by
    rw [← u4h_tri_range_rot F k]; exact Set.inter_subset_right
  have e1 : T.carrier ∩ F.edgeSeg k =
      convexHull ℝ (Set.range T.v ∩ Set.range F.v) ∩ F.edgeSeg k := by
    apply Set.Subset.antisymm
    · rintro x ⟨hx, hxe⟩
      refine ⟨?_, hxe⟩
      rw [← K.inter T hT F hF]
      exact ⟨hx, u4h_tri_edgeSeg_subset F k hxe⟩
    · rintro x ⟨hx, hxe⟩
      exact ⟨convexHull_mono Set.inter_subset_left hx, hxe⟩
  rw [e1, Triangle.edgeSeg, u4h_hull_inter_edge F k hW]
  congr 1
  ext x
  constructor
  · rintro ⟨⟨h1, -⟩, h2⟩; exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    refine ⟨⟨h1, ?_⟩, h2⟩
    rw [u4h_tri_range_rot F k]
    rcases h2 with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)

end U4K_block

section U4L_block

/-! The glued triangulation and the region-data structure (U4 helpers). -/

theorem u4h_glue_inter {U1 U2 : Set Plane} (K1 : Triangulation U1) (K2 : Triangulation U2)
    {F1 : Triangle} (hF1 : F1 ∈ K1.faces) (k1 : Fin 3)
    {F2 : Triangle} (hF2 : F2 ∈ K2.faces) (k2 : Fin 3)
    (hedge : F2.edgeSeg k2 = F1.edgeSeg k1) (hinter : U1 ∩ U2 = F1.edgeSeg k1)
    {T T' : Triangle} (hT : T ∈ K1.faces) (hT' : T' ∈ K2.faces) :
    T.carrier ∩ T'.carrier = convexHull ℝ (Set.range T.v ∩ Set.range T'.v) := by
  have hends : ({F2.v k2, F2.v (k2 + 1)} : Set Plane) = {F1.v k1, F1.v (k1 + 1)} :=
    u4h_segment_endpoints (u4h_tri_ne F2 k2) hedge
  have hTe := u4h_face_inter_edge K1 hT hF1 k1
  have hT'e : T'.carrier ∩ F1.edgeSeg k1 =
      convexHull ℝ (Set.range T'.v ∩ {F1.v k1, F1.v (k1 + 1)}) := by
    rw [← hedge, u4h_face_inter_edge K2 hT' hF2 k2, hends]
  have hsub : T.carrier ∩ T'.carrier ⊆ F1.edgeSeg k1 := by
    rw [← hinter]
    exact Set.inter_subset_inter (u4h_carrier_subset K1 hT) (u4h_carrier_subset K2 hT')
  have e1 : T.carrier ∩ T'.carrier =
      (T.carrier ∩ F1.edgeSeg k1) ∩ (T'.carrier ∩ F1.edgeSeg k1) := by
    ext x
    constructor
    · intro hx
      exact ⟨⟨hx.1, hsub hx⟩, ⟨hx.2, hsub hx⟩⟩
    · rintro ⟨⟨h1, -⟩, ⟨h2, -⟩⟩
      exact ⟨h1, h2⟩
  rw [e1, hTe, hT'e, u4h_hull_inter_pair F1 k1 Set.inter_subset_right Set.inter_subset_right]
  congr 1
  ext p
  constructor
  · rintro ⟨⟨h1, -⟩, ⟨h2, -⟩⟩
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    have hpe : p ∈ T.carrier ∩ F1.edgeSeg k1 := by
      obtain ⟨j, rfl⟩ := h1
      obtain ⟨j', hj'⟩ := h2
      refine ⟨subset_convexHull ℝ _ ⟨j, rfl⟩, hsub ⟨subset_convexHull ℝ _ ⟨j, rfl⟩, ?_⟩⟩
      rw [← hj']
      exact subset_convexHull ℝ _ ⟨j', rfl⟩
    rw [hTe] at hpe
    obtain ⟨j, rfl⟩ := h1
    have := (u4h_vertex_mem_hull_iff T Set.inter_subset_left j).mp hpe
    exact ⟨⟨⟨j, rfl⟩, this.2⟩, ⟨h2, this.2⟩⟩

/-- The glued triangulation of `U1 ∪ U2`. -/
def u4h_glueTri {U1 U2 : Set Plane} (K1 : Triangulation U1) (K2 : Triangulation U2)
    {F1 : Triangle} (hF1 : F1 ∈ K1.faces) (k1 : Fin 3)
    {F2 : Triangle} (hF2 : F2 ∈ K2.faces) (k2 : Fin 3)
    (hedge : F2.edgeSeg k2 = F1.edgeSeg k1) (hinter : U1 ∩ U2 = F1.edgeSeg k1) :
    Triangulation (U1 ∪ U2) where
  faces := K1.faces ∪ K2.faces
  finite := K1.finite.union K2.finite
  cover := by rw [Set.biUnion_union, K1.cover, K2.cover]
  inter := by
    intro T hT T' hT'
    rcases hT with hT | hT <;> rcases hT' with hT' | hT'
    · exact K1.inter T hT T' hT'
    · exact u4h_glue_inter K1 K2 hF1 k1 hF2 k2 hedge hinter hT hT'
    · rw [Set.inter_comm, Set.inter_comm (Set.range T.v)]
      exact u4h_glue_inter K1 K2 hF1 k1 hF2 k2 hedge hinter hT' hT
    · exact K2.inter T hT T' hT'

theorem u4h_glueTri_faces {U1 U2 : Set Plane} (K1 : Triangulation U1) (K2 : Triangulation U2)
    {F1 : Triangle} (hF1 : F1 ∈ K1.faces) (k1 : Fin 3)
    {F2 : Triangle} (hF2 : F2 ∈ K2.faces) (k2 : Fin 3)
    (hedge : F2.edgeSeg k2 = F1.edgeSeg k1) (hinter : U1 ∩ U2 = F1.edgeSeg k1) :
    (u4h_glueTri K1 K2 hF1 k1 hF2 k2 hedge hinter).faces = K1.faces ∪ K2.faces := rfl

/-! ### Basic facts about triangulated sets -/

theorem u4h_tri_isCompact (T : Triangle) : IsCompact T.carrier := by
  rw [u4h_carrier_eq]; exact u4h_hull3_isCompact _ _ _

theorem u4h_triangulation_isCompact {X : Set Plane} (K : Triangulation X) : IsCompact X := by
  rw [← K.cover]
  exact K.finite.isCompact_biUnion fun T _ => u4h_tri_isCompact T

theorem u4h_triangulation_isClosed {X : Set Plane} (K : Triangulation X) : IsClosed X :=
  (u4h_triangulation_isCompact K).isClosed

theorem u4h_tri_interior_nonempty (T : Triangle) : (interior T.carrier).Nonempty := by
  rw [u4h_carrier_eq, u4h_interior_hull3 T.pos]
  refine ⟨(1/3 : ℝ) • T.v 0 + (1/3 : ℝ) • T.v 1 + (1/3 : ℝ) • T.v 2, ?_, ?_, ?_⟩
  all_goals
    simp only [det, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add,
      Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    have := T.pos
    simp only [det, Prod.fst_sub, Prod.snd_sub] at this
    nlinarith

/-- A point of a triangulated set is a limit of interior points. -/
theorem u4h_triangulation_subset_closure_interior {X : Set Plane} (K : Triangulation X) :
    X ⊆ closure (interior X) := by
  intro x hx
  rw [← K.cover] at hx
  obtain ⟨T, hT, hxT⟩ := Set.mem_iUnion₂.mp hx
  have h1 : x ∈ closure (interior T.carrier) := by
    have hconv : Convex ℝ T.carrier := convex_convexHull ℝ _
    rw [hconv.closure_interior_eq_closure_of_nonempty_interior (u4h_tri_interior_nonempty T)]
    exact subset_closure hxT
  exact closure_mono (interior_mono (u4h_carrier_subset K hT)) h1

theorem u4h_triangulation_closure_interior {X : Set Plane} (K : Triangulation X) :
    closure (interior X) = X :=
  Set.Subset.antisymm (closure_minimal interior_subset (u4h_triangulation_isClosed K))
    (u4h_triangulation_subset_closure_interior K)

/-- Region data for an embedded polygon: the invariants carried through the ear/split
induction (U4). -/
structure u4h_Region {n : ℕ} (P : LabelledTuple n) where
  U : Set Plane
  K : Triangulation U
  frontier_eq : frontier U = embeddedPolygonImage P
  edge_face : ∀ i, ∃ T ∈ K.faces, ∃ k : Fin 3, T.edgeSeg k = edgeSegment P i
  edge_unique : ∀ i, ∀ T ∈ K.faces, ∀ T' ∈ K.faces,
    edgeSegment P i ⊆ T.carrier → edgeSegment P i ⊆ T'.carrier → T.carrier = T'.carrier
  hull : U ⊆ convexHull ℝ (Set.range P)
  int_conn : IsPreconnected (interior U)
  σ : ℝ
  σ_pm : σ = 1 ∨ σ = -1
  side : ∀ i, ∀ T ∈ K.faces, ∀ k : Fin 3, T.edgeSeg k = edgeSegment P i →
    0 < σ * det (P (i + 1) - P i) (T.v (k + 2) - P i)
  count : (K.faces.image Triangle.carrier).ncard + 2 ≤ n

end U4L_block

section U4M_block

/-! The local structure of a region at the lexicographically least vertex (U4 helpers):
outside the cone of the two incident edges, nearby points are not in the region. -/

/-- Strict lexicographic order on the plane. -/
def u4h_Lex (x y : Plane) : Prop := x.1 < y.1 ∨ (x.1 = y.1 ∧ x.2 < y.2)

/-- The closed lexicographic half-plane above `p`. -/
def u4h_LexQ (p : Plane) : Set Plane := {x | p.1 < x.1 ∨ (p.1 = x.1 ∧ p.2 ≤ x.2)}

theorem u4h_convex_LexQ (p : Plane) : Convex ℝ (u4h_LexQ p) := by
  intro x hx y hy s t hs ht hst
  simp only [u4h_LexQ, Set.mem_ofPred_eq, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
    Prod.smul_snd, smul_eq_mul] at hx hy ⊢
  have hp1 : s * p.1 + t * p.1 = p.1 := by rw [← add_mul, hst, one_mul]
  have hp2 : s * p.2 + t * p.2 = p.2 := by rw [← add_mul, hst, one_mul]
  have hx1 : s * p.1 ≤ s * x.1 :=
    mul_le_mul_of_nonneg_left (by rcases hx with h | ⟨h, -⟩ <;> linarith) hs
  have hy1 : t * p.1 ≤ t * y.1 :=
    mul_le_mul_of_nonneg_left (by rcases hy with h | ⟨h, -⟩ <;> linarith) ht
  by_cases hlt : p.1 < s * x.1 + t * y.1
  · exact Or.inl hlt
  · right
    have heq : p.1 = s * x.1 + t * y.1 := le_antisymm (by linarith) (not_lt.mp hlt)
    refine ⟨heq, ?_⟩
    have hx1' : s * p.1 = s * x.1 := by linarith
    have hy1' : t * p.1 = t * y.1 := by linarith
    have hsx : s * p.2 ≤ s * x.2 := by
      rcases hs.lt_or_eq with hs' | hs'
      · have : p.1 = x.1 := mul_left_cancel₀ hs'.ne' hx1'
        rcases hx with h | ⟨-, h⟩
        · linarith
        · exact mul_le_mul_of_nonneg_left h hs
      · rw [← hs']; simp
    have hty : t * p.2 ≤ t * y.2 := by
      rcases ht.lt_or_eq with ht' | ht'
      · have : p.1 = y.1 := mul_left_cancel₀ ht'.ne' hy1'
        rcases hy with h | ⟨-, h⟩
        · linarith
        · exact mul_le_mul_of_nonneg_left h ht
      · rw [← ht']; simp
    linarith

theorem u4h_det_neg_left (u w : Plane) : det (-u) w = -det u w := by
  simp only [det, Prod.fst_neg, Prod.snd_neg]; ring

theorem u4h_hull_subset_LexQ {P : LabelledTuple n} {v : ZMod n}
    (hv : ∀ k, k ≠ v → u4h_Lex (P v) (P k)) :
    convexHull ℝ (Set.range P) ⊆ u4h_LexQ (P v) := by
  apply convexHull_min _ (u4h_convex_LexQ _)
  rintro x ⟨k, rfl⟩
  by_cases hk : k = v
  · subst hk; right; exact ⟨rfl, le_rfl⟩
  · rcases hv k hk with h | ⟨h1, h2⟩
    · left; exact h
    · right; exact ⟨h1, h2.le⟩

/-- Edge vectors at the lexmin vertex are in the open lexicographic cone. -/
theorem u4h_edge_lexQ0 {P : LabelledTuple n} {v : ZMod n}
    (hv : ∀ k, k ≠ v → u4h_Lex (P v) (P k)) {k : ZMod n} (hk : k ≠ v) :
    0 < (P k - P v).1 ∨ ((P k - P v).1 = 0 ∧ 0 < (P k - P v).2) := by
  rcases hv k hk with h | ⟨h1, h2⟩
  · left; simp only [Prod.fst_sub]; linarith
  · right; simp only [Prod.fst_sub, Prod.snd_sub]; constructor <;> linarith

/-- Among the two directions `(-1, 1)`, `(-1, -1)` one lies strictly outside the cone spanned by
two vectors `u, u'` of the open lexicographic cone with `det u u' > 0`. -/
theorem u4h_exists_left_dir {u u' : Plane}
    (hu : 0 < u.1 ∨ (u.1 = 0 ∧ 0 < u.2)) (hu' : 0 < u'.1 ∨ (u'.1 = 0 ∧ 0 < u'.2))
    (hdet : 0 < det u u') :
    ∃ w : Plane, w.1 = -1 ∧ ‖w‖ = 1 ∧ (det u w < 0 ∨ 0 < det u' w) := by
  have hn1 : ‖((-1 : ℝ), (1 : ℝ))‖ = 1 := by simp [Prod.norm_def]
  have hn2 : ‖((-1 : ℝ), (-1 : ℝ))‖ = 1 := by simp [Prod.norm_def]
  by_cases h1 : det u (-1, 1) < 0 ∨ 0 < det u' (-1, 1)
  · exact ⟨(-1, 1), rfl, hn1, h1⟩
  by_cases h2 : det u (-1, -1) < 0 ∨ 0 < det u' (-1, -1)
  · exact ⟨(-1, -1), rfl, hn2, h2⟩
  exfalso
  simp only [not_or, not_lt, det] at h1 h2
  simp only [det] at hdet
  rcases hu with hu | ⟨hu1, hu2⟩ <;> rcases hu' with hu' | ⟨hu'1, hu'2⟩ <;> nlinarith

/-- **Local lexmin lemma.** Near the lexicographically least vertex `P v`, every point strictly
outside the closed cone of the two incident edge vectors `u, u'` (`det u u' > 0`) is outside
the region `U`. -/
theorem u4h_local_lexmin [NeZero n] (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Embedded P)
    {U : Set Plane} (hU : IsClosed U) (hfr : frontier U = embeddedPolygonImage P)
    (hhull : U ⊆ convexHull ℝ (Set.range P)) {v : ZMod n}
    (hv : ∀ k, k ≠ v → u4h_Lex (P v) (P k)) {u u' : Plane}
    (hu : u = P (v - 1) - P v ∨ u = P (v + 1) - P v)
    (hu' : u' = P (v - 1) - P v ∨ u' = P (v + 1) - P v) (hdet : 0 < det u u') :
    ∃ ρ > 0, ∀ z, dist z (P v) < ρ → (det u (z - P v) < 0 ∨ 0 < det u' (z - P v)) → z ∉ U := by
  -- the other edges stay away from `P v`
  set C' : Set Plane := ⋃ k ∈ {k : ZMod n | k ≠ v - 1 ∧ k ≠ v}, edgeSegment P k with hC'
  have hC'closed : IsClosed C' := by
    refine (Set.toFinite _).isClosed_biUnion fun k _ => ?_
    rw [u4h_edgeSegment_eq_segment]; exact u4h_isClosed_segment _ _
  have hvC' : P v ∉ C' := by
    intro h
    obtain ⟨k, ⟨hk1, hk2⟩, hk⟩ := Set.mem_iUnion₂.mp h
    rcases u4h_incident_of_vertex_mem hP hk with h | h
    · exact hk2 h.symm
    · exact hk1 (by rw [h, add_sub_cancel_right])
  obtain ⟨ρ, hρ, hball⟩ := Metric.mem_nhds_iff.mp (hC'closed.isOpen_compl.mem_nhds hvC')
  refine ⟨ρ, hρ, fun z hz hzS hzU => ?_⟩
  -- the two half-planes and the set `S`
  set A : Set Plane := {y | det u (y - P v) < 0} ∩ Metric.ball (P v) ρ with hA
  set B : Set Plane := {y | 0 < det u' (y - P v)} ∩ Metric.ball (P v) ρ with hB
  have hAeq : {y : Plane | det u (y - P v) < 0} = {y | 0 < det (-u) (y - P v)} := by
    ext y
    simp only [Set.mem_ofPred_eq, u4h_det_neg_left]
    exact ⟨fun h => by linarith, fun h => by linarith⟩
  have hAconv : Convex ℝ A := by
    rw [hA, hAeq]
    exact (u4h_convex_det_pos _ _).inter (convex_ball _ _)
  have hBconv : Convex ℝ B := (u4h_convex_det_pos _ _).inter (convex_ball _ _)
  -- a common point of `A` and `B`
  have huu' : u + u' ≠ 0 := by
    intro h
    have : u' = -u := eq_neg_of_add_eq_zero_right h
    have h0 : det u (-u) = 0 := by simp only [det, Prod.fst_neg, Prod.snd_neg]; ring
    rw [this, h0] at hdet
    exact lt_irrefl _ hdet
  have hnorm : 0 < ‖u + u'‖ := norm_pos_iff.mpr huu'
  set z0 : Plane := P v - (ρ / (2 * ‖u + u'‖)) • (u + u') with hz0
  have hz0ball : z0 ∈ Metric.ball (P v) ρ := by
    rw [Metric.mem_ball, dist_eq_norm, hz0, sub_sub_cancel_left, norm_neg, norm_smul,
      Real.norm_eq_abs, abs_of_pos (by positivity), div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith
  have hz0 : z0 ∈ A ∩ B := by
    have hpos : 0 < ρ / (2 * ‖u + u'‖) := by positivity
    refine ⟨⟨?_, hz0ball⟩, ⟨?_, hz0ball⟩⟩
    · show det u (z0 - P v) < 0
      rw [hz0, sub_sub_cancel_left, ← neg_smul, u4h_det_smul_right, u4h_det_add_right,
        u4h_det_self, zero_add]
      nlinarith
    · show 0 < det u' (z0 - P v)
      rw [hz0, sub_sub_cancel_left, ← neg_smul, u4h_det_smul_right, u4h_det_add_right,
        u4h_det_self, add_zero, u4h_det_swap' u' u]
      nlinarith
  have hSconn : IsPreconnected (A ∪ B) :=
    IsPreconnected.union z0 hz0.1 hz0.2 hAconv.isPreconnected hBconv.isPreconnected
  -- `S` avoids the frontier
  have hSfr : ∀ y ∈ A ∪ B, y ∉ frontier U := by
    intro y hy hyf
    have hyball : y ∈ Metric.ball (P v) ρ := by rcases hy with h | h <;> exact h.2
    rw [hfr] at hyf
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hyf
    have hnot : ∀ w : Plane, (w = P (v - 1) - P v ∨ w = P (v + 1) - P v) → ∀ t : ℝ, 0 ≤ t →
        y = P v + t • w → False := by
      intro w hw t ht hy'
      have e1 : det u (y - P v) = t * det u w := by rw [hy', add_sub_cancel_left, u4h_det_smul_right]
      have e2 : det u' (y - P v) = t * det u' w := by
        rw [hy', add_sub_cancel_left, u4h_det_smul_right]
      have hw' : w = u ∨ w = u' := by
        rcases hw with hw | hw <;> rcases hu with hu | hu <;> rcases hu' with hu' | hu'
        all_goals first
          | exact Or.inl (hw.trans hu.symm)
          | exact Or.inr (hw.trans hu'.symm)
          | (exfalso
             have huu : u = u' := hu.trans hu'.symm
             rw [huu, u4h_det_self] at hdet
             exact lt_irrefl _ hdet)
      rcases hy with ⟨hyA, -⟩ | ⟨hyB, -⟩
      · have : det u (y - P v) < 0 := hyA
        rw [e1] at this
        rcases hw' with hw' | hw'
        · rw [hw', u4h_det_self] at this; simp at this
        · rw [hw'] at this; nlinarith
      · have : 0 < det u' (y - P v) := hyB
        rw [e2] at this
        rcases hw' with hw' | hw'
        · rw [hw', u4h_det_swap' u' u] at this; nlinarith
        · rw [hw', u4h_det_self] at this; simp at this
    by_cases hk1 : k = v - 1
    · subst hk1
      rw [u4h_edgeSegment_prev, segment_symm, u4h_mem_segment_iff_lin] at hk
      obtain ⟨t, ht0, -, hyt⟩ := hk
      exact hnot _ (Or.inl rfl) t ht0 hyt
    by_cases hk2 : k = v
    · subst hk2
      rw [u4h_edgeSegment_eq_segment, u4h_mem_segment_iff_lin] at hk
      obtain ⟨t, ht0, -, hyt⟩ := hk
      exact hnot _ (Or.inr rfl) t ht0 hyt
    exact hball hyball (Set.mem_iUnion₂.mpr ⟨k, ⟨hk1, hk2⟩, hk⟩)
  have hSsub : A ∪ B ⊆ interior U ∪ Uᶜ := by
    intro y hy
    by_cases hyU : y ∈ U
    · left
      by_contra hyi
      exact hSfr y hy ⟨subset_closure hyU, hyi⟩
    · right; exact hyU
  -- a point of `S` outside the hull
  have hQ0 : ∀ w : Plane, (w = P (v - 1) - P v ∨ w = P (v + 1) - P v) →
      0 < w.1 ∨ (w.1 = 0 ∧ 0 < w.2) := by
    rintro w (rfl | rfl)
    · exact u4h_edge_lexQ0 hv (by
        intro h; exact u4h_one_ne_zero' (n := n) (by omega) (by linear_combination -h))
    · exact u4h_edge_lexQ0 hv (by
        intro h; exact u4h_one_ne_zero' (n := n) (by omega) (by linear_combination h))
  obtain ⟨w, hw1, hwn, hw⟩ := u4h_exists_left_dir (hQ0 u hu) (hQ0 u' hu') hdet
  set z1 : Plane := P v + (ρ / 2) • w with hz1
  have hz1ball : z1 ∈ Metric.ball (P v) ρ := by
    rw [Metric.mem_ball, dist_eq_norm, hz1, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_pos (by positivity), hwn, mul_one]
    linarith
  have hz1S : z1 ∈ A ∪ B := by
    rcases hw with hw | hw
    · left; refine ⟨?_, hz1ball⟩
      show det u (z1 - P v) < 0
      rw [hz1, add_sub_cancel_left, u4h_det_smul_right]; nlinarith
    · right; refine ⟨?_, hz1ball⟩
      show 0 < det u' (z1 - P v)
      rw [hz1, add_sub_cancel_left, u4h_det_smul_right]; nlinarith
  have hz1U : z1 ∉ U := by
    intro h
    have := u4h_hull_subset_LexQ hv (hhull h)
    simp only [u4h_LexQ, Set.mem_ofPred_eq, hz1, Prod.fst_add, Prod.smul_fst, smul_eq_mul, hw1]
      at this
    rcases this with h | ⟨h, -⟩ <;> linarith
  -- conclude
  have hzS' : z ∈ A ∪ B := by
    rcases hzS with h | h
    · exact Or.inl ⟨h, Metric.mem_ball.mpr hz⟩
    · exact Or.inr ⟨h, Metric.mem_ball.mpr hz⟩
  rcases IsPreconnected.subset_or_subset isOpen_interior hU.isOpen_compl
      (Set.disjoint_left.mpr fun y hy hy' => hy' (interior_subset hy)) hSsub hSconn with h | h
  · exact hz1U (interior_subset (h hz1S))
  · exact h hzS' hzU

end U4M_block

section U4N_block

/-! Corollaries of the local lexmin lemma (U4 helpers). -/

/-- An embedded polygon has a (strict) lexicographically least vertex. -/
theorem u4h_exists_lexmin [NeZero n] {P : LabelledTuple n} (hP : Embedded P) :
    ∃ v : ZMod n, ∀ k, k ≠ v → u4h_Lex (P v) (P k) := by
  obtain ⟨v, -, hv⟩ := Finset.exists_min_image Finset.univ
    (fun j : ZMod n => toLex ((P j).1, (P j).2)) Finset.univ_nonempty
  refine ⟨v, fun k hk => ?_⟩
  have h := hv k (Finset.mem_univ k)
  rw [Prod.Lex.le_iff] at h
  rcases h with h | ⟨h1, h2⟩
  · exact Or.inl h
  · right
    refine ⟨h1, lt_of_le_of_ne h2 fun h2' => hk ?_⟩
    exact u4h_vertex_injective hP (Prod.ext h1 h2').symm

/-- Two vectors of the open lexicographic cone with zero determinant are positive multiples. -/
theorem u4h_pos_multiple_of_det_zero {p q : Plane} (hp : 0 < p.1 ∨ (p.1 = 0 ∧ 0 < p.2))
    (hq : 0 < q.1 ∨ (q.1 = 0 ∧ 0 < q.2)) (h : det p q = 0) : ∃ l : ℝ, 0 < l ∧ q = l • p := by
  have hp0 : p ≠ 0 := by
    rintro rfl
    rcases hp with h | ⟨-, h⟩ <;> simp at h
  obtain ⟨l, hl⟩ : ∃ l : ℝ, q = l • p := ⟨_, scalar_of_det_zero hp0 h⟩
  refine ⟨l, ?_, hl⟩
  rw [hl] at hq
  simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at hq
  rcases hp with hp | ⟨hp1, hp2⟩ <;> rcases hq with hq | ⟨hq1, hq2⟩
  · exact pos_of_mul_pos_left hq hp.le
  · exfalso
    have hl0 : l = 0 := by
      rcases mul_eq_zero.mp hq1 with h | h
      · exact h
      · linarith
    rw [hl0] at hq2; simp at hq2
  · exfalso; rw [hp1] at hq; simp at hq
  · exact pos_of_mul_pos_left hq2 hp2.le

/-- At a vertex of an embedded polygon the two edge vectors are not parallel in the same
direction; at the lexmin vertex (both in the open lexicographic cone) this is `det ≠ 0`. -/
theorem u4h_lexmin_det_ne_zero [NeZero n] (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Embedded P)
    {v : ZMod n} (hv : ∀ k, k ≠ v → u4h_Lex (P v) (P k)) :
    det (P (v - 1) - P v) (P (v + 1) - P v) ≠ 0 := by
  intro h
  have h1 : (v - 1 : ZMod n) ≠ v := fun h => u4h_one_ne_zero' (n := n) (by omega)
    (by linear_combination -h)
  have h2 : (v + 1 : ZMod n) ≠ v := fun h => u4h_one_ne_zero' (n := n) (by omega)
    (by linear_combination h)
  obtain ⟨l, hl, hq⟩ := u4h_pos_multiple_of_det_zero (u4h_edge_lexQ0 hv h1) (u4h_edge_lexQ0 hv h2) h
  -- the point `P v + t • p` with `t = min 1 l` lies on both edges at `v`
  set p := P (v - 1) - P v with hp
  have hp0 : p ≠ 0 := sub_ne_zero.mpr (u4h_vertex_injective hP |>.ne h1)
  set t : ℝ := min 1 l with ht
  have ht0 : 0 < t := lt_min one_pos hl
  have hmem1 : P v + t • p ∈ edgeSegment P (v - 1) := by
    rw [u4h_edgeSegment_prev, segment_symm, u4h_mem_segment_iff_lin]
    exact ⟨t, ht0.le, min_le_left _ _, rfl⟩
  have hmem2 : P v + t • p ∈ edgeSegment P v := by
    rw [u4h_edgeSegment_eq_segment, u4h_mem_segment_iff_lin]
    refine ⟨t / l, div_nonneg ht0.le hl.le, (div_le_one hl).mpr (min_le_right _ _), ?_⟩
    rw [hq, smul_smul, div_mul_cancel₀ _ hl.ne']
  have hc := hP.consecutive (v - 1)
  rw [sub_add_cancel] at hc
  have : P v + t • p ∈ edgeSegment P (v - 1) ∩ edgeSegment P v := ⟨hmem1, hmem2⟩
  rw [hc] at this
  have h0 : t • p = 0 := add_eq_left.mp this
  rcases smul_eq_zero.mp h0 with h0 | h0
  · exact ht0.ne' h0
  · exact hp0 h0

/-- A strictly positive convex combination of the vertices of a positively oriented triple lies in
the interior of its hull. -/
theorem u4h_pos_comb_mem_interior {p0 p1 p2 : Plane} (hD : 0 < det (p1 - p0) (p2 - p0))
    {α β γ : ℝ} (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ) (hsum : α + β + γ = 1) :
    α • p0 + β • p1 + γ • p2 ∈ interior (convexHull ℝ {p0, p1, p2}) := by
  rw [u4h_interior_hull3 hD]
  have hα' : α = 1 - β - γ := by linarith
  subst hα'
  refine ⟨?_, ?_, ?_⟩
  · have e : det (p1 - p0) ((1 - β - γ) • p0 + β • p1 + γ • p2 - p0) = γ * det (p1 - p0) (p2 - p0) := by
      simp only [det, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
        Prod.smul_snd, smul_eq_mul]; ring
    rw [e]; exact mul_pos hγ hD
  · have e : det (p2 - p1) ((1 - β - γ) • p0 + β • p1 + γ • p2 - p1) =
        (1 - β - γ) * det (p1 - p0) (p2 - p0) := by
      simp only [det, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
        Prod.smul_snd, smul_eq_mul]; ring
    rw [e]; exact mul_pos hα hD
  · have e : det (p0 - p2) ((1 - β - γ) • p0 + β • p1 + γ • p2 - p2) = β * det (p1 - p0) (p2 - p0) := by
      simp only [det, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
        Prod.smul_snd, smul_eq_mul]; ring
    rw [e]; exact mul_pos hβ hD

/-- The two ends of a face-edge equal to `segment a b` (`a ≠ b`), in one of two orders. -/
theorem u4h_face_edge_ends (T : Triangle) (k : Fin 3) {a b : Plane}
    (h : T.edgeSeg k = segment ℝ a b) :
    (T.v k = a ∧ T.v (k + 1) = b) ∨ (T.v k = b ∧ T.v (k + 1) = a) := by
  have hends : ({T.v k, T.v (k + 1)} : Set Plane) = {a, b} :=
    u4h_segment_endpoints (u4h_tri_ne T k) h
  have h1 : T.v k ∈ ({a, b} : Set Plane) := hends ▸ Set.mem_insert _ _
  have h2 : T.v (k + 1) ∈ ({a, b} : Set Plane) := hends ▸ Set.mem_insert_of_mem _ rfl
  have hne := u4h_tri_ne T k
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · exact absurd (h1.trans h2.symm) hne
  · exact Or.inl ⟨h1, h2⟩
  · exact Or.inr ⟨h1, h2⟩
  · exact absurd (h1.trans h2.symm) hne

/-- Points of a face are in the region. -/
theorem u4h_Region.face_subset {P : LabelledTuple n} (R : u4h_Region P) {T : Triangle}
    (hT : T ∈ R.K.faces) : T.carrier ⊆ R.U := u4h_carrier_subset R.K hT

theorem u4h_Region.isClosed {P : LabelledTuple n} (R : u4h_Region P) : IsClosed R.U :=
  u4h_triangulation_isClosed R.K

end U4N_block

section U4O_block

/-! (LL1) the side of a region is the turn sign at the lexmin vertex; (LL2) rays leaving the
lexmin vertex outside the edge cone leave the region (U4 helpers). -/

/-- (LL1) -/
theorem u4h_region_lexmin_turn [NeZero n] (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Embedded P)
    (R : u4h_Region P) {v : ZMod n} (hv : ∀ k, k ≠ v → u4h_Lex (P v) (P k)) :
    0 < R.σ * det (P v - P (v - 1)) (P (v + 1) - P v) := by
  have hdet0 := u4h_lexmin_det_ne_zero hn hP hv
  obtain ⟨F, hF, k, hFk⟩ := R.edge_face (v - 1)
  have hside := R.side (v - 1) F hF k hFk
  rw [sub_add_cancel] at hside
  have e1 : det (P v - P (v - 1)) (F.v (k + 2) - P (v - 1)) =
      -det (P (v - 1) - P v) (F.v (k + 2) - P v) := by
    simp only [det, Prod.fst_sub, Prod.snd_sub]; ring
  rw [e1] at hside
  have egoal : det (P v - P (v - 1)) (P (v + 1) - P v) =
      -det (P (v - 1) - P v) (P (v + 1) - P v) := by
    simp only [det, Prod.fst_sub, Prod.snd_sub]; ring
  rw [egoal]
  by_contra hcon
  have hcon' : 0 ≤ R.σ * det (P (v - 1) - P v) (P (v + 1) - P v) := by linarith
  have hσ0 : R.σ ≠ 0 := by rcases R.σ_pm with h | h <;> rw [h] <;> norm_num
  have hpos : 0 < R.σ * det (P (v - 1) - P v) (P (v + 1) - P v) :=
    lt_of_le_of_ne hcon' (Ne.symm (mul_ne_zero hσ0 hdet0))
  -- the face at `E_{v-1}` and its vertex order
  rw [u4h_edgeSegment_prev] at hFk
  have hends := u4h_face_edge_ends F k hFk
  have hDk := u4h_tri_pos F k
  -- the interior point `b'` of `F`, close to `P v`, in the direction of the apex plus `p`
  have hbase : ∀ ρ > 0, ∃ ε : ℝ, 0 < ε ∧ ε < 1/3 ∧
      dist (P v + ε • (F.v (k + 2) - P v) + ε • (P (v - 1) - P v)) (P v) < ρ ∧
      P v + ε • (F.v (k + 2) - P v) + ε • (P (v - 1) - P v) ∈ interior F.carrier := by
    intro ρ hρ
    have hM : 0 < ‖F.v (k + 2) - P v‖ + ‖P (v - 1) - P v‖ + 1 := by positivity
    refine ⟨min (1/4) (ρ / (2 * (‖F.v (k + 2) - P v‖ + ‖P (v - 1) - P v‖ + 1))), ?_, ?_, ?_, ?_⟩
    · exact lt_min (by norm_num) (by positivity)
    · exact lt_of_le_of_lt (min_le_left _ _) (by norm_num)
    · set ε := min (1/4) (ρ / (2 * (‖F.v (k + 2) - P v‖ + ‖P (v - 1) - P v‖ + 1))) with hε
      have hε0 : 0 < ε := lt_min (by norm_num) (by positivity)
      have hεle : ε ≤ ρ / (2 * (‖F.v (k + 2) - P v‖ + ‖P (v - 1) - P v‖ + 1)) := min_le_right _ _
      rw [dist_eq_norm, add_assoc, add_sub_cancel_left]
      calc ‖ε • (F.v (k + 2) - P v) + ε • (P (v - 1) - P v)‖
          ≤ ‖ε • (F.v (k + 2) - P v)‖ + ‖ε • (P (v - 1) - P v)‖ := norm_add_le _ _
        _ = ε * (‖F.v (k + 2) - P v‖ + ‖P (v - 1) - P v‖) := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, abs_of_pos hε0]; ring
        _ ≤ ρ / (2 * (‖F.v (k + 2) - P v‖ + ‖P (v - 1) - P v‖ + 1)) *
            (‖F.v (k + 2) - P v‖ + ‖P (v - 1) - P v‖) :=
          mul_le_mul_of_nonneg_right hεle (by positivity)
        _ < ρ := by
          rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
          nlinarith [norm_nonneg (F.v (k + 2) - P v), norm_nonneg (P (v - 1) - P v)]
    · set ε := min (1/4) (ρ / (2 * (‖F.v (k + 2) - P v‖ + ‖P (v - 1) - P v‖ + 1))) with hε
      have hε0 : 0 < ε := lt_min (by norm_num) (by positivity)
      have hε1 : ε ≤ 1/4 := min_le_left _ _
      rw [u4h_tri_carrier_rot F k]
      rcases hends with ⟨h0, h1⟩ | ⟨h0, h1⟩
      · have e : P v + ε • (F.v (k + 2) - P v) + ε • (P (v - 1) - P v) =
            ε • F.v k + (1 - 2 * ε) • F.v (k + 1) + ε • F.v (k + 2) := by
          rw [h0, h1]; module
        rw [e]
        exact u4h_pos_comb_mem_interior hDk hε0 (by linarith) hε0 (by ring)
      · have e : P v + ε • (F.v (k + 2) - P v) + ε • (P (v - 1) - P v) =
            (1 - 2 * ε) • F.v k + ε • F.v (k + 1) + ε • F.v (k + 2) := by
          rw [h0, h1]; module
        rw [e]
        exact u4h_pos_comb_mem_interior hDk (by linarith) hε0 hε0 (by ring)
  -- the determinant of `p` against `b' - P v`
  have hdetb' : ∀ ε : ℝ, det (P (v - 1) - P v)
      (P v + ε • (F.v (k + 2) - P v) + ε • (P (v - 1) - P v) - P v) =
      ε * det (P (v - 1) - P v) (F.v (k + 2) - P v) := by
    intro ε
    simp only [det, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
      Prod.smul_snd, smul_eq_mul]; ring
  rcases R.σ_pm with hσ | hσ
  · rw [hσ, one_mul] at hpos hside
    obtain ⟨ρ, hρ, hLL⟩ := u4h_local_lexmin hn hP R.isClosed R.frontier_eq R.hull hv
      (Or.inl rfl) (Or.inr rfl) hpos
    obtain ⟨ε, hε0, -, hdist, hint⟩ := hbase ρ hρ
    refine hLL _ hdist (Or.inl ?_) (R.face_subset hF (interior_subset hint))
    rw [hdetb']
    nlinarith
  · rw [hσ] at hpos hside
    have hpos' : 0 < det (P (v + 1) - P v) (P (v - 1) - P v) := by
      rw [u4h_det_swap']; linarith
    obtain ⟨ρ, hρ, hLL⟩ := u4h_local_lexmin hn hP R.isClosed R.frontier_eq R.hull hv
      (Or.inr rfl) (Or.inl rfl) hpos'
    obtain ⟨ε, hε0, -, hdist, hint⟩ := hbase ρ hρ
    refine hLL _ hdist (Or.inr ?_) (R.face_subset hF (interior_subset hint))
    rw [hdetb']
    nlinarith

/-- (LL2) -/
theorem u4h_lexmin_ray_outside [NeZero n] (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Embedded P)
    {U : Set Plane} (hU : IsClosed U) (hfr : frontier U = embeddedPolygonImage P)
    (hhull : U ⊆ convexHull ℝ (Set.range P)) {v : ZMod n}
    (hv : ∀ k, k ≠ v → u4h_Lex (P v) (P k)) {w : Plane}
    (hw : (0 < det (P (v - 1) - P v) (P (v + 1) - P v) ∧
        (det (P (v - 1) - P v) w < 0 ∨ 0 < det (P (v + 1) - P v) w)) ∨
      (det (P (v - 1) - P v) (P (v + 1) - P v) < 0 ∧
        (det (P (v + 1) - P v) w < 0 ∨ 0 < det (P (v - 1) - P v) w))) :
    ∃ ρ > 0, ∀ t : ℝ, 0 < t → t < ρ → P v + t • w ∉ U := by
  have hw1 : 0 < ‖w‖ + 1 := by positivity
  rcases hw with ⟨hd, hw⟩ | ⟨hd, hw⟩
  · obtain ⟨ρ, hρ, hLL⟩ := u4h_local_lexmin hn hP hU hfr hhull hv (Or.inl rfl) (Or.inr rfl) hd
    refine ⟨ρ / (‖w‖ + 1), by positivity, fun t ht0 ht => hLL _ ?_ ?_⟩
    · rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos ht0]
      have := (lt_div_iff₀ hw1).mp ht
      nlinarith [norm_nonneg w]
    · rw [add_sub_cancel_left, u4h_det_smul_right, u4h_det_smul_right]
      rcases hw with h | h
      · exact Or.inl (mul_neg_of_pos_of_neg ht0 h)
      · exact Or.inr (mul_pos ht0 h)
  · have hd' : 0 < det (P (v + 1) - P v) (P (v - 1) - P v) := by rw [u4h_det_swap']; linarith
    obtain ⟨ρ, hρ, hLL⟩ := u4h_local_lexmin hn hP hU hfr hhull hv (Or.inr rfl) (Or.inl rfl) hd'
    refine ⟨ρ / (‖w‖ + 1), by positivity, fun t ht0 ht => hLL _ ?_ ?_⟩
    · rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos ht0]
      have := (lt_div_iff₀ hw1).mp ht
      nlinarith [norm_nonneg w]
    · rw [add_sub_cancel_left, u4h_det_smul_right, u4h_det_smul_right]
      rcases hw with h | h
      · exact Or.inl (mul_neg_of_pos_of_neg ht0 h)
      · exact Or.inr (mul_pos ht0 h)

end U4O_block

section U4P_block

/-! Sub-polygons along a diagonal (U4 helpers): the vertices `P i, P (i+1), …, P (i+m)` closed by
the diagonal from `P (i+m)` back to `P i`. -/

/-- The sub-polygon of `P` with vertices `P i, …, P (i + m)` (an `(m+1)`-gon). -/
def u4h_subPoly (P : LabelledTuple n) (i : ZMod n) (m : ℕ) : LabelledTuple (m + 1) :=
  fun k => P (i + (k.val : ZMod n))

theorem u4h_subPoly_apply (P : LabelledTuple n) (i : ZMod n) (m : ℕ) (k : ZMod (m + 1)) :
    u4h_subPoly P i m k = P (i + (k.val : ZMod n)) := rfl

theorem u4h_val_neg_one' (m : ℕ) : ((-1 : ZMod (m + 1))).val = m := ZMod.val_neg_one m

theorem u4h_val_lt_of_ne_neg_one {m : ℕ} {k : ZMod (m + 1)} (hk : k ≠ -1) : k.val < m := by
  have h := ZMod.val_lt k
  rcases Nat.lt_or_ge k.val m with h' | h'
  · exact h'
  · exfalso
    apply hk
    apply ZMod.val_injective
    rw [u4h_val_neg_one']
    omega

theorem u4h_val_add_one {m : ℕ} {k : ZMod (m + 1)} (hk : k ≠ -1) : (k + 1).val = k.val + 1 := by
  have h := u4h_val_lt_of_ne_neg_one hk
  rw [ZMod.val_add_of_lt]
  · rw [ZMod.val_one_eq_one_mod]
    rcases Nat.lt_or_ge 1 (m + 1) with h1 | h1
    · rw [Nat.mod_eq_of_lt h1]
    · omega
  · rw [ZMod.val_one_eq_one_mod]
    rcases Nat.lt_or_ge 1 (m + 1) with h1 | h1
    · rw [Nat.mod_eq_of_lt h1]; omega
    · omega

theorem u4h_subPoly_zero (P : LabelledTuple n) (i : ZMod n) (m : ℕ) :
    u4h_subPoly P i m 0 = P i := by
  simp [u4h_subPoly_apply]

theorem u4h_subPoly_last (P : LabelledTuple n) (i : ZMod n) (m : ℕ) :
    u4h_subPoly P i m (-1) = P (i + m) := by
  rw [u4h_subPoly_apply, u4h_val_neg_one']

theorem u4h_subPoly_edge (P : LabelledTuple n) (i : ZMod n) (m : ℕ) {k : ZMod (m + 1)}
    (hk : k ≠ -1) : edge (u4h_subPoly P i m) k = edge P (i + (k.val : ZMod n)) := by
  simp only [edge, u4h_subPoly_apply, u4h_val_add_one hk, Nat.cast_add, Nat.cast_one, add_assoc]

theorem u4h_subPoly_edgeSegment (P : LabelledTuple n) (i : ZMod n) (m : ℕ) {k : ZMod (m + 1)}
    (hk : k ≠ -1) : edgeSegment (u4h_subPoly P i m) k = edgeSegment P (i + (k.val : ZMod n)) := by
  simp only [edgeSegment, edgePoint, u4h_subPoly_edge P i m hk, u4h_subPoly_apply]

theorem u4h_subPoly_edgeSegment_last (P : LabelledTuple n) (i : ZMod n) (m : ℕ) :
    edgeSegment (u4h_subPoly P i m) (-1) = segment ℝ (P (i + m)) (P i) := by
  rw [u4h_edgeSegment_eq_segment, neg_add_cancel, u4h_subPoly_last, u4h_subPoly_zero]

/-- The natural-number offsets `s < m` index exactly the non-diagonal edges. -/
theorem u4h_subPoly_index_exhaust (m : ℕ) {s : ℕ} (hs : s < m) :
    ∃ k : ZMod (m + 1), k ≠ -1 ∧ k.val = s := by
  refine ⟨(s : ZMod (m + 1)), ?_, ZMod.val_natCast_of_lt (by omega)⟩
  intro h
  have := congrArg ZMod.val h
  rw [ZMod.val_natCast_of_lt (by omega), u4h_val_neg_one'] at this
  omega

/-- Membership in the polygon image of a sub-polygon. -/
theorem u4h_mem_polygonImage_subPoly (P : LabelledTuple n) (i : ZMod n) (m : ℕ) (x : Plane) :
    x ∈ embeddedPolygonImage (u4h_subPoly P i m) ↔
      (∃ s : ℕ, s < m ∧ x ∈ edgeSegment P (i + s)) ∨ x ∈ segment ℝ (P (i + m)) (P i) := by
  constructor
  · intro hx
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hx
    by_cases hk1 : k = -1
    · subst hk1
      rw [u4h_subPoly_edgeSegment_last] at hk
      exact Or.inr hk
    · rw [u4h_subPoly_edgeSegment P i m hk1] at hk
      exact Or.inl ⟨k.val, u4h_val_lt_of_ne_neg_one hk1, hk⟩
  · rintro (⟨s, hs, hx⟩ | hx)
    · obtain ⟨k, hk1, hks⟩ := u4h_subPoly_index_exhaust m hs
      refine Set.mem_iUnion.mpr ⟨k, ?_⟩
      rw [u4h_subPoly_edgeSegment P i m hk1, hks]
      exact hx
    · exact Set.mem_iUnion.mpr ⟨-1, by rw [u4h_subPoly_edgeSegment_last]; exact hx⟩

theorem u4h_subPoly_range_subset (P : LabelledTuple n) (i : ZMod n) (m : ℕ) :
    Set.range (u4h_subPoly P i m) ⊆ Set.range P := by
  rintro x ⟨k, rfl⟩
  exact ⟨_, rfl⟩

/-- An integer of absolute value `< n` that vanishes in `ZMod n` is zero. -/
theorem u4h_int_cast_eq_zero {x : ℤ} (hx : |x| < n) (h : (x : ZMod n) = 0) : x = 0 :=
  Int.eq_zero_of_abs_lt_dvd ((ZMod.intCast_zmod_eq_zero_iff_dvd x n).mp h) hx

/-- Adjacency of the `P`-indices `i + s`, `i + s'` for small offsets. -/
theorem u4h_adjacent_offset {s s' : ℕ} (hs : s + 2 < n) (hs' : s' + 2 < n) (i : ZMod n) :
    adjacent (i + (s : ZMod n)) (i + (s' : ZMod n)) ↔ (s' = s + 1 ∨ s' = s ∨ s = s' + 1) := by
  have key : ∀ x : ℤ, |x| < n → (((x : ℤ) : ZMod n) = 0 ↔ x = 0) := fun x hx =>
    ⟨u4h_int_cast_eq_zero hx, fun h => by rw [h, Int.cast_zero]⟩
  rw [u4h_adjacent_iff]
  have e1 : (i + (s' : ZMod n) = i + (s : ZMod n) - 1) ↔ (((s' : ℤ) - s + 1 : ℤ) : ZMod n) = 0 := by
    push_cast; constructor <;> intro h <;> linear_combination h
  have e2 : (i + (s' : ZMod n) = i + (s : ZMod n)) ↔ (((s' : ℤ) - s : ℤ) : ZMod n) = 0 := by
    push_cast; constructor <;> intro h <;> linear_combination h
  have e3 : (i + (s' : ZMod n) = i + (s : ZMod n) + 1) ↔ (((s' : ℤ) - s - 1 : ℤ) : ZMod n) = 0 := by
    push_cast; constructor <;> intro h <;> linear_combination h
  rw [e1, e2, e3, key _ (by rw [abs_lt]; constructor <;> omega),
    key _ (by rw [abs_lt]; constructor <;> omega), key _ (by rw [abs_lt]; constructor <;> omega)]
  omega

/-- `i + s = i + s'` for offsets `< n` forces `s = s'`. -/
theorem u4h_offset_injective {s s' : ℕ} (hs : s < n) (hs' : s' < n) (i : ZMod n)
    (h : i + (s : ZMod n) = i + (s' : ZMod n)) : s = s' := by
  have h' : (((s : ℤ) - s' : ℤ) : ZMod n) = 0 := by push_cast; linear_combination h
  have := u4h_int_cast_eq_zero (by rw [abs_lt]; constructor <;> omega) h'
  omega

end U4P_block

section U4Q_block

/-! A sub-polygon along a clean diagonal is embedded (U4 helpers). -/

theorem u4h_Pi_mem_offset [NeZero n] {P : LabelledTuple n} (hP : Embedded P) {i : ZMod n}
    {m : ℕ} (hmn : m + 2 ≤ n) {s : ℕ} (hs : s < m) (h : P i ∈ edgeSegment P (i + (s : ZMod n))) :
    s = 0 := by
  rcases u4h_incident_of_vertex_mem hP h with h' | h'
  · have := u4h_offset_injective (s := 0) (s' := s) (by omega) (by omega) i (by simpa using h')
    omega
  · exfalso
    have := u4h_offset_injective (s := 0) (s' := s + 1) (by omega) (by omega) i
      (by rw [Nat.cast_add, Nat.cast_one, ← add_assoc]; simpa using h')
    omega

theorem u4h_Pim_mem_offset [NeZero n] {P : LabelledTuple n} (hP : Embedded P) {i : ZMod n}
    {m : ℕ} (hmn : m + 2 ≤ n) {s : ℕ} (hs : s < m)
    (h : P (i + (m : ZMod n)) ∈ edgeSegment P (i + (s : ZMod n))) : s + 1 = m := by
  rcases u4h_incident_of_vertex_mem hP h with h' | h'
  · have := u4h_offset_injective (s := m) (s' := s) (by omega) (by omega) i h'
    omega
  · have := u4h_offset_injective (s := m) (s' := s + 1) (by omega) (by omega) i
      (by rw [Nat.cast_add, Nat.cast_one, ← add_assoc]; exact h')
    omega

/-- A `P`-edge of the sub-polygon meets the diagonal only at its endpoints (clean diagonal). -/
theorem u4h_edge_inter_diag_subPoly {P : LabelledTuple n} {i : ZMod n} {m : ℕ}
    (hclean : ∀ k, Disjoint (edgeSegment P k) (openSegment ℝ (P i) (P (i + (m : ZMod n)))))
    (k : ZMod n) {x : Plane} (hx : x ∈ edgeSegment P k)
    (hD : x ∈ segment ℝ (P (i + (m : ZMod n))) (P i)) : x = P i ∨ x = P (i + (m : ZMod n)) := by
  rw [← insert_endpoints_openSegment] at hD
  rcases hD with h | h | h
  · exact Or.inr h
  · exact Or.inl h
  · exfalso
    rw [openSegment_symm] at h
    exact Set.disjoint_left.mp (hclean k) hx h

theorem u4h_val_eq_zero_iff {m : ℕ} (k : ZMod (m + 1)) : k.val = 0 ↔ k = 0 := by
  constructor
  · intro h
    apply ZMod.val_injective
    rw [h, ZMod.val_zero]
  · rintro rfl
    exact ZMod.val_zero

theorem u4h_add_one_eq_neg_one {m : ℕ} {k : ZMod (m + 1)} (hk : k ≠ -1) (h : k.val + 1 = m) :
    k + 1 = -1 := by
  apply ZMod.val_injective
  rw [u4h_val_add_one hk, u4h_val_neg_one', h]

/-- **A sub-polygon along a clean diagonal is embedded.** -/
theorem u4h_subPoly_embedded [NeZero n] {P : LabelledTuple n} (hP : Embedded P) {i : ZMod n}
    {m : ℕ} (hm : 2 ≤ m) (hmn : m + 2 ≤ n)
    (hclean : ∀ k, Disjoint (edgeSegment P k) (openSegment ℝ (P i) (P (i + (m : ZMod n))))) :
    Embedded (u4h_subPoly P i m) := by
  have hDinter := u4h_edge_inter_diag_subPoly hclean
  have hm0 : (m : ZMod n) ≠ 0 := u4h_natCast_ne_zero (by omega) (by omega)
  have hPiPm : P i ≠ P (i + (m : ZMod n)) := by
    intro h
    have := u4h_vertex_injective hP h
    exact hm0 (by linear_combination -this)
  refine ⟨fun k => ?_, fun k l hr => ?_, fun k => ?_⟩
  · by_cases hk : k = -1
    · subst hk
      rw [edge, neg_add_cancel, u4h_subPoly_zero, u4h_subPoly_last]
      exact sub_ne_zero.mpr hPiPm
    · rw [u4h_subPoly_edge P i m hk]
      exact hP.edge_ne_zero _
  · -- remote pairs
    have hadj_self : ∀ j : ZMod (m + 1), adjacent j j := fun j => Or.inr (Or.inl (sub_self j))
    -- the diagonal against a `P`-edge with offset `s ∉ {0, m-1}`
    have hdiag : ∀ l : ZMod (m + 1), l ≠ -1 → remote (-1) l →
        Disjoint (edgeSegment (u4h_subPoly P i m) (-1)) (edgeSegment (u4h_subPoly P i m) l) := by
      intro l hl hr
      have hs := u4h_val_lt_of_ne_neg_one hl
      rw [u4h_subPoly_edgeSegment_last, u4h_subPoly_edgeSegment P i m hl, Set.disjoint_left]
      intro x hxD hxl
      rcases hDinter _ hxl hxD with h | h
      · have h0 := u4h_Pi_mem_offset hP hmn hs (h ▸ hxl)
        apply hr
        rw [(u4h_val_eq_zero_iff l).mp h0]
        exact Or.inr (Or.inr (by ring))
      · have h1 := u4h_Pim_mem_offset hP hmn hs (h ▸ hxl)
        apply hr
        have := u4h_add_one_eq_neg_one hl h1
        exact Or.inl (by linear_combination this)
    by_cases hk : k = -1
    · subst hk
      have hl : l ≠ -1 := fun h => hr (h ▸ hadj_self _)
      exact hdiag l hl hr
    · by_cases hl : l = -1
      · subst hl
        exact (hdiag k hk (remote_symm hr)).symm
      · rw [u4h_subPoly_edgeSegment P i m hk, u4h_subPoly_edgeSegment P i m hl]
        apply hP.remote_disjoint
        have hsk := u4h_val_lt_of_ne_neg_one hk
        have hsl := u4h_val_lt_of_ne_neg_one hl
        rw [remote, u4h_adjacent_offset (by omega) (by omega)]
        rintro (h | h | h)
        · apply hr
          have : l = k + 1 := ZMod.val_injective _ (by rw [u4h_val_add_one hk, h])
          exact Or.inr (Or.inr (by rw [this]; ring))
        · apply hr
          have : l = k := ZMod.val_injective _ h
          exact this ▸ hadj_self k
        · apply hr
          have : k = l + 1 := ZMod.val_injective _ (by rw [u4h_val_add_one hl, h])
          exact Or.inl (by rw [this]; ring)
  · -- consecutive pairs
    by_cases hk : k = -1
    · subst hk
      have h0 : (0 : ZMod (m + 1)) ≠ -1 := by
        intro h
        have := congrArg ZMod.val h
        rw [ZMod.val_zero, u4h_val_neg_one'] at this
        omega
      rw [neg_add_cancel, u4h_subPoly_edgeSegment_last, u4h_subPoly_edgeSegment P i m h0,
        u4h_subPoly_zero, ZMod.val_zero, Nat.cast_zero, add_zero]
      ext x
      constructor
      · rintro ⟨hxD, hxi⟩
        rcases hDinter _ hxi hxD with h | h
        · exact h
        · exfalso
          have := u4h_Pim_mem_offset hP hmn (s := 0) (by omega) (by simpa using h ▸ hxi)
          omega
      · intro hx
        have hx' : x = P i := hx
        rw [hx']
        exact ⟨right_mem_segment ℝ _ _, u4h_start_mem_edgeSegment P i⟩
    · by_cases hk1 : k + 1 = -1
      · have hs : k.val + 1 = m := by
          have := congrArg ZMod.val hk1
          rwa [u4h_val_add_one hk, u4h_val_neg_one'] at this
        rw [hk1, u4h_subPoly_edgeSegment_last, u4h_subPoly_edgeSegment P i m hk, u4h_subPoly_last]
        ext x
        constructor
        · rintro ⟨hxk, hxD⟩
          rcases hDinter _ hxk hxD with h | h
          · exfalso
            have := u4h_Pi_mem_offset hP hmn (u4h_val_lt_of_ne_neg_one hk) (h ▸ hxk)
            omega
          · exact h
        · intro hx
          have hx' : x = P (i + (m : ZMod n)) := hx
          rw [hx']
          refine ⟨?_, left_mem_segment ℝ _ _⟩
          have := u4h_end_mem_edgeSegment P (i + (k.val : ZMod n))
          rwa [add_assoc, ← Nat.cast_add_one, hs] at this
      · rw [u4h_subPoly_edgeSegment P i m hk, u4h_subPoly_edgeSegment P i m hk1,
          u4h_subPoly_apply, u4h_val_add_one hk, Nat.cast_succ, ← add_assoc]
        exact hP.consecutive _

end U4Q_block

section U4R_block

/-! Chains of polygon edges lie on one side of a closed set whose frontier they avoid
(U4 helpers). -/

/-- Extreme points of a segment: a strict convex combination of two segment points equal to an
endpoint forces both points to be that endpoint. -/
theorem u4h_segment_extreme {a b x y : Plane} (hx : x ∈ segment ℝ a b) (hy : y ∈ segment ℝ a b)
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (hst : s + t = 1) (h : s • x + t • y = a) :
    x = a := by
  obtain ⟨l, hl0, -, rfl⟩ := (u4h_mem_segment_iff_lin a b x).mp hx
  obtain ⟨l', hl'0, -, rfl⟩ := (u4h_mem_segment_iff_lin a b y).mp hy
  have e : s • (a + l • (b - a)) + t • (a + l' • (b - a)) = a + (s * l + t * l') • (b - a) := by
    rw [smul_add, smul_add, smul_smul, smul_smul, add_add_add_comm, ← add_smul, ← add_smul, hst,
      one_smul]
  rw [e] at h
  have h0 : (s * l + t * l') • (b - a) = 0 := add_eq_left.mp h
  rcases smul_eq_zero.mp h0 with h0 | h0
  · have hl : l = 0 := by nlinarith
    rw [hl, zero_smul, add_zero]
  · rw [h0, smul_zero, add_zero]

/-- A segment minus a set of points all of which are endpoints is convex. -/
theorem u4h_convex_segment_diff {a b : Plane} {S : Set Plane}
    (hS : ∀ x ∈ S, x ∈ segment ℝ a b → x = a ∨ x = b) : Convex ℝ (segment ℝ a b \ S) := by
  intro x hx y hy s t hs ht hst
  refine ⟨(convex_segment a b) hx.1 hy.1 hs ht hst, fun hmem => ?_⟩
  have hz : s • x + t • y ∈ segment ℝ a b := (convex_segment a b) hx.1 hy.1 hs ht hst
  rcases hs.lt_or_eq with hs' | hs'
  · rcases ht.lt_or_eq with ht' | ht'
    · rcases hS _ hmem hz with h | h
      · have := u4h_segment_extreme hx.1 hy.1 hs' ht' hst h
        exact hx.2 (this ▸ h ▸ hmem)
      · rw [segment_symm] at hx hy hz
        have := u4h_segment_extreme hx.1 hy.1 hs' ht' hst h
        exact hx.2 (this ▸ h ▸ hmem)
    · have : s = 1 := by linarith
      subst this
      rw [← ht', zero_smul, add_zero, one_smul] at hmem
      exact hx.2 hmem
  · rw [← hs'] at hst
    have : t = 1 := by linarith
    subst this
    rw [← hs', zero_smul, zero_add, one_smul] at hmem
    exact hy.2 hmem

/-- A piece of a chain: an edge with (some of) its endpoints removed is convex. -/
theorem u4h_chain_piece_convex {P : LabelledTuple n} (hP : Embedded P) (k : ZMod n)
    (S : Set Plane) (hS : ∀ x ∈ S, ∃ j, P j = x) :
    Convex ℝ (edgeSegment P k \ S) := by
  rw [u4h_edgeSegment_eq_segment]
  apply u4h_convex_segment_diff
  intro x hxS hx
  obtain ⟨j, rfl⟩ := hS x hxS
  rw [← u4h_edgeSegment_eq_segment] at hx
  rcases u4h_incident_of_vertex_mem hP hx with h | h
  · exact Or.inl (by rw [h])
  · exact Or.inr (by rw [h])

/-- **Chain-side lemma.** The edges `E_{i+s}` (`s < m`), with the two chain ends removed, all lie
in the interior of `U` or all lie outside `U`, provided they avoid its frontier. -/
theorem u4h_chain_side [NeZero n] {P : LabelledTuple n} (hP : Embedded P) {i : ZMod n} {m : ℕ}
    (hmn : m + 2 ≤ n) {U : Set Plane} (hU : IsClosed U)
    (hfr : ∀ s : ℕ, s < m → ∀ x ∈ edgeSegment P (i + (s : ZMod n)),
      x ∉ ({P i, P (i + (m : ZMod n))} : Set Plane) → x ∉ frontier U) :
    (∀ s : ℕ, s < m → ∀ x ∈ edgeSegment P (i + (s : ZMod n)),
      x ∉ ({P i, P (i + (m : ZMod n))} : Set Plane) → x ∈ interior U) ∨
    (∀ s : ℕ, s < m → ∀ x ∈ edgeSegment P (i + (s : ZMod n)),
      x ∉ ({P i, P (i + (m : ZMod n))} : Set Plane) → x ∉ U) := by
  set S : Set Plane := {P i, P (i + (m : ZMod n))} with hSdef
  have hSv : ∀ x ∈ S, ∃ j, P j = x := by
    rintro x (rfl | rfl)
    · exact ⟨i, rfl⟩
    · exact ⟨_, rfl⟩
  -- each piece is on one side
  have hpiece : ∀ s : ℕ, s < m →
      (edgeSegment P (i + (s : ZMod n)) \ S ⊆ interior U) ∨
      (edgeSegment P (i + (s : ZMod n)) \ S ⊆ Uᶜ) := by
    intro s hs
    have hconv := u4h_chain_piece_convex hP (i + (s : ZMod n)) S hSv
    have hsub : edgeSegment P (i + (s : ZMod n)) \ S ⊆ interior U ∪ Uᶜ := by
      rintro x ⟨hx, hxS⟩
      by_cases hxU : x ∈ U
      · left
        by_contra hxi
        exact hfr s hs x hx hxS ⟨subset_closure hxU, hxi⟩
      · right; exact hxU
    exact IsPreconnected.subset_or_subset isOpen_interior hU.isOpen_compl
      (Set.disjoint_left.mpr fun y hy hy' => hy' (interior_subset hy)) hsub
      hconv.isPreconnected
  -- consecutive pieces share the vertex `P (i + s + 1)`, which is not a chain end
  have hshared : ∀ s : ℕ, s + 1 < m →
      P (i + ((s + 1 : ℕ) : ZMod n)) ∈ edgeSegment P (i + (s : ZMod n)) \ S ∧
      P (i + ((s + 1 : ℕ) : ZMod n)) ∈ edgeSegment P (i + ((s + 1 : ℕ) : ZMod n)) \ S := by
    intro s hs
    have hnotS : P (i + ((s + 1 : ℕ) : ZMod n)) ∉ S := by
      rintro (h | h)
      · have := u4h_offset_injective (s := s + 1) (s' := 0) (by omega) (by omega) i
          (by rw [Nat.cast_zero, add_zero]; exact u4h_vertex_injective hP h)
        omega
      · have := u4h_offset_injective (s := s + 1) (s' := m) (by omega) (by omega) i
          (u4h_vertex_injective hP h)
        omega
    refine ⟨⟨?_, hnotS⟩, ⟨u4h_start_mem_edgeSegment P _, hnotS⟩⟩
    have := u4h_end_mem_edgeSegment P (i + (s : ZMod n))
    rwa [add_assoc, ← Nat.cast_add_one] at this
  by_cases h0 : edgeSegment P (i + ((0 : ℕ) : ZMod n)) \ S ⊆ interior U
  · left
    have key : ∀ s : ℕ, s < m → edgeSegment P (i + (s : ZMod n)) \ S ⊆ interior U := by
      intro s
      induction s with
      | zero => intro _; exact h0
      | succ s ih =>
        intro hs
        rcases hpiece (s + 1) hs with h | h
        · exact h
        · exfalso
          obtain ⟨h1, h2⟩ := hshared s hs
          exact h h2 (interior_subset (ih (by omega) h1))
    intro s hs x hx hxS
    exact key s hs ⟨hx, hxS⟩
  · right
    by_cases hm : m = 0
    · intro s hs; omega
    have h0' : edgeSegment P (i + ((0 : ℕ) : ZMod n)) \ S ⊆ Uᶜ := by
      rcases hpiece 0 (by omega) with h | h
      · exact absurd h h0
      · exact h
    have key : ∀ s : ℕ, s < m → edgeSegment P (i + (s : ZMod n)) \ S ⊆ Uᶜ := by
      intro s
      induction s with
      | zero => intro _; exact h0'
      | succ s ih =>
        intro hs
        rcases hpiece (s + 1) hs with h | h
        · exfalso
          obtain ⟨h1, h2⟩ := hshared s hs
          exact ih (by omega) h1 (interior_subset (h h2))
        · exact h
    intro s hs x hx hxS
    exact key s hs ⟨hx, hxS⟩

end U4R_block

section U4S_block

/-! The base case: the region of an embedded triangle (U4 helpers). -/

theorem u4h_zmod3_cases (i : ZMod 3) : i = 0 ∨ i = 1 ∨ i = 2 := by
  revert i; decide

theorem u4h_range_zmod3 (P : LabelledTuple 3) : Set.range P = {P 0, P 1, P 2} := by
  ext x
  simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨i, rfl⟩
    rcases u4h_zmod3_cases i with rfl | rfl | rfl <;> simp
  · rintro (rfl | rfl | rfl) <;> exact ⟨_, rfl⟩

/-- All three turns of a triangle have the same determinant. -/
theorem u4h_tri3_turn (P : LabelledTuple 3) (i : ZMod 3) :
    det (edge P (i - 1)) (edge P i) = det (P 1 - P 0) (P 2 - P 0) := by
  have h01 : (0 : ZMod 3) + 1 = 1 := by decide
  have h12 : (1 : ZMod 3) + 1 = 2 := by decide
  have h20 : (2 : ZMod 3) + 1 = 0 := by decide
  have hm0 : (0 : ZMod 3) - 1 = 2 := by decide
  have hm1 : (1 : ZMod 3) - 1 = 0 := by decide
  have hm2 : (2 : ZMod 3) - 1 = 1 := by decide
  rcases u4h_zmod3_cases i with rfl | rfl | rfl
  · rw [hm0]; simp only [edge, h20, h01]; simp only [det, Prod.fst_sub, Prod.snd_sub]; ring
  · rw [hm1]; simp only [edge, h01, h12]; simp only [det, Prod.fst_sub, Prod.snd_sub]; ring
  · rw [hm2]; simp only [edge, h12, h20]; simp only [det, Prod.fst_sub, Prod.snd_sub]; ring

/-- An embedded triangle is nondegenerate. -/
theorem u4h_tri3_det_ne_zero (P : LabelledTuple 3) (hP : Embedded P) :
    det (P 1 - P 0) (P 2 - P 0) ≠ 0 := by
  obtain ⟨N, i, -, hturn⟩ := exists_supporting_vertex_turn_ne_zero (le_refl 3) hP
  have hreg := hP.regular (le_refl 3)
  intro hD
  apply hturn
  rw [principalTurn, principalAngle_zero_iff_det_zero (hreg i), u4h_tri3_turn, hD]

/-- The one-face triangulation of a triangle. -/
def u4h_singleTri (T : Triangle) : Triangulation T.carrier where
  faces := {T}
  finite := Set.finite_singleton T
  cover := by simp
  inter := by
    intro T1 h1 T2 h2
    rw [Set.mem_singleton_iff] at h1 h2
    subst h1; subst h2
    rw [Set.inter_self, Set.inter_self]; rfl

theorem u4h_edgeSegment_zmod3 (P : LabelledTuple 3) :
    edgeSegment P 0 = segment ℝ (P 0) (P 1) ∧ edgeSegment P 1 = segment ℝ (P 1) (P 2) ∧
      edgeSegment P 2 = segment ℝ (P 2) (P 0) := by
  have h01 : (0 : ZMod 3) + 1 = 1 := by decide
  have h12 : (1 : ZMod 3) + 1 = 2 := by decide
  have h20 : (2 : ZMod 3) + 1 = 0 := by decide
  refine ⟨?_, ?_, ?_⟩
  · rw [u4h_edgeSegment_eq_segment, h01]
  · rw [u4h_edgeSegment_eq_segment, h12]
  · rw [u4h_edgeSegment_eq_segment, h20]

theorem u4h_polygonImage_zmod3 (P : LabelledTuple 3) :
    embeddedPolygonImage P = segment ℝ (P 0) (P 1) ∪ segment ℝ (P 1) (P 2) ∪ segment ℝ (P 2) (P 0) := by
  obtain ⟨h0, h1, h2⟩ := u4h_edgeSegment_zmod3 P
  ext x
  simp only [embeddedPolygonImage, Set.mem_iUnion, Set.mem_union]
  constructor
  · rintro ⟨i, hi⟩
    rcases u4h_zmod3_cases i with rfl | rfl | rfl
    · rw [h0] at hi; exact Or.inl (Or.inl hi)
    · rw [h1] at hi; exact Or.inl (Or.inr hi)
    · rw [h2] at hi; exact Or.inr hi
  · rintro ((h | h) | h)
    · exact ⟨0, h0 ▸ h⟩
    · exact ⟨1, h1 ▸ h⟩
    · exact ⟨2, h2 ▸ h⟩

/-- A region for an embedded triangle built from a face `T` whose vertices are the polygon's,
given the identification of the edges. -/
def u4h_triRegionOf (P : LabelledTuple 3) (T : Triangle)
    (hcar : T.carrier = convexHull ℝ {P 0, P 1, P 2})
    (hfr : frontier T.carrier = embeddedPolygonImage P)
    (hedges : ∀ i : ZMod 3, ∃ k : Fin 3, T.edgeSeg k = edgeSegment P i)
    (σ : ℝ) (hσ : σ = 1 ∨ σ = -1)
    (hside : ∀ i : ZMod 3, ∀ k : Fin 3, T.edgeSeg k = edgeSegment P i →
      0 < σ * det (P (i + 1) - P i) (T.v (k + 2) - P i)) : u4h_Region P where
  U := T.carrier
  K := u4h_singleTri T
  frontier_eq := hfr
  edge_face := fun i => by
    obtain ⟨k, hk⟩ := hedges i
    exact ⟨T, rfl, k, hk⟩
  edge_unique := by
    intro i T1 h1 T2 h2 _ _
    have h1' : T1 = T := h1
    have h2' : T2 = T := h2
    rw [h1', h2']
  hull := by rw [hcar, u4h_range_zmod3]
  int_conn := (convex_convexHull ℝ _).interior.isPreconnected
  σ := σ
  σ_pm := hσ
  side := by
    intro i T1 h1 k hk
    have h1' : T1 = T := h1
    subst h1'
    exact hside i k hk
  count := by
    show (({T} : Set Triangle).image Triangle.carrier).ncard + 2 ≤ 3
    rw [Set.image_singleton, Set.ncard_singleton]

end U4S_block

section U4T_block

/-! The clean diagonal from the lexmin vertex to the farthest invader of its ear triangle
(U4 helpers). -/

/-- Height of `x` above the base line of the ear triangle at `v`, normalised to be positive at
`P v`. -/
def u4h_height (P : LabelledTuple n) (v : ZMod n) (x : Plane) : ℝ :=
  det (P (v + 1) - P (v - 1)) (x - P (v - 1)) * det (P (v + 1) - P (v - 1)) (P v - P (v - 1))

theorem u4h_height_lin (P : LabelledTuple n) (v : ZMod n) (s t : Plane) (l : ℝ) :
    u4h_height P v (s + l • (t - s)) = u4h_height P v s + l * (u4h_height P v t - u4h_height P v s) := by
  simp only [u4h_height, det, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add,
    Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring

theorem u4h_height_comb (P : LabelledTuple n) (v : ZMod n) (s t : Plane) (l : ℝ) :
    u4h_height P v ((1 - l) • s + l • t) = (1 - l) * u4h_height P v s + l * u4h_height P v t := by
  simp only [u4h_height, det, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add,
    Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring

theorem u4h_height_base (P : LabelledTuple n) (v : ZMod n) {x : Plane}
    (hx : x ∈ segment ℝ (P (v - 1)) (P (v + 1))) : u4h_height P v x = 0 := by
  rw [u4h_height, u4h_det_segment_zero hx, zero_mul]

theorem u4h_height_pos (P : LabelledTuple n) (v : ZMod n)
    (hdet : det (P v - P (v - 1)) (P (v + 1) - P (v - 1)) ≠ 0) : 0 < u4h_height P v (P v) := by
  have : det (P (v + 1) - P (v - 1)) (P v - P (v - 1)) ≠ 0 := by
    rw [u4h_det_swap']; exact neg_ne_zero.mpr hdet
  rw [u4h_height]
  exact mul_self_pos.mpr this

/-- Barycentric description of points of the ear triangle. -/
theorem u4h_earHull_bary (P : LabelledTuple n) (v : ZMod n) {x : Plane} (hx : x ∈ earHull P v) :
    ∃ α β γ : ℝ, 0 ≤ α ∧ 0 ≤ β ∧ 0 ≤ γ ∧ α + β + γ = 1 ∧
      x = α • P (v - 1) + β • P v + γ • P (v + 1) :=
  (u4h_mem_hull3_iff _ _ _ x).mp hx

theorem u4h_height_bary (P : LabelledTuple n) (v : ZMod n) {α β γ : ℝ} (hsum : α + β + γ = 1) :
    u4h_height P v (α • P (v - 1) + β • P v + γ • P (v + 1)) = β * u4h_height P v (P v) := by
  have hα : α = 1 - β - γ := by linarith
  subst hα
  simp only [u4h_height, det, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add,
    Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring

/-- On the ear triangle the height is nonnegative, at most the height of the apex, and equal to
it only at the apex. -/
theorem u4h_height_le (P : LabelledTuple n) (v : ZMod n)
    (hdet : det (P v - P (v - 1)) (P (v + 1) - P (v - 1)) ≠ 0) {x : Plane} (hx : x ∈ earHull P v) :
    0 ≤ u4h_height P v x ∧ u4h_height P v x ≤ u4h_height P v (P v) ∧
      (u4h_height P v x = u4h_height P v (P v) → x = P v) := by
  obtain ⟨α, β, γ, hα, hβ, hγ, hsum, rfl⟩ := u4h_earHull_bary P v hx
  have hpos := u4h_height_pos P v hdet
  rw [u4h_height_bary P v hsum]
  refine ⟨mul_nonneg hβ hpos.le, ?_, fun h => ?_⟩
  · nlinarith
  · have hβ1 : β = 1 := by
      have : (β - 1) * u4h_height P v (P v) = 0 := by linarith
      rcases mul_eq_zero.mp this with h | h
      · linarith
      · exact absurd h hpos.ne'
    have hα0 : α = 0 := by linarith
    have hγ0 : γ = 0 := by linarith
    rw [hα0, hβ1, hγ0]; simp

/-- The frontier of a nondegenerate ear triangle. -/
theorem u4h_frontier_earHull (P : LabelledTuple n) (v : ZMod n)
    (hdet : det (P v - P (v - 1)) (P (v + 1) - P (v - 1)) ≠ 0) :
    frontier (earHull P v) =
      edgeSegment P (v - 1) ∪ edgeSegment P v ∪ segment ℝ (P (v - 1)) (P (v + 1)) := by
  rw [u4h_edgeSegment_prev, u4h_edgeSegment_eq_segment]
  rcases lt_or_gt_of_ne hdet with h | h
  · have h' : 0 < det (P (v + 1) - P (v - 1)) (P v - P (v - 1)) := by
      rw [u4h_det_swap']; linarith
    unfold earHull
    rw [u4h_hull3_comm, u4h_frontier_hull3 h', segment_symm ℝ (P (v + 1)) (P v),
      segment_symm ℝ (P v) (P (v - 1))]
    ext x; simp only [Set.mem_union]; tauto
  · unfold earHull
    rw [u4h_frontier_hull3 h, segment_symm ℝ (P (v + 1)) (P (v - 1))]

/-- The invaders of the ear triangle at `v`. -/
def u4h_Inv (P : LabelledTuple n) (v : ZMod n) : Set (ZMod n) :=
  {k | k ≠ v - 1 ∧ k ≠ v ∧ k ≠ v + 1 ∧ P k ∈ earHull P v}

/-- An affine functional has no strict maximum at an inner point of a segment. -/
theorem u4h_no_strict_max_on_segment (P : LabelledTuple n) (v : ZMod n) {s t x : Plane}
    (hx : x ∈ segment ℝ s t)
    (h1 : ∃ z ∈ segment ℝ x s, z ≠ x ∧ u4h_height P v z < u4h_height P v x)
    (h2 : ∃ z ∈ segment ℝ x t, z ≠ x ∧ u4h_height P v z < u4h_height P v x) : False := by
  obtain ⟨z1, hz1, hz1x, hg1⟩ := h1
  obtain ⟨z2, hz2, hz2x, hg2⟩ := h2
  obtain ⟨l, hl0, hl1, rfl⟩ := (u4h_mem_segment_iff_lin s t x).mp hx
  obtain ⟨α, hα0, -, rfl⟩ := (u4h_mem_segment_iff_lin _ s z1).mp hz1
  obtain ⟨β, hβ0, -, rfl⟩ := (u4h_mem_segment_iff_lin _ t z2).mp hz2
  have hαpos : 0 < α := by
    rcases hα0.lt_or_eq with h | h
    · exact h
    · subst h; exact absurd (by simp) hz1x
  have hβpos : 0 < β := by
    rcases hβ0.lt_or_eq with h | h
    · exact h
    · subst h; exact absurd (by simp) hz2x
  rw [u4h_height_lin] at hg1 hg2
  set Gs := u4h_height P v s with hGs
  set Gt := u4h_height P v t with hGt
  have hxeq : u4h_height P v (s + l • (t - s)) = Gs + l * (Gt - Gs) := u4h_height_lin P v s t l
  rw [hxeq] at hg1 hg2
  have h1 : Gs < Gs + l * (Gt - Gs) := by nlinarith
  have h2 : Gt < Gs + l * (Gt - Gs) := by nlinarith
  rcases hl1.lt_or_eq with hl1' | hl1'
  · have := mul_pos (sub_pos.mpr hl1') (sub_pos.mpr h1)
    have := mul_nonneg hl0 (sub_pos.mpr h2).le
    nlinarith
  · subst hl1'
    linarith

/-- **Clean diagonal.** If the ear triangle at `v` contains a vertex other than `v-1, v, v+1`,
then the farthest such vertex `w` gives a diagonal `(P v, P w)` met by no edge, and `P w - P v`
lies strictly inside the cone of the two edge vectors at `v`. -/
theorem u4h_exists_clean_invader [NeZero n] (hn : 4 ≤ n) {P : LabelledTuple n} (hP : Embedded P)
    (v : ZMod n) (hdet : det (P v - P (v - 1)) (P (v + 1) - P (v - 1)) ≠ 0)
    (hS : ∃ k, k ∈ u4h_Inv P v) :
    ∃ w, w ∈ u4h_Inv P v ∧
      (∀ k, Disjoint (edgeSegment P k) (openSegment ℝ (P v) (P w))) ∧
      (∃ α β : ℝ, 0 < α ∧ 0 < β ∧ P w - P v = α • (P (v - 1) - P v) + β • (P (v + 1) - P v)) := by
  classical
  obtain ⟨k0, hk0⟩ := hS
  obtain ⟨w, hw, hwmax⟩ := Finset.exists_max_image (Finset.univ.filter (· ∈ u4h_Inv P v))
    (fun k => u4h_height P v (P k)) ⟨k0, by simp [hk0]⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw hwmax
  obtain ⟨hw1, hw2, hw3, hwT⟩ := hw
  have hinj := u4h_vertex_injective hP
  -- the cone decomposition
  obtain ⟨la, lv, lc, hla, hlv, hlc, hsum, hPw⟩ := u4h_earHull_bary P v hwT
  have hcone : ∃ α β : ℝ, 0 < α ∧ 0 < β ∧
      P w - P v = α • (P (v - 1) - P v) + β • (P (v + 1) - P v) := by
    refine ⟨la, lc, ?_, ?_, ?_⟩
    · rcases hla.lt_or_eq with h | h
      · exact h
      · exfalso
        have hmem : P w ∈ edgeSegment P v := by
          rw [u4h_edgeSegment_eq_segment, hPw, ← h, zero_smul, zero_add]
          exact ⟨lv, lc, hlv, hlc, by linarith, rfl⟩
        rcases u4h_incident_of_vertex_mem hP hmem with h' | h'
        · exact hw2 h'
        · exact hw3 h'
    · rcases hlc.lt_or_eq with h | h
      · exact h
      · exfalso
        have hmem : P w ∈ edgeSegment P (v - 1) := by
          rw [u4h_edgeSegment_prev, hPw, ← h, zero_smul, add_zero]
          exact ⟨la, lv, hla, hlv, by linarith, rfl⟩
        rcases u4h_incident_of_vertex_mem hP hmem with h' | h'
        · exact hw1 h'
        · exact hw2 (by rw [h', sub_add_cancel])
    · rw [hPw]
      have hv' : lv = 1 - la - lc := by linarith
      rw [hv']; module
  refine ⟨w, ⟨hw1, hw2, hw3, hwT⟩, ?_, hcone⟩
  obtain ⟨α, β, hα, hβ, hcone'⟩ := hcone
  -- heights
  have hwlt : u4h_height P v (P w) < u4h_height P v (P v) := by
    obtain ⟨-, hle, heq⟩ := u4h_height_le P v hdet hwT
    exact lt_of_le_of_ne hle fun h => hw2 (hinj (heq h))
  have hwnn : 0 ≤ u4h_height P v (P w) := (u4h_height_le P v hdet hwT).1
  intro k
  rw [Set.disjoint_left]
  intro x hxk hxo
  rw [openSegment_eq_image] at hxo
  obtain ⟨t, ⟨ht0, ht1⟩, hxeq⟩ := hxo
  simp only at hxeq
  have hxh : u4h_height P v x = (1 - t) * u4h_height P v (P v) + t * u4h_height P v (P w) := by
    rw [← hxeq]; exact u4h_height_comb P v _ _ t
  have hxgt : u4h_height P v (P w) < u4h_height P v x := by rw [hxh]; nlinarith
  have hxpos : 0 < u4h_height P v x := by linarith
  have hvT : P v ∈ earHull P v := subset_convexHull ℝ _ (by simp)
  have hxT : x ∈ earHull P v := by
    rw [← hxeq]
    exact (convex_convexHull ℝ _) hvT hwT (by linarith) ht0.le (by ring)
  -- `k ∉ {v-1, v}`
  have hdetc : det (P (v + 1) - P v) (P w - P v) ≠ 0 := by
    rw [hcone', u4h_det_add_right, u4h_det_smul_right, u4h_det_smul_right, u4h_det_self,
      mul_zero, add_zero]
    have : det (P (v + 1) - P v) (P (v - 1) - P v) ≠ 0 := by
      have e : det (P (v + 1) - P v) (P (v - 1) - P v) =
          det (P v - P (v - 1)) (P (v + 1) - P (v - 1)) := by
        simp only [det, Prod.fst_sub, Prod.snd_sub]; ring
      rw [e]; exact hdet
    exact mul_ne_zero hα.ne' this
  have hdeta : det (P (v - 1) - P v) (P w - P v) ≠ 0 := by
    rw [hcone', u4h_det_add_right, u4h_det_smul_right, u4h_det_smul_right, u4h_det_self,
      mul_zero, zero_add]
    have : det (P (v - 1) - P v) (P (v + 1) - P v) ≠ 0 := by
      have e : det (P (v - 1) - P v) (P (v + 1) - P v) =
          -det (P v - P (v - 1)) (P (v + 1) - P (v - 1)) := by
        simp only [det, Prod.fst_sub, Prod.snd_sub]; ring
      rw [e]; exact neg_ne_zero.mpr hdet
    exact mul_ne_zero hβ.ne' this
  have hxv : x - P v = t • (P w - P v) := by rw [← hxeq]; module
  have hkv : k ≠ v := by
    rintro rfl
    rw [u4h_edgeSegment_eq_segment, u4h_mem_segment_iff_lin] at hxk
    obtain ⟨l, -, -, hl⟩ := hxk
    have : det (P (k + 1) - P k) (x - P k) = 0 := by
      rw [hl, add_sub_cancel_left, u4h_det_smul_right, u4h_det_self, mul_zero]
    rw [hxv, u4h_det_smul_right] at this
    rcases mul_eq_zero.mp this with h | h
    · exact ht0.ne' h
    · exact hdetc h
  have hkv1 : k ≠ v - 1 := by
    intro hk
    subst hk
    rw [u4h_edgeSegment_prev, segment_symm, u4h_mem_segment_iff_lin] at hxk
    obtain ⟨l, -, -, hl⟩ := hxk
    have : det (P (v - 1) - P v) (x - P v) = 0 := by
      rw [hl, add_sub_cancel_left, u4h_det_smul_right, u4h_det_self, mul_zero]
    rw [hxv, u4h_det_smul_right] at this
    rcases mul_eq_zero.mp this with h | h
    · exact ht0.ne' h
    · exact hdeta h
  -- both endpoints of `E_k` give lower points of the segment
  have hEk := u4h_edgeSegment_eq_segment P k
  have hside : ∀ e : Plane, e ∈ edgeSegment P k → (∃ j, P j = e) →
      ∃ z ∈ segment ℝ x e, z ≠ x ∧ u4h_height P v z < u4h_height P v x := by
    rintro e he ⟨j, rfl⟩
    by_cases heT : P j ∈ earHull P v
    · -- a vertex in the triangle: `v-1`, `v+1` or an invader
      have hj : u4h_height P v (P j) ≤ u4h_height P v (P w) := by
        by_cases hj1 : j = v - 1
        · subst hj1; rw [u4h_height_base P v (left_mem_segment ℝ _ _)]; exact hwnn
        by_cases hj3 : j = v + 1
        · subst hj3; rw [u4h_height_base P v (right_mem_segment ℝ _ _)]; exact hwnn
        by_cases hj2 : j = v
        · exfalso
          subst hj2
          rcases u4h_incident_of_vertex_mem hP he with h | h
          · exact hkv h.symm
          · exact hkv1 (by rw [h, add_sub_cancel_right])
        exact hwmax j ⟨hj1, hj2, hj3, heT⟩
      refine ⟨P j, right_mem_segment ℝ _ _, fun h => ?_, by linarith⟩
      rw [h] at hj; linarith
    · obtain ⟨z, hz, hzf⟩ := u4h_preconnected_inter_frontier (convex_segment x (P j)).isPreconnected
        ⟨x, left_mem_segment ℝ _ _, hxT⟩ ⟨P j, right_mem_segment ℝ _ _, heT⟩
      have hzk : z ∈ edgeSegment P k := by
        rw [hEk] at hxk he ⊢
        exact (convex_segment _ _).segment_subset hxk he hz
      have hz0 : u4h_height P v z = 0 := by
        rw [u4h_frontier_earHull P v hdet] at hzf
        rcases hzf with h | h
        · rcases u4h_edge_inter_ears hP hkv1 hkv ⟨hzk, h⟩ with h' | h'
          · rw [h']; exact u4h_height_base P v (left_mem_segment ℝ _ _)
          · rw [h']; exact u4h_height_base P v (right_mem_segment ℝ _ _)
        · exact u4h_height_base P v h
      refine ⟨z, hz, fun h => ?_, by rw [hz0]; exact hxpos⟩
      rw [h] at hz0; linarith
  rw [hEk] at hxk
  exact u4h_no_strict_max_on_segment P v hxk
    (hside (P k) (u4h_start_mem_edgeSegment P k) ⟨k, rfl⟩)
    (hside (P (k + 1)) (u4h_end_mem_edgeSegment P k) ⟨k + 1, rfl⟩)

end U4T_block

section U4U_block

/-! Splitting along a clean diagonal, part 1 (U4 helpers): the two chains and `U1 ∩ U2`. -/

theorem u4h_split_second_start [NeZero n] {m : ℕ} (hmn : m ≤ n) (i : ZMod n) :
    (i + (m : ZMod n)) + ((n - m : ℕ) : ZMod n) = i := by
  rw [add_assoc, ← Nat.cast_add, Nat.add_sub_cancel' hmn, ZMod.natCast_self, add_zero]

/-- Every index is `i + s` for a unique offset `s < n`. -/
theorem u4h_index_offset [NeZero n] (i k : ZMod n) : ∃ s : ℕ, s < n ∧ k = i + (s : ZMod n) :=
  ⟨(k - i).val, ZMod.val_lt _, by rw [ZMod.natCast_zmod_val]; ring⟩

theorem u4h_mem_polygonImage_iff_offset [NeZero n] (P : LabelledTuple n) (i : ZMod n) (x : Plane) :
    x ∈ embeddedPolygonImage P ↔ ∃ s : ℕ, s < n ∧ x ∈ edgeSegment P (i + (s : ZMod n)) := by
  constructor
  · intro hx
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hx
    obtain ⟨s, hs, rfl⟩ := u4h_index_offset i k
    exact ⟨s, hs, hk⟩
  · rintro ⟨s, -, hx⟩
    exact Set.mem_iUnion.mpr ⟨_, hx⟩

/-- Adjacency of `i + s` and `i + s'` for offsets `< n`, including the wrap-around. -/
theorem u4h_adjacent_offset' [NeZero n] {s s' : ℕ} (hs : s < n) (hs' : s' < n) (i : ZMod n)
    (h : adjacent (i + (s : ZMod n)) (i + (s' : ZMod n))) :
    s' = s + 1 ∨ s' = s ∨ s = s' + 1 ∨ (s = 0 ∧ s' + 1 = n) ∨ (s' = 0 ∧ s + 1 = n) := by
  have hn0 : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have key : ∀ x : ℤ, -(n : ℤ) ≤ x → x ≤ n → ((x : ℤ) : ZMod n) = 0 →
      x = 0 ∨ x = -n ∨ x = n := by
    intro x h1 h2 h0
    obtain ⟨c, hc⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd x n).mp h0
    have hc1 : c ≤ 1 := by
      by_contra hc'
      have : (2 : ℤ) ≤ c := by omega
      nlinarith
    have hc2 : -1 ≤ c := by
      by_contra hc'
      have : c ≤ -2 := by omega
      nlinarith
    interval_cases c
    · right; left; rw [hc]; ring
    · left; rw [hc]; ring
    · right; right; rw [hc]; ring
  rw [u4h_adjacent_iff] at h
  rcases h with h | h | h
  · have h' : (((s' : ℤ) - s + 1 : ℤ) : ZMod n) = 0 := by push_cast; linear_combination h
    rcases key _ (by omega) (by omega) h' with h'' | h'' | h'' <;> omega
  · have h' : (((s' : ℤ) - s : ℤ) : ZMod n) = 0 := by push_cast; linear_combination h
    rcases key _ (by omega) (by omega) h' with h'' | h'' | h'' <;> omega
  · have h' : (((s' : ℤ) - s - 1 : ℤ) : ZMod n) = 0 := by push_cast; linear_combination h
    rcases key _ (by omega) (by omega) h' with h'' | h'' | h'' <;> omega

/-- Edges of the two chains meet only at the diagonal endpoints. -/
theorem u4h_cross_chain_inter [NeZero n] {P : LabelledTuple n} (hP : Embedded P) (i : ZMod n)
    {m : ℕ} (hm : 2 ≤ m) (hmn : m + 2 ≤ n) {s s' : ℕ} (hs : s < m) (hs' : s' < n - m) :
    edgeSegment P (i + (s : ZMod n)) ∩ edgeSegment P (i + (m : ZMod n) + (s' : ZMod n)) ⊆
      {P i, P (i + (m : ZMod n))} := by
  rintro x ⟨hx1, hx2⟩
  have e2 : i + (m : ZMod n) + (s' : ZMod n) = i + ((m + s' : ℕ) : ZMod n) := by
    push_cast; ring
  rw [e2] at hx2
  by_cases hadj : adjacent (i + (s : ZMod n)) (i + ((m + s' : ℕ) : ZMod n))
  · rcases u4h_adjacent_offset' (by omega) (by omega) i hadj with h | h | h | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · -- `m + s' = s + 1`: `s = m - 1`, `s' = 0`, shared vertex `P (i + m)`
      have hs0 : s' = 0 := by omega
      have hsm : s + 1 = m := by omega
      have hc := hP.consecutive (i + (s : ZMod n))
      have hmem : x ∈ edgeSegment P (i + (s : ZMod n)) ∩ edgeSegment P (i + (s : ZMod n) + 1) := by
        refine ⟨hx1, ?_⟩
        rw [add_assoc, ← Nat.cast_add_one, hsm]
        rw [hs0, add_zero] at hx2
        exact hx2
      rw [hc] at hmem
      right
      rw [add_assoc, ← Nat.cast_add_one, hsm] at hmem
      exact hmem
    · omega
    · omega
    · -- `s = 0`, `m + s' = n - 1`: shared vertex `P i`
      have hc := hP.consecutive (i + ((m + s' : ℕ) : ZMod n))
      have hnext : i + ((m + s' : ℕ) : ZMod n) + 1 = i := by
        rw [add_assoc, ← Nat.cast_add_one, h2, ZMod.natCast_self, add_zero]
      rw [hnext] at hc
      have hmem : x ∈ edgeSegment P (i + ((m + s' : ℕ) : ZMod n)) ∩ edgeSegment P i := by
        refine ⟨hx2, ?_⟩
        rw [h1, Nat.cast_zero, add_zero] at hx1
        exact hx1
      rw [hc] at hmem
      left
      exact hmem
    · omega
  · exact (Set.disjoint_left.mp (hP.remote_disjoint _ _ hadj) hx1 hx2).elim

/-- Membership in the polygon image of the second sub-polygon. -/
theorem u4h_mem_polygonImage_subPoly2 [NeZero n] (P : LabelledTuple n) (i : ZMod n) {m : ℕ}
    (hmn : m ≤ n) (x : Plane) :
    x ∈ embeddedPolygonImage (u4h_subPoly P (i + (m : ZMod n)) (n - m)) ↔
      (∃ s : ℕ, s < n - m ∧ x ∈ edgeSegment P (i + (m : ZMod n) + (s : ZMod n))) ∨
        x ∈ segment ℝ (P i) (P (i + (m : ZMod n))) := by
  rw [u4h_mem_polygonImage_subPoly, u4h_split_second_start hmn]

/-- A point of the first chain off the diagonal endpoints avoids the second polygon image. -/
theorem u4h_chain1_avoid [NeZero n] {P : LabelledTuple n} (hP : Embedded P) (i : ZMod n) {m : ℕ}
    (hm : 2 ≤ m) (hmn : m + 2 ≤ n)
    (hclean : ∀ k, Disjoint (edgeSegment P k) (openSegment ℝ (P i) (P (i + (m : ZMod n)))))
    {s : ℕ} (hs : s < m) {x : Plane} (hx : x ∈ edgeSegment P (i + (s : ZMod n)))
    (hxe : x ∉ ({P i, P (i + (m : ZMod n))} : Set Plane)) :
    x ∉ embeddedPolygonImage (u4h_subPoly P (i + (m : ZMod n)) (n - m)) := by
  intro hmem
  rcases (u4h_mem_polygonImage_subPoly2 P i (by omega) x).mp hmem with ⟨s', hs', hx'⟩ | hD
  · exact hxe (u4h_cross_chain_inter hP i hm hmn hs hs' ⟨hx, hx'⟩)
  · rw [segment_symm] at hD
    rcases u4h_edge_inter_diag_subPoly hclean _ hx hD with h | h
    · exact hxe (Or.inl h)
    · exact hxe (Or.inr h)

/-- A point of the second chain off the diagonal endpoints avoids the first polygon image. -/
theorem u4h_chain2_avoid [NeZero n] {P : LabelledTuple n} (hP : Embedded P) (i : ZMod n) {m : ℕ}
    (hm : 2 ≤ m) (hmn : m + 2 ≤ n)
    (hclean : ∀ k, Disjoint (edgeSegment P k) (openSegment ℝ (P i) (P (i + (m : ZMod n)))))
    {s : ℕ} (hs : s < n - m) {x : Plane} (hx : x ∈ edgeSegment P (i + (m : ZMod n) + (s : ZMod n)))
    (hxe : x ∉ ({P i, P (i + (m : ZMod n))} : Set Plane)) :
    x ∉ embeddedPolygonImage (u4h_subPoly P i m) := by
  intro hmem
  rcases (u4h_mem_polygonImage_subPoly P i m x).mp hmem with ⟨s', hs', hx'⟩ | hD
  · exact hxe (u4h_cross_chain_inter hP i hm hmn hs' hs ⟨hx', hx⟩)
  · rcases u4h_edge_inter_diag_subPoly hclean _ hx hD with h | h
    · exact hxe (Or.inl h)
    · exact hxe (Or.inr h)

end U4U_block

section U4V_block

/-! Splitting along a clean diagonal, part 2 (U4 helpers): the chains lie outside the other
region, `U1 ∩ U2` is the diagonal, the faces at the diagonal lie on opposite sides. -/

/-- (V1) the first chain lies outside the second region. -/
theorem u4h_chain1_outside [NeZero n] {P : LabelledTuple n} (hP : Embedded P) (i : ZMod n)
    {m : ℕ} (hm : 2 ≤ m) (hmn : m + 2 ≤ n)
    (hclean : ∀ k, Disjoint (edgeSegment P k) (openSegment ℝ (P i) (P (i + (m : ZMod n)))))
    (R2 : u4h_Region (u4h_subPoly P (i + (m : ZMod n)) (n - m)))
    (X1 : ∃ s : ℕ, s < m ∧ ∃ x ∈ edgeSegment P (i + (s : ZMod n)),
      x ∉ ({P i, P (i + (m : ZMod n))} : Set Plane) ∧ x ∉ R2.U) :
    ∀ s : ℕ, s < m → ∀ x ∈ edgeSegment P (i + (s : ZMod n)),
      x ∉ ({P i, P (i + (m : ZMod n))} : Set Plane) → x ∉ R2.U := by
  have hside := u4h_chain_side hP (i := i) (m := m) hmn R2.isClosed (fun s hs x hx hxe => by
    rw [R2.frontier_eq]; exact u4h_chain1_avoid hP i hm hmn hclean hs hx hxe)
  rcases hside with h | h
  · exfalso
    obtain ⟨s, hs, x, hx, hxe, hxU⟩ := X1
    exact hxU (interior_subset (h s hs x hx hxe))
  · exact h

/-- (V2) the second chain lies outside the first region. -/
theorem u4h_chain2_outside [NeZero n] {P : LabelledTuple n} (hP : Embedded P) (i : ZMod n)
    {m : ℕ} (hm : 2 ≤ m) (hmn : m + 2 ≤ n)
    (hclean : ∀ k, Disjoint (edgeSegment P k) (openSegment ℝ (P i) (P (i + (m : ZMod n)))))
    (R1 : u4h_Region (u4h_subPoly P i m))
    (X2 : ∃ s : ℕ, s < n - m ∧ ∃ x ∈ edgeSegment P (i + (m : ZMod n) + (s : ZMod n)),
      x ∉ ({P i, P (i + (m : ZMod n))} : Set Plane) ∧ x ∉ R1.U) :
    ∀ s : ℕ, s < n - m → ∀ x ∈ edgeSegment P (i + (m : ZMod n) + (s : ZMod n)),
      x ∉ ({P i, P (i + (m : ZMod n))} : Set Plane) → x ∉ R1.U := by
  have hends : ({P (i + (m : ZMod n)), P (i + (m : ZMod n) + ((n - m : ℕ) : ZMod n))} : Set Plane)
      = {P i, P (i + (m : ZMod n))} := by
    rw [u4h_split_second_start (by omega), Set.pair_comm]
  have hside := u4h_chain_side hP (i := i + (m : ZMod n)) (m := n - m) (by omega) R1.isClosed
    (fun s hs x hx hxe => by
      rw [R1.frontier_eq]
      rw [hends] at hxe
      exact u4h_chain2_avoid hP i hm hmn hclean hs hx hxe)
  rcases hside with h | h
  · exfalso
    obtain ⟨s, hs, x, hx, hxe, hxU⟩ := X2
    rw [← hends] at hxe
    exact hxU (interior_subset (h s hs x hx hxe))
  · intro s hs x hx hxe
    rw [← hends] at hxe
    exact h s hs x hx hxe

/-- The diagonal lies in both regions. -/
theorem u4h_diag_subset_regions [NeZero n] {P : LabelledTuple n} (i : ZMod n) {m : ℕ}
    (hmn : m + 2 ≤ n) (R1 : u4h_Region (u4h_subPoly P i m))
    (R2 : u4h_Region (u4h_subPoly P (i + (m : ZMod n)) (n - m))) :
    segment ℝ (P i) (P (i + (m : ZMod n))) ⊆ R1.U ∧
      segment ℝ (P i) (P (i + (m : ZMod n))) ⊆ R2.U := by
  constructor
  · intro x hx
    have : x ∈ embeddedPolygonImage (u4h_subPoly P i m) := by
      rw [u4h_mem_polygonImage_subPoly]; right; rw [segment_symm]; exact hx
    rw [← R1.frontier_eq] at this
    exact R1.isClosed.frontier_subset this
  · intro x hx
    have : x ∈ embeddedPolygonImage (u4h_subPoly P (i + (m : ZMod n)) (n - m)) := by
      rw [u4h_mem_polygonImage_subPoly2 P i (by omega)]; right; exact hx
    rw [← R2.frontier_eq] at this
    exact R2.isClosed.frontier_subset this

/-- (V3) `U1 ∩ U2` is the diagonal. -/
theorem u4h_split_inter [NeZero n] {P : LabelledTuple n} (hP : Embedded P) (i : ZMod n)
    {m : ℕ} (hm : 2 ≤ m) (hmn : m + 2 ≤ n)
    (hclean : ∀ k, Disjoint (edgeSegment P k) (openSegment ℝ (P i) (P (i + (m : ZMod n)))))
    (R1 : u4h_Region (u4h_subPoly P i m))
    (R2 : u4h_Region (u4h_subPoly P (i + (m : ZMod n)) (n - m)))
    (X1 : ∃ s : ℕ, s < m ∧ ∃ x ∈ edgeSegment P (i + (s : ZMod n)),
      x ∉ ({P i, P (i + (m : ZMod n))} : Set Plane) ∧ x ∉ R2.U)
    (X2 : ∃ s : ℕ, s < n - m ∧ ∃ x ∈ edgeSegment P (i + (m : ZMod n) + (s : ZMod n)),
      x ∉ ({P i, P (i + (m : ZMod n))} : Set Plane) ∧ x ∉ R1.U) :
    R1.U ∩ R2.U = segment ℝ (P i) (P (i + (m : ZMod n))) := by
  have hout1 := u4h_chain1_outside hP i hm hmn hclean R2 X1
  have hout2 := u4h_chain2_outside hP i hm hmn hclean R1 X2
  obtain ⟨hD1, hD2⟩ := u4h_diag_subset_regions i hmn R1 R2
  have hendsD : ∀ x ∈ ({P i, P (i + (m : ZMod n))} : Set Plane),
      x ∈ segment ℝ (P i) (P (i + (m : ZMod n))) := by
    rintro x (rfl | rfl)
    · exact left_mem_segment ℝ _ _
    · exact right_mem_segment ℝ _ _
  apply Set.Subset.antisymm
  · rintro x ⟨hx1, hx2⟩
    by_contra hxD
    -- `x` is interior to both regions
    have hxi1 : x ∈ interior R1.U := by
      by_contra h
      have hxf : x ∈ frontier R1.U := ⟨subset_closure hx1, h⟩
      rw [R1.frontier_eq, u4h_mem_polygonImage_subPoly] at hxf
      rcases hxf with ⟨s, hs, hx⟩ | hD
      · have hxe : x ∉ ({P i, P (i + (m : ZMod n))} : Set Plane) := fun h => hxD (hendsD x h)
        exact hout1 s hs x hx hxe hx2
      · rw [segment_symm] at hD; exact hxD hD
    have hxi2 : x ∈ interior R2.U := by
      by_contra h
      have hxf : x ∈ frontier R2.U := ⟨subset_closure hx2, h⟩
      rw [R2.frontier_eq, u4h_mem_polygonImage_subPoly2 P i (by omega)] at hxf
      rcases hxf with ⟨s, hs, hx⟩ | hD
      · have hxe : x ∉ ({P i, P (i + (m : ZMod n))} : Set Plane) := fun h => hxD (hendsD x h)
        exact hout2 s hs x hx hxe hx1
      · exact hxD hD
    -- `interior U1 ⊆ interior U2 ∪ U2ᶜ`
    have hsub : interior R1.U ⊆ interior R2.U ∪ R2.Uᶜ := by
      intro y hy
      by_cases hy2 : y ∈ R2.U
      · left
        by_contra hyi
        have hyf : y ∈ frontier R2.U := ⟨subset_closure hy2, hyi⟩
        rw [R2.frontier_eq, u4h_mem_polygonImage_subPoly2 P i (by omega)] at hyf
        have hy1 : y ∉ frontier R1.U := disjoint_interior_frontier.notMem_of_mem_left hy
        rcases hyf with ⟨s, hs, hyE⟩ | hD
        · have hye : y ∉ ({P i, P (i + (m : ZMod n))} : Set Plane) := by
            intro h
            apply hy1
            rw [R1.frontier_eq, u4h_mem_polygonImage_subPoly]
            right; rw [segment_symm]; exact hendsD y h
          exact hout2 s hs y hyE hye (interior_subset hy)
        · apply hy1
          rw [R1.frontier_eq, u4h_mem_polygonImage_subPoly]
          right; rw [segment_symm]; exact hD
      · right; exact hy2
    rcases IsPreconnected.subset_or_subset isOpen_interior R2.isClosed.isOpen_compl
        (Set.disjoint_left.mpr fun y hy hy' => hy' (interior_subset hy)) hsub R1.int_conn
        with h | h
    · -- `U1 ⊆ U2`, contradicting `X1`
      have hU : R1.U ⊆ R2.U := by
        rw [← u4h_triangulation_closure_interior R1.K]
        exact (closure_mono h).trans
          (closure_minimal interior_subset R2.isClosed)
      obtain ⟨s, hs, y, hy, -, hyU⟩ := X1
      apply hyU
      apply hU
      have : y ∈ embeddedPolygonImage (u4h_subPoly P i m) := by
        rw [u4h_mem_polygonImage_subPoly]; exact Or.inl ⟨s, hs, hy⟩
      rw [← R1.frontier_eq] at this
      exact R1.isClosed.frontier_subset this
    · exact h hxi1 hx2
  · intro x hx
    exact ⟨hD1 hx, hD2 hx⟩

/-- (V5) Half-disc lemma at an inner point of a face edge, in terms of the directed edge
`e1 → e2` and the apex. -/
theorem u4h_face_halfdisc (F : Triangle) (k : Fin 3) {e1 e2 : Plane}
    (hFk : F.edgeSeg k = segment ℝ e1 e2) {x : Plane} (hx : x ∈ openSegment ℝ e1 e2) :
    ∃ ε > 0, ∀ y, dist y x < ε →
      (y ∈ F.carrier ↔ 0 ≤ det (e2 - e1) (F.v (k + 2) - e1) * det (e2 - e1) (y - e1)) := by
  have hD : 0 < det (F.v (k + 2) - F.v (k + 1)) (F.v k - F.v (k + 1)) := by
    rw [u4h_det_rot1]; exact u4h_tri_pos F k
  have hcar : F.carrier = convexHull ℝ {F.v (k + 1), F.v (k + 2), F.v k} := by
    rw [u4h_tri_carrier_rot F k, u4h_hull3_rot]
  rcases u4h_face_edge_ends F k hFk with ⟨h0, h1⟩ | ⟨h0, h1⟩
  · have hx' : x ∈ openSegment ℝ (F.v k) (F.v (k + 1)) := by rw [h0, h1]; exact hx
    obtain ⟨ε, hε, hball⟩ := u4h_halfdisc hD hx'
    refine ⟨ε, hε, fun y hy => ?_⟩
    rw [hcar, hball y hy, h0, h1]
    have hpos : 0 < det (e2 - e1) (F.v (k + 2) - e1) := by
      rw [← h0, ← h1]; exact u4h_tri_pos F k
    constructor
    · intro h; exact mul_nonneg hpos.le h
    · intro h; exact nonneg_of_mul_nonneg_right h hpos |> fun h' => by
        nlinarith
  · have hx' : x ∈ openSegment ℝ (F.v k) (F.v (k + 1)) := by
      rw [h0, h1, openSegment_symm]; exact hx
    obtain ⟨ε, hε, hball⟩ := u4h_halfdisc hD hx'
    refine ⟨ε, hε, fun y hy => ?_⟩
    rw [hcar, hball y hy, h0, h1]
    have hpos : 0 < det (e1 - e2) (F.v (k + 2) - e2) := by
      rw [← h0, ← h1]; exact u4h_tri_pos F k
    have e1' : det (e1 - e2) (y - e2) = -det (e2 - e1) (y - e1) := by
      simp only [det, Prod.fst_sub, Prod.snd_sub]; ring
    have e2' : det (e2 - e1) (F.v (k + 2) - e1) = -det (e1 - e2) (F.v (k + 2) - e2) := by
      simp only [det, Prod.fst_sub, Prod.snd_sub]; ring
    rw [e1', e2']
    constructor
    · intro h; nlinarith
    · intro h; nlinarith

end U4V_block

section U4W_block

/-! Splitting along a clean diagonal, part 3 (U4 helpers): opposite sides at the diagonal, the
open diagonal is interior to the union, frontier and interior of the union. -/

/-- The apex of a face is off the line of any of its edges (signed). -/
theorem u4h_apex_det_ne_zero (F : Triangle) (k : Fin 3) {e1 e2 : Plane}
    (hFk : F.edgeSeg k = segment ℝ e1 e2) : det (e2 - e1) (F.v (k + 2) - e1) ≠ 0 := by
  rcases u4h_face_edge_ends F k hFk with ⟨h0, h1⟩ | ⟨h0, h1⟩
  · rw [← h0, ← h1]; exact (u4h_tri_pos F k).ne'
  · have e : det (e2 - e1) (F.v (k + 2) - e1) = -det (e1 - e2) (F.v (k + 2) - e2) := by
      simp only [det, Prod.fst_sub, Prod.snd_sub]; ring
    rw [e, ← h0, ← h1]; exact neg_ne_zero.mpr (u4h_tri_pos F k).ne'

theorem u4h_midpoint_mem_openSegment (e1 e2 : Plane) :
    (1 / 2 : ℝ) • e1 + (1 / 2 : ℝ) • e2 ∈ openSegment ℝ e1 e2 :=
  ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, rfl⟩

/-- (V6) Two faces of the two regions at the common diagonal lie on opposite sides. -/
theorem u4h_split_opposite {U1 U2 : Set Plane} {e1 e2 : Plane}
    (hinter : U1 ∩ U2 = segment ℝ e1 e2) {F1 F2 : Triangle} (hF1U : F1.carrier ⊆ U1)
    (hF2U : F2.carrier ⊆ U2) {k1 k2 : Fin 3} (hk1 : F1.edgeSeg k1 = segment ℝ e1 e2)
    (hk2 : F2.edgeSeg k2 = segment ℝ e1 e2) :
    det (e2 - e1) (F1.v (k1 + 2) - e1) * det (e2 - e1) (F2.v (k2 + 2) - e1) < 0 := by
  set s1 := det (e2 - e1) (F1.v (k1 + 2) - e1) with hs1
  set s2 := det (e2 - e1) (F2.v (k2 + 2) - e1) with hs2
  have hs1ne : s1 ≠ 0 := u4h_apex_det_ne_zero F1 k1 hk1
  have hs2ne : s2 ≠ 0 := u4h_apex_det_ne_zero F2 k2 hk2
  by_contra hcon
  have hpos : 0 < s1 * s2 := lt_of_le_of_ne (not_lt.mp hcon) (Ne.symm (mul_ne_zero hs1ne hs2ne))
  set x : Plane := (1 / 2 : ℝ) • e1 + (1 / 2 : ℝ) • e2 with hx
  have hxo : x ∈ openSegment ℝ e1 e2 := u4h_midpoint_mem_openSegment _ _
  obtain ⟨ε1, hε1, h1⟩ := u4h_face_halfdisc F1 k1 hk1 hxo
  obtain ⟨ε2, hε2, h2⟩ := u4h_face_halfdisc F2 k2 hk2 hxo
  set w := F1.v (k1 + 2) - e1 with hw
  set η : ℝ := min ε1 ε2 / (2 * (‖w‖ + 1)) with hη
  have hηpos : 0 < η := by positivity
  set y := x + η • w with hy
  have hdist : dist y x < min ε1 ε2 := by
    rw [hy, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hηpos, hη,
      div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith [norm_nonneg w, lt_min hε1 hε2]
  have hdet : det (e2 - e1) (y - e1) = η * s1 := by
    rw [hy, hx]
    simp only [hs1, det, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
      Prod.smul_snd, smul_eq_mul, hw]; ring
  have hy1 : y ∈ F1.carrier := by
    rw [h1 y (lt_of_lt_of_le hdist (min_le_left _ _)), hdet]
    nlinarith [mul_self_nonneg s1]
  have hy2 : y ∈ F2.carrier := by
    rw [h2 y (lt_of_lt_of_le hdist (min_le_right _ _)), hdet]
    nlinarith
  have hyD : y ∈ segment ℝ e1 e2 := by rw [← hinter]; exact ⟨hF1U hy1, hF2U hy2⟩
  have := u4h_det_segment_zero hyD
  rw [hdet] at this
  rcases mul_eq_zero.mp this with h | h
  · exact hηpos.ne' h
  · exact hs1ne h

/-- (V8) The open diagonal is interior to the union of the two regions. -/
theorem u4h_split_openDiag_interior {U1 U2 : Set Plane} {e1 e2 : Plane}
    (hinter : U1 ∩ U2 = segment ℝ e1 e2) {F1 F2 : Triangle} (hF1U : F1.carrier ⊆ U1)
    (hF2U : F2.carrier ⊆ U2) {k1 k2 : Fin 3} (hk1 : F1.edgeSeg k1 = segment ℝ e1 e2)
    (hk2 : F2.edgeSeg k2 = segment ℝ e1 e2) :
    openSegment ℝ e1 e2 ⊆ interior (U1 ∪ U2) := by
  intro x hx
  have hopp := u4h_split_opposite hinter hF1U hF2U hk1 hk2
  obtain ⟨ε1, hε1, h1⟩ := u4h_face_halfdisc F1 k1 hk1 hx
  obtain ⟨ε2, hε2, h2⟩ := u4h_face_halfdisc F2 k2 hk2 hx
  rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff]
  refine ⟨min ε1 ε2, lt_min hε1 hε2, fun y hy => ?_⟩
  rw [Metric.mem_ball] at hy
  by_cases hside : 0 ≤ det (e2 - e1) (F1.v (k1 + 2) - e1) * det (e2 - e1) (y - e1)
  · left
    exact hF1U ((h1 y (lt_of_lt_of_le hy (min_le_left _ _))).mpr hside)
  · right
    apply hF2U
    rw [h2 y (lt_of_lt_of_le hy (min_le_right _ _))]
    have hside' := not_le.mp hside
    nlinarith [mul_self_nonneg (det (e2 - e1) (F1.v (k1 + 2) - e1))]

/-- The frontier of a union lies in the union of the frontiers. -/
theorem u4h_frontier_union_subset {α : Type*} [TopologicalSpace α] (s t : Set α) :
    frontier (s ∪ t) ⊆ frontier s ∪ frontier t := by
  intro x hx
  rw [frontier, closure_union] at hx
  obtain ⟨hcl, hint⟩ := hx
  rcases hcl with h | h
  · exact Or.inl ⟨h, fun h' => hint (interior_mono Set.subset_union_left h')⟩
  · exact Or.inr ⟨h, fun h' => hint (interior_mono Set.subset_union_right h')⟩

/-- The midpoint of an edge is not a vertex. -/
theorem u4h_midpoint_not_vertex {P : LabelledTuple n} (hP : Embedded P) (k : ZMod n) :
    (1 / 2 : ℝ) • P k + (1 / 2 : ℝ) • P (k + 1) ∈ edgeSegment P k ∧
      ∀ j, P j ≠ (1 / 2 : ℝ) • P k + (1 / 2 : ℝ) • P (k + 1) := by
  have hne : P k ≠ P (k + 1) := fun h => hP.edge_ne_zero k (by rw [edge, ← h, sub_self])
  have hmem : (1 / 2 : ℝ) • P k + (1 / 2 : ℝ) • P (k + 1) ∈ edgeSegment P k := by
    rw [u4h_edgeSegment_eq_segment]
    exact openSegment_subset_segment ℝ _ _ (u4h_midpoint_mem_openSegment _ _)
  refine ⟨hmem, fun j hj => ?_⟩
  have hjmem : P j ∈ edgeSegment P k := hj ▸ hmem
  have hno := u4h_midpoint_mem_openSegment (P k) (P (k + 1))
  rw [← hj] at hno
  rcases u4h_incident_of_vertex_mem hP hjmem with h | h
  · rw [h] at hno; exact hne (left_mem_openSegment_iff.mp hno)
  · rw [h] at hno; exact hne (right_mem_openSegment_iff.mp hno)

/-- If all non-vertex points of an edge avoid `interior U`, so do all its points (approach a
vertex along the edge). -/
theorem u4h_edge_not_interior {P : LabelledTuple n} (hP : Embedded P) (k : ZMod n) {U : Set Plane}
    {S : Set Plane} (hS : ∀ x ∈ S, ∃ j, P j = x)
    (hA : ∀ y ∈ edgeSegment P k, y ∉ S → y ∉ interior U) {z : Plane} (hz : z ∈ edgeSegment P k) :
    z ∉ interior U := by
  intro hint
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (isOpen_interior.mem_nhds hint)
  have hw0 : P (k + 1) - P k ≠ 0 := hP.edge_ne_zero k
  rw [u4h_edgeSegment_eq_segment, u4h_mem_segment_iff_lin] at hz
  obtain ⟨l, hl0, hl1, rfl⟩ := hz
  set w := P (k + 1) - P k with hw
  set δ : ℝ := min (1 / 4) (ε / (2 * (‖w‖ + 1))) with hδ
  have hδ0 : 0 < δ := lt_min (by norm_num) (by positivity)
  have hδ1 : δ ≤ 1 / 4 := min_le_left _ _
  have hδε : δ * ‖w‖ < ε := by
    have h1 : δ ≤ ε / (2 * (‖w‖ + 1)) := min_le_right _ _
    have h2 : δ * ‖w‖ ≤ ε / (2 * (‖w‖ + 1)) * ‖w‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
    have h3 : ε / (2 * (‖w‖ + 1)) * ‖w‖ < ε := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]; nlinarith [norm_nonneg w]
    linarith
  -- a nearby parameter strictly inside `(0, 1)`
  obtain ⟨l', hl'0, hl'1, hl'd⟩ : ∃ l' : ℝ, 0 < l' ∧ l' < 1 ∧ |l' - l| ≤ δ := by
    by_cases hl : l ≤ 1 / 2
    · exact ⟨l + δ, by linarith, by linarith, by rw [add_sub_cancel_left, abs_of_pos hδ0]⟩
    · exact ⟨l - δ, by linarith, by linarith, by
        rw [sub_sub_cancel_left, abs_neg, abs_of_pos hδ0]⟩
  set y := P k + l' • w with hy
  have hymem : y ∈ edgeSegment P k := by
    rw [u4h_edgeSegment_eq_segment]; exact u4h_lin_mem_segment _ _ hl'0.le hl'1.le
  have hynot : y ∉ S := by
    intro hyS
    obtain ⟨j, hj⟩ := hS y hyS
    have hjmem : P j ∈ edgeSegment P k := hj ▸ hymem
    rcases u4h_incident_of_vertex_mem hP hjmem with h | h
    · rw [h] at hj
      have : l' • w = 0 := add_eq_left.mp hj.symm
      rcases smul_eq_zero.mp this with h' | h'
      · exact hl'0.ne' h'
      · exact hw0 h'
    · rw [h] at hj
      have e : P (k + 1) = P k + (1 : ℝ) • w := by rw [one_smul, hw]; abel
      rw [e] at hj
      have := smul_left_injective ℝ hw0 (add_left_cancel hj)
      linarith
  have hdist : dist y (P k + l • w) < ε := by
    rw [hy, dist_eq_norm]
    have e : P k + l' • w - (P k + l • w) = (l' - l) • w := by module
    rw [e, norm_smul, Real.norm_eq_abs]
    calc |l' - l| * ‖w‖ ≤ δ * ‖w‖ := mul_le_mul_of_nonneg_right hl'd (norm_nonneg _)
      _ < ε := hδε
  exact hA y hymem hynot (hball (Metric.mem_ball.mpr hdist))

end U4W_block

section U4X_block

/-! Splitting along a clean diagonal, part 4 (U4 helpers): the split context and the
frontier / interior / side facts of the union. -/

/-- All data of a split of `P` along the clean diagonal `P i — P (i+m)`. -/
structure u4h_SplitCtx [NeZero n] (P : LabelledTuple n) (i : ZMod n) (m : ℕ) where
  hP : Embedded P
  hm : 2 ≤ m
  hmn : m + 2 ≤ n
  hclean : ∀ k, Disjoint (edgeSegment P k) (openSegment ℝ (P i) (P (i + (m : ZMod n))))
  R1 : u4h_Region (u4h_subPoly P i m)
  R2 : u4h_Region (u4h_subPoly P (i + (m : ZMod n)) (n - m))
  X1 : ∃ s : ℕ, s < m ∧ ∃ x ∈ edgeSegment P (i + (s : ZMod n)),
    x ∉ ({P i, P (i + (m : ZMod n))} : Set Plane) ∧ x ∉ R2.U
  X2 : ∃ s : ℕ, s < n - m ∧ ∃ x ∈ edgeSegment P (i + (m : ZMod n) + (s : ZMod n)),
    x ∉ ({P i, P (i + (m : ZMod n))} : Set Plane) ∧ x ∉ R1.U

theorem u4h_ends_mem_polygonImage (P : LabelledTuple n) (i : ZMod n) (m : ℕ) :
    ∀ x ∈ ({P i, P (i + (m : ZMod n))} : Set Plane), x ∈ embeddedPolygonImage P := by
  rintro x (rfl | rfl) <;> exact u4h_vertex_mem_polygonImage P _

/-- Offsets `≥ m` are second-chain offsets. -/
theorem u4h_offset_split (i : ZMod n) {m s : ℕ} (hs : s < n) (hsm : m ≤ s) :
    i + (s : ZMod n) = i + (m : ZMod n) + ((s - m : ℕ) : ZMod n) ∧ s - m < n - m := by
  constructor
  · rw [add_assoc, ← Nat.cast_add, Nat.add_sub_cancel' hsm]
  · omega

namespace u4h_SplitCtx

variable [NeZero n] {P : LabelledTuple n} {i : ZMod n} {m : ℕ} (C : u4h_SplitCtx P i m)

include C in
theorem hne : P i ≠ P (i + (m : ZMod n)) := by
  intro h
  have := u4h_vertex_injective C.hP h
  exact u4h_natCast_ne_zero (n := n) (k := m) (by have := C.hm; omega) (by have := C.hmn; omega)
    (by linear_combination -this)

theorem inter : C.R1.U ∩ C.R2.U = segment ℝ (P i) (P (i + (m : ZMod n))) :=
  u4h_split_inter C.hP i C.hm C.hmn C.hclean C.R1 C.R2 C.X1 C.X2

theorem out1 : ∀ s : ℕ, s < m → ∀ x ∈ edgeSegment P (i + (s : ZMod n)),
    x ∉ ({P i, P (i + (m : ZMod n))} : Set Plane) → x ∉ C.R2.U :=
  u4h_chain1_outside C.hP i C.hm C.hmn C.hclean C.R2 C.X1

theorem out2 : ∀ s : ℕ, s < n - m → ∀ x ∈ edgeSegment P (i + (m : ZMod n) + (s : ZMod n)),
    x ∉ ({P i, P (i + (m : ZMod n))} : Set Plane) → x ∉ C.R1.U :=
  u4h_chain2_outside C.hP i C.hm C.hmn C.hclean C.R1 C.X2

theorem faces1 : ∃ F1 ∈ C.R1.K.faces, ∃ k1 : Fin 3,
    F1.edgeSeg k1 = segment ℝ (P i) (P (i + (m : ZMod n))) := by
  obtain ⟨F1, hF1, k1, hk1⟩ := C.R1.edge_face (-1)
  rw [u4h_subPoly_edgeSegment_last, segment_symm] at hk1
  exact ⟨F1, hF1, k1, hk1⟩

theorem faces2 : ∃ F2 ∈ C.R2.K.faces, ∃ k2 : Fin 3,
    F2.edgeSeg k2 = segment ℝ (P i) (P (i + (m : ZMod n))) := by
  obtain ⟨F2, hF2, k2, hk2⟩ := C.R2.edge_face (-1)
  rw [u4h_subPoly_edgeSegment_last, u4h_split_second_start (by have := C.hmn; omega)] at hk2
  exact ⟨F2, hF2, k2, hk2⟩

/-- The open diagonal is interior to the union. -/
theorem openDiag_interior :
    openSegment ℝ (P i) (P (i + (m : ZMod n))) ⊆ interior (C.R1.U ∪ C.R2.U) := by
  obtain ⟨F1, hF1, k1, hk1⟩ := C.faces1
  obtain ⟨F2, hF2, k2, hk2⟩ := C.faces2
  exact u4h_split_openDiag_interior C.inter (C.R1.face_subset hF1) (C.R2.face_subset hF2) hk1 hk2

/-- Points of the first chain off the ends are not interior to the union. -/
theorem chain1_not_interior {s : ℕ} (hs : s < m) {y : Plane}
    (hy : y ∈ edgeSegment P (i + (s : ZMod n)))
    (hye : y ∉ ({P i, P (i + (m : ZMod n))} : Set Plane)) :
    y ∉ interior (C.R1.U ∪ C.R2.U) := by
  intro hint
  have hy1 : y ∈ frontier C.R1.U := by
    rw [C.R1.frontier_eq, u4h_mem_polygonImage_subPoly]; exact Or.inl ⟨s, hs, hy⟩
  have hy2 : y ∉ C.R2.U := C.out1 s hs y hy hye
  have h1 : C.R1.U ∪ C.R2.U ∈ nhds y := mem_interior_iff_mem_nhds.mp hint
  have h2 : C.R2.Uᶜ ∈ nhds y := C.R2.isClosed.isOpen_compl.mem_nhds hy2
  have h3 : C.R1.U ∈ nhds y := by
    apply Filter.mem_of_superset (Filter.inter_mem h1 h2)
    rintro z ⟨hz | hz, hz'⟩
    · exact hz
    · exact absurd hz hz'
  exact disjoint_interior_frontier.notMem_of_mem_left (mem_interior_iff_mem_nhds.mpr h3) hy1

theorem chain2_not_interior {s : ℕ} (hs : s < n - m) {y : Plane}
    (hy : y ∈ edgeSegment P (i + (m : ZMod n) + (s : ZMod n)))
    (hye : y ∉ ({P i, P (i + (m : ZMod n))} : Set Plane)) :
    y ∉ interior (C.R1.U ∪ C.R2.U) := by
  intro hint
  have hy2 : y ∈ frontier C.R2.U := by
    rw [C.R2.frontier_eq, u4h_mem_polygonImage_subPoly2 P i (by have := C.hmn; omega)]
    exact Or.inl ⟨s, hs, hy⟩
  have hy1 : y ∉ C.R1.U := C.out2 s hs y hy hye
  have h1 : C.R1.U ∪ C.R2.U ∈ nhds y := mem_interior_iff_mem_nhds.mp hint
  have h2 : C.R1.Uᶜ ∈ nhds y := C.R1.isClosed.isOpen_compl.mem_nhds hy1
  have h3 : C.R2.U ∈ nhds y := by
    apply Filter.mem_of_superset (Filter.inter_mem h1 h2)
    rintro z ⟨hz | hz, hz'⟩
    · exact absurd hz hz'
    · exact hz
  exact disjoint_interior_frontier.notMem_of_mem_left (mem_interior_iff_mem_nhds.mpr h3) hy2

/-- (X-a) The frontier of the union is the polygon image. -/
theorem frontier_eq : frontier (C.R1.U ∪ C.R2.U) = embeddedPolygonImage P := by
  have hmn := C.hmn
  have hends := u4h_ends_mem_polygonImage P i m
  apply Set.Subset.antisymm
  · intro x hx
    have hxi : x ∉ interior (C.R1.U ∪ C.R2.U) :=
      disjoint_interior_frontier.notMem_of_mem_right hx
    rcases u4h_frontier_union_subset _ _ hx with h | h
    · rw [C.R1.frontier_eq, u4h_mem_polygonImage_subPoly] at h
      rcases h with ⟨s, -, hxs⟩ | hD
      · exact u4h_edgeSegment_subset_polygonImage P _ hxs
      · rw [segment_symm, ← insert_endpoints_openSegment] at hD
        rcases hD with h | h | h
        · exact h ▸ hends _ (Or.inl rfl)
        · exact h ▸ hends _ (Or.inr rfl)
        · exact absurd (C.openDiag_interior h) hxi
    · rw [C.R2.frontier_eq, u4h_mem_polygonImage_subPoly2 P i (by omega)] at h
      rcases h with ⟨s, -, hxs⟩ | hD
      · exact u4h_edgeSegment_subset_polygonImage P _ hxs
      · rw [← insert_endpoints_openSegment] at hD
        rcases hD with h | h | h
        · exact h ▸ hends _ (Or.inl rfl)
        · exact h ▸ hends _ (Or.inr rfl)
        · exact absurd (C.openDiag_interior h) hxi
  · intro z hz
    obtain ⟨s, hs, hzs⟩ := (u4h_mem_polygonImage_iff_offset P i z).mp hz
    have hSv : ∀ x ∈ ({P i, P (i + (m : ZMod n))} : Set Plane), ∃ j, P j = x := by
      rintro x (rfl | rfl)
      · exact ⟨i, rfl⟩
      · exact ⟨_, rfl⟩
    by_cases hsm : s < m
    · refine ⟨subset_closure (Or.inl ?_), ?_⟩
      · have : z ∈ embeddedPolygonImage (u4h_subPoly P i m) := by
          rw [u4h_mem_polygonImage_subPoly]; exact Or.inl ⟨s, hsm, hzs⟩
        rw [← C.R1.frontier_eq] at this
        exact C.R1.isClosed.frontier_subset this
      · exact u4h_edge_not_interior C.hP _ hSv
          (fun y hy hye => C.chain1_not_interior hsm hy hye) hzs
    · obtain ⟨heq, hs'⟩ := u4h_offset_split i hs (not_lt.mp hsm)
      rw [heq] at hzs
      refine ⟨subset_closure (Or.inr ?_), ?_⟩
      · have : z ∈ embeddedPolygonImage (u4h_subPoly P (i + (m : ZMod n)) (n - m)) := by
          rw [u4h_mem_polygonImage_subPoly2 P i (by omega)]; exact Or.inl ⟨_, hs', hzs⟩
        rw [← C.R2.frontier_eq] at this
        exact C.R2.isClosed.frontier_subset this
      · exact u4h_edge_not_interior C.hP _ hSv
          (fun y hy hye => C.chain2_not_interior hs' hy hye) hzs

/-- (X-e) The interior of the union is preconnected. -/
theorem int_conn : IsPreconnected (interior (C.R1.U ∪ C.R2.U)) := by
  have hmn := C.hmn
  obtain ⟨F1, hF1, k1, hk1⟩ := C.faces1
  obtain ⟨F2, hF2, k2, hk2⟩ := C.faces2
  set O := openSegment ℝ (P i) (P (i + (m : ZMod n))) with hO
  have hOsub : ∀ (F : Triangle) (k : Fin 3), F.edgeSeg k = segment ℝ (P i) (P (i + (m : ZMod n))) →
      O ⊆ closure (interior F.carrier) := by
    intro F k hk x hx
    have hconv : Convex ℝ F.carrier := convex_convexHull ℝ _
    rw [hconv.closure_interior_eq_closure_of_nonempty_interior (u4h_tri_interior_nonempty F)]
    apply subset_closure
    apply u4h_tri_edgeSeg_subset F k
    rw [hk]; exact openSegment_subset_segment ℝ _ _ hx
  have hA : IsPreconnected (interior C.R1.U ∪ O) := by
    apply IsPreconnected.subset_closure C.R1.int_conn Set.subset_union_left
    rintro x (hx | hx)
    · exact subset_closure hx
    · exact closure_mono (interior_mono (C.R1.face_subset hF1)) (hOsub F1 k1 hk1 hx)
  have hB : IsPreconnected (interior C.R2.U ∪ O) := by
    apply IsPreconnected.subset_closure C.R2.int_conn Set.subset_union_left
    rintro x (hx | hx)
    · exact subset_closure hx
    · exact closure_mono (interior_mono (C.R2.face_subset hF2)) (hOsub F2 k2 hk2 hx)
  have hAB : IsPreconnected ((interior C.R1.U ∪ O) ∪ (interior C.R2.U ∪ O)) := by
    apply IsPreconnected.union' _ hA hB
    exact ⟨_, Or.inr (u4h_midpoint_mem_openSegment _ _), Or.inr (u4h_midpoint_mem_openSegment _ _)⟩
  have heq : interior (C.R1.U ∪ C.R2.U) = (interior C.R1.U ∪ O) ∪ (interior C.R2.U ∪ O) := by
    apply Set.Subset.antisymm
    · intro y hy
      have hyfr : y ∉ frontier (C.R1.U ∪ C.R2.U) :=
        disjoint_interior_frontier.notMem_of_mem_left hy
      rw [C.frontier_eq] at hyfr
      rcases interior_subset hy with hy1 | hy2
      · by_cases hyi : y ∈ interior C.R1.U
        · exact Or.inl (Or.inl hyi)
        · have hyf : y ∈ frontier C.R1.U := ⟨subset_closure hy1, hyi⟩
          rw [C.R1.frontier_eq, u4h_mem_polygonImage_subPoly] at hyf
          rcases hyf with ⟨s, -, hys⟩ | hD
          · exact absurd (u4h_edgeSegment_subset_polygonImage P _ hys) hyfr
          · rw [segment_symm, ← insert_endpoints_openSegment] at hD
            rcases hD with h | h | h
            · exact absurd (h ▸ u4h_ends_mem_polygonImage P i m _ (Or.inl rfl)) hyfr
            · exact absurd (h ▸ u4h_ends_mem_polygonImage P i m _ (Or.inr rfl)) hyfr
            · exact Or.inl (Or.inr h)
      · by_cases hyi : y ∈ interior C.R2.U
        · exact Or.inr (Or.inl hyi)
        · have hyf : y ∈ frontier C.R2.U := ⟨subset_closure hy2, hyi⟩
          rw [C.R2.frontier_eq, u4h_mem_polygonImage_subPoly2 P i (by omega)] at hyf
          rcases hyf with ⟨s, -, hys⟩ | hD
          · exact absurd (u4h_edgeSegment_subset_polygonImage P _ hys) hyfr
          · rw [← insert_endpoints_openSegment] at hD
            rcases hD with h | h | h
            · exact absurd (h ▸ u4h_ends_mem_polygonImage P i m _ (Or.inl rfl)) hyfr
            · exact absurd (h ▸ u4h_ends_mem_polygonImage P i m _ (Or.inr rfl)) hyfr
            · exact Or.inr (Or.inr h)
    · rintro y ((hy | hy) | (hy | hy))
      · exact interior_mono Set.subset_union_left hy
      · exact C.openDiag_interior hy
      · exact interior_mono Set.subset_union_right hy
      · exact C.openDiag_interior hy
  rw [heq]
  exact hAB

end u4h_SplitCtx

end U4X_block

section U4Y_block

/-! Splitting along a clean diagonal, part 5 (U4 helpers): the glued region. -/

namespace u4h_SplitCtx

variable [NeZero n] {P : LabelledTuple n} {i : ZMod n} {m : ℕ} (C : u4h_SplitCtx P i m)

/-- No face of `K2` contains a first-chain edge. -/
theorem no_face2_chain1 {s : ℕ} (hs : s < m) {T : Triangle} (hT : T ∈ C.R2.K.faces) :
    ¬ edgeSegment P (i + (s : ZMod n)) ⊆ T.carrier := by
  intro hsub
  obtain ⟨hmid, hnv⟩ := u4h_midpoint_not_vertex C.hP (i + (s : ZMod n))
  set mid : Plane := (1 / 2 : ℝ) • P (i + (s : ZMod n)) + (1 / 2 : ℝ) • P (i + (s : ZMod n) + 1)
    with hmiddef
  have h2 : mid ∈ C.R2.U := C.R2.face_subset hT (hsub hmid)
  have h1 : mid ∈ C.R1.U := by
    have : mid ∈ embeddedPolygonImage (u4h_subPoly P i m) := by
      rw [u4h_mem_polygonImage_subPoly]; exact Or.inl ⟨s, hs, hmid⟩
    rw [← C.R1.frontier_eq] at this
    exact C.R1.isClosed.frontier_subset this
  have hD : mid ∈ segment ℝ (P i) (P (i + (m : ZMod n))) := by rw [← C.inter]; exact ⟨h1, h2⟩
  rw [segment_symm] at hD
  rcases u4h_edge_inter_diag_subPoly C.hclean _ hmid hD with h | h
  · exact hnv i h.symm
  · exact hnv _ h.symm

/-- No face of `K1` contains a second-chain edge. -/
theorem no_face1_chain2 {s : ℕ} (hs : s < n - m) {T : Triangle} (hT : T ∈ C.R1.K.faces) :
    ¬ edgeSegment P (i + (m : ZMod n) + (s : ZMod n)) ⊆ T.carrier := by
  intro hsub
  obtain ⟨hmid, hnv⟩ := u4h_midpoint_not_vertex C.hP (i + (m : ZMod n) + (s : ZMod n))
  set mid : Plane := (1 / 2 : ℝ) • P (i + (m : ZMod n) + (s : ZMod n)) +
    (1 / 2 : ℝ) • P (i + (m : ZMod n) + (s : ZMod n) + 1) with hmiddef
  have h1 : mid ∈ C.R1.U := C.R1.face_subset hT (hsub hmid)
  have h2 : mid ∈ C.R2.U := by
    have : mid ∈ embeddedPolygonImage (u4h_subPoly P (i + (m : ZMod n)) (n - m)) := by
      rw [u4h_mem_polygonImage_subPoly2 P i (by have := C.hmn; omega)]
      exact Or.inl ⟨s, hs, hmid⟩
    rw [← C.R2.frontier_eq] at this
    exact C.R2.isClosed.frontier_subset this
  have hD : mid ∈ segment ℝ (P i) (P (i + (m : ZMod n))) := by rw [← C.inter]; exact ⟨h1, h2⟩
  rw [segment_symm] at hD
  rcases u4h_edge_inter_diag_subPoly C.hclean _ hmid hD with h | h
  · exact hnv i h.symm
  · exact hnv _ h.symm

end u4h_SplitCtx

/-- The sub-polygon edges as `P`-edges. -/
theorem u4h_subPoly1_edge (P : LabelledTuple n) (i : ZMod n) {m s : ℕ} (hs : s < m) :
    ∃ k : ZMod (m + 1), k ≠ -1 ∧
    edgeSegment (u4h_subPoly P i m) k = edgeSegment P (i + (s : ZMod n)) ∧
    u4h_subPoly P i m k = P (i + (s : ZMod n)) ∧
    u4h_subPoly P i m (k + 1) = P (i + (s : ZMod n) + 1) := by
  obtain ⟨k, hk1, hks⟩ := u4h_subPoly_index_exhaust m hs
  refine ⟨k, hk1, ?_, ?_, ?_⟩
  · rw [u4h_subPoly_edgeSegment P i m hk1, hks]
  · rw [u4h_subPoly_apply, hks]
  · rw [u4h_subPoly_apply, u4h_val_add_one hk1, hks, Nat.cast_add_one, add_assoc]

theorem u4h_subPoly2_edge (P : LabelledTuple n) (i : ZMod n) {m s : ℕ} (hs : s < n - m) :
    ∃ k : ZMod (n - m + 1), k ≠ -1 ∧
    edgeSegment (u4h_subPoly P (i + (m : ZMod n)) (n - m)) k =
      edgeSegment P (i + (m : ZMod n) + (s : ZMod n)) ∧
    u4h_subPoly P (i + (m : ZMod n)) (n - m) k = P (i + (m : ZMod n) + (s : ZMod n)) ∧
    u4h_subPoly P (i + (m : ZMod n)) (n - m) (k + 1) =
      P (i + (m : ZMod n) + (s : ZMod n) + 1) := by
  obtain ⟨k, hk1, hks⟩ := u4h_subPoly_index_exhaust (n - m) hs
  refine ⟨k, hk1, ?_, ?_, ?_⟩
  · rw [u4h_subPoly_edgeSegment P _ _ hk1, hks]
  · rw [u4h_subPoly_apply, hks]
  · rw [u4h_subPoly_apply, u4h_val_add_one hk1, hks, Nat.cast_add_one]
    congr 1; ring

namespace u4h_SplitCtx

variable [NeZero n] {P : LabelledTuple n} {i : ZMod n} {m : ℕ} (C : u4h_SplitCtx P i m)

/-- (X-b) every edge of `P` is a face-edge of the glued triangulation. -/
theorem edge_face (j : ZMod n) : ∃ T ∈ C.R1.K.faces ∪ C.R2.K.faces, ∃ k : Fin 3,
    T.edgeSeg k = edgeSegment P j := by
  obtain ⟨s, hs, rfl⟩ := u4h_index_offset i j
  by_cases hsm : s < m
  · obtain ⟨k', -, hk', -, -⟩ := u4h_subPoly1_edge P i hsm
    obtain ⟨T, hT, k, hk⟩ := C.R1.edge_face k'
    exact ⟨T, Or.inl hT, k, by rw [hk, hk']⟩
  · obtain ⟨heq, hs'⟩ := u4h_offset_split i hs (not_lt.mp hsm)
    obtain ⟨k', -, hk', -, -⟩ := u4h_subPoly2_edge P i hs'
    obtain ⟨T, hT, k, hk⟩ := C.R2.edge_face k'
    exact ⟨T, Or.inr hT, k, by rw [hk, hk', heq]⟩

/-- (X-c) uniqueness of the face at each edge of `P`. -/
theorem edge_unique (j : ZMod n) : ∀ T ∈ C.R1.K.faces ∪ C.R2.K.faces,
    ∀ T' ∈ C.R1.K.faces ∪ C.R2.K.faces, edgeSegment P j ⊆ T.carrier →
      edgeSegment P j ⊆ T'.carrier → T.carrier = T'.carrier := by
  intro T hT T' hT' hsub hsub'
  obtain ⟨s, hs, rfl⟩ := u4h_index_offset i j
  by_cases hsm : s < m
  · obtain ⟨k', -, hk', -, -⟩ := u4h_subPoly1_edge P i hsm
    rcases hT with hT | hT
    · rcases hT' with hT' | hT'
      · exact C.R1.edge_unique k' T hT T' hT' (hk' ▸ hsub) (hk' ▸ hsub')
      · exact absurd hsub' (C.no_face2_chain1 hsm hT')
    · exact absurd hsub (C.no_face2_chain1 hsm hT)
  · obtain ⟨heq, hs'⟩ := u4h_offset_split i hs (not_lt.mp hsm)
    rw [heq] at hsub hsub'
    obtain ⟨k', -, hk', -, -⟩ := u4h_subPoly2_edge P i hs'
    rcases hT with hT | hT
    · exact absurd hsub (C.no_face1_chain2 hs' hT)
    · rcases hT' with hT' | hT'
      · exact absurd hsub' (C.no_face1_chain2 hs' hT')
      · exact C.R2.edge_unique k' T hT T' hT' (hk' ▸ hsub) (hk' ▸ hsub')

/-- (X-g) the two regions have the same side. -/
theorem sigma_eq : C.R1.σ = C.R2.σ := by
  obtain ⟨F1, hF1, k1, hk1⟩ := C.faces1
  obtain ⟨F2, hF2, k2, hk2⟩ := C.faces2
  have hopp := u4h_split_opposite C.inter (C.R1.face_subset hF1) (C.R2.face_subset hF2) hk1 hk2
  -- side facts at the diagonal edge of each sub-polygon
  have hk1' : F1.edgeSeg k1 = edgeSegment (u4h_subPoly P i m) (-1) := by
    rw [u4h_subPoly_edgeSegment_last, segment_symm]; exact hk1
  have hk2' : F2.edgeSeg k2 = edgeSegment (u4h_subPoly P (i + (m : ZMod n)) (n - m)) (-1) := by
    rw [u4h_subPoly_edgeSegment_last, u4h_split_second_start (by have := C.hmn; omega)]; exact hk2
  have h1 := C.R1.side (-1) F1 hF1 k1 hk1'
  have h2 := C.R2.side (-1) F2 hF2 k2 hk2'
  rw [neg_add_cancel, u4h_subPoly_zero, u4h_subPoly_last] at h1 h2
  rw [u4h_split_second_start (by have := C.hmn; omega)] at h2
  have e1 : det (P i - P (i + (m : ZMod n))) (F1.v (k1 + 2) - P (i + (m : ZMod n))) =
      -det (P (i + (m : ZMod n)) - P i) (F1.v (k1 + 2) - P i) := by
    simp only [det, Prod.fst_sub, Prod.snd_sub]; ring
  rw [e1] at h1
  rcases C.R1.σ_pm with hσ1 | hσ1 <;> rcases C.R2.σ_pm with hσ2 | hσ2
  · rw [hσ1, hσ2]
  · exfalso; rw [hσ1] at h1; rw [hσ2] at h2; nlinarith
  · exfalso; rw [hσ1] at h1; rw [hσ2] at h2; nlinarith
  · rw [hσ1, hσ2]

/-- (X-f) the side condition for the glued triangulation. -/
theorem side (j : ZMod n) : ∀ T ∈ C.R1.K.faces ∪ C.R2.K.faces, ∀ k : Fin 3,
    T.edgeSeg k = edgeSegment P j → 0 < C.R1.σ * det (P (j + 1) - P j) (T.v (k + 2) - P j) := by
  intro T hT k hk
  obtain ⟨s, hs, rfl⟩ := u4h_index_offset i j
  by_cases hsm : s < m
  · obtain ⟨k', -, hk', hv0, hv1⟩ := u4h_subPoly1_edge P i hsm
    rcases hT with hT | hT
    · have := C.R1.side k' T hT k (by rw [hk, hk'])
      rwa [hv0, hv1] at this
    · exfalso
      exact C.no_face2_chain1 hsm hT (hk ▸ u4h_tri_edgeSeg_subset T k)
  · obtain ⟨heq, hs'⟩ := u4h_offset_split i hs (not_lt.mp hsm)
    rw [heq] at hk ⊢
    obtain ⟨k', -, hk', hv0, hv1⟩ := u4h_subPoly2_edge P i hs'
    rcases hT with hT | hT
    · exfalso
      exact C.no_face1_chain2 hs' hT (hk ▸ u4h_tri_edgeSeg_subset T k)
    · have := C.R2.side k' T hT k (by rw [hk, hk'])
      rw [hv0, hv1] at this
      rwa [C.sigma_eq]

include C in
/-- **The glued region of a split**, with its carrier. -/
theorem region' : ∃ G : u4h_Region P, G.U = C.R1.U ∪ C.R2.U := by
  obtain ⟨F1, hF1, k1, hk1⟩ := C.faces1
  obtain ⟨F2, hF2, k2, hk2⟩ := C.faces2
  have hedge : F2.edgeSeg k2 = F1.edgeSeg k1 := by rw [hk1, hk2]
  have hinter' : C.R1.U ∩ C.R2.U = F1.edgeSeg k1 := by rw [hk1]; exact C.inter
  refine ⟨{ U := C.R1.U ∪ C.R2.U
            K := u4h_glueTri C.R1.K C.R2.K hF1 k1 hF2 k2 hedge hinter'
            frontier_eq := C.frontier_eq
            edge_face := C.edge_face
            edge_unique := C.edge_unique
            hull := ?_
            int_conn := C.int_conn
            σ := C.R1.σ
            σ_pm := C.R1.σ_pm
            side := C.side
            count := ?_ }, rfl⟩
  · rintro x (hx | hx)
    · exact convexHull_mono (u4h_subPoly_range_subset P i m) (C.R1.hull hx)
    · exact convexHull_mono (u4h_subPoly_range_subset P _ _) (C.R2.hull hx)
  · show ((C.R1.K.faces ∪ C.R2.K.faces).image Triangle.carrier).ncard + 2 ≤ n
    rw [Set.image_union]
    have h := Set.ncard_union_le (C.R1.K.faces.image Triangle.carrier)
      (C.R2.K.faces.image Triangle.carrier)
    have h1 := C.R1.count
    have h2 := C.R2.count
    have hmn := C.hmn
    have hm := C.hm
    omega

include C in
theorem region : Nonempty (u4h_Region P) :=
  let ⟨G, _⟩ := C.region'; ⟨G⟩

end u4h_SplitCtx

end U4Y_block

section U4Za_block

/-! The region of an embedded triangle (U4 helpers). -/

/-- The side sign of a face at an edge `segment (P i) (P (i+1))`, by the order of its ends. -/
theorem u4h_tri_side_of_ends (T : Triangle) (k : Fin 3) {a b : Plane}
    (hk : T.edgeSeg k = segment ℝ a b) :
    (T.v k = a ∧ T.v (k + 1) = b → 0 < det (b - a) (T.v (k + 2) - a)) ∧
    (T.v k = b ∧ T.v (k + 1) = a → det (b - a) (T.v (k + 2) - a) < 0) := by
  have hpos := u4h_tri_pos T k
  constructor
  · rintro ⟨h0, h1⟩
    rw [← h0, ← h1]; exact hpos
  · rintro ⟨h0, h1⟩
    have e : det (b - a) (T.v (k + 2) - a) = -det (a - b) (T.v (k + 2) - b) := by
      simp only [det, Prod.fst_sub, Prod.snd_sub]; ring
    rw [e, ← h0, ← h1]; linarith

theorem u4h_zmod3_add_one (i : ZMod 3) : (i = 0 → i + 1 = 1) ∧ (i = 1 → i + 1 = 2) ∧
    (i = 2 → i + 1 = 0) := by
  refine ⟨?_, ?_, ?_⟩ <;> rintro rfl <;> decide

/-- **The region of an embedded triangle** is its convex hull. -/
theorem u4h_triRegion' (P : LabelledTuple 3) (hP : Embedded P) :
    ∃ R : u4h_Region P, R.U = convexHull ℝ {P 0, P 1, P 2} := by
  have hD := u4h_tri3_det_ne_zero P hP
  have hinj := u4h_vertex_injective hP
  obtain ⟨hE0, hE1, hE2⟩ := u4h_edgeSegment_zmod3 P
  have hpoly := u4h_polygonImage_zmod3 P
  have h01 : (0 : ZMod 3) + 1 = 1 := by decide
  have h12 : (1 : ZMod 3) + 1 = 2 := by decide
  have h20 : (2 : ZMod 3) + 1 = 0 := by decide
  have hne01 : P 0 ≠ P 1 := fun h => absurd (hinj h) (by decide)
  have hne02 : P 0 ≠ P 2 := fun h => absurd (hinj h) (by decide)
  have hne12 : P 1 ≠ P 2 := fun h => absurd (hinj h) (by decide)
  -- the edge of `P` at index `i` as a segment
  have hEi : ∀ i : ZMod 3, edgeSegment P i = segment ℝ (P i) (P (i + 1)) :=
    fun i => u4h_edgeSegment_eq_segment P i
  rcases lt_or_gt_of_ne hD with hneg | hpos
  · -- negative orientation: the positive triple is `(P 0, P 2, P 1)`
    have hD' : 0 < det (P 2 - P 0) (P 1 - P 0) := by rw [u4h_det_swap']; linarith
    refine ⟨u4h_triRegionOf P (u4h_mkTri (P 0) (P 2) (P 1) hD') ?_ ?_ ?_ (-1) (Or.inr rfl) ?_,
      by show (u4h_mkTri (P 0) (P 2) (P 1) hD').carrier = _
         rw [u4h_mkTri_carrier, u4h_hull3_comm]⟩
    · rw [u4h_mkTri_carrier, u4h_hull3_comm]
    · rw [u4h_mkTri_carrier, u4h_frontier_hull3 hD', hpoly, segment_symm ℝ (P 0) (P 2),
        segment_symm ℝ (P 2) (P 1), segment_symm ℝ (P 1) (P 0)]
      ext x; simp only [Set.mem_union]; tauto
    · intro i
      rcases u4h_zmod3_cases i with rfl | rfl | rfl
      · exact ⟨2, by rw [u4h_mkTri_edgeSeg2, hE0, segment_symm]⟩
      · exact ⟨1, by rw [u4h_mkTri_edgeSeg1, hE1, segment_symm]⟩
      · exact ⟨0, by rw [u4h_mkTri_edgeSeg0, hE2, segment_symm]⟩
    · intro i k hk
      rw [hEi] at hk
      obtain ⟨hdir, hrev⟩ := u4h_tri_side_of_ends _ k hk
      rcases u4h_face_edge_ends _ k hk with ⟨h0, h1⟩ | ⟨h0, h1⟩
      · -- direct order is impossible for the reversed triangle
        exfalso
        rcases u4h_zmod3_cases i with rfl | rfl | rfl <;> fin_cases k <;>
          simp only [u4h_mkTri_v0, u4h_mkTri_v1, u4h_mkTri_v2, h01, h12, h20] at h0 h1 <;>
          first
          | exact hne01 h0 | exact hne02 h0 | exact hne12 h0
          | exact hne01 h0.symm | exact hne02 h0.symm | exact hne12 h0.symm
          | exact hne01 h1 | exact hne02 h1 | exact hne12 h1
          | exact hne01 h1.symm | exact hne02 h1.symm | exact hne12 h1.symm
      · have := hrev ⟨h0, h1⟩
        linarith
  · refine ⟨u4h_triRegionOf P (u4h_mkTri (P 0) (P 1) (P 2) hpos) ?_ ?_ ?_ 1 (Or.inl rfl) ?_,
      by show (u4h_mkTri (P 0) (P 1) (P 2) hpos).carrier = _
         rw [u4h_mkTri_carrier]⟩
    · rw [u4h_mkTri_carrier]
    · rw [u4h_mkTri_carrier, u4h_frontier_hull3 hpos, hpoly]
    · intro i
      rcases u4h_zmod3_cases i with rfl | rfl | rfl
      · exact ⟨0, by rw [u4h_mkTri_edgeSeg0, hE0]⟩
      · exact ⟨1, by rw [u4h_mkTri_edgeSeg1, hE1]⟩
      · exact ⟨2, by rw [u4h_mkTri_edgeSeg2, hE2]⟩
    · intro i k hk
      rw [hEi] at hk
      obtain ⟨hdir, hrev⟩ := u4h_tri_side_of_ends _ k hk
      rcases u4h_face_edge_ends _ k hk with ⟨h0, h1⟩ | ⟨h0, h1⟩
      · have := hdir ⟨h0, h1⟩
        linarith
      · exfalso
        rcases u4h_zmod3_cases i with rfl | rfl | rfl <;> fin_cases k <;>
          simp only [u4h_mkTri_v0, u4h_mkTri_v1, u4h_mkTri_v2, h01, h12, h20] at h0 h1 <;>
          first
          | exact hne01 h0 | exact hne02 h0 | exact hne12 h0
          | exact hne01 h0.symm | exact hne02 h0.symm | exact hne12 h0.symm
          | exact hne01 h1 | exact hne02 h1 | exact hne12 h1
          | exact hne01 h1.symm | exact hne02 h1.symm | exact hne12 h1.symm

theorem u4h_triRegion (P : LabelledTuple 3) (hP : Embedded P) : Nonempty (u4h_Region P) :=
  let ⟨R, _⟩ := u4h_triRegion' P hP; ⟨R⟩

end U4Za_block

section U4Zb_block

/-! Strict lexicographic hull bound and the cone-direction conditions for (LL2) (U4 helpers). -/

/-- The open lexicographic half-plane above `p`. -/
def u4h_LexQs (p : Plane) : Set Plane := {x | p.1 < x.1 ∨ (p.1 = x.1 ∧ p.2 < x.2)}

theorem u4h_convex_LexQs (p : Plane) : Convex ℝ (u4h_LexQs p) := by
  intro x hx y hy s t hs ht hst
  simp only [u4h_LexQs, Set.mem_ofPred_eq, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
    Prod.smul_snd, smul_eq_mul] at hx hy ⊢
  have hp1 : s * p.1 + t * p.1 = p.1 := by rw [← add_mul, hst, one_mul]
  have hp2 : s * p.2 + t * p.2 = p.2 := by rw [← add_mul, hst, one_mul]
  have hx1 : s * p.1 ≤ s * x.1 :=
    mul_le_mul_of_nonneg_left (by rcases hx with h | ⟨h, -⟩ <;> linarith) hs
  have hy1 : t * p.1 ≤ t * y.1 :=
    mul_le_mul_of_nonneg_left (by rcases hy with h | ⟨h, -⟩ <;> linarith) ht
  by_cases hlt : p.1 < s * x.1 + t * y.1
  · exact Or.inl hlt
  · right
    have heq : p.1 = s * x.1 + t * y.1 := le_antisymm (by linarith) (not_lt.mp hlt)
    refine ⟨heq, ?_⟩
    have hx1' : s * p.1 = s * x.1 := by linarith
    have hy1' : t * p.1 = t * y.1 := by linarith
    -- at least one of `s, t` is positive; where positive the first coordinates agree
    have hsx : s * p.2 ≤ s * x.2 ∧ (0 < s → s * p.2 < s * x.2) := by
      rcases hs.lt_or_eq with hs' | hs'
      · have : p.1 = x.1 := mul_left_cancel₀ hs'.ne' hx1'
        rcases hx with h | ⟨-, h⟩
        · exact absurd this h.ne
        · exact ⟨(mul_lt_mul_of_pos_left h hs').le, fun _ => mul_lt_mul_of_pos_left h hs'⟩
      · rw [← hs']; simp
    have hty : t * p.2 ≤ t * y.2 ∧ (0 < t → t * p.2 < t * y.2) := by
      rcases ht.lt_or_eq with ht' | ht'
      · have : p.1 = y.1 := mul_left_cancel₀ ht'.ne' hy1'
        rcases hy with h | ⟨-, h⟩
        · exact absurd this h.ne
        · exact ⟨(mul_lt_mul_of_pos_left h ht').le, fun _ => mul_lt_mul_of_pos_left h ht'⟩
      · rw [← ht']; simp
    rcases hs.lt_or_eq with hs' | hs'
    · have := hsx.2 hs'; linarith [hty.1]
    · have ht' : 0 < t := by linarith
      have := hty.2 ht'; linarith [hsx.1]

/-- The lexmin vertex is not in the hull of the other vertices. -/
theorem u4h_lexmin_not_mem_hull {P : LabelledTuple n} {v : ZMod n}
    (hv : ∀ k, k ≠ v → u4h_Lex (P v) (P k)) {S : Set Plane}
    (hS : ∀ x ∈ S, ∃ k, k ≠ v ∧ P k = x) : P v ∉ convexHull ℝ S := by
  have hsub : convexHull ℝ S ⊆ u4h_LexQs (P v) := by
    apply convexHull_min _ (u4h_convex_LexQs _)
    intro x hx
    obtain ⟨k, hk, rfl⟩ := hS x hx
    exact hv k hk
  intro h
  have := hsub h
  simp only [u4h_LexQs, Set.mem_ofPred_eq, lt_self_iff_false, false_or, and_false] at this

/-- Cone-direction condition for (LL2) applied to the second sub-polygon (edges `p, ω`,
direction `q`). -/
theorem u4h_dir_cond1 {p q ω : Plane} {α β : ℝ} (hα : 0 < α) (hβ : 0 < β)
    (hω : ω = α • p + β • q) (hpq : det p q ≠ 0) :
    (0 < det p ω ∧ (det p q < 0 ∨ 0 < det ω q)) ∨ (det p ω < 0 ∧ (det ω q < 0 ∨ 0 < det p q)) := by
  have e1 : det p ω = β * det p q := by
    rw [hω, u4h_det_add_right, u4h_det_smul_right, u4h_det_smul_right, u4h_det_self, mul_zero,
      zero_add]
  have e2 : det ω q = α * det p q := by
    rw [hω]
    simp only [det, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring
  rcases lt_or_gt_of_ne hpq with h | h
  · right; rw [e1, e2]; exact ⟨by nlinarith, Or.inl (by nlinarith)⟩
  · left; rw [e1, e2]; exact ⟨by nlinarith, Or.inr (by nlinarith)⟩

/-- Cone-direction condition for (LL2) applied to the first sub-polygon (edges `ω, q`,
direction `p`). -/
theorem u4h_dir_cond2 {p q ω : Plane} {α β : ℝ} (hα : 0 < α) (hβ : 0 < β)
    (hω : ω = α • p + β • q) (hpq : det p q ≠ 0) :
    (0 < det ω q ∧ (det ω p < 0 ∨ 0 < det q p)) ∨ (det ω q < 0 ∧ (det q p < 0 ∨ 0 < det ω p)) := by
  have e1 : det ω q = α * det p q := by
    rw [hω]
    simp only [det, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring
  have e2 : det ω p = -(β * det p q) := by
    rw [hω]
    simp only [det, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring
  have e3 : det q p = -det p q := by rw [u4h_det_swap']
  rcases lt_or_gt_of_ne hpq with h | h
  · right; rw [e1, e2, e3]; exact ⟨by nlinarith, Or.inr (by nlinarith)⟩
  · left; rw [e1, e2, e3]; exact ⟨by nlinarith, Or.inl (by nlinarith)⟩

end U4Zb_block

section U4Zc_block

/-! Ear extraction by counting faces (U4 helpers): a region triangulation of an `n`-gon with
`n ≥ 4` has a face carrying two consecutive polygon edges; that face is a convex, vertex-empty ear. -/

/-- Three distinct vertices of a triangle are not collinear. -/
theorem u4h_vertices_not_collinear (T : Triangle) {a b c : Plane} (ha : a ∈ Set.range T.v)
    (hb : b ∈ Set.range T.v) (hc : c ∈ Set.range T.v) (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    det (b - a) (c - a) ≠ 0 := by
  intro hD
  have hba : b - a ≠ 0 := sub_ne_zero.mpr hab.symm
  obtain ⟨r, hr⟩ : ∃ r : ℝ, c - a = r • (b - a) := ⟨_, scalar_of_det_zero hba hD⟩
  have hc' : c = a + r • (b - a) := by rw [← hr]; abel
  obtain ⟨ja, rfl⟩ := ha
  obtain ⟨jb, rfl⟩ := hb
  obtain ⟨jc, rfl⟩ := hc
  -- one of the three lies in the hull of the other two
  by_cases hr0 : r < 0
  · -- `a ∈ segment b c`
    have hmem : T.v ja ∈ convexHull ℝ {T.v jb, T.v jc} := by
      rw [convexHull_pair, u4h_mem_segment_iff_lin]
      refine ⟨1 / (1 - r), (one_div_pos.mpr (by linarith)).le, ?_, ?_⟩
      · rw [div_le_one (by linarith)]; linarith
      · rw [hc']
        have : T.v ja + r • (T.v jb - T.v ja) - T.v jb = (1 - r) • (T.v ja - T.v jb) := by module
        rw [this, smul_smul, one_div_mul_cancel (by linarith : (1 : ℝ) - r ≠ 0), one_smul]; abel
    have := (u4h_vertex_mem_hull_iff T (by rintro x (rfl | rfl) <;> exact ⟨_, rfl⟩) ja).mp hmem
    rcases this with h | h
    · exact hab h
    · exact hac h
  · by_cases hr1 : r ≤ 1
    · -- `c ∈ segment a b`
      have hmem : T.v jc ∈ convexHull ℝ {T.v ja, T.v jb} := by
        rw [convexHull_pair, u4h_mem_segment_iff_lin]
        exact ⟨r, not_lt.mp hr0, hr1, hc'⟩
      have := (u4h_vertex_mem_hull_iff T (by rintro x (rfl | rfl) <;> exact ⟨_, rfl⟩) jc).mp hmem
      rcases this with h | h
      · exact hac h.symm
      · exact hbc h.symm
    · -- `b ∈ segment a c`
      have hr1' : 1 < r := not_le.mp hr1
      have hmem : T.v jb ∈ convexHull ℝ {T.v ja, T.v jc} := by
        rw [convexHull_pair, u4h_mem_segment_iff_lin]
        refine ⟨1 / r, by positivity, ?_, ?_⟩
        · rw [div_le_one (by linarith)]; linarith
        · rw [hc', add_sub_cancel_left, smul_smul, one_div_mul_cancel (by linarith : r ≠ 0),
            one_smul]; abel
      have := (u4h_vertex_mem_hull_iff T (by rintro x (rfl | rfl) <;> exact ⟨_, rfl⟩) jb).mp hmem
      rcases this with h | h
      · exact hab h.symm
      · exact hbc h

theorem u4h_range_ncard_le (T : Triangle) : (Set.range T.v).ncard ≤ 3 := by
  rw [u4h_range_fin3]
  refine (Set.ncard_insert_le _ _).trans ?_
  refine (Nat.add_le_add_right (Set.ncard_insert_le _ _) 1).trans ?_
  rw [Set.ncard_singleton]

theorem u4h_range_finite (T : Triangle) : (Set.range T.v).Finite := Set.finite_range _

/-- Endpoints of a polygon edge that is a face-edge are vertices of the face. -/
theorem u4h_edge_ends_mem_range (T : Triangle) (k : Fin 3) {a b : Plane}
    (hk : T.edgeSeg k = segment ℝ a b) : a ∈ Set.range T.v ∧ b ∈ Set.range T.v := by
  rcases u4h_face_edge_ends T k hk with ⟨h0, h1⟩ | ⟨h0, h1⟩
  · exact ⟨⟨k, h0⟩, ⟨k + 1, h1⟩⟩
  · exact ⟨⟨k + 1, h1⟩, ⟨k, h0⟩⟩

/-- Two faces with the same carrier have the same vertex set. -/
theorem u4h_range_eq_of_carrier_eq {X : Set Plane} (K : Triangulation X) {T T' : Triangle}
    (hT : T ∈ K.faces) (hT' : T' ∈ K.faces) (h : T.carrier = T'.carrier) :
    Set.range T'.v ⊆ Set.range T.v := by
  rintro p ⟨j, rfl⟩
  have hp : T'.v j ∈ T.carrier ∩ T'.carrier := ⟨h ▸ subset_convexHull ℝ _ ⟨j, rfl⟩,
    subset_convexHull ℝ _ ⟨j, rfl⟩⟩
  rw [K.inter T hT T' hT'] at hp
  exact ((u4h_vertex_mem_hull_iff T' Set.inter_subset_right j).mp hp).1

/-- The ear at `j = i + 1` when the face at `E_i` also contains the vertex `P (i+2)`. -/
theorem u4h_ear_at [NeZero n] (hn : 4 ≤ n) {P : LabelledTuple n} (hP : Embedded P)
    (R : u4h_Region P) (i : ZMod n) {T : Triangle} (hT : T ∈ R.K.faces) {k : Fin 3}
    (hk : T.edgeSeg k = edgeSegment P i) (hnext : P (i + 2) ∈ Set.range T.v) :
    det (P (i + 1) - P (i + 1 - 1)) (P (i + 1 + 1) - P (i + 1 - 1)) ≠ 0 ∧
      u4h_VertexEmpty P (i + 1) ∧
      0 < R.σ * det (P (i + 1) - P (i + 1 - 1)) (P (i + 1 + 1) - P (i + 1 - 1)) := by
  have hinj := u4h_vertex_injective hP
  have h1 : (1 : ZMod n) ≠ 0 := u4h_one_ne_zero hn
  have h2 : (2 : ZMod n) ≠ 0 := u4h_two_ne_zero hn
  have hi1 : i + 1 - 1 = i := by ring
  have hi2 : i + 1 + 1 = i + 2 := by ring
  rw [hi1, hi2]
  have hk' : T.edgeSeg k = segment ℝ (P i) (P (i + 1)) := by rw [hk, u4h_edgeSegment_eq_segment]
  obtain ⟨ha, hb⟩ := u4h_edge_ends_mem_range T k hk'
  have hab : P i ≠ P (i + 1) := fun h => h1 (by linear_combination -(hinj h))
  have hbc : P (i + 1) ≠ P (i + 2) := fun h => h1 (by linear_combination -(hinj h))
  have hac : P i ≠ P (i + 2) := fun h => h2 (by linear_combination -(hinj h))
  -- the vertex set of `T`
  have hrange : Set.range T.v = {P i, P (i + 1), P (i + 2)} := by
    symm
    apply Set.eq_of_subset_of_ncard_le
    · rintro x (rfl | rfl | rfl)
      · exact ha
      · exact hb
      · exact hnext
    · refine (u4h_range_ncard_le T).trans (le_of_eq ?_)
      rw [Set.ncard_insert_of_notMem, Set.ncard_pair hbc]
      rintro (h | h)
      · exact hab h
      · exact hac h
    · exact u4h_range_finite T
  have hcar : T.carrier = earHull P (i + 1) := by
    rw [Triangle.carrier, hrange, earHull, hi1, hi2]
  refine ⟨u4h_vertices_not_collinear T ha hb hnext hab hbc hac, ?_, ?_⟩
  · -- vertex-empty
    intro m hm
    rw [← hcar] at hm
    obtain ⟨G, hG, kG, hkG⟩ := R.edge_face m
    have hkG' : G.edgeSeg kG = segment ℝ (P m) (P (m + 1)) := by
      rw [hkG, u4h_edgeSegment_eq_segment]
    have hmG : P m ∈ Set.range G.v := (u4h_edge_ends_mem_range G kG hkG').1
    have hmem : P m ∈ T.carrier ∩ G.carrier := ⟨hm, subset_convexHull ℝ _ hmG⟩
    rw [R.K.inter T hT G hG] at hmem
    obtain ⟨jm, hjm⟩ := hmG
    rw [← hjm] at hmem
    have := ((u4h_vertex_mem_hull_iff G Set.inter_subset_right jm).mp hmem).1
    rw [hjm, hrange] at this
    rcases this with h | h | h
    · left; rw [hi1]; exact hinj h
    · right; left; exact hinj h
    · right; right; rw [hi2]; exact hinj h
  · -- side
    have hside := R.side i T hT k hk
    have happ : T.v (k + 2) = P (i + 2) := by
      have hmem : T.v (k + 2) ∈ ({P i, P (i + 1), P (i + 2)} : Set Plane) := by
        rw [← hrange]; exact ⟨_, rfl⟩
      have hne0 : T.v (k + 2) ≠ T.v k := fun h => (u4h_tri_ne' T k) h.symm
      have hne1 : T.v (k + 2) ≠ T.v (k + 1) := fun h => by
        have := u4h_tri_ne T (k + 1)
        rw [show k + 1 + 1 = k + 2 by rw [add_assoc]; rfl] at this
        exact this h.symm
      rcases u4h_face_edge_ends T k hk' with ⟨h0, h1'⟩ | ⟨h0, h1'⟩ <;>
        rcases hmem with h | h | h
      · exact absurd (h.trans h0.symm) hne0
      · exact absurd (h.trans h1'.symm) hne1
      · exact h
      · exact absurd (h.trans h1'.symm) hne1
      · exact absurd (h.trans h0.symm) hne0
      · exact h
    rw [happ] at hside
    have e : det (P (i + 1) - P i) (P (i + 2) - P i) =
        det (P (i + 1) - P i) (P (i + 2) - P i) := rfl
    exact hside

/-- **Ear extraction.** A region of an embedded `n`-gon (`n ≥ 4`) has a convex vertex-empty ear. -/
theorem u4h_exists_ear_of_region [NeZero n] (hn : 4 ≤ n) {P : LabelledTuple n} (hP : Embedded P)
    (R : u4h_Region P) :
    ∃ j : ZMod n, det (P j - P (j - 1)) (P (j + 1) - P (j - 1)) ≠ 0 ∧ u4h_VertexEmpty P j ∧
      0 < R.σ * det (P j - P (j - 1)) (P (j + 1) - P (j - 1)) := by
  classical
  have hinj := u4h_vertex_injective hP
  have h1 : (1 : ZMod n) ≠ 0 := u4h_one_ne_zero hn
  have h2 : (2 : ZMod n) ≠ 0 := u4h_two_ne_zero hn
  choose F hF k hk using R.edge_face
  -- the face-carrier map is not injective
  have hni : ¬ Function.Injective (fun i => (F i).carrier) := by
    intro hinjF
    have hsub : Set.range (fun i => (F i).carrier) ⊆ R.K.faces.image Triangle.carrier := by
      rintro x ⟨i, rfl⟩; exact ⟨F i, hF i, rfl⟩
    have hcard : (Set.range (fun i => (F i).carrier)).ncard = n := by
      rw [Set.ncard_range_of_injective hinjF, Nat.card_eq_fintype_card, ZMod.card]
    have hle := Set.ncard_le_ncard hsub (R.K.finite.image _)
    have := R.count
    omega
  simp only [Function.Injective, not_forall] at hni
  obtain ⟨i, i', heq, hne⟩ := hni
  have hrange : Set.range (F i').v = Set.range (F i).v :=
    Set.Subset.antisymm (u4h_range_eq_of_carrier_eq R.K (hF i) (hF i') heq)
      (u4h_range_eq_of_carrier_eq R.K (hF i') (hF i) heq.symm)
  have hki : (F i).edgeSeg (k i) = segment ℝ (P i) (P (i + 1)) := by
    rw [hk, u4h_edgeSegment_eq_segment]
  have hki' : (F i').edgeSeg (k i') = segment ℝ (P i') (P (i' + 1)) := by
    rw [hk, u4h_edgeSegment_eq_segment]
  obtain ⟨ha, hb⟩ := u4h_edge_ends_mem_range _ _ hki
  obtain ⟨ha', hb'⟩ := u4h_edge_ends_mem_range _ _ hki'
  rw [hrange] at ha' hb'
  -- `i` and `i'` are consecutive
  by_cases hc1 : i' = i + 1
  · subst hc1
    refine ⟨i + 1, u4h_ear_at hn hP R i (hF i) (hk i) ?_⟩
    rw [show i + 1 + 1 = i + 2 by ring] at hb'
    exact hb'
  by_cases hc2 : i = i' + 1
  · subst hc2
    refine ⟨i' + 1, u4h_ear_at hn hP R i' (hF i') (hk i') ?_⟩
    rw [← hrange, show i' + 1 + 1 = i' + 2 by ring] at hb
    exact hb
  · exfalso
    -- four distinct vertices in a 3-element set
    have hd : ∀ x y : ZMod n, x ≠ y → P x ≠ P y := fun x y hxy h => hxy (hinj h)
    have hne1 : i ≠ i + 1 := fun h => h1 (by linear_combination -h)
    have hne2 : i' ≠ i' + 1 := fun h => h1 (by linear_combination -h)
    have hne3 : i + 1 ≠ i' + 1 := fun h => hne (add_right_cancel h)
    have S4 : ({P i, P (i + 1), P i', P (i' + 1)} : Set Plane) ⊆ Set.range (F i).v := by
      rintro x (rfl | rfl | rfl | rfl)
      · exact ha
      · exact hb
      · exact ha'
      · exact hb'
    have hA : P i ∉ ({P (i + 1), P i', P (i' + 1)} : Set Plane) := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨hd _ _ hne1, hd _ _ hne, hd _ _ hc2⟩
    have hB : P (i + 1) ∉ ({P i', P (i' + 1)} : Set Plane) := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨hd _ _ (fun h' => hc1 h'.symm), hd _ _ hne3⟩
    have hcard : ({P i, P (i + 1), P i', P (i' + 1)} : Set Plane).ncard = 4 := by
      rw [Set.ncard_insert_of_notMem hA, Set.ncard_insert_of_notMem hB, Set.ncard_pair (hd _ _ hne2)]
    have := Set.ncard_le_ncard S4 (u4h_range_finite _)
    have := u4h_range_ncard_le (F i)
    omega

end U4Zc_block

section U4Zd_block

/-! The main induction: every embedded polygon bounds a region (U4 helpers). -/

theorem u4h_subPoly_one (P : LabelledTuple n) (i : ZMod n) {m : ℕ} (hm : 1 ≤ m) :
    u4h_subPoly P i m 1 = P (i + 1) := by
  rw [u4h_subPoly_apply]
  have : (1 : ZMod (m + 1)).val = 1 := by
    rw [ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt (by omega)]
  rw [this, Nat.cast_one]

theorem u4h_subPoly_neg_two (P : LabelledTuple n) (i : ZMod n) {m : ℕ} (hm : 1 ≤ m) :
    u4h_subPoly P i m (-2) = P (i + ((m - 1 : ℕ) : ZMod n)) := by
  rw [u4h_subPoly_apply]
  have h2 : (-2 : ZMod (m + 1)) ≠ -1 := by
    intro h
    exact u4h_one_ne_zero' (n := m + 1) (by omega) (by linear_combination -h)
  have hv : (-2 : ZMod (m + 1)).val = m - 1 := by
    have := u4h_val_add_one h2
    rw [show (-2 : ZMod (m + 1)) + 1 = -1 by ring, u4h_val_neg_one'] at this
    omega
  rw [hv]

/-- General-size version of `u4h_edge_disjoint_openDiag`. -/
theorem u4h_edge_disjoint_openDiag' {P : LabelledTuple n} (hP : Embedded P) {j : ZMod n}
    (hac : P (j - 1) ≠ P (j + 1))
    (hstrict : earHull P j ∩ embeddedPolygonImage P = edgeSegment P (j - 1) ∪ edgeSegment P j)
    {k : ZMod n} (hk1 : k ≠ j - 1) (hk2 : k ≠ j) {x : Plane} (hk : x ∈ edgeSegment P k) :
    x ∉ openSegment ℝ (P (j - 1)) (P (j + 1)) := by
  intro hxo
  have hxT : x ∈ earHull P j :=
    u4h_diag_subset_earHull P j (openSegment_subset_segment ℝ _ _ hxo)
  have hx' : x ∈ edgeSegment P (j - 1) ∪ edgeSegment P j := by
    rw [← hstrict]
    exact ⟨hxT, u4h_edgeSegment_subset_polygonImage P k hk⟩
  rcases u4h_edge_inter_ears hP hk1 hk2 ⟨hk, hx'⟩ with h | h
  · rw [h] at hxo
    exact hac (left_mem_openSegment_iff.mp hxo)
  · rw [h] at hxo
    exact hac (right_mem_openSegment_iff.mp hxo)

set_option maxHeartbeats 800000 in
/-- **Existence of the region** for every embedded polygon with at least three vertices. -/
theorem u4h_region_exists : ∀ (N : ℕ) [NeZero N], 3 ≤ N → ∀ P : LabelledTuple N, Embedded P →
    Nonempty (u4h_Region P) := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro _ hN P hP
  rcases Nat.lt_or_ge N 4 with h3 | h4
  · obtain rfl : N = 3 := by omega
    exact u4h_triRegion P hP
  obtain ⟨v, hv⟩ := u4h_exists_lexmin hP
  have hdet0 := u4h_lexmin_det_ne_zero (by omega) hP hv
  have hdet : det (P v - P (v - 1)) (P (v + 1) - P (v - 1)) ≠ 0 := by
    have e : det (P v - P (v - 1)) (P (v + 1) - P (v - 1)) =
        -det (P (v - 1) - P v) (P (v + 1) - P v) := by
      simp only [det, Prod.fst_sub, Prod.snd_sub]; ring
    rw [e]; exact neg_ne_zero.mpr hdet0
  have hinj := u4h_vertex_injective hP
  have h1 : (1 : ZMod N) ≠ 0 := u4h_one_ne_zero h4
  have h2 : (2 : ZMod N) ≠ 0 := u4h_two_ne_zero h4
  have h3' : (3 : ZMod N) ≠ 0 := u4h_three_ne_zero h4
  by_cases hinv : ∃ k, k ∈ u4h_Inv P v
  · -- case (S): split along the clean diagonal to the farthest invader
    obtain ⟨w, ⟨hw1, hw2, hw3, -⟩, hclean, α, β, hα, hβ, hcone⟩ :=
      u4h_exists_clean_invader h4 hP v hdet hinv
    obtain ⟨m, hmN, hwm⟩ := u4h_index_offset v w
    have hm0 : m ≠ 0 := by rintro rfl; apply hw2; rw [hwm]; simp
    have hm1 : m ≠ 1 := by rintro rfl; apply hw3; rw [hwm]; simp
    have hmN1 : m + 1 ≠ N := by
      intro h
      apply hw1
      rw [hwm]
      have : ((m : ℕ) : ZMod N) + 1 = 0 := by
        rw [← Nat.cast_add_one, h, ZMod.natCast_self]
      linear_combination this
    have hm2 : 2 ≤ m := by omega
    have hmn : m + 2 ≤ N := by omega
    rw [hwm] at hclean hcone
    have hP1 : Embedded (u4h_subPoly P v m) := u4h_subPoly_embedded hP hm2 hmn hclean
    have hclean2 : ∀ k, Disjoint (edgeSegment P k)
        (openSegment ℝ (P (v + (m : ZMod N))) (P (v + (m : ZMod N) + ((N - m : ℕ) : ZMod N)))) := by
      intro k
      rw [u4h_split_second_start (by omega), openSegment_symm]
      exact hclean k
    have hP2 : Embedded (u4h_subPoly P (v + (m : ZMod N)) (N - m)) :=
      u4h_subPoly_embedded hP (by omega) (by omega) hclean2
    obtain ⟨R1⟩ := ih (m + 1) (by omega) (by omega) _ hP1
    obtain ⟨R2⟩ := ih (N - m + 1) (by omega) (by omega) _ hP2
    -- lexmin of the sub-polygons
    have hv1 : ∀ k : ZMod (m + 1), k ≠ 0 →
        u4h_Lex (u4h_subPoly P v m 0) (u4h_subPoly P v m k) := by
      intro k hk
      rw [u4h_subPoly_zero, u4h_subPoly_apply]
      apply hv
      intro h
      have := u4h_offset_injective (s := k.val) (s' := 0) (by have := ZMod.val_lt k; omega)
        (by omega) v (by rw [Nat.cast_zero, add_zero]; exact h)
      exact hk ((u4h_val_eq_zero_iff k).mp this)
    have hv2 : ∀ k : ZMod (N - m + 1), k ≠ -1 →
        u4h_Lex (u4h_subPoly P (v + (m : ZMod N)) (N - m) (-1))
          (u4h_subPoly P (v + (m : ZMod N)) (N - m) k) := by
      intro k hk
      rw [u4h_subPoly_last, u4h_split_second_start (by omega), u4h_subPoly_apply]
      apply hv
      intro h
      have hkv := u4h_val_lt_of_ne_neg_one hk
      have := u4h_offset_injective (s := m + k.val) (s' := 0) (by omega) (by omega) v
        (by rw [Nat.cast_zero, add_zero, Nat.cast_add, ← add_assoc]; exact h)
      omega
    have hq0 : P (v + 1) - P v ≠ 0 := hP.edge_ne_zero v
    have hp0 : P (v - 1) - P v ≠ 0 := by
      have := hP.edge_ne_zero (v - 1)
      rw [edge, sub_add_cancel] at this
      exact fun h => this (by rw [← neg_sub, h, neg_zero])
    -- X1: points of `E_v` near `P v` lie outside `R2.U` (LL2 for the second sub-polygon)
    have X1 : ∃ s : ℕ, s < m ∧ ∃ x ∈ edgeSegment P (v + (s : ZMod N)),
        x ∉ ({P v, P (v + (m : ZMod N))} : Set Plane) ∧ x ∉ R2.U := by
      have hw := u4h_dir_cond1 hα hβ hcone hdet0
      have hdir := u4h_lexmin_ray_outside (n := N - m + 1) (by omega) hP2 R2.isClosed
        R2.frontier_eq R2.hull hv2 (w := P (v + 1) - P v) (by
          rw [show (-1 : ZMod (N - m + 1)) - 1 = -2 by ring, neg_add_cancel,
            u4h_subPoly_neg_two _ _ (by omega), u4h_subPoly_last, u4h_subPoly_zero,
            u4h_split_second_start (by omega)]
          have e : v + (m : ZMod N) + ((N - m - 1 : ℕ) : ZMod N) = v - 1 := by
            rw [add_assoc, ← Nat.cast_add, show m + (N - m - 1) = N - 1 by omega,
              Nat.cast_sub (by omega), ZMod.natCast_self, Nat.cast_one]; ring
          rw [e]
          exact hw)
      obtain ⟨ρ, hρ, hray⟩ := hdir
      set t : ℝ := min (ρ / 2) (1 / 2) with ht
      have ht0 : 0 < t := lt_min (by positivity) (by norm_num)
      have htρ : t < ρ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
      have ht1 : t < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
      have hx := hray t ht0 htρ
      rw [u4h_subPoly_last, u4h_split_second_start (by omega)] at hx
      refine ⟨0, by omega, P v + t • (P (v + 1) - P v), ?_, ?_, hx⟩
      · rw [Nat.cast_zero, add_zero, u4h_edgeSegment_eq_segment]
        exact u4h_lin_mem_segment _ _ ht0.le ht1.le
      · rintro (h | h)
        · have : t • (P (v + 1) - P v) = 0 := add_eq_left.mp h
          rcases smul_eq_zero.mp this with h' | h'
          · exact ht0.ne' h'
          · exact hq0 h'
        · have hmem : P (v + (m : ZMod N)) ∈ edgeSegment P v := by
            rw [← h, u4h_edgeSegment_eq_segment]
            exact u4h_lin_mem_segment _ _ ht0.le ht1.le
          rcases u4h_incident_of_vertex_mem hP hmem with h' | h'
          · exact hw2 (by rw [hwm, h'])
          · exact hw3 (by rw [hwm, h'])
    -- X2: points of `E_{v-1}` near `P v` lie outside `R1.U` (LL2 for the first sub-polygon)
    have X2 : ∃ s : ℕ, s < N - m ∧ ∃ x ∈ edgeSegment P (v + (m : ZMod N) + (s : ZMod N)),
        x ∉ ({P v, P (v + (m : ZMod N))} : Set Plane) ∧ x ∉ R1.U := by
      have hw := u4h_dir_cond2 hα hβ hcone hdet0
      have hdir := u4h_lexmin_ray_outside (n := m + 1) (by omega) hP1 R1.isClosed
        R1.frontier_eq R1.hull hv1 (w := P (v - 1) - P v) (by
          rw [zero_sub, zero_add, u4h_subPoly_last, u4h_subPoly_zero, u4h_subPoly_one _ _ (by omega)]
          exact hw)
      obtain ⟨ρ, hρ, hray⟩ := hdir
      set t : ℝ := min (ρ / 2) (1 / 2) with ht
      have ht0 : 0 < t := lt_min (by positivity) (by norm_num)
      have htρ : t < ρ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
      have ht1 : t < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
      have hx := hray t ht0 htρ
      rw [u4h_subPoly_zero] at hx
      have e : v + (m : ZMod N) + ((N - m - 1 : ℕ) : ZMod N) = v - 1 := by
        rw [add_assoc, ← Nat.cast_add, show m + (N - m - 1) = N - 1 by omega,
          Nat.cast_sub (by omega), ZMod.natCast_self, Nat.cast_one]; ring
      refine ⟨N - m - 1, by omega, P v + t • (P (v - 1) - P v), ?_, ?_, hx⟩
      · rw [e, u4h_edgeSegment_prev, segment_symm]
        exact u4h_lin_mem_segment _ _ ht0.le ht1.le
      · rintro (h | h)
        · have : t • (P (v - 1) - P v) = 0 := add_eq_left.mp h
          rcases smul_eq_zero.mp this with h' | h'
          · exact ht0.ne' h'
          · exact hp0 h'
        · have hmem : P (v + (m : ZMod N)) ∈ edgeSegment P (v - 1) := by
            rw [← h, u4h_edgeSegment_prev, segment_symm]
            exact u4h_lin_mem_segment _ _ ht0.le ht1.le
          rcases u4h_incident_of_vertex_mem hP hmem with h' | h'
          · exact hw1 (by rw [hwm, h'])
          · exact hw2 (by rw [hwm, h', sub_add_cancel])
    exact (u4h_SplitCtx.mk hP hm2 hmn hclean R1 R2 X1 X2).region
  · -- case (E): the lexmin vertex is a strict ear; split off its triangle
    have hV : u4h_VertexEmpty P v := by
      intro k hk
      by_contra hne
      simp only [not_or] at hne
      exact hinv ⟨k, hne.1, hne.2.1, hne.2.2, hk⟩
    have hstrict := u4h_strict_ear_of_vertex_empty hP h4 hdet hV
    have hac : P (v - 1) ≠ P (v + 1) := fun h => h2 (by linear_combination -(hinj h))
    have hi2 : v - 1 + ((2 : ℕ) : ZMod N) = v + 1 := by push_cast; ring
    have hclean : ∀ k, Disjoint (edgeSegment P k)
        (openSegment ℝ (P (v - 1)) (P (v - 1 + ((2 : ℕ) : ZMod N)))) := by
      intro k
      rw [hi2, Set.disjoint_left]
      intro x hxk hxo
      by_cases hk1 : k = v - 1
      · rw [hk1, u4h_edgeSegment_prev] at hxk
        have hx' : x ∈ segment ℝ (P (v - 1)) (P v) ∩ segment ℝ (P (v - 1)) (P (v + 1)) :=
          ⟨hxk, openSegment_subset_segment ℝ _ _ hxo⟩
        rw [u4h_segment_inter_same_start hdet] at hx'
        have hx'' : x = P (v - 1) := hx'
        rw [hx''] at hxo
        exact hac (left_mem_openSegment_iff.mp hxo)
      by_cases hk2 : k = v
      · rw [hk2, u4h_edgeSegment_eq_segment, segment_symm] at hxk
        have hD' : det (P v - P (v + 1)) (P (v - 1) - P (v + 1)) ≠ 0 := by
          have e : det (P v - P (v + 1)) (P (v - 1) - P (v + 1)) =
              -det (P v - P (v - 1)) (P (v + 1) - P (v - 1)) := by
            simp only [det, Prod.fst_sub, Prod.snd_sub]; ring
          rw [e]; exact neg_ne_zero.mpr hdet
        have hx' : x ∈ segment ℝ (P (v + 1)) (P v) ∩ segment ℝ (P (v + 1)) (P (v - 1)) :=
          ⟨hxk, by rw [segment_symm]; exact openSegment_subset_segment ℝ _ _ hxo⟩
        rw [u4h_segment_inter_same_start hD'] at hx'
        have hx'' : x = P (v + 1) := hx'
        rw [hx''] at hxo
        exact hac (right_mem_openSegment_iff.mp hxo)
      exact u4h_edge_disjoint_openDiag' hP hac hstrict hk1 hk2 hxk hxo
    have hP1 : Embedded (u4h_subPoly P (v - 1) 2) :=
      u4h_subPoly_embedded hP (le_refl 2) (by omega) hclean
    have hclean2 : ∀ k, Disjoint (edgeSegment P k) (openSegment ℝ (P (v - 1 + ((2 : ℕ) : ZMod N)))
        (P (v - 1 + ((2 : ℕ) : ZMod N) + ((N - 2 : ℕ) : ZMod N)))) := by
      intro k
      rw [u4h_split_second_start (by omega), openSegment_symm]
      exact hclean k
    have hP2 : Embedded (u4h_subPoly P (v - 1 + ((2 : ℕ) : ZMod N)) (N - 2)) :=
      u4h_subPoly_embedded hP (by omega) (by omega) hclean2
    obtain ⟨R1, hR1U⟩ := u4h_triRegion' (u4h_subPoly P (v - 1) 2) hP1
    obtain ⟨R2⟩ := ih (N - 2 + 1) (by omega) (by omega) _ hP2
    -- the triangle's vertices
    have hP10 : u4h_subPoly P (v - 1) 2 0 = P (v - 1) := u4h_subPoly_zero P (v - 1) 2
    have hP11 : u4h_subPoly P (v - 1) 2 1 = P v := by
      rw [u4h_subPoly_one P (v - 1) (by norm_num), sub_add_cancel]
    have hP12 : u4h_subPoly P (v - 1) 2 2 = P (v + 1) := by
      rw [u4h_subPoly_apply]
      have : (2 : ZMod (2 + 1)).val = 2 := by
        rw [show (2 : ZMod (2 + 1)) = ((2 : ℕ) : ZMod (2 + 1)) from Nat.cast_ofNat.symm,
          ZMod.val_natCast_of_lt (by norm_num)]
      rw [this, ← hi2]
    have hR1 : R1.U = earHull P v := by rw [hR1U, hP10, hP11, hP12]; rfl
    -- X1: the apex `P v` is not in the region of the rest (lexmin not in the hull)
    have X1 : ∃ s : ℕ, s < 2 ∧ ∃ x ∈ edgeSegment P (v - 1 + (s : ZMod N)),
        x ∉ ({P (v - 1), P (v - 1 + ((2 : ℕ) : ZMod N))} : Set Plane) ∧ x ∉ R2.U := by
      refine ⟨0, by norm_num, P v, ?_, ?_, ?_⟩
      · rw [Nat.cast_zero, add_zero]
        have := u4h_end_mem_edgeSegment P (v - 1)
        rwa [sub_add_cancel] at this
      · rw [hi2]
        rintro (h | h)
        · exact h1 (by linear_combination (hinj h))
        · exact h1 (by linear_combination -(hinj (Set.mem_singleton_iff.mp h)))
      · intro hmem
        have hhull := R2.hull hmem
        refine u4h_lexmin_not_mem_hull hv ?_ hhull
        rintro x ⟨k, rfl⟩
        rw [u4h_subPoly_apply, hi2]
        refine ⟨v + 1 + (k.val : ZMod N), ?_, rfl⟩
        intro h
        have hkv := ZMod.val_lt k
        have : ((1 + k.val : ℕ) : ZMod N) = 0 := by
          push_cast; linear_combination h
        exact u4h_natCast_ne_zero (n := N) (k := 1 + k.val) (by omega) (by omega) this
    -- X2: the vertex `P (v+2)` of the rest is not in the triangle (vertex-empty)
    have X2 : ∃ s : ℕ, s < N - 2 ∧ ∃ x ∈ edgeSegment P (v - 1 + ((2 : ℕ) : ZMod N) + (s : ZMod N)),
        x ∉ ({P (v - 1), P (v - 1 + ((2 : ℕ) : ZMod N))} : Set Plane) ∧ x ∉ R1.U := by
      refine ⟨0, by omega, P (v + 2), ?_, ?_, ?_⟩
      · rw [Nat.cast_zero, add_zero, hi2]
        have := u4h_end_mem_edgeSegment P (v + 1)
        rwa [show v + 1 + 1 = v + 2 by ring] at this
      · rw [hi2]
        rintro (h | h)
        · exact h3' (by linear_combination (hinj h))
        · exact h1 (by linear_combination (hinj (Set.mem_singleton_iff.mp h)))
      · rw [hR1]
        intro hmem
        rcases hV (v + 2) hmem with h | h | h
        · exact h3' (by linear_combination h)
        · exact h2 (by linear_combination h)
        · exact h1 (by linear_combination h)
    exact (u4h_SplitCtx.mk hP (le_refl 2) (by omega) hclean R1 R2 X1 X2).region

end U4Zd_block

section U4Ze_block

/-! Uniqueness of the region and the canonical region (U4 helpers). -/

/-- All regions of an embedded polygon have the same side. -/
theorem u4h_sigma_unique [NeZero n] (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Embedded P)
    (R R' : u4h_Region P) : R.σ = R'.σ := by
  obtain ⟨v, hv⟩ := u4h_exists_lexmin hP
  have h1 := u4h_region_lexmin_turn hn hP R hv
  have h2 := u4h_region_lexmin_turn hn hP R' hv
  rcases R.σ_pm with h | h <;> rcases R'.σ_pm with h' | h'
  · rw [h, h']
  · exfalso; rw [h] at h1; rw [h'] at h2; linarith
  · exfalso; rw [h] at h1; rw [h'] at h2; linarith
  · rw [h, h']

/-- Two regions of the same embedded polygon have a common interior point. -/
theorem u4h_regions_interior_inter [NeZero n] (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Embedded P) (R R' : u4h_Region P) : (interior R.U ∩ interior R'.U).Nonempty := by
  obtain ⟨v, hv⟩ := u4h_exists_lexmin hP
  have hσ := u4h_sigma_unique hn hP R R'
  obtain ⟨F, hF, k, hk⟩ := R.edge_face (v - 1)
  obtain ⟨F', hF', k', hk'⟩ := R'.edge_face (v - 1)
  have hs := R.side (v - 1) F hF k hk
  have hs' := R'.side (v - 1) F' hF' k' hk'
  rw [sub_add_cancel] at hs hs'
  rw [u4h_edgeSegment_prev] at hk hk'
  set e1 := P (v - 1) with he1
  set e2 := P v with he2
  set x : Plane := (1 / 2 : ℝ) • e1 + (1 / 2 : ℝ) • e2 with hx
  have hxo : x ∈ openSegment ℝ e1 e2 := u4h_midpoint_mem_openSegment _ _
  obtain ⟨ε, hε, h⟩ := u4h_face_halfdisc F k hk hxo
  obtain ⟨ε', hε', h'⟩ := u4h_face_halfdisc F' k' hk' hxo
  -- the open half-disc on the `σ` side
  set B : Set Plane := Metric.ball x (min ε ε') ∩ {y | 0 < R.σ * det (e2 - e1) (y - e1)} with hB
  have hBopen : IsOpen B :=
    Metric.isOpen_ball.inter (isOpen_lt continuous_const (by
      have := u4h_continuous_det_sub (e2 - e1) e1
      exact continuous_const.mul this))
  have hBF : B ⊆ F.carrier := by
    rintro y ⟨hy1, hy2⟩
    rw [h y (lt_of_lt_of_le (Metric.mem_ball.mp hy1) (min_le_left _ _))]
    have hy2' : 0 < R.σ * det (e2 - e1) (y - e1) := hy2
    rcases R.σ_pm with hσ1 | hσ1 <;> rw [hσ1] at hs hy2' <;> nlinarith
  have hBF' : B ⊆ F'.carrier := by
    rintro y ⟨hy1, hy2⟩
    rw [h' y (lt_of_lt_of_le (Metric.mem_ball.mp hy1) (min_le_right _ _))]
    have hy2' : 0 < R.σ * det (e2 - e1) (y - e1) := hy2
    rw [hσ] at hy2'
    rcases R'.σ_pm with hσ1 | hσ1 <;> rw [hσ1] at hs' hy2' <;> nlinarith
  -- `B` is nonempty
  have hsne : det (e2 - e1) (F.v (k + 2) - e1) ≠ 0 := u4h_apex_det_ne_zero F k hk
  set w := F.v (k + 2) - e1 with hw
  set η : ℝ := min ε ε' / (2 * (‖w‖ + 1)) with hη
  have hηpos : 0 < η := by positivity
  have hy0ball : x + η • w ∈ Metric.ball x (min ε ε') := by
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_pos hηpos, hη, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith [norm_nonneg w, lt_min hε hε']
  have hy0 : x + η • w ∈ B := by
    refine ⟨hy0ball, ?_⟩
    show 0 < R.σ * det (e2 - e1) (x + η • w - e1)
    have e : det (e2 - e1) (x + η • w - e1) = η * det (e2 - e1) w := by
      rw [hx]
      simp only [det, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
        Prod.smul_snd, smul_eq_mul]; ring
    rw [e]
    have : 0 < R.σ * det (e2 - e1) w := by
      have e2' : det (e2 - e1) w = det (P v - P (v - 1)) (F.v (k + 2) - P (v - 1)) := rfl
      rw [e2']; exact hs
    nlinarith
  exact ⟨_, interior_maximal (hBF.trans (R.face_subset hF)) hBopen hy0,
    interior_maximal (hBF'.trans (R'.face_subset hF')) hBopen hy0⟩

/-- **Uniqueness of the region.** -/
theorem u4h_region_unique [NeZero n] (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Embedded P)
    (R R' : u4h_Region P) : R.U = R'.U := by
  have key : ∀ (R R' : u4h_Region P), R.U ⊆ R'.U := by
    intro R R'
    obtain ⟨y, hy, hy'⟩ := u4h_regions_interior_inter hn hP R R'
    have hsub : interior R.U ⊆ interior R'.U ∪ R'.Uᶜ := by
      intro z hz
      by_cases hz' : z ∈ R'.U
      · left
        by_contra hzi
        have hzf : z ∈ frontier R'.U := ⟨subset_closure hz', hzi⟩
        rw [R'.frontier_eq, ← R.frontier_eq] at hzf
        exact disjoint_interior_frontier.notMem_of_mem_left hz hzf
      · right; exact hz'
    rcases IsPreconnected.subset_or_subset isOpen_interior R'.isClosed.isOpen_compl
        (Set.disjoint_left.mpr fun z hz hz' => hz' (interior_subset hz)) hsub R.int_conn
        with h | h
    · rw [← u4h_triangulation_closure_interior R.K]
      exact (closure_mono h).trans (closure_minimal interior_subset R'.isClosed)
    · exact absurd (interior_subset hy') (h hy)
  exact Set.Subset.antisymm (key R R') (key R' R)

open Classical in
/-- The canonical region bounded by `P` (junk `∅` when no region exists). -/
noncomputable def u4h_regionOf [NeZero n] (P : LabelledTuple n) : Set Plane :=
  if h : Nonempty (u4h_Region P) then (Classical.choice h).U else ∅

theorem u4h_region_U_eq_regionOf [NeZero n] (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Embedded P)
    (R : u4h_Region P) : R.U = u4h_regionOf P := by
  unfold u4h_regionOf
  rw [dif_pos ⟨R⟩]
  exact u4h_region_unique hn hP R _

end U4Ze_block

section U4Zf_block

/-! Downstream interface (U4 helpers): convex ears, the canonical region and its ear relation. -/

/-- `deleteVertex` is the sub-polygon starting after the deleted vertex. -/
theorem u4h_deleteVertex_eq_subPoly {n' : ℕ} (P : LabelledTuple (n' + 2)) (j : ZMod (n' + 2)) :
    deleteVertex P j = u4h_subPoly P (j + 1) n' := by
  funext k
  show P (((k.val : ℕ) : ZMod (n' + 2)) + (j + 1)) = P (j + 1 + (k.val : ZMod (n' + 2)))
  rw [add_comm]

/-- 2D Cramer decomposition of a vector in a nondegenerate basis. -/
theorem u4h_cone_decomp {a b c : Plane} (hΔ : det (b - a) (c - a) ≠ 0) (w : Plane) :
    w = (det w (c - a) / det (b - a) (c - a)) • (b - a) +
      (det (b - a) w / det (b - a) (c - a)) • (c - a) := by
  apply Prod.ext
  · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul, Prod.fst_sub]
    field_simp
    simp only [det, Prod.fst_sub, Prod.snd_sub]; ring
  · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul, Prod.snd_sub]
    field_simp
    simp only [det, Prod.fst_sub, Prod.snd_sub]; ring

/-- A point `a + t • w` with `w` strictly inside the cone at `a` of the triangle lies in the
triangle for small `t`. -/
theorem u4h_cone_point_mem {a b c w : Plane} {l m : ℝ} (hl : 0 < l) (hm : 0 < m)
    (hw : w = l • (b - a) + m • (c - a)) :
    a + (1 / (l + m + 1)) • w ∈ convexHull ℝ {a, b, c} := by
  rw [u4h_mem_hull3_iff]
  have hpos : 0 < l + m + 1 := by positivity
  refine ⟨1 - l / (l + m + 1) - m / (l + m + 1), l / (l + m + 1), m / (l + m + 1), ?_,
    by positivity, by positivity, by ring, ?_⟩
  · have h1 : l / (l + m + 1) + m / (l + m + 1) ≤ 1 := by
      rw [← add_div, div_le_one hpos]; linarith
    linarith
  · rw [hw]; module

/-- Vertices of the polygon other than `j-1, j, j+1` are the vertices of `deleteVertex P j`
other than the diagonal ends; the lexmin transfers. -/
theorem u4h_lexmin_deleteVertex {n' : ℕ} {P : LabelledTuple (n' + 2)} (hP : Embedded P)
    {j v : ZMod (n' + 2)} (hv : ∀ k, k ≠ v → u4h_Lex (P v) (P k)) {v' : ZMod (n' + 1)}
    (hv' : deletionIndex j v' = v) :
    ∀ k', k' ≠ v' → u4h_Lex (deleteVertex P j v') (deleteVertex P j k') := by
  intro k' hk'
  rw [deleteVertex_apply, deleteVertex_apply, hv']
  apply hv
  intro h
  rw [← hv'] at h
  exact hk' (deletionIndex_injective j h)

/-- **σ-transfer at an ear.** If the lexmin vertex `v` of `P` is not the apex `j`, the regions of
`P` and of `deleteVertex P j` have the same side (the ear being strict and convex). -/
theorem u4h_sigma_ear {n' : ℕ} (hn : 2 ≤ n') {P : LabelledTuple (n' + 2)} (hP : Embedded P)
    {j : ZMod (n' + 2)} (hdet : det (P j - P (j - 1)) (P (j + 1) - P (j - 1)) ≠ 0)
    (hstrict : earHull P j ∩ embeddedPolygonImage P = edgeSegment P (j - 1) ∪ edgeSegment P j)
    (R : u4h_Region P) (R' : u4h_Region (deleteVertex P j))
    (hconv : 0 < R.σ * det (P j - P (j - 1)) (P (j + 1) - P (j - 1)))
    {v : ZMod (n' + 2)} (hv : ∀ k, k ≠ v → u4h_Lex (P v) (P k)) (hvj : v ≠ j) : R.σ = R'.σ := by
  have h4 : 4 ≤ n' + 2 := by omega
  have hinj := u4h_vertex_injective hP
  have h1 : (1 : ZMod (n' + 2)) ≠ 0 := u4h_one_ne_zero h4
  have h2 : (2 : ZMod (n' + 2)) ≠ 0 := u4h_two_ne_zero h4
  have h3 : (3 : ZMod (n' + 2)) ≠ 0 := u4h_three_ne_zero h4
  have h1' : (1 : ZMod (n' + 1)) ≠ 0 := u4h_one_ne_zero' (n := n' + 1) (by omega)
  have hσR := u4h_region_lexmin_turn (by omega) hP R hv
  have hP' : Embedded (deleteVertex P j) := by
    refine u4h_embedded_deleteVertex (n := n' + 1) (by omega) hP ?_ hstrict
    intro h; exact h2 (by linear_combination -(hinj h))
  obtain ⟨v', hv'⟩ := deletionIndex_exhaust j hvj
  have hlex' := u4h_lexmin_deleteVertex hP hv hv'
  have hσR' := u4h_region_lexmin_turn (n := n' + 1) (by omega) hP' R' hlex'
  rw [deleteVertex_apply, deleteVertex_apply, deleteVertex_apply, hv'] at hσR'
  -- the sign facts, and the two cases on `v` (general / adjacent to `j`)
  have hsq : ∀ x y : ℝ, (x = 1 ∨ x = -1) → (y = 1 ∨ y = -1) → x ≠ y → y = -x := by
    rintro x y (rfl | rfl) (rfl | rfl) hxy <;> first | rfl | exact absurd rfl hxy | norm_num
  by_contra hne
  have hσ' : R'.σ = -R.σ := hsq _ _ R.σ_pm R'.σ_pm hne
  rw [hσ'] at hσR'
  by_cases hv1 : v' = -1
  · -- `v = j - 1`
    subst hv1
    rw [deletionIndex_last] at hv'
    rw [show (-1 : ZMod (n' + 1)) - 1 = -2 by ring, neg_add_cancel, deletionIndex_zero,
      u4h_deletionIndex_neg_two (by omega)] at hσR'
    rw [← hv'] at hσR hσR'
    -- `w := P (j-2) - P (j-1)` lies strictly inside the cone at `P (j-1)`
    set a := P (j - 1) with ha
    set b := P j with hb
    set c := P (j + 1) with hc
    set w := P (j - 2) - a with hw
    have hΔ : det (b - a) (c - a) ≠ 0 := hdet
    have e1 : det (a - P (j - 1 - 1)) (P (j - 1 + 1) - a) = det (b - a) w := by
      rw [show j - 1 + 1 = j by ring, show j - 1 - 1 = j - 2 by ring]
      simp only [hb, hw, det, Prod.fst_sub, Prod.snd_sub]; ring
    have e2 : det (a - P (j - 2)) (c - a) = det (-w) (c - a) := by
      simp only [hw, det, Prod.fst_sub, Prod.snd_sub, Prod.fst_neg, Prod.snd_neg]; ring
    rw [e1] at hσR
    rw [e2] at hσR'
    have hl : 0 < det w (c - a) / det (b - a) (c - a) := by
      rw [u4h_det_neg_left] at hσR'
      rcases R.σ_pm with hs | hs <;> rw [hs] at hσR' hconv <;>
        first | exact div_pos (by linarith) (by linarith)
              | exact div_pos_of_neg_of_neg (by linarith) (by linarith)
    have hm : 0 < det (b - a) w / det (b - a) (c - a) := by
      rcases R.σ_pm with hs | hs <;> rw [hs] at hσR hconv <;>
        first | exact div_pos (by linarith) (by linarith)
              | exact div_pos_of_neg_of_neg (by linarith) (by linarith)
    have hmem := u4h_cone_point_mem hl hm (u4h_cone_decomp hΔ w)
    set t := 1 / (det w (c - a) / det (b - a) (c - a) + det (b - a) w / det (b - a) (c - a) + 1)
      with ht
    have ht0 : 0 < t := by positivity
    have ht1 : t ≤ 1 := by
      rw [ht, div_le_one (by positivity)]; linarith
    -- the point lies on `E_{j-2}` and in the ear triangle: contradiction with strictness
    have hE : a + t • w ∈ edgeSegment P (j - 2) := by
      rw [u4h_edgeSegment_eq_segment, show j - 2 + 1 = j - 1 by ring, segment_symm,
        u4h_mem_segment_iff_lin]
      exact ⟨t, ht0.le, ht1, rfl⟩
    have hT : a + t • w ∈ earHull P j := hmem
    have hk1 : j - 2 ≠ j - 1 := fun h => h1 (by linear_combination -h)
    have hk2 : j - 2 ≠ j := fun h => h2 (by linear_combination -h)
    have hx' : a + t • w ∈ edgeSegment P (j - 1) ∪ edgeSegment P j := by
      rw [← hstrict]; exact ⟨hT, u4h_edgeSegment_subset_polygonImage P _ hE⟩
    rcases u4h_edge_inter_ears hP hk1 hk2 ⟨hE, hx'⟩ with h | h
    · have : t • w = 0 := add_eq_left.mp h
      rcases smul_eq_zero.mp this with h' | h'
      · exact ht0.ne' h'
      · have := hinj (sub_eq_zero.mp h')
        exact h1 (by linear_combination -this)
    · have : P (j + 1) ∈ edgeSegment P (j - 2) := h ▸ hE
      rcases u4h_incident_of_vertex_mem hP this with h' | h'
      · exact h3 (by linear_combination h')
      · exact h2 (by linear_combination h')
  by_cases hv0 : v' = 0
  · -- `v = j + 1`
    subst hv0
    rw [deletionIndex_zero] at hv'
    have hd1 : deletionIndex j 1 = j + 1 + 1 := by
      have := deletionIndex_next j (i := 0) (by intro h; exact h1' (by linear_combination h))
      rwa [zero_add, deletionIndex_zero] at this
    rw [zero_sub, zero_add, deletionIndex_last, hd1] at hσR'
    rw [← hv'] at hσR hσR'
    set a := P (j - 1) with ha
    set b := P j with hb
    set c := P (j + 1) with hc
    set w := P (j + 1 + 1) - c with hw
    have hΔ : det (b - a) (c - a) ≠ 0 := hdet
    have hΔ' : det (a - c) (b - c) = det (b - a) (c - a) := u4h_det_rot2 a b c
    have e1 : det (c - P (j + 1 - 1)) (P (j + 1 + 1) - c) = det (c - b) w := by
      rw [show j + 1 - 1 = j by ring]
    have e2 : det (c - a) (P (j + 1 + 1) - c) = det (c - a) w := rfl
    rw [e1] at hσR
    rw [e2] at hσR'
    -- decompose `w` in the cone at `c` spanned by `a - c`, `b - c`
    have hl : 0 < det w (b - c) / det (a - c) (b - c) := by
      have : det w (b - c) = det (c - b) w := by simp only [det, Prod.fst_sub, Prod.snd_sub]; ring
      rw [this, hΔ']
      rcases R.σ_pm with hs | hs <;> rw [hs] at hσR hconv <;>
        first | exact div_pos (by linarith) (by linarith)
              | exact div_pos_of_neg_of_neg (by linarith) (by linarith)
    have hm : 0 < det (a - c) w / det (a - c) (b - c) := by
      have : det (a - c) w = -det (c - a) w := by simp only [det, Prod.fst_sub, Prod.snd_sub]; ring
      rw [this, hΔ']
      rcases R.σ_pm with hs | hs <;> rw [hs] at hσR' hconv <;>
        first | exact div_pos (by linarith) (by linarith)
              | exact div_pos_of_neg_of_neg (by linarith) (by linarith)
    have hΔ'' : det (a - c) (b - c) ≠ 0 := by rw [hΔ']; exact hΔ
    have hmem := u4h_cone_point_mem hl hm (u4h_cone_decomp hΔ'' w)
    set t := 1 / (det w (b - c) / det (a - c) (b - c) + det (a - c) w / det (a - c) (b - c) + 1)
      with ht
    have ht0 : 0 < t := by positivity
    have ht1 : t ≤ 1 := by
      rw [ht, div_le_one (by positivity)]; linarith
    have hE : c + t • w ∈ edgeSegment P (j + 1) := by
      rw [u4h_edgeSegment_eq_segment, u4h_mem_segment_iff_lin]
      exact ⟨t, ht0.le, ht1, rfl⟩
    have hT : c + t • w ∈ earHull P j := by
      unfold earHull
      rw [u4h_hull3_rot, u4h_hull3_rot]
      exact hmem
    have hk1 : j + 1 ≠ j - 1 := fun h => h2 (by linear_combination h)
    have hk2 : j + 1 ≠ j := fun h => h1 (by linear_combination h)
    have hx' : c + t • w ∈ edgeSegment P (j - 1) ∪ edgeSegment P j := by
      rw [← hstrict]; exact ⟨hT, u4h_edgeSegment_subset_polygonImage P _ hE⟩
    rcases u4h_edge_inter_ears hP hk1 hk2 ⟨hE, hx'⟩ with h | h
    · have : P (j - 1) ∈ edgeSegment P (j + 1) := h ▸ hE
      rcases u4h_incident_of_vertex_mem hP this with h' | h'
      · exact h2 (by linear_combination -h')
      · exact h3 (by linear_combination -h')
    · have : t • w = 0 := add_eq_left.mp h
      rcases smul_eq_zero.mp this with h' | h'
      · exact ht0.ne' h'
      · have := hinj (sub_eq_zero.mp h')
        exact h1 (by linear_combination this)
  · -- `v` not adjacent to `j`: the turn at `v` is unchanged
    have hnext : deletionIndex j (v' + 1) = v + 1 := by rw [deletionIndex_next j hv1, hv']
    have hprev : deletionIndex j (v' - 1) = v - 1 := by
      have := deletionIndex_next j (i := v' - 1) (by
        intro h; exact hv0 (by linear_combination h))
      rw [sub_add_cancel, hv'] at this
      linear_combination -this
    rw [hnext, hprev] at hσR'
    rcases R.σ_pm with hs | hs <;> rw [hs] at hσR hσR' <;> linarith

end U4Zf_block

section U4Zg_block

/-! Downstream interface, part 2 (U4 helpers): convex ears, the canonical region of an embedded
polygon, and its ear relation; the leaf-level statements. -/

/-- Transport of a region along an equality of polygons. -/
theorem u4h_Region_transport {n : ℕ} {Q Q' : LabelledTuple n} (h : Q = Q') (R : u4h_Region Q) :
    ∃ R' : u4h_Region Q', R'.U = R.U ∧ R'.σ = R.σ := by
  subst h; exact ⟨R, rfl, rfl⟩

theorem u4h_ends_ne_of_det {P : LabelledTuple n} {j : ZMod n}
    (hdet : det (P j - P (j - 1)) (P (j + 1) - P (j - 1)) ≠ 0) : P (j - 1) ≠ P (j + 1) := by
  intro h
  apply hdet
  rw [h, sub_self]
  simp [det]

/-- The diagonal of a strict ear is clean (split form). -/
theorem u4h_ear_clean {n : ℕ} [NeZero n] (hn : 4 ≤ n) {P : LabelledTuple n} (hP : Embedded P)
    {j : ZMod n} (hdet : det (P j - P (j - 1)) (P (j + 1) - P (j - 1)) ≠ 0)
    (hstrict : earHull P j ∩ embeddedPolygonImage P = edgeSegment P (j - 1) ∪ edgeSegment P j) :
    ∀ k, Disjoint (edgeSegment P k)
      (openSegment ℝ (P (j - 1)) (P (j - 1 + ((2 : ℕ) : ZMod n)))) := by
  have hac := u4h_ends_ne_of_det hdet
  have hi2 : j - 1 + ((2 : ℕ) : ZMod n) = j + 1 := by push_cast; ring
  intro k
  rw [hi2, Set.disjoint_left]
  intro x hxk hxo
  by_cases hk1 : k = j - 1
  · rw [hk1, u4h_edgeSegment_prev] at hxk
    have hx' : x ∈ segment ℝ (P (j - 1)) (P j) ∩ segment ℝ (P (j - 1)) (P (j + 1)) :=
      ⟨hxk, openSegment_subset_segment ℝ _ _ hxo⟩
    rw [u4h_segment_inter_same_start hdet] at hx'
    have hx'' : x = P (j - 1) := hx'
    rw [hx''] at hxo
    exact hac (left_mem_openSegment_iff.mp hxo)
  by_cases hk2 : k = j
  · rw [hk2, u4h_edgeSegment_eq_segment, segment_symm] at hxk
    have hD' : det (P j - P (j + 1)) (P (j - 1) - P (j + 1)) ≠ 0 := by
      have e : det (P j - P (j + 1)) (P (j - 1) - P (j + 1)) =
          -det (P j - P (j - 1)) (P (j + 1) - P (j - 1)) := by
        simp only [det, Prod.fst_sub, Prod.snd_sub]; ring
      rw [e]; exact neg_ne_zero.mpr hdet
    have hx' : x ∈ segment ℝ (P (j + 1)) (P j) ∩ segment ℝ (P (j + 1)) (P (j - 1)) :=
      ⟨hxk, by rw [segment_symm]; exact openSegment_subset_segment ℝ _ _ hxo⟩
    rw [u4h_segment_inter_same_start hD'] at hx'
    have hx'' : x = P (j + 1) := hx'
    rw [hx''] at hxo
    exact hac (right_mem_openSegment_iff.mp hxo)
  exact u4h_edge_disjoint_openDiag' hP hac hstrict hk1 hk2 hxk hxo

/-- **Convex ear existence** for embedded polygons with at least four vertices. -/
theorem u4h_exists_convex_ear {n' : ℕ} (hn : 2 ≤ n') {P : LabelledTuple (n' + 2)}
    (hP : Embedded P) :
    ∃ j : ZMod (n' + 2), det (P j - P (j - 1)) (P (j + 1) - P (j - 1)) ≠ 0 ∧
      u4h_VertexEmpty P j ∧
      ∀ R : u4h_Region P, 0 < R.σ * det (P j - P (j - 1)) (P (j + 1) - P (j - 1)) := by
  obtain ⟨R0⟩ := u4h_region_exists (n' + 2) (by omega) P hP
  obtain ⟨j, hdet, hV, hside⟩ := u4h_exists_ear_of_region (by omega) hP R0
  refine ⟨j, hdet, hV, fun R => ?_⟩
  rw [u4h_sigma_unique (by omega) hP R R0]
  exact hside

/-- The triangle region as a face carrier for the half-disc lemma: a positively oriented
`Triangle` with carrier the ear triangle and an edge equal to the diagonal. -/
theorem u4h_ear_triangle {n : ℕ} (P : LabelledTuple n) (j : ZMod n)
    (hdet : det (P j - P (j - 1)) (P (j + 1) - P (j - 1)) ≠ 0) :
    ∃ (TT : Triangle) (k : Fin 3), TT.carrier = earHull P j ∧
      TT.edgeSeg k = segment ℝ (P (j - 1)) (P (j + 1)) ∧ TT.v (k + 2) = P j := by
  rcases lt_or_gt_of_ne hdet with hneg | hpos
  · have hD' : 0 < det (P (j + 1) - P (j - 1)) (P j - P (j - 1)) := by rw [u4h_det_swap']; linarith
    refine ⟨u4h_mkTri (P (j - 1)) (P (j + 1)) (P j) hD', 0, ?_, ?_, rfl⟩
    · rw [u4h_mkTri_carrier, earHull, u4h_hull3_comm]
    · rfl
  · refine ⟨u4h_mkTri (P (j - 1)) (P j) (P (j + 1)) hpos, 2, ?_, ?_, rfl⟩
    · rw [u4h_mkTri_carrier]; rfl
    · rw [u4h_mkTri_edgeSeg2, segment_symm]

/-- **The canonical region and an ear.** For a strict convex vertex-empty ear `j` the canonical
region of `P` is the union of the region of `deleteVertex P j` and the ear triangle, and the ear
triangle meets that region exactly in the diagonal. -/
theorem u4h_regionOf_ear {n' : ℕ} (hn : 2 ≤ n') {P : LabelledTuple (n' + 2)} (hP : Embedded P)
    {j : ZMod (n' + 2)} (hdet : det (P j - P (j - 1)) (P (j + 1) - P (j - 1)) ≠ 0)
    (hV : u4h_VertexEmpty P j)
    (hconv : ∀ R : u4h_Region P, 0 < R.σ * det (P j - P (j - 1)) (P (j + 1) - P (j - 1))) :
    earHull P j ∩ u4h_regionOf (deleteVertex P j) = segment ℝ (P (j - 1)) (P (j + 1)) ∧
      u4h_regionOf P = u4h_regionOf (deleteVertex P j) ∪ earHull P j := by
  have h4 : 4 ≤ n' + 2 := by omega
  have hinj := u4h_vertex_injective hP
  have h1 : (1 : ZMod (n' + 2)) ≠ 0 := u4h_one_ne_zero h4
  have h2 : (2 : ZMod (n' + 2)) ≠ 0 := u4h_two_ne_zero h4
  have h3 : (3 : ZMod (n' + 2)) ≠ 0 := u4h_three_ne_zero h4
  have hstrict := u4h_strict_ear_of_vertex_empty hP h4 hdet hV
  have hac := u4h_ends_ne_of_det hdet
  have hP' : Embedded (deleteVertex P j) :=
    u4h_embedded_deleteVertex (n := n' + 1) (by omega) hP hac hstrict
  obtain ⟨R⟩ := u4h_region_exists (n' + 2) (by omega) P hP
  obtain ⟨R'⟩ := u4h_region_exists (n' + 1) (by omega) _ hP'
  have hi2 : j - 1 + ((2 : ℕ) : ZMod (n' + 2)) = j + 1 := by push_cast; ring
  have hsub : u4h_subPoly P (j - 1 + ((2 : ℕ) : ZMod (n' + 2))) (n' + 2 - 2) = deleteVertex P j := by
    rw [hi2, u4h_deleteVertex_eq_subPoly]
    rfl
  obtain ⟨R2, hR2U, hR2σ⟩ := u4h_Region_transport hsub.symm R'
  have hclean := u4h_ear_clean h4 hP hdet hstrict
  have hP1 : Embedded (u4h_subPoly P (j - 1) 2) :=
    u4h_subPoly_embedded hP (le_refl 2) (by omega) hclean
  obtain ⟨R1, hR1U⟩ := u4h_triRegion' (u4h_subPoly P (j - 1) 2) hP1
  have hP10 : u4h_subPoly P (j - 1) 2 0 = P (j - 1) := u4h_subPoly_zero P (j - 1) 2
  have hP11 : u4h_subPoly P (j - 1) 2 1 = P j := by
    rw [u4h_subPoly_one P (j - 1) (by norm_num), sub_add_cancel]
  have hP12 : u4h_subPoly P (j - 1) 2 2 = P (j + 1) := by
    rw [u4h_subPoly_apply]
    have : (2 : ZMod (2 + 1)).val = 2 := by
      rw [show (2 : ZMod (2 + 1)) = ((2 : ℕ) : ZMod (2 + 1)) from Nat.cast_ofNat.symm,
        ZMod.val_natCast_of_lt (by norm_num)]
    rw [this, ← hi2]
  have hR1 : R1.U = earHull P j := by rw [hR1U, hP10, hP11, hP12]; rfl
  have hPjD : P j ∉ segment ℝ (P (j - 1)) (P (j + 1)) := by
    intro h
    apply hdet
    have := u4h_det_segment_zero h
    rw [u4h_det_swap']; rw [this]; ring
  -- polygon image of the second sub-polygon
  have hpoly2 : embeddedPolygonImage (u4h_subPoly P (j - 1 + ((2 : ℕ) : ZMod (n' + 2))) (n' + 2 - 2)) =
      embeddedPolygonImage (deleteVertex P j) := by rw [hsub]
  have hTinter : earHull P j ∩ embeddedPolygonImage (deleteVertex P j) =
      segment ℝ (P (j - 1)) (P (j + 1)) := u4h_earHull_inter_polygonImage_delete hP hstrict
  -- X1: the apex is outside the second region
  have X1 : ∃ s : ℕ, s < 2 ∧ ∃ x ∈ edgeSegment P (j - 1 + (s : ZMod (n' + 2))),
      x ∉ ({P (j - 1), P (j - 1 + ((2 : ℕ) : ZMod (n' + 2)))} : Set Plane) ∧ x ∉ R2.U := by
    refine ⟨0, by norm_num, P j, ?_, ?_, ?_⟩
    · rw [Nat.cast_zero, add_zero]
      have := u4h_end_mem_edgeSegment P (j - 1)
      rwa [sub_add_cancel] at this
    · rw [hi2]
      rintro (h | h)
      · exact h1 (by linear_combination (hinj h))
      · exact h1 (by linear_combination -(hinj (Set.mem_singleton_iff.mp h)))
    · intro hPj
      obtain ⟨v, hv⟩ := u4h_exists_lexmin hP
      by_cases hvj : v = j
      · -- the apex is the lexmin: not in the hull of the other vertices
        subst hvj
        apply u4h_lexmin_not_mem_hull hv ?_ (R2.hull hPj)
        rintro x ⟨k, rfl⟩
        rw [u4h_subPoly_apply, hi2]
        refine ⟨v + 1 + (k.val : ZMod (n' + 2)), ?_, rfl⟩
        intro h
        have hkv := ZMod.val_lt k
        have : ((1 + k.val : ℕ) : ZMod (n' + 2)) = 0 := by push_cast; linear_combination h
        exact u4h_natCast_ne_zero (n := n' + 2) (k := 1 + k.val) (by omega) (by omega) this
      · -- sides agree, so the ear triangle would be inside, forcing an interior diagonal point
        have hσ : R.σ = R2.σ := by
          rw [hR2σ]; exact u4h_sigma_ear hn hP hdet hstrict R R' (hconv R) hv hvj
        set a := P (j - 1) with ha
        set c := P (j + 1) with hc
        set D := segment ℝ a c with hD
        -- the ear triangle minus the diagonal lies in the interior of `R2.U`
        have hTD : earHull P j \ D ⊆ interior R2.U := by
          have hconvex : Convex ℝ (earHull P j \ D) := by
            rcases lt_or_gt_of_ne hdet with hneg | hpos
            · have hD' : 0 < det (P j - c) (a - c) := by
                have e : det (P j - c) (a - c) = -det (P j - a) (c - a) := by
                  simp only [det, Prod.fst_sub, Prod.snd_sub]; ring
                rw [e]; linarith
              have := u4h_convex_hull3_diff_edge hD'
              have e2 : earHull P j = convexHull ℝ {c, P j, a} := by
                unfold earHull; rw [u4h_hull3_rot, u4h_hull3_rot, u4h_hull3_comm]
              rw [hD, e2]; exact this
            · have := u4h_convex_hull3_diff_edge hpos
              rw [hD, segment_symm]; exact this
          have hsub' : earHull P j \ D ⊆ interior R2.U ∪ R2.Uᶜ := by
            rintro y ⟨hyT, hyD⟩
            by_cases hy : y ∈ R2.U
            · left
              by_contra hyi
              have hyf : y ∈ frontier R2.U := ⟨subset_closure hy, hyi⟩
              rw [R2.frontier_eq, hpoly2] at hyf
              exact hyD (hTinter ▸ ⟨hyT, hyf⟩)
            · right; exact hy
          rcases IsPreconnected.subset_or_subset isOpen_interior R2.isClosed.isOpen_compl
              (Set.disjoint_left.mpr fun y hy hy' => hy' (interior_subset hy)) hsub'
              hconvex.isPreconnected with h | h
          · exact h
          · exfalso
            exact h ⟨subset_convexHull ℝ _ (by simp), hPjD⟩ hPj
        have hTU : earHull P j ⊆ R2.U := by
          intro y hy
          by_cases hyD : y ∈ D
          · rw [hR2U]
            have hy' : y ∈ earHull P j ∩ embeddedPolygonImage (deleteVertex P j) := by
              rw [hTinter]; exact hyD
            have := hy'.2
            rw [← R'.frontier_eq] at this
            exact R'.isClosed.frontier_subset this
          · exact interior_subset (hTD ⟨hy, hyD⟩)
        -- the face of `R2.K` at the diagonal and the ear triangle cover a ball at the midpoint
        obtain ⟨F2, hF2, k2, hk2⟩ := R2.edge_face (-1)
        rw [u4h_subPoly_edgeSegment_last, u4h_split_second_start (by omega), hi2] at hk2
        have hside := R2.side (-1) F2 hF2 k2 (by
          rw [u4h_subPoly_edgeSegment_last, u4h_split_second_start (by omega), hi2]; exact hk2)
        rw [neg_add_cancel, u4h_subPoly_zero, u4h_subPoly_last,
          u4h_split_second_start (by omega)] at hside
        have ePj : P (j - 1 + ((2 : ℕ) : ZMod (n' + 2))) = P (j + 1) := by rw [hi2]
        rw [ePj] at hside
        obtain ⟨TT, kT, hTTc, hTTk, hTTapex⟩ := u4h_ear_triangle P j hdet
        set x : Plane := (1 / 2 : ℝ) • a + (1 / 2 : ℝ) • c with hx
        have hxo : x ∈ openSegment ℝ a c := u4h_midpoint_mem_openSegment _ _
        obtain ⟨ε1, hε1, hb1⟩ := u4h_face_halfdisc F2 k2 (by rw [hk2, segment_symm]) hxo
        obtain ⟨ε2, hε2, hb2⟩ := u4h_face_halfdisc TT kT hTTk hxo
        rw [hTTapex] at hb2
        have hxD : x ∈ D := openSegment_subset_segment ℝ _ _ hxo
        have hxfr : x ∈ frontier R2.U := by
          rw [R2.frontier_eq, hpoly2]
          have hx' : x ∈ earHull P j ∩ embeddedPolygonImage (deleteVertex P j) := by
            rw [hTinter]; exact hxD
          exact hx'.2
        apply disjoint_interior_frontier.notMem_of_mem_right hxfr
        rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff]
        refine ⟨min ε1 ε2, lt_min hε1 hε2, fun y hy => ?_⟩
        rw [Metric.mem_ball] at hy
        -- signs of the two apexes
        have hs2 : 0 < R.σ * det (c - a) (F2.v (k2 + 2) - a) := by rw [hσ]; exact hside
        have hsT : 0 < R.σ * -det (c - a) (P j - a) := by
          have e : -det (c - a) (P j - a) = det (P j - a) (c - a) := by rw [u4h_det_swap']; ring
          rw [e]; exact hconv R
        by_cases hy1 : 0 ≤ det (c - a) (F2.v (k2 + 2) - a) * det (c - a) (y - a)
        · exact R2.face_subset hF2 ((hb1 y (lt_of_lt_of_le hy (min_le_left _ _))).mpr hy1)
        · apply hTU
          rw [← hTTc]
          rw [hb2 y (lt_of_lt_of_le hy (min_le_right _ _))]
          have hy1' := not_le.mp hy1
          rcases R.σ_pm with hs | hs <;> rw [hs] at hs2 hsT <;> nlinarith
  -- X2: the vertex `P (j+2)` of the rest is not in the ear triangle
  have X2 : ∃ s : ℕ, s < n' + 2 - 2 ∧
      ∃ x ∈ edgeSegment P (j - 1 + ((2 : ℕ) : ZMod (n' + 2)) + (s : ZMod (n' + 2))),
      x ∉ ({P (j - 1), P (j - 1 + ((2 : ℕ) : ZMod (n' + 2)))} : Set Plane) ∧ x ∉ R1.U := by
    refine ⟨0, by omega, P (j + 2), ?_, ?_, ?_⟩
    · rw [Nat.cast_zero, add_zero, hi2]
      have := u4h_end_mem_edgeSegment P (j + 1)
      rwa [show j + 1 + 1 = j + 2 by ring] at this
    · rw [hi2]
      rintro (h | h)
      · exact h3 (by linear_combination (hinj h))
      · exact h1 (by linear_combination (hinj (Set.mem_singleton_iff.mp h)))
    · rw [hR1]
      intro hmem
      rcases hV (j + 2) hmem with h | h | h
      · exact h3 (by linear_combination h)
      · exact h2 (by linear_combination h)
      · exact h1 (by linear_combination h)
  set C : u4h_SplitCtx P (j - 1) 2 := u4h_SplitCtx.mk hP (le_refl 2) (by omega) hclean R1 R2 X1 X2
    with hC
  obtain ⟨G, hG⟩ := C.region'
  have hinter : R1.U ∩ R2.U = segment ℝ (P (j - 1)) (P (j - 1 + ((2 : ℕ) : ZMod (n' + 2)))) :=
    C.inter
  have ePj : P (j - 1 + ((2 : ℕ) : ZMod (n' + 2))) = P (j + 1) := by rw [hi2]
  rw [ePj] at hinter
  have hG' : G.U = R1.U ∪ R2.U := hG
  have hregP : u4h_regionOf P = G.U := (u4h_region_U_eq_regionOf (by omega) hP G).symm
  have hreg' : u4h_regionOf (deleteVertex P j) = R'.U :=
    (u4h_region_U_eq_regionOf (n := n' + 1) (by omega) hP' R').symm
  refine ⟨?_, ?_⟩
  · rw [hreg', ← hR2U, ← hR1]
    exact hinter
  · rw [hregP, hG', hR1, hR2U, hreg', Set.union_comm]

/-- Leaf-level: `U4_exists_ear`. -/
theorem u4h_U4_exists_ear {n : ℕ} [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple (n + 1))
    (hP : Embedded P) :
    ∃ j : ZMod (n + 1), Embedded (deleteVertex P j) ∧
      det (P j - P (j - 1)) (P (j + 1) - P (j - 1)) ≠ 0 ∧
      earHull P j ∩ embeddedPolygonImage (deleteVertex P j) = segment ℝ (P (j - 1)) (P (j + 1)) := by
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  obtain ⟨j, hdet, hV, -⟩ := u4h_exists_convex_ear (n' := n') (by omega) hP
  have hstrict := u4h_strict_ear_of_vertex_empty hP (by omega) hdet hV
  have hac := u4h_ends_ne_of_det hdet
  exact ⟨j, u4h_embedded_deleteVertex (by omega) hP hac hstrict, hdet,
    u4h_earHull_inter_polygonImage_delete hP hstrict⟩

/-- Leaf-level: `U4_exists_triangulation`, with the canonical region as the set. -/
theorem u4h_U4_exists_triangulation {n : ℕ} [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n)
    (hP : Embedded P) :
    ∃ K : Triangulation (u4h_regionOf P), frontier (u4h_regionOf P) = embeddedPolygonImage P ∧
      (∀ i, ∃ T ∈ K.faces, ∃ k : Fin 3, T.edgeSeg k = edgeSegment P i) ∧
      (∀ i, ∀ T ∈ K.faces, ∀ T' ∈ K.faces, edgeSegment P i ⊆ T.carrier →
        edgeSegment P i ⊆ T'.carrier → T.carrier = T'.carrier) ∧
      ∀ L, InsideModel L P → u4h_regionOf P ⊆ interior (square L) := by
  obtain ⟨R⟩ := u4h_region_exists n hn P hP
  have hU := u4h_region_U_eq_regionOf hn hP R
  rw [← hU]
  refine ⟨R.K, R.frontier_eq, R.edge_face, R.edge_unique, fun L hL x hx => ?_⟩
  have hsub : convexHull ℝ (Set.range P) ⊆ Metric.ball 0 L := by
    apply convexHull_min _ (convex_ball _ _)
    rintro y ⟨i, rfl⟩
    exact u4h_mem_ball_of_supNorm_lt (hL i)
  exact u4h_ball_subset_interior_square L (hsub (R.hull hx))

/-- Leaf-level: `U4_triangle_base`. -/
theorem u4h_U4_triangle_base (P : LabelledTuple 3) (hP : Embedded P) :
    det (P 1 - P 0) (P 2 - P 0) ≠ 0 ∧ embeddedPolygonImage P = frontier (earHull P 1) := by
  have hD := u4h_tri3_det_ne_zero P hP
  refine ⟨hD, ?_⟩
  have h10 : (1 : ZMod 3) - 1 = 0 := by decide
  have h11 : (1 : ZMod 3) + 1 = 2 := by decide
  rw [earHull, h10, h11, u4h_polygonImage_zmod3]
  rcases lt_or_gt_of_ne hD with hneg | hpos
  · have hD' : 0 < det (P 2 - P 0) (P 1 - P 0) := by rw [u4h_det_swap']; linarith
    rw [u4h_hull3_comm, u4h_frontier_hull3 hD', segment_symm ℝ (P 0) (P 2),
      segment_symm ℝ (P 2) (P 1), segment_symm ℝ (P 1) (P 0)]
    ext x; simp only [Set.mem_union]; tauto
  · rw [u4h_frontier_hull3 hpos]

/-- The canonical region of an embedded triangle is its hull (the base of the ear sequence). -/
theorem u4h_regionOf_triangle (P : LabelledTuple 3) (hP : Embedded P) :
    u4h_regionOf P = earHull P 1 := by
  obtain ⟨R, hRU⟩ := u4h_triRegion' P hP
  rw [← u4h_region_U_eq_regionOf (le_refl 3) hP R, hRU]
  have h10 : (1 : ZMod 3) - 1 = 0 := by decide
  have h11 : (1 : ZMod 3) + 1 = 2 := by decide
  rw [earHull, h10, h11]

/-- The canonical region: frontier, compactness, hull bound, model square. -/
theorem u4h_regionOf_spec {n : ℕ} [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Embedded P) :
    frontier (u4h_regionOf P) = embeddedPolygonImage P ∧ IsCompact (u4h_regionOf P) ∧
      u4h_regionOf P ⊆ convexHull ℝ (Set.range P) ∧
      ∀ L, InsideModel L P → u4h_regionOf P ⊆ interior (square L) := by
  obtain ⟨R⟩ := u4h_region_exists n hn P hP
  have hU := u4h_region_U_eq_regionOf hn hP R
  rw [← hU]
  refine ⟨R.frontier_eq, u4h_triangulation_isCompact R.K, R.hull, fun L hL x hx => ?_⟩
  have hsub : convexHull ℝ (Set.range P) ⊆ Metric.ball 0 L := by
    apply convexHull_min _ (convex_ball _ _)
    rintro y ⟨i, rfl⟩
    exact u4h_mem_ball_of_supNorm_lt (hL i)
  exact u4h_ball_subset_interior_square L (hsub (R.hull hx))

end U4Zg_block


/-- U4: the polygon image is compact. -/
theorem U4_polygonImage_isCompact [NeZero n] (P : LabelledTuple n) : IsCompact (embeddedPolygonImage P) := by
  exact u4h_polygonImage_isCompact P

/-- U4: the traversal image is the polygon image. -/
theorem U4_range_traversal [NeZero n] (P : LabelledTuple n) : range (traversal P) = embeddedPolygonImage P := by
  exact u4h_range_traversal P

/-- U4 (sm-3:439 "inside a large rectangle"): some model square contains the polygon. -/
theorem U4_exists_insideModel [NeZero n] (P : LabelledTuple n) : ∃ L : ℝ, 0 < L ∧ InsideModel L P := by
  exact u4h_exists_insideModel P

/-- U4: `InsideModel L P` puts the polygon image strictly inside `Q_L`. -/
theorem U4_polygonImage_subset_interior_square [NeZero n] {L : ℝ} (P : LabelledTuple n)
    (hL : InsideModel L P) : embeddedPolygonImage P ⊆ interior (square L) ∧ 0 < L := by
  exact u4h_polygonImage_subset_interior_square P hL

/-- U4: an embedded polygon has at least three vertices. -/
theorem U4_three_le_of_embedded [NeZero n] (P : LabelledTuple n) (hP : Embedded P) : 3 ≤ n := by
  exact u4h_three_le_of_embedded P hP

/-- U4 (base case): an embedded triangle bounds its convex hull. -/
theorem U4_triangle_base (P : LabelledTuple 3) (hP : Embedded P) :
    det (P 1 - P 0) (P 2 - P 0) ≠ 0 ∧ embeddedPolygonImage P = frontier (earHull P 1) := by
  exact u4h_U4_triangle_base P hP

/-- U4 (Meisters' two ears, sm-3:437-439 spirit): an embedded polygon with at least four vertices has
an ear: a vertex `j` with nonzero turn whose ear triangle meets the rest of the polygon exactly in
the diagonal, and whose deletion is again embedded. -/
theorem U4_exists_ear [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple (n + 1)) (hP : Embedded P) :
    ∃ j : ZMod (n + 1), Embedded (deleteVertex P j) ∧
      det (P j - P (j - 1)) (P (j + 1) - P (j - 1)) ≠ 0 ∧
      earHull P j ∩ embeddedPolygonImage (deleteVertex P j) = segment ℝ (P (j - 1)) (P (j + 1)) := by
  exact u4h_U4_exists_ear hn P hP

/-- U4 (ear-cut identity): the polygon image of `P` is that of the cut polygon with the diagonal
replaced by the two ear edges.

W1 ASSEMBLY (rule 3): hypotheses `hP : Embedded P`, `hac : P (j - 1) ≠ P (j + 1)` and
`hstrict : earHull P j ∩ embeddedPolygonImage P = edgeSegment P (j - 1) ∪ edgeSegment P j` (a strict ear) added.
The skeleton form (no hypothesis on `P`, `j`) is false (W1_U4_REPORT.md §2: `n = 4`,
`P = (0,0),(2,0),(2,2),(0,3),(1,-1)`, `j = 1`).  Every ear produced by `U4_exists_ear` /
`u4h_exists_convex_ear` satisfies the added hypotheses (`u4h_strict_ear_of_vertex_empty`).  No other
unit consumes this leaf. -/
theorem U4_polygonImage_ear [NeZero n] (P : LabelledTuple (n + 1)) (hP : Embedded P) (j : ZMod (n + 1))
    (hac : P (j - 1) ≠ P (j + 1))
    (hstrict : earHull P j ∩ embeddedPolygonImage P = edgeSegment P (j - 1) ∪ edgeSegment P j) :
    embeddedPolygonImage P = (embeddedPolygonImage (deleteVertex P j) \ openSegment ℝ (P (j - 1)) (P (j + 1))) ∪
      segment ℝ (P (j - 1)) (P j) ∪ segment ℝ (P j) (P (j + 1)) := by
  have h := u4h_polygonImage_ear hP hac hstrict
  rwa [u4h_edgeSegment_prev, u4h_edgeSegment_eq_segment] at h

/-- U4 (output, sm-3:437-443 "triangulate ... the polygon"): an embedded polygon bounds a compact
set `U` with a triangulation in which every edge of `P` is an edge of exactly one face, `frontier U`
is the circle, and `U` lies strictly inside every model square containing `P`. -/
theorem U4_exists_triangulation [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Embedded P) :
    ∃ (U : Set Plane) (K : Triangulation U), frontier U = embeddedPolygonImage P ∧
      (∀ i, ∃ T ∈ K.faces, ∃ k : Fin 3, T.edgeSeg k = edgeSegment P i) ∧
      (∀ i, ∀ T ∈ K.faces, ∀ T' ∈ K.faces, edgeSegment P i ⊆ T.carrier →
        edgeSegment P i ⊆ T'.carrier → T.carrier = T'.carrier) ∧
      ∀ L, InsideModel L P → U ⊆ interior (square L) := by
  obtain ⟨K, h1, h2, h3, h4⟩ := u4h_U4_exists_triangulation hn P hP
  exact ⟨_, K, h1, h2, h3, h4⟩

/-! ### U5 (sequential) — the ear-cut ambient homeomorphism -/

/-- U5 (sm-3:437-443 realised ambiently, PLAN_FINAL §3.1): cutting an ear `j` of `P` is realised by
a positive PL homeomorphism `h` of the plane, the identity outside a compact subset of `int Q_L`,
carrying the region `U'` bounded by the cut polygon onto `U' ∪ ear` and the cut circle onto the
circle of `P`.

W1 ASSEMBLY (rule 3, flagged by U4): hypothesis `hcut : earHull P j ∩ U' = segment ℝ (P (j - 1)) (P (j + 1))`
added (equivalently `P j ∉ U'`).  Without it the statement is false: for a reflex ear (a notch) all
skeleton hypotheses hold with `earHull P j ⊆ U'`, so `U' ∪ earHull P j = U'` and the clause
`frontier (U' ∪ earHull P j) = embeddedPolygonImage P` fails (`frontier U' = embeddedPolygonImage (deleteVertex P j)`).
U6 obtains `hcut` from `u4h_regionOf_ear` with `U' := u4h_regionOf (deleteVertex P j)`
(W1_U4_REPORT.md §4). -/
theorem U5_exists_ear_homeo [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple (n + 1)) (hP : Embedded P)
    (j : ZMod (n + 1)) (hP' : Embedded (deleteVertex P j))
    (hturn : det (P j - P (j - 1)) (P (j + 1) - P (j - 1)) ≠ 0)
    (hear : earHull P j ∩ embeddedPolygonImage (deleteVertex P j) = segment ℝ (P (j - 1)) (P (j + 1)))
    (U' : Set Plane) (K' : Triangulation U') (hU' : frontier U' = embeddedPolygonImage (deleteVertex P j))
    (hcut : earHull P j ∩ U' = segment ℝ (P (j - 1)) (P (j + 1)))
    (hedge : ∀ T ∈ K'.faces, ∀ T' ∈ K'.faces, segment ℝ (P (j - 1)) (P (j + 1)) ⊆ T.carrier →
      segment ℝ (P (j - 1)) (P (j + 1)) ⊆ T'.carrier → T.carrier = T'.carrier)
    (hface : ∃ T ∈ K'.faces, ∃ k : Fin 3, T.edgeSeg k = segment ℝ (P (j - 1)) (P (j + 1)))
    {L : ℝ} (hL : InsideModel L P) (hU'L : U' ⊆ interior (square L)) :
    ∃ (h : Plane ≃ₜ Plane) (Kh : Triangulation (square L)) (Kin : Triangulation U'),
      IsPositivePLOn h Kh ∧ IsPositivePLOn h Kin ∧ Kin.Refines K' ∧
      (∀ x, L ≤ supNorm x → h x = x) ∧
      h '' U' = U' ∪ earHull P j ∧ h '' embeddedPolygonImage (deleteVertex P j) = embeddedPolygonImage P ∧
      frontier (U' ∪ earHull P j) = embeddedPolygonImage P ∧ U' ∪ earHull P j ⊆ interior (square L) := by
  sorry

/-- U5: the ear-cut homeomorphism sends the faces of the refined triangulation `Kin` of `U'` to a
triangulation of `U' ∪ ear` in which every edge of `P` is an edge of exactly one face. -/
theorem U5_pushforward_edges [NeZero n] (P : LabelledTuple (n + 1)) (j : ZMod (n + 1))
    (U' : Set Plane) (Kin : Triangulation U') (h : Plane ≃ₜ Plane) (hh : IsPositivePLOn h Kin)
    (hU : h '' U' = U' ∪ earHull P j) (hC : h '' embeddedPolygonImage (deleteVertex P j) = embeddedPolygonImage P)
    (hedge' : ∀ i, ∃ T ∈ Kin.faces, ∃ k : Fin 3, T.edgeSeg k = edgeSegment (deleteVertex P j) i)
    (huniq' : ∀ i, ∀ T ∈ Kin.faces, ∀ T' ∈ Kin.faces, edgeSegment (deleteVertex P j) i ⊆ T.carrier →
      edgeSegment (deleteVertex P j) i ⊆ T'.carrier → T.carrier = T'.carrier) :
    ∃ K : Triangulation (U' ∪ earHull P j),
      (∀ i, ∃ T ∈ K.faces, ∃ k : Fin 3, T.edgeSeg k = edgeSegment P i) ∧
      ∀ i, ∀ T ∈ K.faces, ∀ T' ∈ K.faces, edgeSegment P i ⊆ T.carrier →
        edgeSegment P i ⊆ T'.carrier → T.carrier = T'.carrier := by
  sorry

/-! ### U6 (sequential) — 57a and 57e via the ambient parametrisation -/

/-- The ambient parametrisation of the bounded region (PLAN_FINAL §3.1): a base triangle `T₀` inside
`int Q_L` and a positive PL homeomorphism `H` of the plane (`H = h_m ∘ ⋯ ∘ h_1`), the identity
outside `int Q_L`, PL on a triangulation of `Q_L` and on one of `T₀`, with `H (∂T₀) = C`. -/
structure AmbientParam [NeZero n] (P : LabelledTuple n) (L : ℝ) where
  /-- the base triangle (the last 3-gon of the ear sequence) -/
  T₀ : Triangle
  /-- the composite ear-cut homeomorphism -/
  H : Plane ≃ₜ Plane
  /-- a triangulation of the model square on which `H` is positive PL -/
  K : Triangulation (square L)
  /-- a triangulation of the base triangle on which `H` is positive PL -/
  KT : Triangulation T₀.carrier
  pl : IsPositivePLOn H K
  plT : IsPositivePLOn H KT
  /-- `H` is the identity outside `int Q_L` -/
  fix : ∀ x, L ≤ supNorm x → H x = x
  inside : T₀.carrier ⊆ interior (square L)
  /-- `H (∂T₀) = C` -/
  boundary : H '' frontier T₀.carrier = embeddedPolygonImage P

/-- U6 (sm-3:437-443, the ear induction assembled): every embedded polygon inside `Q_L` has an
ambient parametrisation. -/
theorem U6_exists_ambientParam [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Embedded P)
    {L : ℝ} (hL : InsideModel L P) : Nonempty (AmbientParam P L) := by
  sorry

/-- U6: the complement of the frontier of a triangle has exactly the two components `int T₀`, `T₀ᶜ`. -/
theorem U6_compl_frontier_triangle (T : Triangle) :
    (frontier T.carrier)ᶜ = interior T.carrier ∪ (T.carrier)ᶜ ∧
      IsConnected (interior T.carrier) ∧ IsConnected (T.carrier)ᶜ ∧
      Disjoint (interior T.carrier) (T.carrier)ᶜ := by
  sorry

/-- U6 (sm-3:486-489 "the region of the point at infinity"): the exterior region is the image of
the complement of the base triangle together with `∞`. -/
theorem U6_exteriorRegion_eq [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Embedded P) {L : ℝ}
    (A : AmbientParam P L) :
    exteriorRegion P = ((↑) : Plane → Sphere) '' (A.H '' (A.T₀.carrier)ᶜ) ∪ {∞} := by
  sorry

/-- U6: the interior region is the image of the open base triangle. -/
theorem U6_interiorRegion_eq [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Embedded P) {L : ℝ}
    (A : AmbientParam P L) :
    interiorRegion P = ((↑) : Plane → Sphere) '' (A.H '' interior A.T₀.carrier) := by
  sorry

/-- U6: the interior region is open and connected in the sphere. -/
theorem U6_interiorRegion_isConnected [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Embedded P) :
    IsConnected (interiorRegion P) ∧ IsOpen (interiorRegion P) := by
  sorry

/-- U6 (57a, sm-3:430-431 / 486-489): exactly two complementary regions in the sphere. -/
theorem U6_two_regions [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Embedded P) :
    Nat.card (ConnectedComponents (sphereComplement P)) = 2 := by
  sorry

/-- U6 (57e, sm-3:434 / 448-456): the region of `∞` is the unbounded one, the other is a bounded
plane region. -/
theorem U6_exterior [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Embedded P) :
    ∞ ∈ exteriorRegion P ∧ (∀ z ∈ interiorRegion P, z ≠ ∞) ∧
      Bornology.IsBounded (((↑) : Plane → Sphere) ⁻¹' interiorRegion P) ∧
      ¬ Bornology.IsBounded (((↑) : Plane → Sphere) ⁻¹' exteriorRegion P) := by
  sorry

/-- U6 (bridge, plane form of 57a): the exterior region minus `∞` stays connected. -/
theorem U6_two_regions_plane [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Embedded P) :
    Nat.card (ConnectedComponents ((embeddedPolygonImage P)ᶜ : Set Plane)) = 2 := by
  sorry

/-! ### U7 (sequential) — 57b for the interior region -/

/-- U7: the closed bounded region is `H (T₀)`. -/
theorem U7_closure_interiorRegion_eq [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Embedded P)
    {L : ℝ} (A : AmbientParam P L) :
    closure (interiorRegion P) = ((↑) : Plane → Sphere) '' (A.H '' A.T₀.carrier) := by
  sorry

/-- U7 (sm-3:490-493, the interior disc): `H (T₀)` is a plane PL disc. -/
theorem U7_isPLDisc_image [NeZero n] (P : LabelledTuple n) {L : ℝ} (A : AmbientParam P L) :
    IsPLDisc (A.H '' A.T₀.carrier) := by
  sorry

/-- U7: the cap chart sees nothing of the closed bounded region. -/
theorem U7_chartPart_cap_empty [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Embedded P)
    {L : ℝ} (hL : InsideModel L P) : chartPart L true (closure (interiorRegion P)) = ∅ := by
  sorry

/-- U7: `planeOf ∘ H⁻¹` is positive PL to the plane on the closed bounded region. -/
theorem U7_isPositivePLToPlane_inv [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Embedded P)
    {L : ℝ} (hL : InsideModel L P) (A : AmbientParam P L) :
    IsPositivePLToPlane L (closure (interiorRegion P)) (A.H.symm ∘ planeOf) := by
  sorry

/-- U7 (57b interior, sm-3:431 / 490-493): the closure of the bounded region is a PL disc of the
sphere with boundary the circle. -/
theorem U7_pl_discs_inner [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Embedded P) (L : ℝ)
    (hL : InsideModel L P) : IsPLDiscSphere L (closure (regionOf P Side.inner)) (sphereCircle P) := by
  sorry

/-- U7 (bridge): a sphere PL disc lying in the plane chart is a plane PL disc. -/
theorem U7_isPLDisc_of_isPLDiscSphere {L : ℝ} {S B : Set Sphere} (hL : 0 < L)
    (hS : S ⊆ ((↑) : Plane → Sphere) '' square L) (h : IsPLDiscSphere L S B) :
    IsPLDisc (((↑) : Plane → Sphere) ⁻¹' S) := by
  sorry

/-- U7 (bridge): the closed bounded region, as a plane set, is a plane PL disc. -/
theorem U7_isPLDisc_closure_interior [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Embedded P) :
    IsPLDisc (((↑) : Plane → Sphere) ⁻¹' closure (interiorRegion P)) := by
  sorry

/-! ### U8 (sequential) — 57b for the exterior region -/

/-! ### U8 helpers (`u8h_`), 2026-09-19: continuity of the cap chart and its inverse -/

theorem u8h_continuous_supNorm : Continuous supNorm := by
  unfold supNorm; fun_prop

theorem u8h_mem_interior_square_iff {L : ℝ} (x : Plane) : x ∈ interior (square L) ↔ supNorm x < L := by
  constructor
  · exact fun h => u3h_interior_square_subset L h
  · intro h
    exact interior_maximal (t := {y : Plane | supNorm y < L}) (fun y (hy : supNorm y < L) => le_of_lt hy)
      (isOpen_lt u8h_continuous_supNorm continuous_const) h

/-- U8 helper: `capInvFun L` is continuous away from `0`. -/
theorem u8h_continuousAt_capInvFun (L : ℝ) {y : Plane} (hy : y ≠ 0) :
    ContinuousAt (capInvFun L) y := by
  have hN : supNorm y ≠ 0 := (u3h_supNorm_pos hy).ne'
  unfold capInvFun
  refine ContinuousAt.smul (f := fun y : Plane => L / supNorm y ^ 2)
    (g := fun y : Plane => ((y.1, -y.2) : Plane)) ?_ ?_
  · apply ContinuousAt.div continuousAt_const
    · exact (u8h_continuous_supNorm.pow 2).continuousAt
    · exact pow_ne_zero 2 hN
  · fun_prop

/-- U8 helper: a plane set of bounded sup norm. -/
theorem u8h_isCompact_supNorm_le {s : Set Plane} (hs : IsCompact s) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ x ∈ s, supNorm x ≤ R := by
  obtain ⟨R, hR⟩ := hs.isBounded.subset_closedBall 0
  refine ⟨max R 0, le_max_right _ _, fun x hx => ?_⟩
  have := hR hx
  rw [Metric.mem_closedBall, dist_zero_right, u3h_norm_eq_supNorm] at this
  exact this.trans (le_max_left _ _)

/-- U8 helper: `capInvFun L` tends to `0` at infinity. -/
theorem u8h_tendsto_capInvFun_cocompact {L : ℝ} (hL : 0 < L) :
    Filter.Tendsto (capInvFun L) (Filter.coclosedCompact Plane) (nhds 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  rw [Filter.eventually_iff, Filter.hasBasis_coclosedCompact.mem_iff]
  refine ⟨{x | supNorm x ≤ L / ε}, ⟨?_, ?_⟩, ?_⟩
  · exact isClosed_le u8h_continuous_supNorm continuous_const
  · have : {x : Plane | supNorm x ≤ L / ε} = Metric.closedBall 0 (L / ε) := by
      ext x; simp only [mem_ofPred_eq, Metric.mem_closedBall, dist_zero_right, u3h_norm_eq_supNorm]
    rw [this]; exact isCompact_closedBall _ _
  · intro x hx
    simp only [mem_compl_iff, mem_ofPred_eq, not_le] at hx
    have hx0 : x ≠ 0 := by
      rintro rfl
      simp only [supNorm, Prod.fst_zero, Prod.snd_zero, abs_zero, max_self] at hx
      have : 0 < L / ε := div_pos hL hε
      linarith
    simp only [mem_ofPred_eq, dist_zero_right, u3h_norm_eq_supNorm]
    rw [u3h_supNorm_capInvFun hL hx0]
    have hN := u3h_supNorm_pos hx0
    rw [div_lt_iff₀ hN]
    rw [div_lt_iff₀ hε] at hx
    linarith

/-- U8 helper: the cap inverse chart is continuous on the whole sphere. -/
theorem u8h_continuous_capInv {L : ℝ} (hL : 0 < L) :
    ∀ z : Sphere, z ≠ (0 : Plane) → ContinuousAt (modelChartInv L true) z := by
  intro z hz
  induction z using OnePoint.rec with
  | infty =>
    rw [OnePoint.continuousAt_infty']
    show Filter.Tendsto (fun x : Plane => capInvFun L x) _ (nhds 0)
    exact u8h_tendsto_capInvFun_cocompact hL
  | coe x =>
    rw [OnePoint.continuousAt_coe]
    show ContinuousAt (fun x : Plane => capInvFun L x) x
    exact u8h_continuousAt_capInvFun L (fun h => hz (by rw [h]))


/-- U8 helper: `capChart L` is continuous on `Q_1` (at `0` it tends to `∞`). -/
theorem u8h_continuousOn_capChart {L : ℝ} (hL : 0 < L) : ContinuousOn (capChart L) (square 1) := by
  intro y hy
  by_cases hy0 : y = 0
  · subst hy0
    rw [ContinuousWithinAt, show capChart L 0 = ∞ by simp [capChart]]
    rw [OnePoint.hasBasis_nhds_infty.tendsto_right_iff]
    rintro s ⟨-, hsc⟩
    obtain ⟨R, hR0, hR⟩ := u8h_isCompact_supNorm_le hsc
    have hδ : 0 < L / (R + 1) := div_pos hL (by linarith)
    have hnhds : {y : Plane | supNorm y < L / (R + 1)} ∈ nhds (0 : Plane) := by
      apply (isOpen_lt u8h_continuous_supNorm continuous_const).mem_nhds
      show supNorm (0 : Plane) < L / (R + 1)
      rw [show supNorm (0 : Plane) = 0 by simp [supNorm]]
      exact hδ
    filter_upwards [nhdsWithin_le_nhds hnhds] with y hy
    by_cases h0 : y = 0
    · subst h0; simp [capChart]
    · left
      refine ⟨capInvFun L y, fun hmem => ?_, by simp [capChart, h0]⟩
      have h1 := hR _ hmem
      rw [u3h_supNorm_capInvFun hL h0] at h1
      have hN := u3h_supNorm_pos h0
      rw [div_le_iff₀ hN] at h1
      rw [lt_div_iff₀ (by linarith)] at hy
      nlinarith
  · apply ContinuousAt.continuousWithinAt
    have hev : (fun z : Plane => ((capInvFun L z : Plane) : Sphere)) =ᶠ[nhds y] capChart L := by
      filter_upwards [isOpen_ne.mem_nhds hy0] with z hz
      simp [capChart, hz]
    exact (OnePoint.continuous_coe.continuousAt.comp
      (u8h_continuousAt_capInvFun L hy0)).congr_of_eventuallyEq hev.symm

/-! ### U8 helpers: the ambient homeomorphism on the square, `OnePoint.map`, transport of triangulations -/

/-- U8 helper: `H` maps the open square `int Q_L` onto itself (it is the identity outside). -/
theorem u8h_H_image_interior [NeZero n] {P : LabelledTuple n} {L : ℝ} (A : AmbientParam P L) :
    A.H '' interior (square L) = interior (square L) := by
  have key : ∀ x, supNorm x < L → supNorm (A.H x) < L := by
    intro x hx
    by_contra h
    push Not at h
    have h2 : A.H (A.H x) = A.H x := A.fix _ h
    have h3 := A.H.injective h2
    rw [h3] at h
    linarith
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (u8h_mem_interior_square_iff _).2 (key x ((u8h_mem_interior_square_iff x).1 hx))
  · intro hy
    refine ⟨A.H.symm y, ?_, A.H.apply_symm_apply y⟩
    rw [u8h_mem_interior_square_iff]
    by_contra h
    push Not at h
    have := A.fix _ h
    rw [A.H.apply_symm_apply] at this
    have hy' := (u8h_mem_interior_square_iff y).1 hy
    rw [← this] at h
    linarith

theorem u8h_H_symm_fix [NeZero n] {P : LabelledTuple n} {L : ℝ} (A : AmbientParam P L) {x : Plane}
    (hx : L ≤ supNorm x) : A.H.symm x = x := by
  have := A.fix x hx
  rw [← this, A.H.symm_apply_apply, this]

theorem u8h_H_image_square [NeZero n] {P : LabelledTuple n} {L : ℝ} (A : AmbientParam P L) :
    A.H '' square L = square L := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    by_cases h : supNorm x < L
    · have := (u8h_mem_interior_square_iff x).2 h
      have h2 : A.H x ∈ interior (square L) := by
        rw [← u8h_H_image_interior A]; exact ⟨x, this, rfl⟩
      exact interior_subset h2
    · push Not at h
      rw [A.fix x h]; exact hx
  · intro hy
    by_cases h : supNorm y < L
    · have := (u8h_mem_interior_square_iff y).2 h
      rw [← u8h_H_image_interior A] at this
      obtain ⟨x, hx, rfl⟩ := this
      exact ⟨x, interior_subset hx, rfl⟩
    · push Not at h
      exact ⟨y, hy, A.fix y h⟩

/-- U8 helper: `OnePoint.map` of a plane homeomorphism is a homeomorphism of the sphere. -/
theorem u8h_isHomeoOnto_onePoint_map (e : Plane ≃ₜ Plane) (S : Set Sphere) :
    IsHomeoOnto S (OnePoint.map e '' S) (OnePoint.map e) :=
  ⟨(Homeomorph.onePointCongr e).image S, fun _ => rfl⟩

theorem u8h_onePoint_map_bijective (e : Plane ≃ₜ Plane) : Function.Bijective (OnePoint.map e) :=
  (Homeomorph.onePointCongr e).bijective

theorem u8h_onePoint_map_image_coe (e : Plane ≃ₜ Plane) (S : Set Plane) :
    OnePoint.map e '' (((↑) : Plane → Sphere) '' S) = ((↑) : Plane → Sphere) '' (e '' S) := by
  ext z; constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩; exact ⟨e x, ⟨x, hx, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩; exact ⟨(x : Sphere), ⟨x, hx, rfl⟩, rfl⟩

/-! ### U8 helpers (`u8h_f_`): the fan toolkit of U10 (`u10h_rg … u10h_fan_triangulation`, `u10h_gap …
u10h_cover`), copied verbatim with the prefix `u10h_` → `u8h_f_` because U8 precedes U10 in the file
(W2_U8_REPORT.md §4; U12 may dedupe by moving U10's block before U8). -/

/-! #### U10 helpers for `U10_fan_extension` (radial gauge, sectors, marks, fan, cone) -/

/-- U10 helper: the translate of `D` bringing `z` to the origin. -/
def u8h_f_D0 (D : Set Plane) (z : Plane) : Set Plane := (Homeomorph.addRight z) ⁻¹' D

/-- U10 helper: the radial gauge of `D` about `z`. -/
noncomputable def u8h_f_rg (D : Set Plane) (z : Plane) (x : Plane) : ℝ := gauge (u8h_f_D0 D z) (x - z)

theorem u8h_f_mem_D0 {D : Set Plane} {z w : Plane} : w ∈ u8h_f_D0 D z ↔ w + z ∈ D := Iff.rfl

theorem u8h_f_D0_convex {D : Set Plane} (hD : Link.IsDisc D) (z : Plane) : Convex ℝ (u8h_f_D0 D z) := by
  have h : u8h_f_D0 D z = (fun x => x + z) ⁻¹' D := by ext w; simp [u8h_f_D0]
  rw [h]; exact hD.convex.translate_preimage_left z

theorem u8h_f_D0_isCompact {D : Set Plane} (hD : Link.IsDisc D) (z : Plane) : IsCompact (u8h_f_D0 D z) :=
  (Homeomorph.addRight z).isCompact_preimage.mpr hD.isCompact

theorem u8h_f_D0_interior {D : Set Plane} (z : Plane) :
    interior (u8h_f_D0 D z) = (Homeomorph.addRight z) ⁻¹' interior D :=
  ((Homeomorph.addRight z).preimage_interior D).symm

theorem u8h_f_D0_frontier {D : Set Plane} (z : Plane) :
    frontier (u8h_f_D0 D z) = (Homeomorph.addRight z) ⁻¹' frontier D :=
  ((Homeomorph.addRight z).preimage_frontier D).symm

theorem u8h_f_D0_closure {D : Set Plane} (z : Plane) :
    closure (u8h_f_D0 D z) = (Homeomorph.addRight z) ⁻¹' closure D :=
  ((Homeomorph.addRight z).preimage_closure D).symm

theorem u8h_f_D0_nhds {D : Set Plane} {z : Plane} (hz : z ∈ interior D) : u8h_f_D0 D z ∈ nhds (0 : Plane) := by
  rw [mem_nhds_iff]
  refine ⟨interior (u8h_f_D0 D z), interior_subset, isOpen_interior, ?_⟩
  rw [u8h_f_D0_interior]
  simpa using hz

theorem u8h_f_D0_absorbent {D : Set Plane} {z : Plane} (hz : z ∈ interior D) : Absorbent ℝ (u8h_f_D0 D z) :=
  absorbent_nhds_zero (u8h_f_D0_nhds hz)

theorem u8h_f_D0_bounded {D : Set Plane} (hD : Link.IsDisc D) (z : Plane) :
    Bornology.IsVonNBounded ℝ (u8h_f_D0 D z) :=
  (u8h_f_D0_isCompact hD z).isVonNBounded ℝ

theorem u8h_f_rg_nonneg (D : Set Plane) (z x : Plane) : 0 ≤ u8h_f_rg D z x := gauge_nonneg _

theorem u8h_f_rg_lt_one_iff {D : Set Plane} (hD : Link.IsDisc D) {z : Plane} (hz : z ∈ interior D) (x : Plane) :
    u8h_f_rg D z x < 1 ↔ x ∈ interior D := by
  unfold u8h_f_rg
  rw [gauge_lt_one_iff_mem_interior (u8h_f_D0_convex hD z) (u8h_f_D0_nhds hz), u8h_f_D0_interior]
  simp

theorem u8h_f_rg_le_one_iff {D : Set Plane} (hD : Link.IsDisc D) {z : Plane} (hz : z ∈ interior D) (x : Plane) :
    u8h_f_rg D z x ≤ 1 ↔ x ∈ D := by
  unfold u8h_f_rg
  rw [gauge_le_one_iff_mem_closure (u8h_f_D0_convex hD z) (u8h_f_D0_nhds hz), u8h_f_D0_closure,
    hD.isCompact.isClosed.closure_eq]
  simp

theorem u8h_f_rg_eq_one_iff {D : Set Plane} (hD : Link.IsDisc D) {z : Plane} (hz : z ∈ interior D) (x : Plane) :
    u8h_f_rg D z x = 1 ↔ x ∈ frontier D := by
  unfold u8h_f_rg
  rw [gauge_eq_one_iff_mem_frontier (u8h_f_D0_convex hD z) (u8h_f_D0_nhds hz), u8h_f_D0_frontier]
  simp

theorem u8h_f_rg_eq_zero_iff {D : Set Plane} (hD : Link.IsDisc D) {z : Plane} (hz : z ∈ interior D) (x : Plane) :
    u8h_f_rg D z x = 0 ↔ x = z := by
  unfold u8h_f_rg
  rw [gauge_eq_zero (u8h_f_D0_absorbent hz) (u8h_f_D0_bounded hD z), sub_eq_zero]

theorem u8h_f_rg_pos {D : Set Plane} (hD : Link.IsDisc D) {z : Plane} (hz : z ∈ interior D) {x : Plane}
    (hx : x ≠ z) : 0 < u8h_f_rg D z x :=
  lt_of_le_of_ne (u8h_f_rg_nonneg D z x) (fun h => hx ((u8h_f_rg_eq_zero_iff hD hz x).mp h.symm))

theorem u8h_f_rg_self (D : Set Plane) (z : Plane) : u8h_f_rg D z z = 0 := by
  simp [u8h_f_rg, gauge_zero]

theorem u8h_f_rg_smul (D : Set Plane) (z x : Plane) {t : ℝ} (ht : 0 ≤ t) :
    u8h_f_rg D z (z + t • (x - z)) = t * u8h_f_rg D z x := by
  unfold u8h_f_rg
  rw [add_sub_cancel_left, gauge_smul_of_nonneg ht, smul_eq_mul]

theorem u8h_f_rg_continuous {D : Set Plane} (hD : Link.IsDisc D) {z : Plane} (hz : z ∈ interior D) :
    Continuous (u8h_f_rg D z) :=
  (continuous_gauge (u8h_f_D0_convex hD z) (u8h_f_D0_nhds hz)).comp (continuous_id.sub continuous_const)

/-- The frontier point on the ray from `z` through `x ≠ z`. -/
noncomputable def u8h_f_ray (D : Set Plane) (z x : Plane) : Plane := z + (u8h_f_rg D z x)⁻¹ • (x - z)

theorem u8h_f_ray_mem_frontier {D : Set Plane} (hD : Link.IsDisc D) {z : Plane} (hz : z ∈ interior D)
    {x : Plane} (hx : x ≠ z) : u8h_f_ray D z x ∈ frontier D := by
  rw [← u8h_f_rg_eq_one_iff hD hz, u8h_f_ray, u8h_f_rg_smul D z x (inv_nonneg.mpr (u8h_f_rg_nonneg D z x))]
  exact inv_mul_cancel₀ (u8h_f_rg_pos hD hz hx).ne'

theorem u8h_f_ray_spec {D : Set Plane} (hD : Link.IsDisc D) {z : Plane} (hz : z ∈ interior D)
    {x : Plane} (hx : x ≠ z) : x = z + u8h_f_rg D z x • (u8h_f_ray D z x - z) := by
  rw [u8h_f_ray, add_sub_cancel_left, smul_smul, mul_inv_cancel₀ (u8h_f_rg_pos hD hz hx).ne', one_smul,
    add_sub_cancel]

theorem u8h_f_ray_of_frontier {D : Set Plane} (hD : Link.IsDisc D) {z : Plane} (hz : z ∈ interior D)
    {y : Plane} (hy : y ∈ frontier D) : u8h_f_ray D z y = y := by
  rw [u8h_f_ray, (u8h_f_rg_eq_one_iff hD hz y).mpr hy, inv_one, one_smul, add_sub_cancel]

theorem u8h_f_frontier_ne {D : Set Plane} (hD : Link.IsDisc D) {z : Plane} (hz : z ∈ interior D)
    {y : Plane} (hy : y ∈ frontier D) : y ≠ z := by
  intro h; subst h
  have := (u8h_f_rg_eq_one_iff hD hz y).mpr hy
  rw [u8h_f_rg_self] at this; norm_num at this

theorem u8h_f_frontier_subset {D : Set Plane} (hD : Link.IsDisc D) : frontier D ⊆ D :=
  hD.isCompact.isClosed.frontier_subset

/-! ### det algebra -/

theorem u8h_f_det_add_right (u v w : Plane) : det u (v + w) = det u v + det u w := by
  simp only [det, Prod.fst_add, Prod.snd_add]; ring

theorem u8h_f_det_smul_right (u v : Plane) (c : ℝ) : det u (c • v) = c * det u v := by
  simp only [det, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring

theorem u8h_f_det_add_left (u v w : Plane) : det (u + v) w = det u w + det v w := by
  simp only [det, Prod.fst_add, Prod.snd_add]; ring

theorem u8h_f_det_smul_left' (u v : Plane) (c : ℝ) : det (c • u) v = c * det u v := by
  simp only [det, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring

theorem u8h_f_det_self (u : Plane) : det u u = 0 := by simp only [det]; ring

theorem u8h_f_det_zero_right (u : Plane) : det u 0 = 0 := by simp [det]

theorem u8h_f_det_zero_left (u : Plane) : det 0 u = 0 := by simp [det]

theorem u8h_f_det_swap' (u v : Plane) : det u v = -det v u := by simp only [det]; ring

theorem u8h_f_cramer {u v : Plane} (h : det u v ≠ 0) (w : Plane) :
    w = (det w v / det u v) • u + (det u w / det u v) • v := by
  ext
  · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul, div_mul_eq_mul_div, ← add_div]
    rw [eq_div_iff h]; unfold det; ring
  · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul, div_mul_eq_mul_div, ← add_div]
    rw [eq_div_iff h]; unfold det; ring

theorem u8h_f_parallel_of_det_eq_zero {u v : Plane} (hu : u ≠ 0) (h : det u v = 0) :
    ∃ μ : ℝ, v = μ • u := by
  have hn : 0 < u.1 ^ 2 + u.2 ^ 2 := by
    rcases not_and_or.mp (fun hc : u.1 = 0 ∧ u.2 = 0 => hu (Prod.ext hc.1 hc.2)) with h1 | h2 <;>
      positivity
  refine ⟨(u.1 * v.1 + u.2 * v.2) / (u.1 ^ 2 + u.2 ^ 2), ?_⟩
  simp only [det] at h
  ext
  · simp only [Prod.smul_fst, smul_eq_mul]
    field_simp
    linear_combination (-u.2) * h
  · simp only [Prod.smul_snd, smul_eq_mul]
    field_simp
    linear_combination u.1 * h

/-! ### half-planes are convex -/

theorem u8h_f_convex_det_nonneg (z u : Plane) : Convex ℝ {x : Plane | 0 ≤ det u (x - z)} := by
  intro x hx y hy a b ha hb hab
  change 0 ≤ det u (x - z) at hx
  change 0 ≤ det u (y - z) at hy
  change 0 ≤ det u (a • x + b • y - z)
  have hz' : z = a • z + b • z := by rw [← add_smul, hab, one_smul]
  have : a • x + b • y - z = a • (x - z) + b • (y - z) := by
    calc a • x + b • y - z = a • x + b • y - (a • z + b • z) := by rw [← hz']
      _ = a • (x - z) + b • (y - z) := by rw [smul_sub, smul_sub]; abel
  rw [this, u8h_f_det_add_right, u8h_f_det_smul_right, u8h_f_det_smul_right]
  positivity

theorem u8h_f_convex_det_nonneg' (z v : Plane) : Convex ℝ {x : Plane | 0 ≤ det (x - z) v} := by
  intro x hx y hy a b ha hb hab
  change 0 ≤ det (x - z) v at hx
  change 0 ≤ det (y - z) v at hy
  change 0 ≤ det (a • x + b • y - z) v
  have hz' : z = a • z + b • z := by rw [← add_smul, hab, one_smul]
  have : a • x + b • y - z = a • (x - z) + b • (y - z) := by
    calc a • x + b • y - z = a • x + b • y - (a • z + b • z) := by rw [← hz']
      _ = a • (x - z) + b • (y - z) := by rw [smul_sub, smul_sub]; abel
  rw [this, u8h_f_det_add_left, u8h_f_det_smul_left', u8h_f_det_smul_left']
  positivity

/-! ### a straight frontier piece is not seen edge-on from `z` -/

theorem u8h_f_det_ne_zero_of_segment {D : Set Plane} (hD : Link.IsDisc D) {z : Plane} (hz : z ∈ interior D)
    {a b : Plane} (hne : a ≠ b) (hseg : segment ℝ a b ⊆ frontier D) : det (a - z) (b - z) ≠ 0 := by
  intro h0
  have ha : a ∈ frontier D := hseg (left_mem_segment ℝ a b)
  have hb : b ∈ frontier D := hseg (right_mem_segment ℝ a b)
  have haz : a - z ≠ 0 := sub_ne_zero.mpr (u8h_f_frontier_ne hD hz ha)
  obtain ⟨μ, hμ⟩ := u8h_f_parallel_of_det_eq_zero haz h0
  have hb' : b = z + μ • (a - z) := by rw [← hμ]; abel
  rcases le_or_gt 0 μ with hμ0 | hμ0
  · have h1 := (u8h_f_rg_eq_one_iff hD hz b).mpr hb
    rw [hb', u8h_f_rg_smul D z a hμ0, (u8h_f_rg_eq_one_iff hD hz a).mpr ha, mul_one] at h1
    subst h1
    apply hne; rw [hb', one_smul, add_sub_cancel]
  · have h1μ : (1 - μ) ≠ 0 := by linarith
    have hzmem : z ∈ segment ℝ a b := by
      refine ⟨-μ / (1 - μ), 1 / (1 - μ), by
        apply div_nonneg <;> linarith, by
        apply div_nonneg <;> linarith, by
        rw [← add_div, div_eq_one_iff_eq h1μ]; ring, ?_⟩
      rw [hb']
      ext
      · simp only [Prod.fst_add, Prod.smul_fst, Prod.fst_sub, smul_eq_mul]; field_simp; ring
      · simp only [Prod.snd_add, Prod.smul_snd, Prod.snd_sub, smul_eq_mul]; field_simp; ring
    have := (u8h_f_rg_eq_one_iff hD hz z).mpr (hseg hzmem)
    rw [u8h_f_rg_self] at this; norm_num at this

/-! ### the sector lemma and the fan characterisation -/

/-- A frontier point in the closed sector spanned (from `z`) by a straight frontier piece `[a, b]`
lies on that piece. -/
theorem u8h_f_frontier_mem_segment {D : Set Plane} (hD : Link.IsDisc D) {z : Plane} (hz : z ∈ interior D)
    {a b : Plane} (hab : 0 < det (a - z) (b - z)) (hseg : segment ℝ a b ⊆ frontier D) {y : Plane}
    (hy : y ∈ frontier D) (h1 : 0 ≤ det (a - z) (y - z)) (h2 : 0 ≤ det (y - z) (b - z)) :
    y ∈ segment ℝ a b := by
  set β := det (y - z) (b - z) / det (a - z) (b - z) with hβ
  set γ := det (a - z) (y - z) / det (a - z) (b - z) with hγ
  have hβ0 : 0 ≤ β := div_nonneg h2 hab.le
  have hγ0 : 0 ≤ γ := div_nonneg h1 hab.le
  have hdec : y - z = β • (a - z) + γ • (b - z) := u8h_f_cramer hab.ne' (y - z)
  have hs : 0 < β + γ := by
    rcases (add_nonneg hβ0 hγ0).lt_or_eq with h | h
    · exact h
    · exfalso
      have hβz : β = 0 := by linarith
      have hγz : γ = 0 := by linarith
      rw [hβz, hγz, zero_smul, zero_smul, add_zero] at hdec
      exact u8h_f_frontier_ne hD hz hy (sub_eq_zero.mp hdec)
  set s := β + γ with hs_def
  set w : Plane := (β / s) • a + (γ / s) • b with hw
  have hwseg : w ∈ segment ℝ a b :=
    ⟨β / s, γ / s, div_nonneg hβ0 hs.le, div_nonneg hγ0 hs.le, by rw [← add_div, div_self hs.ne'], rfl⟩
  have hyw : y = z + s • (w - z) := by
    have e1 := congrArg Prod.fst hdec
    have e2 := congrArg Prod.snd hdec
    simp only [Prod.fst_sub, Prod.fst_add, Prod.smul_fst, smul_eq_mul, Prod.snd_sub, Prod.snd_add,
      Prod.smul_snd] at e1 e2
    ext
    · simp only [hw, Prod.fst_add, Prod.smul_fst, Prod.fst_sub, smul_eq_mul]
      field_simp
      linear_combination e1
    · simp only [hw, Prod.snd_add, Prod.smul_snd, Prod.snd_sub, smul_eq_mul]
      field_simp
      linear_combination e2
  have hrw : u8h_f_rg D z w = 1 := (u8h_f_rg_eq_one_iff hD hz w).mpr (hseg hwseg)
  have hry : u8h_f_rg D z y = 1 := (u8h_f_rg_eq_one_iff hD hz y).mpr hy
  rw [hyw, u8h_f_rg_smul D z w hs.le, hrw, mul_one] at hry
  rw [hyw, hry, one_smul, add_sub_cancel]
  exact hwseg

/-- The ray point of a point of the closed sector lies on the frontier piece. -/
theorem u8h_f_ray_mem_segment {D : Set Plane} (hD : Link.IsDisc D) {z : Plane} (hz : z ∈ interior D)
    {a b : Plane} (hab : 0 < det (a - z) (b - z)) (hseg : segment ℝ a b ⊆ frontier D) {x : Plane}
    (hxz : x ≠ z) (h1 : 0 ≤ det (a - z) (x - z)) (h2 : 0 ≤ det (x - z) (b - z)) :
    u8h_f_ray D z x ∈ segment ℝ a b := by
  have hyz : u8h_f_ray D z x - z = (u8h_f_rg D z x)⁻¹ • (x - z) := by simp [u8h_f_ray]
  have hr0 : 0 ≤ (u8h_f_rg D z x)⁻¹ := inv_nonneg.mpr (u8h_f_rg_nonneg _ _ _)
  refine u8h_f_frontier_mem_segment hD hz hab hseg (u8h_f_ray_mem_frontier hD hz hxz) ?_ ?_
  · rw [hyz, u8h_f_det_smul_right]; exact mul_nonneg hr0 h1
  · rw [hyz, u8h_f_det_smul_left']; exact mul_nonneg hr0 h2

/-- The fan triangle `conv {z, a, b}` over a straight frontier piece is the closed sector cut off
by `D`. -/
theorem u8h_f_mem_fan_iff {D : Set Plane} (hD : Link.IsDisc D) {z : Plane} (hz : z ∈ interior D)
    {a b : Plane} (hab : 0 < det (a - z) (b - z)) (hseg : segment ℝ a b ⊆ frontier D) (x : Plane) :
    x ∈ convexHull ℝ {z, a, b} ↔ 0 ≤ det (a - z) (x - z) ∧ 0 ≤ det (x - z) (b - z) ∧ x ∈ D := by
  constructor
  · intro hx
    have hsub : convexHull ℝ {z, a, b} ⊆
        ({x | 0 ≤ det (a - z) (x - z)} ∩ {x | 0 ≤ det (x - z) (b - z)}) ∩ D := by
      apply convexHull_min
      · intro p hp
        simp only [mem_insert_iff, mem_singleton_iff] at hp
        rcases hp with rfl | rfl | rfl
        · exact ⟨⟨by simp [u8h_f_det_zero_right], by simp [u8h_f_det_zero_left]⟩, interior_subset hz⟩
        · exact ⟨⟨by simp [u8h_f_det_self], hab.le⟩,
            u8h_f_frontier_subset hD (hseg (left_mem_segment ℝ _ _))⟩
        · exact ⟨⟨hab.le, by simp [u8h_f_det_self]⟩,
            u8h_f_frontier_subset hD (hseg (right_mem_segment ℝ _ _))⟩
      · exact ((u8h_f_convex_det_nonneg z (a - z)).inter (u8h_f_convex_det_nonneg' z (b - z))).inter
          hD.convex
    obtain ⟨⟨h1, h2⟩, h3⟩ := hsub hx
    exact ⟨h1, h2, h3⟩
  · rintro ⟨h1, h2, h3⟩
    by_cases hxz : x = z
    · subst hxz; exact subset_convexHull ℝ _ (mem_insert _ _)
    · have hyseg := u8h_f_ray_mem_segment hD hz hab hseg hxz h1 h2
      have hxeq := u8h_f_ray_spec hD hz hxz
      have hr1 : u8h_f_rg D z x ≤ 1 := (u8h_f_rg_le_one_iff hD hz x).mpr h3
      have hr0 := u8h_f_rg_nonneg D z x
      have hzmem : z ∈ convexHull ℝ {z, a, b} := subset_convexHull ℝ _ (mem_insert _ _)
      have hymem : u8h_f_ray D z x ∈ convexHull ℝ {z, a, b} :=
        segment_subset_convexHull (by simp) (by simp) hyseg
      have := (convex_convexHull ℝ {z, a, b}) hzmem hymem (sub_nonneg.mpr hr1) hr0 (by ring)
      rw [hxeq]
      convert this using 1
      rw [sub_smul, one_smul, smul_sub]; abel

/-! ### marks and adjacent pairs -/

/-- `(a, b)` is an adjacent pair of marks of `V`: a straight frontier piece seen counterclockwise
from `z` with no mark strictly inside. -/
def u8h_f_Adj (D : Set Plane) (z : Plane) (V : Set Plane) (a b : Plane) : Prop :=
  a ∈ V ∧ b ∈ V ∧ 0 < det (a - z) (b - z) ∧ segment ℝ a b ⊆ frontier D ∧
    ∀ c ∈ V, c ∉ openSegment ℝ a b

theorem u8h_f_openSegment_sub {a b y : Plane} (h : y ∈ openSegment ℝ a b) (z : Plane) :
    ∃ β γ : ℝ, 0 < β ∧ 0 < γ ∧ β + γ = 1 ∧ y - z = β • (a - z) + γ • (b - z) := by
  obtain ⟨β, γ, hβ, hγ, hβγ, rfl⟩ := h
  refine ⟨β, γ, hβ, hγ, hβγ, ?_⟩
  have hz' : z = β • z + γ • z := by rw [← add_smul, hβγ, one_smul]
  calc β • a + γ • b - z = β • a + γ • b - (β • z + γ • z) := by rw [← hz']
    _ = β • (a - z) + γ • (b - z) := by rw [smul_sub, smul_sub]; abel

theorem u8h_f_det_comb_right (u v w : Plane) (β γ : ℝ) :
    det u (β • v + γ • w) = β * det u v + γ * det u w := by
  rw [u8h_f_det_add_right, u8h_f_det_smul_right, u8h_f_det_smul_right]

theorem u8h_f_det_comb_left (u v w : Plane) (β γ : ℝ) :
    det (β • v + γ • w) u = β * det v u + γ * det w u := by
  rw [u8h_f_det_add_left, u8h_f_det_smul_left', u8h_f_det_smul_left']

theorem u8h_f_mem_segment_cases {a b y : Plane} (h : y ∈ segment ℝ a b) :
    y = a ∨ y = b ∨ y ∈ openSegment ℝ a b := by
  rw [← insert_endpoints_openSegment] at h
  simpa using h

/-- Where a mark can lie relative to an adjacent pair. -/
theorem u8h_f_adj_trichotomy {D : Set Plane} (hD : Link.IsDisc D) {z : Plane} (hz : z ∈ interior D)
    {V : Set Plane} (hV : V ⊆ frontier D) {a b : Plane} (hab : u8h_f_Adj D z V a b) {c : Plane}
    (hc : c ∈ V) : c = a ∨ c = b ∨ det (a - z) (c - z) < 0 ∨ det (c - z) (b - z) < 0 := by
  rcases lt_or_ge (det (a - z) (c - z)) 0 with h1 | h1
  · exact Or.inr (Or.inr (Or.inl h1))
  rcases lt_or_ge (det (c - z) (b - z)) 0 with h2 | h2
  · exact Or.inr (Or.inr (Or.inr h2))
  have hcseg := u8h_f_frontier_mem_segment hD hz hab.2.2.1 hab.2.2.2.1 (hV hc) h1 h2
  rcases u8h_f_mem_segment_cases hcseg with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact absurd h (hab.2.2.2.2 c hc)

theorem u8h_f_adj_unique_right {D : Set Plane} (hD : Link.IsDisc D) {z : Plane} (hz : z ∈ interior D)
    {V : Set Plane} (hV : V ⊆ frontier D) {a b d : Plane} (hab : u8h_f_Adj D z V a b)
    (had : u8h_f_Adj D z V a d) : b = d := by
  rcases u8h_f_adj_trichotomy hD hz hV hab had.2.1 with h | h | h | h
  · exfalso; subst h; exact lt_irrefl (0:ℝ) (by simpa [u8h_f_det_self] using had.2.2.1)
  · exact h.symm
  · exfalso; linarith [had.2.2.1]
  · exfalso
    have hbd : 0 < det (b - z) (d - z) := by rw [u8h_f_det_swap']; linarith
    have hbseg := u8h_f_frontier_mem_segment hD hz had.2.2.1 had.2.2.2.1 (hV hab.2.1) hab.2.2.1.le hbd.le
    rcases u8h_f_mem_segment_cases hbseg with h1 | h1 | h1
    · subst h1; exact lt_irrefl (0:ℝ) (by simpa [u8h_f_det_self] using hab.2.2.1)
    · subst h1; simp [u8h_f_det_self] at hbd
    · exact had.2.2.2.2 b hab.2.1 h1

theorem u8h_f_adj_unique_left {D : Set Plane} (hD : Link.IsDisc D) {z : Plane} (hz : z ∈ interior D)
    {V : Set Plane} (hV : V ⊆ frontier D) {a b c : Plane} (hab : u8h_f_Adj D z V a b)
    (hcb : u8h_f_Adj D z V c b) : a = c := by
  rcases u8h_f_adj_trichotomy hD hz hV hab hcb.1 with h | h | h | h
  · exact h.symm
  · exfalso; subst h; exact lt_irrefl (0:ℝ) (by simpa [u8h_f_det_self] using hcb.2.2.1)
  · exfalso
    have hca : 0 < det (c - z) (a - z) := by rw [u8h_f_det_swap']; linarith
    have haseg := u8h_f_frontier_mem_segment hD hz hcb.2.2.1 hcb.2.2.2.1 (hV hab.1) hca.le hab.2.2.1.le
    rcases u8h_f_mem_segment_cases haseg with h1 | h1 | h1
    · subst h1; simp [u8h_f_det_self] at hca
    · subst h1; exact lt_irrefl (0:ℝ) (by simpa [u8h_f_det_self] using hab.2.2.1)
    · exact hcb.2.2.2.2 a hab.1 h1
  · exfalso; linarith [hcb.2.2.1]

/-- A point in the open frontier pieces of two adjacent pairs forces the pairs to coincide. -/
theorem u8h_f_adj_eq_of_openSegment {D : Set Plane} (hD : Link.IsDisc D) {z : Plane} (hz : z ∈ interior D)
    {V : Set Plane} (hV : V ⊆ frontier D) {a b c d y : Plane} (hab : u8h_f_Adj D z V a b)
    (hcd : u8h_f_Adj D z V c d) (h1 : y ∈ openSegment ℝ a b) (h2 : y ∈ openSegment ℝ c d) :
    a = c ∧ b = d := by
  obtain ⟨β, γ, hβ, hγ, -, hY1⟩ := u8h_f_openSegment_sub h1 z
  obtain ⟨β', δ, hβ', hδ, -, hY2⟩ := u8h_f_openSegment_sub h2 z
  have dAB := hab.2.2.1
  have dCD := hcd.2.2.1
  have eAY : det (a - z) (y - z) = γ * det (a - z) (b - z) := by
    rw [hY1, u8h_f_det_comb_right, u8h_f_det_self]; ring
  have eBY : det (b - z) (y - z) = -(β * det (a - z) (b - z)) := by
    rw [hY1, u8h_f_det_comb_right, u8h_f_det_self, u8h_f_det_swap' (b - z) (a - z)]; ring
  have eCY : det (c - z) (y - z) = δ * det (c - z) (d - z) := by
    rw [hY2, u8h_f_det_comb_right, u8h_f_det_self]; ring
  have eYD : det (y - z) (d - z) = β' * det (c - z) (d - z) := by
    rw [hY2, u8h_f_det_comb_left, u8h_f_det_self]; ring
  have eAY' : det (a - z) (y - z) = β' * det (a - z) (c - z) + δ * det (a - z) (d - z) := by
    rw [hY2, u8h_f_det_comb_right]
  have eBY' : det (b - z) (y - z) = β' * det (b - z) (c - z) + δ * det (b - z) (d - z) := by
    rw [hY2, u8h_f_det_comb_right]
  have eYD' : det (y - z) (d - z) = β * det (a - z) (d - z) + γ * det (b - z) (d - z) := by
    rw [hY1, u8h_f_det_comb_left]
  rcases u8h_f_adj_trichotomy hD hz hV hab hcd.1 with hc | hc | hc | hc
  · -- c = a
    subst hc
    refine ⟨rfl, ?_⟩
    rcases u8h_f_adj_trichotomy hD hz hV hab hcd.2.1 with hd | hd | hd | hd
    · exfalso; subst hd
      have := hcd.2.2.1; rw [u8h_f_det_self] at this; exact lt_irrefl _ this
    · exact hd.symm
    · exfalso; linarith [hcd.2.2.1]
    · exfalso
      have hbd : 0 < det (b - z) (d - z) := by rw [u8h_f_det_swap']; linarith
      have hbseg := u8h_f_frontier_mem_segment hD hz hcd.2.2.1 hcd.2.2.2.1 (hV hab.2.1) dAB.le hbd.le
      rcases u8h_f_mem_segment_cases hbseg with h | h | h
      · subst h; rw [u8h_f_det_self] at dAB; exact lt_irrefl _ dAB
      · subst h; rw [u8h_f_det_self] at hbd; exact lt_irrefl _ hbd
      · exact hcd.2.2.2.2 b hab.2.1 h
  · -- c = b
    exfalso; subst hc
    have : 0 < det (c - z) (y - z) := by rw [eCY]; positivity
    rw [eBY] at this
    have := mul_pos hβ dAB; linarith
  · -- det (a-z) (c-z) < 0 : `a` lies strictly inside the sector `(c, d)`
    exfalso
    have hAD : 0 < det (a - z) (d - z) := by
      have h0 : 0 < δ * det (a - z) (d - z) := by
        have := mul_pos hγ dAB
        have := mul_neg_of_pos_of_neg hβ' hc
        linarith
      exact (mul_pos_iff_of_pos_left hδ).mp h0
    have hCA : 0 < det (c - z) (a - z) := by rw [u8h_f_det_swap']; linarith
    have haseg := u8h_f_frontier_mem_segment hD hz dCD hcd.2.2.2.1 (hV hab.1) hCA.le hAD.le
    rcases u8h_f_mem_segment_cases haseg with h | h | h
    · subst h; rw [u8h_f_det_self] at hCA; exact lt_irrefl _ hCA
    · subst h; rw [u8h_f_det_self] at hAD; exact lt_irrefl _ hAD
    · exact hcd.2.2.2.2 a hab.1 h
  · -- det (c-z) (b-z) < 0 : `d` lies strictly inside the sector `(a, b)`
    exfalso
    have hBC : 0 < det (b - z) (c - z) := by rw [u8h_f_det_swap']; linarith
    have hBD : det (b - z) (d - z) < 0 := by
      have h0 : δ * det (b - z) (d - z) < 0 := by
        have := mul_pos hβ dAB
        have := mul_pos hβ' hBC
        linarith
      rcases lt_or_ge (det (b - z) (d - z)) 0 with h | h
      · exact h
      · exfalso; linarith [mul_nonneg hδ.le h]
    have hAD : 0 < det (a - z) (d - z) := by
      have h0 : 0 < β * det (a - z) (d - z) := by
        have := mul_pos hβ' dCD
        have := mul_neg_of_pos_of_neg hγ hBD
        linarith
      exact (mul_pos_iff_of_pos_left hβ).mp h0
    have hDB : 0 < det (d - z) (b - z) := by rw [u8h_f_det_swap']; linarith
    have hdseg := u8h_f_frontier_mem_segment hD hz dAB hab.2.2.2.1 (hV hcd.2.1) hAD.le hDB.le
    rcases u8h_f_mem_segment_cases hdseg with h | h | h
    · subst h; rw [u8h_f_det_self] at hAD; exact lt_irrefl _ hAD
    · subst h; rw [u8h_f_det_self] at hDB; exact lt_irrefl _ hDB
    · exact hab.2.2.2.2 d hcd.2.1 h


theorem u8h_f_range_three (z a b : Plane) : range ![z, a, b] = {z, a, b} := by
  ext p
  simp only [mem_range, mem_insert_iff, mem_singleton_iff]
  constructor
  · rintro ⟨i, rfl⟩; fin_cases i <;> simp
  · rintro (rfl | rfl | rfl)
    exacts [⟨0, by simp⟩, ⟨1, by simp⟩, ⟨2, by simp⟩]

/-- The fan faces: one triangle `z a b` per pair with `A a b`. -/
def u8h_f_fanFaces (z : Plane) (A : Plane → Plane → Prop) : Set Triangle :=
  {T | ∃ a b, A a b ∧ T.v = ![z, a, b]}

theorem u8h_f_fanTri_mem {z a b : Plane} {A : Plane → Plane → Prop} (h : A a b)
    (hpos : 0 < det (a - z) (b - z)) :
    (⟨![z, a, b], by simpa using hpos⟩ : Triangle) ∈ u8h_f_fanFaces z A := ⟨a, b, h, rfl⟩

theorem u8h_f_carrier_of_v {T : Triangle} {z a b : Plane} (h : T.v = ![z, a, b]) :
    T.carrier = convexHull ℝ {z, a, b} := by
  rw [Triangle.carrier, h, u8h_f_range_three]

theorem u8h_f_inter_cases {D : Set Plane} (hD : Link.IsDisc D) {z : Plane} (hz : z ∈ interior D)
    {V : Set Plane} (hV : V ⊆ frontier D) {a b c d y : Plane} (hab : u8h_f_Adj D z V a b)
    (hcd : u8h_f_Adj D z V c d) (hy1 : y ∈ segment ℝ a b) (hy2 : y ∈ segment ℝ c d) :
    (a = c ∧ b = d) ∨ (y = a ∧ a = d) ∨ (y = b ∧ b = c) := by
  rcases u8h_f_mem_segment_cases hy1 with h1 | h1 | h1 <;>
    rcases u8h_f_mem_segment_cases hy2 with h2 | h2 | h2
  · subst h1; exact Or.inl ⟨h2, u8h_f_adj_unique_right hD hz hV hab (h2 ▸ hcd)⟩
  · exact Or.inr (Or.inl ⟨h1, h1 ▸ h2⟩)
  · exact absurd (h1 ▸ h2) (hcd.2.2.2.2 a hab.1)
  · exact Or.inr (Or.inr ⟨h1, h1 ▸ h2⟩)
  · subst h1; exact Or.inl ⟨u8h_f_adj_unique_left hD hz hV hab (h2 ▸ hcd), h2⟩
  · exact absurd (h1 ▸ h2) (hcd.2.2.2.2 b hab.2.1)
  · exact absurd (h2 ▸ h1) (hab.2.2.2.2 c hcd.1)
  · exact absurd (h2 ▸ h1) (hab.2.2.2.2 d hcd.2.1)
  · exact Or.inl (u8h_f_adj_eq_of_openSegment hD hz hV hab hcd h1 h2)

theorem u8h_f_fan_subset {D : Set Plane} (hD : Link.IsDisc D) {z : Plane} (hz : z ∈ interior D)
    {a b : Plane} (hseg : segment ℝ a b ⊆ frontier D) : convexHull ℝ {z, a, b} ⊆ D := by
  apply convexHull_min _ hD.convex
  intro p hp
  simp only [mem_insert_iff, mem_singleton_iff] at hp
  rcases hp with rfl | rfl | rfl
  · exact interior_subset hz
  · exact u8h_f_frontier_subset hD (hseg (left_mem_segment ℝ _ _))
  · exact u8h_f_frontier_subset hD (hseg (right_mem_segment ℝ _ _))

theorem u8h_f_frontier_nonempty {D : Set Plane} (hD : Link.IsDisc D) {z : Plane} (hz : z ∈ interior D) :
    (frontier D).Nonempty :=
  ⟨u8h_f_ray D z (z + (1, 0)), u8h_f_ray_mem_frontier hD hz (by simp)⟩

theorem u8h_f_mem_segment_ray {D : Set Plane} (hD : Link.IsDisc D) {z : Plane} (hz : z ∈ interior D)
    {x : Plane} (hx : x ∈ D) (hxz : x ≠ z) : x ∈ segment ℝ z (u8h_f_ray D z x) := by
  have hr0 := u8h_f_rg_nonneg D z x
  have hr1 := (u8h_f_rg_le_one_iff hD hz x).mpr hx
  refine ⟨1 - u8h_f_rg D z x, u8h_f_rg D z x, by linarith, hr0, by ring, ?_⟩
  have := u8h_f_ray_spec hD hz hxz
  rw [smul_sub] at this
  rw [sub_smul, one_smul]
  conv_rhs => rw [this]
  abel

/-- The fan from `z` over the adjacent pairs is a straight triangulation of `D`. -/
theorem u8h_f_fan_triangulation {D : Set Plane} (hD : Link.IsDisc D) {z : Plane} (hz : z ∈ interior D)
    {V : Set Plane} (hVfin : V.Finite) (hV : V ⊆ frontier D) {A : Plane → Plane → Prop}
    (hA : ∀ a b, A a b → u8h_f_Adj D z V a b)
    (hcov : ∀ y ∈ frontier D, ∃ a b, A a b ∧ y ∈ segment ℝ a b) :
    ∃ K : Triangulation D, K.faces = u8h_f_fanFaces z A := by
  have hface : ∀ T ∈ u8h_f_fanFaces z A, ∃ a b, u8h_f_Adj D z V a b ∧ T.v 0 = z ∧ T.v 1 = a ∧
      T.v 2 = b ∧ T.carrier = convexHull ℝ {z, a, b} := by
    rintro T ⟨a, b, hab, hv⟩
    exact ⟨a, b, hA a b hab, by simp [hv], by simp [hv], by simp [hv], u8h_f_carrier_of_v hv⟩
  refine ⟨⟨u8h_f_fanFaces z A, ?_, ?_, ?_⟩, rfl⟩
  · -- finite
    apply Set.Finite.of_finite_image (f := fun T => (T.v 1, T.v 2))
    · refine (hVfin.prod hVfin).subset ?_
      rintro _ ⟨T, hT, rfl⟩
      obtain ⟨a, b, hab, -, h1, h2, -⟩ := hface T hT
      show T.v 1 ∈ V ∧ T.v 2 ∈ V
      rw [h1, h2]; exact ⟨hab.1, hab.2.1⟩
    · intro T hT T' hT' h
      simp only [Prod.mk.injEq] at h
      obtain ⟨a, b, -, h0, -, -, -⟩ := hface T hT
      obtain ⟨c, d, -, h0', -, -, -⟩ := hface T' hT'
      have : T.v = T'.v := by
        funext i
        fin_cases i
        · simpa using h0.trans h0'.symm
        · exact h.1
        · exact h.2
      cases T; cases T'; simp only at this; subst this; rfl
  · -- cover
    apply Set.Subset.antisymm
    · intro x hx
      simp only [mem_iUnion, exists_prop] at hx
      obtain ⟨T, hT, hxT⟩ := hx
      obtain ⟨a, b, hab, -, -, -, hc⟩ := hface T hT
      rw [hc] at hxT
      exact u8h_f_fan_subset hD hz hab.2.2.2.1 hxT
    · intro x hx
      simp only [mem_iUnion, exists_prop]
      by_cases hxz : x = z
      · subst hxz
        obtain ⟨y0, hy0⟩ := u8h_f_frontier_nonempty hD hz
        obtain ⟨a, b, hab, -⟩ := hcov y0 hy0
        refine ⟨_, u8h_f_fanTri_mem hab (hA a b hab).2.2.1, ?_⟩
        rw [u8h_f_carrier_of_v rfl]
        exact subset_convexHull ℝ _ (mem_insert _ _)
      · obtain ⟨a, b, hab, hyab⟩ := hcov _ (u8h_f_ray_mem_frontier hD hz hxz)
        refine ⟨_, u8h_f_fanTri_mem hab (hA a b hab).2.2.1, ?_⟩
        rw [u8h_f_carrier_of_v rfl]
        have hzmem : z ∈ convexHull ℝ {z, a, b} := subset_convexHull ℝ _ (mem_insert _ _)
        have hymem : u8h_f_ray D z x ∈ convexHull ℝ {z, a, b} :=
          segment_subset_convexHull (by simp) (by simp) hyab
        exact (convex_convexHull ℝ _).segment_subset hzmem hymem (u8h_f_mem_segment_ray hD hz hx hxz)
  · -- inter
    intro T hT T' hT'
    obtain ⟨a, b, hab, h0, h1, h2, hc⟩ := hface T hT
    obtain ⟨c, d, hcd, h0', h1', h2', hc'⟩ := hface T' hT'
    have hrT : range T.v = {z, a, b} := by
      rw [← u8h_f_range_three]; congr 1; funext i; fin_cases i <;> simp [h0, h1, h2]
    have hrT' : range T'.v = {z, c, d} := by
      rw [← u8h_f_range_three]; congr 1; funext i; fin_cases i <;> simp [h0', h1', h2']
    rw [hc, hc', hrT, hrT']
    apply Set.Subset.antisymm
    · rintro x ⟨hx1, hx2⟩
      by_cases hxz : x = z
      · subst hxz
        exact subset_convexHull ℝ _ ⟨mem_insert _ _, mem_insert _ _⟩
      · have hx1' := (u8h_f_mem_fan_iff hD hz hab.2.2.1 hab.2.2.2.1 x).mp hx1
        have hx2' := (u8h_f_mem_fan_iff hD hz hcd.2.2.1 hcd.2.2.2.1 x).mp hx2
        have hy1 := u8h_f_ray_mem_segment hD hz hab.2.2.1 hab.2.2.2.1 hxz hx1'.1 hx1'.2.1
        have hy2 := u8h_f_ray_mem_segment hD hz hcd.2.2.1 hcd.2.2.2.1 hxz hx2'.1 hx2'.2.1
        have hxseg := u8h_f_mem_segment_ray hD hz hx1'.2.2 hxz
        rcases u8h_f_inter_cases hD hz hV hab hcd hy1 hy2 with ⟨rfl, rfl⟩ | ⟨hy, rfl⟩ | ⟨hy, rfl⟩
        · rw [inter_self]; exact hx1
        · rw [hy] at hxseg
          exact segment_subset_convexHull (s := {z, a, b} ∩ {z, c, a}) ⟨mem_insert _ _, mem_insert _ _⟩
            ⟨by simp, by simp⟩ hxseg
        · rw [hy] at hxseg
          exact segment_subset_convexHull (s := {z, a, b} ∩ {z, b, d}) ⟨mem_insert _ _, mem_insert _ _⟩
            ⟨by simp, by simp⟩ hxseg
    · exact subset_inter (convexHull_mono inter_subset_left) (convexHull_mono inter_subset_right)

/-! ### the cone map -/


/-- The linear map sending `p ↦ p'`, `q ↦ q'` (for `det p q ≠ 0`), written in `det` coordinates. -/
theorem u8h_f_gap {M : Set ℝ} (hM : M.Finite) (h0 : (0:ℝ) ∈ M) (h1 : (1:ℝ) ∈ M) {θ₀ : ℝ}
    (hθ : θ₀ ∈ Icc (0:ℝ) 1) :
    ∃ θa ∈ M, ∃ θb ∈ M, θa < θb ∧ θa ≤ θ₀ ∧ θ₀ ≤ θb ∧ ∀ θ ∈ M, θa < θ → θ < θb → False := by
  classical
  rcases hθ.2.lt_or_eq with hlt | heq
  · set Fa := hM.toFinset.filter (fun θ => θ ≤ θ₀) with hFa
    set Fb := hM.toFinset.filter (fun θ => θ₀ < θ) with hFb
    have hane : Fa.Nonempty := ⟨0, by simp [hFa, h0, hθ.1]⟩
    have hbne : Fb.Nonempty := ⟨1, by simp [hFb, h1, hlt]⟩
    have hamem := Finset.max'_mem Fa hane
    have hbmem := Finset.min'_mem Fb hbne
    simp only [hFa, Finset.mem_filter, Set.Finite.mem_toFinset] at hamem
    simp only [hFb, Finset.mem_filter, Set.Finite.mem_toFinset] at hbmem
    refine ⟨_, hamem.1, _, hbmem.1, by linarith [hamem.2, hbmem.2], hamem.2, hbmem.2.le, ?_⟩
    intro θ hθM hlo hhi
    rcases le_or_gt θ θ₀ with h | h
    · have hmem : θ ∈ Fa := by simp [hFa, hθM, h]
      have := Finset.le_max' Fa θ hmem
      exact absurd hlo (not_lt.mpr this)
    · have hmem : θ ∈ Fb := by simp [hFb, hθM, h]
      have := Finset.min'_le Fb θ hmem
      exact absurd hhi (not_lt.mpr this)
  · subst heq
    set Fa := hM.toFinset.filter (fun θ => θ < 1) with hFa
    have hane : Fa.Nonempty := ⟨0, by simp [hFa, h0]⟩
    have hamem := Finset.max'_mem Fa hane
    simp only [hFa, Finset.mem_filter, Set.Finite.mem_toFinset] at hamem
    refine ⟨_, hamem.1, 1, h1, hamem.2, hamem.2.le, le_rfl, ?_⟩
    intro θ hθM hlo hhi
    have hmem : θ ∈ Fa := by simp [hFa, hθM, hhi]
    have := Finset.le_max' Fa θ hmem
    exact absurd hlo (not_lt.mpr this)

/-- The marks: all endpoints of the segments of `S`. -/
noncomputable def u8h_f_marks (S : Finset (Plane × Plane)) : Set Plane :=
  ↑(S.image Prod.fst ∪ S.image Prod.snd)

theorem u8h_f_marks_finite (S : Finset (Plane × Plane)) : (u8h_f_marks S).Finite := Finset.finite_toSet _

theorem u8h_f_marks_left {S : Finset (Plane × Plane)} {p : Plane × Plane} (hp : p ∈ S) :
    p.1 ∈ u8h_f_marks S := by
  simp only [u8h_f_marks, Finset.coe_union, Finset.coe_image, mem_union, mem_image, Finset.mem_coe]
  exact Or.inl ⟨p, hp, rfl⟩

theorem u8h_f_marks_right {S : Finset (Plane × Plane)} {p : Plane × Plane} (hp : p ∈ S) :
    p.2 ∈ u8h_f_marks S := by
  simp only [u8h_f_marks, Finset.coe_union, Finset.coe_image, mem_union, mem_image, Finset.mem_coe]
  exact Or.inr ⟨p, hp, rfl⟩

theorem u8h_f_marks_subset_frontier {D : Set Plane} {S : Finset (Plane × Plane)}
    (hS : (⋃ p ∈ S, segment ℝ p.1 p.2) = frontier D) : u8h_f_marks S ⊆ frontier D := by
  intro c hc
  simp only [u8h_f_marks, Finset.coe_union, Finset.coe_image, mem_union, mem_image,
    Finset.mem_coe] at hc
  rw [← hS]
  rcases hc with ⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩
  · exact mem_iUnion₂.mpr ⟨p, hp, left_mem_segment ℝ _ _⟩
  · exact mem_iUnion₂.mpr ⟨p, hp, right_mem_segment ℝ _ _⟩

/-- The adjacent pairs actually used: adjacent marks lying in one segment of `S`. -/
def u8h_f_A (D : Set Plane) (z : Plane) (S : Finset (Plane × Plane)) (a b : Plane) : Prop :=
  u8h_f_Adj D z (u8h_f_marks S) a b ∧ ∃ p ∈ S, segment ℝ a b ⊆ segment ℝ p.1 p.2

theorem u8h_f_cover_of_segment {D : Set Plane} (hD : Link.IsDisc D) {z : Plane} (hz : z ∈ interior D)
    {S : Finset (Plane × Plane)} (hS : (⋃ p ∈ S, segment ℝ p.1 p.2) = frontier D) {p : Plane × Plane}
    (hp : p ∈ S) (hne : p.1 ≠ p.2) {y : Plane} (hy : y ∈ segment ℝ p.1 p.2) :
    ∃ a b, u8h_f_A D z S a b ∧ y ∈ segment ℝ a b := by
  have he : p.2 - p.1 ≠ 0 := sub_ne_zero.mpr hne.symm
  set f : ℝ → Plane := fun θ => p.1 + θ • (p.2 - p.1) with hf
  have hfinj : Function.Injective f := fun θ₁ θ₂ h => smul_left_injective ℝ he (add_left_cancel h)
  have hsegp : segment ℝ p.1 p.2 = f '' Icc 0 1 := segment_eq_image' ℝ p.1 p.2
  have hsegfr : segment ℝ p.1 p.2 ⊆ frontier D := hS ▸ subset_iUnion₂ (s := fun p _ => segment ℝ p.1 p.2) p hp
  set M : Set ℝ := f ⁻¹' u8h_f_marks S ∩ Icc 0 1 with hM
  have hMfin : M.Finite := ((u8h_f_marks_finite S).preimage hfinj.injOn).subset inter_subset_left
  have h0M : (0:ℝ) ∈ M := ⟨by simp [f, u8h_f_marks_left hp], by simp⟩
  have h1M : (1:ℝ) ∈ M := ⟨by simp [f, u8h_f_marks_right hp], by simp⟩
  rw [hsegp] at hy
  obtain ⟨θ₀, hθ₀, rfl⟩ := hy
  obtain ⟨θa, haM, θb, hbM, hlt, hle1, hle2, hgap⟩ := u8h_f_gap hMfin h0M h1M hθ₀
  have haV : f θa ∈ u8h_f_marks S := haM.1
  have hbV : f θb ∈ u8h_f_marks S := hbM.1
  have hap : f θa ∈ segment ℝ p.1 p.2 := hsegp ▸ ⟨θa, haM.2, rfl⟩
  have hbp : f θb ∈ segment ℝ p.1 p.2 := hsegp ▸ ⟨θb, hbM.2, rfl⟩
  have hsub : segment ℝ (f θa) (f θb) ⊆ segment ℝ p.1 p.2 := (convex_segment _ _).segment_subset hap hbp
  have hsegab : segment ℝ (f θa) (f θb) ⊆ frontier D := hsub.trans hsegfr
  have hneab : f θa ≠ f θb := fun h => hlt.ne (hfinj h)
  have hcomb : ∀ lam : ℝ, f θa + lam • (f θb - f θa) = f (θa + lam * (θb - θa)) := by
    intro lam
    simp only [hf]
    ext <;> simp <;> ring
  have hnomark : ∀ c ∈ u8h_f_marks S, c ∉ openSegment ℝ (f θa) (f θb) := by
    intro c hc hco
    rw [openSegment_eq_image'] at hco
    obtain ⟨lam, hlam, rfl⟩ := hco
    beta_reduce at hc
    rw [hcomb] at hc
    have hθc : θa + lam * (θb - θa) ∈ M := by
      refine ⟨hc, ?_, ?_⟩
      · nlinarith [haM.2.1, hlam.1.le, hlt.le]
      · nlinarith [hbM.2.2, hlam.2.le, hlt.le]
    exact hgap _ hθc (by nlinarith [hlam.1]) (by nlinarith [hlam.2])
  have hyab : f θ₀ ∈ segment ℝ (f θa) (f θb) := by
    rw [segment_eq_image']
    refine ⟨(θ₀ - θa) / (θb - θa), ⟨div_nonneg (by linarith) (by linarith),
      div_le_one_of_le₀ (by linarith) (by linarith)⟩, ?_⟩
    beta_reduce
    rw [hcomb]
    congr 1
    have hba : θb - θa ≠ 0 := by linarith
    field_simp
    ring
  have hdet := u8h_f_det_ne_zero_of_segment hD hz hneab hsegab
  rcases hdet.lt_or_gt with hneg | hpos
  · refine ⟨f θb, f θa, ⟨⟨hbV, haV, by rw [u8h_f_det_swap']; linarith, by rw [segment_symm]; exact hsegab,
      fun c hc => by rw [openSegment_symm]; exact hnomark c hc⟩, p, hp, by rw [segment_symm]; exact hsub⟩,
      by rw [segment_symm]; exact hyab⟩
  · exact ⟨f θa, f θb, ⟨⟨haV, hbV, hpos, hsegab, hnomark⟩, p, hp, hsub⟩, hyab⟩

/-! ### frontier points are not isolated; a nondegenerate segment through each -/

/-! ### U8 helpers: sector coordinates and the two triangles of a radial quadrilateral -/

/-- A triangle from three points in positive order. -/
def u8h_mkTri (p q r : Plane) (h : 0 < det (q - p) (r - p)) : Triangle := ⟨![p, q, r], by simpa using h⟩

theorem u8h_mkTri_v0 (p q r : Plane) (h : 0 < det (q - p) (r - p)) : (u8h_mkTri p q r h).v 0 = p := rfl
theorem u8h_mkTri_v1 (p q r : Plane) (h : 0 < det (q - p) (r - p)) : (u8h_mkTri p q r h).v 1 = q := rfl
theorem u8h_mkTri_v2 (p q r : Plane) (h : 0 < det (q - p) (r - p)) : (u8h_mkTri p q r h).v 2 = r := rfl

theorem u8h_mkTri_carrier (p q r : Plane) (h : 0 < det (q - p) (r - p)) :
    (u8h_mkTri p q r h).carrier = convexHull ℝ {p, q, r} := u8h_f_carrier_of_v rfl

theorem u8h_mkTri_range (p q r : Plane) (h : 0 < det (q - p) (r - p)) :
    range (u8h_mkTri p q r h).v = {p, q, r} := u8h_f_range_three p q r

/-- Membership in a triangle by the three `det` signs, for a `u8h_mkTri`. -/
theorem u8h_mem_mkTri (p q r : Plane) (h : 0 < det (q - p) (r - p)) (x : Plane) :
    x ∈ (u8h_mkTri p q r h).carrier ↔
      0 ≤ det (q - p) (x - p) ∧ 0 ≤ det (r - q) (x - q) ∧ 0 ≤ det (p - r) (x - r) := by
  rw [U1_mem_carrier_iff_det]; rfl

theorem u8h_det_combo (A B : Plane) (c₁ c₂ d₁ d₂ : ℝ) :
    det (c₁ • A + c₂ • B) (d₁ • A + d₂ • B) = (c₁ * d₂ - c₂ * d₁) * det A B := by
  simp only [det, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring

/-- Positivity of the outer triangle `(z + sa•A, z + A, z + B)`. -/
theorem u8h_pos_tri2 {A B : Plane} (hAB : 0 < det A B) {sa : ℝ} (hsa1 : sa < 1) (z : Plane) :
    0 < det ((z + A) - (z + sa • A)) ((z + B) - (z + sa • A)) := by
  have : det ((z + A) - (z + sa • A)) ((z + B) - (z + sa • A)) = (1 - sa) * det A B := by
    simp only [det, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd,
      smul_eq_mul]; ring
  rw [this]; exact mul_pos (by linarith) hAB

/-- Positivity of the inner triangle `(z + sa•A, z + B, z + sb•B)`. -/
theorem u8h_pos_tri1 {A B : Plane} (hAB : 0 < det A B) {sa sb : ℝ} (hsa0 : 0 < sa) (hsb1 : sb < 1)
    (z : Plane) : 0 < det ((z + B) - (z + sa • A)) ((z + sb • B) - (z + sa • A)) := by
  have : det ((z + B) - (z + sa • A)) ((z + sb • B) - (z + sa • A)) = sa * (1 - sb) * det A B := by
    simp only [det, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd,
      smul_eq_mul]; ring
  rw [this]; exact mul_pos (mul_pos hsa0 (by linarith)) hAB

/-- The outer triangle in sector coordinates. -/
theorem u8h_mem_tri2 {A B : Plane} (hAB : 0 < det A B) {sa : ℝ} (hsa0 : 0 < sa) (hsa1 : sa < 1)
    (z : Plane) (α β : ℝ) :
    z + α • A + β • B ∈ (u8h_mkTri (z + sa • A) (z + A) (z + B) (u8h_pos_tri2 hAB hsa1 z)).carrier ↔
      0 ≤ β ∧ α + β ≤ 1 ∧ 1 ≤ α / sa + β := by
  rw [u8h_mem_mkTri]
  have e1 : det ((z + A) - (z + sa • A)) ((z + α • A + β • B) - (z + sa • A)) = ((1 - sa) * β) * det A B := by
    simp only [det, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd,
      smul_eq_mul]; ring
  have e2 : det ((z + B) - (z + A)) ((z + α • A + β • B) - (z + A)) = (1 - α - β) * det A B := by
    simp only [det, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd,
      smul_eq_mul]; ring
  have e3 : det ((z + sa • A) - (z + B)) ((z + α • A + β • B) - (z + B)) = (sa * (β - 1) + α) * det A B := by
    simp only [det, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd,
      smul_eq_mul]; ring
  rw [e1, e2, e3, mul_nonneg_iff_of_pos_right hAB, mul_nonneg_iff_of_pos_right hAB,
    mul_nonneg_iff_of_pos_right hAB]
  have h1 : 0 ≤ (1 - sa) * β ↔ 0 ≤ β := mul_nonneg_iff_of_pos_left (by linarith)
  rw [h1]
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, by linarith, ?_⟩
    rw [div_add' _ _ _ hsa0.ne', le_div_iff₀ hsa0]; nlinarith
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, by linarith, ?_⟩
    rw [div_add' _ _ _ hsa0.ne', le_div_iff₀ hsa0] at h3; nlinarith

/-- The inner triangle in sector coordinates. -/
theorem u8h_mem_tri1 {A B : Plane} (hAB : 0 < det A B) {sa sb : ℝ} (hsa0 : 0 < sa) (hsb0 : 0 < sb)
    (hsb1 : sb < 1) (z : Plane) (α β : ℝ) :
    z + α • A + β • B ∈ (u8h_mkTri (z + sa • A) (z + B) (z + sb • B) (u8h_pos_tri1 hAB hsa0 hsb1 z)).carrier ↔
      0 ≤ α ∧ α / sa + β ≤ 1 ∧ 1 ≤ α / sa + β / sb := by
  rw [u8h_mem_mkTri]
  have e1 : det ((z + B) - (z + sa • A)) ((z + α • A + β • B) - (z + sa • A)) = (sa - α - sa * β) * det A B := by
    simp only [det, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd,
      smul_eq_mul]; ring
  have e2 : det ((z + sb • B) - (z + B)) ((z + α • A + β • B) - (z + B)) = ((1 - sb) * α) * det A B := by
    simp only [det, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd,
      smul_eq_mul]; ring
  have e3 : det ((z + sa • A) - (z + sb • B)) ((z + α • A + β • B) - (z + sb • B)) =
      (sa * (β - sb) + sb * α) * det A B := by
    simp only [det, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd,
      smul_eq_mul]; ring
  rw [e1, e2, e3, mul_nonneg_iff_of_pos_right hAB, mul_nonneg_iff_of_pos_right hAB,
    mul_nonneg_iff_of_pos_right hAB]
  have h2 : 0 ≤ (1 - sb) * α ↔ 0 ≤ α := mul_nonneg_iff_of_pos_left (by linarith)
  rw [h2]
  have key1 : α / sa + β ≤ 1 ↔ 0 ≤ sa - α - sa * β := by
    rw [div_add' _ _ _ hsa0.ne', div_le_one hsa0]; constructor <;> intro h <;> nlinarith
  have key2 : 1 ≤ α / sa + β / sb ↔ 0 ≤ sa * (β - sb) + sb * α := by
    rw [div_add_div _ _ hsa0.ne' hsb0.ne', le_div_iff₀ (mul_pos hsa0 hsb0)]
    constructor <;> intro h <;> nlinarith
  rw [key1, key2]
  tauto

/-- The radial quadrilateral is the union of the two triangles. -/
theorem u8h_quad_iff {sa sb : ℝ} (hsa0 : 0 < sa) (hsa1 : sa < 1) (hsb0 : 0 < sb) (hsb1 : sb < 1)
    (α β : ℝ) :
    ((0 ≤ β ∧ α + β ≤ 1 ∧ 1 ≤ α / sa + β) ∨ (0 ≤ α ∧ α / sa + β ≤ 1 ∧ 1 ≤ α / sa + β / sb)) ↔
      (0 ≤ α ∧ 0 ≤ β ∧ α + β ≤ 1 ∧ 1 ≤ α / sa + β / sb) := by
  have hα : α / sa = α * sa⁻¹ := div_eq_mul_inv _ _
  have hβ : β / sb = β * sb⁻¹ := div_eq_mul_inv _ _
  have hsa' : 1 < sa⁻¹ := one_lt_inv_iff₀.2 ⟨hsa0, hsa1⟩
  have hsb' : 1 < sb⁻¹ := one_lt_inv_iff₀.2 ⟨hsb0, hsb1⟩
  rw [hα, hβ]
  constructor
  · rintro (⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩)
    · have hα0 : 0 ≤ α := by nlinarith
      refine ⟨hα0, h1, h2, ?_⟩
      nlinarith
    · have hβ0 : 0 ≤ β := by
        by_contra hneg; push Not at hneg
        nlinarith
      refine ⟨h1, hβ0, ?_, h3⟩
      nlinarith
  · rintro ⟨h0, h1, h2, h3⟩
    by_cases h : 1 ≤ α * sa⁻¹ + β
    · exact Or.inl ⟨h1, h2, h⟩
    · push Not at h
      exact Or.inr ⟨h0, h.le, h3⟩


/-! ### U8 helpers: nested discs, radial projections, sector coordinates -/

/-- The data of a radial annulus: an inner disc `Din` containing the centre `z` in its interior and
lying inside the interior of the outer disc `Dout`. -/
structure u8h_AnnCtx (z : Plane) (Din Dout : Set Plane) : Prop where
  hin : Link.IsDisc Din
  hout : Link.IsDisc Dout
  hz : z ∈ interior Din
  hsub : Din ⊆ interior Dout

namespace u8h_AnnCtx

variable {z : Plane} {Din Dout : Set Plane} (C : u8h_AnnCtx z Din Dout)
include C

theorem hz' : z ∈ interior Dout := C.hsub (interior_subset C.hz)

theorem notMem_of_frontier {a : Plane} (ha : a ∈ frontier Dout) : a ∉ Din := fun h =>
  ha.2 (C.hsub h)

theorem ne_of_frontier {a : Plane} (ha : a ∈ frontier Dout) : a ≠ z := u8h_f_frontier_ne C.hout C.hz' ha

theorem rgin_gt_one {a : Plane} (ha : a ∈ frontier Dout) : 1 < u8h_f_rg Din z a := by
  have := C.notMem_of_frontier ha
  rw [← u8h_f_rg_le_one_iff C.hin C.hz] at this
  push Not at this; exact this

/-- The radial scale `s_a = 1 / rg_in a` of the inner point on the ray through `a`. -/
noncomputable def _root_.SM.u8h_s (Din : Set Plane) (z a : Plane) : ℝ := (u8h_f_rg Din z a)⁻¹

theorem s_pos {a : Plane} (ha : a ∈ frontier Dout) : 0 < u8h_s Din z a :=
  inv_pos.2 (lt_trans one_pos (C.rgin_gt_one ha))

theorem s_lt_one {a : Plane} (ha : a ∈ frontier Dout) : u8h_s Din z a < 1 :=
  inv_lt_one_of_one_lt₀ (C.rgin_gt_one ha)

omit C in
theorem ray_eq (a : Plane) : u8h_f_ray Din z a = z + u8h_s Din z a • (a - z) := rfl

theorem ray_mem_frontier {a : Plane} (ha : a ∈ frontier Dout) : u8h_f_ray Din z a ∈ frontier Din :=
  u8h_f_ray_mem_frontier C.hin C.hz (C.ne_of_frontier ha)

theorem rgout_ray {a : Plane} (ha : a ∈ frontier Dout) :
    u8h_f_rg Dout z (u8h_f_ray Din z a) = u8h_s Din z a := by
  rw [ray_eq, u8h_f_rg_smul _ _ _ (C.s_pos ha).le, (u8h_f_rg_eq_one_iff C.hout C.hz' a).2 ha, mul_one]

/-- The outer radial projection of the inner point is the point itself. -/
theorem rayout_ray {a : Plane} (ha : a ∈ frontier Dout) : u8h_f_ray Dout z (u8h_f_ray Din z a) = a := by
  rw [u8h_f_ray, C.rgout_ray ha, ray_eq, add_sub_cancel_left, smul_smul,
    inv_mul_cancel₀ (C.s_pos ha).ne', one_smul, add_sub_cancel]

theorem ray_ne {a : Plane} (ha : a ∈ frontier Dout) : u8h_f_ray Din z a ≠ z :=
  u8h_f_frontier_ne C.hin C.hz (C.ray_mem_frontier ha)

omit C in
theorem ray_sub (a : Plane) : u8h_f_ray Din z a - z = u8h_s Din z a • (a - z) := by
  rw [ray_eq, add_sub_cancel_left]

theorem det_ray_ray {a b : Plane} (ha : a ∈ frontier Dout) (hb : b ∈ frontier Dout)
    (hab : 0 < det (a - z) (b - z)) :
    0 < det (u8h_f_ray Din z a - z) (u8h_f_ray Din z b - z) := by
  rw [ray_sub, ray_sub, u8h_f_det_smul_left', u8h_f_det_smul_right]
  exact mul_pos (C.s_pos ha) (mul_pos (C.s_pos hb) hab)

end u8h_AnnCtx

/-- Gauge linearity on a sector whose boundary piece is straight. -/
theorem u8h_rg_sector {D : Set Plane} (hD : Link.IsDisc D) {z : Plane} (hz : z ∈ interior D)
    {a b : Plane} (hseg : segment ℝ a b ⊆ frontier D) {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) :
    u8h_f_rg D z (z + α • (a - z) + β • (b - z)) = α + β := by
  rcases eq_or_lt_of_le (add_nonneg hα hβ) with h0 | hpos
  · have hα0 : α = 0 := by linarith
    have hβ0 : β = 0 := by linarith
    subst hα0; subst hβ0
    simp [u8h_f_rg_self]
  · set t := α + β with ht
    set c : Plane := (α / t) • a + (β / t) • b with hc
    have hcseg : c ∈ segment ℝ a b :=
      ⟨α / t, β / t, div_nonneg hα hpos.le, div_nonneg hβ hpos.le, by rw [← add_div, div_self hpos.ne'], rfl⟩
    have hrc : u8h_f_rg D z c = 1 := (u8h_f_rg_eq_one_iff hD hz c).2 (hseg hcseg)
    have e : z + α • (a - z) + β • (b - z) = z + t • (c - z) := by
      rw [hc]
      have h1 : (α / t) • a + (β / t) • b - z = (α / t) • (a - z) + (β / t) • (b - z) := by
        have : z = (α / t) • z + (β / t) • z := by
          rw [← add_smul, ← add_div, div_self hpos.ne', one_smul]
        conv_lhs => rw [this]
        rw [smul_sub, smul_sub]; abel
      rw [h1, smul_add, smul_smul, smul_smul, mul_div_cancel₀ _ hpos.ne', mul_div_cancel₀ _ hpos.ne',
        add_assoc]
    rw [e, u8h_f_rg_smul D z c hpos.le, hrc, mul_one]

/-- Cramer coordinates of `x - z` in the basis `A, B`. -/
theorem u8h_coord {A B : Plane} (hAB : det A B ≠ 0) (z x : Plane) :
    x = z + (det (x - z) B / det A B) • A + (det A (x - z) / det A B) • B := by
  have := u8h_f_cramer hAB (x - z)
  rw [add_assoc, ← this, add_sub_cancel]


/-! ### U8 helpers: the radial annulus triangulation (faces over the adjacent pairs of a fan) -/

/-- The faces of the radial annulus triangulation: for each adjacent pair `(a, b)` of outer marks the
outer triangle `(Pt a, a, b)` and the inner triangle `(Pt a, b, Pt b)`, where `Pt = u8h_f_ray Din z`. -/
def u8h_annFaces (z : Plane) (Din : Set Plane) (A : Plane → Plane → Prop) : Set Triangle :=
  {T | ∃ a b, A a b ∧
    (T.v = ![u8h_f_ray Din z a, a, b] ∨ T.v = ![u8h_f_ray Din z a, b, u8h_f_ray Din z b])}

/-- The hypotheses of the annulus triangulation: nested discs, a finite set of marks on the outer
frontier, an adjacency relation `A` contained in `u8h_f_Adj` and covering the outer frontier, and
straightness of the inner frontier between the radial projections of adjacent marks. -/
structure u8h_AnnData (z : Plane) (Din Dout : Set Plane) (V : Set Plane) (A : Plane → Plane → Prop) :
    Prop where
  ctx : u8h_AnnCtx z Din Dout
  hVfin : V.Finite
  hV : V ⊆ frontier Dout
  hA : ∀ a b, A a b → u8h_f_Adj Dout z V a b
  hcov : ∀ y ∈ frontier Dout, ∃ a b, A a b ∧ y ∈ segment ℝ a b
  hstraight : ∀ a b, A a b → segment ℝ (u8h_f_ray Din z a) (u8h_f_ray Din z b) ⊆ frontier Din

theorem u8h_det_sub_ray (z a b : Plane) (sa : ℝ) :
    det (a - (z + sa • (a - z))) (b - (z + sa • (a - z))) = (1 - sa) * det (a - z) (b - z) := by
  simp only [det, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd,
    smul_eq_mul]; ring

theorem u8h_det_sub_ray' (z a b : Plane) (sa sb : ℝ) :
    det (b - (z + sa • (a - z))) ((z + sb • (b - z)) - (z + sa • (a - z))) =
      sa * (1 - sb) * det (a - z) (b - z) := by
  simp only [det, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd,
    smul_eq_mul]; ring

/-- Sector coordinates of a point with respect to the pair `(a, b)` around `z`. -/
noncomputable def u8h_α (z a b x : Plane) : ℝ := det (x - z) (b - z) / det (a - z) (b - z)
noncomputable def u8h_β (z a b x : Plane) : ℝ := det (a - z) (x - z) / det (a - z) (b - z)

theorem u8h_div_nonneg_iff {p q : ℝ} (hq : 0 < q) : 0 ≤ p / q ↔ 0 ≤ p := by
  constructor
  · intro h; by_contra hn; push Not at hn
    have := div_neg_of_neg_of_pos hn hq; linarith
  · intro h; exact div_nonneg h hq.le

namespace u8h_AnnData

variable {z : Plane} {Din Dout V : Set Plane} {A : Plane → Plane → Prop} (D : u8h_AnnData z Din Dout V A)
include D

theorem C : u8h_AnnCtx z Din Dout := D.ctx
theorem hin : Link.IsDisc Din := D.ctx.hin
theorem hout : Link.IsDisc Dout := D.ctx.hout
theorem hz : z ∈ interior Din := D.ctx.hz

theorem ha {a b : Plane} (h : A a b) : a ∈ frontier Dout := D.hV (D.hA a b h).1
theorem hb {a b : Plane} (h : A a b) : b ∈ frontier Dout := D.hV (D.hA a b h).2.1
theorem hab {a b : Plane} (h : A a b) : 0 < det (a - z) (b - z) := (D.hA a b h).2.2.1
theorem hseg {a b : Plane} (h : A a b) : segment ℝ a b ⊆ frontier Dout := (D.hA a b h).2.2.2.1
theorem hnomark {a b : Plane} (h : A a b) : ∀ c ∈ V, c ∉ openSegment ℝ a b := (D.hA a b h).2.2.2.2

theorem pos2 {a b : Plane} (h : A a b) :
    0 < det (a - u8h_f_ray Din z a) (b - u8h_f_ray Din z a) := by
  rw [u8h_AnnCtx.ray_eq, u8h_det_sub_ray]
  exact mul_pos (by linarith [D.C.s_lt_one (D.ha h)]) (D.hab h)

theorem pos1 {a b : Plane} (h : A a b) :
    0 < det (b - u8h_f_ray Din z a) (u8h_f_ray Din z b - u8h_f_ray Din z a) := by
  rw [u8h_AnnCtx.ray_eq, u8h_AnnCtx.ray_eq, u8h_det_sub_ray']
  exact mul_pos (mul_pos (D.C.s_pos (D.ha h)) (by linarith [D.C.s_lt_one (D.hb h)])) (D.hab h)

/-- The outer face of the pair `(a, b)`. -/
noncomputable def tri2 {a b : Plane} (h : A a b) : Triangle := u8h_mkTri _ _ _ (D.pos2 h)
/-- The inner face of the pair `(a, b)`. -/
noncomputable def tri1 {a b : Plane} (h : A a b) : Triangle := u8h_mkTri _ _ _ (D.pos1 h)

theorem tri2_v {a b : Plane} (h : A a b) : (D.tri2 h).v = ![u8h_f_ray Din z a, a, b] := rfl
theorem tri1_v {a b : Plane} (h : A a b) :
    (D.tri1 h).v = ![u8h_f_ray Din z a, b, u8h_f_ray Din z b] := rfl

theorem tri2_mem {a b : Plane} (h : A a b) : D.tri2 h ∈ u8h_annFaces z Din A := ⟨a, b, h, Or.inl rfl⟩
theorem tri1_mem {a b : Plane} (h : A a b) : D.tri1 h ∈ u8h_annFaces z Din A := ⟨a, b, h, Or.inr rfl⟩

theorem tri2_carrier {a b : Plane} (h : A a b) :
    (D.tri2 h).carrier = convexHull ℝ {u8h_f_ray Din z a, a, b} := u8h_f_carrier_of_v rfl
theorem tri1_carrier {a b : Plane} (h : A a b) :
    (D.tri1 h).carrier = convexHull ℝ {u8h_f_ray Din z a, b, u8h_f_ray Din z b} := u8h_f_carrier_of_v rfl

/-- Every annulus face is one of the two faces of its pair (as a carrier). -/
theorem carrier_cases {T : Triangle} (hT : T ∈ u8h_annFaces z Din A) :
    ∃ a b, ∃ h : A a b, T.carrier = (D.tri2 h).carrier ∨ T.carrier = (D.tri1 h).carrier := by
  obtain ⟨a, b, h, hv | hv⟩ := hT
  · exact ⟨a, b, h, Or.inl (by rw [u8h_f_carrier_of_v hv, D.tri2_carrier])⟩
  · exact ⟨a, b, h, Or.inr (by rw [u8h_f_carrier_of_v hv, D.tri1_carrier])⟩

theorem range_cases {T : Triangle} (hT : T ∈ u8h_annFaces z Din A) :
    ∃ a b, ∃ h : A a b, range T.v = range (D.tri2 h).v ∨ range T.v = range (D.tri1 h).v := by
  obtain ⟨a, b, h, hv | hv⟩ := hT
  · exact ⟨a, b, h, Or.inl (by rw [hv]; rfl)⟩
  · exact ⟨a, b, h, Or.inr (by rw [hv]; rfl)⟩

theorem coord {a b : Plane} (h : A a b) (x : Plane) :
    x = z + u8h_α z a b x • (a - z) + u8h_β z a b x • (b - z) := u8h_coord (D.hab h).ne' z x

theorem α_nonneg_iff {a b : Plane} (h : A a b) (x : Plane) : 0 ≤ u8h_α z a b x ↔ 0 ≤ det (x - z) (b - z) :=
  u8h_div_nonneg_iff (D.hab h)
theorem β_nonneg_iff {a b : Plane} (h : A a b) (x : Plane) : 0 ≤ u8h_β z a b x ↔ 0 ≤ det (a - z) (x - z) :=
  u8h_div_nonneg_iff (D.hab h)

/-- Membership in the outer face, in sector coordinates. -/
theorem mem_tri2_iff {a b : Plane} (h : A a b) (x : Plane) :
    x ∈ (D.tri2 h).carrier ↔ 0 ≤ u8h_β z a b x ∧ u8h_α z a b x + u8h_β z a b x ≤ 1 ∧ 1 ≤ u8h_α z a b x / u8h_s Din z a + u8h_β z a b x := by
  have key := u8h_mem_tri2 (D.hab h) (D.C.s_pos (D.ha h)) (D.C.s_lt_one (D.ha h)) z (u8h_α z a b x) (u8h_β z a b x)
  rw [u8h_mkTri_carrier, add_sub_cancel, add_sub_cancel, ← u8h_AnnCtx.ray_eq, ← D.tri2_carrier h,
    ← D.coord h x] at key
  exact key

/-- Membership in the inner face, in sector coordinates. -/
theorem mem_tri1_iff {a b : Plane} (h : A a b) (x : Plane) :
    x ∈ (D.tri1 h).carrier ↔ 0 ≤ u8h_α z a b x ∧ u8h_α z a b x / u8h_s Din z a + u8h_β z a b x ≤ 1 ∧
      1 ≤ u8h_α z a b x / u8h_s Din z a + u8h_β z a b x / u8h_s Din z b := by
  have key := u8h_mem_tri1 (D.hab h) (D.C.s_pos (D.ha h)) (D.C.s_pos (D.hb h)) (D.C.s_lt_one (D.hb h)) z
    (u8h_α z a b x) (u8h_β z a b x)
  rw [u8h_mkTri_carrier, add_sub_cancel, ← u8h_AnnCtx.ray_eq, ← u8h_AnnCtx.ray_eq, ← D.tri1_carrier h,
    ← D.coord h x] at key
  exact key

/-- The outer gauge in sector coordinates. -/
theorem rgout_coord {a b : Plane} (h : A a b) {x : Plane} (hα : 0 ≤ u8h_α z a b x) (hβ : 0 ≤ u8h_β z a b x) :
    u8h_f_rg Dout z x = u8h_α z a b x + u8h_β z a b x := by
  conv_lhs => rw [D.coord h x]
  exact u8h_rg_sector D.hout D.C.hz' (D.hseg h) hα hβ

/-- The inner gauge in sector coordinates. -/
theorem rgin_coord {a b : Plane} (h : A a b) {x : Plane} (hα : 0 ≤ u8h_α z a b x) (hβ : 0 ≤ u8h_β z a b x) :
    u8h_f_rg Din z x = u8h_α z a b x / u8h_s Din z a + u8h_β z a b x / u8h_s Din z b := by
  have hsa := D.C.s_pos (D.ha h)
  have hsb := D.C.s_pos (D.hb h)
  have e : x = z + (u8h_α z a b x / u8h_s Din z a) • (u8h_f_ray Din z a - z) +
      (u8h_β z a b x / u8h_s Din z b) • (u8h_f_ray Din z b - z) := by
    rw [u8h_AnnCtx.ray_sub, u8h_AnnCtx.ray_sub, smul_smul, smul_smul, div_mul_cancel₀ _ hsa.ne',
      div_mul_cancel₀ _ hsb.ne']
    exact D.coord h x
  conv_lhs => rw [e]
  exact u8h_rg_sector D.hin D.hz (D.hstraight a b h) (div_nonneg hα hsa.le) (div_nonneg hβ hsb.le)

/-- The quadrilateral of the pair `(a, b)`: the union of its two faces, in sector coordinates. -/
theorem mem_quad_iff {a b : Plane} (h : A a b) (x : Plane) :
    x ∈ (D.tri2 h).carrier ∪ (D.tri1 h).carrier ↔
      0 ≤ u8h_α z a b x ∧ 0 ≤ u8h_β z a b x ∧ u8h_α z a b x + u8h_β z a b x ≤ 1 ∧
        1 ≤ u8h_α z a b x / u8h_s Din z a + u8h_β z a b x / u8h_s Din z b := by
  rw [mem_union, D.mem_tri2_iff, D.mem_tri1_iff]
  exact u8h_quad_iff (D.C.s_pos (D.ha h)) (D.C.s_lt_one (D.ha h)) (D.C.s_pos (D.hb h)) (D.C.s_lt_one (D.hb h)) _ _

/-- A point of the quadrilateral lies in the annulus. -/
theorem quad_subset {a b : Plane} (h : A a b) :
    (D.tri2 h).carrier ∪ (D.tri1 h).carrier ⊆ Dout \ interior Din := by
  intro x hx
  obtain ⟨h0, h1, h2, h3⟩ := (D.mem_quad_iff h x).1 hx
  refine ⟨?_, ?_⟩
  · rw [← u8h_f_rg_le_one_iff D.hout D.C.hz', D.rgout_coord h h0 h1]; exact h2
  · rw [← u8h_f_rg_lt_one_iff D.hin D.hz, D.rgin_coord h h0 h1]; linarith

/-- The fan triangulation of the outer disc by the adjacent pairs. -/
theorem fan : ∃ K : Triangulation Dout, K.faces = u8h_f_fanFaces z A :=
  u8h_f_fan_triangulation D.hout D.C.hz' D.hVfin D.hV D.hA D.hcov

/-- Every point of the annulus lies in the quadrilateral of some adjacent pair. -/
theorem cover_of_mem {x : Plane} (hx : x ∈ Dout \ interior Din) :
    ∃ a b, ∃ h : A a b, x ∈ (D.tri2 h).carrier ∪ (D.tri1 h).carrier := by
  obtain ⟨K, hK⟩ := D.fan
  have hxK : x ∈ ⋃ T ∈ K.faces, T.carrier := by rw [K.cover]; exact hx.1
  obtain ⟨T, hT, hxT⟩ := mem_iUnion₂.1 hxK
  rw [hK] at hT
  obtain ⟨a, b, h, hv⟩ := hT
  rw [u8h_f_carrier_of_v hv, u8h_f_mem_fan_iff D.hout D.C.hz' (D.hab h) (D.hseg h)] at hxT
  obtain ⟨h1, h2, h3⟩ := hxT
  refine ⟨a, b, h, (D.mem_quad_iff h x).2 ⟨?_, ?_, ?_, ?_⟩⟩
  · exact (D.α_nonneg_iff h x).2 h2
  · exact (D.β_nonneg_iff h x).2 h1
  · rw [← D.rgout_coord h ((D.α_nonneg_iff h x).2 h2) ((D.β_nonneg_iff h x).2 h1),
      u8h_f_rg_le_one_iff D.hout D.C.hz']; exact h3
  · rw [← D.rgin_coord h ((D.α_nonneg_iff h x).2 h2) ((D.β_nonneg_iff h x).2 h1)]
    have := hx.2
    rw [← u8h_f_rg_lt_one_iff D.hin D.hz] at this
    push Not at this; exact this

end u8h_AnnData

namespace u8h_AnnData

variable {z : Plane} {Din Dout V : Set Plane} {A : Plane → Plane → Prop} (D : u8h_AnnData z Din Dout V A)
include D

/-- The fan face of the pair `(a, b)` in the outer disc. -/
noncomputable def fanTri {a b : Plane} (h : A a b) : Triangle := u8h_mkTri z a b (D.hab h)

theorem fanTri_carrier {a b : Plane} (h : A a b) : (D.fanTri h).carrier = convexHull ℝ {z, a, b} :=
  u8h_mkTri_carrier _ _ _ _

theorem fanTri_mem {K : Triangulation Dout} (hK : K.faces = u8h_f_fanFaces z A) {a b : Plane} (h : A a b) :
    D.fanTri h ∈ K.faces := by
  rw [hK]; exact ⟨a, b, h, rfl⟩

theorem ray_mem_fan {a b : Plane} (h : A a b) : u8h_f_ray Din z a ∈ convexHull ℝ {z, a, b} := by
  have hs0 := (D.C.s_pos (D.ha h)).le
  have hs1 := (D.C.s_lt_one (D.ha h)).le
  have : u8h_f_ray Din z a ∈ segment ℝ z a :=
    ⟨1 - u8h_s Din z a, u8h_s Din z a, by linarith, hs0, by ring, by
      rw [u8h_AnnCtx.ray_eq, smul_sub]; module⟩
  exact segment_subset_convexHull (by simp) (by simp) this

theorem ray_mem_fan' {a b : Plane} (h : A a b) : u8h_f_ray Din z b ∈ convexHull ℝ {z, a, b} := by
  have hs0 := (D.C.s_pos (D.hb h)).le
  have hs1 := (D.C.s_lt_one (D.hb h)).le
  have : u8h_f_ray Din z b ∈ segment ℝ z b :=
    ⟨1 - u8h_s Din z b, u8h_s Din z b, by linarith, hs0, by ring, by
      rw [u8h_AnnCtx.ray_eq, smul_sub]; module⟩
  exact segment_subset_convexHull (by simp) (by simp) this

theorem tri2_subset_fan {a b : Plane} (h : A a b) : (D.tri2 h).carrier ⊆ convexHull ℝ {z, a, b} := by
  rw [D.tri2_carrier]
  apply convexHull_min _ (convex_convexHull ℝ _)
  intro w hw
  simp only [mem_insert_iff, mem_singleton_iff] at hw
  rcases hw with rfl | rfl | rfl
  · exact D.ray_mem_fan h
  · exact subset_convexHull ℝ _ (by simp)
  · exact subset_convexHull ℝ _ (by simp)

theorem tri1_subset_fan {a b : Plane} (h : A a b) : (D.tri1 h).carrier ⊆ convexHull ℝ {z, a, b} := by
  rw [D.tri1_carrier]
  apply convexHull_min _ (convex_convexHull ℝ _)
  intro w hw
  simp only [mem_insert_iff, mem_singleton_iff] at hw
  rcases hw with rfl | rfl | rfl
  · exact D.ray_mem_fan h
  · exact subset_convexHull ℝ _ (by simp)
  · exact D.ray_mem_fan' h

theorem quad_subset_fan {a b : Plane} (h : A a b) :
    (D.tri2 h).carrier ∪ (D.tri1 h).carrier ⊆ convexHull ℝ {z, a, b} :=
  union_subset (D.tri2_subset_fan h) (D.tri1_subset_fan h)

/-- (V1) an outer mark lying in the quadrilateral of `(a, b)` is `a` or `b`. -/
theorem mark_of_mem_quad {a b c : Plane} (h : A a b) (hc : c ∈ V)
    (hcq : c ∈ (D.tri2 h).carrier ∪ (D.tri1 h).carrier) : c = a ∨ c = b := by
  have hcf := D.quad_subset_fan h hcq
  rw [u8h_f_mem_fan_iff D.hout D.C.hz' (D.hab h) (D.hseg h)] at hcf
  have hcs := u8h_f_frontier_mem_segment D.hout D.C.hz' (D.hab h) (D.hseg h) (D.hV hc) hcf.1 hcf.2.1
  rcases u8h_f_mem_segment_cases hcs with h1 | h1 | h1
  · exact Or.inl h1
  · exact Or.inr h1
  · exact absurd h1 (D.hnomark h c hc)

/-- (V2) the inner point of an outer mark lying in the quadrilateral of `(a, b)` is `Pt a` or `Pt b`. -/
theorem ray_of_mem_quad {a b c : Plane} (h : A a b) (hc : c ∈ V)
    (hcq : u8h_f_ray Din z c ∈ (D.tri2 h).carrier ∪ (D.tri1 h).carrier) :
    u8h_f_ray Din z c = u8h_f_ray Din z a ∨ u8h_f_ray Din z c = u8h_f_ray Din z b := by
  have hcf := D.quad_subset_fan h hcq
  rw [u8h_f_mem_fan_iff D.hout D.C.hz' (D.hab h) (D.hseg h)] at hcf
  have hne : u8h_f_ray Din z c ≠ z := D.C.ray_ne (D.hV hc)
  have hcs := u8h_f_ray_mem_segment D.hout D.C.hz' (D.hab h) (D.hseg h) hne hcf.1 hcf.2.1
  rw [D.C.rayout_ray (D.hV hc)] at hcs
  rcases u8h_f_mem_segment_cases hcs with h1 | h1 | h1
  · exact Or.inl (by rw [h1])
  · exact Or.inr (by rw [h1])
  · exact absurd h1 (D.hnomark h c hc)

/-- (V3) the outer mark `a` is not in the inner face. -/
theorem a_notMem_tri1 {a b : Plane} (h : A a b) : a ∉ (D.tri1 h).carrier := by
  rw [D.mem_tri1_iff]
  have hα : u8h_α z a b a = 1 := div_self (D.hab h).ne'
  have hβ : u8h_β z a b a = 0 := by rw [u8h_β, u8h_f_det_self, zero_div]
  rw [hα, hβ, add_zero]
  rintro ⟨-, h1, -⟩
  have hs := D.C.s_pos (D.ha h)
  rw [div_le_one hs] at h1
  linarith [D.C.s_lt_one (D.ha h)]

/-- (V4) the inner point `Pt b` is not in the outer face. -/
theorem ray_b_notMem_tri2 {a b : Plane} (h : A a b) : u8h_f_ray Din z b ∉ (D.tri2 h).carrier := by
  rw [D.mem_tri2_iff]
  have hα : u8h_α z a b (u8h_f_ray Din z b) = 0 := by
    rw [u8h_α, u8h_AnnCtx.ray_sub, u8h_f_det_smul_left', u8h_f_det_self, mul_zero, zero_div]
  have hβ : u8h_β z a b (u8h_f_ray Din z b) = u8h_s Din z b := by
    rw [u8h_β, u8h_AnnCtx.ray_sub, u8h_f_det_smul_right, mul_div_assoc, div_self (D.hab h).ne', mul_one]
  rw [hα, hβ, zero_div, zero_add]
  rintro ⟨-, -, h1⟩
  linarith [D.C.s_lt_one (D.hb h)]

/-- The vertex condition of the gluing criterion. -/
theorem vert_mem {T T' : Triangle} (hT : T ∈ u8h_annFaces z Din A) (hT' : T' ∈ u8h_annFaces z Din A)
    (j : Fin 3) (hj : T'.v j ∈ T.carrier) : T'.v j ∈ range T.v := by
  obtain ⟨a, b, h, hcar⟩ := D.carrier_cases hT
  obtain ⟨a', b', h', hr'⟩ := D.range_cases hT'
  have hw : T'.v j ∈ range T'.v := mem_range_self j
  have ha' : a' ∈ V := (D.hA a' b' h').1
  have hb' : b' ∈ V := (D.hA a' b' h').2.1
  -- the vertex is an outer mark or the inner point of an outer mark
  have hcases : (∃ c ∈ V, T'.v j = c) ∨ (∃ c ∈ V, T'.v j = u8h_f_ray Din z c) := by
    rcases hr' with hr' | hr'
    · rw [hr', D.tri2_v, u8h_f_range_three] at hw
      simp only [mem_insert_iff, mem_singleton_iff] at hw
      rcases hw with hw | hw | hw
      · exact Or.inr ⟨a', ha', hw⟩
      · exact Or.inl ⟨a', ha', hw⟩
      · exact Or.inl ⟨b', hb', hw⟩
    · rw [hr', D.tri1_v, u8h_f_range_three] at hw
      simp only [mem_insert_iff, mem_singleton_iff] at hw
      rcases hw with hw | hw | hw
      · exact Or.inr ⟨a', ha', hw⟩
      · exact Or.inl ⟨b', hb', hw⟩
      · exact Or.inr ⟨b', hb', hw⟩
  rcases hcar with hcar | hcar
  · -- `T` is the outer face of `(a, b)`
    have hrT : range T.v = range (D.tri2 h).v := u3h_range_eq_of_carrier_eq hcar
    rw [hcar] at hj
    have hq : T'.v j ∈ (D.tri2 h).carrier ∪ (D.tri1 h).carrier := Or.inl hj
    rw [hrT, D.tri2_v, u8h_f_range_three]
    rcases hcases with ⟨c, hcV, hwc⟩ | ⟨c, hcV, hwc⟩
    · rw [hwc] at hq ⊢
      rcases D.mark_of_mem_quad h hcV hq with rfl | rfl <;> simp
    · rw [hwc] at hq hj ⊢
      rcases D.ray_of_mem_quad h hcV hq with hcc | hcc
      · rw [hcc]; simp
      · rw [hcc] at hj; exact absurd hj (D.ray_b_notMem_tri2 h)
  · -- `T` is the inner face of `(a, b)`
    have hrT : range T.v = range (D.tri1 h).v := u3h_range_eq_of_carrier_eq hcar
    rw [hcar] at hj
    have hq : T'.v j ∈ (D.tri2 h).carrier ∪ (D.tri1 h).carrier := Or.inr hj
    rw [hrT, D.tri1_v, u8h_f_range_three]
    rcases hcases with ⟨c, hcV, hwc⟩ | ⟨c, hcV, hwc⟩
    · rw [hwc] at hq hj ⊢
      rcases D.mark_of_mem_quad h hcV hq with rfl | rfl
      · exact absurd hj (D.a_notMem_tri1 h)
      · simp
    · rw [hwc] at hq ⊢
      rcases D.ray_of_mem_quad h hcV hq with hcc | hcc <;> rw [hcc] <;> simp



/-- Two adjacent pairs spanning the same fan face are equal. -/
theorem pair_eq_of_range {a b a' b' : Plane} (h : A a b) (h' : A a' b')
    (hr : ({z, a, b} : Set Plane) = {z, a', b'}) : a = a' ∧ b = b' := by
  have haz : a ≠ z := D.C.ne_of_frontier (D.ha h)
  have hbz : b ≠ z := D.C.ne_of_frontier (D.hb h)
  have hab_ne : a ≠ b := fun e => by
    have := D.hab h; rw [e, u8h_f_det_self] at this; exact lt_irrefl _ this
  have ha : a ∈ ({z, a', b'} : Set Plane) := by rw [← hr]; simp
  have hb : b ∈ ({z, a', b'} : Set Plane) := by rw [← hr]; simp
  simp only [mem_insert_iff, mem_singleton_iff] at ha hb
  rcases ha with ha | ha | ha
  · exact absurd ha haz
  · rcases hb with hb | hb | hb
    · exact absurd hb hbz
    · exact absurd (ha.trans hb.symm) hab_ne
    · exact ⟨ha, hb⟩
  · rcases hb with hb | hb | hb
    · exact absurd hb hbz
    · exfalso
      have h1 := D.hab h
      have h2 := D.hab h'
      rw [ha, hb, u8h_f_det_swap'] at h1
      linarith
    · exact absurd (ha.trans hb.symm) hab_ne

/-- The two faces of a pair are separated by their common diagonal. -/
theorem diag_sep {a b : Plane} (h : A a b) :
    ∃ (p : Plane) (r : ℝ), p ≠ 0 ∧ (∀ i, planeDot p ((D.tri2 h).v i) ≤ r) ∧
      ∀ i, r ≤ planeDot p ((D.tri1 h).v i) := by
  set Pa := u8h_f_ray Din z a with hPa
  set Pb := u8h_f_ray Din z b with hPb
  have hne : b - Pa ≠ 0 := by
    intro e; have := D.pos1 h; rw [← hPa, ← hPb, e, u8h_f_det_zero_left] at this; exact lt_irrefl _ this
  have key : ∀ x, planeDot (u3h_dir (b - Pa)) x - planeDot (u3h_dir (b - Pa)) Pa = det (b - Pa) (x - Pa) := by
    intro x; rw [u3h_det_eq_planeDot, u3h_planeDot_sub]
  refine ⟨u3h_dir (b - Pa), planeDot (u3h_dir (b - Pa)) Pa, u3h_dir_ne_zero hne, ?_, ?_⟩
  · intro i
    fin_cases i
    · exact le_refl _
    · show planeDot (u3h_dir (b - Pa)) a ≤ _
      have h1 := key a
      have h2 := D.pos2 h
      rw [← hPa] at h2
      rw [u8h_f_det_swap'] at h1
      linarith
    · show planeDot (u3h_dir (b - Pa)) b ≤ _
      have h1 := key b
      rw [u8h_f_det_self] at h1
      linarith
  · intro i
    fin_cases i
    · exact le_refl _
    · show _ ≤ planeDot (u3h_dir (b - Pa)) b
      have h1 := key b
      rw [u8h_f_det_self] at h1
      linarith
    · show _ ≤ planeDot (u3h_dir (b - Pa)) Pb
      have h1 := key Pb
      have h2 := D.pos1 h
      rw [← hPa, ← hPb] at h2
      linarith

/-- The separation condition of the gluing criterion. -/
theorem sep {T T' : Triangle} (hT : T ∈ u8h_annFaces z Din A) (hT' : T' ∈ u8h_annFaces z Din A)
    (hne : T.carrier ≠ T'.carrier) :
    ∃ (p : Plane) (r : ℝ), p ≠ 0 ∧ (∀ i, planeDot p (T.v i) ≤ r) ∧ ∀ i, r ≤ planeDot p (T'.v i) := by
  obtain ⟨K, hK⟩ := D.fan
  obtain ⟨a, b, h, hc⟩ := D.carrier_cases hT
  obtain ⟨a', b', h', hc'⟩ := D.carrier_cases hT'
  have hvT : ∀ i, T.v i ∈ T.carrier := fun i => subset_convexHull ℝ _ (mem_range_self i)
  have hvT' : ∀ i, T'.v i ∈ T'.carrier := fun i => subset_convexHull ℝ _ (mem_range_self i)
  have hsubT : T.carrier ⊆ convexHull ℝ {z, a, b} := by
    rcases hc with hc | hc
    · rw [hc]; exact D.tri2_subset_fan h
    · rw [hc]; exact D.tri1_subset_fan h
  have hsubT' : T'.carrier ⊆ convexHull ℝ {z, a', b'} := by
    rcases hc' with hc' | hc'
    · rw [hc']; exact D.tri2_subset_fan h'
    · rw [hc']; exact D.tri1_subset_fan h'
  by_cases hF : (D.fanTri h).carrier = (D.fanTri h').carrier
  · have hr := u3h_range_eq_of_carrier_eq hF
    rw [fanTri, fanTri, u8h_mkTri_range, u8h_mkTri_range] at hr
    obtain ⟨rfl, rfl⟩ := D.pair_eq_of_range h h' hr
    obtain ⟨p, r, hp, h1, h2⟩ := D.diag_sep h
    rcases hc with hc | hc <;> rcases hc' with hc' | hc'
    · exact absurd (hc.trans hc'.symm) hne
    · refine ⟨p, r, hp, fun i => ?_, fun i => ?_⟩
      · exact u3h_carrier_subset_le _ h1 (hc ▸ hvT i)
      · exact u3h_carrier_subset_ge _ h2 (hc' ▸ hvT' i)
    · refine ⟨-p, -r, neg_ne_zero.2 hp, fun i => ?_, fun i => ?_⟩
      · rw [u3h_planeDot_neg_left]
        have := u3h_carrier_subset_ge _ h2 (hc ▸ hvT i)
        simp only [mem_setOf_eq] at this; linarith
      · rw [u3h_planeDot_neg_left]
        have := u3h_carrier_subset_le _ h1 (hc' ▸ hvT' i)
        simp only [mem_setOf_eq] at this; linarith
    · exact absurd (hc.trans hc'.symm) hne
  · obtain ⟨p, r, hp, h1, h2⟩ := u3h_faces_separated K (D.fanTri_mem hK h) (D.fanTri_mem hK h') hF
    refine ⟨p, r, hp, fun i => ?_, fun i => ?_⟩
    · have := hsubT (hvT i)
      rw [← D.fanTri_carrier h] at this
      exact u3h_carrier_subset_le _ h1 this
    · have := hsubT' (hvT' i)
      rw [← D.fanTri_carrier h'] at this
      exact u3h_carrier_subset_ge _ h2 this

theorem faces_finite : (u8h_annFaces z Din A).Finite := by
  have hS : {p : Plane × Plane | A p.1 p.2}.Finite := by
    apply (D.hVfin.prod D.hVfin).subset
    rintro ⟨a, b⟩ h; exact ⟨(D.hA a b h).1, (D.hA a b h).2.1⟩
  have himg : Triangle.v '' u8h_annFaces z Din A ⊆
      (fun p : Plane × Plane => ![u8h_f_ray Din z p.1, p.1, p.2]) '' {p | A p.1 p.2} ∪
      (fun p : Plane × Plane => ![u8h_f_ray Din z p.1, p.2, u8h_f_ray Din z p.2]) '' {p | A p.1 p.2} := by
    rintro _ ⟨T, ⟨a, b, h, hv | hv⟩, rfl⟩
    · exact Or.inl ⟨(a, b), h, hv.symm⟩
    · exact Or.inr ⟨(a, b), h, hv.symm⟩
  refine Set.Finite.of_finite_image (f := Triangle.v) (((hS.image _).union (hS.image _)).subset himg) ?_
  rintro ⟨v, hv⟩ _ ⟨v', hv'⟩ _ hTT'
  simp only at hTT'
  subst hTT'; rfl

theorem cover_eq : (⋃ T ∈ u8h_annFaces z Din A, T.carrier) = Dout \ interior Din := by
  apply Subset.antisymm
  · intro x hx
    obtain ⟨T, hT, hxT⟩ := mem_iUnion₂.1 hx
    obtain ⟨a, b, h, hc⟩ := D.carrier_cases hT
    apply D.quad_subset h
    rcases hc with hc | hc
    · exact Or.inl (hc ▸ hxT)
    · exact Or.inr (hc ▸ hxT)
  · intro x hx
    obtain ⟨a, b, h, hq⟩ := D.cover_of_mem hx
    rcases hq with hq | hq
    · exact mem_iUnion₂.2 ⟨_, D.tri2_mem h, hq⟩
    · exact mem_iUnion₂.2 ⟨_, D.tri1_mem h, hq⟩

/-- **The radial annulus triangulation.** -/
theorem triangulation : ∃ K : Triangulation (Dout \ interior Din), K.faces = u8h_annFaces z Din A :=
  ⟨⟨u8h_annFaces z Din A, D.faces_finite, D.cover_eq,
    u3h_inter_of_family (fun T hT T' hT' hne => D.sep hT hT' hne)
      (fun T hT T' hT' j hj => D.vert_mem hT hT' j hj)⟩, rfl⟩

/-- Every point of the inner frontier lies on the inner edge of some pair. -/
theorem frontier_in_cover {y : Plane} (hy : y ∈ frontier Din) :
    ∃ a b, ∃ h : A a b, y ∈ segment ℝ (u8h_f_ray Din z a) (u8h_f_ray Din z b) := by
  have hyD : y ∈ Din := D.hin.2.1.isClosed.frontier_subset hy
  have hy' : y ∈ Dout \ interior Din := ⟨interior_subset (D.ctx.hsub hyD), hy.2⟩
  obtain ⟨a, b, h, hq⟩ := D.cover_of_mem hy'
  have hf := D.quad_subset_fan h hq
  rw [u8h_f_mem_fan_iff D.hout D.C.hz' (D.hab h) (D.hseg h)] at hf
  have h1 : 0 ≤ det (u8h_f_ray Din z a - z) (y - z) := by
    rw [u8h_AnnCtx.ray_sub, u8h_f_det_smul_left']; exact mul_nonneg (D.C.s_pos (D.ha h)).le hf.1
  have h2 : 0 ≤ det (y - z) (u8h_f_ray Din z b - z) := by
    rw [u8h_AnnCtx.ray_sub, u8h_f_det_smul_right]; exact mul_nonneg (D.C.s_pos (D.hb h)).le hf.2.1
  exact ⟨a, b, h, u8h_f_frontier_mem_segment D.hin D.hz (D.C.det_ray_ray (D.ha h) (D.hb h) (D.hab h))
    (D.hstraight a b h) hy h1 h2⟩

end u8h_AnnData

/-! ### U8 helpers: the model square as a disc, its frontier and corners -/

theorem u8h_isClosed_square (L : ℝ) : IsClosed (square L) :=
  isClosed_le u8h_continuous_supNorm continuous_const

theorem u8h_frontier_square (L : ℝ) : frontier (square L) = {x | supNorm x = L} := by
  ext x
  rw [(u8h_isClosed_square L).frontier_eq, mem_sdiff, u8h_mem_interior_square_iff]
  simp only [square, mem_setOf_eq, not_lt]
  constructor
  · rintro ⟨h1, h2⟩; exact le_antisymm h1 h2
  · intro h; exact ⟨h.le, h.ge⟩

theorem u8h_mem_frontier_square {L : ℝ} {x : Plane} : x ∈ frontier (square L) ↔ supNorm x = L := by
  rw [u8h_frontier_square]; rfl

/-- The four corners of `Q_L`, counterclockwise from `(L, -L)`. -/
def u8h_corner (L : ℝ) : Fin 4 → Plane := ![(L, -L), (L, L), (-L, L), (-L, -L)]

theorem u8h_supNorm_eq_of_abs {x : Plane} {L : ℝ} (h1 : |x.1| ≤ L) (h2 : |x.2| ≤ L)
    (h : |x.1| = L ∨ |x.2| = L) : supNorm x = L := by
  unfold supNorm
  rcases h with h | h
  · rw [max_eq_left (h ▸ h2), h]
  · rw [max_eq_right (h ▸ h1), h]

/-- A side of the square lies on its frontier. -/
theorem u8h_side_subset_frontier {L : ℝ} (hL : 0 < L) (j : Fin 4) :
    segment ℝ (u8h_corner L j) (u8h_corner L (j + 1)) ⊆ frontier (square L) := by
  intro x hx
  rw [u8h_mem_frontier_square]
  obtain ⟨s, t, hs, ht, hst, rfl⟩ := hx
  have hL' : |L| = L := abs_of_pos hL
  fin_cases j <;> simp only [u8h_corner, Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
    Fin.reduceAdd, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons] <;>
  · apply u8h_supNorm_eq_of_abs <;>
      simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;>
      first
      | (left; rw [show s * L + t * L = L by rw [← add_mul, hst, one_mul]]; exact hL')
      | (right; rw [show s * L + t * L = L by rw [← add_mul, hst, one_mul]]; exact hL')
      | (left; rw [show s * -L + t * -L = -L by rw [← add_mul, hst, one_mul]]; rw [abs_neg]; exact hL')
      | (right; rw [show s * -L + t * -L = -L by rw [← add_mul, hst, one_mul]]; rw [abs_neg]; exact hL')
      | (rw [abs_le]; constructor <;> nlinarith [abs_nonneg s, abs_nonneg t])


/-- A point of the frontier lies on one of the four sides. -/
theorem u8h_frontier_subset_sides {L : ℝ} (hL : 0 < L) {x : Plane} (hx : x ∈ frontier (square L)) :
    ∃ j : Fin 4, x ∈ segment ℝ (u8h_corner L j) (u8h_corner L (j + 1)) := by
  rw [u8h_mem_frontier_square] at hx
  have h1 : |x.1| ≤ L := hx ▸ le_max_left _ _
  have h2 : |x.2| ≤ L := hx ▸ le_max_right _ _
  rw [abs_le] at h1 h2
  have hL2 : (0 : ℝ) < 2 * L := by linarith
  rcases max_choice |x.1| |x.2| with h | h
  · have hx' : |x.1| = L := by rw [← h]; exact hx
    rcases abs_eq (hL.le) |>.1 hx' with h' | h'
    · -- right side, from (L, -L) to (L, L)
      refine ⟨0, (L - x.2) / (2 * L), (x.2 + L) / (2 * L), div_nonneg (by linarith) hL2.le,
        div_nonneg (by linarith) hL2.le, ?_, ?_⟩
      · field_simp; ring
      · show ((L - x.2) / (2 * L)) • ((L, -L) : Plane) + ((x.2 + L) / (2 * L)) • ((L, L) : Plane) = x
        ext <;> simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;>
          field_simp <;> ring_nf <;> linarith
    · -- left side, from (-L, L) to (-L, -L)
      refine ⟨2, (x.2 + L) / (2 * L), (L - x.2) / (2 * L), div_nonneg (by linarith) hL2.le,
        div_nonneg (by linarith) hL2.le, ?_, ?_⟩
      · field_simp; ring
      · show ((x.2 + L) / (2 * L)) • ((-L, L) : Plane) + ((L - x.2) / (2 * L)) • ((-L, -L) : Plane) = x
        ext <;> simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;>
          field_simp <;> ring_nf <;> linarith
  · have hx' : |x.2| = L := by rw [← h]; exact hx
    rcases abs_eq (hL.le) |>.1 hx' with h' | h'
    · -- top side, from (L, L) to (-L, L)
      refine ⟨1, (x.1 + L) / (2 * L), (L - x.1) / (2 * L), div_nonneg (by linarith) hL2.le,
        div_nonneg (by linarith) hL2.le, ?_, ?_⟩
      · field_simp; ring
      · show ((x.1 + L) / (2 * L)) • ((L, L) : Plane) + ((L - x.1) / (2 * L)) • ((-L, L) : Plane) = x
        ext <;> simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;>
          field_simp <;> ring_nf <;> linarith
    · -- bottom side, from (-L, -L) to (L, -L)
      refine ⟨3, (L - x.1) / (2 * L), (x.1 + L) / (2 * L), div_nonneg (by linarith) hL2.le,
        div_nonneg (by linarith) hL2.le, ?_, ?_⟩
      · field_simp; ring
      · show ((L - x.1) / (2 * L)) • ((-L, -L) : Plane) + ((x.1 + L) / (2 * L)) • ((L, -L) : Plane) = x
        ext <;> simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;>
          field_simp <;> ring_nf <;> linarith

theorem u8h_frontier_square_eq_sides {L : ℝ} (hL : 0 < L) :
    (⋃ j : Fin 4, segment ℝ (u8h_corner L j) (u8h_corner L (j + 1))) = frontier (square L) := by
  apply Subset.antisymm
  · exact iUnion_subset fun j => u8h_side_subset_frontier hL j
  · intro x hx
    obtain ⟨j, hj⟩ := u8h_frontier_subset_sides hL hx
    exact mem_iUnion.2 ⟨j, hj⟩


/-! ### U8 helpers: `det` algebra around a centre -/

/-- Expansion of `det V B` in the basis `A, M`. -/
theorem u8h_cramer_det {A M : Plane} (hAM : det A M ≠ 0) (V B : Plane) :
    det V B = (det V M / det A M) * det A B + (det A V / det A M) * det M B := by
  conv_lhs => rw [u8h_f_cramer hAM V]
  rw [u8h_f_det_comb_left]

/-- The `det` signs of a point of a segment seen from a centre. -/
theorem u8h_det_of_mem_segment {z p q y : Plane} (hy : y ∈ segment ℝ p q) (hpq : 0 ≤ det (p - z) (q - z)) :
    0 ≤ det (p - z) (y - z) ∧ 0 ≤ det (y - z) (q - z) := by
  obtain ⟨s, t, hs, ht, hst, rfl⟩ := hy
  have e : s • p + t • q - z = s • (p - z) + t • (q - z) := by
    have : z = s • z + t • z := by rw [← add_smul, hst, one_smul]
    conv_lhs => rw [this]
    rw [smul_sub, smul_sub]; abel
  rw [e, u8h_f_det_comb_right, u8h_f_det_comb_left, u8h_f_det_self, u8h_f_det_self]
  constructor
  · nlinarith
  · nlinarith

/-- Two frontier points on the same ray from an interior point coincide. -/
theorem u8h_eq_of_det_zero {D : Set Plane} (hD : Link.IsDisc D) {z : Plane} (hz : z ∈ interior D)
    {a a' : Plane} (ha : a ∈ frontier D) (ha' : a' ∈ frontier D) (h0 : det (a' - z) (a - z) = 0)
    {y : Plane} (hy : 0 < det (a - z) (y - z)) (hy' : 0 ≤ det (a' - z) (y - z)) : a' = a := by
  have hne : a' - z ≠ 0 := sub_ne_zero.2 (u8h_f_frontier_ne hD hz ha')
  obtain ⟨t, ht⟩ := u8h_f_parallel_of_det_eq_zero hne h0
  have htpos : 0 < t := by
    rw [ht, u8h_f_det_smul_left'] at hy
    by_contra hneg; push Not at hneg
    nlinarith
  have h1 : u8h_f_rg D z a = t * u8h_f_rg D z a' := by
    have : a = z + t • (a' - z) := by rw [← ht]; abel
    rw [this, u8h_f_rg_smul _ _ _ htpos.le]
  rw [(u8h_f_rg_eq_one_iff hD hz a).2 ha, (u8h_f_rg_eq_one_iff hD hz a').2 ha', mul_one] at h1
  rw [← h1, one_smul] at ht
  exact (sub_left_inj.1 ht).symm

/-- The sign of `det (a - z) (b - z)` is the same for all interior points `z` (for a frontier piece
`[a, b]`). -/
theorem u8h_det_sign_const {D : Set Plane} (hD : Link.IsDisc D) {z z' : Plane} (hz : z ∈ interior D)
    (hz' : z' ∈ interior D) {a b : Plane} (hne : a ≠ b) (hseg : segment ℝ a b ⊆ frontier D)
    (hpos : 0 < det (a - z) (b - z)) : 0 < det (a - z') (b - z') := by
  have hne' := u8h_f_det_ne_zero_of_segment hD hz' hne hseg
  rcases lt_or_gt_of_ne hne' with hneg | hpos'
  · exfalso
    set f : Plane → ℝ := fun w => det (a - w) (b - w) with hf
    have haff : ∀ w w' : Plane, ∀ t : ℝ, f (w + t • (w' - w)) = f w + t * (f w' - f w) := by
      intro w w' t
      simp only [hf, det, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst,
        Prod.smul_snd, smul_eq_mul]; ring
    have hfz : 0 < f z := hpos
    have hfz' : f z' < 0 := hneg
    set t := f z / (f z - f z') with ht
    have hden : 0 < f z - f z' := by linarith
    have ht0 : 0 ≤ t := div_nonneg hfz.le hden.le
    have ht1 : t ≤ 1 := by rw [ht, div_le_one hden]; linarith
    have hw : z + t • (z' - z) ∈ interior D :=
      (Convex.interior hD.1) hz hz' (by linarith : 0 ≤ 1 - t) ht0 (by ring) |> fun h => by
        convert h using 1; rw [smul_sub]; module
    have h0 : f (z + t • (z' - z)) = 0 := by
      rw [haff, ht]; field_simp; ring
    exact u8h_f_det_ne_zero_of_segment hD hw hne hseg h0
  · exact hpos'

/-- The inner projection of the outer projection of an inner frontier point is the point. -/
theorem u8h_AnnCtx.rayin_rayout {z : Plane} {Din Dout : Set Plane} (C : u8h_AnnCtx z Din Dout) {v : Plane}
    (hv : v ∈ frontier Din) : u8h_f_ray Din z (u8h_f_ray Dout z v) = v := by
  have hvz : v ≠ z := u8h_f_frontier_ne C.hin C.hz hv
  have hr : 0 < u8h_f_rg Dout z v := u8h_f_rg_pos C.hout C.hz' hvz
  have e : u8h_f_ray Dout z v = z + (u8h_f_rg Dout z v)⁻¹ • (v - z) := rfl
  rw [u8h_f_ray, e, u8h_f_rg_smul _ _ _ (inv_pos.2 hr).le, (u8h_f_rg_eq_one_iff C.hin C.hz v).2 hv, mul_one,
    inv_inv, add_sub_cancel_left, smul_smul, mul_inv_cancel₀ hr.ne', one_smul, add_sub_cancel]


/-! ### U8 helpers: the seam reflection `ρ_L x = (x₁ / L, -x₂ / L)` -/

/-- The affine seam map: `capInvFun L` restricted to `∂Q_L`, extended linearly. -/
noncomputable def u8h_ρ (L : ℝ) (x : Plane) : Plane := (x.1 / L, -x.2 / L)

theorem u8h_ρ_smul (L c : ℝ) (x : Plane) : u8h_ρ L (c • x) = c • u8h_ρ L x := by
  ext <;> simp [u8h_ρ] <;> ring

theorem u8h_ρ_add (L : ℝ) (x y : Plane) : u8h_ρ L (x + y) = u8h_ρ L x + u8h_ρ L y := by
  ext <;> simp [u8h_ρ] <;> ring

theorem u8h_ρ_sub (L : ℝ) (x y : Plane) : u8h_ρ L (x - y) = u8h_ρ L x - u8h_ρ L y := by
  ext <;> simp [u8h_ρ] <;> ring

theorem u8h_ρ_zero (L : ℝ) : u8h_ρ L 0 = 0 := by ext <;> simp [u8h_ρ]

theorem u8h_det_ρ (L : ℝ) (x y : Plane) : det (u8h_ρ L x) (u8h_ρ L y) = -(det x y / L ^ 2) := by
  simp only [u8h_ρ, det]; ring

theorem u8h_supNorm_ρ {L : ℝ} (hL : 0 < L) (x : Plane) : supNorm (u8h_ρ L x) = supNorm x / L := by
  simp only [u8h_ρ, supNorm, abs_div, abs_neg, abs_of_pos hL]
  rcases le_total |x.1| |x.2| with h | h
  · rw [max_eq_right h, max_eq_right (div_le_div_of_nonneg_right h hL.le)]
  · rw [max_eq_left h, max_eq_left (div_le_div_of_nonneg_right h hL.le)]

theorem u8h_ρ_injective {L : ℝ} (hL : 0 < L) : Function.Injective (u8h_ρ L) := by
  intro x y h
  simp only [u8h_ρ, Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  rw [div_left_inj' hL.ne'] at h1 h2
  exact Prod.ext h1 (neg_inj.1 h2)

theorem u8h_ρ_ρ (L : ℝ) (x : Plane) : u8h_ρ L (u8h_ρ L x) = (L ^ 2)⁻¹ • x := by
  ext <;> simp [u8h_ρ] <;> ring

theorem u8h_ρ_mem_segment {L : ℝ} (hL : 0 < L) {a b y : Plane} :
    u8h_ρ L y ∈ segment ℝ (u8h_ρ L a) (u8h_ρ L b) ↔ y ∈ segment ℝ a b := by
  constructor
  · rintro ⟨s, t, hs, ht, hst, h⟩
    refine ⟨s, t, hs, ht, hst, u8h_ρ_injective hL ?_⟩
    rw [u8h_ρ_add, u8h_ρ_smul, u8h_ρ_smul, h]
  · rintro ⟨s, t, hs, ht, hst, rfl⟩
    exact ⟨s, t, hs, ht, hst, by rw [u8h_ρ_add, u8h_ρ_smul, u8h_ρ_smul]⟩

theorem u8h_ρ_mem_openSegment {L : ℝ} (hL : 0 < L) {a b y : Plane} :
    u8h_ρ L y ∈ openSegment ℝ (u8h_ρ L a) (u8h_ρ L b) ↔ y ∈ openSegment ℝ a b := by
  constructor
  · rintro ⟨s, t, hs, ht, hst, h⟩
    refine ⟨s, t, hs, ht, hst, u8h_ρ_injective hL ?_⟩
    rw [u8h_ρ_add, u8h_ρ_smul, u8h_ρ_smul, h]
  · rintro ⟨s, t, hs, ht, hst, rfl⟩
    exact ⟨s, t, hs, ht, hst, by rw [u8h_ρ_add, u8h_ρ_smul, u8h_ρ_smul]⟩

theorem u8h_ρ_image_segment {L : ℝ} (hL : 0 < L) (a b : Plane) :
    u8h_ρ L '' segment ℝ a b = segment ℝ (u8h_ρ L a) (u8h_ρ L b) := by
  ext y; constructor
  · rintro ⟨x, hx, rfl⟩; exact (u8h_ρ_mem_segment hL).2 hx
  · intro hy
    refine ⟨(L ^ 2) • u8h_ρ L y, ?_, ?_⟩
    · rw [← u8h_ρ_mem_segment hL, u8h_ρ_smul, u8h_ρ_ρ, smul_smul, mul_inv_cancel₀ (pow_ne_zero 2 hL.ne'),
        one_smul]; exact hy
    · rw [u8h_ρ_smul, u8h_ρ_ρ, smul_smul, mul_inv_cancel₀ (pow_ne_zero 2 hL.ne'), one_smul]

/-- On the seam the cap inverse is `ρ`. -/
theorem u8h_capInvFun_eq_ρ {L : ℝ} (hL : 0 < L) {x : Plane} (hx : supNorm x = L) :
    capInvFun L x = u8h_ρ L x := by
  simp only [capInvFun, u8h_ρ, hx]
  ext <;> simp <;> field_simp <;> ring

/-! ### U8 helpers: the remaining piece of the fan toolkit (`u10h_cover`, copied) -/

theorem u8h_f_ray_continuousAt {D : Set Plane} (hD : Link.IsDisc D) {z : Plane} (hz : z ∈ interior D)
    {x : Plane} (hx : x ≠ z) : ContinuousAt (u8h_f_ray D z) x := by
  have : u8h_f_ray D z = fun x => z + (u8h_f_rg D z x)⁻¹ • (x - z) := rfl
  rw [this]
  exact continuousAt_const.add
    ((((u8h_f_rg_continuous hD hz).continuousAt).inv₀ (u8h_f_rg_pos hD hz hx).ne').smul
      (continuousAt_id.sub continuousAt_const))

theorem u8h_f_not_isolated {D : Set Plane} (hD : Link.IsDisc D) {z : Plane} (hz : z ∈ interior D)
    {y : Plane} (hy : y ∈ frontier D) {ε : ℝ} (hε : 0 < ε) :
    ∃ w ∈ frontier D, w ≠ y ∧ dist w y < ε := by
  have hyz := u8h_f_frontier_ne hD hz hy
  have hu : y - z ≠ 0 := sub_ne_zero.mpr hyz
  set v : Plane := (-(y - z).2, (y - z).1) with hv
  have hdet : 0 < det (y - z) v := by
    have : det (y - z) v = (y - z).1 ^ 2 + (y - z).2 ^ 2 := by simp only [det, hv]; ring
    rw [this]
    rcases not_and_or.mp (fun hc : (y - z).1 = 0 ∧ (y - z).2 = 0 => hu (Prod.ext hc.1 hc.2)) with h1 | h2 <;>
      positivity
  set g : ℝ → Plane := fun t => u8h_f_ray D z (y + t • v) with hg
  have hg0 : g 0 = y := by simp [hg, u8h_f_ray_of_frontier hD hz hy]
  have hgc : ContinuousAt g 0 := by
    have h1 : ContinuousAt (fun t : ℝ => y + t • v) 0 := continuousAt_const.add (continuousAt_id.smul continuousAt_const)
    have h2 : ContinuousAt (u8h_f_ray D z) (y + (0:ℝ) • v) := by
      rw [zero_smul, add_zero]; exact u8h_f_ray_continuousAt hD hz hyz
    exact ContinuousAt.comp (f := fun t : ℝ => y + t • v) h2 h1
  obtain ⟨δ, hδ, hδε⟩ := Metric.continuousAt_iff.mp hgc ε hε
  have hpt : y + (δ / 2) • v ≠ z := by
    intro h
    have : det (y - z) (y + (δ / 2) • v - z) = 0 := by rw [h, sub_self, u8h_f_det_zero_right]
    rw [add_sub_right_comm, u8h_f_det_add_right, u8h_f_det_self, u8h_f_det_smul_right] at this
    have : 0 < δ / 2 * det (y - z) v := by positivity
    linarith
  refine ⟨g (δ / 2), u8h_f_ray_mem_frontier hD hz hpt, ?_, ?_⟩
  · intro h
    have h1 : det (y - z) (g (δ / 2) - z) = 0 := by rw [h, u8h_f_det_self]
    have h2 : g (δ / 2) - z = (u8h_f_rg D z (y + (δ / 2) • v))⁻¹ • ((δ / 2) • v + (y - z)) := by
      simp only [hg, u8h_f_ray, add_sub_cancel_left]; congr 1; abel
    rw [h2, u8h_f_det_smul_right, u8h_f_det_add_right, u8h_f_det_smul_right, u8h_f_det_self, add_zero] at h1
    have hr := u8h_f_rg_pos hD hz hpt
    have : 0 < (u8h_f_rg D z (y + (δ / 2) • v))⁻¹ * (δ / 2 * det (y - z) v) := by positivity
    linarith
  · have := hδε (x := δ / 2) (by rw [Real.dist_eq, sub_zero, abs_of_pos (by positivity)]; linarith)
    rwa [hg0] at this

theorem u8h_f_isClosed_segment (a b : Plane) : IsClosed (segment ℝ a b) := by
  rw [segment_eq_image']
  exact (isCompact_Icc.image (by fun_prop)).isClosed

theorem u8h_f_exists_nondeg {D : Set Plane} (hD : Link.IsDisc D) {z : Plane} (hz : z ∈ interior D)
    {S : Finset (Plane × Plane)} (hS : (⋃ p ∈ S, segment ℝ p.1 p.2) = frontier D) {y : Plane}
    (hy : y ∈ frontier D) : ∃ p ∈ S, p.1 ≠ p.2 ∧ y ∈ segment ℝ p.1 p.2 := by
  classical
  by_contra hcon
  have hdeg : ∀ p ∈ S, y ∈ segment ℝ p.1 p.2 → p.1 = p.2 := fun p hp hyp =>
    by_contra fun hne => hcon ⟨p, hp, hne, hyp⟩
  set U : Set Plane := ⋃ p ∈ S.filter (fun p => y ∉ segment ℝ p.1 p.2), segment ℝ p.1 p.2 with hU
  have hUc : IsClosed U := isClosed_biUnion_finset (fun p _ => u8h_f_isClosed_segment _ _)
  have hyU : y ∉ U := by
    intro h
    rw [hU, mem_iUnion₂] at h
    obtain ⟨p, hp, hyp⟩ := h
    exact (Finset.mem_filter.mp hp).2 hyp
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hUc.isOpen_compl y hyU
  obtain ⟨w, hw, hwy, hwd⟩ := u8h_f_not_isolated hD hz hy hε
  rw [← hS, mem_iUnion₂] at hw
  obtain ⟨p, hp, hwp⟩ := hw
  by_cases hyp : y ∈ segment ℝ p.1 p.2
  · have h12 := hdeg p hp hyp
    rw [h12, segment_same] at hyp hwp
    exact hwy (hwp.trans hyp.symm)
  · have hwU : w ∈ U := by
      rw [hU, mem_iUnion₂]
      exact ⟨p, Finset.mem_filter.mpr ⟨hp, hyp⟩, hwp⟩
    exact hball (Metric.mem_ball.mpr hwd) hwU

/-! ### coverage, a third mark, positivity from the cyclic order -/

theorem u8h_f_cover {D : Set Plane} (hD : Link.IsDisc D) {z : Plane} (hz : z ∈ interior D)
    {S : Finset (Plane × Plane)} (hS : (⋃ p ∈ S, segment ℝ p.1 p.2) = frontier D) {y : Plane}
    (hy : y ∈ frontier D) : ∃ a b, u8h_f_A D z S a b ∧ y ∈ segment ℝ a b := by
  obtain ⟨p, hp, hne, hyp⟩ := u8h_f_exists_nondeg hD hz hS hy
  exact u8h_f_cover_of_segment hD hz hS hp hne hyp


/-- The gauge of the square `Q_r` about the origin is `‖x‖_∞ / r`. -/
theorem u8h_rg_square {r : ℝ} (hr : 0 < r) (x : Plane) : u8h_f_rg (square r) 0 x = supNorm x / r := by
  have hD := U1_square_isDisc hr
  have h0 : (0 : Plane) ∈ interior (square r) := by
    rw [u8h_mem_interior_square_iff]; simp [supNorm, hr]
  by_cases hx : x = 0
  · subst hx; rw [u8h_f_rg_self]; simp [supNorm]
  · have hN := u3h_supNorm_pos hx
    set y : Plane := (r / supNorm x) • x with hy
    have hyfr : y ∈ frontier (square r) := by
      rw [u8h_mem_frontier_square, hy, u3h_supNorm_smul, abs_of_pos (div_pos hr hN), div_mul_cancel₀ _ hN.ne']
    have hc : supNorm x / r * (r / supNorm x) = 1 := by field_simp
    have e : x = 0 + (supNorm x / r) • (y - 0) := by
      rw [hy, sub_zero, zero_add, smul_smul, hc, one_smul]
    conv_lhs => rw [e]
    rw [u8h_f_rg_smul _ _ _ (div_pos hN hr).le, (u8h_f_rg_eq_one_iff hD h0 y).2 hyfr, mul_one]

theorem u8h_zero_mem_interior_square {r : ℝ} (hr : 0 < r) : (0 : Plane) ∈ interior (square r) := by
  rw [u8h_mem_interior_square_iff]; simp [supNorm, hr]

/-! ### U8: the source annulus `Q_L \ int T₀` -/

/-- A fixed interior point of the base triangle. -/
noncomputable def u8h_o (T₀ : Triangle) : Plane := Classical.choose (U1_triangle_interior_nonempty T₀)

theorem u8h_o_mem (T₀ : Triangle) : u8h_o T₀ ∈ interior T₀.carrier :=
  Classical.choose_spec (U1_triangle_interior_nonempty T₀)

/-- The nested-disc context of the source annulus. -/
theorem u8h_ctx {L : ℝ} (hL : 0 < L) (T₀ : Triangle) (hT : T₀.carrier ⊆ interior (square L)) :
    u8h_AnnCtx (u8h_o T₀) T₀.carrier (square L) :=
  ⟨U1_triangle_isDisc T₀, U1_square_isDisc hL, u8h_o_mem T₀, hT⟩

theorem u8h_vertex_mem_frontier (T₀ : Triangle) (i : Fin 3) : T₀.v i ∈ frontier T₀.carrier := by
  rw [U1_frontier_triangle]
  exact mem_iUnion.2 ⟨i, left_mem_segment ℝ _ _⟩

theorem u8h_vertex_ne_o (T₀ : Triangle) (i : Fin 3) : T₀.v i ≠ u8h_o T₀ := fun h =>
  (u8h_vertex_mem_frontier T₀ i).2 (h ▸ u8h_o_mem T₀)

/-- The outer radial projections of the vertices of `T₀`. -/
noncomputable def u8h_q (L : ℝ) (T₀ : Triangle) (i : Fin 3) : Plane :=
  u8h_f_ray (square L) (u8h_o T₀) (T₀.v i)

theorem u8h_q_mem_frontier {L : ℝ} (hL : 0 < L) (T₀ : Triangle) (hT : T₀.carrier ⊆ interior (square L))
    (i : Fin 3) : u8h_q L T₀ i ∈ frontier (square L) :=
  u8h_f_ray_mem_frontier (U1_square_isDisc hL) (u8h_ctx hL T₀ hT).hz' (u8h_vertex_ne_o T₀ i)

/-- The inner projection of `q i` is the vertex `v i`. -/
theorem u8h_ray_q {L : ℝ} (hL : 0 < L) (T₀ : Triangle) (hT : T₀.carrier ⊆ interior (square L)) (i : Fin 3) :
    u8h_f_ray T₀.carrier (u8h_o T₀) (u8h_q L T₀ i) = T₀.v i :=
  (u8h_ctx hL T₀ hT).rayin_rayout (u8h_vertex_mem_frontier T₀ i)

open Classical in
/-- The frontier pieces of the source: the four sides and the three vertex projections as
degenerate pieces (so that they are marks). -/
noncomputable def u8h_S (L : ℝ) (T₀ : Triangle) : Finset (Plane × Plane) :=
  Finset.univ.image (fun j : Fin 4 => (u8h_corner L j, u8h_corner L (j + 1))) ∪
    Finset.univ.image (fun i : Fin 3 => (u8h_q L T₀ i, u8h_q L T₀ i))

theorem u8h_S_cover {L : ℝ} (hL : 0 < L) (T₀ : Triangle) (hT : T₀.carrier ⊆ interior (square L)) :
    (⋃ p ∈ u8h_S L T₀, segment ℝ p.1 p.2) = frontier (square L) := by
  apply Subset.antisymm
  · intro x hx
    obtain ⟨p, hp, hxp⟩ := mem_iUnion₂.1 hx
    rcases Finset.mem_union.1 hp with hp | hp
    · obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hp
      exact u8h_side_subset_frontier hL j hxp
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hp
      rw [segment_same] at hxp
      rw [mem_singleton_iff] at hxp
      rw [hxp]; exact u8h_q_mem_frontier hL T₀ hT i
  · intro x hx
    obtain ⟨j, hj⟩ := u8h_frontier_subset_sides hL hx
    exact mem_iUnion₂.2 ⟨(u8h_corner L j, u8h_corner L (j + 1)),
      Finset.mem_union.2 (Or.inl (Finset.mem_image.2 ⟨j, Finset.mem_univ _, rfl⟩)), hj⟩

/-- The outer marks and the adjacency relation of the source fan. -/
noncomputable def u8h_V (L : ℝ) (T₀ : Triangle) : Set Plane := u8h_f_marks (u8h_S L T₀)
def u8h_A (L : ℝ) (T₀ : Triangle) (a b : Plane) : Prop := u8h_f_A (square L) (u8h_o T₀) (u8h_S L T₀) a b

theorem u8h_q_mem_V (L : ℝ) (T₀ : Triangle) (i : Fin 3) : u8h_q L T₀ i ∈ u8h_V L T₀ :=
  u8h_f_marks_left (Finset.mem_union.2 (Or.inr (Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩)))

theorem u8h_V_finite (L : ℝ) (T₀ : Triangle) : (u8h_V L T₀).Finite := u8h_f_marks_finite _

theorem u8h_V_subset {L : ℝ} (hL : 0 < L) (T₀ : Triangle) (hT : T₀.carrier ⊆ interior (square L)) :
    u8h_V L T₀ ⊆ frontier (square L) := u8h_f_marks_subset_frontier (u8h_S_cover hL T₀ hT)

theorem u8h_A_adj (L : ℝ) (T₀ : Triangle) (a b : Plane) (h : u8h_A L T₀ a b) :
    u8h_f_Adj (square L) (u8h_o T₀) (u8h_V L T₀) a b := h.1

theorem u8h_A_cover {L : ℝ} (hL : 0 < L) (T₀ : Triangle) (hT : T₀.carrier ⊆ interior (square L)) :
    ∀ y ∈ frontier (square L), ∃ a b, u8h_A L T₀ a b ∧ y ∈ segment ℝ a b := fun y hy =>
  u8h_f_cover (U1_square_isDisc hL) (u8h_ctx hL T₀ hT).hz' (u8h_S_cover hL T₀ hT) hy

/-- The source annulus data, given straightness of the inner frontier between adjacent marks. -/
theorem u8h_srcData {L : ℝ} (hL : 0 < L) (T₀ : Triangle) (hT : T₀.carrier ⊆ interior (square L))
    (hstraight : ∀ a b, u8h_A L T₀ a b →
      segment ℝ (u8h_f_ray T₀.carrier (u8h_o T₀) a) (u8h_f_ray T₀.carrier (u8h_o T₀) b) ⊆ frontier T₀.carrier) :
    u8h_AnnData (u8h_o T₀) T₀.carrier (square L) (u8h_V L T₀) (u8h_A L T₀) :=
  ⟨u8h_ctx hL T₀ hT, u8h_V_finite L T₀, u8h_V_subset hL T₀ hT, u8h_A_adj L T₀, u8h_A_cover hL T₀ hT, hstraight⟩

/-! ### U8 helpers: the face-wise affine map glued from a vertex assignment -/

/-- Two affine maps of the plane agreeing on a set agree on its convex hull. -/
theorem u8h_affine_eq_on_hull {f g : Plane → Plane} (hf : AffineOn f univ) (hg : AffineOn g univ)
    {S : Set Plane} (h : ∀ v ∈ S, f v = g v) : ∀ x ∈ convexHull ℝ S, f x = g x := by
  obtain ⟨M, b, hM⟩ := hf
  obtain ⟨M', b', hM'⟩ := hg
  have hconv : Convex ℝ {x | f x = g x} := by
    intro x hx y hy s t hs ht hst
    simp only [mem_setOf_eq] at hx hy ⊢
    rw [hM _ (mem_univ _), hM' _ (mem_univ _)] at hx hy ⊢
    rw [map_add, map_smul, map_smul, map_add, map_smul, map_smul]
    have ht' : t = 1 - s := by linarith
    subst ht'
    have e1 : s • M x + (1 - s) • M y + b = s • (M x + b) + (1 - s) • (M y + b) := by module
    have e2 : s • M' x + (1 - s) • M' y + b' = s • (M' x + b') + (1 - s) • (M' y + b') := by module
    rw [e1, e2, hx, hy]
  exact fun x hx => convexHull_min h hconv hx

/-- The affine map of the plane taking the vertices of `T` to their `w`-values. -/
noncomputable def u8h_aff (T : Triangle) (w : Plane → Plane) : Plane → Plane :=
  Classical.choose (U1_exists_affine_of_triangle T (w ∘ T.v))

theorem u8h_aff_affine (T : Triangle) (w : Plane → Plane) : AffineOn (u8h_aff T w) univ :=
  (Classical.choose_spec (U1_exists_affine_of_triangle T (w ∘ T.v))).1

theorem u8h_aff_vertex (T : Triangle) (w : Plane → Plane) (i : Fin 3) : u8h_aff T w (T.v i) = w (T.v i) :=
  (Classical.choose_spec (U1_exists_affine_of_triangle T (w ∘ T.v))).2 i

open Classical in
/-- The glued map: on each face of `K` the affine map of that face. -/
noncomputable def u8h_glue {X : Set Plane} (K : Triangulation X) (w : Plane → Plane) (x : Plane) : Plane :=
  if h : ∃ T, T ∈ K.faces ∧ x ∈ T.carrier then u8h_aff (Classical.choose h) w x else 0

/-- Two face maps agree on the intersection of their faces. -/
theorem u8h_aff_eq_of_inter {X : Set Plane} (K : Triangulation X) (w : Plane → Plane) {T T' : Triangle}
    (hT : T ∈ K.faces) (hT' : T' ∈ K.faces) {x : Plane} (hx : x ∈ T.carrier) (hx' : x ∈ T'.carrier) :
    u8h_aff T w x = u8h_aff T' w x := by
  have hmem : x ∈ convexHull ℝ (range T.v ∩ range T'.v) := by rw [← K.inter T hT T' hT']; exact ⟨hx, hx'⟩
  refine u8h_affine_eq_on_hull (u8h_aff_affine T w) (u8h_aff_affine T' w) ?_ x hmem
  rintro v ⟨⟨i, rfl⟩, ⟨j, hj⟩⟩
  rw [u8h_aff_vertex, ← hj, u8h_aff_vertex, hj]

theorem u8h_glue_eq {X : Set Plane} (K : Triangulation X) (w : Plane → Plane) {T : Triangle}
    (hT : T ∈ K.faces) {x : Plane} (hx : x ∈ T.carrier) : u8h_glue K w x = u8h_aff T w x := by
  have h : ∃ T, T ∈ K.faces ∧ x ∈ T.carrier := ⟨T, hT, hx⟩
  rw [u8h_glue, dif_pos h]
  have hs := Classical.choose_spec h
  exact u8h_aff_eq_of_inter K w hs.1 hT hs.2 hx

theorem u8h_glue_vertex {X : Set Plane} (K : Triangulation X) (w : Plane → Plane) {T : Triangle}
    (hT : T ∈ K.faces) (i : Fin 3) : u8h_glue K w (T.v i) = w (T.v i) := by
  rw [u8h_glue_eq K w hT (subset_convexHull ℝ _ (mem_range_self i)), u8h_aff_vertex]

/-- The glued map is positive PL when the vertex images are positively oriented on every face. -/
theorem u8h_glue_isPositivePLOn {X : Set Plane} (K : Triangulation X) (w : Plane → Plane)
    (hpos : ∀ T ∈ K.faces, 0 < det (w (T.v 1) - w (T.v 0)) (w (T.v 2) - w (T.v 0))) :
    IsPositivePLOn (u8h_glue K w) K := by
  intro T hT
  have haff : IsPositiveAffineOn (u8h_aff T w) T := by
    refine U1_isPositiveAffineOn_of_det T (u8h_aff_affine T w) ?_
    rw [u8h_aff_vertex, u8h_aff_vertex, u8h_aff_vertex]; exact hpos T hT
  exact u3h_isPositiveAffineOn_congr (fun x hx => (u8h_glue_eq K w hT hx).symm) haff

/-- A positive affine map is injective on its face. -/
theorem u8h_injOn_of_isPositiveAffineOn {f : Plane → Plane} {T : Triangle} (h : IsPositiveAffineOn f T) :
    InjOn f T.carrier := by
  obtain ⟨M, c, hMc⟩ := id h.1
  have hdet := u3h_detM_pos T h hMc
  obtain ⟨N, hN⟩ := u3h_exists_linear_inverse M hdet.ne'
  intro x hx y hy hxy
  rw [hMc x hx, hMc y hy] at hxy
  have : M x = M y := add_right_cancel hxy
  rw [← hN x, this, hN]

/-- The image of a face under a face-wise affine map is the face of the vertex images. -/
theorem u8h_image_face {f : Plane → Plane} {T : Triangle} (h : IsPositiveAffineOn f T) :
    f '' T.carrier = convexHull ℝ (f '' range T.v) :=
  u2h_image_convexHull_of_affineOn h.1 (U1_triangle_convex T) (subset_convexHull ℝ _)

/-- **Bijection lemma**: a face-wise positive affine map carrying faces of `K` onto faces of `K'`,
surjectively on faces and injectively on vertices, is a bijection of the carriers. -/
theorem u8h_bij_of_faces {X X' : Set Plane} (K : Triangulation X) (K' : Triangulation X') {g : Plane → Plane}
    (hg : IsPositivePLOn g K)
    (himg : ∀ T ∈ K.faces, ∃ T' ∈ K'.faces, g '' T.carrier = T'.carrier)
    (hsurj : ∀ T' ∈ K'.faces, ∃ T ∈ K.faces, g '' T.carrier = T'.carrier)
    (hvinj : ∀ T ∈ K.faces, ∀ T' ∈ K.faces, ∀ i j, g (T.v i) = g (T'.v j) → T.v i = T'.v j) :
    InjOn g X ∧ g '' X = X' := by
  have hmemX : ∀ x ∈ X, ∃ T ∈ K.faces, x ∈ T.carrier := by
    intro x hx; rw [← K.cover] at hx
    obtain ⟨T, hT, hxT⟩ := mem_iUnion₂.1 hx
    exact ⟨T, hT, hxT⟩
  have hsubX' : ∀ T' ∈ K'.faces, T'.carrier ⊆ X' := by
    intro T' hT'
    have := subset_biUnion_of_mem (u := fun T : Triangle => T.carrier) hT'
    rwa [K'.cover] at this
  have hsubX : ∀ T ∈ K.faces, T.carrier ⊆ X := by
    intro T hT
    have := subset_biUnion_of_mem (u := fun T : Triangle => T.carrier) hT
    rwa [K.cover] at this
  constructor
  · intro x hx y hy hxy
    obtain ⟨T, hT, hxT⟩ := hmemX x hx
    obtain ⟨T₂, hT₂, hyT⟩ := hmemX y hy
    obtain ⟨T', hT', hTT'⟩ := himg T hT
    obtain ⟨T₂', hT₂', hTT₂'⟩ := himg T₂ hT₂
    have hp : g x ∈ T'.carrier ∩ T₂'.carrier := ⟨hTT' ▸ ⟨x, hxT, rfl⟩, hTT₂' ▸ ⟨y, hyT, hxy.symm⟩⟩
    rw [K'.inter T' hT' T₂' hT₂'] at hp
    -- the vertex sets of the image faces are the images of the vertex sets
    have hr : ∀ {S S' : Triangle}, S ∈ K.faces → g '' S.carrier = S'.carrier →
        range S'.v = g '' range S.v := by
      intro S S' hS hSS'
      have e : (S.map g (hg S hS)).carrier = S'.carrier := by rw [← u3h_image_carrier S (hg S hS), hSS']
      rw [← u3h_range_eq_of_carrier_eq e]
      exact range_comp g S.v
    rw [hr hT hTT', hr hT₂ hTT₂'] at hp
    have hint : g '' range T.v ∩ g '' range T₂.v = g '' (range T.v ∩ range T₂.v) := by
      apply Subset.antisymm
      · rintro p ⟨⟨u, ⟨i, rfl⟩, rfl⟩, ⟨v, ⟨j, rfl⟩, huv⟩⟩
        have := hvinj T hT T₂ hT₂ i j huv.symm
        exact ⟨T.v i, ⟨⟨i, rfl⟩, ⟨j, this.symm⟩⟩, rfl⟩
      · exact Set.image_inter_subset g _ _
    rw [hint] at hp
    have hS : range T.v ∩ range T₂.v ⊆ T.carrier := inter_subset_left.trans (subset_convexHull ℝ _)
    rw [← u2h_image_convexHull_of_affineOn (hg T hT).1 (U1_triangle_convex T) hS,
      ← K.inter T hT T₂ hT₂] at hp
    obtain ⟨u, ⟨huT, huT₂⟩, hu⟩ := hp
    have h1 : x = u := u8h_injOn_of_isPositiveAffineOn (hg T hT) hxT huT hu.symm
    have h2 : y = u := u8h_injOn_of_isPositiveAffineOn (hg T₂ hT₂) hyT huT₂ (hxy.symm.trans hu.symm)
    rw [h1, h2]
  · apply Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      obtain ⟨T, hT, hxT⟩ := hmemX x hx
      obtain ⟨T', hT', hTT'⟩ := himg T hT
      exact hsubX' T' hT' (hTT' ▸ ⟨x, hxT, rfl⟩)
    · intro x' hx'
      rw [← K'.cover] at hx'
      obtain ⟨T', hT', hx'T⟩ := mem_iUnion₂.1 hx'
      obtain ⟨T, hT, hTT'⟩ := hsurj T' hT'
      rw [← hTT'] at hx'T
      obtain ⟨x, hxT, rfl⟩ := hx'T
      exact ⟨x, hsubX T hT hxT, rfl⟩


/-! ### U8: the target annulus `Q_2 \ int Q_1` with the reflected marks -/

/-- The target marks `ρ_{L/2}(V) = 2 ρ_L (V) ⊆ ∂Q_2`. -/
noncomputable def u8h_V' (L : ℝ) (T₀ : Triangle) : Set Plane := u8h_ρ (L / 2) '' u8h_V L T₀

/-- The target adjacency: the reflected source adjacency, with the order reversed. -/
def u8h_A' (L : ℝ) (T₀ : Triangle) (a' b' : Plane) : Prop :=
  ∃ a b, u8h_A L T₀ a b ∧ a' = u8h_ρ (L / 2) b ∧ b' = u8h_ρ (L / 2) a

theorem u8h_half_pos {L : ℝ} (hL : 0 < L) : 0 < L / 2 := by linarith

theorem u8h_ctx' : u8h_AnnCtx (0 : Plane) (square 1) (square 2) :=
  ⟨U1_square_isDisc one_pos, U1_square_isDisc two_pos, u8h_zero_mem_interior_square one_pos, fun x hx => by
    rw [u8h_mem_interior_square_iff]; have : supNorm x ≤ 1 := hx; linarith⟩

theorem u8h_supNorm_ρ' {L : ℝ} (hL : 0 < L) {c : Plane} (hc : c ∈ frontier (square L)) :
    supNorm (u8h_ρ (L / 2) c) = 2 := by
  rw [u8h_supNorm_ρ (u8h_half_pos hL), u8h_mem_frontier_square.1 hc]; field_simp

theorem u8h_ρ'_mem_frontier {L : ℝ} (hL : 0 < L) {c : Plane} (hc : c ∈ frontier (square L)) :
    u8h_ρ (L / 2) c ∈ frontier (square 2) := by
  rw [u8h_mem_frontier_square]; exact u8h_supNorm_ρ' hL hc

theorem u8h_ρ_mem_frontier_one {L : ℝ} (hL : 0 < L) {c : Plane} (hc : c ∈ frontier (square L)) :
    u8h_ρ L c ∈ frontier (square 1) := by
  rw [u8h_mem_frontier_square, u8h_supNorm_ρ hL, u8h_mem_frontier_square.1 hc, div_self hL.ne']

/-- The inner projection of a target mark `ρ_{L/2} c` is `ρ_L c`. -/
theorem u8h_ray_ρ' {L : ℝ} (hL : 0 < L) {c : Plane} (hc : c ∈ frontier (square L)) :
    u8h_f_ray (square 1) 0 (u8h_ρ (L / 2) c) = u8h_ρ L c := by
  rw [u8h_f_ray, u8h_rg_square one_pos, u8h_supNorm_ρ' hL hc, div_one, sub_zero, zero_add]
  ext <;> simp [u8h_ρ] <;> field_simp <;> ring

theorem u8h_V'_subset {L : ℝ} (hL : 0 < L) (T₀ : Triangle) (hT : T₀.carrier ⊆ interior (square L)) :
    u8h_V' L T₀ ⊆ frontier (square 2) := by
  rintro _ ⟨c, hc, rfl⟩
  exact u8h_ρ'_mem_frontier hL (u8h_V_subset hL T₀ hT hc)

/-- `det a b > 0` about the origin for adjacent source marks. -/
theorem u8h_det_origin_pos {L : ℝ} (hL : 0 < L) (T₀ : Triangle) (hT : T₀.carrier ⊆ interior (square L))
    {a b : Plane} (h : u8h_A L T₀ a b) : 0 < det a b := by
  have hadj := u8h_A_adj L T₀ a b h
  have hne : a ≠ b := fun e => by
    have := hadj.2.2.1; rw [e, u8h_f_det_self] at this; exact lt_irrefl _ this
  have := u8h_det_sign_const (U1_square_isDisc hL) (u8h_ctx hL T₀ hT).hz' (u8h_zero_mem_interior_square hL)
    hne hadj.2.2.2.1 hadj.2.2.1
  simpa using this

theorem u8h_A'_adj {L : ℝ} (hL : 0 < L) (T₀ : Triangle) (hT : T₀.carrier ⊆ interior (square L))
    (a' b' : Plane) (h : u8h_A' L T₀ a' b') : u8h_f_Adj (square 2) 0 (u8h_V' L T₀) a' b' := by
  obtain ⟨a, b, h, rfl, rfl⟩ := h
  have hadj := u8h_A_adj L T₀ a b h
  have hL2 := u8h_half_pos hL
  refine ⟨⟨b, hadj.2.1, rfl⟩, ⟨a, hadj.1, rfl⟩, ?_, ?_, ?_⟩
  · rw [sub_zero, sub_zero, u8h_det_ρ, u8h_f_det_swap' b a]
    have := u8h_det_origin_pos hL T₀ hT h
    have h2 : 0 < (L / 2) ^ 2 := by positivity
    rw [neg_div, neg_neg]; exact div_pos this h2
  · intro x hx
    rw [segment_symm, ← u8h_ρ_image_segment hL2] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact u8h_ρ'_mem_frontier hL (hadj.2.2.2.1 hy)
  · rintro _ ⟨c, hc, rfl⟩ hmem
    rw [u8h_ρ_mem_openSegment hL2, openSegment_symm] at hmem
    exact hadj.2.2.2.2 c hc hmem

theorem u8h_A'_cover {L : ℝ} (hL : 0 < L) (T₀ : Triangle) (hT : T₀.carrier ⊆ interior (square L)) :
    ∀ y' ∈ frontier (square 2), ∃ a' b', u8h_A' L T₀ a' b' ∧ y' ∈ segment ℝ a' b' := by
  intro y' hy'
  have hL2 := u8h_half_pos hL
  set y : Plane := ((L / 2) ^ 2) • u8h_ρ (L / 2) y' with hy
  have hyy : u8h_ρ (L / 2) y = y' := by
    rw [hy, u8h_ρ_smul, u8h_ρ_ρ, smul_smul, mul_inv_cancel₀ (pow_ne_zero 2 hL2.ne'), one_smul]
  have hyfr : y ∈ frontier (square L) := by
    rw [u8h_mem_frontier_square, hy, u3h_supNorm_smul, u8h_supNorm_ρ hL2, u8h_mem_frontier_square.1 hy',
      abs_of_pos (by positivity)]
    field_simp
  obtain ⟨a, b, h, hseg⟩ := u8h_A_cover hL T₀ hT y hyfr
  refine ⟨u8h_ρ (L / 2) b, u8h_ρ (L / 2) a, ⟨a, b, h, rfl, rfl⟩, ?_⟩
  rw [← hyy, segment_symm, u8h_ρ_mem_segment hL2]; exact hseg

theorem u8h_A'_straight {L : ℝ} (hL : 0 < L) (T₀ : Triangle) (hT : T₀.carrier ⊆ interior (square L)) :
    ∀ a' b', u8h_A' L T₀ a' b' →
      segment ℝ (u8h_f_ray (square 1) 0 a') (u8h_f_ray (square 1) 0 b') ⊆ frontier (square 1) := by
  rintro _ _ ⟨a, b, h, rfl, rfl⟩
  have hadj := u8h_A_adj L T₀ a b h
  have ha := u8h_V_subset hL T₀ hT hadj.1
  have hb := u8h_V_subset hL T₀ hT hadj.2.1
  rw [u8h_ray_ρ' hL hb, u8h_ray_ρ' hL ha]
  intro x hx
  rw [segment_symm, ← u8h_ρ_image_segment hL] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  exact u8h_ρ_mem_frontier_one hL (hadj.2.2.2.1 hy)

/-- The target annulus data. -/
theorem u8h_tgtData {L : ℝ} (hL : 0 < L) (T₀ : Triangle) (hT : T₀.carrier ⊆ interior (square L)) :
    u8h_AnnData (0 : Plane) (square 1) (square 2) (u8h_V' L T₀) (u8h_A' L T₀) :=
  ⟨u8h_ctx', (u8h_V_finite L T₀).image _, u8h_V'_subset hL T₀ hT, u8h_A'_adj hL T₀ hT, u8h_A'_cover hL T₀ hT,
    u8h_A'_straight hL T₀ hT⟩


/-! ### U8: straightness of `∂T₀` between adjacent outer marks -/

/-- Two frontier points on the same ray from an interior point coincide (anchor on the right). -/
theorem u8h_eq_of_det_zero' {D : Set Plane} (hD : Link.IsDisc D) {z : Plane} (hz : z ∈ interior D)
    {a a' : Plane} (ha : a ∈ frontier D) (ha' : a' ∈ frontier D) (h0 : det (a' - z) (a - z) = 0)
    {y : Plane} (hy : 0 < det (y - z) (a - z)) (hy' : 0 ≤ det (y - z) (a' - z)) : a' = a := by
  have hne : a' - z ≠ 0 := sub_ne_zero.2 (u8h_f_frontier_ne hD hz ha')
  obtain ⟨t, ht⟩ := u8h_f_parallel_of_det_eq_zero hne h0
  have htpos : 0 < t := by
    rw [ht, u8h_f_det_smul_right] at hy
    by_contra hneg; push Not at hneg
    nlinarith
  have h1 : u8h_f_rg D z a = t * u8h_f_rg D z a' := by
    have : a = z + t • (a' - z) := by rw [← ht]; abel
    rw [this, u8h_f_rg_smul _ _ _ htpos.le]
  rw [(u8h_f_rg_eq_one_iff hD hz a).2 ha, (u8h_f_rg_eq_one_iff hD hz a').2 ha', mul_one] at h1
  rw [← h1, one_smul] at ht
  exact (sub_left_inj.1 ht).symm

open Classical in
/-- The frontier pieces of `T₀`: its three edges and the inner projections of all outer marks. -/
noncomputable def u8h_ST (L : ℝ) (T₀ : Triangle) : Finset (Plane × Plane) :=
  Finset.univ.image (fun i : Fin 3 => (T₀.v i, T₀.v (i + 1))) ∪
    (u8h_V_finite L T₀).toFinset.image
      (fun c => (u8h_f_ray T₀.carrier (u8h_o T₀) c, u8h_f_ray T₀.carrier (u8h_o T₀) c))

theorem u8h_ST_cover {L : ℝ} (hL : 0 < L) (T₀ : Triangle) (hT : T₀.carrier ⊆ interior (square L)) :
    (⋃ p ∈ u8h_ST L T₀, segment ℝ p.1 p.2) = frontier T₀.carrier := by
  have C := u8h_ctx hL T₀ hT
  apply Subset.antisymm
  · intro x hx
    obtain ⟨p, hp, hxp⟩ := mem_iUnion₂.1 hx
    rcases Finset.mem_union.1 hp with hp | hp
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hp
      rw [U1_frontier_triangle]; exact mem_iUnion.2 ⟨i, hxp⟩
    · obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 hp
      rw [Set.Finite.mem_toFinset] at hc
      rw [segment_same, mem_singleton_iff] at hxp
      rw [hxp]; exact C.ray_mem_frontier (u8h_V_subset hL T₀ hT hc)
  · intro x hx
    rw [U1_frontier_triangle] at hx
    obtain ⟨i, hi⟩ := mem_iUnion.1 hx
    exact mem_iUnion₂.2 ⟨(T₀.v i, T₀.v (i + 1)),
      Finset.mem_union.2 (Or.inl (Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩)), hi⟩

theorem u8h_ray_mem_marksT {L : ℝ} (T₀ : Triangle) {c : Plane} (hc : c ∈ u8h_V L T₀) :
    u8h_f_ray T₀.carrier (u8h_o T₀) c ∈ u8h_f_marks (u8h_ST L T₀) :=
  u8h_f_marks_left (Finset.mem_union.2 (Or.inr (Finset.mem_image.2
    ⟨c, (Set.Finite.mem_toFinset _).2 hc, rfl⟩)))

theorem u8h_marksT_eq {L : ℝ} (hL : 0 < L) (T₀ : Triangle) (hT : T₀.carrier ⊆ interior (square L))
    {m : Plane} (hm : m ∈ u8h_f_marks (u8h_ST L T₀)) :
    ∃ c ∈ u8h_V L T₀, m = u8h_f_ray T₀.carrier (u8h_o T₀) c := by
  simp only [u8h_f_marks, Finset.coe_union, Finset.coe_image, mem_union, mem_image, Finset.mem_coe] at hm
  rcases hm with ⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩ <;> rcases Finset.mem_union.1 hp with hp | hp
  · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hp
    exact ⟨u8h_q L T₀ i, u8h_q_mem_V L T₀ i, (u8h_ray_q hL T₀ hT i).symm⟩
  · obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 hp
    exact ⟨c, (Set.Finite.mem_toFinset _).1 hc, rfl⟩
  · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hp
    exact ⟨u8h_q L T₀ (i + 1), u8h_q_mem_V L T₀ (i + 1), (u8h_ray_q hL T₀ hT (i + 1)).symm⟩
  · obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 hp
    exact ⟨c, (Set.Finite.mem_toFinset _).1 hc, rfl⟩


/-- **Straightness of the inner frontier**: between the inner projections of two adjacent outer
marks, the frontier of `T₀` is a straight segment. -/
theorem u8h_src_straight {L : ℝ} (hL : 0 < L) (T₀ : Triangle) (hT : T₀.carrier ⊆ interior (square L)) :
    ∀ a b, u8h_A L T₀ a b →
      segment ℝ (u8h_f_ray T₀.carrier (u8h_o T₀) a) (u8h_f_ray T₀.carrier (u8h_o T₀) b) ⊆
        frontier T₀.carrier := by
  intro a b h
  have C := u8h_ctx hL T₀ hT
  set o := u8h_o T₀ with ho
  have hadj := u8h_A_adj L T₀ a b h
  have haV : a ∈ u8h_V L T₀ := hadj.1
  have hbV : b ∈ u8h_V L T₀ := hadj.2.1
  have hab : 0 < det (a - o) (b - o) := hadj.2.2.1
  have hseg : segment ℝ a b ⊆ frontier (square L) := hadj.2.2.2.1
  have hnomark := hadj.2.2.2.2
  have ha : a ∈ frontier (square L) := u8h_V_subset hL T₀ hT haV
  have hb : b ∈ frontier (square L) := u8h_V_subset hL T₀ hT hbV
  have hPta : u8h_f_ray T₀.carrier o a ∈ frontier T₀.carrier := C.ray_mem_frontier ha
  have hPtb : u8h_f_ray T₀.carrier o b ∈ frontier T₀.carrier := C.ray_mem_frontier hb
  have hsa := C.s_pos ha
  have hsb := C.s_pos hb
  -- the anchor `y`: the inner frontier point on the bisecting ray
  set m : Plane := a + b - o with hm
  have hm1 : det (a - o) (m - o) = det (a - o) (b - o) := by
    simp only [hm, det, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub]; ring
  have hm2 : det (m - o) (b - o) = det (a - o) (b - o) := by
    simp only [hm, det, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub]; ring
  have hmo : m ≠ o := by
    intro e; rw [e, sub_self, u8h_f_det_zero_right] at hm1; linarith
  set y := u8h_f_ray T₀.carrier o m with hy
  have hyfr : y ∈ frontier T₀.carrier := u8h_f_ray_mem_frontier C.hin C.hz hmo
  have hrm : 0 < u8h_f_rg T₀.carrier o m := u8h_f_rg_pos C.hin C.hz hmo
  have hysub : y - o = (u8h_f_rg T₀.carrier o m)⁻¹ • (m - o) := by rw [hy, u8h_f_ray, add_sub_cancel_left]
  have F2 : 0 < det (a - o) (y - o) := by
    rw [hysub, u8h_f_det_smul_right, hm1]; exact mul_pos (inv_pos.2 hrm) hab
  have F3 : 0 < det (y - o) (b - o) := by
    rw [hysub, u8h_f_det_smul_left', hm2]; exact mul_pos (inv_pos.2 hrm) hab
  -- the inner adjacent pair covering `y`
  obtain ⟨a₁, b₁, hA₁, hy₁⟩ := u8h_f_cover C.hin C.hz (u8h_ST_cover hL T₀ hT) hyfr
  have hAdj₁ := hA₁.1
  obtain ⟨a', ha'V, rfl⟩ := u8h_marksT_eq hL T₀ hT hAdj₁.1
  obtain ⟨b', hb'V, rfl⟩ := u8h_marksT_eq hL T₀ hT hAdj₁.2.1
  simp only [← ho] at hA₁ hy₁ hAdj₁
  have ha' : a' ∈ frontier (square L) := u8h_V_subset hL T₀ hT ha'V
  have hb' : b' ∈ frontier (square L) := u8h_V_subset hL T₀ hT hb'V
  have hsa' := C.s_pos ha'
  have hsb' := C.s_pos hb'
  have hseg₁ : segment ℝ (u8h_f_ray T₀.carrier o a') (u8h_f_ray T₀.carrier o b') ⊆ frontier T₀.carrier := hAdj₁.2.2.2.1
  have hdet₁ : 0 < det (u8h_f_ray T₀.carrier o a' - o) (u8h_f_ray T₀.carrier o b' - o) := hAdj₁.2.2.1
  have F4 : 0 < det (a' - o) (b' - o) := by
    rw [u8h_AnnCtx.ray_sub, u8h_AnnCtx.ray_sub, u8h_f_det_smul_left', u8h_f_det_smul_right] at hdet₁
    exact pos_of_mul_pos_right (pos_of_mul_pos_right hdet₁ hsa'.le) hsb'.le
  obtain ⟨F5', F6'⟩ := u8h_det_of_mem_segment (z := o) hy₁ hdet₁.le
  have F5 : 0 ≤ det (a' - o) (y - o) := by
    rw [u8h_AnnCtx.ray_sub a', u8h_f_det_smul_left'] at F5'
    exact nonneg_of_mul_nonneg_right F5' hsa'
  have F6 : 0 ≤ det (y - o) (b' - o) := by
    rw [u8h_AnnCtx.ray_sub b', u8h_f_det_smul_right] at F6'
    exact nonneg_of_mul_nonneg_right F6' hsb'
  -- a mark strictly inside the sector `(a, b)` is impossible
  have hno : ∀ c ∈ u8h_V L T₀, 0 < det (a - o) (c - o) → 0 < det (c - o) (b - o) → False := by
    intro c hcV h1 h2
    have hc : c ∈ frontier (square L) := u8h_V_subset hL T₀ hT hcV
    have hcs := u8h_f_frontier_mem_segment C.hout C.hz' hab hseg hc h1.le h2.le
    rcases u8h_f_mem_segment_cases hcs with e | e | e
    · rw [e, u8h_f_det_self] at h1; exact lt_irrefl _ h1
    · rw [e, u8h_f_det_self] at h2; exact lt_irrefl _ h2
    · exact hnomark c hcV e
  -- a mark strictly inside the inner sector `(u8h_f_ray T₀.carrier o a', u8h_f_ray T₀.carrier o b')` is impossible
  have hno₁ : ∀ c ∈ u8h_V L T₀, 0 < det (a' - o) (c - o) → 0 < det (c - o) (b' - o) → False := by
    intro c hcV h1 h2
    have hc : c ∈ frontier (square L) := u8h_V_subset hL T₀ hT hcV
    have hsc := C.s_pos hc
    have h1' : 0 ≤ det (u8h_f_ray T₀.carrier o a' - o) (u8h_f_ray T₀.carrier o c - o) := by
      rw [u8h_AnnCtx.ray_sub, u8h_AnnCtx.ray_sub, u8h_f_det_smul_left', u8h_f_det_smul_right]
      positivity
    have h2' : 0 ≤ det (u8h_f_ray T₀.carrier o c - o) (u8h_f_ray T₀.carrier o b' - o) := by
      rw [u8h_AnnCtx.ray_sub, u8h_AnnCtx.ray_sub, u8h_f_det_smul_left', u8h_f_det_smul_right]
      positivity
    have hcs := u8h_f_frontier_mem_segment C.hin C.hz hdet₁ hseg₁ (C.ray_mem_frontier hc) h1' h2'
    rcases u8h_f_mem_segment_cases hcs with e | e | e
    · have h0 : det (a' - o) (u8h_f_ray T₀.carrier o c - o) = det (a' - o) (u8h_f_ray T₀.carrier o a' - o) := by rw [e]
      rw [u8h_AnnCtx.ray_sub c, u8h_AnnCtx.ray_sub a', u8h_f_det_smul_right, u8h_f_det_smul_right,
        u8h_f_det_self, mul_zero] at h0
      have : det (a' - o) (c - o) = 0 := by
        rcases mul_eq_zero.1 h0 with h | h
        · exact absurd h hsc.ne'
        · exact h
      linarith
    · have h0 : det (u8h_f_ray T₀.carrier o c - o) (b' - o) = det (u8h_f_ray T₀.carrier o b' - o) (b' - o) := by rw [e]
      rw [u8h_AnnCtx.ray_sub c, u8h_AnnCtx.ray_sub b', u8h_f_det_smul_left', u8h_f_det_smul_left',
        u8h_f_det_self, mul_zero] at h0
      have : det (c - o) (b' - o) = 0 := by
        rcases mul_eq_zero.1 h0 with h | h
        · exact absurd h hsc.ne'
        · exact h
      linarith
    · exact hAdj₁.2.2.2.2 (u8h_f_ray T₀.carrier o c) (u8h_ray_mem_marksT T₀ hcV) e
  -- Step 1: `a'` is not strictly after `a`
  have S1 : det (a - o) (a' - o) ≤ 0 := by
    by_contra hpos; push Not at hpos
    apply hno a' ha'V hpos
    rw [u8h_cramer_det F2.ne' (a' - o) (b - o)]
    have h1 : 0 ≤ det (a' - o) (y - o) / det (a - o) (y - o) * det (a - o) (b - o) := by positivity
    have h2 : 0 < det (a - o) (a' - o) / det (a - o) (y - o) * det (y - o) (b - o) := by positivity
    linarith
  -- Step 2: `b'` is not strictly before `b`
  have S2 : det (b' - o) (b - o) ≤ 0 := by
    by_contra hpos; push Not at hpos
    apply hno b' hb'V _ hpos
    have e := u8h_cramer_det F3.ne' (b' - o) (a - o)
    have t1 : det (b' - o) (b - o) / det (y - o) (b - o) * det (y - o) (a - o) < 0 := by
      have hq : 0 < det (b' - o) (b - o) / det (y - o) (b - o) := div_pos hpos F3
      have : det (y - o) (a - o) < 0 := by rw [u8h_f_det_swap']; linarith
      exact mul_neg_of_pos_of_neg hq this
    have t2 : det (y - o) (b' - o) / det (y - o) (b - o) * det (b - o) (a - o) ≤ 0 := by
      have hq : 0 ≤ det (y - o) (b' - o) / det (y - o) (b - o) := div_nonneg F6 F3.le
      have : det (b - o) (a - o) ≤ 0 := by rw [u8h_f_det_swap']; linarith
      exact mul_nonpos_of_nonneg_of_nonpos hq this
    have : det (b' - o) (a - o) < 0 := by rw [e]; linarith
    rw [u8h_f_det_swap'] at this; linarith
  -- Step 3: `a' = a`
  have hay : 0 < det (a' - o) (y - o) := by
    rcases eq_or_lt_of_le F5 with h0 | h0
    · exfalso
      have hne : a' - o ≠ 0 := sub_ne_zero.2 (C.ne_of_frontier ha')
      obtain ⟨t, ht⟩ := u8h_f_parallel_of_det_eq_zero hne h0.symm
      have hF2 := F2
      rw [ht, u8h_f_det_smul_right] at hF2
      have hF6 := F6
      rw [ht, u8h_f_det_smul_left'] at hF6
      have ht0 : 0 ≤ t := by
        by_contra hneg; push Not at hneg
        nlinarith [F4]
      nlinarith [S1]
    · exact h0
  have S3 : det (a' - o) (a - o) = 0 := by
    by_contra hne0
    have hpos : 0 < det (a' - o) (a - o) := by
      rcases lt_or_gt_of_ne hne0 with h | h
      · exfalso; rw [u8h_f_det_swap'] at h; linarith
      · exact h
    apply hno₁ a haV hpos
    rw [u8h_cramer_det hay.ne' (a - o) (b' - o)]
    have h1 : 0 < det (a - o) (y - o) / det (a' - o) (y - o) * det (a' - o) (b' - o) := by positivity
    have h2 : 0 ≤ det (a' - o) (a - o) / det (a' - o) (y - o) * det (y - o) (b' - o) := by positivity
    linarith
  have hEa : a' = a := u8h_eq_of_det_zero C.hout C.hz' ha ha' S3 F2 F5
  subst hEa
  -- Step 4: `b' = b`
  have S4 : det (b - o) (b' - o) = 0 := by
    by_contra hne0
    have hpos : 0 < det (b - o) (b' - o) := by
      rcases lt_or_gt_of_ne hne0 with h | h
      · exfalso; rw [u8h_f_det_swap'] at h; linarith
      · exact h
    exact hno₁ b hbV hab hpos
  have hEb : b' = b := by
    apply u8h_eq_of_det_zero' C.hout C.hz' hb hb' _ F3 F6
    rw [u8h_f_det_swap']; linarith
  subst hEb
  exact hseg₁

/-! ### U8: the annulus map `g_A : Q_L \ int T₀ → Q_2 \ int Q_1` -/

theorem u8h_ρ_half (L : ℝ) (x : Plane) : u8h_ρ (L / 2) x = (2 : ℝ) • u8h_ρ L x := by
  ext <;> simp [u8h_ρ] <;> ring

/-- The source annulus data. -/
theorem u8h_D {L : ℝ} (hL : 0 < L) (T₀ : Triangle) (hT : T₀.carrier ⊆ interior (square L)) :
    u8h_AnnData (u8h_o T₀) T₀.carrier (square L) (u8h_V L T₀) (u8h_A L T₀) :=
  u8h_srcData hL T₀ hT (u8h_src_straight hL T₀ hT)

/-- The source annulus triangulation. -/
noncomputable def u8h_K {L : ℝ} (hL : 0 < L) (T₀ : Triangle) (hT : T₀.carrier ⊆ interior (square L)) :
    Triangulation (square L \ interior T₀.carrier) :=
  Classical.choose (u8h_D hL T₀ hT).triangulation

theorem u8h_K_faces {L : ℝ} (hL : 0 < L) (T₀ : Triangle) (hT : T₀.carrier ⊆ interior (square L)) :
    (u8h_K hL T₀ hT).faces = u8h_annFaces (u8h_o T₀) T₀.carrier (u8h_A L T₀) :=
  Classical.choose_spec (u8h_D hL T₀ hT).triangulation

/-- The target annulus triangulation. -/
noncomputable def u8h_K' {L : ℝ} (hL : 0 < L) (T₀ : Triangle) (hT : T₀.carrier ⊆ interior (square L)) :
    Triangulation (square 2 \ interior (square 1)) :=
  Classical.choose (u8h_tgtData hL T₀ hT).triangulation

theorem u8h_K'_faces {L : ℝ} (hL : 0 < L) (T₀ : Triangle) (hT : T₀.carrier ⊆ interior (square L)) :
    (u8h_K' hL T₀ hT).faces = u8h_annFaces 0 (square 1) (u8h_A' L T₀) :=
  Classical.choose_spec (u8h_tgtData hL T₀ hT).triangulation

open Classical in
/-- The vertex assignment: outer marks go to `ρ_L (∂Q_L) = ∂Q_1`, inner points to `ρ_{L/2}` of their
outer projections (on `∂Q_2`). -/
noncomputable def u8h_w (L : ℝ) (T₀ : Triangle) (x : Plane) : Plane :=
  if x ∈ frontier (square L) then u8h_ρ L x else u8h_ρ (L / 2) (u8h_f_ray (square L) (u8h_o T₀) x)

theorem u8h_w_mark {L : ℝ} (T₀ : Triangle) {c : Plane} (hc : c ∈ frontier (square L)) :
    u8h_w L T₀ c = u8h_ρ L c := by
  rw [u8h_w, if_pos hc]

theorem u8h_ray_notMem_frontier {L : ℝ} (hL : 0 < L) (T₀ : Triangle) (hT : T₀.carrier ⊆ interior (square L))
    {c : Plane} (hc : c ∈ frontier (square L)) :
    u8h_f_ray T₀.carrier (u8h_o T₀) c ∉ frontier (square L) := by
  intro h
  have C := u8h_ctx hL T₀ hT
  have h1 : u8h_f_ray T₀.carrier (u8h_o T₀) c ∈ interior (square L) :=
    hT (C.hin.2.1.isClosed.frontier_subset (C.ray_mem_frontier hc))
  exact h.2 h1

theorem u8h_w_ray {L : ℝ} (hL : 0 < L) (T₀ : Triangle) (hT : T₀.carrier ⊆ interior (square L)) {c : Plane}
    (hc : c ∈ frontier (square L)) :
    u8h_w L T₀ (u8h_f_ray T₀.carrier (u8h_o T₀) c) = u8h_ρ (L / 2) c := by
  rw [u8h_w, if_neg (u8h_ray_notMem_frontier hL T₀ hT hc), (u8h_ctx hL T₀ hT).rayout_ray hc]

/-- The annulus map. -/
noncomputable def u8h_g {L : ℝ} (hL : 0 < L) (T₀ : Triangle) (hT : T₀.carrier ⊆ interior (square L)) :
    Plane → Plane :=
  u8h_glue (u8h_K hL T₀ hT) (u8h_w L T₀)

theorem u8h_face_v {L : ℝ} (hL : 0 < L) (T₀ : Triangle) (hT : T₀.carrier ⊆ interior (square L))
    {T : Triangle} (hTK : T ∈ (u8h_K hL T₀ hT).faces) :
    ∃ a b, u8h_A L T₀ a b ∧
      (T.v = ![u8h_f_ray T₀.carrier (u8h_o T₀) a, a, b] ∨
        T.v = ![u8h_f_ray T₀.carrier (u8h_o T₀) a, b, u8h_f_ray T₀.carrier (u8h_o T₀) b]) := by
  rw [u8h_K_faces] at hTK; exact hTK

theorem u8h_A_frontier {L : ℝ} (hL : 0 < L) (T₀ : Triangle) (hT : T₀.carrier ⊆ interior (square L))
    {a b : Plane} (h : u8h_A L T₀ a b) : a ∈ frontier (square L) ∧ b ∈ frontier (square L) :=
  ⟨u8h_V_subset hL T₀ hT (u8h_A_adj L T₀ a b h).1, u8h_V_subset hL T₀ hT (u8h_A_adj L T₀ a b h).2.1⟩

/-- The vertex images of the two faces of a pair. -/
theorem u8h_w_tri2 {L : ℝ} (hL : 0 < L) (T₀ : Triangle) (hT : T₀.carrier ⊆ interior (square L))
    {a b : Plane} (h : u8h_A L T₀ a b) :
    u8h_w L T₀ (u8h_f_ray T₀.carrier (u8h_o T₀) a) = (2 : ℝ) • u8h_ρ L a ∧
      u8h_w L T₀ a = u8h_ρ L a ∧ u8h_w L T₀ b = u8h_ρ L b := by
  obtain ⟨ha, hb⟩ := u8h_A_frontier hL T₀ hT h
  exact ⟨by rw [u8h_w_ray hL T₀ hT ha, u8h_ρ_half], u8h_w_mark T₀ ha, u8h_w_mark T₀ hb⟩

theorem u8h_w_tri1 {L : ℝ} (hL : 0 < L) (T₀ : Triangle) (hT : T₀.carrier ⊆ interior (square L))
    {a b : Plane} (h : u8h_A L T₀ a b) :
    u8h_w L T₀ (u8h_f_ray T₀.carrier (u8h_o T₀) a) = (2 : ℝ) • u8h_ρ L a ∧
      u8h_w L T₀ b = u8h_ρ L b ∧ u8h_w L T₀ (u8h_f_ray T₀.carrier (u8h_o T₀) b) = (2 : ℝ) • u8h_ρ L b := by
  obtain ⟨ha, hb⟩ := u8h_A_frontier hL T₀ hT h
  exact ⟨by rw [u8h_w_ray hL T₀ hT ha, u8h_ρ_half], u8h_w_mark T₀ hb, by rw [u8h_w_ray hL T₀ hT hb, u8h_ρ_half]⟩

/-- Positivity of the vertex images on every source face. -/
theorem u8h_w_pos {L : ℝ} (hL : 0 < L) (T₀ : Triangle) (hT : T₀.carrier ⊆ interior (square L)) :
    ∀ T ∈ (u8h_K hL T₀ hT).faces,
      0 < det (u8h_w L T₀ (T.v 1) - u8h_w L T₀ (T.v 0)) (u8h_w L T₀ (T.v 2) - u8h_w L T₀ (T.v 0)) := by
  intro T hTK
  obtain ⟨a, b, h, hv | hv⟩ := u8h_face_v hL T₀ hT hTK
  · have hab := u8h_det_origin_pos hL T₀ hT h
    obtain ⟨e0, e1, e2⟩ := u8h_w_tri2 hL T₀ hT h
    rw [hv]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons]
    rw [e0, e1, e2]
    have : det (u8h_ρ L a - (2 : ℝ) • u8h_ρ L a) (u8h_ρ L b - (2 : ℝ) • u8h_ρ L a) =
        det ((-1 : ℝ) • u8h_ρ L a + (0 : ℝ) • u8h_ρ L b) ((-2 : ℝ) • u8h_ρ L a + (1 : ℝ) • u8h_ρ L b) := by
      congr 1 <;> module
    rw [this, u8h_det_combo, u8h_det_ρ]
    have h2 : 0 < L ^ 2 := by positivity
    have : 0 < det a b / L ^ 2 := div_pos hab h2
    nlinarith
  · have hab := u8h_det_origin_pos hL T₀ hT h
    obtain ⟨e0, e1, e2⟩ := u8h_w_tri1 hL T₀ hT h
    rw [hv]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons]
    rw [e0, e1, e2]
    have : det (u8h_ρ L b - (2 : ℝ) • u8h_ρ L a) ((2 : ℝ) • u8h_ρ L b - (2 : ℝ) • u8h_ρ L a) =
        det ((-2 : ℝ) • u8h_ρ L a + (1 : ℝ) • u8h_ρ L b) ((-2 : ℝ) • u8h_ρ L a + (2 : ℝ) • u8h_ρ L b) := by
      congr 1 <;> module
    rw [this, u8h_det_combo, u8h_det_ρ]
    have h2 : 0 < L ^ 2 := by positivity
    have : 0 < det a b / L ^ 2 := div_pos hab h2
    nlinarith

/-- The annulus map is positive PL on the source triangulation. -/
theorem u8h_g_isPositivePLOn {L : ℝ} (hL : 0 < L) (T₀ : Triangle) (hT : T₀.carrier ⊆ interior (square L)) :
    IsPositivePLOn (u8h_g hL T₀ hT) (u8h_K hL T₀ hT) :=
  u8h_glue_isPositivePLOn _ _ (u8h_w_pos hL T₀ hT)


/-- `g` at the vertices of a source face. -/
theorem u8h_g_vertex {L : ℝ} (hL : 0 < L) (T₀ : Triangle) (hT : T₀.carrier ⊆ interior (square L))
    {T : Triangle} (hTK : T ∈ (u8h_K hL T₀ hT).faces) (i : Fin 3) :
    u8h_g hL T₀ hT (T.v i) = u8h_w L T₀ (T.v i) :=
  u8h_glue_vertex _ _ hTK i

theorem u8h_image_three {f : Plane → Plane} (p q r : Plane) : f '' {p, q, r} = {f p, f q, f r} := by
  rw [image_insert_eq, image_insert_eq, image_singleton]

/-- The image of a source face is the face of its vertex images. -/
theorem u8h_g_image_face {L : ℝ} (hL : 0 < L) (T₀ : Triangle) (hT : T₀.carrier ⊆ interior (square L))
    {T : Triangle} (hTK : T ∈ (u8h_K hL T₀ hT).faces) :
    u8h_g hL T₀ hT '' T.carrier =
      convexHull ℝ {u8h_w L T₀ (T.v 0), u8h_w L T₀ (T.v 1), u8h_w L T₀ (T.v 2)} := by
  rw [u8h_image_face (u8h_g_isPositivePLOn hL T₀ hT T hTK)]
  congr 1
  have hr : range T.v = {T.v 0, T.v 1, T.v 2} := by
    ext w; simp only [mem_range, mem_insert_iff, mem_singleton_iff]
    constructor
    · rintro ⟨i, rfl⟩; fin_cases i <;> simp
    · rintro (rfl | rfl | rfl) <;> exact ⟨_, rfl⟩
  rw [hr, u8h_image_three, u8h_g_vertex hL T₀ hT hTK, u8h_g_vertex hL T₀ hT hTK, u8h_g_vertex hL T₀ hT hTK]

/-- The target adjacency of the reflected pair. -/
theorem u8h_A'_of {L : ℝ} (T₀ : Triangle) {a b : Plane} (h : u8h_A L T₀ a b) :
    u8h_A' L T₀ (u8h_ρ (L / 2) b) (u8h_ρ (L / 2) a) := ⟨a, b, h, rfl, rfl⟩

/-- Every source face maps onto a target face. -/
theorem u8h_g_himg {L : ℝ} (hL : 0 < L) (T₀ : Triangle) (hT : T₀.carrier ⊆ interior (square L)) :
    ∀ T ∈ (u8h_K hL T₀ hT).faces, ∃ T' ∈ (u8h_K' hL T₀ hT).faces, u8h_g hL T₀ hT '' T.carrier = T'.carrier := by
  intro T hTK
  have D' := u8h_tgtData hL T₀ hT
  obtain ⟨a, b, h, hv | hv⟩ := u8h_face_v hL T₀ hT hTK
  · obtain ⟨ha, hb⟩ := u8h_A_frontier hL T₀ hT h
    obtain ⟨e0, e1, e2⟩ := u8h_w_tri2 hL T₀ hT h
    refine ⟨D'.tri1 (u8h_A'_of T₀ h), by rw [u8h_K'_faces]; exact D'.tri1_mem _, ?_⟩
    rw [u8h_g_image_face hL T₀ hT hTK, D'.tri1_carrier, hv]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons]
    rw [e0, e1, e2, u8h_ray_ρ' hL hb, u8h_ray_ρ' hL ha, ← u8h_ρ_half]
    congr 1
    ext w; simp only [mem_insert_iff, mem_singleton_iff]; tauto
  · obtain ⟨ha, hb⟩ := u8h_A_frontier hL T₀ hT h
    obtain ⟨e0, e1, e2⟩ := u8h_w_tri1 hL T₀ hT h
    refine ⟨D'.tri2 (u8h_A'_of T₀ h), by rw [u8h_K'_faces]; exact D'.tri2_mem _, ?_⟩
    rw [u8h_g_image_face hL T₀ hT hTK, D'.tri2_carrier, hv]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons]
    rw [e0, e1, e2, u8h_ray_ρ' hL hb, ← u8h_ρ_half, ← u8h_ρ_half]
    congr 1
    ext w; simp only [mem_insert_iff, mem_singleton_iff]; tauto

/-- Every target face is the image of a source face. -/
theorem u8h_g_hsurj {L : ℝ} (hL : 0 < L) (T₀ : Triangle) (hT : T₀.carrier ⊆ interior (square L)) :
    ∀ T' ∈ (u8h_K' hL T₀ hT).faces, ∃ T ∈ (u8h_K hL T₀ hT).faces, u8h_g hL T₀ hT '' T.carrier = T'.carrier := by
  intro T' hT'
  have D := u8h_D hL T₀ hT
  rw [u8h_K'_faces] at hT'
  obtain ⟨a', b', ⟨a, b, h, rfl, rfl⟩, hv' | hv'⟩ := hT'
  · -- `T' = (Pt' (ρ' b), ρ' b, ρ' a)` is the image of the inner source face
    obtain ⟨ha, hb⟩ := u8h_A_frontier hL T₀ hT h
    obtain ⟨e0, e1, e2⟩ := u8h_w_tri1 hL T₀ hT h
    refine ⟨D.tri1 h, by rw [u8h_K_faces]; exact D.tri1_mem h, ?_⟩
    have hTK : D.tri1 h ∈ (u8h_K hL T₀ hT).faces := by rw [u8h_K_faces]; exact D.tri1_mem h
    rw [u8h_g_image_face hL T₀ hT hTK, u8h_f_carrier_of_v hv', D.tri1_v]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons]
    rw [e0, e1, e2, u8h_ray_ρ' hL hb, ← u8h_ρ_half, ← u8h_ρ_half]
    congr 1
    ext w; simp only [mem_insert_iff, mem_singleton_iff]; tauto
  · obtain ⟨ha, hb⟩ := u8h_A_frontier hL T₀ hT h
    obtain ⟨e0, e1, e2⟩ := u8h_w_tri2 hL T₀ hT h
    refine ⟨D.tri2 h, by rw [u8h_K_faces]; exact D.tri2_mem h, ?_⟩
    have hTK : D.tri2 h ∈ (u8h_K hL T₀ hT).faces := by rw [u8h_K_faces]; exact D.tri2_mem h
    rw [u8h_g_image_face hL T₀ hT hTK, u8h_f_carrier_of_v hv', D.tri2_v]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons]
    rw [e0, e1, e2, u8h_ray_ρ' hL hb, u8h_ray_ρ' hL ha, ← u8h_ρ_half]
    congr 1
    ext w; simp only [mem_insert_iff, mem_singleton_iff]; tauto

/-- Every vertex of a source face is an outer mark or the inner point of an outer mark. -/
theorem u8h_vertex_cases {L : ℝ} (hL : 0 < L) (T₀ : Triangle) (hT : T₀.carrier ⊆ interior (square L))
    {T : Triangle} (hTK : T ∈ (u8h_K hL T₀ hT).faces) (i : Fin 3) :
    (T.v i ∈ frontier (square L)) ∨
      (∃ c ∈ frontier (square L), T.v i = u8h_f_ray T₀.carrier (u8h_o T₀) c) := by
  obtain ⟨a, b, h, hv | hv⟩ := u8h_face_v hL T₀ hT hTK
  · obtain ⟨ha, hb⟩ := u8h_A_frontier hL T₀ hT h
    rw [hv]; fin_cases i
    · exact Or.inr ⟨a, ha, rfl⟩
    · exact Or.inl ha
    · exact Or.inl hb
  · obtain ⟨ha, hb⟩ := u8h_A_frontier hL T₀ hT h
    rw [hv]; fin_cases i
    · exact Or.inr ⟨a, ha, rfl⟩
    · exact Or.inl hb
    · exact Or.inr ⟨b, hb, rfl⟩

/-- `w` is injective on the vertices. -/
theorem u8h_g_hvinj {L : ℝ} (hL : 0 < L) (T₀ : Triangle) (hT : T₀.carrier ⊆ interior (square L)) :
    ∀ T ∈ (u8h_K hL T₀ hT).faces, ∀ T' ∈ (u8h_K hL T₀ hT).faces, ∀ i j,
      u8h_g hL T₀ hT (T.v i) = u8h_g hL T₀ hT (T'.v j) → T.v i = T'.v j := by
  intro T hTK T' hT'K i j hij
  rw [u8h_g_vertex hL T₀ hT hTK, u8h_g_vertex hL T₀ hT hT'K] at hij
  have hL2 := u8h_half_pos hL
  rcases u8h_vertex_cases hL T₀ hT hTK i with hc | ⟨c, hc, hci⟩ <;>
    rcases u8h_vertex_cases hL T₀ hT hT'K j with hc' | ⟨c', hc', hcj⟩
  · rw [u8h_w_mark T₀ hc, u8h_w_mark T₀ hc'] at hij
    exact u8h_ρ_injective hL hij
  · exfalso
    rw [hcj, u8h_w_mark T₀ hc, u8h_w_ray hL T₀ hT hc'] at hij
    have := congrArg supNorm hij
    rw [u8h_supNorm_ρ hL, u8h_supNorm_ρ' hL hc', u8h_mem_frontier_square.1 hc, div_self hL.ne'] at this
    norm_num at this
  · exfalso
    rw [hci, u8h_w_mark T₀ hc', u8h_w_ray hL T₀ hT hc] at hij
    have := congrArg supNorm hij
    rw [u8h_supNorm_ρ hL, u8h_supNorm_ρ' hL hc, u8h_mem_frontier_square.1 hc', div_self hL.ne'] at this
    norm_num at this
  · rw [hci, hcj, u8h_w_ray hL T₀ hT hc, u8h_w_ray hL T₀ hT hc'] at hij
    rw [hci, hcj, u8h_ρ_injective hL2 hij]

/-- **The annulus map is a bijection** `Q_L \ int T₀ → Q_2 \ int Q_1`. -/
theorem u8h_g_bij {L : ℝ} (hL : 0 < L) (T₀ : Triangle) (hT : T₀.carrier ⊆ interior (square L)) :
    InjOn (u8h_g hL T₀ hT) (square L \ interior T₀.carrier) ∧
      u8h_g hL T₀ hT '' (square L \ interior T₀.carrier) = square 2 \ interior (square 1) :=
  u8h_bij_of_faces (u8h_K hL T₀ hT) (u8h_K' hL T₀ hT) (u8h_g_isPositivePLOn hL T₀ hT)
    (u8h_g_himg hL T₀ hT) (u8h_g_hsurj hL T₀ hT) (u8h_g_hvinj hL T₀ hT)


/-- `ρ_L` as a linear map. -/
noncomputable def u8h_ρ_linear (L : ℝ) : Plane →ₗ[ℝ] Plane where
  toFun := u8h_ρ L
  map_add' := u8h_ρ_add L
  map_smul' := fun c x => by simpa using u8h_ρ_smul L c x

theorem u8h_ρ_affineOn (L : ℝ) : AffineOn (u8h_ρ L) univ :=
  ⟨u8h_ρ_linear L, 0, fun x _ => by rw [add_zero]; rfl⟩

/-- `g` agrees with `ρ_L` on the seam `∂Q_L`. -/
theorem u8h_g_seam {L : ℝ} (hL : 0 < L) (T₀ : Triangle) (hT : T₀.carrier ⊆ interior (square L)) {x : Plane}
    (hx : x ∈ frontier (square L)) : u8h_g hL T₀ hT x = u8h_ρ L x := by
  have D := u8h_D hL T₀ hT
  obtain ⟨a, b, h, hxs⟩ := u8h_A_cover hL T₀ hT x hx
  obtain ⟨ha, hb⟩ := u8h_A_frontier hL T₀ hT h
  have hTK : D.tri2 h ∈ (u8h_K hL T₀ hT).faces := by rw [u8h_K_faces]; exact D.tri2_mem h
  have hsub : segment ℝ a b ⊆ (D.tri2 h).carrier := by
    rw [D.tri2_carrier]; exact segment_subset_convexHull (by simp) (by simp)
  rw [u8h_g, u8h_glue_eq _ _ hTK (hsub hxs)]
  have hagree : ∀ v ∈ ({a, b} : Set Plane), u8h_aff (D.tri2 h) (u8h_w L T₀) v = u8h_ρ L v := by
    intro v hv
    simp only [mem_insert_iff, mem_singleton_iff] at hv
    rcases hv with rfl | rfl
    · have e := u8h_aff_vertex (D.tri2 h) (u8h_w L T₀) 1
      have e1 : (D.tri2 h).v 1 = v := rfl
      rw [e1] at e
      rw [e, u8h_w_mark T₀ ha]
    · have e := u8h_aff_vertex (D.tri2 h) (u8h_w L T₀) 2
      have e2 : (D.tri2 h).v 2 = v := rfl
      rw [e2] at e
      rw [e, u8h_w_mark T₀ hb]
  exact u8h_affine_eq_on_hull (u8h_aff_affine _ _) (u8h_ρ_affineOn L) hagree x
    (by rw [convexHull_pair]; exact hxs)

/-- The image of an inner edge `[Pt a, Pt b]` under `g` is `[ρ_{L/2} a, ρ_{L/2} b] ⊆ ∂Q_2`. -/
theorem u8h_g_image_inner_edge {L : ℝ} (hL : 0 < L) (T₀ : Triangle) (hT : T₀.carrier ⊆ interior (square L))
    {a b : Plane} (h : u8h_A L T₀ a b) :
    u8h_g hL T₀ hT '' segment ℝ (u8h_f_ray T₀.carrier (u8h_o T₀) a) (u8h_f_ray T₀.carrier (u8h_o T₀) b) =
      segment ℝ (u8h_ρ (L / 2) a) (u8h_ρ (L / 2) b) := by
  have D := u8h_D hL T₀ hT
  obtain ⟨ha, hb⟩ := u8h_A_frontier hL T₀ hT h
  have hTK : D.tri1 h ∈ (u8h_K hL T₀ hT).faces := by rw [u8h_K_faces]; exact D.tri1_mem h
  have haff : IsPositiveAffineOn (u8h_g hL T₀ hT) (D.tri1 h) := u8h_g_isPositivePLOn hL T₀ hT _ hTK
  have hsub : ({u8h_f_ray T₀.carrier (u8h_o T₀) a, u8h_f_ray T₀.carrier (u8h_o T₀) b} : Set Plane) ⊆
      (D.tri1 h).carrier := by
    rw [D.tri1_carrier]
    intro w hw
    simp only [mem_insert_iff, mem_singleton_iff] at hw
    rcases hw with rfl | rfl
    · exact subset_convexHull ℝ _ (by simp)
    · exact subset_convexHull ℝ _ (by simp)
  rw [← convexHull_pair, u2h_image_convexHull_of_affineOn haff.1 (U1_triangle_convex _) hsub, image_pair,
    convexHull_pair]
  have e0 := u8h_g_vertex hL T₀ hT hTK 0
  have e2 := u8h_g_vertex hL T₀ hT hTK 2
  have v0 : (D.tri1 h).v 0 = u8h_f_ray T₀.carrier (u8h_o T₀) a := rfl
  have v2 : (D.tri1 h).v 2 = u8h_f_ray T₀.carrier (u8h_o T₀) b := rfl
  rw [v0] at e0; rw [v2] at e2
  rw [e0, e2, u8h_w_ray hL T₀ hT ha, u8h_w_ray hL T₀ hT hb]

/-- **The image of `∂T₀` is `∂Q_2`.** -/
theorem u8h_g_frontier {L : ℝ} (hL : 0 < L) (T₀ : Triangle) (hT : T₀.carrier ⊆ interior (square L)) :
    u8h_g hL T₀ hT '' frontier T₀.carrier = frontier (square 2) := by
  have D := u8h_D hL T₀ hT
  have hL2 := u8h_half_pos hL
  apply Subset.antisymm
  · rintro _ ⟨y, hy, rfl⟩
    obtain ⟨a, b, h, hys⟩ := D.frontier_in_cover hy
    have hmem : u8h_g hL T₀ hT y ∈ segment ℝ (u8h_ρ (L / 2) a) (u8h_ρ (L / 2) b) := by
      rw [← u8h_g_image_inner_edge hL T₀ hT h]; exact ⟨y, hys, rfl⟩
    rw [← u8h_ρ_image_segment hL2] at hmem
    obtain ⟨w, hw, hw'⟩ := hmem
    rw [← hw']
    exact u8h_ρ'_mem_frontier hL ((u8h_A_adj L T₀ a b h).2.2.2.1 hw)
  · intro y' hy'
    obtain ⟨a', b', hA', hseg⟩ := u8h_A'_cover hL T₀ hT y' hy'
    obtain ⟨a, b, h, ha', hb'⟩ := hA'
    rw [ha', hb', segment_symm, ← u8h_g_image_inner_edge hL T₀ hT h] at hseg
    obtain ⟨y, hy, rfl⟩ := hseg
    exact ⟨y, u8h_src_straight hL T₀ hT a b h hy, rfl⟩

/-! ### U8: the exterior fan map on the sphere -/

/-- Transport of a triangulation along a set equality. -/
def u8h_triangulation_congr {X Y : Set Plane} (h : X = Y) (K : Triangulation X) : Triangulation Y :=
  ⟨K.faces, K.finite, h ▸ K.cover, K.inter⟩

theorem u8h_isPositiveAffineOn_id (T : Triangle) : IsPositiveAffineOn id T :=
  ⟨⟨LinearMap.id, 0, fun x _ => by simp⟩, T.pos⟩

/-- U8 helper: the plane chart part of the model exterior of `T₀` is `Q_L \ int T₀`. -/
theorem u8h_chartPart_false_exterior {L : ℝ} (T₀ : Triangle) :
    chartPart L false (((↑) : Plane → Sphere) '' interior T₀.carrier)ᶜ = square L \ interior T₀.carrier := by
  ext x
  simp only [chartPart, modelDomain, modelChart, mem_inter_iff, mem_preimage, mem_compl_iff, mem_sdiff]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, fun h => h2 ⟨x, h, rfl⟩⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun ⟨y, hy, hyx⟩ => h2 (by rw [OnePoint.coe_eq_coe] at hyx; rw [← hyx]; exact hy)⟩

/-- U8 helper: the cap chart part of a set containing the closed exterior of `Q_L` and `∞` is `Q_1`. -/
theorem u8h_chartPart_true_eq {L : ℝ} (hL : 0 < L) {S : Set Sphere} (hinf : ∞ ∈ S)
    (hS : ∀ x : Plane, L ≤ supNorm x → (x : Sphere) ∈ S) : chartPart L true S = square 1 := by
  ext y
  simp only [chartPart, modelDomain, modelChart, mem_inter_iff, mem_preimage]
  refine ⟨fun h => h.1, fun hy => ⟨hy, ?_⟩⟩
  by_cases h0 : y = 0
  · subst h0; simpa [capChart] using hinf
  · simp only [capChart, h0, ↓reduceIte]
    apply hS
    rw [u3h_supNorm_capInvFun hL h0, le_div_iff₀ (u3h_supNorm_pos h0)]
    have : supNorm y ≤ 1 := hy
    nlinarith

/-- The exterior fan map: the annulus map on `Q_L`, the cap inverse (`capInvFun`) outside, `0` at `∞`. -/
noncomputable def u8h_gS {L : ℝ} (hL : 0 < L) (T₀ : Triangle) (hT : T₀.carrier ⊆ interior (square L)) :
    Sphere → Plane
  | ∞ => 0
  | (x : Plane) => if supNorm x ≤ L then u8h_g hL T₀ hT x else capInvFun L x

theorem u8h_gS_infty {L : ℝ} (hL : 0 < L) (T₀ : Triangle) (hT : T₀.carrier ⊆ interior (square L)) :
    u8h_gS hL T₀ hT ∞ = 0 := rfl

theorem u8h_gS_coe {L : ℝ} (hL : 0 < L) (T₀ : Triangle) (hT : T₀.carrier ⊆ interior (square L)) (x : Plane) :
    u8h_gS hL T₀ hT x = if supNorm x ≤ L then u8h_g hL T₀ hT x else capInvFun L x := rfl

theorem u8h_gS_coe_of_le {L : ℝ} (hL : 0 < L) (T₀ : Triangle) (hT : T₀.carrier ⊆ interior (square L))
    {x : Plane} (hx : supNorm x ≤ L) : u8h_gS hL T₀ hT x = u8h_g hL T₀ hT x := by
  rw [u8h_gS_coe, if_pos hx]

/-- Outside `int Q_L` the fan map is the cap inverse. -/
theorem u8h_gS_coe_of_ge {L : ℝ} (hL : 0 < L) (T₀ : Triangle) (hT : T₀.carrier ⊆ interior (square L))
    {x : Plane} (hx : L ≤ supNorm x) : u8h_gS hL T₀ hT x = capInvFun L x := by
  rw [u8h_gS_coe]
  split_ifs with h
  · have hxL : supNorm x = L := le_antisymm h hx
    rw [u8h_g_seam hL T₀ hT (u8h_mem_frontier_square.2 hxL), u8h_capInvFun_eq_ρ hL hxL]
  · rfl

theorem u8h_ρ_seam_inv {L : ℝ} (hL : 0 < L) (y : Plane) : u8h_ρ L (L • (y.1, -y.2)) = y := by
  ext <;> simp [u8h_ρ] <;> field_simp

/-- The fan map read in the cap chart is the identity. -/
theorem u8h_gS_capChart {L : ℝ} (hL : 0 < L) (T₀ : Triangle) (hT : T₀.carrier ⊆ interior (square L))
    {y : Plane} (hy : y ∈ square 1) : u8h_gS hL T₀ hT (capChart L y) = y := by
  by_cases h0 : y = 0
  · subst h0; simp [capChart, u8h_gS_infty]
  · have hy1 : supNorm y ≤ 1 := hy
    have hN := u3h_supNorm_pos h0
    have hge : L ≤ supNorm (capInvFun L y) := by
      rw [u3h_supNorm_capInvFun hL h0, le_div_iff₀ hN]; nlinarith
    simp only [capChart, h0, ↓reduceIte]
    rw [u8h_gS_coe_of_ge hL T₀ hT hge, u3h_capInvFun_capInvFun hL.ne' h0]

/-- The model exterior of `T₀`. -/
def u8h_E (T₀ : Triangle) : Set Sphere := (((↑) : Plane → Sphere) '' interior T₀.carrier)ᶜ

theorem u8h_infty_mem_E (T₀ : Triangle) : ∞ ∈ u8h_E T₀ := OnePoint.infty_notMem_image_coe

theorem u8h_coe_mem_E {T₀ : Triangle} {x : Plane} : (x : Sphere) ∈ u8h_E T₀ ↔ x ∉ interior T₀.carrier := by
  simp only [u8h_E, mem_compl_iff, mem_image, OnePoint.coe_eq_coe, exists_eq_right]

theorem u8h_coe_mem_E_of_ge {L : ℝ} (T₀ : Triangle) (hT : T₀.carrier ⊆ interior (square L)) {x : Plane}
    (hx : L ≤ supNorm x) : (x : Sphere) ∈ u8h_E T₀ := by
  rw [u8h_coe_mem_E]
  intro h
  have := (u8h_mem_interior_square_iff x).1 (hT (interior_subset h))
  linarith

/-- **The fan map is positive PL in the two model charts.** -/
theorem u8h_gS_isPositivePLToPlane {L : ℝ} (hL : 0 < L) (T₀ : Triangle) (hT : T₀.carrier ⊆ interior (square L)) :
    IsPositivePLToPlane L (u8h_E T₀) (u8h_gS hL T₀ hT) := by
  intro b
  cases b
  · -- plane chart: the annulus triangulation
    refine ⟨u8h_triangulation_congr (u8h_chartPart_false_exterior T₀).symm (u8h_K hL T₀ hT), fun T hT' => ?_⟩
    have hT'' : T ∈ (u8h_K hL T₀ hT).faces := hT'
    refine u3h_isPositiveAffineOn_congr (fun x hx => ?_) (u8h_g_isPositivePLOn hL T₀ hT T hT'')
    have hxs : x ∈ square L := (u3h_face_subset_chartPart (K := u8h_triangulation_congr
      (u8h_chartPart_false_exterior T₀).symm (u8h_K hL T₀ hT)) hT' hx).1
    show u8h_g hL T₀ hT x = u8h_gS hL T₀ hT x
    rw [u8h_gS_coe_of_le hL T₀ hT hxs]
  · -- cap chart: the identity
    have hset : square 1 = chartPart L true (u8h_E T₀) := by
      rw [u8h_chartPart_true_eq hL (u8h_infty_mem_E T₀) (fun x hx => u8h_coe_mem_E_of_ge T₀ hT hx)]
    obtain ⟨K⟩ := U2_triangulation_square (one_pos : (0 : ℝ) < 1)
    refine ⟨u8h_triangulation_congr hset K, fun T hT' => ?_⟩
    refine u3h_isPositiveAffineOn_congr (fun x hx => ?_) (u8h_isPositiveAffineOn_id T)
    have hxs : x ∈ square 1 := (u3h_face_subset_chartPart (K := u8h_triangulation_congr hset K) hT' hx).1
    show x = u8h_gS hL T₀ hT (capChart L x)
    rw [u8h_gS_capChart hL T₀ hT hxs]

/-- **The boundary clause**: `∂T₀ ↦ ∂Q_2`. -/
theorem u8h_gS_frontier {L : ℝ} (hL : 0 < L) (T₀ : Triangle) (hT : T₀.carrier ⊆ interior (square L)) :
    u8h_gS hL T₀ hT '' (((↑) : Plane → Sphere) '' frontier T₀.carrier) = frontier (square 2) := by
  rw [← u8h_g_frontier hL T₀ hT, ← image_comp]
  apply image_congr
  intro x hx
  have hxs : x ∈ square L := interior_subset (hT (T₀.carrier |> fun _ =>
    (U1_triangle_isCompact T₀).isClosed.frontier_subset hx))
  exact u8h_gS_coe_of_le hL T₀ hT hxs


/-! ### U8 helpers: compactness builder for `IsHomeoOnto`, continuity of the cap inverse -/

theorem u8h_continuousOn_of_isHomeoOnto {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    {S : Set α} {S' : Set β} {f : α → β} (h : IsHomeoOnto S S' f) : ContinuousOn f S := by
  obtain ⟨e, he⟩ := h
  rw [continuousOn_iff_continuous_restrict]
  exact (continuous_subtype_val.comp e.continuous).congr fun x => he x

/-- A continuous injection of a compact set onto a set of a T₂ space is `IsHomeoOnto`. -/
theorem u8h_isHomeoOnto_of_compact {α β : Type*} [TopologicalSpace α] [TopologicalSpace β] [T2Space β]
    {S : Set α} {S' : Set β} {f : α → β} (hS : IsCompact S) (hf : ContinuousOn f S) (hinj : InjOn f S)
    (himg : f '' S = S') : IsHomeoOnto S S' f := by
  have : CompactSpace S := isCompact_iff_compactSpace.mp hS
  have hc : Continuous (Equiv.Set.imageOfInjOn f S hinj) := by
    apply Continuous.subtype_mk
    exact hf.restrict
  refine ⟨(hc.homeoOfEquivCompactToT2).trans (Homeomorph.setCongr himg), fun z => rfl⟩

/-- The closed cap `coe '' {L ≤ ‖x‖_∞} ∪ {∞}` is closed. -/
theorem u8h_isClosed_cap {L : ℝ} :
    IsClosed (((↑) : Plane → Sphere) '' {x | L ≤ supNorm x} ∪ {∞}) := by
  have : ((↑) : Plane → Sphere) '' {x | L ≤ supNorm x} ∪ {∞} = (((↑) : Plane → Sphere) '' {x | supNorm x < L})ᶜ := by
    ext z
    induction z using OnePoint.rec with
    | infty => simp
    | coe x =>
      simp only [mem_union, mem_image, OnePoint.coe_eq_coe, exists_eq_right, mem_setOf_eq,
        mem_singleton_iff, mem_compl_iff, not_lt]
      constructor
      · rintro (h | h)
        · exact h
        · exact absurd h (OnePoint.coe_ne_infty x)
      · exact Or.inl
  rw [this]
  exact (OnePoint.isOpen_image_coe.2 (isOpen_lt u8h_continuous_supNorm continuous_const)).isClosed_compl

/-- The closed annulus `Q_L \ int T₀` is compact. -/
theorem u8h_isCompact_annulus {L : ℝ} (hL : 0 < L) (T₀ : Triangle) :
    IsCompact (square L \ interior T₀.carrier) :=
  (U1_square_isDisc hL).2.1.of_isClosed_subset
    ((isClosed_le u8h_continuous_supNorm continuous_const).inter isOpen_interior.isClosed_compl)
    sdiff_subset

/-- U8 (chart algebra, PLAN_FINAL §4): the sup-norm inversion is an involution off `0`. -/
theorem U8_capInvFun_capInvFun {L : ℝ} (hL : 0 < L) {y : Plane} (hy : y ≠ 0) :
    capInvFun L (capInvFun L y) = y := by
  exact u3h_capInvFun_capInvFun hL.ne' hy

/-- U8: `‖capInvFun L y‖_∞ = L / ‖y‖_∞`. -/
theorem U8_supNorm_capInvFun {L : ℝ} (hL : 0 < L) {y : Plane} (hy : y ≠ 0) :
    supNorm (capInvFun L y) = L / supNorm y := by
  exact u3h_supNorm_capInvFun hL hy

/-- U8 (sm-3:448-456 "the actual one-point-compactified exterior"): the cap chart is a homeomorphism
of `Q_1` onto the closed exterior of `Q_L` together with `∞`. -/
theorem U8_capChart_isHomeoOnto {L : ℝ} (hL : 0 < L) :
    IsHomeoOnto (square 1) (((↑) : Plane → Sphere) '' {x | L ≤ supNorm x} ∪ {∞}) (capChart L) := by
  refine u1h_isHomeoOnto_of_inv (g := modelChartInv L true) (u8h_continuousOn_capChart hL) ?_ ?_ ?_
    (fun y _ => u3h_chartInv_chart hL.ne' true y) ?_
  · intro z hz
    apply ContinuousAt.continuousWithinAt
    apply u8h_continuous_capInv hL
    rcases hz with ⟨x, hx, rfl⟩ | hz
    · intro h
      rw [OnePoint.coe_eq_coe] at h
      subst h
      simp only [mem_ofPred_eq, supNorm, Prod.fst_zero, Prod.snd_zero, abs_zero, max_self] at hx
      linarith
    · rw [mem_singleton_iff] at hz; subst hz; exact OnePoint.infty_ne_coe _
  · intro y hy
    by_cases h0 : y = 0
    · subst h0; right; simp [capChart]
    · left
      refine ⟨capInvFun L y, ?_, by simp [capChart, h0]⟩
      show L ≤ supNorm (capInvFun L y)
      rw [u3h_supNorm_capInvFun hL h0]
      have hN := u3h_supNorm_pos h0
      rw [le_div_iff₀ hN]
      have : supNorm y ≤ 1 := hy
      nlinarith
  · rintro z (⟨x, hx, rfl⟩ | hz)
    · show supNorm (capInvFun L x) ≤ 1
      have hx0 : x ≠ 0 := by
        rintro rfl
        simp only [mem_ofPred_eq, supNorm, Prod.fst_zero, Prod.snd_zero, abs_zero, max_self] at hx
        linarith
      rw [u3h_supNorm_capInvFun hL hx0, div_le_one (u3h_supNorm_pos hx0)]
      exact hx
    · rw [mem_singleton_iff] at hz; subst hz
      show supNorm 0 ≤ 1
      simp [supNorm]
  · rintro z (⟨x, hx, rfl⟩ | hz)
    · have hx0 : x ≠ 0 := by
        rintro rfl
        simp only [mem_ofPred_eq, supNorm, Prod.fst_zero, Prod.snd_zero, abs_zero, max_self] at hx
        linarith
      show capChart L (capInvFun L x) = (x : Sphere)
      simp [capChart, u3h_capInvFun_ne_zero hL hx0, u3h_capInvFun_capInvFun hL.ne' hx0]
    · rw [mem_singleton_iff] at hz; subst hz
      show capChart L 0 = ∞
      simp [capChart]

/-- U8: on the seam `‖y‖_∞ = 1` the cap chart is the affine map `y ↦ L • (y₁, −y₂)`. -/
theorem U8_capInvFun_seam {L : ℝ} {y : Plane} (hy : supNorm y = 1) :
    capInvFun L y = L • (y.1, -y.2) := by
  exact u3h_capInvFun_seam hy

/-! ### U8: the exterior fan map is a homeomorphism onto `Q_2` -/

theorem u8h_cap_eq {L : ℝ} (hL : 0 < L) :
    capChart L '' square 1 = ((↑) : Plane → Sphere) '' {x | L ≤ supNorm x} ∪ {∞} :=
  u1h_isHomeoOnto_image (U8_capChart_isHomeoOnto hL)

theorem u8h_notMem_interior_of_ge {L : ℝ} (T₀ : Triangle) (hT : T₀.carrier ⊆ interior (square L))
    {x : Plane} (hx : L ≤ supNorm x) : x ∉ interior T₀.carrier := by
  intro h
  have := (u8h_mem_interior_square_iff x).1 (hT (interior_subset h))
  linarith

/-- The model exterior is the union of the closed annulus and the closed cap. -/
theorem u8h_E_eq {L : ℝ} (T₀ : Triangle) (hT : T₀.carrier ⊆ interior (square L)) :
    u8h_E T₀ = ((↑) : Plane → Sphere) '' (square L \ interior T₀.carrier) ∪
      (((↑) : Plane → Sphere) '' {x | L ≤ supNorm x} ∪ {∞}) := by
  ext z
  induction z using OnePoint.rec with
  | infty => simp [u8h_infty_mem_E]
  | coe x =>
    rw [u8h_coe_mem_E]
    simp only [mem_union, mem_image, OnePoint.coe_eq_coe, exists_eq_right, mem_sdiff, mem_setOf_eq,
      mem_singleton_iff]
    constructor
    · intro h
      by_cases hx : supNorm x ≤ L
      · exact Or.inl ⟨hx, h⟩
      · push Not at hx; exact Or.inr (Or.inl hx.le)
    · rintro (⟨-, h⟩ | (h | h))
      · exact h
      · exact u8h_notMem_interior_of_ge T₀ hT h
      · exact absurd h (OnePoint.coe_ne_infty x)

theorem u8h_gS_continuousOn {L : ℝ} (hL : 0 < L) (T₀ : Triangle) (hT : T₀.carrier ⊆ interior (square L)) :
    ContinuousOn (u8h_gS hL T₀ hT) (u8h_E T₀) := by
  rw [u8h_E_eq T₀ hT]
  apply ContinuousOn.union_of_isClosed
  · have hA : ContinuousOn (u8h_g hL T₀ hT) (square L \ interior T₀.carrier) :=
      U2_continuousOn_of_isPositivePLOn (u8h_K hL T₀ hT) (u8h_g_isPositivePLOn hL T₀ hT)
    have hpl : ContinuousOn planeOf (((↑) : Plane → Sphere) '' (square L \ interior T₀.carrier)) :=
      u8h_continuousOn_of_isHomeoOnto (U1_isHomeoOnto_inv (U1_isHomeoOnto_coe _) (fun x _ => rfl))
    have hmaps : MapsTo planeOf (((↑) : Plane → Sphere) '' (square L \ interior T₀.carrier))
        (square L \ interior T₀.carrier) := by rintro _ ⟨x, hx, rfl⟩; exact hx
    refine (hA.comp hpl hmaps).congr ?_
    rintro _ ⟨x, hx, rfl⟩
    show u8h_gS hL T₀ hT x = u8h_g hL T₀ hT (planeOf x)
    rw [u8h_gS_coe_of_le hL T₀ hT hx.1]; rfl
  · have hcont : ContinuousOn (modelChartInv L true)
        (((↑) : Plane → Sphere) '' {x | L ≤ supNorm x} ∪ {∞}) := by
      intro z hz
      apply ContinuousAt.continuousWithinAt
      apply u8h_continuous_capInv hL
      rcases hz with ⟨x, hx, rfl⟩ | hz
      · intro h
        rw [OnePoint.coe_eq_coe] at h
        subst h
        simp only [mem_setOf_eq, supNorm, Prod.fst_zero, Prod.snd_zero, abs_zero, max_self] at hx
        linarith
      · rw [mem_singleton_iff] at hz; subst hz; exact OnePoint.infty_ne_coe _
    refine hcont.congr ?_
    rintro z (⟨x, hx, rfl⟩ | hz)
    · show u8h_gS hL T₀ hT x = capInvFun L x
      exact u8h_gS_coe_of_ge hL T₀ hT hx
    · rw [mem_singleton_iff] at hz; subst hz; rfl
  · exact OnePoint.isClosed_image_coe.2
      ⟨(isClosed_le u8h_continuous_supNorm continuous_const).inter isOpen_interior.isClosed_compl,
        u8h_isCompact_annulus hL T₀⟩
  · exact u8h_isClosed_cap

theorem u8h_gS_image_cap {L : ℝ} (hL : 0 < L) (T₀ : Triangle) (hT : T₀.carrier ⊆ interior (square L)) :
    u8h_gS hL T₀ hT '' (((↑) : Plane → Sphere) '' {x | L ≤ supNorm x} ∪ {∞}) = square 1 := by
  rw [← u8h_cap_eq hL, ← image_comp]
  apply Subset.antisymm
  · rintro _ ⟨y, hy, rfl⟩
    show u8h_gS hL T₀ hT (capChart L y) ∈ square 1
    rw [u8h_gS_capChart hL T₀ hT hy]; exact hy
  · intro y hy; exact ⟨y, hy, u8h_gS_capChart hL T₀ hT hy⟩

theorem u8h_gS_image_annulus {L : ℝ} (hL : 0 < L) (T₀ : Triangle) (hT : T₀.carrier ⊆ interior (square L)) :
    u8h_gS hL T₀ hT '' (((↑) : Plane → Sphere) '' (square L \ interior T₀.carrier)) =
      square 2 \ interior (square 1) := by
  rw [← image_comp, ← (u8h_g_bij hL T₀ hT).2]
  apply image_congr
  intro x hx
  exact u8h_gS_coe_of_le hL T₀ hT hx.1

theorem u8h_gS_image {L : ℝ} (hL : 0 < L) (T₀ : Triangle) (hT : T₀.carrier ⊆ interior (square L)) :
    u8h_gS hL T₀ hT '' u8h_E T₀ = square 2 := by
  rw [u8h_E_eq T₀ hT, image_union, u8h_gS_image_cap hL T₀ hT, u8h_gS_image_annulus hL T₀ hT]
  ext x
  simp only [mem_union, mem_sdiff]
  constructor
  · rintro (⟨h, -⟩ | h)
    · exact h
    · show supNorm x ≤ 2
      have : supNorm x ≤ 1 := h
      linarith
  · intro h
    by_cases hx : x ∈ square 1
    · exact Or.inr hx
    · exact Or.inl ⟨h, fun hi => hx (interior_subset hi)⟩

/-- A cap point whose image is not in `int Q_1` lies on the seam, hence in the closed annulus. -/
theorem u8h_cap_seam_case {L : ℝ} (hL : 0 < L) (T₀ : Triangle) (hT : T₀.carrier ⊆ interior (square L))
    {z : Sphere} (hz : z ∈ ((↑) : Plane → Sphere) '' {x | L ≤ supNorm x} ∪ {∞})
    (hg : u8h_gS hL T₀ hT z ∉ interior (square 1)) :
    z ∈ ((↑) : Plane → Sphere) '' (square L \ interior T₀.carrier) := by
  rw [← u8h_cap_eq hL] at hz
  obtain ⟨y, hy, rfl⟩ := hz
  rw [u8h_gS_capChart hL T₀ hT hy, u8h_mem_interior_square_iff, not_lt] at hg
  have hy1 : supNorm y = 1 := le_antisymm hy hg
  have hy0 : y ≠ 0 := by rintro rfl; simp [supNorm] at hy1
  have hx : supNorm (capInvFun L y) = L := by rw [u3h_supNorm_capInvFun hL hy0, hy1, div_one]
  refine ⟨capInvFun L y, ⟨hx.le, u8h_notMem_interior_of_ge T₀ hT hx.ge⟩, ?_⟩
  simp [capChart, hy0]

theorem u8h_gS_injOn {L : ℝ} (hL : 0 < L) (T₀ : Triangle) (hT : T₀.carrier ⊆ interior (square L)) :
    InjOn (u8h_gS hL T₀ hT) (u8h_E T₀) := by
  have hbij := u8h_g_bij hL T₀ hT
  have hann : ∀ z ∈ ((↑) : Plane → Sphere) '' (square L \ interior T₀.carrier),
      ∀ z' ∈ ((↑) : Plane → Sphere) '' (square L \ interior T₀.carrier),
        u8h_gS hL T₀ hT z = u8h_gS hL T₀ hT z' → z = z' := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨x', hx', rfl⟩ heq
    rw [u8h_gS_coe_of_le hL T₀ hT hx.1, u8h_gS_coe_of_le hL T₀ hT hx'.1] at heq
    rw [hbij.1 hx hx' heq]
  have hannB : ∀ z ∈ ((↑) : Plane → Sphere) '' (square L \ interior T₀.carrier),
      u8h_gS hL T₀ hT z ∉ interior (square 1) := by
    rintro _ ⟨x, hx, rfl⟩
    rw [u8h_gS_coe_of_le hL T₀ hT hx.1]
    have : u8h_g hL T₀ hT x ∈ square 2 \ interior (square 1) := hbij.2 ▸ ⟨x, hx, rfl⟩
    exact this.2
  intro z hz z' hz' heq
  rw [u8h_E_eq T₀ hT] at hz hz'
  rcases hz with hz | hz <;> rcases hz' with hz' | hz'
  · exact hann z hz z' hz' heq
  · exact hann z hz z' (u8h_cap_seam_case hL T₀ hT hz' (heq ▸ hannB z hz)) heq
  · exact hann z (u8h_cap_seam_case hL T₀ hT hz (heq ▸ hannB z' hz')) z' hz' heq
  · rw [← u8h_cap_eq hL] at hz hz'
    obtain ⟨y, hy, rfl⟩ := hz
    obtain ⟨y', hy', rfl⟩ := hz'
    rw [u8h_gS_capChart hL T₀ hT hy, u8h_gS_capChart hL T₀ hT hy'] at heq
    rw [heq]

theorem u8h_isCompact_E (T₀ : Triangle) : IsCompact (u8h_E T₀) :=
  (OnePoint.isOpen_image_coe.2 isOpen_interior).isClosed_compl.isCompact

/-- **The exterior fan map is a homeomorphism of the model exterior onto `Q_2`.** -/
theorem u8h_gS_isHomeoOnto {L : ℝ} (hL : 0 < L) (T₀ : Triangle) (hT : T₀.carrier ⊆ interior (square L)) :
    IsHomeoOnto (u8h_E T₀) (square 2) (u8h_gS hL T₀ hT) :=
  u8h_isHomeoOnto_of_compact (u8h_isCompact_E T₀) (u8h_gS_continuousOn hL T₀ hT) (u8h_gS_injOn hL T₀ hT)
    (u8h_gS_image hL T₀ hT)

/-- U8 (the 11-ray fan, PLAN_FINAL §3.3): the model exterior `Sphere \ int T₀` of a triangle inside
`int Q_L` is carried onto the square `Q_2` by a homeomorphism that is positive PL in the two model
charts and sends `∂T₀` onto `∂Q_2`. -/
theorem U8_exists_exterior_fan {L : ℝ} (hL : 0 < L) (T₀ : Triangle)
    (hT : T₀.carrier ⊆ interior (square L)) :
    ∃ g : Sphere → Plane,
      IsHomeoOnto (((↑) : Plane → Sphere) '' interior T₀.carrier)ᶜ (square 2) g ∧
      IsPositivePLToPlane L (((↑) : Plane → Sphere) '' interior T₀.carrier)ᶜ g ∧
      g '' (((↑) : Plane → Sphere) '' frontier T₀.carrier) = frontier (square 2) := by
  exact ⟨u8h_gS hL T₀ hT, u8h_gS_isHomeoOnto hL T₀ hT, u8h_gS_isPositivePLToPlane hL T₀ hT,
    u8h_gS_frontier hL T₀ hT⟩

/-- U8: the closed exterior region is the sphere minus the open image triangle. -/
theorem U8_closure_exteriorRegion_eq [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Embedded P)
    {L : ℝ} (A : AmbientParam P L) :
    closure (exteriorRegion P) = (((↑) : Plane → Sphere) '' (A.H '' interior A.T₀.carrier))ᶜ := by
  have hext := U6_exteriorRegion_eq hn P hP A
  have hopen : IsOpen (((↑) : Plane → Sphere) '' (A.H '' interior A.T₀.carrier)) :=
    OnePoint.isOpen_image_coe.2 (A.H.isOpenMap _ isOpen_interior)
  apply Subset.antisymm
  · apply closure_minimal _ hopen.isClosed_compl
    rw [hext]
    rintro z (⟨_, ⟨x, hx, rfl⟩, rfl⟩ | hz)
    · rintro ⟨_, ⟨x', hx', rfl⟩, h⟩
      rw [OnePoint.coe_eq_coe] at h
      have := A.H.injective h
      subst this
      exact hx (interior_subset hx')
    · rw [mem_singleton_iff] at hz; subst hz
      exact OnePoint.infty_notMem_image_coe
  · intro z hz
    induction z using OnePoint.rec with
    | infty => exact subset_closure (by rw [hext]; exact Or.inr rfl)
    | coe y =>
      have hy : y ∉ A.H '' interior A.T₀.carrier := fun h => hz ⟨y, h, rfl⟩
      have hy' : A.H.symm y ∈ closure (A.T₀.carrier)ᶜ := by
        rw [closure_compl]
        intro h; apply hy
        exact ⟨A.H.symm y, h, A.H.apply_symm_apply y⟩
      have h2 : y ∈ closure (A.H '' (A.T₀.carrier)ᶜ) := by
        rw [← A.H.image_closure]
        exact ⟨A.H.symm y, hy', A.H.apply_symm_apply y⟩
      have h3 : ((y : Plane) : Sphere) ∈ closure (((↑) : Plane → Sphere) '' (A.H '' (A.T₀.carrier)ᶜ)) :=
        image_closure_subset_closure_image OnePoint.continuous_coe ⟨y, h2, rfl⟩
      refine closure_mono ?_ h3
      rw [hext]; exact subset_union_left

theorem u8h_closure_ext_mem_coe [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Embedded P)
    {L : ℝ} (A : AmbientParam P L) {x : Plane} (hx : L ≤ supNorm x) :
    (x : Sphere) ∈ closure (exteriorRegion P) := by
  rw [U8_closure_exteriorRegion_eq hn P hP A]
  rintro ⟨_, ⟨w, hw, rfl⟩, h⟩
  rw [OnePoint.coe_eq_coe] at h
  have : A.H w ∈ interior (square L) := by
    rw [← u8h_H_image_interior A]; exact ⟨w, A.inside (interior_subset hw), rfl⟩
  rw [h, u8h_mem_interior_square_iff] at this
  linarith

/-- U8: `H⁻¹` extended by the identity at `∞` is a positive PL sphere map (model `L` to model `L`)
on the closed exterior region. -/
theorem U8_isPositivePLSphereMap_inv [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Embedded P)
    {L : ℝ} (hL : InsideModel L P) (A : AmbientParam P L) :
    IsPositivePLSphereMap L L (closure (exteriorRegion P)) (OnePoint.map A.H.symm) ∧
      IsHomeoOnto (closure (exteriorRegion P)) (((↑) : Plane → Sphere) '' interior A.T₀.carrier)ᶜ
        (OnePoint.map A.H.symm) := by
  have hL0 : 0 < L := lt_of_le_of_lt (u3h_supNorm_nonneg _) (hL 0)
  have hcl := U8_closure_exteriorRegion_eq hn P hP A
  set F := OnePoint.map A.H.symm with hF
  have himg : F '' closure (exteriorRegion P) = (((↑) : Plane → Sphere) '' interior A.T₀.carrier)ᶜ := by
    rw [hcl, Set.image_compl_eq (u8h_onePoint_map_bijective _), u8h_onePoint_map_image_coe]
    have hss : A.H.symm '' (A.H '' interior A.T₀.carrier) = interior A.T₀.carrier := by
      ext v; constructor
      · rintro ⟨_, ⟨u, hu, rfl⟩, rfl⟩; simpa using hu
      · intro hv; exact ⟨A.H v, ⟨v, hv, rfl⟩, A.H.symm_apply_apply v⟩
    rw [hss]
  constructor
  · intro b
    cases b
    · -- plane chart
      obtain ⟨g, -, hpl, -⟩ := U8_exists_exterior_fan hL0 A.T₀ A.inside
      obtain ⟨K₀, -⟩ := hpl false
      rw [u8h_chartPart_false_exterior] at K₀
      obtain ⟨K₁, hK₁, hfaces⟩ := U3_refine_into K₀ A.K sdiff_subset
      have hH : IsPositivePLOn A.H K₁ := by
        intro T hT
        obtain ⟨T', hT', hsub⟩ := hfaces T hT
        exact U1_isPositiveAffineOn_mono (A.pl T' hT') hsub
      obtain ⟨K₂, hK₂⟩ := U2_inverse_isPositivePLOn K₁ A.H hH
      have hset : A.H '' (square L \ interior A.T₀.carrier) =
          chartPart L false (closure (exteriorRegion P)) := by
        rw [hcl, Set.image_sdiff A.H.injective, u8h_H_image_square]
        ext x
        simp only [chartPart, modelDomain, modelChart, mem_inter_iff, mem_preimage, mem_compl_iff, mem_sdiff]
        constructor
        · rintro ⟨h1, h2⟩; exact ⟨h1, fun ⟨y, hy, hyx⟩ => h2 (by rw [OnePoint.coe_eq_coe] at hyx; rw [← hyx]; exact hy)⟩
        · rintro ⟨h1, h2⟩; exact ⟨h1, fun h => h2 ⟨x, h, rfl⟩⟩
      refine ⟨u8h_triangulation_congr hset K₂, fun T hT => ⟨false, fun x hx => ?_, ?_⟩⟩
      · have hxs : x ∈ square L := by
          have := u3h_face_subset_chartPart (u8h_triangulation_congr hset K₂) hT hx
          exact this.1
        refine ⟨A.H.symm x, ?_, rfl⟩
        rw [← u8h_H_image_square A] at hxs
        obtain ⟨w, hw, rfl⟩ := hxs
        rw [A.H.symm_apply_apply]; exact hw
      · exact u3h_isPositiveAffineOn_congr (fun x _ => rfl) (hK₂ T hT)
    · -- cap chart
      have hset : square 1 = chartPart L true (closure (exteriorRegion P)) := by
        rw [u8h_chartPart_true_eq hL0]
        · exact subset_closure (by rw [exteriorRegion]; exact mem_connectedComponentIn (by
            show ∞ ∉ sphereCircle P; exact OnePoint.infty_notMem_image_coe))
        · exact fun x hx => u8h_closure_ext_mem_coe hn P hP A hx
      obtain ⟨K⟩ := U2_triangulation_square (one_pos : (0 : ℝ) < 1)
      refine ⟨u8h_triangulation_congr hset K, fun T hT => ⟨true, fun x hx => ?_, ?_⟩⟩
      · have hxs : x ∈ square 1 := u3h_face_subset_chartPart (u8h_triangulation_congr hset K) hT hx |>.1
        refine ⟨x, hxs, ?_⟩
        show capChart L x = F (capChart L x)
        by_cases h0 : x = 0
        · subst h0; simp [capChart, F]
        · simp only [capChart, h0, ↓reduceIte, F, OnePoint.map_some]
          rw [u8h_H_symm_fix A]
          rw [u3h_supNorm_capInvFun hL0 h0, le_div_iff₀ (u3h_supNorm_pos h0)]
          have : supNorm x ≤ 1 := hxs
          nlinarith
      · refine u3h_isPositiveAffineOn_congr (fun x hx => ?_) (u8h_isPositiveAffineOn_id T)
        have hxs : x ∈ square 1 := u3h_face_subset_chartPart (u8h_triangulation_congr hset K) hT hx |>.1
        show x = modelChartInv L true (F (capChart L x))
        by_cases h0 : x = 0
        · subst h0; simp [capChart, F, modelChartInv]
        · have hfix : A.H.symm (capInvFun L x) = capInvFun L x := by
            rw [u8h_H_symm_fix A]
            rw [u3h_supNorm_capInvFun hL0 h0, le_div_iff₀ (u3h_supNorm_pos h0)]
            have : supNorm x ≤ 1 := hxs
            nlinarith
          simp only [capChart, h0, ↓reduceIte, F, OnePoint.map_some, hfix]
          show x = capInvFun L (capInvFun L x)
          rw [u3h_capInvFun_capInvFun hL0.ne' h0]
  · rw [← himg]
    exact u8h_isHomeoOnto_onePoint_map A.H.symm _

/-- U8 (57b exterior, sm-3:431 / 448-456 / 490-493): the closure of the exterior region is a PL disc
of the sphere with boundary the circle. -/
theorem U8_pl_discs_outer [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Embedded P) (L : ℝ)
    (hL : InsideModel L P) : IsPLDiscSphere L (closure (regionOf P Side.outer)) (sphereCircle P) := by
  have hL0 : 0 < L := lt_of_le_of_lt (u3h_supNorm_nonneg _) (hL 0)
  obtain ⟨A⟩ := U6_exists_ambientParam hn P hP hL
  obtain ⟨g, hg1, hg2, hg3⟩ := U8_exists_exterior_fan hL0 A.T₀ A.inside
  obtain ⟨hF1, hF2⟩ := U8_isPositivePLSphereMap_inv hn P hP hL A
  have hcl := U8_closure_exteriorRegion_eq hn P hP A
  show IsPLDiscSphere L (closure (exteriorRegion P)) (sphereCircle P)
  have hFimg : OnePoint.map A.H.symm '' closure (exteriorRegion P) =
      (((↑) : Plane → Sphere) '' interior A.T₀.carrier)ᶜ := u1h_isHomeoOnto_image hF2
  have hcirc : sphereCircle P = ((↑) : Plane → Sphere) '' (A.H '' frontier A.T₀.carrier) := by
    rw [sphereCircle, A.boundary]
  refine ⟨square 2, g ∘ OnePoint.map A.H.symm, U1_square_isDisc two_pos, ?_, ?_, ?_, ?_⟩
  · rw [hcirc, hcl]
    rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩ ⟨_, ⟨y, hy, rfl⟩, h⟩
    rw [OnePoint.coe_eq_coe] at h
    have := A.H.injective h
    subst this
    exact hx.2 hy
  · exact U1_isHomeoOnto_comp hF2 hg1
  · rw [image_comp, hcirc, u8h_onePoint_map_image_coe, ← hg3]
    congr 2
    ext v; constructor
    · rintro ⟨_, ⟨u, hu, rfl⟩, rfl⟩; simpa using hu
    · intro hv; exact ⟨A.H v, ⟨v, hv, rfl⟩, A.H.symm_apply_apply v⟩
  · exact U3_isPositivePLToPlane_comp hF1 hFimg.le hg2

/-! ### U9 (sequential) — orientation bookkeeping (FR-TD-9) -/

/-- U9: the left normal `(−u₂, u₁)` of a direction `u`. -/
def leftNormal (u : Plane) : Plane := (-u.2, u.1)

/-- U9: the bounded region lies on the left of edge `i` (a short left normal from the midpoint of
the edge enters the interior region). -/
def InteriorOnLeft [NeZero n] (P : LabelledTuple n) (i : ZMod n) : Prop :=
  ∃ ε > 0, ∀ t ∈ Ioo (0 : ℝ) ε,
    (((1 / 2 : ℝ) • (P i + P (i + 1)) + t • leftNormal (edge P i) : Plane) : Sphere) ∈ interiorRegion P

/-- U9: `b` lies strictly between `a` and `c` in the counterclockwise cyclic order around `z`
(two-of-three `det` signs). -/
def CyclicPos (z a b c : Plane) : Prop :=
  (0 < det (a - z) (b - z) ∧ 0 < det (b - z) (c - z)) ∨
  (0 < det (b - z) (c - z) ∧ 0 < det (c - z) (a - z)) ∨
  (0 < det (c - z) (a - z) ∧ 0 < det (a - z) (b - z))

/-- U9: "interior on the left of edge `i`" is the sign of the face of the ear triangulation adjacent
to that edge; it is the same for all edges (consistency along the ear induction). -/
theorem U9_interiorOnLeft_consistent [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Embedded P)
    (i j : ZMod n) : InteriorOnLeft P i ↔ InteriorOnLeft P j := by
  sorry

/-- U9 (sm-3:4762-4764 read at a supporting vertex): at a supporting vertex with nonzero turn the
interior is on the left iff the turn is positive. -/
theorem U9_interiorOnLeft_iff_turn [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Embedded P)
    {N : Plane} {i : ZMod n} (hs : IsSupportingVertex P N i) (ht : principalTurn P i ≠ 0) :
    InteriorOnLeft P i ↔ 0 < principalTurn P i := by
  sorry

/-- U9 (with `cb_embedded_rotation.orientation`): the interior is on the left of the traversal iff
the rotation number is positive. -/
theorem U9_interiorOnLeft_iff_rotation [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Embedded P)
    (i : ZMod n) : InteriorOnLeft P i ↔ 0 < rotationNumber P := by
  sorry

/-- U9 (the convention of `traversalPositiveFor`, FR-TD-9): a positive PL parametrisation `f` of the
closed region `s` onto a convex model `D` carries the traversal, read around an interior point `z`,
to the counterclockwise cyclic order exactly when `traversalPositiveFor P s`. -/
theorem U9_traversalPositiveFor_iff_cyclicPos [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n)
    (hP : Embedded P) (s : Side) {L : ℝ} (hL : InsideModel L P) {D : Set Plane} {f : Sphere → Plane}
    (hD : Link.IsDisc D) (hf : IsHomeoOnto (closure (regionOf P s)) D f)
    (hB : f '' sphereCircle P = frontier D) (hpl : IsPositivePLToPlane L (closure (regionOf P s)) f)
    {z : Plane} (hz : z ∈ interior D) {x y w : ℝ} (hxy : x < y) (hyw : y < w) (hwx : w < x + n) :
    traversalPositiveFor P s ↔
      CyclicPos z (f ((traversal P x : Plane) : Sphere)) (f ((traversal P y : Plane) : Sphere))
        (f ((traversal P w : Plane) : Sphere)) := by
  sorry

/-- U9 (positivity of the boundary map, sm-3:431-434 "positive"): a positive boundary lift, read in
two positive parametrisations, preserves the counterclockwise cyclic order. -/
theorem U9_lift_preserves_cyclicPos [NeZero n] {n' : ℕ} [NeZero n'] (hn : 3 ≤ n) (P : LabelledTuple n)
    (hP : Embedded P) (hn' : 3 ≤ n') (P' : LabelledTuple n') (hP' : Embedded P') (s s' : Side)
    {L L' : ℝ} (hL : InsideModel L P) (hL' : InsideModel L' P') {D D' : Set Plane}
    {f f' : Sphere → Plane} (hD : Link.IsDisc D) (hD' : Link.IsDisc D')
    (hf : IsHomeoOnto (closure (regionOf P s)) D f) (hf' : IsHomeoOnto (closure (regionOf P' s')) D' f')
    (hB : f '' sphereCircle P = frontier D) (hB' : f' '' sphereCircle P' = frontier D')
    (hpl : IsPositivePLToPlane L (closure (regionOf P s)) f)
    (hpl' : IsPositivePLToPlane L' (closure (regionOf P' s')) f')
    {z z' : Plane} (hz : z ∈ interior D) (hz' : z' ∈ interior D') {φ : ℝ → ℝ}
    (hφ : IsPositiveBoundaryLift P s P' s' φ) {x y w : ℝ} (hxy : x < y) (hyw : y < w) (hwx : w < x + n)
    (h : CyclicPos z (f ((traversal P x : Plane) : Sphere)) (f ((traversal P y : Plane) : Sphere))
      (f ((traversal P w : Plane) : Sphere))) :
    CyclicPos z' (f' ((traversal P' (φ x) : Plane) : Sphere)) (f' ((traversal P' (φ y) : Plane) : Sphere))
      (f' ((traversal P' (φ w) : Plane) : Sphere)) := by
  sorry

/-! ### U10 (lane C convex model, then sequential) — 57c -/

/-- U10: `β` is finite PL on the frontier of `D`: affine on each of finitely many segments covering
`frontier D`. -/
def IsFinitePLOnFrontier (D : Set Plane) (β : Plane → Plane) : Prop :=
  ∃ s : Finset (Plane × Plane), (⋃ p ∈ s, segment ℝ p.1 p.2) = frontier D ∧
    ∀ p ∈ s, AffineOn β (segment ℝ p.1 p.2)

/-- U10: `β` preserves the counterclockwise cyclic order of `frontier D` around `z` (to that of
`frontier D'` around `z'`). -/
def PreservesCyclicPos (D : Set Plane) (z z' : Plane) (β : Plane → Plane) : Prop :=
  ∀ a ∈ frontier D, ∀ b ∈ frontier D, ∀ c ∈ frontier D,
    CyclicPos z a b c → CyclicPos z' (β a) (β b) (β c)

/-! #### U10 helpers for `U10_fan_extension` (radial gauge, sectors, marks, fan, cone) -/

/-- U10 helper: the translate of `D` bringing `z` to the origin. -/
def u10h_D0 (D : Set Plane) (z : Plane) : Set Plane := (Homeomorph.addRight z) ⁻¹' D

/-- U10 helper: the radial gauge of `D` about `z`. -/
noncomputable def u10h_rg (D : Set Plane) (z : Plane) (x : Plane) : ℝ := gauge (u10h_D0 D z) (x - z)

theorem u10h_mem_D0 {D : Set Plane} {z w : Plane} : w ∈ u10h_D0 D z ↔ w + z ∈ D := Iff.rfl

theorem u10h_D0_convex {D : Set Plane} (hD : Link.IsDisc D) (z : Plane) : Convex ℝ (u10h_D0 D z) := by
  have h : u10h_D0 D z = (fun x => x + z) ⁻¹' D := by ext w; simp [u10h_D0]
  rw [h]; exact hD.convex.translate_preimage_left z

theorem u10h_D0_isCompact {D : Set Plane} (hD : Link.IsDisc D) (z : Plane) : IsCompact (u10h_D0 D z) :=
  (Homeomorph.addRight z).isCompact_preimage.mpr hD.isCompact

theorem u10h_D0_interior {D : Set Plane} (z : Plane) :
    interior (u10h_D0 D z) = (Homeomorph.addRight z) ⁻¹' interior D :=
  ((Homeomorph.addRight z).preimage_interior D).symm

theorem u10h_D0_frontier {D : Set Plane} (z : Plane) :
    frontier (u10h_D0 D z) = (Homeomorph.addRight z) ⁻¹' frontier D :=
  ((Homeomorph.addRight z).preimage_frontier D).symm

theorem u10h_D0_closure {D : Set Plane} (z : Plane) :
    closure (u10h_D0 D z) = (Homeomorph.addRight z) ⁻¹' closure D :=
  ((Homeomorph.addRight z).preimage_closure D).symm

theorem u10h_D0_nhds {D : Set Plane} {z : Plane} (hz : z ∈ interior D) : u10h_D0 D z ∈ nhds (0 : Plane) := by
  rw [mem_nhds_iff]
  refine ⟨interior (u10h_D0 D z), interior_subset, isOpen_interior, ?_⟩
  rw [u10h_D0_interior]
  simpa using hz

theorem u10h_D0_absorbent {D : Set Plane} {z : Plane} (hz : z ∈ interior D) : Absorbent ℝ (u10h_D0 D z) :=
  absorbent_nhds_zero (u10h_D0_nhds hz)

theorem u10h_D0_bounded {D : Set Plane} (hD : Link.IsDisc D) (z : Plane) :
    Bornology.IsVonNBounded ℝ (u10h_D0 D z) :=
  (u10h_D0_isCompact hD z).isVonNBounded ℝ

theorem u10h_rg_nonneg (D : Set Plane) (z x : Plane) : 0 ≤ u10h_rg D z x := gauge_nonneg _

theorem u10h_rg_lt_one_iff {D : Set Plane} (hD : Link.IsDisc D) {z : Plane} (hz : z ∈ interior D) (x : Plane) :
    u10h_rg D z x < 1 ↔ x ∈ interior D := by
  unfold u10h_rg
  rw [gauge_lt_one_iff_mem_interior (u10h_D0_convex hD z) (u10h_D0_nhds hz), u10h_D0_interior]
  simp

theorem u10h_rg_le_one_iff {D : Set Plane} (hD : Link.IsDisc D) {z : Plane} (hz : z ∈ interior D) (x : Plane) :
    u10h_rg D z x ≤ 1 ↔ x ∈ D := by
  unfold u10h_rg
  rw [gauge_le_one_iff_mem_closure (u10h_D0_convex hD z) (u10h_D0_nhds hz), u10h_D0_closure,
    hD.isCompact.isClosed.closure_eq]
  simp

theorem u10h_rg_eq_one_iff {D : Set Plane} (hD : Link.IsDisc D) {z : Plane} (hz : z ∈ interior D) (x : Plane) :
    u10h_rg D z x = 1 ↔ x ∈ frontier D := by
  unfold u10h_rg
  rw [gauge_eq_one_iff_mem_frontier (u10h_D0_convex hD z) (u10h_D0_nhds hz), u10h_D0_frontier]
  simp

theorem u10h_rg_eq_zero_iff {D : Set Plane} (hD : Link.IsDisc D) {z : Plane} (hz : z ∈ interior D) (x : Plane) :
    u10h_rg D z x = 0 ↔ x = z := by
  unfold u10h_rg
  rw [gauge_eq_zero (u10h_D0_absorbent hz) (u10h_D0_bounded hD z), sub_eq_zero]

theorem u10h_rg_pos {D : Set Plane} (hD : Link.IsDisc D) {z : Plane} (hz : z ∈ interior D) {x : Plane}
    (hx : x ≠ z) : 0 < u10h_rg D z x :=
  lt_of_le_of_ne (u10h_rg_nonneg D z x) (fun h => hx ((u10h_rg_eq_zero_iff hD hz x).mp h.symm))

theorem u10h_rg_self (D : Set Plane) (z : Plane) : u10h_rg D z z = 0 := by
  simp [u10h_rg, gauge_zero]

theorem u10h_rg_smul (D : Set Plane) (z x : Plane) {t : ℝ} (ht : 0 ≤ t) :
    u10h_rg D z (z + t • (x - z)) = t * u10h_rg D z x := by
  unfold u10h_rg
  rw [add_sub_cancel_left, gauge_smul_of_nonneg ht, smul_eq_mul]

theorem u10h_rg_continuous {D : Set Plane} (hD : Link.IsDisc D) {z : Plane} (hz : z ∈ interior D) :
    Continuous (u10h_rg D z) :=
  (continuous_gauge (u10h_D0_convex hD z) (u10h_D0_nhds hz)).comp (continuous_id.sub continuous_const)

/-- The frontier point on the ray from `z` through `x ≠ z`. -/
noncomputable def u10h_ray (D : Set Plane) (z x : Plane) : Plane := z + (u10h_rg D z x)⁻¹ • (x - z)

theorem u10h_ray_mem_frontier {D : Set Plane} (hD : Link.IsDisc D) {z : Plane} (hz : z ∈ interior D)
    {x : Plane} (hx : x ≠ z) : u10h_ray D z x ∈ frontier D := by
  rw [← u10h_rg_eq_one_iff hD hz, u10h_ray, u10h_rg_smul D z x (inv_nonneg.mpr (u10h_rg_nonneg D z x))]
  exact inv_mul_cancel₀ (u10h_rg_pos hD hz hx).ne'

theorem u10h_ray_spec {D : Set Plane} (hD : Link.IsDisc D) {z : Plane} (hz : z ∈ interior D)
    {x : Plane} (hx : x ≠ z) : x = z + u10h_rg D z x • (u10h_ray D z x - z) := by
  rw [u10h_ray, add_sub_cancel_left, smul_smul, mul_inv_cancel₀ (u10h_rg_pos hD hz hx).ne', one_smul,
    add_sub_cancel]

theorem u10h_ray_of_frontier {D : Set Plane} (hD : Link.IsDisc D) {z : Plane} (hz : z ∈ interior D)
    {y : Plane} (hy : y ∈ frontier D) : u10h_ray D z y = y := by
  rw [u10h_ray, (u10h_rg_eq_one_iff hD hz y).mpr hy, inv_one, one_smul, add_sub_cancel]

theorem u10h_frontier_ne {D : Set Plane} (hD : Link.IsDisc D) {z : Plane} (hz : z ∈ interior D)
    {y : Plane} (hy : y ∈ frontier D) : y ≠ z := by
  intro h; subst h
  have := (u10h_rg_eq_one_iff hD hz y).mpr hy
  rw [u10h_rg_self] at this; norm_num at this

theorem u10h_frontier_subset {D : Set Plane} (hD : Link.IsDisc D) : frontier D ⊆ D :=
  hD.isCompact.isClosed.frontier_subset

/-! ### det algebra -/

theorem u10h_det_add_right (u v w : Plane) : det u (v + w) = det u v + det u w := by
  simp only [det, Prod.fst_add, Prod.snd_add]; ring

theorem u10h_det_smul_right (u v : Plane) (c : ℝ) : det u (c • v) = c * det u v := by
  simp only [det, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring

theorem u10h_det_add_left (u v w : Plane) : det (u + v) w = det u w + det v w := by
  simp only [det, Prod.fst_add, Prod.snd_add]; ring

theorem u10h_det_smul_left' (u v : Plane) (c : ℝ) : det (c • u) v = c * det u v := by
  simp only [det, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring

theorem u10h_det_self (u : Plane) : det u u = 0 := by simp only [det]; ring

theorem u10h_det_zero_right (u : Plane) : det u 0 = 0 := by simp [det]

theorem u10h_det_zero_left (u : Plane) : det 0 u = 0 := by simp [det]

theorem u10h_det_swap' (u v : Plane) : det u v = -det v u := by simp only [det]; ring

theorem u10h_cramer {u v : Plane} (h : det u v ≠ 0) (w : Plane) :
    w = (det w v / det u v) • u + (det u w / det u v) • v := by
  ext
  · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul, div_mul_eq_mul_div, ← add_div]
    rw [eq_div_iff h]; unfold det; ring
  · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul, div_mul_eq_mul_div, ← add_div]
    rw [eq_div_iff h]; unfold det; ring

theorem u10h_parallel_of_det_eq_zero {u v : Plane} (hu : u ≠ 0) (h : det u v = 0) :
    ∃ μ : ℝ, v = μ • u := by
  have hn : 0 < u.1 ^ 2 + u.2 ^ 2 := by
    rcases not_and_or.mp (fun hc : u.1 = 0 ∧ u.2 = 0 => hu (Prod.ext hc.1 hc.2)) with h1 | h2 <;>
      positivity
  refine ⟨(u.1 * v.1 + u.2 * v.2) / (u.1 ^ 2 + u.2 ^ 2), ?_⟩
  simp only [det] at h
  ext
  · simp only [Prod.smul_fst, smul_eq_mul]
    field_simp
    linear_combination (-u.2) * h
  · simp only [Prod.smul_snd, smul_eq_mul]
    field_simp
    linear_combination u.1 * h

/-! ### half-planes are convex -/

theorem u10h_convex_det_nonneg (z u : Plane) : Convex ℝ {x : Plane | 0 ≤ det u (x - z)} := by
  intro x hx y hy a b ha hb hab
  change 0 ≤ det u (x - z) at hx
  change 0 ≤ det u (y - z) at hy
  change 0 ≤ det u (a • x + b • y - z)
  have hz' : z = a • z + b • z := by rw [← add_smul, hab, one_smul]
  have : a • x + b • y - z = a • (x - z) + b • (y - z) := by
    calc a • x + b • y - z = a • x + b • y - (a • z + b • z) := by rw [← hz']
      _ = a • (x - z) + b • (y - z) := by rw [smul_sub, smul_sub]; abel
  rw [this, u10h_det_add_right, u10h_det_smul_right, u10h_det_smul_right]
  positivity

theorem u10h_convex_det_nonneg' (z v : Plane) : Convex ℝ {x : Plane | 0 ≤ det (x - z) v} := by
  intro x hx y hy a b ha hb hab
  change 0 ≤ det (x - z) v at hx
  change 0 ≤ det (y - z) v at hy
  change 0 ≤ det (a • x + b • y - z) v
  have hz' : z = a • z + b • z := by rw [← add_smul, hab, one_smul]
  have : a • x + b • y - z = a • (x - z) + b • (y - z) := by
    calc a • x + b • y - z = a • x + b • y - (a • z + b • z) := by rw [← hz']
      _ = a • (x - z) + b • (y - z) := by rw [smul_sub, smul_sub]; abel
  rw [this, u10h_det_add_left, u10h_det_smul_left', u10h_det_smul_left']
  positivity

/-! ### a straight frontier piece is not seen edge-on from `z` -/

theorem u10h_det_ne_zero_of_segment {D : Set Plane} (hD : Link.IsDisc D) {z : Plane} (hz : z ∈ interior D)
    {a b : Plane} (hne : a ≠ b) (hseg : segment ℝ a b ⊆ frontier D) : det (a - z) (b - z) ≠ 0 := by
  intro h0
  have ha : a ∈ frontier D := hseg (left_mem_segment ℝ a b)
  have hb : b ∈ frontier D := hseg (right_mem_segment ℝ a b)
  have haz : a - z ≠ 0 := sub_ne_zero.mpr (u10h_frontier_ne hD hz ha)
  obtain ⟨μ, hμ⟩ := u10h_parallel_of_det_eq_zero haz h0
  have hb' : b = z + μ • (a - z) := by rw [← hμ]; abel
  rcases le_or_gt 0 μ with hμ0 | hμ0
  · have h1 := (u10h_rg_eq_one_iff hD hz b).mpr hb
    rw [hb', u10h_rg_smul D z a hμ0, (u10h_rg_eq_one_iff hD hz a).mpr ha, mul_one] at h1
    subst h1
    apply hne; rw [hb', one_smul, add_sub_cancel]
  · have h1μ : (1 - μ) ≠ 0 := by linarith
    have hzmem : z ∈ segment ℝ a b := by
      refine ⟨-μ / (1 - μ), 1 / (1 - μ), by
        apply div_nonneg <;> linarith, by
        apply div_nonneg <;> linarith, by
        rw [← add_div, div_eq_one_iff_eq h1μ]; ring, ?_⟩
      rw [hb']
      ext
      · simp only [Prod.fst_add, Prod.smul_fst, Prod.fst_sub, smul_eq_mul]; field_simp; ring
      · simp only [Prod.snd_add, Prod.smul_snd, Prod.snd_sub, smul_eq_mul]; field_simp; ring
    have := (u10h_rg_eq_one_iff hD hz z).mpr (hseg hzmem)
    rw [u10h_rg_self] at this; norm_num at this

/-! ### the sector lemma and the fan characterisation -/

/-- A frontier point in the closed sector spanned (from `z`) by a straight frontier piece `[a, b]`
lies on that piece. -/
theorem u10h_frontier_mem_segment {D : Set Plane} (hD : Link.IsDisc D) {z : Plane} (hz : z ∈ interior D)
    {a b : Plane} (hab : 0 < det (a - z) (b - z)) (hseg : segment ℝ a b ⊆ frontier D) {y : Plane}
    (hy : y ∈ frontier D) (h1 : 0 ≤ det (a - z) (y - z)) (h2 : 0 ≤ det (y - z) (b - z)) :
    y ∈ segment ℝ a b := by
  set β := det (y - z) (b - z) / det (a - z) (b - z) with hβ
  set γ := det (a - z) (y - z) / det (a - z) (b - z) with hγ
  have hβ0 : 0 ≤ β := div_nonneg h2 hab.le
  have hγ0 : 0 ≤ γ := div_nonneg h1 hab.le
  have hdec : y - z = β • (a - z) + γ • (b - z) := u10h_cramer hab.ne' (y - z)
  have hs : 0 < β + γ := by
    rcases (add_nonneg hβ0 hγ0).lt_or_eq with h | h
    · exact h
    · exfalso
      have hβz : β = 0 := by linarith
      have hγz : γ = 0 := by linarith
      rw [hβz, hγz, zero_smul, zero_smul, add_zero] at hdec
      exact u10h_frontier_ne hD hz hy (sub_eq_zero.mp hdec)
  set s := β + γ with hs_def
  set w : Plane := (β / s) • a + (γ / s) • b with hw
  have hwseg : w ∈ segment ℝ a b :=
    ⟨β / s, γ / s, div_nonneg hβ0 hs.le, div_nonneg hγ0 hs.le, by rw [← add_div, div_self hs.ne'], rfl⟩
  have hyw : y = z + s • (w - z) := by
    have e1 := congrArg Prod.fst hdec
    have e2 := congrArg Prod.snd hdec
    simp only [Prod.fst_sub, Prod.fst_add, Prod.smul_fst, smul_eq_mul, Prod.snd_sub, Prod.snd_add,
      Prod.smul_snd] at e1 e2
    ext
    · simp only [hw, Prod.fst_add, Prod.smul_fst, Prod.fst_sub, smul_eq_mul]
      field_simp
      linear_combination e1
    · simp only [hw, Prod.snd_add, Prod.smul_snd, Prod.snd_sub, smul_eq_mul]
      field_simp
      linear_combination e2
  have hrw : u10h_rg D z w = 1 := (u10h_rg_eq_one_iff hD hz w).mpr (hseg hwseg)
  have hry : u10h_rg D z y = 1 := (u10h_rg_eq_one_iff hD hz y).mpr hy
  rw [hyw, u10h_rg_smul D z w hs.le, hrw, mul_one] at hry
  rw [hyw, hry, one_smul, add_sub_cancel]
  exact hwseg

/-- The ray point of a point of the closed sector lies on the frontier piece. -/
theorem u10h_ray_mem_segment {D : Set Plane} (hD : Link.IsDisc D) {z : Plane} (hz : z ∈ interior D)
    {a b : Plane} (hab : 0 < det (a - z) (b - z)) (hseg : segment ℝ a b ⊆ frontier D) {x : Plane}
    (hxz : x ≠ z) (h1 : 0 ≤ det (a - z) (x - z)) (h2 : 0 ≤ det (x - z) (b - z)) :
    u10h_ray D z x ∈ segment ℝ a b := by
  have hyz : u10h_ray D z x - z = (u10h_rg D z x)⁻¹ • (x - z) := by simp [u10h_ray]
  have hr0 : 0 ≤ (u10h_rg D z x)⁻¹ := inv_nonneg.mpr (u10h_rg_nonneg _ _ _)
  refine u10h_frontier_mem_segment hD hz hab hseg (u10h_ray_mem_frontier hD hz hxz) ?_ ?_
  · rw [hyz, u10h_det_smul_right]; exact mul_nonneg hr0 h1
  · rw [hyz, u10h_det_smul_left']; exact mul_nonneg hr0 h2

/-- The fan triangle `conv {z, a, b}` over a straight frontier piece is the closed sector cut off
by `D`. -/
theorem u10h_mem_fan_iff {D : Set Plane} (hD : Link.IsDisc D) {z : Plane} (hz : z ∈ interior D)
    {a b : Plane} (hab : 0 < det (a - z) (b - z)) (hseg : segment ℝ a b ⊆ frontier D) (x : Plane) :
    x ∈ convexHull ℝ {z, a, b} ↔ 0 ≤ det (a - z) (x - z) ∧ 0 ≤ det (x - z) (b - z) ∧ x ∈ D := by
  constructor
  · intro hx
    have hsub : convexHull ℝ {z, a, b} ⊆
        ({x | 0 ≤ det (a - z) (x - z)} ∩ {x | 0 ≤ det (x - z) (b - z)}) ∩ D := by
      apply convexHull_min
      · intro p hp
        simp only [mem_insert_iff, mem_singleton_iff] at hp
        rcases hp with rfl | rfl | rfl
        · exact ⟨⟨by simp [u10h_det_zero_right], by simp [u10h_det_zero_left]⟩, interior_subset hz⟩
        · exact ⟨⟨by simp [u10h_det_self], hab.le⟩,
            u10h_frontier_subset hD (hseg (left_mem_segment ℝ _ _))⟩
        · exact ⟨⟨hab.le, by simp [u10h_det_self]⟩,
            u10h_frontier_subset hD (hseg (right_mem_segment ℝ _ _))⟩
      · exact ((u10h_convex_det_nonneg z (a - z)).inter (u10h_convex_det_nonneg' z (b - z))).inter
          hD.convex
    obtain ⟨⟨h1, h2⟩, h3⟩ := hsub hx
    exact ⟨h1, h2, h3⟩
  · rintro ⟨h1, h2, h3⟩
    by_cases hxz : x = z
    · subst hxz; exact subset_convexHull ℝ _ (mem_insert _ _)
    · have hyseg := u10h_ray_mem_segment hD hz hab hseg hxz h1 h2
      have hxeq := u10h_ray_spec hD hz hxz
      have hr1 : u10h_rg D z x ≤ 1 := (u10h_rg_le_one_iff hD hz x).mpr h3
      have hr0 := u10h_rg_nonneg D z x
      have hzmem : z ∈ convexHull ℝ {z, a, b} := subset_convexHull ℝ _ (mem_insert _ _)
      have hymem : u10h_ray D z x ∈ convexHull ℝ {z, a, b} :=
        segment_subset_convexHull (by simp) (by simp) hyseg
      have := (convex_convexHull ℝ {z, a, b}) hzmem hymem (sub_nonneg.mpr hr1) hr0 (by ring)
      rw [hxeq]
      convert this using 1
      rw [sub_smul, one_smul, smul_sub]; abel

/-! ### marks and adjacent pairs -/

/-- `(a, b)` is an adjacent pair of marks of `V`: a straight frontier piece seen counterclockwise
from `z` with no mark strictly inside. -/
def u10h_Adj (D : Set Plane) (z : Plane) (V : Set Plane) (a b : Plane) : Prop :=
  a ∈ V ∧ b ∈ V ∧ 0 < det (a - z) (b - z) ∧ segment ℝ a b ⊆ frontier D ∧
    ∀ c ∈ V, c ∉ openSegment ℝ a b

theorem u10h_openSegment_sub {a b y : Plane} (h : y ∈ openSegment ℝ a b) (z : Plane) :
    ∃ β γ : ℝ, 0 < β ∧ 0 < γ ∧ β + γ = 1 ∧ y - z = β • (a - z) + γ • (b - z) := by
  obtain ⟨β, γ, hβ, hγ, hβγ, rfl⟩ := h
  refine ⟨β, γ, hβ, hγ, hβγ, ?_⟩
  have hz' : z = β • z + γ • z := by rw [← add_smul, hβγ, one_smul]
  calc β • a + γ • b - z = β • a + γ • b - (β • z + γ • z) := by rw [← hz']
    _ = β • (a - z) + γ • (b - z) := by rw [smul_sub, smul_sub]; abel

theorem u10h_det_comb_right (u v w : Plane) (β γ : ℝ) :
    det u (β • v + γ • w) = β * det u v + γ * det u w := by
  rw [u10h_det_add_right, u10h_det_smul_right, u10h_det_smul_right]

theorem u10h_det_comb_left (u v w : Plane) (β γ : ℝ) :
    det (β • v + γ • w) u = β * det v u + γ * det w u := by
  rw [u10h_det_add_left, u10h_det_smul_left', u10h_det_smul_left']

theorem u10h_mem_segment_cases {a b y : Plane} (h : y ∈ segment ℝ a b) :
    y = a ∨ y = b ∨ y ∈ openSegment ℝ a b := by
  rw [← insert_endpoints_openSegment] at h
  simpa using h

/-- Where a mark can lie relative to an adjacent pair. -/
theorem u10h_adj_trichotomy {D : Set Plane} (hD : Link.IsDisc D) {z : Plane} (hz : z ∈ interior D)
    {V : Set Plane} (hV : V ⊆ frontier D) {a b : Plane} (hab : u10h_Adj D z V a b) {c : Plane}
    (hc : c ∈ V) : c = a ∨ c = b ∨ det (a - z) (c - z) < 0 ∨ det (c - z) (b - z) < 0 := by
  rcases lt_or_ge (det (a - z) (c - z)) 0 with h1 | h1
  · exact Or.inr (Or.inr (Or.inl h1))
  rcases lt_or_ge (det (c - z) (b - z)) 0 with h2 | h2
  · exact Or.inr (Or.inr (Or.inr h2))
  have hcseg := u10h_frontier_mem_segment hD hz hab.2.2.1 hab.2.2.2.1 (hV hc) h1 h2
  rcases u10h_mem_segment_cases hcseg with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact absurd h (hab.2.2.2.2 c hc)

theorem u10h_adj_unique_right {D : Set Plane} (hD : Link.IsDisc D) {z : Plane} (hz : z ∈ interior D)
    {V : Set Plane} (hV : V ⊆ frontier D) {a b d : Plane} (hab : u10h_Adj D z V a b)
    (had : u10h_Adj D z V a d) : b = d := by
  rcases u10h_adj_trichotomy hD hz hV hab had.2.1 with h | h | h | h
  · exfalso; subst h; exact lt_irrefl (0:ℝ) (by simpa [u10h_det_self] using had.2.2.1)
  · exact h.symm
  · exfalso; linarith [had.2.2.1]
  · exfalso
    have hbd : 0 < det (b - z) (d - z) := by rw [u10h_det_swap']; linarith
    have hbseg := u10h_frontier_mem_segment hD hz had.2.2.1 had.2.2.2.1 (hV hab.2.1) hab.2.2.1.le hbd.le
    rcases u10h_mem_segment_cases hbseg with h1 | h1 | h1
    · subst h1; exact lt_irrefl (0:ℝ) (by simpa [u10h_det_self] using hab.2.2.1)
    · subst h1; simp [u10h_det_self] at hbd
    · exact had.2.2.2.2 b hab.2.1 h1

theorem u10h_adj_unique_left {D : Set Plane} (hD : Link.IsDisc D) {z : Plane} (hz : z ∈ interior D)
    {V : Set Plane} (hV : V ⊆ frontier D) {a b c : Plane} (hab : u10h_Adj D z V a b)
    (hcb : u10h_Adj D z V c b) : a = c := by
  rcases u10h_adj_trichotomy hD hz hV hab hcb.1 with h | h | h | h
  · exact h.symm
  · exfalso; subst h; exact lt_irrefl (0:ℝ) (by simpa [u10h_det_self] using hcb.2.2.1)
  · exfalso
    have hca : 0 < det (c - z) (a - z) := by rw [u10h_det_swap']; linarith
    have haseg := u10h_frontier_mem_segment hD hz hcb.2.2.1 hcb.2.2.2.1 (hV hab.1) hca.le hab.2.2.1.le
    rcases u10h_mem_segment_cases haseg with h1 | h1 | h1
    · subst h1; simp [u10h_det_self] at hca
    · subst h1; exact lt_irrefl (0:ℝ) (by simpa [u10h_det_self] using hab.2.2.1)
    · exact hcb.2.2.2.2 a hab.1 h1
  · exfalso; linarith [hcb.2.2.1]

/-- A point in the open frontier pieces of two adjacent pairs forces the pairs to coincide. -/
theorem u10h_adj_eq_of_openSegment {D : Set Plane} (hD : Link.IsDisc D) {z : Plane} (hz : z ∈ interior D)
    {V : Set Plane} (hV : V ⊆ frontier D) {a b c d y : Plane} (hab : u10h_Adj D z V a b)
    (hcd : u10h_Adj D z V c d) (h1 : y ∈ openSegment ℝ a b) (h2 : y ∈ openSegment ℝ c d) :
    a = c ∧ b = d := by
  obtain ⟨β, γ, hβ, hγ, -, hY1⟩ := u10h_openSegment_sub h1 z
  obtain ⟨β', δ, hβ', hδ, -, hY2⟩ := u10h_openSegment_sub h2 z
  have dAB := hab.2.2.1
  have dCD := hcd.2.2.1
  have eAY : det (a - z) (y - z) = γ * det (a - z) (b - z) := by
    rw [hY1, u10h_det_comb_right, u10h_det_self]; ring
  have eBY : det (b - z) (y - z) = -(β * det (a - z) (b - z)) := by
    rw [hY1, u10h_det_comb_right, u10h_det_self, u10h_det_swap' (b - z) (a - z)]; ring
  have eCY : det (c - z) (y - z) = δ * det (c - z) (d - z) := by
    rw [hY2, u10h_det_comb_right, u10h_det_self]; ring
  have eYD : det (y - z) (d - z) = β' * det (c - z) (d - z) := by
    rw [hY2, u10h_det_comb_left, u10h_det_self]; ring
  have eAY' : det (a - z) (y - z) = β' * det (a - z) (c - z) + δ * det (a - z) (d - z) := by
    rw [hY2, u10h_det_comb_right]
  have eBY' : det (b - z) (y - z) = β' * det (b - z) (c - z) + δ * det (b - z) (d - z) := by
    rw [hY2, u10h_det_comb_right]
  have eYD' : det (y - z) (d - z) = β * det (a - z) (d - z) + γ * det (b - z) (d - z) := by
    rw [hY1, u10h_det_comb_left]
  rcases u10h_adj_trichotomy hD hz hV hab hcd.1 with hc | hc | hc | hc
  · -- c = a
    subst hc
    refine ⟨rfl, ?_⟩
    rcases u10h_adj_trichotomy hD hz hV hab hcd.2.1 with hd | hd | hd | hd
    · exfalso; subst hd
      have := hcd.2.2.1; rw [u10h_det_self] at this; exact lt_irrefl _ this
    · exact hd.symm
    · exfalso; linarith [hcd.2.2.1]
    · exfalso
      have hbd : 0 < det (b - z) (d - z) := by rw [u10h_det_swap']; linarith
      have hbseg := u10h_frontier_mem_segment hD hz hcd.2.2.1 hcd.2.2.2.1 (hV hab.2.1) dAB.le hbd.le
      rcases u10h_mem_segment_cases hbseg with h | h | h
      · subst h; rw [u10h_det_self] at dAB; exact lt_irrefl _ dAB
      · subst h; rw [u10h_det_self] at hbd; exact lt_irrefl _ hbd
      · exact hcd.2.2.2.2 b hab.2.1 h
  · -- c = b
    exfalso; subst hc
    have : 0 < det (c - z) (y - z) := by rw [eCY]; positivity
    rw [eBY] at this
    have := mul_pos hβ dAB; linarith
  · -- det (a-z) (c-z) < 0 : `a` lies strictly inside the sector `(c, d)`
    exfalso
    have hAD : 0 < det (a - z) (d - z) := by
      have h0 : 0 < δ * det (a - z) (d - z) := by
        have := mul_pos hγ dAB
        have := mul_neg_of_pos_of_neg hβ' hc
        linarith
      exact (mul_pos_iff_of_pos_left hδ).mp h0
    have hCA : 0 < det (c - z) (a - z) := by rw [u10h_det_swap']; linarith
    have haseg := u10h_frontier_mem_segment hD hz dCD hcd.2.2.2.1 (hV hab.1) hCA.le hAD.le
    rcases u10h_mem_segment_cases haseg with h | h | h
    · subst h; rw [u10h_det_self] at hCA; exact lt_irrefl _ hCA
    · subst h; rw [u10h_det_self] at hAD; exact lt_irrefl _ hAD
    · exact hcd.2.2.2.2 a hab.1 h
  · -- det (c-z) (b-z) < 0 : `d` lies strictly inside the sector `(a, b)`
    exfalso
    have hBC : 0 < det (b - z) (c - z) := by rw [u10h_det_swap']; linarith
    have hBD : det (b - z) (d - z) < 0 := by
      have h0 : δ * det (b - z) (d - z) < 0 := by
        have := mul_pos hβ dAB
        have := mul_pos hβ' hBC
        linarith
      rcases lt_or_ge (det (b - z) (d - z)) 0 with h | h
      · exact h
      · exfalso; linarith [mul_nonneg hδ.le h]
    have hAD : 0 < det (a - z) (d - z) := by
      have h0 : 0 < β * det (a - z) (d - z) := by
        have := mul_pos hβ' dCD
        have := mul_neg_of_pos_of_neg hγ hBD
        linarith
      exact (mul_pos_iff_of_pos_left hβ).mp h0
    have hDB : 0 < det (d - z) (b - z) := by rw [u10h_det_swap']; linarith
    have hdseg := u10h_frontier_mem_segment hD hz dAB hab.2.2.2.1 (hV hcd.2.1) hAD.le hDB.le
    rcases u10h_mem_segment_cases hdseg with h | h | h
    · subst h; rw [u10h_det_self] at hAD; exact lt_irrefl _ hAD
    · subst h; rw [u10h_det_self] at hDB; exact lt_irrefl _ hDB
    · exact hab.2.2.2.2 d hcd.2.1 h


theorem u10h_range_three (z a b : Plane) : range ![z, a, b] = {z, a, b} := by
  ext p
  simp only [mem_range, mem_insert_iff, mem_singleton_iff]
  constructor
  · rintro ⟨i, rfl⟩; fin_cases i <;> simp
  · rintro (rfl | rfl | rfl)
    exacts [⟨0, by simp⟩, ⟨1, by simp⟩, ⟨2, by simp⟩]

/-- The fan faces: one triangle `z a b` per pair with `A a b`. -/
def u10h_fanFaces (z : Plane) (A : Plane → Plane → Prop) : Set Triangle :=
  {T | ∃ a b, A a b ∧ T.v = ![z, a, b]}

theorem u10h_fanTri_mem {z a b : Plane} {A : Plane → Plane → Prop} (h : A a b)
    (hpos : 0 < det (a - z) (b - z)) :
    (⟨![z, a, b], by simpa using hpos⟩ : Triangle) ∈ u10h_fanFaces z A := ⟨a, b, h, rfl⟩

theorem u10h_carrier_of_v {T : Triangle} {z a b : Plane} (h : T.v = ![z, a, b]) :
    T.carrier = convexHull ℝ {z, a, b} := by
  rw [Triangle.carrier, h, u10h_range_three]

theorem u10h_inter_cases {D : Set Plane} (hD : Link.IsDisc D) {z : Plane} (hz : z ∈ interior D)
    {V : Set Plane} (hV : V ⊆ frontier D) {a b c d y : Plane} (hab : u10h_Adj D z V a b)
    (hcd : u10h_Adj D z V c d) (hy1 : y ∈ segment ℝ a b) (hy2 : y ∈ segment ℝ c d) :
    (a = c ∧ b = d) ∨ (y = a ∧ a = d) ∨ (y = b ∧ b = c) := by
  rcases u10h_mem_segment_cases hy1 with h1 | h1 | h1 <;>
    rcases u10h_mem_segment_cases hy2 with h2 | h2 | h2
  · subst h1; exact Or.inl ⟨h2, u10h_adj_unique_right hD hz hV hab (h2 ▸ hcd)⟩
  · exact Or.inr (Or.inl ⟨h1, h1 ▸ h2⟩)
  · exact absurd (h1 ▸ h2) (hcd.2.2.2.2 a hab.1)
  · exact Or.inr (Or.inr ⟨h1, h1 ▸ h2⟩)
  · subst h1; exact Or.inl ⟨u10h_adj_unique_left hD hz hV hab (h2 ▸ hcd), h2⟩
  · exact absurd (h1 ▸ h2) (hcd.2.2.2.2 b hab.2.1)
  · exact absurd (h2 ▸ h1) (hab.2.2.2.2 c hcd.1)
  · exact absurd (h2 ▸ h1) (hab.2.2.2.2 d hcd.2.1)
  · exact Or.inl (u10h_adj_eq_of_openSegment hD hz hV hab hcd h1 h2)

theorem u10h_fan_subset {D : Set Plane} (hD : Link.IsDisc D) {z : Plane} (hz : z ∈ interior D)
    {a b : Plane} (hseg : segment ℝ a b ⊆ frontier D) : convexHull ℝ {z, a, b} ⊆ D := by
  apply convexHull_min _ hD.convex
  intro p hp
  simp only [mem_insert_iff, mem_singleton_iff] at hp
  rcases hp with rfl | rfl | rfl
  · exact interior_subset hz
  · exact u10h_frontier_subset hD (hseg (left_mem_segment ℝ _ _))
  · exact u10h_frontier_subset hD (hseg (right_mem_segment ℝ _ _))

theorem u10h_frontier_nonempty {D : Set Plane} (hD : Link.IsDisc D) {z : Plane} (hz : z ∈ interior D) :
    (frontier D).Nonempty :=
  ⟨u10h_ray D z (z + (1, 0)), u10h_ray_mem_frontier hD hz (by simp)⟩

theorem u10h_mem_segment_ray {D : Set Plane} (hD : Link.IsDisc D) {z : Plane} (hz : z ∈ interior D)
    {x : Plane} (hx : x ∈ D) (hxz : x ≠ z) : x ∈ segment ℝ z (u10h_ray D z x) := by
  have hr0 := u10h_rg_nonneg D z x
  have hr1 := (u10h_rg_le_one_iff hD hz x).mpr hx
  refine ⟨1 - u10h_rg D z x, u10h_rg D z x, by linarith, hr0, by ring, ?_⟩
  have := u10h_ray_spec hD hz hxz
  rw [smul_sub] at this
  rw [sub_smul, one_smul]
  conv_rhs => rw [this]
  abel

/-- The fan from `z` over the adjacent pairs is a straight triangulation of `D`. -/
theorem u10h_fan_triangulation {D : Set Plane} (hD : Link.IsDisc D) {z : Plane} (hz : z ∈ interior D)
    {V : Set Plane} (hVfin : V.Finite) (hV : V ⊆ frontier D) {A : Plane → Plane → Prop}
    (hA : ∀ a b, A a b → u10h_Adj D z V a b)
    (hcov : ∀ y ∈ frontier D, ∃ a b, A a b ∧ y ∈ segment ℝ a b) :
    ∃ K : Triangulation D, K.faces = u10h_fanFaces z A := by
  have hface : ∀ T ∈ u10h_fanFaces z A, ∃ a b, u10h_Adj D z V a b ∧ T.v 0 = z ∧ T.v 1 = a ∧
      T.v 2 = b ∧ T.carrier = convexHull ℝ {z, a, b} := by
    rintro T ⟨a, b, hab, hv⟩
    exact ⟨a, b, hA a b hab, by simp [hv], by simp [hv], by simp [hv], u10h_carrier_of_v hv⟩
  refine ⟨⟨u10h_fanFaces z A, ?_, ?_, ?_⟩, rfl⟩
  · -- finite
    apply Set.Finite.of_finite_image (f := fun T => (T.v 1, T.v 2))
    · refine (hVfin.prod hVfin).subset ?_
      rintro _ ⟨T, hT, rfl⟩
      obtain ⟨a, b, hab, -, h1, h2, -⟩ := hface T hT
      show T.v 1 ∈ V ∧ T.v 2 ∈ V
      rw [h1, h2]; exact ⟨hab.1, hab.2.1⟩
    · intro T hT T' hT' h
      simp only [Prod.mk.injEq] at h
      obtain ⟨a, b, -, h0, -, -, -⟩ := hface T hT
      obtain ⟨c, d, -, h0', -, -, -⟩ := hface T' hT'
      have : T.v = T'.v := by
        funext i
        fin_cases i
        · simpa using h0.trans h0'.symm
        · exact h.1
        · exact h.2
      cases T; cases T'; simp only at this; subst this; rfl
  · -- cover
    apply Set.Subset.antisymm
    · intro x hx
      simp only [mem_iUnion, exists_prop] at hx
      obtain ⟨T, hT, hxT⟩ := hx
      obtain ⟨a, b, hab, -, -, -, hc⟩ := hface T hT
      rw [hc] at hxT
      exact u10h_fan_subset hD hz hab.2.2.2.1 hxT
    · intro x hx
      simp only [mem_iUnion, exists_prop]
      by_cases hxz : x = z
      · subst hxz
        obtain ⟨y0, hy0⟩ := u10h_frontier_nonempty hD hz
        obtain ⟨a, b, hab, -⟩ := hcov y0 hy0
        refine ⟨_, u10h_fanTri_mem hab (hA a b hab).2.2.1, ?_⟩
        rw [u10h_carrier_of_v rfl]
        exact subset_convexHull ℝ _ (mem_insert _ _)
      · obtain ⟨a, b, hab, hyab⟩ := hcov _ (u10h_ray_mem_frontier hD hz hxz)
        refine ⟨_, u10h_fanTri_mem hab (hA a b hab).2.2.1, ?_⟩
        rw [u10h_carrier_of_v rfl]
        have hzmem : z ∈ convexHull ℝ {z, a, b} := subset_convexHull ℝ _ (mem_insert _ _)
        have hymem : u10h_ray D z x ∈ convexHull ℝ {z, a, b} :=
          segment_subset_convexHull (by simp) (by simp) hyab
        exact (convex_convexHull ℝ _).segment_subset hzmem hymem (u10h_mem_segment_ray hD hz hx hxz)
  · -- inter
    intro T hT T' hT'
    obtain ⟨a, b, hab, h0, h1, h2, hc⟩ := hface T hT
    obtain ⟨c, d, hcd, h0', h1', h2', hc'⟩ := hface T' hT'
    have hrT : range T.v = {z, a, b} := by
      rw [← u10h_range_three]; congr 1; funext i; fin_cases i <;> simp [h0, h1, h2]
    have hrT' : range T'.v = {z, c, d} := by
      rw [← u10h_range_three]; congr 1; funext i; fin_cases i <;> simp [h0', h1', h2']
    rw [hc, hc', hrT, hrT']
    apply Set.Subset.antisymm
    · rintro x ⟨hx1, hx2⟩
      by_cases hxz : x = z
      · subst hxz
        exact subset_convexHull ℝ _ ⟨mem_insert _ _, mem_insert _ _⟩
      · have hx1' := (u10h_mem_fan_iff hD hz hab.2.2.1 hab.2.2.2.1 x).mp hx1
        have hx2' := (u10h_mem_fan_iff hD hz hcd.2.2.1 hcd.2.2.2.1 x).mp hx2
        have hy1 := u10h_ray_mem_segment hD hz hab.2.2.1 hab.2.2.2.1 hxz hx1'.1 hx1'.2.1
        have hy2 := u10h_ray_mem_segment hD hz hcd.2.2.1 hcd.2.2.2.1 hxz hx2'.1 hx2'.2.1
        have hxseg := u10h_mem_segment_ray hD hz hx1'.2.2 hxz
        rcases u10h_inter_cases hD hz hV hab hcd hy1 hy2 with ⟨rfl, rfl⟩ | ⟨hy, rfl⟩ | ⟨hy, rfl⟩
        · rw [inter_self]; exact hx1
        · rw [hy] at hxseg
          exact segment_subset_convexHull (s := {z, a, b} ∩ {z, c, a}) ⟨mem_insert _ _, mem_insert _ _⟩
            ⟨by simp, by simp⟩ hxseg
        · rw [hy] at hxseg
          exact segment_subset_convexHull (s := {z, a, b} ∩ {z, b, d}) ⟨mem_insert _ _, mem_insert _ _⟩
            ⟨by simp, by simp⟩ hxseg
    · exact subset_inter (convexHull_mono inter_subset_left) (convexHull_mono inter_subset_right)

/-! ### the cone map -/


/-- The linear map sending `p ↦ p'`, `q ↦ q'` (for `det p q ≠ 0`), written in `det` coordinates. -/
noncomputable def u10h_linOfDet (p q p' q' : Plane) : Plane →ₗ[ℝ] Plane where
  toFun v := (det v q / det p q) • p' + (det p v / det p q) • q'
  map_add' v w := by
    rw [u10h_det_add_left, u10h_det_add_right, add_div, add_div, add_smul, add_smul]; abel
  map_smul' c v := by
    simp only [RingHom.id_apply]
    rw [u10h_det_smul_left', u10h_det_smul_right, mul_div_assoc, mul_div_assoc, mul_smul, mul_smul,
      smul_add]

theorem u10h_linOfDet_apply (p q p' q' v : Plane) :
    u10h_linOfDet p q p' q' v = (det v q / det p q) • p' + (det p v / det p q) • q' := rfl

theorem u10h_linOfDet_left {p q : Plane} (h : det p q ≠ 0) (p' q' : Plane) :
    u10h_linOfDet p q p' q' p = p' := by
  rw [u10h_linOfDet_apply, div_self h, u10h_det_self, zero_div, one_smul, zero_smul, add_zero]

theorem u10h_linOfDet_right {p q : Plane} (h : det p q ≠ 0) (p' q' : Plane) :
    u10h_linOfDet p q p' q' q = q' := by
  rw [u10h_linOfDet_apply, div_self h, u10h_det_self, zero_div, one_smul, zero_smul, zero_add]

/-- The cone extension of a frontier map `β`: `z ↦ z'`, `z + t (y - z) ↦ z' + t (β y - z')` for
`y ∈ frontier D`, `0 ≤ t ≤ 1`. -/
noncomputable def u10h_cone (D : Set Plane) (z z' : Plane) (β : Plane → Plane) (x : Plane) : Plane :=
  z' + u10h_rg D z x • (β (u10h_ray D z x) - z')

theorem u10h_cone_center (D : Set Plane) (z z' : Plane) (β : Plane → Plane) :
    u10h_cone D z z' β z = z' := by
  simp [u10h_cone, u10h_rg_self]

theorem u10h_cone_frontier {D : Set Plane} (hD : Link.IsDisc D) {z : Plane} (hz : z ∈ interior D)
    (z' : Plane) (β : Plane → Plane) {y : Plane} (hy : y ∈ frontier D) :
    u10h_cone D z z' β y = β y := by
  rw [u10h_cone, u10h_ray_of_frontier hD hz hy, (u10h_rg_eq_one_iff hD hz y).mpr hy, one_smul,
    add_sub_cancel]

/-- The radial coordinate is preserved by the cone map (for `β` into `frontier D'`). -/
theorem u10h_rg_cone {D D' : Set Plane} (hD : Link.IsDisc D) (hD' : Link.IsDisc D') {z z' : Plane}
    (hz : z ∈ interior D) (hz' : z' ∈ interior D') {β : Plane → Plane}
    (hβ : ∀ y ∈ frontier D, β y ∈ frontier D') {x : Plane} (hxz : x ≠ z) :
    u10h_rg D' z' (u10h_cone D z z' β x) = u10h_rg D z x := by
  rw [u10h_cone, u10h_rg_smul D' z' _ (u10h_rg_nonneg D z x),
    (u10h_rg_eq_one_iff hD' hz' _).mpr (hβ _ (u10h_ray_mem_frontier hD hz hxz)), mul_one]

theorem u10h_cone_ray_formula {D : Set Plane} (hD : Link.IsDisc D) {z : Plane} (hz : z ∈ interior D)
    (z' : Plane) (β : Plane → Plane) {y : Plane} (hy : y ∈ frontier D) {t : ℝ} (ht : 0 < t) :
    u10h_cone D z z' β (z + t • (y - z)) = z' + t • (β y - z') := by
  have hyz := u10h_frontier_ne hD hz hy
  have hrg : u10h_rg D z (z + t • (y - z)) = t := by
    rw [u10h_rg_smul D z y ht.le, (u10h_rg_eq_one_iff hD hz y).mpr hy, mul_one]
  have hray : u10h_ray D z (z + t • (y - z)) = y := by
    rw [u10h_ray, hrg, add_sub_cancel_left, smul_smul, inv_mul_cancel₀ ht.ne', one_smul, add_sub_cancel]
  rw [u10h_cone, hrg, hray]

theorem u10h_combo_sub {s t : ℝ} (hst : s + t = 1) (a b z : Plane) :
    s • a + t • b - z = s • (a - z) + t • (b - z) := by
  have hz' : z = s • z + t • z := by rw [← add_smul, hst, one_smul]
  calc s • a + t • b - z = s • a + t • b - (s • z + t • z) := by rw [← hz']
    _ = s • (a - z) + t • (b - z) := by rw [smul_sub, smul_sub]; abel

/-- On a fan triangle over a piece where `β` is affine, the cone map is affine. -/
theorem u10h_cone_eq_on_fan {D : Set Plane} (hD : Link.IsDisc D) {z : Plane} (hz : z ∈ interior D)
    (z' : Plane) {β : Plane → Plane} {a b : Plane} (hab : 0 < det (a - z) (b - z))
    (hseg : segment ℝ a b ⊆ frontier D) (haff : AffineOn β (segment ℝ a b)) {x : Plane}
    (hx : x ∈ convexHull ℝ {z, a, b}) :
    u10h_cone D z z' β x = u10h_linOfDet (a - z) (b - z) (β a - z') (β b - z') (x - z) + z' := by
  by_cases hxz : x = z
  · subst hxz; simp [u10h_cone_center]
  · obtain ⟨M, c, hM⟩ := haff
    have hx' := (u10h_mem_fan_iff hD hz hab hseg x).mp hx
    have hyseg := u10h_ray_mem_segment hD hz hab hseg hxz hx'.1 hx'.2.1
    obtain ⟨s, t, hs, ht, hst, hy⟩ := id hyseg
    have hβy : β (u10h_ray D z x) - z' = s • (β a - z') + t • (β b - z') := by
      rw [hM _ hyseg, hM a (left_mem_segment ℝ a b), hM b (right_mem_segment ℝ a b), ← hy, map_add,
        map_smul, map_smul]
      have hc : c = s • c + t • c := by rw [← add_smul, hst, one_smul]
      have hz' : z' = s • z' + t • z' := by rw [← add_smul, hst, one_smul]
      calc s • M a + t • M b + c - z' = s • M a + t • M b + (s • c + t • c) - (s • z' + t • z') := by
            rw [← hc, ← hz']
        _ = s • (M a + c - z') + t • (M b + c - z') := by
            rw [smul_sub, smul_sub, smul_add, smul_add]; abel
    have hyz : u10h_ray D z x - z = s • (a - z) + t • (b - z) := by
      rw [← hy, u10h_combo_sub hst]
    have hxz' : x - z = u10h_rg D z x • (s • (a - z) + t • (b - z)) := by
      rw [← hyz]
      have := u10h_ray_spec hD hz hxz
      conv_lhs => rw [this]
      rw [add_sub_cancel_left]
    rw [u10h_cone, hβy, hxz', map_smul, map_add, map_smul, map_smul,
      u10h_linOfDet_left hab.ne', u10h_linOfDet_right hab.ne', add_comm]

/-- The cone map is positive PL on the fan triangulation. -/
theorem u10h_cone_isPositivePLOn {D : Set Plane} (hD : Link.IsDisc D) {z : Plane} (hz : z ∈ interior D)
    (z' : Plane) {V : Set Plane} {A : Plane → Plane → Prop} (hA : ∀ a b, A a b → u10h_Adj D z V a b)
    {β : Plane → Plane} (haff : ∀ a b, A a b → AffineOn β (segment ℝ a b))
    (hpos : ∀ a b, A a b → 0 < det (β a - z') (β b - z')) (K : Triangulation D)
    (hK : K.faces = u10h_fanFaces z A) : IsPositivePLOn (u10h_cone D z z' β) K := by
  intro T hT
  rw [hK] at hT
  obtain ⟨a, b, hab, hv⟩ := hT
  have hadj := hA a b hab
  have hc := u10h_carrier_of_v hv
  refine ⟨⟨u10h_linOfDet (a - z) (b - z) (β a - z') (β b - z'),
    z' - u10h_linOfDet (a - z) (b - z) (β a - z') (β b - z') z, ?_⟩, ?_⟩
  · intro x hx
    rw [hc] at hx
    rw [u10h_cone_eq_on_fan hD hz z' hadj.2.2.1 hadj.2.2.2.1 (haff a b hab) hx, map_sub]; abel
  · have h0 : T.v 0 = z := by simp [hv]
    have h1 : T.v 1 = a := by simp [hv]
    have h2 : T.v 2 = b := by simp [hv]
    rw [h0, h1, h2, u10h_cone_center,
      u10h_cone_frontier hD hz z' β (hadj.2.2.2.1 (left_mem_segment ℝ a b)),
      u10h_cone_frontier hD hz z' β (hadj.2.2.2.1 (right_mem_segment ℝ a b))]
    exact hpos a b hab

/-- The cone map is injective on `D`. -/
theorem u10h_cone_injOn {D D' : Set Plane} (hD : Link.IsDisc D) (hD' : Link.IsDisc D') {z z' : Plane}
    (hz : z ∈ interior D) (hz' : z' ∈ interior D') {β : Plane → Plane}
    (hβ : ∀ y ∈ frontier D, β y ∈ frontier D') (hinj : InjOn β (frontier D)) :
    InjOn (u10h_cone D z z' β) D := by
  have key : ∀ x, x ≠ z → u10h_cone D z z' β x ≠ z' := by
    intro x hx h
    have := u10h_rg_cone hD hD' hz hz' hβ hx
    rw [h, u10h_rg_self] at this
    exact u10h_rg_pos hD hz hx |>.ne this
  intro x₁ hx₁ x₂ hx₂ heq
  by_cases h₁ : x₁ = z
  · subst h₁
    by_contra h₂
    exact key x₂ (Ne.symm h₂) (heq.symm.trans (u10h_cone_center D x₁ z' β))
  by_cases h₂ : x₂ = z
  · subst h₂
    exact absurd (heq.trans (u10h_cone_center D x₂ z' β)) (key x₁ h₁)
  have hr : u10h_rg D z x₁ = u10h_rg D z x₂ := by
    rw [← u10h_rg_cone hD hD' hz hz' hβ h₁, ← u10h_rg_cone hD hD' hz hz' hβ h₂, heq]
  have hrpos := u10h_rg_pos hD hz h₁
  have hβeq : β (u10h_ray D z x₁) = β (u10h_ray D z x₂) := by
    unfold u10h_cone at heq
    rw [hr] at heq
    have := smul_right_injective Plane (hr ▸ hrpos).ne' (add_left_cancel heq)
    exact sub_left_injective this
  have hyeq := hinj (u10h_ray_mem_frontier hD hz h₁) (u10h_ray_mem_frontier hD hz h₂) hβeq
  rw [u10h_ray_spec hD hz h₁, u10h_ray_spec hD hz h₂, hr, hyeq]

/-- The cone map carries `D` onto `D'`. -/
theorem u10h_cone_image {D D' : Set Plane} (hD : Link.IsDisc D) (hD' : Link.IsDisc D') {z z' : Plane}
    (hz : z ∈ interior D) (hz' : z' ∈ interior D') {β : Plane → Plane}
    (hβ : ∀ y ∈ frontier D, β y ∈ frontier D') (hsurj : frontier D' ⊆ β '' frontier D) :
    u10h_cone D z z' β '' D = D' := by
  apply Set.Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    by_cases hxz : x = z
    · subst hxz; rw [u10h_cone_center]; exact interior_subset hz'
    · have hr0 := u10h_rg_nonneg D z x
      have hr1 := (u10h_rg_le_one_iff hD hz x).mpr hx
      have hy := u10h_frontier_subset hD' (hβ _ (u10h_ray_mem_frontier hD hz hxz))
      have := hD'.convex (interior_subset hz') hy (sub_nonneg.mpr hr1) hr0 (by ring)
      convert this using 1
      rw [u10h_cone, sub_smul, one_smul, smul_sub]; abel
  · intro x' hx'
    by_cases hx'z : x' = z'
    · exact ⟨z, interior_subset hz, by rw [u10h_cone_center, hx'z]⟩
    · obtain ⟨y, hy, hyβ⟩ := hsurj (u10h_ray_mem_frontier hD' hz' hx'z)
      have hr := u10h_rg_pos hD' hz' hx'z
      have hr1 := (u10h_rg_le_one_iff hD' hz' x').mpr hx'
      refine ⟨z + u10h_rg D' z' x' • (y - z), ?_, ?_⟩
      · rw [← u10h_rg_le_one_iff hD hz, u10h_rg_smul D z y hr.le, (u10h_rg_eq_one_iff hD hz y).mpr hy,
          mul_one]
        exact hr1
      · rw [u10h_cone_ray_formula hD hz z' β hy hr, hyβ]
        exact (u10h_ray_spec hD' hz' hx'z).symm

/-! ### the marks of a finite frontier cover -/

theorem u10h_gap {M : Set ℝ} (hM : M.Finite) (h0 : (0:ℝ) ∈ M) (h1 : (1:ℝ) ∈ M) {θ₀ : ℝ}
    (hθ : θ₀ ∈ Icc (0:ℝ) 1) :
    ∃ θa ∈ M, ∃ θb ∈ M, θa < θb ∧ θa ≤ θ₀ ∧ θ₀ ≤ θb ∧ ∀ θ ∈ M, θa < θ → θ < θb → False := by
  classical
  rcases hθ.2.lt_or_eq with hlt | heq
  · set Fa := hM.toFinset.filter (fun θ => θ ≤ θ₀) with hFa
    set Fb := hM.toFinset.filter (fun θ => θ₀ < θ) with hFb
    have hane : Fa.Nonempty := ⟨0, by simp [hFa, h0, hθ.1]⟩
    have hbne : Fb.Nonempty := ⟨1, by simp [hFb, h1, hlt]⟩
    have hamem := Finset.max'_mem Fa hane
    have hbmem := Finset.min'_mem Fb hbne
    simp only [hFa, Finset.mem_filter, Set.Finite.mem_toFinset] at hamem
    simp only [hFb, Finset.mem_filter, Set.Finite.mem_toFinset] at hbmem
    refine ⟨_, hamem.1, _, hbmem.1, by linarith [hamem.2, hbmem.2], hamem.2, hbmem.2.le, ?_⟩
    intro θ hθM hlo hhi
    rcases le_or_gt θ θ₀ with h | h
    · have hmem : θ ∈ Fa := by simp [hFa, hθM, h]
      have := Finset.le_max' Fa θ hmem
      exact absurd hlo (not_lt.mpr this)
    · have hmem : θ ∈ Fb := by simp [hFb, hθM, h]
      have := Finset.min'_le Fb θ hmem
      exact absurd hhi (not_lt.mpr this)
  · subst heq
    set Fa := hM.toFinset.filter (fun θ => θ < 1) with hFa
    have hane : Fa.Nonempty := ⟨0, by simp [hFa, h0]⟩
    have hamem := Finset.max'_mem Fa hane
    simp only [hFa, Finset.mem_filter, Set.Finite.mem_toFinset] at hamem
    refine ⟨_, hamem.1, 1, h1, hamem.2, hamem.2.le, le_rfl, ?_⟩
    intro θ hθM hlo hhi
    have hmem : θ ∈ Fa := by simp [hFa, hθM, hhi]
    have := Finset.le_max' Fa θ hmem
    exact absurd hlo (not_lt.mpr this)

/-- The marks: all endpoints of the segments of `S`. -/
noncomputable def u10h_marks (S : Finset (Plane × Plane)) : Set Plane :=
  ↑(S.image Prod.fst ∪ S.image Prod.snd)

theorem u10h_marks_finite (S : Finset (Plane × Plane)) : (u10h_marks S).Finite := Finset.finite_toSet _

theorem u10h_marks_left {S : Finset (Plane × Plane)} {p : Plane × Plane} (hp : p ∈ S) :
    p.1 ∈ u10h_marks S := by
  simp only [u10h_marks, Finset.coe_union, Finset.coe_image, mem_union, mem_image, Finset.mem_coe]
  exact Or.inl ⟨p, hp, rfl⟩

theorem u10h_marks_right {S : Finset (Plane × Plane)} {p : Plane × Plane} (hp : p ∈ S) :
    p.2 ∈ u10h_marks S := by
  simp only [u10h_marks, Finset.coe_union, Finset.coe_image, mem_union, mem_image, Finset.mem_coe]
  exact Or.inr ⟨p, hp, rfl⟩

theorem u10h_marks_subset_frontier {D : Set Plane} {S : Finset (Plane × Plane)}
    (hS : (⋃ p ∈ S, segment ℝ p.1 p.2) = frontier D) : u10h_marks S ⊆ frontier D := by
  intro c hc
  simp only [u10h_marks, Finset.coe_union, Finset.coe_image, mem_union, mem_image,
    Finset.mem_coe] at hc
  rw [← hS]
  rcases hc with ⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩
  · exact mem_iUnion₂.mpr ⟨p, hp, left_mem_segment ℝ _ _⟩
  · exact mem_iUnion₂.mpr ⟨p, hp, right_mem_segment ℝ _ _⟩

/-- The adjacent pairs actually used: adjacent marks lying in one segment of `S`. -/
def u10h_A (D : Set Plane) (z : Plane) (S : Finset (Plane × Plane)) (a b : Plane) : Prop :=
  u10h_Adj D z (u10h_marks S) a b ∧ ∃ p ∈ S, segment ℝ a b ⊆ segment ℝ p.1 p.2

theorem u10h_cover_of_segment {D : Set Plane} (hD : Link.IsDisc D) {z : Plane} (hz : z ∈ interior D)
    {S : Finset (Plane × Plane)} (hS : (⋃ p ∈ S, segment ℝ p.1 p.2) = frontier D) {p : Plane × Plane}
    (hp : p ∈ S) (hne : p.1 ≠ p.2) {y : Plane} (hy : y ∈ segment ℝ p.1 p.2) :
    ∃ a b, u10h_A D z S a b ∧ y ∈ segment ℝ a b := by
  have he : p.2 - p.1 ≠ 0 := sub_ne_zero.mpr hne.symm
  set f : ℝ → Plane := fun θ => p.1 + θ • (p.2 - p.1) with hf
  have hfinj : Function.Injective f := fun θ₁ θ₂ h => smul_left_injective ℝ he (add_left_cancel h)
  have hsegp : segment ℝ p.1 p.2 = f '' Icc 0 1 := segment_eq_image' ℝ p.1 p.2
  have hsegfr : segment ℝ p.1 p.2 ⊆ frontier D := hS ▸ subset_iUnion₂ (s := fun p _ => segment ℝ p.1 p.2) p hp
  set M : Set ℝ := f ⁻¹' u10h_marks S ∩ Icc 0 1 with hM
  have hMfin : M.Finite := ((u10h_marks_finite S).preimage hfinj.injOn).subset inter_subset_left
  have h0M : (0:ℝ) ∈ M := ⟨by simp [f, u10h_marks_left hp], by simp⟩
  have h1M : (1:ℝ) ∈ M := ⟨by simp [f, u10h_marks_right hp], by simp⟩
  rw [hsegp] at hy
  obtain ⟨θ₀, hθ₀, rfl⟩ := hy
  obtain ⟨θa, haM, θb, hbM, hlt, hle1, hle2, hgap⟩ := u10h_gap hMfin h0M h1M hθ₀
  have haV : f θa ∈ u10h_marks S := haM.1
  have hbV : f θb ∈ u10h_marks S := hbM.1
  have hap : f θa ∈ segment ℝ p.1 p.2 := hsegp ▸ ⟨θa, haM.2, rfl⟩
  have hbp : f θb ∈ segment ℝ p.1 p.2 := hsegp ▸ ⟨θb, hbM.2, rfl⟩
  have hsub : segment ℝ (f θa) (f θb) ⊆ segment ℝ p.1 p.2 := (convex_segment _ _).segment_subset hap hbp
  have hsegab : segment ℝ (f θa) (f θb) ⊆ frontier D := hsub.trans hsegfr
  have hneab : f θa ≠ f θb := fun h => hlt.ne (hfinj h)
  have hcomb : ∀ lam : ℝ, f θa + lam • (f θb - f θa) = f (θa + lam * (θb - θa)) := by
    intro lam
    simp only [hf]
    ext <;> simp <;> ring
  have hnomark : ∀ c ∈ u10h_marks S, c ∉ openSegment ℝ (f θa) (f θb) := by
    intro c hc hco
    rw [openSegment_eq_image'] at hco
    obtain ⟨lam, hlam, rfl⟩ := hco
    beta_reduce at hc
    rw [hcomb] at hc
    have hθc : θa + lam * (θb - θa) ∈ M := by
      refine ⟨hc, ?_, ?_⟩
      · nlinarith [haM.2.1, hlam.1.le, hlt.le]
      · nlinarith [hbM.2.2, hlam.2.le, hlt.le]
    exact hgap _ hθc (by nlinarith [hlam.1]) (by nlinarith [hlam.2])
  have hyab : f θ₀ ∈ segment ℝ (f θa) (f θb) := by
    rw [segment_eq_image']
    refine ⟨(θ₀ - θa) / (θb - θa), ⟨div_nonneg (by linarith) (by linarith),
      div_le_one_of_le₀ (by linarith) (by linarith)⟩, ?_⟩
    beta_reduce
    rw [hcomb]
    congr 1
    have hba : θb - θa ≠ 0 := by linarith
    field_simp
    ring
  have hdet := u10h_det_ne_zero_of_segment hD hz hneab hsegab
  rcases hdet.lt_or_gt with hneg | hpos
  · refine ⟨f θb, f θa, ⟨⟨hbV, haV, by rw [u10h_det_swap']; linarith, by rw [segment_symm]; exact hsegab,
      fun c hc => by rw [openSegment_symm]; exact hnomark c hc⟩, p, hp, by rw [segment_symm]; exact hsub⟩,
      by rw [segment_symm]; exact hyab⟩
  · exact ⟨f θa, f θb, ⟨⟨haV, hbV, hpos, hsegab, hnomark⟩, p, hp, hsub⟩, hyab⟩

/-! ### frontier points are not isolated; a nondegenerate segment through each -/

theorem u10h_ray_continuousAt {D : Set Plane} (hD : Link.IsDisc D) {z : Plane} (hz : z ∈ interior D)
    {x : Plane} (hx : x ≠ z) : ContinuousAt (u10h_ray D z) x := by
  have : u10h_ray D z = fun x => z + (u10h_rg D z x)⁻¹ • (x - z) := rfl
  rw [this]
  exact continuousAt_const.add
    ((((u10h_rg_continuous hD hz).continuousAt).inv₀ (u10h_rg_pos hD hz hx).ne').smul
      (continuousAt_id.sub continuousAt_const))

theorem u10h_not_isolated {D : Set Plane} (hD : Link.IsDisc D) {z : Plane} (hz : z ∈ interior D)
    {y : Plane} (hy : y ∈ frontier D) {ε : ℝ} (hε : 0 < ε) :
    ∃ w ∈ frontier D, w ≠ y ∧ dist w y < ε := by
  have hyz := u10h_frontier_ne hD hz hy
  have hu : y - z ≠ 0 := sub_ne_zero.mpr hyz
  set v : Plane := (-(y - z).2, (y - z).1) with hv
  have hdet : 0 < det (y - z) v := by
    have : det (y - z) v = (y - z).1 ^ 2 + (y - z).2 ^ 2 := by simp only [det, hv]; ring
    rw [this]
    rcases not_and_or.mp (fun hc : (y - z).1 = 0 ∧ (y - z).2 = 0 => hu (Prod.ext hc.1 hc.2)) with h1 | h2 <;>
      positivity
  set g : ℝ → Plane := fun t => u10h_ray D z (y + t • v) with hg
  have hg0 : g 0 = y := by simp [hg, u10h_ray_of_frontier hD hz hy]
  have hgc : ContinuousAt g 0 := by
    have h1 : ContinuousAt (fun t : ℝ => y + t • v) 0 := continuousAt_const.add (continuousAt_id.smul continuousAt_const)
    have h2 : ContinuousAt (u10h_ray D z) (y + (0:ℝ) • v) := by
      rw [zero_smul, add_zero]; exact u10h_ray_continuousAt hD hz hyz
    exact ContinuousAt.comp (f := fun t : ℝ => y + t • v) h2 h1
  obtain ⟨δ, hδ, hδε⟩ := Metric.continuousAt_iff.mp hgc ε hε
  have hpt : y + (δ / 2) • v ≠ z := by
    intro h
    have : det (y - z) (y + (δ / 2) • v - z) = 0 := by rw [h, sub_self, u10h_det_zero_right]
    rw [add_sub_right_comm, u10h_det_add_right, u10h_det_self, u10h_det_smul_right] at this
    have : 0 < δ / 2 * det (y - z) v := by positivity
    linarith
  refine ⟨g (δ / 2), u10h_ray_mem_frontier hD hz hpt, ?_, ?_⟩
  · intro h
    have h1 : det (y - z) (g (δ / 2) - z) = 0 := by rw [h, u10h_det_self]
    have h2 : g (δ / 2) - z = (u10h_rg D z (y + (δ / 2) • v))⁻¹ • ((δ / 2) • v + (y - z)) := by
      simp only [hg, u10h_ray, add_sub_cancel_left]; congr 1; abel
    rw [h2, u10h_det_smul_right, u10h_det_add_right, u10h_det_smul_right, u10h_det_self, add_zero] at h1
    have hr := u10h_rg_pos hD hz hpt
    have : 0 < (u10h_rg D z (y + (δ / 2) • v))⁻¹ * (δ / 2 * det (y - z) v) := by positivity
    linarith
  · have := hδε (x := δ / 2) (by rw [Real.dist_eq, sub_zero, abs_of_pos (by positivity)]; linarith)
    rwa [hg0] at this

theorem u10h_isClosed_segment (a b : Plane) : IsClosed (segment ℝ a b) := by
  rw [segment_eq_image']
  exact (isCompact_Icc.image (by fun_prop)).isClosed

theorem u10h_exists_nondeg {D : Set Plane} (hD : Link.IsDisc D) {z : Plane} (hz : z ∈ interior D)
    {S : Finset (Plane × Plane)} (hS : (⋃ p ∈ S, segment ℝ p.1 p.2) = frontier D) {y : Plane}
    (hy : y ∈ frontier D) : ∃ p ∈ S, p.1 ≠ p.2 ∧ y ∈ segment ℝ p.1 p.2 := by
  classical
  by_contra hcon
  have hdeg : ∀ p ∈ S, y ∈ segment ℝ p.1 p.2 → p.1 = p.2 := fun p hp hyp =>
    by_contra fun hne => hcon ⟨p, hp, hne, hyp⟩
  set U : Set Plane := ⋃ p ∈ S.filter (fun p => y ∉ segment ℝ p.1 p.2), segment ℝ p.1 p.2 with hU
  have hUc : IsClosed U := isClosed_biUnion_finset (fun p _ => u10h_isClosed_segment _ _)
  have hyU : y ∉ U := by
    intro h
    rw [hU, mem_iUnion₂] at h
    obtain ⟨p, hp, hyp⟩ := h
    exact (Finset.mem_filter.mp hp).2 hyp
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hUc.isOpen_compl y hyU
  obtain ⟨w, hw, hwy, hwd⟩ := u10h_not_isolated hD hz hy hε
  rw [← hS, mem_iUnion₂] at hw
  obtain ⟨p, hp, hwp⟩ := hw
  by_cases hyp : y ∈ segment ℝ p.1 p.2
  · have h12 := hdeg p hp hyp
    rw [h12, segment_same] at hyp hwp
    exact hwy (hwp.trans hyp.symm)
  · have hwU : w ∈ U := by
      rw [hU, mem_iUnion₂]
      exact ⟨p, Finset.mem_filter.mpr ⟨hp, hyp⟩, hwp⟩
    exact hball (Metric.mem_ball.mpr hwd) hwU

/-! ### coverage, a third mark, positivity from the cyclic order -/

theorem u10h_cover {D : Set Plane} (hD : Link.IsDisc D) {z : Plane} (hz : z ∈ interior D)
    {S : Finset (Plane × Plane)} (hS : (⋃ p ∈ S, segment ℝ p.1 p.2) = frontier D) {y : Plane}
    (hy : y ∈ frontier D) : ∃ a b, u10h_A D z S a b ∧ y ∈ segment ℝ a b := by
  obtain ⟨p, hp, hne, hyp⟩ := u10h_exists_nondeg hD hz hS hy
  exact u10h_cover_of_segment hD hz hS hp hne hyp

theorem u10h_det_neg_right (u v : Plane) : det u (-v) = -det u v := by
  simp only [det, Prod.fst_neg, Prod.snd_neg]; ring

theorem u10h_affine_combo {β : Plane → Plane} {M : Plane →ₗ[ℝ] Plane} {c a b : Plane}
    (hM : ∀ x ∈ segment ℝ a b, β x = M x + c) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (hst : s + t = 1) :
    β (s • a + t • b) = s • β a + t • β b := by
  rw [hM _ ⟨s, t, hs, ht, hst, rfl⟩, hM a (left_mem_segment ℝ a b), hM b (right_mem_segment ℝ a b),
    map_add, map_smul, map_smul, smul_add, smul_add]
  have hc : c = s • c + t • c := by rw [← add_smul, hst, one_smul]
  conv_lhs => rw [hc]
  abel

theorem u10h_affine_image_segment {β : Plane → Plane} {a b : Plane} (h : AffineOn β (segment ℝ a b)) :
    β '' segment ℝ a b = segment ℝ (β a) (β b) := by
  obtain ⟨M, c, hM⟩ := h
  ext w
  constructor
  · rintro ⟨x, ⟨s, t, hs, ht, hst, rfl⟩, rfl⟩
    exact ⟨s, t, hs, ht, hst, (u10h_affine_combo hM hs ht hst).symm⟩
  · rintro ⟨s, t, hs, ht, hst, rfl⟩
    exact ⟨s • a + t • b, ⟨s, t, hs, ht, hst, rfl⟩, u10h_affine_combo hM hs ht hst⟩

theorem u10h_third_mark {D : Set Plane} (hD : Link.IsDisc D) {z : Plane} (hz : z ∈ interior D)
    {S : Finset (Plane × Plane)} (hS : (⋃ p ∈ S, segment ℝ p.1 p.2) = frontier D) {a b : Plane}
    (hab : u10h_A D z S a b) : ∃ c ∈ u10h_marks S, c ≠ a ∧ c ≠ b := by
  have hadj := hab.1
  have hV := u10h_marks_subset_frontier hS
  have haz : a - z ≠ 0 := sub_ne_zero.mpr (u10h_frontier_ne hD hz (hV hadj.1))
  have hxz : z - (a - z) ≠ z := by
    intro h; apply haz; have := congrArg (fun w => z - w) h; simpa using this
  set y := u10h_ray D z (z - (a - z)) with hy_def
  have hy : y ∈ frontier D := u10h_ray_mem_frontier hD hz hxz
  have hyz' : y - z = (u10h_rg D z (z - (a - z)))⁻¹ • (-(a - z)) := by
    rw [hy_def, u10h_ray, add_sub_cancel_left]; congr 1; abel
  obtain ⟨c, d, hcd, hycd⟩ := u10h_cover hD hz hS hy
  have hynot : y ∉ segment ℝ a b := by
    rintro ⟨s, t, hs, ht, hst, hy'⟩
    have hyz : y - z = s • (a - z) + t • (b - z) := by rw [← hy', u10h_combo_sub hst]
    have h1 : det (a - z) (y - z) = t * det (a - z) (b - z) := by
      rw [hyz, u10h_det_comb_right, u10h_det_self]; ring
    have h2 : det (a - z) (y - z) = 0 := by
      rw [hyz', u10h_det_smul_right, u10h_det_neg_right, u10h_det_self]; ring
    have ht0 : t = 0 := (mul_eq_zero.mp (h1.symm.trans h2)).resolve_right hadj.2.2.1.ne'
    have hs1 : s = 1 := by linarith
    rw [ht0, hs1, one_smul, zero_smul, add_zero] at hy'
    rw [← hy', smul_neg] at hyz'
    have h3 : (1 + (u10h_rg D z (z - (a - z)))⁻¹) • (a - z) = 0 := by
      rw [add_smul, one_smul]
      nth_rewrite 1 [hyz']
      abel
    rcases smul_eq_zero.mp h3 with h | h
    · have := u10h_rg_pos hD hz hxz
      have : 0 < 1 + (u10h_rg D z (z - (a - z)))⁻¹ := by positivity
      linarith
    · exact haz h
  by_contra hcon
  have hall : ∀ c ∈ u10h_marks S, c = a ∨ c = b := by
    intro c hc
    by_contra h
    exact hcon ⟨c, hc, fun h1 => h (Or.inl h1), fun h2 => h (Or.inr h2)⟩
  have hsub : segment ℝ c d ⊆ segment ℝ a b := by
    rcases hall c hcd.1.1 with rfl | rfl <;> rcases hall d hcd.1.2.1 with rfl | rfl
    · rw [segment_same]; exact singleton_subset_iff.mpr (left_mem_segment ℝ _ _)
    · exact le_rfl
    · rw [segment_symm]
    · rw [segment_same]; exact singleton_subset_iff.mpr (right_mem_segment ℝ _ _)
  exact hynot (hsub hycd)


theorem u10h_pos_of_preserves {D D' : Set Plane} (hD : Link.IsDisc D) (hD' : Link.IsDisc D')
    {z z' : Plane} (hz : z ∈ interior D) (hz' : z' ∈ interior D') {S : Finset (Plane × Plane)}
    (hS : (⋃ p ∈ S, segment ℝ p.1 p.2) = frontier D) {β : Plane → Plane}
    (hβmap : ∀ y ∈ frontier D, β y ∈ frontier D') (hinj : InjOn β (frontier D))
    (haffS : ∀ p ∈ S, AffineOn β (segment ℝ p.1 p.2)) (hpos : PreservesCyclicPos D z z' β)
    {a b : Plane} (hab : u10h_A D z S a b) : 0 < det (β a - z') (β b - z') := by
  obtain ⟨hadj, p, hp, hsub⟩ := hab
  have hV := u10h_marks_subset_frontier hS
  have haff : AffineOn β (segment ℝ a b) := by
    obtain ⟨M, c, hM⟩ := haffS p hp
    exact ⟨M, c, fun x hx => hM x (hsub hx)⟩
  have himg := u10h_affine_image_segment haff
  have hseg' : segment ℝ (β a) (β b) ⊆ frontier D' := by
    rw [← himg]; rintro _ ⟨w, hw, rfl⟩; exact hβmap w (hadj.2.2.2.1 hw)
  have hane : a ≠ b := by
    intro h; have := hadj.2.2.1; rw [h, u10h_det_self] at this; exact lt_irrefl _ this
  have hane' : β a ≠ β b := fun h => hane (hinj (hV hadj.1) (hV hadj.2.1) h)
  have hdet' := u10h_det_ne_zero_of_segment hD' hz' hane' hseg'
  rcases hdet'.lt_or_gt with hneg | hpos'
  · exfalso
    obtain ⟨c, hcV, hca, hcb⟩ := u10h_third_mark hD hz hS ⟨hadj, p, hp, hsub⟩
    have hcyc : CyclicPos z a b c := by
      rcases u10h_adj_trichotomy hD hz hV hadj hcV with h | h | h | h
      · exact absurd h hca
      · exact absurd h hcb
      · exact Or.inr (Or.inr ⟨by rw [u10h_det_swap']; linarith, hadj.2.2.1⟩)
      · exact Or.inl ⟨hadj.2.2.1, by rw [u10h_det_swap']; linarith⟩
    have hcyc' := hpos a (hV hadj.1) b (hV hadj.2.1) c (hV hcV) hcyc
    have hba' : 0 < det (β b - z') (β a - z') := by rw [u10h_det_swap']; linarith
    rcases hcyc' with ⟨h1, -⟩ | ⟨h1, h2⟩ | ⟨-, h2⟩
    · linarith
    · have hsegba : segment ℝ (β b) (β a) ⊆ frontier D' := by rw [segment_symm]; exact hseg'
      have hmem := u10h_frontier_mem_segment hD' hz' hba' hsegba (hβmap c (hV hcV)) h1.le h2.le
      rw [segment_symm, ← himg] at hmem
      obtain ⟨w, hw, hwc⟩ := hmem
      have hwc' : w = c := hinj (hadj.2.2.2.1 hw) (hV hcV) hwc
      subst hwc'
      rcases u10h_mem_segment_cases hw with h | h | h
      · exact hca h
      · exact hcb h
      · exact hadj.2.2.2.2 w hcV h
    · linarith
  · exact hpos'

/-- U10 (sm-3:535-537, the fan extension on convex models): a finite positive PL homeomorphism
between the boundaries of two convex discs, preserving the cyclic order around interior points
`z ↦ z'`, extends to a positive PL homeomorphism of the discs (cone from `z` to `z'`). -/
theorem U10_fan_extension {D D' : Set Plane} (hD : Link.IsDisc D) (hD' : Link.IsDisc D')
    {z z' : Plane} (hz : z ∈ interior D) (hz' : z' ∈ interior D') {β : Plane → Plane}
    (hβ : IsHomeoOnto (frontier D) (frontier D') β) (hpl : IsFinitePLOnFrontier D β)
    (hpos : PreservesCyclicPos D z z' β) :
    ∃ (K : Triangulation D) (F : Plane → Plane), IsPositivePLOn F K ∧ IsHomeoOnto D D' F ∧
      ∀ x ∈ frontier D, F x = β x := by
  obtain ⟨e, he⟩ := hβ
  have hβmap : ∀ y ∈ frontier D, β y ∈ frontier D' := by
    intro y hy; have := (e ⟨y, hy⟩).2; rwa [he] at this
  have hinj : InjOn β (frontier D) := by
    intro y₁ h₁ y₂ h₂ heq
    have : e ⟨y₁, h₁⟩ = e ⟨y₂, h₂⟩ := Subtype.ext (by rw [he, he]; exact heq)
    exact congrArg Subtype.val (e.injective this)
  have hsurj : frontier D' ⊆ β '' frontier D := by
    intro w hw
    refine ⟨e.symm ⟨w, hw⟩, (e.symm ⟨w, hw⟩).2, ?_⟩
    rw [← he]; simp
  obtain ⟨S, hS, haffS⟩ := hpl
  have hV := u10h_marks_subset_frontier hS
  have hA : ∀ a b, u10h_A D z S a b → u10h_Adj D z (u10h_marks S) a b := fun a b h => h.1
  have hcov : ∀ y ∈ frontier D, ∃ a b, u10h_A D z S a b ∧ y ∈ segment ℝ a b :=
    fun y hy => u10h_cover hD hz hS hy
  obtain ⟨K, hK⟩ := u10h_fan_triangulation hD hz (u10h_marks_finite S) hV hA hcov
  have haff : ∀ a b, u10h_A D z S a b → AffineOn β (segment ℝ a b) := by
    rintro a b ⟨-, p, hp, hsub⟩
    obtain ⟨M, c, hM⟩ := haffS p hp
    exact ⟨M, c, fun x hx => hM x (hsub hx)⟩
  have hposdet : ∀ a b, u10h_A D z S a b → 0 < det (β a - z') (β b - z') :=
    fun a b h => u10h_pos_of_preserves hD hD' hz hz' hS hβmap hinj haffS hpos h
  have hPL := u10h_cone_isPositivePLOn hD hz z' hA haff hposdet K hK
  refine ⟨K, u10h_cone D z z' β, hPL, ?_, fun x hx => u10h_cone_frontier hD hz z' β hx⟩
  have := U2_isHomeoOnto_of_isPositivePLOn K hPL (u10h_cone_injOn hD hD' hz hz' hβmap hinj)
  rwa [u10h_cone_image hD hD' hz hz' hβmap hsurj] at this

/-! #### U10 helpers for `U10_boundary_map_of_lift` (circle in the closure, periodicity, the lift) -/

theorem u10h_coe_traversal_mem_circle [NeZero n] (P : LabelledTuple n) (x : ℝ) :
    ((traversal P x : Plane) : Sphere) ∈ sphereCircle P :=
  ⟨traversal P x, by rw [← U4_range_traversal P]; exact mem_range_self x, rfl⟩

/-! ### CyclicPos: rotation, antisymmetry, totality on a convex frontier -/

theorem u10h_cyclicPos_rotate {z a b c : Plane} (h : CyclicPos z a b c) : CyclicPos z b c a := by
  unfold CyclicPos at *; tauto

theorem u10h_cyclicPos_antisymm {z a b c : Plane} (h1 : CyclicPos z a b c) (h2 : CyclicPos z a c b) :
    False := by
  unfold CyclicPos at *
  have e1 := u10h_det_swap' (a - z) (b - z)
  have e2 := u10h_det_swap' (b - z) (c - z)
  have e3 := u10h_det_swap' (c - z) (a - z)
  rcases h1 with ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ <;> rcases h2 with ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ <;> linarith

theorem u10h_cyclicPos_ne {z a b c : Plane} (h : CyclicPos z a b c) : a ≠ b ∧ b ≠ c ∧ a ≠ c := by
  refine ⟨?_, ?_, ?_⟩ <;> rintro rfl <;> unfold CyclicPos at h
  · have := u10h_det_self (a - z); have := u10h_det_swap' (a - z) (c - z)
    rcases h with ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ <;> linarith
  · have := u10h_det_self (b - z); have := u10h_det_swap' (a - z) (b - z)
    rcases h with ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ <;> linarith
  · have := u10h_det_self (a - z); have := u10h_det_swap' (a - z) (b - z)
    rcases h with ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ <;> linarith

theorem u10h_eq_of_ray {D : Set Plane} (hD : Link.IsDisc D) {z : Plane} (hz : z ∈ interior D)
    {p r : Plane} (hp : p ∈ frontier D) (hr : r ∈ frontier D) {μ : ℝ} (hμ : 0 ≤ μ)
    (h : r - z = μ • (p - z)) : r = p := by
  have hr' : r = z + μ • (p - z) := by rw [← h]; abel
  have h1 := (u10h_rg_eq_one_iff hD hz r).mpr hr
  rw [hr', u10h_rg_smul D z p hμ, (u10h_rg_eq_one_iff hD hz p).mpr hp, mul_one] at h1
  rw [hr', h1, one_smul, add_sub_cancel]

theorem u10h_antipodal {D : Set Plane} (hD : Link.IsDisc D) {z : Plane} (hz : z ∈ interior D)
    {p q : Plane} (hp : p ∈ frontier D) (hq : q ∈ frontier D) (hne : q ≠ p)
    (h0 : det (p - z) (q - z) = 0) : ∃ lam : ℝ, 0 < lam ∧ q - z = -(lam • (p - z)) := by
  obtain ⟨μ, hμ⟩ := u10h_parallel_of_det_eq_zero (sub_ne_zero.mpr (u10h_frontier_ne hD hz hp)) h0
  rcases le_or_gt 0 μ with hμ0 | hμ0
  · exact absurd (u10h_eq_of_ray hD hz hp hq hμ0 hμ) hne
  · exact ⟨-μ, by linarith, by rw [hμ, neg_smul, neg_neg]⟩

theorem u10h_det_prod_pos {D : Set Plane} (hD : Link.IsDisc D) {z : Plane} (hz : z ∈ interior D)
    {p q r : Plane} (hp : p ∈ frontier D) (hq : q ∈ frontier D) (hr : r ∈ frontier D) (hqp : q ≠ p)
    (hrp : r ≠ p) (hrq : r ≠ q) (h0 : det (p - z) (q - z) = 0) :
    0 < det (q - z) (r - z) * det (r - z) (p - z) := by
  obtain ⟨lam, hlam, hq'⟩ := u10h_antipodal hD hz hp hq hqp h0
  have e : det (q - z) (r - z) = lam * det (r - z) (p - z) := by
    rw [hq', ← neg_smul, u10h_det_smul_left', u10h_det_swap' (p - z) (r - z)]; ring
  rw [e, mul_assoc]
  have hne : det (r - z) (p - z) ≠ 0 := by
    intro h
    have h' : det (p - z) (r - z) = 0 := by rw [u10h_det_swap']; linarith
    obtain ⟨μ, hμ⟩ := u10h_parallel_of_det_eq_zero (sub_ne_zero.mpr (u10h_frontier_ne hD hz hp)) h'
    rcases le_or_gt 0 μ with hμ0 | hμ0
    · exact hrp (u10h_eq_of_ray hD hz hp hr hμ0 hμ)
    · apply hrq
      refine u10h_eq_of_ray hD hz hq hr (μ := -μ / lam) (div_nonneg (by linarith) hlam.le) ?_
      rw [hμ, hq', smul_neg, smul_smul]
      have : -μ / lam * lam = -μ := div_mul_cancel₀ _ hlam.ne'
      rw [this, neg_smul, neg_neg]
  have : 0 < det (r - z) (p - z) * det (r - z) (p - z) := mul_self_pos.mpr hne
  positivity

theorem u10h_cyclicPos_total {D : Set Plane} (hD : Link.IsDisc D) {z : Plane} (hz : z ∈ interior D)
    {p q r : Plane} (hp : p ∈ frontier D) (hq : q ∈ frontier D) (hr : r ∈ frontier D) (hpq : p ≠ q)
    (hqr : q ≠ r) (hpr : p ≠ r) : CyclicPos z p q r ∨ CyclicPos z p r q := by
  have e1 := u10h_det_swap' (q - z) (p - z)
  have e2 := u10h_det_swap' (r - z) (q - z)
  have e3 := u10h_det_swap' (p - z) (r - z)
  unfold CyclicPos
  by_cases hA : det (p - z) (q - z) = 0
  · have := u10h_det_prod_pos hD hz hp hq hr hpq.symm hpr.symm hqr.symm hA
    rcases pos_and_pos_or_neg_and_neg_of_mul_pos this with ⟨hB, hC⟩ | ⟨hB, hC⟩
    · exact Or.inl (Or.inr (Or.inl ⟨hB, hC⟩))
    · exact Or.inr (Or.inl ⟨by linarith, by linarith⟩)
  by_cases hB : det (q - z) (r - z) = 0
  · have := u10h_det_prod_pos hD hz hq hr hp hqr.symm hpq hpr hB
    rcases pos_and_pos_or_neg_and_neg_of_mul_pos this with ⟨hC, hA'⟩ | ⟨hC, hA'⟩
    · exact Or.inl (Or.inr (Or.inr ⟨hC, hA'⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨by linarith, by linarith⟩))
  by_cases hC : det (r - z) (p - z) = 0
  · have := u10h_det_prod_pos hD hz hr hp hq hpr hqr hpq.symm hC
    rcases pos_and_pos_or_neg_and_neg_of_mul_pos this with ⟨hA', hB'⟩ | ⟨hA', hB'⟩
    · exact Or.inl (Or.inl ⟨hA', hB'⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨by linarith, by linarith⟩))
  rcases lt_or_gt_of_ne hA with hA | hA <;> rcases lt_or_gt_of_ne hB with hB | hB <;>
    rcases lt_or_gt_of_ne hC with hC | hC <;>
    first
    | exact Or.inl (Or.inl ⟨by linarith, by linarith⟩)
    | exact Or.inl (Or.inr (Or.inl ⟨by linarith, by linarith⟩))
    | exact Or.inl (Or.inr (Or.inr ⟨by linarith, by linarith⟩))
    | exact Or.inr (Or.inl ⟨by linarith, by linarith⟩)
    | exact Or.inr (Or.inr (Or.inl ⟨by linarith, by linarith⟩))
    | exact Or.inr (Or.inr (Or.inr ⟨by linarith, by linarith⟩))

/-! ### abstract refinement of finite interval covers -/

/-- `g : ℝ → Plane` is affine on `I`. -/
def u10h_AffOn (g : ℝ → Plane) (I : Set ℝ) : Prop := ∃ p u : Plane, ∀ t ∈ I, g t = p + t • u

theorem u10h_AffOn_mono {g : ℝ → Plane} {I J : Set ℝ} (h : u10h_AffOn g I) (hJ : J ⊆ I) :
    u10h_AffOn g J := by
  obtain ⟨p, u, h⟩ := h; exact ⟨p, u, fun t ht => h t (hJ ht)⟩

theorem u10h_gap' {B : Set ℝ} (hB : B.Finite) {lo hi : ℝ} (hlo : lo ∈ B) (hhi : hi ∈ B)
    (hlh : lo < hi) {t : ℝ} (ht : t ∈ Icc lo hi) :
    ∃ b ∈ B, ∃ b' ∈ B, b < b' ∧ b ≤ t ∧ t ≤ b' ∧ ∀ a ∈ B, b < a → a < b' → False := by
  classical
  rcases ht.2.lt_or_eq with hlt | heq
  · set Fa := hB.toFinset.filter (fun θ => θ ≤ t) with hFa
    set Fb := hB.toFinset.filter (fun θ => t < θ) with hFb
    have hane : Fa.Nonempty := ⟨lo, by simp [hFa, hlo, ht.1]⟩
    have hbne : Fb.Nonempty := ⟨hi, by simp [hFb, hhi, hlt]⟩
    have hamem := Finset.max'_mem Fa hane
    have hbmem := Finset.min'_mem Fb hbne
    simp only [hFa, Finset.mem_filter, Set.Finite.mem_toFinset] at hamem
    simp only [hFb, Finset.mem_filter, Set.Finite.mem_toFinset] at hbmem
    refine ⟨_, hamem.1, _, hbmem.1, by linarith [hamem.2, hbmem.2], hamem.2, hbmem.2.le, ?_⟩
    intro θ hθM hlo' hhi'
    rcases le_or_gt θ t with h | h
    · have hmem : θ ∈ Fa := by simp [hFa, hθM, h]
      exact absurd hlo' (not_lt.mpr (Finset.le_max' Fa θ hmem))
    · have hmem : θ ∈ Fb := by simp [hFb, hθM, h]
      exact absurd hhi' (not_lt.mpr (Finset.min'_le Fb θ hmem))
  · subst heq
    set Fa := hB.toFinset.filter (fun θ => θ < t) with hFa
    have hane : Fa.Nonempty := ⟨lo, by simp [hFa, hlo, hlh]⟩
    have hamem := Finset.max'_mem Fa hane
    simp only [hFa, Finset.mem_filter, Set.Finite.mem_toFinset] at hamem
    refine ⟨_, hamem.1, t, hhi, hamem.2, hamem.2.le, le_rfl, ?_⟩
    intro θ hθM hlo' hhi'
    have hmem : θ ∈ Fa := by simp [hFa, hθM, hhi']
    exact absurd hlo' (not_lt.mpr (Finset.le_max' Fa θ hmem))

/-- Midpoint argument: an interval with no breakpoint strictly inside lies in one covering piece. -/
theorem u10h_subset_piece {B : Set ℝ} {C : Set (ℝ × ℝ)} (hCB : ∀ c ∈ C, c.1 ∈ B ∧ c.2 ∈ B) {lo hi : ℝ}
    (hcov : ∀ t ∈ Icc lo hi, ∃ c ∈ C, t ∈ Icc c.1 c.2) {b b' : ℝ} (hb : lo ≤ b) (hb' : b' ≤ hi)
    (hlt : b < b') (hgap : ∀ a ∈ B, b < a → a < b' → False) : ∃ c ∈ C, Icc b b' ⊆ Icc c.1 c.2 := by
  obtain ⟨c, hc, hm⟩ := hcov ((b + b') / 2) ⟨by linarith, by linarith⟩
  refine ⟨c, hc, Icc_subset_Icc ?_ ?_⟩
  · rcases le_or_gt c.1 b with h | h
    · exact h
    · exact absurd (hgap c.1 (hCB c hc).1 h (by linarith [hm.1])) id
  · rcases le_or_gt b' c.2 with h | h
    · exact h
    · exact absurd (hgap c.2 (hCB c hc).2 (by linarith [hm.2]) h) id

/-- The linear map `w ↦ (⟪w, u⟫ / ⟪u, u⟫) • u''`. -/
noncomputable def u10h_dotLin (u u'' : Plane) : Plane →ₗ[ℝ] Plane where
  toFun w := (planeDot w u / planeDot u u) • u''
  map_add' v w := by
    have : planeDot (v + w) u = planeDot v u + planeDot w u := by
      simp only [planeDot, Prod.fst_add, Prod.snd_add]; ring
    rw [this, add_div, add_smul]
  map_smul' c w := by
    have : planeDot (c • w) u = c * planeDot w u := by
      simp only [planeDot, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring
    simp only [RingHom.id_apply]
    rw [this, mul_div_assoc, mul_smul]

theorem u10h_planeDot_self_pos {u : Plane} (hu : u ≠ 0) : 0 < planeDot u u := by
  have : planeDot u u = u.1 ^ 2 + u.2 ^ 2 := by simp only [planeDot]; ring
  rw [this]
  rcases not_and_or.mp (fun hc : u.1 = 0 ∧ u.2 = 0 => hu (Prod.ext hc.1 hc.2)) with h1 | h2 <;>
    positivity

theorem u10h_planeDot_add_smul (p u : Plane) (t : ℝ) :
    planeDot (p + t • u) u = planeDot p u + t * planeDot u u := by
  simp only [planeDot, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring

/-- A map that is affine in the parameter of an affinely parametrised segment is affine on it. -/
theorem u10h_affineOn_of_param {β : Plane → Plane} {c : ℝ → Plane} {b b' : ℝ} {p u p'' u'' : Plane}
    (hc : ∀ t ∈ Icc b b', c t = p + t • u) (hβ : ∀ t ∈ Icc b b', β (c t) = p'' + t • u'')
    (hbb : b ≤ b') : AffineOn β (c '' Icc b b') := by
  by_cases hu : u = 0
  · refine ⟨0, p'' + b • u'', ?_⟩
    rintro _ ⟨t, ht, rfl⟩
    have : c t = c b := by rw [hc t ht, hc b ⟨le_rfl, hbb⟩, hu, smul_zero, smul_zero]
    rw [this, hβ b ⟨le_rfl, hbb⟩, LinearMap.zero_apply, zero_add]
  · have hpos := u10h_planeDot_self_pos hu
    refine ⟨u10h_dotLin u u'', p'' - (planeDot p u / planeDot u u) • u'', ?_⟩
    rintro _ ⟨t, ht, rfl⟩
    rw [hβ t ht]
    have : u10h_dotLin u u'' (c t) = (planeDot p u / planeDot u u) • u'' + t • u'' := by
      change (planeDot (c t) u / planeDot u u) • u'' = _
      rw [hc t ht, u10h_planeDot_add_smul, add_div, mul_div_assoc, div_self hpos.ne', mul_one, add_smul]
    rw [this]; abel

theorem u10h_image_Icc_eq_segment {c : ℝ → Plane} {b b' : ℝ} {p u : Plane}
    (hc : ∀ t ∈ Icc b b', c t = p + t • u) (hbb : b ≤ b') :
    c '' Icc b b' = segment ℝ (c b) (c b') := by
  rw [segment_eq_image']
  ext w
  constructor
  · rintro ⟨t, ht, rfl⟩
    rcases hbb.lt_or_eq with hlt | heq
    · refine ⟨(t - b) / (b' - b), ⟨div_nonneg (by linarith [ht.1]) (by linarith),
        div_le_one_of_le₀ (by linarith [ht.2]) (by linarith)⟩, ?_⟩
      rw [hc t ht, hc b ⟨le_rfl, hbb⟩, hc b' ⟨hbb, le_rfl⟩]
      have hne : b' - b ≠ 0 := by linarith
      ext
      · simp only [Prod.fst_add, Prod.smul_fst, Prod.fst_sub, smul_eq_mul]; field_simp; ring
      · simp only [Prod.snd_add, Prod.smul_snd, Prod.snd_sub, smul_eq_mul]; field_simp; ring
    · subst heq
      have : t = b := le_antisymm ht.2 ht.1
      subst this
      exact ⟨0, ⟨le_rfl, zero_le_one⟩, by simp⟩
  · rintro ⟨θ, hθ, rfl⟩
    refine ⟨b + θ * (b' - b), ⟨by nlinarith [hθ.1], by nlinarith [hθ.2]⟩, ?_⟩
    rw [hc _ ⟨by nlinarith [hθ.1], by nlinarith [hθ.2]⟩, hc b ⟨le_rfl, hbb⟩, hc b' ⟨hbb, le_rfl⟩]
    ext
    · simp only [Prod.fst_add, Prod.smul_fst, Prod.fst_sub, smul_eq_mul]; ring
    · simp only [Prod.snd_add, Prod.smul_snd, Prod.snd_sub, smul_eq_mul]; ring

theorem u10h_circle_subset_closure [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Embedded P)
    (s : Side) {L : ℝ} (hL : InsideModel L P) : sphereCircle P ⊆ closure (regionOf P s) := by
  obtain ⟨A⟩ := U6_exists_ambientParam hn P hP hL
  have hcl : IsClosed A.T₀.carrier := by
    show IsClosed (convexHull ℝ (range A.T₀.v))
    exact ((Set.finite_range A.T₀.v).isCompact_convexHull ℝ).isClosed
  cases s with
  | inner =>
    show sphereCircle P ⊆ closure (interiorRegion P)
    rw [U7_closure_interiorRegion_eq hn P hP A]
    rintro _ ⟨w, hw, rfl⟩
    rw [← A.boundary] at hw
    obtain ⟨v, hv, rfl⟩ := hw
    exact ⟨A.H v, ⟨v, hcl.frontier_subset hv, rfl⟩, rfl⟩
  | outer =>
    show sphereCircle P ⊆ closure (exteriorRegion P)
    rw [U8_closure_exteriorRegion_eq hn P hP A]
    rintro _ ⟨w, hw, rfl⟩ ⟨_, ⟨v, hv, rfl⟩, hvw⟩
    rw [← A.boundary] at hw
    obtain ⟨u, hu, rfl⟩ := hw
    have : v = u := A.H.injective (OnePoint.coe_eq_coe.mp hvw)
    subst this
    exact hu.2 hv

theorem u10h_traversal_add_int_mul [NeZero n] (P : LabelledTuple n) (x : ℝ) (m : ℤ) :
    traversal P (x + m * n) = traversal P x := by
  induction m using Int.induction_on with
  | zero => simp
  | succ k ih =>
    push_cast at ih ⊢
    rw [show x + ((k : ℝ) + 1) * n = (x + k * n) + n by ring, traversal_add_nat, ih]
  | pred k ih =>
    push_cast at ih ⊢
    have := traversal_add_nat P (x + (-(k : ℝ) - 1) * n)
    rw [show x + (-(k : ℝ) - 1) * n + n = x + -(k : ℝ) * n by ring] at this
    rw [← this, ih]

theorem u10h_lift_shift_same {n n' : ℕ} {φ : ℝ → ℝ} (h : ∀ x, φ (x + n) = φ x + n') (x : ℝ) (m : ℤ) :
    φ (x + m * n) = φ x + m * n' := by
  induction m using Int.induction_on with
  | zero => simp
  | succ k ih =>
    push_cast at ih ⊢
    rw [show x + ((k : ℝ) + 1) * n = (x + k * n) + n by ring, h, ih]; ring
  | pred k ih =>
    push_cast at ih ⊢
    have := h (x + (-(k : ℝ) - 1) * n)
    rw [show x + (-(k : ℝ) - 1) * n + n = x + -(k : ℝ) * n by ring, ih] at this
    linarith

theorem u10h_lift_shift_opp {n n' : ℕ} {φ : ℝ → ℝ} (h : ∀ x, φ (x + n) = φ x - n') (x : ℝ) (m : ℤ) :
    φ (x + m * n) = φ x - m * n' := by
  induction m using Int.induction_on with
  | zero => simp
  | succ k ih =>
    push_cast at ih ⊢
    rw [show x + ((k : ℝ) + 1) * n = (x + k * n) + n by ring, h, ih]; ring
  | pred k ih =>
    push_cast at ih ⊢
    have := h (x + (-(k : ℝ) - 1) * n)
    rw [show x + (-(k : ℝ) - 1) * n + n = x + -(k : ℝ) * n by ring, ih] at this
    linarith

theorem u10h_isHomeoOnto_injOn {α β : Type*} [TopologicalSpace α] [TopologicalSpace β] {S : Set α}
    {S' : Set β} {f : α → β} (h : IsHomeoOnto S S' f) : InjOn f S := by
  obtain ⟨e, he⟩ := h
  intro x hx y hy hxy
  have : e ⟨x, hx⟩ = e ⟨y, hy⟩ := Subtype.ext (by rw [he, he]; exact hxy)
  exact congrArg Subtype.val (e.injective this)

/-- Two parameters give the same point of the parametrised frontier iff they differ by a multiple
of the period. -/
theorem u10h_param_eq_iff [NeZero n] (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Embedded P) {s : Side}
    {D : Set Plane} {f : Sphere → Plane} (hf : IsHomeoOnto (closure (regionOf P s)) D f)
    (hBS : sphereCircle P ⊆ closure (regionOf P s)) (x y : ℝ) :
    f ((traversal P x : Plane) : Sphere) = f ((traversal P y : Plane) : Sphere) ↔
      ∃ m : ℤ, y = x + m * n := by
  constructor
  · intro h
    have h1 := u10h_isHomeoOnto_injOn hf (hBS (u10h_coe_traversal_mem_circle P x))
      (hBS (u10h_coe_traversal_mem_circle P y)) h
    exact hP.traversal_injective hn (OnePoint.coe_eq_coe.mp h1)
  · rintro ⟨m, rfl⟩
    rw [u10h_traversal_add_int_mul]

theorem u10h_reduce {n : ℕ} (hn : 0 < n) (x : ℝ) : ∃ x₀ ∈ Ico (0:ℝ) n, ∃ m : ℤ, x = x₀ + m * n := by
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  refine ⟨x - ⌊x / n⌋ * n, ⟨?_, ?_⟩, ⌊x / n⌋, by ring⟩
  · have := Int.floor_le (x / n)
    have : (⌊x / n⌋ : ℝ) * n ≤ x / n * n := by nlinarith
    rw [div_mul_cancel₀ _ hn'.ne'] at this
    linarith
  · have := Int.lt_floor_add_one (x / n)
    have : x / n * n < ((⌊x / n⌋ : ℝ) + 1) * n := by nlinarith
    rw [div_mul_cancel₀ _ hn'.ne'] at this
    linarith

/-- A positive boundary lift is onto. -/
theorem u10h_lift_surj [NeZero n] {n' : ℕ} [NeZero n'] {P : LabelledTuple n} {s : Side}
    {P' : LabelledTuple n'} {s' : Side} {φ : ℝ → ℝ} (hφ : IsPositiveBoundaryLift P s P' s' φ) :
    Function.Surjective φ := by
  have hn : (0:ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have hn' : (0:ℝ) < n' := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n')
  intro v
  by_cases hsame : (traversalPositiveFor P s ↔ traversalPositiveFor P' s')
  · obtain ⟨-, hper⟩ := hφ.same hsame
    obtain ⟨m₁, hm₁⟩ := exists_int_lt ((v - φ 0) / n')
    obtain ⟨m₂, hm₂⟩ := exists_int_gt ((v - φ 0) / n')
    have h1 : φ (m₁ * n) ≤ v := by
      have := u10h_lift_shift_same hper 0 m₁; rw [zero_add] at this; rw [this]
      have : (m₁ : ℝ) * n' < v - φ 0 := by rwa [lt_div_iff₀ hn'] at hm₁
      linarith
    have h2 : v ≤ φ (m₂ * n) := by
      have := u10h_lift_shift_same hper 0 m₂; rw [zero_add] at this; rw [this]
      have : v - φ 0 < (m₂ : ℝ) * n' := by rwa [div_lt_iff₀ hn'] at hm₂
      linarith
    have hm : (m₁ : ℝ) * n ≤ m₂ * n := by
      have : (m₁ : ℝ) < m₂ := by linarith
      nlinarith
    obtain ⟨x, -, hx⟩ := intermediate_value_Icc hm hφ.continuous.continuousOn ⟨h1, h2⟩
    exact ⟨x, hx⟩
  · obtain ⟨-, hper⟩ := hφ.opposite hsame
    obtain ⟨m₁, hm₁⟩ := exists_int_lt ((φ 0 - v) / n')
    obtain ⟨m₂, hm₂⟩ := exists_int_gt ((φ 0 - v) / n')
    have h1 : v ≤ φ (m₁ * n) := by
      have := u10h_lift_shift_opp hper 0 m₁; rw [zero_add] at this; rw [this]
      have : (m₁ : ℝ) * n' < φ 0 - v := by rwa [lt_div_iff₀ hn'] at hm₁
      linarith
    have h2 : φ (m₂ * n) ≤ v := by
      have := u10h_lift_shift_opp hper 0 m₂; rw [zero_add] at this; rw [this]
      have : φ 0 - v < (m₂ : ℝ) * n' := by rwa [div_lt_iff₀ hn'] at hm₂
      linarith
    have hm : (m₁ : ℝ) * n ≤ m₂ * n := by
      have : (m₁ : ℝ) < m₂ := by linarith
      nlinarith
    obtain ⟨x, -, hx⟩ := intermediate_value_Icc' hm hφ.continuous.continuousOn ⟨h2, h1⟩
    exact ⟨x, hx⟩

/-- The parameter set of edge piece `[k, k+1]` inside a face `T`. -/
def u10h_J [NeZero n] (P : LabelledTuple n) (k : ℤ) (T : Triangle) : Set ℝ :=
  {t | t ∈ Icc (k : ℝ) (k + 1) ∧ traversal P t ∈ T.carrier}

theorem u10h_J_ordConnected [NeZero n] (P : LabelledTuple n) (k : ℤ) (T : Triangle) :
    (u10h_J P k T).OrdConnected := by
  refine ⟨fun t₁ h₁ t₂ h₂ t ht => ⟨⟨by linarith [h₁.1.1, ht.1], by linarith [h₂.1.2, ht.2]⟩, ?_⟩⟩
  have hconv : Convex ℝ T.carrier := convex_convexHull ℝ _
  have e1 := ea_traversal_eq_on_Icc P k h₁.1.1 h₁.1.2
  have e2 := ea_traversal_eq_on_Icc P k h₂.1.1 h₂.1.2
  have e := ea_traversal_eq_on_Icc P k (by linarith [h₁.1.1, ht.1] : (k:ℝ) ≤ t)
    (by linarith [h₂.1.2, ht.2] : t ≤ k + 1)
  rcases (ht.1.trans ht.2).lt_or_eq with hlt | heq
  · have hmem : traversal P t ∈ segment ℝ (traversal P t₁) (traversal P t₂) := by
      rw [segment_eq_image']
      refine ⟨(t - t₁) / (t₂ - t₁), ⟨div_nonneg (by linarith [ht.1]) (by linarith),
        div_le_one_of_le₀ (by linarith [ht.2]) (by linarith)⟩, ?_⟩
      rw [e1, e2, e]
      have hne : t₂ - t₁ ≠ 0 := by linarith
      ext
      · simp only [Prod.fst_add, Prod.smul_fst, Prod.fst_sub, smul_eq_mul]; field_simp; ring
      · simp only [Prod.snd_add, Prod.smul_snd, Prod.snd_sub, smul_eq_mul]; field_simp; ring
    exact hconv.segment_subset h₁.2 h₂.2 hmem
  · have : t = t₁ := le_antisymm (heq ▸ ht.2) ht.1
    rw [this]; exact h₁.2

theorem u10h_J_isCompact [NeZero n] (P : LabelledTuple n) (k : ℤ) (T : Triangle) :
    IsCompact (u10h_J P k T) := by
  have hT : IsClosed T.carrier := by
    show IsClosed (convexHull ℝ (range T.v))
    exact ((Set.finite_range T.v).isCompact_convexHull ℝ).isClosed
  exact isCompact_Icc.of_isClosed_subset (isClosed_Icc.inter (hT.preimage (continuous_traversal P)))
    (fun t ht => ht.1)

theorem u10h_J_eq_Icc [NeZero n] (P : LabelledTuple n) (k : ℤ) (T : Triangle)
    (hne : (u10h_J P k T).Nonempty) :
    u10h_J P k T = Icc (sInf (u10h_J P k T)) (sSup (u10h_J P k T)) :=
  eq_Icc_of_connected_compact ⟨hne, (u10h_J_ordConnected P k T).isPreconnected⟩ (u10h_J_isCompact P k T)

theorem u10h_modelChart_false (L : ℝ) (x : Plane) : modelChart L false x = (x : Sphere) := rfl

/-- On a piece, `f ∘ ↑ ∘ traversal` is affine in the parameter. -/
theorem u10h_affOn_J [NeZero n] (P : LabelledTuple n) {L : ℝ} {S : Set Sphere} {f : Sphere → Plane}
    {K : Triangulation (chartPart L false S)} (hK : IsPositivePLOn (f ∘ modelChart L false) K)
    (k : ℤ) {T : Triangle} (hT : T ∈ K.faces) :
    u10h_AffOn (fun t => f ((traversal P t : Plane) : Sphere)) (u10h_J P k T) := by
  obtain ⟨M, b₀, hM⟩ := (hK T hT).1
  refine ⟨M (P (k : ZMod n)) - (k : ℝ) • M (edge P (k : ZMod n)) + b₀, M (edge P (k : ZMod n)), ?_⟩
  intro t ht
  have := hM _ ht.2
  simp only [Function.comp, u10h_modelChart_false] at this
  show f ((traversal P t : Plane) : Sphere) = _
  rw [this, ea_traversal_eq_on_Icc P k ht.1.1 ht.1.2, map_add, map_smul]
  simp only [sub_smul]
  abel

theorem u10h_supNorm_combo {x y : Plane} {L a b : ℝ} (hx : supNorm x ≤ L) (hy : supNorm y ≤ L)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) : supNorm (a • x + b • y) ≤ L := by
  have h1 : |x.1| ≤ L := le_trans (le_max_left _ _) hx
  have h2 : |x.2| ≤ L := le_trans (le_max_right _ _) hx
  have h3 : |y.1| ≤ L := le_trans (le_max_left _ _) hy
  have h4 : |y.2| ≤ L := le_trans (le_max_right _ _) hy
  unfold supNorm
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  apply max_le
  · calc |a * x.1 + b * y.1| ≤ |a * x.1| + |b * y.1| := abs_add_le _ _
      _ = a * |x.1| + b * |y.1| := by rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
      _ ≤ a * L + b * L := by gcongr
      _ = L := by rw [← add_mul, hab, one_mul]
  · calc |a * x.2 + b * y.2| ≤ |a * x.2| + |b * y.2| := abs_add_le _ _
      _ = a * |x.2| + b * |y.2| := by rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
      _ ≤ a * L + b * L := by gcongr
      _ = L := by rw [← add_mul, hab, one_mul]

/-- Every traversal point lies in the plane chart part of the closed region. -/
theorem u10h_traversal_mem_chartPart [NeZero n] (P : LabelledTuple n) {L : ℝ} (hL : InsideModel L P)
    {S : Set Sphere} (hBS : sphereCircle P ⊆ S) (t : ℝ) :
    traversal P t ∈ chartPart L false S := by
  refine ⟨?_, hBS (u10h_coe_traversal_mem_circle P t)⟩
  show supNorm (traversal P t) ≤ L
  have h0 : (⌊t⌋ : ℝ) ≤ t := Int.floor_le t
  have h1 : t ≤ ⌊t⌋ + 1 := (Int.lt_floor_add_one t).le
  rw [ea_traversal_eq_on_Icc P ⌊t⌋ h0 h1, edge]
  have : P (⌊t⌋ : ZMod n) + (t - ⌊t⌋) • (P ((⌊t⌋ : ZMod n) + 1) - P (⌊t⌋ : ZMod n)) =
      (1 - (t - ⌊t⌋)) • P (⌊t⌋ : ZMod n) + (t - ⌊t⌋) • P ((⌊t⌋ : ZMod n) + 1) := by
    simp only [sub_smul, one_smul, smul_sub]; abel
  rw [this]
  exact u10h_supNorm_combo (hL _).le (hL _).le (by linarith) (by linarith) (by ring)

/-- The P-side pieces: one parameter interval per edge `k < n` and face `T` meeting it. -/
def u10h_pieceSet [NeZero n] (P : LabelledTuple n) (K : Set Triangle) : Set (ℝ × ℝ) :=
  {c | ∃ k : ℕ, k < n ∧ ∃ T ∈ K, (u10h_J P k T).Nonempty ∧ c = (sInf (u10h_J P k T), sSup (u10h_J P k T))}

theorem u10h_pieceSet_finite [NeZero n] (P : LabelledTuple n) {K : Set Triangle} (hK : K.Finite) :
    (u10h_pieceSet P K).Finite := by
  have : u10h_pieceSet P K ⊆
      (fun q : ℕ × Triangle => (sInf (u10h_J P q.1 q.2), sSup (u10h_J P q.1 q.2))) ''
        ({k | k < n} ×ˢ K) := by
    rintro c ⟨k, hk, T, hT, -, rfl⟩
    exact ⟨(k, T), ⟨hk, hT⟩, rfl⟩
  exact ((Set.finite_lt_nat n).prod hK).image _ |>.subset this

theorem u10h_pieceSet_affOn [NeZero n] (P : LabelledTuple n) {L : ℝ} {S : Set Sphere}
    {f : Sphere → Plane} {K : Triangulation (chartPart L false S)}
    (hK : IsPositivePLOn (f ∘ modelChart L false) K) {c : ℝ × ℝ} (hc : c ∈ u10h_pieceSet P K.faces) :
    u10h_AffOn (fun t => f ((traversal P t : Plane) : Sphere)) (Icc c.1 c.2) := by
  obtain ⟨k, -, T, hT, hne, rfl⟩ := hc
  have := u10h_affOn_J P hK k hT
  rwa [u10h_J_eq_Icc P k T hne] at this

theorem u10h_pieceSet_cover [NeZero n] (P : LabelledTuple n) {L : ℝ} (hL : InsideModel L P)
    {S : Set Sphere} (hBS : sphereCircle P ⊆ S) (K : Triangulation (chartPart L false S)) {t : ℝ}
    (ht : t ∈ Icc (0:ℝ) n) : ∃ c ∈ u10h_pieceSet P K.faces, t ∈ Icc c.1 c.2 := by
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  -- choose the edge index
  obtain ⟨k, hk, hkt⟩ : ∃ k : ℕ, k < n ∧ t ∈ Icc (k : ℝ) (k + 1) := by
    rcases ht.2.lt_or_eq with hlt | heq
    · refine ⟨⌊t⌋.toNat, ?_, ?_⟩
      · have h1 : ⌊t⌋ < n := Int.floor_lt.mpr hlt
        have h2 : (0:ℤ) ≤ ⌊t⌋ := Int.floor_nonneg.mpr ht.1
        omega
      · have h2 : (0:ℤ) ≤ ⌊t⌋ := Int.floor_nonneg.mpr ht.1
        have : ((⌊t⌋.toNat : ℤ) : ℝ) = (⌊t⌋ : ℝ) := by rw [Int.toNat_of_nonneg h2]
        push_cast at this
        rw [this]
        exact ⟨Int.floor_le t, (Int.lt_floor_add_one t).le⟩
    · refine ⟨n - 1, by omega, ?_⟩
      have : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega)]; simp
      rw [this, heq]
      constructor <;> linarith
  have hmem := u10h_traversal_mem_chartPart P hL hBS t
  rw [← K.cover, mem_iUnion₂] at hmem
  obtain ⟨T, hT, hTt⟩ := hmem
  have hJ : t ∈ u10h_J P k T := ⟨by exact_mod_cast hkt, hTt⟩
  refine ⟨(sInf (u10h_J P k T), sSup (u10h_J P k T)), ⟨k, hk, T, hT, ⟨t, hJ⟩, rfl⟩, ?_⟩
  have := u10h_J_eq_Icc P k T ⟨t, hJ⟩
  rw [← this]; exact hJ

/-- The P′-side pieces pulled back through `φ`: parameters `t ∈ [lo, hi]` with `φ t` in the `m`-th
translate of the edge piece `[k', k'+1]` and `traversal P' (φ t)` in the face `T'`. -/
def u10h_J' {n' : ℕ} [NeZero n'] (P' : LabelledTuple n') (φ : ℝ → ℝ) (lo hi : ℝ) (k' m : ℤ)
    (T' : Triangle) : Set ℝ :=
  Icc lo hi ∩ φ ⁻¹' ((fun u => u - m * n') ⁻¹' u10h_J P' k' T')

theorem u10h_J'_ordConnected {n' : ℕ} [NeZero n'] (P' : LabelledTuple n') {φ : ℝ → ℝ}
    (hφ : Monotone φ ∨ Antitone φ) (lo hi : ℝ) (k' m : ℤ) (T' : Triangle) :
    (u10h_J' P' φ lo hi k' m T').OrdConnected := by
  have hg : Monotone (fun u : ℝ => u - m * n') := fun a b h => sub_le_sub_right h _
  have h1 := (u10h_J_ordConnected P' k' T').preimage_mono hg
  rcases hφ with hφ | hφ
  · exact ordConnected_Icc.inter (h1.preimage_mono hφ)
  · exact ordConnected_Icc.inter (h1.preimage_anti hφ)

theorem u10h_J'_isCompact {n' : ℕ} [NeZero n'] (P' : LabelledTuple n') {φ : ℝ → ℝ} (hφ : Continuous φ)
    (lo hi : ℝ) (k' m : ℤ) (T' : Triangle) : IsCompact (u10h_J' P' φ lo hi k' m T') := by
  have hcl : IsClosed ((fun u : ℝ => u - m * n') ⁻¹' u10h_J P' k' T') :=
    (u10h_J_isCompact P' k' T').isClosed.preimage (continuous_id.sub continuous_const)
  exact isCompact_Icc.of_isClosed_subset (isClosed_Icc.inter (hcl.preimage hφ)) inter_subset_left

theorem u10h_J'_eq_Icc {n' : ℕ} [NeZero n'] (P' : LabelledTuple n') {φ : ℝ → ℝ} (hφc : Continuous φ)
    (hφ : Monotone φ ∨ Antitone φ) (lo hi : ℝ) (k' m : ℤ) (T' : Triangle)
    (hne : (u10h_J' P' φ lo hi k' m T').Nonempty) :
    u10h_J' P' φ lo hi k' m T' = Icc (sInf (u10h_J' P' φ lo hi k' m T')) (sSup (u10h_J' P' φ lo hi k' m T')) :=
  eq_Icc_of_connected_compact ⟨hne, (u10h_J'_ordConnected P' hφ lo hi k' m T').isPreconnected⟩
    (u10h_J'_isCompact P' hφc lo hi k' m T')

/-- On a P′-piece, `f' ∘ ↑ ∘ traversal P' ∘ φ` is affine in `φ t`. -/
theorem u10h_affOn_J' {n' : ℕ} [NeZero n'] (P' : LabelledTuple n') (φ : ℝ → ℝ) (lo hi : ℝ) {L' : ℝ}
    {S' : Set Sphere} {f' : Sphere → Plane} {K' : Triangulation (chartPart L' false S')}
    (hK' : IsPositivePLOn (f' ∘ modelChart L' false) K') (k' m : ℤ) {T' : Triangle} (hT' : T' ∈ K'.faces) :
    ∃ p'' u'' : Plane, ∀ t ∈ u10h_J' P' φ lo hi k' m T',
      f' ((traversal P' (φ t) : Plane) : Sphere) = p'' + φ t • u'' := by
  obtain ⟨M, b₀, hM⟩ := (hK' T' hT').1
  refine ⟨M (P' (k' : ZMod n')) - ((m : ℝ) * n' + k') • M (edge P' (k' : ZMod n')) + b₀,
    M (edge P' (k' : ZMod n')), ?_⟩
  rintro t ⟨-, ht⟩
  change (φ t - m * n') ∈ Icc (k' : ℝ) (k' + 1) ∧ traversal P' (φ t - m * n') ∈ T'.carrier at ht
  have hper : traversal P' (φ t) = traversal P' (φ t - m * n') := by
    have := u10h_traversal_add_int_mul P' (φ t - m * n') m
    rwa [sub_add_cancel] at this
  have := hM _ ht.2
  simp only [Function.comp, u10h_modelChart_false] at this
  rw [hper, this, ea_traversal_eq_on_Icc P' k' ht.1.1 ht.1.2, map_add, map_smul]
  simp only [sub_smul, add_smul]
  abel

theorem u10h_J'_cover {n' : ℕ} [NeZero n'] (P' : LabelledTuple n') (φ : ℝ → ℝ) (lo hi : ℝ) {L' : ℝ}
    (hL' : InsideModel L' P') {S' : Set Sphere} (hBS' : sphereCircle P' ⊆ S')
    (K' : Triangulation (chartPart L' false S')) {t : ℝ} (ht : t ∈ Icc lo hi) :
    ∃ k' m : ℤ, 0 ≤ k' ∧ k' < n' ∧ ∃ T' ∈ K'.faces, t ∈ u10h_J' P' φ lo hi k' m T' := by
  have hn' : (0:ℝ) < n' := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n')
  obtain ⟨v, hv, m, hvm⟩ := u10h_reduce (Nat.pos_of_ne_zero (NeZero.ne n')) (φ t)
  have hv' : φ t - m * n' = v := by linarith
  refine ⟨⌊v⌋, m, Int.floor_nonneg.mpr hv.1, ?_, ?_⟩
  · have : (⌊v⌋ : ℝ) < n' := by linarith [Int.floor_le v, hv.2]
    exact_mod_cast this
  · have hmem := u10h_traversal_mem_chartPart P' hL' hBS' v
    rw [← K'.cover, mem_iUnion₂] at hmem
    obtain ⟨T', hT', hTv⟩ := hmem
    refine ⟨T', hT', ht, ?_⟩
    change (φ t - m * n') ∈ Icc (⌊v⌋ : ℝ) (⌊v⌋ + 1) ∧ traversal P' (φ t - m * n') ∈ T'.carrier
    rw [hv']
    exact ⟨⟨Int.floor_le v, (Int.lt_floor_add_one v).le⟩, hTv⟩

/-- The P′-side piece set (endpoints of the nonempty pieces, `0 ≤ k' < n'`). -/
def u10h_pieceSet' {n' : ℕ} [NeZero n'] (P' : LabelledTuple n') (φ : ℝ → ℝ) (lo hi : ℝ)
    (K' : Set Triangle) : Set (ℝ × ℝ) :=
  {c | ∃ k' m : ℤ, 0 ≤ k' ∧ k' < n' ∧ ∃ T' ∈ K', (u10h_J' P' φ lo hi k' m T').Nonempty ∧
    c = (sInf (u10h_J' P' φ lo hi k' m T'), sSup (u10h_J' P' φ lo hi k' m T'))}

theorem u10h_pieceSet'_finite {n' : ℕ} [NeZero n'] (P' : LabelledTuple n') {φ : ℝ → ℝ}
    (hφ : Monotone φ ∨ Antitone φ) (lo hi : ℝ) {K' : Set Triangle} (hK' : K'.Finite) :
    (u10h_pieceSet' P' φ lo hi K').Finite := by
  have hn' : (0:ℝ) < n' := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n')
  set A := min (φ lo) (φ hi)
  set B := max (φ lo) (φ hi)
  have hbound : ∀ t ∈ Icc lo hi, A ≤ φ t ∧ φ t ≤ B := by
    intro t ht
    rcases hφ with hφ | hφ
    · exact ⟨le_trans (min_le_left _ _) (hφ ht.1), le_trans (hφ ht.2) (le_max_right _ _)⟩
    · exact ⟨le_trans (min_le_right _ _) (hφ ht.2), le_trans (hφ ht.1) (le_max_left _ _)⟩
  set m₁ : ℤ := ⌈(A - n') / n'⌉
  set m₂ : ℤ := ⌊B / n'⌋
  have hsub : u10h_pieceSet' P' φ lo hi K' ⊆
      (fun q : (ℤ × ℤ) × Triangle => (sInf (u10h_J' P' φ lo hi q.1.1 q.1.2 q.2),
        sSup (u10h_J' P' φ lo hi q.1.1 q.1.2 q.2))) '' ((Ico 0 (n' : ℤ) ×ˢ Icc m₁ m₂) ×ˢ K') := by
    rintro c ⟨k', m, hk0, hk1, T', hT', ⟨t, ht⟩, rfl⟩
    refine ⟨((k', m), T'), ⟨⟨⟨hk0, hk1⟩, ?_, ?_⟩, hT'⟩, rfl⟩
    · obtain ⟨hA, -⟩ := hbound t ht.1
      have h2 : (k' : ℝ) + 1 ≤ n' := by
        have : k' + 1 ≤ (n' : ℤ) := hk1
        exact_mod_cast this
      have h3 : φ t - m * n' ≤ k' + 1 := ht.2.1.2
      apply Int.ceil_le.mpr
      rw [div_le_iff₀ hn']
      linarith
    · obtain ⟨-, hB⟩ := hbound t ht.1
      have h0 : (0:ℝ) ≤ k' := by exact_mod_cast hk0
      have h3 : (k' : ℝ) ≤ φ t - m * n' := ht.2.1.1
      apply Int.le_floor.mpr
      rw [le_div_iff₀ hn']
      linarith
  exact (((Set.finite_Ico _ _).prod (Set.finite_Icc _ _)).prod hK').image _ |>.subset hsub

theorem u10h_frontier_param [NeZero n] {P : LabelledTuple n} {D : Set Plane} {f : Sphere → Plane}
    (hB : f '' sphereCircle P = frontier D) {a : Plane} (ha : a ∈ frontier D) :
    ∃ x ∈ Ico (0:ℝ) n, f ((traversal P x : Plane) : Sphere) = a := by
  rw [← hB] at ha
  obtain ⟨_, ⟨w, hw, rfl⟩, rfl⟩ := ha
  rw [← U4_range_traversal P] at hw
  obtain ⟨x₁, rfl⟩ := hw
  obtain ⟨x₀, hx₀, m, rfl⟩ := u10h_reduce (Nat.pos_of_ne_zero (NeZero.ne n)) x₁
  exact ⟨x₀, hx₀, by rw [u10h_traversal_add_int_mul]⟩

theorem u10h_param_ne [NeZero n] (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Embedded P) {s : Side}
    {D : Set Plane} {f : Sphere → Plane} (hf : IsHomeoOnto (closure (regionOf P s)) D f)
    (hBS : sphereCircle P ⊆ closure (regionOf P s)) {u v : ℝ} (huv : u < v) (hvu : v < u + n) :
    f ((traversal P u : Plane) : Sphere) ≠ f ((traversal P v : Plane) : Sphere) := by
  intro h
  obtain ⟨m, hm⟩ := (u10h_param_eq_iff hn hP hf hBS u v).mp h
  have hn0 : (0:ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have h1 : (0:ℝ) < m * n := by linarith
  have h2 : (m:ℝ) * n < 1 * n := by linarith
  have h3 : (0:ℝ) < m := by
    by_contra h
    have : (m:ℝ) * n ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (not_lt.mp h) hn0.le
    linarith
  have h4 : (m:ℝ) < 1 := lt_of_mul_lt_mul_right h2 hn0.le
  have h5 : (0:ℤ) < m := by exact_mod_cast h3
  have h6 : m < (1:ℤ) := by exact_mod_cast h4
  omega

/-- The two ordered cases of cyclic-order preservation (parameters `x < y < w < x + n`). -/
theorem u10h_pres_ordered [NeZero n] {n' : ℕ} [NeZero n'] (hn : 3 ≤ n) (P : LabelledTuple n)
    (hP : Embedded P) (hn' : 3 ≤ n') (P' : LabelledTuple n') (hP' : Embedded P') (s s' : Side)
    {L L' : ℝ} (hL : InsideModel L P) (hL' : InsideModel L' P') {D D' : Set Plane}
    {f f' : Sphere → Plane} (hD : Link.IsDisc D) (hD' : Link.IsDisc D')
    (hf : IsHomeoOnto (closure (regionOf P s)) D f) (hf' : IsHomeoOnto (closure (regionOf P' s')) D' f')
    (hB : f '' sphereCircle P = frontier D) (hB' : f' '' sphereCircle P' = frontier D')
    (hpl : IsPositivePLToPlane L (closure (regionOf P s)) f)
    (hpl' : IsPositivePLToPlane L' (closure (regionOf P' s')) f')
    {φ : ℝ → ℝ} (hφ : IsPositiveBoundaryLift P s P' s' φ) {z z' : Plane} (hz : z ∈ interior D)
    (hz' : z' ∈ interior D') {x y w : ℝ} (hxy : x < y) (hyw : y < w) (hwx : w < x + n) :
    (CyclicPos z (f ((traversal P x : Plane) : Sphere)) (f ((traversal P y : Plane) : Sphere))
        (f ((traversal P w : Plane) : Sphere)) →
      CyclicPos z' (f' ((traversal P' (φ x) : Plane) : Sphere)) (f' ((traversal P' (φ y) : Plane) : Sphere))
        (f' ((traversal P' (φ w) : Plane) : Sphere))) ∧
    (CyclicPos z (f ((traversal P x : Plane) : Sphere)) (f ((traversal P w : Plane) : Sphere))
        (f ((traversal P y : Plane) : Sphere)) →
      CyclicPos z' (f' ((traversal P' (φ x) : Plane) : Sphere)) (f' ((traversal P' (φ w) : Plane) : Sphere))
        (f' ((traversal P' (φ y) : Plane) : Sphere))) := by
  have hBS' := u10h_circle_subset_closure hn' P' hP' s' hL'
  have hfr' : ∀ u, f' ((traversal P' u : Plane) : Sphere) ∈ frontier D' := fun u =>
    hB' ▸ mem_image_of_mem f' (u10h_coe_traversal_mem_circle P' u)
  have hiff := U9_traversalPositiveFor_iff_cyclicPos hn P hP s hL hD hf hB hpl hz hxy hyw hwx
  by_cases hsame : (traversalPositiveFor P s ↔ traversalPositiveFor P' s')
  · obtain ⟨hmono, hper⟩ := hφ.same hsame
    have h1 : φ x < φ y := hmono hxy
    have h2 : φ y < φ w := hmono hyw
    have h3 : φ w < φ x + n' := by have := hmono hwx; rwa [hper] at this
    have hiff' := U9_traversalPositiveFor_iff_cyclicPos hn' P' hP' s' hL' hD' hf' hB' hpl' hz' h1 h2 h3
    constructor
    · intro hc
      exact hiff'.mp (hsame.mp (hiff.mpr hc))
    · intro hc
      have hnot : ¬ traversalPositiveFor P s := fun ht => u10h_cyclicPos_antisymm (hiff.mp ht) hc
      have hnot' : ¬ CyclicPos z' _ _ _ := fun hc' => hnot (hsame.mpr (hiff'.mpr hc'))
      rcases u10h_cyclicPos_total hD' hz' (hfr' (φ x)) (hfr' (φ y)) (hfr' (φ w))
        (u10h_param_ne hn' hP' hf' hBS' h1 (by linarith)) (u10h_param_ne hn' hP' hf' hBS' h2 (by linarith))
        (u10h_param_ne hn' hP' hf' hBS' (h1.trans h2) h3) with h | h
      · exact absurd h hnot'
      · exact h
  · obtain ⟨hanti, hper⟩ := hφ.opposite hsame
    have h1 : φ y < φ x := hanti hxy
    have h2 : φ w < φ y := hanti hyw
    have h3 : φ x - n' < φ w := by have := hanti hwx; rwa [hper] at this
    have hiff' := U9_traversalPositiveFor_iff_cyclicPos hn' P' hP' s' hL' hD' hf' hB' hpl' hz' h2 h1
      (by linarith)
    have hopp : traversalPositiveFor P s ↔ ¬ traversalPositiveFor P' s' := by tauto
    constructor
    · intro hc
      have hnot' : ¬ CyclicPos z' _ _ _ := fun hc' => (hopp.mp (hiff.mpr hc)) (hiff'.mpr hc')
      rcases u10h_cyclicPos_total hD' hz' (hfr' (φ x)) (hfr' (φ y)) (hfr' (φ w))
        (u10h_param_ne hn' hP' hf' hBS' h1 (by linarith)).symm
        (u10h_param_ne hn' hP' hf' hBS' h2 (by linarith)).symm
        (u10h_param_ne hn' hP' hf' hBS' (h2.trans h1) (by linarith)).symm with h | h
      · exact h
      · exact absurd (u10h_cyclicPos_rotate h) hnot'
    · intro hc
      have hnot : ¬ traversalPositiveFor P s := fun ht => u10h_cyclicPos_antisymm (hiff.mp ht) hc
      have hpos' : traversalPositiveFor P' s' := by tauto
      exact u10h_cyclicPos_rotate (u10h_cyclicPos_rotate (hiff'.mp hpos'))

theorem u10h_preservesCyclicPos [NeZero n] {n' : ℕ} [NeZero n'] (hn : 3 ≤ n) (P : LabelledTuple n)
    (hP : Embedded P) (hn' : 3 ≤ n') (P' : LabelledTuple n') (hP' : Embedded P') (s s' : Side)
    {L L' : ℝ} (hL : InsideModel L P) (hL' : InsideModel L' P') {D D' : Set Plane}
    {f f' : Sphere → Plane} (hD : Link.IsDisc D) (hD' : Link.IsDisc D')
    (hf : IsHomeoOnto (closure (regionOf P s)) D f) (hf' : IsHomeoOnto (closure (regionOf P' s')) D' f')
    (hB : f '' sphereCircle P = frontier D) (hB' : f' '' sphereCircle P' = frontier D')
    (hpl : IsPositivePLToPlane L (closure (regionOf P s)) f)
    (hpl' : IsPositivePLToPlane L' (closure (regionOf P' s')) f')
    {φ : ℝ → ℝ} (hφ : IsPositiveBoundaryLift P s P' s' φ) {z z' : Plane} (hz : z ∈ interior D)
    (hz' : z' ∈ interior D') {β : Plane → Plane}
    (hβc : ∀ x, β (f ((traversal P x : Plane) : Sphere)) = f' ((traversal P' (φ x) : Plane) : Sphere)) :
    PreservesCyclicPos D z z' β := by
  intro a ha b hb c hc habc
  obtain ⟨x, hx, rfl⟩ := u10h_frontier_param hB ha
  obtain ⟨y, hy, rfl⟩ := u10h_frontier_param hB hb
  obtain ⟨w, hw, rfl⟩ := u10h_frontier_param hB hc
  obtain ⟨hab, hbc, hac⟩ := u10h_cyclicPos_ne habc
  have hxy : x ≠ y := fun h => hab (by rw [h])
  have hyw : y ≠ w := fun h => hbc (by rw [h])
  have hxw : x ≠ w := fun h => hac (by rw [h])
  rw [hβc, hβc, hβc]
  have key := fun {x y w : ℝ} (hxy : x < y) (hyw : y < w) (hwx : w < x + n) =>
    u10h_pres_ordered hn P hP hn' P' hP' s s' hL hL' hD hD' hf hf' hB hB' hpl hpl' hφ hz hz' hxy hyw hwx
  have hn0 : (0:ℝ) ≤ n := by positivity
  rcases lt_or_gt_of_ne hxy with h1 | h1 <;> rcases lt_or_gt_of_ne hyw with h2 | h2 <;>
    rcases lt_or_gt_of_ne hxw with h3 | h3
  · exact (key h1 h2 (by linarith [hw.2, hx.1])).1 habc
  · exact absurd (h1.trans h2) (not_lt.mpr h3.le)
  · exact (key h3 h2 (by linarith [hy.2, hx.1])).2 habc
  · have := (key h3 h1 (by linarith [hy.2, hw.1])).1 (u10h_cyclicPos_rotate (u10h_cyclicPos_rotate habc))
    exact u10h_cyclicPos_rotate this
  · have := (key h1 h3 (by linarith [hw.2, hy.1])).2 (u10h_cyclicPos_rotate habc)
    exact u10h_cyclicPos_rotate (u10h_cyclicPos_rotate this)
  · have := (key h2 h3 (by linarith [hx.2, hy.1])).1 (u10h_cyclicPos_rotate habc)
    exact u10h_cyclicPos_rotate (u10h_cyclicPos_rotate this)
  · exact absurd (h2.trans h1) (not_lt.mpr h3.le)
  · have := (key h2 h1 (by linarith [hx.2, hw.1])).2 (u10h_cyclicPos_rotate (u10h_cyclicPos_rotate habc))
    exact u10h_cyclicPos_rotate this

theorem u10h_continuousOn_of_isHomeoOnto {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    {S : Set α} {S' : Set β} {f : α → β} (h : IsHomeoOnto S S' f) : ContinuousOn f S := by
  obtain ⟨e, he⟩ := h
  rw [continuousOn_iff_continuous_restrict]
  have : S.domRestrict f = fun x => (e x : β) := by funext x; exact (he x).symm
  rw [this]
  exact continuous_subtype_val.comp e.continuous

/-- The boundary map induced by a positive lift is a homeomorphism of the model frontiers. -/
theorem u10h_boundary_homeo [NeZero n] {n' : ℕ} [NeZero n'] (hn : 3 ≤ n) (P : LabelledTuple n)
    (hP : Embedded P) (hn' : 3 ≤ n') (P' : LabelledTuple n') (hP' : Embedded P') (s s' : Side)
    {L L' : ℝ} (hL : InsideModel L P) (hL' : InsideModel L' P') {D D' : Set Plane}
    {f f' : Sphere → Plane} (hD : Link.IsDisc D) (hD' : Link.IsDisc D')
    (hf : IsHomeoOnto (closure (regionOf P s)) D f) (hf' : IsHomeoOnto (closure (regionOf P' s')) D' f')
    (hB : f '' sphereCircle P = frontier D) (hB' : f' '' sphereCircle P' = frontier D')
    {φ : ℝ → ℝ} (hφ : IsPositiveBoundaryLift P s P' s' φ) {β : Plane → Plane}
    (hβc : ∀ x, β (f ((traversal P x : Plane) : Sphere)) = f' ((traversal P' (φ x) : Plane) : Sphere)) :
    IsHomeoOnto (frontier D) (frontier D') β := by
  have hBS := u10h_circle_subset_closure hn P hP s hL
  have hBS' := u10h_circle_subset_closure hn' P' hP' s' hL'
  have hfr : ∀ t, f ((traversal P t : Plane) : Sphere) ∈ frontier D := fun t =>
    hB ▸ mem_image_of_mem f (u10h_coe_traversal_mem_circle P t)
  have hfr' : ∀ u, f' ((traversal P' u : Plane) : Sphere) ∈ frontier D' := fun u =>
    hB' ▸ mem_image_of_mem f' (u10h_coe_traversal_mem_circle P' u)
  have hc : Continuous fun t => f ((traversal P t : Plane) : Sphere) :=
    (u10h_continuousOn_of_isHomeoOnto hf).comp_continuous
      (OnePoint.continuous_coe.comp (continuous_traversal P))
      (fun t => hBS (u10h_coe_traversal_mem_circle P t))
  have hc' : Continuous fun t => f' ((traversal P' (φ t) : Plane) : Sphere) :=
    (u10h_continuousOn_of_isHomeoOnto hf').comp_continuous
      (OnePoint.continuous_coe.comp ((continuous_traversal P').comp hφ.continuous))
      (fun t => hBS' (u10h_coe_traversal_mem_circle P' (φ t)))
  have hβfr : ∀ w ∈ frontier D, β w ∈ frontier D' := by
    intro w hw
    obtain ⟨x, -, rfl⟩ := u10h_frontier_param hB hw
    rw [hβc]; exact hfr' _
  -- the map on subtypes
  let e₀ : frontier D → frontier D' := fun w => ⟨β w, hβfr w w.2⟩
  have hinj : Function.Injective e₀ := by
    rintro ⟨w₁, hw₁⟩ ⟨w₂, hw₂⟩ h
    have h' : β w₁ = β w₂ := congrArg Subtype.val h
    obtain ⟨x, -, rfl⟩ := u10h_frontier_param hB hw₁
    obtain ⟨y, -, rfl⟩ := u10h_frontier_param hB hw₂
    rw [hβc, hβc] at h'
    obtain ⟨m, hm⟩ := (u10h_param_eq_iff hn' hP' hf' hBS' (φ x) (φ y)).mp h'
    apply Subtype.ext
    show f _ = f _
    rw [u10h_param_eq_iff hn hP hf hBS]
    by_cases hsame : (traversalPositiveFor P s ↔ traversalPositiveFor P' s')
    · obtain ⟨hmono, hper⟩ := hφ.same hsame
      refine ⟨m, hmono.injective ?_⟩
      rw [u10h_lift_shift_same hper, hm]
    · obtain ⟨hanti, hper⟩ := hφ.opposite hsame
      refine ⟨-m, hanti.injective ?_⟩
      rw [u10h_lift_shift_opp hper, hm]; push_cast; ring
  have hsurj : Function.Surjective e₀ := by
    rintro ⟨w', hw'⟩
    obtain ⟨u, -, rfl⟩ := u10h_frontier_param hB' hw'
    obtain ⟨x, rfl⟩ := u10h_lift_surj hφ u
    exact ⟨⟨_, hfr x⟩, Subtype.ext (hβc x)⟩
  have hcont : Continuous e₀ := by
    rw [continuous_iff_isClosed]
    intro C hC
    obtain ⟨C₀, hC₀, rfl⟩ := isClosed_induced_iff.mp hC
    have hKc : IsCompact ((fun t => f ((traversal P t : Plane) : Sphere)) ''
        ((fun t => f' ((traversal P' (φ t) : Plane) : Sphere)) ⁻¹' C₀ ∩ Icc (0:ℝ) n)) :=
      (isCompact_Icc.inter_left (hC₀.preimage hc')).image hc
    have : e₀ ⁻¹' (Subtype.val ⁻¹' C₀) = Subtype.val ⁻¹' ((fun t => f ((traversal P t : Plane) : Sphere)) ''
        ((fun t => f' ((traversal P' (φ t) : Plane) : Sphere)) ⁻¹' C₀ ∩ Icc (0:ℝ) n)) := by
      ext ⟨w, hw⟩
      simp only [mem_preimage, e₀]
      constructor
      · intro h
        obtain ⟨x, hx, rfl⟩ := u10h_frontier_param hB hw
        rw [hβc] at h
        exact ⟨x, ⟨h, hx.1, hx.2.le⟩, rfl⟩
      · rintro ⟨x, ⟨hx, -⟩, hxw⟩
        show β w ∈ C₀
        rw [← hxw, hβc]; exact hx
    rw [this]
    exact hKc.isClosed.preimage continuous_subtype_val
  have : CompactSpace (frontier D) :=
    isCompact_iff_compactSpace.mp (hD.isCompact.of_isClosed_subset isClosed_frontier (u10h_frontier_subset hD))
  exact ⟨Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective e₀ ⟨hinj, hsurj⟩) hcont, fun w => rfl⟩

theorem u10h_marks_mono {m : ℕ} {a : ℕ → ℝ} (hainc : ∀ j < m, a j < a (j + 1)) :
    ∀ i j, i ≤ j → j ≤ m → a i ≤ a j := by
  intro i j hij hjm
  induction j with
  | zero =>
    have : i = 0 := by omega
    rw [this]
  | succ j ih =>
    rcases Nat.lt_or_ge i (j + 1) with h | h
    · exact (ih (by omega) (by omega)).trans (hainc j (by omega)).le
    · have : i = j + 1 := by omega
      rw [this]

theorem u10h_marks_cover {m : ℕ} {a : ℕ → ℝ} (hainc : ∀ j < m, a j < a (j + 1)) (hm : 1 ≤ m) :
    ∀ t ∈ Icc (a 0) (a m), ∃ j < m, t ∈ Icc (a j) (a (j + 1)) := by
  suffices h : ∀ j, 1 ≤ j → j ≤ m → ∀ t ∈ Icc (a 0) (a j), ∃ i < j, t ∈ Icc (a i) (a (i + 1)) from
    h m hm le_rfl
  intro j hj1 hjm
  induction j with
  | zero => omega
  | succ j ih =>
    intro t ht
    rcases Nat.eq_zero_or_pos j with hj | hj
    · subst hj; exact ⟨0, by omega, ht⟩
    · rcases le_or_gt t (a j) with h | h
      · obtain ⟨i, hi, hti⟩ := ih hj (by omega) t ⟨ht.1, h⟩
        exact ⟨i, by omega, hti⟩
      · exact ⟨j, by omega, h.le, ht.2⟩

/-- The induced boundary map is finite PL on the frontier of the model. -/
theorem u10h_finitePL [NeZero n] {n' : ℕ} [NeZero n'] (hn : 3 ≤ n) (P : LabelledTuple n)
    (hP : Embedded P) (hn' : 3 ≤ n') (P' : LabelledTuple n') (hP' : Embedded P') (s s' : Side)
    {L L' : ℝ} (hL : InsideModel L P) (hL' : InsideModel L' P') {D : Set Plane}
    {f f' : Sphere → Plane} (hB : f '' sphereCircle P = frontier D)
    (hpl : IsPositivePLToPlane L (closure (regionOf P s)) f)
    (hpl' : IsPositivePLToPlane L' (closure (regionOf P' s')) f')
    {φ : ℝ → ℝ} (hφ : IsPositiveBoundaryLift P s P' s' φ) (hfin : IsFinitePL n φ) {β : Plane → Plane}
    (hβc : ∀ x, β (f ((traversal P x : Plane) : Sphere)) = f' ((traversal P' (φ x) : Plane) : Sphere)) :
    IsFinitePLOnFrontier D β := by
  classical
  have hBS := u10h_circle_subset_closure hn P hP s hL
  have hBS' := u10h_circle_subset_closure hn' P' hP' s' hL'
  have hn0 : (0:ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have hfr : ∀ t, f ((traversal P t : Plane) : Sphere) ∈ frontier D := fun t =>
    hB ▸ mem_image_of_mem f (u10h_coe_traversal_mem_circle P t)
  obtain ⟨K, hK⟩ := hpl false
  obtain ⟨K', hK'⟩ := hpl' false
  obtain ⟨m, a, ha0, ham, hainc, haff⟩ := hfin
  have hmono : Monotone φ ∨ Antitone φ := by
    by_cases hsame : (traversalPositiveFor P s ↔ traversalPositiveFor P' s')
    · exact Or.inl (hφ.same hsame).1.monotone
    · exact Or.inr (hφ.opposite hsame).1.antitone
  have hφc : Continuous φ := hφ.continuous
  have hm1 : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · exfalso; subst h; rw [ha0] at ham; linarith
    · exact h
  set c : ℝ → Plane := fun t => f ((traversal P t : Plane) : Sphere) with hc_def
  -- the three covers of `[0, n]`
  set C₁ := u10h_pieceSet P K.faces with hC₁
  set C₂ : Set (ℝ × ℝ) := (fun j : ℕ => (a j, a (j + 1))) '' {j | j < m} with hC₂
  set C₃ := u10h_pieceSet' P' φ 0 n K'.faces with hC₃
  have hC₁fin : C₁.Finite := u10h_pieceSet_finite P K.finite
  have hC₂fin : C₂.Finite := (Set.finite_lt_nat m).image _
  have hC₃fin : C₃.Finite := u10h_pieceSet'_finite P' hmono 0 n K'.finite
  have hC₁in : ∀ q ∈ C₁, 0 ≤ q.1 ∧ q.1 ≤ q.2 ∧ q.2 ≤ n := by
    rintro q ⟨k, hk, T, hT, hne, rfl⟩
    have hcpt := u10h_J_isCompact P k T
    have h1 := hcpt.sInf_mem hne
    have h2 := hcpt.sSup_mem hne
    have h1' := h1.1.1
    have h2' := h2.1.2
    have h12 : sInf (u10h_J P k T) ≤ sSup (u10h_J P k T) :=
      csInf_le_csSup hne hcpt.bddBelow hcpt.bddAbove
    push_cast at h1' h2'
    have hk1 : (k:ℝ) + 1 ≤ n := by
      have : (k + 1 : ℕ) ≤ n := hk
      exact_mod_cast this
    exact ⟨(by positivity : (0:ℝ) ≤ k).trans h1', h12, h2'.trans hk1⟩
  have hC₂in : ∀ q ∈ C₂, 0 ≤ q.1 ∧ q.1 ≤ q.2 ∧ q.2 ≤ n := by
    rintro q ⟨j, hj, rfl⟩
    have hmo := u10h_marks_mono hainc
    refine ⟨?_, (hainc j hj).le, ?_⟩
    · rw [← ha0]; exact hmo 0 j (Nat.zero_le _) hj.le
    · rw [← ham]; exact hmo (j + 1) m hj le_rfl
  have hC₃in : ∀ q ∈ C₃, 0 ≤ q.1 ∧ q.1 ≤ q.2 ∧ q.2 ≤ n := by
    rintro q ⟨k', mm, hk0, hk1, T', hT', hne, rfl⟩
    have hcpt := u10h_J'_isCompact P' hφc 0 n k' mm T'
    have h1 := hcpt.sInf_mem hne
    have h2 := hcpt.sSup_mem hne
    exact ⟨h1.1.1, csInf_le_csSup hne hcpt.bddBelow hcpt.bddAbove, h2.1.2⟩
  have hC₁cov : ∀ t ∈ Icc (0:ℝ) n, ∃ q ∈ C₁, t ∈ Icc q.1 q.2 := fun t ht =>
    u10h_pieceSet_cover P hL hBS K ht
  have hC₂cov : ∀ t ∈ Icc (0:ℝ) n, ∃ q ∈ C₂, t ∈ Icc q.1 q.2 := by
    intro t ht
    obtain ⟨j, hj, htj⟩ := u10h_marks_cover hainc hm1 t (by rw [ha0, ham]; exact ht)
    exact ⟨(a j, a (j + 1)), ⟨j, hj, rfl⟩, htj⟩
  have hC₃cov : ∀ t ∈ Icc (0:ℝ) n, ∃ q ∈ C₃, t ∈ Icc q.1 q.2 := by
    intro t ht
    obtain ⟨k', mm, hk0, hk1, T', hT', htJ⟩ := u10h_J'_cover P' φ 0 n hL' hBS' K' ht
    refine ⟨_, ⟨k', mm, hk0, hk1, T', hT', ⟨t, htJ⟩, rfl⟩, ?_⟩
    have := u10h_J'_eq_Icc P' hφc hmono 0 n k' mm T' ⟨t, htJ⟩
    rw [← this]; exact htJ
  have hC₁aff : ∀ q ∈ C₁, u10h_AffOn c (Icc q.1 q.2) := fun q hq => u10h_pieceSet_affOn P hK hq
  have hC₂aff : ∀ q ∈ C₂, ∃ α δ : ℝ, ∀ t ∈ Icc q.1 q.2, φ t = α * t + δ := by
    rintro q ⟨j, hj, rfl⟩
    exact haff j hj
  have hC₃aff : ∀ q ∈ C₃, ∃ p'' u'' : Plane, ∀ t ∈ Icc q.1 q.2,
      f' ((traversal P' (φ t) : Plane) : Sphere) = p'' + φ t • u'' := by
    rintro q ⟨k', mm, hk0, hk1, T', hT', hne, rfl⟩
    obtain ⟨p'', u'', h⟩ := u10h_affOn_J' P' φ 0 n hK' k' mm hT'
    refine ⟨p'', u'', fun t ht => h t ?_⟩
    rwa [u10h_J'_eq_Icc P' hφc hmono 0 n k' mm T' hne]
  -- the breakpoints
  set B : Set ℝ := ({0, (n:ℝ)} ∪ (Prod.fst '' C₁ ∪ Prod.snd '' C₁)) ∪
    ((Prod.fst '' C₂ ∪ Prod.snd '' C₂) ∪ (Prod.fst '' C₃ ∪ Prod.snd '' C₃)) with hB_def
  have hBfin : B.Finite :=
    ((Set.toFinite _).union ((hC₁fin.image _).union (hC₁fin.image _))).union
      (((hC₂fin.image _).union (hC₂fin.image _)).union ((hC₃fin.image _).union (hC₃fin.image _)))
  have h0B : (0:ℝ) ∈ B := Or.inl (Or.inl (by simp))
  have hnB : (n:ℝ) ∈ B := Or.inl (Or.inl (by simp))
  have hC₁B : ∀ q ∈ C₁, q.1 ∈ B ∧ q.2 ∈ B := fun q hq =>
    ⟨Or.inl (Or.inr (Or.inl ⟨q, hq, rfl⟩)), Or.inl (Or.inr (Or.inr ⟨q, hq, rfl⟩))⟩
  have hC₂B : ∀ q ∈ C₂, q.1 ∈ B ∧ q.2 ∈ B := fun q hq =>
    ⟨Or.inr (Or.inl (Or.inl ⟨q, hq, rfl⟩)), Or.inr (Or.inl (Or.inr ⟨q, hq, rfl⟩))⟩
  have hC₃B : ∀ q ∈ C₃, q.1 ∈ B ∧ q.2 ∈ B := fun q hq =>
    ⟨Or.inr (Or.inr (Or.inl ⟨q, hq, rfl⟩)), Or.inr (Or.inr (Or.inr ⟨q, hq, rfl⟩))⟩
  have hBin : ∀ b ∈ B, 0 ≤ b ∧ b ≤ n := by
    intro b hb
    rcases hb with (hb | (⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩)) | ((⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩) | (⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩))
    · simp only [mem_insert_iff, mem_singleton_iff] at hb
      rcases hb with rfl | rfl <;> constructor <;> linarith
    · obtain ⟨h1, h2, h3⟩ := hC₁in q hq; exact ⟨h1, h2.trans h3⟩
    · obtain ⟨h1, h2, h3⟩ := hC₁in q hq; exact ⟨h1.trans h2, h3⟩
    · obtain ⟨h1, h2, h3⟩ := hC₂in q hq; exact ⟨h1, h2.trans h3⟩
    · obtain ⟨h1, h2, h3⟩ := hC₂in q hq; exact ⟨h1.trans h2, h3⟩
    · obtain ⟨h1, h2, h3⟩ := hC₃in q hq; exact ⟨h1, h2.trans h3⟩
    · obtain ⟨h1, h2, h3⟩ := hC₃in q hq; exact ⟨h1.trans h2, h3⟩
  -- the gap pairs
  set G : Set (ℝ × ℝ) := {g | g.1 ∈ B ∧ g.2 ∈ B ∧ g.1 < g.2 ∧ ∀ a ∈ B, g.1 < a → a < g.2 → False}
    with hG
  have hGfin : G.Finite := (hBfin.prod hBfin).subset (fun g hg => ⟨hg.1, hg.2.1⟩)
  have hgap : ∀ g ∈ G, (∃ p u : Plane, ∀ t ∈ Icc g.1 g.2, c t = p + t • u) ∧
      (∃ p'' u'' : Plane, ∀ t ∈ Icc g.1 g.2, β (c t) = p'' + t • u'') := by
    rintro g ⟨hg1, hg2, hlt, hnone⟩
    have hb0 : 0 ≤ g.1 := (hBin _ hg1).1
    have hbn : g.2 ≤ n := (hBin _ hg2).2
    obtain ⟨q₁, hq₁, hsub₁⟩ := u10h_subset_piece hC₁B hC₁cov hb0 hbn hlt hnone
    obtain ⟨q₂, hq₂, hsub₂⟩ := u10h_subset_piece hC₂B hC₂cov hb0 hbn hlt hnone
    obtain ⟨q₃, hq₃, hsub₃⟩ := u10h_subset_piece hC₃B hC₃cov hb0 hbn hlt hnone
    obtain ⟨p, u, hpu⟩ := hC₁aff q₁ hq₁
    obtain ⟨α, δ, hαδ⟩ := hC₂aff q₂ hq₂
    obtain ⟨p'', u'', hpu''⟩ := hC₃aff q₃ hq₃
    refine ⟨⟨p, u, fun t ht => hpu t (hsub₁ ht)⟩, ⟨p'' + δ • u'', α • u'', ?_⟩⟩
    intro t ht
    show β (f ((traversal P t : Plane) : Sphere)) = _
    rw [hβc, hpu'' t (hsub₃ ht), hαδ t (hsub₂ ht), add_smul, smul_smul, mul_comm t α]
    abel
  -- the segments
  set sF : Finset (Plane × Plane) := (hGfin.image (fun g : ℝ × ℝ => (c g.1, c g.2))).toFinset with hsF
  refine ⟨sF, ?_, ?_⟩
  · apply Set.Subset.antisymm
    · intro w hw
      rw [mem_iUnion₂] at hw
      obtain ⟨p, hp, hwp⟩ := hw
      rw [hsF, Set.Finite.mem_toFinset] at hp
      obtain ⟨g, hg, rfl⟩ := hp
      obtain ⟨⟨pp, u, hpu⟩, -⟩ := hgap g hg
      rw [← u10h_image_Icc_eq_segment hpu hg.2.2.1.le] at hwp
      obtain ⟨t, -, rfl⟩ := hwp
      exact hfr t
    · intro w hw
      obtain ⟨x, hx, rfl⟩ := u10h_frontier_param hB hw
      obtain ⟨b, hb, b', hb', hlt, hbx, hxb, hnone⟩ := u10h_gap' hBfin h0B hnB hn0 ⟨hx.1, hx.2.le⟩
      have hgG : (b, b') ∈ G := ⟨hb, hb', hlt, hnone⟩
      rw [mem_iUnion₂]
      refine ⟨(c b, c b'), ?_, ?_⟩
      · rw [hsF, Set.Finite.mem_toFinset]; exact ⟨(b, b'), hgG, rfl⟩
      · obtain ⟨⟨pp, u, hpu⟩, -⟩ := hgap (b, b') hgG
        show f ((traversal P x : Plane) : Sphere) ∈ segment ℝ (c b) (c b')
        rw [← u10h_image_Icc_eq_segment hpu hlt.le]
        exact ⟨x, ⟨hbx, hxb⟩, rfl⟩
  · intro p hp
    rw [hsF, Set.Finite.mem_toFinset] at hp
    obtain ⟨g, hg, rfl⟩ := hp
    obtain ⟨⟨pp, u, hpu⟩, ⟨p'', u'', hβ⟩⟩ := hgap g hg
    show AffineOn β (segment ℝ (c g.1) (c g.2))
    rw [← u10h_image_Icc_eq_segment hpu hg.2.2.1.le]
    exact u10h_affineOn_of_param hpu hβ hg.2.2.1.le

/-- U10 (sm-3:431-433 "finite prescribed positive PL boundary maps" read in the models): a finite PL
positive boundary lift `φ`, conjugated by two positive PL disc parametrisations, is a finite PL
homeomorphism of the model frontiers preserving the cyclic order around suitable interior points. -/
theorem U10_boundary_map_of_lift [NeZero n] {n' : ℕ} [NeZero n'] (hn : 3 ≤ n) (P : LabelledTuple n)
    (hP : Embedded P) (hn' : 3 ≤ n') (P' : LabelledTuple n') (hP' : Embedded P') (s s' : Side)
    {L L' : ℝ} (hL : InsideModel L P) (hL' : InsideModel L' P') {D D' : Set Plane}
    {f f' : Sphere → Plane} (hD : Link.IsDisc D) (hD' : Link.IsDisc D')
    (hf : IsHomeoOnto (closure (regionOf P s)) D f) (hf' : IsHomeoOnto (closure (regionOf P' s')) D' f')
    (hB : f '' sphereCircle P = frontier D) (hB' : f' '' sphereCircle P' = frontier D')
    (hpl : IsPositivePLToPlane L (closure (regionOf P s)) f)
    (hpl' : IsPositivePLToPlane L' (closure (regionOf P' s')) f')
    {φ : ℝ → ℝ} (hφ : IsPositiveBoundaryLift P s P' s' φ) (hfin : IsFinitePL n φ) :
    ∃ (β : Plane → Plane) (z z' : Plane), z ∈ interior D ∧ z' ∈ interior D' ∧
      IsHomeoOnto (frontier D) (frontier D') β ∧ IsFinitePLOnFrontier D β ∧
      PreservesCyclicPos D z z' β ∧
      ∀ x : ℝ, β (f ((traversal P x : Plane) : Sphere)) = f' ((traversal P' (φ x) : Plane) : Sphere) := by
  classical
  obtain ⟨z, hz⟩ := hD.interior_nonempty
  obtain ⟨z', hz'⟩ := hD'.interior_nonempty
  have hBS := u10h_circle_subset_closure hn P hP s hL
  let β : Plane → Plane := fun w =>
    if h : ∃ x : ℝ, f ((traversal P x : Plane) : Sphere) = w then
      f' ((traversal P' (φ h.choose) : Plane) : Sphere) else w
  have hβc : ∀ x, β (f ((traversal P x : Plane) : Sphere)) =
      f' ((traversal P' (φ x) : Plane) : Sphere) := by
    intro x
    have hex : ∃ x' : ℝ, f ((traversal P x' : Plane) : Sphere) = f ((traversal P x : Plane) : Sphere) :=
      ⟨x, rfl⟩
    show (if h : ∃ x' : ℝ, f ((traversal P x' : Plane) : Sphere) = f ((traversal P x : Plane) : Sphere) then
      f' ((traversal P' (φ h.choose) : Plane) : Sphere) else _) = _
    rw [dif_pos hex]
    have hspec := hex.choose_spec
    set x₀ := hex.choose with hx₀
    clear_value x₀
    obtain ⟨m, hm⟩ := (u10h_param_eq_iff hn hP hf hBS x₀ x).mp hspec
    rw [hm]
    by_cases hsame : (traversalPositiveFor P s ↔ traversalPositiveFor P' s')
    · rw [u10h_lift_shift_same (hφ.same hsame).2, u10h_traversal_add_int_mul]
    · rw [u10h_lift_shift_opp (hφ.opposite hsame).2, sub_eq_add_neg, ← neg_mul, ← Int.cast_neg,
        u10h_traversal_add_int_mul]
  exact ⟨β, z, z', hz, hz',
    u10h_boundary_homeo hn P hP hn' P' hP' s s' hL hL' hD hD' hf hf' hB hB' hφ hβc,
    u10h_finitePL hn P hP hn' P' hP' s s' hL hL' hB hpl hpl' hφ hfin hβc,
    u10h_preservesCyclicPos hn P hP hn' P' hP' s s' hL hL' hD hD' hf hf' hB hB' hpl hpl' hφ hz hz' hβc,
    hβc⟩

/-! #### U10 helpers for `U10_pl_extension` -/

theorem u10h_isHomeoOnto_image {α β : Type*} [TopologicalSpace α] [TopologicalSpace β] {S : Set α}
    {S' : Set β} {f : α → β} (h : IsHomeoOnto S S' f) : f '' S = S' := by
  obtain ⟨e, he⟩ := h
  ext w
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [← he ⟨x, hx⟩]; exact (e ⟨x, hx⟩).2
  · intro hw
    refine ⟨e.symm ⟨w, hw⟩, (e.symm ⟨w, hw⟩).2, ?_⟩
    rw [← he]; simp

theorem u10h_pl_discs [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Embedded P) (s : Side)
    (L : ℝ) (hL : InsideModel L P) :
    IsPLDiscSphere L (closure (regionOf P s)) (sphereCircle P) := by
  cases s with
  | inner => exact U7_pl_discs_inner hn P hP L hL
  | outer => exact U8_pl_discs_outer hn P hP L hL

/-- U10 (57c, sm-3:431-433 / 535-537): finite positive PL boundary maps extend to positive PL disc
maps `F = Φ'⁻¹ ∘ Fan ∘ Φ`. -/
theorem U10_pl_extension [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Embedded P)
    {n' : ℕ} [NeZero n'] (P' : LabelledTuple n') (hn' : 3 ≤ n') (hP' : Embedded P')
    (s s' : Side) (L L' : ℝ) (hL : InsideModel L P) (hL' : InsideModel L' P')
    (φ : ℝ → ℝ) (hφ : IsPositiveBoundaryLift P s P' s' φ) (hfin : IsFinitePL n φ) :
    ∃ F : Sphere → Sphere,
      IsHomeoOnto (closure (regionOf P s)) (closure (regionOf P' s')) F ∧
      IsPositivePLSphereMap L L' (closure (regionOf P s)) F ∧
      ∀ x : ℝ, F ((traversal P x : Plane) : Sphere) = ((traversal P' (φ x) : Plane) : Sphere) := by
  obtain ⟨D, f, hD, hBS, hf, hB, hpl⟩ := u10h_pl_discs hn P hP s L hL
  obtain ⟨D', f', hD', hBS', hf', hB', hpl'⟩ := u10h_pl_discs hn' P' hP' s' L' hL'
  obtain ⟨β, z, z', hz, hz', hβ, hβpl, hβpos, hβc⟩ :=
    U10_boundary_map_of_lift hn P hP hn' P' hP' s s' hL hL' hD hD' hf hf' hB hB' hpl hpl' hφ hfin
  obtain ⟨K, Fan, hFanK, hFan, hFanβ⟩ := U10_fan_extension hD hD' hz hz' hβ hβpl hβpos
  obtain ⟨g', hg'pl, hg'l, hg'r⟩ :=
    U3_isPositivePLFromPlane_inv (U4_polygonImage_subset_interior_square P' hL').2 hD' hf' hpl'
  have hfS : f '' closure (regionOf P s) = D := u10h_isHomeoOnto_image hf
  have hFanD : Fan '' D = D' := u10h_isHomeoOnto_image hFan
  have hg' : IsHomeoOnto D' (closure (regionOf P' s')) g' := U1_isHomeoOnto_inv hf' hg'l
  refine ⟨g' ∘ (Fan ∘ f), ?_, ?_, ?_⟩
  · exact U1_isHomeoOnto_comp (U1_isHomeoOnto_comp hf hFan) hg'
  · have h1 : IsPositivePLToPlane L (closure (regionOf P s)) (Fan ∘ f) :=
      U3_isPositivePLToPlane_comp_plane K hpl hfS.le hFanK
    have h2 : (Fan ∘ f) '' closure (regionOf P s) ⊆ D' := by rw [image_comp, hfS, hFanD]
    exact U3_isPositivePLSphereMap_comp h1 h2 hg'pl
  · intro x
    have hfx : f ((traversal P x : Plane) : Sphere) ∈ frontier D :=
      hB ▸ mem_image_of_mem f (u10h_coe_traversal_mem_circle P x)
    have hx' : ((traversal P' (φ x) : Plane) : Sphere) ∈ closure (regionOf P' s') :=
      hBS' (u10h_coe_traversal_mem_circle P' (φ x))
    simp only [Function.comp]
    rw [hFanβ _ hfx, hβc x, hg'l _ hx']

/-! ### U11 (lane C convex model, then sequential) — 57d -/

/-- a disc with `0` interior is a neighbourhood of `0`. -/
theorem u11h_mem_nhds_of_interior {D : Set Plane} (h0 : (0 : Plane) ∈ interior D) : D ∈ nhds 0 :=
  mem_interior_iff_mem_nhds.mp h0

theorem u11h_isVonNBounded {D : Set Plane} (hD : Link.IsDisc D) : Bornology.IsVonNBounded ℝ D :=
  hD.2.1.isVonNBounded ℝ

/-- U11 (gauge coordinates): for a convex disc with `0` in its interior, the frontier is the gauge
level `1` and the disc is the sublevel `≤ 1`. -/
theorem U11_frontier_eq_gauge_one {D : Set Plane} (hD : Link.IsDisc D) (h0 : (0 : Plane) ∈ interior D) :
    frontier D = {x | gauge D x = 1} ∧ D = {x | gauge D x ≤ 1} := by
  have hn : D ∈ nhds (0 : Plane) := u11h_mem_nhds_of_interior h0
  refine ⟨?_, ?_⟩
  · ext x
    simp only [mem_ofPred_eq]
    exact (gauge_eq_one_iff_mem_frontier hD.1 hn).symm
  · ext x
    simp only [mem_ofPred_eq]
    rw [gauge_le_one_iff_mem_closure hD.1 hn, hD.2.1.isClosed.closure_eq]
/-- gauge positivity off `0` for a disc with `0` interior. -/
theorem u11h_gauge_pos {D : Set Plane} (hD : Link.IsDisc D) (h0 : (0 : Plane) ∈ interior D)
    {x : Plane} (hx : x ≠ 0) : 0 < gauge D x :=
  (gauge_pos (absorbent_nhds_zero (u11h_mem_nhds_of_interior h0)) (u11h_isVonNBounded hD)).mpr hx

/-- The radial projection onto the frontier: `x ↦ (gauge D x)⁻¹ • x`. -/
noncomputable def u11h_proj (D : Set Plane) (x : Plane) : Plane := (gauge D x)⁻¹ • x

/-- The radial map: `x ↦ gauge D x • b (proj D x)`. -/
noncomputable def u11h_rad (D : Set Plane) (b : Plane → Plane) (x : Plane) : Plane :=
  gauge D x • b (u11h_proj D x)

theorem u11h_gauge_proj {D : Set Plane} (hD : Link.IsDisc D) (h0 : (0 : Plane) ∈ interior D)
    {x : Plane} (hx : x ≠ 0) : gauge D (u11h_proj D x) = 1 := by
  have hp := u11h_gauge_pos hD h0 hx
  unfold u11h_proj
  rw [gauge_smul_of_nonneg (inv_nonneg.mpr hp.le), smul_eq_mul, inv_mul_cancel₀ hp.ne']

theorem u11h_proj_mem_frontier {D : Set Plane} (hD : Link.IsDisc D) (h0 : (0 : Plane) ∈ interior D)
    {x : Plane} (hx : x ≠ 0) : u11h_proj D x ∈ frontier D := by
  rw [(U11_frontier_eq_gauge_one hD h0).1]
  exact u11h_gauge_proj hD h0 hx

theorem u11h_rad_zero (D : Set Plane) (b : Plane → Plane) : u11h_rad D b 0 = 0 := by
  simp [u11h_rad]

theorem u11h_rad_of_mem_frontier {D : Set Plane} (hD : Link.IsDisc D) (h0 : (0 : Plane) ∈ interior D)
    (b : Plane → Plane) {x : Plane} (hx : x ∈ frontier D) : u11h_rad D b x = b x := by
  have h1 : gauge D x = 1 := by
    rw [(U11_frontier_eq_gauge_one hD h0).1] at hx; exact hx
  simp [u11h_rad, u11h_proj, h1]

theorem u11h_gauge_rad {D D' : Set Plane} (hD : Link.IsDisc D) (h0 : (0 : Plane) ∈ interior D)
    (hD' : Link.IsDisc D') (h0' : (0 : Plane) ∈ interior D') {b : Plane → Plane}
    (hb : MapsTo b (frontier D) (frontier D')) (x : Plane) :
    gauge D' (u11h_rad D b x) = gauge D x := by
  by_cases hx : x = 0
  · subst hx; simp [u11h_rad]
  · have h1 : gauge D' (b (u11h_proj D x)) = 1 := by
      have := hb (u11h_proj_mem_frontier hD h0 hx)
      rw [(U11_frontier_eq_gauge_one hD' h0').1] at this; exact this
    unfold u11h_rad
    rw [gauge_smul_of_nonneg (gauge_nonneg _), smul_eq_mul, h1, mul_one]

theorem u11h_proj_rad {D D' : Set Plane} (hD : Link.IsDisc D) (h0 : (0 : Plane) ∈ interior D)
    (hD' : Link.IsDisc D') (h0' : (0 : Plane) ∈ interior D') {b : Plane → Plane}
    (hb : MapsTo b (frontier D) (frontier D')) {x : Plane} (hx : x ≠ 0) :
    u11h_proj D' (u11h_rad D b x) = b (u11h_proj D x) := by
  have hp := u11h_gauge_pos hD h0 hx
  unfold u11h_proj
  rw [u11h_gauge_rad hD h0 hD' h0' hb x]
  unfold u11h_rad
  rw [smul_smul, inv_mul_cancel₀ hp.ne', one_smul]
  rfl

theorem u11h_rad_mem {D D' : Set Plane} (hD : Link.IsDisc D) (h0 : (0 : Plane) ∈ interior D)
    (hD' : Link.IsDisc D') (h0' : (0 : Plane) ∈ interior D') {b : Plane → Plane}
    (hb : MapsTo b (frontier D) (frontier D')) {x : Plane} (hx : x ∈ D) : u11h_rad D b x ∈ D' := by
  rw [(U11_frontier_eq_gauge_one hD' h0').2]
  show gauge D' (u11h_rad D b x) ≤ 1
  rw [u11h_gauge_rad hD h0 hD' h0' hb x]
  exact gauge_le_one_of_mem hx

theorem u11h_rad_rad {D D' : Set Plane} (hD : Link.IsDisc D) (h0 : (0 : Plane) ∈ interior D)
    (hD' : Link.IsDisc D') (h0' : (0 : Plane) ∈ interior D') {b b' : Plane → Plane}
    (hb : MapsTo b (frontier D) (frontier D')) (hb' : ∀ u ∈ frontier D, b' (b u) = u) (x : Plane) :
    u11h_rad D' b' (u11h_rad D b x) = x := by
  by_cases hx : x = 0
  · subst hx; simp [u11h_rad]
  · have hp := u11h_gauge_pos hD h0 hx
    have h1 := u11h_gauge_rad hD h0 hD' h0' hb x
    have h2 := u11h_proj_rad hD h0 hD' h0' hb hx
    show gauge D' (u11h_rad D b x) • b' (u11h_proj D' (u11h_rad D b x)) = x
    rw [h1, h2, hb' _ (u11h_proj_mem_frontier hD h0 hx)]
    unfold u11h_proj
    rw [smul_smul, mul_inv_cancel₀ hp.ne', one_smul]

theorem u11h_continuousOn_proj {D : Set Plane} (hD : Link.IsDisc D) (h0 : (0 : Plane) ∈ interior D) :
    ContinuousOn (u11h_proj D) {x | x ≠ 0} := by
  have hg : Continuous (gauge D) := continuous_gauge hD.1 (u11h_mem_nhds_of_interior h0)
  refine ContinuousOn.smul (hg.continuousOn.inv₀ ?_) continuousOn_id
  intro x hx
  exact (u11h_gauge_pos hD h0 hx).ne'

theorem u11h_continuous_rad {D D' : Set Plane} (hD : Link.IsDisc D) (h0 : (0 : Plane) ∈ interior D)
    (hD' : Link.IsDisc D') {b : Plane → Plane}
    (hb : ContinuousOn b (frontier D)) (hbm : MapsTo b (frontier D) (frontier D')) :
    Continuous (u11h_rad D b) := by
  have hg : Continuous (gauge D) := continuous_gauge hD.1 (u11h_mem_nhds_of_interior h0)
  have hmaps : MapsTo (u11h_proj D) {x | x ≠ 0} (frontier D) := fun x hx =>
    u11h_proj_mem_frontier hD h0 hx
  have hne : ContinuousOn (u11h_rad D b) {x | x ≠ 0} :=
    hg.continuousOn.smul (hb.comp (u11h_continuousOn_proj hD h0) hmaps)
  obtain ⟨M, hM⟩ := hD'.2.1.isBounded.subset_closedBall 0
  have hbound : ∀ x, ‖u11h_rad D b x‖ ≤ gauge D x * M := by
    intro x
    by_cases hx : x = 0
    · subst hx; simp [u11h_rad_zero]
    · have hmem : b (u11h_proj D x) ∈ D' :=
        hD'.2.1.isClosed.frontier_subset (hbm (u11h_proj_mem_frontier hD h0 hx))
      have hM' : ‖b (u11h_proj D x)‖ ≤ M := by simpa using hM hmem
      unfold u11h_rad
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (gauge_nonneg _)]
      exact mul_le_mul_of_nonneg_left hM' (gauge_nonneg _)
  refine continuous_iff_continuousAt.mpr fun x => ?_
  by_cases hx : x = 0
  · subst hx
    rw [ContinuousAt, u11h_rad_zero]
    refine squeeze_zero_norm hbound ?_
    have : Filter.Tendsto (fun x => gauge D x * M) (nhds 0) (nhds (gauge D 0 * M)) :=
      (hg.tendsto 0).mul_const M
    simpa [gauge_zero] using this
  · exact hne.continuousAt (isOpen_ne.mem_nhds hx)

/-- Translating a disc so that an interior point `c` goes to `0`: the preimage under `x ↦ x + c`. -/
theorem u11h_translate {D : Set Plane} (hD : Link.IsDisc D) {c : Plane} (hc : c ∈ interior D) :
    Link.IsDisc ((fun x => x + c) ⁻¹' D) ∧ (0 : Plane) ∈ interior ((fun x => x + c) ⁻¹' D) ∧
      frontier ((fun x => x + c) ⁻¹' D) = (fun x => x + c) ⁻¹' frontier D := by
  have hint : interior ((fun x => x + c) ⁻¹' D) = (fun x => x + c) ⁻¹' interior D :=
    ((Homeomorph.addRight c).preimage_interior D).symm
  have hfr : frontier ((fun x => x + c) ⁻¹' D) = (fun x => x + c) ⁻¹' frontier D :=
    ((Homeomorph.addRight c).preimage_frontier D).symm
  have h0 : (0 : Plane) ∈ interior ((fun x => x + c) ⁻¹' D) := by
    rw [hint]; show (0 : Plane) + c ∈ interior D; simpa using hc
  refine ⟨⟨hD.1.translate_preimage_left c, ?_, ⟨0, h0⟩⟩, h0, hfr⟩
  exact (Homeomorph.addRight c).isCompact_preimage.mpr hD.2.1

open Classical in
/-- The inverse of a set homeomorphism, as a plane map (junk `0` off the target). -/
noncomputable def u11h_homeoInv {S S' : Set Plane} (e : S ≃ₜ S') (y : Plane) : Plane :=
  if h : y ∈ S' then (e.symm ⟨y, h⟩ : Plane) else 0

theorem u11h_isHomeoOnto_facts {S S' : Set Plane} {β : Plane → Plane}
    (hβ : IsHomeoOnto S S' β) :
    ∃ βi : Plane → Plane, ContinuousOn β S ∧ MapsTo β S S' ∧ ContinuousOn βi S' ∧ MapsTo βi S' S ∧
      (∀ u ∈ S, βi (β u) = u) ∧ (∀ u ∈ S', β (βi u) = u) := by
  obtain ⟨e, he⟩ := hβ
  refine ⟨u11h_homeoInv e, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [continuousOn_iff_continuous_domRestrict]
    have : domRestrict S β = fun z => (e z : Plane) := funext fun z => (he z).symm
    rw [this]; exact continuous_subtype_val.comp e.continuous
  · intro z hz; rw [← he ⟨z, hz⟩]; exact (e ⟨z, hz⟩).2
  · rw [continuousOn_iff_continuous_domRestrict]
    have : domRestrict S' (u11h_homeoInv e) = fun y => (e.symm y : Plane) := by
      funext y; simp only [domRestrict, u11h_homeoInv, y.2, ↓reduceDIte]
    rw [this]; exact continuous_subtype_val.comp e.symm.continuous
  · intro y hy; simp only [u11h_homeoInv, hy, ↓reduceDIte]; exact (e.symm ⟨y, hy⟩).2
  · intro u hu
    have h1 : β u ∈ S' := by rw [← he ⟨u, hu⟩]; exact (e ⟨u, hu⟩).2
    simp only [u11h_homeoInv, h1, ↓reduceDIte]
    have : (⟨β u, h1⟩ : S') = e ⟨u, hu⟩ := Subtype.ext (he ⟨u, hu⟩).symm
    rw [this, e.symm_apply_apply]
  · intro u hu
    simp only [u11h_homeoInv, hu, ↓reduceDIte]
    rw [← he (e.symm ⟨u, hu⟩), e.apply_symm_apply]

/-- U11 (sm-3:537-542, the radial / Alexander extension on convex models): a homeomorphism between
the frontiers of two convex discs extends to a homeomorphism of the discs. -/
theorem U11_radial_extension {D D' : Set Plane} (hD : Link.IsDisc D) (hD' : Link.IsDisc D')
    {β : Plane → Plane} (hβ : IsHomeoOnto (frontier D) (frontier D') β) :
    ∃ F : Plane → Plane, IsHomeoOnto D D' F ∧ ∀ x ∈ frontier D, F x = β x := by
  obtain ⟨c, hc⟩ := hD.2.2
  obtain ⟨c', hc'⟩ := hD'.2.2
  obtain ⟨hA, h0, hfrA⟩ := u11h_translate hD hc
  obtain ⟨hA', h0', hfrA'⟩ := u11h_translate hD' hc'
  obtain ⟨βi, hβc, hβm, hβic, hβim, hβiβ, hββi⟩ := u11h_isHomeoOnto_facts hβ
  set A : Set Plane := (fun x => x + c) ⁻¹' D with hAdef
  set A' : Set Plane := (fun x => x + c') ⁻¹' D' with hA'def
  set b : Plane → Plane := fun y => β (y + c) - c' with hbdef
  set b' : Plane → Plane := fun y => βi (y + c') - c with hb'def
  have hmA : ∀ y, y ∈ frontier A ↔ y + c ∈ frontier D := fun y => by rw [hfrA]; rfl
  have hmA' : ∀ y, y ∈ frontier A' ↔ y + c' ∈ frontier D' := fun y => by rw [hfrA']; rfl
  have hbc : ContinuousOn b (frontier A) := by
    refine ContinuousOn.sub (hβc.comp (continuous_add_const c).continuousOn ?_) continuousOn_const
    intro y hy; exact (hmA y).mp hy
  have hbm : MapsTo b (frontier A) (frontier A') := by
    intro y hy; rw [hmA']; simp only [hbdef, sub_add_cancel]; exact hβm ((hmA y).mp hy)
  have hb'c : ContinuousOn b' (frontier A') := by
    refine ContinuousOn.sub (hβic.comp (continuous_add_const c').continuousOn ?_) continuousOn_const
    intro y hy; exact (hmA' y).mp hy
  have hb'm : MapsTo b' (frontier A') (frontier A) := by
    intro y hy; rw [hmA]; simp only [hb'def, sub_add_cancel]; exact hβim ((hmA' y).mp hy)
  have hb'b : ∀ u ∈ frontier A, b' (b u) = u := by
    intro u hu; simp only [hbdef, hb'def, sub_add_cancel]
    rw [hβiβ _ ((hmA u).mp hu), add_sub_cancel_right]
  have hbb' : ∀ u ∈ frontier A', b (b' u) = u := by
    intro u hu; simp only [hbdef, hb'def, sub_add_cancel]
    rw [hββi _ ((hmA' u).mp hu), add_sub_cancel_right]
  have hcont : Continuous (u11h_rad A b) := u11h_continuous_rad hA h0 hA' hbc hbm
  have hcont' : Continuous (u11h_rad A' b') := u11h_continuous_rad hA' h0' hA hb'c hb'm
  have hmemA : ∀ x, x ∈ D → x - c ∈ A := fun x hx => by
    show x - c + c ∈ D; rwa [sub_add_cancel]
  have hmemA' : ∀ x, x ∈ D' → x - c' ∈ A' := fun x hx => by
    show x - c' + c' ∈ D'; rwa [sub_add_cancel]
  refine ⟨fun x => u11h_rad A b (x - c) + c', ⟨?_, ?_⟩, ?_⟩
  · exact
      { toFun := fun x => ⟨u11h_rad A b (x.1 - c) + c', u11h_rad_mem hA h0 hA' h0' hbm (hmemA _ x.2)⟩
        invFun := fun y => ⟨u11h_rad A' b' (y.1 - c') + c,
          u11h_rad_mem hA' h0' hA h0 hb'm (hmemA' _ y.2)⟩
        left_inv := fun x => by
          apply Subtype.ext
          simp only [add_sub_cancel_right]
          rw [u11h_rad_rad hA h0 hA' h0' hbm hb'b, sub_add_cancel]
        right_inv := fun y => by
          apply Subtype.ext
          simp only [add_sub_cancel_right]
          rw [u11h_rad_rad hA' h0' hA h0 hb'm hbb', sub_add_cancel]
        continuous_toFun := by
          exact ((hcont.comp (continuous_subtype_val.sub continuous_const)).add
            continuous_const).subtype_mk _
        continuous_invFun := by
          exact ((hcont'.comp (continuous_subtype_val.sub continuous_const)).add
            continuous_const).subtype_mk _ }
  · intro z; rfl
  · intro x hx
    have hxA : x - c ∈ frontier A := by rw [hmA, sub_add_cancel]; exact hx
    show u11h_rad A b (x - c) + c' = β x
    rw [u11h_rad_of_mem_frontier hA h0 b hxA]
    simp only [hbdef, sub_add_cancel]
/-- integer periodicity of the traversal. -/
theorem u11h_traversal_add_int (P : LabelledTuple n) (x : ℝ) (m : ℤ) :
    traversal P (x + m * n) = traversal P x := by
  induction m using Int.induction_on with
  | zero => simp
  | succ k ih =>
    have : x + (((k : ℤ) + 1 : ℤ) : ℝ) * n = (x + ((k : ℤ) : ℝ) * n) + n := by push_cast; ring
    rw [this, traversal_add_nat, ih]
  | pred k ih =>
    have : x + ((-(k : ℤ) : ℤ) : ℝ) * n = (x + ((-(k : ℤ) - 1 : ℤ) : ℝ) * n) + n := by
      push_cast; ring
    rw [this, traversal_add_nat] at ih
    exact ih

/-- a lift with `φ (x + n) = φ x + a` satisfies `φ (x + m n) = φ x + m a`. -/
theorem u11h_lift_add_int {φ : ℝ → ℝ} {a : ℝ} (hper : ∀ x, φ (x + n) = φ x + a) (x : ℝ) (m : ℤ) :
    φ (x + m * n) = φ x + m * a := by
  induction m using Int.induction_on with
  | zero => simp
  | succ k ih =>
    have : x + (((k : ℤ) + 1 : ℤ) : ℝ) * n = (x + ((k : ℤ) : ℝ) * n) + n := by push_cast; ring
    rw [this, hper, ih]; push_cast; ring
  | pred k ih =>
    have h1 : x + ((-(k : ℤ) : ℤ) : ℝ) * n = (x + ((-(k : ℤ) - 1 : ℤ) : ℝ) * n) + n := by
      push_cast; ring
    rw [h1, hper] at ih
    have : φ (x + ((-(k : ℤ) - 1 : ℤ) : ℝ) * n) = φ x + ((-(k : ℤ) : ℤ) : ℝ) * a - a := by linarith
    rw [this]; push_cast; ring

/-- surjectivity of a continuous map with `φ (x + n) = φ x + a`, `a > 0` (IVT). -/
theorem u11h_surj_of_period {φ : ℝ → ℝ} (hc : Continuous φ) {a : ℝ} (ha : 0 < a)
    (hper : ∀ x, φ (x + n) = φ x + a) : Function.Surjective φ := by
  intro y
  set m : ℤ := ⌊(y - φ 0) / a⌋ with hm
  have h1 : (m : ℝ) ≤ (y - φ 0) / a := Int.floor_le _
  have h2 : (y - φ 0) / a < m + 1 := Int.lt_floor_add_one _
  have hlo : φ ((m : ℝ) * n) ≤ y := by
    have := u11h_lift_add_int hper 0 m
    rw [zero_add] at this; rw [this]
    have := (le_div_iff₀ ha).mp h1; linarith
  have hhi : y ≤ φ (((m + 1 : ℤ) : ℝ) * n) := by
    have := u11h_lift_add_int hper 0 (m + 1)
    rw [zero_add] at this; rw [this]
    have := (div_lt_iff₀ ha).mp h2; push_cast; linarith
  have hab : (m : ℝ) * n ≤ ((m + 1 : ℤ) : ℝ) * n := by
    push_cast; nlinarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
  obtain ⟨x, -, hx⟩ := intermediate_value_Icc hab hc.continuousOn ⟨hlo, hhi⟩
  exact ⟨x, hx⟩

/-- Packaging of a positive boundary lift: a sign `ε = ±1` with `φ (x + n) = φ x + ε n'`,
injectivity and surjectivity. -/
theorem u11h_lift_facts [NeZero n] {n' : ℕ} [NeZero n'] (hn' : 3 ≤ n') (P : LabelledTuple n)
    (P' : LabelledTuple n') (s s' : Side) {φ : ℝ → ℝ} (hφ : IsPositiveBoundaryLift P s P' s' φ) :
    ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧ (∀ x, φ (x + n) = φ x + ε * n') ∧
      Function.Injective φ ∧ Function.Surjective φ := by
  have hn'0 : (0 : ℝ) < n' := by exact_mod_cast (show 0 < n' by omega)
  by_cases h : (traversalPositiveFor P s ↔ traversalPositiveFor P' s')
  · obtain ⟨hmono, hper⟩ := hφ.same h
    refine ⟨1, Or.inl rfl, fun x => by rw [hper, one_mul], hmono.injective, ?_⟩
    exact u11h_surj_of_period hφ.continuous hn'0 hper
  · obtain ⟨hanti, hper⟩ := hφ.opposite h
    refine ⟨-1, Or.inr rfl, fun x => by rw [hper]; ring, hanti.injective, ?_⟩
    have hneg : ∀ x, (fun t => -φ t) (x + n) = (fun t => -φ t) x + n' := fun x => by
      simp only; rw [hper]; ring
    have hs := u11h_surj_of_period hφ.continuous.neg hn'0 hneg
    intro y
    obtain ⟨x, hx⟩ := hs (-y)
    exact ⟨x, by simpa using congrArg Neg.neg hx⟩

/-- the boundary lift respects the traversal identifications. -/
theorem u11h_traversal_congr [NeZero n] {n' : ℕ} (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Embedded P) (P' : LabelledTuple n') {φ : ℝ → ℝ} {ε : ℝ} (hε : ε = 1 ∨ ε = -1)
    (hper : ∀ x, φ (x + n) = φ x + ε * n') {x y : ℝ} (hxy : traversal P x = traversal P y) :
    traversal P' (φ x) = traversal P' (φ y) := by
  obtain ⟨m, hm⟩ := hP.traversal_injective hn hxy
  rcases hε with rfl | rfl
  · have h1 : φ y = φ x + m * n' := by rw [hm, u11h_lift_add_int hper x m]; ring
    rw [h1, u11h_traversal_add_int]
  · have h1 : φ y = φ x + ((-m : ℤ) : ℝ) * n' := by
      rw [hm, u11h_lift_add_int hper x m]; push_cast; ring
    rw [h1, u11h_traversal_add_int]

/-- and conversely (injectivity of the induced circle map). -/
theorem u11h_traversal_congr_inv [NeZero n] {n' : ℕ} [NeZero n'] (hn' : 3 ≤ n') (P : LabelledTuple n)
    {P' : LabelledTuple n'} (hP' : Embedded P') {φ : ℝ → ℝ} {ε : ℝ} (hε : ε = 1 ∨ ε = -1)
    (hper : ∀ x, φ (x + n) = φ x + ε * n') (hinj : Function.Injective φ) {x y : ℝ}
    (hxy : traversal P' (φ x) = traversal P' (φ y)) : traversal P x = traversal P y := by
  obtain ⟨m, hm⟩ := hP'.traversal_injective hn' hxy
  rcases hε with rfl | rfl
  · have h1 : φ y = φ (x + m * n) := by rw [u11h_lift_add_int hper x m, hm]; ring
    rw [hinj h1, u11h_traversal_add_int]
  · have h1 : φ y = φ (x + ((-m : ℤ) : ℝ) * n) := by
      rw [u11h_lift_add_int hper x (-m), hm]; push_cast; ring
    rw [hinj h1, u11h_traversal_add_int]

/-- the traversal image is the polygon image. -/
theorem u11h_range_traversal [NeZero n] (P : LabelledTuple n) : range (traversal P) = embeddedPolygonImage P := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    refine mem_iUnion.mpr ⟨((⌊x⌋ : ℤ) : ZMod n), Int.fract x, Int.fract_nonneg x, (Int.fract_lt_one x).le, rfl⟩
  · intro hz
    obtain ⟨i, t, ht0, ht1, rfl⟩ := mem_iUnion.mp hz
    refine ⟨((i.val : ℕ) : ℝ) + t, ?_⟩
    have := ea_traversal_eq_on_Icc P (i.val : ℤ) (y := ((i.val : ℕ) : ℝ) + t) (by push_cast; linarith)
      (by push_cast; linarith)
    rw [this]
    simp [edgePoint]

/-- every traversal point is reached from `[0, n]`. -/
theorem u11h_exists_reduce [NeZero n] (P : LabelledTuple n) (x : ℝ) :
    ∃ t ∈ Icc (0 : ℝ) n, traversal P t = traversal P x := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  set m : ℤ := ⌊x / n⌋ with hm
  refine ⟨x + (-m : ℤ) * n, ⟨?_, ?_⟩, u11h_traversal_add_int P x (-m)⟩
  · have := Int.floor_le (x / n)
    have := (le_div_iff₀ hn0).mp this
    push_cast; linarith
  · have := Int.lt_floor_add_one (x / n)
    have := (div_lt_iff₀ hn0).mp this
    push_cast; linarith

/-- continuity, image and injectivity of a set homeomorphism. -/
theorem u11h_isHomeoOnto_cont_inj {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    {S : Set α} {S' : Set β} {f : α → β} (hf : IsHomeoOnto S S' f) :
    ContinuousOn f S ∧ MapsTo f S S' ∧ InjOn f S := by
  obtain ⟨e, he⟩ := hf
  refine ⟨?_, ?_, ?_⟩
  · rw [continuousOn_iff_continuous_domRestrict]
    have : domRestrict S f = fun z => (e z : β) := funext fun z => (he z).symm
    rw [this]; exact continuous_subtype_val.comp e.continuous
  · intro z hz; rw [← he ⟨z, hz⟩]; exact (e ⟨z, hz⟩).2
  · intro z hz w hw hzw
    have : e ⟨z, hz⟩ = e ⟨w, hw⟩ := Subtype.ext (by rw [he, he]; exact hzw)
    exact congrArg Subtype.val (e.injective this)

/-- The traversal parametrisation of the frontier through a disc parametrisation `f`:
`q x = f ↑(traversal P x)` is continuous, lands in the frontier, covers it, and identifies exactly
the traversal identifications. -/
theorem u11h_param_facts [NeZero n] (P : LabelledTuple n) {S : Set Sphere}
    (hCS : sphereCircle P ⊆ S) {D : Set Plane} {f : Sphere → Plane} (hf : IsHomeoOnto S D f)
    (hB : f '' sphereCircle P = frontier D) :
    Continuous (fun x : ℝ => f ((traversal P x : Plane) : Sphere)) ∧
      (∀ x : ℝ, f ((traversal P x : Plane) : Sphere) ∈ frontier D) ∧
      (∀ y ∈ frontier D, ∃ x : ℝ, f ((traversal P x : Plane) : Sphere) = y) ∧
      (∀ x y : ℝ, f ((traversal P x : Plane) : Sphere) = f ((traversal P y : Plane) : Sphere) ↔
        traversal P x = traversal P y) := by
  obtain ⟨hfc, -, hfi⟩ := u11h_isHomeoOnto_cont_inj hf
  have hcirc : ∀ x : ℝ, ((traversal P x : Plane) : Sphere) ∈ sphereCircle P := fun x =>
    ⟨traversal P x, (u11h_range_traversal P) ▸ mem_range_self x, rfl⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact hfc.comp_continuous (continuous_coe.comp (continuous_traversal P)) fun x => hCS (hcirc x)
  · intro x; rw [← hB]; exact ⟨_, hcirc x, rfl⟩
  · intro y hy
    rw [← hB] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    obtain ⟨w, hw, rfl⟩ := hz
    rw [← u11h_range_traversal P] at hw
    obtain ⟨x, rfl⟩ := hw
    exact ⟨x, rfl⟩
  · intro x y
    refine ⟨fun h => ?_, fun h => by rw [h]⟩
    have := hfi (hCS (hcirc x)) (hCS (hcirc y)) h
    exact coe_eq_coe.mp this

open Classical Topology in
/-- Abstract form of `U11_boundary_homeo_of_lift`: the closed regions are replaced by any sets
`S ⊇ sphereCircle P`, `S' ⊇ sphereCircle P'`. -/
theorem u11h_boundary_homeo_aux [NeZero n] {n' : ℕ} [NeZero n'] (hn : 3 ≤ n) (P : LabelledTuple n)
    (hP : Embedded P) (hn' : 3 ≤ n') (P' : LabelledTuple n') (hP' : Embedded P') (s s' : Side)
    {S S' : Set Sphere} (hCS : sphereCircle P ⊆ S) (hCS' : sphereCircle P' ⊆ S')
    {D D' : Set Plane} {f f' : Sphere → Plane} (hD : Link.IsDisc D)
    (hf : IsHomeoOnto S D f) (hf' : IsHomeoOnto S' D' f')
    (hB : f '' sphereCircle P = frontier D) (hB' : f' '' sphereCircle P' = frontier D')
    {φ : ℝ → ℝ} (hφ : IsPositiveBoundaryLift P s P' s' φ) :
    ∃ β : Plane → Plane, IsHomeoOnto (frontier D) (frontier D') β ∧
      ∀ x : ℝ, β (f ((traversal P x : Plane) : Sphere)) = f' ((traversal P' (φ x) : Plane) : Sphere) := by
  obtain ⟨ε, hε, hper, hinj, hsurj⟩ := u11h_lift_facts hn' P P' s s' hφ
  obtain ⟨hqc, hqf, hqs, hqi⟩ := u11h_param_facts P hCS hf hB
  obtain ⟨hqc', hqf', hqs', hqi'⟩ := u11h_param_facts P' hCS' hf' hB'
  set q : ℝ → Plane := fun x => f ((traversal P x : Plane) : Sphere) with hq
  set q' : ℝ → Plane := fun x => f' ((traversal P' x : Plane) : Sphere) with hq'
  -- the induced map on the frontier
  let β₀ : frontier D → frontier D' := fun y => ⟨q' (φ (choose (hqs y.1 y.2))), hqf' _⟩
  have key : ∀ x : ℝ, β₀ ⟨q x, hqf x⟩ = ⟨q' (φ x), hqf' _⟩ := by
    intro x
    apply Subtype.ext
    show q' (φ (choose (hqs (q x) (hqf x)))) = q' (φ x)
    have h1 : q (choose (hqs (q x) (hqf x))) = q x := choose_spec (hqs (q x) (hqf x))
    have h2 := (hqi _ _).mp h1
    show f' _ = f' _
    rw [u11h_traversal_congr hn hP P' hε hper h2]
  -- continuity via the quotient map from `[0, n]`
  have : CompactSpace (Icc (0 : ℝ) n) := isCompact_iff_compactSpace.mp isCompact_Icc
  let Q : Icc (0 : ℝ) n → frontier D := fun t => ⟨q t.1, hqf t.1⟩
  have hQc : Continuous Q := (hqc.comp continuous_subtype_val).subtype_mk _
  have hQs : Function.Surjective Q := by
    intro y
    obtain ⟨x, hx⟩ := hqs y.1 y.2
    obtain ⟨t, ht, htx⟩ := u11h_exists_reduce P x
    refine ⟨⟨t, ht⟩, Subtype.ext ?_⟩
    show q t = y.1
    rw [← hx]; show f _ = f _; rw [htx]
  have hQq : IsQuotientMap Q := hQc.isClosedMap.isQuotientMap hQc hQs
  have hβc : Continuous β₀ := by
    rw [hQq.continuous_iff]
    have : β₀ ∘ Q = fun t => ⟨q' (φ t.1), hqf' _⟩ := funext fun t => key t.1
    rw [this]
    exact ((hqc'.comp hφ.continuous).comp continuous_subtype_val).subtype_mk _
  have hβbij : Function.Bijective β₀ := by
    constructor
    · intro y₁ y₂ h
      obtain ⟨x₁, hx₁⟩ := hqs y₁.1 y₁.2
      obtain ⟨x₂, hx₂⟩ := hqs y₂.1 y₂.2
      have e₁ : y₁ = ⟨q x₁, hqf x₁⟩ := Subtype.ext hx₁.symm
      have e₂ : y₂ = ⟨q x₂, hqf x₂⟩ := Subtype.ext hx₂.symm
      rw [e₁, e₂, key, key] at h
      have h3 : q' (φ x₁) = q' (φ x₂) := congrArg Subtype.val h
      have h4 := (hqi' _ _).mp h3
      have h5 := u11h_traversal_congr_inv hn' P hP' hε hper hinj h4
      rw [e₁, e₂]
      exact Subtype.ext ((hqi _ _).mpr h5)
    · intro y'
      obtain ⟨x', hx'⟩ := hqs' y'.1 y'.2
      obtain ⟨x, rfl⟩ := hsurj x'
      exact ⟨⟨q x, hqf x⟩, by rw [key]; exact Subtype.ext hx'⟩
  have : CompactSpace (frontier D) := isCompact_iff_compactSpace.mp
    (hD.2.1.of_isClosed_subset isClosed_frontier hD.2.1.isClosed.frontier_subset)
  let E : frontier D ≃ₜ frontier D' :=
    Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective β₀ hβbij) hβc
  refine ⟨fun y => if h : y ∈ frontier D then (β₀ ⟨y, h⟩ : Plane) else 0, ⟨E, ?_⟩, ?_⟩
  · intro z; simp only [z.2, ↓reduceDIte]; rfl
  · intro x
    simp only [hqf x, ↓reduceDIte]
    have := congrArg Subtype.val (key x)
    exact this

/-- 57b for either side (consumes `U7_pl_discs_inner` / `U8_pl_discs_outer`). -/
theorem u11h_pl_disc [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Embedded P) (L : ℝ)
    (hL : InsideModel L P) (s : Side) :
    IsPLDiscSphere L (closure (regionOf P s)) (sphereCircle P) := by
  cases s with
  | inner => exact U7_pl_discs_inner hn P hP L hL
  | outer => exact U8_pl_discs_outer hn P hP L hL

/-- The circle lies in the closure of each region (the `B ⊆ S` clause of 57b, via
`U4_exists_insideModel`). -/
theorem u11h_circle_subset_closure [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Embedded P)
    (s : Side) : sphereCircle P ⊆ closure (regionOf P s) := by
  obtain ⟨L, -, hL⟩ := U4_exists_insideModel P
  obtain ⟨D, f, -, h, -⟩ := u11h_pl_disc hn P hP L hL s
  exact h

/-- U11 (sm-3:433-434 "continuous positive boundary map", FR-TD-10): a positive boundary lift `φ`,
conjugated by two disc parametrisations, is a homeomorphism of the model frontiers. -/
theorem U11_boundary_homeo_of_lift [NeZero n] {n' : ℕ} [NeZero n'] (hn : 3 ≤ n) (P : LabelledTuple n)
    (hP : Embedded P) (hn' : 3 ≤ n') (P' : LabelledTuple n') (hP' : Embedded P') (s s' : Side)
    {D D' : Set Plane} {f f' : Sphere → Plane} (hD : Link.IsDisc D) (hD' : Link.IsDisc D')
    (hf : IsHomeoOnto (closure (regionOf P s)) D f) (hf' : IsHomeoOnto (closure (regionOf P' s')) D' f')
    (hB : f '' sphereCircle P = frontier D) (hB' : f' '' sphereCircle P' = frontier D')
    {φ : ℝ → ℝ} (hφ : IsPositiveBoundaryLift P s P' s' φ) :
    ∃ β : Plane → Plane, IsHomeoOnto (frontier D) (frontier D') β ∧
      ∀ x : ℝ, β (f ((traversal P x : Plane) : Sphere)) = f' ((traversal P' (φ x) : Plane) : Sphere) := by
  exact u11h_boundary_homeo_aux hn P hP hn' P' hP' s s' (u11h_circle_subset_closure hn P hP s)
    (u11h_circle_subset_closure hn' P' hP' s') hD hf hf' hB hB' hφ

/-- U11 (57d, sm-3:433-434 / 537-542): a continuous positive boundary map extends to a topological
disc map `F = Φ'⁻¹ ∘ A ∘ Φ` (the positivity hypothesis is kept as printed and unused, FR-TD-5). -/
theorem U11_top_extension [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Embedded P)
    {n' : ℕ} [NeZero n'] (P' : LabelledTuple n') (hn' : 3 ≤ n') (hP' : Embedded P')
    (s s' : Side) (φ : ℝ → ℝ) (hφ : IsPositiveBoundaryLift P s P' s' φ) :
    ∃ F : Sphere → Sphere,
      IsHomeoOnto (closure (regionOf P s)) (closure (regionOf P' s')) F ∧
      ∀ x : ℝ, F ((traversal P x : Plane) : Sphere) = ((traversal P' (φ x) : Plane) : Sphere) := by
  classical
  obtain ⟨L, -, hL⟩ := U4_exists_insideModel P
  obtain ⟨L', -, hL'⟩ := U4_exists_insideModel P'
  obtain ⟨D, f, hD, -, hf, hB, -⟩ := u11h_pl_disc hn P hP L hL s
  obtain ⟨D', f', hD', hCS', hf', hB', -⟩ := u11h_pl_disc hn' P' hP' L' hL' s'
  obtain ⟨β, hβ, hβφ⟩ := U11_boundary_homeo_of_lift hn P hP hn' P' hP' s s' hD hD' hf hf' hB hB' hφ
  obtain ⟨A, hA, hAβ⟩ := U11_radial_extension hD hD' hβ
  obtain ⟨e, he⟩ := hf
  obtain ⟨e', he'⟩ := hf'
  obtain ⟨eA, heA⟩ := hA
  let finv' : Plane → Sphere := fun y => if h : y ∈ D' then (e'.symm ⟨y, h⟩ : Sphere) else ∞
  refine ⟨fun z => finv' (A (f z)), ⟨e.trans (eA.trans e'.symm), ?_⟩, ?_⟩
  · intro z
    show (e'.symm (eA (e z)) : Sphere) = finv' (A (f z))
    have h1 : (eA (e z) : Plane) = A (f z) := by rw [heA, he]
    have h2 : A (f z) ∈ D' := h1 ▸ (eA (e z)).2
    simp only [finv', h2, ↓reduceDIte]
    have h3 : (⟨A (f z), h2⟩ : D') = eA (e z) := Subtype.ext h1.symm
    rw [h3]
  · intro x
    have hz : ((traversal P x : Plane) : Sphere) ∈ sphereCircle P :=
      ⟨_, (u11h_range_traversal P) ▸ mem_range_self x, rfl⟩
    have hfz : f ((traversal P x : Plane) : Sphere) ∈ frontier D := hB ▸ ⟨_, hz, rfl⟩
    show finv' (A (f _)) = _
    rw [hAβ _ hfz, hβφ x]
    have hz' : ((traversal P' (φ x) : Plane) : Sphere) ∈ closure (regionOf P' s') :=
      hCS' ⟨_, (u11h_range_traversal P') ▸ mem_range_self (φ x), rfl⟩
    have hmem : f' ((traversal P' (φ x) : Plane) : Sphere) ∈ D' := by
      rw [← he' ⟨_, hz'⟩]; exact (e' ⟨_, hz'⟩).2
    simp only [finv', hmem, ↓reduceDIte]
    have : (⟨f' ((traversal P' (φ x) : Plane) : Sphere), hmem⟩ : D') = e' ⟨_, hz'⟩ :=
      Subtype.ext (he' ⟨_, hz'⟩).symm
    rw [this, e'.symm_apply_apply]
/-! ## §5 The row: one field per printed clause -/

/-- **lem:gauss-two-discs** (sm-3:428-436), one field per printed clause; the model scale `L` is
any square containing the polygon (sm-3:439 "a large rectangle"), universally quantified.

Hypotheses of the row theorem `lem_gauss_two_discs`: `Embedded P` is the printed "simple polygonal
circle".  `hn : 3 ≤ n` is derivable from `Embedded P` (a simple closed polygon has at least three
vertices) but is kept for uniformity with row 104 (`cb_embedded_rotation`).  `Generic` is
deliberately *not* a hypothesis: flat vertices are in the domain (sm-3:4791), exactly as in row 104. -/
structure GaussTwoDiscsData [NeZero n] (P : LabelledTuple n) : Prop where
  /-- 57a (sm-3:430-431) "has exactly two complementary regions": the complement of the circle in
  the sphere has exactly two connected components. -/
  two_regions : Nat.card (ConnectedComponents (sphereComplement P)) = 2
  /-- 57b (sm-3:431) "both closures are PL discs": in every model square containing the polygon, the
  closure of each of the two regions is a PL disc of the sphere whose boundary is the circle. -/
  pl_discs : ∀ (s : Side) (L : ℝ), InsideModel L P →
    IsPLDiscSphere L (closure (regionOf P s)) (sphereCircle P)
  /-- 57c (sm-3:431-433) "Finite prescribed positive PL boundary maps between such discs extend to
  positive PL disc maps": for every second simple polygonal circle `P'`, every pair of regions and
  every finite positive PL boundary map (as a lift `φ`), there is a positive PL homeomorphism of the
  closures restricting to the prescribed boundary map. -/
  pl_extension : ∀ {n' : ℕ} [NeZero n'] (P' : LabelledTuple n'), 3 ≤ n' → Embedded P' →
    ∀ (s s' : Side) (L L' : ℝ), InsideModel L P → InsideModel L' P' →
    ∀ φ : ℝ → ℝ, IsPositiveBoundaryLift P s P' s' φ → IsFinitePL n φ →
    ∃ F : Sphere → Sphere,
      IsHomeoOnto (closure (regionOf P s)) (closure (regionOf P' s')) F ∧
      IsPositivePLSphereMap L L' (closure (regionOf P s)) F ∧
      ∀ x : ℝ, F ((traversal P x : Plane) : Sphere) = ((traversal P' (φ x) : Plane) : Sphere)
  /-- 57d (sm-3:433-434) "A continuous positive boundary map also extends to a topological disc
  map": a homeomorphism of the closures restricting to the prescribed boundary map (no PL claim). -/
  top_extension : ∀ {n' : ℕ} [NeZero n'] (P' : LabelledTuple n'), 3 ≤ n' → Embedded P' →
    ∀ (s s' : Side) (φ : ℝ → ℝ), IsPositiveBoundaryLift P s P' s' φ →
    ∃ F : Sphere → Sphere,
      IsHomeoOnto (closure (regionOf P s)) (closure (regionOf P' s')) F ∧
      ∀ x : ℝ, F ((traversal P x : Plane) : Sphere) = ((traversal P' (φ x) : Plane) : Sphere)
  /-- 57e (sm-3:434) "The statement includes the exterior region": the region of `∞` is one of the
  two regions (57b-57d above range over both sides), it is the unbounded one, and the other region
  is a bounded region of the plane. -/
  exterior : ∞ ∈ exteriorRegion P ∧ (∀ z ∈ interiorRegion P, z ≠ ∞) ∧
    Bornology.IsBounded (((↑) : Plane → Sphere) ⁻¹' interiorRegion P) ∧
    ¬ Bornology.IsBounded (((↑) : Plane → Sphere) ⁻¹' exteriorRegion P)

/-- **lem:gauss-two-discs** (row 57, sm-3:428-436). -/
theorem lem_gauss_two_discs [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Embedded P) :
    GaussTwoDiscsData P := by
  refine ⟨U6_two_regions hn P hP, ?_, ?_, ?_, U6_exterior hn P hP⟩
  · intro s L hL
    cases s with
    | inner => exact U7_pl_discs_inner hn P hP L hL
    | outer => exact U8_pl_discs_outer hn P hP L hL
  · intro n' _ P' hn' hP' s s' L L' hL hL' φ hφ hfin
    exact U10_pl_extension hn P hP P' hn' hP' s s' L L' hL hL' φ hφ hfin
  · intro n' _ P' hn' hP' s s' φ hφ
    exact U11_top_extension hn P hP P' hn' hP' s s' φ hφ

/-! ## §6 Bridges for consumers (not part of the row; assembled from the U6/U7 leaves) -/

/-- The plane form of 57a: the complement of the circle in the plane also has exactly two connected
components (the exterior region minus `∞` stays connected). -/
theorem two_regions_plane [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Embedded P) :
    Nat.card (ConnectedComponents ((embeddedPolygonImage P)ᶜ : Set Plane)) = 2 :=
  U6_two_regions_plane hn P hP

/-- A sphere PL disc lying in the plane chart is a plane PL disc (its plane trace). -/
theorem isPLDisc_of_isPLDiscSphere {L : ℝ} {S B : Set Sphere} (hL : 0 < L)
    (hS : S ⊆ ((↑) : Plane → Sphere) '' square L) (h : IsPLDiscSphere L S B) :
    IsPLDisc (((↑) : Plane → Sphere) ⁻¹' S) :=
  U7_isPLDisc_of_isPLDiscSphere hL hS h

/-- The closure of the bounded region, as a plane set, is a plane PL disc. -/
theorem isPLDisc_closure_interior [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Embedded P) :
    IsPLDisc (((↑) : Plane → Sphere) ⁻¹' closure (interiorRegion P)) :=
  U7_isPLDisc_closure_interior hn P hP

end SM
