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
* circle = `Embedded P` (accepted, SM/EmbeddedRotation.lean), its image `polygonImage P = ⋃ edgeSegment`;
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
def polygonImage (P : LabelledTuple n) : Set Plane := ⋃ i, edgeSegment P i

/-- The oriented sphere (sm-3:430 "in the oriented sphere"): the one-point compactification of the
plane, oriented by the plane's `det`. -/
abbrev Sphere : Type := OnePoint Plane

/-- The circle as a subset of the sphere. -/
def sphereCircle (P : LabelledTuple n) : Set Sphere := ((↑) : Plane → Sphere) '' polygonImage P

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

/-- U2: the set `X` of a triangulation is compact. -/
theorem U2_isCompact_of_triangulation {X : Set Plane} (K : Triangulation X) : IsCompact X := by
  sorry

/-- U2 (sm-3:440-443, the empty part of a chart): the empty set has a triangulation. -/
theorem U2_triangulation_empty : Nonempty (Triangulation (∅ : Set Plane)) := by
  sorry

/-- U2: a triangle is triangulated by itself. -/
theorem U2_triangulation_triangle (T : Triangle) : Nonempty (Triangulation T.carrier) := by
  sorry

/-- U2 (sm-3:440 "triangulate the rectangle"): the square `Q_L` has a triangulation. -/
theorem U2_triangulation_square {L : ℝ} (hL : 0 < L) : Nonempty (Triangulation (square L)) := by
  sorry

/-- U2: a refinement carries positive PL maps (positivity is inherited by sub-triangles). -/
theorem U2_isPositivePLOn_of_refines {X : Set Plane} {K K' : Triangulation X} {f : Plane → Plane}
    (hf : IsPositivePLOn f K) (h : K'.Refines K) : IsPositivePLOn f K' := by
  sorry

/-- U2 (fan refinement): a face may be replaced by its fan from an interior point. -/
theorem U2_refine_fan {X : Set Plane} (K : Triangulation X) {T : Triangle} (hT : T ∈ K.faces)
    {o : Plane} (ho : o ∈ interior T.carrier) :
    ∃ K' : Triangulation X, K'.Refines K ∧
      (∀ T' ∈ K.faces, T'.carrier ≠ T.carrier → T' ∈ K'.faces) ∧
      (∀ i : Fin 3, ∃ T' ∈ K'.faces, T'.carrier = convexHull ℝ {o, T.v i, T.v (i + 1)}) := by
  sorry

/-- U2 (edge split): an edge lying in exactly one face may be subdivided at an interior point. -/
theorem U2_refine_edge_split {X : Set Plane} (K : Triangulation X) {T : Triangle} (hT : T ∈ K.faces)
    (i : Fin 3) (huniq : ∀ T' ∈ K.faces, T.edgeSeg i ⊆ T'.carrier → T'.carrier = T.carrier)
    {p : Plane} (hp : p ∈ openSegment ℝ (T.v i) (T.v (i + 1))) :
    ∃ K' : Triangulation X, K'.Refines K ∧
      (∀ T' ∈ K.faces, T'.carrier ≠ T.carrier → T' ∈ K'.faces) ∧
      (∃ T₁ ∈ K'.faces, T₁.carrier = convexHull ℝ {T.v i, p, T.v (i + 2)}) ∧
      (∃ T₂ ∈ K'.faces, T₂.carrier = convexHull ℝ {p, T.v (i + 1), T.v (i + 2)}) := by
  sorry

/-- U2 (positive distance): the faces not containing `x` stay at positive distance from `x`. -/
theorem U2_exists_ball_disjoint_faces {X : Set Plane} (K : Triangulation X) (x : Plane) :
    ∃ ε > 0, ∀ T ∈ K.faces, x ∉ T.carrier → Disjoint (Metric.ball x ε) T.carrier := by
  sorry

/-- U2 (local structure): near `x ∈ X` the set `X` is the union of the faces containing `x`. -/
theorem U2_local_structure {X : Set Plane} (K : Triangulation X) {x : Plane} (hx : x ∈ X) :
    ∃ ε > 0, Metric.ball x ε ∩ X = Metric.ball x ε ∩ ⋃ T ∈ {T ∈ K.faces | x ∈ T.carrier}, T.carrier := by
  sorry

/-- U2 (sm-3:490-491 "single boundary"): an edge lying in exactly one face is in the frontier. -/
theorem U2_edgeSeg_subset_frontier {X : Set Plane} (K : Triangulation X) {T : Triangle}
    (hT : T ∈ K.faces) (i : Fin 3)
    (huniq : ∀ T' ∈ K.faces, T.edgeSeg i ⊆ T'.carrier → T'.carrier = T.carrier) :
    T.edgeSeg i ⊆ frontier X := by
  sorry

/-- U2: the open faces lie in the interior of `X`. -/
theorem U2_interior_face_subset_interior {X : Set Plane} (K : Triangulation X) {T : Triangle}
    (hT : T ∈ K.faces) : interior T.carrier ⊆ interior X := by
  sorry

/-- U2: an open edge shared by two distinct faces lies in the interior of `X`. -/
theorem U2_openSegment_subset_interior_of_two_faces {X : Set Plane} (K : Triangulation X)
    {T T' : Triangle} (hT : T ∈ K.faces) (hT' : T' ∈ K.faces) (hne : T.carrier ≠ T'.carrier)
    (i : Fin 3) (h : T.edgeSeg i ⊆ T'.carrier) : openSegment ℝ (T.v i) (T.v (i + 1)) ⊆ interior X := by
  sorry

/-- U2: the frontier of `X` is the union of the edges lying in exactly one face. -/
theorem U2_frontier_eq_iUnion_boundary_edges {X : Set Plane} (K : Triangulation X) :
    frontier X = ⋃ T ∈ K.faces, ⋃ i : Fin 3,
      ⋃ (_ : ∀ T' ∈ K.faces, T.edgeSeg i ⊆ T'.carrier → T'.carrier = T.carrier), T.edgeSeg i := by
  sorry

/-- U2 (pushforward): the image triangulation under a positive PL homeomorphism of the plane. -/
theorem U2_pushforward {X : Set Plane} (K : Triangulation X) (H : Plane ≃ₜ Plane)
    (hH : IsPositivePLOn H K) :
    ∃ K' : Triangulation (H '' X), (∀ T ∈ K.faces, ∃ hT : IsPositiveAffineOn H T, T.map H hT ∈ K'.faces) ∧
      ∀ T' ∈ K'.faces, ∃ T ∈ K.faces, T'.carrier = H '' T.carrier := by
  sorry

/-- U2 (inverse): the inverse of a positive PL homeomorphism is positive PL on the pushforward. -/
theorem U2_inverse_isPositivePLOn {X : Set Plane} (K : Triangulation X) (H : Plane ≃ₜ Plane)
    (hH : IsPositivePLOn H K) :
    ∃ K' : Triangulation (H '' X), IsPositivePLOn H.symm K' := by
  sorry

/-- U2 (sm-3:520-523, the disc parametrisation is a homeomorphism): a face-wise positive affine map
that is injective on `X` is a homeomorphism of `X` onto its image (compactness). -/
theorem U2_isHomeoOnto_of_isPositivePLOn {X : Set Plane} (K : Triangulation X) {f : Plane → Plane}
    (hf : IsPositivePLOn f K) (hinj : InjOn f X) : IsHomeoOnto X (f '' X) f := by
  sorry

/-- U2: a positive PL map is continuous on `X`. -/
theorem U2_continuousOn_of_isPositivePLOn {X : Set Plane} (K : Triangulation X) {f : Plane → Plane}
    (hf : IsPositivePLOn f K) : ContinuousOn f X := by
  sorry

/-! ### U3 (lane A) — overlay / common refinement -/

/-- U3: `g : Plane → Sphere` is positive PL from the plane set `D` into the sphere with model `L'`:
`D` carries a triangulation each of whose faces is sent into one target chart image, where `g` read
in that chart is positive affine (the inverse-parametrisation side of `IsPositivePLSphereMap`). -/
def IsPositivePLFromPlane (L' : ℝ) (D : Set Plane) (g : Plane → Sphere) : Prop :=
  ∃ K : Triangulation D, ∀ T ∈ K.faces, ∃ b' : Bool,
    (∀ x ∈ T.carrier, g x ∈ modelChart L' b' '' modelDomain L' b') ∧
    IsPositiveAffineOn (modelChartInv L' b' ∘ g) T

/-- U3 (sm-3:462-466 "subdivide"): a triangulation can be refined so that every face lies on one
side of each of finitely many lines `{x | ⟪a j, x⟫ = c j}`. -/
theorem U3_refine_along_lines {X : Set Plane} (K : Triangulation X) {m : ℕ} (a : Fin m → Plane)
    (c : Fin m → ℝ) :
    ∃ K' : Triangulation X, K'.Refines K ∧ ∀ T' ∈ K'.faces, ∀ j,
      T'.carrier ⊆ {x | planeDot (a j) x ≤ c j} ∨ T'.carrier ⊆ {x | c j ≤ planeDot (a j) x} := by
  sorry

/-- U3: a triangulation can be refined so that every face lies in one face of a second
triangulation of a superset. -/
theorem U3_refine_into {X Y : Set Plane} (K : Triangulation X) (K' : Triangulation Y) (h : X ⊆ Y) :
    ∃ K'' : Triangulation X, K''.Refines K ∧ ∀ T'' ∈ K''.faces, ∃ T' ∈ K'.faces, T''.carrier ⊆ T'.carrier := by
  sorry

/-- U3 (common refinement): two triangulations of the same set have a common refinement. -/
theorem U3_common_refinement {X : Set Plane} (K K' : Triangulation X) :
    ∃ K'' : Triangulation X, K''.Refines K ∧ K''.Refines K' := by
  sorry

/-- U3 (sm-3:535-537, composition): the composite of positive PL maps is positive PL on a
refinement of the source triangulation. -/
theorem U3_isPositivePLOn_comp {X Y : Set Plane} (K : Triangulation X) (K' : Triangulation Y)
    {f g : Plane → Plane} (hf : IsPositivePLOn f K) (hg : IsPositivePLOn g K') (h : f '' X ⊆ Y) :
    ∃ K'' : Triangulation X, K''.Refines K ∧ IsPositivePLOn (g ∘ f) K'' := by
  sorry

/-- U3 (chart bookkeeping, FR-TD-14): a positive PL map to the plane followed by a positive PL map
from the plane into the sphere is a positive PL sphere map. -/
theorem U3_isPositivePLSphereMap_comp {L L' : ℝ} {S : Set Sphere} {D : Set Plane}
    {f : Sphere → Plane} {g : Plane → Sphere} (hf : IsPositivePLToPlane L S f) (hfD : f '' S ⊆ D)
    (hg : IsPositivePLFromPlane L' D g) : IsPositivePLSphereMap L L' S (g ∘ f) := by
  sorry

/-- U3: a positive PL sphere map followed by a positive PL map to the plane is positive PL to the
plane. -/
theorem U3_isPositivePLToPlane_comp {L L' : ℝ} {S S' : Set Sphere} {F : Sphere → Sphere}
    {f : Sphere → Plane} (hF : IsPositivePLSphereMap L L' S F) (hFS : F '' S ⊆ S')
    (hf : IsPositivePLToPlane L' S' f) : IsPositivePLToPlane L S (f ∘ F) := by
  sorry

/-- U3: a positive PL map to the plane followed by a positive PL plane map is positive PL to the
plane. -/
theorem U3_isPositivePLToPlane_comp_plane {L : ℝ} {S : Set Sphere} {D : Set Plane}
    (K : Triangulation D) {f : Sphere → Plane} {g : Plane → Plane} (hf : IsPositivePLToPlane L S f)
    (hfD : f '' S ⊆ D) (hg : IsPositivePLOn g K) : IsPositivePLToPlane L S (g ∘ f) := by
  sorry

/-- U3 (inverse chart bookkeeping): the inverse of a positive PL parametrisation `f : S → D` (a
homeomorphism, positive PL in charts) is positive PL from the plane. -/
theorem U3_isPositivePLFromPlane_inv {L : ℝ} {S : Set Sphere} {D : Set Plane} {f : Sphere → Plane}
    (hD : Link.IsDisc D) (hf : IsHomeoOnto S D f) (hpl : IsPositivePLToPlane L S f) :
    ∃ g : Plane → Sphere, IsPositivePLFromPlane L D g ∧ (∀ z ∈ S, g (f z) = z) ∧
      ∀ x ∈ D, f (g x) = x := by
  sorry

/-! ### U4 (lane B) — ear triangulation of an embedded polygon (Meisters) -/

/-- U4: the ear triangle at vertex `j` (vertices `P (j-1), P j, P (j+1)`). -/
def earHull (P : LabelledTuple n) (j : ZMod n) : Set Plane :=
  convexHull ℝ {P (j - 1), P j, P (j + 1)}

/-- U4: the polygon image is compact. -/
theorem U4_polygonImage_isCompact [NeZero n] (P : LabelledTuple n) : IsCompact (polygonImage P) := by
  sorry

/-- U4: the traversal image is the polygon image. -/
theorem U4_range_traversal [NeZero n] (P : LabelledTuple n) : range (traversal P) = polygonImage P := by
  sorry

/-- U4 (sm-3:439 "inside a large rectangle"): some model square contains the polygon. -/
theorem U4_exists_insideModel [NeZero n] (P : LabelledTuple n) : ∃ L : ℝ, 0 < L ∧ InsideModel L P := by
  sorry

/-- U4: `InsideModel L P` puts the polygon image strictly inside `Q_L`. -/
theorem U4_polygonImage_subset_interior_square [NeZero n] {L : ℝ} (P : LabelledTuple n)
    (hL : InsideModel L P) : polygonImage P ⊆ interior (square L) ∧ 0 < L := by
  sorry

/-- U4: an embedded polygon has at least three vertices. -/
theorem U4_three_le_of_embedded [NeZero n] (P : LabelledTuple n) (hP : Embedded P) : 3 ≤ n := by
  sorry

/-- U4 (base case): an embedded triangle bounds its convex hull. -/
theorem U4_triangle_base (P : LabelledTuple 3) (hP : Embedded P) :
    det (P 1 - P 0) (P 2 - P 0) ≠ 0 ∧ polygonImage P = frontier (earHull P 1) := by
  sorry

/-- U4 (Meisters' two ears, sm-3:437-439 spirit): an embedded polygon with at least four vertices has
an ear: a vertex `j` with nonzero turn whose ear triangle meets the rest of the polygon exactly in
the diagonal, and whose deletion is again embedded. -/
theorem U4_exists_ear [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple (n + 1)) (hP : Embedded P) :
    ∃ j : ZMod (n + 1), Embedded (deleteVertex P j) ∧
      det (P j - P (j - 1)) (P (j + 1) - P (j - 1)) ≠ 0 ∧
      earHull P j ∩ polygonImage (deleteVertex P j) = segment ℝ (P (j - 1)) (P (j + 1)) := by
  sorry

/-- U4 (ear-cut identity): the polygon image of `P` is that of the cut polygon with the diagonal
replaced by the two ear edges. -/
theorem U4_polygonImage_ear [NeZero n] (P : LabelledTuple (n + 1)) (j : ZMod (n + 1)) :
    polygonImage P = (polygonImage (deleteVertex P j) \ openSegment ℝ (P (j - 1)) (P (j + 1))) ∪
      segment ℝ (P (j - 1)) (P j) ∪ segment ℝ (P j) (P (j + 1)) := by
  sorry

/-- U4 (output, sm-3:437-443 "triangulate ... the polygon"): an embedded polygon bounds a compact
set `U` with a triangulation in which every edge of `P` is an edge of exactly one face, `frontier U`
is the circle, and `U` lies strictly inside every model square containing `P`. -/
theorem U4_exists_triangulation [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Embedded P) :
    ∃ (U : Set Plane) (K : Triangulation U), frontier U = polygonImage P ∧
      (∀ i, ∃ T ∈ K.faces, ∃ k : Fin 3, T.edgeSeg k = edgeSegment P i) ∧
      (∀ i, ∀ T ∈ K.faces, ∀ T' ∈ K.faces, edgeSegment P i ⊆ T.carrier →
        edgeSegment P i ⊆ T'.carrier → T.carrier = T'.carrier) ∧
      ∀ L, InsideModel L P → U ⊆ interior (square L) := by
  sorry

/-! ### U5 (sequential) — the ear-cut ambient homeomorphism -/

/-- U5 (sm-3:437-443 realised ambiently, PLAN_FINAL §3.1): cutting an ear `j` of `P` is realised by
a positive PL homeomorphism `h` of the plane, the identity outside a compact subset of `int Q_L`,
carrying the region `U'` bounded by the cut polygon onto `U' ∪ ear` and the cut circle onto the
circle of `P`. -/
theorem U5_exists_ear_homeo [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple (n + 1)) (hP : Embedded P)
    (j : ZMod (n + 1)) (hP' : Embedded (deleteVertex P j))
    (hturn : det (P j - P (j - 1)) (P (j + 1) - P (j - 1)) ≠ 0)
    (hear : earHull P j ∩ polygonImage (deleteVertex P j) = segment ℝ (P (j - 1)) (P (j + 1)))
    (U' : Set Plane) (K' : Triangulation U') (hU' : frontier U' = polygonImage (deleteVertex P j))
    (hedge : ∀ T ∈ K'.faces, ∀ T' ∈ K'.faces, segment ℝ (P (j - 1)) (P (j + 1)) ⊆ T.carrier →
      segment ℝ (P (j - 1)) (P (j + 1)) ⊆ T'.carrier → T.carrier = T'.carrier)
    (hface : ∃ T ∈ K'.faces, ∃ k : Fin 3, T.edgeSeg k = segment ℝ (P (j - 1)) (P (j + 1)))
    {L : ℝ} (hL : InsideModel L P) (hU'L : U' ⊆ interior (square L)) :
    ∃ (h : Plane ≃ₜ Plane) (Kh : Triangulation (square L)) (Kin : Triangulation U'),
      IsPositivePLOn h Kh ∧ IsPositivePLOn h Kin ∧ Kin.Refines K' ∧
      (∀ x, L ≤ supNorm x → h x = x) ∧
      h '' U' = U' ∪ earHull P j ∧ h '' polygonImage (deleteVertex P j) = polygonImage P ∧
      frontier (U' ∪ earHull P j) = polygonImage P ∧ U' ∪ earHull P j ⊆ interior (square L) := by
  sorry

/-- U5: the ear-cut homeomorphism sends the faces of the refined triangulation `Kin` of `U'` to a
triangulation of `U' ∪ ear` in which every edge of `P` is an edge of exactly one face. -/
theorem U5_pushforward_edges [NeZero n] (P : LabelledTuple (n + 1)) (j : ZMod (n + 1))
    (U' : Set Plane) (Kin : Triangulation U') (h : Plane ≃ₜ Plane) (hh : IsPositivePLOn h Kin)
    (hU : h '' U' = U' ∪ earHull P j) (hC : h '' polygonImage (deleteVertex P j) = polygonImage P)
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
  boundary : H '' frontier T₀.carrier = polygonImage P

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
    Nat.card (ConnectedComponents ((polygonImage P)ᶜ : Set Plane)) = 2 := by
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

/-- U8 (chart algebra, PLAN_FINAL §4): the sup-norm inversion is an involution off `0`. -/
theorem U8_capInvFun_capInvFun {L : ℝ} (hL : 0 < L) {y : Plane} (hy : y ≠ 0) :
    capInvFun L (capInvFun L y) = y := by
  sorry

/-- U8: `‖capInvFun L y‖_∞ = L / ‖y‖_∞`. -/
theorem U8_supNorm_capInvFun {L : ℝ} (hL : 0 < L) {y : Plane} (hy : y ≠ 0) :
    supNorm (capInvFun L y) = L / supNorm y := by
  sorry

/-- U8 (sm-3:448-456 "the actual one-point-compactified exterior"): the cap chart is a homeomorphism
of `Q_1` onto the closed exterior of `Q_L` together with `∞`. -/
theorem U8_capChart_isHomeoOnto {L : ℝ} (hL : 0 < L) :
    IsHomeoOnto (square 1) (((↑) : Plane → Sphere) '' {x | L ≤ supNorm x} ∪ {∞}) (capChart L) := by
  sorry

/-- U8: on the seam `‖y‖_∞ = 1` the cap chart is the affine map `y ↦ L • (y₁, −y₂)`. -/
theorem U8_capInvFun_seam {L : ℝ} {y : Plane} (hy : supNorm y = 1) :
    capInvFun L y = L • (y.1, -y.2) := by
  sorry

/-- U8 (the 11-ray fan, PLAN_FINAL §3.3): the model exterior `Sphere \ int T₀` of a triangle inside
`int Q_L` is carried onto the square `Q_2` by a homeomorphism that is positive PL in the two model
charts and sends `∂T₀` onto `∂Q_2`. -/
theorem U8_exists_exterior_fan {L : ℝ} (hL : 0 < L) (T₀ : Triangle)
    (hT : T₀.carrier ⊆ interior (square L)) :
    ∃ g : Sphere → Plane,
      IsHomeoOnto (((↑) : Plane → Sphere) '' interior T₀.carrier)ᶜ (square 2) g ∧
      IsPositivePLToPlane L (((↑) : Plane → Sphere) '' interior T₀.carrier)ᶜ g ∧
      g '' (((↑) : Plane → Sphere) '' frontier T₀.carrier) = frontier (square 2) := by
  sorry

/-- U8: the closed exterior region is the sphere minus the open image triangle. -/
theorem U8_closure_exteriorRegion_eq [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Embedded P)
    {L : ℝ} (A : AmbientParam P L) :
    closure (exteriorRegion P) = (((↑) : Plane → Sphere) '' (A.H '' interior A.T₀.carrier))ᶜ := by
  sorry

/-- U8: `H⁻¹` extended by the identity at `∞` is a positive PL sphere map (model `L` to model `L`)
on the closed exterior region. -/
theorem U8_isPositivePLSphereMap_inv [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Embedded P)
    {L : ℝ} (hL : InsideModel L P) (A : AmbientParam P L) :
    IsPositivePLSphereMap L L (closure (exteriorRegion P)) (OnePoint.map A.H.symm) ∧
      IsHomeoOnto (closure (exteriorRegion P)) (((↑) : Plane → Sphere) '' interior A.T₀.carrier)ᶜ
        (OnePoint.map A.H.symm) := by
  sorry

/-- U8 (57b exterior, sm-3:431 / 448-456 / 490-493): the closure of the exterior region is a PL disc
of the sphere with boundary the circle. -/
theorem U8_pl_discs_outer [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Embedded P) (L : ℝ)
    (hL : InsideModel L P) : IsPLDiscSphere L (closure (regionOf P Side.outer)) (sphereCircle P) := by
  sorry

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

/-- U10 (sm-3:535-537, the fan extension on convex models): a finite positive PL homeomorphism
between the boundaries of two convex discs, preserving the cyclic order around interior points
`z ↦ z'`, extends to a positive PL homeomorphism of the discs (cone from `z` to `z'`). -/
theorem U10_fan_extension {D D' : Set Plane} (hD : Link.IsDisc D) (hD' : Link.IsDisc D')
    {z z' : Plane} (hz : z ∈ interior D) (hz' : z' ∈ interior D') {β : Plane → Plane}
    (hβ : IsHomeoOnto (frontier D) (frontier D') β) (hpl : IsFinitePLOnFrontier D β)
    (hpos : PreservesCyclicPos D z z' β) :
    ∃ (K : Triangulation D) (F : Plane → Plane), IsPositivePLOn F K ∧ IsHomeoOnto D D' F ∧
      ∀ x ∈ frontier D, F x = β x := by
  sorry

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
  sorry

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
  sorry

/-! ### U11 (lane C convex model, then sequential) — 57d -/

/-- U11 (gauge coordinates): for a convex disc with `0` in its interior, the frontier is the gauge
level `1` and the disc is the sublevel `≤ 1`. -/
theorem U11_frontier_eq_gauge_one {D : Set Plane} (hD : Link.IsDisc D) (h0 : (0 : Plane) ∈ interior D) :
    frontier D = {x | gauge D x = 1} ∧ D = {x | gauge D x ≤ 1} := by
  sorry

/-- U11 (sm-3:537-542, the radial / Alexander extension on convex models): a homeomorphism between
the frontiers of two convex discs extends to a homeomorphism of the discs. -/
theorem U11_radial_extension {D D' : Set Plane} (hD : Link.IsDisc D) (hD' : Link.IsDisc D')
    {β : Plane → Plane} (hβ : IsHomeoOnto (frontier D) (frontier D') β) :
    ∃ F : Plane → Plane, IsHomeoOnto D D' F ∧ ∀ x ∈ frontier D, F x = β x := by
  sorry

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
  sorry

/-- U11 (57d, sm-3:433-434 / 537-542): a continuous positive boundary map extends to a topological
disc map `F = Φ'⁻¹ ∘ A ∘ Φ` (the positivity hypothesis is kept as printed and unused, FR-TD-5). -/
theorem U11_top_extension [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Embedded P)
    {n' : ℕ} [NeZero n'] (P' : LabelledTuple n') (hn' : 3 ≤ n') (hP' : Embedded P')
    (s s' : Side) (φ : ℝ → ℝ) (hφ : IsPositiveBoundaryLift P s P' s' φ) :
    ∃ F : Sphere → Sphere,
      IsHomeoOnto (closure (regionOf P s)) (closure (regionOf P' s')) F ∧
      ∀ x : ℝ, F ((traversal P x : Plane) : Sphere) = ((traversal P' (φ x) : Plane) : Sphere) := by
  sorry
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
    Nat.card (ConnectedComponents ((polygonImage P)ᶜ : Set Plane)) = 2 :=
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
