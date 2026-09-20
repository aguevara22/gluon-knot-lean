import SM.EmbeddedRotation
import SM.LinkMoves
import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Analysis.Convex.Hull
import Mathlib.SetTheory.Cardinal.Finite
import SM.DeletedTuple
import Mathlib.Analysis.Convex.Gauge
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.Connected

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
theorem U1_triangle_isCompact (T : Triangle) : IsCompact T.carrier := by
  sorry

/-- U1: a triangle is convex. -/
theorem U1_triangle_convex (T : Triangle) : Convex ℝ T.carrier := by
  sorry

/-- U1: a nondegenerate triangle has nonempty interior. -/
theorem U1_triangle_interior_nonempty (T : Triangle) : (interior T.carrier).Nonempty := by
  sorry

/-- U1 (sm-3:431 "PL discs", model disc): a triangle is a `Link.IsDisc`. -/
theorem U1_triangle_isDisc (T : Triangle) : Link.IsDisc T.carrier := by
  sorry

/-- U1 (sm-3:439 "large rectangle"): the square `Q_L` is a `Link.IsDisc`. -/
theorem U1_square_isDisc {L : ℝ} (hL : 0 < L) : Link.IsDisc (square L) := by
  sorry

/-- U1: membership in a positively oriented triangle by the three `det` signs. -/
theorem U1_mem_carrier_iff_det (T : Triangle) (x : Plane) :
    x ∈ T.carrier ↔ 0 ≤ det (T.v 1 - T.v 0) (x - T.v 0) ∧ 0 ≤ det (T.v 2 - T.v 1) (x - T.v 1) ∧
      0 ≤ det (T.v 0 - T.v 2) (x - T.v 2) := by
  sorry

/-- U1: the frontier of a triangle is the union of its three edges. -/
theorem U1_frontier_triangle (T : Triangle) :
    frontier T.carrier = ⋃ i : Fin 3, segment ℝ (T.v i) (T.v (i + 1)) := by
  sorry

/-- U1 (sm-3:486-489 "regions"): the interior of a convex set with nonempty interior is connected. -/
theorem U1_interior_convex_isConnected {S : Set Plane} (hS : Convex ℝ S)
    (hne : (interior S).Nonempty) : IsConnected (interior S) := by
  sorry

/-- U1 (sm-3:486-489, the exterior): the complement of a compact convex set in the plane is
connected. -/
theorem U1_compl_compact_convex_isConnected {S : Set Plane} (hS : Convex ℝ S) (hc : IsCompact S) :
    IsConnected Sᶜ := by
  sorry

/-- U1: `AffineOn` is stable under composition. -/
theorem U1_affineOn_comp {f g : Plane → Plane} {S S' : Set Plane} (hf : AffineOn f S)
    (hg : AffineOn g S') (h : f '' S ⊆ S') : AffineOn (g ∘ f) S := by
  sorry

/-- U1: `AffineOn` restricts to subsets. -/
theorem U1_affineOn_mono {f : Plane → Plane} {S S' : Set Plane} (hf : AffineOn f S) (h : S' ⊆ S) :
    AffineOn f S' := by
  sorry

/-- U1: an affine map on a triangle with positive determinant is positive on every sub-triangle. -/
theorem U1_isPositiveAffineOn_mono {f : Plane → Plane} {T T' : Triangle}
    (hf : IsPositiveAffineOn f T) (h : T'.carrier ⊆ T.carrier) : IsPositiveAffineOn f T' := by
  sorry

/-- U1 (sm-3:535-537, positivity multiplicative): composition of positive affine maps is positive. -/
theorem U1_isPositiveAffineOn_comp {f g : Plane → Plane} {T : Triangle}
    (hf : IsPositiveAffineOn f T) (hg : IsPositiveAffineOn g (T.map f hf)) :
    IsPositiveAffineOn (g ∘ f) T := by
  sorry

/-- U1: the affine map of the plane sending the vertices of `T` to three prescribed points. -/
theorem U1_exists_affine_of_triangle (T : Triangle) (w : Fin 3 → Plane) :
    ∃ f : Plane → Plane, AffineOn f univ ∧ ∀ i, f (T.v i) = w i := by
  sorry

/-- U1: the affine map of `U1_exists_affine_of_triangle` is positive on `T` iff the image triple is
positively oriented. -/
theorem U1_isPositiveAffineOn_of_det {f : Plane → Plane} (T : Triangle) (hf : AffineOn f univ)
    (hpos : 0 < det (f (T.v 1) - f (T.v 0)) (f (T.v 2) - f (T.v 0))) : IsPositiveAffineOn f T := by
  sorry

/-- U1 (pasting lemma): a map continuous on each of finitely many closed sets is continuous on
their union. -/
theorem U1_continuousOn_iUnion_of_finite {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    {ι : Type*} [Finite ι] {C : ι → Set α} {f : α → β} (hC : ∀ i, IsClosed (C i))
    (hf : ∀ i, ContinuousOn f (C i)) : ContinuousOn f (⋃ i, C i) := by
  sorry

/-- U1: `IsHomeoOnto` composes. -/
theorem U1_isHomeoOnto_comp {α β γ : Type*} [TopologicalSpace α] [TopologicalSpace β]
    [TopologicalSpace γ] {S : Set α} {S' : Set β} {S'' : Set γ} {f : α → β} {g : β → γ}
    (hf : IsHomeoOnto S S' f) (hg : IsHomeoOnto S' S'' g) : IsHomeoOnto S S'' (g ∘ f) := by
  sorry

/-- U1: `IsHomeoOnto` inverts (any left inverse on `S` is a homeomorphism `S' → S`). -/
theorem U1_isHomeoOnto_inv {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    {S : Set α} {S' : Set β} {f : α → β} {g : β → α} (hf : IsHomeoOnto S S' f)
    (hg : ∀ x ∈ S, g (f x) = x) : IsHomeoOnto S' S g := by
  sorry

/-- U1: `IsHomeoOnto` restricts to a subset and its image. -/
theorem U1_isHomeoOnto_restrict {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    {S : Set α} {S' : Set β} {f : α → β} (hf : IsHomeoOnto S S' f) {A : Set α} (hA : A ⊆ S) :
    IsHomeoOnto A (f '' A) f := by
  sorry

/-- U1: a plane homeomorphism is `IsHomeoOnto` any set onto its image. -/
theorem U1_isHomeoOnto_of_homeomorph (H : Plane ≃ₜ Plane) (A : Set Plane) :
    IsHomeoOnto A (H '' A) H := by
  sorry

/-- U1: a set is `IsHomeoOnto` its coercion image in the sphere. -/
theorem U1_isHomeoOnto_coe (A : Set Plane) :
    IsHomeoOnto A (((↑) : Plane → Sphere) '' A) ((↑) : Plane → Sphere) := by
  sorry

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
