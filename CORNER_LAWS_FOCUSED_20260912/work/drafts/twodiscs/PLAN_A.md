# Row 57 lem:gauss-two-discs — PLAN A (architect A, fidelity first)

Date 2026-09-19.  Trigger: D-AUTH-20260919 G-09 (row 57 un-deferred; cost is not a reason to stop).
Source: reference/SM/sm-3-statesum.tex:428-436 (statement), 437-542 (proof).  Predecessor memo:
work/drafts/pldiscs/PLDISCS_FEASIBILITY.md §2 (clause table 2.1, constructive route 2.2, FR-TD-1..6 in 2.5,
recommended order 2.4).  Statement file: `Statements_A.lean` (this directory; typechecks with
`cd work/lean && lake env lean ../drafts/twodiscs/Statements_A.lean`: 0 errors, 4 `sorry` = the row theorem
and three consumer bridges).  Consumers: none in the checklist that still need it (row 104 accepted 2026-09-14
by an independent proof, D-ER1), so the statement is constrained only by the print.  Row 57 has no fixed
checker name (not in axiom-policy `targets`); the row theorem is `SM.lem_gauss_two_discs`.

## 0. Summary

* The row is stated as one Prop-valued bundle `SM.GaussTwoDiscsData P` with exactly five fields, one per printed
  clause 57a-57e, and the row theorem `SM.lem_gauss_two_discs [NeZero n] (hn : 3 ≤ n) (P) (hP : Embedded P) :
  GaussTwoDiscsData P`.  Hypothesis = "simple polygonal circle" = the accepted `Embedded P` (row 104's
  vocabulary; `Regular` is derived, `Embedded.regular`).
* The sphere is `OnePoint Plane`, the regions are connected components of the complement of the circle in the
  sphere, the exterior region is the component of `∞` (FR-TD-1, FR-TD-2).
* The PL structure of the sphere is the printed two-disc model made explicit: the square `Q_L` with the plane's
  straight structure, capped by a second square `Q_1` carried to the closed exterior of `Q_L` (with `∞ ↦ 0`) by an
  orientation-preserving sup-norm radial inversion that is affine on the seam (FR-TD-7).  PL discs, positive PL
  maps and positive PL homeomorphisms are defined in these charts on finite straight triangulations (§2 of the
  statement file).  The model scale `L` is universally quantified over squares containing the polygon (FR-TD-8).
* Boundary maps are given by their lift `φ : ℝ → ℝ` in the accepted traversal coordinates; "positive" is
  orientation preservation for the induced boundary orientations, expressed through `rotationNumber` (FR-TD-9,
  FR-TD-10); "finite PL" is affine between finitely many marks of one period (the accepted `rexB_pl` pattern).
* Proof route A ("ambient ear induction"): ear-triangulate the polygon; each ear cut is realised by an explicit
  positive PL homeomorphism of the plane supported in a small quadrilateral; their composite `H` carries a base
  triangle `T₀` onto the closed bounded region and `∂T₀` onto the circle.  57a, 57b (interior), 57e and the
  orientation bookkeeping all fall out of `H`; 57b (exterior) is `H` composed with an explicit fan homeomorphism
  of the model exterior of a triangle; 57c is the printed fan extension on convex models conjugated by the disc
  parametrisations; 57d is the printed radial (Alexander) extension conjugated likewise.  No `ZMod 2` chains, no
  Euler characteristic, no ray parity, no strip connectivity.  Total ≈ 21 500 lines (range 17 000-26 000), twelve
  units, four parallel lanes at the start.  The two hardest steps: the ear triangulation with its set-level
  invariants (U4) and the overlay / common-refinement lemma for finite straight triangulations (U3).

## 1. The clauses and their Lean rendering (memo numbering)

| clause | print (sm-3) | field of `GaussTwoDiscsData P` | rendering |
|---|---|---|---|
| 57a | 430-431 "A simple polygonal circle in the oriented sphere has exactly two complementary regions" | `two_regions : Nat.card (ConnectedComponents (sphereComplement P)) = 2` | circle = `sphereCircle P = (↑) '' polygonImage P`, `polygonImage P = ⋃ i, edgeSegment P i`; `Nat.card = 2` forces finitely many components and exactly two |
| 57b | 431 "and both closures are PL discs" | `pl_discs : ∀ (s : Side) (L : ℝ), InsideModel L P → IsPLDiscSphere L (closure (regionOf P s)) (sphereCircle P)` | both regions (`Side.inner`/`Side.outer`), every model square strictly containing the polygon; `IsPLDiscSphere L S B` = a homeomorphism of `S` onto a convex compact plane set with nonempty interior (`Link.IsDisc`) that is positive PL in both model charts and carries `B` onto the frontier of the model (FR-TD-12) |
| 57c | 431-433 "Finite prescribed positive PL boundary maps between such discs extend to positive PL disc maps" | `pl_extension : ∀ {n'} [NeZero n'] (P') (3 ≤ n') (Embedded P') (s s' L L') …, ∀ φ, IsPositiveBoundaryLift P s P' s' φ → IsFinitePL n φ → ∃ F, IsHomeoOnto (closure (regionOf P s)) (closure (regionOf P' s')) F ∧ IsPositivePLSphereMap L L' (closure (regionOf P s)) F ∧ ∀ x, F ↑(traversal P x) = ↑(traversal P' (φ x))` | "such discs" = closures of regions of any two embedded polygons (both sides); the extension is a homeomorphism of closures, positive PL from model `L` to model `L'`, restricting to the prescribed boundary map |
| 57d | 433-434 "A continuous positive boundary map also extends to a topological disc map" | `top_extension : … IsPositiveBoundaryLift P s P' s' φ → ∃ F, IsHomeoOnto … F ∧ ∀ x, F ↑(traversal P x) = ↑(traversal P' (φ x))` | homeomorphism of closures, no PL and no positivity claim in the conclusion (FR-TD-5) |
| 57e | 434 "The statement includes the exterior region" | `exterior : ∞ ∈ exteriorRegion P ∧ (∀ z ∈ interiorRegion P, z ≠ ∞) ∧ IsBounded ((↑) ⁻¹' interiorRegion P) ∧ ¬ IsBounded ((↑) ⁻¹' exteriorRegion P)` | 57b-57d range over both sides by construction; this field identifies the exterior region as the region of `∞`, unbounded, the other one a bounded plane region (FR-TD-11) |

Definitions (all in `Statements_A.lean`, namespace `SM`):
`polygonImage, Sphere, sphereCircle, sphereComplement, exteriorRegion (= connectedComponentIn Ω ∞),
interiorRegion (= Ω \ exteriorRegion), Side, regionOf` (§1);
`Triangle (v : Fin 3 → Plane, 0 < det (v 1 - v 0) (v 2 - v 0)), Triangle.carrier (= convexHull ℝ (range v)),
Triangulation X (faces : Set Triangle, finite, cover : ⋃ carriers = X, inter : carrier ∩ carrier' = convexHull (common
vertices)), AffineOn f S (∃ M : Plane →ₗ[ℝ] Plane, b, f = M · + b on S), IsPositiveAffineOn f T (affine on T and
det of the image triangle > 0), IsPositivePLOn f K, IsHomeoOnto S S' f (∃ e : S ≃ₜ S', e = f), IsPLDisc S`
(§2; `IsPLDisc S := ∃ D K g, Link.IsDisc D ∧ IsPositivePLOn g K ∧ IsHomeoOnto D S g` — the image of a convex
compact set with nonempty interior under a homeomorphism affine with positive determinant on each triangle of a
finite straight triangulation of the model, exactly as requested);
`supNorm, square L, InsideModel L P (∀ i, supNorm (P i) < L), capInvFun L y = (L / supNorm y ^ 2) • (y.1, -y.2),
capChart L (0 ↦ ∞), modelChart L (false ↦ coe, true ↦ capChart L), modelDomain (false ↦ square L, true ↦ square 1),
planeOf, modelChartInv, chartPart L b S, IsPositivePLToPlane L S f, IsPLDiscSphere L S B, IsPositivePLSphereMap
L L' S F` (§3);
`IsFinitePL n φ, traversalPositiveFor P s (:= 0 < rotationNumber P ↔ s = Side.inner), IsPositiveBoundaryLift
P s P' s' φ` (§4).

Why the sphere and not the plane for 57a: the print says "in the oriented sphere" and 57e/57b-exterior only make
sense there (the closure of the unbounded plane region is not compact); the plane form ("one bounded, one
unbounded") is the bridge `two_regions_plane` (sorry in the file; ≈ 400 lines: the exterior region minus `∞` is
still connected, because `∞` has a connected punctured neighbourhood basis `{supNorm ≥ R}` inside the region).

Why the two-disc model is explicit: "PL disc in the sphere" needs a PL structure on `OnePoint Plane`; the plane's
straight structure does not extend across `∞` by any affine chart, and the print itself installs the structure by
the rectangle-plus-cap construction (440-456).  Making the model a definition is the only way to render 57b for the
exterior and the PL clause of 57c literally.  The sup-norm inversion instead of the Euclidean radial map is a
different but PL-homeomorphic model whose seam gluing `y ↦ L • (y.1, −y.2)` is affine, which is what makes
"positive PL in charts" a coherent PL notion (FR-TD-7).

## 2. Fidelity risks and the reading chosen (to be recorded in AUTHOR_NOTES before the statement is frozen)

Memo §2.5 risks:

* **FR-TD-1** (430 "simple polygonal circle in the oriented sphere").  Reading: `Embedded P` with `3 ≤ n` (flat
  vertices allowed, as row 104); sphere = `OnePoint Plane`; `∞` is the printed "one point off the curve" (439);
  orientation = the plane's `det`, transported to the cap chart by an orientation-preserving chart, so "positive"
  is `det > 0` in either chart.  No `Regular` hypothesis (derived, `Embedded.regular`).
* **FR-TD-2** (430-431 "complementary regions").  Reading: connected components of `(sphereCircle P)ᶜ` in the
  subspace topology; the exterior region is `connectedComponentIn Ω ∞`, the interior region is the rest (57a makes
  it one component).  The plane version is a bridge lemma, not a field.
* **FR-TD-3** (431 "PL discs").  Reading: any finite straight triangulation is admissible (the print fixes none);
  the model is `Link.IsDisc` (convex, compact, nonempty interior; a convex compact set with a finite straight
  triangulation is a convex polygon, so this is the printed "convex polygonal disc"); the parametrisation is a
  homeomorphism affine with positive determinant on each triangle.  In the sphere: positive PL in the two-disc
  model charts, at every scale containing the polygon.
* **FR-TD-4** (431-433 "finite prescribed positive PL boundary maps between such discs").  Reading: a boundary map
  `C → C'` is given by a lift `φ : ℝ → ℝ` in traversal coordinates (`traversal P' (φ x)` is the image of
  `traversal P x`), continuous, strictly monotone, degree `±1` (`IsPositiveBoundaryLift`); "finite PL" = affine
  between finitely many marks of one period (`IsFinitePL`, the accepted `rexB_pl` pattern of def:gauss-record,
  affine in the accepted traversal coordinates); "between such discs" = closures of regions (either side) of any two
  embedded polygons, including the two sides of one polygon.  The affine pieces are affine in traversal
  coordinates, which is the same as affine on segments of the plane since `traversal` is affine on each edge.
* **FR-TD-5** (433-434 "topological disc map").  Reading: `∃ F` with `IsHomeoOnto` of the closures and the
  boundary condition; no PL and no positivity claim in the conclusion.  The hypothesis "positive" is kept as
  printed even though the radial extension does not use it (proving the printed statement, not less).
* **FR-TD-6** (437 "no Jordan or Schoenflies conclusion is being assumed").  Route A derives 57a from the ear
  triangulation and the ambient ear homeomorphisms (a finite construction, in the spirit of the printed
  triangulation-first proof); 57b is not derived from 57a; no Mathlib Jordan/winding input exists to import.

New risks introduced by this statement:

* **FR-TD-7** (two-disc model).  The PL structure at `∞` is the explicit model: square `Q_L`, cap `Q_1`, chart
  `capChart L` (`capInvFun L y = (L / ‖y‖_∞²) • (y₁, −y₂)`, `0 ↦ ∞`).  Differs from the printed Euclidean radial
  map `ru ↦ (R(u)/r) u` onto the unit disc (449-452) — same construction in the square's own gauge, plus the
  reflection that makes the chart orientation-preserving; the models are PL-homeomorphic.  Chosen because the seam
  gluing is affine (a real PL atlas) and because a consumer needs the model explicit anyway.  Reviewers should check
  the sign convention: `det > 0` in the cap chart means orientation-preserving on the sphere (verified by the
  Jacobian on `|y₁| > |y₂|`: `det = L²/y₁⁴ > 0`).
* **FR-TD-8** (universal model scale).  57b and 57c hold for every `L` with `InsideModel L P` (all vertices strictly
  inside `Q_L`), not for one large rectangle.  Stronger than the print; the proof is uniform in `L`.
* **FR-TD-9** (`traversalPositiveFor` through `rotationNumber`).  "Positive boundary map" needs the induced boundary
  orientations of the two discs.  The statement *defines* the positive boundary orientation of the interior region
  to be the traversal iff `0 < rotationNumber P` (counterclockwise), and the opposite for the exterior.  This is
  the convention of the accepted `EmbeddedRotationData.orientation` ("left turn = bounded region on the left").  If
  the convention were wrong, 57c would be *false* (not vacuous), so the proof checks it (unit U9).
* **FR-TD-10** (boundary maps as lifts).  Quantifying over lifts `φ` instead of over boundary homeomorphisms `β`:
  every boundary homeomorphism has such a lift (covering theory of `traversal`, injective mod `n` by
  `Embedded.traversal_injective`), and every such `φ` defines a boundary homeomorphism, so the two forms are
  equivalent; the lifting lemma is not part of the row.  The degree condition `φ (x + n) = φ x ± n'` with strict
  monotonicity and continuity makes `β` a homeomorphism `C ≃ₜ C'`.
* **FR-TD-11** (57e rendering).  "The statement includes the exterior region" is rendered by (i) `∀ s : Side` in
  57b-57d and (ii) the identification field `exterior` (the region of `∞` is the unbounded region, the other is a
  bounded plane region).  No duplicate PL-disc restatement for `Side.outer`.
* **FR-TD-12** (boundary of the PL disc).  `IsPLDiscSphere` carries the clause `f '' sphereCircle P = frontier D`:
  the circle is the whole boundary of each region (print 490-491 "each with its single boundary C").  Without it
  57c/57d would not be about boundary maps of the discs.
* **FR-TD-13** (`Triangulation` is set-based).  Faces are a finite set of positively oriented `Triangle`s covering
  exactly `X` with pairwise intersections equal to the convex hull of the common vertices.  Two faces with the
  same carrier and rotated vertex lists are allowed; this is harmless for PL maps and avoids `DecidableEq` on
  triangles.  Not a simplicial complex in Mathlib's sense (no down-closure), by design.
* **FR-TD-14** (chart-membership clause of `IsPositivePLSphereMap`).  Each source face must land in a single
  target chart image; this is the standard "subdivide until each simplex maps into a simplex" PL condition and is
  achievable by refinement (U3).  A reviewer should confirm it does not over-constrain (it does not: the two chart
  images overlap on the seam `↑∂Q_{L'}`, which is closed, so a face can touch the seam from either side).

## 3. Proof plan (route A: ambient ear induction)

### 3.1 Idea

For an embedded polygon `P` (n ≥ 3) build, by induction on `n`, (i) an ear triangulation `Tri(P)` of a compact set
`U(P) ⊆ Plane` with `frontier U(P) = polygonImage P`, and (ii) a positive PL homeomorphism `H : Plane ≃ₜ Plane`,
the identity outside a compact subset of `int Q_L`, with `H(T₀) = U(P)` and `H(∂T₀) = polygonImage P` for a base
triangle `T₀` (the last 3-gon).  Each ear cut `P' = P minus the ear b` (`P` = `P'` with edge `e = [a,c]` replaced by
`[a,b] ∪ [b,c]`, `T = (a,b,c)`, `T ∩ U(P') = e`) is realised by a positive PL homeomorphism `h` of the plane with
`h(U(P')) = U(P)`, affine on four triangles of a convex quadrilateral `K = (o,a,b',c)` and the identity outside:
`o ∈ int T'` close to the midpoint of `e` (`T'` the face of `Tri(P')` at `e`), `b' = o + (1+δ)(b − o)` with the thin
wedge `(a,b',c) \ T` inside `U(P')ᶜ`, `p = [o,b'] ∩ e`, and
`(o,a,p) ↦ (o,a,b)`, `(o,p,c) ↦ (o,b,c)`, `(a,p,b') ↦ (a,b,b')`, `(p,b',c) ↦ (b,b',c)` (each affine, fixing the
shared vertices, `p ↦ b`).  Then

* 57a: `Ω = H(int T₀) ⊔ H(T₀ᶜ)`, two disjoint nonempty open connected sets (interior of a triangle; complement of
  a compact convex set), transported by `Homeomorph.onePointCongr H` to the sphere (`H(T₀ᶜ) ∪ {∞}` stays connected);
  `Nat.card (ConnectedComponents Ω) = 2`; `interiorRegion P = H(int T₀)`, `exteriorRegion P = H(T₀ᶜ) ∪ {∞}`.
* 57b interior: `H` is positive PL on a triangulation of `T₀` (built by local refinements only, §3.3 U7); its
  inverse is positive PL on `U(P)`; `IsPLDiscSphere L (closure interior) C` with model `D = T₀`, `f = planeOf ∘ H⁻¹`
  on the plane chart and an empty cap part.
* 57b exterior / 57e: `closure (exteriorRegion P) = Sphere \ H(int T₀)`; the model exterior
  `E₀ = Sphere \ int T₀ = (Q_L \ int T₀) ∪ cap` has an explicit positive PL homeomorphism `g` onto the square `Q_2`
  (fans from a point of `int T₀` through the vertices of `T₀` and the corners of `Q_L`, inner/outer swapped, the
  identity on the cap chart); `f = g ∘ H⁻¹` (identity on the cap, PL on the plane part) gives
  `IsPLDiscSphere L (closure exterior) C`.
* Orientation (U9): the interior lies on the left of every edge iff `0 < rotationNumber P`, from row 104's
  `orientation` field at a supporting vertex, the fan structure at that vertex, and the ear-induction consistency
  of "interior on the left".  Hence a positive PL parametrisation `Φ : closure (regionOf P s) → D` carries the
  boundary orientation `traversalPositiveFor P s` to the counterclockwise order of `∂D`.
* 57c: `β̃ = Φ' ∘ β ∘ Φ⁻¹ : ∂D → ∂D'` is a finite positive PL circle map between convex polygon boundaries; fan
  extension from interior points `z, z'` with positive determinants by cyclic order (printed 535-537);
  `F = Φ'⁻¹ ∘ Fan ∘ Φ`, positive PL in charts by the composition lemma (U3), boundary condition by construction.
* 57d: radial extension `A(r,u) = (r, b(u))` in gauge coordinates of the convex models (printed 537-542; Mathlib
  `gauge`), `F = Φ'⁻¹ ∘ A ∘ Φ`.

### 3.2 Why not the memo's order or the printed route

* The printed route (arrangement of lines, `ZMod 2` chains, Euler characteristic, collapses, regular
  neighbourhoods) costs 12-20k on the memo's count and needs the whole sphere triangulation before the first
  clause; route A needs no chains, no Euler count, no arrangement of the whole rectangle.
* The memo's ray-parity route for 57a (4-5.5k) gives no PL disc and has the strip-connectivity step (1.5-2.5k, its
  hardest); in route A 57a is a corollary of the construction needed for 57b anyway, and connectivity of the
  exterior is the connectivity of the complement of a triangle.
* The memo's ear route for 57b needed "inductive fan PL homeomorphisms"; route A makes them *ambient* (plane
  homeomorphisms), which is what yields 57a and the exterior for free.  The cost is the thin-wedge argument at the
  two base vertices of each ear (U5), which is a finite positive-distance estimate on `Tri(P')`.
* Admissibility: a different proof of the same statement is admissible (package rules); FR-TD-6 is respected.

### 3.3 Units, estimates, order

| unit | content | reuses | lines | depends on |
|---|---|---|---|---|
| U0 | freeze `Statements_A.lean` → `Statements_FINAL.lean`; record FR-TD-1..14 in AUTHOR_NOTES; skeleton with the definitions and the assembly `lem_gauss_two_discs` from leaves | — | 200 | — |
| U1 | convex/affine toolkit: `Triangle.carrier` compact, convex, nonempty interior, barycentric description (`convexHull_insert`, `convexHull_pair`/`segment`), membership by three `det` signs, the fan of a triangle from an interior point, edge subdivision; `Link.IsDisc` of a triangle and of `square L` (`isDisc_closedBall` pattern); interior of a convex set is connected; complement of a compact convex set in the plane is connected (separating line + far arc); `AffineOn` composition, inverse, restriction; the affine map sending a triangle's vertices to given points (2×2 linear solve), positivity = `det > 0` multiplicative; pasting lemma for finitely many closed sets; `IsHomeoOnto` composition/inverse/restriction | `det`, `planeDot` API (Polygon, Chirotope, EuclideanPlane); Mathlib convex API | 1 300 | — |
| U2 | triangulation basics: `Triangulation` of `∅`, of a triangle, of `square L`; refinement by the fan of one face from an interior point and by subdividing an edge that lies in exactly one face; positive-distance lemma (faces not containing `x` are at positive distance); local structure (a small ball at `x ∈ X` meets `X` only inside the faces containing `x`); frontier of `X`: an edge in exactly one face is in the frontier, open faces / open edges in two faces / vertices with a full fan are interior; pushforward of a triangulation under a positive PL homeomorphism; inverse of a positive PL homeomorphism is positive PL on the pushforward; a face-wise affine, face-wise positive, globally bijective and continuous map is a homeomorphism (compactness) | U1 | 1 600 | U1 |
| U3 | overlay / common refinement: for a face `σ` and finitely many lines, a triangulation of `σ` each of whose faces lies in one closed cell (convex cells = intersections of half-planes; fan from the cell's barycentre; cyclic order of the cell's vertices via `det`); corollaries: common refinement of two triangulations of the same set; composition of positive PL maps is positive PL (`f` PL on `K`, `g` PL on `K'` ⇒ `g ∘ f` PL on a refinement of `K`); refinement so that every face maps into one target chart image (`IsPositivePLSphereMap` composition) | U1, U2 | 2 600 | U2 |
| U4 | ear triangulation of an embedded polygon (Meisters): a supporting vertex with nonzero turn exists (`exists_supporting_vertex_turn_ne_zero`), its triangle is either an ear (no vertex in the closed triangle, no edge crossing) or contains a farthest vertex giving an interior diagonal; cutting an ear gives `deleteVertex P j` (SM/DeletedTuple.lean) embedded; diagonal splits handled by cutting the smaller side first (or by the standard "farthest vertex ⇒ ear elsewhere" induction); output: an ear sequence `(T_k, a_k, b_k, c_k)` with invariants `Tri(P_k)` a `Triangulation (U_k)`, `frontier U_k = polygonImage P_k`, every edge of `P_k` is an edge of exactly one face of `Tri(P_k)`, `T_{k+1} ∩ U_k = e_{k+1}`; also `U_k ⊆ int (square L)` when `InsideModel L P` | `Embedded` (+ `.shift`, `.regular`, `.traversal_injective`), `edgeSegment` API, `deleteVertex`, G1/G2 segment-intersection lemmas (Crossings, G1Consequences) as patterns | 3 800 | U1, U2 |
| U5 | ear-cut ambient homeomorphism `h`: choice of `o` (in the face `T'` at `e`, near the midpoint), of `b'` (thin wedge inside `U(P')ᶜ` by the positive-distance and vertex-cone estimates), `p = [o,b'] ∩ e`; the four affine pieces; `h` is a positive PL homeomorphism of the plane, identity outside `K ⊆ int Q_L`, `h(U') = U`, `h(polygonImage P') = polygonImage P`, `h(T') ⊇ (o,a,c) ∪ T` and the refined faces | U1, U2, U4 | 2 100 | U4 |
| U6 | 57a and 57e: `H = h_m ∘ ⋯ ∘ h_1`, `H(T₀) = U(P)`, `H(∂T₀) = C`, `H(int T₀) = U \ C`; the complement of `∂T₀` has exactly two components; transport by `Homeomorph.onePointCongr`; `exteriorRegion P = H(T₀ᶜ) ∪ {∞}`, `interiorRegion P = H(int T₀)`; `Nat.card (ConnectedComponents Ω) = 2` from a two-open-set partition; boundedness clauses; bridge `two_regions_plane` | Mathlib `connectedComponentIn`, `IsPreconnected.union`, `OnePoint` nhds API | 1 500 | U5 |
| U7 | 57b interior: inductive triangulation `𝒯_k` of `T₀` with `H_k` positive PL on it (local refinement of the face over `T'` by the fan from `H_k⁻¹ o` and the split at `H_k⁻¹ p`; every edge of `P_k` is an edge of `H_k(𝒯_k)`); `IsPLDisc U(P)`; `IsPLDiscSphere L (closure interior) C` via the inverse (U2), empty cap part, `f '' C = frontier T₀`; bridge `isPLDisc_of_isPLDiscSphere`, `isPLDisc_closure_interior` | U2, U5, U6 | 1 500 | U6 |
| U8 | 57b exterior: the model exterior `E₀ = Sphere \ int T₀` → `Q_2` by the 11-ray fan (rays from `o₀ ∈ int T₀` through the 3 vertices of `T₀` and the 4 corners of `Q_L`; radial quadrilaterals split by diagonals; on `∂Q_L` the map is `x ↦ (x₁/L, −x₂/L)`, matching the cap identity; inner/outer swapped, positive by the reflection); `f = g ∘ H⁻¹` positive PL in charts (U3 on the plane part, identity on the cap); `closure (exteriorRegion P) = Sphere \ H(int T₀)` | U3, U6, U7 | 2 600 | U3, U7 |
| U9 | orientation: "interior on the left of edge `i`" ⟺ `det` of the adjacent face; consistency along the ear induction; at the supporting vertex with nonzero turn, left ⟺ `0 < principalTurn`; with `cb_embedded_rotation.orientation` ⟺ `0 < rotationNumber P`; a positive PL homeomorphism `Φ : closure (regionOf P s) → D` carries `traversalPositiveFor P s` to the counterclockwise cyclic order on `∂D` (cyclic order of boundary points around an interior point by two-of-three `det` signs); `IsPositiveBoundaryLift` ⇒ `β̃` preserves that order | `cb_embedded_rotation`, `IsSupportingVertex`, `principalTurn`, `principalAngle` sign API | 1 300 | U4, U7 |
| U10 | 57c: finite positive PL circle map between convex polygon boundaries (marks = images of the `IsFinitePL` marks and the polygon vertices under `Φ`, `Φ'`); fan extension from `z ∈ int D`, `z' ∈ int D'`, positive determinants by preserved cyclic order; `F = Φ'⁻¹ ∘ Fan ∘ Φ` with the chart bookkeeping (U3); `F ↑(traversal P x) = ↑(traversal P' (φ x))` | `rexB_pl`/`rexB_clamp` lemma patterns, `traversal` affine formula `ea_traversal_eq_on_Icc`, U3, U9 | 2 600 | U3, U8, U9 |
| U11 | 57d: gauge coordinates of a convex body with an interior point (Mathlib `gauge`, `gauge_lt_one_iff_mem_interior`-type API), radial homeomorphism of `D` onto `D'` extending a boundary homeomorphism (`x ↦ gauge_D x • b (x / gauge_D x)`-style, continuity at the centre by the radial bound, inverse via `b⁻¹`); `F = Φ'⁻¹ ∘ A ∘ Φ`; boundary condition | Mathlib `Analysis.Convex.Gauge`, U7/U8 parametrisations, U9 (not needed for the proof, kept as hypothesis) | 1 300 | U7, U8 |
| U12 | bundle assembly (`GaussTwoDiscsData` from the leaves), `lem_gauss_two_discs`, `#print axioms`, port to `work/lean/SM/GaussTwoDiscs*.lean` incrementally (D-FR1) | — | 500 | all |
| **total** | | | **≈ 21 500** (range 17 000-26 000) | |

Order and lanes.  Lane A (generic PL library, polygon-free): U1 → U2 → U3.  Lane B (geometry of the polygon):
U4 (needs only U1's triangle basics; can start against a frozen interface of U1).  Lane C (convex-model clauses,
polygon-free, the memo's "57c/57d on convex discs first"): U11's radial extension and U10's fan extension on convex
models, against the `Link.IsDisc`/`Triangulation` interface.  Lane D: U0 (freeze, AUTHOR_NOTES).  Then sequentially
U5 → U6 (57a) → U7 (57b interior, first PL disc) → U9 → U8 (exterior) → U10/U11 assembly → U12.  The first
kernel-checked clause is 57a at U6 (≈ 10k lines in); 57b-interior at U7; the exterior clauses last, as in the memo's
order, but 57a is no longer a separate ray-parity lane.

### 3.4 The two hardest steps

1. **U4, the ear triangulation with set-level invariants** (≈ 3 800).  The ear/diagonal dichotomy needs point-in-
   triangle by `det` signs, "no edge crosses the ear triangle" against all `n` edges, and that the cut polygon
   `deleteVertex P j` is `Embedded` (remote/adjacent case split under the reindexing `ZMod (n+1) → ZMod n`, the
   same kind of surgery as CuspLawTree's).  The invariant `T ∩ U(P') = e` (the new ear meets the old region only in
   the diagonal) is what everything downstream (U5's wedge, U6's two components) rests on; it must be carried
   through the induction as a set identity, not re-derived.  Risk: the memo's 3 500-5 000 estimate for the ear
   route was for row 104; here the invariants are stronger.  Fallback: if the diagonal case (no immediate ear at
   the supporting vertex) is expensive, use the "farthest vertex inside the triangle" argument to produce an ear
   *somewhere* (Meisters' two-ears theorem by induction on `n`) rather than splitting.
2. **U3, overlay / common refinement** (≈ 2 600).  Needed three times: composition of PL maps (57c, and
   `f = g ∘ H⁻¹` in U8), refinement so that faces land in one target chart, and the inverse-image triangulation.
   The clean form: for a face `σ` and a finite set of lines, the closed cells `σ ∩ ⋂ half-planes` are convex
   polygons; triangulate each by the fan from its barycentre — the fan lemma needs the cyclic order of the cell's
   vertices around the barycentre (finite, by `det`, or via `Complex.arg` as in the accepted turn-lift files).
   Risk: 30-50 % overrun.  Mitigation: state the lemma in the weakest form the three uses need ("every face of `K`
   lies in one cell of `K'` after refinement of `K`"), never "the overlay is a triangulation of the union".
   Third in difficulty: **U5**, the ambient ear homeomorphism (the wedge choice with positive-distance estimates
   and the vertex-cone estimate at `a` and `c`).

### 3.5 Genuinely new vocabulary versus reusable accepted material

New (all in the statement file or the skeleton): `Triangle`, `Triangulation`, `AffineOn`, `IsPositiveAffineOn`,
`IsPositivePLOn`, `IsHomeoOnto`, `IsPLDisc`, the two-disc model (`supNorm`, `square`, `InsideModel`, `capInvFun`,
`capChart`, `modelChart`, `modelDomain`, `planeOf`, `modelChartInv`, `chartPart`), `IsPositivePLToPlane`,
`IsPLDiscSphere`, `IsPositivePLSphereMap`, `IsFinitePL`, `Side`, `regionOf`, `traversalPositiveFor`,
`IsPositiveBoundaryLift`, `polygonImage`, `sphereCircle`, `sphereComplement`, `exteriorRegion`, `interiorRegion`;
in the proof: ear sequences, the ear-cut homeomorphism, the fan/overlay refinements, gauge coordinates.  **Not**
needed in route A: chains over `ZMod 2`, Euler characteristic, collapses, regular neighbourhoods, winding numbers,
the `IsLiftOn` calculus (it remains available as a fallback for the orientation unit U9 if the fan argument at the
supporting vertex is awkward).

Reusable accepted material: `Embedded` and its lemmas (`Embedded.regular`, `.traversal_injective`, `.shift`,
`embedded_of_generic_of_isEmpty_crossing`), `traversal` (`traversal_add_nat`, `continuous_traversal`,
`traversal_int_add`, `ea_traversal_eq_on_Icc`), `IsSupportingVertex`, `exists_supporting_vertex_turn_ne_zero`,
`isSupportingVertex_shift`, `cb_embedded_rotation` (rotation `±1` and the orientation field), `rotationNumber`,
`principalTurn`, `Link.IsDisc` and `isDisc_closedBall`, `det`/`planeDot`/`bracket` API, `deleteVertex`
(SM/DeletedTuple.lean), `rexB_pl`/`rexB_clamp`/`rexB_slope` lemmas as the PL-in-one-variable pattern, the G1/G2
segment-intersection lemmas as patterns for "no edge crosses the triangle".  Mathlib: `convexHull` API,
`Convex`/`IsCompact`, `Homeomorph.onePointCongr`, `OnePoint` neighbourhood API, `connectedComponentIn`,
`IsPreconnected` unions, `gauge`, `Metric` on `ℝ × ℝ`.

## 4. Statement checks performed

* `Statements_A.lean`: 0 errors, 4 `sorry` (row theorem, `two_regions_plane`, `isPLDisc_of_isPLDiscSphere`,
  `isPLDisc_closure_interior`).
* Sanity of the chart algebra (by hand, to be made lemmas in U8): `capInvFun L` is an involution of `Plane \ {0}`
  up to the scale (`capInvFun L (capInvFun L y) = y`), `supNorm (capInvFun L y) = L / supNorm y`, so it carries
  `square 1 \ {0}` onto `{supNorm ≥ L}` and `∂(square 1)` onto `∂(square L)` by `y ↦ L • (y₁, −y₂)`; Jacobian
  determinant `L² / y₁⁴ > 0` on `|y₁| > |y₂|` and `L² / y₂⁴ > 0` on `|y₂| > |y₁|` (orientation-preserving).
* Sanity of the positivity convention: `P = P'`, `s = s' = inner`, `φ = id` is a positive boundary lift and
  `F = id` is a positive PL extension; `s = inner`, `s' = outer` for the same `P` forces `φ` decreasing
  (`traversalPositiveFor P inner ↔ traversalPositiveFor P outer` is false), which is what an orientation-preserving
  homeomorphism from the inside disc to the outside disc must do on the common boundary.
* For `InsideModel L P` and `s = inner`, `chartPart L true (closure interior) = ∅` (the cap chart image misses the
  closed bounded region), so `IsPositivePLToPlane` needs only the plane chart there; `Triangulation ∅` is the
  empty face set.
