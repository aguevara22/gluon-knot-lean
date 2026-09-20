# Row 57 — unit U3 (overlay / common refinement) — report W1_U3

Written 2026-09-19 by the U3 executor.  File: `work/drafts/twodiscs/W1_U3.lean` (3 660 lines; skeleton 1 039).
Check: `cd work/lean && lake env lean ../drafts/twodiscs/W1_U3.lean` → **0 errors, 85 `sorry` warnings** (the
85 leaves of the other units; every U3 helper and every closed U3 leaf is `sorry`-free in its own body).
`python3 check_57_identity.py W1_U3.lean` → `IDENTITY OK` (DEFS, BUNDLE, THM).  `grep -c sorry`: skeleton 95 →
W1_U3 88 (the 7 closed leaves; the 3 other hits are in docstrings, as in the skeleton).

## 1. Leaves

| leaf | status |
|---|---|
| `U3_refine_along_lines` | **closed** (projection of `u3h_refine_along_lines`, which also tracks vertices) |
| `U3_refine_into` | **closed** |
| `U3_common_refinement` | **closed** (from `U3_refine_into` with `Y = X`) |
| `U3_isPositivePLOn_comp` | **closed** |
| `U3_isPositivePLSphereMap_comp` | **closed** |
| `U3_isPositivePLToPlane_comp` | **closed** (all `L'`; at `L' = 0` the source triangulation has no faces) |
| `U3_isPositivePLToPlane_comp_plane` | **closed** |
| `U3_isPositivePLFromPlane_inv` | **open — FALSE as stated** (rule 3); corrected form `u3h_isPositivePLFromPlane_inv` proved, see §3 |

`#print axioms` (scratch copy) of each closed leaf: `[propext, sorryAx, Classical.choice, Quot.sound]` — the
`sorryAx` comes only through the consumed leaves of §2 (e.g. `u3h_split_exists` and `u3h_inter_of_family`, which
consume nothing, print `[propext, Classical.choice, Quot.sound]`).

## 2. Black boxes (consumed leaves of other units, by name, statements untouched)

U1: `U1_triangle_isCompact`, `U1_triangle_convex`, `U1_triangle_interior_nonempty`, `U1_frontier_triangle`,
`U1_mem_carrier_iff_det`, `U1_isPositiveAffineOn_mono`, `U1_isPositiveAffineOn_comp`.
U2: `U2_interior_face_subset_interior`, `U2_isPositivePLOn_of_refines` (both only in the corrected inverse).
No U8 chart leaf is used: the chart algebra needed (`capInvFun` involution for `L ≠ 0`, `supNorm` of a multiple,
seam identity, the two charts cover the sphere for `L > 0`) is proved in `u3h_` form.

## 3. Rule 3: `U3_isPositivePLFromPlane_inv` is false as stated

The leaf has no hypothesis on `L`.  Counterexample at `L = 0`: take `S = ↑D` for `D` the closed unit square
about `(10,10)` (a `Link.IsDisc`), `f = planeOf`; `IsHomeoOnto S D f` holds.  `chartPart 0 false S = square 0 ∩ … ⊆ {0}`
and `capChart 0 y ∈ {∞, ↑0}`, so both chart parts of `S` are empty and `IsPositivePLToPlane 0 S f` holds with the
empty triangulations.  Any `g` with `g (f z) = z` on `S` satisfies `g x = ↑x` on `D`, but the conclusion demands
`g x ∈ modelChart 0 b' '' modelDomain 0 b' ⊆ {↑0, ∞}` on a whole face — impossible.  The same construction with
`L < 0` (say `L = −100`, chart images `{∞} ∪ ↑{‖x‖_∞ ≥ 100}`) also refutes it.  The leaf is therefore FALSE for every
`L ≤ 0`; it is not edited.

**Corrected form, proved** (`u3h_isPositivePLFromPlane_inv`, line ≈2941):
```
theorem u3h_isPositivePLFromPlane_inv {L : ℝ} (hL : 0 < L) {S : Set Sphere} {D : Set Plane}
    {f : Sphere → Plane} (_hD : Link.IsDisc D) (hf : IsHomeoOnto S D f)
    (hpl : IsPositivePLToPlane L S f) :
    ∃ g : Plane → Sphere, IsPositivePLFromPlane L D g ∧ (∀ z ∈ S, g (f z) = z) ∧ ∀ x ∈ D, f (g x) = x
```
**What the assembly needs changed:** add `(hL : 0 < L)` to `U3_isPositivePLFromPlane_inv` (then its body is
`u3h_isPositivePLFromPlane_inv hL hD hf hpl`).  Its only consumer is `U10_pl_extension` (via the U10 route
`g' ∘ Fan ∘ f`), where `L` comes with `InsideModel L P`, which gives `0 < L` (`0 ≤ supNorm (P i) < L`), so the
extra hypothesis costs nothing downstream.  `Link.IsDisc D` turned out unnecessary for the corrected statement.

## 4. Method (how the engine works; ≈ 2 000 lines of `u3h_` helpers, 157 declarations)

* **Barycentric basics** (`u3h_mem_carrier_iff`, `u3h_bary_unique`): membership by three weights (via
  `convexHull_insert`/`convexHull_pair`), uniqueness of weights from `det ≠ 0`; hence vertex distinctness, "edges
  meet only in the common vertex", "a vertex in the hull of a set of vertices is one of them" (`u3h_v_mem_convexHull`),
  vertices are extreme points (so equal carriers ⇒ equal vertex sets, `u3h_range_eq_of_carrier_eq`).
* **Face on a supporting line** (`u3h_carrier_inter_line`): `T ∩ {h = r} = conv (vertices on the line)` when `h ≤ r`
  on the vertices.  **Separation**: two faces of a triangulation with distinct carriers have disjoint
  interior/other (from `inter` + `U1_frontier_triangle`) and are separated by a line via Mathlib's
  `geometric_hahn_banach_open` (`u3h_faces_separated`).
* **Gluing criterion** (`u3h_inter_of_family`): a finite family of triangles, pairwise line-separated when their
  carriers differ, in which every vertex of one triangle lying in another is a vertex of it, satisfies the
  `Triangulation.inter` clause.  Proof: intersect inside the separating line (both sides are segments spanned by the
  vertices on the line), coordinates along the line (`u3h_dir`, `u3h_mem_segment_iff_coord`) and a 4-point
  interval case analysis (`u3h_real_comb`).
* **Splitting one triangle by one line** (`u3h_SplitSpec`, `u3h_split_exists`): sign-pattern normalisation by
  cyclic rotation (27-case trichotomy, `u3h_rot`), pattern A (one vertex strictly on one side: 3 pieces) and pattern
  B (a vertex on the line: 2 pieces), each proved by explicit homogeneous barycentric weights for the cover and by the
  gluing criterion for `inter`.  The spec records the sides, which vertices are old / crossing points, and that every
  transversal crossing point is a vertex (`cross`).
* **One-line refinement of a triangulation** (`u3h_refine_one_line`): pieces are taken of a canonical triangle with
  the given carrier (`u3h_canonTri`, so faces with equal carriers get identical piece sets), glued by the criterion;
  the vertex-compatibility across faces is `u3h_compat` (`u3h_endpoints_mem` + the `cross` clause).  Then induction
  over `Fin m` (`u3h_refine_along_lines`, also exporting "every new vertex is old or on one of the lines").
* **P15** (`u3h_subset_face_of_sides`): a triangle inside `Y` on one side of every edge line of every face of a
  triangulation of `Y` lies in one face (Baire/`dense_iInter_of_isOpen` to find an interior point off all frontiers,
  then `U1_mem_carrier_iff_det`).  **Refining so faces map into faces** (`u3h_refine_map_into_dep`): pull the edge
  lines back through the face-wise affine maps (`u3h_pull`); face-dependent targets are allowed, which is what the
  chart bookkeeping leaves need.
* **Chart algebra** (`u3h_capInvFun_capInvFun` for `L ≠ 0`, `u3h_chartInv_chart`, `u3h_chart_chartInv`,
  `u3h_chartInv_zero` for the degenerate `L' = 0` case of `U3_isPositivePLToPlane_comp`).
* **Corrected inverse**: `g x := e.symm x` on `D`; both chart triangulations are refined along the lines
  `x₁ + x₂ = c` (plane chart) / `y₁ − y₂ = c / L` (cap chart) for all vertex "sums" `c` of both charts, so that the
  seam vertex sets agree (`u3h_seam_vertex`: a boundary point of a face one-sided w.r.t. a line transversal to the
  square's sides is a vertex); the image faces `T.map (f ∘ chart)` are glued by the criterion (separation via
  `u3h_interior_map` — affine maps carry interiors to interiors — and the seam relation `u3h_seam`); the inverse
  affine maps come from `u3h_exists_linear_inverse`.

Reassessment discipline: no lemma needed a change of method; iterations were compile-fix cycles (tactic-level:
`first` with term-mode `by` blocks does not backtrack — replaced by tactic alternatives; `subst`/`obtain` naming).

## 5. Notes for the skeleton / other units

* Imports added (not part of the identity check): `Mathlib.Analysis.Convex.Join`,
  `Mathlib.Analysis.LocallyConvex.Separation`, `Mathlib.Analysis.Convex.Extreme`,
  `Mathlib.Topology.Baire.CompleteMetrizable`.
* Reusable for other units: `u3h_inter_of_family` (gluing criterion), `u3h_faces_separated`,
  `u3h_triangulation_vertex` (a vertex of a face lying in another face is a vertex of it), `u3h_mem_interior_iff`
  (interior of a face = strict edge inequalities), `u3h_image_carrier`, `u3h_affine_inverse`, `u3h_interior_map`,
  `u3h_sphere_cover` (`L > 0`), `u3h_seam`, `u3h_interior_square_subset`; U8 may take `u3h_capInvFun_capInvFun`
  and `u3h_supNorm_capInvFun` (proved for `L ≠ 0` resp. `L > 0`).
* `U2_isPositivePLOn_of_refines` and `U2_interior_face_subset_interior` are used only in the corrected inverse.
