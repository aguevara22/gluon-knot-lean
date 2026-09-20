# Row 57 lem:gauss-two-discs — unit U5 report (W2_U5)

Written 2026-09-19 (≈ 13:40 UTC / 9:40am ET) by the U5 prover.  File: `work/drafts/twodiscs/W2_U5.lean`
(15 677 lines = `W1_Assembled.lean` + 112 `u5h_`-prefixed declarations in two `section`s placed immediately
before the U5 leaf they serve + the body of `U5_exists_ear_homeo`).  Scratch (private):
`/workspace/scratch/claude-0/-workspace-repos-lean/d4284a43-f199-4eff-82e0-1573731546fc/scratchpad/w2u5/`
(pieces `A.lean … L.lean`, prefix olean `pfx/W2U5Prefix.olean` = `W1_Assembled.lean` up to the U5 header,
`assemble.py`, `full_compile.log`, `W2_U5_axioms.lean` + `axioms.log`).

## 1. Checks

| check | result |
|---|---|
| `cd work/lean && lake env lean ../drafts/twodiscs/W2_U5.lean` | **0 errors** (54 s wall); 29 `declaration uses sorry` warnings (= the 30 open wave-2 leaves minus the closed `U5_exists_ear_homeo`; the 29 are `U5_pushforward_edges` and the U6–U9 leaves); other warnings: the linter/deprecation warnings already present in `W1_Assembled.lean` plus `unused variable` on the frozen header of `U5_exists_ear_homeo` (`hn`, `hP`, `hedge` are not needed — the statement is frozen, so they stay) |
| `python3 check_57_identity.py W2_U5.lean` | `IDENTITY OK` (DEFS, BUNDLE, THM byte-identical) |
| `grep -c sorry` | W1_Assembled 33 → W2_U5 **32** (one leaf `sorry` removed; the remaining 32 = 29 open leaves + 3 docstring mentions) |
| `#print axioms` (scratch copy `W2_U5_axioms.lean`) | `U5_exists_ear_homeo`, `u5h_leaf`, `u5h_core`, `u5h_earHomeo`, `u5h_pushforward_edges_false`, `u5h_pushforward_edges`: **`[propext, Classical.choice, Quot.sound]`** — no `sorryAx`, no literature axiom, no `native_decide` (the wave-1 leaves consumed are all closed in `W1_Assembled.lean`); the open leaf `U5_pushforward_edges` prints `sorryAx` as expected |
| leaf statements | unchanged (docstrings, names, statements frozen; `U5_pushforward_edges` keeps its `sorry`, rule 3) |

## 2. Leaves

| leaf | status |
|---|---|
| `U5_exists_ear_homeo` (line 12294, corrected form with `hcut`) | **closed**: body `exact u5h_leaf P j hP' hturn hear U' K' hU' hcut hface hL hU'L` (`hn`, `hP`, `hedge` unused) |
| `U5_pushforward_edges` (line 12561) | **open — FALSE as stated** (rule 3).  Kernel-checked counterexample `u5h_pushforward_edges_false : ¬ u5h_pushforward_edges_stmt` (line 12343; `u5h_pushforward_edges_stmt` is the leaf's statement as a `Prop`, line 12318).  Corrected form **proved**: `u5h_pushforward_edges` (line 12453), see §3. |

Consumer check: `W2_U6.lean` (already written) consumes only `U5_exists_ear_homeo` (line 10990 there, with the
frozen statement, `U' := u4h_regionOf (deleteVertex P j)`) and, per `W2_U6_REPORT.md`, not
`U5_pushforward_edges`.  So the false leaf has no consumer; nothing downstream changes.

## 3. Rule 3: `U5_pushforward_edges` is false as stated

**Counterexample** (`u5h_pushforward_edges_false`, kernel-checked, no `sorry`): `n = 3`, `P : LabelledTuple 4 =
(A, A, B, C)` with `A = (0,0)`, `B = (1,0)`, `C = (0,1)`, `j = 1` (a repeated vertex, so `earHull P 1 =
segment A B` and `deleteVertex P 1 = (B, C, A)`), `U' = conv {B, C, A}` with the one-face triangulation
`u4h_singleTri`, `h = Homeomorph.refl`.  All hypotheses hold (`h` is positive PL, `h '' U' = U' ∪ earHull P 1`
because the ear is the edge `AB ⊆ U'`, `h '' polygonImage (deleteVertex P 1) = polygonImage P` because the extra
edge of `P` is the point `{A}`, the three edges of the cut triangle are the three face edges), but the
conclusion demands a face edge `T.edgeSeg k = edgeSegment P 0 = segment A A = {A}`, impossible since the two
endpoints of a face edge are distinct (`u2h_v_ne`).

**Why the intended proof cannot work even for embedded `P`.**  The hypotheses `hedge'`/`huniq'` make *every*
edge of the cut polygon, including the diagonal `[P (j-1), P (j+1)]`, a face edge of `Kin`; with `h` affine on
each face, `h` is then affine on the diagonal and its image is one straight segment inside `polygonImage P`,
while the ear needs the bent path `[P (j-1), P j] ∪ [P j, P (j+1)]`.  The `Kin` produced by
`U5_exists_ear_homeo` therefore does **not** satisfy `hedge'` at `i = -1` (the diagonal is split at its midpoint
`m`, `h m = P j`), and for a hypothetical `Kin` satisfying the leaf's hypotheses the pushforward would have
`n` straight boundary segments covering the `n + 1` edges of `P` — the required triangulation of `U' ∪ ear` would
have to be re-built from scratch (the U4 machinery), which the statement's hypotheses (no `Embedded P`, no
control of `U'`) do not support.

**Corrected form, proved** (`u5h_pushforward_edges`, line 12453): what differs from the leaf is exactly
* the diagonal is **not** required to be a face edge of `Kin`; instead a point `m` with `h m = P j` splits it and
  the two halves `segment (P (j-1)) m`, `segment m (P (j+1))` are face edges of exactly one face
  (`hedge1`, `hedge2`, `huniq1`, `huniq2`), while `hedge'`/`huniq'` are required only for `i ≠ -1`;
* `h` fixes every non-diagonal edge of the cut polygon pointwise and fixes `P (j-1)`, `P (j+1)`
  (`hfix`, `hfa`, `hfc`) — the shape produced by `U5_exists_ear_homeo` (its clauses `h '' segment a c =
  segment a b ∪ segment b c` and "frontier points off the open diagonal are fixed", `u5h_core`);
* the clause `h '' polygonImage (deleteVertex P j) = polygonImage P` is dropped (it follows).

The conclusion is the leaf's, realised by the pushforward `u2h_pushforward Kin h hh` (faces `T.map h _`): the
image face edges are `segment (h (T.v k)) (h (T.v (k+1)))`, which are the fixed edges resp. `[P (j-1), P j]`,
`[P j, P (j+1)]`; uniqueness pulls back along `h.symm` (`u5h_image_segment_of_affine`).

## 4. Method (what was actually built) — `U5_exists_ear_homeo`

Notation: `a = P (j-1)`, `b = P j`, `c = P (j+1)`, `P' = deleteVertex P j` (`P' (-1) = a`, `P' 0 = c`),
`T = earHull P j = conv {a, b, c}`, `D = det (b - a) (c - a) ≠ 0`, `m = u5h_mid a c` the midpoint of the
diagonal, `u5h_apex a b c τ = m + τ • (b - m)` (so `apex 1 = b`).  The route of PLAN_FINAL §3.1 was followed
with three simplifications:

1. **Hub at the midpoint, no `p = [o, b'] ∩ diagonal`.**  `o := apex (-ε)` (behind the diagonal, inside the
   face `T'` at the diagonal for small `ε`, Part O), `b' := apex τ` (beyond `b`, `τ > 1` close to `1`, Part W).
   Then `o, m, b, b'` are collinear and the quadrilateral `Q = (a, b', c, o)` is convex with both diagonals
   through `m`; `h` moves the hub `m` to `b`.
2. **Explicit hat-function formula for `h`** (`u5h_hmap v p q x = x + φ_p x • (q - p)`,
   `φ_p = max 0 (min_i ℓ_i)` with `ℓ_i` the edge functionals of `Q` normalised to `1` at the hub `p`).  On each
   fan triangle `conv {p, v i, v (i+1)}` the hat function is the barycentric weight of the hub
   (`u5h_phi_fan`, from convexity of `Q`: `ℓ_j ≥ 0` at all vertices), so `h` is affine there with
   `h (p + α (v i - p) + β (v (i+1) - p)) = q + α (v i - q) + β (v (i+1) - q)` (`u5h_hmap_fan`); outside `Q`
   some `ℓ_i ≤ 0` and `h = id`.  Continuity is free; the inverse is the same map with the hubs exchanged
   (`u5h_hmap_inv`, needing the cover lemma `u5h_cover`: for a hub on a diagonal the four fan triangles cover
   `{∀ i, ℓ_i ≥ 0}` by a four-step sign chain).  Hence `Plane ≃ₜ Plane` directly (`u5h_earHomeo`), without
   `U2_isHomeoOnto_of_isPositivePLOn`.  The framework (`u5h_IsConvexQuad`, `u5h_IsHub`, `u5h_OnDiag`,
   `Fin 4`-indexed) is generic; the concrete quadrilateral `u5h_quadV a b c ε τ = ![a, b', c, o]` is checked by
   16 + 4 + 4 determinant identities, each a positive multiple of `D` (`u5h_quadV_conv`, `_hub_mid`, `_hub_b`).
3. **`Kh` and `Kin` by one lemma** (`u5h_refine_pl`): `U3_refine_along_lines` with the 6 lines (4 edges of `Q`,
   2 diagonals through `m`) refines *any* triangulation into one on which `h` is positive PL: a face on the
   outer side of an edge line is fixed pointwise; otherwise its diagonal sign pattern puts it into one fan
   triangle, where `U1_isPositiveAffineOn_mono` applies.  Applied to `U2_triangulation_square` (→ `Kh`) and to
   `K'` (→ `Kin`, refining `K'`).  `U2_refine_fan` / `U2_refine_edge_split` and the hypothesis `hedge` were not
   needed.

**Part W** (`u5h_wedge_main`): for `τ → 1⁺`, `conv {a, apex τ, c} ∩ U' = segment a c`.  Per edge of `P'`
(`u5h_edge_wedge`, `Filter.eventually_all` over `ZMod n`): the diagonal trivially; the two adjacent edges by
the cone lemma `u5h_wedge_adj` (an edge `[d, a]` meeting the ear only at `a` has direction outside the closed
cone at `a`, so it misses the enlarged ear near `a` — barycentric coordinates in the basis `b - a, c - a`,
`u5h_basis`/`u5h_coords_unique`); remote edges by positive distance (`u5h_wedge_far`, `Disjoint.exists_cthickenings`).
Then a point `x` of the enlarged ear in `U'` off the diagonal is joined to `b ∉ U'` by a segment in the open
half-plane of `b` (`u5h_convex_side`), which meets `frontier U' = polygonImage P'` (`u5h_segment_meets_frontier`,
via `IsPreconnected.subset_of_closure_inter_subset`) in a point excluded by the edge lemmas.

**Part O** (`u5h_exists_o`): the face `T'` with edge `segment a c` (from `hface`) has its third vertex on the side
opposite to `b` — otherwise the two triangles overlap off the diagonal (`u5h_same_side_overlap`), contradicting
`hcut` — and `apex (-ε) ∈ interior T'` for small `ε` (`u2h_mem_interior_of_det_pos`).  Orientation: the core
`u5h_core` assumes `0 < D`; the leaf body `u5h_leaf` applies it to `(a, b, c)` or to `(c, b, a)` and converts
(`u5h_hull3_perm_*`, `segment_symm`, `openSegment_symm`).

**Polygon clauses** (`u5h_image_polygonImage`, `u5h_assemble`): `polygonImage P' = A ∪ segment a c` with
`A = {x | ∃ k ≠ j-1, j, x ∈ edgeSegment P k}` (`u4h_mem_polygonImage_deleteVertex`); `h` fixes `A` pointwise
(frontier points off the open diagonal, `u5h_not_mem_openSegment` from `Embedded P'`), `h '' segment a c =
segment a b ∪ segment b c`; `frontier (U' ∪ T) = h '' frontier U'` by `Homeomorph.image_frontier`.

### Method audits (reassessment discipline)
No lemma needed a second method-level attempt; iterations were compile-fix cycles (`field_simp` needing the
denominator in the hypothesis' syntactic form — replaced by an explicit Cramer identity `u5h_basis`; `subst`
eliminating the wrong variable; `rw` on `Fin 4` index arithmetic `3 + 1` — replaced by `show`/defeq).  One
design decision was taken before coding: the leaf `U5_pushforward_edges` was analysed first (§3) and found
false; the counterexample and corrected form were written after the critical leaf, not instead of it.

## 5. Black boxes consumed (all closed in `W1_Assembled.lean`, hence no `sorryAx`)

Leaves: `U1_triangle_convex`, `U1_isPositiveAffineOn_mono`, `U2_triangulation_square`,
`U2_isCompact_of_triangulation`, `U3_refine_along_lines`, `U4_polygonImage_subset_interior_square`.
Helpers: `u1h_vertex_mem_carrier`; `u2h_carrier_subset`, `u2h_pos_cyc`, `u2h_v_ne`, `u2h_mem_interior_of_det_pos`,
`u2h_pushforward`, `u2h_map_carrier`, `u2h_image_convexHull_of_affineOn`; `u3h_det_eq_planeDot`, `u3h_dir`,
`u3h_interior_square_subset`; `u4h_mem_hull3_iff`, `u4h_mem_hull3_iff_det`, `u4h_hull3_rot`,
`u4h_segment_subset_hull3`, `u4h_mkTri` (+ `_carrier`, `_v0/1/2`), `u4h_det_sub_right`, `u4h_det_swap'`,
`u4h_det_self`, `u4h_det_rot2`, `u4h_det_segment_zero`, `u4h_segment_endpoints`, `u4h_isCompact_segment`,
`u4h_supNorm_eq_norm`, `u4h_mem_ball_of_supNorm_lt`, `u4h_edgeSegment_eq_segment`, `u4h_edgeSegment_prev`,
`u4h_edgeSegment_subset_polygonImage`, `u4h_edgeSegment_deleteVertex`, `u4h_mem_polygonImage_deleteVertex`,
`u4h_singleTri` (counterexample).  Accepted library: `Embedded` (fields), `deleteVertex_zero/last`,
`deletionIndex_exhaust/last`, `edge`, `adjacent`/`remote`.  No new interface from another unit was needed
(no `u5h_` Prop with `sorry`).

## 6. Notes / pitfalls for the assembler and U6–U9

* Two new `section`s (`U5_block`, `U5_block2`) with `open Filter` inside; a tactic macro `u5h_hull_perm`
  (`congr 1; ext; simp; tauto` for permuted three-point hulls) is defined in `U5_block`.  No new imports.
* `u5h_apex`, `u5h_mid`, `u5h_earHomeo`, `u5h_quadV` are `noncomputable def`s; everything else is a theorem.
* Frozen-header `unused variable` warnings on `U5_exists_ear_homeo` (`hn`, `hP`, `hedge`) are expected.
* U6's call `U5_exists_ear_homeo (n := m + 3) … hL (hsq L hL')` matches the frozen statement; no change.
* `U5_pushforward_edges` stays `sorry` (false); if the wave-2 assembler wants a sorry-free file it can delete the
  leaf (no consumer) or replace its statement by `u5h_pushforward_edges`.
