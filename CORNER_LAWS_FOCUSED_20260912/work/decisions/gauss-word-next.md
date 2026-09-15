# Completed Gauss definition; remaining downstream work

Full def:gauss is implemented as SM.gauss_definition and independently accepted
on 2026-09-10. Review: reviews/def-gauss.json. Initial full audit:
checks/checkpoint-013-output.json, 454 declarations, only standard Lean axioms.
The final metadata refresh is checkpoint 014. This is an original DEFINE row;
it does not increment the 132 original PROVE obligations.

Implementation: Traversal, GaussVisits, GaussWord, TraversalRelabel, VisitRelabel,
SortedCut, GaussRelabel and GaussDefinition. The word is sorted once by actual
visit coordinates; a general sorted-list cut argument proves relabelled words
are rotations of mapped originals. It does not define the relabelled word by
rotation. Traversal order preservation covers arbitrary half-open edge points.

def:interlace and def:visible are now independently accepted. Their completion
records are in decisions/interlacement-next.md and decisions/visible-signature-next.md.
The next executable branch is decisions/regular-rotation-next.md. The text below is the historical plan;
its UNPROVED designation records the status when written.

## Historical construction plan

UNPROVED PLAN. The retained def:gauss, def:interlace and def:visible remain
pending. Source: reference/SM/sm-1-polygons.tex lines 237–265. Read the entire
definitions and their surrounding convention; do not count helper lemmas as
these full source rows. These objects are needed for the corner state sum.

## Available concrete ingredients

Crossings.lean defines actual unordered two-edge crossings, their unique plane
points, affine parameters, strict interior bounds, and finiteness.
`crossing_card_two` proves each support has exactly two edges.
`generic_crossingPoint_injective` proves different crossings have different
points under the original n>=3 and Generic premises.
`crossingParameter_spec` gives the affine evaluation equation.

CrossingEquiv.lean supplies the true cyclic-relabelling bijection, with point,
parameter and sign compatibility. ChamberPaths.lean proves the actual crossing
set and all edge-parameter comparisons remain constant at any two path times.
WeakOpen.lean is separately accepted support for later weak-locus arguments;
its stronger-domain extension must not silently be assumed for Gauss data.

## Concrete construction to implement

1. Represent a traversal point by `ZMod n × Set.Ico (0 : Real) 1`, with actual
   plane evaluation `edgePoint P i t`. This is exactly the printed half-open
   edge-parameter set, including vertices and excluding duplicate right ends.
   Use scalar coordinate `i.val + t` to choose a cut in the circle. Under
   n>=3 this enumerates all labels, and intervals for distinct labels do not
   overlap. Prove injectivity using their half-open bounds and val injectivity.
   The linear order after a cut is not a replacement for cyclic order: expose
   the ternary cyclic relation and prove the equivalence to the printed order.

2. Define an actual visit as `Sigma c : Crossing P, {i // i in c.val}`. Prove
   its finite cardinality is twice the number of crossings, using the two-edge
   support theorem. Map each visit to its actual `(i, crossingParameter ...)`.
   Prove this map injective: equal edge and parameter give equal affine plane
   points, hence equal crossings; the remaining membership proofs are irrelevant.

3. Sort all visits by their traversal coordinate and form a cyclic list modulo
   `List.IsRotated.setoid`. Prove no visits are missing or repeated, every
   crossing has precisely two visits, the length is 2|X(P)|, and the sorted
   order is precisely the traversal order. Empty crossing sets must be allowed.
   Changing a cut or cyclically relabelling the polygon must produce the same
   cyclic sequence after the existing crossing relabelling bijection. Prove
   this compatibility; do not supply an arbitrary Gauss list as input.

4. Interlacement uses exactly one y-visit in the open cyclic interval between
   x's two visits, for distinct crossings. Prove independence of the choices
   of first visits and symmetry before creating the simple graph. Define
   independent supports, N(S), and U(S) exactly as in the source, including
   the empty support. These are not additional arbitrary graph parameters.

5. The visible signature is the actual turn tuple, crossing set and Gauss
   cyclic word. Transport equality through the accepted chamber path theorem
   and the sorted/cyclic representation equivalences. Its chamber constancy
   is an assertion in the definition and needs proof before accepting the row.

## Pinned Mathlib entry points inspected

- `Mathlib/Order/Circular.lean`: ternary `btw`/`sbtw`, circularizing a linear
  order (`LE.toBtw`, `LT.toSBtw`). They are definitions rather than global
  instances because of a known instance diamond. Use explicit/local instances.
- `Mathlib/Data/Finset/Sort.lean`: `Finset.sort`, `sort_nodup`, `mem_sort`,
  `length_sort`, `sort_perm_toList`, `sortedLT_sort`.
- `Mathlib/Data/List/Rotate.lean`: `List.IsRotated.setoid`, `isRotated_append`,
  rotation/permutation lemmas. A rotation quotient alone does not prove cyclic
  relabelling compatibility for independently constructed sorted lists.
- `Mathlib/Data/Fintype/Card.lean`: `Fintype.card_coe`, subtype-cardinality
  lemmas. Use sigma-cardinality APIs for the visit count.

Only work/ may change. Preserve all eight main roots and all 132 original
proof obligations; the final wall/soft theorem and R discharge remain pending.
