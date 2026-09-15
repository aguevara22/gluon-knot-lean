# Unordered support and integer gap candidates — technical review

Review date: 2026-09-11. Reviewer: another agent of the same currently available model. This is independent technical/source-comparison evidence, **not the stronger-model statement-fidelity approval requested by the user**, and not source-claim acceptance. Progress remains 39/192 accepted (20.3%), targets 0/8.

## Findings

No mathematical defect was found in these eighteen declarations within the inspected dependencies and stated scope.

1. **Unordered support and the source domain.** `boundaryIndex_surjective` explicitly inverts the root reading using the label `k - g - 1`. `exists_positionSet` covers all six strict orders of three distinct positions. `existsUnique_vertexSet` transports an arbitrary three-element label support through that reading and proves uniqueness using the existing support-injectivity theorem. This applies at every root; no adjacency, named wall type, preferred permutation, or hypothesis `4 ≤ n` is introduced.
2. **Physical distinctness is preserved as a hypothesis.** `boundary_points_distinct_of_support` uses pairwise distinct *points* on the support, plus injectivity of the label reading, to obtain the three ordered point inequalities. It does not derive physical separation from cardinality or unique zero support. Consequently the source's physically distinct critical triple remains explicit when `n = 3`. The nonempty three-element support supplies the necessary label count implicitly.
3. **The sign-change input is orientation independent.** Cyclic permutations preserve `chi`; an odd swap negates its real value. The existing `signChanges_neg` unfolds the exact local paired-product predicate and uses `neg_mul_neg`. `three_support_predicate` covers the six permutations and rules out repeated labels by cardinality three. `single_triple_boundary_data` therefore transports any enumeration of the unordered support to the actual reversed boundary order used by the geometric array. Its conclusion is existence and uniqueness of the sorted triple with physical separation and sign change. It is an input-conversion theorem, not the response theorem; omission of the unrelated `Z_c = ∅` premise here adds no restriction to the eventual application.
4. **Noncritical closed gaps have actual G1.** The two interval-exclusion theorems use the strict middle inequalities. The dependency `restrictedWord_G1_off_critical` proves G1 for the actual closed endpoint tuple: if a distinct-triple determinant vanished, the unique zero support would force both extreme critical positions into the interval, contradicting its exclusion hypothesis. `critical_closed_gaps_G1` applies this to the two gaps. These are derived geometric facts, not supplied replacement G1 assumptions.
5. **E/B/U/V match the printed meanings.** `criticalIntervalIntegerOutput` is the integer `1` on a formal leaf; otherwise it is the actual integer `treeCoefficient` of that closed endpoint tuple at local root `0`, with at least three vertices proved from positive interval length and nonleafness. The restricted-word root correspondence identifies this root with the closing edge. `boundaryUnitArray` gives integer E, namely 1 on leaves and 0 otherwise. Integer U chooses E for epsilon +1 and B otherwise; integer V exchanges the choices. On the source's proved ±1 domain these are precisely `afr:wall-uv`. The definitions also permit epsilon zero with an arbitrary total default matching `wallGapU/V`; this is not an assertion that a source epsilon can be zero. The leaf theorem gives B/U/V = 1 without treating a leaf as a polygon.
6. **Integrality belongs to outputs.** The four cast theorems identify E/B/U/V with their arbitrary-ring counterparts. For nonleaf B the proof invokes `farOnlyOutput_restricted_tree` with the derived G1; for leaves it invokes the formal leaf output theorem. Definitions of the integer values are independent of the coefficient ring. There is no inverse over the integers and no asserted integrality of the inverse coordinates `c`. These results provide the intended ingredients for an integer amplitude equality by faithful specialization to the rationals; the subsequent aggregate integer theorem is outside this review.

The comparison used `lem:farout` (source lines 146–169), the hypotheses and E/B/U/V conventions of `thm:single-triple` (229–282), and its gap-sum argument (283–318). Existing `BoundaryTripleSupports`, `RestrictedCriticalG1`, `WallGapValues`, `UnorderedWallTriples`, `SinglePointTriple`, `NearFar`, `FarOnlyOutput`, `RestrictedWordRoot`, and `TreeCoefficient` were inspected for the relevant dependencies. No circular response assumption was found.

## Receipt and hash evidence

All **4/4** hashes in the unordered receipt and **6/6** in the integer-gap receipt match the current files. Every listed body occurs verbatim exactly once in its corresponding prototype. The passing logs contain the eight and ten declarations respectively, and list only `propext`, `Classical.choice`, and `Quot.sound` (or subsets). They contain no `sorryAx`, errors, `native_decide`, or `Lean.ofReduceBool`. I did not run a Lean kernel, build, or other proof checker.

The unordered receipt records second session **94314**, exit 0. The preserved first session **4424** failed from recursive simplification in the sign-swap proof and its log contains downstream `sorryAx`; it is not passing evidence. Comparison with the preserved first body shows only replacement of that proof step by an explicit function equality and negation rewrite; the eight statements are unchanged. The integer-gap receipt records first session **69894**, exit 0.

SHA-256 bindings (paths relative to the focused work root):

| File | SHA-256 |
|---|---|
| `work/checks/UnorderedCriticalTriple.body.lean` | `985956064e7fa879661ee9a144753639f56a73cf48741d1e8e503cf5a201c110` |
| `work/checks/UnorderedCriticalTriple.prototype.lean` | `f26153ac6ef62a55523d12d7fde2628293d1ea415dba9aa7eaf9f790d1a3b387` |
| `work/checks/UnorderedCriticalTriple-second-kernel.log` | `a4df74ba47488bc4bdecf6ac98763c9bd11237e54e828f44129e30a89168781c` |
| `work/checks/UnorderedCriticalTriple-prototype-result.json` | `84155db0c68e0d9450483886e017c4e6aee6b3468bdd2794a81e46c0b862a768` |
| `work/checks/IntegerCriticalGaps.body.lean` | `0ad1c8c46a927d04c736b49f06a092028463264675fd2a2a0d85420f638cba05` |
| `work/checks/IntegerCriticalGaps.prototype.lean` | `34d22f189453595778d25413505f1f28cdefc4cfe40274c5ffc0dbbf6ec09ea3` |
| `work/checks/IntegerCriticalGaps-first-kernel.log` | `f5867cd64f121a28bd3c213474901e6cb4f2123876d385f2f0817d08b0f14050` |
| `work/checks/IntegerCriticalGaps-prototype-result.json` | `c53ed7193788ecf471b0a515d39db29cc29ebfe60734f9cdd1b5ff759f51c37c` |
| `work/checks/BoundaryTripleSupports.body.lean` | `60199670494951bea511f187f7f894fd63fd4d074237e5b0442602e2c4f02e42` |
| `work/checks/RestrictedCriticalG1.body.lean` | `be36ad6817db31270a9ea436505688e2d2e65f00a8c839449bdcfdd268b2df60` |
| `work/checks/WallGapValues.body.lean` | `4c12a44985c7c3ffb2fa820e7836689fac116f8776d9346e1f3a6df2d3d38841` |
| `work/lean/SM/UnorderedWallTriples.lean` | `99cb9bfe32248b00e9ab5890e68a8ff5865b8038958d04b607d7b64b623041e1` |
| `reference/SM/sm-2-amplitude.tex` | `014068e2f6e2d86b0ff4edf48877b5967847d661eaae04d2d4c5fd9f54b7c9cf` |

Hashes and recorded successful checks bind this review to particular artifacts; they do not establish stronger statement fidelity or approval of the original claims. No frozen body, canonical file, acceptance map, or status was edited.
