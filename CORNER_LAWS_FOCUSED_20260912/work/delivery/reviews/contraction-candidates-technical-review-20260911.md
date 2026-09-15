# Contraction candidates: technical review, 2026-09-11

Reviewer: `/root/review_contraction_candidates`, a separate agent with no authorship of these candidates, using the **same currently available model** as the authoring agent. This is a technical review of candidate algebra and evidence. It is **NOT the stronger statement-fidelity approval requested by the user**, and does not approve an original source claim or change acceptance status. No Lean kernel, build, or checker was run by this reviewer.

Reported checklist at review startup and completion: **39/192 (20.3%)**, targets 0/8; original shift-scope obstruction remains recorded. These counts are reported statuses, not a proof-verification conclusion.

## Finding

No algebraic defect found in the four declarations of `NonunaryContraction.body.lean` or the one theorem of `ContractionPropagation.body.lean`. Their definitions and induction implement the algebraic mechanism in `reference/SM/sm-2-amplitude.tex:319–355`; the unchanged-coordinate prerequisite matches lines 280–284. This finding is conditional on the checked definitions below and does not establish the entire geometric single-triple theorem at lines 229–373.

1. **Exact composition domain.** `expandNonunaryComposition` preserves `parts` definitionally, so the subtype is exactly all compositions with at least two parts. Injectivity and `mem_range_expandNonunary` use the explicit expansion/contraction inverses. `SurvivingCuts` tests every cut, including endpoints, and excludes precisely positions strictly between the critical endpoints. Under containment, `survivingCuts_iff_containing_child` identifies this range with the source's compositions having a child containing the whole critical arc. No nonzero-weight or geometric condition restricts the domain.

2. **Reindexing discards differences only.** `sum_nonunary_expansion` works over an arbitrary additive commutative monoid and explicitly requires zero summands outside that range. Its propagation caller proves this premise for the old weight times the child-product difference. `nonsurviving_child_product_unchanged` derives it from locality and the contrapositive of `survivingCuts_of_containing_child`. No claim that an individual original composition value vanishes is used.

3. **Actual inverse and explicit premises.** Propagation assumes an increasing critical triple, arbitrary arrays agreeing away from that triple, a commutative ring with invertible two, and containment of the distinguished contracted leaf. `farOnlyCoordinates` is the constructed `nearFarInverse 0 H boundaryUnitArray`; its inverse is recursive subtraction of the full nonunary sum, not a placeholder. The scalar multiplying the contracted inverse is the *actual* difference at the critical span. No propagation formula, wall law, nonzero scalar, or division by that scalar is assumed. Permitting unchanged critical entries also correctly includes zero response.

4. **Containment and unary cases.** Expansion deletes exactly the open critical arc and preserves its endpoints. `expandInterval_contains` gives the exact containment equivalence; `containing_interval_is_expanded` supplies every original containing interval, including the full span. The base case expands the distinguished one-leaf interval to the critical span and uses its inverse coordinate value one. For every other containing interval, `containing_contracted_nonleaf` proves at least two contracted leaves, so the contracted unit-array right side is zero. The uncontracted interval has at least two leaves because it contains the increasing triple. Thus no two-gon amplitude or invalid zero right side is introduced.

5. **Unique changed factor and unchanged companions.** `part_contains_unique` uses positive interval length and ordered adjacent parts; shared endpoints cannot produce two containing children. `expanded_child_product_response` removes that unique factor from both full products. All other factors agree across the two original arrays by `farOnlyCoordinates_unchanged_off_critical`, and with contracted inverse coordinates by `farOnlyCoordinates_expanded_off_leaf`. The latter is separately proved by complete composition transport and a shorter-interval induction. Its hypothesis is sufficient: an interval not containing the distinguished adjacent-position leaf lies wholly on one side. Empty companion products and zero coordinates require no additional hypotheses.

6. **Weights, termination, and final sign.** For a strictly larger interval, injectivity of expansion proves that its endpoints are not both the critical endpoints. `farWeight_unchanged_off_span` therefore equates its complete weights across the arrays. Expanded far triples are definitionally the pullbacks used in `contractedTripleArray`, preserving every gate. The recursive propagation call occurs only inside the nonunary sum. Its termination measure is the expanded interval's leaf count, and `expandComposition.part_leaves_lt` proves every called child strictly shorter. It does not recursively invoke itself at the same interval. Finally, subtracting the original inverse equations says that the coordinate difference is the negative nonunary-sum difference. Reindexing identifies that sum difference with the source scalar times the contracted nonunary sum. The contracted inverse equation makes the latter sum the negative contracted coordinate. The two negatives give the displayed positive response factor. This is the `linear_combination` step at the end of the proof.

## Scope and evidence limitations

The candidate proves the containing-interval branch with the critical difference left in its actual-coordinate form. The complementary zero branch is supplied by existing locality, not restated in this theorem. The source identification of that critical difference with the epsilon/gap expression, geometric sign stability and wall evaluation, and the final barred-transform/root-amplitude conclusions are separate obligations. The contracted array here is a pullback of `H₁`; identifying it with the geometric contracted word at the wall remains an application obligation. Those omissions are appropriate for this helper, but prohibit treating it as the complete original wall theorem.

The reviewed proof path uses explicit inverse construction, restriction, composition bijections, and the two well-founded inductions; no circular use of the single-triple conclusion was found. The scanned target and contraction dependency bodies contain no `axiom`, `sorry`, `admit`, `native_decide`, or `unsafe` token. The root logs print only `propext`, `Classical.choice`, and `Quot.sound` for the theorem dependencies (the expansion definition omits choice). This reviewer did not independently reproduce kernel elaboration or audit every transitive imported artifact.

## Receipt and hash binding

Using Python SHA-256 over current file bytes, **all 10/10 hashes** in `NonunaryContraction-prototype-result.json` and **all 13/13 hashes** in `ContractionPropagation-prototype-result.json` matched. Each target body occurs exactly once, byte-for-byte, in its corresponding prototype. Every recorded dependency body also occurs exactly once; the `CriticalContractionPositions-first` entry aliases identical bytes and does not mean the prototype contains a second copy. Logs contain the requested declarations and axiom reports. Root receipts record **session 70905, exit 0**, and **session 96039, exit 0**, respectively; both explicitly report a failed first run. These are verified receipt contents, not newly executed sessions.

Paths below are relative to the focused handoff root. The hashed receipts bind their exact prototype, log, and listed dependency files. They do not individually bind all imported canonical sources or `.olean` files; the inspected canonical-source snapshot is separately bound below.

| File | SHA-256 |
|---|---|
| `work/checks/NonunaryContraction.body.lean` | `a4d3f95360deeaa279851bd8ee00a4e155ef71ff85fe87642dac4d80afff8c7c` |
| `work/checks/ContractionPropagation.body.lean` | `82af9dbc8bb2f930b99d49e76f998479dd944b9a3ce29c914be172f0ff6dbe13` |
| `work/checks/NonunaryContraction-prototype-result.json` | `2ab65ec9779489bc0a4ae8bd7fde3cd18ff380fad9b491272224c6776ad1c062` |
| `work/checks/ContractionPropagation-prototype-result.json` | `a96166f615fb37613ef4acdb0515a7a1b3943ae11a565d1682fd3f09f7429aa2` |
| `reference/SM/sm-2-amplitude.tex` | `014068e2f6e2d86b0ff4edf48877b5967847d661eaae04d2d4c5fd9f54b7c9cf` |

Inspected contraction dependencies: `CriticalContractionPositions`, `CriticalContractionBounds`, `BoundaryTripleSupports`, `ContractedGeometricWord`, `ContractedIntervals`, `ContractedCompositions`, `OffLeafContraction`, `UniqueChangingChild`, and `ContractedChildResponse`, all under `work/checks/` with `.body.lean` suffixes and exact hashes in the receipts above. Review of these dependencies is restricted to the mechanism and premises needed here, not blanket source approval of every declaration.

Canonical sources inspected for the referenced definitions/proofs (some inspected only at the relevant declarations):

```text
604906b750e1ab198a2db3fc3cc011ab325493a91404a0b52ffe4583dd403f1a  work/lean/SM/RootBoundary.lean
e8d64c8add8ffddb3aa487ccacf8a44e991e6f65eed84270eb0dfaa62d7c7009  work/lean/SM/FiniteCompositions.lean
e55a09f154dd85ad4e4d7e0b35b5c87ccf78459a2c4344a80c7669b909e48144  work/lean/SM/CompositionSegments.lean
3d243e1d12636a02743e0f8dc37e3eecc7d46306fbd3cfca5170fd223ad6fa60  work/lean/SM/NearFar.lean
2ab97aefcf1216934b9e44ce6897c73e70d6d16487a4f82123e68d415c47176d  work/lean/SM/UnaryComposition.lean
851c9d30affbb3d38893bdc72249173f4b830d552768ba04e971e1ee848663b2  work/lean/SM/NearFarTriangular.lean
c1ad3aab34d9695ee82fa41284461d921125d0d67281c1a67d46cbb48c0f5db2  work/lean/SM/TriangularInverse.lean
d773b636e2dc37babf11ae3df6b1eb813f5bc2812ad10f5e9bb76faf7d133aa4  work/lean/SM/FarOnlyOutput.lean
acabcc232d65c15d1b3137751bdc91d16c9f5b452898e33685be67964a29639c  work/lean/SM/FarOnlyLocality.lean
3a85c4eef913ff6e5c7e26374f93a166376ff0686a35995da6d630598b9d81f0  work/lean/SM/CriticalFarOccurrence.lean
8d24a82540feb67b99bcdf636e0642cd11451f8b7718f9f22cdeee29ec22cc17  work/lean/SM/CriticalInverseDifference.lean
8c5f49e94ae0240cb9ae6e7e233ea369c1b496c330a4357af74b418f1366495b  work/lean/SM/Farout.lean
057fda75b742c22a8112736bc73f368766212d49d2df07024756673d848bcb1b  work/lean/SM/CriticalCutSplit.lean
1f95b822cd0c8ea8dd0668dd6c64143510d496955b8cbd9b302dda2c50eae458  work/lean/SM/IntervalRestriction.lean
```

Only this review report was created. No Lean body, canonical source, acceptance map, or status file was changed.
