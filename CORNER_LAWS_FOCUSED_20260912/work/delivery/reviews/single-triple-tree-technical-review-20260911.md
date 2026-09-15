# Single-triple aggregate: technical review, 2026-09-11

Reviewer: `/root/review_contraction_candidates`, a separate agent without authorship of the candidate, using the **same currently available model** as the authoring agent. This is limited independent technical/source-comparison evidence, **NOT the stronger statement-fidelity approval requested by the user**. No source claim or acceptance row is approved. No Lean kernel, build, or checker was run.

Reported startup/completion checklist: **39/192 (20.3%)**, targets 0/8; the original shift-scope obstruction remains recorded.

## Finding and source comparison

No defect found in either aggregate statement or its proof. `single_triple_tree_response_of_affine` proves both branches for every valid supplied affine representation. `single_triple_tree_response` constructs a representation from the three explicit physical point inequalities and then applies that universal theorem. The comparison target is `reference/SM/sm-2-amplitude.tex:229–373`, with the actual wall-germ/sign-change definition from `sm-1-polygons.tex:653–668`.

| Printed source clause | Candidate correspondence and technical finding |
|---|---|
| Domain, lines 230–235 | The hypotheses retain an actual continuous `WallGerm`, one exact unordered point-zero support, empty `concurrenceTriples`, a fixed root, increasing critical boundary positions, and local critical sign change. The second theorem explicitly retains all three physical point inequalities. `spanInterval`, `leftInterval`, `rightInterval`, and `fullBoundaryInterval` use the indicated endpoints. |
| `afr:wall-data`, lines 236–238 | A single integer d, proved minus one or one, is chosen before the neighborhood radius and either evaluation point. The conclusion explicitly equates the positive-minus-negative geometric half-difference with its ring cast. The sign-change lemma fixes d from the positive-side basepoint, so it is not a conveniently chosen response factor. |
| `afr:wall-epsilons`, lines 239–244 | The definitions are the signs of the printed affine-coordinate ratios. The constructed theorem supplies a nonzero direction, all three scalar inequalities, both epsilon sign alternatives, and the additional proved fact that at least one epsilon is positive. The universal theorem uses those same definitions for every valid representation. |
| `afr:wall-uv`, lines 245–252 | `wallGapU` selects E for positive epsilon and B for negative epsilon; `wallGapV` selects the reverse. Here E is exactly `boundaryUnitArray`, equal to the ordinary inverse output; B is the complete barred far-only output. The scalar inequalities exclude epsilon zero, so the definitions' default branches do not silently enlarge the intended cases. |
| `afr:wall-proper`, lines 253–259 | The proper conditional branch is exactly d times the two U factors times the actual contracted tree coefficient. `proper_span_tree_response` supplies the derived source jump and full output contraction; the aggregate substitutes the normalized jump and reassociates multiplication. It does not assume the final factorization. |
| `afr:wall-full`, lines 260–264 | The full branch is d times the sum of the U-product and V-product. `full_span_tree_response`, inspected in this review, uses the separately derived critical barred-output response, then transports all four gap values to the center. It does not reuse the proper formula at a forbidden contracted arity. |
| Evaluation convention, lines 265–267 | The radius is positive and chosen before independent negative and positive parameters. Both are constrained separately by that radius; no symmetric-time restriction appears. Gap arrays and Q use `w.center`. The previously reviewed common-neighborhood and contraction-exclusion lemmas prove equality with the relevant noncritical signs on either sufficiently close side. |

## Key checks

**Both affine quantifiers are correct.** The `_of_affine` theorem's coordinates are universally supplied arguments satisfying the printed conditions; it is not limited to the convenient coordinates later constructed. The second theorem constructs base point at the first wall point, nonzero endpoint direction, and distinct scalar coordinates using the explicit zero-determinant argument. It then invokes `_of_affine`. There is no unproved coordinate-existence hypothesis remaining in the second theorem. The source's nonzero direction and empty-concurrence premises remain in the universal theorem even though the underlying algebra proves the response without using them; unused-variable warnings do not remove these premises or introduce a gap.

**Arity three and full/proper coverage are retained.** Physical distinctness is not inferred from singleton zero support. No arity-four premise appears. At arity three the increasing critical triple spans the full boundary; the two gaps each have one formal leaf, whose E and B values are one. The full expression consequently has both contributions. The dependent conditional creates a contracted tree coefficient only under a proof of properness, which supplies contracted arity at least three. Negating properness gives exact full-span equality; no third case is lost. The first failed elaboration was about decidability of this conditional, not a missing mathematical branch.

**Q is the source polygon, not a substituted coefficient.** The construction deletes exactly the open critical arc, retains both endpoints and every exterior vertex in order, and evaluates those vertices at the center. `contractedWord_G1` proves that its distinct triples avoid the unique zero support. `contractedSize_of_proper` proves its arity, and `contractedWord_physical_root` proves equality of its actual directed closing edge with the original root edge. The coefficient at label zero in the contracted tuple therefore denotes the original physical root. G1 and arity are supplied directly to the coefficient term; root preservation is an independently proved accompanying helper fact.

**The full branch has its own source term.** The new full-span dependency applies `geometric_critical_output_response` to the two punctured arrays. That dependency separates the unary inverse jump from the direct reversed-far coefficient change and identifies the latter with the V-product. Full-span equality changes the interval to the actual full boundary. Gap exclusion and output locality replace both U and V values by center values. Thus there is neither an omitted barred contribution nor a hidden contraction to a two-gon.

**No circular or artificial response premise was found.** The aggregate depends on inverse construction and locality, the critical one-gate response, composition contraction, ordinary inverse propagation, complete barred output, affine construction, and connected-side sign normalization. None takes either aggregate wall-response conclusion as a premise. The domains have actual continuous curves, positive radii, physical points and raw compositions; they are not opaque “lawful response” predicates. Both candidate bodies contain no `axiom`, `sorry`, `admit`, `native_decide`, or `unsafe` token. The passing log reports only the standard `propext`, `Classical.choice`, and `Quot.sound` dependencies.

## Source packaging and remaining limits

No unresolved algebraic proof step was found in the two displayed branch formulas. The following distinctions still matter for final statement mapping and stronger review:

- The aggregate does not conjoin every auxiliary source assertion into its output. Q's geometry/root properties and equality of nearby versus center coefficients are provided by the accompanying helpers just identified. The nondegeneracy of nonleaf closed gaps is additionally proved by the existing `critical_closed_gaps_G1` in `RestrictedCriticalG1.body.lean`. That file is outside this aggregate prototype; its separate passing receipt was checked and its point/label restriction proof inspected here. These supporting declarations should accompany the final source mapping.
- The equations are stated in arbitrary commutative R with invertible two, while `treeCoefficient` itself is integer-valued. This preserves the source calculation, but the map should explicitly record a faithful specialization, such as rational or real coefficients, when reading it as the printed integer-amplitude equality. E/B identification with closed-gap coefficients uses `farOnlyOutput_restricted_tree` and gap G1; one-leaf gaps use the formal value one. There is no claim that casting into every possible R is injective.
- The statements begin after the source's instruction to choose the increasing critical boundary positions. They do not separately export a sorting theorem from an independently supplied unordered K or type-specific corollaries for (F), (K), (V), (E), and (C). If the final map uses those alternative input presentations, their conversion to the explicit premises must be recorded. The response formulas themselves impose no additional wall-type restriction.
- All of this remains same-model technical review. Stronger statement-fidelity approval, canonical integration, and current acceptance-checker evidence are not established by this report or by the prototype build.

## Receipt and hash binding

Python SHA-256 checks matched **all 29/29 recorded hashes** in `SingleTripleTreeResponse-prototype-result.json`. Each target/dependency body occurs exactly once, byte-for-byte, in the combined prototype. Shared dependencies match the prior proper-germ, affine, signed-jump, propagation, and output receipts. All **31 distinct canonical hashes** from the prior five technical reviews were rechecked without changes.

The root receipt records **second session 84196, exit 0**, failed first session 66657, and zero source-claim acceptance increment. The first log records failure to synthesize `Decidable` for the dependent proper/full condition and reports `sorryAx` in the failed aggregates. The passing log has no such dependency. A byte comparison confirms that removing the added local `Classical.propDecidable` attribute from the final body reproduces the first body exactly; both declaration and proof texts were retained. This is a standard classical elaboration instance, not an added theorem axiom. No failed output is treated as proof.

| File, relative to focused handoff root | SHA-256 |
|---|---|
| `work/checks/SingleTripleTreeResponse.body.lean` | `6e60aa2449dbc4eb4ddbe942ec908b52f1e28d0c81a10d0801580d511b1fa328` |
| `work/checks/SingleTripleTreeResponse.prototype.lean` | `464dbdac8b97e02e2e527eebf8845a9bb413950b928f6fca244cbc7f29f8f569` |
| `work/checks/SingleTripleTreeResponse-second-kernel.log` | `4b518b3fc368aa8133c2b44fa0c2cb2b26c3d97e9a82f555a3b58bfef8e0b85b` |
| `work/checks/SingleTripleTreeResponse-prototype-result.json` | `62507d282623027bf41689eb410b684eb107e8e6c50c6501d8bfa41cdfa9ec61` |
| `work/checks/FullSpanGermResponse.body.lean` | `36f2f2ba96fcd4ae0b33e9a9331f0c8e240c11122d09df2272ba4055c16d5c89` |
| `work/checks/SingleTripleTreeResponse-first.body.lean` | `b16f9be3f665c6c0efa85f76d5b10966a517671429c39b5237a47ba9fbaf8887` |
| `work/checks/SingleTripleTreeResponse-first.prototype.lean` | `8844d60858db088db8cd5d1f0cc1e202513d8e2d8fc5c930acb9856d1a5a7c54` |
| `work/checks/SingleTripleTreeResponse-first-kernel.log` | `11c112f7c3319089abb182f90175de6dcc06af6ea1bf208f44b6d2a2d9e1bb81` |
| `reference/SM/sm-2-amplitude.tex` | `014068e2f6e2d86b0ff4edf48877b5967847d661eaae04d2d4c5fd9f54b7c9cf` |
| `reference/SM/sm-1-polygons.tex` | `8bc30167c9cde79c3eb4b9cf52052f81f040ec91490f49517b9f1b7ad0333a00` |

Supplementary closed-gap receipt: `RestrictedCriticalG1-prototype-result.json`, SHA-256 `7f0c7790f1522bbca24708cacabb5b7ca249cb1a762f86ad8ebaa8c8da14cc56`, records session 18064, exit zero; all seven recorded hashes match. Its current body hash is `be36ad6817db31270a9ea436505688e2d2e65f00a8c839449bdcfdd268b2df60`. Newly inspected canonical source bindings are `d070e70dfbb61e036641f0d5fac4adae83fd1cadfe22f3ce2ffd8c8e1de9ab06` for `work/lean/SM/TreeCoefficient.lean` and `a2d45634865602373437222b5e190794f31375624fa3021745ae6a0043551e8e` for `work/lean/SM/RestrictedWordRoot.lean`.

Prior reports in `work/reviews/` supplying the remaining exact source bindings and bounded dependency analyses:

```text
daff29fbdc79ee5e132a54d58255fc0d3fe04377cccd99e5045aecd901edec24  contraction-candidates-technical-review-20260911.md
d1f569f0dadbd0df2d86bc2439a1020cd6ae0b20f6ad7f7e93b154d73ecab47d  contraction-output-technical-review-20260911.md
52599dab0db79f7de84a6dd96af6526532fa24f88b944c3690da820acd2ba125  proper-germ-technical-review-20260911.md
54d13066acfea1dea559a16f945f76ee9d8490a8455755dbec3264cc87d6b9a4  critical-affine-data-technical-review-20260911.md
b36e2c5f869a327ce6af11d4b5e7e70ea891154b74b489d3f5f5037ced8cd099  signed-critical-jump-technical-review-20260911.md
```

Hashes bind the inspected bytes and receipts, not every imported compiled artifact. Only this report was created; no Lean body, canonical source, map, or status file was edited.
