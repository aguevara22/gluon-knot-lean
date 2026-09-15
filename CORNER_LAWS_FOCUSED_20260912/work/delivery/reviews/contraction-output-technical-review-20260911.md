# Contraction output: technical review, 2026-09-11

Reviewer: `/root/review_contraction_candidates`, a separate agent without authorship of the candidate, using the **same currently available model** as the authoring agent. This is independent technical evidence only. It is **NOT the stronger statement-fidelity approval requested by the user**; stronger review and original source acceptance remain pending. No Lean kernel, build, or checker was run by this reviewer.

Reported startup/completion checklist: **39/192 (20.3%)**, targets 0/8; the original shift-scope obstruction remains recorded. No acceptance increment is justified by this report.

## Finding

No algebraic defect found in the seven theorems in `work/checks/ContractionOutput.body.lean`. The containing-coordinate wrapper matches the containing branch at source lines 324–331. The complete-transform response implements the proper-output argument at `reference/SM/sm-2-amplitude.tex:357–365`, using the propagation and composition mechanism at lines 319–355.

- **Complete composition sums, lines 8–38.** `expandComposition_injective` and `mem_range_expandComposition` use the explicit raw-cut equivalence and its inverses. `sum_composition_expansion` sums over `IntervalComposition`, without the earlier nonunary subtype. Its image is exactly all surviving cut lists; its explicit zero premise discards only responses outside that image. The unary composition has two retained endpoints and expands to the unary composition, whose sole child is the whole interval and whose coefficient is the empty product, one. Original zero-weight terms are not filtered out.

- **Every original containing interval, lines 51–62.** `farOnlyCoordinates_response_containing` starts with an arbitrary original interval and only the two endpoint containment inequalities. Those inequalities provide the survival proofs needed by `contractInterval`. `expand_contractInterval` returns the exact original interval, and `expandInterval_contains` transports precisely the same containment condition. Thus this is not restricted to a chosen subset of original intervals. It includes the critical span itself; the noncontaining zero branch remains the separate locality theorem.

- **Independent inverse and coefficient arrays, lines 67–117.** `H₁,H₂` determine the actual inverse coordinates; `K₁,K₂` independently determine the outer far weights. Each pair need only agree away from the critical triple. The scalar is the actual critical-coordinate difference, not an assumed response. Proper containment proves that the parent is not the critical span, so `farWeight_unchanged_off_span` equates the outer weights even when the critical entries of `K₁,K₂` differ. Subtracting the two full sums then yields the common old weight times the child-product difference. Nonsurviving products agree by locality, which supplies the reindexing zero premise. Expanded gates are exactly the pullback gates. The established product-response lemma supplies the remaining factorization without division, nonzero assumptions, or a product of two changing factors.

- **Unary handling and absence of circularity, lines 108–110.** In a unary composition the containing child equals the parent. Here the call is to the *already proved* `farOnlyCoordinates_contraction_propagation`, not recursively to the output theorem being proved. It is therefore valid for that child. The earlier inverse-propagation proof itself recurses only through nonunary proper children, as audited in the prior report. No extra base-case assumption or missing unary correction appears in this output argument.

- **Barred reversal, lines 121–130.** `farOnlyOutput_contraction_response` substitutes the negatives of `H₁,H₂` only for `K₁,K₂`. The inverse coordinates continue to use the unnegated arrays. Pointwise pullback commutes definitionally with negation, so the contracted outer transform is exactly the barred transform of the contracted inverse. This gives the source's same critical response scalar with no additional minus sign. The proof obtains the coefficient-equality premise by applying negation to the given off-critical equality.

- **Exact full-boundary specialization, lines 134–156.** `farOnlyOutput_full_contraction` assumes precisely original arity at least three and a critical span different from the original full boundary. `contractedSize_of_proper` derives contracted arity at least three: the proved size-two characterization is exactly the excluded full-span case. `expandInterval_full` preserves both full-boundary endpoints. Original containment follows from their actual bounds, and equality of the contracted full interval with the distinguished leaf would contradict properness. Thus no convenient shorter interval replaces the full boundary, and no two-position amplitude is used.

## Limits

These are algebraic helpers over the source's commutative-ring/invertible-two domain. They do not yet identify the critical inverse difference with the epsilon/gap expression, derive the off-critical hypotheses from an actual wall germ, identify the pulled-back arrays with geometric wall data, or identify the final output with the polygon coefficient at its physical root. The proper-germ assembly being tested by root is outside this review. The exceptional full-span barred response at source lines 368–372 is also outside this candidate, correctly excluded by properness rather than silently treated by the proper-output formula.

No `axiom`, `sorry`, `admit`, `native_decide`, or `unsafe` token occurs in the target body. The root log lists all seven theorem signatures and only `propext`, `Classical.choice`, and `Quot.sound` as axiom dependencies. This is inspection of supplied root evidence, not independent kernel reproduction or a complete audit of transitive compiled artifacts.

## Hash and receipt binding

Python SHA-256 checks matched **all 14/14 recorded file hashes** in `ContractionOutput-prototype-result.json`. The target and every recorded dependency body occur exactly once, byte-for-byte, in the prototype. The receipt records **root session 16114, exit 0, first run passed**, and zero source-claim acceptance increment. The log agrees on the seven printed declarations and their axiom lists.

| File, relative to focused handoff root | SHA-256 |
|---|---|
| `work/checks/ContractionOutput.body.lean` | `0825a335eecee26967be082037a848c933cf6595a0dd4c5d3047162555b6b4ab` |
| `work/checks/ContractionOutput.prototype.lean` | `6b8e9d47cc66ede3926d94400a6920382c605a65ec59baad7c2a7ef61aaa9a66` |
| `work/checks/ContractionOutput-first-kernel.log` | `55682c649b71c41c8c39578b0a5153647524df62802e37c008464723626b36c3` |
| `work/checks/ContractionOutput-prototype-result.json` | `45421c9733362067d5e7a393af96e8f6410d4e8d06d0624b6da8b3a41bc0da85` |
| `reference/SM/sm-2-amplitude.tex` | `014068e2f6e2d86b0ff4edf48877b5967847d661eaae04d2d4c5fd9f54b7c9cf` |
| `work/reviews/contraction-candidates-technical-review-20260911.md` | `daff29fbdc79ee5e132a54d58255fc0d3fe04377cccd99e5045aecd901edec24` |

The receipt binds the exact ten earlier contraction dependency bodies plus `ContractionPropagation.body.lean`. Their shared hashes match the earlier propagation receipt. The prior technical review above records the dependency reasoning and fourteen canonical-source hashes; **all fourteen canonical hashes were rechecked and still match**. `CriticalContractionBounds.body.lean` was also reread for the size-two/full-span equivalence and proper arity proof. These source bindings do not independently bind or reproduce imported `.olean` files.

Only this report was created. No Lean body, canonical source, map, or status file was edited.
