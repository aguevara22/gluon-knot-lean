# Single-triple response: checked candidate, fidelity approval pending

The assembled candidate now passes Lean for both the proper-span and full-span
branches of the single-triple tree response. This is an intermediate result
toward the corner state sum's wall laws and soft theorem. It does not establish
the final corner theorem, the R assembly, or the soft theorem.

The source is `reference/SM/sm-2-amplitude.tex:229–373`, including all six labels
attached to `thm:single-triple`. The accepted declaration map remains unchanged;
its source row is still pending. Stronger statement-fidelity approval has not
been supplied. Technical reviews by a separate agent of the same available
model are supporting evidence, not a substitute for that approval.

## Checked candidates

| Body | New declarations | Successful root session |
|---|---:|---:|
| ContractionOutput | 7 | 16114, first run |
| GeometricProperResponse and ProperSpanGermResponse | 2 | 50436, first run |
| CriticalAffineData | 2 | 2001, first run |
| SignedCriticalJump | 4 | 61164, second run |
| SingleTripleTreeResponse | 2 | 84196, second run |

All 17 new declarations have passing axiom traces containing only `propext`,
`Classical.choice`, and `Quot.sound`. All 436 files in this turn's baseline are
unchanged, including the 327 canonical SM modules, accepted declaration map,
axiom policy, pins, checks, and previously frozen candidates. No literature
interface or new mathematical axiom was used. No canonical port or whole-library
audit was performed; checkpoint 070 remains the last canonical audit.

The aggregate exposes two distinct statements:

- `SM.WallGerm.single_triple_tree_response_of_affine` proves the signed piecewise
  response for every affine coordinate choice satisfying the printed conditions.
- `SM.WallGerm.single_triple_tree_response` constructs valid affine coordinates
  from the physically distinct collinear critical points and supplies that
  response, the epsilon ranges, and the fact that at least one epsilon is positive.

Both use the actual tree coefficients on independent sufficiently close negative
and positive parameters. They prove one fixed integer sign, equal to minus one
or one, whose cast is the actual critical half-jump. The proper branch contains
the actual contracted polygon's tree coefficient with proved G1 and arity. The
full branch contains the separately computed ordinary and reversed gap products;
it does not introduce a two-vertex polygon amplitude.

## Source comparison prepared for review

| Printed item | Candidate evidence |
|---|---|
| Wall domain, source line 229 | Actual continuous WallGerm; singleton critical vertex support; empty concurrence support; explicit physical pairwise distinctness in the constructed-data theorem |
| `afr:wall-data`, line 236 | `boundary_half_jump_signed`: a fixed integer sign for all independent punctured-side parameters, derived from source SignChanges and generic connected sides |
| `afr:wall-epsilons`, line 241 | Existing exact ratio-sign definitions; `critical_boundary_affine_data` supplies a nonzero direction and all three distinct scalar coordinates |
| `afr:wall-uv`, line 247 | Existing wallGapU/V switch between the exact unit array and complete barred output; actual gap outputs are transported to wall-center values |
| `afr:wall-proper`, line 257 | `proper_span_tree_response`, followed by exact signed-jump substitution in the aggregate |
| `afr:wall-full`, line 261 | Previously checked `full_span_tree_response`, followed by the same signed-jump substitution |
| Propagation proof, line 326 | Earlier checked ContractionPropagation, now extended to every original containing interval and the entire barred sum, including unary terms |

Physical-root retention and the gap/polygon interpretation use the existing
contracted-word, restricted-word and far-only representation lemmas. Their
definition/source correspondence remains part of the stronger review; the table
does not itself certify it. Likewise, the final corner sum's definitions and
literature interfaces remain separate pending specifications.

The existing `critical_closed_gaps_G1` lemma explicitly supplies G1 for both
nonleaf closed gap polygons. It is separate from the aggregate prototype;
RestrictedCriticalG1's passing receipt (session 18064) has four declarations
and seven file bindings, all rechecked unchanged in this turn.

## Proof construction and repairs

The complete-composition expansion is injective and its range is exactly the
surviving cut lists. Contributions outside that range have zero difference by
unchanged child coordinates, so reindexing preserves the entire response sum.
The already proved inverse propagation supplies the response on the unique
containing child. All other children agree with their contracted coordinates.
This yields the full barred transform response, including its unary term.

Off-critical sign agreement identifies the contracted array with the center's
actual contracted polygon. The geometric critical-span formula supplies the
source scalar. A common positive radius fixes every required gap output and
noncritical array entry, which puts all right-hand data at the center.

The affine construction takes the endpoint difference as its direction. Physical
endpoint inequality makes that direction nonzero; the zero determinant and the
positive squared-length denominator determine the middle scalar. The remaining
two physical inequalities prove that scalar is neither endpoint scalar. No
arity-four assumption or inference of physical distinctness from zero support
is used.

The local paired sign-change witness extends to independent parameters because
each generic germ side is connected and every chirotope is constant there. An
exact integer identity, cast into the coefficient ring, then cancels only the
assumed invertible two. The aggregate selects the appropriate already proved
branch and substitutes this fixed signed scalar.

Two failed first attempts are preserved. SignedCriticalJump session 57122 left
one finite sign-case contradiction unsimplified; substituting the opposite sign
before three closed kernel-decide cases fixed it without changing any theorem
header. SingleTripleTreeResponse session 66657 lacked a decision instance for
the dependent piecewise expression. Adding the standard local
`Classical.propDecidable` instance retained all declaration and proof text.
Failed logs are not successful proof evidence.

## Evidence and continuation

Each body group has a `work/checks/*-prototype-result.json` receipt binding the
successful prototype, log, bodies and axiom traces. The complete executable
candidate is `work/checks/SingleTripleTreeResponse.prototype.lean`; from
`work/lean`, run `lake env lean ../checks/SingleTripleTreeResponse.prototype.lean`.
Do not run simultaneous kernels sharing the dependency directory.

Accepted original proofs remain 19/132 (14.39%). Original checklist: 38/191;
expanded checklist: 39/192 (20.31%). Main targets: 0/8. These candidate results
are not counted as accepted source claims.

Next obtain stronger statement/definition review and a controlled canonical
integration for this source result. Candidate proof work can meanwhile continue
with the unordered-support input conversion and explicit faithful coefficient
specialization identified by the aggregate technical review; see
decisions/single-triple-source-packaging-next.md. Then continue `thm:A-S3` at
source line 396: identify the physical deletion root in all
three root positions, transport the contracted/restricted word to the actual
deletion, and specialize the proved epsilon and response formulas. Preserve
both incident-root cases and the nonincident case; none is a permission question.

Six technical review reports are sealed, including the earlier five contraction
candidates and this turn's 17 declarations. The aggregate report is
work/reviews/single-triple-tree-technical-review-20260911.md. It found no missing
algebraic step and records the remaining source-presentation and stronger-review
qualifications. These reports do not grant source acceptance.
