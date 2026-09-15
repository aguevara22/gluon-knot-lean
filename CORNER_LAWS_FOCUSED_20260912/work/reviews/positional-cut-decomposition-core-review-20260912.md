# Positional decomposition: independent review of the core construction

Reviewer: root. Original implementer: /root/review_contraction_candidates.
Root authored only the two subsequent zero-function transport repairs. This
review covers the independent mathematical construction and its unchanged
statements; the original implementer independently reviews those two repairs
in a separate record. Neither review grants stronger fidelity approval.

Root read the original8 declarations and their canonical dependencies. The
synthetic arrays D(t)=2*b(t.middle), H(t)=-2*a(t.middle) sample exactly the same
physical interior position in each near/far triple. The half-factor identity
uses only multiplication by the inverse of2 and commutative-ring arithmetic.
It holds with zero divisors and zero weights. Setting either positional weight
to zero gives the near-only/far-only identities. All transforms retain the
complete actual composition sum and unchanged actual child-coordinate product.

The final identity applies the already proved nearFar_factorization_coordinate,
then expands its actual far transform and each near transform. The physical
Finset cut product follows prod_interior_positions, whose bijection was reviewed
independently. Thus arbitrary subsets are represented by all outer compositions,
and each gap retains every independent composition, including unary cases and
one-leaf gaps. No nonzero-cut, degree, realizability, restricted-marking,
coefficient, or geometric-independence premise is assumed. No defect found.

Root second kernel64127 exited0; all8 axiom traces use only propext,
Classical.choice and Quot.sound. The exact first43011 body/prototype/log are
preserved. Only the two zero-array proof transports differ from the first draft;
all theorem types and dependency bodies remain unchanged. Formal cancellation
still needs the actual silent polynomial and geometric zero-gap argument.

| File | SHA-256 |
| --- | --- |
| `work/checks/PositionalCutDecomposition-first-draft.body.lean` | `b2d4791ce6ad2a41846ce999b0cc99cecda860dc545064640d526559f7c04fcb` |
| `work/checks/PositionalCutDecomposition.body.lean` | `ed59789e73793bd8b885ab65bd9096abe7065de2b7cd4386f19de6ff26a82b6d` |
| `work/checks/PositionalCutDecomposition.prototype.lean` | `5b179f40dba6858a80146a652d0658715067eacbb183a3397869420b24a191d2` |
| `work/checks/PositionalCutDecomposition-second-kernel.log` | `6bcb68dccb6d1fb76fef022b3f1187befc026f1fbebf33f8bbee4f86eb797a9a` |
| `work/checks/PositionalCutDecomposition-prototype-result.json` | `9b640c1217703f93148374b3f9940a8373810c62ae558ba312d7450c2661284e` |
| `work/checks/SelectedCutRefinement.body.lean` | `14813200d24d78c3da98cdc7508400e3b82251cfed19f4dddbf4f81cfe190b18` |
| `work/reviews/selected-cut-refinement-technical-review-20260911.md` | `fdc5706133aabcdd77ca0c7419269866b257b8c77377f9cc2336904738af1c13` |
| `work/lean/SM/NearFarFactorization.lean` | `5ba746897c43bb5382e4a409feba3c77acfca9bbbadcd6a5e708b94263d92628` |
