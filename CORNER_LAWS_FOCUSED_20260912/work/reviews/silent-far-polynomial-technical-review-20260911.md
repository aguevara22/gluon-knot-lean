# Silent far polynomial setup: technical review

Independent technical/source comparison by another agent of the **same currently available model**, not the author of SilentFarPolynomial. This is **not the stronger-model statement-fidelity approval requested by the user**, and does not accept the source formal-cancellation claim. No Lean/kernel/build/audit or frozen-file/map edit was performed.

Reviewed all fourteen declarations against the exact formal setup of `reference/SM/sm-2-amplitude.tex:845–860` and its later use through line984. Also read the complete actual near/far definitions, the earlier ring-map naturality group, and the imported polynomial inverse-of-constants instance. No mathematical or domain defect was found in these setup/specialization statements.

- `SilentFarEntry H0` is exactly the subtype of IncreasingBoundaryTriple n whose fixed array value is zero. Its value retains the entire actual boundary triple, so different triples give different variable indices. Proof irrelevance identifies alternative witnesses of the same zero equality. No nonzero triple is included, no zero triple is omitted, and no derivative-independence or realizability relation is imposed. `MvPolynomial` is the ordinary unrestricted polynomial ring in that index type. In the source specialization R=ℚ these are precisely the independent silent far variables.
- `silentFarArray` puts X at each zero triple and C(H0 t) at each nonzero triple. Its dependent branch preserves the actual triple and zero witness. The separate variable array is zero at every nonzero entry, and the proved constant-plus-variable identity uses C(0)=0 at a zero entry. Classical branching decides an equality proposition; it neither changes the variable domain nor assumes computable zero tests for the coefficient ring.
- `silentFarZeroHom` is the unital polynomial evaluation map with identity on base coefficients and every variable sent to zero. The two explicit branch proofs show that applying it to the full formal array gives exactly H0. This is a complete array equality, not an equality only on a selected interval or on nonzero entries.
- `silentPolynomialTwoInvertible` is a proved local instance. The standard `MvPolynomial.invertibleC` transports the actual base-ring inverse through the constant ring homomorphism; the numeral identity C(2)=2 then transports the instance to polynomial two. Only the already stated base-ring Invertible(2) premise is used. There is no new caller assumption of polynomial invertibility, no cancellation-domain assumption, and no field-only argument.
- `constantFarCoordinates` is exactly C applied coordinatewise to `farOnlyCoordinates H0`, the source fixed c0. Its equation is for the **constant lifted far array** C∘H0, proved by complete transform naturality and the actual inverse equation. Its inverse identity is likewise the inverse of that constant array. Neither theorem replaces that constant array with the formal variable array.
- The final two specialization theorems map the actual inverse of silentFarArray and its complete reversed-far output through silentFarZeroHom. Complete naturality plus the proved array specialization yields their original H0 values at every interval. This includes the full-root interval but does not assert reversed-far constancy for arbitrary intervals: equality after evaluation at zero is all that is claimed.

The setup is algebraic for arbitrary base CommRing (and invertible two for the inverse/output declarations). WeakGeneric and geometric H0 are not needed for specialization; they remain essential later for **constancy**, which none of these declarations claims. In particular, zero specialization alone cannot prove that inverse coordinates equal constantFarCoordinates or that all nonconstant silent terms vanish. That source obligation remains open in this group.

Root third59081 exited0. All 4/4 receipt-bound hashes match; both current bodies occur exactly once in the prototype. All fourteen traces are present: SilentFarEntry has no axioms, and the others use only propext, Classical.choice and Quot.sound. No error, sorryAx, native_decide or Lean.ofReduceBool marker occurs. First80793 and second76834 files/logs remain preserved failed evidence. Comparing the displayed declaration types confirms all original thirteen types are unchanged; the added fourteenth declaration is the proved local invertibility instance. Other changes are explicit classical decisions, dependent-if/evaluation proofs and the standard polynomial invertibility import, not stronger hypotheses or modified array branches.

SHA-256 bindings:

| File | SHA-256 |
|---|---|
| `work/checks/SilentFarPolynomial.body.lean` | `46ce117365d9aa9b3f262c215a50a73bde1f4c4939fd2eeb9aed64051a876fe0` |
| `work/checks/SilentFarPolynomial.prototype.lean` | `d5445821b6d7efce5d8da734da6da927d51447f2aebec1313794053f90272144` |
| `work/checks/SilentFarPolynomial-third-kernel.log` | `3ff56e346cc1009c20a2791c582d40aa882246695cebd5510ced5ea8a5ba4ec6` |
| `work/checks/SilentFarPolynomial-prototype-result.json` | `ef8f339051e90412f05547df24a842b8704683f498b545cd6e7bf42e860e6957` |
| `work/checks/SilentFarPolynomial-first-failed.body.lean` | `e67b585e3204d5770e8d8fed144564406b0265a4117a3a14751973ae8d5cb922` |
| `work/checks/SilentFarPolynomial-first-failed.prototype.lean` | `74035512b18120f41fe1bc5693362c8099cd2e48b212837aad325202507fc9c4` |
| `work/checks/SilentFarPolynomial-first-kernel.log` | `c3252b2f04febb57dad8b5d920033dd9e6e2e34059fb7a72f5fc8c63e0d56728` |
| `work/checks/SilentFarPolynomial-second-failed.body.lean` | `2204ebdf59f0c3796d7f3e0f22761449c8a99fa8e0476cb09cc31b1a96d47b5d` |
| `work/checks/SilentFarPolynomial-second-failed.prototype.lean` | `b76feaaaf06471170d8f7e6719ee463130dad33e7dcc2934e48f226fa70c4d16` |
| `work/checks/SilentFarPolynomial-second-kernel.log` | `138bd61a5f63ea931943e402f1de5adc237f9fb036dad73b313308a6ad7709b3` |
| `work/checks/NearFarRingMaps.body.lean` | `7a5aaadbc1a8041a39f316fb825632afd3493d892e0722fc32defd8fc64c8f16` |
| `work/reviews/near-far-ring-maps-technical-review-20260911.md` | `06b3c12b6e19e777e858c5a0e0bdc475235812dbc797cc771a8030e4c9611047` |
| `work/lean/.lake/packages/mathlib/Mathlib/Algebra/MvPolynomial/Invertible.lean` | `7617c5dae2b3466359ba04a35d22bca430560910ce19c20305d2f97b8cfff3f9` |
| `work/lean/SM/FarOnlyOutput.lean` | `d773b636e2dc37babf11ae3df6b1eb813f5bc2812ad10f5e9bb76faf7d133aa4` |
| `reference/SM/sm-2-amplitude.tex` | `014068e2f6e2d86b0ff4edf48877b5967847d661eaae04d2d4c5fd9f54b7c9cf` |

Stronger statement/definition fidelity and source acceptance remain pending. Accepted progress is unchanged: 39/192 (20.3%); targets 0/8.
