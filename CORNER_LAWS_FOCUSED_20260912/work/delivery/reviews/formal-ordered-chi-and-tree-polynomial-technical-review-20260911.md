# Ordered chi and exact tree polynomial: technical review

2026-09-11. Reviewer: another agent of the same currently available model, independently reviewing the root-authored `FormalOrderedChi` (14 declarations) and `FormalTriplePolynomial` (16 declarations). This is **not the stronger-model statement-fidelity approval requested by the user**, nor acceptance of `lem:multiaffine`. No Lean/kernel/build, proof edit, canonical edit or acceptance-map change was performed. The reviewer authored the dependency `CompositionTripleSupports`; root's independent review of it is separately bound below. This report does not independently approve that self-authored dependency.

**Finding:** no mathematical or domain defect found in the normalization, prescribed polynomial, unary/binary identities or G1 evaluation. These groups establish the exact source polynomial and its evaluation; they do not establish its individual-variable degree bound or complete all structural clauses of the multi-affine lemma.

`orderedTripleData` sends three distinct physical residue labels through the proved inverse of source order 1,…,n, then performs the six-case signed sort. Its sign is ±1 and its canonical variable has exactly the original unordered physical support. `formalOrderedChi` is defined in the unrestricted rational multivariate polynomial ring: distinct labels produce that one signed variable; any repeated pair produces the zero polynomial. The repeated-label theorem covers all three possible equalities. `eval_formalOrderedChi` treats the distinct and repeated cases separately and recovers the actual rational cast of chi for every tuple, including zero determinants. There is no use of realizability, evaluation equality, or chi-square relations to identify formal polynomials.

`boundaryTripleData` uses precisely the reversed order upper/middle/lower of the source near/far entries. Its variable support is the actual physical support under the given root reading. If two canonical variable indices agree, their physical support sets agree; the proved injectivity of `vertexSet g` forces equality of the complete increasing boundary triples. Thus distinct boundary-position triples remain distinct formal variables at each fixed root. This is a statement about labels, not physical point coordinates or chi values. `formalBoundaryChi_eq` and its evaluation theorem preserve the exact parity multiplier and reversed-order chi.

The formal ordinary and root factors are exactly one half times the difference and sum, respectively, of those near/far expressions. Their weight definitions multiply over every actual interior cut. `gate_pair_rational` checks the four nonzero sign pairs directly from the gate definitions: it does not transport integer division through a ring cast. The factor evaluation lemmas derive both nonzero sign premises from the actual G1 tuple and strict cut map; no caller-supplied gate identity or G2 premise is added.

The binary near/far equality is equality of actual increasing triples, so the ordinary factor and weight vanish as formal polynomials, while the root factor and single-cut weight equal that signed canonical entry. The proof of the latter uses the actual singleton cut-index domain. Unary weights are both the empty product one. These facts are valid before evaluation, and neither binary compositions nor the unary distinguished root are removed from the raw sum. The ordinary tree constructor separately requires at least two children, exactly as in the source.

`canonicalTreePolynomial` uses the existing full rooted recursion with these prescribed factors. Its type is `MvPolynomial (IncreasingBoundaryTriple n) ℚ`, with canonical increasing physical-label indices interpreted through root-zero order; it is not a quotient polynomial ring or a polynomial in independent composition weights. The signed-tree theorem specializes the existing proved finite-tree expansion: one minus sign per ordinary internal node, no additional root sign, every ordered child composition, and the permitted unary root. Finiteness and recursive decrease are supplied by the canonical actual tree construction, not an externally chosen height or restricted tree family.

`eval_canonicalTreePolynomial` maps the complete recursion under polynomial evaluation, and separately maps the original integer recursion under the actual integer-to-rational ring homomorphism. The factor/weight evaluation theorems identify the resulting coefficient arrays pointwise. This gives equality with the same-root original `treeCoefficient`, with precisely n≥3 and G1, as required by source `lem:multiaffine`; the proof uses neither root independence nor R. It does not assert that the literal gate sum is defined at silent zeros: only ordered-chi normalization is evaluated on arbitrary tuples, whereas the final gate-sum equality requires G1.

Compared with source lines 714–797, these declarations discharge ordered-variable interpretation, the prescribed half-sum/half-difference polynomial, local unary/binary identities, the exact finite signed-tree expression and G1 evaluation. Tree-level nonrepetition, the exceptional shared interval of the unary root and its immediate child, and the unrestricted individual-variable degree bound remain separate proof/assembly obligations. The local binary zero identity supports the later whole-tree zero assertion, but these groups do not expose that whole-tree assertion as a separate theorem. No source acceptance is inferred from these partial ingredients.

Verified receipts: `FormalOrderedChi` second root **82948**, exit **0**, **5/5** hashes; `FormalTriplePolynomial` first **95654**, exit **0**, **7/7** hashes. Each exact body occurs once in its prototype. All 30 successful traces contain only the standard foundations `propext`, `Classical.choice`, `Quot.sound` (some use fewer); neither successful log contains `error:`, `sorryAx`, `native_decide` or `Lean.ofReduceBool`. The preserved ordered-chi first run **20845** failed only an untyped conjunction passed to `dif_pos`. Its exact body/prototype diff adds the intended explicit proposition to that proof term; definitions and all theorem types remain unchanged. Failed-run traces are not used as successful evidence.

| Bound file | SHA-256 |
| --- | --- |
| `work/checks/FormalOrderedChi.body.lean` | `1df0e2ad12df3d28dc32318201fe2a786eb880fe56ea2fff374f7fc3f2d3ebe6` |
| `work/checks/FormalOrderedChi.prototype.lean` | `51f18a07af5334f300d00b8ad2c551109abcf1f14e7997394db0a8b7ed4982e4` |
| `work/checks/FormalOrderedChi-second-kernel.log` | `b38d81683c167153dc423bf9422d0fe3d49a38d609c72d3c73a99dee7758028d` |
| `work/checks/FormalOrderedChi-prototype-result.json` | `8e9bacaeaae94866977825c0f2825d1097a415cc70fcee8e17a56f90a24c8e57` |
| `work/checks/FormalOrderedChi-first-failed.body.lean` | `50fe2275fcad48aeb0941fdb0928e8bf393282d352eb751a67756e1c6d8166da` |
| `work/checks/FormalOrderedChi-first-failed.prototype.lean` | `ce18d5dd6ea9d70db35411e3fcaccd8bfcf8bd53d9d97ea63742935f39cc8fee` |
| `work/checks/FormalOrderedChi-first-kernel.log` | `2f09ce8b50a4e22d806795c842b261ceb26dcf3a53e7e1c9f4c3ac2013c564fd` |
| `work/checks/FormalTriplePolynomial.body.lean` | `138f5620027a3be64bbaed123b2a8ef6723b50fe6911bd4b2f6cf06a8b6c2d84` |
| `work/checks/FormalTriplePolynomial.prototype.lean` | `39d0f91909b73907fc924be3797fd0ef1b13d48781f0beccf8bfcf0c9f41b501` |
| `work/checks/FormalTriplePolynomial-first-kernel.log` | `93ccc90d3c07d4bdd7464d17997d2833d522b4f1d8390568cf4702ad906c27e2` |
| `work/checks/FormalTriplePolynomial-prototype-result.json` | `3e0aff7ef134e1b3c8ba5cc80f1b7e9089380d1d2da8ae3f0c69f161518acc30` |
| `work/checks/CanonicalTripleSigns.body.lean` | `76321d75b54c5a31611575577ecbf36bb1edaeef2142f0177bfd22f042fbbe54` |
| `work/checks/BoundaryTripleSupports.body.lean` | `60199670494951bea511f187f7f894fd63fd4d074237e5b0442602e2c4f02e42` |
| `work/checks/CompositionTripleSupports.body.lean` | `c6600e67a028ccffb28c0aae1d02e782b689f24e823ddd3a49b297e0cb069cff` |
| `work/lean/SM/Gates.lean` | `91abf2e71af3d1ee9090b3c1a30cd15458d2e0884cb8f46f0b8f59af06065c83` |
| `work/lean/SM/NearFar.lean` | `3d243e1d12636a02743e0f8dc37e3eecc7d46306fbd3cfca5170fd223ad6fa60` |
| `work/lean/SM/TreeCoefficient.lean` | `d070e70dfbb61e036641f0d5fac4adae83fd1cadfe22f3ce2ffd8c8e1de9ab06` |
| `work/lean/SM/PlaneTreeShape.lean` | `749fc1127dc506251ea5c081636580ab02797425f4092d6d15ef39541d4d753b` |
| `work/lean/SM/PlaneTreeWeights.lean` | `bc0e6a06e62193b96fba3a7327ce035422ca0b8be6da2f87c22b0d1e1035eda0` |
| `work/lean/SM/PlaneTreeExpansion.lean` | `c8730af354e242689181de79683ad35e5ab1e052637aa17ee50e95de475c3877` |
| `work/lean/SM/PlaneTreeFormal.lean` | `e36d624ef09a1accfb48326fc17a61473c767729e37a05d990cb31264debd1b9` |
| `work/reviews/composition-triple-supports-technical-review-20260911.md` | `1873942067abdb990d28a5cd1b646ef0cf43d3379508a4201e08dd8a5d5e9355` |
| `reference/SM/sm-2-amplitude.tex` | `014068e2f6e2d86b0ff4edf48877b5967847d661eaae04d2d4c5fd9f54b7c9cf` |

The receipts bind the remaining embedded dependencies. Passing/hash evidence does not establish stronger statement fidelity. Acceptance remains **39/192 (20.3%)**, targets **0/8**.
