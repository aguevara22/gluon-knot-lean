# Explicit vertex positions in the newborn arc

Author: /root/review_contraction_candidates, same currently available model as root. This is a seven-declaration implementation draft, not independent self-review, stronger-model statement-fidelity approval or source acceptance. No Lean kernel/build/audit was run. Root owns testing and independent review. All passing bodies, source and canonical files remain unchanged.

Source role: the precise passage through M and M_epsilon in lem:soft-generic(iv), SM2 lines 1034–1042 and the final proof paragraph. The preceding checked Gauss geometry already gives the actual empty arc and incoming next=return. This additive body supplies the formerly separate vertex-position predicates themselves.

`softAttachmentVertexPosition j` is exactly `(softOldIndex j j, 0)` in the half-open traversal domain. `softInsertedVertexPosition j` is exactly `(softNewIndex j, 0)`. The two evaluation theorems unfold the actual traversal evaluation to edgePoint at parameter zero and use the frozen literal insertion tuple identities. Their values are P j and P j + epsilon*q for every real epsilon.

`soft_vertex_arc_label_values` proves the incoming, soft and return numerical labels. The incoming label has value canonicalPosition(j); the soft label has value canonicalPosition(j)+1; the return label has value zero for j=0 and j.val+1 otherwise. Incoming labels follow from the actual parent-edge formula and predecessor arithmetic. The soft label follows from its proved Nat cast representation and the strict bound canonicalPosition(j)<n. The return formula follows from the parent-edge formula at the attachment itself. No endpoint equality is used as a substitute for these numerical position calculations.

`soft_vertex_arc_of_edges` takes arbitrary actual incoming and return traversal points a,b, with b's parameter positive. This is an explicitly generic helper; it does not assume an ordering. Half-open domain bounds and the computed labels imply key(a)<key(M). Equality of the inserted vertex's edge with b's edge and positivity of b's parameter imply key(M_epsilon)<key(b).

For j nonzero, canonicalPosition(j)=j.val-1 and j.val>0. Thus the soft label lies strictly before the return label, proving key(M)<key(M_epsilon). The four positions consequently increase as a,M,M_epsilon,b. Each of the four asserted strict cyclic predicates follows from its increasing-order branch and the relevant transitive inequality.

For j=0, the incoming label is n-1, the soft label is n, and the return label is zero. Since n>=3, every half-open return point has smaller key than every incoming point: key(b)<key(a). Combining the already established inequalities gives key(M_epsilon)<key(b)<key(a)<key(M). The proof explicitly chooses the wrap branches of each cyclic predicate. This is precisely the same oriented order a,M,M_epsilon,b across the numerical cut; no j=0 exception or relabelling assumption is added.

`softNewbornVisits_vertex_arc` applies this helper to the actual newborn incoming and return visits built from classification and the loop sector. Their edge formulas are definitional. The positive return parameter is derived from checked child-G1 strict interiority, not a new caller premise. The conclusion states all four predicates:

- incoming, M, return;
- incoming, M_epsilon, return;
- incoming, M, M_epsilon;
- M, M_epsilon, return.

These are direct `traversalBetween` propositions on the actual positions. The final theorem takes child G1 and the actual classification/loop proofs because it is a pointwise assembly interface. The existing checked positive-interval theorems derive child Generic and classification from the original parent Generic/admissible domain. Root's all-clause source assembly will use those derived proofs; this body introduces no interval, order, or density oracle and never asks for child Generic at zero.

## First-draft bindings

- Body and first-draft body: `e22c73c8ed25393274a85df855eb391640b0261d121d4d35559530b2a388ae9a`.
- Prototype and first-draft prototype: `570d6e92fe576c3a7d9d5d2095bb0985436154067b07ddbff7da4f0096d8a881`.
- Ordered 21-body manifest: `work/checks/SoftNewbornVertexArc-body-dependencies.json`, SHA256 `5c66fbe0828a2ad7d029729c32205e551a86bd10148be08f49ecf40ef871cabe`.
- Full source/receipt/body bindings: `work/checks/SoftNewbornVertexArc-draft-dependency-bindings.json`, SHA256 `3df87f2abd7880e6798682757906e7f95190602415266444d98be26f83fafd1e`.

The prototype preserves the actual dependency order of the frozen SoftNewbornVisits prototype and appends this one new body. All source receipt hashes and each complete body's single embedding were checked by file inspection. This is not a kernel-pass claim.
