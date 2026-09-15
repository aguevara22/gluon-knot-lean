# Nonincident flat contraction and signed response — technical review

2026-09-11. Independent review by another agent of the **same currently available model**. This is **not stronger-model statement-fidelity approval** and not original-source acceptance. Progress remains 39/192 accepted (20.3%), targets 0/8.

Reviewed: four declarations in `NonincidentFlatContraction` and the separately checked `flat_nonincident_signed_response`. No mathematical statement/proof defect was found. A documentation wording issue is recorded below.

## Complete contraction and coefficient

- `nonincident_flat_contracted_labels` quantifies over **every** label of the actual contracted tuple. It explicitly transports the label through `ZMod.ringEquivCongr` for the proved child-size equality. Preservation of natural representatives, subtraction and 1 identifies the old and transported local positions. The proof then expands the actual deletion-of-one-position formula and uses both branches of the checked modular cut calculation. For v below k it keeps position v and compensates for the cyclic wrap in the deletion reading; for v at or above k it uses old position v+1. The natural-subtraction bounds are supplied before each cast. No surviving label or boundary value is omitted.
- In particular local label 0 has local position q-1, at or above k, so its expanded position is the parent's final position q and its parent label is g. Local label 1 has position 0, below positive k, and retains parent label g+1. This verifies the directed root explicitly, while the universal label theorem supplies all other vertices as well.
- `nonincident_flat_contracted_tuple` uses function extensionality and the label theorem to identify the **whole** size-reindexed tuple with `shift (fusionIndex j g) (deleteVertex P j)`. The inverse/forward equality equivalences cancel on every label. Endpoint agreement is not used as a substitute for tuple equality.
- `nonincident_flat_contracted_support` identifies the actual critical support with the neighboring turn support. The coefficient theorem supplies the corresponding constructed G1 proof to the contracted tuple, and uses `g1_deleteVertex` for the actual deleted tuple. `treeCoefficient_of_reindexed_tuple_eq` transports the full tuple, dependent G1 and root across the size equality. Then `treeCoefficient_shift` is used with both root and shift equal to `fusionIndex j g`, so local root 0 becomes exactly the induced root in the deleted tuple. No arbitrary permutation or root independence is assumed.
- The coefficient equality is in **the integers**, between actual `treeCoefficient` values. The bound `3 ≤ q` is precisely parent arity q+1 ≥ 4 and includes the four-vertex source case. The source properness follows from the previously proved consecutive-span result; it is not an additional geometric assumption here. The label/tuple identities themselves require no geometry. The coefficient statement requires only the stated singleton zero support and derived G1, not parent G1 or G2.

## Nonincident germ response

`flat_nonincident_signed_response` has the source `FlatAt` predicate and actual nonincidence as its caller premises, at parent arity n+1. It constructs the occurrence k of j using boundary-index surjectivity, derives both interior bounds from nonincidence, and forms the actual consecutive triple. Its support, cyclic order, two leaf gaps and proper span are then proved from these data and the arity bound in `FlatAt`.

Strict betweenness constructs the actual affine coordinates (0,r,1), with a nonzero endpoint direction and all required distinct-coordinate inequalities. The existing sign-change transport supplies the reversed chirotope premise. The proof applies the integer single-triple response on the proper branch, reduces the U product to 1 using the formal leaf theorem, and substitutes the complete contracted/deleted coefficient equality above. The two-leaf factor holds for all signs, so no unsupported epsilon assertion is needed; the actual (0,r,1) ratios still agree with the source (+,+) pair.

The conclusion retains one fixed d = ±1 and one positive radius bounded by the germ radius, chosen before independently quantified negative/positive parameters. Both the signed turn difference and integer amplitude difference use that same pair and radius. Genericity at each punctured point comes from the actual wall germ. The deletion coefficient is at the center and the exact root `fusionIndex j g`. There is no hidden coordinate, size-normalization, side-symmetry, or extra genericity premise.

This is a **signed time-side** response. Right-minus-left normalization and the final combination with the incident branch remain separate; this review does not mark the full flat law complete. For a fixed nonincident root, its domain matches the corresponding source paragraph in `sm-2-amplitude.tex` lines 425–434, with the source flat inputs from `sm-1-polygons.tex` lines 714–718 and induced-root definition at `sm-2-amplitude.tex` 380–386.

**Documentation note:** the final contraction theorem and response comments refer to a “fused root.” In this nonincident case `fusionIndex j g` is the induced **retained** root, and is not the fused-edge label -1. The actual statements and proofs use the correct root. The frozen comments were preserved, as requested; this is a wording issue, not a mathematical defect.

## Receipt and repair evidence

All **11/11** contraction receipt hashes and **44/44** response receipt hashes match current bytes. Every listed body occurs verbatim exactly once in its prototype. Root's contraction **second session 86583** and response **first session 31841** exited 0. Their logs print the four and one declarations with only `propext`, `Classical.choice`, and `Quot.sound`. Neither passing log contains errors, `sorryAx`, `native_decide`, or `Lean.ofReduceBool`. This reviewer ran no Lean kernel or build.

Contraction first session **7171** is a preserved failure, with a dependent rewrite-motive error in the label proof and downstream `sorryAx`. The passing body inserts only an explicit `change` exposing the natural-valued conditional after `expandPosition_val`, before rewriting its representative. All four statements before `:= by` are byte-for-byte unchanged. The repair changes reducibility exposure, not the mathematical domain or assertion.

Receipt hashes bind the full manifests, including dependency bodies. Principal SHA-256 bindings (relative to the focused root):

| File | SHA-256 |
|---|---|
| `work/checks/NonincidentFlatContraction.body.lean` | `6c728f41bf8b741a46fc3566c2270c457555546793b17c3e66b9f84eca15a7e1` |
| `work/checks/NonincidentFlatContraction.prototype.lean` | `cccd644a474cc97ebc020c885e25fec0b4c36661ac7cc230b5d9cc30fd1a188b` |
| `work/checks/NonincidentFlatContraction-second-kernel.log` | `f96500856f2f53055a940a4374e7ac6d89bba2c5f9e818a1845b4ca99b52d007` |
| `work/checks/NonincidentFlatContraction-prototype-result.json` | `6e3d6a0d650fcbfa8402968b26373d805a6d9ea3eb09fff3b4a45ee1c750ddc3` |
| `work/checks/FlatNonincidentResponse.body.lean` | `1a5a34782a9cf59504edd015f92607d85d63e9c1dc461ef82bd6ac8c26342be3` |
| `work/checks/FlatNonincidentResponse.prototype.lean` | `4e639eaeb10a39b12241a2f1fb611e6d5a0cdd6fb32d8eb2224e50b549d9bb6f` |
| `work/checks/FlatNonincidentResponse-first-kernel.log` | `c4a26af6bcc036879284ae387b2995bef2abafbfddd750d34cff74d3183f254d` |
| `work/checks/FlatNonincidentResponse-prototype-result.json` | `eee51190f00433c97d7df8884bb781a9db39cc849b2226ebde64cbdc15548c91` |
| `work/checks/FlatContractionArithmetic.body.lean` | `45aa1ca887728c3d32dbf7a0e1df36966894d273d868bf6fc3a4f842eaa7f52a` |
| `work/checks/TupleArityTransport.body.lean` | `d18e9d42a019ba7a88be7963e0bb77ddaac1a32a2c533c77ddc779de7cbb002f` |
| `work/lean/SM/NamedWallPredicates.lean` | `828a9c5dc91455d6d171a01c0ece96901708dd9720f3a379563850b0a61e7513` |
| `reference/SM/sm-2-amplitude.tex` | `014068e2f6e2d86b0ff4edf48877b5967847d661eaae04d2d4c5fd9f54b7c9cf` |

Recorded checks and hash agreement bind the reviewed artifacts without supplying stronger fidelity approval. No frozen Lean body, canonical file, map, or acceptance status was edited.
