# Canonical triple signs: technical review

2026-09-11. Reviewer: another agent of the same currently available model, independently reviewing eleven root-authored declarations. This is **not the stronger-model statement-fidelity approval requested by the user**, nor acceptance of `lem:multiaffine`. No Lean/kernel/build, proof edit, canonical edit or acceptance-map change was performed.

**Finding:** no mathematical or domain defect found. The declarations supply the exact source label order, six-order signed sorting, preservation of the unordered position support, and rational evaluation of these signed canonical triples for arbitrary tuples.

`canonicalPosition i` uses the representative of i−1. The two proved inverse identities show that it is exactly the inverse of `boundaryIndex 0`, which sends position k to physical source label k+1 modulo n. The separate range lemma places that integer label in 1,…,n. Thus residue zero is the source label n at the final position, rather than the first label in the canonical ordering. Injectivity follows from the proved inverse. No geometry or genericity assumption is needed.

For three distinct positions a,b,c, `sortTriplePositions` exhausts the six strict orders. Its output, written as (sorted positions; multiplier), is: a<b<c gives (a,b,c; +1); a<c<b gives (a,c,b; −1); c<a<b gives (c,a,b; +1); b<a<c gives (b,a,c; −1); b<c<a gives (b,c,a; +1); c<b<a gives (c,b,a; −1). These are exactly the parity signs of alternation. The distinctness premises justify all reversed strict inequalities; no order case is dropped. The sign theorem restricts every output multiplier to ±1, and the position-set theorem proves equality of the complete three-element unordered support.

`canonicalTripleValue` evaluates an increasing position triple using the **forward** physical label order under `boundaryIndex 0`, matching the source variable X indexed by increasing physical labels. `sortTriplePositions_evaluation` uses the actual cyclic and swap identities for chi, then the exact SignType-to-integer and integer-to-rational casts. It does not infer parity from a geometric orientation or introduce a scaling factor. Its conclusion holds for every labelled tuple, including collinear or physically coincident vertices, because the underlying chi alternation identities hold also at zero. The sorting inputs themselves are three distinct positions; a general repeated-label polynomial evaluation is not supplied by this helper and is not claimed here.

The canonical boundary map for every root is injective, and the embedded `BoundaryTripleSupports` supplies injectivity of the actual unordered physical support map. Together these are the relevant position/label facts for the first paragraph of source `lem:multiaffine` (714–797). This file does not yet define the unrestricted polynomial, normalize every ordered label expression, prove nonrepetition across trees, or establish multi-affinity/equality with the full gate sum. Those remain separate assembly obligations. No root-independence or polynomial relation among canonical variables is assumed.

Receipt verification: second root **60299**, exit **0**, all **4/4** manifest hashes match; the exact body occurs once in the prototype. All eleven successful traces contain only the standard foundations `propext`, `Classical.choice`, `Quot.sound` (some use fewer); the successful log contains no `error:`, `sorryAx`, `native_decide` or `Lean.ofReduceBool`. The preserved first run **11385** is failed evidence. Its prototype differs by the missing `SM.SinglePointTriple` import and the final evaluation proof repair: the already-closed reflexive branch was removed and explicit chi arguments fix the remaining rewrites. The canonical body diff changes only that proof; all definitions and theorem types are retained. The embedded boundary-support body is unchanged. No conclusion or caller premise was weakened to repair elaboration.

| Bound file | SHA-256 |
| --- | --- |
| `work/checks/CanonicalTripleSigns.body.lean` | `76321d75b54c5a31611575577ecbf36bb1edaeef2142f0177bfd22f042fbbe54` |
| `work/checks/CanonicalTripleSigns.prototype.lean` | `6e50bba7ee1b376b928ad1dc0838c74063db18a9a583beb33fb50c42a14effad` |
| `work/checks/CanonicalTripleSigns-second-kernel.log` | `7e2a6ec29b17d2faae708a452df304c62fd19b90da62fec417fd30de8a993f7a` |
| `work/checks/CanonicalTripleSigns-prototype-result.json` | `53e6a7ae2f98efec1a636723522852d62c779ecf03db425902d8e53e36f51f7b` |
| `work/checks/CanonicalTripleSigns-first-failed.body.lean` | `e4547610821cbab3e828d55205c4680bf949b7bd7b4ce04bcfe179b4c062cc1c` |
| `work/checks/CanonicalTripleSigns-first-failed.prototype.lean` | `9ecc72b8ebae27a43604bd3c6b9259cb17f0e1979f7611b3bd3a68fb08cfe277` |
| `work/checks/CanonicalTripleSigns-first-kernel.log` | `c66ab78721a4418f41f312269a5df25449d8f10cc03f14a75395c90c794daa85` |
| `work/checks/BoundaryTripleSupports.body.lean` | `60199670494951bea511f187f7f894fd63fd4d074237e5b0442602e2c4f02e42` |
| `work/lean/SM/RootBoundary.lean` | `604906b750e1ab198a2db3fc3cc011ab325493a91404a0b52ffe4583dd403f1a` |
| `work/lean/SM/Chirotope.lean` | `e0225bc712162273f43269ed764ac4849ae8fcd8798245a367d4262858fbf575` |
| `work/lean/SM/NearFar.lean` | `3d243e1d12636a02743e0f8dc37e3eecc7d46306fbd3cfca5170fd223ad6fa60` |
| `reference/SM/sm-2-amplitude.tex` | `014068e2f6e2d86b0ff4edf48877b5967847d661eaae04d2d4c5fd9f54b7c9cf` |

Passing and hash evidence do not establish stronger statement fidelity. Acceptance remains **39/192 (20.3%)**, targets **0/8**.
