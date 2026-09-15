# Flat boundary positions — technical review

2026-09-11. Independent review by another agent of the **same currently available model**. This is **not stronger-model statement-fidelity approval** and not original-source acceptance. Progress remains 39/192 accepted (20.3%), targets 0/8.

## Findings

No mathematical defect was found in the sixteen declarations in `FlatBoundaryPositions.body.lean`, compared with the root cases in the proof of `thm:A-S3`, `reference/SM/sm-2-amplitude.tex` lines 407–452, and the deletion-root definition at 380–386.

| Physical parent root | Increasing critical positions | Actual labels in that order | Gap leaves | Span |
|---|---|---|---|---|
| Nonincident g | k - 1, k, k + 1 | j - 1, j, j + 1 | 1, 1 | Proper |
| Incoming j - 1 | 0, 1, n - 1 | j, j + 1, j - 1 | 1, n - 2 | Full |
| Outgoing j | 0, n - 2, n - 1 | j + 1, j - 1, j | n - 2, 1 | Full |

1. `boundaryIndex_first` and `boundaryIndex_last` use the actual reading `g + position + 1`. The last-position proof explicitly casts the natural identity `(n - 1) + 1 = n` before reducing modulo n; no unproved wrap convention is assumed.
2. In `boundaryIndex_nonincident_interior`, a first-position occurrence of j would give g = j - 1, and a last-position occurrence would give g = j. Both contradict the stated nonincidence. This derives the two strict interior bounds needed to construct `consecutiveBoundaryTriple`; they are not extra source restrictions. Surjectivity of the boundary reading supplies k for every nonincident root.
3. The consecutive-label proof respects natural subtraction by proving its lower bound before casting k - 1. The two unit gap lengths follow by subtraction of the actual endpoint values. For properness, equality with the full interval would force k - 1 = 0 and k + 1 = n - 1. The first equation and positivity force k = 1; the second then forces n = 3, contradicting the source bound n ≥ 4. The existential nonincident theorem assembles exactly these labels, the actual `turnSupport j`, both leaf counts, and properness.
4. The two incident triples have the positions shown in the table. Their strict-order proofs use only n ≥ 4. Incoming labels follow from the first two positions and the last-position wrap; outgoing middle label uses the justified cast of n - 2. Both supports are exactly the source unordered turn support, by the corresponding cyclic permutations. The span in each case has the actual full interval endpoints, not merely equal length.
5. **The boundary case n = 4 is included.** Incoming positions are 0,1,3 with gap lengths 1,2; outgoing positions are 0,2,3 with lengths 2,1. For a nonincident root k can be 1 or 2, giving spans [0,2] or [1,3], each properly inside [0,3]. Thus the incident nonleaf gap closes to a three-vertex polygon, and the nonincident case is never incorrectly classified as full. This is a direct arithmetic consequence of the statements and definitions, not a separate kernel test.
6. The cases are exhaustive because `incident j g` is exactly the disjunction g = j - 1 or g = j. The file provides the three cases separately rather than one final disjunction theorem. No additional location, convexity, strict betweenness, G1, physical point separation, or named-wall hypothesis is used: this is the combinatorial positioning stage, valid on the source flat-wall domain without narrowing it. It does not infer physical distinctness from label support.

The inspected dependencies include `RootBoundary`/`Polygon` for reading, intervals and incidence, `TurnSupports` for the unordered support, and the hash-bound boundary-support and surjectivity candidates. No circular wall-response premise occurs. These declarations establish boundary positions and interval data; the actual deleted-tuple identification, epsilons, side orientation and flat amplitude equation require the subsequent work and are not claimed here.

## Receipt and hash verification

All **5/5** receipt hashes match current bytes. Each of the three listed bodies occurs verbatim exactly once in the prototype. Root's **second session 50897** exited 0; its log prints all sixteen declarations with only `propext`, `Classical.choice`, and `Quot.sound` (or subsets). The passing log contains no error, `sorryAx`, `native_decide`, or `Lean.ofReduceBool`. No Lean kernel or build was run by this reviewer.

Preserved first session **30193** failed on a hidden Fin value, an unexpanded local triple, and two numeral-cast `change` steps; its log includes downstream `sorryAx` and is not passing evidence. The body diff shows only exposing the Fin value, adding `dsimp only [t]`, and replacing those two `change` steps with explicit unfolding/cast simplification. All sixteen declaration statements remain unchanged.

SHA-256 bindings (relative to the focused root):

| File | SHA-256 |
|---|---|
| `work/checks/FlatBoundaryPositions.body.lean` | `13f01dbe3050125a22ce407f5d6e01101ee680b98627f6b226ff325964a6fc56` |
| `work/checks/FlatBoundaryPositions.prototype.lean` | `f815ba924897a4566737b8a519afb1f45d918cb1dbbef009557c5de0eda54df7` |
| `work/checks/FlatBoundaryPositions-second-kernel.log` | `0dc4ad65c1e5331f524d8510eeb85b77ff3893711ecc19c7c4a8094fc5bab172` |
| `work/checks/FlatBoundaryPositions-prototype-result.json` | `f712aacca7af62a344aa40741a8f73d5ca67ec2a9ba6150da0919eb0cfa224e5` |
| `work/checks/BoundaryTripleSupports.body.lean` | `60199670494951bea511f187f7f894fd63fd4d074237e5b0442602e2c4f02e42` |
| `work/checks/UnorderedCriticalTriple.body.lean` | `985956064e7fa879661ee9a144753639f56a73cf48741d1e8e503cf5a201c110` |
| `reference/SM/sm-2-amplitude.tex` | `014068e2f6e2d86b0ff4edf48877b5967847d661eaae04d2d4c5fd9f54b7c9cf` |

Recorded successful checks and hash agreement bind this technical review; they do not establish stronger fidelity approval. No frozen Lean body, canonical file, acceptance map, or status was edited.
