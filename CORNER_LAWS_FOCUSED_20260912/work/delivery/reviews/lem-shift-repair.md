# Independent review of the explicit lem:shift repair

Reviewer: `review_chirotope-independent-20260910` (not the Lean author).

**Verdict: `SM.shift_reversal_corrected` is a valid, explicitly scoped repair. This report does not certify or accept the original unrestricted `lem:shift`.**

Original source: `reference/SM/sm-1-polygons.tex:484`, especially the omitted condition in the left-count consequence of clause (iii). The separate `work/reviews/lem-shift-scope.md` and exact counterexample remain unchanged and establish why a repair is required.

## Exact repair boundary

The new aggregate is on arbitrary real labelled tuples with source n>=3. Its `NeZero n` instance is redundant at that size. The only newly required mathematical condition for the disputed count is explicit and local: `forall i, turn P i != 0`. The unconditional result is instead `leftTurns(reversal P)=rightTurns P`, with rightTurns defined as the actual number of indices where the source turn equals -1. The count `n-leftTurns P` is derived only under the nonzero-turn premise. The rotation conclusions are explicitly on Regular P, their previously established source domain. No global Generic premise silently restricts the otherwise unrestricted chirotope, affine edge or turn formulas.

This is an honest correction to a false source consequence. It is not a faithful proof of the source's missing-premise statement, and the original row remains pending and unmapped. The repaired declaration is deliberately absent from the original declaration map. Neither this review nor its helper proofs authorize an original proof/checklist increment or a source/checker amendment.

## Source/type/body comparison

The shift chirotope identity reads the actual vertices at i+1,j+1,k+1, and the reversal identity reads the actual vertices at 2-i,2-j,2-k. Reversal is the previously reviewed actual map P(i)->P(2-i); it is not an arbitrary index involution or identified with a cyclic shift.

The new affine edge identity is proved for every real parameter t and every tuple, including degenerate tuples: the reversed point at label i and t equals the old point at tail label 1-i and parameter 1-t. This exactly records the directed edge traversed backwards. The supporting closed/open segment theorems prove equality of the actual segment sets by transporting both directions of the parameter witness; 1-t preserves [0,1] and (0,1), respectively. The shift formula retains t unchanged. These stronger parameter statements establish the source's edge statements without assuming nonzero edges or genericity.

G1 reversal transport uses the actual chirotope identity and injectivity of the vertex permutation i->2-i, preserving all three distinctness conditions. G2 reversal transport maps three distinct actual edge-interior witnesses through the tail permutation i->1-i and the proved interior-set identity. It therefore preserves the source prohibition of a common point in three distinct edge interiors, not a substituted weaker genericity condition. Reversal involution proves the backward direction. The existing shift theorem covers the same full G1/G2 predicate. The aggregate includes both genericity equivalences and actual surjectivity of shift/reversal on GenericTuple.

The topological statements concern the genuine generic subtype and its actual cyclic quotient. genericReversal is the coordinate reversal restricted to GenericTuple. Its continuity is proved coordinatewise, and the same involution supplies the continuous inverse. Images of labelledChamber are equal to full actual connected components, not just subsets or combinatorial sign classes; the reverse inclusion is proved with that inverse homeomorphism. On GenericPolygon, Quotient.map uses the already proved compatibility of reversal with cyclic shifts, and its continuity follows from the quotient universal property. The actual quotient involution gives a homeomorphism, which again carries a whole actual chamber onto the corresponding chamber. For cyclic shift, the accepted genericShift homeomorphism gives the labelled component image equality; on the quotient the projection is unchanged, so the induced map is the identity and preserves every chamber. No unproved path lifting or artificial discrete topology is used.

Crossing transport uses the actual unordered finite supports of remote closed edges that meet geometrically. The old tail index i maps to 1-i under reversal; this is deliberately different from the vertex/turn map 2-i. remote_sub_left proves remote pairs stay remote by the actual modular adjacency definition. edgeSegment_reversal preserves their actual geometric intersection, so isCrossing_reversal_iff is an equivalence of the true crossing predicates. reverseSupport is the finite image under i->1-i and is proved involutive. The concrete crossingReversalEquiv and crossingSet_reversal therefore give the full source crossing inventory under relabelling. Under shift 1, old edge labels move by -1, and crossingSet_shift uses exactly translateSupport(-1). No crossing oracle, generic-only fake support set, omitted crossing, or arbitrary graph is supplied.

The turn identities retain the actual determinant orientation. leftTurns_reversal_eq_right uses the bijection i->2-i and the three-valued sign identity (-s=1 iff s=-1); a zero turn remains zero and contributes to neither count. Only sign_right_iff_not_left requires s!=0. Under the explicit all-nonzero premise, the two finite filters for left and right partition the full cyclic index universe, so their cardinalities sum to n. The conditional subtraction formula is then derived with natural-number arithmetic from that exact partition identity. It does not silently count zero turns as right turns. `leftTurns_reversal_of_generic` separately proves the condition from actual G1 using n>=3 and the determinant nonzero theorem; the consumer is not asked to provide an additional unexplained turn assumption.

The final rotation clause invokes the previously reviewed actual finite-sum invariance under shift and negation under traversal reversal on Regular P. It introduces neither a desired-law parameter nor an arbitrary integer rotation. The minimal repair changes only the problematic counting scope while preserving the natural domains of the other source assertions.

The source's labelled/equivariant formalization permission is fully respected: both actual labelled and quotient homeomorphisms/components are used where needed, and all vertex, edge, crossing and turn relabellings have their correct distinct index formulas.

## Consumer and acceptance limits

The two direct consumers examined in the separate scope report have explicit Generic domains: the reversal law for C in SM4 and the reversed-star statements in SM5 after genericity of the positive star is established. The new generic count corollary proves that their Generic premise supplies nonzero turns. This is a verified interface compatibility result; it does not certify the consumers' entire proofs, assert that they have already been ported, or erase the original source omission.

The original `lem:shift` is still pending with blank declaration and module fields. `SM.shift_reversal_corrected` is deliberately unmapped. The source/counterexample scope report has not been rewritten or superseded as a claim of original-source truth. Frozen source files are unchanged. No Lean or map file was authored or edited by this reviewer.

## Verification and bindings

All five new repair modules were read independently together with their concrete definitions and supporting proof bodies. The 38 inherited local modules in their 43-file import closure match earlier independent review inventories. All 43 current local files match the passed checkpoint-025 project receipt, which audits 852 local declarations and 20 mapped claims and leaves stage_accepted false. The checkpoint receipt equals the current development receipt.

I independently loaded SM.Admissible and SM.ShiftReversal with `lake env lean --stdin`, checked the full repaired theorem type, and ran `#print axioms` on both `SM.shift_reversal_corrected` and `SM.leftTurns_reversal_of_generic`. The command completed with exit code 0; both theorems reported only `propext`, `Classical.choice`, and `Quot.sound`. The repair has no original-source semantic statement hash because it is intentionally unmapped; the current code, source and receipt hashes below bind this separate review.

Source SHA256: `8bc30167c9cde79c3eb4b9cf52052f81f040ec91490f49517b9f1b7ad0333a00`.

Checkpoint-025 receipt SHA256: `e3e0a5f9b64120a436cf7d7a48f2161968cf3d8e1bf248b65b8e48a8b5a6eccc`.

Current development receipt SHA256: `e3e0a5f9b64120a436cf7d7a48f2161968cf3d8e1bf248b65b8e48a8b5a6eccc`.

Prior omission review SHA256: `3ed7dd5da78abc4e50e6f79a18766f5bfe6c91e8dbef250c8e1ccb8e905e9295`.

Separate counterexample SHA256: `3db5b53e42a7efffcd9b2e9a196b25ab2f2f0744b7d715c0901f8bb7a008b583`.

Inspected local supporting files:

```json
{
  "work/lean/SM/ChamberPaths.lean": "cabb36d739563036aeee39c1a7bc0cf925a6259c5f90a22ecd61c9e2e737d44a",
  "work/lean/SM/Chambers.lean": "595dbb81227c5e368a9aaa696d6a609338961899c3c948590ab6a6f94d70ecc9",
  "work/lean/SM/Chirotope.lean": "e0225bc712162273f43269ed764ac4849ae8fcd8798245a367d4262858fbf575",
  "work/lean/SM/ContinuousGeometry.lean": "61250145831b23c7d8bedc54956643d844bc52ef4ff1ab55b87b81b26cc2000c",
  "work/lean/SM/CrossingCriterion.lean": "855c16a0d99ed9abb634a5494f7e30d947d68592d4f2878762b5ecd6c8aef648",
  "work/lean/SM/CrossingEquiv.lean": "a505d6a14ecc81ff72512016a68817d70fec010e12722b08f4b6c8b10f132055",
  "work/lean/SM/CrossingPair.lean": "d8e3c78897cedbf024c3676b66e529b7a937d991f8839a449b02a1623cf4a933",
  "work/lean/SM/CrossingTransport.lean": "fa4afdc28700747051a62192660556ec1facb1165294f64e3a556dd00f2191fa",
  "work/lean/SM/Crossings.lean": "e337375a30160a74c7c04fdd5d2def19c419afedf189c16f72ce33b814153885",
  "work/lean/SM/CycleMaps.lean": "4abab0e47663f9c0b875a20aeacedff40bd69f4dd49b603484d093d2d27a6eb0",
  "work/lean/SM/CyclicChambers.lean": "4ccfd2ca935569715942948987467564944d4f0946d6ce879fd055f64d08b5e5",
  "work/lean/SM/EuclideanPlane.lean": "30a5956221225bc9811a792b5a67c6c5967fb6dda0b4cb14be997051b32b7a4f",
  "work/lean/SM/G1Consequences.lean": "61debba77e41a48207c8d01bdeb113ee05048ec5f1f8a5868588fcf4601a4763",
  "work/lean/SM/GaussDefinition.lean": "c649abae154373c0ebe7409ac269a847af254bbafa41661e2161cc2304883a6d",
  "work/lean/SM/GaussFamily.lean": "b31d7a22937c5149a951c61a3ac3b8484567d359d4b0625b0067d7da0b59c518",
  "work/lean/SM/GaussFamilyOrder.lean": "51a425eda5dd9bb6fb308353d8be9ad8268aebe01af956d257b987c439ea9276",
  "work/lean/SM/GaussRelabel.lean": "909d3259bc877ab86f19cf34c7eb680d25b5b4acd18c95240e116e1491853e79",
  "work/lean/SM/GaussVisits.lean": "50dbbfa547bf24786d4491717f422aff25e179126e5ccee18146bbe7847e5496",
  "work/lean/SM/GaussWord.lean": "d903156efdddbbe6682eb89d6fe13c2ccc7f02d1f3dde22dc2dc8bbdc936619c",
  "work/lean/SM/Generic.lean": "d66da53bd155faf33a26116324dfe2211e01ac75a8b9f2ccbf028630ee1e6417",
  "work/lean/SM/GenericReversal.lean": "b30ccc14ad30f18eab952178035f8ddbfd7fae2a7507b2522c7f302d49981d01",
  "work/lean/SM/GenericTopology.lean": "040360bc1e5bd08f2fc1c8d4ea1d2d673f83bd59589dd1206c1d9547d51842ea",
  "work/lean/SM/Polygon.lean": "d0b5d37591c252d66e1a3f060cea1e3d58625fedd6c5491cf4c1cf6d2b8c149d",
  "work/lean/SM/PrincipalAngles.lean": "d618c6e2b040d5f5dbaf4b0bc7ef46a565dfb439756587d6f1c83e5c8955672a",
  "work/lean/SM/RegularDefinition.lean": "1abcbd05624a34d5df1963ebef27e1497296f1986b39dd5a635561fed4ce86e1",
  "work/lean/SM/RegularLocus.lean": "ad97d04e3eda38ba6f46d435ee9873344808d0d811ce28c410cd91e35b963acf",
  "work/lean/SM/RegularPairs.lean": "7d09c9ecbb9b2515808d606a060256ee83b744ce42f946c5d9ff9f97ade80a06",
  "work/lean/SM/Reversal.lean": "be95b73303a842c7eefbd41aa0422541e05e97e0a4f4f71f7f06cb070707747b",
  "work/lean/SM/ReversalChambers.lean": "90ada0697719e4fdd3beb2ab749dbac8c050f2552633eb86753a136bb66944fc",
  "work/lean/SM/ReversalCrossings.lean": "3a59986313f843a7bbca5f2093f4db3e73954d9b44d2c9b9a543f28add784f6f",
  "work/lean/SM/RotationNumber.lean": "8d6dc7680484539bf4243b6256155f900061ad34740b29b4f0d0eae6dbd1c0df",
  "work/lean/SM/RotationReversal.lean": "9c66a51229506b886ffc7fa4f9901c483dcb21025009d88a047e05c1ebdadd1b",
  "work/lean/SM/Segment.lean": "40fcfef972866bf0d762b08240941b3f7cd189259692d330709702ad1c9a7465",
  "work/lean/SM/SegmentStability.lean": "9a6cea7cc27227212a23856056f9b07c4a09cc1d48f6f7e214a9381ffc07a0e4",
  "work/lean/SM/ShiftReversal.lean": "9fc4a65c26979463429e81a23ec9869c8b24c0fb9fcca52acff734df4bc0390c",
  "work/lean/SM/SortedCut.lean": "de84127302f1300571e0805e93c1454504da2bf23d09f1ed951da95f44884052",
  "work/lean/SM/Traversal.lean": "3a8494f9376c80e7afbc0e2666bded6763feeec87e1f701db974e73df092acac",
  "work/lean/SM/TraversalRelabel.lean": "a06ef7c15fb0244303882a96dbf3cc3e4ef5b356840dba5590c338e6a25b97ab",
  "work/lean/SM/TurnCountReversal.lean": "a2c139221bffa4e0aeb54707a65e9be0b758ff2fa3741444bef8574dbd2596de",
  "work/lean/SM/VisibleRelabel.lean": "b25f16c1e8df309e3f329c6ea825314a89ccab3886d00e15c0a9b1c06df5de12",
  "work/lean/SM/VisibleSignature.lean": "1a642aceb4a987601b54a6b18da1dca719fad6860918224473e0759e394ee9d7",
  "work/lean/SM/VisitRelabel.lean": "e6c17b7b57552dababf3472ed65f9a9d67b431d413526703ff7032e7e0305174",
  "work/lean/SM/WallSegmentStability.lean": "2780b5212553bca3f703e6c3c9fe37393ebd872ec729980a5eae884039f646aa"
}
```
