# Independent PARTIAL review: flat-side local geometry, checkpoint033

Reviewer: `review_chirotope-independent-20260910` (independent of code author).

**Verdict: the inspected local geometry and record-persistence results are sound and faithful to the corresponding portions of the source. This is NOT acceptance of the complete original `lem:flat-sides`.** The source row, including its `flatpr:fusion` alias, remains pending and unmapped. This report adds no original proof or checklist count. It is not a `verdict=faithful` acceptance JSON for that row.

## Source and exact reviewed scope

The authoritative source is `reference/SM/sm-1-polygons.tex`, lines 751–893: central flat geometry, all crossing records, and actual deletion/fusion. Its SHA256 is `8bc30167c9cde79c3eb4b9cf52052f81f040ec91490f49517b9f1b7ad0333a00`.

The current partial aggregate is `SM.flat_germ_local_data` in `SM.FlatLocal`. I inspected its source, proof and elaborated type, together with all twenty new supporting modules and forty-four unchanged previously reviewed local imports. Its actual assumptions are the inherited natural vertex count with at least four vertices, an actual continuous wall germ, the singleton critical point-zero support, strict betweenness of the critical middle vertex, and absence of central remote concurrence triples. The `NeZero` instance is redundant under the size bound. It does not assume central G1, central WeakGeneric, supplied crossing records, a derivative, or transversality of the germ. The printed sign-change hypothesis is not needed for these stronger local ingredients; omitting it here does not certify a rewritten full source lemma.

The aggregate proves actual central vertex injectivity, all nonzero edges, Regular, exactly the critical zero turn, the strict affine fusion coefficients, and one positive real radius on which every noncritical triple has its constant nonzero central sign and the actual geometric records agree with the centre. Every original interval parameter of absolute value less than that radius is covered, INCLUDING zero. The radius is bounded by the original germ radius. `SM.pointZeroCurveGerm` accepts the raw continuous interval curve and punctured Generic hypothesis from the source and derives nongenericity of the centre from the singleton zero support. Thus using WallGerm has not introduced an extra central assumption or a global extension of the curve.

## Central geometry checked

`SinglePointTriple` proves distinctness of all actual central vertices. If two labels had the same vertex, adding a third distinct label produces the unique zero support; since that support has three elements and the size is at least four, a label outside it produces a second distinct zero support. The contradiction uses the exact all-triples condition. Nonzero edges follow from vertex injectivity and distinct cyclic successor labels.

`TurnSupports` proves that distinct cyclic centres have distinct consecutive three-label supports for every size at least four. The explicit nonzero residues one, two and three handle the size-four and wraparound cases. Consequently only the critical turn can vanish. `StrictBetween` is a genuine strict affine parameter with distinct endpoints; scalar injectivity proves uniqueness. The two real edge vectors have positive coefficients of the actual fused endpoint direction, and their ratio is positive. `FlatCenter` derives true Regular at every corner: the critical corner is positive-flat, while all other corners have nonzero determinant. It also proves the actual principal turn at the critical vertex is zero. This is not an assumed angle inventory.

`FlatIndices` exhausts the edge/vertex triples whose support is the critical triple. They are exactly the right endpoint on the left subsegment's line and the left endpoint on the right subsegment's line. The closed affine-segment arguments in `AffineSegments` put these two vertices outside the corresponding closed subsegments. `FlatContacts` therefore excludes every central vertex from every nonincident closed edge segment, not just its interior.

`SingleTripleTransverse` proves that a remote parallel meeting would force both endpoints of one edge onto the line of the other. The four endpoint indices give two distinct zero point supports, contradicting the singleton condition. Transversality is derived. `FlatAdjacent` handles the actual positive-collinear pair by the intersection of its successive affine subsegments, and every other adjacent pair by its nonzero turn determinant. Distinct adjacent edges meet only at their common endpoint, so their interiors do not meet. Three distinct interiors sharing a point would therefore be pairwise remote; the empty remote-concurrence set then implies the full central G2 condition. None of these arguments falsely asserts G1 or WeakGeneric at the flat centre.

`CrossingGeometry` is an auxiliary domain proved from these flat hypotheses. It requires nonzero edges, actual remote closed meetings that are interior and transverse, and G2. It is also proved for Generic tuples through the existing weak-geometry results. At the flat centre the proof uses the new contact/transversality/adjacent-intersection arguments, not a WeakGeneric premise. All crossingPoint and crossingParameter results use the EXISTING actual crossing support, chosen common point and chosen segment parameter definitions. Their uniqueness, strict interior bounds, and crossing-point injectivity are derived geometrically and from G2. No synthetic crossing relation or arbitrarily assigned point has been introduced.

## Actual records and local persistence checked

`GeometricVisits` places the actual sigma visits at their actual segment parameters in the existing half-open traversal space. Evaluation gives the actual crossing point. Crossing-point injectivity and the incident edge recover the visit, giving an injective traversal key. The complete finite universe of these visits is independently sorted; it is nodup, contains every visit, and has twice the number of crossings. The geometric Gauss word is the rotation cycle of that full list mapped to its actual crossing labels. It is not supplied as input or formed only from selected crossings. Position, key, list and word agree exactly with the accepted Generic definitions whenever Generic holds. Generic functions are not evaluated at the nongeneric centre.

`GeometricParameters` proves the actual chosen crossing parameter equals the existing Cramer formula under CrossingGeometry. Actual central transversality supplies the nonzero denominator, and G2 supplies distinct parameters for different crossing partners on one edge. Continuity is therefore proved at the actual centre, without imposing G1 there.

`GeometricCrossingStability` treats every remote pair, using the previously reviewed segment-stability theorem: disjoint compact segments remain disjoint, and an actual transverse interior meeting persists. Finite intersection supplies equality of the COMPLETE crossing-support predicates in both directions. Thus the proof covers potential nearby crossings absent at the centre, including the exceptional pairs discussed in the source, rather than ignoring them or assuming a fixed support.

`GeometricOrderStability` preserves every same-edge parameter comparison for actual central crossings. Equal partners are explicitly handled; unequal partners use their proved distinct central parameters and continuity. It also preserves the directed determinant signs for every actual crossing. These are exactly the determinant signs in the source's positive over/under convention, not the oppositely signed bracket convention. Equality of complete crossing supports ensures that these assertions cover all nearby crossings too.

`GeometricTransport` uses the existing canonical support equivalence: the finite edge-pair support is unchanged, and the incident edge of each visit is unchanged. This preserves the crossing pairing. Exhaustion by each visit's other partner reduces all same-edge comparisons to the proved parameter comparisons; different-edge key comparisons are preserved directly. `GeometricRecords` proves equality of the independently sorted complete lists from their full bijection and common order, then proves actual Cycle-word transport. This is stronger than merely finding some word with the same letter counts. Empty crossing sets are covered by the same finite-universe construction.

`GeometricInterlacement` uses the actual alternating four-visit condition in the genuine cyclic traversal order. The two visits of each crossing must be distinct, and the crossings must differ. Symmetry, the actual simple graph, exact agreement with the Generic relation/graph, and the canonical transport graph isomorphism are proved. Thus no artificial graph or oracle interlacement predicate replaces the source construction.

`GeometricRecordsAgree` contains complete support equality, full sorted-list equality under canonical visit transport, Cycle-word equality under canonical crossing transport, equivalence of all interlacement pairs, and all crossing determinant-sign equalities. `flat_germ_crossingGeometry` proves the requisite geometric domain at EVERY curve parameter: central geometry at zero, Generic geometry at nonzero parameters. `flat_germ_local_data` intersects the finite noncritical-chi and record neighborhoods, composes with the actual continuous curve, and converts the interval-subtype neighborhood into a single absolute-radius condition. The result includes both punctured sides and the centre. Its noncritical determinant signs and records are compared with the same central tuple, not separately with unrelated representatives.

## Work not certified and still missing

The full source lemma is NOT established or accepted. In particular, the strict positive vector fusion identity is only part of clause (iii). The following requested mathematics is still absent from this implementation checkpoint:

- Construction and proof for the actual deleted tuple, including its central Generic property.
- The actual crossing bijection obtained by replacing either incident edge label with the fused edge, including exclusion of collisions and of crossings at the deleted middle vertex.
- Transport through that size-changing deletion/fusion map of cyclic visit order, pairing, interlacement where required, determinant signs, and positive over/under data.
- Genericity of nearby deletions and their membership in the actual chamber of the central deletion on one smaller interval.
- A complete source-facing aggregate covering every clause under the exact printed hypotheses, followed by full independent source review.

This report records the current local geometry, crossing-record extension and persistence. It does not turn the partial aggregate into acceptance of a whole original row, a named-wall law, any corner-state-sum wall-crossing law, or the soft theorem. All helper results remain uncounted as additional original claims.

## Compilation and receipt binding

Candidate `work/checks/checkpoint-033-output.json` is identical to `work/checks/stage-development.json`. The checked receipt has `passed=true`, `stage=null`, `stage_accepted=false`, 120 SM modules, 1302 audited local declarations and 23 mapped claims. I independently verified all 126 project-file hashes and all 38 frozen bundle hashes in this receipt against current bytes. The declaration map still has `lem:flat-sides` pending with blank module/declaration; no full-source semantic acceptance hash is issued by this partial report.

The elaborated-type trace confirms the actual partial-aggregate domain and conclusion, and the raw-curve bridge. Its printed axiom sets for `SM.flat_germ_local_data` and `SM.geometricInterlacementTransportIso` are exactly `propext`, `Classical.choice`, and `Quot.sound`. The successful whole-project audit reports only the permitted standard axioms. Hashes and builds bind the independent mathematical review above; they are not its substitute.

| Evidence | SHA256 |
| --- | --- |
| `reference/SM/sm-1-polygons.tex` | `8bc30167c9cde79c3eb4b9cf52052f81f040ec91490f49517b9f1b7ad0333a00` |
| `work/checks/checkpoint-033-output.json` | `e63c292ddc011cbab3f6863976ea0a002d213211bd4ac1f07cf5bf0ca69a265b` |
| `work/checks/stage-development.json` | `e63c292ddc011cbab3f6863976ea0a002d213211bd4ac1f07cf5bf0ca69a265b` |
| `work/checks/declaration-audit.json` | `a8682b45698d4ba86ac94652c4e63e739575c0bd15f4efa5769621c0d03b4cfa` |
| `work/checks/flat-local-types.log` | `ed7bd2c033262c4f6c7b7903d294caecbee5809c747401b11981fb4434ffc035` |

## Inspected local supporting-file inventory

The full import closure of `SM.FlatLocal` contains 64 local files: twenty new files inspected in this review and forty-four previously reviewed files whose current bytes match their independent review inventories. Paths below are relative to the focused delivery root.

| Supporting file | SHA256 |
| --- | --- |
| `work/lean/SM/AffineSegments.lean` | `6d028816c7e7e5ec6b2cdb440f4ec88b3dc3877ce2b4310d7e2c71234e6d1c58` |
| `work/lean/SM/AngleScaling.lean` | `781af6da4003ffb1d862496edefdc5cb6c0d716d0919d2d547f8df458217465a` |
| `work/lean/SM/ChamberPaths.lean` | `cabb36d739563036aeee39c1a7bc0cf925a6259c5f90a22ecd61c9e2e737d44a` |
| `work/lean/SM/Chambers.lean` | `595dbb81227c5e368a9aaa696d6a609338961899c3c948590ab6a6f94d70ecc9` |
| `work/lean/SM/Chirotope.lean` | `e0225bc712162273f43269ed764ac4849ae8fcd8798245a367d4262858fbf575` |
| `work/lean/SM/ContinuousGeometry.lean` | `61250145831b23c7d8bedc54956643d844bc52ef4ff1ab55b87b81b26cc2000c` |
| `work/lean/SM/CrossingCriterion.lean` | `855c16a0d99ed9abb634a5494f7e30d947d68592d4f2878762b5ecd6c8aef648` |
| `work/lean/SM/CrossingEquiv.lean` | `a505d6a14ecc81ff72512016a68817d70fec010e12722b08f4b6c8b10f132055` |
| `work/lean/SM/CrossingGeometry.lean` | `c349208214f58edda2ec95db5f8ce7229cef89206d2ff45389810c630ea4999d` |
| `work/lean/SM/CrossingPair.lean` | `d8e3c78897cedbf024c3676b66e529b7a937d991f8839a449b02a1623cf4a933` |
| `work/lean/SM/CrossingTransport.lean` | `fa4afdc28700747051a62192660556ec1facb1165294f64e3a556dd00f2191fa` |
| `work/lean/SM/Crossings.lean` | `e337375a30160a74c7c04fdd5d2def19c419afedf189c16f72ce33b814153885` |
| `work/lean/SM/CyclicChambers.lean` | `4ccfd2ca935569715942948987467564944d4f0946d6ce879fd055f64d08b5e5` |
| `work/lean/SM/EuclideanPlane.lean` | `30a5956221225bc9811a792b5a67c6c5967fb6dda0b4cb14be997051b32b7a4f` |
| `work/lean/SM/FiniteChiStability.lean` | `7160db9c4ac930a64c65ce44b9e9a41d4f139a3442a49604b3c96f9a347cadc9` |
| `work/lean/SM/FlatAdjacent.lean` | `bdc87da4c2fec65e0ac63650001b92909b022038843cf71595cad9ba90c6e5e4` |
| `work/lean/SM/FlatCenter.lean` | `8601de7515c59dcde062bd2ce03b426508ceb090519f6068aaadc147cf41bd85` |
| `work/lean/SM/FlatContacts.lean` | `b4bc6e3570f805b18918439bb619aa381e279c49dff4f7984a412b5eead120de` |
| `work/lean/SM/FlatCrossingGeometry.lean` | `75c29f1f94c84360ef95d74de4048461c4bcbdd17cdc072ce934316db15e8c9d` |
| `work/lean/SM/FlatIndices.lean` | `90a47d1bf6650de8f9d4c2a1cda2d3a2cb356a8a7a1a66adfc71570e5b16e866` |
| `work/lean/SM/FlatLocal.lean` | `16620f83ec4a3347da199206170f050116497b90e2b1287ef9a574f7525e6329` |
| `work/lean/SM/G1Consequences.lean` | `61debba77e41a48207c8d01bdeb113ee05048ec5f1f8a5868588fcf4601a4763` |
| `work/lean/SM/GaussVisits.lean` | `50dbbfa547bf24786d4491717f422aff25e179126e5ccee18146bbe7847e5496` |
| `work/lean/SM/GaussWord.lean` | `d903156efdddbbe6682eb89d6fe13c2ccc7f02d1f3dde22dc2dc8bbdc936619c` |
| `work/lean/SM/Generic.lean` | `d66da53bd155faf33a26116324dfe2211e01ac75a8b9f2ccbf028630ee1e6417` |
| `work/lean/SM/GenericTopology.lean` | `040360bc1e5bd08f2fc1c8d4ea1d2d673f83bd59589dd1206c1d9547d51842ea` |
| `work/lean/SM/GeometricCrossingStability.lean` | `6ab1ee43e6c78e74ffd7fd5dc241f138cb5b616f0fd53d5f4149f04f34a1bf7d` |
| `work/lean/SM/GeometricInterlacement.lean` | `1a08a6705fdec2865db346ec69c194dfc18ca554c8e374349a7c06eb61fc320a` |
| `work/lean/SM/GeometricOrderStability.lean` | `0edef9e799a263e9c2b05355aacfa20dfe53dc1724050c2c99e64f30f6c8acb5` |
| `work/lean/SM/GeometricParameters.lean` | `6ded28baebff3627a251fe4eebe931c1f4296945936e175cf6b01b6ad72119a0` |
| `work/lean/SM/GeometricRecords.lean` | `811563881e5504ccf3e7f57c56ddd069ec4f82d13651821f9488adf696d741c9` |
| `work/lean/SM/GeometricTransport.lean` | `d221b0b74905c66f172cac71edc2886f31c81cfa439a6e088ea7bfa754361d21` |
| `work/lean/SM/GeometricVisits.lean` | `0d8bc683744f133dfc38d242b71f87901bad622485b99a3093edaa706d45d579` |
| `work/lean/SM/GermDefinition.lean` | `bd33269270393122371529e33deed075c34348d1a2455537303abc4579206ed8` |
| `work/lean/SM/GermNeighborhood.lean` | `b5b30d800215dde4ff3a11d04b16a261501f6736224807df97a434a2aed0ca5a` |
| `work/lean/SM/GermRelabel.lean` | `6b3b502329e87eb0abd75e9d42cf8cfb41280ee90675b9c0142ac762d337934f` |
| `work/lean/SM/GermSides.lean` | `a95418d15b11a300c5e6a88cbb43ecd9877b5fd061dab754e2efc19eac625d0a` |
| `work/lean/SM/GermSignChange.lean` | `18a9abb6b32839d22aabfdba3e45d533ff515aef021adc6efb5337854be0d91a` |
| `work/lean/SM/InterlaceCount.lean` | `94ba915c268288b5a09ae9062a74fe1f8a2ce9de3f0b45e2ea5f325a057f0f04` |
| `work/lean/SM/InterlaceRelabel.lean` | `4417e63627c398a588a18f169a698909dbda4c0fe1e3f0f22baf10944d52f005` |
| `work/lean/SM/InterlaceSupports.lean` | `2195d77dcf5c15107445ffb98bc74a3b1a2aef3a745afa081eae89b270a7ce3a` |
| `work/lean/SM/Interlacement.lean` | `a762f207004d4f128d4f6b41810c3ea79e273b205a700f356ac73d73678addb9` |
| `work/lean/SM/Polygon.lean` | `d0b5d37591c252d66e1a3f060cea1e3d58625fedd6c5491cf4c1cf6d2b8c149d` |
| `work/lean/SM/PrincipalAngles.lean` | `d618c6e2b040d5f5dbaf4b0bc7ef46a565dfb439756587d6f1c83e5c8955672a` |
| `work/lean/SM/RegularDefinition.lean` | `1abcbd05624a34d5df1963ebef27e1497296f1986b39dd5a635561fed4ce86e1` |
| `work/lean/SM/RegularLocus.lean` | `ad97d04e3eda38ba6f46d435ee9873344808d0d811ce28c410cd91e35b963acf` |
| `work/lean/SM/RegularPairs.lean` | `7d09c9ecbb9b2515808d606a060256ee83b744ce42f946c5d9ff9f97ade80a06` |
| `work/lean/SM/Segment.lean` | `40fcfef972866bf0d762b08240941b3f7cd189259692d330709702ad1c9a7465` |
| `work/lean/SM/SegmentStability.lean` | `9a6cea7cc27227212a23856056f9b07c4a09cc1d48f6f7e214a9381ffc07a0e4` |
| `work/lean/SM/SinglePointTriple.lean` | `5930e77bd3eb05d371b5226c226d9caa464f99d0be48038b1154d02c623dc2c8` |
| `work/lean/SM/SingleTripleTransverse.lean` | `b87c994ee8d533210f16b8ba0c19f53b7ee7b069cfe4cd813a4e84c897fbf72f` |
| `work/lean/SM/StrictBetween.lean` | `8237f0fbd090fd42b15f62c1436cb3ba7f790e921df48d6a9d6a8e4b80becdce` |
| `work/lean/SM/Traversal.lean` | `3a8494f9376c80e7afbc0e2666bded6763feeec87e1f701db974e73df092acac` |
| `work/lean/SM/TraversalArcs.lean` | `293a8a075c368a340c64c763d252e815922cb3a2c915a562ed653bf398bd8800` |
| `work/lean/SM/TraversalRelabel.lean` | `a06ef7c15fb0244303882a96dbf3cc3e4ef5b356840dba5590c338e6a25b97ab` |
| `work/lean/SM/TurnSupports.lean` | `dae8e2331c348700930337443fc9af9d1a51d9ca54fc73174265aa5c325aa468` |
| `work/lean/SM/VisitRelabel.lean` | `e6c17b7b57552dababf3472ed65f9a9d67b431d413526703ff7032e7e0305174` |
| `work/lean/SM/WallGerm.lean` | `fca24dab7111c6b6f404b075ab4e1b8c20d2fb48083565b6ba89758ebf684f9b` |
| `work/lean/SM/WallSegmentStability.lean` | `2780b5212553bca3f703e6c3c9fe37393ebd872ec729980a5eae884039f646aa` |
| `work/lean/SM/WeakGeneric.lean` | `1a72ebddb4ddb4d72a89f14a5fede9badc3dbed095a972f6dd1b85db30789b22` |
| `work/lean/SM/WeakGeometry.lean` | `4504cad4539531adc6f8271d30d389c62aa72249e3506cffed0352b73f22bcb2` |
| `work/lean/SM/WeakTopology.lean` | `1a0c7b165f333b81e575c1a0f0bc865d1309f87e752d142c533d7ae0cf038ae2` |
| `work/lean/SM/ZeroTripleRelabel.lean` | `ba2a7a5174923198645d8eed3a0e72bc46ba6d58ce812ee6c81f58fa44f0dae7` |
| `work/lean/SM/ZeroTriples.lean` | `33e64bb519d61fdb2d9e7613cd42af12831246e5774276ca5e2e21f63ea2c23a` |

Only this partial report was written. No Lean source, authoritative reference or declaration-map file was edited.
