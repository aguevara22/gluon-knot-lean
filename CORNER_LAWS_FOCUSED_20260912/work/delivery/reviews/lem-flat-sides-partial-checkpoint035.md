# PARTIAL independent review: flat-side cyclic fusion, checkpoint035

Reviewer: `review_chirotope-independent-20260910`. The reviewer did not author or edit Lean code or the declaration map.

**Verdict: the newly implemented actual cyclic visit-order transport is faithful to the corresponding part of source clause (iii). This is a PARTIAL review, not acceptance of original `lem:flat-sides` or its `flatpr:fusion` alias.** The original row remains pending with blank module/declaration. No original proof/checklist count is added. No full-row semantic acceptance hash or acceptance JSON is issued.

This report extends checkpoint034 and retains the independently reviewed central geometry, local records, actual deletion, central Generic deletion, nearby deleted chambers, crossing/visit bijections, pairing, affine parameters and determinant/positive over-under signs described there. The checkpoint033 and checkpoint034 reports remain unchanged as historical evidence. The global cyclic-order obligation listed as unproved in checkpoint034 is now proved; complete independently formed Gauss-word transport and the full source aggregate remain pending.

## Source and theorem scope

The authoritative source is `reference/SM/sm-1-polygons.tex`, lines 751–893, especially the cyclic visit-order assertion at lines 788–790 and the affine subdivision/order argument in the proof. Its SHA256 is `8bc30167c9cde79c3eb4b9cf52052f81f040ec91490f49517b9f1b7ad0333a00`.

`SM.fusionVisit_cyclic_order` uses an actual parent tuple of size `n+1` with `3 <= n`, covering every source parent size at least four, including four-to-three deletion. The nonzero-size instance is redundant under this bound. Its geometric premises are exactly the singleton central zero point support, strict betweenness of the middle vertex and the absence of remote concurrence triples. The parent crossing geometry and the child's full Generic condition are proved from those premises. The theorem does not assume Generic, G1 or WeakGeneric at the flat parent, and does not evaluate a function restricted to the Generic locus there.

The conclusion compares actual positions of arbitrary three parent visits with their images under the already proved `fusionVisitEquiv`. That equivalence uses the actual crossing-support fusion map and actual visit-edge fibres. The conclusion is an iff of the defined oriented cyclic ternary order, without extra distinctness hypotheses or a restriction to visits on one edge. Equal visits are covered by the strict-order definition. No derivative, transverse-wall or sign-change premise is needed for this central helper. This stronger helper has not been substituted for an accepted full source statement omitting printed hypotheses.

## Scalar compression and actual index calculations

`positiveBend` is the identity below its breakpoint and an affine function of positive slope above it. Its monotonicity proof treats both same-piece cases and the case crossing the breakpoint; the values match at the breakpoint. `fusionKey` adds a second affine piece. With the strict-betweenness parameter strictly between zero and one, the three slopes are respectively one, the first subdivision coefficient and its positive complement. The proof explicitly compares values across the second breakpoint using the value of the first bend there. Thus it proves a genuinely strictly increasing function on the real line, rather than only asserting order for a selected collection of visit keys.

`retained_shift_index` derives the retained parent's shifted cyclic index from the actual deletion-index exhaustion and inverse law. The cut is the old successor of the deleted vertex. It is the cut used by the actual child tuple; it does not reverse traversal or identify unrelated natural representatives of cyclic indices.

`fusionVisitKey_compression` then proves equality of actual numerical keys. The point/parameter transport is supplied by the actual affine middle-vertex identity, and the parent crossing geometry gives strict interior parameter bounds. The proof covers all possibilities for the parent edge:

- On an unchanged edge, the shifted parent label is the inserted image of the child label. The child label is not the final cyclic label. Its natural value therefore leaves at least one further edge before the fused edge, and the strict interior parameter places the key in the identity piece.
- On the first incident edge, both the shifted parent label and child label have natural value `n-1`. The actual parameter lies in the middle piece and is multiplied by the first subdivision coefficient.
- On the second incident edge, the shifted parent label is the last label of the parent, with natural value `n`. The child label is the last label of the child, with natural value `n-1`. Its parameter is the first coefficient plus the positive complement times the old parameter, exactly the high piece of the compression.

The last-index equalities are obtained from the proved natural-value identities and explicit real casts. The argument does not interchange natural subtraction and modular subtraction without justification. The retained-index identity and exhaustive incident-edge cases include every deletion label and all wraparound cases. The strict parameter bounds place actual visits away from the subdivision point; no crossing is silently assigned an arbitrary key at a join.

## Global cyclic order

The proof extracts the actual coefficient and its strict bounds from `StrictBetween`. It uses the compression identity for each actual visit. Strict monotonicity then gives an iff for every pairwise key comparison between child visits and the shifted parent visits. Expanding the defined cyclic order into its three strict-order alternatives proves equivalence of those two cyclic orders.

The last step composes this equivalence with the already proved `traversalBetween_shift` for the complete half-open traversal circle. I reinspected that theorem: it derives the exact shifted key with one modular wrap, uses nonnegativity and the strict upper bound by the parent size, and covers all relative positions against the cut. It applies to arbitrary traversal points and needs no Generic premise. Consequently the final result preserves the original parent's oriented cyclic order, not just the linear order after a convenient unproved relabelling. This proves the formerly missing global cyclic visit-order clause under the actual size-changing fusion equivalence.

## Remaining full-source obligations

The following remain outside this partial certification:

- Prove transport of the complete independently constructed actual Gauss cycle/word under the crossing equivalence, including empty crossing/visit sets and rotation of the changed cut. The new ternary-order theorem alone is not a certified equality of those constructed words.
- Complete any derived fusion interlacement/record transport used by the final aggregate.
- Assemble all three printed clauses on a single genuine smaller interval where required, with the actual continuous curve and source size domain. This must explicitly include that no actual crossing point equals any vertex throughout that interval, in addition to interiority on its two crossing edges and distinct crossing points. Existing central contact lemmas and punctured Generic geometry must be connected to that full statement; it must not be silently dropped.
- Retain the source's actual turn-sign-change hypothesis through the established sign-change predicate and its real-parameter meaning, even where stronger supporting lemmas do not use that premise. Do not replace it by a derivative assumption or an unrelated supplied Boolean condition.
- Compile and audit the complete source-facing aggregate and obtain a new independent full source/type/definition review before accepting the original row.

This review certifies neither the full flat-side source lemma nor any main wall-crossing or soft theorem. The separately recorded original `lem:shift` scope omission is unaffected.

## Current receipt and elaborated-type binding

I verified that `checkpoint-035-output.json` and `stage-development.json` are byte-identical, with `passed=true`, `stage=null`, `stage_accepted=false`, 1413 audited local declarations and 23 mapped claims. The exact 135-module SM inventory matches the receipt. All 141 project-file hashes and all 38 frozen bundle hashes were independently recomputed and matched. Every file in the earlier cumulative 82-file review inventory is unchanged. The original flat-side declaration-map row is still pending and unmapped.

The actual elaborated-type trace was inspected for `fusionVisitKey_compression` and `fusionVisit_cyclic_order`, alongside their current source definitions and proof bodies. The three printed axiom sets, also including `fusionKey_strictMono`, contain only `propext`, `Classical.choice` and `Quot.sound`. The trace's abbreviated implicit geometry proof terms were checked against the actual source code. These build/audit bindings support the independent semantic assessment above; they do not prove the missing source scope.

| Evidence | SHA256 |
| --- | --- |
| `reference/SM/sm-1-polygons.tex` | `8bc30167c9cde79c3eb4b9cf52052f81f040ec91490f49517b9f1b7ad0333a00` |
| `work/checks/checkpoint-035-output.json` | `ed048830165e507b03775c619c6352763929fdf3f44b67e5981891ee1ea71eea` |
| `work/checks/stage-development.json` | `ed048830165e507b03775c619c6352763929fdf3f44b67e5981891ee1ea71eea` |
| `work/checks/declaration-audit.json` | `562261283592b7c1bc4a8767e7a93fa203fc4d8e83639d4bed943f0d08733f87` |
| `work/checks/flat-cyclic-types.log` | `5f731895dc365eca109e8d135ac8a2b8d5baf543b43741043dc86c31759298b6` |
| `work/reviews/lem-flat-sides-partial-checkpoint034.md` | `1088eca7bf7e750e39796459bb8a8e11ac15c53481dfb999d857ea9e46103282` |

## Inspected supporting-file inventory

The new `SM.FusionKey` root has a 55-file local import closure. Its only addition beyond the previously reviewed cumulative inventory is `FusionKey.lean`; all other imported bytes were previously reviewed and were rechecked unchanged. Preserving the full earlier central/local/deletion/fusion scope gives the cumulative 83-file inventory below. Paths are relative to the focused delivery root.

| Supporting file | SHA256 |
| --- | --- |
| `work/lean/SM/AffineSegments.lean` | `6d028816c7e7e5ec6b2cdb440f4ec88b3dc3877ce2b4310d7e2c71234e6d1c58` |
| `work/lean/SM/AffineSubdivision.lean` | `e6c257ae82bdf7e01604cde3791837227bcecc16fe3631828ddac7561fc808b8` |
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
| `work/lean/SM/DeletedTuple.lean` | `b2e591d11b1f25d82511de7979be131fb2158e7bf3a62a0e3e962f1e2cca634c` |
| `work/lean/SM/DeletionChamber.lean` | `62946bca0284ad8c1338f9598f2c62e60e73aaa5537b3f6ba2d3d104392eac47` |
| `work/lean/SM/DeletionG1.lean` | `84dc86e59d7baee28017ae1c01871769a90741aba59002869ccdb40cdc4881b7` |
| `work/lean/SM/DeletionGeneric.lean` | `63ccc4a0c8e2b77f499ca2fd86eb015980d33bfda1dbe5fab5ce47ca320276d3` |
| `work/lean/SM/DeletionIndices.lean` | `15078436d16d1d233a3005ebdd5027156dd36200236a5a7928eef9e4071cec58` |
| `work/lean/SM/DeletionInteriors.lean` | `ea1a88c5ec8367505114f541379f72b5b78a20690b3257d1b44ffb05c1ddfc8c` |
| `work/lean/SM/EuclideanPlane.lean` | `30a5956221225bc9811a792b5a67c6c5967fb6dda0b4cb14be997051b32b7a4f` |
| `work/lean/SM/FiniteChiStability.lean` | `7160db9c4ac930a64c65ce44b9e9a41d4f139a3442a49604b3c96f9a347cadc9` |
| `work/lean/SM/FlatAdjacent.lean` | `bdc87da4c2fec65e0ac63650001b92909b022038843cf71595cad9ba90c6e5e4` |
| `work/lean/SM/FlatCenter.lean` | `8601de7515c59dcde062bd2ce03b426508ceb090519f6068aaadc147cf41bd85` |
| `work/lean/SM/FlatContacts.lean` | `b4bc6e3570f805b18918439bb619aa381e279c49dff4f7984a412b5eead120de` |
| `work/lean/SM/FlatCrossingGeometry.lean` | `75c29f1f94c84360ef95d74de4048461c4bcbdd17cdc072ce934316db15e8c9d` |
| `work/lean/SM/FlatIndices.lean` | `90a47d1bf6650de8f9d4c2a1cda2d3a2cb356a8a7a1a66adfc71570e5b16e866` |
| `work/lean/SM/FlatLocal.lean` | `16620f83ec4a3347da199206170f050116497b90e2b1287ef9a574f7525e6329` |
| `work/lean/SM/FusionCrossings.lean` | `6a390a60d903e68f14f34b7ad6c178be96c01e53c1993d839fcecf23644db296` |
| `work/lean/SM/FusionGeometry.lean` | `a19f835b2c058ef13b81c656fd279ac140f57c9e3d9795f067f820df30ac0aba` |
| `work/lean/SM/FusionIndices.lean` | `6ea253ca0032b57388319e838d7aac9d985ad1144589261a6606ac32dc9f468f` |
| `work/lean/SM/FusionKey.lean` | `df5f8bfe27a65a1f54b54aa58a99c589105b4525fb380c6ee332269bfeba6257` |
| `work/lean/SM/FusionParameterOrder.lean` | `deae7b15552a53a0f3fcd4052d405719a3ca9f9ae80bb3da887ac6a1ad30c2e0` |
| `work/lean/SM/FusionSigns.lean` | `0a265aa5ee995ca9f27413d0dee1b8efe8cd820eb094c833ccaa0b4034b20043` |
| `work/lean/SM/FusionVisits.lean` | `7eedd9d55bc121954e8424ddf9271d97537e2fb327d78dc7b3a18b816f7a19b5` |
| `work/lean/SM/G1Consequences.lean` | `61debba77e41a48207c8d01bdeb113ee05048ec5f1f8a5868588fcf4601a4763` |
| `work/lean/SM/G1CrossingStability.lean` | `0d9f43d0312e6ac03b3616cdcceea5a20e48e189e62d537aa9c34fb0597429b2` |
| `work/lean/SM/GaussVisits.lean` | `50dbbfa547bf24786d4491717f422aff25e179126e5ccee18146bbe7847e5496` |
| `work/lean/SM/GaussWord.lean` | `d903156efdddbbe6682eb89d6fe13c2ccc7f02d1f3dde22dc2dc8bbdc936619c` |
| `work/lean/SM/Generic.lean` | `d66da53bd155faf33a26116324dfe2211e01ac75a8b9f2ccbf028630ee1e6417` |
| `work/lean/SM/GenericCurveChamber.lean` | `deea0d2fba2fcfd533069f8365300248b575db69b161bd900f6a119bdb9853a2` |
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
| `work/lean/SM/InsertedTuple.lean` | `d968ca68c46375a90cad885973bae642d58e212e570b932bb666ecdef2ff7e1c` |
| `work/lean/SM/InsertionIndices.lean` | `c78e97431c61f0ef613e77253d97fe0cb32a888f176bb90fd3fdee8076e73902` |
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
| `work/lean/SM/TripleCenter.lean` | `fb18bd60e87f1cbda15cc963b9738f6b9e2291481f4e73ac5070aebdc63f9dec` |
| `work/lean/SM/TurnSupports.lean` | `dae8e2331c348700930337443fc9af9d1a51d9ca54fc73174265aa5c325aa468` |
| `work/lean/SM/VisitRelabel.lean` | `e6c17b7b57552dababf3472ed65f9a9d67b431d413526703ff7032e7e0305174` |
| `work/lean/SM/WallGerm.lean` | `fca24dab7111c6b6f404b075ab4e1b8c20d2fb48083565b6ba89758ebf684f9b` |
| `work/lean/SM/WallSegmentStability.lean` | `2780b5212553bca3f703e6c3c9fe37393ebd872ec729980a5eae884039f646aa` |
| `work/lean/SM/WeakGeneric.lean` | `1a72ebddb4ddb4d72a89f14a5fede9badc3dbed095a972f6dd1b85db30789b22` |
| `work/lean/SM/WeakGeometry.lean` | `4504cad4539531adc6f8271d30d389c62aa72249e3506cffed0352b73f22bcb2` |
| `work/lean/SM/WeakTopology.lean` | `1a0c7b165f333b81e575c1a0f0bc865d1309f87e752d142c533d7ae0cf038ae2` |
| `work/lean/SM/ZeroTripleRelabel.lean` | `ba2a7a5174923198645d8eed3a0e72bc46ba6d58ce812ee6c81f58fa44f0dae7` |
| `work/lean/SM/ZeroTriples.lean` | `33e64bb519d61fdb2d9e7613cd42af12831246e5774276ca5e2e21f63ea2c23a` |
