# Independent PARTIAL review: flat-side deletion and fusion, checkpoint034

Reviewer: `review_chirotope-independent-20260910` (independent of the code author).

**Verdict: the inspected deletion, genuine chamber, crossing/visit bijection, affine-parameter, pairing, sign and within-piece-order results are sound and faithful to the corresponding parts of source clause (iii). This is NOT acceptance of complete `lem:flat-sides`.** Global cyclic-order/word transport across the changed cut and the full source aggregate remain unproved. The original row, including its `flatpr:fusion` alias, remains pending and unmapped. No original proof/checklist count is added, and no whole-row acceptance JSON or semantic acceptance hash is issued.

This report extends the historical checkpoint033 partial review. Deletion, its central Generic property, nearby deleted chambers and the actual fusion crossing/visit bijections were missing at checkpoint033 and are now proved as described below. The earlier report is retained unchanged as evidence for its own checkpoint. Its conclusions about central geometry and local records still apply; its list of then-unproved work should be read with this update.

## Source, domains and concrete deletion

The source is `reference/SM/sm-1-polygons.tex`, especially lines 782–792 and 863–893 of `lem:flat-sides`, under the hypotheses at lines 751–760. The authoritative SHA256 is `8bc30167c9cde79c3eb4b9cf52052f81f040ec91490f49517b9f1b7ad0333a00`.

The new results use parent size `n+1` with child size `n>=3`. This represents every source parent size at least four, including deletion from four vertices to three; it imposes no extra numerical restriction. The nonzero-size instance follows from that bound. The parent is an actual labelled tuple, with exactly the critical unordered zero point support, strict betweenness of the deleted middle vertex, and no remote concurrence triple. Parent G1 or WeakGeneric is not assumed. Sign change is unnecessary for these central ingredients; the full original source lemma has not been replaced or accepted without its printed hypotheses.

`DeletionIndices` defines the actual retained-label embedding, proves it injective, excludes exactly the deleted label, and proves that every other parent label occurs. The child cut starts at the old successor of the deleted vertex and ends at its old predecessor. Away from the child's last edge, successor indices advance by the actual parent successor. The child last edge is therefore the correctly oriented predecessor-to-successor fused segment, including all modular wraparound cases.

`DeletedTuple` is coordinate restriction along this embedding. The edge, point and interior formulas for unchanged edges are exact. The last edge is the actual endpoint difference of the fused segment. `append_deleteVertex` recovers the actual parent tuple after a cyclic shift when the deleted vertex is inserted with its actual affine parameter, and the strict-betweenness corollary supplies that parameter. Thus the implementation does not substitute an abstract shorter polygon or an angle-only model for deletion, and does not reverse the traversal. Coordinate deletion is genuinely continuous.

## Central Generic deletion and nearby chambers

`DeletionG1` proves full child G1: distinct child indices remain distinct under the retained-label embedding, and no child triple can equal the sole central zero support because that support contains the deleted label. This is the source's all-triples genericity, not a guarded list or a parent G1 assumption.

`AffineSubdivision` supplies one of the two open subsegments for an actual interior point of the fused segment different from the middle vertex. It uses the actual affine parameters and their strict inequalities. Its module comment was corrected from “exactly one” to “one of”; the theorem is a disjunction, and the later bijection proof does not assume exclusivity from this helper.

`DeletionInteriors` excludes the middle parent vertex from every unchanged child edge using the proved nonincident closed-segment exclusion. Every other child interior point lifts to an actual parent interior: unchanged edges have their retained parent label, and the fused edge has the two incident parent labels as alternatives. `DeletionEdgeLift` is a genuine index relation; one parent label cannot lift two different child edges. It does not falsely claim that the fused child edge has only one possible parent label.

`DeletionGeneric` explicitly handles the point at the deleted middle vertex. A hypothetical concurrence of three distinct child interiors includes an unchanged child edge, which excludes that point. Every other common point lifts to three parent interiors, and distinct child edges give distinct parent labels by the lift relation. The already proved full central parent G2 then rules this out. Combined with the retained-triple argument this proves actual central child Generic, without using the fusion crossing bijection circularly.

`GenericCurveChamber` uses openness of the actual Generic locus at the central child tuple and continuity of the actual curve. On a smaller genuine real interval its lift to the Generic subtype is continuous and has connected range containing the central child. Both the labelled range and its actual cyclic-quotient projection therefore lie in their corresponding connected components. `DeletionChamber` applies this to coordinate deletion along the original germ. It gives one positive radius, bounded by the original radius, covering every parameter with small absolute value, including zero and both sides. The chambers are actual connected components, not chirotope classes or assumed record equivalence classes.

## Actual fusion crossing and visit bijections

`FusionIndices` is the total edge map induced by deletion. It sends both parent incident edges to the child's closing edge and assigns every other edge its unique retained child label. Its lift characterization and inverse identities were checked. The map cannot identify the two edges of a remote parent pair, because its only nontrivial fibre consists of the two adjacent incident edges. The proof does NOT falsely assert that every remote parent pair maps to a remote child pair.

`FusionGeometry` proves exact positive edge-scale and affine point formulas. The first incident edge uses the first portion of the fused edge; the second incident edge uses the offset second portion; all other edges retain their parameter. Strict betweenness makes both scales positive, and actual parent interior parameters map to child interior parameters. These are vector/point identities for the actual tuples, not prescribed abstract crossing coordinates.

`FusionCrossings.isCrossing_fusion` maps the actual parent crossing support by this edge map. Its actual common interior point maps into both child interiors, and the child G1 condition plus distinct image labels proves that those images are remote. This geometric argument also prevents losing an actual crossing through an exceptional neighbouring pair; image remoteness is derived only for genuine crossings.

The constructed map preserves the exact actual crossingPoint: the parent point lies in every image segment, and the proved child crossing geometry gives uniqueness. Injectivity then follows from child-image point equality and the proved parent crossing-point injectivity/G2. In particular, two different parent crossings on the first and second pieces cannot be silently merged into one child support. This proof does not presuppose unique choice of a subdivision branch.

For surjectivity, an actual child crossing has interior visits on two distinct edges. At least one edge is unchanged, so its crossing point cannot be the deleted middle vertex. Lift the point to parent interiors, use the lift relation to prove the parent labels distinct, and derive their remoteness from the actual flat-parent adjacent-edge geometry. The resulting genuine parent crossing has exactly the required image support. `fusionCrossingEquiv` packages this explicit forward map and its proved bijectivity. No oracle inverse or supplied crossing correspondence is assumed.

`FusionVisits` proves that the edge map is injective on each crossing's two incident labels, hence gives an actual equivalence of its visit fibres. Combined with the crossing equivalence this produces the full sigma-visit equivalence. Its crossing projection and edge projection are the specified fusion maps; equality of crossing projections is preserved in both directions, which is precisely preservation of the two-visit pairing. Both occurrences of every crossing remain present and distinct.

The parameter formula is proved from the actual crossing-point equality and injectivity of the child edge parametrization. Its explicit affine parameter premise is the real identity supplied by strict betweenness, not an extra geometric assumption; the unique parameter with strict bounds is available from that same source hypothesis. The first-piece parameter is multiplied by its positive coefficient, the second-piece parameter is offset by the first coefficient and scaled by the remaining coefficient, and unchanged-edge parameters remain unchanged.

## Signs and proved order scope

`FusionSigns` proves the actual direction determinant changes by the product of two strictly positive edge scales. Thus the existing directed crossingSign is unchanged, and positivity of the parent determinant is equivalent to positivity of the fused determinant. The source's positive over/under convention uses this determinant sign; no opposite bracket convention or hidden edge reversal is used. The identities hold for arbitrary edge arguments, and in particular for the actual corresponding crossings.

`FusionParameterOrder` proves strict monotonicity of every individual affine parameter map and the exact comparison equivalence for any two actual visits on the same parent edge. It also proves that every actual first-piece visit precedes every actual second-piece visit after fusion: the first mapped parameter lies below the subdivision coefficient, and the second lies above it, using the strict interior bounds of the actual parent crossing parameters. Equal-partner/order edge cases are not silently excluded from the same-edge statement.

These are genuine local order results. They do NOT yet prove preservation of the complete cyclic order between arbitrary visits on different parent edges after changing both the vertex count and the numerical cut. Nor do they establish equality of the complete independently sorted words modulo rotation under the fusion equivalence.

## Remaining work and acceptance boundary

The following still require actual proofs before original `lem:flat-sides` can be accepted:

- Global cyclic visit-order transport through the size-changing fusion map, with the old and new cuts handled correctly.
- Transport of the complete actual Gauss cycle/word under the proved crossing equivalence, and any derived interlacement transport required by the final formulation.
- A full source-facing aggregate covering every original clause, the source vertex-count domain and all printed hypotheses, with one common shrunk interval where the clauses require it.
- A final successful candidate audit and independent full source/type/definition review bound to that aggregate.

The current crossing/visit bijections, pairing, signs, affine parameters and deleted chamber must not be misreported as that missing global cyclic proof. This partial report neither accepts nor counts the original row or any main wall-crossing/soft theorem. The historical unsupported original `lem:shift` is unaffected.

## Receipt and elaborated-type binding

Candidate `work/checks/checkpoint-034-output.json` is identical to `stage-development.json`, with `passed=true`, `stage=null`, `stage_accepted=false`, 134 SM modules, 1396 audited local declarations and 23 mapped claims. I independently verified the exact 134-module inventory, all 140 receipt project-file hashes and all 38 frozen bundle hashes. Every file in the checkpoint033 partial inventory remains unchanged. The original `lem:flat-sides` declaration-map row remains pending with blank module/declaration.

The actual elaborated-type trace was inspected for central deletion Generic, the genuine chamber theorem, both equivalences, actual visit parameters, pairing, both proved order statements and positive over/under transport. The printed axiom sets for the seven traced declarations are exactly `propext`, `Classical.choice` and `Quot.sound`. The whole-project audit passed. These checks bind the independent source/body review; successful compilation alone does not certify missing mathematical scope.

| Evidence | SHA256 |
| --- | --- |
| `reference/SM/sm-1-polygons.tex` | `8bc30167c9cde79c3eb4b9cf52052f81f040ec91490f49517b9f1b7ad0333a00` |
| `work/checks/checkpoint-034-output.json` | `9b157769fd4d892423f8b1df881bf376149fd6011a8f3ed2df818baaa1c1ca36` |
| `work/checks/stage-development.json` | `9b157769fd4d892423f8b1df881bf376149fd6011a8f3ed2df818baaa1c1ca36` |
| `work/checks/declaration-audit.json` | `518eb3806b0f6b30d7c05b109bf348e63025a6d758d2bad0b29ba309f9b14a0a` |
| `work/checks/flat-deletion-types.log` | `c6e3870976dfd24b98584748d2628613957ccbf9646a1e25dd1b7d391313e8e5` |
| `work/reviews/lem-flat-sides-partial-checkpoint033.md` | `03ad30f1ec92df75921b7c7a2d81e281f8bbba0a1841486551c5ba9472fbc3f8` |

## Inspected supporting-file inventory

The new deletion/fusion roots (`SM.DeletionChamber`, `SM.FusionParameterOrder`, `SM.FusionSigns`) have a 64-file local import closure: fourteen new modules and fifty inherited files. Preserving the complete earlier `SM.FlatLocal` closure gives the cumulative 82-file inventory below: fourteen new modules and sixty-eight unchanged previously reviewed files. All current hashes were checked. Paths are relative to the focused delivery root.

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

Only this partial report was written. No Lean source, frozen reference or declaration-map file was edited.
