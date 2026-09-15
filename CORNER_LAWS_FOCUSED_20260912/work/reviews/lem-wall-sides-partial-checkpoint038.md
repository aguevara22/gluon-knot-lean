# PARTIAL independent review: named-wall sides, checkpoint038

Reviewer: `review_chirotope-independent-20260910`. The reviewer did not author or edit Lean code or the declaration map.

**Verdict: the implemented named-wall predicates, complete E/C side helpers, and specified V crossing/order/approach helpers faithfully cover the partial source scope detailed below. This is NOT acceptance of full `def:walls` or `lem:wall-sides`.** Both original rows remain pending with blank module/declaration. No original acceptance JSON or whole-row semantic acceptance hash is issued. Helpers and partial clauses add no original proof/checklist count. The main wall laws and soft theorem are not certified.

The authoritative source is `reference/SM/sm-1-polygons.tex`, `def:walls` at lines 710–750 and the complete statement/proof of `lem:wall-sides` at lines 896–1020. Its SHA256 is `8bc30167c9cde79c3eb4b9cf52052f81f040ec91490f49517b9f1b7ad0333a00`. The earlier full flat-side review remains valid and unchanged; this report does not replace it or repeat its original count.

## Named predicates, cyclic indices and central regularity

`NamedWallPredicates` transparently encodes the printed F/V/T/E/C hypotheses on actual WallGerms, retaining the actual local real sign-change conditions. F has the printed minimum size, singleton turn support, empty concurrence set, strict betweenness and actual turn sign change. V uses the four excluded cyclic labels, the exact point-zero support, actual base-edge interior membership and the specified chirotope sign change. Its bigon/sliding split is equality/inequality of the two actual central neighbour signs. E adds actual affine line membership and exclusion from the closed base segment. T has empty point-zero support, exactly the actual concurrence support, and all three actual edge-parameter difference sign changes. The finite concurrence-set meaning forces a genuine three-element remote support; the Cramer parameters are the already proved actual crossing parameters where those crossings exist. The complete T side-swap assembly is not certified by these predicate definitions.

`ContactSeparated` is exactly membership exclusion from the source's four cyclic labels. Under the inherited polygon size at least three, the proof derives at least five vertices by exhausting the smaller cyclic groups; it does not impose this as a new wall assumption. `contactSupport_successive` proves that the only forward consecutive pair in the contact support is its base edge. Thus that support is never a turn support. `contactSupport_vertex_edge` identifies any zero support containing an edge and a nonincident vertex with precisely the specified base edge and contact vertex, including cyclic wraparound.

For C, the singleton point-zero set first forces the written support to have exactly three elements, so repeated labels are not an unnoticed degenerate case. `NoConsecutive S` requires that for every member its successor is outside S. On this actual three-element support this is exactly the source's prohibition of consecutive pairs in either orientation: choosing the predecessor catches either ordering of any adjacent pair. The support and its successor image are disjoint; successor translation is injective; their union has six elements inside the cyclic index set. This proves the source minimum size six, rather than assuming it. A nonincident vertex on an edge would yield the prohibited consecutive pair in the unique zero support, giving full vertex exclusion in C.

`NonFlatCenter` derives every nonzero central turn when the sole zero support is not a turn support. This yields actual nonzero edges and Regular, excluding all antiparallel consecutive directions without assuming G1. To derive full G2 from the empty remote-concurrence set, the proof first shows that distinct edges sharing an interior point must be remote: nonzero-turn adjacent edges meet only at their shared endpoint, which cannot be an interior point of a nonzero segment. Hence a full three-interior concurrence would be one of the forbidden remote triples. V/E regularity and G2 use this derivation; T regularity uses the actual G1 obtained from its empty point-zero set. These helpers do not assert central Generic or global CrossingGeometry for V.

## Complete E/C central and local side helpers

`ContactCenter` classifies every possible nonincident closed-segment vertex incidence as the named pair (M,a). In E, the source's exclusion of M from the actual closed base segment therefore removes every such incidence. This checks the finite segment condition; being on the extension of a supporting line is not confused with being on the segment. Remote parallel segments may remain disjoint. Nonzero determinant is required only when a remote pair actually meets, and its proof derives a contradiction from two different zero triples if a parallel meeting existed.

`SilentCenter` combines this actual geometry with nonzero turns, vertex exclusion and full G2 to derive the complete accepted WeakGeneric predicate for E/C centres. It proves weak geometry throughout the germ: at zero from these source hypotheses, and at every punctured parameter from actual Generic. No generic-locus function is evaluated at a nongeneric silent centre. The centre also lies in the actual silent locus by the WallGerm's derived/recorded nongeneric-centre condition.

`GermChiStability` covers every ordered distinct-label chirotope outside the actual finite central zero set. The implication from not belonging to the zero set to nonzero central chi is proved via the exact triple-membership characterization. Finite continuity then provides one common real radius, not a separate radius for each determinant.

`SilentSides.silent_sides` proves central Regular and one positive radius bounded by the original germ radius. At every original interval parameter with absolute value below that radius, including zero and both sides, it asserts all noncritical chi signs, WeakGeneric, actual CrossingGeometry, injective actual crossing points, inequality of every crossing point with every vertex, every same-edge crossing-parameter comparison, and complete GeometricRecordsAgree. The latter contains all finite crossing-support equivalences, equality of independently sorted complete visit lists, actual Cycle-word transport, actual alternating-visit interlacement and directed determinant signs. The canonical visit map preserves edge labels and crossing projections, hence pairing. All visits and crossings, including empty sets and equal-partner comparison cases, are covered. This supplies the full E/C geometric-record clauses under their printed predicates, while the original lemma with F/V/T remains unfinished.

## V finite-segment crossing test and exact side patterns

`ContactLine` proves the source's affine height identity, direction determinant difference, exact supporting-line foot ratio and its strict interior criterion. It also proves the second separation inequality: the two base endpoints lie strictly on opposite sides of the leg's line at the actual interior contact, because the coefficient is strictly between zero and one and the neighbour height is nonzero. Reversing the incoming leg preserves this product. The supporting Cramer identities retain both segment parameters.

`ContactLegs` uses the actual tail convention: the predecessor leg has label M-1 and neighbour M-1, and the successor leg has label M and neighbour M+1. The contact separation hypotheses prove each leg remote from the base and each neighbour distinct from the critical triple labels. Singleton zero support gives both neighbour signs nonzero. Actual base-interior membership and the derived nonzero base edge supply strict betweenness; the second finite-segment separation product follows for both leg orientations.

`ContactCrossingTest` invokes the full proved two-segment crossing criterion on nearby G1 tuples. One of its two strict separation tests is the height product; the other is the actual base-endpoint product just proved negative at the centre and preserved by continuity. Thus a line straddling alone is not misreported as a finite-segment crossing. Both actual interiors and transversality are controlled. The neighbour chi signs also persist. The resulting actual IsCrossing test is the contact sign times the fixed central neighbour sign being minus one, with the predecessor orientation handled correctly.

`ContactPairGeometry` shows every endpoint incidence in a remote pair makes that support one of the two named contact supports. Any other closed meeting avoids all four endpoints and is therefore in both actual interiors; its determinant is nonzero by the singleton-zero argument. `ContactPersistence` applies disjoint/transverse segment stability to each such pair and then finite simultaneous quantification to all supports. It proves both directions of crossing persistence for every unaffected support, including the impossibility of a new crossing elsewhere, without assuming global central Generic or CrossingGeometry.

`ContactSignPatterns` exhausts the actual three-valued signs under the source real opposite-sign inequality. `ContactCrossingPatterns` uses those identities with the actual crossing tests to prove the exact symmetric difference of the two finite crossing sets, both-or-neither in the equal-neighbour bigon case, and exactly-one/exchange in the unequal nonzero-neighbour sliding case. The wrapper proves the two displayed support pairs distinct. The unaffected-support equality is quantified over all finite supports, not an arbitrary list of known crossings.

`vertex_crossing_sides_local` combines the crossing-test, unaffected-support and actual sign-change radii. `vertex_crossing_sides` then evaluates at a genuine small positive sample and transports crossing predicates along each connected actual Generic side. The arbitrary positive and negative evaluation parameters are independent. Thus the bigon/sliding orientation is fixed on the sides, not a disjunction allowed to change with a paired parameter. This is a proved consequence of the original continuous Generic half-intervals, not an added chamber-constancy premise.

## V persistent parameters, vertices and approach limits

`ContactParameters` derives transverse/interior data for every unaffected actual central crossing and proves its Cramer parameter equals the already chosen geometric crossing parameter. Coincident base-edge parameters for distinct unaffected crossings would give three distinct actual interior incidences; the derived full central G2 excludes them. The Cramer expressions are actually continuous at the centre because their actual determinants are nonzero. No global central CrossingGeometry is assumed.

`ContactOrder` uses these continuities and distinctness for every pair of unaffected persistent crossings on a common edge. Equal partners are handled explicitly. Finite quantification and the actual germ-neighbourhood bridge give one radius for all such strict comparisons, including zero. Together with complete unaffected-support persistence, this accounts for every persistent crossing, not only those selected before the perturbation.

`ContactVertices` treats both possible incident endpoints using nonzero-edge parameter injectivity. If an unaffected persistent crossing point equalled any vertex, its membership in both actual interiors would give two nonincident vertex-edge incidences. The exact contact classification would make both remote edges the same base edge, a contradiction. In particular persistent crossings on the base have parameters different from the actual contact parameter. Persistent crossings on the legs have strict interior parameters and hence differ from the contact endpoint.

`ContactApproach` gives the correct actual endpoint parameter: one on the predecessor leg and zero on the successor leg. At the contact, each leg meets the base at M with nonzero determinant. Exact Cramer equations show the base parameter is the actual coefficient locating M and the leg parameter is that endpoint value. Both functions are continuous at the centre, so for any positive tolerance both approach estimates hold simultaneously for both legs on a neighbourhood. These are honest line-parameter limits even where a contact pair is not a nearby crossing. When it is an actual Generic crossing, the existing proved Generic parameter bridge identifies them with its visit parameters; the future localization assembly must use that bridge rather than silently treating every parameter evaluation as a visit.

## Essential V-centre interpretation boundary

The shared raw `IsCrossing` predicate uses remote **closed** segment meetings. At a V centre its two affected supports meet at a leg endpoint, so they belong to that raw closed-meeting predicate but are not the source's transverse **interior** central crossings. The present persistent-centre helpers correctly and explicitly exclude `ContactAffected`; on the remaining supports they prove actual transverse interior geometry. The nearby side-pattern theorems evaluate Generic tuples, where raw IsCrossing agrees with the source crossing meaning. The approach helpers use total Cramer line parameters at the boundary and do not claim central interior visits there.

This report therefore does not certify the unfiltered raw central crossing set or a full central Gauss word in case V. A later full source aggregate must retain the unaffected/interior restriction at that centre, or prove a separate exact interior-crossing characterization. It must not erase this distinction or infer global central CrossingGeometry from the reviewed helpers.

## Remaining proof and acceptance scope

- Construct finite simultaneous contact neighbourhoods and a common germ radius separating every persistent visit from each contact location, including the base contact parameter and the appropriate leg endpoints.
- Convert actual contact-pair approach estimates into the required actual visit localization whenever those pairs cross, with all relevant comparisons and unchanged order outside the contact neighbourhood. The current convergence and separate order lemmas are necessary support, not the finished localization assertion.
- Complete the T case: actual side order exchanges for exactly the named triangle pairs, their adjacency, and constancy of every other persistent order on a common interval, using all three printed sign changes. A predicate and central regularity alone do not establish this.
- Assemble the complete original F/V/T/E/C wall-sides statement, all its general clauses and genuine central-data conventions, with the appropriate common intervals and then a full successful candidate audit and independent full review.
- Complete original def:walls separately, including K and its newborn/loop/empty conventions, the other named side/contact-sign conventions, mutual exclusivity, centre classification and cyclic compatibility. The current transparent F/V/T/E/C predicates are explicitly incomplete for that original definition row.

No original row is accepted or counted by this partial report. The historical unsupported original lem:shift is unaffected.

## Frozen receipt, type and axiom binding

I independently verified that checkpoint038 is byte-identical to stage-development.json, with `passed=true`, `stage=null`, `stage_accepted=false`, 1632 audited local declarations and 24 mapped claims. The exact 162-module SM inventory matches the receipt; all 168 project-file hashes and all 38 frozen bundle hashes were recomputed and matched. All twenty new modules match the bytes inspected during preliminary source/body review. All 91 files from the previous full flat-side review remain unchanged, including the 58 inherited files used by the present roots.

The actual type/definition trace was inspected for silent_sides, vertex_crossing_sides, persistent parameter order, persistent vertex exclusion and both contact approach estimates, together with the transparent SilentSidesData, VertexCrossingData and V/E/C/T predicates. The five printed axiom sets contain only `propext`, `Classical.choice` and `Quot.sound`. The source/proof bodies were independently reviewed; successful compilation and hashes alone are not treated as mathematical fidelity or closure of the missing scope.

| Evidence | SHA256 |
| --- | --- |
| `reference/SM/sm-1-polygons.tex` | `8bc30167c9cde79c3eb4b9cf52052f81f040ec91490f49517b9f1b7ad0333a00` |
| `work/checks/checkpoint-038-output.json` | `23d75299bbcf8305e314e141e45f43f6f1bade0cf4365f5be74fbe31e30941ef` |
| `work/checks/stage-development.json` | `23d75299bbcf8305e314e141e45f43f6f1bade0cf4365f5be74fbe31e30941ef` |
| `work/checks/declaration-audit.json` | `37a5b6b70f7d28fa7bc8ee1c5e02671664c577a4bba72f5a986d279ae9a1f604` |
| `work/checks/named-wall-partial-types.log` | `bb59fbf90f7167a0b3663efb82f6ecb5b835f9da4029af39284f493102fdced6` |
| `work/reviews/lem-flat-sides.json` | `ed07a0b556323b4409efe25852fb981c5ad58e8167622bd2290d3bf45c643e7a` |

## Inspected supporting-file inventory

The roots `SM.SilentSides`, `SM.ContactCrossingSides`, `SM.ContactOrder`, `SM.ContactVertices` and `SM.ContactApproach` have a 78-file local import closure: all twenty new modules and 58 unchanged previously reviewed dependencies. The complete closure is bound below. Paths are relative to the focused delivery root.

| Supporting file | SHA256 |
| --- | --- |
| `work/lean/SM/AngleScaling.lean` | `781af6da4003ffb1d862496edefdc5cb6c0d716d0919d2d547f8df458217465a` |
| `work/lean/SM/ChamberPaths.lean` | `cabb36d739563036aeee39c1a7bc0cf925a6259c5f90a22ecd61c9e2e737d44a` |
| `work/lean/SM/Chambers.lean` | `595dbb81227c5e368a9aaa696d6a609338961899c3c948590ab6a6f94d70ecc9` |
| `work/lean/SM/Chirotope.lean` | `e0225bc712162273f43269ed764ac4849ae8fcd8798245a367d4262858fbf575` |
| `work/lean/SM/ContactApproach.lean` | `b08d7d8d3baa265919b554047f19e40a46fee7d31ac4de3ab41eae07fa1d6aa6` |
| `work/lean/SM/ContactCenter.lean` | `088773192feb3d06b423eeebc35bbe760577da281f6ffe33093267cc78437e67` |
| `work/lean/SM/ContactCrossingPatterns.lean` | `c66dcf9dfa509276fe78778c513322f4eb30ace6943442977f921c60c54a3c39` |
| `work/lean/SM/ContactCrossingSides.lean` | `eda80e53eaaa89274fbbd22efc40f78252e39f8f071007fe985d4e7b3bfe894e` |
| `work/lean/SM/ContactCrossingTest.lean` | `5ddbebebc2781fc111d1c05cd9fa7eb5026da5dbc45af3ecd2bb1492cf8a2ae2` |
| `work/lean/SM/ContactIndices.lean` | `7c89d34ffd6e6d173d85822fc8138e6f95bc505f8c409b33700d178c86dbc56e` |
| `work/lean/SM/ContactLegs.lean` | `b7c00b8be9cf0615aaf77b34d4f5d7e193b6ebb1647c9646937cada95d0e8b5a` |
| `work/lean/SM/ContactLine.lean` | `0bf010d23bcc7a24c11937c8d4083649ff1870d32e75fc997b15e6f6770d6130` |
| `work/lean/SM/ContactOrder.lean` | `0445421ca8a7a98684d7c37e211234da02bdd732b284d7f8b6f823f31648ef94` |
| `work/lean/SM/ContactPairGeometry.lean` | `1982230c95c9fd92df04916a7ecc32370ed12c4ff4f90b5ebbc57c349f8d871e` |
| `work/lean/SM/ContactParameters.lean` | `1907b361532e09f0f379c267f51ba8cb12c61f24b55fba0b6f09253768d4d224` |
| `work/lean/SM/ContactPersistence.lean` | `ac423123ecb6daf3e123ca979b20f7bda40ab99a6a17c3e12c818a5c0b6e6ef8` |
| `work/lean/SM/ContactSignPatterns.lean` | `31319e456bf39d5c643a5f52cd0d1e796b24d1787eb7601167d40369cde541c6` |
| `work/lean/SM/ContactVertices.lean` | `ff63348364c930f3802aa5c2c2cd315aba37f661de6469638afd8ab087e60854` |
| `work/lean/SM/ContinuousGeometry.lean` | `61250145831b23c7d8bedc54956643d844bc52ef4ff1ab55b87b81b26cc2000c` |
| `work/lean/SM/CrossingCriterion.lean` | `855c16a0d99ed9abb634a5494f7e30d947d68592d4f2878762b5ecd6c8aef648` |
| `work/lean/SM/CrossingEquiv.lean` | `a505d6a14ecc81ff72512016a68817d70fec010e12722b08f4b6c8b10f132055` |
| `work/lean/SM/CrossingGeometry.lean` | `c349208214f58edda2ec95db5f8ce7229cef89206d2ff45389810c630ea4999d` |
| `work/lean/SM/CrossingPair.lean` | `d8e3c78897cedbf024c3676b66e529b7a937d991f8839a449b02a1623cf4a933` |
| `work/lean/SM/CrossingTransport.lean` | `fa4afdc28700747051a62192660556ec1facb1165294f64e3a556dd00f2191fa` |
| `work/lean/SM/CrossingVertexExclusion.lean` | `ca6496cebc2d8d75b723bbe15fa21bb42f582d621853edfc0cb718ad6e538b76` |
| `work/lean/SM/Crossings.lean` | `e337375a30160a74c7c04fdd5d2def19c419afedf189c16f72ce33b814153885` |
| `work/lean/SM/CyclicChambers.lean` | `4ccfd2ca935569715942948987467564944d4f0946d6ce879fd055f64d08b5e5` |
| `work/lean/SM/EuclideanPlane.lean` | `30a5956221225bc9811a792b5a67c6c5967fb6dda0b4cb14be997051b32b7a4f` |
| `work/lean/SM/FiniteChiStability.lean` | `7160db9c4ac930a64c65ce44b9e9a41d4f139a3442a49604b3c96f9a347cadc9` |
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
| `work/lean/SM/GermChiStability.lean` | `612e2c1937a9b4a984f0f8c37b6a59dd724dce1f7dc3ed2d2d48ae5433256bef` |
| `work/lean/SM/GermDefinition.lean` | `bd33269270393122371529e33deed075c34348d1a2455537303abc4579206ed8` |
| `work/lean/SM/GermNeighborhood.lean` | `b5b30d800215dde4ff3a11d04b16a261501f6736224807df97a434a2aed0ca5a` |
| `work/lean/SM/GermRelabel.lean` | `6b3b502329e87eb0abd75e9d42cf8cfb41280ee90675b9c0142ac762d337934f` |
| `work/lean/SM/GermSides.lean` | `a95418d15b11a300c5e6a88cbb43ecd9877b5fd061dab754e2efc19eac625d0a` |
| `work/lean/SM/GermSignChange.lean` | `18a9abb6b32839d22aabfdba3e45d533ff515aef021adc6efb5337854be0d91a` |
| `work/lean/SM/InterlaceCount.lean` | `94ba915c268288b5a09ae9062a74fe1f8a2ce9de3f0b45e2ea5f325a057f0f04` |
| `work/lean/SM/InterlaceRelabel.lean` | `4417e63627c398a588a18f169a698909dbda4c0fe1e3f0f22baf10944d52f005` |
| `work/lean/SM/InterlaceSupports.lean` | `2195d77dcf5c15107445ffb98bc74a3b1a2aef3a745afa081eae89b270a7ce3a` |
| `work/lean/SM/Interlacement.lean` | `a762f207004d4f128d4f6b41810c3ea79e273b205a700f356ac73d73678addb9` |
| `work/lean/SM/NamedWallPredicates.lean` | `828a9c5dc91455d6d171a01c0ece96901708dd9720f3a379563850b0a61e7513` |
| `work/lean/SM/NonFlatCenter.lean` | `79297e5edc3912d5dbaab3583f6e5dbb29f20935f183ace13dcc8c4feeea907b` |
| `work/lean/SM/Polygon.lean` | `d0b5d37591c252d66e1a3f060cea1e3d58625fedd6c5491cf4c1cf6d2b8c149d` |
| `work/lean/SM/PrincipalAngles.lean` | `d618c6e2b040d5f5dbaf4b0bc7ef46a565dfb439756587d6f1c83e5c8955672a` |
| `work/lean/SM/PureCutIndices.lean` | `6ba45cb5653d6d5a768729309e8bb632b73ff1ef3525d347d267c6e06037f426` |
| `work/lean/SM/RegularDefinition.lean` | `1abcbd05624a34d5df1963ebef27e1497296f1986b39dd5a635561fed4ce86e1` |
| `work/lean/SM/RegularLocus.lean` | `ad97d04e3eda38ba6f46d435ee9873344808d0d811ce28c410cd91e35b963acf` |
| `work/lean/SM/RegularPairs.lean` | `7d09c9ecbb9b2515808d606a060256ee83b744ce42f946c5d9ff9f97ade80a06` |
| `work/lean/SM/Segment.lean` | `40fcfef972866bf0d762b08240941b3f7cd189259692d330709702ad1c9a7465` |
| `work/lean/SM/SegmentStability.lean` | `9a6cea7cc27227212a23856056f9b07c4a09cc1d48f6f7e214a9381ffc07a0e4` |
| `work/lean/SM/SilentCenter.lean` | `20fa33f369f6c9f588fb7c94d1828532f12b9c03c08daaae3524b547f5673d5d` |
| `work/lean/SM/SilentSides.lean` | `5a54d3c9592ef6d9862de2badda10a81ba3928d4d5420f81511ce54c6d5ce580` |
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
