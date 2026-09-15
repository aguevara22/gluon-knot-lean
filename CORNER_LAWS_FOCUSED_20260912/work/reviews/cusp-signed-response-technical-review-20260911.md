# Cusp signed and oriented responses — technical review

2026-09-11. Independent technical/source comparison by another agent of the **same currently available model**. This is **not stronger-model statement-fidelity approval**, and supplies no original-source acceptance. Progress remains 39/192 accepted (20.3%), targets 0/8.

Both frozen passing receipts have been verified. The seven statement/proof texts and the applications of their dependencies have been inspected.

Scope: five declarations in `CuspSignedResponse` and two in `CuspOrientedResponse`. No mathematical defect was found in the inspected assembly. This reviewer authored the separate `CuspAffineSigns` and `TurnResponseOrientation` candidates, which root checked/reviewed as nonauthor. Their applications are inspected here, but their proofs are **not independently re-reviewed** by their author.

## Source domain and reuse

The response assumptions are the actual `CuspAt` predicate: parent arity at least four, exactly the unordered neighboring zero triple, no concurrence triple, the cusp vertex outside its neighbors' closed segment, and local turn sign change. There is no assumed affine data, `CuspCase`, `FlatAt`, strict betweenness, rotation formula or response identity. Although `thm:A-S4` explicitly asks that the deletion satisfy G1, these statements derive it from singleton zero support using `g1_deleteVertex`: every retained triple avoids the deleted vertex and therefore the sole zero support. Omitting that redundant caller premise does not narrow the printed domain.

The reused helpers with “flat” in their names have suitable hypotheses:

- `incomingFlatTriple`, `outgoingFlatTriple`, their label/support/interval theorems, and the consecutive-triple bounds are pure cyclic-label and arity statements.
- `CyclicTurnBoundaryOrder` and `flat_boundary_geometric_sign` require only the three cyclic label orders. `flat_boundary_chi_signChanges` transports an actual turn sign-change hypothesis; it does not require a flat germ.
- `incoming_flat_integer_gap` and `outgoing_flat_integer_gap` require the exact singleton zero support. Their full tuple equalities sample every retained vertex and use a cyclic shift of the deletion tuple; no betweenness premise enters.
- `nonincident_flat_contracted_coefficient` uses label bounds, nonincidence, singleton zero support and child arity. Its explicit size reindexing and equality of every tuple entry preserve the actual induced root.

Thus the cusp proof does not invoke the flat response or manufacture a contradictory `FlatAt` hypothesis. The previously proved tree-coefficient shift is applied with its simultaneous root shift; root independence is never assumed.

## Five signed declarations

`cusp_nonincident_signed_response` finds the actual occurrence of j in the root word and proves that it is interior from nonincidence. The constructed consecutive triple has the exact neighboring support, two singleton gaps, and proper span at every allowed arity. It uses the constructed exterior affine coordinate (0,r,1), with r < 0 or r > 1; these inequalities supply every coordinate-separation premise of the integer single-triple response. Both U leaf factors equal 1 for either epsilon sign, so no flat epsilon calculation is imported. The full contracted tuple coefficient is then replaced by the actual center deletion coefficient at `fusionIndex j g`.

`cusp_incoming_signed_response` and `cusp_outgoing_signed_response` use the full-span branch and all four source table rows:

| Root and coordinate range | Cut coordinates; epsilon pair | U product + V product |
|---|---|---|
| incoming, r < 0 | (r,1,0); (+,-) | B_R + 0 |
| incoming, r > 1 | (r,1,0); (+,+) | 0 + B_R |
| outgoing, r < 0 | (1,0,r); (+,+) | 0 + B_L |
| outgoing, r > 1 | (1,0,r); (-,+) | B_L + 0 |

The nonleaf gap has m+2 leaves, including two when the parent has four vertices. The exact integer gap theorem identifies B with the deletion tuple at its induced fused root. These reductions preserve the coefficient's integer domain and introduce neither division nor a nonvanishing assumption.

`cusp_incident_signed_response_all_sizes` constructs m with n = m+3 from the bound in `CuspAt`, then covers g = j-1 and g = j. `cusp_signed_response_all_roots` splits on incidence to cover the complementary roots too. Accordingly the parent parameterization n+1 and internal m+4 forms leave no size restriction beyond the source bound; `[NeZero n]` follows from the resulting child bound n ≥ 3.

Every signed conclusion chooses a single d in {-1,1} and a positive radius bounded by the germ radius before quantifying independent negative/positive parameters. The reverse-ordered far sign is exactly minus the neighboring turn in every cyclic cut. The same d appears in the doubled signed turn difference and actual integer amplitude difference; the center output and physical root remain fixed.

## Two oriented declarations

`cusp_negative_minus_positive_near` applies the generic orientation theorem to the actual integer coefficient on punctured points. Its total-function extension assigns 0 at the center, but all uses are under proved nonzero parameter hypotheses, so that arbitrary center value is never evaluated in the conclusion. Fixed d, common radius, independent-pair response and both actual turn values are all supplied.

`cusp_negative_minus_positive` removes proximity by independently choosing nearby points on the same generic sides with their entire chirotopes unchanged. It transfers the neighboring turn using the relevant triple and the actual rooted coefficient using `treeCoefficient_eq_of_chi`. It assumes no coefficient constancy or desired wall identity. Every original parameter may lie anywhere in the punctured germ interval; no symmetric sampling or hidden local bound remains. The sign selectors are nonvacuous under the cusp turn sign-change condition: `turn_signChanges_opposite` and the two nonzero sign cases put -1 and +1 on opposite sides.

The final sign is negative-chirotope coefficient minus positive-chirotope coefficient equal to the positive deletion coefficient, equivalent to the source's consecutive signed identity. **This is not yet the full displayed cusp law:** identifying loop/no-loop sides and proving their actual rotation difference κ in {-1,1}, with the factor -κ, are separate remaining obligations. No such rotation assertion is silently assumed here.

Compared source: `reference/SM/sm-2-amplitude.tex` lines 456–502 (cusp hypotheses and signed table argument), with the physical deletion map at 380–386 and `sm-1-polygons.tex` named cusp predicate. The subsequent rotation argument at 503–520 remains outside this review's theorem scope.

## Checked evidence

All **51/51** signed-response manifest hashes match current files; every listed body occurs verbatim exactly once in the prototype. Root's first session **30121** exited 0. The five printed declarations depend only on `propext`, `Classical.choice`, and `Quot.sound`; the passing log contains no `error:`, `sorryAx`, `native_decide`, or `Lean.ofReduceBool`. This reviewer ran no Lean kernel or build.

All **52/52** oriented-response manifest hashes also match current files, with every listed body embedded verbatim exactly once. Root's first session **95209** exited 0. Both printed declarations have the same foundational-only axiom set, and its log contains none of the four error/forbidden markers above. The reviewed oriented body is unchanged from the inspected candidate.

Principal SHA-256 bindings, relative to the focused root:

| File | SHA-256 |
|---|---|
| `work/checks/CuspSignedResponse.body.lean` | `3e0d834d2bbe56bed3cf16ec9eb353d18382bb564d5c2da26a7fa0bdeebc2c5f` |
| `work/checks/CuspSignedResponse.prototype.lean` | `251b2466d0101a93819600469bd18aa9bc7ac5d2debbc0294e6f3437f94da70b` |
| `work/checks/CuspSignedResponse-first-kernel.log` | `78e2b17b51a7036f8b50cf1055130140557f52634f4c5829f1e2984ba3542030` |
| `work/checks/CuspSignedResponse-prototype-result.json` | `e40c5b239829594a459e41f34a1fafbdf5b75528189fdea098280f0f693c1c29` |
| `work/checks/CuspOrientedResponse.body.lean` | `af7e475e33378769092ce87bb499bd3aa3ac9ff8bcd6b9dca468326fa8aa0c34` |
| `work/checks/CuspOrientedResponse.prototype.lean` | `779fc6f4a25fb828adcd773c94a065d0368040fe98c2f46b57425cec5191a541` |
| `work/checks/CuspOrientedResponse-first-kernel.log` | `4b26576ac4976a494f4b07afea0044b62aef22c9ffbca8a3ca2c240b16722740` |
| `work/checks/CuspOrientedResponse-prototype-result.json` | `ffb5fbce1fdf70abf0d4e11b015caeb360122f0720e7aca23f576c97f722f97b` |
| `work/checks/CuspAffineSigns.body.lean` | `e7ad55db9a7bca0fa2be15ffe982da0dfed607e8b6a8312331c124803b991945` |
| `work/checks/CuspIntegerFactors.body.lean` | `f34d8db440519782d6e12a16afe9e2146a5ff3d8288fa0267378c800f832429d` |
| `work/checks/IncidentFlatGapTuples.body.lean` | `1b7035b83d8b6d8f91118233ecb3140bae49465bd715ba28a507077371106915` |
| `work/checks/NonincidentFlatContraction.body.lean` | `6c728f41bf8b741a46fc3566c2270c457555546793b17c3e66b9f84eca15a7e1` |
| `work/checks/FlatAffineSigns.body.lean` | `cae5189896235fe01203b831cb1f390cf315fcd3cbaa42b831ba1ceb0ac9e07b` |
| `work/lean/SM/CuspDefinition.lean` | `af2d8abcea1c4ac66b975b22e5d79d4c1e95a44e271923bb8323ab4a1a105bda` |
| `work/lean/SM/DeletionG1.lean` | `84dc86e59d7baee28017ae1c01871769a90741aba59002869ccdb40cdc4881b7` |
| `reference/SM/sm-2-amplitude.tex` | `014068e2f6e2d86b0ff4edf48877b5967847d661eaae04d2d4c5fd9f54b7c9cf` |

Hashes and kernel receipts bind checked artifacts without establishing statement fidelity. No frozen body, canonical/source file, map or acceptance status was edited.
