# Integer factors and incident flat response — technical review

2026-09-11. Independent review by another agent of the **same currently available model**. This is **not stronger-model statement-fidelity approval** and not original-source acceptance. Progress remains 39/192 accepted (20.3%), targets 0/8.

Reviewed: four declarations in `FlatIntegerFactors`, three in `FlatIncidentResponse`, and the single `FlatIncidentAllSizes` wrapper. No mathematical defect was found within their stated scope.

## Technical/source comparison

1. **The factor reductions use the exact integer E/B/U/V meanings.** `boundaryUnitArray_nonleaf_zero` derives nonadjacency from at least two leaves and evaluates E to zero; it requires no inverse over the integers. `integer_wall_factor_two_leaves` invokes the proved formal leaf values and obtains U_L U_R = 1 for arbitrary signs, which includes the source (+,+) case. For a left leaf and right nonleaf at (-,+), U_L is 1 and U_R is E_R = 0, while V_L is 1 and V_R is B_R. The outgoing (+,-) case exchanges left and right. Thus each incident unbarred product is zero and each barred product is the actual nonleaf integer B. No leaf polygon amplitude or inverse-coordinate integrality is introduced.
2. **The assembled hypotheses are exactly the flat-germ inputs used here.** The inspected `FlatAt` definition includes arity at least four, the singleton neighboring-point zero support, empty concurrence set, actual strict betweenness, and the exact local turn sign-change condition. Its `pointZeros` and `concurrences` are the actual center sets. The incoming and outgoing proofs unpack these fields, construct the boundary support/order, obtain a common affine base and nonzero direction from strict betweenness, and use coordinates (r,1,0) or (1,0,r) with 0 < r < 1. Every coordinate inequality and sign-change premise required by the integer single-triple theorem is derived. No response premise or extra geometric genericity assumption is supplied by the caller.
3. **The correct full-span branch is selected.** Both incident triples have full span. The proof specializes the integer response, substitutes the proved epsilon pair, applies the appropriate factor reduction, and replaces the surviving B with the previously proved actual deletion coefficient. The result uses `deleteVertex w.center j`, its G1 proof `g1_deleteVertex`, and precisely `fusionIndex j g`. Both its geometry and coefficients are at the wall center. The closed tuple/fused-root identification is an existing proved dependency, not an assumed identification by endpoints.
4. **The sign and time orientation remain explicit.** The conclusion includes `-turn(sPlus) + turn(sMinus) = 2 * d`, with d an integer equal to -1 or 1. This comes from the same integer geometric-array jump used by the response and the exact identity H = -turn. The amplitude conclusion is positive-time coefficient minus negative-time coefficient equals d times the deletion coefficient. If the positive time side is the source right side (turn -1), the integer jump makes d = 1. If it is the source left side (turn +1), it makes d = -1. Thus the signs are consistent with the source; the theorem deliberately retains the time-side orientation rather than claiming that positive time always means right.
5. **Quantifiers and nonvacuity are preserved.** For each selected incident root, d and a positive radius δ ≤ the germ radius are chosen before both side points. The two conclusions share that radius and that d. The theorem then quantifies over independently chosen negative and positive parameters in the full original parameter interval, imposing only their respective absolute-distance bounds. It does not restrict them to a symmetric pair. These punctured neighborhoods are nonempty because δ is positive; their genericity is derived from `WallGerm.generic_punctured`. The statement does not claim a simultaneously chosen radius for all roots.
6. **Both incident roots and all source arities are covered.** The combined theorem splits the literal incidence disjunction and substitutes the chosen root, preserving `fusionIndex j g`. The all-sizes theorem accepts a parent of arity n + 1 and derives n ≥ 3 from `hf.1`; it constructs the witness m = n - 3 for n = m + 3, substitutes that equality, and applies the normalized result. The caller supplies no size decomposition or additional bound. Parent arity four is included, with triangular deletion. The residual `[NeZero n]` agrees with the derived child bound and excludes no flat-wall case.

The source comparison used `sm-1-polygons.tex` lines 653–668 (`def:germ`) and 710–718 (flat-wall inputs and named side convention), and `sm-2-amplitude.tex` lines 146–165 (`lem:farout`), 380–386 (deletion roots), and 395–452 (`thm:A-S3` and its three cases). Existing `NamedWallPredicates`, `GermDefinition`, `WallGerm`, the previously reviewed integer response, affine signs, gap values and incident tuple identifications were inspected. The dependency chain contains no circular flat-law premise.

**Scope remaining:** these eight declarations establish the incident response in signed time-side form for all source sizes. They do not yet establish the nonincident response, formally convert the incident result into the source right-minus-left equation, or assemble the complete all-root flat law. The two-leaf factor is an ingredient for that remaining nonincident branch.

## Receipt verification and bindings

All **7/7**, **39/39**, and **40/40** file hashes in the factor, response, and all-sizes receipts respectively match current bytes. Every listed body occurs verbatim exactly once in its corresponding prototype. Passing sessions are:

- Factors: root **65014**, first run, exit 0.
- Incident response: root **5174**, second run, exit 0.
- All-sizes wrapper: root **86495**, first run, exit 0; confirmed by root before finalizing this report.

The corresponding passing logs print all four, three, and one declarations, with only `propext`, `Classical.choice`, and `Quot.sound` (or subsets). No passing-log error, `sorryAx`, `native_decide`, or `Lean.ofReduceBool` was found. This reviewer ran no Lean kernel or build.

The response's preserved first session **87626** failed at the singleton-support rewrite and contains downstream `sorryAx`; it is not passing evidence. The successful body adds unfolding of `pointZeros` in those two proof steps and explicitly substitutes g in the final incidence cases. All three declaration statements before `:= by` are byte-for-byte unchanged.

Each receipt hash below binds its complete manifest, including the prototype, passing log, and dependency bodies. Principal SHA-256 bindings (relative to the focused root):

| File | SHA-256 |
|---|---|
| `work/checks/FlatIntegerFactors.body.lean` | `b441262771ca2212a4200a18b0dc3f8334cde9180f3085769ccccbeabdbf696d` |
| `work/checks/FlatIntegerFactors-prototype-result.json` | `7c7a0762de3cdd0349ec465d8e5d1823ce837cbeab1f80c13a4cd6e41ef27bec` |
| `work/checks/FlatIncidentResponse.body.lean` | `d3cce41d8c2e24ac798bfbae8347c212304cc0f2dad2d9518a2830f8065cc728` |
| `work/checks/FlatIncidentResponse-prototype-result.json` | `01ab8dec5a822254cd781e8f52f9bc63eea5404d337b4ebf356f73f7563883a3` |
| `work/checks/FlatIncidentAllSizes.body.lean` | `a7e05d0e989360e364d485e734eefcdf6e9fbc19dc1ba4c6bd5fa7d7663e0ad7` |
| `work/checks/FlatIncidentAllSizes-prototype-result.json` | `6bcb6cd7d4147a1ad9f5c736eb52bad6028b6d8c546acc73a9e13f8ae3cf620c` |
| `work/lean/SM/NamedWallPredicates.lean` | `828a9c5dc91455d6d171a01c0ece96901708dd9720f3a379563850b0a61e7513` |
| `reference/SM/sm-1-polygons.tex` | `8bc30167c9cde79c3eb4b9cf52052f81f040ec91490f49517b9f1b7ad0333a00` |
| `reference/SM/sm-2-amplitude.tex` | `014068e2f6e2d86b0ff4edf48877b5967847d661eaae04d2d4c5fd9f54b7c9cf` |

Recorded checks and hash agreement bind this technical review; they do not establish stronger statement fidelity or source acceptance. No frozen Lean body, canonical file, map, or acceptance status was edited.
