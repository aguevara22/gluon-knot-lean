# Partial independent review of lem:rot — checkpoint 020

Reviewer: `review_chirotope-independent-20260910` (not the Lean author).

**Assessment: the implemented clauses are source-faithful on their stated domains. This is a partial implementation review, not acceptance of the full source lemma.**

Source: `reference/SM/sm-1-polygons.tex`, lines 395–426, with the regular-locus definition and labelled/cyclic-equivariant conventions inherited from the same source.

## Exact supported scope

| Source obligation | Compiled declarations inspected | Assessment |
| --- | --- | --- |
| Actual rotation-number definition | `SM.rotationNumber` | The finite sum of the actual principal turns divided by `2 * Real.pi`. |
| (i) Integer-valued rotation | `SM.sum_principalTurn_coe_angle`, `SM.rotationNumber_integer` | Supported: an actual integer `k` is proved to cast to this real-valued sum. |
| (ii) Constancy on continuous regular paths | `SM.continuous_principalTurn_family`, `SM.continuous_rotationNumber_family`, `SM.rotationNumber_family_constant`, `SM.rotationNumber_path_constant` | Supported under the source's permitted labelled/equivariant reading. The family theorem compares all parameter pairs, and the path theorem exports endpoint equality. |
| (iii), reversal part | `SM.regular_reversal`, `SM.principalTurn_reversal`, `SM.rotationNumber_reversal` | Supported for the actual source reversal, including preservation of the regular domain. |
| (iii), vertex-insertion part | No implementation | **Missing.** No actual insertion construction or corresponding invariance theorem is supplied. |
| (iv) Regular triangles | `SM.regular_triangle_det_ne_zero`, `SM.triangle_turn_det`, `SM.rotationNumber_triangle` | Supported: equality with every actual turn sign, membership in `{1,-1}`, and nonzero rotation. |
| (v) Strict bound | `SM.rotationNumber_strict_bound` | Supported: exactly `2 * abs(rotationNumber P) < n`, with the natural number cast to the reals. |
| Inherited cyclic invariance | `SM.rotationNumber_shift` | Supported for every cyclic shift of the actual tuple. |

## Fidelity reasoning

The inherited `Regular` predicate allows positive collinear consecutive edges and excludes exactly zero edges and negative consecutive multiples. All general rotation claims require this genuine regularity, without a stronger genericity, immersion oracle, chosen angle lift, or pre-assumed integral rotation. The finite-sum declarations use `[NeZero n]`; this covers every source size `n >= 3` and merely extends some helpers to smaller nonzero sizes. The triangle statement fixes the actual type `LabelledTuple 3` and has no additional genericity premise.

For integrality, the principal angle is the argument of conjugate(incoming complex edge) times outgoing complex edge, as already independently reviewed in `def:regular`. The new proof compares it with the difference of the two actual edge arguments in `Real.Angle`. I inspected the pinned Mathlib definition: `Real.Angle` is the additive circle of period `2*pi`, not an arbitrary angle abstraction. Argument multiplication and conjugation yield the difference identity modulo this exact period. Summing telescopes because `i -> i-1` is a bijection of the finite cyclic index set. The inspected `Real.Angle.coe_eq_zero_iff` identifies a zero class precisely with an integer multiple of `2*pi`; division by its proved positive, nonzero period yields the real integer cast. Thus the integer witness is derived from actual edge geometry and the finite sum, rather than obtained by rounding or encoded in the rotation-number definition.

For continuity, the complex coordinate map is continuous in the actual real coordinate topology, and the rotor is its continuous conjugate-product. At each regular pair, the previously proved regular/slit-plane relation supplies exactly the domain on which the inspected Mathlib real-valued argument is continuous. Positive collinear pairs remain inside this domain. The proof does not require a global argument branch for individual edge directions, a uniform angular margin, or any extra hypothesis on the parameter topology. Finite summation and division by the fixed period give rotation continuity for every continuous family whose values are regular. The independently proved integer range is discrete in the real line; preconnectedness then gives equality at every pair of parameters. A genuine `Path P Q` with regularity at every point of the closed unit interval specializes this result, including both endpoints. The family formulation also specializes to the canonical inclusion of the actual regular subtype. Cyclic invariance is separately proved by reindexing the sum using `i -> i+a`, so this uses the source's explicit permission to formalize on labelled tuples with equivariance. There is no separate quotient-path API in these modules, and no unproved path-lifting assertion is being used.

For reversal, the inherited map is exactly `P i -> P (2-i)`, with reversed edge `-edge P (1-i)`. The new proof checks the transformed pair `(-v,-u)`: its dot product and product of Euclidean lengths are unchanged, its determinant is negated, and `-theta` remains in the same strict principal interval. Hence `-theta` satisfies the exact reversed cosine/sign specification. Previously proved existence and uniqueness give both reversed-pair regularity and angle negation. At the polygon level this proves `principalTurn (reversal P) i = -principalTurn P (2-i)`, then reindexes the actual finite sum through the bijection `i -> 2-i`. It correctly proves orientation reversal negates rotation rather than treating reversal as a cyclic shift.

For triangles, the nonzero common determinant is derived from regularity and actual edge closure. If the first two nonzero regular edges had zero determinant, the previously proved zero-angle criterion would make the second a positive multiple of the first. Their closing third edge would then be a strictly negative multiple of the second, contradicting regularity of that next pair. No source noncollinearity claim is silently assumed. `triangle_sum_edges` specializes the previously proved telescoping edge sum, and `triangle_turn_det` verifies in actual coordinates that all three corner determinants coincide. Their nonzero common sign gives a strictly positive or strictly negative principal-angle sum. Integrality together with the independently proved strict bound for three edges forces rotation to be exactly the corresponding integer `1` or `-1`. The final statement relates it to every actual `turn P i`, so it covers source labels 1, 2 and 3 after the usual cyclic residue convention.

The strict bound uses each actual principal turn's strict interval to obtain `abs(turnAngle) < pi`. The sum is strict because the cyclic finite index set is nonempty; the triangle inequality bounds the absolute value of the signed sum by the sum of absolute values. Division by positive `pi` yields exactly the source inequality, without a nonzero-rotation or all-turns-nonzero premise.

No fidelity defect was found in these implemented clauses. This assessment does not remove the following missing work.

## Missing work and acceptance boundary

The insertion half of (iii) is unimplemented. Completion requires an actual new tuple of size `n+1` obtained by inserting an arbitrary strict interior point on an arbitrary old edge, verification that it remains regular, and a proved correspondence showing one added zero principal turn and the transported old turns, hence equality of the actual sums. It must cover the cyclic wrap edge and arbitrary representatives; a desired turn inventory supplied as a premise would not establish the source's insertion assertion.

There is no full `SM` aggregate for `lem:rot` and no accepted/mapped declaration for that row. The declaration-map row is still `pending` with empty declaration and module fields. The declaration audit has no semantic statement hash for `lem:rot`; none is invented here. This report is not an acceptance JSON and must not be used to increment the original proof count, the checklist count, or any fractional count for the full row. Full `lem:rot` remains incomplete until insertion and the complete source aggregate receive independent review. The later `lem:uniformrot`, other source claims, the corner state sum, and the main wall/soft targets are outside this report.

## Verification and bindings

Checkpoint 020 is a passed development audit of 689 local declarations and 17 mapped claims, with `stage_accepted=false`. Its saved receipt equals the current `stage-development.json`. Every receipt-bound project file matches its current hash. The six new reviewed files are unchanged from this review; the eleven inherited local files match earlier independent review inventories. The already accepted regular-definition semantic hash remains `8a62d85fc1d8b3723b863093d7c2b1a555fc3064cd36980a36668c701bc9cfc2`.

I also independently loaded the compiled rotation modules with `lake env lean --stdin`, checked the seven principal theorem types listed below, and ran `#print axioms` on each. All checks completed successfully; each reported only `propext`, `Classical.choice`, and `Quot.sound`: `rotationNumber_integer`, `rotationNumber_family_constant`, `rotationNumber_path_constant`, `rotationNumber_reversal`, `rotationNumber_triangle`, `rotationNumber_strict_bound`, and `rotationNumber_shift`. No Lean or declaration-map file was edited by this reviewer.

Source SHA256: `8bc30167c9cde79c3eb4b9cf52052f81f040ec91490f49517b9f1b7ad0333a00`.

Checkpoint receipt SHA256: `c49bcb2bda4a6241cf95300564a1b754f9b4a896ce040e3ac2bc1e3c0af6db1e`.

Current development receipt SHA256: `c49bcb2bda4a6241cf95300564a1b754f9b4a896ce040e3ac2bc1e3c0af6db1e`.

### Inspected local supporting files

```json
{
  "work/lean/SM/Chirotope.lean": "e0225bc712162273f43269ed764ac4849ae8fcd8798245a367d4262858fbf575",
  "work/lean/SM/EuclideanPlane.lean": "30a5956221225bc9811a792b5a67c6c5967fb6dda0b4cb14be997051b32b7a4f",
  "work/lean/SM/G1Consequences.lean": "61debba77e41a48207c8d01bdeb113ee05048ec5f1f8a5868588fcf4601a4763",
  "work/lean/SM/Generic.lean": "d66da53bd155faf33a26116324dfe2211e01ac75a8b9f2ccbf028630ee1e6417",
  "work/lean/SM/Polygon.lean": "d0b5d37591c252d66e1a3f060cea1e3d58625fedd6c5491cf4c1cf6d2b8c149d",
  "work/lean/SM/PrincipalAngles.lean": "d618c6e2b040d5f5dbaf4b0bc7ef46a565dfb439756587d6f1c83e5c8955672a",
  "work/lean/SM/RegularDefinition.lean": "1abcbd05624a34d5df1963ebef27e1497296f1986b39dd5a635561fed4ce86e1",
  "work/lean/SM/RegularLocus.lean": "ad97d04e3eda38ba6f46d435ee9873344808d0d811ce28c410cd91e35b963acf",
  "work/lean/SM/RegularPairs.lean": "7d09c9ecbb9b2515808d606a060256ee83b744ce42f946c5d9ff9f97ade80a06",
  "work/lean/SM/RegularTriangle.lean": "f57e8ad619b28abffc5b94c0e70e623685b116bc95346f19c0653c999c98215d",
  "work/lean/SM/Reversal.lean": "be95b73303a842c7eefbd41aa0422541e05e97e0a4f4f71f7f06cb070707747b",
  "work/lean/SM/RotationBounds.lean": "ef8a6e795cae03b9c4fc7a1a41f0e2b3e0e709b78ec6ce9f36d620608d3ac84f",
  "work/lean/SM/RotationContinuity.lean": "bf50759ea133797a9261172c39e32e551bb40b23dfed483b8c541524d3c6c005",
  "work/lean/SM/RotationNumber.lean": "8d6dc7680484539bf4243b6256155f900061ad34740b29b4f0d0eae6dbd1c0df",
  "work/lean/SM/RotationReversal.lean": "9c66a51229506b886ffc7fa4f9901c483dcb21025009d88a047e05c1ebdadd1b",
  "work/lean/SM/RotationTriangle.lean": "d03c49fc16b070068c0e53a5df5e88c63577b95e1a973e018470b9899c3849f4",
  "work/lean/SM/Segment.lean": "40fcfef972866bf0d762b08240941b3f7cd189259692d330709702ad1c9a7465"
}
```

### Pinned Mathlib files additionally inspected

These hashes record the library source consulted for the angle-period and argument facts; they are not additional source claims.

```json
{
  "work/lean/.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Trigonometric/Angle.lean": "6aa97be3dcd9fe78f0c06119c28a717792dc2c1e023794d3b5bbeca8cd933e89",
  "work/lean/.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Complex/Arg.lean": "1d5235cf145b64f8fd01c81ac7d3d6080b595fd6e1eb8abb06cbdc53e113fbce"
}
```
