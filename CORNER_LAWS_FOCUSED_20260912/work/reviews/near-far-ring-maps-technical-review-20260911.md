# Near/far ring maps: technical review

Independent technical/source comparison by another agent of the **same currently available model**, not the author of NearFarRingMaps. This is **not the stronger-model statement-fidelity approval requested by the user**, and no source claim is accepted. No Lean/kernel/build/audit or frozen-file/map edit was performed.

Read all eight declarations, the actual near/far transform, inverse and output definitions, and canonical map_triangularInverse including its termination argument. Compared their role with the constant lifts and polynomial specializations used in `reference/SM/sm-2-amplitude.tex:845–984`. No mathematical or coefficient-domain defect was found.

- `ringHom_map_half` holds for arbitrary unital ring homomorphisms between the stated commutative rings, with invertible two in each. Mapping the actual inverse equation shows that the image of the source half multiplied by target two is one. Multiplying this equation by the target inverse identifies the two inverses. This uses unit multiplication, not a domain cancellation law: zero divisors, noninjective maps, and the trivial ring are not excluded. No numerical field division or unproved choice of compatible inverse instances is assumed.
- `map_nearFarWeight` maps each actual cut factor, its subtraction and half, and the complete finite cut product. `map_nearFarTransform` maps the complete composition sum and all actual child-coordinate products. Empty products and the unary term remain in the same indexing domain. The geometry and interval labels are unchanged by the scalar map.
- `map_boundaryUnitArray` maps the actual one-leaf branch to one and every other branch to zero; the branch test depends only on natural endpoint positions. `map_farTransform` explicitly identifies the mapped zero near array as the target zero function.
- `map_nearFarInverse` specializes the existing well-founded inverse naturality theorem to the actual mapped near/far weights. That theorem proceeds by the recursive equation, mapping subtraction, sums and products; every recursive child is strictly shorter because the recursion is over nonunary compositions. It does not assume inverse naturality, polynomial equality on evaluations, or injectivity/surjectivity of the ring map as a premise.
- `map_farOnlyCoordinates` maps both the zero near array and the actual boundary unit array before applying inverse naturality. `map_farOnlyOutput` maps the actual reversed far array `-H` and the entire inverse-coordinate function, then applies complete far-transform naturality. Thus the sign and child array in the output are both preserved, for every interval, without a full-root restriction.

These are algebraic naturality identities over unrestricted arrays. In particular, they justify using a constant-polynomial inclusion or an evaluation homomorphism once the silent polynomial arrays have been defined. They do not by themselves show that a formal silent-variable array is constant or that its inverse/output is independent of those variables; that remains the formal-cancellation obligation.

Root second39998 exited0. All 3/3 receipt-bound hashes match; the current body occurs exactly once in its prototype. All eight requested axiom traces contain only propext, Classical.choice and Quot.sound (some use subsets); no error, sorryAx, native_decide or Lean.ofReduceBool marker occurs. The exact first50920 body/prototype/log are preserved. Comparing bodies and prototypes shows only explicit branches in the boundary-unit proof and explicit function equalities for mapped zero, unit-array, negation and inverse-coordinate functions. All eight theorem types remain unchanged.

SHA-256 bindings (relative to the focused root):

| File | SHA-256 |
|---|---|
| `work/checks/NearFarRingMaps.body.lean` | `7a5aaadbc1a8041a39f316fb825632afd3493d892e0722fc32defd8fc64c8f16` |
| `work/checks/NearFarRingMaps.prototype.lean` | `5f3bb4821f0e2ea1b29b78f32860dbbcd12a2129a92fddc18cf643eaa85e4fde` |
| `work/checks/NearFarRingMaps-second-kernel.log` | `6996750b04cc0bc87d432248b7456487de3509c98ba0b2dda42281fba7521bb5` |
| `work/checks/NearFarRingMaps-prototype-result.json` | `837c3254fbe8870fe33943d3e87d6afb1c387c4a7ed1edd5fef75e68b9aa1df9` |
| `work/checks/NearFarRingMaps-first-failed.body.lean` | `15944ea4b5dd3077e12dc9ea52a22670d3b593940bc33283aa093cc591e95c42` |
| `work/checks/NearFarRingMaps-first-failed.prototype.lean` | `2a016311fa7902227d78ac9e661e2bddbcabe013b96d353c295bc631652798b9` |
| `work/checks/NearFarRingMaps-first-kernel.log` | `156b97917ee265f4c5ef31d2c9d1273f82ae9f107c9d1d8b461494aa9a8e4a5f` |
| `work/lean/SM/NearFar.lean` | `3d243e1d12636a02743e0f8dc37e3eecc7d46306fbd3cfca5170fd223ad6fa60` |
| `work/lean/SM/NearFarTriangular.lean` | `851c9d30affbb3d38893bdc72249173f4b830d552768ba04e971e1ee848663b2` |
| `work/lean/SM/TriangularPolynomial.lean` | `ec63d8347f1a639d7f6a9033864ceb09a3e083bf7025a1d19e00624d56b40b67` |
| `work/lean/SM/TriangularInverse.lean` | `c1ad3aab34d9695ee82fa41284461d921125d0d67281c1a67d46cbb48c0f5db2` |
| `work/lean/SM/FarOnlyOutput.lean` | `d773b636e2dc37babf11ae3df6b1eb813f5bc2812ad10f5e9bb76faf7d133aa4` |
| `reference/SM/sm-2-amplitude.tex` | `014068e2f6e2d86b0ff4edf48877b5967847d661eaae04d2d4c5fd9f54b7c9cf` |

Stronger statement/definition fidelity and source acceptance remain pending. Accepted progress is unchanged: 39/192 (20.3%); targets 0/8.
