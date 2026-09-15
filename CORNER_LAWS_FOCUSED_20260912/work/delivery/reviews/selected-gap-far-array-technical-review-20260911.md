# Selected-gap geometric far array: technical review

Independent technical/source comparison by another agent of the **same currently available model**, not the author of SelectedGapFarArray. This is **not the stronger-model statement-fidelity approval requested by the user**. No source acceptance, Lean/kernel/build/audit run, or frozen-file/map edit was performed.

Compared all six declarations with source `pf:gap-sign-identity`, `reference/SM/sm-2-amplitude.tex:867–902`, and the actual canonical geometricBoundaryArray, boundaryWord and chi definitions. Reviewed the complete InternalGapSigns and selected-coordinate dependencies separately. No mathematical, domain, orientation or cast defect was found.

1. `selectedOuterCutTriple` retains the actual global endpoints `r 0` and `r (Fin.last k)` and the further physical position u. Its increasing bounds follow from strict order of r and the actual strict gap bounds. `selectedGapCutTriple` uses the actual endpoints `r j.castSucc`, `r j.succ` and the same u. Neither definition substitutes neighboring composition cuts for the selected gap endpoints or treats an endpoint identity as a tuple identity.
2. `selected_gap_epsilon_nonzero` derives distinct successive coordinates from injectivity and unequal Fin values, and distinct global endpoint coordinates from `0<k`. Its epsilon is the exact source ratio of those coordinate differences; no positivity or scalar-order restriction is imposed.
3. `weak_selected_gap_far_sign` derives coordinate injectivity from the actual weak polygon and strictly selected boundary positions, then supplies both nonzero coordinate differences to the general internal-gap sign theorem. Its further point u is completely arbitrary. It can be on the common line, off it, or even a selected endpoint; zero far signs are covered. This helper does not require G1 or an externally supplied nonzero line direction.
4. `weak_selected_gap_far_array` adds precisely the strict bounds on u needed to form both increasing triples. Unfolding the actual array reads chi at upper/middle/lower physical boundary labels, exactly the reversed pointFarSign. The equality is the outer geometric array value equal to the integer-cast source epsilon times the gap array value. Sign multiplication is cast into any CommRing; no inverse of two, injective cast, characteristic assumption or ring division is needed.
5. `weak_selected_gap_far_array_of_collinear` constructs all affine point equations from actual determinant collinearity via the previously checked dot-product coordinate theorem. Thus actual WeakGeneric, strict selected positions and determinant zeros suffice; no affine-coordinate oracle remains in this wrapper. The direct affine version still covers every valid initial coordinate choice, including a negative endpoint difference.
6. The source case `k≥2` lies within the helper's `0<k` domain. There is no `n≥4`, distinguished root, full-boundary endpoint, or unique-collinear-triple assumption. One-leaf gaps remain possible in the selected list: there is then no strict internal position u, as appropriate for an empty inner-cut product. No identity on a nonexistent further cut is used to remove such a gap from the later composition domain.

These declarations specialize the sign relation to actual array entries. They do not identify polynomial coefficients, prove the gap-composition factorization, or establish formal cancellation; those remain separate obligations.

Root second3596 exited0. All 9/9 receipt-bound file hashes match and all seven embedded bodies occur exactly once. All six requested traces are present: selectedGapCutTriple has no axioms; the others contain only propext, Classical.choice and Quot.sound. No error, sorryAx, native_decide or Lean.ofReduceBool marker occurs in the passing log. Read-only comparison with preserved first77146 files shows only explicit Fin-value bounds inside the triple's proof fields and an explicitly written target in the cast proof. All declaration types and mathematical triple entries are unchanged; the first run remains failed evidence.

SHA-256 bindings (relative to the focused root):

| File | SHA-256 |
|---|---|
| `work/checks/SelectedGapFarArray.body.lean` | `51a021cbde0a113355cf7657f9a94e331dac24721840692c31afc63c4eabd031` |
| `work/checks/SelectedGapFarArray.prototype.lean` | `862f71a953da5d123093119f1f280ca6e76f2701b5244c3328f42aa33654868e` |
| `work/checks/SelectedGapFarArray-second-kernel.log` | `af61eb00b8b42fef124ebb06b16a2bc414a2cc7541b4c67fdfa00c7746d534f0` |
| `work/checks/SelectedGapFarArray-prototype-result.json` | `b672bec69c1f245b4c22568a875a04665cad04df7158d6ecc44d39e78ca9503c` |
| `work/checks/SelectedGapFarArray-first-failed.body.lean` | `32ead4f2caf17d887e1c14143f5e3da23ab9505d244de8e9defaa4b65d44d317` |
| `work/checks/SelectedGapFarArray-first-failed.prototype.lean` | `170eea0cf5b59471c3bc54b270508009d7b00df3c00d962828fa7e2603448d09` |
| `work/checks/SelectedGapFarArray-first-kernel.log` | `8fcda008a453bef4020b33cd6ed20ee1fe4c3d6f0791d9f3d8e4123ab83ef22c` |
| `work/checks/InternalGapSigns.body.lean` | `09846a9e9beba9fdf6a68b7c7f32e1dfc7c46b3bd12fb3cdfee33d4d67355a6c` |
| `work/checks/LineCoordinateNormalization.body.lean` | `95806b56f50651011b05d31989e3ce43076c9a129ac9a7de6f0f08d903c37797` |
| `work/checks/WeakSelectedLineCoordinates.body.lean` | `a711895a3661f741753269d46d480168b15840561b488d7a8ebd78c17b431d3b` |
| `work/reviews/internal-gap-signs-technical-review-20260911.md` | `50dd4db102bdc1df8968679e6813ad3c54ca17bcd6cd106c8498752fda265c76` |
| `work/reviews/line-coordinate-normalization-technical-review-20260911.md` | `e5d17671f8cb44b3aef304a43f29edceddacf348868fae6d537bb4b40aba6a6d` |
| `work/lean/SM/NearFar.lean` | `3d243e1d12636a02743e0f8dc37e3eecc7d46306fbd3cfca5170fd223ad6fa60` |
| `work/lean/SM/RootBoundary.lean` | `604906b750e1ab198a2db3fc3cc011ab325493a91404a0b52ffe4583dd403f1a` |
| `work/lean/SM/Chirotope.lean` | `e0225bc712162273f43269ed764ac4849ae8fcd8798245a367d4262858fbf575` |
| `reference/SM/sm-2-amplitude.tex` | `014068e2f6e2d86b0ff4edf48877b5967847d661eaae04d2d4c5fd9f54b7c9cf` |

Stronger statement/definition fidelity and source acceptance remain pending. Accepted progress is unchanged: 39/192 (20.3%); targets 0/8.
