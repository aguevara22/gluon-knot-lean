# Cusp integer factors — technical review

2026-09-11. Independent technical/source comparison by another agent of the **same currently available model**. This is **not stronger-model statement-fidelity approval**, and supplies no original-source acceptance. Progress remains 39/192 accepted (20.3%), targets 0/8. Root authored these factors; this reviewer authored the separate cusp affine candidate, which is outside this review's independent scope.

Reviewed all four declarations in `CuspIntegerFactors.body.lean` against the four rows of `afr:s4-table` and its explanation, `reference/SM/sm-2-amplitude.tex` lines 480–502. No mathematical defect was found.

| Declaration suffix | Singleton gap; epsilon pair | U product | V product | Source case |
|---|---|---|---|---|
| `left_leaf_pos_pos` | L; (+,+) | 0 | B_R | incoming, t > 1 |
| `left_leaf_pos_neg` | L; (+,-) | B_R | 0 | incoming, t < 0 |
| `right_leaf_neg_pos` | R; (-,+) | B_L | 0 | outgoing, t > 1 |
| `right_leaf_pos_pos` | R; (+,+) | 0 | B_L | outgoing, t < 0 |

The full names begin `SM.integer_wall_factor_`. Each conclusion is the conjunction of both entries, so the unlisted source summand is explicitly proved zero, rather than merely omitted. No nonvanishing assumption is placed on B; it remains the source's *possibly* nonzero summand.

The proofs use `critical_integer_leaf_values` to replace both U and V on the singleton gap by 1. On the other gap, `boundaryUnitArray_nonleaf_zero` derives E = 0 from the explicit bound of at least two leaves. The definitions then select (U,V) = (E,B) at epsilon +1 and (B,E) at epsilon -1. Multiplication by the leaf value 1 gives exactly the displayed conjunctions, with no sign or factor of two introduced.

Here B is `criticalIntervalIntegerOutput`, an actual integer: on the nonleaf gap it is the rooted tree coefficient of the full `restrictedWordTuple`, at its closing root 0. The singleton zero-support premise and proved exclusion of the critical span supply that tuple's G1; its leaf bound supplies at least three vertices. Earlier proved cast identities identify this integer output with the far-only B output. There is no claim that inverse-array coordinates are integers, and no use of division in these four factor proofs.

The hypotheses are deliberately algebraic/geometric gap data: actual P, physical root g, increasing boundary triple t, its exact singleton zero support, and one leaf/nonleaf count for each gap. They do not assume the cusp law or require a `CuspCase`, nor do they claim to construct epsilon signs. Source n = 4 is included since its nonleaf incident gap has exactly two leaves. No full-span premise is needed for these factor identities themselves. Identifying the gap with the physical deletion polygon, assembling the signed tree response, and proving the rotation/loop normalization remain separate obligations; these four lemmas do not complete `thm:A-S4`.

## Receipt and repair

All **8/8** files in `CuspIntegerFactors-prototype-result.json` match their recorded SHA-256 values. Each of its six body files occurs verbatim exactly once in the passing prototype. Root's second session **35543** exited 0; all four printed axiom traces contain only `propext`, `Classical.choice`, and `Quot.sound`. The passing log contains no `error:`, `sorryAx`, `native_decide`, or `Lean.ofReduceBool`. This reviewer ran no Lean kernel or build.

First session **7575** is preserved with eight unsolved conditional-simplification goals and four downstream `sorryAx` traces. All four declaration types before `:= by` are byte-for-byte unchanged. The only body changes replace limited `norm_num only` calls by `simp` with the closed, kernel-decided fact `(-1 : SignType) ≠ 1`. This resolves the conditional selectors without changing their definitions, domains or conclusions; it is not `native_decide` or an external certificate.

Principal SHA-256 bindings, relative to the focused root:

| File | SHA-256 |
|---|---|
| `work/checks/CuspIntegerFactors.body.lean` | `f34d8db440519782d6e12a16afe9e2146a5ff3d8288fa0267378c800f832429d` |
| `work/checks/CuspIntegerFactors.prototype.lean` | `3570c453f6fe334e0db7ecb5f9ae2adc32c0f64404e8b75b9ad04414cd30efb1` |
| `work/checks/CuspIntegerFactors-second-kernel.log` | `8fff7688b934206a83eda51e7630e9fba7c0a7aa438ac438532405d033f68af0` |
| `work/checks/CuspIntegerFactors-prototype-result.json` | `363f5ace50c3e2cbdb6bc1e7ef9b225225acc7aaeb6470cf2479eaf2f4d71b57` |
| `work/checks/CuspIntegerFactors-first.body.lean` | `70cf20a2caffaafe12a19ba201f4651b3f12103168da41be9ad3dd5df7f8a0c8` |
| `work/checks/CuspIntegerFactors-first.prototype.lean` | `752d720757742a0ed4e51297606264c9f61253d6386a183e25512278acef630f` |
| `work/checks/CuspIntegerFactors-first-kernel.log` | `3de1f0e3278fb3a612f20fe07998c8c79715e4c15cea42612afb816ca822190d` |
| `work/checks/IntegerCriticalGaps.body.lean` | `0ad1c8c46a927d04c736b49f06a092028463264675fd2a2a0d85420f638cba05` |
| `work/checks/FlatIntegerFactors.body.lean` | `b441262771ca2212a4200a18b0dc3f8334cde9180f3085769ccccbeabdbf696d` |
| `reference/SM/sm-2-amplitude.tex` | `014068e2f6e2d86b0ff4edf48877b5967847d661eaae04d2d4c5fd9f54b7c9cf` |

Hash agreement and successful kernel evidence bind the reviewed files without establishing source fidelity. No frozen body, canonical/source file, map or acceptance status was edited.
