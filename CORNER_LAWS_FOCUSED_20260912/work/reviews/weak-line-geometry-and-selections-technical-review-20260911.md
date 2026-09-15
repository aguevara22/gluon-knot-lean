# Weak selected-line geometry: technical review

Independent technical/source comparison by another agent of the **same currently available model**. I did not author WeakLineGeometry or WeakLineSelections. This is **not the stronger-model statement-fidelity approval requested by the user**, and it does not accept a source claim. No Lean kernel, build, or audit was run by this reviewer; no frozen body, canonical module, or acceptance map was edited.

Compared the eight geometry declarations and nine selected-list declarations with `reference/SM/sm-2-amplitude.tex:795–842`, particularly the geometric premises used in both assertions of `pf:line-gap`. No mathematical or domain defect was found in these helper statements.

- Actual vertex injectivity follows from the nonzero-edge and nonincident **closed**-edge exclusions in WeakGeneric. The adjacent successor case gives a zero edge; every other distinct label is excluded from the edge beginning at the second label. Composing with the actual boundary-index injection gives boundary-word injectivity. This does not assume G1 or distinctness as extra data.
- Scalar interpolation uses the directed-edge parameter `(z-x)/(y-x)`. Both signs of the denominator are handled: scalar strict betweenness in either order produces a parameter strictly between zero and one, hence an actual forbidden point of the closed edge. A nonzero line direction is unnecessary for these implications. Three consecutive affine points give the actual zero determinant/turn, contradicting WeakGeneric.
- A selected leaf gap is explicitly the natural-position equation `r(j+1)=r(j)+1`; the boundary-index identity converts it to the actual physical successor. The exclusion quantifies over every selected point, treating its two endpoints separately. Strict monotonicity supplies all remaining selected-label inequalities. Consecutive leaf gaps share the actual middle label, so the forbidden-turn argument uses genuine adjacent edges.
- Full-word positions zero and `n-1` have labels `g+1` and `g`. Thus the closing edge is the physical edge `g → g+1`, with line coordinates `t_last → t_0`. `weak_line_selection_root_clear` correctly uses the reversed scalar-between case. The first and last leaf contradictions occur at turns `g+1` and `g`, respectively; wraparound is included. These three closing statements require both full-word endpoints, and are not asserted for an arbitrary subinterval.
- Geometry helpers impose no `n≥4`, G1, generic perturbation, or extra polygon condition. The selected-coordinate injection and open-gap statements retain exactly their stated actual affine representation/strict-index data; first/last nonleaf only require `0<k`. Source `k≥2` is consequently retained by later assembly. These helpers alone do not prove the source existence of positive/negative nonleaf gaps or its ratio normalization.

Evidence: Geometry first root session98317 exited0; Selections second session98027 exited0. All 3/3 and 4/4 receipt-bound file hashes match; each current body appears exactly once in its prototype. The logs contain all eight/nine requested axiom traces and only `propext`, `Classical.choice`, and `Quot.sound` (some traces use a subset), with no error, sorryAx, native_decide, or Lean.ofReduceBool marker. This is evidence read from root's runs, not an independent kernel run.

Selections first70739 failed on a cast rewrite. Comparing the preserved first body and prototype with the passing files shows only an explicit natural-to-ZMod calculation substituted inside `boundaryIndex_last_of_val`; all nine declaration types remain unchanged. The failed files/log remain historical failed evidence, not a passing receipt.

SHA-256 bindings (paths relative to the focused root):

| File | SHA-256 |
|---|---|
| `work/checks/WeakLineGeometry.body.lean` | `33fa407bf8a5c37dd2c9459d56e50cb3c48faa85f48076f679a2197694135dc3` |
| `work/checks/WeakLineGeometry.prototype.lean` | `ba95e2e75a24638dcefed742faad18bc0a82964c0b163046d5b95b9ed9aa289d` |
| `work/checks/WeakLineGeometry-first-kernel.log` | `e10f17057f1a8553a3cadbdea5dbc50994365dc19738adcf1dc4b24258e704c2` |
| `work/checks/WeakLineGeometry-prototype-result.json` | `c18f8c128c6163cc95a2e90db6d992c091a4fef4663f06cfd2d9beeb03035b3d` |
| `work/checks/WeakLineSelections.body.lean` | `a91324f0380378fd48fcecea0bb1642f52dcdcc9fbfd45c626d43209cc6782c5` |
| `work/checks/WeakLineSelections.prototype.lean` | `970e8c9c5d8f12a889711e58edc11da8d638edcf3a6fcf1cfd6de287654d26bd` |
| `work/checks/WeakLineSelections-second-kernel.log` | `038c1f873e950a3a1994a158cb1d8fc9c9434328308cee1c84415e3df92b7caa` |
| `work/checks/WeakLineSelections-prototype-result.json` | `e47eba3aeaed98299ed74fe329ae70e070ecaf3256ad6bbb3dcd190e943e5827` |
| `work/checks/WeakLineSelections-first-failed.body.lean` | `8ee69c3e36ee6f98854df89cb5d90d3fee4b9173808b1b17a928395891921ce5` |
| `work/checks/WeakLineSelections-first-failed.prototype.lean` | `dedc6b3b25d46ed6fde671d73ce3d800c8d7b53ebd056c45ccd345a9f4a7dc4b` |
| `work/checks/WeakLineSelections-first-kernel.log` | `bca35ceec00ab70f6270a1d6a6e9352c47805edbeb3b3bf485363ee1109e2c5d` |
| `reference/SM/sm-2-amplitude.tex` | `014068e2f6e2d86b0ff4edf48877b5967847d661eaae04d2d4c5fd9f54b7c9cf` |
| `work/lean/SM/WeakGeneric.lean` | `1a72ebddb4ddb4d72a89f14a5fede9badc3dbed095a972f6dd1b85db30789b22` |
| `work/lean/SM/WeakGeometry.lean` | `4504cad4539531adc6f8271d30d389c62aa72249e3506cffed0352b73f22bcb2` |
| `work/lean/SM/Polygon.lean` | `d0b5d37591c252d66e1a3f060cea1e3d58625fedd6c5491cf4c1cf6d2b8c149d` |
| `work/lean/SM/RootBoundary.lean` | `604906b750e1ab198a2db3fc3cc011ab325493a91404a0b52ffe4583dd403f1a` |

Stronger statement/definition fidelity review and source acceptance remain pending. Accepted checklist progress is unchanged: 39/192 (20.3%); target acceptance 0/8.
