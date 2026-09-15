# Local tree path helpers: technical review

2026-09-11. Reviewer: another agent of the same currently available model, independently reviewing four root-authored declarations. This is **not the stronger-model statement-fidelity approval requested by the user**, nor source-claim acceptance. No Lean/kernel/build, proof edit, canonical edit or acceptance-map change was performed.

**Finding:** no mathematical or domain defect found. These are local persistence and parameter-transport helpers. They do not themselves derive silence or prove the continuation theorem.

`g1_all_chi_persists` applies the existing finite simultaneous persistence theorem to every distinct triple, using the actual G1 hypothesis for nonvanishing. It treats each repeated-label case separately by the corresponding zero identity. Thus all chi values persist in one neighbourhood, without incorrectly requiring nonvanishing for repeated labels or adding G2.

`tree_path_pair_near_generic` pulls that actual neighbourhood back by continuity at the stated point, then extracts an open parameter neighbourhood. Both generic parameters have all chi values equal to those at the centre; transitivity gives the pairwise equality needed by `treeCoefficient_eq_of_chi`. The root g is identical throughout. Arbitrary parameter spaces are supported; no density or connectedness is assumed or inferred here. The G1 assumption concerns the centre, while each evaluated coefficient is supplied the actual generic parameter's G1 proof.

`WallGerm.tree_coefficient_same_side` uses the actual continuous generic side family and the proved connectedness of `SideParameter = (0,radius)`. Constancy of its complete chirotope gives equality of the full integer tree coefficient at the same root. There is no assertion that the two different sides agree, and no root-independence assertion. The prototype imports `SM.GermSides`, which supplies the required proved connected-space instance.

`WallGerm.tree_parameter_eq_positive_of_sides_equal` explicitly assumes equality between every independent negative-side and positive-side parameter. For positive u it uses the side parameter u; for negative u it uses −u, deriving its positivity and radius bound from the actual punctured parameter domain. In both cases `sideTime` is proved equal to the original u, giving equality of the whole generic tuple. Applying the coefficient function to this subtype equality transports its G1 witness correctly. Positive parameters then use same-side constancy; negative parameters use the supplied cross-side equality. The chosen positive reference parameter remains arbitrary and the result covers the whole punctured germ domain.

The cross-side hypothesis in the fourth declaration is an explicit helper premise that the application must establish from the actual named E/C wall laws. It is not an axiom, an implicit silent-wall assumption, or a proved source continuation assertion. The reviewed statements supply the local generic and parameter-identification steps appropriate to source `thm:A-continuation` (lines 656–692); event classification and path gluing remain separate application work.

Receipt verification: second root **1045**, exit **0**, all **3/3** manifest hashes match. The exact body occurs once in the prototype. All four successful axiom traces contain only `propext`, `Classical.choice`, `Quot.sound`; the successful log contains no `error:`, `sorryAx`, `native_decide` or `Lean.ofReduceBool`. The preserved first run **26364** failed dependent rewrites in the last proof. The exact repair replaces both raw tuple-value rewrites with complete `GenericTuple` equality followed by `congrArg` of the coefficient function. All four theorem types are byte-identical to the first types; no premise or conclusion changed. Failed-run traces are not successful evidence.

| Bound file | SHA-256 |
| --- | --- |
| `work/checks/TreePathLocal.body.lean` | `8e092c2403ebcc45dc96d7df151fccf60c423d9930f3d186ff960a744f656f87` |
| `work/checks/TreePathLocal.prototype.lean` | `2193b3902a5ab7342197d4f4dece4035267d5fb8863d038a8e2fa3f298d74585` |
| `work/checks/TreePathLocal-second-kernel.log` | `3933a9060350773d7276f8a345a31121a2c0e2496ca1b62a2b5cc15857d595a1` |
| `work/checks/TreePathLocal-prototype-result.json` | `f0543d55f739ed3f69f6dcf90d14124988e8835016a7a3585362eb740e8929ee` |
| `work/checks/TreePathLocal-first.body.lean` | `047379d14e79e0d0678d7943c580b886766b669a51d17e2c95e6cd4fa183aeab` |
| `work/checks/TreePathLocal-first.prototype.lean` | `7de142f2cbb40db6641e5c21fa8635885447f639c2f9bfb5b057c55eed4e119c` |
| `work/checks/TreePathLocal-first-kernel.log` | `f32f7c66235820b572c6b427d606b901c364d513e5b12c14c25d4bfc2ed4c104` |
| `work/lean/SM/FiniteChiStability.lean` | `7160db9c4ac930a64c65ce44b9e9a41d4f139a3442a49604b3c96f9a347cadc9` |
| `work/lean/SM/TreeCoefficient.lean` | `d070e70dfbb61e036641f0d5fac4adae83fd1cadfe22f3ce2ffd8c8e1de9ab06` |
| `work/lean/SM/WallGerm.lean` | `fca24dab7111c6b6f404b075ab4e1b8c20d2fb48083565b6ba89758ebf684f9b` |
| `work/lean/SM/GermSides.lean` | `a95418d15b11a300c5e6a88cbb43ecd9877b5fd061dab754e2efc19eac625d0a` |
| `work/lean/SM/ChamberPaths.lean` | `cabb36d739563036aeee39c1a7bc0cf925a6259c5f90a22ecd61c9e2e737d44a` |
| `reference/SM/sm-2-amplitude.tex` | `014068e2f6e2d86b0ff4edf48877b5967847d661eaae04d2d4c5fd9f54b7c9cf` |

Passing evidence does not establish stronger statement fidelity. Acceptance remains **39/192 (20.3%)**, targets **0/8**.
