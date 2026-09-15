# PLAN B — row 89 ce:rounding (literal spatial reading): statement, construction, chain

Row: ce:rounding, reference/SM/sm-3-statesum.tex:3029-3062 (lemma environment; the statement proper is
3031-3058, `\status` 3059, `\end{lemma}` 3062), proof 3063-3169. Architect B (pod subagent), 2026-09-14.
Inputs: the memo work/drafts/gap2/GAP2_STATEMENTS_MEMO.md §2, §3(d), §4 "89", §5 and its sketch
work/drafts/gap2/Gap2Statements.lean §3-§4; the accepted front/rounding/transverse modules cited in §4 below;
work/AUTHOR_NOTES.md FR-1..FR-7 (3311-3356) and FR-R1..FR-R7 (3770-3786).

Deliverables (this directory; `cd work/lean && lake env lean <file>`, ~7-10 s warm each):
- `Statements_B.lean` (328 lines): compiles, exit 0; ONE `sorry` = the row `SM.ce_rounding : CeRoundingData`.
  `CuspedProjection.not_isCusp_of_isDouble`, `SpatialLink.ext'`, `CuspRoundingFamily.{a_lt_b, isDoubleOf_iff,
  same_circles}` proved.
- `Skeleton_B.lean` (897 lines): compiles, exit 0, no non-sorry warning; statement text verbatim (§1-3),
  construction (§4), chain (§5), glue proved (§6), constant family proved (§7), row PROVED from the chain (§8).
  **19 `sorry`**, all leaf lemmas (32 leaves written, 13 proved here). `#print axioms SM.ce_rounding` =
  [propext, sorryAx, Classical.choice, Quot.sound]; `#print axioms SM.CeRounding.constFamily` =
  [propext, Classical.choice, Quot.sound] (the "with no cusps" clause is already kernel-checked).
Nothing written under work/lean.

## 1. Clause map (printed → Lean; tex lines)

| tex | printed clause | Lean (Statements_B.lean) |
|---|---|---|
| 3031-3032 | smooth oriented spatial embedding of a finite nonempty union of parameter circles in ℝ³ | `L : SpatialLink c` (`T : Fin c → ℝ → Space`, `smooth`, `periodic` (FR-3), `embedded`, `regular`), `0 < c` |
| 3032 | write p = (x,z) for its projection | `L.projLoop i : SmoothLoop`, `γ = xzOf (L.T i)` |
| 3033-3034 | only failures of regularity: finitely many isolated cusps | `IsCusp i t := deriv (xzOf (L.T i)) t = 0`; `CuspedProjection.cusps_finite` |
| 3034-3035 | all other coincidences finitely many transverse double points | `doubles_finite`, `transverse` (det of projected velocities ≠ 0) |
| 3035-3036 | no triple points or cusps on another branch | `no_triple`; "cusps on another branch" = `not_isCusp_of_isDouble` (PROVED consequence of `transverse`) |
| 3036 | the two y heights at every double point distinct | `heights_distinct` (`height p = yOf (L.T p.1) p.2`) |
| 3037-3042 | exact germ at every cusp on an interval with coordinate u = y − y₀ | `exact_germ : ∀ p ∈ cuspSet, ExactCuspGerm p.1 p.2` (∃ A ≠ 0, δ > 0: `y′ ≠ 0` on `(t₀−δ,t₀+δ)`, the displayed formula with `u = y t − y t₀`) |
| 3043-3046 | u may increase or decrease; orientation not changed; formula a hypothesis | `y′ ≠ 0` of either sign; the family keeps the parameter; `exact_germ` is a hypothesis field |
| 3048-3049 | jointly smooth family L_λ, 0 ≤ λ ≤ 1, of oriented spatial embeddings, L_0 = L | `CuspRoundingFamily.fam : SpatialFamily c` (`G : ℝ → SpatialLink c`, `joint_smooth : ContDiffOn ℝ ∞ … (Icc 0 1 ×ˢ univ)`), `start : fam.G 0 = L` |
| 3049-3050 | fixed outside disjoint cusp parameter intervals | `a b : cuspSet → ℝ`, `a_lt`, `lt_b`, `len`, `intervals_disjoint` (mod ℤ), `fixed_outside` (λ ∈ [0,1]) |
| 3050-3051 | for every λ > 0 the xz projection is an ordinary finite regular generic diagram | `generic : ∀ λ ∈ Ioc 0 1, (fam.G λ).RegularGenericProjection` |
| 3051-3052 | cleanly smooths the cusps | `U : cuspSet → Set Plane`; `clean : ∀ λ ∈ Ioc 0 1, ∃ cs : L.CleanCuspSmoothing (fam.G λ).projLoop, cs.U = U ∧ cs.a = a ∧ cs.b = b` |
| 3052 | creates no crossing | `creates_no_crossing` (`IsDoubleOf (fam.G λ).projLoop p q → IsDoubleOf L.projLoop p q`) |
| 3052-3053 | retains every original crossing with its oriented decorated data | `retains_crossings` (converse), `same_data` (`crossSignOf` equal; height order equal) |
| 3053-3054 | all parameter circles, component labels, traversal orientations retained | structural (same `Fin c`, same parameter, T-1); `CuspRoundingFamily.same_circles` |
| 3054 | with no cusps take the constant family | `CeRoundingData.const_of_no_cusps` |
| 3055-3057 | ordinary spatial deformation; not Legendrian/transverse; no sl transport | disclaimer: no contact condition, no `sl` in the conclusion |

Row bundle `SM.CeRoundingData : Prop` = `exists_family` (3048-3054) + `const_of_no_cusps` (3054). Main theorem
`SM.ce_rounding : CeRoundingData`.

## 2. Model decisions (with the fidelity argument)

D1 **The spatial class is literal.** `SpatialLink c` is a `C^∞` 1-periodic map of `c` circles into `Space = ℝ×ℝ×ℝ`
(TransverseFront.lean:100), jointly injective, with nonvanishing derivative. "Embedding" of a compact manifold =
injective immersion; 91's text says "with nonvanishing parameter derivative" explicitly. Orientation = parameter
direction (T-1, accepted). The projection is the accepted `SmoothLoop` (FrontSmooth.lean:166) so the plain-loop
record vocabulary `IsDoubleOf/occSetOf/crossSignOf` (FrontRecordBridge.lean:97/105/118) applies verbatim.

D2 **"Ordinary finite regular generic diagram" = `RegularGenericProjection`** (regular immersion, finitely many
transverse double points, no triple point, heights distinct = the over/under choice by height): the SM's own smooth
diagram notion (sm-3:341-343) with the height rule of fd:contact. The POLYGONAL reading of `p(L_λ)` (FR-1,
`HeightMarking` of the memo) is NOT asserted by the row: its existence for a given smooth curve is PL approximation
(GAP-1, closed by design: consumers 90/91 take `Nonempty (HeightMarking …)` as a hypothesis). Recorded narrowing of
what "is a diagram" delivers to the accepted layer; nothing the printed proof claims is dropped.

D3 **"Cleanly smooths" = the accepted `GeomRounding` shape.** `CleanCuspSmoothing` (memo, verbatim) is field for
field `SmoothFront.GeomRounding` (FrontSmooth.lean:1129) on `L`'s cusps: clean discs `IsDisc` (LinkMoves.lean:100),
closed arcs, `clean/arc_in/arc_simple`, `agree` off the open arcs, `inside/regular/simple/no_crossing` on them. The
printed "clean cusp neighbourhood" becomes a compact convex disc — a stronger witness, provable (D6).

D4 **Changes against the memo's sketch** (forced or tightening; recorded for the units of rows 90 and 91):
1. `SpatialFamily.joint_smooth`: global `ContDiff` → `ContDiffOn … (Icc 0 1 ×ˢ univ)`. Forced: "0 ≤ λ ≤ 1" and the
   proof's "embeddedness outside [0,1] is not claimed" (sm-3:3103-3104). With `G : ℝ → SpatialLink c` every slice
   is embedded by type; the construction clamps λ to [0,1] outside (values there carry no claim). A globally smooth
   embedded family IS provable (the clearance has a factor-2 margin, so a smooth saturation of λ into (−2,2) works)
   but asserts more than printed by a device foreign to the text. Syntax of `ContactPathData`/
   `AmbientIsotopyDescent` (`F.G 0 = L`, `(F.G 1).RegularGenericProjection`, `HeightMarking (F.G 1) …`) unchanged.
2. `intervals_disjoint` on the circle (mod ℤ); the memo's ℝ-disjointness admits wrap-around overlap (weaker).
3. `U` added to `CuspRoundingFamily`; `clean` yields a `CleanCuspSmoothing` with `cs.U = U, cs.a = a, cs.b = b`:
   one neighbourhood and one interval per cusp for the whole family, the SAME intervals as `fixed_outside`
   (the proof: "Each modified portion is one regular embedded oriented arc in a clean cusp neighbourhood").
4. `same_doubles` split into `creates_no_crossing`/`retains_crossings`; quantifiers `λ ∈ Icc 0 1`/`Ioc 0 1`.
5. `CeRoundingData.const_of_no_cusps` added. 6. `not_isCusp_of_isDouble` proved (no new field).
Unchanged verbatim: `SpatialLink`, `projLoop`, `height`, `IsCusp`, `cuspSet`, `ExactCuspGerm`, `CuspedProjection`,
`RegularGenericProjection`, `CleanCuspSmoothing`; `HeightMarking` untouched (not needed by 89).

D5 **What the printed statement says that the bundle does not check as a Prop:** "component labels and traversal
orientations retained" — true by the TYPE (`Fin c`, the parameter); the disclaimer sentence — a non-claim. Both
recorded in docstrings; `same_circles` states the checkable residue.

D6 **Construction = the printed one, with an explicit chart-rectangle clearance.** The moved arc is the printed
ce:rounding-formula in the positive chart ce:positive-chart, i.e. the physical displacement ce:physical-displacement
`Δ = (A λ ε u ρ(u), 0, A y₀ λ ε u ρ(u))` with `ρ` = Mathlib `ContDiffBump` (1 on `|u| ≤ s/4`, 0 for `|u| ≥ s/2`).
The clean neighbourhood is `rectU` = chart preimage of `[−s²,s²]×[−s³,s³]` (compact convex, cusp interior; on the
chart arc it cuts out exactly `|u| ≤ s`), and `ε := s/2`: moved points have `|X_λ| ≤ s²/4 + λ ε s/2 < s²`,
`|Z_λ| = |u|³ < s³`, replacing the printed page-distance inequality ce:support-clearance (d/2) by an explicit
chart bound. The printed d-argument is still what proves `clean` (remote compact image at positive distance,
Leaf N2). Everything else (Z = u³ injectivity ce:cubic-difference, regularity by `dZ/du = 3u²`, `dX/du(0) = λε`,
spatial immersion by `dy/du = 1`, disjoint modifications) is the printed proof verbatim.

## 3. The chain (Skeleton_B.lean §4-§6; exact Lean statements there)

Construction (§4): `cuspPt, x₀, y₀, z₀, uOf, germPt, chartX, chartZ, rectU`; `structure CuspChart L k`
(A δ s a b; A ≠ 0, δ > 0, 0 < s < 1; `coord`, `germ`; `a_mem < a < t₀ < b < b_mem`, `len : b − a < 1/4`;
`u_injOn`; `|u a| = |u b| = s`, `u_lt` on (a,b), `u_gt` off [a,b]; `clean`); `sep`/`chart` by `Classical.choose`
of N0/N5; `Uk aK bK sK AK δK`; `bump`, `φ`, `Φ` (periodized by `round`), `ε`, `disp`, `cuspFinset`, `dispRaw`,
`famMap lam i t := L.T i t + ∑ cusps p of i, dispRaw p lam t`; `clamp`, `slice`, `family`.

Leaves (S = sorry, P = proved in the skeleton):
- N0 S `exists_sep : ∃ r > 0, ∀ k ≠ k', 2r < dist (cuspPt k) (cuspPt k')` (needs hL: finiteness; distinct images by `transverse`).
- N1 S `strictMono_or_strictAnti_of_deriv_ne_zero` (Darboux: `Set.OrdConnected.image_deriv`).
- N2 S `remote_far k hδ : ∃ r₀ > 0, ∀ q, (q.1 = i → ∀ n, q.2+n ∉ Ioo(t₀−δ,t₀+δ)) → r₀ ≤ dist (xz(L q)) (cuspPt k)`.
- N3 S `rectU_subset_closedBall : 0<s≤1 → rectU ⊆ closedBall (cuspPt k) (|A|(|y₀|+2)s²)` (sup metric on `Plane`).
- N4 S `chart_germ : chartX (xzOf (germPt A) t) = u² ∧ chartZ … = u³` (field_simp; ring).
- N5 S `exists_cuspChart k r hr : ∃ P : CuspChart L k, rectU P.A P.s ⊆ closedBall (cuspPt k) r` (from N1-N4 + IVT).
- P1 S `φ_contDiff`; P2 P `φ_eq_zero_of_notMem`; P3 P `φ_eventuallyEq_u : φ =ᶠ[𝓝 t₀] uOf`; P4 P `Φ_periodic`;
  P5 S `Φ_contDiff`; P6 P `Φ_eq_φ (|t−t₀|<1/2)`; P7 P `Φ_eq_zero_of_notMem` (orbit avoids the open arc).
- F1 P `famMap_smooth` (from P5); F2 P `famMap_periodic`; F3 P `famMap_joint_smooth` (global ContDiff on ℝ×ℝ,
  from P5); F4 P `famMap_zero : famMap 0 = L.T`; F5 P `yOf_famMap : yOf (famMap lam i) = yOf (L.T i)`;
  F6 P `famMap_eq_of_outside`; F7 S `famMap_on_arc : t ∈ Ioo(aK k)(bK k) → famMap lam i t = L.T i t + disp k lam t`;
  F8 P `arcs_disjoint` (glue from F9, F12); F9 P `Uk_disjoint` (glue from `chart_small`, `sep_spec`);
  F10 S `Uk_isDisc`; F11 S `cuspPt_mem_interior_Uk`; F12 P `arc_in` (from N4); F13 S `arc_simple`.
- I1 S `famMap_regular lam i t` (all λ: `y′ ≠ 0` on arcs, `L` off them); I2 S `famMap_embedded (λ∈[0,1])`;
  I3 S `proj_regular (λ∈(0,1])`; I4 S `proj_eq_of_proj_eq (λ∈[0,1])` (no new projected coincidence);
  I5 S `famMap_eventuallyEq_of_double lam h : famMap lam p.1 =ᶠ[𝓝 p.2] L.T p.1`; I6 S `famMap_inside (λ∈[0,1])`;
  I7 S `famMap_injOn_arc (λ∈[0,1])`.
- Z1 P `regular_of_no_cusps (h0 : cuspSet = ∅)`.
Glue (all proved): `slice_T`, `slice_zero`, `family`, `xzOf_famMap_{eventuallyEq,eq}_of_double`,
`deriv_xzOf_famMap_eq_of_double`, `isDoubleOf_slice_iff`, `occSetOf_slice_eq`, `height_slice`, G1 `slice_generic`,
G2 `sliceClean : CleanCuspSmoothing`, G3 `slice_same_data`, `roundingFamily : CuspRoundingFamily L`,
`constFamily`, and the row `ce_rounding`.

## 4. Accepted declarations used (file:line, work/lean/)

SM/TransverseFront.lean: `Space` 100, `xOf/yOf/zOf/xzOf` 103-109, `contactForm` 118 (not used: the disclaimer),
`SameT` 125, `eq_of_sameT_of_periodic` 172, `SmoothKnotDiagram` 189, `TransverseKnot` 571 (style only).
SM/FrontSmooth.lean: `SmoothLoop` 166 (+ `eq_add_int` 196, `deriv_eq_add_int` 216), `Param` 242, `SameParam` 246,
`SameParam.eq_of_mem_Ico` 268, `int_eq_of_add_mem_Icc` 1050, `eventually_add_int_notMem_Icc` 1060 (I5),
`GeomRounding` 1129 (the shape of `CleanCuspSmoothing`), `ClosedArcFree` 1226, `isOpen_closedArcFree` 1234,
`eventuallyEq_of_closedArcFree` 1245, `deriv_eq_of_notMem` 1339, `regular_everywhere` 1373,
`closedArcFree_of_isDouble` 1394, `deriv_eq_of_isDouble` 1409, `isDouble_iff` 1425 (templates for I1, I4, I5).
SM/FrontRecordBridge.lean: `IsDoubleOf` 97, `occSetOf` 105, `mem_occSetOf` 109, `crossSignOf` 118.
SM/FrontGeomModel.lean: `OccOf` 76, `GeomMarking` 120 (rows 90/91 only), `P_eq_of_geomModels` 351 (row 90).
SM/Polygon.lean: `Plane` 13, `det` 16. SM/LinkMoves.lean: `IsDisc` 100, `isDisc_closedBall` 104.
SM/Rounding.lean (cf:lem-rounding, accepted): Unit P `smoothTransition_*` 595-660 (not needed: the cutoff is a
Mathlib `ContDiffBump`, whose `one_of_mem_closedBall`/`zero_of_le_dist`/`contDiff` replace them),
`iteratedDeriv_eq_zero_of_const_left/right` 679/686 and `X_iteratedDeriv_eq_zero_of_eqOn_open` 2855 (flatness, if a
reviewer asks for "every derivative of the change vanishes" on the collars — not a printed clause of 89),
`far` 547 + `E_far_pos` 1890 (N2: positive distance of a point from a compact set), `cornerDisc_isDisc` 2072
(template for F10), `X_junction_injOn` 2358 / `doubles_curveMap` 2778 (templates for I7/I4), `roundedWitness` 3008
and `cf_lem_rounding` 3131 (the accepted ∃-form-with-named-construction pattern followed here).
Mathlib: `ContDiffBump` (Analysis/Calculus/BumpFunction/Basic, InnerProduct instance for ℝ), `round_add_intCast`,
`round_eq_zero_iff`, `Set.OrdConnected.image_deriv` (Darboux), `Metric.closedBall_disjoint_closedBall`,
`ContDiffOn.congr`, `ContDiff.sum`, `Filter.EventuallyEq.{deriv_eq, fun_comp, eq_of_nhds}`, `pow_le_pow_left₀`.

## 5. Unit split and effort (19 leaves; estimates in lines / agent-hours)

| unit | leaves | content | est. |
|---|---|---|---|
| N (chart package) | N0, N1, N2, N3, N4, N5 | Darboux monotonicity; IVT for the arc ends; compactness of the remote image + `E_far_pos`-style distance; the rectangle-in-ball bound; the chart algebra; assembling `CuspChart` with `clean` (remote points excluded by distance, chart points by `|u| ≤ s ↔ ∈ rectU`) | 900-1300 / 8-12 h |
| P (cutoff) | P1, P5 | `φ` smooth by the two-open-cover argument (germ interval / complement of `[a,b]`), `Φ` smooth (locally `φ(t−n)`; zero near the half-integer seams because `b − a < 1/4`) | 250-400 / 3 h |
| F (neighbourhood facts) | F7, F10, F11, F13 | one active cusp per arc (from P7 + F8); `IsDisc rectU` (affine preimage of a compact convex rectangle: `Homeomorph`/`Convex.affine_preimage`); interior; `arc_simple` from `clean` + `chartZ = u³` injectivity | 400-600 / 4-5 h |
| I (slices) | I1, I2, I3, I4, I5, I6, I7 | I1: `y′ ≠ 0` on closed arcs (F5, `coord`), `L` regular off them (open complement, `eventually_add_int_notMem_Icc`); I3: the derivative computation `z′ − y₀x′ = 2Au²u′`, `x′(t₀) = Aλε u′(t₀)` (P3); I4: moved points lie in `Uk` (I6), remote points do not (`clean`), `Z_λ = u³` on the chart, different cusps have disjoint `Uk`; I2 from I4 + `L.embedded` + `yOf_famMap`; I5 from F6 + openness; I6/I7 chart algebra with `|Φ| ≤ s/2` | 1300-1800 / 12-16 h |
| assembly | — | done (this skeleton) | 0 |
Total ≈ 2.9-4.1k lines, 27-36 agent-hours — within the memo's 3-5k estimate. Independent of GAP-2; no interface
change; no axiom. Recommended order: N4, N3, P5, P1 (pure), then N1/N2/N0 → N5, then F7/F13, I5, I1, I6/I7, I3, I4, I2, F10/F11.

## 6. Fidelity risks (to be cited by the reviewer of 89 and by the units of 90, 91)

R-1 (polygonal reading, FR-1/GAP-1). The row asserts the SMOOTH genericity of `p(L_λ)`; the polygonal `Diagram`
carrying its record (`HeightMarking`) is a consumer hypothesis, never proved to exist. Consistent with every
accepted front row; must be repeated in FINAL_REVIEW for 89-91.
R-2 (embedding). "Spatial embedding" is rendered as injective immersion of compact circles (equivalent classically);
no `Embedding`/`IsEmbedding` topology object is used. Orientation = parameter direction (T-1).
R-3 (family on [0,1]). `SpatialFamily.G : ℝ → SpatialLink c` has junk values off `[0,1]` (clamped); the claim is
`ContDiffOn` on `Icc 0 1 ×ˢ univ` and properties for `λ ∈ [0,1]` / `(0,1]`. The memo's global-`ContDiff` version is
stronger than printed (D4.1). Reviewers should confirm `ContDiffOn` on the closed strip is the intended "jointly
smooth, 0 ≤ λ ≤ 1".
R-4 (clean neighbourhood = disc). The printed "clean cusp neighbourhood" is realised by the accepted compact convex
`IsDisc` (ng:front-domain's "clean cusp discs"); a conclusion strengthening, provable (chart rectangle).
R-5 (decorated data). "Oriented decorated data" = sign (`crossSignOf`, over-first tangent determinant) + height order
(over = smaller y, fd:contact/T-2) + the pairing and cyclic orders (literally the same parameters). The record
itself (`HeightMarking`) is not mentioned in 89's bundle; 90 states the record consequences.
R-6 (exact germ hypothesis). `ExactCuspGerm` requires the formula on an OPEN interval with `y′ ≠ 0` there; the
printed "on a parameter interval with smooth coordinate u" could also be read with a closed interval — immaterial.
R-7 (proof route ≠ printed constants). `ε = s/2` and the rectangle bound replace ce:support-clearance's `d/2`
inequality; the printed d-argument survives only inside N2/N5 (`clean`). The statement is unaffected (∃-form).
R-8 (nonvacuity). `CuspedProjection` is nonempty (a round circle at height 0 has no cusp, no double point); a
kernel-checked witness is ~40 lines and recommended before the row is accepted; a cusped witness (two exact germs
glued to a smooth arc) is harder (~300 lines) and not needed for the row.
R-9 (coordination with rows 90/91). The sibling unit must adopt D4.1-D4.3 (or record why not) before its file is
reviewed; `HeightMarking`, `CleanCuspSmoothing`, `RegularGenericProjection`, `CuspedProjection` are unchanged, so
row 90's statement is unaffected; row 91's `AmbientIsotopyDescent`/`ContactPathData` need only the new
`SpatialFamily` (same field names).
R-10 (leaf N0 needs `hL`). `exists_sep` and `remote_far` are stated with `include hL`; they are false without
finiteness/transversality (two cusps could share an image) — the skeleton states them correctly, the reviewer of the
proof units should check that no leaf drops `hL`.
