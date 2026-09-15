# Row 154 — CV:lem:curl — report

File: `work/drafts/cvdom/CVCurl.lean` (383 lines). Main declaration `CV.curl : CV.CVCurlData` (Prop bundle, one
field per printed sentence / clause; name per DECISION_FINAL.md §3 R3, `CV.<label>` for PROVE rows), on the CV
site `CV.CurlSite` (the printed binder d3:306–311), proved from the accepted twin `SM.cf_lem_curl` (work/lean/SM/Curl.lean,
ACCEPTED 2026-09-14 ~08:49Z) by transporting the site (`CurlSite.toSM`, a field-for-field repackaging with both
round trips `rfl`) and reading the twin's witness `SM.CurlWitness S.toSM Δ` on it.

Compiled 2026-09-14 ~09:05 UTC / 05:05am ET with `cd work/lean && lake env lean ../drafts/cvdom/CVCurl.lean`: exit 0,
0 errors, 0 warnings, no incomplete proofs, no new axioms, no `axiom` declaration. `#print axioms` on a /tmp copy:
`CV.curl`, `CV.curl_of_carried`, `CV.rotCurve_eq_sub_one`, `CV.CurlSite.next`: `[propext, Classical.choice, Quot.sound,
SM.lp_lm]` (the policy axiom of every consumer of the accepted polynomial `P`; it enters through `SM.cf_lem_curl` and
through the type `SM.CurlWitness`, whose field `poly_eq` mentions `P`); `CV.CurlSite.toSM`, `ofSM_toSM`, `ofCarried_toSM`,
`doublePoints_finite`, `no_triple`: `[propext, Classical.choice, Quot.sound]`; the corollary `CV.curl_homfly_eq`
(the polynomial in CV:def:homfly's letter `homfly`): `[propext, Classical.choice, Quot.sound, SM.lit_homfly, SM.lp_lm,
SM.lp_lm_uniqueness]` through `P_eq_homfly` (lp:core). Imports: `SM.Curl` (the twin; brings `SM.Rounding`, `SM.LinkMoves`,
`SM.PolynomialBlock`), `CV.Rounding` (→ `CV.TurnLift` → `CV.RotationSmooth`: `rotCurve`; row 152's `Carried` output
for the consumer entry). Nothing written under work/lean; `lake build` not run; the machine load did not matter (the
file only loads oleans: ~8 s).

Sources. CV: reference/R/CV/d3_floor.tex, `lem:curl`, statement 304–323 (scoping 305, hypotheses 306–311, existence
311–313, (i) 315–317, (ii) 318–319, (iii) 320, (iv) 321), proof 324–701 (model 325–356, ordered-ray lemma 360–390,
chart and cuts 392–418, affine fit 420–459 with "the disc is fixed first and the cuts afterwards" 456–459, separation
461–474, replacement and collars 476–640, "the four conclusions, separately" 642–671, "the polynomial conclusion,
without a knot-category detour" 673–700), remark `rem:curlauthor` 703–733; consumer `thm:carrierfloor` (C) 885–912
(switch 897–899, curl applied 899–912). SM: reference/SM/sm-3-statesum.tex, `cf:lem-curl`, statement 3870–3891
(scoping 3871–3872, hypotheses 3873–3878, existence 3878–3880, (i) 3882–3884, (ii) 3885–3886, (iii) 3887, (iv) 3888,
`\status` 3890 "transcribed from CV lem:curl (C032)"), proof 3892–4280; consumer cf:thm-carrierfloor (C) 4423–4455.
SM row: `SM.cf_lem_curl : SM.CurlData`, work/lean/SM/Curl.lean (8381 lines; statement §§1–4 = lines 37–360; fixed
statement work/drafts/curl/Statements_FINAL.lean + PORT_REPORT.md §3 (the field `old_crossingPoint` and its conjunct
in `CurlData.i`); plan PLAN_FINAL.md §§1, 5, 7; AUTHOR_NOTES 2026-09-14 ~06:19Z "Curl lane" (FR-C1..FR-C10) and ~08:49Z
"cf:lem-curl ACCEPTED").

## 1. Clause → field map (tex lines of BOTH papers)

| CV d3_floor.tex | SM sm-3 | printed sentence / clause | Lean (field of `CV.CVCurlData`, or binder) | proof |
|---|---|---|---|---|
| 305 | 3871–3872 | "Here rot is as in Definition def:rot." (SM: "Lemma lem:rot for polygons and Definition cf:def-turning for closed C¹ regular curves") | not a clause; fixes the reading of (iv). Only curve rotations occur in this lemma (`F`, `F'` are `C^∞` immersed circles): `CV.rotCurve γ = tw(T_γ)` (d1_setup.tex:775–780; CV/RotationSmooth.lean:57, `abbrev … := γ.rot`, decision F6) | — |
| 306–307 | 3873–3874 | "Let F be a connected C^∞ immersed circle in the plane — one component" | `CurlSite.F : SmoothRegularLoop` (accepted `C^∞` 1-periodic regular class, SM/Rounding.lean §3 — the class of row 152's `L_ε`); "one component" is `S.one : S.D.Γ.c = 1` (the record's `one`) | — |
| 307–308 | 3874–3875 | "with finitely many transverse double points and no triple points — given with an oriented diagram" | `CurlSite.D : Diagram`, `CurlSite.carried : RecordCarried F D` (the twin's record-level carrying, FR-C1); "finitely many" = `CurlSite.doublePoints_finite`, "transverse" = `carried.transverse`, "no triple points" = `CurlSite.no_triple` (theorems of the record) | `RecordCarried.doublePoints_eq` + `Set.finite_range`; `RecordCarried.no_triple` |
| 308–309 | 3875–3876 | "let p be a point of F at which the tangent points in a fixed direction u" | `t₀ : ℝ`, `CurlSite.p := F.γ t₀`, `u : Plane`, `tangent_at : normalize (deriv F.γ t₀) = u` | — |
| 309 | 3876 | "isolated among such points" | `isolated : ∀ t ∈ Icc α β, normalize (deriv F.γ t) = u → t = t₀` (`CurlSite.T_eq_u_iff`) | — |
| 309–310 | 3876–3877 | "lying in an embedded arc of F that contains no double point" | `α β : ℝ`, `α_lt`, `lt_β`, `short : β − α < 1`, `embedded : InjOn F.γ (Icc α β)`, `no_double : ∀ v n, carried.τ v + n ∉ Icc α β` | — |
| 310–311 | 3877–3878 | "along which the tangent turns strictly positively" | `θ : ℝ → ℝ`, `lift : IsLiftOn (fun t => normalize (deriv F.γ t)) θ α β` (CV:def:rot's "tangent-angle lift", d1_setup.tex:767–771), `turns_pos : StrictMonoOn θ (Icc α β)` | — |
| 311–313 | 3878–3880 | "Then F may be modified inside a disc Δ meeting the rest of the diagram only in that arc, so that the resulting diagram F' [(i)–(iv)]" | `exists_curl : ∀ S Δ₀, S.p ∈ interior Δ₀ → ∃ Δ ⊆ Δ₀, Nonempty (SM.CurlWitness S.toSM Δ)` (disc inside any preassigned neighbourhood, FR-C2; the proof's 456–459, the consumer's 899–905); `exists_curl' : ∀ S, ∃ Δ, Nonempty (SM.CurlWitness S.toSM Δ)` (as printed); `disc` (`IsDisc Δ`, `p ∈ interior Δ`, every point of `F` in `Δ` traversed on the arc, `F' = F` with velocity off the window `(s₁, s₂)` mod 1, the modified arc in `Δ`) | `SM.cf_lem_curl.exists_curl S.toSM`, `.exists_curl' S.toSM`, `.disc S.toSM Δ W` |
| 315 | 3882 | (i) "is again such an oriented diagram" | `i` conjuncts 1–6: `ContDiff ℝ ∞ W.F'.γ`, `Periodic W.F'.γ 1`, `∀ t, deriv W.F'.γ t ≠ 0`, `W.D'.Γ.c = 1`, `Nonempty (RecordCarried W.F' W.D')`, `RI S.D W.D'` (the accepted Reidemeister-I move; FR-C6 export) | `SM.cf_lem_curl.i S.toSM Δ W` |
| 316 | 3883 | (i) "satisfies P_{F'}(a,z) = P_F(a,z)" | `i` conjunct 7: `P W.D' = P S.D` (the accepted polynomial of a diagram; FR-C4); in CV:def:homfly's letter: `curl_homfly_eq : homfly W.D' = homfly S.D` (outside the bundle, adds `SM.lit_homfly`) | `W.poly_eq`; `P_eq_homfly` |
| 316–317 | 3883–3884 | (i) "has the same double points outside Δ, with the same signs" | `i` conjuncts 8–9: `doublePoints W.F'.γ \ Δ = doublePoints S.F.γ \ Δ`; `∀ x : S.D.Γ.Crossing`, `W.F'.γ (τ' (overVisit (old x))) = S.F.γ (τ (overVisit x))` ∧ `W.D'.Γ.crossingPoint (old x) = S.D.Γ.crossingPoint x` (the port's FR-C1 mitigation) ∧ `W.D'.sign (old x) = S.D.sign x` | `W.doubles_outside`, `W.old_point`, `W.old_crossingPoint`, `W.old_sign` |
| 318–319 | 3885–3886 | (ii) "has no point of Δ at which the tangent equals u, and exactly one at which it equals −u" | `ii`: `∀ t, W.F'.γ t ∈ Δ → normalize (deriv W.F'.γ t) ≠ S.u` ∧ `∃! t ∈ Ico 0 1, W.F'.γ t ∈ Δ ∧ normalize (deriv W.F'.γ t) = −S.u` | `SM.cf_lem_curl.ii S.toSM Δ W` |
| 320 | 3887 | (iii) "has exactly one double point inside Δ, and it is negative" | `iii`: the kink crossing realised in `Δ`; every double point of `F'` in `Δ` is that point; `W.D'.sign W.kink = −1 ∧ W.carried'.smoothSign W.kink = −1` | `SM.cf_lem_curl.iii S.toSM Δ W` |
| 321 | 3888 | (iv) "satisfies rot(F') = rot(F) − 1" | `iv` conjunct 1: `rotCurve W.curve = rotCurve S.F.toClosedC1Curve − 1` (CV:def:rot on both sides) | `rotCurve_eq_sub_one W` (= `W.rot_eq`, `rotCurve` being an `abbrev` of `ClosedC1Curve.rot`) |
| 321 | 3888 | (iv) "and w(F') = w(F) − 1" | `iv` conjuncts 2–3: `W.D'.writhe = S.D.writhe − 1 ∧ W.carried'.smoothWrithe = S.carried.smoothWrithe − 1` | `W.writhe_eq`, `W.smoothWrithe_eq` |
| — | 3890 | `\status{…transcribed from CV lem:curl (C032)}` | no CV counterpart; no field | — |
| 703–733 | — | `rem:curlauthor` (authorship of the construction; "The HOMFLY conclusion is narrower than the former knot-isotopy conclusion. It uses only Reidemeister-I invariance from Axiom ax:homfly and the record comparison from Axiom ax:gausscode"; the (C) turn-hypothesis tightening) | reading, no field: the polynomial conclusion is the RI route (`ri : RI S.D W.D'`, `P_reidemeister_I`), see R6 | — |
| thm:carrierfloor (C) 885–905 | cf:thm-carrierfloor (C) 4423–4442 | input "the rounding record … Switch every crossing … Apply Lemma lem:curl at each of the R downward vertical tangencies; … the rounding discs are pairwise disjoint and meet no crossing … so the R discs are disjoint and each replacement leaves the others intact" | `CurlSite.ofCarried` (site from a `Carried` record — row 152's output — through `Carried.toRecordCarried`; `ofCarried_toSM` = the twin's `SM.CurlSite.ofCarried`), `curl_of_carried` (the existence sentence in that form, `Δ ⊆ Δ₀`), `CurlSite.next` (the site of the second and later curls from `W.F'`, `W.D'`, `W.carried'`) | `curl.exists_curl` |

## 2. CV versus SM, clause by clause (design task (1))

Hypotheses (CV 306–311 / SM 3873–3878): word for word the same. Existence sentence (CV 311–313 / SM 3878–3880): word
for word the same. Clauses (i)–(iv) (CV 315–321 / SM 3882–3888): word for word the same. SM's `\status` (3890) says so:
"transcribed from CV lem:curl (C032)". Exactly one difference in the statements:

1. Scoping sentence (CV 305 / SM 3871–3872). CV: one Definition def:rot for polygons (the `ε_i` ray formula,
   d1_setup.tex:734–739) and for closed `C¹` regular curves (`rot(γ) = tw(T_γ)`, 775–780). SM: Lemma lem:rot for
   polygons, Definition cf:def-turning for curves. In row 152 (CV:lem:rounding (d)) this mattered because the polygon
   `rot` appeared on one side and the two polygon notions agree only as a theorem (`CV.rot_eq_rotationNumber`). In the
   curl lemma no polygon is named: `F` and `F'` are `C^∞` immersed circles, so both `rot`s in (iv) are curve
   rotations, and the curve notion is one definition under two names (`CV.rotCurve γ := γ.rot`, decision F6). (iv) is
   therefore stated as `rotCurve W.curve = rotCurve S.F.toClosedC1Curve − 1` and proved by the twin's `rot_eq` with no
   identification theorem. The diagram's writhe `w` has one definition in both papers (`Diagram.writhe`; smooth writhe
   `smoothWrithe`).

Non-statement differences, recorded because the design task asked for every difference:

2. CV's proof ends with "the polynomial conclusion, without a knot-category detour" (673–700: delete the monogon by a
   Reidemeister-I move, `P_{F'} = P_{F°}` by ax:homfly, `F°` and `F` have isomorphic records, `P_{F°} = P_F` by
   ax:gausscode) and the authorship remark 703–733 says the HOMFLY conclusion "uses only Reidemeister-I invariance
   from Axiom ax:homfly and the record comparison from Axiom ax:gausscode". The Lean proof (the twin's) gets
   `P D' = P D` from the polygonal move `ri : RI D D'` and the accepted `P_reidemeister_I` (FR-C4) — the Reidemeister-I
   half of CV's own route, with no record-comparison step needed because the polygonal `D'` is `D` plus the kink by
   construction. CV's axiom rows are theorems of the same library (`CV.ax_homfly.reidemeister`, CV/Axioms.lean; the
   ax:gausscode polynomial replacement `CV.gausscode_polynomial`), so the route is inside CV's own toolkit.
3. The consumer's phrasing. SM (4438–4442) says "Choose each curl disc inside its corresponding rounding disc";
   CV (899–905) says the tangencies "lie in the interiors of positively turning rounding arcs (clause (B)), and the
   rounding discs are pairwise disjoint and meet no crossing … so the R discs are disjoint and each replacement leaves
   the others intact" — the curl discs are the rounding discs or inside them, implicitly. Both need `exists_curl`'s
   preassigned-neighbourhood form (FR-C2), which is therefore the CV row's existence field as well.
4. The diagram class (design task (1) "CV's diagram class"). CV states the lemma "for the smooth curve with its carried
   diagram after CV:lem:rounding": row 152's output is `Carried W.Lε D.toDiagram` (SM/Rounding.lean §4, with the
   point-coincidence clause `τ_eval`). The input class here is `RecordCarried` (the accepted `Carried` minus `τ_eval`
   plus `twin_eval`), as in the twin, for two reasons that are CV's own: (a) the consumer applies the lemma `R` times in
   succession (899–905), and after the first curl the carried diagram is record-level only (the polygonal kink of `D'`
   cannot sit at the smooth double point; FR-C1 / FR-C9) — so the input class must be the output class for the
   iteration (`CurlSite.next`); (b) CV:def:record (d1_setup.tex:522–531) defines "the record of a link diagram" by the
   traversal circle, the preimages of the crossings, the crossing correspondence and the over/under and sign data —
   marked points on a circle, not points of the plane — which is exactly what `RecordCarried` realises on the traversal
   circle of `F`. Row 152's `Carried` output enters through the accepted `Carried.toRecordCarried` (`CurlSite.ofCarried`).

## 3. The bridge used (design task (2))

There is no polygon bridge to build (row 152's `polyComp` / `OverUnder` / `toPolygonDiagram` are not involved: the
binder of this lemma is a smooth curve with a carried record, and those objects are already CV's vocabulary through
row 152). The transport is:

* `CV.CurlSite` (§1 of the file) — the printed binder d3:306–311, one field per printed object/hypothesis, docstrings
  quoting the CV lines; the same field list as the twin's `SM.CurlSite` (sm-3:3873–3878).
* `CurlSite.toSM : CV.CurlSite → SM.CurlSite` and `CurlSite.ofSM` — field-for-field repackagings; `ofSM_toSM`,
  `toSM_ofSM` are `rfl` (structure eta); `toSM_F`, `toSM_D`, …, `toSM_p`, `toSM_T` are `rfl` simp lemmas. `u_unit`,
  `one`, `T_eq_u_iff` re-export the twin's site lemmas on the CV site.
* The witness is the twin's, at the transported site: `W : SM.CurlWitness S.toSM Δ`. Its field list is the fixed content
  of (i)–(iv) (Statements_FINAL.lean §3 + PORT_REPORT.md §3); the CV bundle's clause fields are stated on it in CV's
  words and proved by `SM.cf_lem_curl.<field> S.toSM Δ W` — the terms typecheck against the CV statement because
  `S.toSM.F`, `S.toSM.D`, `S.toSM.carried`, `S.toSM.p` reduce to `S.F`, `S.D`, `S.carried`, `S.p` (definitional
  unfolding of `toSM`; the `@[simp]` lemmas record the same equalities for consumers).
* The one CV re-reading is (iv)'s `rot`: `rotCurve_eq_sub_one W : rotCurve W.curve = rotCurve S.F.toClosedC1Curve − 1
  := W.rot_eq` (`CV.rotCurve` is an `abbrev` of `SM.ClosedC1Curve.rot`; `W.curve := W.F'.toClosedC1Curve`).
* Nothing CV asserts is missing from the twin's witness. Checked clause by clause: (i)'s six "again such a diagram"
  facts, the polynomial, the outside double points and the old-crossing correspondence with points, polygonal
  crossing points and signs; (ii)'s two tangency facts; (iii)'s three; (iv)'s two — every one is a projection or a
  named corollary of `SM.CurlWitness` (`smooth`, `periodic`, `regular`, `one`, `carried'`, `ri`, `poly_eq`,
  `doubles_outside`, `old_point`, `old_crossingPoint`, `old_sign`, `no_u`, `one_neg_u`, `kink_mem`, `one_double`,
  `kink_neg`, `kink_smoothSign`, `rot_eq`, `writhe_eq`, `smoothWrithe_eq`). The only CV-specific assertions are (iv)'s
  `rot` in CV's letter (a definitional re-reading) and (i)'s polynomial in CV:def:homfly's letter (`curl_homfly_eq`,
  a rewrite by `P_eq_homfly`, kept outside the bundle so that `CV.curl`'s axioms stay those of the twin).
* Consumer entries (§4 of the file): `curl_of_carried` (the existence sentence for a site built from a `Carried`
  record — row 152's `smooth_regular_carried` — with `Δ ⊆ Δ₀`), `CurlSite.next` (the site of the next curl from a
  witness's `F'`, `D'`, `carried'`).

## 4. Readings

R1 (binder). `S : CV.CurlSite` — the printed objects `F`, its oriented diagram, `p`, `u`, the embedded arc and its
tangent-angle lift — with `p = F.γ t₀` and the arc the parameter interval `[α, β]` around `t₀`; no CV `LabelledTuple`,
no `[NeZero n]`, no `hn` (nothing polygonal is in the statement).

R2 (hypotheses as printed; inherited FR-C5). "Isolated among such points" = uniqueness of the `u`-tangency on the arc;
"along which the tangent turns strictly positively" = strict monotonicity of a tangent-angle lift on the arc (CV:def:rot's
own lift notion, d1_setup.tex:767–771); "an embedded arc" = `InjOn` on `[α, β]` with `β − α < 1` (an arc, not the whole
circle); "contains no double point" = no occurrence parameter of the record on the arc (mod 1). Row 152's junction
supplies all of these (`junction_embedded`, `same_strands`, `θ_lift`, `θ_strict`, `direction_once`; PLAN_FINAL.md §5).

R3 (the oriented diagram; inherited FR-C1, CV-native). `RecordCarried F D`: CV:def:record's record of `D` realised on the
traversal circle of `F` (§2 item 4 above). "Finitely many transverse double points and no triple points" (307) are
theorems of the record (`doublePoints_finite`, `carried.transverse`, `no_triple`), not extra hypotheses. Row 152's
`Carried` output enters through `Carried.toRecordCarried`; the output class of this row is `RecordCarried` (`carried'`),
strictly weaker than `Carried` at the kink (`old_crossingPoint` makes it `Carried`-like at every old crossing).

R4 (the disc; inherited FR-C2, FR-C3). "Modified inside a disc Δ" = equality of the parametrised curves, with velocity,
off the window `(s₁, s₂) ⊆ [α, β]` (mod 1), both the old and the new arc inside `Δ`, `IsDisc Δ` (the accepted clean-disc
vocabulary), `p ∈ interior Δ`; "meeting the rest of the diagram only in that arc" = every point of `F` in `Δ` is traversed
on the arc. The existence field takes `Δ` inside any preassigned neighbourhood `Δ₀` of `p` (the printed proof's
"the disc is fixed first and the cuts afterwards", 456–459; the consumer's disjoint discs, 899–905); the bare printed
form is `exists_curl'`.

R5 ((ii) "point of Δ"). Read on parameters: no `t` with `F'(t) ∈ Δ` has unit tangent `u`; exactly one `t` in the
fundamental period `[0, 1)` has `F'(t) ∈ Δ` and unit tangent `−u` (the twin's reading; "exactly one" counts parameters,
which is what the consumer counts at 892–896 "exactly R downward vertical tangencies").

R6 ((i) polynomial; inherited FR-C4). `P W.D' = P S.D` for the accepted `P : Diagram → R` — the polynomial of the smooth
diagram is that of its carried polygonal diagram (well defined at record level by rp:record-polynomial); proved in the
twin by the polygonal Reidemeister-I move and `P_reidemeister_I`, the RI half of CV's printed route (673–700). In
CV:def:homfly's letter, `curl_homfly_eq : homfly W.D' = homfly S.D` (`P_eq_homfly`).

R7 ((iv) `rot`). `CV.rotCurve` on both sides (CV:def:rot for closed `C¹` regular curves, d1_setup.tex:775–780), the
smooth loops read in the accepted `C¹` class by `toClosedC1Curve`; no polygon `rot` occurs. `w` is `Diagram.writhe` of
the carried polygonal diagram, with the smooth writhe (sum of the smooth signs `sgn det(velocity_over, velocity_under)`)
dropping by one as well (the vocabulary of row 152's (c)).

R8 (shape; inherited FR-R5/FR-C6). The existence field is the theorem; the clause fields hold for every witness and are
the twin's projections re-read; the witness exports more than printed (the window `[s₁, s₂]`, `unchanged_deriv`,
`old_in_disc`, `disc_meets_arc`, `ri : RI D D'`, the crossing correspondence `old` with points and polygonal crossing
points, the smooth sign/writhe corollaries) — all read by the consumer (C).

R9 (the authorship remark 703–733 and the (C) hypothesis note). Commentary, no field; the tightened turn hypothesis it
describes belongs to thm:carrierfloor (C) (row 155), not to this lemma.

## 5. Fidelity risks (to be cited in the review of this row and of its consumer)

Inherited from the SM row (AUTHOR_NOTES 2026-09-14 ~06:19Z "Curl lane"; PLAN_FINAL.md §7): FR-C1 (record-level carrying,
input and output — here argued CV-native through CV:def:record, R3; the port's mitigation `old_crossingPoint` is in
`i`), FR-C2 (disc inside a preassigned neighbourhood; bare form `exists_curl'`), FR-C3 (modification support read on the
parametrised curves with velocity), FR-C4 (polynomial via the polygonal RI and `P_reidemeister_I`), FR-C5 (hypothesis
readings), FR-C6 (exports beyond print), FR-C9 (the polygonal kink is at a free edge point in the cyclic gap of `t₀`;
the smooth double point and the polygonal kink point are unrelated). FR-C7/8/10 concern the twin's proof and check
environment only.

CV-specific:

* FR-CV-C1 (a CV-side site structure). `CV.CurlSite` duplicates the twin's `SM.CurlSite` field for field (the printed
  hypotheses being word for word the same) so that CV's binder carries CV's tex lines; `toSM`/`ofSM` with `rfl` round
  trips make the two interchangeable. A reviewer preferring the SM object directly can read every field through
  `toSM_*` or state the row on `SM.CurlSite` via `ofSM` — no content differs. The witness is not duplicated: CV's
  clauses are read on `SM.CurlWitness S.toSM Δ`, as row 152 read its clauses on `SM.RoundingWitness`.
* FR-CV-C2 (`rot` identification). Definitional (`abbrev`), decision F6; unlike row 152 no theorem is used, because no
  polygon rotation occurs.
* FR-CV-C3 (polynomial letter). The bundle uses the accepted `P` (axioms of `CV.curl` = those of the twin); CV:def:homfly's
  letter `homfly` is the corollary `curl_homfly_eq`, whose axioms add `SM.lit_homfly` and `SM.lp_lm_uniqueness` (through
  `P_eq_homfly`, lp:core). A reviewer wanting `homfly` inside the bundle would change only the axiom list, not the content.
* FR-CV-C4 (consumer entry). CV's (C) applies the lemma to the rounded diagram after switching every crossing (897–899).
  `CurlSite.ofCarried` takes any `Carried F D`; producing the `Carried` record of the switched diagram from row 152's
  `W.carried` (the over/under bits of the polygon flip, the smooth signs flip with them) is the consumer's obligation,
  not this row's (open item 2). The junction data (`[α, β] = [a j, b j]`, `θ j`, the tangency parameter) come from
  `RoundingWitness` as PLAN_FINAL.md §5 lists.
* FR-CV-C5 (no scope change). Same binder as printed, same quantifiers, one field per printed sentence/clause; the only
  additions over print are the twin's disclosed exports (R8) and the preassigned-neighbourhood form of the existence
  sentence (R4), both of which the consumer needs.

## 6. Open items

1. `SM.cf_lem_curl` is accepted; this row consumes its fixed statement (`CurlSite`, `CurlWitness`, `CurlData`,
   `RecordCarried`, `Carried.toRecordCarried`) and its row theorem. Any later change there propagates mechanically
   (the CV fields are the twin's field list; re-sync `i` if `CurlWitness` changes again).
2. For CV:thm:carrierfloor (C) (row 155): (a) a `Carried` record for the all-crossings-switched diagram of row 152's
   output (the switch of every crossing of a `Diagram`, its effect on `sign`/`writhe`, and the smooth signs — the over
   and under visits exchange, so `smoothSign` negates); (b) the site at each downward tangency from `RoundingWitness`
   (`junction_embedded`, `same_strands` ⇒ `no_double`, `θ_lift`/`θ_strict` ⇒ `lift`/`turns_pos`, `direction_once` ⇒
   `isolated`, `b j − a j < 1`) with `Δ₀ := cornerDisc C ε j`; (c) the iteration through `CurlSite.next`, whose
   `no_double` for `D'` needs: old parameters as before, the two kink parameters inside the previous window, disjoint
   from the other junctions (`unchanged`, `disc_meets_arc`, the disjointness of the rounding discs). None of this is
   part of the present row.
3. Port: module `work/lean/CV/Curl.lean` (imports `SM.Curl`, `CV.Rounding`), namespace `CV`. Name-safety scan done
   (grep over work/lean CV/*.lean for `CurlSite`, `CVCurlData`, `theorem curl`): no collisions; inside `namespace CV`
   the file uses `open SM hiding CurlSite CurlData` so that bare `CurlSite` is CV's and `SM.CurlSite` is named in full
   (`CurlWitness` is not hidden: it is always the twin's).

## 7. Declarations (work/drafts/cvdom/CVCurl.lean, namespace `CV`)

`CurlSite` (structure; fields `F`, `D`, `carried`, `u`, `t₀`, `tangent_at`, `α`, `β`, `α_lt`, `lt_β`, `short`, `embedded`,
`no_double`, `θ`, `lift`, `turns_pos`, `isolated`), `CurlSite.p`, `CurlSite.T`, `CurlSite.toSM`, `CurlSite.ofSM`,
`CurlSite.toSM_F`, `toSM_D`, `toSM_carried`, `toSM_u`, `toSM_t₀`, `toSM_α`, `toSM_β`, `toSM_θ`, `toSM_p`, `toSM_T`,
`CurlSite.ofSM_toSM`, `CurlSite.toSM_ofSM`, `CurlSite.u_unit`, `CurlSite.one`, `CurlSite.T_eq_u_iff`,
`CurlSite.doublePoints_finite`, `CurlSite.no_triple`, `CurlSite.ofCarried`, `CurlSite.ofCarried_toSM`,
`rotCurve_eq_sub_one`, `curl_homfly_eq`, `CVCurlData` (structure, fields `exists_curl`, `exists_curl'`, `disc`, `i`,
`ii`, `iii`, `iv`), `curl`, `curl_of_carried`, `CurlSite.next`.
