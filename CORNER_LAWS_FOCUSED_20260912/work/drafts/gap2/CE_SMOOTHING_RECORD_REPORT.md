# Row 90 ce:smoothing-record — statement fixed and PROVED (draft, statement review pending)

Written 2026-09-14 08:12 UTC / 4:12am ET on the pod (architect-prover subagent of the executor).
Deliverable: `work/drafts/gap2/CeSmoothingRecord.lean` (873 lines, 61 declarations). Nothing written
under work/lean. Companion inputs: GAP2_STATEMENTS_MEMO.md §2, §3(d), §4 "90", §5; Gap2Statements.lean §3-§5.

## 0. Status in one block

| item | value |
|---|---|
| file | `work/drafts/gap2/CeSmoothingRecord.lean` |
| compile | `cd work/lean && lake env lean ../drafts/gap2/CeSmoothingRecord.lean` — exit 0, **0 errors, 0 warnings**, ~7 s warm |
| main theorem | `SM.ce_smoothing_record : SM.CeSmoothingRecordData` (8 fields, one per printed clause) |
| `#print axioms SM.ce_smoothing_record` (on a /tmp copy) | `[propext, Classical.choice, Quot.sound, SM.lp_lm]` |
| `#print axioms SM.SpatialLink.recordIso_nonempty_of_cleanCuspSmoothings` | `[propext, Classical.choice, Quot.sound]` |
| `#print axioms SM.SpatialLink.P_eq_of_cleanCuspSmoothings`, `…lmF_eq_of_cleanCuspSmoothings` | `[propext, Classical.choice, Quot.sound, SM.lp_lm]` |
| `#print axioms …CleanCuspSmoothing.isDoubleOf_iff`, `…deriv_eq_of_isDouble`, `SM.CuspRoundingFamily.recordIsoEnd` | `[propext, Classical.choice, Quot.sound]` |
| admitted goals / new axioms / `axiom` keyword | none (grep clean) |
| dependence on rows 89, 91, 94 | none: no theorem of those rows is used; row 89's *conclusion* enters only as the hypothesis structure `CuspRoundingFamily L` (see §6 R-7) |
| imports | `SM.TransverseFront`, `SM.FrontRecordBridge`, `SM.FrontGeomModel`, `SM.PolynomialBlock` (work/lean only) |

`SM.lp_lm` is the registered literature interface lp:lm (work/lean/axiom-policy.json); it enters only
through `lmF`/`P` (the statement of the "Consequently" clause), exactly as in the accepted
`SM.ng_smoothing_record` (SM/FrontRecordBridge.lean, "standard axioms and SM.lp_lm (through P) only").

## 1. The printed text (reference/SM/sm-3-statesum.tex)

Statement 3173-3180 (corollary environment 3171-3182):
"For a front satisfying Lemma ce:rounding, define a permitted smoothed-front diagram by replacing
each cusp with one regular embedded oriented arc in a clean cusp neighbourhood, agreeing with the old
germs in endpoint collars and creating no crossing. Retain every double point with its original
height choice. Every such actual diagram has the same named decorated record as the diagram
D_ε = p(L_1) of the lemma, including crossing-free components. Consequently their source values
F_D(l,m) and campaign polynomials P_D(a,z) agree."

Proof 3184-3194: "A cusp replacement introduces no crossing visit and changes no successor of an old
visit along the oriented parameter circle. All crossing pairings, signs and O/U bits remain unchanged
because their germs lie outside the cusp neighbourhoods. The component correspondence is the identity
on the original circles, including those without crossings. Thus the two actual diagrams have a named
decorated-record isomorphism. Lemma rp:record-polynomial, with the same source construction of
Literature input lp:lm, gives equality of F_D; the common substitution of Theorem lp:core preserves
it. This is a scalar statement, not a classification of arbitrary relative arc embeddings or an
ambient completeness assertion."

Context read: ce:rounding 3029-3058 (statement) and its proof 3059-3170 (for what "clean cusp
smoothing", "collars", "clean neighbourhood V" mean in the construction), ce:scope 3197-3209.

## 2. Clause → field map (`SM.CeSmoothingRecordData`)

Every field is prefixed by `∀ {c} (L : SpatialLink c), 0 < c → L.CuspedProjection → …` ("For a front
satisfying Lemma ce:rounding", 3173: the lemma's hypotheses, sm-3:3031-3042). The definition sentence
3173-3176 is split at its four sub-clauses, following the accepted `FrontDomainDefinitionData`
(SM/FrontSmooth.lean §9), which splits ng:front-domain's rounding sentence into `rounding_discs`,
`rounding_arc`, `rounding_attachments`, `rounding_no_crossing`.

| tex | printed clause | field | Lean content |
|---|---|---|---|
| 3173-3175 | "define a permitted smoothed-front diagram by replacing each cusp with one regular embedded oriented arc" | `smoothing_arc` | for `r : L.CleanCuspSmoothing G`, `k : L.cuspSet`: `G i` is `C^∞`, 1-periodic (same parameter circles, parameter direction = orientation); `r.a k < k.1.2 < r.b k`, `r.b k − r.a k < 1`; `deriv (G k.1.1).γ ≠ 0` and `InjOn` on `Ioo (a k) (b k)` |
| 3175 | "in a clean cusp neighbourhood" | `clean_neighbourhood` | `IsDisc (r.U k)`, cusp point in `interior (U k)`, discs pairwise disjoint; projection points of `U k` lie on the closed arc `[a k, b k]` of the cusp's circle (`clean`), the closed arc lies in `U k` (`arc_in`) and carries no double point (`arc_simple`); the new arc stays in `U k` (`inside`) |
| 3175-3176 | "agreeing with the old germs in endpoint collars" | `endpoint_collars` | `∃ η > 0`, `G = p(L)` on `Ioo (a k) (a k + η) ∪ Ioo (b k − η) (b k)` (`collar`, change D-1); and `G = p(L)` at every parameter whose orbit avoids the open arcs of the circle (`agree`) |
| 3176 | "and creating no crossing" | `no_crossing` | no point of the smoothed curves meets a point of a replacing arc (`no_crossing`); consequence: `IsDoubleOf G p q → IsDoubleOf L.projLoop p q` (`isDoubleOf_iff`) |
| 3176-3177 | "Retain every double point with its original height choice." | `height_choice` | every double point of `p(L)` is a double point of `G` with `p(L)`'s value and velocity (`isDoubleOf_iff`, `eval_eq_of_isDouble`, `deriv_eq_of_isDouble`); in a reading `m : L.HeightMarking G S`, `S.overBit (m.Φ p) = true ↔ L.height p < L.height q` at every double point (`HeightMarking.over_iff`) |
| 3177-3178 | "Every such actual diagram has the same named decorated record as the diagram D_ε = p(L_1) of the lemma" | `same_record_as_endpoint` | `∀ (R : CuspRoundingFamily L) X, Nonempty ((R.fam.G 1).HeightMarking (R.fam.G 1).projLoop X) → ∀ G S, Nonempty (L.CleanCuspSmoothing G) → Nonempty (L.HeightMarking G S) → Nonempty (RecordIso S.record X.record)` |
| 3179 | "including crossing-free components" | `crossing_free_components` | `S.componentCount = c ∧ X.componentCount = c ∧ ∀ v, X.compOf (ι.Φ v) = ι.e (S.compOf v)` for the explicit `ι = R.recordIsoEnd hL r m mX` |
| 3179-3180 | "Consequently their source values F_D(l,m) and campaign polynomials P_D(a,z) agree." (consequence) | `source_and_polynomial` | same data as above → `lmF S = lmF X ∧ P S = P X` |

Printed PROOF sentences → module lemmas (not bundle fields, the trimming rule of SM/FrontRecordBridge.lean):

| tex | printed | Lean |
|---|---|---|
| 3184 | "introduces no crossing visit" | `CleanCuspSmoothing.isDoubleOf_iff : IsDoubleOf G p q ↔ IsDoubleOf L.projLoop p q` |
| 3184-3185 | "changes no successor of an old visit along the oriented parameter circle" | `CleanCuspSmoothing.occSetOf_eq : occSetOf G = occSetOf L.projLoop` (same parameters on the same oriented circles), `occEquiv` |
| 3185-3187 | "All crossing pairings, signs and O/U bits remain unchanged because their germs lie outside the cusp neighbourhoods" | `closedArcFree_of_isDouble`, `eventuallyEq_of_closedArcFree`, `deriv_eq_of_isDouble`, `crossSignOf_eq`; bits: the over rule is `L`'s height order on both sides (`HeightMarking.ofSmoothing.over_iff`, no transport needed) |
| 3187-3188 | "The component correspondence is the identity on the original circles, including those without crossings" | `HeightMarking.ofSmoothing` keeps `e : Fin c ≃ Fin S.Γ.c`; `HeightMarking.c_eq`, `componentCount_eq` |
| 3189 | "Thus the two actual diagrams have a named decorated-record isomorphism" | `HeightMarking.recordIso` (composite), `CleanCuspSmoothing.recordIso`, `SpatialLink.recordIso_nonempty_of_cleanCuspSmoothings` |
| 3190-3191 | "Lemma rp:record-polynomial … gives equality of F_D" | `lmF_eq_of_cleanCuspSmoothings` via the accepted `lmF_eq_of_recordIso` |
| 3191-3192 | "the common substitution of Theorem lp:core preserves it" | `P_eq_of_cleanCuspSmoothings` via the accepted `presentations` |
| 3192-3194 | "This is a scalar statement, not a classification … or an ambient completeness assertion" | `#print axioms`: no ambient-isotopy or spatial statement is used; only `SM.lp_lm` through `lmF`/`P` |

## 3. Definitions (file §1) and their provenance

All copied from Gap2Statements.lean §3-§4 (verified by `diff` of the structure field lines: identical
except for the addition below): `SpatialLink c` (T, smooth, periodic, embedded, regular), `projLoop`,
`height`, `IsCusp`, `cuspSet`, `ExactCuspGerm`, `CuspedProjection`, `RegularGenericProjection`,
`HeightMarking L G S`, `CleanCuspSmoothing L G`, `SpatialFamily`, `CuspRoundingFamily L`. Added:
`@[simp] projLoop_γ : (L.projLoop i).γ = xzOf (L.T i) := rfl` (harmless). NOT copied: the row bundles
of other rows (`CeRoundingData`, `ContactPathData`, …) and `SmoothKnotDiagram.Carries`.

**Change D-1 — `CleanCuspSmoothing.collar` (new field).**
`collar : ∀ k, ∃ η : ℝ, 0 < η ∧ ∀ t ∈ Set.Ioo (a k) (a k + η) ∪ Set.Ioo (b k - η) (b k), (G k.1.1).γ t = xzOf (L.T k.1.1) t`.
Why: the printed definition says the arc agrees "with the old germs in endpoint collars". The sketch
rendered this by `agree` alone (equality with the projection at every parameter whose orbit avoids the
OPEN arcs — the end points and everything outside; the accepted `GeomRounding.agree`, whose printed
source was "with the same oriented attachments", a weaker phrase). Equality outside the open arc does
NOT give germ agreement at the end points from inside: a `C^∞` loop can match the old arc and all its
derivatives at `a k` yet differ from it at every interior point (flat difference). `collar` + `agree`
give equality on a full neighbourhood of each end point, which is the printed germ agreement.
Realizability: ce:rounding's construction has it — the cutoff `ρ` has "support strictly inside
(−b,b)" (sm-3:3083-3084) and "vanishes on collars of the chart ends" (3105-3106). The proof of row 90
does not use `collar` (it is a definitional clause, restated in `endpoint_collars`); deleting the field
and the first conjunct of `endpoint_collars` compiles unchanged if the reviewer prefers the sketch's
reading. Consequence for other rows: `CuspRoundingFamily.clean` (row 89's conclusion) and row 91's
hypothesis `Nonempty (L.CleanCuspSmoothing G)` now refer to the strengthened class — row 89's proof
must supply collars (it does, see above); row 91's statement gets a smaller class of `S(F)`, which is
what "clean ordinary cusp smoothing" means with the collar clause.

**Which definitional clauses the proof consumes.** `CleanCuspSmoothing`: `a_lt`, `lt_b` (openness of
closed-arc-freeness needs `a k ≤ b k`), `arc_simple`, `agree`, `no_crossing`. `CuspedProjection`:
`cusps_finite` (openness argument, `Filter.eventually_all` over the finite cusp set) and
`heights_distinct` (the case split on the over branch in `HeightMarking.recordIso`). `CuspRoundingFamily`:
`clean 1`, `same_doubles 1`, `same_data 1`. The other clauses (`U`, `disc`, `center`, `disjoint`, `len`,
`clean`, `arc_in`, `collar`, `inside`, `regular`, `simple`; `exact_germ`, `doubles_finite`,
`transverse`, `no_triple`; `0 < c`) are transcriptions carried by the definitional fields only. This
is expected: the record depends on the germs at the double points, which lie outside the arcs.

## 4. Route (file §2-§6) against the accepted analogue

| accepted (ng:smoothing-record) | this file (ce:smoothing-record) |
|---|---|
| `SmoothFront F`, `F.comp i : SmoothLoop`, `F.Cusp` (Fintype) | `SpatialLink L`, `L.projLoop i : SmoothLoop`, `L.cuspSet` (finite by `CuspedProjection.cusps_finite`) |
| `F.GeomRounding G` | `L.CleanCuspSmoothing G` (+ `collar`) |
| `GeomRounding.closedArcFree_of_isDouble`, `isOpen_closedArcFree`, `eventuallyEq_of_closedArcFree`, `deriv_eq_of_isDouble`, `notMem_Ioo_of_double`, `isDouble_iff` (FrontSmooth §8) | `CleanCuspSmoothing.*` of the same names (file §2), with `hfin : L.cuspSet.Finite` where finiteness is needed; reused verbatim from the library: `SM.eventually_add_int_notMem_Icc`, `SameParam.*`, `SmoothLoop.eq_add_int`, `deriv_eq_add_int` |
| `GeomRounding.occSetOf_eq`, `occEquiv`, `eval_eq_iff`, `crossSignOf_eq` (FrontRecordBridge §3, FrontGeomModel §3) | `CleanCuspSmoothing.occSetOf_eq`, `occEquiv`, `eval_eq_iff`, `crossSignOf_eq` |
| `GeomMarking G S` (over = smaller `slopeOf G`) | `L.HeightMarking G S` (over = smaller `L.height`) |
| `Marking.ofGeom : GeomRounding → GeomMarking G S → F.Marking S` (transports meeting, slopes, signs) | `HeightMarking.ofSmoothing : CleanCuspSmoothing → L.HeightMarking G S → L.HeightMarking L.projLoop S` (transports meeting and signs; the over rule is literally the same on both sides) |
| `Marking.recordIso (m m' : F.Marking S/S') : RecordIso` (case split on `slope_ne_of_isDouble`) | `HeightMarking.recordIso (hd : heights distinct) (m m' : L.HeightMarking G S/S')` (case split on `hd`) |
| `recordIso_nonempty_of_geomModels`, `P_eq_of_geomModels` | `recordIso_nonempty_of_cleanCuspSmoothings`, `lmF_eq_of_cleanCuspSmoothings`, `P_eq_of_cleanCuspSmoothings` |
| — | §5 `CuspRoundingFamily.endSmoothing/endMarking/recordIsoEnd`: the end `D_ε = p(L_1)` is a permitted diagram, its own height reading converted to `L`'s (`HeightMarking.ofHeightOrder`) |
| `SmoothingRecordData` / `ng_smoothing_record` | `CeSmoothingRecordData` / `ce_smoothing_record` |

Size: ≈ 190 lines of docstring/header, ≈ 150 lines of copied vocabulary, ≈ 160 lines §2, ≈ 160 lines §3,
≈ 110 lines §4-§5, ≈ 110 lines §6. Compile 7 s.

## 5. Readings (how the printed words are rendered)

* **R-1 "a front satisfying Lemma ce:rounding"** = a spatial link `L : SpatialLink c` (smooth,
  1-periodic, jointly injective, nonvanishing derivative — sm-3:3031-3032) with `0 < c` ("nonempty
  union") and `L.CuspedProjection` (3033-3042: finitely many cusps, each with the exact germ; finitely
  many transverse double points; no triple point; distinct `y` at every double point). "The front" is
  the cusped projection `p(L) = L.projLoop`; the row is stated on `L` because the decoration ("height
  choice") needs `y`. "no cusps on another branch" is a consequence of `transverse` (a cusp branch has
  zero projected velocity, so the determinant vanishes). `0 < c` is never used by a proof (the theorem
  holds for `c = 0`).
* **R-2 "the spatial link"** = `SpatialLink c`: `T : Fin c → ℝ → Space`, `Space = ℝ × ℝ × ℝ` (accepted,
  SM/TransverseFront.lean), `embedded` = injective on the union of circles (`SameT`), orientation = the
  parameter direction (T-1).
* **R-3 "its cusped projection"** = `L.projLoop i := ⟨xzOf (L.T i), …⟩`, a `SmoothLoop` per circle, so
  the accepted plain-loop vocabulary (`IsDoubleOf`, `occSetOf`, `crossSignOf`, `OccOf`) applies; cusps
  = zeros of the projected velocity (`IsCusp`), `cuspSet` in the fundamental period.
* **R-4 "clean cusp smoothing" / "permitted smoothed-front diagram"** = a loop family
  `G : Fin c → SmoothLoop` on the SAME parameter circles (FR-4, parametrized replacement) with
  `L.CleanCuspSmoothing G`: per cusp a closed disc `U k` (`IsDisc`) and an arc `[a k, b k]`; clean =
  the projection meets `U k` only along that arc, which carries no double point; the new arc is
  regular, embedded, inside `U k`, creates no crossing, and agrees with the old arc outside the open
  arc and on end collars (D-1). "one … arc" = one parameter interval per cusp. "oriented" = traversed
  in the parameter direction (T-1).
* **R-5 "actual diagram" and FR-1 (polygonal reading).** No smooth `Diagram` exists in the accepted
  layer; the smoothed curves are read polygonally: a `Diagram S` with `L.HeightMarking G S` carries the
  named record of `G` (circles incl. crossing-free ones, occurrences = double-point parameters, cyclic
  orders on each oriented circle, pairing, over bit = smaller `y` of `L`, sign = over-first tangent
  determinant `sgn det_xz(u_O, u_U)` of `G`). This is the memo's FR-1 (accepted for ng:front-domain,
  cf:lem-rounding, def:transverse-front) with the height over-rule of cp:finite-contact-path / fd:contact
  (sm-3:3406-3407). Existence of a polygonal carrier is not asserted (as in ng:front-domain); the row
  quantifies over all carriers.
* **R-6 "Retain every double point with its original height choice"** = every double point of `p(L)`
  is a double point of `G` (with the same value and velocity), and the over bit is `L`'s height order
  at the two branches — `L`'s heights, not `G`'s slopes and not another link's heights.
* **R-7 "the diagram D_ε = p(L_1) of the lemma"** = for any `R : CuspRoundingFamily L` (the sketch's
  §4 structure: a family with the properties ce:rounding asserts — `L_0 = L`, fixed outside disjoint
  cusp intervals, every `λ > 0` slice regular generic, cleanly smoothing, same double points with the
  same signs and height order), the end `R.fam.G 1` and any polygonal reading `X` of its projection
  with ITS OWN heights (`(R.fam.G 1).HeightMarking (R.fam.G 1).projLoop X` — the actual diagram of the
  spatial link `L_1`). `R.clean 1` makes `p(L_1)` a permitted diagram of `L`; `R.same_doubles 1` and
  `R.same_data 1` ("retains every original crossing with its oriented decorated data") convert the
  reading to one with `L`'s heights (`endMarking`). The theorem of row 89 is NOT used; if row 89 is
  later proved, `same_record_as_endpoint` applies to its witness directly.
* **R-8 "the same named decorated record" / "the full named record"** = `Nonempty (RecordIso S.record
  X.record)` with the accepted `RecordIso` (SM/LinkRecord.lean: circles `e`, occurrences `Φ`,
  successor, pairing, bits, signs) — the reading of ng:smoothing-record; "including crossing-free
  components" = both `componentCount = c` and `compOf` compatibility of the explicit isomorphism.
* **R-9 "source values F_D(l,m)"** = `lmF S` (the accepted source function of lp:lm, `Classical.choose
  lp_lm`); **"campaign polynomials P_D(a,z)"** = `P S` (LocalPolynomial). Equality through the accepted
  `lmF_eq_of_recordIso` and `presentations` (rp:record-polynomial), which is exactly the printed proof's
  citation of rp:record-polynomial, lp:lm and lp:core.
* **R-10 "germs"**: rendered as `=ᶠ[nhds t]` equality of the smoothing and the projection
  (`eventuallyEq_of_closedArcFree`), from which velocity equality follows; the collar clause D-1 is the
  definitional form at the arc ends.

## 6. Fidelity risks (for the statement reviewer)

* **K-1 (D-1, divergence from the sketch).** `collar` strengthens `CleanCuspSmoothing` relative to
  Gap2Statements.lean. Consequences for rows 89/91 recorded in §3. Decision needed: propagate `collar`
  into the sketch (recommended: it is the printed text) or drop it here. Either way row 90's proof is
  unaffected.
* **K-2 (FR-1 polygonal reading).** The "actual diagram" is a polygonal `Diagram` carrying the record
  of a smooth loop family; the smooth object itself never becomes a `Diagram`. Same reading as the four
  accepted front rows; the reviewer of those rows accepted it. The alternative (a smooth `Diagram`
  class) does not exist in the layer.
* **K-3 (D_ε through `CuspRoundingFamily`).** `same_record_as_endpoint`, `crossing_free_components`,
  `source_and_polynomial` quantify over `R : CuspRoundingFamily L`, the unreviewed sketch rendering of
  row 89's conclusion. If that structure is revised, these fields follow (only `clean`, `same_doubles`,
  `same_data` at `λ = 1` are used, through `clean_end`, `same_doubles_end`, `height_lt_iff_end`). If
  `CuspRoundingFamily L` were empty for some `L` the fields would be vacuous for that `L`; the printed
  proof's pairwise content is carried unconditionally by `recordIso_nonempty_of_cleanCuspSmoothings`
  and `P_eq_of_cleanCuspSmoothings` (module theorems, §4), which the reviewer should read as the
  row's substance.
* **K-4 (non-vacuity of the class).** Consistency of `CleanCuspSmoothing` (with `collar`) is argued
  in the file's docstring against ce:rounding's construction but not kernel-checked; a witness is row
  89's business. The class mirrors the accepted `GeomRounding` v2, whose first version was found empty
  and repaired (SM/FrontRecordBridge.lean "Basis"); the repair (closed arc in `clean`, `arc_in`,
  `arc_simple`) is inherited.
* **K-5 (`IsDisc` convexity).** "clean cusp neighbourhood" is rendered by a convex compact disc with
  nonempty interior (accepted `IsDisc`), inherited from `GeomRounding`; convexity is an unprinted
  restriction on the class (ce:rounding's `V` is merely an open neighbourhood). Harmless for row 90
  (no proof uses `U`); a concern only for the existence rows 89/91.
* **K-6 (`0 < c`).** Kept as a printed hypothesis ("nonempty union" of ce:rounding), never used; the
  general theorems are stated without it.
* **K-7 (sign convention).** `HeightMarking.sgn_eq` fixes sign = over-first tangent determinant with
  over = smaller `y` (fd:contact's dictionary). The corollary itself says only "original height
  choice" and "named decorated record"; the convention is the one every consumer (rows 91, 94) uses.
* **K-8 (vocabulary duplication).** The file redeclares the sketch's `SM.SpatialLink` etc. under the
  same names (it cannot import a draft). Porting: the vocabulary must live in ONE library module
  (e.g. `SM/SpatialLink.lean`) imported by the row modules of 89, 90, 91; do not port both drafts as is.
* **K-9 (`same_record_as_endpoint` is not symmetric in form).** The printed clause compares every
  permitted diagram to D_ε; the field does exactly that. The pairwise statement is a module theorem and
  not a bundle field (no unprinted fields).

## 7. Changes relative to the memo's sketch (all recorded)

1. `CleanCuspSmoothing.collar` added (D-1, §3).
2. Bundle: the sketch's two pairwise fields `record_iso`, `polynomials_agree` are replaced by eight
   fields, one per printed clause (§2); the pairwise content is `SpatialLink.recordIso_nonempty_of_cleanCuspSmoothings`,
   `lmF_eq_of_cleanCuspSmoothings`, `P_eq_of_cleanCuspSmoothings`.
3. Hypothesis `0 < c` added to every field (the sketch's row-90 bundle had only `CuspedProjection`).
4. `D_ε` rendered explicitly through `CuspRoundingFamily` (the sketch's row-90 bundle did not mention
   it; the memo said "D_ε is one of them").
5. `@[simp] projLoop_γ` added; docstrings of the copied structures now cite tex lines.
6. Everything else verbatim (diff-checked).

## 8. Independence from rows 89, 91, 94

No declaration of the file depends on `CeRoundingData`, `ContactPathData`, `FdContactData`,
`AmbientIsotopyDescent` or any unproved declaration; `#print axioms` of every declaration lists only the
standard three axioms plus, where `lmF`/`P` occur, the registered `SM.lp_lm`. Row 89's *conclusion
shape* (`CuspRoundingFamily`) is a hypothesis of three fields, not a dependency on its proof.

## 9. Open items

1. **Statement review** (independent reviewer, given sm-3:3171-3195 and the Lean type of
   `CeSmoothingRecordData` only), per ACCEPT_CYCLE.md; then decide the module name (proposal:
   `SM/CeSmoothingRecord.lean` importing a shared `SM/SpatialLink.lean`) and the lean-declarations.json
   mapping. Until then: draft, not mapped.
2. **D-1 decision** for the sketch (K-1): propagate `collar` into Gap2Statements.lean's
   `CleanCuspSmoothing` (rows 89, 91) or not.
3. **Reuse for row 91**: with `AmbientIsotopyDescent` as an explicit hypothesis, `P S = P X` for row 91
   is `P_eq_of_cleanCuspSmoothings` (this file) + the descent clause + `lit_homfly`; the memo's ~500-line
   estimate for 91-given-the-gap stands and can start from §4-§5 here.
4. **Optional library extras** not needed by the row and therefore not included: `regular_everywhere`
   (the smoothed curves are regular closed curves), `transverse`, `no_triple` for `G` (the analogues of
   FrontSmooth §8's "resulting ordinary diagram" lemmas, ~80 lines) — add if row 91 or a DEFINE row for
   "smoothed-front diagram" needs them.
5. **FINAL_REVIEW sentence (proposed)**: "Row 90 ce:smoothing-record: statement fixed as
   `SM.CeSmoothingRecordData` (work/drafts/gap2/CeSmoothingRecord.lean; one field per printed clause on
   the spatial vocabulary `SpatialLink`, `CuspedProjection`, `CleanCuspSmoothing` (+ collar clause),
   `HeightMarking`, `CuspRoundingFamily`) and PROVED as `SM.ce_smoothing_record` (axioms: standard +
   `SM.lp_lm` through `lmF`/`P`); the printed proof's record isomorphism is
   `SpatialLink.recordIso_nonempty_of_cleanCuspSmoothings`; not blocked by any interface; statement
   review and porting pending; rows 89, 91, 94 not used."

## 10. Verification commands (run 2026-09-14 08:12 UTC / 4:12am ET)

```
source /workspace/envs/lean/env.sh
cd work/lean && lake env lean ../drafts/gap2/CeSmoothingRecord.lean          # exit 0, no output
cp ../drafts/gap2/CeSmoothingRecord.lean /tmp/ce90/CeSmoothingRecordAxioms.lean
# appended: #print axioms SM.ce_smoothing_record (and six more, §0)
lake env lean /tmp/ce90/CeSmoothingRecordAxioms.lean
#  'SM.ce_smoothing_record' depends on axioms: [propext, Classical.choice, Quot.sound, SM.lp_lm]
#  'SM.SpatialLink.recordIso_nonempty_of_cleanCuspSmoothings' depends on axioms: [propext, Classical.choice, Quot.sound]
wc -l ../drafts/gap2/CeSmoothingRecord.lean                                    # 873
grep -n "^axiom" ../drafts/gap2/CeSmoothingRecord.lean                          # nothing
diff <(sketch §3 structure field lines) <(this file §1 structure field lines)   # only `collar` added
```

## 11. Declaration inventory (61)

Structures (8): `SM.SpatialLink`, `SM.SpatialLink.CuspedProjection`, `SM.SpatialLink.RegularGenericProjection`,
`SM.SpatialLink.HeightMarking`, `SM.SpatialLink.CleanCuspSmoothing`, `SM.SpatialFamily`,
`SM.CuspRoundingFamily`, `SM.CeSmoothingRecordData`.

Definitions (14): `SpatialLink.{projLoop, height, IsCusp, cuspSet, ExactCuspGerm}`,
`SpatialLink.CleanCuspSmoothing.{ClosedArcFree, occEquiv, recordIso}`,
`SpatialLink.HeightMarking.{ofSmoothing, recordIso, ofHeightOrder}`,
`CuspRoundingFamily.{endSmoothing, endMarking, recordIsoEnd}`.

Theorems (39): `SpatialLink.{projLoop_γ, xz_add_int, xz_eq_of_sameParam, isDoubleOf_projLoop_iff}`;
`SpatialLink.CleanCuspSmoothing.{a_lt_b, cusp_mem_Ioo, eval_eq_of_notMem, ClosedArcFree.eval_eq,
isOpen_closedArcFree, eventuallyEq_of_closedArcFree, deriv_eq_of_closedArcFree, closedArcFree_of_isDouble,
eval_eq_of_isDouble, deriv_eq_of_isDouble, notMem_Ioo_of_double, isDoubleOf_iff, occSetOf_eq,
crossSignOf_eq, occEquiv_apply_val, occEquiv_symm_apply_val, eval_eq_iff}`;
`SmoothFront.OccOf.exists_partner`; `SpatialLink.HeightMarking.{c_eq, componentCount_eq,
partner_of_Φ_eq_twin, compOf_eq_e, compOf_eq_iff, visitBetween_iff, ofSmoothing_e, ofSmoothing_Φ,
recordIso_e, recordIso_Φ}`; `SpatialLink.{recordIso_nonempty_of_cleanCuspSmoothings,
lmF_eq_of_cleanCuspSmoothings, P_eq_of_cleanCuspSmoothings}`; `CuspRoundingFamily.{clean_end,
same_doubles_end, height_lt_iff_end}`; `SM.ce_smoothing_record`.
