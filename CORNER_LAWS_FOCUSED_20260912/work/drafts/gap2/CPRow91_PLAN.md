# Row 91 cp:finite-contact-path "modulo the descent clause" — plan, leaf table, fidelity risks, FINAL_REVIEW text

Architect note, 2026-09-14 (pod, subagent of the executor; lane commissioned AUTHOR_NOTES ~10:02Z).
Files (all under work/drafts/gap2/, nothing written under work/lean):

| file | content | check |
|---|---|---|
| `CPRow91_Statements.lean` (182 lines) | the frozen statements: `ContactPathData`, `AmbientIsotopyDescent`, `AmbientIsotopyLinkEquiv` (+ `.descent`), `AmbientIsotopy`, `AmbientIsotopyDescentLit`, `IsotopyExtension`, `ambientIsotopyDescent_of_lit`; NO sorry, NO axiom, NO row theorem; byte-identical to §1 of the skeleton (verified) | `cd work/lean && lake env lean ../drafts/gap2/CPRow91_Statements.lean` → exit 0 |
| `CPRow91_Skeleton.lean` (685 lines) | §1 the statements, §1.3-§5 the proof in five units (A-E), row theorem `SM.cp_finite_contact_path_of_descent : AmbientIsotopyDescent → ContactPathData` + two corollaries | exit 0, **0 errors, 0 sorry**; 58 declarations; `#print axioms cp_finite_contact_path_of_descent = [propext, Classical.choice, Quot.sound, SM.lit_homfly, SM.lp_lm, SM.lp_lm_uniqueness]` (the set of the accepted `presentations`/`P_eq_homfly`; `contactPath` and `toSmoothing` use only the standard three) |
| this file | plan, leaf table, unit table, FR-CP-1..FR-CP-10, FINAL_REVIEW paragraph | — |

Outcome in one sentence: **every leaf of the skeleton turned out to be provable now, so "row 91 modulo
the descent clause" is a THEOREM, not a skeleton** — the only thing between the accepted layer and row 91
is the Prop `SM.AmbientIsotopyDescent` (§1), and FINAL_REVIEW can say exactly that (§6).  Compile time
~9 s warm (imports SM.CeRounding only).

Inputs read: GAP2_STATEMENTS_MEMO.md (§1, §3(d), §4 "89/90/91", §5, §6), Gap2Statements.lean §3-§6,
SM/CeSmoothingRecord.lean (whole), SM/CeRounding.lean §1-§3 and §5-§6 (the `fam`/`witness`/`ce_rounding`
assembly), SM/LinkInterfaces.lean header + `HomflyClauses`/`lit_homfly`/`homfly`/`homfly_descent`,
PolynomialBlock `P_eq_homfly`/`presentations`/`lmF_eq_of_recordIso`, FrontRecordBridge/FrontGeomModel
(`IsDoubleOf`, `occSetOf`, `OccOf`, `crossSignOf`), sm-3-statesum.tex 3205-3330, AUTHOR_NOTES entries
~07:51Z (D-F10..D-F12), ~08:17Z (D-1, K-1..K-9), ~08:42Z (D-F13), ~09:05Z (CE-R1..CE-R11, D-2), ~09:40Z
(CE-R12/13), ~09:53Z, ~10:02Z.

## 1. The descent clause settled on (decision D-CP-1)

```lean
def AmbientIsotopyDescent : Prop :=
  ∀ {c : ℕ} (H : SpatialFamily c),
    (H.G 0).RegularGenericProjection → (H.G 1).RegularGenericProjection →
    ∀ X₀ X₁ : Diagram,
      Nonempty ((H.G 0).HeightMarking (H.G 0).projLoop X₀) →
      Nonempty ((H.G 1).HeightMarking (H.G 1).projLoop X₁) →
      homfly X₀ = homfly X₁
```
In words: along a jointly smooth family `H` of oriented spatial embeddings of the same `c` parameter
circles (the accepted `SpatialFamily`: every slice embedded and regular, orientation and component labels
carried by the parameter) whose two ends have ordinary finite regular generic `xz` projections, the
HOMFLY–PT values `homfly` of ANY polygonal readings (`HeightMarking`, over = smaller `y`, FR-1/CE-R1) of
the two end diagrams agree.  It is lit:homfly's fifth clause "Its value depends only on the oriented link
presented by D" read spatially, exactly the sentence consumed at sm-3:3313-3316.

**D-CP-1 (shape).**  The memo (§1, §6) named the gap in `LinkEquiv` form.  The skeleton keeps that form
as `AmbientIsotopyLinkEquiv` and proves `AmbientIsotopyLinkEquiv → AmbientIsotopyDescent`
(`AmbientIsotopyLinkEquiv.descent`, via the frozen `homfly_descent`), but takes the `homfly` form as THE
hypothesis of the row theorem, because it is the weakest clause the printed proof consumes: the proof
never needs a move sequence, only `H_{D_ε} = H_{D_T}`.  Consequences: (i) closing GAP-2 by the memo's
route (α) — a spatial descent field on the frozen interface — supplies `AmbientIsotopyDescent` directly;
(ii) closing by route (β) — formalising Reidemeister — supplies `AmbientIsotopyLinkEquiv`, and the
corollary `cp_finite_contact_path_of_linkEquiv` gives the row; (iii) the printed proof's own split is
also recorded: `AmbientIsotopy L₀ L₁` (a jointly smooth family of diffeomorphisms `Φ_s` of `ℝ³` with
smooth inverses, `Φ_0 = id`, compactly supported — "fixes the complement of a compact set" — with
`Φ_1 ∘ L₀ = L₁` as parametrized maps), `AmbientIsotopyDescentLit` (the literal literature premise: an
ambient isotopy gives equal `homfly` of the readings) and `IsotopyExtension` (every `SpatialFamily` is
carried by an ambient isotopy — the analysis of sm-3:3264-3313, TRUE by the isotopy extension theorem,
excluded by no policy, outside the horizon by effort ~3-5k lines), with
`cp_finite_contact_path_of_lit : AmbientIsotopyDescentLit → IsotopyExtension → ContactPathData` proved.
So FINAL_REVIEW can name what is missing BY POLICY (`AmbientIsotopyDescentLit`, or equivalently
`AmbientIsotopyDescent`) separately from what is missing BY EFFORT (`IsotopyExtension`).

**Why it is exactly Reidemeister's theorem for spatial isotopies, and why the frozen `SM.lit_homfly`
cannot supply it.**  `homfly := Classical.choose lit_homfly`, `lit_homfly : ∃ H : Diagram → R,
HomflyClauses H`, and every field of `HomflyClauses` (planar isotopy, RI, RII, RIII, the circle value,
the skein relation, `descent : LinkEquiv D D' → H D = H D'`) speaks about polygonal `Diagram`s and the
combinatorial relation `LinkEquiv := EqvGen (PlanarIsotopic ∨ RI ∨ RII ∨ RIII)`; `P` is defined from
`lmF := Classical.choose lp_lm` with clauses of the same kind, and `P_eq_homfly` identifies the two.  No
accepted declaration relates a `Diagram` to a point of `ℝ³`: the only bridge between the spatial class
and the polygonal class is `HeightMarking`, whose fields record the combinatorial data of ONE projection
(circles, occurrences, cyclic order, pairing, over bit, sign).  Hence any proof of `AmbientIsotopyDescent`
must turn the hypothesis — a smooth family of embeddings — into a fact about the two records, and the
only fact about two records that the frozen interface converts into `homfly X₀ = homfly X₁` is
`LinkEquiv X₀ X₁`: a finite chain of planar isotopies and Reidemeister moves between the two polygonal
diagrams.  Producing that chain from a smooth isotopy of the spatial links is Reidemeister's theorem
(general position of the projected isotopy: the projection of a generic isotopy changes the diagram only
by the three moves and planar isotopy; plus the PL/smooth bridge for the polygonal readings).  Design D2
(SM/LinkInterfaces.lean header, SOURCES/INDEX.md §D) declares that theorem outside the formal scope and
the axiom policy admits no sixth axiom.  Note the direction of the obstacle: in the standard model the
clause is TRUE (Reidemeister 1927 for PL links, its smooth version, and the isotopy extension theorem), so
hypothesising it introduces no falsehood; the gap is a scope exclusion on a frozen interface, not a
conjecture and not a logical independence claim.  Conversely `AmbientIsotopyDescent` is not weaker than
Reidemeister in any useful sense: since `homfly` is an opaque witness, a derivation of the `homfly` form
from the frozen clauses alone would work for every `LinkEquiv`-invariant `H`, i.e. would prove
`LinkEquiv X₀ X₁` itself.

## 2. `ContactPathData` (one field per printed clause; tex 3210-3233)

| tex | printed clause | field | provable now? |
|---|---|---|---|
| 3211-3213 | "Let C be a finite nonempty disjoint union of oriented parameter circles, and let L : C → ℝ³ be a smooth embedding with nonvanishing parameter derivative." | `link_class` (re-export of `SpatialLink` on `L`, `0 < c`) | yes, proved (E-3) |
| 3213-3218 | "Assume its xz projection F is regular except at finitely many cusps, each with the exact germ [cp:exact-cusp]" | `cusped_front` (`cuspSet.Finite`, `ExactCuspGerm` at every cusp) | yes (E-4) |
| 3219-3221 | "Assume the only multiple points of F are finitely many transverse double points, none at a cusp, and the two y values differ at every double point." | `double_points` (finite, transverse, no triple, `¬ IsCusp` at a double point, heights distinct) | yes (E-5; "none at a cusp" = CE-R3's theorem) |
| 3221-3225 | "Suppose a supplied jointly smooth family of oriented spatial embeddings G_t starts at this parametrized L and ends at T, whose specified xz projection D_T is an ordinary finite regular generic diagram." | `supplied_family` (joint smoothness, slices embedded/regular/periodic, `(F.G 0).T = L.T`, end cuspless + generic clauses) | yes (E-6) |
| 3225-3227 | "every clean ordinary cusp smoothing S(F), with smaller y over at the unchanged crossings" | `smaller_y_over` (`isDoubleOf_iff`, `no_crossing`, `over_iff`) | yes (E-7) |
| 3227-3230 | "has the same campaign polynomial as D_T: P_{S(F)} = P_{D_T}" | `endpoint_polynomial` (the memo's rendering, unchanged) | **only from `AmbientIsotopyDescent`** (E-2) |
| 3231 | "No contact condition is imposed on G_t or on the rounding family." | no field (asserts nothing; the hypotheses mention no `contactForm`) | — |

`endpoint_polynomial` verbatim (= GAP2_STATEMENTS_MEMO.md §4 "91" and Gap2Statements.lean §6, now on
the accepted vocabulary): `∀ {c} (L : SpatialLink c), 0 < c → L.CuspedProjection → ∀ (F : SpatialFamily c),
F.G 0 = L → (F.G 1).RegularGenericProjection → ∀ X, Nonempty ((F.G 1).HeightMarking (F.G 1).projLoop X) →
∀ G S, Nonempty (L.CleanCuspSmoothing G) → Nonempty (L.HeightMarking G S) → P S = P X`.

## 3. Unit table

| unit | content | leaves | lines | status |
|---|---|---|---|---|
| A (§1.3) | consequences of the clause: `P` form (`P_eq_homfly`), ends named by equations | 2 (+2 implications in §1) | 26 | PROVED |
| B (§2) | the flattened family `H_s`: `reparam`, `glue` (the gluing lemma, isolated), clocks, `contactPath`, its ends, join, slices, generic ends | 19 | 212 | PROVED |
| C (§3) | the polygonal reading of `D_ε` from the reading of `S(F)`: `toSmoothing` (inverse of `ofSmoothing`), `toHeightOrder`, `readingOfSmoothing`, existence | 4 | 73 | PROVED |
| D (§4) | `P_{S(F)} = P_{D_ε}` (row 90) and `P_{D_ε} = P_{D_T}` (descent on `H_s`) | 2 | 27 | PROVED |
| E (§5) | row 89 applied, the assembly of cp:endpoint-polynomial, the five hypothesis readings, the row theorem and two corollaries | 7 + 3 row theorems | 110 | PROVED |
| (F) | `IsotopyExtension` — NOT a leaf of the row theorem; a named Prop for the report; would be its own lane (sm-3:3264-3313, ~3-5k lines of analysis: uniform normal radius by compactness, cutoff-weighted normal extension of the velocity, ODE flow with smooth dependence, chain rule) | 0 | — | out of horizon by effort, not by policy |

The concatenation needed no hard gluing lemma: both halves are jointly smooth on all of `ℝ × ℝ` and
each is the CONSTANT `L` on its closed side of the join, so the glued map is `A + B − L` pointwise in the
vector space `ℝ³` and joint smoothness is a sum (`glue_joint_smooth`, 14 lines).  The printed argument
("every positive-order time derivative vanishes at the join … the chain rule gives joint smoothness")
is replaced by this identity — same fact, no one-sided derivatives (FR-CP-4).

## 4. Leaf table (statement in words, proof, tools, size, truth check, status)

Sizes are ACTUAL lines (everything is proved).  "Truth check" records the sanity performed.

### Unit A — consequences of the clause
| leaf | statement | proof | tools | lines | truth check | status |
|---|---|---|---|---|---|---|
| `AmbientIsotopyLinkEquiv.descent` | Reidemeister form ⇒ homfly form | `homfly_descent` on the produced `LinkEquiv` | LinkInterfaces | 2 | frozen clause applied literally | PROVED |
| `ambientIsotopyDescent_of_lit` | literal premise + isotopy extension ⇒ homfly form | apply `hlit` to `H.G 0, H.G 1` with `hext H` | — | 2 | — | PROVED |
| A-1 `AmbientIsotopyDescent.P_eq` | the clause for `P` | `rw [P_eq_homfly, P_eq_homfly]` | lp:core (`P_eq_homfly`) | 6 | sm-3:3316-3317 "Theorem lp:core identifies these original values with P" | PROVED |
| A-2 `P_eq_of_ends` | same, with `H.G 0 = L₀`, `H.G 1 = L₁` as equations | `subst` twice | — | 8 | avoids rewriting inside `HeightMarking (H.G 0) …` | PROVED |

### Unit B — the flattened family (sm-3:3254-3262)
| leaf | statement | proof | tools | lines | truth check | status |
|---|---|---|---|---|---|---|
| B-1 `SpatialFamily.reparam` | reparametrise a family by a smooth clock; jointly smooth | `comp` with `(φ ∘ fst, snd)` | `ContDiff.comp/prodMk`, `contDiff_fst/snd` | 5 | — | PROVED |
| B-2 `glue_joint_smooth` (the isolated gluing lemma) | if `A = L` on `[1/2,∞)` and `B = L` on `(−∞,1/2]`, the piecewise map is jointly `C^∞` | pointwise identity `= A + B − L` (funext, split_ifs, abel), then `add/sub` | `ContDiff.add/sub` | 14 | the identity checked in both branches | PROVED |
| B-3 `glue` (+ `glue_G_of_le`, `glue_G_of_lt`) | the glued `SpatialFamily`; its value on each side | `if`; `simp only [hs, ↓reduceIte]` | — | 5+6+6 | — | PROVED |
| B-4 `glue_G_half` | "Both branches equal L at the join" | from `hA`, `hB` at `1/2` | — | 6 | sm-3:3263 | PROVED |
| B-5/B-6 `roundClock_contDiff`, `pathClock_contDiff` | the clocks `1 − η(2s)`, `η(2s−1)` are `C^∞` | `Real.smoothTransition.contDiff.comp` | Mathlib SmoothTransition | 4+4 | η = `Real.smoothTransition` (FR-CP-3) | PROVED |
| B-7 `roundClock_of_half_le` | first clock `= 0` for `s ≥ 1/2` | `one_of_one_le`, `1 ≤ 2s` by linarith | — | 5 | — | PROVED |
| B-8 `roundClock_zero` | first clock `= 1` at `s = 0` | `smoothTransition.zero` | — | 5 | start is `L_1` | PROVED |
| B-9 `pathClock_of_le_half` | second clock `= 0` for `s ≤ 1/2` | `zero_of_nonpos` | — | 4 | — | PROVED |
| B-10 `pathClock_one` | second clock `= 1` at `s = 1` | `norm_num` (`smoothTransition.one`) | — | 4 | end is `T` | PROVED |
| B-11 `roundClock_mem`, `pathClock_mem` | clocks in `[0,1]` | `nonneg`, `le_one` | — | 6+3 | needed for "every slice is one of the supplied or proved embeddings" | PROVED |
| B-12 `roundHalf`, `roundHalf_G_of_half_le`, `roundHalf_G_zero` | `L_{1−η(2s)}`; constant `L` from the join on; starts at `L_1` | B-7 + `R.start`; B-8 | — | 2+4+4 | — | PROVED |
| B-13 `pathHalf`, `pathHalf_G_of_le_half`, `pathHalf_G_one` | `G_{η(2s−1)}`; constant `L` up to the join (`hF0`); ends at `T` | B-9 + `hF0`; B-10 | — | 2+5+4 | — | PROVED |
| `contactPath` | `H_s` = glue of the halves | B-3 with B-12, B-13 | — | 4 | cp:flattened-family 3258-3262 | PROVED |
| B-14 `contactPath_G_zero` | `H_0 = L_1` | `glue_G_of_le` + B-12 | `norm_num` for `0 ≤ 1/2` | 6 | "The literal endpoints are L_1, T" 3265 | PROVED |
| B-15 `contactPath_G_one` | `H_1 = T` | `glue_G_of_lt` + B-13 | — | 6 | idem | PROVED |
| B-16 `contactPath_G_half` | `H_{1/2} = L` | B-4 | — | 4 | 3263 | PROVED |
| B-17 `contactPath_slice` | every slice is some `L_λ` (λ ∈ [0,1]) or some `G_t` (t ∈ [0,1]) | case on `s ≤ 1/2`, B-11 | — | 15 | 3264 | PROVED |
| B-18 `contactPath_start_generic` | `D_ε` is regular generic | B-14 + `R.generic 1` | row 90's `CuspRoundingFamily.generic` | 5 | 3238-3239 | PROVED |
| B-19 `contactPath_end_generic` | `D_T` is regular generic | B-15 + `hT` | — | 6 | hypothesis | PROVED |

### Unit C — the reading of `D_ε` (sm-3:3243-3248)
| leaf | statement | proof | tools | lines | truth check | status |
|---|---|---|---|---|---|---|
| C-1 `HeightMarking.toSmoothing` | a polygonal reading of `p(L)` with `L`'s heights is a reading of any clean smoothing `G` of it | mirror of the accepted `ofSmoothing` with `occEquiv` in the other direction; `eval_eq_iff`, `crossSignOf_eq`, `isDoubleOf_iff` | CeSmoothingRecord §2-§3 | 22 | field for field the inverse of `ofSmoothing` (occurrences literally the same parameters) | PROVED |
| C-2 `toHeightOrder` | reading with `L`'s heights ⇒ reading with `L₁`'s, given the height-order iff at every double point | `ofHeightOrder` with roles swapped, `.symm` | CeSmoothingRecord §3 | 5 | — | PROVED |
| C-3 `CuspRoundingFamily.readingOfSmoothing` | the diagram `S` of `S(F)` (with `L`'s heights) carries `D_ε = p(L_1)` with `L_1`'s heights | `ofSmoothing r` → `toSmoothing R.endSmoothing` → `toHeightOrder` with `same_data`/`same_doubles` at λ = 1 | row 90's `endSmoothing`, `height_lt_iff_end`, `same_doubles_end` | 7 | this is the printed "identical named decorated records" made into a reading | PROVED |
| C-4 `exists_endpoint_reading` | `D_ε` has a polygonal reading as soon as `S(F)` has one | `⟨S, readingOfSmoothing⟩` | — | 5 | no carrier existence asserted (FR-CP-2) | PROVED |

### Unit D — the two equalities (sm-3:3249-3251, 3314-3318)
| leaf | statement | proof | tools | lines | truth check | status |
|---|---|---|---|---|---|---|
| D-1 `P_eq_endpoint_reading` | `P_{S(F)} = P_{D_ε}` (cp:smoothing-record) | `ce_smoothing_record.source_and_polynomial … .2` | accepted row 90 | 7 | the printed citation of ce:smoothing-record | PROVED |
| D-2 `P_endpoint_eq_of_descent` | `P_{D_ε} = P_{D_T}` from the clause on `H_s` | A-2 with `contactPath`, B-14, B-15, `R.generic 1`, `hT` | — | 8 | the GAP-2 step, consumed as hypothesis | PROVED (from `hdesc`) |

### Unit E — the row
| leaf | statement | proof | tools | lines | truth check | status |
|---|---|---|---|---|---|---|
| E-1 `exists_cuspRoundingFamily'` | ce:rounding supplies the family | `ce_rounding.exists_cuspRoundingFamily` | accepted row 89 | 3 | 3235-3237 | PROVED (port note: use the accepted name directly, drop the prime) |
| E-2 `endpoint_polynomial_of_descent` | cp:endpoint-polynomial from the clause | obtain `R`, obtain `Xε` (C-4), `calc` D-1, D-2 | — | 11 | 3317-3318 "Combining this equality with cp:smoothing-record" | PROVED |
| E-3 `link_class_reading` | field 1 | structure fields | — | 6 | — | PROVED |
| E-4 `cusped_front_reading` | field 2 | `CuspedProjection` fields | — | 3 | — | PROVED |
| E-5 `double_points_reading` | field 3 | fields + `CuspedProjection.not_isCusp_of_isDouble` (accepted, CeRounding §1) | — | 11 | — | PROVED |
| `RegularGenericProjection.cuspSet_eq_empty` | a regular projection has no cusp in the period | `ext`, `h.regular` | — | 7 | — | PROVED |
| E-6 `supplied_family_reading` | field 4 | structure fields + `hF0` + `hT` fields | — | 18 | — | PROVED |
| E-7 `smaller_y_over_reading` | field 5 | `isDoubleOf_iff`, `no_crossing`, `over_iff` | CeSmoothingRecord §2 | 9 | — | PROVED |
| `cp_finite_contact_path_of_descent` | **the row modulo GAP-2** | the six fields from E-2..E-7 | — | 9 | — | PROVED |
| `cp_finite_contact_path_of_linkEquiv` | from Reidemeister's theorem | `h.descent` | — | 2 | — | PROVED |
| `cp_finite_contact_path_of_lit` | from the literal premise + isotopy extension | `ambientIsotopyDescent_of_lit` | — | 3 | — | PROVED |

## 5. Fidelity risks FR-CP-1 .. FR-CP-10 (recorded BEFORE the row is stated in work/lean)

- **FR-CP-1 (tex 3221-3230; FR-1/GAP-1, = CE-R1).**  "D_T is an ordinary finite regular generic
  diagram" and "S(F)" are SMOOTH diagrams; `P` exists only on polygonal `Diagram`s, so both are read
  through `HeightMarking` and the row is quantified over the readings (`Nonempty (… HeightMarking …)` as
  hypotheses, the shape of the accepted row 90).  No existence of a polygonal carrier is asserted; for a
  smoothing/endpoint without a reading the row says nothing.  Same reading as def:transverse-front,
  ng:front-domain, rows 89/90.
- **FR-CP-2 (tex 3238-3239, 3243-3251).**  The printed proof uses "the diagram D_ε" of `L_1` as if it
  had a polynomial; here `P_{D_ε}` is `P Xε` for a reading `Xε` of `p(L_1)`, and the proof CONSTRUCTS one:
  the polygonal diagram `S` carrying `S(F)` also carries `D_ε` (unit C).  So display cp:smoothing-record is
  realised by the accepted row 90 applied to `Xε := S` (where it is `P S = P S`) — the content of
  ce:smoothing-record is absorbed into the transport `toSmoothing`, which is the same record-isomorphism
  argument (the accepted `ofSmoothing` reversed).  Fidelity is intact (the printed sentence "the two
  actual diagrams have identical named decorated records" is exactly what `readingOfSmoothing` states),
  but a reviewer should know the step is not a black-box citation of row 90 alone.
- **FR-CP-3 (tex 3254-3257).**  The printed `η` ("smooth and increasing, endpoint values 0, 1, every
  positive-order derivative zero at both endpoints; e.g. the normalized integral of exp(−1/(s(1−s)))") is
  `Real.smoothTransition` (Mathlib): `C^∞`, `0` on `(−∞,0]`, `1` on `[1,∞)`, values in `[0,1]`,
  monotone.  Strict increase is not used by the proof and not asserted.
- **FR-CP-4 (tex 3258-3264; = CE-R2).**  The printed `H_s` lives on `[0,1]`; `SpatialFamily` is indexed
  by all of `ℝ` and demands embedded regular slices everywhere.  `contactPath` is defined on `ℝ`, equals
  `L_1` for `s ≤ 0` and `T` for `s ≥ 1` (constant outside `[0,1]`), and its slices are exactly the
  `L_λ`, `G_t` with `λ, t ∈ [0,1]` (B-17).  Joint smoothness at the join is proved by the identity
  `H = A + B − L` in `ℝ³`, not by the printed vanishing of one-sided time derivatives — the same fact.
- **FR-CP-5 (tex 3221-3223).**  "a supplied jointly smooth family of oriented spatial embeddings G_t" is
  a `SpatialFamily` on ALL of `ℝ` — a hypothesis STRONGER than a family on `[0,1]` (a narrowing of the
  row's domain).  Any printed family on `[0,1]` becomes one by the clamp `t ↦ smoothTransition t`
  (as row 89 does, CE-R2), so nothing is lost, but the consumer (fd:contact / cf:thm-carrierfloor (C))
  must supply the family in this form.  Row 89's output is already of this form.
- **FR-CP-6 (tex 3223-3225).**  "ends at T, whose specified xz projection D_T": `T := F.G 1` and its
  "specified" diagram is `(F.G 1).RegularGenericProjection` read with `T`'s OWN heights (over = smaller
  `y` of `T`, the fd:contact convention sm-3:3406-3407) — `(F.G 1).HeightMarking (F.G 1).projLoop X`.
  Nothing else is "specified" by the text.
- **FR-CP-7 (tex 3264-3316).**  The isotopy-extension construction (normal charts, uniform normal
  radius, weighted normal extension of `∂_s H_s`, compactly supported field, ODE flow, orientation) is
  NOT formalised: the hypothesis `AmbientIsotopyDescent` is stated on the smooth FAMILY OF EMBEDDINGS,
  so it absorbs that step together with the literature premise.  The split is recorded
  (`AmbientIsotopy`, `AmbientIsotopyDescentLit`, `IsotopyExtension`, `cp_finite_contact_path_of_lit`);
  `IsotopyExtension` is true and provable in principle (its own lane if ever wanted).  `AmbientIsotopy`
  includes `compact_support` and smooth two-sided inverses, exactly what the printed flow delivers
  ("fixes the complement of a compact set and preserves ambient orientation" — orientation preservation
  follows from `start` by connectedness and is not a field).
- **FR-CP-8 (tex 3313-3316; THE GAP).**  "The retained global source premise yields H_{D_ε} = H_{D_T}"
  is consumed as the hypothesis `hdesc : AmbientIsotopyDescent`; the frozen `SM.lit_homfly` cannot
  supply it (§1).  The row theorem is CONDITIONAL and, per D-F11/D-F14, may be ported as library
  material after statement review but is NEVER mapped as implemented while GAP-2 is open.
- **FR-CP-9 (tex 3211, 3230; = CE-R8/K-6).**  `0 < c` ("nonempty") is a hypothesis of every field but is
  used by no proof (row 90's `source_and_polynomial` takes it and ignores it); "oriented" = parameter
  direction (T-1); "smooth embedding with nonvanishing parameter derivative" = `embedded` + `regular`
  (injective immersion of compact circles); the hypothesis fields 1-5 are read-backs of the structures
  (the accepted `CeRoundingData` pattern, CE-R7).
- **FR-CP-10 (tex 3231, 3319-3327).**  "No contact condition is imposed …" and the closing paragraph
  (cusped diagram at the join harmless because `H_s` is a spatial embedding throughout; the rounding is
  not Legendrian; no self-linking transported) are commentary: no field, nothing about `contactForm`
  or `sl` is stated.  The join slice `H_{1/2} = L` has a CUSPED projection and is a `SpatialLink` (B-16),
  which is all the descent clause needs of it.

## 6. Paragraph for FINAL_REVIEW (row 91)

"Row 91 cp:finite-contact-path: statement fixed as `SM.ContactPathData` (work/drafts/gap2/
CPRow91_Statements.lean; one field per printed clause of sm-3:3210-3233, on the accepted vocabulary of
rows 89/90).  The row is PROVED MODULO ONE NAMED CLAUSE: `SM.cp_finite_contact_path_of_descent :
SM.AmbientIsotopyDescent → SM.ContactPathData` (CPRow91_Skeleton.lean, 0 sorry; axioms = the standard
three + the registered `lit_homfly`, `lp_lm`, `lp_lm_uniqueness`), from the accepted rows 89
(`ce_rounding`), 90 (`ce_smoothing_record`), rp:record-polynomial and lp:core.  `AmbientIsotopyDescent`
is a `def … : Prop`, not an axiom: for a jointly smooth family of oriented spatial embeddings whose two
ends have ordinary regular generic xz projections, the HOMFLY–PT values of any polygonal readings of the
two end diagrams agree.  It is lit:homfly's fifth clause ('Its value depends only on the oriented link
presented by D') read on spatial isotopies — the single sentence of the printed proof (sm-3:3313-3316)
that the frozen interface cannot discharge: `SM.lit_homfly` states that clause as `HomflyClauses.descent`
over `LinkEquiv` (planar isotopy and the three Reidemeister moves between polygonal diagrams; design D2),
and passing from a smooth spatial isotopy to such a move sequence is Reidemeister's theorem, declared
outside the formal scope with no sixth axiom admitted.  The clause is a true theorem of mathematics
(Reidemeister + isotopy extension), so the conditional row asserts nothing false; the gap is a scope
exclusion, not a conjecture.  Three equivalent-by-implication forms are recorded: `AmbientIsotopyDescent`
(what the proof consumes), `AmbientIsotopyLinkEquiv` (Reidemeister's theorem proper; implies the first
through the frozen descent), and `AmbientIsotopyDescentLit ∧ IsotopyExtension` (the printed proof's own
split into the literature premise on an actual ambient isotopy and the isotopy-extension analysis of
sm-3:3264-3313, the latter provable in principle, ~3-5k lines).  The declaration is library material
(D-F11/D-F14) and is not mapped as implemented; consequently rows 94, 99(C), 100(a_floor), 103, 105,
thm:C-S7, thm:C-soft, thm:comparison, cor:C-inherits and SM:corner_laws_and_soft remain open with this
single reason."

## 7. What closing GAP-2 would take, per form (for Mark; not decided here)

| form | what must be built | policy | effort |
|---|---|---|---|
| `AmbientIsotopyDescent` by route (α) | a spatial descent field on the frozen `HomflyClauses` (type change of `SM.lit_homfly`) — needs `SpatialLink`/`SpatialFamily`/`HeightMarking` in LinkInterfaces' import closure, re-acceptance of every consumer of the axiom | policy change on a frozen interface | small in code, large in process |
| `AmbientIsotopyLinkEquiv` by route (β) | Reidemeister's theorem for smooth isotopies of polygonal readings (general position of the projected isotopy, the PL bridge) | none (a theorem) | multi-thousand lines; out of horizon |
| `AmbientIsotopyDescentLit` + `IsotopyExtension` | the literal fifth clause on `AmbientIsotopy` (same status as (α)) PLUS the isotopy extension theorem for `SpatialFamily` (pure analysis, sm-3:3264-3313) | (α)'s status for the first; none for the second | second part ~3-5k lines |

## 8. Porting notes (after the statement review; NOT before)

- Module: `work/lean/SM/ContactPath.lean` (or `CpFiniteContactPath.lean`), import `SM.CeRounding`.  Map
  NOTHING in lean-declarations.json as implemented (D-F11); FINAL_REVIEW carries §6.
- Names checked against work/lean (grep): `ContactPathData`, `AmbientIsotopy*`, `IsotopyExtension`,
  `SpatialFamily.reparam/glue`, `roundClock/pathClock`, `CuspRoundingFamily.roundHalf/pathHalf/contactPath/
  readingOfSmoothing/exists_endpoint_reading`, `HeightMarking.toSmoothing/toHeightOrder`,
  `RegularGenericProjection.cuspSet_eq_empty`, `AmbientIsotopyDescent.P_eq/P_eq_of_ends` — no clash in
  SM/CV/RProof (`SM/Curl.lean` has a namespaced `η`; the skeleton uses `Real.smoothTransition` directly).
- Drop `exists_cuspRoundingFamily'` at port time (use `ce_rounding.exists_cuspRoundingFamily`).
- The linter is clean except for nothing; compile ~9 s warm.
- Statement review brief should cite FR-CP-1..FR-CP-10 and the D-CP-1 shape decision, and ask the reviewer
  to compare `endpoint_polynomial` with the memo's §4 "91" rendering (identical) and `ContactPathData`'s
  fields 1-5 with sm-3:3211-3227.
