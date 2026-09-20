# PLAN_FINAL — contact lane: `SM.src_contact`, `SM.sl`, rows 94 / 161 / 162

Judge, 2026-09-15 (panel D-GAP2-4: DESIGN_A.md / Sketch_A.lean, DESIGN_B.md / Sketch_B.lean).
Statements: `work/drafts/contact/Statements_FINAL.lean` — typechecks
(`cd work/lean && lake env lean ../drafts/contact/Statements_FINAL.lean`; one `sorry`, the row theorem
`SM.fd_contact`, which `CV.ax_slbound` inherits; `SM.fd_contact_of_units` PROVED with axiom footprint
= the five registered literature axioms + `SM.src_contact` + standard; `SM.src_contact_iff_consequence`
standard axioms only; `CV.ax_etnyre` PROVED from `SM.src_contact` alone).

## 0. Verdict

**Winner: DESIGN B (proof feasibility), with four fidelity grafts from DESIGN A.**

| | A | B | why |
|---|---|---|---|
| FIDELITY | 8 | 7 | Same core (∃-form over `r`, `tb`; one field per printed formula; `T₊` = every `IsPositivePushoff`; `sl` = row-88 `selfLinking` ε-free; transverse clause over `TransverseKnot`; equivalence theorem). A follows the `ng_finite_word` precedent exactly (a field only for clauses with formal content; convention / consequence sentences are theorems, not axiom fields) and records 10 FR-SC items; B adds three PROVABLE fields (`contact_space`, `positive_orientation`, `cusps_down_or_up`) — never stronger than printed, but an axiom carrying theorems of the accepted layer is the kind of thing an interface reviewer flags, and B's own D-SC-5 leaves it to the reviewer. A's row 161 keeps the printed shape (a front DIAGRAM `D` with the vertical-tangency hypothesis on `D`); B states it on `K.T`. A names the number `SM.sl`. |
| CONSISTENCY | 9 | 9 | Both true on the accepted definitions. Judge's independent probe (§4): transverse unknots (both architects' curves) give Gauss `sl = −1.0000 =` front writhe; for the 2-cusp Legendrian eye (w = 0, D = U = 1) an explicit annulus of the accepted `IsPushoffAnnulus` shape has a positive circle whose front acquires exactly one kink crossing at the DOWN cusp (sign −1) and Gauss `sl = −0.9998 = w − D = tb − r`. Both sign audits (observer `−∂_y`, `det(e_x, e_z, −e_y) = +1`, over = smaller y / smaller slope, `∂_y` pushoff = blackboard framing) are correct. |
| FEASIBILITY | 6 | 9 | B's assembly `fd_contact_of_units` is kernel-checked end to end from four named unit Props (rows 84 → 87 → axiom → 93 → 91, including the `obtain … rfl` on the pushoff and the row-91 application); A's assembly stops at a `sorry` before the `sl` transport. B's period-2π `sl` (through `K.circle`) and the reparametrization FAMILY `ρ_s = (1−s)·id + s·ρ` remove A's hard step H3 (change of variables in the periodic Gauss double integral, B-3 / B-3′, 300-500 lines) entirely — everything about `sl` is row 88. B's `LegendrianPackage` + `U_package_of` is proved through `ce_rounding.exists_family` / `endSmoothing`. B's estimate (4,600) is the realistic one; A's B-5 at 300-500 lines is optimistic against the order-3 Leibniz computation under `u = y − y₀`. |
| REUSE | 7 | 8 | B's unit Props (`U_reading : ∀ F : SmoothFront, ∃ S, Nonempty (F.Marking S)` is the FR-1 existence statement every front consumer lacked; `TransverseKnot.circle/spatial`; eta bridges TN ↔ GF) are first-class, parallelizable, and reusable by the floor lane (99(C) consumes only `fd_contact`). A's period-generic `slOf P` has no second consumer. |

Grafts from A into B (all applied in Statements_FINAL.lean):
1. **Field set** = the four printed formulas only (`rotation`, `thurston_bennequin`, `pushoff_self_linking`,
   `transverse_front_writhe`); B's three convention fields become theorems next to the axiom
   (`lcContactForm_toE3`, `alpha_eq_lcContactForm`, `gf_alpha_eq_lcContactForm`, `isPositiveTransverse_iff`,
   and the accepted `SmoothFront.downCount_add_upCount`), cited in the module docstring table (precedent:
   `SM.ng_finite_word`, FrontInterfaces.lean:448-480).
2. **`SM.sl (K : TransverseKnot) : ℝ`** is the name of the document's number (`:= slCircle K.circle`, B's route).
3. **`IsLegendrianFrontOf L F`** (A's one-predicate reading of "an oriented Legendrian front", fields `hyp :
   GenericFrontHyp L`, `one : F.c = 1`, `front : (F.comp i).γ t = GenericFront.front L (2πt)`), in row 87's
   vocabulary — the axiom's only consumer is row 87's output `L_T`, so the assembly needs no eta bridge on
   the Legendrian side (`pkg.F_front`, `hpos2` are used verbatim); `IsLegendrianFrontOf.unique` proved.
4. **Row 161 in printed shape**: `∀ (D : SmoothKnotDiagram) (K : TransverseKnot), K.front = D →
   (∀ t, (D.vel t).1 = 0 → 0 < (D.vel t).2) → sl K = D.writhe`, inside B's CV bundle pattern
   (`CV.AxEtnyreData`, like `CV.AxHomflyData`).

Kept from B: coordinate bridges, `TransverseKnot.circle` / `spatial` / `spatial_projLoop`, `slCircle`,
`SrcContactConsequence` + `srcContact_iff_consequence` (renamed `src_contact_iff_consequence`),
`FdContactData`, `CV.AxSlboundData`, `ax_etnyre_of` / `ax_slbound_of`, eta bridges §5.0, units U0-U6,
`LegendrianPackage`, `fd_contact_of_units`, `U_package_of`.

## 1. What the judge verified

* Both sketches typecheck (Sketch_A: 9 `sorry` bridge lemmas + assembly; Sketch_B: zero `sorry`,
  `#print axioms` as claimed).  Statements_FINAL.lean typechecks (§0).
* Registry text read: sm-3:3341-3365 (src:contact), 3404-3492 (fd:contact + proof), 3012-3022
  (rem:sl-convention), 3328-3339 (def:transverse-front), 2486-2505 (the pushoff annulus of row 84's proof:
  "A sufficiently small positive circle is therefore the positive pushoff in the source convention"),
  1825-1834 (ng:front-domain), d10_axioms.tex:387-425 (CV 161/162); Etnyre §2.2 (3), §2.6.2 (5)/(7),
  §2.6.4 (9), §2.9 Fig. 23-24, Warning, Lemma 2.22 (17) (SOURCES/audit/L-3_EXIT/work/etnyre_p4-20.txt).
* Accepted vocabulary read: `selfLinking`/`linking`/`gaussDensity`/`lcCrossingSign`/`TransverseFamily`/
  `IsPositiveTransverseEmbedding` (LinkingCalculus.lean 360-640), `LinkingCalculusData` (Row), rows 84/87
  statements (TransverseNeighborhood.lean 47-212, GenericFront.lean 52-220), `SmoothFront` fields +
  `IsDownCusp`/`slope`/`IsOverUnder`/`Marking`/`GeomRounding`/`Rounding` (FrontSmooth.lean), `TransverseKnot`
  + `front` (TransverseFront.lean), `NgBoundClauses.ng_input`, `ContactPathData.endpoint_polynomial`
  (ContactPathOfDescent.lean 101-170), `SpatialLink`/`HeightMarking`/`CuspedProjection`/
  `RegularGenericProjection`/`CleanCuspSmoothing`/`SpatialFamily`/`CuspRoundingFamily` (CeSmoothingRecord
  141-330), `CeRoundingData.exists_family`, `frontRecord`, `markingRecordIso`, `U8R.recordIso`,
  `U8R.sweep_proof`, `word_ne_nil`, `realizeRecordIso` (needs `W.letters ≠ []`, supplied), `RecordIso`,
  `record_succ_no_between`, `cycNext_no_between` and the successor-uniqueness lemma (FrontRowsW2 ~13480-13550).
  Mathlib: `Real.smoothTransition` (+ `.contDiff`, `zero_of_nonpos`, `one_of_one_le`), `ContDiffOn.comp_contDiff`.
* Consistency probe (`work/drafts/contact/probe_judge.py`, run with a numpy python, e.g. /workspace/envs/persona/bin/python): §4.
* Precedent for sentence → field policy: `SM.ng_finite_word` docstring ("the remaining sentences are
  theorems here … which add no clause").  Pattern for the ∃-form: `SM.lit_homfly : ∃ H, HomflyClauses H`,
  `homfly := Classical.choose lit_homfly`.
* Names: policy name `SM.src_contact` (axiom-policy.json); cv-lane plan §161/§162 fixes `theorem CV.ax_etnyre`,
  `theorem CV.ax_slbound`; row 94 is `SM.fd_contact` (FINAL_REVIEW row table, GAP-2 memo).  No entry for these
  rows exists yet in lean-declarations.json.

## 2. The chosen statements — sentence by sentence

### 2.1 src:contact (sm-3:3341-3365) → `SM.src_contact`

| tex | printed | rendering |
|---|---|---|
| 3342-3345 | "Use standard contact space (ℝ³, ker(dz − y dx)), with positive transverse orientation z′ − y x′ > 0 (Etnyre §2.1, 2.4)" | conventions; theorems `lcContactForm_toE3` (`rfl`), `alpha_eq_lcContactForm`, `gf_alpha_eq_lcContactForm` (`rfl`), `isPositiveTransverse_iff` (`Iff.rfl`); NO field (FR-SC-8) |
| 3345-3351 | "Etnyre's front and pushoff statements give, for an oriented Legendrian front with downward and upward cusp counts D, U" | binder `∀ L F, IsLegendrianFrontOf L F →`; `D = F.downCount`, `U = F.upCount`, `w = F.writhe` on the accepted class `SmoothFront` (row 73) |
| 3349-3351 | "every cusp of an oriented front is traversed either downward or upward, so the total cusp count in his tb formula is D+U" | the accepted theorem `SmoothFront.downCount_add_upCount : D + U = #cusps`; NO field (FR-SC-6) |
| 3352 | `r = (D − U)/2` | `rotation : r L = ((D:ℝ) − U)/2` |
| 3352 | `tb = w − (D + U)/2` | `thurston_bennequin : tb L = (w:ℝ) − ((D:ℝ) + U)/2` |
| 3353 | `sl(T₊(L)) = tb(L) − r(L)` | `pushoff_self_linking : ∀ T′, GenericFront.IsPositivePushoff L T′ → slCircle T′ = tb L − r L` |
| 3355-3357 | "(For the second formula … Geiges Prop. 3.5.9 …; Etnyre's (7) reduces to his Remark 2.14 …)" | provenance; NO field |
| 3358-3363 | "For a generic positive transverse front (Definition def:transverse-front), self-linking equals its front writhe: Geiges Lemma 3.3 …; Etnyre's equation (9) states it." | `transverse_front_writhe : ∀ K : TransverseKnot, sl K = (K.front.writhe : ℝ)` |
| 3363-3364 | "These are the local front and pushoff source formulas only." | scope; NO field |

Readings of the literature's quantities on the accepted vocabulary:
* "an oriented Legendrian front" = `IsLegendrianFrontOf L F`: `L : ℝ → E3` a smooth embedded 2π-periodic
  circle with `α(L′) = 0` (`GenericFrontHyp`, rows 84/87; orientation = parameter direction, T-1), `F : SmoothFront`
  with one circle whose loop is `t ↦ (x(2πt), z(2πt))`.  The front of `L` is unique (`IsLegendrianFrontOf.unique`),
  so `r L`, `tb L` are functions of `L`.
* `D`, `U`: `IsDownCusp` = "traversed from its locally upper arm to its locally lower arm" (FR-2, FrontSmooth 457)
  = Etnyre's down cusp ("positive when going down a cusp", §2.6.2).
* `w`: `SmoothFront.writhe`, over = smaller slope (`IsOverUnder`), sign `sgn det(u_O, u_U)` = Etnyre §2.2 (3) with
  "the positive y axis goes into the page" (observer at `y = −∞`, plane basis `(∂_x, ∂_z)`, `det(e_x, e_z, −e_y) = +1`).
* `T₊(L)`: `GenericFront.IsPositivePushoff L T′` — a positive circle `B(·, s₀)`, `0 < s₀ < b`, of a pushoff annulus
  transverse to `ξ` (FR-TN-4, the document's own reading, sm-3:2501-2502; Etnyre §2.9 Fig. 23 `L₊ = S¹ × {½}`);
  quantified over EVERY such pushoff (all are transversely isotopic, Etnyre p. 19; `sl` is an isotopy invariant).
* `sl`: `slCircle` on the fd block's circle `ℝ/2πℤ` (§2.2), the document's fd:framed-linking number made ε-free.
* "a generic positive transverse front" = `K.front` for `K : TransverseKnot` (row 92; "the knot T is named separately").

### 2.2 `SM.sl` (fd:framed-linking sm-3:2820-2824 through row 88)

```lean
theorem IsPositiveTransverseEmbedding.constFamily (h : IsPositiveTransverseEmbedding (2π) T) :
    TransverseFamily (2π) (fun _ => T)                                              -- proved
def slCircle (T : ℝ → E3) : ℝ :=
  if h : IsPositiveTransverseEmbedding (2 * π) T then
    selfLinking (2 * π) T
      (Classical.choose (fd_linking_calculus.transverse_uniform (2 * π) (fun _ => T) h.constFamily))
  else 0
def TransverseKnot.circle (K) : ℝ → E3 := fun θ => toE3 (K.T (θ / (2 * π)))   -- ℝ/ℤ → ℝ/2πℤ
def sl (K : TransverseKnot) : ℝ := slCircle K.circle
```
Real-valued; the radius is row 88's `ε₀` for the constant family, fixed once; U1a proves the value is
`selfLinking (2π) T ε` for EVERY admissible `ε`; integrality of `sl` on transverse knots is the axiom's
transverse clause (`sl K = ↑writhe`), not a prerequisite.  Period 2π is the fd block's `S¹` (FR-LC-1,
sm-3:2398); def:transverse-front's `ℝ/ℤ` knot is bridged by `circle` (definitional in the proof route).

### 2.3 Row 94 fd:contact (sm-3:3404-3423) → `SM.FdContactData`, `theorem SM.fd_contact`

| printed | field |
|---|---|
| "In the xz front page the smaller-y branch is over, and its crossing sign is sgn det_xz(u_O,u_U)" | `over_rule_sign : ∀ K s t, K.front.IsDouble s t → (K.front.isOver s t ↔ yOf K.T s < yOf K.T t) ∧ K.front.crossSign s t = sign (det (vel s) (vel t))` — definitional on row 92, PROVED (`fdContact_over_rule_sign`) |
| display fd:front-writhe | `front_writhe : ∀ K, sl K = ↑K.front.writhe` — PROVED from the axiom (`fdContact_front_writhe`) |
| "Let T be an individual smooth positive transverse knot whose specified xz projection D_T is an ordinary finite regular generic diagram. With P_T … one has [fd:representative-bound]" | `representative_bound : ∀ K X, Nonempty (K.spatial.HeightMarking K.spatial.projLoop X) → sl K ≤ ((-degAZ (P X) - 1 : ℤ) : ℝ)` |
| the two closing sentences (3418-3421) | commentary; no field |

`T` = every `TransverseKnot` (def:transverse-front IS "smooth positive transverse knot whose xz projection
is an ordinary finite regular generic diagram"); `D_T` read polygonally (FR-1) by `SpatialLink.HeightMarking`
of the one-component `K.spatial` (over = smaller `y`), the SAME reading row 91 uses for its endpoint (so no
`Carries`-to-`HeightMarking` bridge; the GAP-2 memo's `Carries` is not in work/lean and is dropped);
`P_T = P X` for every reading `X` (independent of `X` by rp:record-polynomial, not re-proved here).

### 2.4 Rows 161 / 162 → `CV.AxEtnyreData` / `CV.AxSlboundData`, theorems `CV.ax_etnyre`, `CV.ax_slbound`

```lean
structure CV.AxEtnyreData : Prop where
  self_linking_eq_writhe : ∀ (D : SmoothKnotDiagram) (K : TransverseKnot), K.front = D →
    (∀ t, (D.vel t).1 = 0 → 0 < (D.vel t).2) → sl K = (D.writhe : ℝ)
structure CV.AxSlboundData : Prop where
  bound : ∀ (K : TransverseKnot) (X : Diagram), Nonempty (K.spatial.HeightMarking K.spatial.projLoop X) →
    sl K ≤ ((-degAZ (homfly X) - 1 : ℤ) : ℝ)
theorem CV.ax_etnyre_of : FdContactData → AxEtnyreData          -- proved
theorem CV.ax_slbound_of : FdContactData → AxSlboundData        -- proved (P_eq_homfly)
theorem CV.ax_etnyre : CV.AxEtnyreData                          -- PROVED from src_contact_spec
theorem CV.ax_slbound : CV.AxSlboundData := CV.ax_slbound_of fd_contact
```
161: "a front diagram of a transverse knot" = `D` with `K.front = D`; "with no downward vertical tangency" =
the printed hypothesis kept explicitly on `D` (redundant on the class: `front_vertical_up`); `sl(T)` = SM's `sl`
(CV: "presupposes the contact-geometric definition of sl; this document never defines it").  D-F10 (iii)
SUPERSEDED: an independent `sl` exists (row 88 accepted), so 161 is a theorem about the real number, and the
parametrised bundle `CV.SlBoundData (sl)` is not needed.  162: recorded narrowing to `TransverseKnot`
(fd:contact's own domain; the only consumer thm:carrierfloor (C) applies it to the constructed lift `K_T`
with front `T`, d3_floor:930-987); "the knot it presents" → `homfly X` for a reading `X` (FR-1), ax:homfly's
normalization = `CV.ax_homfly`'s map = `SM.homfly`.

## 3. Fidelity risks — record in AUTHOR_NOTES BEFORE stating the axiom

FR-SC-1 (∃-form over undefined `r`, `tb`).  The document never defines `r`, `tb`; the ∃-form is PROVABLY
  equivalent to the substituted consequence (`src_contact_iff_consequence`: `sl(T₊) = w − D` on the Legendrian
  class ∧ `sl = w` on the transverse class) — no hidden content, neither stronger nor weaker than the display with
  `r`, `tb` eliminated.  Reviewers must accept the ∃ pattern (as for lit:homfly, lp:lm).
FR-SC-2 (domain of the Legendrian formulas — WEAKER than printed, safe).  Printed: "an oriented Legendrian front"
  (Etnyre: any front with generalized cusps).  Lean: knots only (`F.c = 1`), fronts on ng:front-domain
  (semicubical cusps with `x″ ≠ 0`, transverse double points, no triple point, cusps alone; "no vertical tangency
  on regular arcs" is automatic for Legendrian fronts).  The consumer's instance `L_T` (exact germs) is inside.
FR-SC-3 (`T₊(L)` = every positive circle of every transverse pushoff annulus).  The literature's `T₊(L)` is a
  transverse-isotopy class; quantifying over every `IsPositivePushoff` is what it MEANS on the accepted vocabulary
  (FR-TN-4).  The accepted annulus is transverse to `ξ` along `s = 0` too (row 84's own construction).
FR-SC-4 (which `sl`).  `sl` is the document's `selfLinking` (fd:framed-linking) made ε-free through row 88; the
  identification with Etnyre's / Geiges' `sl` is rem:sl-convention — a REMARK, the document's own reading, which
  fd:contact's printed proof cites (3441-3443).  Sign/normalization checked by the judge's probe (§4).
FR-SC-5 (parametrizations).  Legendrian clauses on `E3`, period 2π (rows 84/87's objects); the transverse clause
  on def:transverse-front's period-1 `Space` knot through `circle` (period 2π).  The Gauss integral is
  parametrization-free (FR-LC-1); the bridges are theorems (U0, U1), not axiom content.
FR-SC-6 (D + U).  "every cusp … either downward or upward" is the accepted `downCount_add_upCount`; not a field.
FR-SC-7 (front writhe of a transverse front).  Over = smaller y, sign `det_xz`: accepted row 92; consistent with
  row 88's observer `ν = −∂_y` and Etnyre's "y into the page".
FR-SC-8 (no field for the convention / provenance / scope sentences).  As for ng:finite-word; the conventions
  are `rfl` theorems in the module.
FR-SC-9 (`slCircle` off its domain).  `slCircle T = 0` when `T` is not a 2π-periodic positive transverse embedding;
  every field applies it only on the class (pushoffs are positive transverse by `IsPushoffAnnulus.positive`;
  `K.circle` by U0).  The default is never exercised (as `degAZ`'s 0-at-0, FR-NB).
FR-SC-10 (real-valued).  `r`, `tb`, `sl : ℝ` (the literature's `(D−U)/2` is a half-integer); integrality of `sl` on
  transverse knots is a CONSEQUENCE of the axiom.  Rows 94/161/162 compare reals with integer casts, as printed.
FR-SC-11 (truth rests on Etnyre's naming of `T₊`).  Etnyre's Warning: Bennequin reverses `±`; fd:contact fixes
  exactly this reading ("identifies Ng's pushoff as Etnyre's positive pushoff") and row 93 is proved for
  `slNg = w − D`; the judge's probe confirms `w − D` (not `w − U`) on an accepted-shape annulus.

FR-FC-1 (row 94: reading of `D_T` = `HeightMarking`, FR-1; the bound holds for EVERY reading `X`; `P X` is
  reading-independent by rp:record-polynomial, not re-proved).
FR-FC-2 (row 94: "individual smooth positive transverse knot whose specified xz projection is an ordinary finite
  regular generic diagram" = `TransverseKnot`, whose fields are exactly those clauses; `spatial`'s
  `RegularGenericProjection` is unit U6a).
FR-FC-3 (row 94: sentence 1 rendered on the accepted class, definitional; `sl` real-valued, casts).
FR-FC-4 (161: hypothesis "no downward vertical tangency" kept though redundant (`vertical_up`); CV's `sl` read as SM's;
  D-F10 (iii) superseded; a CV lift of an arbitrary front (d3:930-987) is the consumer's job).
FR-FC-5 (162: narrowing "a transverse knot in the standard contact ℝ³" → `TransverseKnot` (knots with a generic front,
  fd:contact's own domain and the only consumer's instance)).
FR-FC-6 (162: "the HOMFLY–PT polynomial of the knot it presents, in the normalization of ax:homfly" = `homfly X`,
  `P X = homfly X` by lp:core; the source-fidelity paragraph (max over representatives read at one value) is commentary).
FR-FC-7 (rows 94/161/162 are theorems about the same fixed witness `sl`; row 161 is closable the moment the axiom is
  accepted; 162 waits on 94).

## 4. Consistency (the axiom is true mathematics on the accepted definitions)

Sign audit (all three vocabularies agree): fd:contact's computation (3432-3441) — observer at `−y`, `ν = −∂_y`,
`det_xyz(∂_x, ∂_z, ν) = 1`, source crossing sign = campaign sign `det_xz(u_O, u_U)`.  Row 88's `lcCrossingSign`:
over = larger `⟪·, ν⟫` = smaller y for `ν = −∂_y`, `planeDet ν x y = det(x, y, ν) = det_xz(x, y)`.  Row 92: over =
smaller y, `crossSign = sgn det(vel_O, vel_U)`, `det (u, v) = u.1 v.2 − u.2 v.1` on `Plane = (x, z)`.  Etnyre: "positive
y axis goes into the page", over = smaller slope (= smaller y on Legendrian fronts, `y = dz/dx`).  Row 88's
`crossing_formula` (proved) pins the Gauss normalization to ½·Σ(over-first signs), the standard linking number.

Transverse clause: `ℓ(T, T + ε∂_y)` is the blackboard-framing self-linking (the `∂_y` framing is homotopic through
framings avoiding `T′` to the in-plane normal, since `(x′, z′) ≠ 0`), = writhe of the xz projection with the nearer
(smaller-y) strand over.  Probe: `T = (cos t, sin t, sin 2t/4)` (`α(T′) = ½`) and `T = (−sin t, 2cos t, −sin t cos t)`
(`α(T′) = 1`): Gauss `sl = −1.0000` at `ε = 0.05, 0.1`; front writhe `−1` (accepted rules).

Pushoff clause: for the Legendrian eye `L(t) = (cos t, −sin 2t/2, sin³t/3)` (Legendrian to 1e-10; front = the
2-cusp unknot, `w = 0`, up cusp at `t = 0`, down cusp at `t = π`, so `D = U = 1`, Etnyre `tb = −1, r = 0,
sl(T₊) = −1`), the annulus `B(t, s) = L + s(e_z − x′ e_y) + s² (sin 2t / 2) e_z` satisfies the accepted
`IsPushoffAnnulus` clauses (transverse along `s = 0`: `α(∂_s B) = 1`; `α(∂_t B_s) = s x′² + s² cos 2t > 0` for
`0 < s < ½`; embedded numerically).  Its positive circle `B(·, 0.3)` has front writhe `−1` — exactly ONE kink crossing,
at the DOWN cusp, sign `−1` — and Gauss `sl(B_{0.3}, ε = 0.05) = −0.9998 = w − D = tb − r`.  Mechanism (proves the
asymmetry is forced, not an artefact): positivity makes the pushoff's vertical turn point UPWARD (`z′ > 0` at
`x′ = 0`); at an up cusp (`z ∼ +u³`) the turn is monotone, at a down cusp (`z ∼ −u³`) it conflicts with the descending
arm and produces a small loop.  Hence `sl(T₊) = w − D` for these annuli, and every `IsPositivePushoff` is
transversely isotopic to one of them (Etnyre §2.9), `sl` being row-88 invariant.

Non-vacuity: `SrcContactClauses` is satisfiable iff `SrcContactConsequence` holds (§2.1 theorem), i.e. iff Etnyre (5),
(7), (17) and Geiges Lemma 3.3 hold for the specific real number `slCircle` in the checked conventions — true.  No
clause asserts existence of fronts, pushoffs or readings.

## 5. Proof route of row 94 (printed proof sm-3:3424-3492) with every bridge

```
K : TransverseKnot ──U0──▶ TransverseNeighborhoodHyp K.circle
  row 84 (fd_transverse_neighborhood): L, Ψ; T′ with IsPositivePushoff L T′ ∧ TransverselyIsotopic T′ K.circle
  eta (§5.0): GenericFrontHyp L
  row 87 (fd_generic_front): Φ, L_T = Φ 1 ∘ L, IsGenericFront L_T;
      pushoff clause on T′'s annulus: TransverselyIsotopic T′ (Φ 1 ∘ T′) ∧ GenericFront.IsPositivePushoff L_T (Φ 1 ∘ T′)
  U1: sl K = slCircle T′ = slCircle (Φ 1 ∘ T′)                              (row 88; e1, e2)
  U2 (+U3): F_T with IsLegendrianFrontOf L_T F_T, sp : SpatialLink 1 of L_T with CuspedProjection
  axiom: src_contact_spec.pushoff_slNg : slCircle (Φ 1 ∘ T′) = F_T.slNg      (e3, the cusp calculation)
  row 89 (ce_rounding.exists_family sp): CuspRoundingWitness W; G := (W.fam.G 1).projLoop; W.endSmoothing : CleanCuspSmoothing
  U4: S : Diagram with Marking F_T S                                          (FR-1 existence, the risk item)
  U5: HeightMarking sp G S ∧ F_T.IsRounding S                                (slope = height on the Legendrian; GeomRounding from CleanCuspSmoothing)
  row 93 (fd_ng_bound.ng_input F_T S): F_T.slNg ≤ −degAZ (P S) − 1           (e4)
  U6 (+U6a): Fam : SpatialFamily 1, Fam.G 0 = sp, (Fam.G 1).RegularGenericProjection, reading of K.spatial transported
  row 91 (cp_finite_contact_path.endpoint_polynomial): P S = P X               (e5)
  rw [e1, e2, e3, ← e5]; exact_mod_cast e4                                   (fd_contact_of_units — PROVED)
```
Vocabulary bridges (all theorems): `toE3`/`toSpace` (inverse, `rfl`), contact forms agree (`rfl`),
`TransverseKnot.circle` (ℝ/ℤ → ℝ/2πℤ), `TransverseKnot.spatial` (`projLoop = xz`, `rfl`), `IsLegendrianFrontOf`
(2π curve → 1-periodic `SmoothFront`), TN ↔ GF eta bridges (proved, §5.0), `LegendrianPackage` (one object
carrying front, spatial link, rounding as `IsRounding` AND as `CleanCuspSmoothing` + `HeightMarking`);
`U_package_of : U2 → U3 → U4 → U5 → U_package` PROVED through `ce_rounding`.

## 6. Units, effort, order

| unit | statement (Statements_FINAL.lean) | content | lines | hours | risk |
|---|---|---|---|---|---|
| U-AX | port §0-§4 to `SM/SrcContact.lean` (axiom + `slCircle` + `sl` + `IsLegendrianFrontOf` + sanity theorems + `FdContactData`/CV bundles) | verbatim from the file; interface review 3 lenses + 2 refuters against the registry text with §3 disclosed; map `src:contact → SM.src_contact`; then close row 161 (`CV.ax_etnyre`, proved) and map it | 350 | 2 + review | — |
| U0 | `U_circle` | `IsEmbeddedCircle K.circle` (smooth: `contDiff_toE3.comp (K.smooth.comp (contDiff_id.div_const _))`; periodic; injective mod 2π from `K.embedded`; immersion) and `α(deriv K.circle) > 0` (chain rule `deriv (toE3 ∘ K.T ∘ (·/2π)) = (1/2π) • toE3 (deriv K.T)`, `K.positive`) | 150 | 3 | low |
| U1 | `U_sl_radius`, `U_sl_family`, `U_sl_reparam`, `U_sl_isotopy` | U1a: `self_linking_invariant` on the constant family with common radius `min ε ε₁`; U1b: `transverse_uniform` + `self_linking_invariant` then U1a at both ends; U1c: the family `ρ_s = (1−s)·id + s·ρ` is a `TransverseFamily (2π)` (`ρ_s′ = (1−s) + sρ′ > 0`, lift, `α((T∘ρ_s)′) = ρ_s′ · α(T′∘ρ_s)`); U1: the strip family `F` of `TransverselyIsotopic` composed with the clock `η(s) = Real.smoothTransition s` (`η = 0` on `s ≤ 0`, `1` on `s ≥ 1`) is a `TransverseFamily` on `ℝ × ℝ` (`ContDiffOn.comp_contDiff`, slices for `η s ∈ [0,1]`), U1b gives `slCircle T₀ = slCircle (T₁ ∘ ρ)`, U1c finishes | 450 | 8 | low |
| U4 | `U_reading` | `S := (realize (oword F)).diagram`; `RecordIso (frontRecord F) S.record := (U8R.recordIso F).trans (U2.realizeRecordIso (oword F) (word_ne_nil F)).symm`; `Marking.ofRecordIso : RecordIso (frontRecord F) S.record → F.Marking S` — `e`, `Φ`, `comp_eq`, `pair_eq` (`partnerPerm` ↔ `twin`), `over_iff` (`frontOver` ↔ `overBit`), `sgn_eq` (`frontSgn` ↔ `sign`) are the record fields; `between_iff` from `succ_eq`: on a finite cycle a successor-preserving bijection preserves `cycBetween` — both sides have "nothing strictly between an element and its successor" (`cycNext_no_between`, `record_succ_no_between`) and the uniqueness lemma; prove `cycBetween a b c ↔ b is met before c when iterating succ from a` on each side | 900 | 16 | MAIN (R1) |
| U2+U3 | `U_legendrianFront`, `U_spatialOf` (one unit) | build `sp : SpatialLink 1` first (`T 0 t := toSpace (Lc (2πt))`; smooth, periodic, embedded, regular from `IsEmbeddedCircle`); `CuspedProjection`: `cuspSet` finite from `finite_cusps` (`z′ = y x′`: projected velocity `0 ⇔ x′ = 0`), `ExactCuspGerm` on an interval from `IsExactCuspGerm` (`y′ ≠ 0` on a δ-interval by continuity), doubles/transverse/no_triple under `θ = 2πt`, heights distinct from embeddedness; then `F : SmoothFront` FROM `sp.projLoop 0` (so `F.comp 0 = sp.projLoop 0` and `IsLegendrianFrontOf` are `rfl`): `cusp_semicubical`/`cusp_nonvertical` from the exact germ under `u = y − y₀` (`det(γ″, γ‴) = 8A² u′⁵`, `x″ = 2A u′²`: Leibniz to order 3 for `γ ∘ u`, or `iteratedDeriv` chain rule; FrontSmooth's `germFront_*` covers the linear parameter), `no_vertical` from `z′ = y x′`, the rest verbatim | 1,400 | 24 | R2 |
| U5 | `U_transport` | `GeomRounding F G` from `sp.CleanCuspSmoothing G` (drop `collar`; `F.Cusp ≃ sp.cuspSet` since `F.comp 0 = sp.projLoop 0`); `HeightMarking sp G S` from `Marking F S`: `OccOf G ≃ F.Occ` via `CleanCuspSmoothing.occEquiv` (a clean smoothing keeps the double points), `over_iff`: `F.slope p < F.slope q ↔ sp.height p < sp.height q` at double points of a Legendrian (`slope = z′/x′ = y`, `x′ ≠ 0` since cusps are not double points), `sgn_eq` via `crossSignOf_eq`; `F.IsRounding S := ⟨G, geom, m⟩` | 600 | 10 | low-med |
| U6+U6a | `U_family`, `U_regular` | `G_t := toSpace ∘ Ψ (η t) ∘ Φ (1 − η t) ∘ L ∘ (2π·)` with the clock `η = Real.smoothTransition`: joint `C^∞` on `ℝ × ℝ` from the two `ContDiffOn (Icc 0 1 ×ˢ univ)` isotopies (`ContDiffOn.comp_contDiff`); slices embedded (bijections ∘ embedding, `diffeo`) and regular (`fderiv` of a map with smooth inverse is injective; chain rule); `G 0 = sp` (`Ψ 0 = id`, `η 0 = 0`; `SpatialLink` ext on `T`), `G 1 = K.spatial` (`Φ 0 = id`, `Ψ 1 ∘ L = K.circle`, `toSpace ∘ toE3 = id`); reading transported by `▸`; U6a: `occSetOf` finite from `doubles_finite`, heights distinct from `y_ne_of_isDouble`, no cusp from `immersion` | 750 | 12 | R3 |
| ROW | `fd_contact := fd_contact_of_units u0 u1 (U_package_of u2 u3 u4 u5) u6`; `CV.ax_slbound := ax_slbound_of fd_contact`; map rows 94, 162; 3-lens + 2-refuter reviews | — | 1 + reviews | — |

Total ≈ 4,600 lines (range 4,000-6,500), ≈ 75 prover-hours; U1, U4, U2+U3, U6 are independent and run in parallel
(2-3 working days of wall clock).  Order: U-AX first (unblocks 161 and fixes every unit's target); U4 started
early (the risk item); U1 next (cheap, unlocks the `sl` chain); U2+U3; U6; U5 last (needs U2's `F` and row 89's
`G` shapes but its statement is fixed).

Module placement: `SM/SrcContact.lean` (imports `SM.TransverseFront`, `SM.LinkingCalculusRow`, `SM.NgBound`,
`SM.ContactPath`, `SM.GenericFront`, `SM.TransverseNeighborhood` — the axiom needs rows 84/87/88/92's vocabulary,
so NOT FrontInterfaces as FINAL §11 once placed it): §0-§3 of the file + the sanity theorems; exactly one `axiom`.
`SM/FdContact.lean`: §4-§6 (bundles, units, `fd_contact_of_units`, `U_package_of`, the row theorems).
`CV/SlBound.lean` (or inside FdContact under `namespace CV`): `CV.ax_etnyre`, `CV.ax_slbound`.  Unit proofs in
`SM/FdContactUnits*.lean` as the lanes deliver.

## 7. Blocking risks and fallbacks

R1 (U4, `Marking.ofRecordIso`).  A structural lemma about finite cyclic orders on both sides; 600-1,200 lines.  All
  ingredients exist (`record_succ_no_between`, `cycNext_no_between`, successor uniqueness, `frontRecord.succ = cycSucc`,
  `S.record.succ = nextVisit`).  Fallback: extract a `Marking` directly from the sweep block's construction
  (`U8R.occEquiv F`, `circleEquiv F`, `ΦFun_cycNext F`: the sweep already proves successor preservation on the
  front's own occurrences; `between_iff` may follow from `traversalBetween_iff_cycBetween` on the realized diagram).
  If neither closes, row 94 is blocked by FR-1 (readings never asserted) — record as a package-level gap.
R2 (U2, cusp criteria under the nonlinear coordinate).  Pure calculus; the `u`-parametrized case is in FrontSmooth's
  `germFront_*`; a chain-rule lemma for `iteratedDeriv 2/3` of `γ ∘ u` with `u′ ≠ 0` is the whole content.
R3 (U6, joint smoothness and slice regularity of composed isotopies on a closed strip).  Engineering.
Fidelity (interface review): FR-SC-1 (∃-form), FR-SC-4 (rem:sl-convention is a remark), FR-SC-3 (universal
  quantifier over pushoffs), FR-FC-5 (narrowing of 162).  Each is disclosed with its justification in §3; none is
  an axiom stronger than printed.

## 8. AUTHOR_NOTES text to record (proposed)

D-SC-1 `SM.src_contact` in ∃-form over the literature's `r`, `tb` with the four printed formulas as the fields of
`SrcContactClauses`; the convention / consequence / provenance / scope sentences have no field (theorems
`lcContactForm_toE3`, `alpha_eq_lcContactForm`, `isPositiveTransverse_iff`, accepted `downCount_add_upCount`; precedent
ng:finite-word); equivalence with the substituted form proved (`src_contact_iff_consequence`).  D-SC-2 `SM.sl K :=
slCircle K.circle`, the fd:framed-linking number at row 88's radius for the constant family (ℝ-valued; integrality a
corollary); "an oriented Legendrian front" = `IsLegendrianFrontOf` (row 87's vocabulary); `T₊(L)` = every
`GenericFront.IsPositivePushoff`.  D-SC-3 `D_T` read by `HeightMarking` of `K.spatial` (row 91's own endpoint reading);
the memo's `Carries` dropped.  D-SC-4 D-F10 (iii) superseded: rows 161/162 are theorems on the real `sl`
(`CV.AxEtnyreData`, `CV.AxSlboundData`; `CV.ax_etnyre` proved from the axiom; `CV.ax_slbound` from `fd_contact`);
narrowing of 162 recorded (FR-FC-5).  D-SC-5 `SM/SrcContact.lean` is the module (rows 84/87/88/92's vocabulary
needed), not FrontInterfaces.  D-SC-6 the consistency check (judge's probe, §4) is on file in this plan.
FR-SC-1..11, FR-FC-1..7 as in §3.
