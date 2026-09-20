# DESIGN A — `SM.src_contact`, `SM.sl`, rows 94 / 161 / 162 (fidelity-first)

Architect A, 2026-09-15 (panel for D-GAP2-4). Sketch: `work/drafts/contact/Sketch_A.lean`
(463 lines; typechecks with `lake env lean`; `sorry` only in the eight bridge lemmas of §4 and
the final assembly; the axiom footprint of every proved theorem is standard + `SM.src_contact`
where the axiom is cited, checked with `#print axioms`). Registry text: AXIOM_REGISTRY.md
§src:contact = sm-3:3341-3365. Sources read: Etnyre (SOURCES/audit/L-3_EXIT/work/etnyre_p4-20.txt
§2.2 (3), §2.6.1 (5), (7), §2.6.4 (9), §2.9 Fig. 23-24, Lemma 2.22 (17)), Geiges survey Lemma 3.3.

## 0. What changed since the GAP-2 memo (why D-F10 is void)

The memo (§3(a)(ii), §4 "94") rejected any axiom about `sl` because no independent definition of
`sl` existed. Row 88 is accepted: `SM.selfLinking P T ε = linking P T (pushoff T (fun _ => ey) ε)`
(SM/LinkingCalculus.lean:574) IS fd:framed-linking `sl(T_s) = ℓ(T_s, T_s + ε ∂_y)`, with the
uniform radius and the ε/s-independence proved (`transverse_uniform`, `self_linking_invariant`),
the Gauss normalization proved to be the standard linking number (`crossing_formula`: one half
the sum of the overpass-first signs; I checked by hand that the density
`G·(G_u×G_v) = det(C₁′, C₂′, C₁−C₂)/|r|³` is the classical Gauss integrand). So an axiom of the
form "sl(…) = front formula" now has content relative to the document's own number. The
identification of that number with the literature's self-linking number is rem:sl-convention
(sm-3:3012-3022), the document's own reading; fd:contact's proof cites it (3441-3443). The axiom
therefore asserts the literature's formulas ABOUT `selfLinking` — exactly what the printed proof
consumes.

## 1. The axiom `SM.src_contact` — clause by clause

### 1.1 The printed block (sm-3:3341-3365) and what each sentence becomes

| tex | printed | Lean |
|---|---|---|
| 3342-3345 | "Use standard contact space (ℝ³, ker(dz − y dx)), with positive transverse orientation z′ − y x′ > 0 (Etnyre §2.1, 2.4 for the conventions)." | no field: a convention sentence; the vocabulary's forms agree (`lcContactForm_toE3`, `alpha_eq_lcContactForm`, both `rfl`) |
| 3345-3351 | "Etnyre's front and pushoff statements give, for an oriented Legendrian front with downward and upward cusp counts D, U" | the binder `∀ L F, IsLegendrianFrontOf L F →`, `D = F.downCount`, `U = F.upCount`, `w = F.writhe` on the accepted ng:front-domain class `SmoothFront` (§1.2) |
| 3349-3351 | "— every cusp of an oriented front is traversed either downward or upward, so the total cusp count in his tb formula is D+U —" | no field: the accepted theorem `SmoothFront.downCount_add_upCount : D + U = #cusps` (FrontSmooth.lean:740) |
| 3352 (display) | `r = (D − U)/2` | field `rotation : r L = (D − U)/2` |
| 3352 | `tb = w − (D + U)/2` | field `thurston_bennequin : tb L = w − (D + U)/2` |
| 3353 | `sl(T₊(L)) = tb(L) − r(L)` | field `pushoff_self_linking : ∀ T', GenericFront.IsPositivePushoff L T' → slOf (2π) T' = tb L − r L` |
| 3355-3357 | "(For the second formula … Geiges Prop. 3.5.9 …; Etnyre's (7) reduces to his Remark 2.14 …)" | no field: provenance |
| 3358-3363 | "For a generic positive transverse front (Definition def:transverse-front), self-linking equals its front writhe: Geiges Lemma 3.3 …; Etnyre's equation (9) states it." | field `transverse_front_writhe : ∀ K : TransverseKnot, sl K = K.front.writhe` |
| 3363-3364 | "These are the local front and pushoff source formulas only." | no field: scope |

```lean
structure SrcContactClauses (r tb : (ℝ → E3) → ℝ) : Prop where
  rotation : ∀ L F, IsLegendrianFrontOf L F → r L = ((F.downCount : ℝ) - F.upCount) / 2
  thurston_bennequin : ∀ L F, IsLegendrianFrontOf L F →
    tb L = (F.writhe : ℝ) - ((F.downCount : ℝ) + F.upCount) / 2
  pushoff_self_linking : ∀ L F, IsLegendrianFrontOf L F →
    ∀ T', GenericFront.IsPositivePushoff L T' → slOf (2 * π) T' = tb L - r L
  transverse_front_writhe : ∀ K : TransverseKnot, sl K = (K.front.writhe : ℝ)
axiom src_contact : ∃ r tb : (ℝ → E3) → ℝ, SrcContactClauses r tb
```
with `rot := Classical.choose src_contact`, `tb := …`, `src_contact_spec`. This is the pattern of
lit:homfly / lp:lm (∃-form over the literature's objects the document never defines, Prop
structure with one field per printed clause, the maps fixed by choice).

### 1.2 How the literature's quantities are read on the accepted vocabulary

* **"an oriented Legendrian front"** — `IsLegendrianFrontOf (L : ℝ → E3) (F : SmoothFront)`:
  `GenericFrontHyp L` (rows 84/87: smooth embedded `2π`-periodic circle, `α(L′) = 0`), `F.c = 1`,
  and `(F.comp i).γ t = GenericFront.front L (2π t)`. So the front is a `SmoothFront` (ng:front-domain,
  accepted row 73) and `D, U, w` are its accepted `downCount`, `upCount`, `writhe`. The front of `L`
  is unique (`IsLegendrianFrontOf.unique`, proved), so `r L`, `tb L` are well defined functions of `L`.
* **`D`, `U`** — `IsDownCusp` = "traversed from its locally upper arm to its locally lower arm"
  (FrontSmooth.lean:457, FR-2) = Etnyre's "down cusp" (§2.6.1: "positive when going down a cusp").
* **`w`** — `SmoothFront.writhe` with over = smaller slope (`IsOverUnder`) and sign
  `sgn det(u_O, u_U)`: Etnyre §2.2 (3) "at each crossing the slope of the overcrossing is smaller …
  the positive y axis goes into the page", i.e. observer at `y = −∞`, plane basis `(∂_x, ∂_z)`,
  `(∂_x, ∂_z, −∂_y)` positive — the same frame as fd:contact's own computation (sm-3:3432-3441) and
  as row 88's `lcCrossingSign` with `ν = −∂_y` (I re-did the 3×3 determinant: `det(x, y, −e_y) =
  det_xz(x, y)` for `x, y` in the `xz`-plane).
* **`T₊(L)`** — `GenericFront.IsPositivePushoff L T'`: a positive circle `B(·, s₀)`, `0 < s₀ < b`,
  of a pushoff annulus of `L` transverse to `ξ` (fd:transverse-neighborhood's notion, row 87's copy;
  the two copies are field-for-field identical — bridge B-dedup, an anonymous-constructor
  conversion, used in the sketch's assembly). This is Etnyre §2.9 Fig. 23: `L₊ = S¹ × {½}` in the
  transverse annulus, "positively transverse"; quantified over EVERY such pushoff because "any two
  transversal push-offs are transversely isotopic" (Etnyre p. 18) and sl is a transverse-isotopy
  invariant — the literature's `T₊(L)` is the class.
* **`sl`** — `slOf P T` (§2), the ε-free fd:framed-linking number; for the Legendrian clauses at
  period `2π` on `E3` (the rows 84/87 objects live there, no coordinate bridge); for the transverse
  clause `sl K := slOf 1 (toE3 ∘ K.T)` (def:transverse-front lives in `Space`, period 1).
* **"a generic positive transverse front (def:transverse-front)"** — `K : TransverseKnot`, its front
  `K.front : SmoothKnotDiagram` (accepted row 92), `K.front.writhe` = Σ_q sgn det_xz(u_O(q), u_U(q))
  with over = smaller y (T-2) — the source observer of fd:contact.

### 1.3 ∃-form over `r`, `tb` versus the substituted consequence

The document never defines `r` or `tb`; fd:contact's proof substitutes the first two formulas
into the third (3452-3457) and uses only `sl(T₊(L)) = w − D`. Both readings were weighed:
* The substituted form alone (`slOf (2π) T' = w − D` and `sl K = w`) is what the document
  consumes, but it is NOT the registry text: the registry prints three separate formulas and a
  reviewer comparing clause by clause would find the first two missing.
* The ∃-form transcribes the three formulas verbatim. Its first two fields pin `r`, `tb` down
  completely, so the ∃-form is PROVABLY EQUIVALENT to the substituted form: theorem
  `src_contact_iff_composite` (proved in the sketch, standard axioms only). Hence the axiom is
  neither stronger nor weaker than the printed formulas on the class, and the cusp calculation of
  fd:contact's proof is the theorem `SrcContactClauses.pushoff_slNg : slOf (2π) T' = F.slNg`
  (proved; `slNg` is the accepted `w − D` of row 93).
Decision: ∃-form, three fields + the transverse field; equivalence theorem shipped with the axiom
so nobody can claim hidden content. (Reviewer flag FR-SC-1.)

### 1.4 Where the axiom is stronger / weaker than printed — the candid list (FR-SC-*)

* **FR-SC-1 (∃-form; `r`, `tb` undefined).** Content = the two consequences, no more
  (`src_contact_iff_composite`). Not stronger. The first two fields carry no content by themselves.
* **FR-SC-2 (domain of the Legendrian clauses — WEAKER than printed, safe).** Printed: "an oriented
  Legendrian front" (Etnyre: any front with generalized cusps). Lean: knots only (`F.c = 1`), fronts on
  ng:front-domain (semicubical cusps with `x″ ≠ 0`, transverse double points, no triple point, cusps
  alone, no vertical tangency on regular arcs — the last is automatic for Legendrian fronts:
  `z′ = y x′` makes `x′ = 0 ⇒ γ′ = 0`). The consumer's instance (`L_T` of fd:generic-front, exact
  germs) is inside. No exact-germ requirement in the axiom.
* **FR-SC-3 (`T₊(L)` as any positive pushoff of an annulus).** Quantifying over all pushoffs is
  the literature's statement (well-defined up to transverse isotopy). The accepted `IsPushoffAnnulus`
  demands transversality of the annulus along `s = 0` too (fd:transverse-neighborhood's own
  construction, sm-3:2490-2502); Etnyre's annulus is the same object.
* **FR-SC-4 (which `sl`).** `sl` is the document's `selfLinking` (fd:framed-linking) made ε-free
  through row 88; the identification with Etnyre's/Geiges' `sl` is rem:sl-convention
  (Etnyre uses the same `∂_y` pushoff, §2.6.4; Geiges' `∂_X = −∂_y`, both framings homotopic through
  framings). A reviewer must accept rem:sl-convention as the document's reading; the axiom then says
  what the sources say about that number. Sign check: see §1.5.
* **FR-SC-5 (two parametrizations).** Legendrian clauses at period `2π` on `E3`; transverse clause
  at period `1` on `Space` through `toE3` (identity on coordinates, `rfl` lemmas). `selfLinking P` is
  period-generic (FR-LC-1), so no clause is distorted; the bridges (§4) are theorems, not axiom
  content.
* **FR-SC-6 (D + U).** "every cusp … either downward or upward" is the accepted theorem
  `downCount_add_upCount`; not a field.
* **FR-SC-7 (front writhe of a transverse front).** Over = smaller y, sign det_xz: the accepted row
  92; consistent with row 88's observer `ν = −∂_y` and Etnyre's "y into the page".
* **FR-SC-8 (no field for the convention/provenance/scope sentences).** As for ng:finite-word.
* **FR-SC-9 (`slOf` outside its domain).** `slOf P T = 0` when `T` is not a positive transverse
  embedding or `P ≤ 0`; every field applies it only on positive transverse embeddings (pushoffs are
  positive transverse by `IsPushoffAnnulus.positive`; `K` by `TransverseKnot.isPositiveTransverseEmbedding`,
  proved). The default is never exercised (as `degAZ`'s `0`-at-`0`, FR-NB).
* **FR-SC-10 (real-valued).** `sl : TransverseKnot → ℝ`; integrality is a CONSEQUENCE of the axiom
  (`sl K = ↑writhe`), not a prerequisite. The displays of rows 94/161/162 compare reals with integer
  casts, which is what the printed displays do.

### 1.5 Non-vacuity and consistency (a false axiom is fatal)

* **Sign/observer conventions.** fd:contact's computation (3432-3441): observer at `−y`, `ν = −∂_y`,
  `det_xyz(∂_x, ∂_z, ν) = 1`, source crossing sign = campaign sign `det_xz(u_O, u_U)`. Row 88's
  `lcCrossingSign`: over = larger `⟪·, ν⟫` = smaller y for `ν = −∂_y`; `planeDet ν x y = det(x, y, ν)`
  = `det_xz(x, y)` on the `xz`-plane. Row 92: over = smaller y, `crossSign = sgn det(vel_O, vel_U)`
  with `det (u, v) = u.1 v.2 − u.2 v.1` on `Plane = (x, z)`. All three agree. Etnyre: "positive y axis
  goes into the page", overcrossing = smaller slope (= smaller y for Legendrian fronts, `y = dz/dx`).
* **The transverse clause is the blackboard-framing fact** (`ℓ(T, T + ε∂_y)` = writhe of the
  `xz`-projection with the nearer strand over): the `∂_y`-framing is homotopic through framings to
  the in-plane normal framing (the rotation `cos t ∂_y + sin t n` never meets `T′` because `(x′, z′) ≠ 0`),
  and the classical mixed-crossing count gives two crossings of the crossing's sign per double point.
  Direction of the pushoff (`+∂_y` or `−∂_y`) is immaterial for the same reason.
* **Numerical probe** (scratchpad `probe.py`): `T(θ) = (−sin θ, 2cos θ, −sin θ cos θ)` has
  `z′ − y x′ ≡ 1` (positive transverse, embedded), front = reversed lemniscate with one double
  point, over = the `θ = π` branch (`y = −2`), `u_O = (1, −1)`, `u_U = (−1, −1)`, `det_xz = −2`,
  writhe `−1`; the Gauss integral `ℓ(T, T + 0.1 ∂_y)` (1200² Riemann sum) = `−1.000000000023`.
  Consistent with Bennequin (transverse unknot: `sl ≤ −1`) and with the axiom's clause.
* **Legendrian clause.** `tb − r = w − ½(D+U) − ½(D−U) = w − D`: Etnyre (5), (7), (17) with the
  same cusp conventions; sanity on the 2-cusp unknot (`D = U = 1, w = 0`): `tb = −1, r = 0,
  sl(T₊) = −1` ✓. The naming `T₊` vs `T₋` follows Etnyre (his Warning notes Bennequin reverses it);
  fd:contact fixes exactly this reading ("identifies Ng's pushoff as Etnyre's positive pushoff").
  Row 93 is PROVED for `slNg = w − D` and the accepted `IsPositivePushoff` is Etnyre's `L₊`
  (positively transverse circles of the annulus), so the two halves of the document are consistent.

## 2. `SM.sl` from fd:framed-linking (sketch §1, proved)

```lean
theorem exists_uniform_radius (hP : 0 < P) (h : IsPositiveTransverseEmbedding P T) :
    ∃ ε₀ > 0, ∀ ε, 0 < ε → ε ≤ ε₀ → DisjointPair P T (pushoff T (fun _ => ey) ε)   -- row 88, constant family
def slOf (P : ℝ) (T : ℝ → E3) : ℝ :=
  if h : 0 < P ∧ IsPositiveTransverseEmbedding P T then
    selfLinking P T (Classical.choose (exists_uniform_radius h.1 h.2)) else 0
theorem slOf_eq_selfLinking … : slOf P T = selfLinking P T ε      -- for EVERY admissible ε (proved)
def sl (K : TransverseKnot) : ℝ := slOf 1 (fun t => toE3 (K.T t))
```
ε is chosen by `Classical.choose` from row 88's `transverse_uniform` applied to the constant
family; `slOf_eq_selfLinking` shows the choice is immaterial (row 88's `self_linking_invariant`
applied twice through the common radius `min ε ε₁`). `TransverseKnot.isPositiveTransverseEmbedding`
is proved (the derivative passes through the continuous linear `toE3`). Integrality: not needed
(FR-SC-10); the crossing formula alone gives ½ℤ, and an evenness argument would be ~1-2k lines of
plane topology — not pursued.

## 3. The row statements (sketch §4-§5)

**Row 94 fd:contact — `SM.FdContactData` (the memo's shape with the real `sl`):**
* `over_rule_sign` (first sentence): `isOver s t ↔ y s < y t` and `crossSign = sign det(vel_O, vel_U)`
  — definitional on row 92, proved now (`fdContact_over_rule_sign`).
* `front_writhe` (display fd:front-writhe): `sl K = ↑K.front.writhe` — proved now from the axiom
  (`fdContact_front_writhe`).
* `representative_bound` (display fd:representative-bound): `∀ K X, K.Reads X →
  sl K ≤ −↑(degAZ (P X)) − 1`, where `K.Reads X := Nonempty (K.spatial.HeightMarking K.spatial.projLoop X)`
  — the ACCEPTED FR-1 reading of rows 90/91 for the endpoint `T` (over = smaller y of `T`), applied to
  `K.spatial : SpatialLink 1`. No new `Carries` structure: the gap2 sketch's `Carries` is not in
  work/lean and `HeightMarking` is what row 91 consumes, so reuse it (FR-FC-1).
* The two closing sentences are commentary (no field).
* FR-FC-1 (reading = `HeightMarking`, FR-1); FR-FC-2 ("individual smooth positive transverse knot
  whose specified xz projection is an ordinary finite regular generic diagram" = `TransverseKnot`,
  whose fields are exactly those clauses; `spatial_regularGeneric` bridges to rows 89-91's
  `RegularGenericProjection`); FR-FC-3 (`P_T = P X` for every reading, independent by
  rp:record-polynomial/`presentations`); FR-FC-4 (`sl` real-valued, casts).

**Row 161 CV:ax:etnyre — `CV.ax_etnyre` (theorem, PROVED in the sketch from the axiom):**
`∀ (D : SmoothKnotDiagram) (K : TransverseKnot), K.front = D → (∀ t, (D.vel t).1 = 0 → 0 < (D.vel t).2)
→ sl K = ↑D.writhe`. Printed shape kept: "a front diagram of a transverse knot" = `K.front = D`,
"with no downward vertical tangency" = the (redundant, row 92 `vertical_up`) hypothesis, kept as
printed; `sl(T)` = `SM.sl`. D-F10 (iii) is superseded: an independent `sl` exists. FR-FC-5: the
redundant hypothesis; FR-FC-6: CV's `sl` read as the SM's (CV: "presupposes the contact-geometric
definition of sl; this document never defines it"). Closable immediately after the axiom's review.

**Row 162 CV:ax:slbound — `CV.AxSlboundStatement`:** `∀ K X, K.Reads X → sl K ≤ −↑(degAZ (homfly X)) − 1`;
`CV.ax_slbound_of : FdContactData → AxSlboundStatement` proved (`P_eq_homfly`). Recorded narrowing
(memo §3(b)): "a transverse knot in the standard contact ℝ³" → knots with a generic front
(`TransverseKnot`), fd:contact's own domain and the only consumer's instance (thm:carrierfloor (C));
"the polynomial of the knot it presents" = `homfly X` of a reading (FR-1), ax:homfly's normalization
= `SM.lit_homfly` (FR-FC-7).

## 4. Proof route of row 94 (sketch §6; the printed proof sm-3:3459-3499)

Vocabulary bridges (named; all theorems, none an axiom):
* **B-0** `Space → E3`, `toE3` (proved smooth, `rfl` on coordinates); contact forms agree (`rfl`).
* **B-1** `TransverseKnot.spatial : SpatialLink 1` (built) and `spatial_regularGeneric`
  (heights distinct from embeddedness, `y_ne_of_isDouble`).
* **B-2** period 1 → 2π: `toCircle2π K.T` satisfies `TransverseNeighborhoodHyp` (row 84's input).
* **B-3** reparametrization invariance of `slOf` under `IsCircleReparam ρ` (change of variables in
  the Gauss double integral; NOT a clause of row 88 — `TransverselyIsotopic` ends at `T₁ ∘ ρ`), and
  **B-3′** period rescaling `sl K = slOf (2π) (toCircle2π K.T)` (same technique).
* **B-4** `slOf` constant along `TransverselyIsotopic`: time clamp `Real.smoothTransition` from the
  strip `ContDiffOn (Icc 0 1 ×ˢ univ)` to row 88's `ContDiff ℝ ∞ (uncurry T)` (the CE-R2 trick),
  then `self_linking_invariant`, then B-3 at the end.
* **B-dedup** `TransverseNeighborhood.IsPushoffAnnulus ↔ GenericFront.IsPushoffAnnulus`
  (anonymous constructor; done inline in the sketch's assembly).
* **B-5** `exists_legendrianFront`: a generic Legendrian front (row 87's output) is a `SmoothFront`
  with `IsLegendrianFrontOf`: `cusp_semicubical`/`cusp_nonvertical` from the exact germ by the chain
  rule through `u = y − y₀` (`det(γ″, γ‴) = 8A² u′⁵`, `x″ = 2A u′²`; FrontSmooth's `germFront` lemmas
  give the `u`-parametrized case), `no_vertical` from `z′ = y x′`, the rest verbatim; period `2π → 1`.
* **B-6** rounding + reading existence for `F_T` (the FR-1 hard step): (a) `L₁ : SpatialLink 1` in
  `Space` from `L_T` with `CuspedProjection` (heights distinct from embeddedness; `ExactCuspGerm`'s
  `y′ ≠ 0` on a δ-interval by continuity); (b) row 89 `ce_rounding.exists_family L₁` gives `G` with a
  `CleanCuspSmoothing` (with collar); (c) a polygonal `S` carrying `F_T`'s record from the certificate
  lane's sweep: `sweep_proof F_T : SweepStatement F_T` → `OWord W` with `RecordIso (frontRecord F_T)
  (slotRecord …)` → through `U2.realizeRecordIso`, `RecordIso (frontRecord F_T) (realize W).diagram.record`;
  `S := (realize W).diagram`; (d) `F_T.Marking S` from that `RecordIso` — the INVERSE of
  `markingRecordIso` (cyclic order `between_iff` from successor preservation: LinkDiagramRecord §G,
  the def:gauss-record equivalence); (e) `GeomRounding G` for `F_T` from the `CleanCuspSmoothing`
  (drop `collar`; cusp index types identified) ⇒ `F_T.IsRounding S`; (f) `L₁.HeightMarking G S` from
  the `Marking` via slope = height on Legendrian fronts (`y = z′/x′` at double points, `x′ ≠ 0`) and
  `CleanCuspSmoothing.occEquiv`/`crossSignOf_eq`. Design point that makes (f) cheap: build `F_T`
  FROM `L₁` so that `F_T.comp 0 = L₁.projLoop 0` definitionally.
* **B-7** the supplied family `G_t θ := Ψ t (Φ (1 − t) (L θ))` (no inverse of `Φ` needed since
  `Φ₁⁻¹ ∘ L_T = L`), jointly smooth on the strip (both isotopies are `ContDiffOn` there), time-clamped,
  each slice embedded and regular (diffeomorphisms with smooth inverses ⇒ injective differentials),
  converted to `Space`/period 1 as a `SpatialFamily 1` with `G 0 = L₁` (`Ψ 0 = id`) and
  `G 1 = K.spatial` (`Φ 0 = id`, `carries`; `SpatialLink` ext on the `T` field).

Assembly (`fd_contact_of_bridges`, skeleton in the sketch up to the `sl`-transport): row 84 on
`toCircle2π K.T` → `L`, `Ψ`, `T'` with `IsPositivePushoff L T'` and `TransverselyIsotopic T' T₂π`;
row 87 on `L` → `Φ`, `L_T = Φ 1 ∘ L`, `F_T`; the pushoff clause → `T'' = Φ 1 ∘ T'` positive pushoff
of `L_T`, `TransverselyIsotopic T' T''`; B-2/B-3′/B-4: `sl K = slOf T₂π = slOf T' = slOf T''`;
the axiom (`pushoff_slNg`): `slOf T'' = F_T.slNg`; B-5/B-6 give `S`, `G`, `L₁`; row 93
`fd_ng_bound.ng_input F_T S : F_T.slNg ≤ −degAZ (P S) − 1`; B-7 + row 91
`cp_finite_contact_path.endpoint_polynomial L₁ … X … S : P S = P X`; substitute.

Hard steps, in order of risk: **H1** = B-6(d) `Marking` from a `RecordIso` (400-800 lines; the only
place a new structural lemma about records is needed — check LinkDiagramRecord §G for the
successor/cyclic-order equivalence before writing); **H2** = B-5 (300-500 lines; chain rule for
`iteratedDeriv 2/3` of `γ ∘ u`); **H3** = B-3/B-3′ (300-500 lines; change of variables in the
periodic double integral, `intervalIntegral.integral_comp_mul_deriv` + periodicity); **H4** = B-7
(300-400 lines; clamp, slice regularity, `SpatialLink` ext); **H5** = assembly with coordinate
conversions (300-400 lines). Everything else is bookkeeping (B-0/B-1/B-2/B-4/B-dedup ≈ 300 lines).

Effort: axiom module (statement + sanity theorems, from the sketch) ≈ 300 lines, 2 h + interface
review; `sl` ≈ 150 lines (done in sketch); rows 161/162 statements ≈ 60 lines; bridges + assembly
≈ 2,200-3,000 lines, 10-16 h of prover lanes in parallel (H1-H4 independent). Total ≈ 3,000 lines.

## 5. Module placement and first prover units

Module `SM/SrcContact.lean` (new; FINAL §11 placed the axiom in FrontInterfaces, but it needs
rows 84/87/88/92's vocabulary: imports `SM.GenericFront`, `SM.LinkingCalculusRow`,
`SM.TransverseFront`, `SM.FrontSmooth` via TransverseFront). Contents = sketch §0-§3: `toE3`,
`slOf`, `sl`, `IsLegendrianFrontOf`, `SrcContactClauses`, `axiom src_contact`, `rot`, `tb`,
`src_contact_spec`, `pushoff_slNg`, `src_contact_iff_composite`. Exactly one `axiom`. Map
`src:contact → SM.src_contact`, interface review (3 lenses + 2 refuters) against the registry
text with §1.4 as the disclosed readings. Then `SM/FdContact.lean` (statement `FdContactData`,
`TransverseKnot.spatial`, `Reads`; the two proved fields) and `CV/AxEtnyre.lean` (row 161, closable
at once).

Units:
1. **U-SC1 (statement unit, now):** port sketch §0-§3 to `SM/SrcContact.lean`; interface review.
   Then row 161 `CV.ax_etnyre` and the two proved fields of row 94.
2. **U-SC2 (H1):** `SmoothFront.Marking.ofRecordIso : RecordIso (frontRecord F) S.record → F.Marking S`
   and `exists_marking : ∀ F : SmoothFront, ∃ S : Diagram, Nonempty (F.Marking S)` via `sweep_proof`
   + `U2.realizeRecordIso`.
3. **U-SC3 (H2 + B-6 a,e,f):** `exists_legendrianFront` built from `L₁ : SpatialLink 1`;
   `GeomRounding` from `CleanCuspSmoothing`; `HeightMarking` from `Marking` (slope = height).
4. **U-SC4 (H3 + B-4 + B-2):** `slOf_comp_reparam`, `sl_eq_slOf_toCircle2π`,
   `slOf_eq_of_transverselyIsotopic`, `TransverseKnot.transverseNeighborhoodHyp`.
5. **U-SC5 (H4 + H5):** `exists_suppliedFamily`, then `fd_contact_of_bridges` → `SM.fd_contact`,
   then `CV.ax_slbound`.
