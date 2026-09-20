# DESIGN B — `SM.src_contact`, `SM.sl`, rows 94 / 161 / 162, and the proof route of fd:contact (emphasis: PROOF FEASIBILITY)

Architect B, 2026-09-15.  Sketch: `work/drafts/contact/Sketch_B.lean` (507 lines, typechecks with
`cd work/lean && lake env lean ../drafts/contact/Sketch_B.lean`, zero errors/warnings; one `axiom`).
Method: start from the printed proof of fd:contact (sm-3:3424-3492) and the ACCEPTED rows 84 (SM/TransverseNeighborhood),
87 (SM/GenericFront), 88 (SM/LinkingCalculus[Row]), 93 (SM/NgBound), 91 (SM/ContactPath), 89/90 (SM/CeRounding,
SM/CeSmoothingRecord), 92 (SM/TransverseFront); determine which bridges are missing; state the axiom so that the proof
composes and NO MORE; then check that the composition kernel-checks.  It does: `SM.fd_contact_of_units` (sketch §5.2)
PROVES `FdContactData` from the accepted rows, `SM.src_contact`, and four named unit-Props (U0, U1, U2-5, U6);
`#print axioms` = the five registered literature axioms + `SM.src_contact` + standard.  What remains is the units.

## 0. Findings that drive the design

F-1. **The chain composes with the axiom giving only two things**: (a) `sl(T₊(L)) = tb(L) − r(L)` with `tb`, `r` given by
the two front formulas — the printed proof uses ONLY their substitution `tb − r = w − D = sl_Ng(F)` (sm-3:3441-3447); and
(b) `sl(T) = w(front)` for generic positive transverse fronts (display fd:front-writhe, sm-3:3437-3440 "Summing the
source transverse-front writhe formula … proves fd:front-writhe").  Nothing else of src:contact enters any proof.
F-2. **`sl` is definable NOW from row 88 alone** (`selfLinking` + `transverse_uniform` on the constant family), ℝ-valued;
integrality is a COROLLARY of fd:front-writhe, not a prerequisite (integrality via `crossing_formula` would need a
generic direction (Sard/row 85 machinery) and the parity of mixed crossings — 1-2k lines, unnecessary).
F-3. **Consistency check passed numerically**: for the transverse unknot `T(t) = (cos t, sin t, sin 2t/4)` (`z′ − yx′ = 1/2`),
the accepted Gauss integral `linking 2π T (T + ε∂_y)` is `−1.0000` (ε = 0.2, 0.1, 0.05; scratch `probe_sl.py`) and the
accepted front writhe (over = smaller y, `sgn det_xz(u_O,u_U)`) is `−1` — the two conventions agree in sign and
normalization, and `−1` is Bennequin's maximal sl of the unknot.  Sign audit: observer at −y (`ν = −∂_y`,
`det(e_x,e_z,−e_y) = +1`, so the (x,z) page is positively oriented as seen), over = smaller y = nearer the observer
(`lcCrossingSign`'s rule with `ν = −e_y`), pushoff `+∂_y` (away from the observer; `ℓ(T, T+εν) = ℓ(T, T−εν)` by translation
and symmetry, so the side is immaterial); the blackboard-pushoff identity `lk = writhe` holds because the "diagonal"
mixed crossings near tangents parallel to the projected shift cancel in pairs (rotation number ± cancels).  The
Legendrian side is Etnyre's standard convention set (smaller slope over; `r = (D−U)/2`; `tb = w − (D+U)/2`;
`sl(T₊) = tb − r`), consistent: the Legendrian unknot eye (w = 0, D = U = 1) gives tb = −1, r = 0, sl(T₊) = −1.
F-4. **The one genuinely missing existence statement is a polygonal reading of `S(F_T)`** (FR-1 "no existence of carriers is
asserted" in rows 89-91; row 93 quantifies over roundings, row 91 over readings).  It is obtainable from the accepted
sweep block: `U8R.recordIso F : RecordIso (frontRecord F) (slotRecord …)` and `realizeRecordIso W : RecordIso
(realize W).diagram.record (slotRecord …)` give `RecordIso (frontRecord F) (realize (oword F)).diagram.record`; what
is missing is the CONVERSE of `U8R.markingRecordIso` (a `RecordIso` to `frontRecord F` → `F.Marking S`: successor
determines `cycBetween`).  This is unit U4, the main risk (§4).
F-5. Three parametrization conventions must be bridged: 1-periodic `Space` (rows 89-92), 2π-periodic `E3` (rows 84/87/88),
period-`P` `E3` (row 88, used at `P = 2π`).  Two verbatim COPIES of row 84's notions live in `SM.GenericFront.*`
(`IsEmbeddedCircle`, `IsLegendrian`, `IsPushoffAnnulus`, `IsPositivePushoff`, `TransverselyIsotopic`,
`IsCircleReparam`); the eta bridges are proved in the sketch (§5.0, 60 lines).

## 1. The axiom `SM.src_contact` (sketch §3)

```lean
structure SrcContactClauses (r tb : (ℝ → E3) → ℝ) : Prop where
  contact_space        : ∀ p v : E3, lcContactForm p v = v 2 - p 1 * v 0                       -- convention, rfl
  positive_orientation : ∀ T, IsPositiveTransverse T ↔ ∀ θ, 0 < lcContactForm (T θ) (deriv T θ) -- convention, Iff.rfl
  cusps_down_or_up     : ∀ F : SmoothFront, F.downCount + F.upCount = F.cuspSet.card           -- theorem of the class
  rotation             : ∀ L F, IsEmbeddedCircle L → IsLegendrian L → IsFrontOf F L → r L = ((D:ℝ) − U)/2
  thurston_bennequin   : ∀ L F, … → tb L = (w:ℝ) − ((D:ℝ) + U)/2
  pushoff_self_linking : ∀ L T' F, … → IsPositivePushoff L T' → slCircle T' = tb L − r L
  transverse_front_writhe : ∀ K : TransverseKnot, K.sl = K.front.writhe
axiom src_contact : ∃ r tb : (ℝ → E3) → ℝ, SrcContactClauses r tb
def legRotation := Classical.choose src_contact ; def legTb := Classical.choose (Classical.choose_spec src_contact)
```
with `D = F.downCount`, `U = F.upCount`, `w = F.writhe` (accepted, SM/FrontSmooth.lean) and
`IsFrontOf F L := F.c = 1 ∧ ∀ i t, (F.comp i).γ t = (L (2πt) 0, L (2πt) 2)` (the 2π ↔ 1 parameter bridge is INSIDE the
relation).  Registry clause → field:

| registry (sm-3) | printed | field / reading |
|---|---|---|
| 3342-3343 | "Use standard contact space (ℝ³, ker(dz − y dx))" | `contact_space` — the accepted `lcContactForm` (= `TN.alpha` = `GF.alpha`, rfl) |
| 3343-3344 | "with positive transverse orientation z′ − yx′ > 0" | `positive_orientation` — the accepted `IsPositiveTransverse` |
| 3344-3347 | "Etnyre's front and pushoff statements … give, for an oriented Legendrian front with downward and upward cusp counts D, U" | the hypotheses of the three formula fields: `L` an oriented (parameter direction, T-1) Legendrian embedded circle (`IsEmbeddedCircle`, `IsLegendrian`, row 84's notions), `F : SmoothFront` its front (`IsFrontOf`, the ng:front-domain class = "front" in Etnyre's generic sense), `D = downCount`, `U = upCount` (accepted "traversed from its locally upper arm to its locally lower arm", FR-2) |
| 3348-3350 | "every cusp of an oriented front is traversed either downward or upward, so the total cusp count in his tb formula is D+U" | `cusps_down_or_up` (provable: `downCount_add_upCount`) |
| 3352 | `r = (D − U)/2` | `rotation` |
| 3352 | `tb = w − (D+U)/2` | `thurston_bennequin`; `w` = the accepted over-first `sgn det(u_O,u_U)` writhe with over = smaller slope |
| 3353 | `sl(T₊(L)) = tb(L) − r(L)` | `pushoff_self_linking`; `T₊(L)` = every positive transverse pushoff of `L` in the document's own sense `IsPositivePushoff` (row 84, FR-TN-4 "a sufficiently small positive circle is therefore the positive pushoff in the source convention"); `sl` = `slCircle` (§2) |
| 3354-3357 | "(For the second formula … Geiges … Etnyre's equation (7) reduces to his Remark 2.14 …)" | provenance; no field |
| 3358-3361 | "For a generic positive transverse front (Definition def:transverse-front), self-linking equals its front writhe" | `transverse_front_writhe`: for the knot `T` of every generic positive transverse front (`TransverseKnot`, row 92; "the knot T is named separately where it is used"), `sl(T) = K.front.writhe` (the accepted `SmoothKnotDiagram.writhe`, = Σ_q sgn det_xz(u_O,u_U), over = smaller y) |
| 3361-3363 | citations; "These are the local front and pushoff source formulas only." | scope; no field |

**Decision D-SC-1 (∃-form, not the substituted consequence).**  The registry prints three formulas; `r` and `tb` are the
literature's objects, undefined in the document.  Following the adopted pattern (lit:homfly, lp:lm: ∃-form over the
undefined map, fixed by `Classical.choose`), the axiom quantifies `∃ r tb` and states the three formulas SEPARATELY.
The sketch PROVES (`srcContact_iff_consequence`, standard axioms only) that this ∃-form is EQUIVALENT to the
substituted form `SrcContactConsequence` (`slCircle T' = sl_Ng(F)` ∧ the transverse clause): → is the printed cusp
calculation (`SrcContactClauses.pushoff_slNg`, `push_cast; ring`); ← defines `r`, `tb` by the two formulas on the
(unique, `IsFrontOf.eq`) front of `L`.  So a reviewer flagging "the ∃ over r, tb adds content" is answered by a theorem:
neither stronger nor weaker than the display with r, tb eliminated.  The proof of fd:contact consumes only
`pushoff_slNg` and `transverse_front_writhe`.

**Where the axiom is stronger / weaker than the registry text (record as FR-SC-*).**
- FR-SC-1 (`sl` = the document's number).  "sl" is read as `slCircle`, the fd:framed-linking number at the row-88 radius
  (rem:sl-convention identifies it with the literature's).  This is exactly what fd:contact's proof does ("whose sl is the
  number of fd:framed-linking by Remark rem:sl-convention"); the identification rests on a remark, not a theorem.  The
  numeric probe (F-3) supports it in sign and normalization.
- FR-SC-2 ("T₊(L)" = every pushoff).  The literature's `T₊(L)` is well defined up to transverse isotopy; the axiom asserts
  the formula for every `IsPositivePushoff L T'` (the document's definition).  Not stronger than the literature (all such
  pushoffs are transversely isotopic, Etnyre §2.9); it is what "T₊(L)" MEANS on the accepted vocabulary.
- FR-SC-3 (domain of the Legendrian formulas).  All three formulas are stated under "for an oriented Legendrian front":
  `L` with a front `F` on ng:front-domain.  Etnyre's Lemma 2.22 holds for all Legendrian knots; restricting to those with
  a generic front is WEAKER than the literature and exactly the registry's scope.  `IsEmbeddedCircle L` (2π-periodic,
  injective, immersed) is the "oriented Legendrian knot" of row 84.
- FR-SC-4 (conventions as fields).  `contact_space`, `positive_orientation`, `cusps_down_or_up` are provable on the
  accepted layer (proved in the sketch: `srcContact_contact_space`, `srcContact_positive_orientation`,
  `downCount_add_upCount`), so they add no strength; they are kept so that the printed sentences have fields.  Option:
  drop them (the interface reviewer's call); the consumers do not use them.
- FR-SC-5 (real-valued).  `r`, `tb`, `sl` are `ℝ`-valued (the literature's `(D−U)/2` is a half-integer).  Integrality of
  `sl` on transverse knots FOLLOWS from `transverse_front_writhe`.
- FR-SC-6 (D, U on the parametrized front).  `downCount`/`upCount` are the accepted FR-2 derivative criteria on `F`'s own
  parametrization (`IsFrontOf` fixes it to `θ = 2πt`); counts are parametrization-free but this is not re-proved.
- Non-vacuity: `SrcContactClauses` is satisfiable iff the two substantive consequences hold for the specific real number
  `slCircle` — true mathematics (Etnyre eq. (5), (7), (17); Geiges Lemma 3.3) in the checked conventions (F-3).  No clause
  is stated for an object the document lacks; no clause asserts existence of fronts/pushoffs.

## 2. `SM.sl` (sketch §1-2)

```lean
theorem IsPositiveTransverseEmbedding.constFamily (h : IsPositiveTransverseEmbedding (2π) T) : TransverseFamily (2π) (fun _ => T)  -- proved
def slCircle (T : ℝ → E3) : ℝ :=
  if h : IsPositiveTransverseEmbedding (2π) T then
    selfLinking (2π) T (Classical.choose (fd_linking_calculus.transverse_uniform (2π) (fun _ => T) h.constFamily)) else 0
def TransverseKnot.circle (K) : ℝ → E3 := fun θ => toE3 (K.T (θ / 2π))      -- 1-periodic Space → 2π-periodic E3
def TransverseKnot.spatial (K) : SpatialLink 1 := ⟨fun _ => K.T, …⟩          -- the row-91 object; projLoop = K.xz (rfl)
def TransverseKnot.sl (K) : ℝ := slCircle K.circle
```
`ε` is the radius `ε₀` of row 88's `transverse_uniform` for the constant family (fixed once by `Classical.choose`);
`self_linking_invariant` makes the value independent of every admissible radius (U1a) and constant along transverse
families (U1b).  ℝ-valued by decision (F-2); `∃ n : ℤ, K.sl = n` is a corollary of row 94.  Bridge lemmas needed
(U1, §4): `slCircle_eq_selfLinking`, `slCircle_family`, `slCircle_reparam` (via the family `ρ_s = (1−s)id + sρ`,
positive since `α((T∘ρ_s)′) = ρ_s′·α(T′)`), `slCircle_of_transverselyIsotopic` (the `ContDiffOn … (Icc 0 1 ×ˢ univ)`
family of `TransverselyIsotopic` becomes a `TransverseFamily` on `ℝ × ℝ` after the clock `Real.smoothTransition`;
`ContDiffOn.comp_contDiff`).  No change of variables in the Gauss integral is ever needed.

## 3. The rows (sketch §4)

```lean
structure FdContactData : Prop where
  over_rule_sign : ∀ K s t, K.front.IsDouble s t → (K.front.isOver s t ↔ yOf K.T s < yOf K.T t) ∧
      K.front.crossSign s t = (SignType.sign (det (K.front.vel s) (K.front.vel t)) : ℤ)          -- sentence 1 (definitional)
  front_writhe : ∀ K : TransverseKnot, K.sl = K.front.writhe                                       -- fd:front-writhe
  representative_bound : ∀ K X, Nonempty (K.spatial.HeightMarking K.spatial.projLoop X) →
      K.sl ≤ ((-degAZ (P X) - 1 : ℤ) : ℝ)                                                          -- fd:representative-bound
namespace CV
structure AxEtnyreData  : Prop where self_linking_eq_writhe : ∀ K, (∀ t, deriv (xOf K.T) t = 0 → 0 < deriv (zOf K.T) t) → K.sl = K.front.writhe
structure AxSlboundData : Prop where bound : ∀ K X, Nonempty (K.spatial.HeightMarking K.spatial.projLoop X) → K.sl ≤ ((-degAZ (homfly X) - 1 : ℤ) : ℝ)
theorem ax_etnyre_of (h : FdContactData) : AxEtnyreData ; theorem ax_slbound_of (h : FdContactData) : AxSlboundData  -- proved (P_eq_homfly)
```
Row 94 readings.  "T … whose specified xz projection D_T is an ordinary finite regular generic diagram" = every
`TransverseKnot` (def:transverse-front is that class), `D_T` read polygonally as a `HeightMarking` of the one-component
spatial link `K.spatial` (over = smaller y = `K.IsOver`; the SAME reading row 91 uses for its endpoint, so no
`Carries`-to-`HeightMarking` bridge exists — the memo's `SmoothKnotDiagram.Carries` is NOT in work/lean (grep) and is
dropped); "P_T the original campaign polynomial of this actual diagram" = `P X`; the two closing sentences (3418-3421)
are commentary (no field).  Rows 161/162: `CV.ax_etnyre`, `CV.ax_slbound` are free theorem names (plan §161/§162);
recorded narrowing of 162 to knots with a generic front (the accepted class = fd:contact's domain; the only consumer,
thm:carrierfloor (C), applies it to the constructed lift `K_T` with front `T`, d3_floor:930-987).
Fidelity risks:
- FR-FC-1 `sl` is `TransverseKnot.sl` (ℝ), the fd:framed-linking number at the row-88 radius; equality with the integer
  writhe is the printed display; the memo's `sl`-as-parameter (D-F10 (iii)) is superseded — D-F10 is void now that
  `selfLinking` is accepted (the memo's objection was the absence of an independent definition).
- FR-FC-2 the reading of `D_T` is `HeightMarking` (FR-1); the bound is stated for EVERY polygonal reading `X`
  (`P X` is reading-independent by rp:record-polynomial, not re-proved here).
- FR-FC-3 sentence 1 is rendered on the accepted class (definitional), as the memo did.
- FR-FC-4 (161) "front diagram of a transverse knot with no downward vertical tangency" = `K.front` of a
  `TransverseKnot` with the printed hypothesis kept explicitly (redundant: `vertical_up`); the CV text never defines
  `sl`; it is read as SM's (rem:sl-convention).  A CV lift of an arbitrary front (d3:930-987) is the consumer's job.
- FR-FC-5 (162) "the HOMFLY–PT polynomial of the knot it presents, in the normalization of ax:homfly" = `homfly X`
  (`CV.ax_homfly`'s map = `SM.homfly`; `P X = homfly X` by lp:core); narrowing as recorded.
- FR-FC-6 (162) the source-fidelity paragraph (max over representatives read at one value) is commentary; no field.

## 4. The proof route of row 94 and the missing bridges (sketch §5)

Printed proof step → accepted row → bridge:
1. `T` (row-92 knot) → row 84 input: `K.circle` 2π-periodic on `E3`; `TransverseNeighborhoodHyp K.circle` = **U0**
   (`IsEmbeddedCircle`: smooth, 2π-periodic, injective mod 2π, immersed; `α(T′) > 0` — from `K.positive`, chain rule
   `deriv (K.T ∘ (·/2π)) = (1/2π) K.T′`; ~120 lines).  Row 84 gives `L`, `T′` with `IsPositivePushoff L T′ ∧
   TransverselyIsotopic T′ T`, and `Ψ` with `Ψ 1 (L θ) = T θ`.
2. Row 87 on `L` (`GenericFrontHyp` from row 84's `legendrian_circle`, `legendrian` via the eta bridges §5.0, proved):
   `Φ`, `L_T = Φ 1 ∘ L`, `IsGenericFront L_T`, and the pushoff clause on the annulus of `T′`: `TransverselyIsotopic T′
   (Φ 1 ∘ T′) ∧ IsPositivePushoff L_T (Φ 1 ∘ T′)`.
3. "fd:linking-calculus preserves self-linking along this smooth positive transverse family": `sl(T) = sl(T′) = sl(Φ₁∘T′)`
   = **U1** (`U_sl_isotopy`; §2).
4. "The preceding cusp calculation identifies its value with sl_Ng(F_T)": `src_contact_clauses.pushoff_slNg` (proved)
   applied with `F_T` = **U2** (`U_legendrianFront`: `L_T`'s xz front as a `SmoothFront` with `IsFrontOf`): the sketch's
   `IsFrontOf` needs `F.comp 0 = t ↦ (x(2πt), z(2πt))`; fields: `cusps_finite` from `finite_cusps` (+ `z′ = yx′`: a cusp
   of the loop ⇔ `x′ = 0`), `cusp_semicubical`/`cusp_nonvertical` from `IsExactCuspGerm` (with `u = y − y₀`,
   `u′ ≠ 0`: `det(γ″,γ‴) = 8A²u′⁵`, `x″ = 2Au′²` — FrontSmooth's `germFront_*` covers the linear parameter; a chain-rule
   reparametrization lemma or a direct Leibniz computation is needed), `no_vertical` (the printed "z′ = yx′ makes the
   front tangent vanish wherever x′ = 0"), `doubles_finite`/`transverse`/`no_triple`/`cusp_alone` from `IsGenericFront`
   under `θ = 2πt`.  HARD-ish: ~800 lines.
5. "Lemma fd:ng-bound, applied to F_T": needs a rounding `S` with `F_T.IsRounding S` = `∃ G, GeomRounding F_T G ∧
   Marking F_T S`.  `G` := the end of ce:rounding's family (accepted `ce_rounding.exists_family` on the spatial link of
   `L_T` = **U3** `U_spatialOf`: `SpatialLink 1` with `CuspedProjection` — heights distinct at double points from
   embeddedness, the exact germ on an interval from continuity of `y′`, all under `θ = 2πt`; ~600 lines), converted to
   `GeomRounding` (forgetful: drop `collar`, reindex cusps — `F_T.comp 0 = sp.projLoop 0` definitionally when `F_T` is
   BUILT from `sp`; the sketch's `LegendrianPackage` fixes both) = part of **U5**.  `S` with `Marking F_T S` = **U4**
   (`U_reading`, F-4: `S := (realize (oword F)).diagram`, `RecordIso (frontRecord F) S.record` from `U8R.recordIso` +
   `realizeRecordIso`, then `Marking.ofRecordIso` — the missing converse: `between_iff` from `succ_eq`, i.e. on a finite
   cycle the successor determines `cycBetween` (both `frontRecord.succ = cycSucc` on parameter keys and `S.record.succ
   = nextVisit` with `nextVisit_no_between`, `visitBetween_iff_cycBetween` available); ~900 lines, the main risk).
6. "Lemma cp:finite-contact-path … P_{S(F_T)} = P_{D_T}": needs (i) `Nonempty (sp.CleanCuspSmoothing G)` ✓ (row 89's
   end), (ii) `Nonempty (sp.HeightMarking G S)` from `Marking F_T S`: slope rule = height rule on a Legendrian at its
   double points (`y = z′/x′`, `x′ ≠ 0` there since cusps are not double points), occurrences via the accepted
   `CleanCuspSmoothing.occEquiv`, signs via `crossSignOf_eq` = **U5** (`U_transport`, ~600 lines); (iii) the supplied
   family `G_t = Ψ_t ∘ Φ_{1−t} ∘ L` as a `SpatialFamily 1` = **U6** (`U_family`): time reparametrized by the clock
   `η = Real.smoothTransition` so that joint `C^∞` on `ℝ × ℝ` follows from the two `ContDiffOn … (Icc 0 1 ×ˢ univ)`
   isotopies by `ContDiffOn.comp_contDiff`; slices embedded (bijections ∘ embedding) and regular (`fderiv` of a map with a
   smooth inverse is injective); ends `G 0 = L_T` (`Ψ 0 = id`, `η 0 = 0`), `G 1 = K.spatial` (`Φ 0 = id`, `Ψ 1 ∘ L = T`,
   `toSpace ∘ toE3 = id`), as `SpatialLink` equalities (ext on `T`); the endpoint reading transported by `▸`; plus **U6a**
   `U_regular` (`K.spatial.RegularGenericProjection`: `occSetOf` finite from `K.doubles_finite`, heights distinct from
   `y_ne_of_isDouble`); ~700 lines.  Row 91 (`cp_finite_contact_path.endpoint_polynomial`) then gives `P S = P X`.
7. Assembly: `rw [e1, e2, e3, ← e5]; exact_mod_cast e4` — DONE (`fd_contact_of_units`, sketch §5.2).  Also
   `U_package_of : U2 → U3 → U4 → U5 → U_package` is PROVED through `ce_rounding` (sketch §5.3).

Vocabulary bridges, named: `toE3`/`toSpace` (proved inverse), `TransverseKnot.circle` (1-periodic → 2π), `TransverseKnot.spatial`
(knot → `SpatialLink 1`, `projLoop = xz` rfl), `IsFrontOf` (2π curve → 1-periodic `SmoothFront` loop), `alpha_eq_lcContactForm`
(TN/GF/LC contact forms, rfl), the six TN ↔ GF eta bridges (proved), `LegendrianPackage` (one object carrying the front,
the spatial link, the rounding as `IsRounding` AND as `CleanCuspSmoothing` + `HeightMarking`).

Hard steps and risks (ordered): (R1) U4 polygonal reading via `Marking.ofRecordIso` — combinatorics of finite cyclic
orders on both sides, 600-1200 lines; fallback: extract a `Marking` directly from the sweep block's construction
(FrontRowsW2S §U8R builds `oword F` from the front's events; a marking may be recoverable from `recordIso F`'s data) —
if neither, row 94 is blocked by FR-1 (readings never asserted), which would then have to be recorded as a package-level
gap.  (R2) U2 cusp criteria under the nonlinear coordinate `u = y − y₀` (Leibniz to order 3).  (R3) U6 joint smoothness
and slice regularity of the composed isotopies (ContDiffOn on a closed strip; inverse-function derivative argument).
(R4) U1 extension of a `ContDiffOn (Icc 0 1 ×ˢ univ)` family to `ℝ × ℝ` and the reparametrization family.  None is
mathematically doubtful; all are engineering.

Effort estimate: axiom module (`SM/SrcContact.lean`, from sketch §0-3) 250 lines / 2 h; rows module (`SM/FdContact.lean`,
`CV/SlBound.lean`) 150 lines / 1 h; U0 150 / 3 h; U1 400 / 8 h; U2 800 / 14 h; U3 600 / 10 h; U4 900 / 16 h (risk R1);
U5 600 / 10 h; U6 700 / 12 h; assembly 80 / done.  Total ≈ 4,600 lines (range 4,000-6,500), ≈ 75 prover-hours; with
U1, U2, U3, U4, U6 independent and in parallel, 2-3 working days of wall clock.

First prover units (in this order, all against the sketch's exact Prop statements):
1. `SM/SrcContact.lean` — port sketch §0-3 (axiom + `slCircle` + `IsFrontOf` + sanity theorems); interface review
   against the registry text (3 lenses + 2 refuters); register nothing new (name already fixed).
2. **U1** `U_sl_radius`, `U_sl_family`, `U_sl_reparam`, then `U_sl_isotopy` (row 88 only; unlocks the sl chain).
3. **U4** `U_reading` (`Marking.ofRecordIso` + the sweep/realize isos) — the risk item, started early.
4. **U2 + U3** `U_legendrianFront`, `U_spatialOf` (one unit: build the `SpatialLink 1` first, the `SmoothFront` from
   its `projLoop`, so `IsFrontOf` and the cusp-set identifications are `rfl`).
5. **U6** `U_family` + `U_regular`, then **U5** `U_transport`, then the row: `fd_contact := fd_contact_of_units …`,
   `CV.ax_etnyre := ax_etnyre_of fd_contact`, `CV.ax_slbound := ax_slbound_of fd_contact`.

## 5. Decisions to record in AUTHOR_NOTES (proposed text)

D-SC-1 ∃-form with the three formulas as separate fields; equivalence with the substituted form proved
(`srcContact_iff_consequence`).  D-SC-2 `sl` := `slCircle`/`TransverseKnot.sl` (ℝ-valued, radius fixed by
`Classical.choose` on row 88's `transverse_uniform`); integrality a corollary.  D-SC-3 `D_T` read by `HeightMarking` of
`K.spatial` (row 91's own endpoint reading); the memo's `Carries` dropped (never in work/lean).  D-SC-4 D-F10 (iii)
superseded: rows 161/162 are theorems on the real `sl` (`CV.AxEtnyreData`, `CV.AxSlboundData`, derived from
`FdContactData`); narrowing of 162 recorded (FR-FC-5).  D-SC-5 the convention fields FR-SC-4 kept unless the interface
reviewer asks to drop them.  D-SC-6 the transverse-front clause uses the accepted `SmoothKnotDiagram.writhe` (over =
smaller y), consistent with `selfLinking` by the sign audit and the numeric probe (F-3).
