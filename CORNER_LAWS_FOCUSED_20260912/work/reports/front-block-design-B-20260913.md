# Front block design — TAG B (the printed SMOOTH front class, with a record bridge to polygonal diagrams), 2026-09-14 02:10 UTC / 10:10pm ET

Scope: pending rows 73-94 of `tools/claims.py` (sm-3:1825-3520), the literature interfaces ng:finite-word (sm-3:2170-2206) and
src:contact (sm-3:3341-3365), `work/lean/axiom-policy.json` (policy names `SM.ng_finite_word`, `SM.src_contact`). Emphasis of this
panel member: fidelity to the printed smooth class (semicubical cusps, dz/dx, vertical tangencies) and what a record-level bridge to the
accepted polygonal `Diagram` can and cannot carry. Every Lean fragment quoted below is in the companion file
`work/reports/front-block-design-B-20260913-sketch.lean.txt` (519 lines), which elaborates against the built library with
`lake env lean` (Lean v4.34.0-rc2, Mathlib 85e3a25e); it contains exactly one `sorry`, the proof body of the ng:smoothing-record
statement (marked). Nothing was written under `work/lean`.

## 0. Verdict in six lines

1. The printed smooth class IS cheaply statable and faithful: a front = `c ≥ 1` `C^∞` 1-periodic maps `ℝ → Plane`, cusps = zeros of
   `γ'` with `det(γ'', γ''') ≠ 0` (the derivative form of the semicubical normal form) and `x'' ≠ 0`, no vertical tangency on regular
   arcs, finitely many transverse double points, no triple point, cusps alone; over = smaller `dz/dx`; downward cusp iff
   `x''·det(γ'',γ''') < 0`. Typechecked (`SmoothFront`, section 1 of the sketch); the printed exact germ passes the criterion with
   `det = 8A²`, `x'' = 2A`, discriminant `16A³` (proved, `germFront_semicubical`, `germFront_cuspDisc`).
2. `S(F)` as a Lean object must be a polygonal `Diagram` (that is where `P` lives). The faithful-and-cheap bridge is a *named-record
   marking* `F.Marking S` whose fields are verbatim the items of ng:smoothing-record ("component circles, including crossing-free
   ones, crossing occurrences, cyclic orders, over/under bits and signs"); `d(F) = degAZ (P S)` is then independent of `S` by
   rp:record-polynomial (`lmF_eq_of_recordIso`, accepted). This is the same polygonal reading the accepted layer made for
   "diagram" (sm-3:337-343, lem:gauss-pl-model) and must be recorded, not hidden.
3. The record bridge CANNOT carry the disc-local move certificates (rows 77-80, 82): a record does not know which arcs are planar-
   adjacent, so "after rounding the arcs bound an empty bigon" is not derivable from a marking (section 4). The certificates must be
   proved where the diagrams are polygonal: on Rutherford words realized as grid diagrams (this is also what the printed proofs do).
4. Hence the only place the smooth class costs real proof effort is the second sentence of ng:commutation, "every supplied finite
   front can be represented by a finite elementary front word" — for smooth fronts an analytic sweep theorem (6-10k lines, the
   block's rock; printed, not an unprinted bridge). Rows 83/93 on the smooth class are exactly as far away as that theorem.
5. Rows 84-92, 94 are smooth contact geometry in either design; statable now (sketch section 6), provable far beyond the horizon;
   rows 90-91 and 94 additionally hit a scope gap (ambient isotopy ⇒ `LinkEquiv` is Reidemeister's theorem, excluded by D2).
6. Recommendation: adopt the smooth class for the DEFINITION rows and the contact rows, words + grid realizations for the
   certificates, the abstract descent induction (sorry-free, section 4 of the sketch) for row 83, and isolate the smooth-front →
   word representation theorem as the single named bridge, attacked last. If it does not land, 83/93 fall back to the word/PL
   class (panel A) with the class change recorded on those two rows only.

## 1. Printed inventory (rows, lines, objects and operations used)

| # | id | lines | kind | objects / operations the statement uses | inputs |
|---|---|---|---|---|---|
| 73 | ng:front-domain | 1825-1841 | def | map of a nonempty finite union of parameter circles → oriented (x,z) plane; finitely many transverse double points; ordinary semicubical cusps with `x''(0) ≠ 0` in a semicubical parameter; no vertical tangency on regular arcs; cusps meet nothing; over = smaller dz/dx; downward cusp = upper arm → lower arm; D, w (over-first det signs), s; S(F) by clean-disc cusp replacement | — |
| 74 | ng:smoothing-record | 1843-1868 | lemma | any two S(F) have the same full named record (components incl. crossing-free, occurrences, cyclic orders, bits, signs) ⇒ same P | rp:record-polynomial |
| 76 | ng:commutation | 1921-1948 | lemma | disjoint-gadget commutations, deformations without singular event preserve D, w, d, B; every front = finite elementary word `l_m, r_m, σ_m` | rp (records equal) |
| 77-79 | ng:front-I/II/III | 1950-2006 | lemma | word replacements `l_mσ_{m∓1}r_m ↔ ∅`, `l_{m∓1}σ_mσ_{m∓1} ↔ l_m`, `σσσ ↔ σσσ`; roundings are RI/RII/RIII sites; Δw, ΔD, Δd | lmF RI/RII/RIII invariance (lp:lm) |
| 80 | ng:deletions | 2008-2044 | lemma | empty zigzag: Δs = −2, ΔD ∈ {0,−2}, Δw = Δd = 0; crossed cusp `l_iσ_i ↦ l_i`: Δs = −1, Δw = 1, ΔD = ∓1, ΔB ∈ {−2,0} | planar isotopy, RI |
| 81 | ng:circle | 2046-2074 | lemma | separated standard circle (one left, one right cusp, no crossing): deletion preserves B; unions have B = 0; nesting allowed | lp:split-circle, P_U = 1, P ≠ 0, `degAZ_mul` |
| 82 | ng:cusp-skein | 2076-2168 | lemma | `A = l₂σ₁, A' = l₁σ₂, C_top = l₁, C_bottom = l₂`; (t,u) sign table; skein in R; degree of sums; `B(A) ≥ min(B(A'),B(C))`; `s(C) = s(A)−1` | lp:core skein, P ≠ 0, `degA_add_le` |
| lit | ng:finite-word | 2170-2206 | axiom | typed words; principal chain from moves (1)-(3); stop at first strict s-decrease or standard-circle base; s never increases before; smoothing branch has smaller s | — |
| 83 | ng:local-front-bound | 2305-2350 | thm | `w(F) − D(F) ≤ −deg_a P_{S(F)} − 1` for every front on the domain; strong induction on s(F) along the chain | 74, 76-82, ng:finite-word |
| 84 | fd:transverse-neighborhood | 2395-2559 | lemma | smooth embedded T with α(T') > 0; embedding `H : S¹×D_δ → ℝ³`, `H*α = hα₀`; Legendrian L with positive pushoff transversely isotopic to T; explicit ambient isotopy L → T | smooth calculus, ODE, Moser |
| 85 | fd:parameter-avoidance | 2561-2584 | lemma | F smooth near K×B, rank q > d at zeros ⇒ bad parameters closed with empty interior | IFT, volume |
| 86 | fd:contact-motions | 2586-2611 | lemma | `X_H = −H_y∂_x + (H_x + yH_z)∂_y + (H − yH_y)∂_z`; global flow; `(φ^s)*α = c α`, c > 0; C^k-closeness | ODE |
| 87 | fd:generic-front | 2613-2783 | thm | contact isotopy to `L_g` with finitely many EXACT germs `x = x₀+Au², y = y₀+u, z = z₀+Ay₀u²+⅔Au³`, transverse doubles, no triple/cusp-on-branch; pushoff annulus carried | 85, 86 |
| 88 | fd:linking-calculus | 2785-3027 | lemma | Gauss integral ℓ; symmetry, family invariance; generic direction; ℓ = ½ Σ mixed signs; uniform framed pairs; `sl(T_s) = ℓ(T_s, T_s + ε∂_y)` constant | analysis on the torus |
| 89 | ce:rounding | 3029-3169 | lemma | spatial L with exact germs; family `L_λ` fixed outside cusp intervals; λ > 0 ⇒ ordinary regular generic diagram, no new crossing | smooth diagram class |
| 90 | ce:smoothing-record | 3171-3208 | cor | permitted smoothed-front diagrams share the record of `D_ε` ⇒ F_D, P_D agree | 89, rp, lp:core |
| 91 | cp:finite-contact-path | 3210-3326 | lemma | spatial L with exact germs; supplied family `G_t` from L to T with generic `D_T` ⇒ `P_{S(F)} = P_{D_T}` | 89, 90, 88, lp:core, lit:homfly *descent under ambient isotopy* |
| 92 | def:transverse-front | 3328-3339 | def | smooth T with `z' − yx' > 0`; xz projection an immersion with finitely many transverse doubles, no triple point; over = smaller y; vertical tangents point up (consequence) | — |
| lit | src:contact | 3341-3365 | axiom | `r = (D−U)/2`, `tb = w − (D+U)/2`, `sl(T₊(L)) = tb − r`; for generic positive transverse fronts sl = front writhe | — |
| 93 | fd:ng-bound | 3379-3402 | lemma | `sl_Ng(F) := w − c↓ ≤ −maxdeg_a P_{S(F)} − 1` (83 restated) | 83, 74, lp:core |
| 94 | fd:contact | 3404-3520 | thm | sign dictionary; `sl(T) = Σ signs` for generic positive transverse fronts; `sl(T) ≤ −maxdeg_a P_T − 1` for T with specified generic `D_T` | 84, 87, 88, 91, 92, 93, src:contact, lit:homfly |

## 2. Facts about the accepted layer that constrain the design

- `P : Diagram → R` (`LocalPolynomial.lean`) on POLYGONAL diagrams only; `P_ne_zero`, `P_skein`, `P_circle`, `P_crossingFree`,
  `P_split_circle`, `P_reidemeister_I/II/III`, `P_planar`, `lmF_eq_of_recordIso` (all in `SM`, `PolynomialBlock.lean`) are accepted:
  lp:core / rp:record-polynomial / lp:split-circle / the smoothing gate are no longer gates for this block.
- `degAZ : R → ℤ` with `degAZ_spec`, `degAZ_mul` (domain), `degA_add_le` (WithBot form) exist; the ℤ-valued
  `degAZ (f+g) ≤ max` for nonzero sums is a 30-line corollary.
- `Diagram.record`, `RecordIso`, `Diagram.compOf/visitCoord/twin/overBit/sign`, `cycBetween`, `cycNext_unique`,
  `nextVisit_no_between` give a complete vocabulary to say "S carries this named record" without building a second record type.
- The move predicates `RI/RII/RIII/IsOrientedSmoothing/IsSplitCircleAddition` are disc-local counting predicates on polygonal
  diagrams (`LocalFrame`, `MoveMatch`, `ArcCover`). Nothing smooth can be fed to them directly.
- Mathlib: `ContDiff ℝ ∞`, `iteratedDeriv`, `Function.Periodic`, `HasDerivAt.prodMk`, `intervalIntegral` all present; no
  `AddCircle`-valued smoothness is needed (period-1 maps of ℝ suffice).

## 3. Options and fidelity (judged clause by clause against sm-3:1825-1841)

**(d) Smooth fronts with an explicit cusp model** (this panel's recommendation for the definition rows).

| printed clause | Lean rendering (`SmoothFront`) | verdict |
|---|---|---|
| actual map of a nonempty finite union of parameter circles to the oriented (x,z) plane | `comp : Fin c → SmoothLoop` (`γ : ℝ → Plane`, `ContDiff ℝ ∞ γ`, `Periodic γ 1`), `0 < c` | faithful (`C^∞`; the text says "smooth" throughout sm-3:2352-2360) |
| finitely many transverse double points, no other singularities | `doubles_finite`, `transverse` (det of velocities ≠ 0), `no_triple`; every zero of `γ'` is a cusp (`cusp_semicubical`) | faithful |
| ordinary semicubical cusps | `deriv γ t = 0 → det (γ'' t) (γ''' t) ≠ 0` | derivative form of the `(u², u³)` normal form (Bruce–Giblin, *Curves and Singularities*, the standard criterion); equivalence with "a semicubical parameter exists" is classical but NOT proved in Lean — recorded as risk 4; verified on the printed exact germ (`8A²`) |
| limiting tangent nonvertical, `x''(0) ≠ 0` | `(γ'' t).1 ≠ 0` at cusps | faithful: `γ''` is the limiting tangent direction in every parametrization |
| no vertical tangencies on regular arcs | `deriv γ t ≠ 0 → (deriv γ t).1 ≠ 0` | faithful |
| cusps meet no other strand or singularity | `cusp_alone` | faithful |
| over = smaller dz/dx | `slope p := (γ' p).2 / (γ' p).1`, `IsOverUnder p q := IsDouble ∧ slope p < slope q` | faithful; sanity `det_pos_iff_of_slope_lt` (proved): the crossing is positive iff the x-velocities agree in sign |
| downward cusp: upper arm → lower arm | `IsDownCusp p := IsCusp p ∧ (γ'' p).1 · det(γ'' p, γ''' p) < 0` | a computed criterion, not the printed words (arms lie on the `γ''` side, the first arm on the `−sgn det` side); exactly one of down/up holds (`isDownCusp_xor_isUpCusp`, proved); on the exact germ the discriminant is `16A³`, so `u` increasing with `A > 0` is upward — agrees with `z(u) − z(−u) = ⅔·2Au³ > 0`. Risk 4 |
| D, w, s | `downCount`, `writhe := Σ_{(over,under)} crossSign`, `sCount := #crossings + #cusps` over the finite sets | faithful |
| S(F): in disjoint clean cusp discs replace each cusp by a simple regular arc, same oriented attachments, no crossing | `IsRounding F S := Nonempty (F.Marking S)` for polygonal `S` | WEAKER geometrically (any polygonal diagram with the front's named record counts); no consumer can tell (rp:record-polynomial); the printed lemma 74 becomes "markings compose to a RecordIso". Recorded as risk 3 with the sm-3:337-343 precedent |

Where (d) is stronger than printed: nowhere (the derivative criteria are exactly the printed ones once "semicubical parameter" is
unpacked). Where weaker: the rounding clause; and the words "actual ordinary diagram" for S(F) are read polygonally.

**(a) PL fronts** (panel A). Faithful on every counted datum; the class is different (no germ, corners for cusps, identity rounding).
Cheapest for the certificates. Its own bridge to fd:contact (smooth F_T → PL front) is unprinted.
**(b) Words as the definition.** Faithful to the certificate section and to ng:finite-word ("For an actual finite front word"), but
deletes the second sentence of ng:commutation and changes rows 73/83/93 to a combinatorial class. Adopted here as the CERTIFICATE
layer, not as the definition.
**(c) Structural class** (free D, w, S with a record iso). Makes ΔD = 1 in type I meaningless; rejected.

## 4. What the record bridge carries, and what it cannot

Carries: (i) well-definedness of `d(F)` and of `B(F)` (`P_eq_of_recordIso`, 2 lines); (ii) row 74 in full (markings compose;
successor from cyclic order by `cycNext_unique`, ~500 lines); (iii) rows 83/93 as statements over `SmoothFront` for EVERY rounding
(`LocalFrontBoundStatement`, typechecked); (iv) the transfer of the word-level bound to a smooth front once a word with a marking-
compatible realization is supplied (ng:commutation's second sentence).
Cannot carry: the Δd = 0 steps of rows 77-80 and the skein triple of 82. Argument: an RII pattern at the record level (two
occurrence-free arcs, a bigon inserted with one common over strand) is realizable planarly only if the two arcs are adjacent in the
plane; a polygonal `S` carrying the same record may place other components between them, so no `RII S S'` exists and the record-
level invariance would need either a re-realization theorem (polygonal Jordan–Schoenflies, lem:gauss-two-discs is itself deferred) or
the P-invariance proof of Lickorish–Millett redone combinatorially. The same holds for the empty monogon of RI and the empty triangle
of RIII. Consequence: the certificates are proved on words realized as grid polygonal diagrams glued to the exterior word (as the
printed proofs do, sm-3:1908-1919), where `RIData/RIIData/RIIIData/OrientedSmoothingData` instances are concrete.

## 5. Recommended representation, with the typechecked sketch (abridged; full text in the companion file)

Module plan (all new, all under `SM/`): `FrontSmooth.lean` (row 73, sketch §1-3), `FrontDescent.lean` (the abstract `Calculus`
and `defect_nonneg`, sketch §4; row 83's induction), `FrontWords.lean` (letters, typing, oriented words, word record, rewrites; sketch
§5), `FrontRealize.lean` (grid realization of an oriented word as a `Diagram` with a marking), `FrontCertificates.lean` (rows 77-82),
`FrontInterfaces.lean` (`SM.ng_finite_word`, `SM.src_contact`), `FrontRepresentation.lean` (row 76b), `ContactVocabulary.lean`
(rows 84-92, 94 statements; sketch §6).

```lean
structure SmoothLoop where (γ : ℝ → Plane) (smooth : ContDiff ℝ ∞ γ) (periodic : Function.Periodic γ 1)
structure SmoothFront where
  c : ℕ;  hc : 0 < c;  comp : Fin c → SmoothLoop
  cusps_finite : {p : Param c | p.2 ∈ Set.Ico 0 1 ∧ deriv (comp p.1).γ p.2 = 0}.Finite
  cusp_semicubical : ∀ i t, deriv (comp i).γ t = 0 → det (iteratedDeriv 2 (comp i).γ t) (iteratedDeriv 3 (comp i).γ t) ≠ 0
  cusp_nonvertical : ∀ i t, deriv (comp i).γ t = 0 → (iteratedDeriv 2 (comp i).γ t).1 ≠ 0
  no_vertical : ∀ i t, deriv (comp i).γ t ≠ 0 → (deriv (comp i).γ t).1 ≠ 0
  doubles_finite : {q : Param c × Param c | … q.1 ≠ q.2 ∧ eval q.1 = eval q.2}.Finite
  transverse : ∀ p q, ¬ SameParam p q → eval p = eval q → det (vel p) (vel q) ≠ 0
  no_triple : …;  cusp_alone : ∀ p q, ¬ SameParam p q → vel p = 0 → eval p ≠ eval q
def IsDownCusp (p) : Prop := F.IsCusp p ∧ (F.acc p).1 * det (F.acc p) (F.jerk p) < 0
def slope (p) : ℝ := (F.vel p).2 / (F.vel p).1        -- over = smaller slope
def writhe : ℤ := ∑ q ∈ F.crossingPairs, F.crossSign q.1 q.2   -- crossingPairs = (over, under) per double point
structure Marking (S : Diagram) where            -- the printed record items of ng:smoothing-record, one field each
  e : Fin F.c ≃ Fin S.Γ.c;  Φ : F.Occ ≃ S.Γ.Visit;  comp_eq : ∀ p, S.compOf (Φ p) = e p.1.1
  between_iff : ∀ p q r, same circle → (cycBetween p.1.2 q.1.2 r.1.2 ↔ cycBetween (S.visitCoord (Φ p)) (…q) (…r))
  pair_eq : ∀ p q, p ≠ q → F.eval p = F.eval q → Φ q = S.twin (Φ p)
  over_iff : ∀ p q, … → (S.overBit (Φ p) = true ↔ F.slope p.1 < F.slope q.1)
  sgn_eq : ∀ p q, … → F.slope p.1 < F.slope q.1 → (S.sign (Φ p).1 : ℤ) = F.crossSign p.1 q.1
def IsRounding (S : Diagram) : Prop := Nonempty (F.Marking S)
def LocalFrontBoundStatement : Prop := ∀ (F : SmoothFront) (S : Diagram), F.IsRounding S →
    F.writhe - (F.downCount : ℤ) ≤ -degAZ (P S) - 1                          -- rows 83 and 93 (slNg F = writhe − downCount)
theorem germFront_semicubical (A y₀) (hA : A ≠ 0) : deriv (germFront A y₀) 0 = 0 ∧ det (γ'' 0) (γ''' 0) = 8 * A ^ 2 ∧ (γ'' 0).1 = 2 * A ∧ …
structure Calculus where  -- row 83's inputs: s, B, Pres, Del, Skein, Base + the seven B/s clauses of rows 76-82
inductive Calculus.Chain : K.α → Prop | base | del | pres | skein   -- ng:finite-word's principal chain
theorem Calculus.defect_nonneg (hfw : ∀ F, K.Chain F) : ∀ F, 0 ≤ K.B F   -- PROVED (strong induction on s)
inductive Letter | l (m : ℕ) | r (m : ℕ) | σ (m : ℕ);  def Letter.step : Letter → ℕ → Option ℕ;  def Word.Closed
def IsTypeI/IsTypeII/IsTypeIII/IsZigzagDeletion/IsCrossedCuspShortcut (W W' : Word) : Prop  -- list rewrites, letter by letter
def IsCuspSkein (A A' C : Word) : Prop  -- A = l_{m+1}σ_m, A' = l_mσ_{m+1}, C ∈ {l_m, l_{m+1}}
structure SmoothKnot where (T : ℝ → Space) (smooth) (periodic) (immersed) (injective)
def IsPositiveTransverse : Prop := ∀ θ, 0 < alpha (K.T θ) (deriv K.T θ)     -- alpha p v = v.z − p.y * v.x
structure GenericTransverseFront (K) : Prop  -- def:transverse-front; theorem vertical_tangent_up PROVED
def gaussLinking (C₁ C₂ : ℝ → Space) : ℝ := (1/(4π)) * ∫ u in 0..1, ∫ v in 0..1, dot3 (C₁ u − C₂ v) (cross3 (C₁' u) (C₂' v)) / ‖…‖³
def HasSl (K) (s : ℝ) : Prop := ∃ ε₀ > 0, ∀ ε, 0 < ε → ε ≤ ε₀ → gaussLinking K.T (K.pushY ε) = s   -- eq. fd:framed-linking
def ContactBoundStatement (IsFrontDiagram) : Prop := ∀ K, GenericTransverseFront K → ∀ S, IsFrontDiagram K S → ∀ s, K.HasSl s → s ≤ −degAZ (P S) − 1
```

Oriented words (not in the sketch): Rutherford's letters are unoriented; the certificates use strand directions (t, u). Add
`dir : cut position → Bool` per cut with consistency through letters; D(W), w(W) read from letter + directions ("The permitted
orientations need not produce a single component" — quantify over all consistent direction assignments). The word record
`Word.record : Record` is computed by tracing strands (occurrences = σ letters × {upper, lower}); the grid realization theorem
supplies a `Diagram` carrying it (`realize_marking`), and `d(W)` is `degAZ (P S)` for any such `S`.

## 6. Row dependency graph and effort (Lean lines; L = lane-days at the smoothing-gate pace)

```
73 SmoothFront ──► 74 (markings ⇒ RecordIso ⇒ P equal)            73 ──► 92/src:contact vocabulary ──► 94 statement
words+typing+orientation ──► word record ──► grid realization ──┬─► 77, 78, 79 (RI/RII/RIII instances, lmF invariance)
                                                                ├─► 80 (Deform/planar + RI, sign −1)
                                                                ├─► 81 (IsSplitCircleAddition, P_split_circle, degAZ_mul)
                                                                └─► 82 (switch + OrientedSmoothingData, P_skein, degA_add_le)
ng:finite-word (axiom on oriented words) + 77-82 ──► Calculus instance ──► 83 on words (defect_nonneg)
76a commutations/deformations (words: planar isotopy of realizations; smooth: record locally constant in a family)
76b smooth front → oriented word with a compatible marking [THE ROCK] ──► 83 on SmoothFront ──► 93
84, 85, 86, 88 independent; 87 ◄ 85, 86; 89 ◄ smooth spatial class; 90 ◄ 89, rp; 91 ◄ 89, 90, 88, lit:homfly descent (GAP); 94 ◄ 84, 87, 88, 91, 92, 93
```

| row | estimate | notes |
|---|---|---|
| 73 | 700-900 | class, derived counts, `Marking`, definition bundle `FrontDomainDefinitionData`; sketch §1-3 is 60% of it |
| 74 | 500-700 | marking composition, successor from cyclic order (`cycNext_unique`), `P_eq_of_recordIso` |
| words | 1500-2200 | letters, typing, oriented words, tracing, `Word.record`, D/w/s |
| realize | 2500-3500 | grid realization → `Shadow.Generic`, marking to the word record; the volume is in `ArcCover`/`Clean` proofs |
| 77/78/79 | 700-1000 each | concrete RI/RII/RIII instances inside one grid cell with arbitrary exterior word; ΔD, Δw bookkeeping |
| 80 | 900-1300 | zigzag: `Deform` of the realization; crossed cusp: RI, old crossing sign −1, cusp direction flips |
| 81 | 400-600 | `degAZ (δ f) = degAZ f + 1` from `degAZ_mul` in a domain; `P_split_circle`; last-component case |
| 82 | 1000-1500 | (t,u) table; triple `(realize A, (realize A).switch x, realize C)`; `degAZ (f+g) ≤ max` in ℤ |
| ng:finite-word | 250-350 | `Calculus` instance on oriented words + `∀ W, Chain W`; independent review before use |
| 83 (words) | 300-500 | instantiate `defect_nonneg`; base = standard circles (`P_circle`, `P_crossingFree`) |
| 76a | 600-900 (words) + 2500-4000 (smooth deformations) | smooth clause: finite data locally constant along a jointly smooth family — compactness/isolation |
| 76b | 6000-10000 | perturb singular x-coordinates apart, prove regular arcs are x-graphs (`x' ≠ 0`), read vertical cuts, build the marking; the only analytic theorem the ng rows need |
| 93 | 60-100 | restatement (`ng_bound_form` is `Iff.rfl`) |
| 92, src:contact | 250-350 + 300-500 | sketch §6 covers 92; src:contact needs Legendrian fronts as `SmoothFront`s of Legendrian knots, `HasSl`, a pushoff predicate |
| 84-88 statements | 100-400 each | embeddings `S¹ × D → ℝ³`, Hamiltonian flows, Gauss integral: statable; proofs 85 ≈ 2-3k, 86 ≈ 2-3k, 88 ≥ 5k, 84 ≥ 6k, 87 ≥ 10k |
| 89-91, 94 | statements 400-600 + 300-500 | 91/94 blocked by the GAP (section 7); proofs ≥ 8k after a decision |

Totals: certificate core (73, 74, words, realize, 77-82, axiom, 83-words, 76a-words, 93) ≈ 14-19k; smooth extras (76a smooth,
76b) ≈ 8.5-14k; statements of 84-92, 94 and src:contact ≈ 3k. Planned total ≈ 29k lines. Not planned: proofs of 84-91, 94 (≥ 35k).
Independent of lp:core / rp / the smoothing gate (all accepted anyway): 73, 77-80 (lmF invariance only), 84-88, 92; 74 and 76 use rp;
81-83, 93 use lp:core.

## 7. First rows to attack and their statements

1. **ng:front-domain** (73): `SM.front_domain_definition : FrontDomainDefinitionData` bundling: `SmoothFront` fields ↔ the printed
   clauses; `isDownCusp_xor_isUpCusp`, `isLeftCusp_xor_isRightCusp` (proved); `det_pos_iff_of_slope_lt` (proved);
   `germFront_semicubical` (proved) as the printed germ's certificate; `IsRounding` with `Marking`; `sCount = crossingPairs.card +
   cuspSet.card`. Reviewer lenses to pre-empt: derivative-form cusp; record-marking rounding.
2. **ng:smoothing-record** (74): `∀ F S S', F.IsRounding S → F.IsRounding S' → Nonempty (RecordIso S.record S'.record) ∧ P S = P S'`
   (`smoothing_record_statement`, the one `sorry` of the sketch).
3. **Word layer + ng:front-III** (79): `∀ W W', IsTypeIII W W' → B W = B W'` via `RIII (realize W) (realize W')` and
   `P_reidemeister_III`; D unchanged (no cusp letters), w unchanged (same strands, same bits).
4. **ng:front-II** (78), then **ng:front-I** (77): `RII`/`RI` instances; for I: Δw = ΔD = 1 in the curl-creating direction, one
   down and one up cusp from `(l_m, σ, r_m)` with the direction bits.
5. **ng:deletions** (80). Then 81, 82 (gate-free now), the axiom statement (independent review), 83 on words.
Deferred to last: 76b; on its outcome rows 83/93 are either smooth (this design) or word/PL (panel A) — decide then, not now.

## 8. Riskiest points and decisions needed

1. **76b** (smooth front → word with marking): 6-10k analytic lines, the block's only genuinely smooth proof; I put its in-horizon
   success at roughly 40%. Without it the smooth statements of 83/93 stay pending while the word-level bound is proved. Decision
   for Mark: is a smooth-class 83/93 worth ~10k lines over a PL-class 83/93 with a recorded class change?
2. **GAP (rows 91, 94)**: cp:finite-contact-path's last step takes `H_{D_ε} = H_{D_T}` from an *ambient isotopy* using
   lit:homfly's descent; the accepted descent clause is `LinkEquiv` (moves + planar isotopy) and "ambient isotopy ⇒ finite move
   sequence" is Reidemeister's theorem, excluded by design decision D2 (`LinkInterfaces.lean` header). Unprovable from the accepted
   interfaces; needs a policy decision (new literature interface, or statement-only rows) before any effort on 89-91, 94.
3. **Rounding = record marking**: geometrically weaker than the printed clean-disc replacement. Mitigation: docstring with the
   sm-3:337-343 / lem:gauss-pl-model precedent; optionally a geometric `SmoothRounding F G` (smooth cusp-free ordinary diagram
   agreeing with F outside disjoint clean discs) with the theorem "every geometric rounding admits a marking-compatible polygonal
   model" — that theorem IS lem:gauss-pl-model for fronts (≥ 8k) and should not be promised.
4. **Cusp criterion in derivative form** and the computed down/up rule: standard mathematics, checked on the exact germ, but a
   reviewer must accept the unpacking of "in a semicubical parameter u". An optional lemma (Taylor at the cusp, ~500 lines) can prove
   the printed geometric reading (first arm is the locally upper one iff the discriminant is negative).
5. **ng:finite-word fidelity**: `Chain` must not add strength (no global length bound) nor drop clauses ("smoothing branch has
   smaller s", "s does not increase before the first strict decrease" — here consequences of `pres_s`/`skein_s`); the two index
   corrections of sm-3:2284-2290 must be transcribed letter by letter. Independent review before any consumer.
6. **Orientation on words**: Rutherford's words are unoriented; adding direction bits is where the Lean class could silently restrict
   "the permitted orientations" — quantify over every consistent assignment and prove the type-I/II templates admit all of them.
7. **Rows 84-88**: statable with the §6 vocabulary but each proof is a multi-thousand-line analysis project (Moser, ODE flows,
   Gauss integral on the torus); none is within horizon; do not let their statements block the ng rows.
