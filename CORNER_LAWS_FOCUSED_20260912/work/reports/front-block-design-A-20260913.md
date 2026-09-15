# Front block design — TAG A (PL fronts on the accepted polygonal layer), 2026-09-13 23:30 UTC / 7:30pm ET

Scope: pending rows 73-94 of `tools/claims.py` (sm-3:1825-3520), the literature interfaces ng:finite-word
(sm-3:2170-2206) and src:contact (sm-3:3341-3365), `work/lean/axiom-policy.json`. Everything below was checked
against the built library with `lake env lean` (Lean v4.34.0-rc2, Mathlib 85e3a25e); the full sketch (331 lines,
all lemmas sorry-free, only the word-pattern placeholders and `realize` carry `sorry`) is
`work/reports/front-block-design-A-20260913-sketch.lean.txt`.

## 0. Recommendation in five lines

1. Represent a front as a **PL front**: an accepted generic polygonal `Shadow` all of whose edges are nonvertical.
   Cusps are *derived* (vertices where the x-direction reverses), left/right and up/down are sign conditions on the two
   incident edges, over = smaller slope, `w` = accepted writhe, `S(F)` relational (disc-local replacement in clean cusp
   discs via the accepted `OutsideMatch`/`ArcCover`/`Clean`), and — a PL fact — the front's own diagram is a rounding.
2. Prove the local certificates (rows 76-82) on **Rutherford words** realized as grid PL fronts, exactly as the printed
   proofs do; state ng:finite-word on words; prove ng:local-front-bound first for words, then for all PL fronts via
   ng:commutation's representation theorem (the one big geometric rock of the block).
3. The block splits cleanly: rows 73-83, 93 are combinatorial/PL and fully plannable (~12.8k lines); rows 84-92, 94 are
   smooth contact geometry — statable now (tested vocabulary below), provable only far beyond the horizon, and rows 89-91,
   94 hit two structural gaps that need a decision from Mark (section 7).
4. Be explicit everywhere that the PL class is **not** the printed smooth class with semicubical cusps; the printed text
   sanctions PL diagrams (sm-3:337-343, lem:gauss-pl-model) but has no PL-front model lemma. That lemma is the unprinted
   bridge fd:contact would need; it is not a defect of rows 73-83 but must be recorded on row 94.
5. First rows: ng:front-domain, the word layer + ng:front-III, ng:front-II, ng:front-I, ng:deletions (all gate-free).

## 1. Printed inventory (rows, lines, objects and operations used)

| # | id | lines | kind | objects / operations the statement uses | consumes |
|---|---|---|---|---|---|
| 73 | ng:front-domain | 1825-1841 | def | map of ≥1 parameter circles → oriented (x,z) plane; transverse double points; semicubical cusps (x''(0)≠0); no vertical tangency; cusps meet nothing; over = smaller dz/dx; downward cusp; D, w, s; rounding S(F) in disjoint clean cusp discs | — |
| 74 | ng:smoothing-record | 1843-1868 | lemma | two roundings S(F) → same full named record (components incl. crossing-free, occurrences, cyclic orders, bits, signs) → same P | rp:record-polynomial |
| 76 | ng:commutation | 1921-1948 | lemma | disjoint-gadget commutations; deformations without singular event preserve D,w,d,B; every front = finite elementary word (l_m, r_m, σ_m) | rp (or planar isotopy) |
| 77-79 | ng:front-I/II/III | 1950-2006 | lemmas | word replacements l_mσ_{m∓1}r_m / l_{m∓1}σ_mσ_{m∓1} for l_m / σσσ; roundings are ordinary RI/RII/RIII sites; Δw, ΔD, Δd | lmF RI/II/III invariance |
| 80 | ng:deletions | 2008-2044 | lemma | empty zigzag (two cusps, no crossing) deletion: Δs=−2, ΔD∈{0,−2}, Δw=Δd=0; crossed-cusp shortcut l_iσ_i→l_i: Δs=−1, Δw=1, ΔB∈{−2,0} | planar isotopy, RI |
| 81 | ng:circle | 2046-2074 | lemma | separated standard circle (one left, one right cusp, no crossing) deletion preserves B; unions have B=0; nesting allowed | lp:split-circle, P_U=1, P≠0 |
| 82 | ng:cusp-skein | 2076-2168 | lemma | A=l₂σ₁, A'=l₁σ₂, C_top=l₁, C_bottom=l₂; (t,u) sign table; skein triple E±,E₀; degree of sums; B(A)≥min(B(A'),B(C)); s(C)=s(A)−1 | lp:core skein + P≠0, deg lemmas |
| lit | ng:finite-word | 2170-2206 | axiom | typed words; principal chain of moves 1-3; stop at first strict s-decrease or standard-circle base; block progress; smoothing branch has smaller s | — |
| 83 | ng:local-front-bound | 2305-2350 | thm | w(F)−D(F) ≤ −deg_a P_{S(F)} −1 for every front on the domain; strong induction on s | 74,76-82, ng:finite-word |
| 84 | fd:transverse-neighborhood | 2395-2559 | lemma | smooth embedded T with α(T')>0; embedding H: S¹×D_δ→ℝ³ with H*α = hα₀; Legendrian L with positive pushoff ≃ T; explicit ambient isotopy L→T | smooth calculus, ODE |
| 85 | fd:parameter-avoidance | 2561-2584 | lemma | F smooth near K×B, rank q>d at zeros ⇒ bad parameters closed with empty interior; finite collections | IFT, volume |
| 86 | fd:contact-motions | 2586-2611 | lemma | X_H = (−H_y, H_x+yH_z, H−yH_y); global flow; (φ^s)*α = c α, c>0; C^k-closeness | ODE |
| 87 | fd:generic-front | 2613-2783 | thm | contact isotopy to L_g with finitely many exact semicubical germs (x=x₀+Au², y=y₀+u, z=…), transverse double points, no triple point/cusp on branch; pushoff annulus carried | 85, 86 |
| 88 | fd:linking-calculus | 2785-3027 | lemma | Gauss integral ℓ(C₁,C₂); symmetry, family invariance; generic direction; ℓ = ½Σ mixed signs; uniform framed pairs; sl(T_s) constant | analysis on the torus |
| 89 | ce:rounding | 3029-3169 | lemma | spatial L with exact germs; family L_λ fixed outside cusp intervals; λ>0 ⇒ ordinary regular generic diagram, no new crossing, all data retained | smooth diagram class |
| 90 | ce:smoothing-record | 3171-3208 | cor | permitted smoothed-front diagrams all have the record of D_ε ⇒ F_D, P_D agree | 89, rp, lp:core |
| 91 | cp:finite-contact-path | 3210-3326 | lemma | spatial embedding L with exact germs; supplied smooth family G_t from L to T with generic D_T ⇒ P_{S(F)} = P_{D_T} | 89, 90, 88, lp:core, lit:homfly descent |
| 92 | def:transverse-front | 3328-3339 | def | smooth T with z'−yx'>0, xz projection an immersion with finitely many transverse double points, no triple point, over = smaller y; no cusp; vertical tangents point up | — |
| lit | src:contact | 3341-3365 | axiom | r=(D−U)/2, tb=w−(D+U)/2, sl(T₊(L))=tb−r; sl = front writhe for generic positive transverse fronts | — |
| 93 | fd:ng-bound | 3379-3402 | lemma | sl_Ng(F) := w(F)−c↓(F) ≤ −maxdeg_a P_{S(F)} −1 (restatement of 83) | 83, 74, lp:core |
| 94 | fd:contact | 3404-3520 | thm | sign dictionary; sl(T)=Σ signs for generic positive transverse fronts; sl(T) ≤ −maxdeg_a P_T −1 for T with specified generic D_T | 84, 87, 88, 91, 92, 93, src:contact, lit:homfly |

## 2. Facts about the accepted layer that decide the design

- `RegularPair u v := u ≠ 0 ∧ v ≠ 0 ∧ ¬∃ r<0, v = r•u` (RegularPairs.lean:8): only *exactly antiparallel* consecutive
  edges are forbidden. A PL "wedge" cusp (two edges leaving a vertex to the same x-side, non-collinear) is a legal
  vertex of `Shadow.Generic`. So a PL front **is** a generic polygonal shadow; no new geometric class is needed.
- `Shadow.Generic` = regular ∧ tail_off ∧ transverse ∧ no_triple (LinkDiagram.lean:376-392): tail_off already says
  "no vertex on a non-incident edge", i.e. "cusps meet no other strand"; crossing points are interior points of edges.
- `P D := reMap (phi (T.toTG (lmF D)))` (LocalPolynomial.lean): `P D = P D'` follows from `lmF D = lmF D'`, so the
  RI/RII/RIII/planar-isotopy invariance of `P` is available **now** from `lmF_spec` (LMClauses), without lp:core.
  lp:core is needed only for the skein identity in `R`, `P ≠ 0`, `P_U = 1`; lp:split-circle for `δ·P`.
- `degAZ : R → ℤ` with def:adeg accepted (`AdegDefinition.lean`); `Diagram.record`, `RecordIso` accepted.
- Move predicates are disc-local counting predicates (`LocalFrame`, `MoveMatch`, `ArcCover`, RI/RII/RIIIData,
  `OrientedSmoothingData`, `IsSplitCircleAddition`): exhibiting an instance needs an `OutsideMatch` equivalence and
  arc covers — mechanical on explicit grid coordinates, hard on an arbitrary polygon (design record, fidelity risk 2).

## 3. Options and fidelity

**(a) PL fronts, cusps derived from x-reversal** (recommended). Clause-by-clause against sm-3:1825-1841:

| printed clause | PL rendering | verdict |
|---|---|---|
| actual map of a nonempty finite union of parameter circles to the oriented (x,z) plane | `Shadow` (c ≥ 1 polygons, `traversalEvaluation`) | same reading as accepted def:positive-lift; **class changed** smooth→PL |
| finitely many transverse double points, no other singularities | `Γ.Generic` | faithful (accepted) |
| ordinary semicubical cusps | vertex with `eIn.1 * eOut.1 < 0`; arms non-collinear is a theorem (`cusp_det_ne_zero` from `Regular`) | **divergent**: no germ, no vanishing tangent; captured: location, side, up/down, arm order; lost: (u²,u³) normal form |
| no vertical tangency on regular arcs | every edge has `dir.1 ≠ 0`; between cusps x is monotone (x-sign constant at non-cusp vertices by definition) | faithful in PL; corners are not tangencies |
| limiting tangent at a cusp nonvertical (x''(0)≠0) | built in: a vertical-tangent cusp would not be an x-reversal, so it is not a cusp; the class excludes it as the printed hypothesis does | faithful as an exclusion, **stronger** in that the PL class cannot even express a vertical cusp |
| cusps meet no other strand or singularity | `tail_off` + crossings interior to edges | faithful |
| over = smaller dz/dx | `overStrand x := if slope A < slope B then A else B` (slopes differ by transversality) | faithful; sanity: sign = sgn(o.1·u.1) proved (`det_pos_iff_of_slope_lt`) |
| downward cusp: upper arm → lower arm | `IsCusp ∧ 0 < det eIn eOut` (upper arm = larger slope from the vertex) | faithful for wedge cusps; for smooth cusps "locally upper" means larger z at equal x, which agrees |
| D, w, s | `Nat.card` of down cusps; `diagram.writhe`; crossings + cusps | faithful |
| S(F): replace each cusp in disjoint clean cusp discs by a simple regular arc, same oriented attachments, no crossing | `RoundingData`: disjoint `CuspDisc`s, `OutsideMatch` on their union, one crossing-free arc per disc with equal end points | faithful and relational (as `IsOrientedSmoothing`); **PL peculiarity**: the identity replacement is already a rounding (`F.diagram`), so existence is trivial and d(F) is canonical |

Where (a) is weaker than printed: the theorems hold for PL fronts, and fd:contact needs them for the smooth front F_T
of a Legendrian knot; the passage smooth front → PL front with equal D, w and record-isomorphic rounding is an
unprinted lemma (the text has lem:gauss-pl-model only for ordinary diagrams). Where it is stronger: nothing beyond
the exclusions noted.

**(b) Words only (Rutherford letters as the front).** Faithful to the certificate section and to ng:finite-word ("For an
actual finite front word"), and the printed proofs of 77-82 are word computations. But ng:front-domain says "actual
map ... to the plane" and ng:commutation's second sentence *is* the front→word passage; making words the definition
deletes that theorem and changes the class of 73/83/93 to a combinatorial one. Rejected as the definition, adopted as
the certificate layer (realized words are PL fronts, so nothing is lost).

**(c) Axiomatic/structural class** (components, cusps with types, S(F) as a Diagram with a record iso). Makes D and w
free data: "type-I preserves B" is then not a theorem about geometry (ΔD = 1 has no meaning). Quietly changes the
class to "anything"; rejected.

**(d) Smooth fronts with a semicubical-germ model.** The only option that literally matches fd:contact's consumer.
Needs: `ContDiff` maps of circles, cusp = zero of the derivative with (u²,u³) up to local diffeomorphism, transverse
double points, and a PL-model theorem to even *define* S(F) as a polygonal `Diagram` (there is no smooth `Diagram`).
Statable; every proof passes through the PL model anyway. Rejected for rows 73-83; its vocabulary is what rows 84-92
need (section 6).

## 4. Recommended representation — typechecked Lean sketch (abridged from the companion file)

```lean
structure Front where
  Γ : Shadow
  generic : Γ.Generic
  nonvertical : ∀ s : Γ.Strand, (Γ.dir s).1 ≠ 0                 -- no vertical tangency anywhere

namespace Front  -- (F : Front)
def prev (s : F.Γ.Strand) : F.Γ.Strand := ⟨s.1, s.2 - 1⟩
def eIn (s) : Plane := F.Γ.dir (F.prev s)          def eOut (s) : Plane := F.Γ.dir s
def IsCusp (s) : Prop := (F.eIn s).1 * (F.eOut s).1 < 0            -- x-direction reverses at the tail of s
def IsLeftCusp (s) : Prop := (F.eIn s).1 < 0 ∧ 0 < (F.eOut s).1    -- arms extend to the right
def IsDownCusp (s) : Prop := F.IsCusp s ∧ 0 < det (F.eIn s) (F.eOut s)   -- upper arm → lower arm
def slope (s) : ℝ := (F.Γ.dir s).2 / (F.Γ.dir s).1
def overStrand (x : F.Γ.Crossing) : F.Γ.Strand :=                  -- smaller dz/dx is over
  if F.slope (F.strandA x) < F.slope (F.strandB x) then F.strandA x else F.strandB x
def diagram : Diagram := ⟨F.Γ, F.generic, F.overStrand, F.overStrand_mem⟩
def downCount : ℕ := Nat.card {s : F.Γ.Strand // F.IsDownCusp s}   -- D(F)
def writhe : ℤ := F.diagram.writhe                                  -- w(F)
def sCount : ℕ := Fintype.card F.Γ.Crossing + F.cuspCount           -- s(F)

structure CuspDisc (U : Set Plane) (s : F.Γ.Strand) : Prop where
  disc : IsDisc U            cusp : F.IsCusp s          clean : Clean U F.diagram
  center : F.Γ.tail s ∈ interior U
  other_cusps : ∀ s', F.IsCusp s' → s' ≠ s → F.Γ.tail s' ∉ U
  one_arc : ∃ a : F.Γ.Arc, F.Γ.ArcCover U {a}
  no_inner : ∀ x : F.Γ.Crossing, F.Γ.crossingPoint x ∉ interior U

structure RoundingData (S : Diagram) where                          -- S = S(F)
  U : {s : F.Γ.Strand // F.IsCusp s} → Set Plane
  discs : ∀ c, F.CuspDisc (U c) c.1
  disjoint : ∀ c c', c ≠ c' → Disjoint (U c) (U c')
  out : OutsideMatch (⋃ c, U c) F.diagram S
  clean : ∀ c, Clean (U c) S
  arcs : ∀ c, ∃ (a : S.Γ.Arc) (a₀ : F.Γ.Arc), S.Γ.ArcCover (U c) {a} ∧ F.Γ.ArcCover (U c) {a₀} ∧
    S.Γ.eval a.startPt = F.Γ.eval a₀.startPt ∧ S.Γ.eval a.stopPt = F.Γ.eval a₀.stopPt
  no_inner : ∀ c, ∀ y : S.Γ.Crossing, S.Γ.crossingPoint y ∉ interior (U c)
def IsRounding (S : Diagram) : Prop := Nonempty (F.RoundingData S)
def defectOn (S : Diagram) : ℤ := (F.downCount : ℤ) - F.writhe - degAZ (SM.P S) - 1   -- B(F)
def defect : ℤ := F.defectOn F.diagram
theorem cusp_det_ne_zero {s} (h : F.IsCusp s) : det (F.eIn s) (F.eOut s) ≠ 0      -- proved (from Regular)
theorem det_pos_iff_of_slope_lt {o u : Plane} (ho : o.1 ≠ 0) (hu : u.1 ≠ 0)
    (h : o.2 / o.1 < u.2 / u.1) : 0 < det o u ↔ 0 < o.1 * u.1                     -- proved
end Front

def ng_smoothing_record_statement : Prop := ∀ (F : Front) (S S' : Diagram),
  F.IsRounding S → F.IsRounding S' → Nonempty (RecordIso S.record S'.record)
def ng_local_front_bound_statement : Prop := ∀ (F : Front) (S : Diagram), F.IsRounding S →
  F.writhe - (F.downCount : ℤ) ≤ -degAZ (SM.P S) - 1                                 -- also fd:ng-bound

inductive Letter | l (m : ℕ) | r (m : ℕ) | σ (m : ℕ)               -- Rutherford's letters
def Letter.step (n : ℕ) : Letter → Option ℕ                        -- typing by strand counts
  | .l m => if m ≤ n then some (n + 2) else none
  | .r m => if m + 1 < n then some (n - 2) else none
  | .σ m => if m + 1 < n then some n else none
structure FrontWord where
  letters : List Letter
  typed : letters.foldlM (fun n ℓ => ℓ.step n) 0 = some 0          -- closed fronts: 0 → 0 strands
def FrontWord.realize (W : FrontWord) : Front := sorry              -- grid realization (to build)
def IsTypeIStep (W W' : FrontWord) : Prop := sorry                  -- W = X++Y, W' = X++[l m, σ (m∓1), r m]++Y
def IsCuspSkeinStep (W W' C : FrontWord) : Prop := sorry            -- l₂σ₁ ↔ l₁σ₂ with smoothing C
inductive Step : FrontWord → FrontWord → Prop                       -- comm | typeI | typeII | typeIII |
  ...                                                               -- cuspSkein | zigzag | crossedCusp | circle
structure FrontDeformData (F F' : Front) extends DeformData F.diagram F'.diagram where
  nonvertical : ∀ t ∈ Set.Icc (0:ℝ) 1, ∀ s : F.Γ.Strand, ((F.Γ.withVertices (γ t)).dir s).1 ≠ 0
def FrontEquiv : Front → Front → Prop := Relation.EqvGen fun F F' => FrontDeform F F' ∨ Reparam F.diagram F'.diagram
def ng_commutation_word_statement : Prop := ∀ F : Front, ∃ W : FrontWord, FrontEquiv F (FrontWord.realize W)
def ng_finite_word_statement : Prop := ∀ W : FrontWord, ¬ W.IsStandardCircles →
  ∃ chain : List FrontWord, chain.head? = some W ∧ List.IsChain FrontWord.Step chain ∧
    (∀ V ∈ chain, V.sCount ≤ W.sCount) ∧
    (∃ V, chain.getLast? = some V ∧ (V.sCount < W.sCount ∨ V.IsStandardCircles)) ∧
    (∀ V V' C, FrontWord.IsCuspSkeinStep V V' C → V ∈ chain → C.sCount < W.sCount)
```

Design notes. (i) `FrontDeformData` needs no "cusps constant" field: a continuous never-zero x-component keeps its
sign, and `DeformData.crossings` keeps the crossing pairs — this is "no singular event". (ii) `IsRounding F F.diagram`
is a lemma (choose disjoint small discs; `tail_off` and finiteness give clearance); after it, `d(F)` is canonical and
ng:smoothing-record's record clause is the general **disc-local crossing-free replacement preserves the record**
lemma — the same infrastructure the smoothing gate needs (`smoothing_record`), so it should be built once.
(iii) The word `Step` patterns must be filled with the exact printed factors and index shifts (sm-3:1955-1956,
1977-1978, 1995-1996, 2014-2018, 2087-2090, 2130-2136); the sketch leaves them as named placeholders on purpose — they are the review-sensitive part
of the ng:finite-word axiom. (iv) Modules: `SM/FrontDomain.lean` (row 73), `SM/FrontRounding.lean` (74),
`SM/FrontWords.lean` + `SM/FrontRealize.lean` (76 part), `SM/FrontMoves{I,II,III}.lean`, `SM/FrontDeletions.lean`,
`SM/FrontCircle.lean`, `SM/FrontCuspSkein.lean`, `SM/FrontWordInterface.lean` (axiom `SM.ng_finite_word`),
`SM/FrontBound.lean` (83, 93), `SM/FrontCommutation.lean` (76 sweep). Smooth block: `SM/Contact*.lean`
(names free: the existing `Cusp*`/`Contact*` modules are Chapter-1/2 corner geometry, unrelated).

## 5. Dependency graph, gates, effort (Lean lines, one lane)

```
73 front-domain ──┬─► 74 smoothing-record (record clause: disc-local record lemma [shared with smoothing gate];
                  │        poly clause: + rp:record-polynomial)
                  ├─► words/realize ─┬─► 79 front-III (RIII instance on grid; lmF RIII)         ─┐
                  │                  ├─► 78 front-II  (RII instance; lmF RII)                   │
                  │                  ├─► 77 front-I   (RI instance; new crossing sign; ΔD=1)     │
                  │                  ├─► 80 deletions (zigzag: Deform + lmF isotopy; crossed cusp: RI) │
                  │                  ├─► 81 circle    (IsSplitCircleAddition; needs lp:split-circle + lp:core.ne_zero) │
                  │                  ├─► 82 cusp-skein (switch + concrete IsOrientedSmoothing; needs lp:core skein,   │
                  │                  │        ne_zero; ring lemmas degAZ(f+g) ≤ max, degAZ(a^k f) = degAZ f + k)     │
                  │                  └─► 76a commutations = PlanarIsotopic realizations (lmF isotopy)               │
                  └─► 76b representation: FrontEquiv F (realize W)  [hardest]                                        │
ng:finite-word axiom (on words) + 77-82 + 74 ──► 83 local-front-bound (words) ──76b──► 83 (all PL fronts) ──► 93 ◄──┘
84 ◄─(none)   85 ◄─(none)   86 ◄─(none)   87 ◄─ 85, 86   88 ◄─(none)   92 ◄─(none)
89 ◄─ smooth-diagram class + PL model (GAP-1)   90 ◄─ 89, rp, lp:core   91 ◄─ 89, 90, 88, lp:core, lit:homfly descent (GAP-2)
94 ◄─ 84, 87, 88, 91, 92, 93, src:contact (needs 88's sl and Legendrian fronts to be stated), GAP-1, GAP-2
```

| row | estimate | gates | notes |
|---|---|---|---|
| 73 | 500-700 | none | class, cusps, over rule, counts, `IsRounding`, `IsRounding F F.diagram`, definition bundle |
| 74 | 800-1200 (+50) | rp for the poly clause | disc-local record lemma; reusable by the smoothing gate |
| 76 | 1200-1800 (words+realize+Generic) + 800-1200 (76a) + 2500-4000 (76b) | none | 76b = perturb x-coordinates apart, vertical sweep, deform to the grid: the block's rock |
| 77 / 78 / 79 | 600-900 / 600-900 / 500-800 | none | concrete RI/RII/RIII instances on grid realizations; sign and cusp bookkeeping |
| 80 | 800-1200 | none | zigzag via `Deform`; crossed cusp via RI with sign −1 |
| 81 | 400-600 | lp:split-circle, lp:core.ne_zero | `degAZ (δ * f) = degAZ f + 1` in a domain |
| 82 | 900-1400 | lp:core (skein, ne_zero) | sign table (t,u); triple `(realize A, (realize A).diagram.switch x, realize C)` |
| ng:finite-word | 150-250 statement | independent review | the review-sensitive item of the block |
| 83 | 400-700 (words) + 100 (fronts) | 74, 76b, 77-82, axiom | strong induction on `sCount` along the chain |
| 93 | 60-100 | 83 | restatement |
| 92 | 200-300 statement | none | smooth vocabulary (tested: `SmoothLoop`, `GenericFront`, `vertical_tangent_up` proved) |
| 84-88 | 80-300 each, statements | none | proofs: 85 ≈ 1.5-2.5k, 86 ≈ 1.5-2.5k, 84 ≥ 5k, 87 ≥ 8k, 88 ≥ 4k — beyond the horizon |
| 89-91, 94 | statements blocked by GAP-1/GAP-2 | decision | proofs ≥ 7k after the gaps are resolved |

Plannable total (73-83, 93 fully; 84-88, 92 and the src:contact vocabulary as statements): **≈ 14,500 lines**
(12.8k PL block + 1.7k smooth statements), 10-14 weeks for one lane; three-way parallel: (α) 73 + 74 + 76b,
(β) words/realize + 77-80, (γ) 81-82 + ring lemmas + 83 once (β) lands. Smooth proofs: ≥ 28k more, not planned.

## 6. First rows to attack (all gate-free) and their statements

1. **ng:front-domain** — `structure FrontDomainDefinitionData : Prop` bundling: `Front` ↔ (Generic ∧ nonvertical);
   `IsCusp` ↔ x-reversal; every cusp is left xor right and down xor up (`isDownCusp_or_isUpCusp`, proved);
   `overStrand` is the smaller-slope strand; `writhe = Σ sign`; `sCount = crossings + cusps`; `IsRounding` as printed;
   `IsRounding F F.diagram`. Reviewer lens to pre-empt: "PL class; wedge cusps; identity rounding".
2. **Word layer** (part of 76): `Letter`, `FrontWord`, `realize`, `realize_generic`, letters ↔ singularities
   (`σ` ↔ crossings, `l`/`r` ↔ left/right cusps), word-level `D`/`w`/`s` = those of the realization.
3. **ng:front-III** — `∀ W W', IsTypeIIIStep W W' → (realize W).defect = (realize W').defect`, via
   `RIII (realize W).diagram (realize W').diagram`, `lmF_spec.reidemeister_III`, and sign preservation
   (front sign = product of x-directions, `det_pos_iff_of_slope_lt`; x-directions are constant on x-monotone arcs).
4. **ng:front-II** — same shape with `RII` and `lmF_spec.reidemeister_II`; ΔD = 0 because the two cusp arms persist.
5. **ng:front-I** — `RI` + `lmF_spec.reidemeister_I`; Δw = ΔD = 1 in the curl-creating direction (one down, one up cusp
   by the (l_m, σ, r_m) coordinates); then **ng:deletions** (zigzag: `FrontDeform` inside the rectangle; crossed cusp: RI).

## 7. Riskiest points and decisions needed

1. **76b (front → word)** is the single hardest theorem; without it ng:local-front-bound is proved for realized words
   only (still a faithful theorem about the words ng:finite-word speaks of). Estimate 2.5-4k lines; plan it last.
2. **Class change** (PL vs smooth semicubical): faithful on every datum the ng rows use, but rows 73, 83, 93 are about a
   different class than printed, and fd:contact would need an unprinted smooth→PL front model lemma. Record this in
   AUTHOR_NOTES with the sm-3:337-343 / lem:gauss-pl-model precedent; do not paper over it.
3. **Rounding is near-vacuous in PL** (`F.diagram` is a rounding). Real content of 74 = the disc-local record lemma.
4. **GAP-1**: rows 89-91, 94 speak of P on *smooth* projections ("ordinary finite regular generic diagram" of a smooth
   embedding); the accepted `Diagram` is polygonal and lem:gauss-pl-model is not a selected row. Options: a documented
   smooth-diagram → polygonal-record interface (new literature-style axiom: a policy change, only with Mark's OK),
   statement-only rows with the gap recorded, or consuming CV:ax:slbound directly in the CV lane (cv-lane-plan:897).
5. **GAP-2**: cp:finite-contact-path derives `H_{D_ε} = H_{D_T}` from an *ambient isotopy*; the accepted lit:homfly
   descent clause is `LinkEquiv` (moves + planar isotopy), and "ambient isotopy ⇒ LinkEquiv" is Reidemeister's theorem,
   placed outside the formal scope by design decision D2. Row 91 and hence 94 are unprovable from the accepted
   interfaces without a new interface. Decision needed before any effort on 89-91, 94.
6. **ng:finite-word statement fidelity**: "principal chain", "block progress", "stop at the first strict decrease" are
   prose; the Lean must not add strength (e.g. a global bound on chain length) or drop the smoothing-branch clause. State
   on words, with the eight `Step` patterns transcribed letter by letter (including the two index corrections the SM
   notes at sm-3:2284-2290), and send it to independent review before anything consumes it.
7. **Gates**: 81, 82 need lp:core (skein, `ne_zero`) and lp:split-circle; 74's poly clause needs rp:record-polynomial.
   Everything else in 73-83 is startable now. The concrete move instances on grids are voluminous but mechanical.
