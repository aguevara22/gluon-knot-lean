import SM.Curl
import SM.TransverseFront
import SM.UniformRotation
import SM.CornerStateSum
import SM.LinkPositiveLift
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! # Rows 99 cf:thm-carrierfloor and 100 thm:floor — design sketch B (proof feasibility)

Companion of work/drafts/floor/DESIGN_B.md (2026-09-15).  Statement-level sketch: `structure … : Prop`
bundles, `def`s, and the interfaces of the proof units as `Prop`s.  NO theorem with `sorry`, NO axiom.
Check: `cd work/lean && lake env lean ../drafts/floor/Sketch_B.lean`.

§0 the assumed interface of the contact lane (row 94): `SmoothKnotDiagram.Carries` copied from
work/drafts/gap2/Gap2Statements.lean §1 and the sl-free writhe bound `TransverseFrontBound`
("to be unified with the contact lane").
§1 row 99: vocabulary (`PositiveMajority`, `UniformOrOneDissent`, `Round`) and the four clause bundles
`CarrierFloorRData/AData/BData/CData`, the row bundle `CarrierFloorData`.
§2 row 100: `CarrierUniformOrOneDissent`, `FloorTheoremData`.
§3 the proof route as library interfaces: `Diagram.switchAll` (the printed D̄), the mirror substitution
`ι`, the rotation unit, the transverse-lift construction (explicit formulas `liftY0`, `circBump`, `liftY`,
`liftT`) and its unit, the curl chain unit, the (B) internals; §4 the assembly signatures. -/

namespace SM

open Link
open scoped ContDiff

noncomputable section
open Classical

/-! ## 0. Assumed interface (contact lane, row 94) — copied, to be unified -/

/-- record-level carrying of the polygonal one-component diagram `X` by the smooth knot diagram `D`
(work/drafts/gap2/Gap2Statements.lean §1, verbatim; the contact lane fixes the final form) -/
structure SmoothKnotDiagram.Carries (D : SmoothKnotDiagram) (X : Diagram) where
  one : X.Γ.c = 1
  τ : X.Γ.Visit → ℝ
  τ_mem : ∀ v, τ v ∈ Set.Ico (0 : ℝ) 1
  τ_inj : Function.Injective τ
  twin_double : ∀ v, D.IsDouble (τ v) (τ (X.twin v))
  doubles : ∀ s t : ℝ, s ∈ Set.Ico (0 : ℝ) 1 → t ∈ Set.Ico (0 : ℝ) 1 → D.IsDouble s t →
    ∃ v : X.Γ.Visit, s = τ v ∧ t = τ (X.twin v)
  order : ∀ v w z : X.Γ.Visit,
    (cycBetween (τ v) (τ w) (τ z) ↔ cycBetween (X.visitCoord v) (X.visitCoord w) (X.visitCoord z))
  over_eq : ∀ x : X.Γ.Crossing, D.isOver (τ (X.overVisit x)) (τ (X.underVisit x))
  sign_eq : ∀ x : X.Γ.Crossing,
    (X.sign x : ℤ) = D.crossSign (τ (X.overVisit x)) (τ (X.underVisit x))

/-- the sl-free consequence of fd:contact (row 94) that clause (C) consumes: "sl(K_T) = w(T)" and
"max deg_a P_{D̄} ≤ −sl(K_T) − 1" composed (= `TransverseFrontBoundData.writhe_bound` of the memo).
EXPLICIT HYPOTHESIS of this lane until row 94 lands. -/
def TransverseFrontBound : Prop :=
  ∀ (K : TransverseKnot) (X : Diagram), K.front.Carries X → K.front.writhe ≤ -degAZ (P X) - 1

/-- the writhe of a carrying front is the polygonal writhe (from `Carries`; unit CARRIES-W) -/
def CarriesWritheUnit : Prop :=
  ∀ (D : SmoothKnotDiagram) (X : Diagram), D.Carries X → D.writhe = X.writhe

/-! ## 1. Row 99 cf:thm-carrierfloor (sm-3:4282-4339) -/

/-- the normalised alternative: "either all principal turns are positive, or exactly one is negative and
all others are positive" -/
def PositiveMajority (C : PolyComp) : Prop :=
  (∀ i, 0 < principalTurn C.P i) ∨
  (∃ i, principalTurn C.P i < 0 ∧ ∀ j, j ≠ i → 0 < principalTurn C.P j)

/-- "after reversing orientation if necessary, …": the alternative holds for `L` or for `−L`
(`PolyComp.reverse`, the accepted `reversal`; `principalTurn_reversal` negates every turn) -/
def UniformOrOneDissent (C : PolyComp) : Prop := PositiveMajority C ∨ PositiveMajority C.reverse

/-- (A) the rounding record `Round(L, D, ε) = (L_ε, D_ε)`: the accepted named construction of
cf:lem-rounding, a function of the data -/
def Round (C : PolyComp) (D : PolygonDiagram C) (ε : ℝ) (h : CornerRounding.Admissible C D ε) :
    RoundingWitness C D ε :=
  CornerRounding.roundedWitness h

/-- Clause (R), sm-3:4284-4290.  `P_reverse` holds for every link diagram (the printed proof is for all
diagrams); the knot sentence and its LinkEquiv consequence are stated as printed. -/
structure CarrierFloorRData : Prop where
  /-- "Then P_{−D} = P_D" -/
  P_reverse : ∀ X : Diagram, P X.reverse = P X
  /-- "consequently an oriented knot and its reverse have the same polynomial" (the knot presented by
  `X`, read through the accepted `LinkEquiv`) -/
  knot_reverse : ∀ X X' : Diagram, X.componentCount = 1 → LinkEquiv X X' → P X'.reverse = P X
  /-- "−D has the same crossing signs" -/
  sign_reverse : ∀ (X : Diagram) (x : X.Γ.reverseShadow.Crossing),
    X.reverse.sign x = X.sign (X.Γ.reverseCrossingEquiv x)
  /-- "and the same writhe as D" -/
  writhe_reverse : ∀ X : Diagram, X.reverse.writhe = X.writhe
  /-- "the rotation of its underlying plane curve is the negative of that of D": for the polygonal
  underlying curve of every component (lem:rot's `rotationNumber`, FR-FL-1) … -/
  rot_reverse_polygon : ∀ (X : Diagram) (i : Fin X.Γ.c),
    rotationNumber (X.reverse.Γ.comp i).P = - rotationNumber (X.Γ.comp i).P
  /-- … and for the underlying plane curve of a smooth diagram (cf:def-turning) -/
  rot_reverse_curve : ∀ γ : ClosedC1Curve, γ.reverse.rot = - γ.rot

/-- Clause (A), sm-3:4291-4304. -/
structure CarrierFloorAData : Prop where
  /-- "returns one curve and one diagram at those data" -/
  one_record : ∀ (C : PolyComp) (D : PolygonDiagram C) (ε : ℝ)
    (h h' : CornerRounding.Admissible C D ε), Round C D ε h = Round C D ε h'
  /-- `D_ε` is `D` (carried) -/
  diagram_eq : ∀ (C : PolyComp) (D : PolygonDiagram C) (ε : ℝ) (h : CornerRounding.Admissible C D ε),
    Nonempty (Carried (Round C D ε h).Lε D.toDiagram)
  /-- "the junction inserted at the corner q_i is determined by ε, by the two incident unit directions
  and by the transition profile" -/
  junction_local : ∀ (C C' : PolyComp) (D : PolygonDiagram C) (D' : PolygonDiagram C') (ε : ℝ)
    (h : CornerRounding.Admissible C D ε) (h' : CornerRounding.Admissible C' D' ε)
    (j j' : ℕ), j < C.k → j' < C'.k →
    C.P j = C'.P j' → CornerRounding.uDir C j = CornerRounding.uDir C' j' →
    CornerRounding.vDir C j = CornerRounding.vDir C' j' →
    (Round C D ε h).Lε.γ '' Set.Icc ((Round C D ε h).a j) ((Round C D ε h).b j) =
      (Round C' D' ε h').Lε.γ '' Set.Icc ((Round C' D' ε h').a j') ((Round C' D' ε h').b j')
  /-- "the rest of the curve is L itself" -/
  rest_is_L : ∀ (C : PolyComp) (D : PolygonDiagram C) (ε : ℝ) (h : CornerRounding.Admissible C D ε)
    (p : Plane), p ∉ (⋃ i, cornerDisc C ε i) → (p ∈ Set.range (Round C D ε h).Lε.γ ↔ p ∈ polygonImage C)

/-- the parameters of `[0,1)` at which the unit tangent of the record equals `u` -/
def tangencySet {C : PolyComp} {D : PolygonDiagram C} {ε : ℝ} (W : RoundingWitness C D ε) (u : Plane) :
    Set ℝ :=
  {t | t ∈ Set.Ico (0 : ℝ) 1 ∧ W.T t = u}

/-- "at each of them the tangent crosses that direction in the positive sense": the parameter lies in
an open junction whose lift has positive derivative there (FR-FL-3) -/
def CrossesPositively {C : PolyComp} {D : PolygonDiagram C} {ε : ℝ} (W : RoundingWitness C D ε)
    (t : ℝ) : Prop :=
  ∃ j, j < C.k ∧ t ∈ Set.Ioo (W.a j) (W.b j) ∧ 0 < deriv (W.θ j) t

/-- Clause (B), sm-3:4305-4318, stated on the normalised data (`PositiveMajority C`); the printed
"after reversing orientation if necessary" is the same clause applied to `(C.reverse, D.reverse)`,
whose record is `Round C.reverse _ ε` (FR-FL-5). -/
structure CarrierFloorBData : Prop where
  tangencies : ∀ (C : PolyComp) (D : PolygonDiagram C), (∀ i, principalTurn C.P i ≠ 0) →
    PositiveMajority C →
    ∃ (u : Plane) (ε₁ : ℝ), euclideanLength u = 1 ∧ 0 < ε₁ ∧ ε₁ ≤ CornerRounding.clearance C ∧
      ∀ (ε : ℝ) (h : CornerRounding.Admissible C D ε), ε < ε₁ →
        ((tangencySet (Round C D ε h) u).ncard : ℝ) = |rotationNumber C.P| ∧
        ((tangencySet (Round C D ε h) (-u)).ncard : ℝ) = |rotationNumber C.P| ∧
        (∀ t ∈ tangencySet (Round C D ε h) u, CrossesPositively (Round C D ε h) t) ∧
        (∀ t ∈ tangencySet (Round C D ε h) (-u), CrossesPositively (Round C D ε h) t)

/-- the hypotheses of clause (C) on a knot diagram `X` whose underlying plane curve is the polygon `C`
(sm-3:4319-4331); the double-point and corner conditions are `X.generic` on `Shadow.single C`
(FR-FL-6); `turn_lt_pi` is printed and redundant (`principalAngle_bounds`) -/
structure CarrierFloorCHyp (C : PolyComp) (X : Diagram) : Prop where
  shadow : X.Γ = Shadow.single C
  positive : ∀ x : X.Γ.Crossing, X.IsPositive x
  turn_ne : ∀ i, principalTurn C.P i ≠ 0
  turn_lt_pi : ∀ i, |principalTurn C.P i| < Real.pi
  alternative : UniformOrOneDissent C

/-- Clause (C), sm-3:4332-4337: display cf:eq-floor, the `f_D = [z⁰]P_D` sentence literally (the
coefficient of `a^d` in `f_D` is `coeffAt d 0`), and the support form covering both. -/
structure CarrierFloorCData : Prop where
  floor : ∀ (C : PolyComp) (X : Diagram), CarrierFloorCHyp C X →
    ((1 - X.writhe : ℤ) : ℝ) - |rotationNumber C.P| ≤ (mindegAZ (P X) : ℝ)
  floor_f : ∀ (C : PolyComp) (X : Diagram), CarrierFloorCHyp C X →
    ∀ d : ℤ, coeffAt d 0 (P X) ≠ 0 → ((1 - X.writhe : ℤ) : ℝ) - |rotationNumber C.P| ≤ (d : ℝ)
  floor_support : ∀ (C : PolyComp) (X : Diagram), CarrierFloorCHyp C X →
    ∀ d k : ℤ, coeffAt d k (P X) ≠ 0 → ((1 - X.writhe : ℤ) : ℝ) - |rotationNumber C.P| ≤ (d : ℝ)

/-- the row: one field per printed clause -/
structure CarrierFloorData : Prop where
  R : CarrierFloorRData
  A : CarrierFloorAData
  B : CarrierFloorBData
  C : CarrierFloorCData

/-! ## 2. Row 100 thm:floor (sm-3:4576-4585) -/

section Floor

open Carrier

variable {n : ℕ} [NeZero n]

/-- "after possibly reversing its orientation either all turns are left, or exactly one turn is right"
(FR-FL-10) -/
def CarrierUniformOrOneDissent (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) (q : Component hn hP S) : Prop :=
  CarrierUniform hn hP S q ∨
  ∃ τ : SignType, τ ≠ 0 ∧ ∃ j₀, turn (ccpCornerPolygon hn hP S q) j₀ = -τ ∧
    ∀ j, j ≠ j₀ → turn (ccpCornerPolygon hn hP S q) j = τ

/-- thm:floor: `min deg_a H⁺_Q ≥ 1 − m_Q − |r_Q| = d_Q`, `H⁺_Q ∈ ℤ[a^{±1}, z²]`, `min deg_z H⁺_Q ≥ 0` -/
structure FloorTheoremData : Prop where
  a_floor : ∀ {n : ℕ} [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Generic P)
    (S : Finset (Crossing P)) (hS : IsDecomposition hn hP S) (q : Component hn hP S),
    CarrierUniformOrOneDissent hn hP S q →
    cornerSlot hn hP S q ≤ mindegAZ (cornerHomfly hn hP S q hS)
  z_parity : ∀ {n : ℕ} [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Generic P)
    (S : Finset (Crossing P)) (hS : IsDecomposition hn hP S) (q : Component hn hP S),
    InSupportM 1 (cornerHomfly hn hP S q hS) ∧ 0 ≤ mindegZZ (cornerHomfly hn hP S q hS)

end Floor

/-! ## 3. The proof route, as library interfaces (one `Prop` per unit; the units prove them) -/

/-! ### 3.1 the printed `D̄`: "the diagram with every crossing switched" (FR-FL-7; NOT `Diagram.mirror`) -/

/-- every crossing switched: the same shadow, the under strand made over -/
def Link.Diagram.switchAll (D : Diagram) : Diagram := D.withOver D.underStrand D.under_mem

theorem Link.Diagram.switchAll_Γ (D : Diagram) : D.switchAll.Γ = D.Γ := rfl

theorem Link.Diagram.switchAll_overStrand (D : Diagram) (x : D.Γ.Crossing) :
    D.switchAll.overStrand x = D.underStrand x := rfl

/-- unit MIR-SW (a): signs negate, writhe negates, the curve still carries the record -/
def SwitchAllBasicUnit : Prop :=
  (∀ (D : Diagram) (x : D.Γ.Crossing), D.switchAll.sign x = - D.sign x) ∧
  (∀ D : Diagram, D.switchAll.writhe = - D.writhe) ∧
  (∀ (γ : SmoothRegularLoop) (X : Diagram), Carried γ X → Nonempty (Carried γ X.switchAll))

/-- unit MIR-SW (b): switching every crossing carries the generators of `LinkEquiv`, the crossing-free
circle and the skein triples (with `D₊`, `D₋` exchanged) — the analogue of `MirrorCarries` for the
printed `D̄` (the accepted `mirrorCarries_*` are about the reflection `Diagram.mirror`) -/
def SwitchAllCarriesUnit : Prop :=
  (∀ D D' : Diagram, PlanarIsotopic D D' → PlanarIsotopic D.switchAll D'.switchAll) ∧
  (∀ D D' : Diagram, RI D D' → RI D.switchAll D'.switchAll) ∧
  (∀ D D' : Diagram, RII D D' → RII D.switchAll D'.switchAll) ∧
  (∀ D D' : Diagram, RIII D D' → RIII D.switchAll D'.switchAll) ∧
  (∀ D : Diagram, D.IsCrossingFreeCircle → D.switchAll.IsCrossingFreeCircle) ∧
  (∀ Dp Dm D0 : Diagram, IsSkeinTriple Dp Dm D0 →
    IsSkeinTriple Dm.switchAll Dp.switchAll D0.switchAll)

/-! ### 3.2 the involutive substitution `ι : (a, z) ↦ (a⁻¹, −z)` of the Laurent ring -/

/-- unit MIR-ι: a ring endomorphism of `R` with `ι a = a⁻¹`, `ι z = −z`, acting on coefficients by
`[a^d z^k] (ι f) = (−1)^k [a^{−d} z^k] f`; hence `max deg_a (ι f) = −min deg_a f` -/
structure MirrorSubstitutionData (ι : R →+* R) : Prop where
  ι_a : ι R.a = R.aInv
  ι_aInv : ι R.aInv = R.a
  ι_z : ι R.z = - R.z
  coeff : ∀ (f : R) (d k : ℤ), coeffAt d k (ι f) = (-1) ^ k.toNat * coeffAt (-d) k f
  degAZ_eq : ∀ f : R, f ≠ 0 → degAZ (ι f) = - mindegAZ f
  ne_zero : ∀ f : R, f ≠ 0 → ι f ≠ 0

/-- unit MIR-EQ: the printed identity `P_{D̄}(a, z) = P_D(a⁻¹, −z)` (sm-3:4531-4566) -/
def SwitchAllPolynomialUnit (ι : R →+* R) : Prop := ∀ D : Diagram, P D.switchAll = ι (P D)

/-! ### 3.3 rotation of coordinates ("Rotate coordinates so that u is the downward vertical") -/

/-- the rotation of the plane by the angle `φ` -/
def rotPlane (φ : ℝ) (p : Plane) : Plane :=
  (Real.cos φ * p.1 - Real.sin φ * p.2, Real.sin φ * p.1 + Real.cos φ * p.2)

/-- the downward vertical direction of the `xz` page -/
def downDir : Plane := ((0 : ℝ), (-1 : ℝ))

/-- unit ROT: a record-carrying regular loop may be rotated so that a given unit direction becomes the
downward vertical; the polygonal record is untouched (`det` is rotation-invariant) -/
def RotationUnit : Prop :=
  ∀ (F : SmoothRegularLoop) (X : Diagram) (_ : RecordCarried F X) (u : Plane), euclideanLength u = 1 →
    ∃ (φ : ℝ) (G : SmoothRegularLoop), G.γ = rotPlane φ ∘ F.γ ∧ Nonempty (RecordCarried G X) ∧
      ∀ t, normalize (deriv G.γ t) = downDir ↔ normalize (deriv F.γ t) = u

/-! ### 3.4 the transverse lift (sm-3:4456-4523), explicit formulas -/

/-- `y₀ = −x′ / (v + z′)`, `v = |(x′, z′)|` -/
def liftY0 (γ : ℝ → Plane) (s : ℝ) : ℝ :=
  -(deriv γ s).1 / (euclideanLength (deriv γ s) + (deriv γ s).2)

/-- a `C^∞` 1-periodic bump on the circle, `= 1` at `s₀`, `= 0` at circle distance `≥ δ`, values in
`[0, 1]` (the printed `ψ_j`, realised through `Real.smoothTransition` and `cos` so that periodicity and
smoothness are free) -/
def circBump (δ s₀ s : ℝ) : ℝ :=
  Real.smoothTransition
    ((Real.cos (2 * Real.pi * (s - s₀)) - Real.cos (2 * Real.pi * δ)) / (1 - Real.cos (2 * Real.pi * δ)))

/-- `y = y₀ + Σ_j ψ_j (c_j − y₀)` over the crossing occurrences `v` at parameters `τ v` with the chosen
admissible constants `c v` -/
def liftY (γ : ℝ → Plane) {ι : Type} [Fintype ι] (τ c : ι → ℝ) (δ : ℝ) (s : ℝ) : ℝ :=
  liftY0 γ s + ∑ v, circBump δ (τ v) s * (c v - liftY0 γ s)

/-- the lift `s ↦ (x(s), y(s), z(s))` -/
def liftT (γ : ℝ → Plane) {ι : Type} [Fintype ι] (τ c : ι → ℝ) (δ : ℝ) (s : ℝ) : Space :=
  ((γ s).1, liftY γ τ c δ s, (γ s).2)

/-- "the admissible constants": `z′(s) − c x′(s) > 0` -/
def Admissible' (γ : ℝ → Plane) (s c : ℝ) : Prop := 0 < (deriv γ s).2 - c * (deriv γ s).1

/-- unit LIFT-CONST (sm-3:4477-4494): at a negative crossing an ordered admissible pair exists -/
def LiftConstantsUnit : Prop :=
  ∀ (γ : ℝ → Plane) (sO sU : ℝ), deriv γ sO ≠ 0 → deriv γ sU ≠ 0 →
    normalize (deriv γ sO) ≠ downDir → normalize (deriv γ sU) ≠ downDir →
    det (deriv γ sO) (deriv γ sU) < 0 →
    ∃ cO cU : ℝ, cO < cU ∧ Admissible' γ sO cO ∧ Admissible' γ sU cU

/-- unit LIFT (sm-3:4456-4523): a regular loop without downward vertical tangency carrying an
all-negative record lifts to a positive transverse knot whose front is the loop and carries the record -/
def TransverseLiftUnit : Prop :=
  ∀ (F : SmoothRegularLoop) (X : Diagram), RecordCarried F X →
    (∀ t, normalize (deriv F.γ t) ≠ downDir) → (∀ x : X.Γ.Crossing, X.sign x = -1) →
    ∃ K : TransverseKnot, xzOf K.T = F.γ ∧ Nonempty (K.front.Carries X)

/-! ### 3.5 the iterated curl (sm-3:4423-4455) -/

/-- unit CURL-CHAIN: from the rounding record with its `R` positively crossed `u`-tangencies and an
all-negative carried diagram, `R` applications of `cf_lem_curl` (sites `CurlSite.ofCarried`, discs
inside the corner discs) produce a loop without `u`-tangency carrying a diagram with the same `P`,
writhe lowered by `R`, all crossings negative -/
def CurlChainUnit : Prop :=
  ∀ (C : PolyComp) (D : PolygonDiagram C) (ε : ℝ) (h : CornerRounding.Admissible C D ε)
    (u : Plane) (R : ℕ), euclideanLength u = 1 →
    (tangencySet (Round C D ε h) u).ncard = R →
    (∀ t ∈ tangencySet (Round C D ε h) u, CrossesPositively (Round C D ε h) t) →
    ∀ Xbar : Diagram, Carried (Round C D ε h).Lε Xbar → (∀ x : Xbar.Γ.Crossing, Xbar.sign x = -1) →
    ∃ (F : SmoothRegularLoop) (X : Diagram), Nonempty (RecordCarried F X) ∧
      P X = P Xbar ∧ X.writhe = Xbar.writhe - R ∧ (∀ x : X.Γ.Crossing, X.sign x = -1) ∧
      ∀ t, normalize (deriv F.γ t) ≠ u

/-! ### 3.6 the internals of (B) -/

/-- unit B-LIFT: the construction's global angle `Θ` lifts the unit tangent of the record and equals the
junction lifts on the junctions -/
def GlobalLiftUnit : Prop :=
  ∀ (C : PolyComp) (D : PolygonDiagram C) (ε : ℝ) (h : CornerRounding.Admissible C D ε) (t : ℝ),
    (Round C D ε h).T t = CornerRounding.dirOf (CornerRounding.Θ C ε t) ∧
    (∀ j, j < C.k → t ∈ Set.Icc ((Round C D ε h).a j) ((Round C D ε h).b j) →
      CornerRounding.Θ C ε t = (Round C D ε h).θ j t)

/-- unit B-CHOICE: a unit direction `u` with `±u` no edge direction and, in the one-dissent case, `±u`
outside the closed swept arc of the negative junction (sm-3:4362-4368) -/
def DirectionChoiceUnit : Prop :=
  ∀ (C : PolyComp), (∀ i, principalTurn C.P i ≠ 0) → PositiveMajority C →
    ∃ φ : ℝ, (∀ (j : ℕ) (n : ℤ), CornerRounding.θu C j ≠ φ + n * Real.pi) ∧
      ∀ j, j < C.k → CornerRounding.turn C j < 0 →
        ∀ n : ℤ, φ + n * Real.pi ∉
          Set.Icc (CornerRounding.θu C j + CornerRounding.turn C j) (CornerRounding.θu C j)

/-- unit B-COUNT: the levels `φ + 2πℤ` are met exactly `rot(L)` times, all in open positive junctions,
by the floor identity `⌊x + rot⌋ − ⌊x⌋ = rot` telescoped over the junctions (sm-3:4383-4419) -/
def LevelCountUnit : Prop :=
  ∀ (C : PolyComp) (D : PolygonDiagram C) (ε : ℝ) (h : CornerRounding.Admissible C D ε) (φ : ℝ),
    (∀ (j : ℕ) (n : ℤ), CornerRounding.θu C j ≠ φ + n * Real.pi) →
    (∀ j, j < C.k → CornerRounding.turn C j < 0 →
      ∀ n : ℤ, φ + n * Real.pi ∉
        Set.Icc (CornerRounding.θu C j + CornerRounding.turn C j) (CornerRounding.θu C j)) →
    0 < rotationNumber C.P →
    ((tangencySet (Round C D ε h) (CornerRounding.dirOf φ)).ncard : ℝ) = rotationNumber C.P ∧
    ∀ t ∈ tangencySet (Round C D ε h) (CornerRounding.dirOf φ), CrossesPositively (Round C D ε h) t

/-! ## 4. Assembly signatures (theorems of the units, listed as a route bundle) -/

/-- everything the assembly of (C) consumes besides the accepted rows -/
structure FloorRoute : Prop where
  switchAll_basic : SwitchAllBasicUnit
  switchAll_carries : SwitchAllCarriesUnit
  mirror_subst : ∃ ι : RingHom R R, MirrorSubstitutionData ι ∧ SwitchAllPolynomialUnit ι
  rotation : RotationUnit
  lift : TransverseLiftUnit
  carries_writhe : CarriesWritheUnit
  chain : CurlChainUnit
  clauseR : CarrierFloorRData
  clauseB : CarrierFloorBData

/-- the shape of the (C) assembly theorem (unit C-ASSEMBLE): `FloorRoute → TransverseFrontBound →
CarrierFloorCData`; the row theorem `cf_thm_carrierfloor : CarrierFloorData` is assembled once row 94
lands, as `⟨R, A, B, C_of_bound route fd_contact_bound⟩` -/
def CAssemblyShape : Prop := FloorRoute → TransverseFrontBound → CarrierFloorCData

/-- the shape of thm:floor's assembly (unit FLOOR): `a_floor` from (C) + lem:carriers +
`positiveLift_writhe_eq_carrierCrossingCount` + `cornerSlot_cast`; `z_parity` from `lp_core` -/
def FloorAssemblyShape : Prop := CarrierFloorCData → FloorTheoremData

end

end SM
