import SM.Rounding
import SM.LinkMoves
import SM.PolynomialBlock

/-! # SM cf:lem-curl — exact negative-curl replacement: SKELETON (judge's FINAL)

Source: reference/SM/sm-3-statesum.tex:3870-3891 (statement), 3892-4280 (proof).  Judge, 2026-09-14:
Skeleton_A.lean (Architect A) with the grafts and repairs of PLAN_FINAL.md §0/§4 — the velocity export
`unchanged_deriv`; Unit R split into the cut/fit package `CutFit` + `exists_cutFit` and the glued arc
`exists_glued_arc` (B's `Cuts`/`InsertedArc`/`GluedLoop` decomposition, so the analytic heart is two
provers, not one); the false clauses of `inserted_arc_props` repaired (`hℓ`, explicit diameter bound);
B's reusable `RIData.crossingPoint_ψ / sign_ψ / writhe_eq`; the printed ordered-ray determinants
(`orderedRay_condition`); the off-window derivative leaf strengthened to the open window
(`deriv_eq_of_offWindow`).  Sections 1-4 are the statement text of Statements_FINAL.lean verbatim; §5
the construction (the printed model `b`, `c`, the positive-turn chart, the affine fit); §6 the three
packages the proof produces (the smooth curl `SmoothCurl`, the polygonal kink `KinkLocation`/
`KinkInsertion`, the record assembly `CarriedAssembly`); §7 the chain of leaf lemmas (all `sorry`,
grouped by the seven prover units U1-U7 of PLAN_FINAL.md §4); §8 the assembly of a `CurlWitness` from
the packages (PROVED from the leaves); §9 the row (PROVED from §8).
Check: `cd work/lean && lake env lean ../drafts/curl/Skeleton_FINAL.lean` (SM/Rounding.olean is built).
Statements of the packages and of every leaf are the interface between units: byte-identical for all
provers; a prover may add intermediate lemmas but must not change a package field or a leaf statement. -/

namespace SM

open Link
open scoped ContDiff

noncomputable section
open Classical

/-! ## 1. Record-level carrying of a polygonal diagram by a `C^∞` regular loop (FR-C1) -/

/-- The polygonal one-component `Diagram X` *carries the record* of the regular smooth loop `γ`
(FR-R1 at record level; lem:gauss-pl-model "the crossing names, the four-ray orders, the traversal
direction and the over/under designations are retained"): every occurrence of `X` is realised at a
parameter `τ v` of `γ`, the two occurrences of a crossing are realised at the same point, the double
points of `γ` are exactly these twin pairs, the branches are transverse, the cyclic order of the
occurrences along the circle is that of `X` (accepted `cycBetween`/`visitCoord`), and the over/under
assignment is `X`'s (sign consistency, def:positive-lift).  This is the accepted `Carried` (Rounding.lean
§4) without its clause `γ (τ v) = crossingPoint v`, which ties the polygon's crossing *points* to the
curve's double points and cannot hold once a curl is inserted near `p` while the polygonal kink lives
on an edge of `X`; it is the reading of the accepted front record `SmoothFront.Marking` (FrontSmooth.lean
§7: occurrence bijection, cyclic order, pairing, over/under bits, signs — no point coincidence).  The
polynomial of the smooth diagram, `P X` (FR-R1), is well defined at this level: two polygons whose records
`γ` carries have isomorphic records, so rp:record-polynomial gives them one `P`. -/
structure RecordCarried (γ : SmoothRegularLoop) (X : Diagram) where
  /-- one parameter circle -/
  one : X.Γ.c = 1
  /-- the parameter (in the fundamental period) at which the occurrence `v` is traversed -/
  τ : X.Γ.Visit → ℝ
  τ_mem : ∀ v, τ v ∈ Set.Ico (0 : ℝ) 1
  τ_inj : Function.Injective τ
  /-- the two occurrences of a crossing are realised at one point of the plane -/
  twin_eval : ∀ v, γ.γ (τ v) = γ.γ (τ (X.twin v))
  /-- every double point of `γ` is one of the crossings, with the two occurrences paired by `twin` -/
  doubles : ∀ s t : ℝ, s ∈ Set.Ico (0 : ℝ) 1 → t ∈ Set.Ico (0 : ℝ) 1 → s ≠ t → γ.γ s = γ.γ t →
    ∃ v : X.Γ.Visit, s = τ v ∧ t = τ (X.twin v)
  /-- transverse double points -/
  transverse : ∀ v, det (deriv γ.γ (τ v)) (deriv γ.γ (τ (X.twin v))) ≠ 0
  /-- the cyclic order of the occurrences along the oriented circle is that of `X` -/
  order : ∀ v w z : X.Γ.Visit,
    (cycBetween (τ v) (τ w) (τ z) ↔ cycBetween (X.visitCoord v) (X.visitCoord w) (X.visitCoord z))
  /-- the over/under assignment is `X`'s: the over-first tangent-determinant sign of the smooth
  double point equals the crossing sign of `X` -/
  sign_eq : ∀ x : X.Γ.Crossing,
    SignType.sign (det (deriv γ.γ (τ (X.overVisit x))) (deriv γ.γ (τ (X.underVisit x)))) = X.sign x

namespace RecordCarried

variable {γ : SmoothRegularLoop} {X : Diagram}

/-- the crossing sign of the smooth diagram at `x`: `sgn det(velocity_over, velocity_under)` -/
def smoothSign (c : RecordCarried γ X) (x : X.Γ.Crossing) : SignType :=
  SignType.sign (det (deriv γ.γ (c.τ (X.overVisit x))) (deriv γ.γ (c.τ (X.underVisit x))))

/-- the writhe of the smooth diagram -/
def smoothWrithe (c : RecordCarried γ X) : ℤ := ∑ x : X.Γ.Crossing, (c.smoothSign x : ℤ)

theorem smoothSign_eq (c : RecordCarried γ X) (x : X.Γ.Crossing) : c.smoothSign x = X.sign x :=
  c.sign_eq x

theorem smoothWrithe_eq (c : RecordCarried γ X) : c.smoothWrithe = X.writhe := by
  unfold smoothWrithe Diagram.writhe
  exact Finset.sum_congr rfl fun x _ => by rw [c.smoothSign_eq]

/-- "no triple points": no three distinct parameters of the fundamental period trace one point -/
theorem no_triple (c : RecordCarried γ X) {r s t : ℝ} (hr : r ∈ Set.Ico (0 : ℝ) 1) (hs : s ∈ Set.Ico (0 : ℝ) 1)
    (ht : t ∈ Set.Ico (0 : ℝ) 1) (hrs : r ≠ s) (hrt : r ≠ t) (hrs' : γ.γ r = γ.γ s)
    (hrt' : γ.γ r = γ.γ t) : s = t := by
  obtain ⟨v, hv, hv'⟩ := c.doubles r s hr hs hrs hrs'
  obtain ⟨w, hw, hw'⟩ := c.doubles r t hr ht hrt hrt'
  have : v = w := c.τ_inj (hv.symm.trans hw)
  subst this
  exact hv'.trans hw'.symm

/-- the double points of `γ` are exactly the realised crossings -/
theorem doublePoints_eq (c : RecordCarried γ X) :
    SmoothRegularLoop.doublePoints γ.γ = {q | ∃ v : X.Γ.Visit, q = γ.γ (c.τ v)} := by
  ext q
  constructor
  · rintro ⟨s, t, hs, ht, hne, rfl, hts⟩
    obtain ⟨v, rfl, -⟩ := c.doubles s t hs ht hne hts.symm
    exact ⟨v, rfl⟩
  · rintro ⟨v, rfl⟩
    refine ⟨c.τ v, c.τ (X.twin v), c.τ_mem v, c.τ_mem _, fun h => ?_, rfl, (c.twin_eval v).symm⟩
    exact X.twin_ne v (c.τ_inj h).symm

end RecordCarried

/-- the accepted `Carried` (Rounding.lean §4) carries the record: the bridge from the output of
cf:lem-rounding to the input of cf:lem-curl -/
def Carried.toRecordCarried {γ : SmoothRegularLoop} {X : Diagram} (c : Carried γ X) :
    RecordCarried γ X where
  one := c.one
  τ := c.τ
  τ_mem := c.τ_mem
  τ_inj := c.τ_inj
  twin_eval := fun v => by rw [c.τ_eval, c.τ_eval, Diagram.twin_fst]
  doubles := c.doubles
  transverse := c.transverse
  order := c.order
  sign_eq := c.sign_eq

@[simp] theorem Carried.toRecordCarried_τ {γ : SmoothRegularLoop} {X : Diagram} (c : Carried γ X) :
    c.toRecordCarried.τ = c.τ := rfl

/-! ## 2. The site: the curve, its diagram, the direction `u`, the point `p` and the embedded arc -/

/-- The hypotheses of cf:lem-curl (sm-3:3873-3878): "Let F be a connected C^∞ immersed circle in
the plane — one component, with finitely many transverse double points and no triple points — given
with an oriented diagram, and let p be a point of F at which the tangent points in a fixed direction
u, isolated among such points, lying in an embedded arc of F that contains no double point and along
which the tangent turns strictly positively."  The arc is the parameter interval `[α, β]` (shorter
than the period), `p = F.γ t₀`. -/
structure CurlSite where
  /-- "a connected C^∞ immersed circle in the plane — one component" -/
  F : SmoothRegularLoop
  /-- "given with an oriented diagram" … -/
  D : Diagram
  /-- … whose record `F` carries ("finitely many transverse double points and no triple points") -/
  carried : RecordCarried F D
  /-- "a fixed direction u" -/
  u : Plane
  /-- the parameter of "a point p of F" … -/
  t₀ : ℝ
  /-- … "at which the tangent points in a fixed direction u" -/
  tangent_at : normalize (deriv F.γ t₀) = u
  /-- "lying in an embedded arc of F": the parameter interval `[α, β]` around `t₀`, shorter than the
  period … -/
  α : ℝ
  β : ℝ
  α_lt : α < t₀
  lt_β : t₀ < β
  short : β - α < 1
  /-- … on which the curve is embedded -/
  embedded : Set.InjOn F.γ (Set.Icc α β)
  /-- "that contains no double point": no crossing occurrence is traversed on the arc -/
  no_double : ∀ v : D.Γ.Visit, ∀ n : ℤ, carried.τ v + n ∉ Set.Icc α β
  /-- "along which the tangent turns strictly positively": a tangent-angle lift on the arc … -/
  θ : ℝ → ℝ
  lift : IsLiftOn (fun t => normalize (deriv F.γ t)) θ α β
  /-- … strictly increasing -/
  turns_pos : StrictMonoOn θ (Set.Icc α β)
  /-- "isolated among such points": `p` is the only point of the arc with tangent `u` -/
  isolated : ∀ t ∈ Set.Icc α β, normalize (deriv F.γ t) = u → t = t₀

namespace CurlSite

variable (S : CurlSite)

/-- the point `p` -/
def p : Plane := S.F.γ S.t₀

/-- the unit tangent `T = F'/|F'|` -/
def T : ℝ → Plane := fun t => normalize (deriv S.F.γ t)

theorem T_eq_tangentLoop : S.T = S.F.toClosedC1Curve.tangentLoop.T := rfl

theorem u_unit : euclideanLength S.u = 1 := by
  rw [← S.tangent_at]; exact euclideanLength_normalize (S.F.regular _)

theorem one : S.D.Γ.c = 1 := S.carried.one

/-- "the tangent equals u" only at `p`: the printed isolation, on the arc -/
theorem T_eq_u_iff {t : ℝ} (ht : t ∈ Set.Icc S.α S.β) : S.T t = S.u ↔ t = S.t₀ :=
  ⟨S.isolated t ht, fun h => h ▸ S.tangent_at⟩

end CurlSite

/-! ## 3. The witness: the modified curve and diagram at a disc `Δ`, one field per printed sub-clause -/

/-- "Then F may be modified inside a disc Δ meeting the rest of the diagram only in that arc, so
that the resulting diagram F' [(i)–(iv)]" (sm-3:3878-3890), at the disc `Δ`.  The modification is
the parameter window `[s₁, s₂] ⊆ [α, β]` around `t₀`: outside it (mod 1) `F'` *is* `F`; the polygonal
diagram changes by one accepted Reidemeister-I move (the kink `kink`), and `F'` carries the record of
`D'`.  The kink is the new double point; the printed (ii)–(iv) are read on `F'`, `D'`. -/
structure CurlWitness (S : CurlSite) (Δ : Set Plane) where
  /-- "the resulting diagram F'": the modified curve … -/
  F' : SmoothRegularLoop
  /-- … its oriented diagram … -/
  D' : Diagram
  /-- … whose record `F'` carries ((i) "is again such an oriented diagram") -/
  carried' : RecordCarried F' D'
  /-- the modification window `[s₁, s₂]` around `t₀`, inside the arc -/
  s₁ : ℝ
  s₂ : ℝ
  s₁_lt : s₁ < S.t₀
  lt_s₂ : S.t₀ < s₂
  α_le : S.α ≤ s₁
  le_β : s₂ ≤ S.β
  /-- "F may be modified inside a disc Δ": `F'` coincides with `F` outside the window (mod 1) … -/
  unchanged : ∀ t : ℝ, (∀ n : ℤ, t + n ∉ Set.Ioo s₁ s₂) → F'.γ t = S.F.γ t
  /-- … with its velocity (the tangents of `F'` off the window are those of `F`; read by the
  consumer at the other tangency points, sm-3:4443-4445 "leave one another intact") … -/
  unchanged_deriv : ∀ t : ℝ, (∀ n : ℤ, t + n ∉ Set.Ioo s₁ s₂) → deriv F'.γ t = deriv S.F.γ t
  /-- … the modified arc lies in `Δ` … -/
  new_in_disc : ∀ t ∈ Set.Icc s₁ s₂, F'.γ t ∈ Δ
  /-- … and so does the replaced arc of `F` -/
  old_in_disc : ∀ t ∈ Set.Icc s₁ s₂, S.F.γ t ∈ Δ
  /-- "a disc Δ" (accepted clean-disc vocabulary) about `p` … -/
  disc : IsDisc Δ
  p_mem : S.p ∈ interior Δ
  /-- … "meeting the rest of the diagram only in that arc": every point of `F` in `Δ` is traversed
  on the arc -/
  disc_meets_arc : ∀ t : ℝ, S.F.γ t ∈ Δ → ∃ n : ℤ, t + n ∈ Set.Icc S.α S.β
  /-- (i) the polygonal diagram changes by one Reidemeister-I move (the accepted `RI`: a monogon
  created in a disc) -/
  ri : RI S.D D'
  /-- (i) "satisfies P_{F'}(a,z) = P_F(a,z)" -/
  poly_eq : P D' = P S.D
  /-- (i) "has the same double points outside Δ" -/
  doubles_outside :
    SmoothRegularLoop.doublePoints F'.γ \ Δ = SmoothRegularLoop.doublePoints S.F.γ \ Δ
  /-- (iii) the new double point: the kink crossing of `D'` -/
  kink : D'.Γ.Crossing
  /-- (i) the old crossings correspond to the crossings of `D'` other than the kink … -/
  old : S.D.Γ.Crossing ≃ {y : D'.Γ.Crossing // y ≠ kink}
  /-- … realised at the same points of the plane … -/
  old_point : ∀ x : S.D.Γ.Crossing,
    F'.γ (carried'.τ (D'.overVisit (old x).1)) = S.F.γ (S.carried.τ (S.D.overVisit x))
  /-- … "with the same signs" -/
  old_sign : ∀ x : S.D.Γ.Crossing, D'.sign (old x).1 = S.D.sign x
  /-- (ii) "has no point of Δ at which the tangent equals u" … -/
  no_u : ∀ t : ℝ, F'.γ t ∈ Δ → normalize (deriv F'.γ t) ≠ S.u
  /-- … "and exactly one at which it equals −u" -/
  one_neg_u : ∃! t : ℝ, t ∈ Set.Ico (0 : ℝ) 1 ∧ F'.γ t ∈ Δ ∧ normalize (deriv F'.γ t) = -S.u
  /-- (iii) "has exactly one double point inside Δ": the kink is realised in `Δ` … -/
  kink_mem : F'.γ (carried'.τ (D'.overVisit kink)) ∈ Δ
  /-- … and every double point of `F'` in `Δ` is that point -/
  one_double : ∀ q ∈ SmoothRegularLoop.doublePoints F'.γ ∩ Δ,
    q = F'.γ (carried'.τ (D'.overVisit kink))
  /-- (iii) "and it is negative" -/
  kink_neg : D'.sign kink = -1
  /-- (iv) "rot(F') = rot(F) − 1" (cf:def-turning on both sides) -/
  rot_eq : F'.toClosedC1Curve.rot = S.F.toClosedC1Curve.rot - 1
  /-- (iv) "w(F') = w(F) − 1" -/
  writhe_eq : D'.writhe = S.D.writhe - 1

namespace CurlWitness

variable {S : CurlSite} {Δ : Set Plane} (W : CurlWitness S Δ)

/-- the modified curve in the accepted `C¹` class -/
def curve : ClosedC1Curve := W.F'.toClosedC1Curve

/-- the unit tangent of `F'` -/
def T : ℝ → Plane := fun t => normalize (deriv W.F'.γ t)

theorem smooth : ContDiff ℝ ∞ W.F'.γ := W.F'.smooth
theorem periodic : Function.Periodic W.F'.γ 1 := W.F'.periodic
theorem regular : ∀ t, deriv W.F'.γ t ≠ 0 := W.F'.regular

/-- (i) one component -/
theorem one : W.D'.Γ.c = 1 := W.carried'.one

/-- (iii) the smooth sign of the new double point is negative -/
theorem kink_smoothSign : W.carried'.smoothSign W.kink = -1 := by
  rw [W.carried'.smoothSign_eq]; exact W.kink_neg

/-- (i) the smooth signs of the old double points are unchanged -/
theorem old_smoothSign (x : S.D.Γ.Crossing) :
    W.carried'.smoothSign (W.old x).1 = S.carried.smoothSign x := by
  rw [W.carried'.smoothSign_eq, S.carried.smoothSign_eq]; exact W.old_sign x

/-- (iv) the smooth writhe drops by one -/
theorem smoothWrithe_eq : W.carried'.smoothWrithe = S.carried.smoothWrithe - 1 := by
  rw [W.carried'.smoothWrithe_eq, S.carried.smoothWrithe_eq]; exact W.writhe_eq

end CurlWitness

/-! ## 4. The row bundle: one field per printed sentence / clause -/

/-- cf:lem-curl (sm-3:3870-3891), one field per printed sentence or clause; the objects are those of
`CurlSite` and `CurlWitness`.  The existence sentence (`exists_curl`) carries the theorem, in the
form the proof establishes and the consumer cf:thm-carrierfloor (C) reads (sm-3:4438-4442 "Choose
each curl disc inside its corresponding rounding disc"): the disc `Δ` may be taken inside any
preassigned neighbourhood `Δ₀` of `p`; the printed bare existence is `exists_curl'`.  The clause
fields state how each printed clause reads on a witness (projections of `CurlWitness`, so the fixed
content of (i)–(iv) is the field list of that structure). -/
structure CurlData : Prop where
  /-- "Then F may be modified inside a disc Δ meeting the rest of the diagram only in that arc, so
  that the resulting diagram F' [has (i)–(iv)]" — with the disc inside any preassigned neighbourhood
  `Δ₀` of `p` (the proof's "the disc is fixed first and the cuts afterwards", sm-3:4038-4041). -/
  exists_curl : ∀ (S : CurlSite) (Δ₀ : Set Plane), S.p ∈ interior Δ₀ →
    ∃ Δ : Set Plane, Δ ⊆ Δ₀ ∧ Nonempty (CurlWitness S Δ)
  /-- the printed existence sentence as printed (no preassigned neighbourhood) -/
  exists_curl' : ∀ S : CurlSite, ∃ Δ : Set Plane, Nonempty (CurlWitness S Δ)
  /-- "a disc Δ meeting the rest of the diagram only in that arc", the modification inside it -/
  disc : ∀ (S : CurlSite) (Δ : Set Plane) (W : CurlWitness S Δ),
    IsDisc Δ ∧ S.p ∈ interior Δ ∧ (∀ t : ℝ, S.F.γ t ∈ Δ → ∃ n : ℤ, t + n ∈ Set.Icc S.α S.β) ∧
    (∀ t : ℝ, (∀ n : ℤ, t + n ∉ Set.Ioo W.s₁ W.s₂) →
      W.F'.γ t = S.F.γ t ∧ deriv W.F'.γ t = deriv S.F.γ t) ∧
    (∀ t ∈ Set.Icc W.s₁ W.s₂, W.F'.γ t ∈ Δ)
  /-- (i) "is again such an oriented diagram, satisfies P_{F'}(a,z) = P_F(a,z), and has the same
  double points outside Δ, with the same signs" -/
  i : ∀ (S : CurlSite) (Δ : Set Plane) (W : CurlWitness S Δ),
    ContDiff ℝ ∞ W.F'.γ ∧ Function.Periodic W.F'.γ 1 ∧ (∀ t, deriv W.F'.γ t ≠ 0) ∧
    W.D'.Γ.c = 1 ∧ Nonempty (RecordCarried W.F' W.D') ∧ RI S.D W.D' ∧
    P W.D' = P S.D ∧
    SmoothRegularLoop.doublePoints W.F'.γ \ Δ = SmoothRegularLoop.doublePoints S.F.γ \ Δ ∧
    (∀ x : S.D.Γ.Crossing,
      W.F'.γ (W.carried'.τ (W.D'.overVisit (W.old x).1)) = S.F.γ (S.carried.τ (S.D.overVisit x)) ∧
      W.D'.sign (W.old x).1 = S.D.sign x)
  /-- (ii) "has no point of Δ at which the tangent equals u, and exactly one at which it equals −u" -/
  ii : ∀ (S : CurlSite) (Δ : Set Plane) (W : CurlWitness S Δ),
    (∀ t, W.F'.γ t ∈ Δ → normalize (deriv W.F'.γ t) ≠ S.u) ∧
    (∃! t : ℝ, t ∈ Set.Ico (0 : ℝ) 1 ∧ W.F'.γ t ∈ Δ ∧ normalize (deriv W.F'.γ t) = -S.u)
  /-- (iii) "has exactly one double point inside Δ, and it is negative" -/
  iii : ∀ (S : CurlSite) (Δ : Set Plane) (W : CurlWitness S Δ),
    W.F'.γ (W.carried'.τ (W.D'.overVisit W.kink)) ∈ Δ ∧
    (∀ q ∈ SmoothRegularLoop.doublePoints W.F'.γ ∩ Δ,
      q = W.F'.γ (W.carried'.τ (W.D'.overVisit W.kink))) ∧
    W.D'.sign W.kink = -1 ∧ W.carried'.smoothSign W.kink = -1
  /-- (iv) "satisfies rot(F') = rot(F) − 1 and w(F') = w(F) − 1" -/
  iv : ∀ (S : CurlSite) (Δ : Set Plane) (W : CurlWitness S Δ),
    W.F'.toClosedC1Curve.rot = S.F.toClosedC1Curve.rot - 1 ∧
    W.D'.writhe = S.D.writhe - 1 ∧ W.carried'.smoothWrithe = S.carried.smoothWrithe - 1

/-- The site of the consumer: the output of cf:lem-rounding (a `Carried` record, here the rounded
curve `L_ε` carrying `D`) is a curl site through `Carried.toRecordCarried`; the hypotheses are those
of `CurlSite` with `τ` the parameters of the `Carried` record. -/
def CurlSite.ofCarried (F : SmoothRegularLoop) (D : Diagram) (c : Carried F D) (u : Plane)
    (t₀ α β : ℝ) (θ : ℝ → ℝ) (tangent_at : normalize (deriv F.γ t₀) = u) (α_lt : α < t₀)
    (lt_β : t₀ < β) (short : β - α < 1) (embedded : Set.InjOn F.γ (Set.Icc α β))
    (no_double : ∀ v : D.Γ.Visit, ∀ n : ℤ, c.τ v + n ∉ Set.Icc α β)
    (lift : IsLiftOn (fun t => normalize (deriv F.γ t)) θ α β) (turns_pos : StrictMonoOn θ (Set.Icc α β))
    (isolated : ∀ t ∈ Set.Icc α β, normalize (deriv F.γ t) = u → t = t₀) : CurlSite :=
  ⟨F, D, c.toRecordCarried, u, t₀, tangent_at, α, β, α_lt, lt_β, short, embedded, no_double, θ, lift,
    turns_pos, isolated⟩


/-! ## 5. The construction (printed proof, sm-3:3892-4041): model, chart, affine fit -/

namespace Curl

/-- the positive quarter turn `J` (sm-3:3966) -/
def J (w : Plane) : Plane := (-w.2, w.1)

/-- the replacement model `c(t) = (t² − 1, t − t³)`, `−2 ≤ t ≤ 2` (sm-3:3893-3896) -/
def cModel (t : ℝ) : Plane := (t ^ 2 - 1, t - t ^ 3)

/-- the old-arc model `b(t) = (3(t²+7)/11, −3t)` (sm-3:3893-3896) -/
def bModel (t : ℝ) : Plane := (3 * (t ^ 2 + 7) / 11, -3 * t)

/-- the model frame `v₀ = (−1,0)`, `u₀ = (0,−1)`, positively oriented (sm-3:3978) -/
def u₀ : Plane := (0, -1)
def v₀ : Plane := (-1, 0)

/-- `q = 4/11` (sm-3:3979) -/
def qFit : ℝ := 4 / 11

/-- the printed `x = H/q = 2ac/(q(bc+ad))` of the affine fit (sm-3:3990-3996), for endpoint
tangents `T₋ = a v + b u`, `T₊ = −c v + d u` -/
def xFit (a b c d : ℝ) : ℝ := 2 * a * c / (qFit * (b * c + a * d))

/-- the printed `y = (bc − ad)/(q(bc+ad))` -/
def yFit (a b c d : ℝ) : ℝ := (b * c - a * d) / (qFit * (b * c + a * d))

/-- the linear map `A` with `A u₀ = u`, `A v₀ = x v + y u` (sm-3:3996-3997), on a model vector
`z = (−z.1) v₀ + (−z.2) u₀` -/
def fitA (u v : Plane) (x y : ℝ) (z : Plane) : Plane := (-z.1) • (x • v + y • u) + (-z.2) • u

/-- the inserted arc `Φ ∘ c`, `Φ(z) = p₋ + B(z − b(−2))`, `B = (ℓ/12) A` (sm-3:4033-4036) -/
def inserted (pm : Plane) (ℓ : ℝ) (u v : Plane) (x y : ℝ) (t : ℝ) : Plane :=
  pm + (ℓ / 12) • fitA u v x y (cModel t - bModel (-2))

variable (S : CurlSite)

/-- `v = −J u`, so that `(v, u)` is a positively oriented orthonormal basis (sm-3:3966-3967) -/
def vDir : Plane := -J S.u

/-- the transverse chart coordinate `ξ(s) = ⟨γ(s) − p, v⟩` (sm-3:3969) -/
def ξ (t : ℝ) : ℝ := planeDot (S.F.γ t - S.p) (vDir S)

/-- the longitudinal chart coordinate `η(s) = ⟨γ(s) − p, u⟩` (sm-3:3970) -/
def η (t : ℝ) : ℝ := planeDot (S.F.γ t - S.p) S.u

/-- the tangent angle relative to `u` (`θ(0) = 0` in the printed normalisation, sm-3:3964) -/
def θrel (t : ℝ) : ℝ := S.θ t - S.θ S.t₀

/-- the closed Euclidean disc of radius `r` about `p` -/
def disc (r : ℝ) : Set Plane := {z | euclideanLength (z - S.p) ≤ r}

/-- "meets the rest of the diagram only in that arc" at the parameter level -/
def MeetsOnlyArc (Δ : Set Plane) : Prop := ∀ t : ℝ, S.F.γ t ∈ Δ → ∃ n : ℤ, t + n ∈ Set.Icc S.α S.β

/-- a parameter is off the open window `(s₁, s₂)` modulo the period -/
def OffWindow (s₁ s₂ t : ℝ) : Prop := ∀ n : ℤ, t + n ∉ Set.Ioo s₁ s₂

/-- a parameter is off the closed window `[s₁, s₂]` modulo the period -/
def OffClosedWindow (s₁ s₂ t : ℝ) : Prop := ∀ n : ℤ, t + n ∉ Set.Icc s₁ s₂

end Curl

/-! ## 6. The three packages produced by the proof -/

namespace Curl

/-- The smooth curl inside the disc `Δ` (sm-3:3959-4212): the modified curve `F'`, its window
`[s₁, s₂]` (the cuts `p₋ = F(s₁)`, `p₊ = F(s₂)`), the model's own double point at the parameters
`q₁ < q₂` (later branch over the earlier one), the tangent facts and the lift increment. -/
structure SmoothCurl (S : CurlSite) (Δ : Set Plane) where
  F' : SmoothRegularLoop
  s₁ : ℝ
  s₂ : ℝ
  s₁_lt : s₁ < S.t₀
  lt_s₂ : S.t₀ < s₂
  α_le : S.α ≤ s₁
  le_β : s₂ ≤ S.β
  /-- "Replace the sub-arc of F between p₋ and p₊" (sm-3:4056): `F'` is `F` off the window -/
  unchanged : ∀ t : ℝ, OffWindow s₁ s₂ t → F'.γ t = S.F.γ t
  /-- "the whole inserted arc lies in a preassigned disc Δ" (sm-3:4039) -/
  new_in_disc : ∀ t ∈ Set.Icc s₁ s₂, F'.γ t ∈ Δ
  old_in_disc : ∀ t ∈ Set.Icc s₁ s₂, S.F.γ t ∈ Δ
  disc : IsDisc Δ
  p_mem : S.p ∈ interior Δ
  /-- "whose intersection with the diagram is contained in the embedded chart" (sm-3:4040) -/
  meets_arc : MeetsOnlyArc S Δ
  /-- the model's double point `c(−1) = c(1)` (sm-3:3915): earlier parameter `q₁`, later `q₂` -/
  q₁ : ℝ
  q₂ : ℝ
  q₁_mem : q₁ ∈ Set.Ioo s₁ s₂
  q₂_mem : q₂ ∈ Set.Ioo s₁ s₂
  q₁_lt : q₁ < q₂
  double : F'.γ q₁ = F'.γ q₂
  /-- "putting the later branch over the earlier one makes it negative" (sm-3:3917-3920) -/
  double_neg : det (deriv F'.γ q₂) (deriv F'.γ q₁) < 0
  /-- "Only the model's own double point is created" (sm-3:4043-4054): within the window … -/
  only_double : ∀ s ∈ Set.Icc s₁ s₂, ∀ t ∈ Set.Icc s₁ s₂, s ≠ t → F'.γ s = F'.γ t →
    (s = q₁ ∧ t = q₂) ∨ (s = q₂ ∧ t = q₁)
  /-- … and between the inserted arc and the rest of the curve -/
  arc_off_rest : ∀ s ∈ Set.Ioo s₁ s₂, ∀ t : ℝ, OffWindow s₁ s₂ t → F'.γ s ≠ S.F.γ t
  /-- (ii) on the inserted arc: no tangent `u` (sm-3:4213-4217) … -/
  new_no_u : ∀ t ∈ Set.Icc s₁ s₂, normalize (deriv F'.γ t) ≠ S.u
  /-- … and exactly one tangent `−u` -/
  new_one_neg_u : ∃! t : ℝ, t ∈ Set.Icc s₁ s₂ ∧ normalize (deriv F'.γ t) = -S.u
  /-- "the retained tails have neither, their angles lying in (−π/2, π/2) away from 0" (sm-3:4216) -/
  tails_no_neg_u : ∀ t : ℝ, S.F.γ t ∈ Δ → OffWindow s₁ s₂ t → S.T t ≠ -S.u
  /-- (iv) for rot: a lift of the new tangent on the window whose increment is the old one minus
  `2π` (sm-3:3908-3911, 4226-4244) -/
  θ' : ℝ → ℝ
  lift' : IsLiftOn (fun t => normalize (deriv F'.γ t)) θ' s₁ s₂
  increment : θ' s₂ - θ' s₁ = (S.θ s₂ - S.θ s₁) - 2 * Real.pi

/-- Where the polygonal kink goes: a traversal point `r` of `D` in the interior of its edge, off
every other edge (so off every crossing), at the cyclic position of `t₀` among the occurrences. -/
structure KinkLocation (S : CurlSite) where
  r : S.D.Γ.Pt
  interior : 0 < (r.2.2 : ℝ)
  off_edges : ∀ s : S.D.Γ.Strand, s ≠ ⟨r.1, r.2.1⟩ → S.D.Γ.eval r ∉ S.D.Γ.seg s
  /-- the cyclic position of `r` among the occurrences of `D` is that of `t₀` among their
  parameters on `F` -/
  gap : ∀ v w : S.D.Γ.Visit,
    cycBetween (S.D.visitCoord v) (traversalKey r.2) (S.D.visitCoord w) ↔
      cycBetween (S.carried.τ v) (Int.fract S.t₀) (S.carried.τ w)

/-- The polygonal kink: the accepted Reidemeister-I move `RIData U D D'` inserting a negative
monogon (later branch over) at the location `L`, with the correspondence of the old crossings and
occurrences and the cyclic-order clauses the record assembly needs. -/
structure KinkInsertion (S : CurlSite) (L : KinkLocation S) where
  D' : Diagram
  U : Set Plane
  ri : RIData U S.D D'
  kink_neg : D'.sign ri.kink = -1
  c_eq : D'.Γ.c = S.D.Γ.c
  old : S.D.Γ.Crossing ≃ {y : D'.Γ.Crossing // y ≠ ri.kink}
  oldVisit : S.D.Γ.Visit ≃ {v : D'.Γ.Visit // v.1 ≠ ri.kink}
  oldVisit_over : ∀ x, (oldVisit (S.D.overVisit x)).1 = D'.overVisit (old x).1
  oldVisit_under : ∀ x, (oldVisit (S.D.underVisit x)).1 = D'.underVisit (old x).1
  oldVisit_twin : ∀ v, (oldVisit (S.D.twin v)).1 = D'.twin (oldVisit v).1
  old_point : ∀ x, D'.Γ.crossingPoint (old x).1 = S.D.Γ.crossingPoint x
  old_sign : ∀ x, D'.sign (old x).1 = S.D.sign x
  order_old : ∀ v w z : S.D.Γ.Visit,
    cycBetween (D'.visitCoord (oldVisit v).1) (D'.visitCoord (oldVisit w).1)
        (D'.visitCoord (oldVisit z).1) ↔
      cycBetween (S.D.visitCoord v) (S.D.visitCoord w) (S.D.visitCoord z)
  order_gap : ∀ (v w : S.D.Γ.Visit) (k : D'.Γ.Visit), k.1 = ri.kink →
    (cycBetween (D'.visitCoord (oldVisit v).1) (D'.visitCoord k) (D'.visitCoord (oldVisit w).1) ↔
      cycBetween (S.D.visitCoord v) (traversalKey L.r.2) (S.D.visitCoord w))
  /-- the under occurrence of the kink is met first -/
  order_pair : ∀ v : S.D.Γ.Visit,
    cycBetween (D'.visitCoord (oldVisit v).1) (D'.visitCoord (D'.underVisit ri.kink))
      (D'.visitCoord (D'.overVisit ri.kink))
  writhe : D'.writhe = S.D.writhe - 1

/-- The record of `D'` carried by `F'`: the occurrence parameters are the old ones on the old
occurrences and the two parameters of the model's double point on the kink (under = earlier). -/
structure CarriedAssembly (S : CurlSite) {Δ : Set Plane} (sc : SmoothCurl S Δ) {L : KinkLocation S}
    (K : KinkInsertion S L) where
  rc : RecordCarried sc.F' K.D'
  τ_old : ∀ v : S.D.Γ.Visit, rc.τ (K.oldVisit v).1 = S.carried.τ v
  τ_under : rc.τ (K.D'.underVisit K.ri.kink) = Int.fract sc.q₁
  τ_over : rc.τ (K.D'.overVisit K.ri.kink) = Int.fract sc.q₂

end Curl

/-! ## 7. The chain of leaf lemmas (all `sorry`; unit split and estimates in PLAN_A.md §5) -/

namespace Curl

open Set

/-! ### Unit M — the rational model (sm-3:3893-3921, 4213-4223) -/

/-- "b(±2) = c(±2) = (3, ∓6)" -/
theorem cModel_two : cModel 2 = (3, -6) := by simp [cModel]; norm_num
theorem cModel_neg_two : cModel (-2) = (3, 6) := by simp [cModel]; norm_num
theorem bModel_two : bModel 2 = (3, -6) := by simp [bModel]; norm_num
theorem bModel_neg_two : bModel (-2) = (3, 6) := by simp [bModel]; norm_num

/-- `c'(t) = (2t, 1 − 3t²)` -/
theorem hasDerivAt_cModel (t : ℝ) : HasDerivAt cModel (2 * t, 1 - 3 * t ^ 2) t := by
  have h1 : HasDerivAt (fun t : ℝ => t ^ 2 - 1) (2 * t) t :=
    ((hasDerivAt_pow 2 t).sub_const 1).congr_deriv (by norm_num)
  have h2 : HasDerivAt (fun t : ℝ => t - t ^ 3) (1 - 3 * t ^ 2) t :=
    ((hasDerivAt_id' t).sub (hasDerivAt_pow 3 t)).congr_deriv (by norm_num)
  exact h1.prodMk h2

/-- `b'(t) = (6t/11, −3)` -/
theorem hasDerivAt_bModel (t : ℝ) : HasDerivAt bModel (6 * t / 11, -3) t := by
  have h1 : HasDerivAt (fun t : ℝ => 3 * (t ^ 2 + 7) / 11) (6 * t / 11) t :=
    ((((hasDerivAt_pow 2 t).add_const 7).const_mul 3).div_const 11).congr_deriv
      (by norm_num; ring)
  have h2 : HasDerivAt (fun t : ℝ => -3 * t) (-3) t :=
    ((hasDerivAt_id' t).const_mul (-3)).congr_deriv (by ring)
  exact h1.prodMk h2

/-- "b'(±2) = (3/11) c'(±2)": the endpoint tangent rays agree up to positive scale -/
theorem deriv_bModel_eq_smul : (6 * (2:ℝ) / 11, (-3:ℝ)) = (3 / 11 : ℝ) • (2 * (2:ℝ), 1 - 3 * (2:ℝ) ^ 2) ∧
    (6 * (-2:ℝ) / 11, (-3:ℝ)) = (3 / 11 : ℝ) • (2 * (-2:ℝ), 1 - 3 * (-2:ℝ) ^ 2) := by
  constructor <;> (ext <;> (simp; norm_num))

/-- "det(b', b'') = 18/11 > 0", "det(c', c'') = −2(1+3t²) < 0" (sm-3:3900-3907) -/
theorem cModel_turn_neg (t : ℝ) : det (2 * t, 1 - 3 * t ^ 2) (2, -6 * t) = -2 * (1 + 3 * t ^ 2) := by
  simp [det]; ring
theorem bModel_turn_pos (t : ℝ) : det (6 * t / 11, -3) (6 / 11, 0) = 18 / 11 := by
  simp [det]; ring

/-- "the first derivative has vanishing first component only at t = 0" (sm-3:3908) -/
theorem cModel_vertical_iff (t : ℝ) : (2 * t : ℝ) = 0 ↔ t = 0 := by
  constructor
  · intro h; linarith
  · intro h; rw [h]; ring

/-- `c'(0) = (0, 1) = −u₀` -/
theorem deriv_cModel_zero : ((2 * (0:ℝ), 1 - 3 * (0:ℝ) ^ 2) : Plane) = -u₀ := by
  simp [u₀]

/-- "if c(s) = c(t) then s = ±t, and … the only pair of distinct parameters is {−1, 1}" (sm-3:4219-4221) -/
theorem cModel_double {s t : ℝ} (h : cModel s = cModel t) : s = t ∨ (s = -1 ∧ t = 1) ∨ (s = 1 ∧ t = -1) := by
  have h1 : s ^ 2 - 1 = t ^ 2 - 1 := congrArg Prod.fst h
  have h2 : s - s ^ 3 = t - t ^ 3 := congrArg Prod.snd h
  have hsq : (s - t) * (s + t) = 0 := by nlinarith
  rcases mul_eq_zero.mp hsq with hst | hst
  · left; linarith
  · have hts : t = -s := by linarith
    subst hts
    have h3 : s * (1 - s) * (1 + s) = 0 := by nlinarith
    rcases mul_eq_zero.mp h3 with h4 | h4
    · rcases mul_eq_zero.mp h4 with h5 | h5
      · left; rw [h5]; ring
      · right; right; constructor <;> linarith
    · right; left; constructor <;> linarith

/-- "c(−1) = c(1) = (0,0)" -/
theorem cModel_one : cModel 1 = 0 ∧ cModel (-1) = 0 := by
  constructor <;> simp [cModel] <;> norm_num

/-- "det(c'(1), c'(−1)) = −8 < 0" (sm-3:3920): the later branch over the earlier one is negative -/
theorem det_cModel_one_neg_one : det (2 * (1:ℝ), 1 - 3 * (1:ℝ) ^ 2) (2 * (-1:ℝ), 1 - 3 * (-1:ℝ) ^ 2) = -8 := by
  simp [det]; norm_num

/-- "the model's transverse excess over its endpoint chord is 4 − t² > 0 for −2 < t < 2" (sm-3:4046) -/
theorem cModel_excess_pos {t : ℝ} (ht : t ∈ Ioo (-2 : ℝ) 2) : 0 < 4 - t ^ 2 := by
  obtain ⟨h1, h2⟩ := ht; nlinarith

/-! ### Unit F — the affine fit (sm-3:3977-4001) and the ordered-ray lemma (sm-3:3927-3949) -/

/-- `A u₀ = u` -/
theorem fitA_u₀ (u v : Plane) (x y : ℝ) : fitA u v x y u₀ = u := by
  simp [fitA, u₀]

/-- `A v₀ = x v + y u` -/
theorem fitA_v₀ (u v : Plane) (x y : ℝ) : fitA u v x y v₀ = x • v + y • u := by
  simp [fitA, v₀]

/-- `A` is linear -/
theorem fitA_add (u v : Plane) (x y : ℝ) (z w : Plane) :
    fitA u v x y (z + w) = fitA u v x y z + fitA u v x y w := by
  apply Prod.ext <;> simp [fitA] <;> ring
theorem fitA_smul (u v : Plane) (x y : ℝ) (r : ℝ) (z : Plane) :
    fitA u v x y (r • z) = r • fitA u v x y z := by
  apply Prod.ext <;> simp [fitA] <;> ring

/-- "det A = x > 0" (sm-3:4000-4001), for `(v, u)` positively oriented orthonormal -/
theorem det_fitA_pos (u v : Plane) (hvu : det v u = 1) {x y : ℝ} (hx : 0 < x) :
    0 < det (fitA u v x y v₀) (fitA u v x y u₀) := by
  rw [fitA_u₀, fitA_v₀]
  have : det (x • v + y • u) u = x * det v u := by
    simp only [det, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring
  rw [this, hvu]; linarith

/-- "A(q v₀ + u₀) = (H/a) T₋, A(−q v₀ + u₀) = (H/c) T₊" (sm-3:3998-3999), with `T₋ = a v + b u`,
`T₊ = −c v + d u`, `a, b, c, d > 0`, `H = 2ac/(bc+ad)` -/
theorem fitA_ray_minus (u v : Plane) {a b c d : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    fitA u v (xFit a b c d) (yFit a b c d) (qFit • v₀ + u₀) =
      (2 * a * c / (b * c + a * d) / a) • (a • v + b • u) := by
  have hden : b * c + a * d ≠ 0 := by positivity
  simp only [fitA, xFit, yFit, qFit, u₀, v₀]
  ext <;> simp <;> field_simp <;> ring
theorem fitA_ray_plus (u v : Plane) {a b c d : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    fitA u v (xFit a b c d) (yFit a b c d) (-(qFit • v₀) + u₀) =
      (2 * a * c / (b * c + a * d) / c) • (-(c • v) + d • u) := by
  have hden : b * c + a * d ≠ 0 := by positivity
  simp only [fitA, xFit, yFit, qFit, u₀, v₀]
  ext <;> simp <;> field_simp <;> ring

/-- "1 − (qy)² = 4abcd/(bc+ad)² > 0, so |y| < 1/q uniformly" (sm-3:4003-4006) -/
theorem yFit_bound {a b c d : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    |qFit * yFit a b c d| < 1 := by
  have hden : 0 < b * c + a * d := by positivity
  have hq : qFit ≠ 0 := by norm_num [qFit]
  have : qFit * yFit a b c d = (b * c - a * d) / (b * c + a * d) := by
    unfold yFit; field_simp
  rw [this, abs_div, abs_of_pos hden, div_lt_one hden]
  have hbc : 0 < b * c := by positivity
  have had : 0 < a * d := by positivity
  rw [abs_lt]; constructor <;> linarith

/-- `x > 0` -/
theorem xFit_pos {a b c d : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    0 < xFit a b c d := by
  unfold xFit qFit; positivity

/-- "The two outer determinants are det(q v₀ + u₀, −q v₀ + u₀) = 2q > 0 and det(T₋, T₊) = ad + bc > 0, so
the ordered-ray condition holds; it is computed, not inferred" (sm-3:3987-3990), for `(v, u)` positively
oriented orthonormal -/
theorem orderedRay_condition (u v : Plane) (hvu : det v u = 1) (a b c d : ℝ) :
    det (qFit • v₀ + u₀) (-(qFit • v₀) + u₀) = 2 * qFit ∧
      det (a • v + b • u) (-(c • v) + d • u) = a * d + b * c := by
  constructor
  · simp only [det, qFit, u₀, v₀, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
      Prod.fst_neg, Prod.snd_neg, smul_eq_mul]
    norm_num
  · have : det (a • v + b • u) (-(c • v) + d • u) = (a * d + b * c) * det v u := by
      simp only [det, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, Prod.fst_neg,
        Prod.snd_neg, smul_eq_mul]; ring
    rw [this, hvu, mul_one]

/-! ### Unit G — the positive-turn chart and the cuts (sm-3:3959-3976, 3981-3984) -/

variable (S : CurlSite)

/-- `u₁² + u₂² = 1` (`u` is a unit vector) -/
theorem g_u_sq : S.u.1 * S.u.1 + S.u.2 * S.u.2 = 1 := by
  have h := S.u_unit
  rw [euclideanLength_formula, Real.sqrt_eq_one] at h
  exact h

/-- `v = −J u = (u₂, −u₁)` -/
theorem g_vDir_eq : vDir S = (S.u.2, -S.u.1) := by
  simp [vDir, J]

/-- `(v, u)` is a positively oriented orthonormal basis -/
theorem det_vDir_u : det (vDir S) S.u = 1 := by
  have h := g_u_sq S
  rw [g_vDir_eq]; simp only [det]; linarith
theorem planeDot_vDir_u : planeDot (vDir S) S.u = 0 := by
  rw [g_vDir_eq]; simp only [planeDot]; ring

/-- the chart expansion `γ(s) − p = ξ(s) v + η(s) u` -/
theorem expansion (t : ℝ) : S.F.γ t = S.p + ξ S t • vDir S + η S t • S.u := by
  have h := g_u_sq S
  rw [g_vDir_eq]
  ext
  · simp only [ξ, η, planeDot, g_vDir_eq, Prod.fst_add, Prod.smul_fst, smul_eq_mul, Prod.fst_sub,
      Prod.snd_sub]
    linear_combination (S.p.1 - (S.F.γ t).1) * h
  · simp only [ξ, η, planeDot, g_vDir_eq, Prod.snd_add, Prod.smul_snd, smul_eq_mul, Prod.fst_sub,
      Prod.snd_sub]
    linear_combination (S.p.2 - (S.F.γ t).2) * h

/-- "after shrinking the chart … |θ(s)| < π/2": a sub-arc `[α', β']` around `t₀` on which the
relative angle stays in `(−π/2, π/2)` -/
theorem exists_chart : ∃ α' β' : ℝ, S.α ≤ α' ∧ α' < S.t₀ ∧ S.t₀ < β' ∧ β' ≤ S.β ∧
    ∀ t ∈ Icc α' β', |θrel S t| < Real.pi / 2 := by
  have hc : ContinuousWithinAt S.θ (Icc S.α S.β) S.t₀ := S.lift.1 S.t₀ ⟨S.α_lt.le, S.lt_β.le⟩
  rw [Metric.continuousWithinAt_iff] at hc
  obtain ⟨δ, hδ, hδ'⟩ := hc (Real.pi / 2) (by positivity)
  refine ⟨max S.α (S.t₀ - δ / 2), min S.β (S.t₀ + δ / 2), le_max_left _ _, ?_, ?_,
    min_le_left _ _, ?_⟩
  · exact max_lt S.α_lt (by linarith)
  · exact lt_min S.lt_β (by linarith)
  · intro t ht
    have h1 : t ∈ Icc S.α S.β := ⟨(le_max_left _ _).trans ht.1, ht.2.trans (min_le_left _ _)⟩
    have h2 : dist t S.t₀ < δ := by
      rw [Real.dist_eq, abs_lt]
      constructor <;> linarith [le_max_right S.α (S.t₀ - δ / 2), min_le_right S.β (S.t₀ + δ / 2),
        ht.1, ht.2]
    have := hδ' h1 h2
    rw [Real.dist_eq] at this
    exact this

/-- the derivative of a coordinate `⟨γ(s) − p, w⟩` is `⟨γ'(s), w⟩` -/
theorem g_hasDerivAt_planeDot (w : Plane) (t : ℝ) :
    HasDerivAt (fun s => planeDot (S.F.γ s - S.p) w) (planeDot (deriv S.F.γ t) w) t := by
  have hγ : HasDerivAt S.F.γ (deriv S.F.γ t) t := S.F.hasDerivAt t
  have h1 : HasDerivAt (fun s => (S.F.γ s).1) (deriv S.F.γ t).1 t :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt t hγ
  have h2 : HasDerivAt (fun s => (S.F.γ s).2) (deriv S.F.γ t).2 t :=
    (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt t hγ
  have := ((h1.sub_const S.p.1).mul_const w.1).add ((h2.sub_const S.p.2).mul_const w.2)
  simp only [planeDot, Prod.fst_sub, Prod.snd_sub]
  exact this

/-- `γ' = |γ'| T` -/
theorem g_deriv_eq_smul_T (t : ℝ) : deriv S.F.γ t = euclideanLength (deriv S.F.γ t) • S.T t := by
  simp only [CurlSite.T, normalize, smul_smul]
  rw [mul_inv_cancel₀ (euclideanLength_pos (S.F.regular t)).ne', one_smul]

theorem g_planeDot_smul_left (r : ℝ) (a b : Plane) : planeDot (r • a) b = r * planeDot a b := by
  simp only [planeDot, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring

/-- `u = (cos θ(t₀), sin θ(t₀))` -/
theorem g_u_eq : S.u = (Real.cos (S.θ S.t₀), Real.sin (S.θ S.t₀)) := by
  rw [← S.tangent_at]; exact S.lift.2 S.t₀ ⟨S.α_lt.le, S.lt_β.le⟩

/-- `T(t) = (cos θ(t), sin θ(t))` on the arc -/
theorem g_T_eq {t : ℝ} (ht : t ∈ Icc S.α S.β) : S.T t = (Real.cos (S.θ t), Real.sin (S.θ t)) :=
  S.lift.2 t ht

/-- `⟨T, u⟩ = cos θrel` -/
theorem g_planeDot_T_u {t : ℝ} (ht : t ∈ Icc S.α S.β) :
    planeDot (S.T t) S.u = Real.cos (θrel S t) := by
  rw [g_T_eq S ht, g_u_eq, θrel, Real.cos_sub]; simp [planeDot]

/-- `⟨T, v⟩ = −sin θrel` -/
theorem g_planeDot_T_v {t : ℝ} (ht : t ∈ Icc S.α S.β) :
    planeDot (S.T t) (vDir S) = -Real.sin (θrel S t) := by
  rw [g_T_eq S ht, g_vDir_eq, g_u_eq, θrel, Real.sin_sub]; simp [planeDot]; ring

/-- "ξ'(s) = −sin θ(s), η'(s) = cos θ(s)" up to the speed (the parameter is not arclength) -/
theorem hasDerivAt_η {t : ℝ} (ht : t ∈ Icc S.α S.β) :
    HasDerivAt (η S) (euclideanLength (deriv S.F.γ t) * Real.cos (θrel S t)) t := by
  have h := g_hasDerivAt_planeDot S S.u t
  rw [g_deriv_eq_smul_T, g_planeDot_smul_left, g_planeDot_T_u S ht] at h
  exact h
theorem hasDerivAt_ξ {t : ℝ} (ht : t ∈ Icc S.α S.β) :
    HasDerivAt (ξ S) (-(euclideanLength (deriv S.F.γ t) * Real.sin (θrel S t))) t := by
  have h := g_hasDerivAt_planeDot S (vDir S) t
  rw [g_deriv_eq_smul_T, g_planeDot_smul_left, g_planeDot_T_v S ht, mul_neg] at h
  exact h

/-- Lagrange's mean value theorem from Rolle (`exists_hasDerivAt_eq_zero`; Mathlib's
`exists_hasDerivAt_eq_slope` / `strictMonoOn_of_deriv_pos` are not in the import closure) -/
theorem g_exists_hasDerivAt_eq_slope {f f' : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hfc : ContinuousOn f (Icc a b)) (hff' : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x) :
    ∃ c ∈ Ioo a b, f' c * (b - a) = f b - f a := by
  set m := (f b - f a) / (b - a) with hm
  have hba : b - a ≠ 0 := (sub_pos.mpr hab).ne'
  have hg : ∀ x ∈ Ioo a b, HasDerivAt (fun x => f x - m * (x - a)) (f' x - m) x := fun x hx => by
    have h1 : HasDerivAt (fun x => m * (x - a)) (m * 1) x :=
      ((hasDerivAt_id x).sub_const a).const_mul m
    exact ((hff' x hx).sub h1).congr_deriv (by ring)
  have hgc : ContinuousOn (fun x => f x - m * (x - a)) (Icc a b) :=
    hfc.sub (continuousOn_const.mul (continuousOn_id.sub continuousOn_const))
  have hI : f a - m * (a - a) = f b - m * (b - a) := by
    rw [hm, sub_self, mul_zero, sub_zero, div_mul_cancel₀ _ hba]; ring
  obtain ⟨c, hc, hc'⟩ := exists_hasDerivAt_eq_zero hab hgc hI hg
  refine ⟨c, hc, ?_⟩
  have : f' c = m := by linarith
  rw [this, hm, div_mul_cancel₀ _ hba]

/-- strict monotonicity from a positive derivative on the open interval -/
theorem g_strictMonoOn_of_deriv_pos {f f' : ℝ → ℝ} {a b : ℝ} (hfc : ContinuousOn f (Icc a b))
    (hff' : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x) (hpos : ∀ x ∈ Ioo a b, 0 < f' x) :
    StrictMonoOn f (Icc a b) := by
  intro x hx y hy hxy
  obtain ⟨c, hc, hc'⟩ := g_exists_hasDerivAt_eq_slope hxy (hfc.mono (Icc_subset_Icc hx.1 hy.2))
    (fun z hz => hff' z ⟨hx.1.trans_lt hz.1, hz.2.trans_le hy.2⟩)
  have := hpos c ⟨hx.1.trans_lt hc.1, hc.2.trans_le hy.2⟩
  nlinarith

/-- strict antitonicity from a negative derivative on the open interval -/
theorem g_strictAntiOn_of_deriv_neg {f f' : ℝ → ℝ} {a b : ℝ} (hfc : ContinuousOn f (Icc a b))
    (hff' : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x) (hneg : ∀ x ∈ Ioo a b, f' x < 0) :
    StrictAntiOn f (Icc a b) := by
  intro x hx y hy hxy
  obtain ⟨c, hc, hc'⟩ := g_exists_hasDerivAt_eq_slope hxy (hfc.mono (Icc_subset_Icc hx.1 hy.2))
    (fun z hz => hff' z ⟨hx.1.trans_lt hz.1, hz.2.trans_le hy.2⟩)
  have := hneg c ⟨hx.1.trans_lt hc.1, hc.2.trans_le hy.2⟩
  nlinarith

theorem g_continuous_ξ : Continuous (ξ S) :=
  continuous_iff_continuousAt.mpr fun t => (g_hasDerivAt_planeDot S (vDir S) t).continuousAt
theorem g_continuous_η : Continuous (η S) :=
  continuous_iff_continuousAt.mpr fun t => (g_hasDerivAt_planeDot S S.u t).continuousAt

theorem g_θrel_t₀ : θrel S S.t₀ = 0 := sub_self _
theorem g_ξ_t₀ : ξ S S.t₀ = 0 := by
  show planeDot (S.F.γ S.t₀ - S.p) (vDir S) = 0
  rw [show S.F.γ S.t₀ - S.p = 0 from sub_self _]; simp [planeDot]
theorem g_η_t₀ : η S S.t₀ = 0 := by
  show planeDot (S.F.γ S.t₀ - S.p) S.u = 0
  rw [show S.F.γ S.t₀ - S.p = 0 from sub_self _]; simp [planeDot]

/-- the relative angle is negative before `t₀` and positive after it (the lift is strictly
increasing on the arc) -/
theorem g_θrel_neg {t : ℝ} (ht : t ∈ Icc S.α S.β) (h : t < S.t₀) : θrel S t < 0 :=
  sub_neg.mpr (S.turns_pos ht ⟨S.α_lt.le, S.lt_β.le⟩ h)
theorem g_θrel_pos {t : ℝ} (ht : t ∈ Icc S.α S.β) (h : S.t₀ < t) : 0 < θrel S t :=
  sub_pos.mpr (S.turns_pos ⟨S.α_lt.le, S.lt_β.le⟩ ht h)

/-- `ξ` increases strictly on `[α', t₀]` when `|θrel| < π/2` *on that interval* (the form the
construction uses; the leaf `ξ_strictMonoOn` below is this with `[α', t₀] ⊆ [α', β']`) -/
theorem g_ξ_strictMonoOn {α' : ℝ} (hα : S.α ≤ α')
    (hθ : ∀ t ∈ Icc α' S.t₀, |θrel S t| < Real.pi / 2) : StrictMonoOn (ξ S) (Icc α' S.t₀) := by
  refine g_strictMonoOn_of_deriv_pos (g_continuous_ξ S).continuousOn
    (fun x hx => hasDerivAt_ξ S ⟨hα.trans hx.1.le, hx.2.le.trans S.lt_β.le⟩) ?_
  intro x hx
  have hx' : x ∈ Icc S.α S.β := ⟨hα.trans hx.1.le, hx.2.le.trans S.lt_β.le⟩
  have h1 := g_θrel_neg S hx' hx.2
  have h2 := (abs_lt.mp (hθ x ⟨hx.1.le, hx.2.le⟩)).1
  have h3 : Real.sin (θrel S x) < 0 :=
    Real.sin_neg_of_neg_of_neg_pi_lt h1 (by linarith [Real.pi_pos])
  have h4 := euclideanLength_pos (S.F.regular x)
  rw [neg_pos]; exact mul_neg_of_pos_of_neg h4 h3

/-- `ξ` decreases strictly on `[t₀, β']` when `|θrel| < π/2` on that interval -/
theorem g_ξ_strictAntiOn {β' : ℝ} (hβ : β' ≤ S.β)
    (hθ : ∀ t ∈ Icc S.t₀ β', |θrel S t| < Real.pi / 2) : StrictAntiOn (ξ S) (Icc S.t₀ β') := by
  refine g_strictAntiOn_of_deriv_neg (g_continuous_ξ S).continuousOn
    (fun x hx => hasDerivAt_ξ S ⟨S.α_lt.le.trans hx.1.le, hx.2.le.trans hβ⟩) ?_
  intro x hx
  have hx' : x ∈ Icc S.α S.β := ⟨S.α_lt.le.trans hx.1.le, hx.2.le.trans hβ⟩
  have h1 := g_θrel_pos S hx' hx.1
  have h2 := (abs_lt.mp (hθ x ⟨hx.1.le, hx.2.le⟩)).2
  have h3 : 0 < Real.sin (θrel S x) := Real.sin_pos_of_pos_of_lt_pi h1 (by linarith [Real.pi_pos])
  have h4 := euclideanLength_pos (S.F.regular x)
  rw [neg_lt_zero]; exact mul_pos h4 h3

/-- "ξ increases strictly for s < 0 and decreases strictly for s > 0, with a strict maximum ξ(0) = 0,
while η increases throughout" (sm-3:3972-3974), on the chart -/
theorem ξ_strictMonoOn {α' β' : ℝ} (hα : S.α ≤ α') (hβ : β' ≤ S.β)
    (hθ : ∀ t ∈ Icc α' β', |θrel S t| < Real.pi / 2) : StrictMonoOn (ξ S) (Icc α' S.t₀) := by
  sorry
theorem ξ_strictAntiOn {α' β' : ℝ} (hα : S.α ≤ α') (hβ : β' ≤ S.β)
    (hθ : ∀ t ∈ Icc α' β', |θrel S t| < Real.pi / 2) : StrictAntiOn (ξ S) (Icc S.t₀ β') := by
  sorry
theorem η_strictMonoOn {α' β' : ℝ} (hα : S.α ≤ α') (hβ : β' ≤ S.β)
    (hθ : ∀ t ∈ Icc α' β', |θrel S t| < Real.pi / 2) : StrictMonoOn (η S) (Icc α' β') := by
  refine g_strictMonoOn_of_deriv_pos (g_continuous_η S).continuousOn
    (fun x hx => hasDerivAt_η S ⟨hα.trans hx.1.le, hx.2.le.trans hβ⟩) ?_
  intro x hx
  have h := abs_lt.mp (hθ x ⟨hx.1.le, hx.2.le⟩)
  exact mul_pos (euclideanLength_pos (S.F.regular x)) (Real.cos_pos_of_mem_Ioo ⟨h.1, h.2⟩)

/-- "For every level sufficiently close to ξ(0) from below, strict monotonicity and the intermediate
value theorem give unique cuts s₋ < 0 < s₊ with ξ(s₋) = ξ(s₊), and both tend to 0" (sm-3:3975-3977):
cuts within `δ` of `t₀` -/
theorem exists_cuts {α' β' : ℝ} (hα : S.α ≤ α') (hα' : α' < S.t₀) (hβ' : S.t₀ < β') (hβ : β' ≤ S.β)
    (hθ : ∀ t ∈ Icc α' β', |θrel S t| < Real.pi / 2) {δ : ℝ} (hδ : 0 < δ) :
    ∃ s₁ s₂ : ℝ, α' ≤ s₁ ∧ s₁ < S.t₀ ∧ S.t₀ < s₂ ∧ s₂ ≤ β' ∧ s₂ - s₁ < δ ∧ ξ S s₁ = ξ S s₂ := by
  have ha1 : α' ≤ max α' (S.t₀ - δ / 3) := le_max_left _ _
  have ha2 : S.t₀ - δ / 3 ≤ max α' (S.t₀ - δ / 3) := le_max_right _ _
  have ha3 : max α' (S.t₀ - δ / 3) < S.t₀ := max_lt hα' (by linarith)
  have hb1 : min β' (S.t₀ + δ / 3) ≤ β' := min_le_left _ _
  have hb2 : min β' (S.t₀ + δ / 3) ≤ S.t₀ + δ / 3 := min_le_right _ _
  have hb3 : S.t₀ < min β' (S.t₀ + δ / 3) := lt_min hβ' (by linarith)
  have hmono := g_ξ_strictMonoOn S hα (fun t ht => hθ t ⟨ht.1, ht.2.trans hβ'.le⟩)
  have hanti := g_ξ_strictAntiOn S hβ (fun t ht => hθ t ⟨hα'.le.trans ht.1, ht.2⟩)
  have hξa : ξ S (max α' (S.t₀ - δ / 3)) < ξ S S.t₀ := hmono ⟨ha1, ha3.le⟩ ⟨hα'.le, le_rfl⟩ ha3
  have hξb : ξ S (min β' (S.t₀ + δ / 3)) < ξ S S.t₀ := hanti ⟨le_rfl, hβ'.le⟩ ⟨hb3.le, hb1⟩ hb3
  have hm1 : max (ξ S (max α' (S.t₀ - δ / 3))) (ξ S (min β' (S.t₀ + δ / 3))) < ξ S S.t₀ :=
    max_lt hξa hξb
  obtain ⟨s₁, hs₁, hs₁'⟩ := intermediate_value_Icc ha3.le (g_continuous_ξ S).continuousOn
    ⟨le_max_left _ _, hm1.le⟩
  obtain ⟨s₂, hs₂, hs₂'⟩ := intermediate_value_Icc' hb3.le (g_continuous_ξ S).continuousOn
    ⟨le_max_right _ _, hm1.le⟩
  have hs₁t : s₁ < S.t₀ := lt_of_le_of_ne hs₁.2 (fun h => by rw [h] at hs₁'; linarith)
  have hs₂t : S.t₀ < s₂ := lt_of_le_of_ne hs₂.1 (fun h => by rw [← h] at hs₂'; linarith)
  refine ⟨s₁, s₂, ha1.trans hs₁.1, hs₁t, hs₂t, hs₂.2.trans hb1, ?_, hs₁'.trans hs₂'.symm⟩
  linarith [hs₁.1, hs₂.2]

/-- "p₊ − p₋ = ℓ u, ℓ > 0" (sm-3:3980-3981) -/
theorem cut_displacement {s₁ s₂ : ℝ} (h : ξ S s₁ = ξ S s₂) :
    S.F.γ s₂ - S.F.γ s₁ = (η S s₂ - η S s₁) • S.u := by
  rw [expansion S s₂, expansion S s₁, h, sub_smul]; abel

/-- the endpoint tangents in the frame: `T₋ = a v + b u` with `a = −sin θ(s₋) > 0`, `b = cos θ(s₋) > 0`;
`T₊ = −c v + d u` with `c = sin θ(s₊) > 0`, `d = cos θ(s₊) > 0` (sm-3:3984-3987) -/
theorem endpoint_tangent {t : ℝ} (ht : t ∈ Icc S.α S.β) :
    S.T t = (-Real.sin (θrel S t)) • vDir S + Real.cos (θrel S t) • S.u := by
  rw [g_T_eq S ht, g_vDir_eq, g_u_eq, θrel, Real.sin_sub, Real.cos_sub]
  ext
  · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
    linear_combination (-Real.cos (S.θ t)) * Real.sin_sq_add_cos_sq (S.θ S.t₀)
  · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
    linear_combination (-Real.sin (S.θ t)) * Real.sin_sq_add_cos_sq (S.θ S.t₀)

theorem g_γ_fract (x : ℝ) : S.F.γ (Int.fract x) = S.F.γ x := by
  have := S.F.eq_add_int (-⌊x⌋) x
  rw [Int.cast_neg, ← sub_eq_add_neg, Int.self_sub_floor] at this
  exact this

/-- no point of the complementary arc `[β', α' + 1]` is `p`: on `[β', β]` by `embedded`, beyond
`β` because a coincidence would be a double point of `F` at a parameter of the arc (`doubles`,
`no_double`) -/
theorem g_ne_p {α' β' : ℝ} (hα : S.α ≤ α') (hα' : α' < S.t₀) (hβ' : S.t₀ < β') (hβ : β' ≤ S.β)
    {t : ℝ} (ht : t ∈ Icc β' (α' + 1)) : S.F.γ t ≠ S.p := by
  intro heq
  by_cases htβ : t ≤ S.β
  · have h1 : t ∈ Icc S.α S.β := ⟨by linarith [ht.1], htβ⟩
    have := S.embedded h1 ⟨S.α_lt.le, S.lt_β.le⟩ heq
    linarith [ht.1]
  · have htβ' := not_le.mp htβ
    have hne : Int.fract S.t₀ ≠ Int.fract t := by
      intro h
      obtain ⟨z, hz⟩ := Int.fract_eq_fract.mp h
      have h1 : (z : ℝ) < 0 := by rw [← hz]; linarith
      have h2 : (-1 : ℝ) < z := by rw [← hz]; linarith [ht.2]
      have h3 : z < 0 := by exact_mod_cast h1
      have h4 : -1 < z := by exact_mod_cast h2
      omega
    have hγ : S.F.γ (Int.fract S.t₀) = S.F.γ (Int.fract t) := by
      rw [g_γ_fract, g_γ_fract, heq]; rfl
    obtain ⟨v, hv, -⟩ := S.carried.doubles _ _ ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩
      ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩ hne hγ
    apply S.no_double v ⌊S.t₀⌋
    rw [← hv, ← Int.self_sub_floor, sub_add_cancel]
    exact ⟨S.α_lt.le, S.lt_β.le⟩

/-- "the disc is fixed first": a closed Euclidean disc about `p` inside a preassigned neighbourhood
`Δ₀` whose intersection with the curve is contained in the chart arc (compactness of the rest of
the curve, which misses `p` since the arc is embedded and carries no double point) -/
theorem exists_disc_in_chart {α' β' : ℝ} (hα : S.α ≤ α') (hα' : α' < S.t₀) (hβ' : S.t₀ < β')
    (hβ : β' ≤ S.β) (Δ₀ : Set Plane) (h₀ : S.p ∈ interior Δ₀) :
    ∃ r : ℝ, 0 < r ∧ disc S r ⊆ Δ₀ ∧ ∀ t : ℝ, S.F.γ t ∈ disc S r → ∃ n : ℤ, t + n ∈ Icc α' β' := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp h₀)
  have hK : β' ≤ α' + 1 := by linarith [S.short]
  have hcont : Continuous fun t => eucDist (S.F.γ t) S.p :=
    (CornerRounding.E_continuous_eucDist S.p).comp S.F.continuous
  obtain ⟨t₁, ht₁, hmin⟩ := isCompact_Icc.exists_isMinOn ⟨β', le_rfl, hK⟩ hcont.continuousOn
  have hm : 0 < eucDist (S.F.γ t₁) S.p :=
    euclideanLength_pos (sub_ne_zero.mpr (g_ne_p S hα hα' hβ' hβ ht₁))
  refine ⟨min (eucDist (S.F.γ t₁) S.p / 2) (ε / 2), by positivity, ?_, ?_⟩
  · intro z hz
    apply hball
    rw [Metric.mem_ball]
    have h1 : eucDist z S.p ≤ min (eucDist (S.F.γ t₁) S.p / 2) (ε / 2) := hz
    have h2 := CornerRounding.E_dist_le_eucDist z S.p
    linarith [min_le_right (eucDist (S.F.γ t₁) S.p / 2) (ε / 2)]
  · intro t ht
    have h1 : eucDist (S.F.γ t) S.p ≤ min (eucDist (S.F.γ t₁) S.p / 2) (ε / 2) := ht
    have h2 := min_le_left (eucDist (S.F.γ t₁) S.p / 2) (ε / 2)
    have hlo : β' ≤ t + ((-⌊t - β'⌋ : ℤ) : ℝ) := by
      rw [Int.cast_neg]; linarith [Int.floor_le (t - β')]
    have hhi : t + ((-⌊t - β'⌋ : ℤ) : ℝ) < β' + 1 := by
      rw [Int.cast_neg]; linarith [Int.lt_floor_add_one (t - β')]
    have hγ : S.F.γ (t + ((-⌊t - β'⌋ : ℤ) : ℝ)) = S.F.γ t := S.F.eq_add_int _ t
    have hgt : α' + 1 < t + ((-⌊t - β'⌋ : ℤ) : ℝ) := by
      by_contra hle
      have := isMinOn_iff.mp hmin _ ⟨hlo, not_lt.mp hle⟩
      rw [hγ] at this
      linarith
    refine ⟨-⌊t - β'⌋ - 1, ?_⟩
    rw [Int.cast_sub, Int.cast_one]
    exact ⟨by linarith, by linarith⟩

/-- the disc is the `planeComplex`-preimage of a closed Euclidean ball -/
theorem g_disc_eq_preimage (r : ℝ) :
    disc S r = planeComplex ⁻¹' Metric.closedBall (planeComplex S.p) r := by
  ext z
  show euclideanLength (z - S.p) ≤ r ↔ _
  rw [Set.mem_preimage, Metric.mem_closedBall, ← CornerRounding.E_eucDist_eq]
  rfl

/-- the product ball of radius `r/2` lies in the Euclidean disc of radius `r` -/
theorem g_ball_subset_disc {r : ℝ} : Metric.ball S.p (r / 2) ⊆ disc S r := by
  intro z hz
  rw [Metric.mem_ball, Prod.dist_eq, Real.dist_eq, Real.dist_eq, max_lt_iff] at hz
  show eucDist z S.p ≤ r
  have := CornerRounding.E_eucDist_le_add z S.p
  linarith [hz.1, hz.2]

/-- the closed Euclidean disc is an accepted disc with `p` in its interior -/
theorem disc_isDisc {r : ℝ} (hr : 0 < r) : IsDisc (disc S r) := by
  refine ⟨?_, ?_, ⟨S.p, ?_⟩⟩
  · rw [g_disc_eq_preimage]
    exact (convex_closedBall _ _).is_linear_preimage
      ⟨CornerRounding.E_planeComplex_add, planeComplex_smul⟩
  · refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
    · show IsClosed {z | eucDist z S.p ≤ r}
      exact isClosed_le (CornerRounding.E_continuous_eucDist S.p) continuous_const
    · refine (Metric.isBounded_closedBall (x := S.p) (r := r)).subset ?_
      intro z hz
      rw [Metric.mem_closedBall]
      exact (CornerRounding.E_dist_le_eucDist z S.p).trans hz
  · rw [mem_interior_iff_mem_nhds]
    exact Filter.mem_of_superset (Metric.ball_mem_nhds _ (half_pos hr)) (g_ball_subset_disc S)
theorem p_mem_interior_disc {r : ℝ} (hr : 0 < r) : S.p ∈ interior (disc S r) := by
  rw [mem_interior_iff_mem_nhds]
  exact Filter.mem_of_superset (Metric.ball_mem_nhds _ (half_pos hr)) (g_ball_subset_disc S)

/-- the retained tails: on the chart arc away from `t₀` the tangent is neither `u` nor `−u`
(sm-3:4216-4217) -/
theorem tail_tangent_ne {t : ℝ} (ht : t ∈ Icc S.α S.β) (hθ : |θrel S t| < Real.pi / 2) (hne : t ≠ S.t₀) :
    S.T t ≠ S.u ∧ S.T t ≠ -S.u := by
  refine ⟨fun h => hne (S.isolated t ht h), fun h => ?_⟩
  have h1 : planeDot (S.T t) S.u = Real.cos (θrel S t) := g_planeDot_T_u S ht
  rw [h] at h1
  have h2 : planeDot (-S.u) S.u = -1 := by
    have := g_u_sq S; simp only [planeDot, Prod.fst_neg, Prod.snd_neg]; linarith
  have h3 : 0 < Real.cos (θrel S t) :=
    Real.cos_pos_of_mem_Ioo ⟨(abs_lt.mp hθ).1, (abs_lt.mp hθ).2⟩
  linarith

/-! ### Unit H — the collar, as a graph (sm-3:4080-4212): abstract real-function lemmas -/

/-- the blend `h = (1 − φ_lam) f + φ_lam g`, `φ_lam(η) = φ((η − e₁)/lam)` (sm-3:4098-4104) -/
def blend (f g : ℝ → ℝ) (e₁ lam : ℝ) (η : ℝ) : ℝ :=
  (1 - Real.smoothTransition ((η - e₁) / lam)) * f η + Real.smoothTransition ((η - e₁) / lam) * g η

/-- the rescaled profile `η ↦ φ((η − e₁)/lam)` is `C^∞` -/
theorem ht_contDiff_profile (e₁ lam : ℝ) :
    ContDiff ℝ ∞ (fun η : ℝ => Real.smoothTransition ((η - e₁) / lam)) :=
  Real.smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).div_const lam)

/-- "(1) It is C^∞": the blend of `C^∞` functions is `C^∞`, equals `f` on `(−∞, e₁]` and `g` on
`[e₁ + lam, ∞)` (the flat endpoint jets of `φ`, exact equality here) -/
theorem blend_smooth {f g : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) {e₁ lam : ℝ} (hlam : 0 < lam) :
    ContDiff ℝ ∞ (blend f g e₁ lam) := by
  unfold blend
  exact ((contDiff_const.sub (ht_contDiff_profile e₁ lam)).mul hf).add ((ht_contDiff_profile e₁ lam).mul hg)
theorem blend_eq_left {f g : ℝ → ℝ} {e₁ lam : ℝ} (hlam : 0 < lam) {η : ℝ} (h : η ≤ e₁) :
    blend f g e₁ lam η = f η := by
  unfold blend
  have h1 : (η - e₁) / lam ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hlam.le
  rw [Real.smoothTransition.zero_of_nonpos h1]
  ring
theorem blend_eq_right {f g : ℝ → ℝ} {e₁ lam : ℝ} (hlam : 0 < lam) {η : ℝ} (h : e₁ + lam ≤ η) :
    blend f g e₁ lam η = g η := by
  unfold blend
  have h1 : 1 ≤ (η - e₁) / lam := by rw [le_div_iff₀ hlam]; linarith
  rw [Real.smoothTransition.one_of_one_le h1]
  ring

/-- the mean value theorem in slope form, from Rolle (`exists_hasDerivAt_eq_zero`; Mathlib's
`exists_deriv_eq_slope` is not in the import closure) -/
theorem ht_exists_deriv_eq_slope {d : ℝ → ℝ} (hd : Differentiable ℝ d) {a b : ℝ} (hab : a < b) :
    ∃ c ∈ Ioo a b, deriv d c * (b - a) = d b - d a := by
  have hba : b - a ≠ 0 := (sub_pos.mpr hab).ne'
  set m := (d b - d a) / (b - a) with hm
  have hk : ∀ x, HasDerivAt (fun x => d x - m * (x - a)) (deriv d x - m) x := fun x =>
    ((hd x).hasDerivAt.sub (((hasDerivAt_id' x).sub_const a).const_mul m)).congr_deriv (by ring)
  have hI : d a - m * (a - a) = d b - m * (b - a) := by
    rw [hm, div_mul_cancel₀ _ hba]; ring
  obtain ⟨c, hc, hc0⟩ := exists_hasDerivAt_eq_zero hab
    (hd.continuous.sub (continuous_const.mul (continuous_id.sub continuous_const))).continuousOn hI
    (fun x _ => hk x)
  refine ⟨c, hc, ?_⟩
  have : deriv d c = m := by linarith
  rw [this, hm, div_mul_cancel₀ _ hba]

/-- "g > f on (e₁, e₁+lam]" from `f(e₁) = g(e₁)` and `g' > f'` there (sm-3:4093-4095) -/
theorem sep_of_deriv {f g : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) {e₁ lam : ℝ} (hlam : 0 < lam)
    (h0 : f e₁ = g e₁) (hd : ∀ η ∈ Ioc e₁ (e₁ + lam), deriv f η < deriv g η) :
    ∀ η ∈ Ioc e₁ (e₁ + lam), f η < g η := by
  intro η hη
  have hfd : Differentiable ℝ f := hf.differentiable (by decide)
  have hgd : Differentiable ℝ g := hg.differentiable (by decide)
  obtain ⟨c, hc, hslope⟩ := ht_exists_deriv_eq_slope (hgd.sub hfd) hη.1
  rw [deriv_sub (hgd c) (hfd c)] at hslope
  have hc' : 0 < deriv g c - deriv f c := by linarith [hd c ⟨hc.1, hc.2.le.trans hη.2⟩]
  have := mul_pos hc' (sub_pos.mpr hη.1)
  simp only [Pi.sub_apply] at hslope
  linarith

/-- the derivative of the blend: `h' = (1−φ_lam) f' + φ_lam g' + (φ'((η−e₁)/lam)/lam)(g − f)` -/
theorem ht_hasDerivAt_blend {f g : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (e₁ lam η : ℝ) :
    HasDerivAt (blend f g e₁ lam)
      ((1 - Real.smoothTransition ((η - e₁) / lam)) * deriv f η
        + Real.smoothTransition ((η - e₁) / lam) * deriv g η
        + deriv Real.smoothTransition ((η - e₁) / lam) / lam * (g η - f η)) η := by
  have hfd : HasDerivAt f (deriv f η) η := (hf.differentiable (by decide) η).hasDerivAt
  have hgd : HasDerivAt g (deriv g η) η := (hg.differentiable (by decide) η).hasDerivAt
  have ha : HasDerivAt (fun η : ℝ => (η - e₁) / lam) (1 / lam) η :=
    ((hasDerivAt_id' η).sub_const e₁).div_const lam
  have hφ : HasDerivAt Real.smoothTransition
      (deriv Real.smoothTransition ((η - e₁) / lam)) ((η - e₁) / lam) :=
    ((Real.smoothTransition.contDiff (n := 1)).differentiable (by decide) _).hasDerivAt
  have hφa : HasDerivAt (fun η : ℝ => Real.smoothTransition ((η - e₁) / lam))
      (deriv Real.smoothTransition ((η - e₁) / lam) * (1 / lam)) η := by
    have := hφ.comp η ha
    exact this
  have h := (((hasDerivAt_const η (1 : ℝ)).sub hφa).mul hfd).add (hφa.mul hgd)
  refine h.congr_deriv ?_
  try simp only [Pi.sub_apply]
  ring

/-- "(2) No tangent of the collar equals u, and no smallness condition is needed": pointwise
`h' ≥ (1−φ_lam) f' + φ_lam g' ≥ f' > 0` (sm-3:4117-4133) -/
theorem deriv_blend_ge {f g : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) {e₁ lam : ℝ} (hlam : 0 < lam)
    (h0 : f e₁ = g e₁) (hpos : ∀ η ∈ Icc e₁ (e₁ + lam), 0 < deriv f η)
    (hd : ∀ η ∈ Ioc e₁ (e₁ + lam), deriv f η < deriv g η) :
    ∀ η ∈ Icc e₁ (e₁ + lam), deriv f η ≤ deriv (blend f g e₁ lam) η := by
  intro η hη
  rw [(ht_hasDerivAt_blend hf hg e₁ lam η).deriv]
  have hφ0 : 0 ≤ Real.smoothTransition ((η - e₁) / lam) := Real.smoothTransition.nonneg _
  have hφ' : 0 ≤ deriv Real.smoothTransition ((η - e₁) / lam) :=
    Real.smoothTransition.monotone.deriv_nonneg
  have hgf : f η ≤ g η := by
    rcases eq_or_lt_of_le hη.1 with h | h
    · rw [← h, h0]
    · exact (sep_of_deriv hf hg hlam h0 hd η ⟨h, hη.2⟩).le
  have hterm : 0 ≤ Real.smoothTransition ((η - e₁) / lam) * (deriv g η - deriv f η) := by
    rcases eq_or_lt_of_le hη.1 with h | h
    · rw [← h, sub_self, zero_div, Real.smoothTransition.zero, zero_mul]
    · exact mul_nonneg hφ0 (by linarith [hd η ⟨h, hη.2⟩])
  have hterm2 : 0 ≤ deriv Real.smoothTransition ((η - e₁) / lam) / lam * (g η - f η) :=
    mul_nonneg (div_nonneg hφ' hlam.le) (by linarith)
  nlinarith

/-- "(3) … Pointwise f ≤ h ≤ g on the collar" (sm-3:4143-4144) -/
theorem blend_between {f g : ℝ → ℝ} {e₁ lam : ℝ} (hlam : 0 < lam) {η : ℝ} (hη : η ∈ Icc e₁ (e₁ + lam))
    (hfg : f η ≤ g η) : f η ≤ blend f g e₁ lam η ∧ blend f g e₁ lam η ≤ g η := by
  unfold blend
  have hφ0 := Real.smoothTransition.nonneg ((η - e₁) / lam)
  have hφ1 := Real.smoothTransition.le_one ((η - e₁) / lam)
  constructor <;> nlinarith

/-- the mirrored separation: `g > f` on `[e₂ − lam, e₂)` from `f(e₂) = g(e₂)` and `g' < f'` there -/
theorem ht_sep_of_deriv_left {f g : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) {e₂ lam : ℝ}
    (h0 : f e₂ = g e₂) (hd : ∀ η ∈ Ico (e₂ - lam) e₂, deriv g η < deriv f η) :
    ∀ η ∈ Ico (e₂ - lam) e₂, f η < g η := by
  intro η hη
  have hfd : Differentiable ℝ f := hf.differentiable (by decide)
  have hgd : Differentiable ℝ g := hg.differentiable (by decide)
  obtain ⟨c, hc, hslope⟩ := ht_exists_deriv_eq_slope (hgd.sub hfd) hη.2
  rw [deriv_sub (hgd c) (hfd c)] at hslope
  have hc' : deriv g c - deriv f c < 0 := by linarith [hd c ⟨hη.1.trans hc.1.le, hc.2⟩]
  have := mul_neg_of_neg_of_pos hc' (sub_pos.mpr hη.2)
  simp only [Pi.sub_apply] at hslope
  linarith

/-- the collar at `p₊`, "with its own signs printed" (sm-3:4166-4212): the mirrored blend
`h = (1 − χ) g + χ f` with `g' < m₊ < f' < 0` gives `h' ≤ f' < 0` -/
theorem deriv_blend_le {f g : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) {e₂ lam : ℝ} (hlam : 0 < lam)
    (h0 : f e₂ = g e₂) (hneg : ∀ η ∈ Icc (e₂ - lam) e₂, deriv f η < 0)
    (hd : ∀ η ∈ Ico (e₂ - lam) e₂, deriv g η < deriv f η) :
    ∀ η ∈ Icc (e₂ - lam) e₂, deriv (blend g f (e₂ - lam) lam) η ≤ deriv f η := by
  intro η hη
  rw [(ht_hasDerivAt_blend hg hf (e₂ - lam) lam η).deriv]
  have hφ1 : Real.smoothTransition ((η - (e₂ - lam)) / lam) ≤ 1 := Real.smoothTransition.le_one _
  have hφ' : 0 ≤ deriv Real.smoothTransition ((η - (e₂ - lam)) / lam) :=
    Real.smoothTransition.monotone.deriv_nonneg
  have hgf : f η ≤ g η := by
    rcases eq_or_lt_of_le hη.2 with h | h
    · rw [h, h0]
    · exact (ht_sep_of_deriv_left hf hg h0 hd η ⟨hη.1, h⟩).le
  have hterm : (1 - Real.smoothTransition ((η - (e₂ - lam)) / lam)) * (deriv g η - deriv f η) ≤ 0 := by
    rcases eq_or_lt_of_le hη.2 with h | h
    · have h1 : (η - (e₂ - lam)) / lam = 1 := by rw [h, sub_sub_cancel, div_self hlam.ne']
      rw [h1, Real.smoothTransition.one, sub_self, zero_mul]
    · exact mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith [hd η ⟨hη.1, h⟩])
  have hterm2 : deriv Real.smoothTransition ((η - (e₂ - lam)) / lam) / lam * (f η - g η) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (div_nonneg hφ' hlam.le) (by linarith)
  nlinarith

/-! ### Unit R — the replacement and its smooth regular parametrisation (sm-3:4033-4079, 4213-4244) -/


/-! #### Unit R helpers: `fitA` as a linear map, the derivative of `Φ ∘ c`, plane-vector bounds -/

theorem r_fitA_zero (u v : Plane) (x y : ℝ) : fitA u v x y 0 = 0 := by simp [fitA]

theorem r_det_fitA (u v : Plane) (x y : ℝ) (z w : Plane) :
    det (fitA u v x y z) (fitA u v x y w) = x * det v u * det z w := by
  simp only [fitA, det, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

theorem r_planeDot_fitA (u v : Plane) (x y : ℝ) (z w : Plane) :
    planeDot (fitA u v x y z) w =
      -(z.1 * (x * planeDot v w + y * planeDot u w)) - z.2 * planeDot u w := by
  simp only [fitA, planeDot, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

theorem r_planeDot_add_left (a b w : Plane) : planeDot (a + b) w = planeDot a w + planeDot b w := by
  simp only [planeDot, Prod.fst_add, Prod.snd_add]; ring
theorem r_planeDot_comm (a w : Plane) : planeDot a w = planeDot w a := by
  simp only [planeDot]; ring

/-- `fitA` is injective when `x ≠ 0` and `(v, u)` is a basis -/
theorem r_fitA_injective (u v : Plane) {x : ℝ} (hx : x ≠ 0) (hvu : det v u ≠ 0) (y : ℝ)
    {z w : Plane} (h : fitA u v x y z = fitA u v x y w) : z = w := by
  have h1 := congrArg (fun q => det q (fitA u v x y (0, 1))) h
  have h2 := congrArg (fun q => det q (fitA u v x y (1, 0))) h
  simp only [r_det_fitA] at h1 h2
  have hxv : x * det v u ≠ 0 := mul_ne_zero hx hvu
  have e1 : det z (0, 1) = det w (0, 1) := mul_left_cancel₀ hxv h1
  have e2 : det z (1, 0) = det w (1, 0) := mul_left_cancel₀ hxv h2
  simp only [det, mul_one, mul_zero, zero_sub, sub_zero, neg_inj] at e1 e2
  exact Prod.ext e1 e2

/-- the derivative of the inserted arc `Φ ∘ c`: `(ℓ/12) A c'(t)` -/
theorem r_hasDerivAt_inserted (pm : Plane) (ℓ : ℝ) (u v : Plane) (x y : ℝ) (t : ℝ) :
    HasDerivAt (inserted pm ℓ u v x y) ((ℓ / 12) • fitA u v x y (2 * t, 1 - 3 * t ^ 2)) t := by
  have hc : HasDerivAt (fun t => cModel t - bModel (-2)) (2 * t, 1 - 3 * t ^ 2) t :=
    (hasDerivAt_cModel t).sub_const _
  have h1 : HasDerivAt (fun t => (cModel t - bModel (-2)).1) (2 * t) t :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt t hc
  have h2 : HasDerivAt (fun t => (cModel t - bModel (-2)).2) (1 - 3 * t ^ 2) t :=
    (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt t hc
  have hA : HasDerivAt (fun t => fitA u v x y (cModel t - bModel (-2)))
      (fitA u v x y (2 * t, 1 - 3 * t ^ 2)) t := by
    have := ((h1.neg.smul_const (x • v + y • u)).add (h2.neg.smul_const u))
    exact this
  exact (hA.const_smul (ℓ / 12)).const_add pm

theorem r_euclideanLength_add_le (a b : Plane) :
    euclideanLength (a + b) ≤ euclideanLength a + euclideanLength b := by
  simp only [euclideanLength, CornerRounding.E_planeComplex_add]; exact norm_add_le _ _

theorem r_euclideanLength_vDir : euclideanLength (vDir S) = 1 := by
  have h := S.u_unit
  rw [euclideanLength_formula] at h ⊢
  simp only [vDir, J, Prod.fst_neg, Prod.snd_neg, neg_neg]
  rw [← h]; congr 1; ring

theorem r_planeDot_vDir_vDir : planeDot (vDir S) (vDir S) = 1 := by
  have h := S.u_unit
  rw [euclideanLength_formula, Real.sqrt_eq_one] at h
  simp only [vDir, J, planeDot, Prod.fst_neg, Prod.snd_neg, neg_neg]
  linarith

theorem r_planeDot_u_u : planeDot S.u S.u = 1 := by
  have h := S.u_unit
  rw [euclideanLength_formula, Real.sqrt_eq_one] at h
  simpa [planeDot] using h

/-- `0 ≤ 6 + t³ − t ≤ 12` on `[−2, 2]` -/
theorem r_cubic_bounds {t : ℝ} (ht : t ∈ Icc (-2 : ℝ) 2) : 0 ≤ 6 + t ^ 3 - t ∧ 6 + t ^ 3 - t ≤ 12 := by
  obtain ⟨h1, h2⟩ := ht
  constructor
  · have : 6 + t ^ 3 - t = (t + 2) * ((t - 1) ^ 2 + 2) := by ring
    rw [this]; exact mul_nonneg (by linarith) (by positivity)
  · have : 12 - (6 + t ^ 3 - t) = (2 - t) * ((t + 1) ^ 2 + 2) := by ring
    nlinarith [this, mul_nonneg (sub_nonneg.mpr h2) (by positivity : (0:ℝ) ≤ (t + 1) ^ 2 + 2)]

/-- The inserted arc `Φ ∘ c` (sm-3:4033-4054): endpoints `p₋`, `p₊`, endpoint tangents positive
multiples of the old ones, diameter of order `ℓ`, interior strictly on the side `ξ > ξ(s₁)`, exactly
one double point (at `t = ±1`), negative with the later branch over.  (Judge's repair, PLAN_FINAL.md
§3: the hypothesis `hℓ` — `ℓ = η(s₂) − η(s₁) > 0`, printed sm-3:3981, which the cuts of the chart supply
— is needed for the positive endpoint scalars and the excess; the diameter bound is
`ℓ · (x + 2)`, since `|Φc(t) − p₋| ≤ (ℓ/12)((4 − t²)x + |(4 − t²)y + 6 + t³ − t|) ≤ ℓ(4x + 23)/12` with
`|qy| < 1`, `0 ≤ 6 + t³ − t ≤ 12`; `x` is not uniformly bounded in `a, b, c, d`, only `x → 0` at the
cuts of the construction.) -/
theorem inserted_arc_props {s₁ s₂ : ℝ} (hs : s₁ < s₂) (hcut : ξ S s₁ = ξ S s₂) (hℓ : η S s₁ < η S s₂)
    {a b c d : ℝ} (hT₁ : S.T s₁ = a • vDir S + b • S.u) (hT₂ : S.T s₂ = -(c • vDir S) + d • S.u)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    let ℓ := η S s₂ - η S s₁
    let Φc := inserted (S.F.γ s₁) ℓ S.u (vDir S) (xFit a b c d) (yFit a b c d)
    Φc (-2) = S.F.γ s₁ ∧ Φc 2 = S.F.γ s₂ ∧
    (∃ r : ℝ, 0 < r ∧ deriv Φc (-2) = r • S.T s₁) ∧ (∃ r : ℝ, 0 < r ∧ deriv Φc 2 = r • S.T s₂) ∧
    (∀ t ∈ Ioo (-2 : ℝ) 2, ξ S s₁ < planeDot (Φc t - S.p) (vDir S)) ∧
    Φc (-1) = Φc 1 ∧ det (deriv Φc 1) (deriv Φc (-1)) < 0 ∧
    (∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2, s ≠ t → Φc s = Φc t →
      (s = -1 ∧ t = 1) ∨ (s = 1 ∧ t = -1)) ∧
    (∀ t ∈ Icc (-2 : ℝ) 2, euclideanLength (Φc t - S.F.γ s₁) ≤ ℓ * (xFit a b c d + 2)) := by
  intro ℓ Φc
  have hℓpos : 0 < ℓ := sub_pos.mpr hℓ
  have hvv : planeDot (vDir S) (vDir S) = 1 := r_planeDot_vDir_vDir S
  have huv : planeDot S.u (vDir S) = 0 := by rw [r_planeDot_comm]; exact planeDot_vDir_u S
  have hdet : det (vDir S) S.u = 1 := det_vDir_u S
  have hx : 0 < xFit a b c d := xFit_pos ha hb hc hd
  set x := xFit a b c d with hxdef
  set y := yFit a b c d with hydef
  have hΦ : ∀ t, Φc t = S.F.γ s₁ + (ℓ / 12) • fitA S.u (vDir S) x y (cModel t - bModel (-2)) :=
    fun t => rfl
  have hdΦ : ∀ t, deriv Φc t = (ℓ / 12) • fitA S.u (vDir S) x y (2 * t, 1 - 3 * t ^ 2) :=
    fun t => (r_hasDerivAt_inserted _ _ _ _ _ _ t).deriv
  have hz : ∀ t, cModel t - bModel (-2) = (t ^ 2 - 4, t - t ^ 3 - 6) := fun t => by
    rw [bModel_neg_two]
    refine Prod.ext ?_ ?_ <;> simp only [cModel, Prod.fst_sub, Prod.snd_sub] <;> ring
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hΦ, cModel_neg_two, bModel_neg_two, sub_self, r_fitA_zero, smul_zero, add_zero]
  · rw [hΦ, cModel_two, bModel_neg_two]
    have e : fitA S.u (vDir S) x y ((3, -6) - (3, 6)) = (12 : ℝ) • S.u := by
      refine Prod.ext ?_ ?_ <;> simp only [fitA, Prod.fst_sub, Prod.snd_sub, Prod.fst_add,
        Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;> ring
    rw [e, smul_smul, div_mul_cancel₀ _ (by norm_num : (12:ℝ) ≠ 0)]
    have := cut_displacement S hcut
    have h2 : S.F.γ s₂ = S.F.γ s₁ + ℓ • S.u := by
      rw [add_comm]; exact sub_eq_iff_eq_add.mp this
    exact h2.symm
  · have e1 : ((2 * (-2:ℝ), 1 - 3 * (-2:ℝ) ^ 2) : Plane) = (11:ℝ) • (qFit • v₀ + u₀) := by
      ext <;> simp [qFit, v₀, u₀] <;> norm_num
    refine ⟨ℓ / 12 * 11 * (2 * a * c / (b * c + a * d) / a), by positivity, ?_⟩
    rw [hdΦ, e1, fitA_smul, hxdef, hydef, fitA_ray_minus S.u (vDir S) ha hb hc hd, ← hT₁,
      smul_smul, smul_smul]
  · have e1 : ((2 * (2:ℝ), 1 - 3 * (2:ℝ) ^ 2) : Plane) = (11:ℝ) • (-(qFit • v₀) + u₀) := by
      ext <;> simp [qFit, v₀, u₀] <;> norm_num
    refine ⟨ℓ / 12 * 11 * (2 * a * c / (b * c + a * d) / c), by positivity, ?_⟩
    rw [hdΦ, e1, fitA_smul, hxdef, hydef, fitA_ray_plus S.u (vDir S) ha hb hc hd, ← hT₂,
      smul_smul, smul_smul]
  · intro t ht
    have e : Φc t - S.p = (S.F.γ s₁ - S.p) + (ℓ / 12) • fitA S.u (vDir S) x y (cModel t - bModel (-2)) := by
      rw [hΦ]; abel
    rw [e, r_planeDot_add_left, g_planeDot_smul_left, r_planeDot_fitA, hvv, huv, hz]
    show ξ S s₁ < ξ S s₁ + ℓ / 12 * (-((t ^ 2 - 4) * (x * 1 + y * 0)) - (t - t ^ 3 - 6) * 0)
    have := cModel_excess_pos ht
    have : 0 < ℓ / 12 * (-((t ^ 2 - 4) * (x * 1 + y * 0)) - (t - t ^ 3 - 6) * 0) := by
      rw [mul_one, mul_zero, add_zero, mul_zero, sub_zero, ← neg_mul, neg_sub]; positivity
    linarith
  · rw [hΦ, hΦ, cModel_one.1, cModel_one.2]
  · rw [hdΦ, hdΦ, CornerRounding.X_det_smul_smul, r_det_fitA, hdet, det_cModel_one_neg_one]
    have : 0 < ℓ / 12 * (ℓ / 12) := by positivity
    nlinarith
  · intro s hs t ht hst hΦst
    rw [hΦ, hΦ, add_right_inj] at hΦst
    have h1 := smul_right_injective Plane (by positivity : ℓ / 12 ≠ 0) hΦst
    have h2 := r_fitA_injective S.u (vDir S) hx.ne' (by rw [hdet]; exact one_ne_zero) y h1
    have h3 : cModel s = cModel t := sub_left_injective h2
    rcases cModel_double h3 with h | h | h
    · exact absurd h hst
    · exact Or.inl h
    · exact Or.inr h
  · intro t ht
    have e : Φc t - S.F.γ s₁ = (ℓ / 12) • fitA S.u (vDir S) x y (cModel t - bModel (-2)) := by
      rw [hΦ]; abel
    rw [e, hz, euclideanLength_smul, abs_of_pos (by positivity : (0:ℝ) < ℓ / 12)]
    -- `A z = α v + β u` with `α = (4 − t²) x`, `β = (4 − t²) y + 6 + t³ − t`
    have eA : fitA S.u (vDir S) x y (t ^ 2 - 4, t - t ^ 3 - 6) =
        ((4 - t ^ 2) * x) • vDir S + ((4 - t ^ 2) * y + (6 + t ^ 3 - t)) • S.u := by
      refine Prod.ext ?_ ?_ <;> simp only [fitA, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
        Prod.smul_snd, smul_eq_mul] <;> ring
    rw [eA]
    have hyb : |y| < 11 / 4 := by
      have h := yFit_bound ha hb hc hd
      rw [← hydef, abs_mul, abs_of_pos (by norm_num [qFit] : (0:ℝ) < qFit)] at h
      simp only [qFit] at h; linarith
    obtain ⟨hc0, hc12⟩ := r_cubic_bounds ht
    have ht4 : 0 ≤ 4 - t ^ 2 := by nlinarith [ht.1, ht.2]
    have ht4' : 4 - t ^ 2 ≤ 4 := by nlinarith [sq_nonneg t]
    have hlen : euclideanLength (((4 - t ^ 2) * x) • vDir S +
        ((4 - t ^ 2) * y + (6 + t ^ 3 - t)) • S.u) ≤ 4 * x + 23 := by
      refine (r_euclideanLength_add_le _ _).trans ?_
      rw [euclideanLength_smul, euclideanLength_smul, r_euclideanLength_vDir, S.u_unit, mul_one,
        mul_one, abs_of_nonneg (mul_nonneg ht4 hx.le)]
      have hb1 : |(4 - t ^ 2) * y + (6 + t ^ 3 - t)| ≤ 11 + 12 := by
        refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
        · rw [abs_mul, abs_of_nonneg ht4]; nlinarith [abs_nonneg y]
        · rw [abs_of_nonneg hc0]; exact hc12
      nlinarith
    calc ℓ / 12 * euclideanLength _ ≤ ℓ / 12 * (4 * x + 23) :=
          mul_le_mul_of_nonneg_left hlen (by positivity)
      _ ≤ ℓ * (x + 2) := by nlinarith

/-- The cuts and the affine fit at the disc `disc S r` (sm-3:3975-4041, "the disc is fixed first and
the cuts afterwards"): cuts `s₁ < t₀ < s₂` in the chart `[α', β']` with `ξ(s₁) = ξ(s₂)`, `ℓ = η(s₂) − η(s₁) > 0`,
the endpoint tangents `T₋ = a v + b u`, `T₊ = −c v + d u` with positive coefficients (sm-3:3984-3987), the
removed arc and the whole inserted arc `Φ ∘ c` inside the disc (sm-3:4038-4041).  (B's `Cuts` +
`InsertedArc.in_disc`, merged so that the smallness of the cuts and the containment of the inserted arc
are chosen together — for arbitrary cuts the containment is false.) -/
structure CutFit (S : CurlSite) (α' β' r : ℝ) where
  s₁ : ℝ
  s₂ : ℝ
  α'_le : α' ≤ s₁
  s₁_lt : s₁ < S.t₀
  lt_s₂ : S.t₀ < s₂
  le_β' : s₂ ≤ β'
  /-- "unique cuts s₋ < 0 < s₊ with ξ(s₋) = ξ(s₊)" -/
  ξ_eq : ξ S s₁ = ξ S s₂
  /-- "p₊ − p₋ = ℓ u, ℓ > 0" -/
  ℓ_pos : η S s₁ < η S s₂
  /-- the endpoint tangent coefficients, all positive -/
  a : ℝ
  b : ℝ
  c : ℝ
  d : ℝ
  a_pos : 0 < a
  b_pos : 0 < b
  c_pos : 0 < c
  d_pos : 0 < d
  T_minus : S.T s₁ = a • vDir S + b • S.u
  T_plus : S.T s₂ = -(c • vDir S) + d • S.u
  /-- the removed arc lies in the disc -/
  old_in_disc : ∀ t ∈ Icc s₁ s₂, S.F.γ t ∈ disc S r
  /-- "the cuts may be chosen so that the whole inserted arc lies in a preassigned disc Δ about p" -/
  ins_in_disc : ∀ t ∈ Icc (-2 : ℝ) 2,
    inserted (S.F.γ s₁) (η S s₂ - η S s₁) S.u (vDir S) (xFit a b c d) (yFit a b c d) t ∈ disc S r

/-- `|z₁| ≤ 4` and `|z₂| ≤ 12` for `z = c(t) − b(−2) = (t² − 4, t − t³ − 6)`, `−2 ≤ t ≤ 2`
(`t³ − t + 6 = (t + 2)((t − 1)² + 2) ≥ 0`, `6 + t − t³ = (2 − t)((t + 1)² + 2) ≥ 0`) -/
theorem g_model_diff_bounds {t : ℝ} (ht : t ∈ Icc (-2 : ℝ) 2) :
    |(cModel t - bModel (-2)).1| ≤ 4 ∧ |(cModel t - bModel (-2)).2| ≤ 12 := by
  rw [bModel_neg_two]
  simp only [cModel, Prod.fst_sub, Prod.snd_sub]
  obtain ⟨h1, h2⟩ := ht
  have e1 : 0 ≤ (t + 2) * ((t - 1) ^ 2 + 2) := mul_nonneg (by linarith) (by positivity)
  have e2 : 0 ≤ (2 - t) * ((t + 1) ^ 2 + 2) := mul_nonneg (by linarith) (by positivity)
  constructor
  · rw [abs_le]; constructor <;> nlinarith
  · rw [abs_le]; constructor <;> nlinarith

/-- triangle inequality for the Euclidean length -/
theorem g_euclideanLength_add_le (a b : Plane) :
    euclideanLength (a + b) ≤ euclideanLength a + euclideanLength b := by
  simp only [euclideanLength, CornerRounding.E_planeComplex_add]; exact norm_add_le _ _

theorem g_vDir_unit : euclideanLength (vDir S) = 1 := by
  rw [g_vDir_eq, euclideanLength_formula, Real.sqrt_eq_one]
  have := g_u_sq S
  show S.u.2 * S.u.2 + -S.u.1 * -S.u.1 = 1
  nlinarith

/-- the fitted model vector is bounded by `4(x + |y|) + 12` for `|z₁| ≤ 4`, `|z₂| ≤ 12`
(`A z = (−z₁)(x v + y u) + (−z₂) u`, `(v, u)` orthonormal) -/
theorem g_fitA_bound {x y : ℝ} (hx : 0 ≤ x) {z : Plane} (h1 : |z.1| ≤ 4) (h2 : |z.2| ≤ 12) :
    euclideanLength (fitA S.u (vDir S) x y z) ≤ 4 * (x + |y|) + 12 := by
  have hu := S.u_unit
  have hv := g_vDir_unit S
  have hin : euclideanLength (x • vDir S + y • S.u) ≤ |x| + |y| := by
    calc euclideanLength (x • vDir S + y • S.u)
        ≤ euclideanLength (x • vDir S) + euclideanLength (y • S.u) := g_euclideanLength_add_le _ _
      _ = |x| + |y| := by rw [euclideanLength_smul, euclideanLength_smul, hu, hv, mul_one, mul_one]
  have hout : euclideanLength (fitA S.u (vDir S) x y z) ≤ |z.1| * (|x| + |y|) + |z.2| := by
    calc euclideanLength (fitA S.u (vDir S) x y z)
        = euclideanLength ((-z.1) • (x • vDir S + y • S.u) + (-z.2) • S.u) := rfl
      _ ≤ euclideanLength ((-z.1) • (x • vDir S + y • S.u)) + euclideanLength ((-z.2) • S.u) :=
          g_euclideanLength_add_le _ _
      _ = |z.1| * euclideanLength (x • vDir S + y • S.u) + |z.2| := by
          rw [euclideanLength_smul, euclideanLength_smul, abs_neg, abs_neg, hu, mul_one]
      _ ≤ |z.1| * (|x| + |y|) + |z.2| := by gcongr
  rw [abs_of_nonneg hx] at hout
  have h3 := mul_le_mul_of_nonneg_right h1 (add_nonneg hx (abs_nonneg y))
  linarith

/-- `x = 2ac/(q(bc + ad)) ≤ 11` when `a ≤ 1` and `b > 1/2` (`q = 4/11`; `bc + ad > bc`) -/
theorem g_xFit_le {a b c d : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (hb : 1 / 2 < b) (hc : 0 < c)
    (hd : 0 < d) : xFit a b c d ≤ 11 := by
  unfold xFit qFit
  have hden : 0 < 4 / 11 * (b * c + a * d) := by positivity
  rw [div_le_iff₀ hden]
  nlinarith [mul_pos hc (by linarith : 0 < 2 * b - a), mul_pos ha hd]

/-- `|y| < 11/4`, from `|q y| < 1` (`yFit_bound`) -/
theorem g_yFit_abs_lt {a b c d : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    |yFit a b c d| < 11 / 4 := by
  have h := yFit_bound ha hb hc hd
  rw [abs_mul, abs_of_pos (by norm_num [qFit] : (0:ℝ) < qFit)] at h
  unfold qFit at h
  linarith

/-- the cuts and the fit exist at every disc about `p` (Unit G: `exists_cuts` with the cuts close to
`t₀`, `endpoint_tangent` for `a, b, c, d`, `η_strictMonoOn` for `ℓ > 0`, continuity of `F` for the removed
arc, and the diameter bound of `inserted_arc_props` with `x → 0`, `ℓ → 0` for the inserted arc) -/
theorem exists_cutFit {α' β' : ℝ} (hα : S.α ≤ α') (hα' : α' < S.t₀) (hβ' : S.t₀ < β') (hβ : β' ≤ S.β)
    (hθ : ∀ t ∈ Icc α' β', |θrel S t| < Real.pi / 2) {r : ℝ} (hr : 0 < r) :
    Nonempty (CutFit S α' β' r) := by
  -- (1) continuity data at `t₀`: the curve (within `r/2` of `p`), `η` (within `r/24` of `0`) and
  -- the angle (within `π/3` of `θ(t₀)`)
  have hc1 : ContinuousAt (fun t => eucDist (S.F.γ t) S.p) S.t₀ :=
    ((CornerRounding.E_continuous_eucDist S.p).comp S.F.continuous).continuousAt
  rw [Metric.continuousAt_iff] at hc1
  obtain ⟨δ₁, hδ₁, hδ₁'⟩ := hc1 (r / 2) (by positivity)
  have hc2 : ContinuousAt (η S) S.t₀ := (g_continuous_η S).continuousAt
  rw [Metric.continuousAt_iff] at hc2
  obtain ⟨δ₂, hδ₂, hδ₂'⟩ := hc2 (r / 24) (by positivity)
  have hc3 : ContinuousWithinAt S.θ (Icc S.α S.β) S.t₀ := S.lift.1 S.t₀ ⟨S.α_lt.le, S.lt_β.le⟩
  rw [Metric.continuousWithinAt_iff] at hc3
  obtain ⟨δ₃, hδ₃, hδ₃'⟩ := hc3 (Real.pi / 3) (by positivity)
  have h0 : eucDist (S.F.γ S.t₀) S.p = 0 := by
    show euclideanLength (S.F.γ S.t₀ - S.p) = 0
    rw [show S.F.γ S.t₀ - S.p = 0 from sub_self _, euclideanLength, planeComplex_zero, norm_zero]
  -- (2) the cuts, within `min δ₁ δ₂ δ₃` of `t₀`
  obtain ⟨s₁, s₂, hs₁, hs₁t, hts₂, hs₂, hδ, hξ⟩ :=
    exists_cuts S hα hα' hβ' hβ hθ (lt_min hδ₁ (lt_min hδ₂ hδ₃))
  have hwin : ∀ t ∈ Icc s₁ s₂, dist t S.t₀ < min δ₁ (min δ₂ δ₃) := fun t ht => by
    rw [Real.dist_eq, abs_lt]; constructor <;> linarith [ht.1, ht.2]
  have hs₁αβ : s₁ ∈ Icc S.α S.β := ⟨hα.trans hs₁, by linarith⟩
  have hs₂αβ : s₂ ∈ Icc S.α S.β := ⟨by linarith, hs₂.trans hβ⟩
  have hs₁w : s₁ ∈ Icc s₁ s₂ := ⟨le_rfl, by linarith⟩
  have hs₂w : s₂ ∈ Icc s₁ s₂ := ⟨by linarith, le_rfl⟩
  have hnear : ∀ t ∈ Icc s₁ s₂, eucDist (S.F.γ t) S.p < r / 2 := fun t ht => by
    have := hδ₁' ((hwin t ht).trans_le (min_le_left _ _))
    rw [Real.dist_eq, h0, sub_zero] at this
    exact (abs_lt.mp this).2
  have hη : ∀ t ∈ Icc s₁ s₂, |η S t| < r / 24 := fun t ht => by
    have := hδ₂' ((hwin t ht).trans_le ((min_le_right _ _).trans (min_le_left _ _)))
    rwa [Real.dist_eq, g_η_t₀, sub_zero] at this
  have hθ3 : ∀ t ∈ Icc s₁ s₂, |θrel S t| < Real.pi / 3 := fun t ht => by
    have := hδ₃' ⟨hα.trans (hs₁.trans ht.1), ht.2.trans (hs₂.trans hβ)⟩
      ((hwin t ht).trans_le ((min_le_right _ _).trans (min_le_right _ _)))
    rwa [Real.dist_eq] at this
  -- (3) the endpoint tangent coefficients `a = −sin θ(s₁)`, `b = cos θ(s₁)`, `c = sin θ(s₂)`,
  -- `d = cos θ(s₂)`, all positive, with `b, d > 1/2`
  have hθ₁ := hθ3 s₁ hs₁w
  have hθ₂ := hθ3 s₂ hs₂w
  have hθ₁n : θrel S s₁ < 0 := g_θrel_neg S hs₁αβ hs₁t
  have hθ₂p : 0 < θrel S s₂ := g_θrel_pos S hs₂αβ hts₂
  have ha : 0 < -Real.sin (θrel S s₁) := by
    rw [neg_pos]
    exact Real.sin_neg_of_neg_of_neg_pi_lt hθ₁n (by linarith [(abs_lt.mp hθ₁).1, Real.pi_pos])
  have hb : 1 / 2 < Real.cos (θrel S s₁) := by
    rw [← Real.cos_pi_div_three, ← Real.cos_abs (θrel S s₁)]
    exact Real.cos_lt_cos_of_nonneg_of_le_pi_div_two (abs_nonneg _) (by linarith [Real.pi_pos]) hθ₁
  have hc : 0 < Real.sin (θrel S s₂) :=
    Real.sin_pos_of_pos_of_lt_pi hθ₂p (by linarith [(abs_lt.mp hθ₂).2, Real.pi_pos])
  have hd : 1 / 2 < Real.cos (θrel S s₂) := by
    rw [← Real.cos_pi_div_three, ← Real.cos_abs (θrel S s₂)]
    exact Real.cos_lt_cos_of_nonneg_of_le_pi_div_two (abs_nonneg _) (by linarith [Real.pi_pos]) hθ₂
  have hℓ : η S s₁ < η S s₂ :=
    η_strictMonoOn S hα hβ hθ ⟨hs₁, by linarith⟩ ⟨by linarith, hs₂⟩ (by linarith)
  -- fields in order: s₁ s₂ α'_le s₁_lt lt_s₂ le_β' ξ_eq ℓ_pos a b c d a_pos b_pos c_pos d_pos
  -- T_minus T_plus old_in_disc ins_in_disc
  refine ⟨⟨s₁, s₂, hs₁, hs₁t, hts₂, hs₂, hξ, hℓ, -Real.sin (θrel S s₁), Real.cos (θrel S s₁),
    Real.sin (θrel S s₂), Real.cos (θrel S s₂), ha, by linarith, hc, by linarith,
    endpoint_tangent S hs₁αβ, ?_, ?_, ?_⟩⟩
  · -- `T₊ = −(c v) + d u`
    rw [endpoint_tangent S hs₂αβ, neg_smul]
  · -- the removed arc lies in the disc
    intro t ht
    show eucDist (S.F.γ t) S.p ≤ r
    linarith [hnear t ht]
  · -- the inserted arc lies in the disc: `|Φc(t) − p| ≤ |p₋ − p| + (ℓ/12)(4(x + |y|) + 12)` with
    -- `|p₋ − p| < r/2`, `x ≤ 11`, `|y| < 11/4`, `ℓ < r/12`, so `< r/2 + 67 r/144 < r`
    intro t ht
    simp only [disc, Set.mem_ofPred_eq, inserted]
    set x := xFit (-Real.sin (θrel S s₁)) (Real.cos (θrel S s₁)) (Real.sin (θrel S s₂))
      (Real.cos (θrel S s₂)) with hxdef
    set y := yFit (-Real.sin (θrel S s₁)) (Real.cos (θrel S s₁)) (Real.sin (θrel S s₂))
      (Real.cos (θrel S s₂)) with hydef
    set ℓ := η S s₂ - η S s₁ with hℓdef
    set w := fitA S.u (vDir S) x y (cModel t - bModel (-2)) with hwdef
    obtain ⟨hz1, hz2⟩ := g_model_diff_bounds ht
    have hxpos : 0 < x := xFit_pos ha (by linarith) hc (by linarith)
    have hx11 : x ≤ 11 :=
      g_xFit_le ha (by linarith [Real.neg_one_le_sin (θrel S s₁)]) hb hc (by linarith)
    have hy : |y| < 11 / 4 := g_yFit_abs_lt ha (by linarith) hc (by linarith)
    have hℓ12 : ℓ < r / 12 := by
      have h1 := abs_lt.mp (hη s₁ hs₁w); have h2 := abs_lt.mp (hη s₂ hs₂w); linarith
    have hℓpos : 0 < ℓ := sub_pos.mpr hℓ
    have hF : euclideanLength w ≤ 4 * (x + |y|) + 12 := g_fitA_bound S hxpos.le hz1 hz2
    have hnear₁ : euclideanLength (S.F.γ s₁ - S.p) < r / 2 := hnear s₁ hs₁w
    have e : S.F.γ s₁ + (ℓ / 12) • w - S.p = (S.F.γ s₁ - S.p) + (ℓ / 12) • w := by abel
    rw [e]
    refine (g_euclideanLength_add_le _ _).trans ?_
    rw [euclideanLength_smul, abs_of_pos (by linarith : (0:ℝ) < ℓ / 12)]
    have hprod : ℓ / 12 * euclideanLength w ≤ ℓ / 12 * 67 :=
      mul_le_mul_of_nonneg_left (hF.trans (by linarith)) (by linarith)
    linarith


/-! #### Unit R helpers: profile bounds, the flat-difference bound, the collar blend, the reparametrisation -/

/-- the derivative of the transition profile is bounded on `ℝ` (continuous, zero off `[0,1]`) -/
theorem r_smoothTransition_deriv_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, |deriv Real.smoothTransition x| ≤ C := by
  have hc : Continuous (deriv Real.smoothTransition) :=
    Real.smoothTransition.contDiff.continuous_deriv (by exact_mod_cast le_top)
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0:ℝ)) (b := 1)).exists_bound_of_continuousOn
    hc.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun x => ?_⟩
  by_cases hx : x ∈ Icc (0:ℝ) 1
  · exact (hC x hx).trans (le_max_left _ _)
  · have h0 : deriv Real.smoothTransition x = 0 := by
      rcases not_and_or.mp hx with h | h
      · push Not at h
        have : Real.smoothTransition =ᶠ[nhds x] fun _ => 0 :=
          Filter.eventually_of_mem (Iio_mem_nhds h)
            fun y hy => Real.smoothTransition.zero_of_nonpos (le_of_lt hy)
        rw [this.deriv_eq]; exact deriv_const _ _
      · push Not at h
        have : Real.smoothTransition =ᶠ[nhds x] fun _ => 1 :=
          Filter.eventually_of_mem (Ioi_mem_nhds h)
            fun y hy => Real.smoothTransition.one_of_one_le (le_of_lt hy)
        rw [this.deriv_eq]; exact deriv_const _ _
    rw [h0, abs_zero]; exact le_max_right _ _

/-- `φ'(0) = 0 = φ'(1)` (flat endpoint jets) -/
theorem r_deriv_smoothTransition_zero : deriv Real.smoothTransition 0 = 0 := by
  have := CornerRounding.iteratedDeriv_eq_zero_of_const_left Real.smoothTransition.contDiff
    (fun t ht => Real.smoothTransition.zero_of_nonpos ht) (x := 0) (m := 1) le_rfl
  simpa [iteratedDeriv_one] using this
theorem r_deriv_smoothTransition_one : deriv Real.smoothTransition 1 = 0 := by
  have := CornerRounding.iteratedDeriv_eq_zero_of_const_right Real.smoothTransition.contDiff
    (fun t ht => Real.smoothTransition.one_of_one_le ht) (x := 1) (m := 1) le_rfl
  simpa [iteratedDeriv_one] using this

/-- a smooth `D` with `D c = 0`, `D' c = 0` is `O(|t − c|²)` and its derivative `O(|t − c|)` near
`c`: the flat-difference bound of the collar (two mean value inequalities) -/
theorem r_flat_bound {D : ℝ → Plane} (hD : ContDiff ℝ ∞ D) {c : ℝ} (h0 : D c = 0)
    (h1 : deriv D c = 0) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t ∈ Icc (c - 1) (c + 1),
      ‖deriv D t‖ ≤ K * |t - c| ∧ ‖D t‖ ≤ K * |t - c| ^ 2 := by
  have hD1 : ContDiff ℝ ∞ (deriv D) := (contDiff_infty_iff_deriv.mp hD).2
  have hD2 : Continuous (deriv (deriv D)) := hD1.continuous_deriv (by exact_mod_cast le_top)
  obtain ⟨K, hK⟩ := (isCompact_Icc (a := c - 1) (b := c + 1)).exists_bound_of_continuousOn
    hD2.continuousOn
  have hcmem : c ∈ Icc (c - 1) (c + 1) := Set.mem_Icc.mpr ⟨by linarith, by linarith⟩
  have hK0 : 0 ≤ K := le_trans (norm_nonneg _) (hK c hcmem)
  refine ⟨K, hK0, fun t ht => ?_⟩
  have hdiff1 : ∀ x ∈ Icc (c - 1) (c + 1), DifferentiableAt ℝ (deriv D) x := fun x _ =>
    (hD1.differentiable (by decide)) x
  have hA : ∀ s ∈ Icc (c - 1) (c + 1), ‖deriv D s‖ ≤ K * |s - c| := by
    intro s hs
    have := (convex_Icc (c - 1) (c + 1)).norm_image_sub_le_of_norm_deriv_le hdiff1 hK hcmem hs
    rwa [h1, sub_zero, Real.norm_eq_abs] at this
  refine ⟨hA t ht, ?_⟩
  have hsub : uIcc c t ⊆ Icc (c - 1) (c + 1) := uIcc_subset_Icc hcmem ht
  have hdiff0 : ∀ x ∈ uIcc c t, DifferentiableAt ℝ D x := fun x _ =>
    (hD.differentiable (by decide)) x
  have hbound : ∀ x ∈ uIcc c t, ‖deriv D x‖ ≤ K * |t - c| := by
    intro x hx
    refine (hA x (hsub hx)).trans (mul_le_mul_of_nonneg_left ?_ hK0)
    rcases le_total c t with h | h
    · rw [uIcc_of_le h] at hx
      rw [abs_of_nonneg (by linarith [hx.1]), abs_of_nonneg (by linarith)]
      linarith [hx.2]
    · rw [uIcc_of_ge h] at hx
      rw [abs_of_nonpos (by linarith [hx.2]), abs_of_nonpos (by linarith)]
      linarith [hx.1]
  have := (convex_uIcc c t).norm_image_sub_le_of_norm_deriv_le hdiff0 hbound left_mem_uIcc
    right_mem_uIcc
  rw [h0, sub_zero, Real.norm_eq_abs] at this
  calc ‖D t‖ ≤ K * |t - c| * |t - c| := this
    _ = K * |t - c| ^ 2 := by ring

/-- strict monotonicity from a positive derivative on a closed interval (Rolle applied to the
chord difference; `Mathlib.Analysis.Calculus.Deriv.MeanValue` is not imported here) -/
theorem r_strictMonoOn_of_deriv_pos {f : ℝ → ℝ} {a b : ℝ} (hf : Differentiable ℝ f)
    (hpos : ∀ x ∈ Icc a b, 0 < deriv f x) : StrictMonoOn f (Icc a b) := by
  intro x hx y hy hxy
  by_contra hcon
  push Not at hcon
  set m := (f y - f x) / (y - x) with hm
  have hm0 : m ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
  let g : ℝ → ℝ := fun t => f t - f x - m * (t - x)
  have hg : ∀ t, HasDerivAt g (deriv f t - m) t := fun t => by
    have := ((hf t).hasDerivAt.sub_const (f x)).sub
      (((hasDerivAt_id t).sub_const x).const_mul m)
    rw [mul_one] at this
    exact this
  have hgx : g x = 0 := by simp [g]
  have hgy : g y = 0 := by
    simp only [g, hm]
    rw [div_mul_cancel₀ _ (by linarith : y - x ≠ 0)]; ring
  obtain ⟨c, hc, hc'⟩ := exists_deriv_eq_zero hxy
    (fun t _ => (hg t).continuousAt.continuousWithinAt) (hgx.trans hgy.symm)
  rw [(hg c).deriv] at hc'
  have := hpos c ⟨hx.1.trans hc.1.le, hc.2.le.trans hy.2⟩
  linarith

/-! ### the transition profiles of a collar of width `lam` -/

/-- the rising profile on `[c, c + lam]` -/
noncomputable def r_prof (c lam t : ℝ) : ℝ := Real.smoothTransition ((t - c) / lam)
/-- the falling profile on `[c − lam, c]` -/
noncomputable def r_profNeg (c lam t : ℝ) : ℝ := Real.smoothTransition ((c - t) / lam)

theorem r_prof_smooth (c lam : ℝ) : ContDiff ℝ ∞ (r_prof c lam) :=
  Real.smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).div_const lam)
theorem r_profNeg_smooth (c lam : ℝ) : ContDiff ℝ ∞ (r_profNeg c lam) :=
  Real.smoothTransition.contDiff.comp ((contDiff_const.sub contDiff_id).div_const lam)

theorem r_prof_hasDerivAt (c lam t : ℝ) :
    HasDerivAt (r_prof c lam) (deriv Real.smoothTransition ((t - c) / lam) / lam) t := by
  have h1 : HasDerivAt (fun t => (t - c) / lam) (1 / lam) t := by
    simpa using ((hasDerivAt_id t).sub_const c).div_const lam
  have h2 : HasDerivAt Real.smoothTransition (deriv Real.smoothTransition ((t - c) / lam))
      ((t - c) / lam) :=
    ((Real.smoothTransition.contDiff (n := 1)).differentiable (by simp) _).hasDerivAt
  exact (h2.comp t h1).congr_deriv (by ring)
theorem r_profNeg_hasDerivAt (c lam t : ℝ) :
    HasDerivAt (r_profNeg c lam) (-(deriv Real.smoothTransition ((c - t) / lam) / lam)) t := by
  have h1 : HasDerivAt (fun t => (c - t) / lam) (-1 / lam) t := by
    simpa using ((hasDerivAt_id t).const_sub c).div_const lam
  have h2 : HasDerivAt Real.smoothTransition (deriv Real.smoothTransition ((c - t) / lam))
      ((c - t) / lam) :=
    ((Real.smoothTransition.contDiff (n := 1)).differentiable (by simp) _).hasDerivAt
  exact (h2.comp t h1).congr_deriv (by ring)

theorem r_prof_zero {c lam t : ℝ} (hlam : 0 < lam) (h : t ≤ c) : r_prof c lam t = 0 :=
  Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) hlam.le)
theorem r_prof_one {c lam t : ℝ} (hlam : 0 < lam) (h : c + lam ≤ t) : r_prof c lam t = 1 :=
  Real.smoothTransition.one_of_one_le ((le_div_iff₀ hlam).mpr (by linarith))
theorem r_profNeg_zero {c lam t : ℝ} (hlam : 0 < lam) (h : c ≤ t) : r_profNeg c lam t = 0 :=
  Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) hlam.le)
theorem r_profNeg_one {c lam t : ℝ} (hlam : 0 < lam) (h : t ≤ c - lam) : r_profNeg c lam t = 1 :=
  Real.smoothTransition.one_of_one_le ((le_div_iff₀ hlam).mpr (by linarith))
theorem r_prof_mem (c lam t : ℝ) : r_prof c lam t ∈ Icc (0:ℝ) 1 :=
  ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
theorem r_profNeg_mem (c lam t : ℝ) : r_profNeg c lam t ∈ Icc (0:ℝ) 1 :=
  ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

theorem r_prof_deriv_bound {C : ℝ} (hC : ∀ x, |deriv Real.smoothTransition x| ≤ C) (c : ℝ)
    {lam : ℝ} (hlam : 0 < lam) (t : ℝ) : |deriv (r_prof c lam) t| ≤ C / lam := by
  rw [(r_prof_hasDerivAt c lam t).deriv, abs_div, abs_of_pos hlam]
  exact div_le_div_of_nonneg_right (hC _) hlam.le
theorem r_profNeg_deriv_bound {C : ℝ} (hC : ∀ x, |deriv Real.smoothTransition x| ≤ C) (c : ℝ)
    {lam : ℝ} (hlam : 0 < lam) (t : ℝ) : |deriv (r_profNeg c lam) t| ≤ C / lam := by
  rw [(r_profNeg_hasDerivAt c lam t).deriv, abs_neg, abs_div, abs_of_pos hlam]
  exact div_le_div_of_nonneg_right (hC _) hlam.le

/-- the profile derivative vanishes at the end of the collar -/
theorem r_prof_deriv_end (c : ℝ) {lam : ℝ} (hlam : 0 < lam) :
    deriv (r_prof c lam) (c + lam) = 0 := by
  rw [(r_prof_hasDerivAt c lam _).deriv]
  have : (c + lam - c) / lam = 1 := by rw [show c + lam - c = lam by ring, div_self hlam.ne']
  rw [this, r_deriv_smoothTransition_one, zero_div]
theorem r_profNeg_deriv_end (c : ℝ) {lam : ℝ} (hlam : 0 < lam) :
    deriv (r_profNeg c lam) (c - lam) = 0 := by
  rw [(r_profNeg_hasDerivAt c lam _).deriv]
  have : (c - (c - lam)) / lam = 1 := by rw [show c - (c - lam) = lam by ring, div_self hlam.ne']
  rw [this, r_deriv_smoothTransition_one, zero_div, neg_zero]


/-! ### the collar blend -/

/-- The collar blend of two smooth arcs with equal position and velocity at both cuts (sm-3:4080-4212,
in the parameter rather than as a graph): for every `ε > 0` and width bound `lam₀ < (s₂ − s₁)/2`, a width
`lam ≤ lam₀` and a smooth `N` equal to `F` off the window, to `G` (with velocity) on `[s₁ + lam, s₂ − lam]`,
a convex combination of `F t` and `G t` at every `t`, with `N`, `N'` within `ε` of `F`, `F'` on both
collars.  The smallness comes from the flat difference `G − F` (`r_flat_bound`): `|Ψ'| ≤ C/lam` while
`|G − F| ≤ K lam²` on a collar. -/
theorem r_glue {F G : ℝ → Plane} (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G) {s₁ s₂ : ℝ}
    (h₁ : G s₁ = F s₁) (h₁' : deriv G s₁ = deriv F s₁) (h₂ : G s₂ = F s₂)
    (h₂' : deriv G s₂ = deriv F s₂) {ε lam₀ : ℝ} (hε : 0 < ε) (hlam₀ : 0 < lam₀)
    (hlam₀' : 2 * lam₀ < s₂ - s₁) :
    ∃ lam : ℝ, 0 < lam ∧ lam ≤ lam₀ ∧ ∃ N : ℝ → Plane, ContDiff ℝ ∞ N ∧
      (∀ t, t ≤ s₁ → N t = F t) ∧ (∀ t, s₂ ≤ t → N t = F t) ∧
      (∀ t, t < s₁ → deriv N t = deriv F t) ∧ (∀ t, s₂ < t → deriv N t = deriv F t) ∧
      deriv N s₁ = deriv F s₁ ∧ deriv N s₂ = deriv F s₂ ∧
      (∀ t ∈ Icc (s₁ + lam) (s₂ - lam), N t = G t ∧ deriv N t = deriv G t) ∧
      (∀ t, ∃ θ : ℝ, θ ∈ Icc (0:ℝ) 1 ∧ N t = F t + θ • (G t - F t)) ∧
      (∀ t ∈ Icc s₁ (s₁ + lam), ‖deriv N t - deriv F t‖ ≤ ε ∧ ‖N t - F t‖ ≤ ε) ∧
      (∀ t ∈ Icc (s₂ - lam) s₂, ‖deriv N t - deriv F t‖ ≤ ε ∧ ‖N t - F t‖ ≤ ε) := by
  obtain ⟨D, hDdef⟩ : ∃ D : ℝ → Plane, D = fun t => G t - F t := ⟨_, rfl⟩
  have hD : ContDiff ℝ ∞ D := by rw [hDdef]; exact hG.sub hF
  have hFd : Differentiable ℝ F := hF.differentiable (by decide)
  have hGd : Differentiable ℝ G := hG.differentiable (by decide)
  have hDd : Differentiable ℝ D := hD.differentiable (by decide)
  have hDderiv : ∀ t, deriv D t = deriv G t - deriv F t := fun t => by
    rw [hDdef]; exact deriv_sub (hGd t) (hFd t)
  have hDt : ∀ t, D t = G t - F t := fun t => by rw [hDdef]
  have hD₁ : D s₁ = 0 := by rw [hDt, h₁, sub_self]
  have hD₁' : deriv D s₁ = 0 := by rw [hDderiv, h₁', sub_self]
  have hD₂ : D s₂ = 0 := by rw [hDt, h₂, sub_self]
  have hD₂' : deriv D s₂ = 0 := by rw [hDderiv, h₂', sub_self]
  obtain ⟨K₁, hK₁0, hK₁⟩ := r_flat_bound hD hD₁ hD₁'
  obtain ⟨K₂, hK₂0, hK₂⟩ := r_flat_bound hD hD₂ hD₂'
  obtain ⟨C, hC0, hC⟩ := r_smoothTransition_deriv_bound
  obtain ⟨K, hKdef⟩ : ∃ K : ℝ, K = max K₁ K₂ := ⟨_, rfl⟩
  have hK0 : 0 ≤ K := by rw [hKdef]; exact le_max_of_le_left hK₁0
  have hK₁K : K₁ ≤ K := by rw [hKdef]; exact le_max_left _ _
  have hK₂K : K₂ ≤ K := by rw [hKdef]; exact le_max_right _ _
  -- the width
  have hden : 0 < K * (C + 1) + 1 := by positivity
  obtain ⟨lam, hlamdef⟩ : ∃ lam : ℝ, lam = min (min lam₀ 1) (ε / (K * (C + 1) + 1)) := ⟨_, rfl⟩
  have hlam_pos : 0 < lam := by rw [hlamdef]; exact lt_min (lt_min hlam₀ one_pos) (div_pos hε hden)
  have hlam_lam₀ : lam ≤ lam₀ := by rw [hlamdef]; exact (min_le_left _ _).trans (min_le_left _ _)
  have hlam_1 : lam ≤ 1 := by rw [hlamdef]; exact (min_le_left _ _).trans (min_le_right _ _)
  have hlam_ε : lam * (K * (C + 1)) ≤ ε := by
    have h1 : lam ≤ ε / (K * (C + 1) + 1) := by rw [hlamdef]; exact min_le_right _ _
    have h2 : lam * (K * (C + 1) + 1) ≤ ε := by rwa [le_div_iff₀ hden] at h1
    nlinarith
  have hKlam : K * lam ^ 2 ≤ lam * (K * (C + 1)) := by
    have : K * lam ≤ K * 1 := mul_le_mul_of_nonneg_left hlam_1 hK0
    nlinarith [mul_nonneg hK0 hlam_pos.le, mul_nonneg hlam_pos.le hC0]
  have h2lam : s₁ + lam < s₂ - lam := by linarith
  -- the blend
  obtain ⟨Ψ, hΨdef⟩ : ∃ Ψ : ℝ → ℝ, Ψ = fun t => r_prof s₁ lam t * r_profNeg s₂ lam t := ⟨_, rfl⟩
  have hΨt : ∀ t, Ψ t = r_prof s₁ lam t * r_profNeg s₂ lam t := fun t => by rw [hΨdef]
  have hΨs : ContDiff ℝ ∞ Ψ := by rw [hΨdef]; exact (r_prof_smooth _ _).mul (r_profNeg_smooth _ _)
  have hΨd : Differentiable ℝ Ψ := hΨs.differentiable (by decide)
  have hΨmem : ∀ t, Ψ t ∈ Icc (0:ℝ) 1 := fun t => by
    rw [hΨt]
    exact ⟨mul_nonneg (r_prof_mem _ _ _).1 (r_profNeg_mem _ _ _).1,
      mul_le_one₀ (r_prof_mem _ _ _).2 (r_profNeg_mem _ _ _).1 (r_profNeg_mem _ _ _).2⟩
  have hΨabs : ∀ t, |Ψ t| ≤ 1 := fun t => by
    rw [abs_of_nonneg (hΨmem t).1]; exact (hΨmem t).2
  have hΨ_left : ∀ t, t ≤ s₁ → Ψ t = 0 := fun t ht => by
    rw [hΨt, r_prof_zero hlam_pos ht, zero_mul]
  have hΨ_right : ∀ t, s₂ ≤ t → Ψ t = 0 := fun t ht => by
    rw [hΨt, r_profNeg_zero hlam_pos ht, mul_zero]
  have hΨ_mid : ∀ t ∈ Icc (s₁ + lam) (s₂ - lam), Ψ t = 1 := fun t ht => by
    rw [hΨt, r_prof_one hlam_pos ht.1, r_profNeg_one hlam_pos ht.2, mul_one]
  have hΨ_eq_left : ∀ t, t < s₂ - lam → Ψ =ᶠ[nhds t] r_prof s₁ lam := fun t ht =>
    Filter.eventually_of_mem (Iio_mem_nhds ht) fun y hy => by
      rw [hΨt, r_profNeg_one hlam_pos (le_of_lt hy), mul_one]
  have hΨ_eq_right : ∀ t, s₁ + lam < t → Ψ =ᶠ[nhds t] r_profNeg s₂ lam := fun t ht =>
    Filter.eventually_of_mem (Ioi_mem_nhds ht) fun y hy => by
      rw [hΨt, r_prof_one hlam_pos (le_of_lt hy), one_mul]
  obtain ⟨N, hNdef⟩ : ∃ N : ℝ → Plane, N = fun t => F t + Ψ t • D t := ⟨_, rfl⟩
  have hNt : ∀ t, N t = F t + Ψ t • D t := fun t => by rw [hNdef]
  have hNs : ContDiff ℝ ∞ N := by rw [hNdef]; exact hF.add (hΨs.smul hD)
  have hN' : ∀ t, HasDerivAt N (deriv F t + (Ψ t • deriv D t + deriv Ψ t • D t)) t := fun t => by
    rw [hNdef]; exact (hFd t).hasDerivAt.add ((hΨd t).hasDerivAt.smul (hDd t).hasDerivAt)
  refine ⟨lam, hlam_pos, hlam_lam₀, N, hNs, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t ht; rw [hNt, hΨ_left t ht, zero_smul, add_zero]
  · intro t ht; rw [hNt, hΨ_right t ht, zero_smul, add_zero]
  · intro t ht
    have : N =ᶠ[nhds t] F := Filter.eventually_of_mem (Iio_mem_nhds ht) fun y hy => by
      rw [hNt, hΨ_left y (le_of_lt hy), zero_smul, add_zero]
    exact this.deriv_eq
  · intro t ht
    have : N =ᶠ[nhds t] F := Filter.eventually_of_mem (Ioi_mem_nhds ht) fun y hy => by
      rw [hNt, hΨ_right y (le_of_lt hy), zero_smul, add_zero]
    exact this.deriv_eq
  · rw [(hN' s₁).deriv, hΨ_left s₁ le_rfl, hD₁, zero_smul, smul_zero, add_zero, add_zero]
  · rw [(hN' s₂).deriv, hΨ_right s₂ le_rfl, hD₂, zero_smul, smul_zero, add_zero, add_zero]
  · intro t ht
    refine ⟨by rw [hNt, hΨ_mid t ht, one_smul, hDt]; abel, ?_⟩
    have hΨ'0 : deriv Ψ t = 0 := by
      rcases lt_or_eq_of_le ht.1 with h | h
      · rw [(hΨ_eq_right t h).deriv_eq]
        rcases lt_or_eq_of_le ht.2 with h' | h'
        · have : r_profNeg s₂ lam =ᶠ[nhds t] fun _ => 1 :=
            Filter.eventually_of_mem (Iio_mem_nhds h') fun y hy =>
              r_profNeg_one hlam_pos (le_of_lt hy)
          rw [this.deriv_eq]; exact deriv_const _ _
        · rw [h']; exact r_profNeg_deriv_end s₂ hlam_pos
      · rw [← h, (hΨ_eq_left (s₁ + lam) (by linarith)).deriv_eq]
        exact r_prof_deriv_end s₁ hlam_pos
    rw [(hN' t).deriv, hΨ_mid t ht, one_smul, hDderiv, hΨ'0, zero_smul, add_zero]; abel
  · intro t; exact ⟨Ψ t, hΨmem t, by rw [hNt, hDt]⟩
  · -- the left collar
    intro t ht
    have hΨ't : |deriv Ψ t| ≤ C / lam := by
      rw [(hΨ_eq_left t (by linarith [ht.2])).deriv_eq]
      exact r_prof_deriv_bound hC s₁ hlam_pos t
    have htmem : t ∈ Icc (s₁ - 1) (s₁ + 1) := ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have habs : |t - s₁| ≤ lam := by
      rw [abs_of_nonneg (by linarith [ht.1])]; linarith [ht.2]
    obtain ⟨hDb', hDb⟩ := hK₁ t htmem
    have hD'le : ‖deriv D t‖ ≤ K * lam := hDb'.trans (mul_le_mul hK₁K habs (abs_nonneg _) hK0)
    have hDle : ‖D t‖ ≤ K * lam ^ 2 :=
      hDb.trans (mul_le_mul hK₁K (pow_le_pow_left₀ (abs_nonneg _) habs 2) (sq_nonneg _) hK0)
    constructor
    · rw [(hN' t).deriv, add_sub_cancel_left]
      calc ‖Ψ t • deriv D t + deriv Ψ t • D t‖
          ≤ ‖Ψ t • deriv D t‖ + ‖deriv Ψ t • D t‖ := norm_add_le _ _
        _ = |Ψ t| * ‖deriv D t‖ + |deriv Ψ t| * ‖D t‖ := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
        _ ≤ 1 * (K * lam) + (C / lam) * (K * lam ^ 2) :=
          add_le_add (mul_le_mul (hΨabs t) hD'le (norm_nonneg _) zero_le_one)
            (mul_le_mul hΨ't hDle (norm_nonneg _) (div_nonneg hC0 hlam_pos.le))
        _ = lam * (K * (C + 1)) := by field_simp; ring
        _ ≤ ε := hlam_ε
    · rw [hNt, add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
      calc |Ψ t| * ‖D t‖ ≤ 1 * (K * lam ^ 2) :=
            mul_le_mul (hΨabs t) hDle (norm_nonneg _) zero_le_one
        _ ≤ lam * (K * (C + 1)) := by rw [one_mul]; exact hKlam
        _ ≤ ε := hlam_ε
  · -- the right collar
    intro t ht
    have hΨ't : |deriv Ψ t| ≤ C / lam := by
      rw [(hΨ_eq_right t (by linarith [ht.1])).deriv_eq]
      exact r_profNeg_deriv_bound hC s₂ hlam_pos t
    have htmem : t ∈ Icc (s₂ - 1) (s₂ + 1) := ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have habs : |t - s₂| ≤ lam := by
      rw [abs_of_nonpos (by linarith [ht.2])]; linarith [ht.1]
    obtain ⟨hDb', hDb⟩ := hK₂ t htmem
    have hD'le : ‖deriv D t‖ ≤ K * lam := hDb'.trans (mul_le_mul hK₂K habs (abs_nonneg _) hK0)
    have hDle : ‖D t‖ ≤ K * lam ^ 2 :=
      hDb.trans (mul_le_mul hK₂K (pow_le_pow_left₀ (abs_nonneg _) habs 2) (sq_nonneg _) hK0)
    constructor
    · rw [(hN' t).deriv, add_sub_cancel_left]
      calc ‖Ψ t • deriv D t + deriv Ψ t • D t‖
          ≤ ‖Ψ t • deriv D t‖ + ‖deriv Ψ t • D t‖ := norm_add_le _ _
        _ = |Ψ t| * ‖deriv D t‖ + |deriv Ψ t| * ‖D t‖ := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
        _ ≤ 1 * (K * lam) + (C / lam) * (K * lam ^ 2) :=
          add_le_add (mul_le_mul (hΨabs t) hD'le (norm_nonneg _) zero_le_one)
            (mul_le_mul hΨ't hDle (norm_nonneg _) (div_nonneg hC0 hlam_pos.le))
        _ = lam * (K * (C + 1)) := by field_simp; ring
        _ ≤ ε := hlam_ε
    · rw [hNt, add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
      calc |Ψ t| * ‖D t‖ ≤ 1 * (K * lam ^ 2) :=
            mul_le_mul (hΨabs t) hDle (norm_nonneg _) zero_le_one
        _ ≤ lam * (K * (C + 1)) := by rw [one_mul]; exact hKlam
        _ ≤ ε := hlam_ε


/-! ### the reparametrisation of the model with prescribed end speeds -/

/-- A smooth increasing change of variable fixing `s₁`, `s₂` with prescribed positive derivatives
`k₁`, `k₂` at the ends: the FTC of a positive speed profile `k₁ (1 − φ₁) + m (φ₁ − φ₂) + k₂ φ₂`
with two transitions of width `δ` and the middle speed `m` fixed by the total length. -/
theorem r_exists_reparam {s₁ s₂ : ℝ} (hs : s₁ < s₂) {k₁ k₂ : ℝ} (hk₁ : 0 < k₁) (hk₂ : 0 < k₂) :
    ∃ μ : ℝ → ℝ, ContDiff ℝ ∞ μ ∧ (∀ t, 0 < deriv μ t) ∧ μ s₁ = s₁ ∧ μ s₂ = s₂ ∧
      deriv μ s₁ = k₁ ∧ deriv μ s₂ = k₂ := by
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = (s₂ - s₁) / (2 + k₁ + k₂) := ⟨_, rfl⟩
  have hne : (2 + k₁ + k₂) ≠ 0 := by positivity
  have hδ : 0 < δ := by rw [hδdef]; positivity
  have hδeq : δ * (2 + k₁ + k₂) = s₂ - s₁ := by rw [hδdef, div_mul_cancel₀ _ hne]
  have hδ2 : 2 * δ < s₂ - s₁ := by nlinarith [mul_pos hδ (add_pos hk₁ hk₂)]
  have hδk : δ * (k₁ + k₂) < s₂ - s₁ := by nlinarith
  have hs1δ : s₁ + δ ≤ s₂ - δ := by linarith
  -- the two profiles
  obtain ⟨φ₁, hφ₁def⟩ : ∃ φ₁ : ℝ → ℝ, φ₁ = r_prof s₁ δ := ⟨_, rfl⟩
  obtain ⟨φ₂, hφ₂def⟩ : ∃ φ₂ : ℝ → ℝ, φ₂ = r_prof (s₂ - δ) δ := ⟨_, rfl⟩
  have hφ₁s : ContDiff ℝ ∞ φ₁ := by rw [hφ₁def]; exact r_prof_smooth _ _
  have hφ₂s : ContDiff ℝ ∞ φ₂ := by rw [hφ₂def]; exact r_prof_smooth _ _
  have hφ₁c : Continuous φ₁ := hφ₁s.continuous
  have hφ₂c : Continuous φ₂ := hφ₂s.continuous
  have hφ₁mem : ∀ s, φ₁ s ∈ Icc (0:ℝ) 1 := fun s => by rw [hφ₁def]; exact r_prof_mem _ _ _
  have hφ₂mem : ∀ s, φ₂ s ∈ Icc (0:ℝ) 1 := fun s => by rw [hφ₂def]; exact r_prof_mem _ _ _
  have hφ₁0 : ∀ s, s ≤ s₁ → φ₁ s = 0 := fun s hs => by rw [hφ₁def]; exact r_prof_zero hδ hs
  have hφ₁1 : ∀ s, s₁ + δ ≤ s → φ₁ s = 1 := fun s hs => by rw [hφ₁def]; exact r_prof_one hδ hs
  have hφ₂0 : ∀ s, s ≤ s₂ - δ → φ₂ s = 0 := fun s hs => by rw [hφ₂def]; exact r_prof_zero hδ hs
  have hφ₂1 : ∀ s, s₂ ≤ s → φ₂ s = 1 := fun s hs => by
    rw [hφ₂def]; exact r_prof_one hδ (by linarith)
  have hφ₂₁ : ∀ s, φ₂ s ≤ φ₁ s := fun s => by
    rw [hφ₁def, hφ₂def]
    exact Real.smoothTransition.monotone (div_le_div_of_nonneg_right (by linarith) hδ.le)
  -- the three integrals
  obtain ⟨A, hAdef⟩ : ∃ A : ℝ, A = ∫ s in s₁..s₂, (1 - φ₁ s) := ⟨_, rfl⟩
  obtain ⟨B, hBdef⟩ : ∃ B : ℝ, B = ∫ s in s₁..s₂, (φ₁ s - φ₂ s) := ⟨_, rfl⟩
  obtain ⟨Cc, hCdef⟩ : ∃ Cc : ℝ, Cc = ∫ s in s₁..s₂, φ₂ s := ⟨_, rfl⟩
  have hi1 : ∀ a b : ℝ, IntervalIntegrable (fun s => 1 - φ₁ s) MeasureTheory.volume a b :=
    fun a b => (continuous_const.sub hφ₁c).intervalIntegrable a b
  have hi2 : ∀ a b : ℝ, IntervalIntegrable (fun s => φ₁ s - φ₂ s) MeasureTheory.volume a b :=
    fun a b => (hφ₁c.sub hφ₂c).intervalIntegrable a b
  have hi3 : ∀ a b : ℝ, IntervalIntegrable φ₂ MeasureTheory.volume a b :=
    fun a b => hφ₂c.intervalIntegrable a b
  have hA0 : 0 ≤ A := by
    rw [hAdef]
    exact intervalIntegral.integral_nonneg hs.le fun s _ => by linarith [(hφ₁mem s).2]
  have hAδ : A ≤ δ := by
    rw [hAdef, ← intervalIntegral.integral_add_adjacent_intervals (hi1 s₁ (s₁ + δ))
      (hi1 (s₁ + δ) s₂)]
    have h1 : ∫ s in s₁..(s₁ + δ), (1 - φ₁ s) ≤ ∫ s in s₁..(s₁ + δ), (1 : ℝ) := by
      refine intervalIntegral.integral_mono_on (by linarith) (hi1 _ _)
        (continuous_const.intervalIntegrable _ _) fun s _ => ?_
      linarith [(hφ₁mem s).1]
    have h2 : ∫ s in (s₁ + δ)..s₂, (1 - φ₁ s) = 0 := by
      rw [intervalIntegral.integral_congr (g := fun _ => (0:ℝ)) fun s hs => ?_]
      · simp
      · rw [uIcc_of_le (by linarith)] at hs
        show 1 - φ₁ s = 0
        rw [hφ₁1 s hs.1, sub_self]
    rw [intervalIntegral.integral_const, smul_eq_mul, mul_one] at h1
    linarith
  have hC0 : 0 ≤ Cc := by
    rw [hCdef]; exact intervalIntegral.integral_nonneg hs.le fun s _ => (hφ₂mem s).1
  have hCδ : Cc ≤ δ := by
    rw [hCdef, ← intervalIntegral.integral_add_adjacent_intervals (hi3 s₁ (s₂ - δ))
      (hi3 (s₂ - δ) s₂)]
    have h1 : ∫ s in s₁..(s₂ - δ), φ₂ s = 0 := by
      rw [intervalIntegral.integral_congr (g := fun _ => (0:ℝ)) fun s hs => ?_]
      · simp
      · rw [uIcc_of_le (by linarith)] at hs
        exact hφ₂0 s hs.2
    have h2 : ∫ s in (s₂ - δ)..s₂, φ₂ s ≤ ∫ s in (s₂ - δ)..s₂, (1 : ℝ) :=
      intervalIntegral.integral_mono_on (by linarith) (hi3 _ _)
        (continuous_const.intervalIntegrable _ _) fun s _ => (hφ₂mem s).2
    rw [intervalIntegral.integral_const, smul_eq_mul, mul_one] at h2
    linarith
  have hB : s₂ - s₁ - 2 * δ ≤ B := by
    rw [hBdef, ← intervalIntegral.integral_add_adjacent_intervals (hi2 s₁ (s₁ + δ))
      (hi2 (s₁ + δ) s₂),
      ← intervalIntegral.integral_add_adjacent_intervals (hi2 (s₁ + δ) (s₂ - δ)) (hi2 (s₂ - δ) s₂)]
    have h1 : 0 ≤ ∫ s in s₁..(s₁ + δ), (φ₁ s - φ₂ s) :=
      intervalIntegral.integral_nonneg (by linarith) fun s _ => by linarith [hφ₂₁ s]
    have h3 : 0 ≤ ∫ s in (s₂ - δ)..s₂, (φ₁ s - φ₂ s) :=
      intervalIntegral.integral_nonneg (by linarith) fun s _ => by linarith [hφ₂₁ s]
    have h2 : ∫ s in (s₁ + δ)..(s₂ - δ), (φ₁ s - φ₂ s) = s₂ - s₁ - 2 * δ := by
      rw [intervalIntegral.integral_congr (g := fun _ => (1:ℝ)) fun s hs => ?_]
      · rw [intervalIntegral.integral_const, smul_eq_mul, mul_one]; ring
      · rw [uIcc_of_le hs1δ] at hs
        show φ₁ s - φ₂ s = 1
        rw [hφ₁1 s hs.1, hφ₂0 s hs.2, sub_zero]
    linarith
  have hBpos : 0 < B := by linarith
  -- the middle speed
  obtain ⟨m, hmdef⟩ : ∃ m : ℝ, m = (s₂ - s₁ - k₁ * A - k₂ * Cc) / B := ⟨_, rfl⟩
  have hm : 0 < m := by
    rw [hmdef]; apply div_pos _ hBpos
    nlinarith [mul_le_mul_of_nonneg_left hAδ hk₁.le, mul_le_mul_of_nonneg_left hCδ hk₂.le]
  have hmB : m * B = s₂ - s₁ - k₁ * A - k₂ * Cc := by rw [hmdef, div_mul_cancel₀ _ hBpos.ne']
  -- the speed profile
  obtain ⟨w, hwdef⟩ : ∃ w : ℝ → ℝ,
      w = fun s => k₁ * (1 - φ₁ s) + m * (φ₁ s - φ₂ s) + k₂ * φ₂ s := ⟨_, rfl⟩
  have hwt : ∀ s, w s = k₁ * (1 - φ₁ s) + m * (φ₁ s - φ₂ s) + k₂ * φ₂ s := fun s => by rw [hwdef]
  have hws : ContDiff ℝ ∞ w := by
    rw [hwdef]
    exact ((contDiff_const.mul (contDiff_const.sub hφ₁s)).add
      (contDiff_const.mul (hφ₁s.sub hφ₂s))).add (contDiff_const.mul hφ₂s)
  have hwc : Continuous w := hws.continuous
  have hwpos : ∀ s, 0 < w s := fun s => by
    rw [hwt]
    obtain ⟨μ₀, hμ₀def⟩ : ∃ μ₀ : ℝ, μ₀ = min (min k₁ k₂) m := ⟨_, rfl⟩
    have hμ₀ : 0 < μ₀ := by rw [hμ₀def]; exact lt_min (lt_min hk₁ hk₂) hm
    have h1 : μ₀ ≤ k₁ := by rw [hμ₀def]; exact (min_le_left _ _).trans (min_le_left _ _)
    have h2 : μ₀ ≤ k₂ := by rw [hμ₀def]; exact (min_le_left _ _).trans (min_le_right _ _)
    have h3 : μ₀ ≤ m := by rw [hμ₀def]; exact min_le_right _ _
    have ha : 0 ≤ 1 - φ₁ s := by linarith [(hφ₁mem s).2]
    have hb : 0 ≤ φ₁ s - φ₂ s := by linarith [hφ₂₁ s]
    have hc : 0 ≤ φ₂ s := (hφ₂mem s).1
    nlinarith [mul_le_mul_of_nonneg_right h1 ha, mul_le_mul_of_nonneg_right h2 hc,
      mul_le_mul_of_nonneg_right h3 hb]
  have hwint : ∫ s in s₁..s₂, w s = s₂ - s₁ := by
    have e : ∫ s in s₁..s₂, w s = k₁ * A + m * B + k₂ * Cc := by
      rw [hAdef, hBdef, hCdef, ← intervalIntegral.integral_const_mul,
        ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
        ← intervalIntegral.integral_add ((hi1 _ _).const_mul k₁) ((hi2 _ _).const_mul m),
        ← intervalIntegral.integral_add (((hi1 _ _).const_mul k₁).add ((hi2 _ _).const_mul m))
          ((hi3 _ _).const_mul k₂)]
      exact intervalIntegral.integral_congr fun s _ => hwt s
    rw [e]; linarith [hmB]
  -- the change of variable
  obtain ⟨μ, hμdef⟩ : ∃ μ : ℝ → ℝ, μ = fun t => s₁ + ∫ s in s₁..t, w s := ⟨_, rfl⟩
  have hμ' : ∀ t, HasDerivAt μ (w t) t := fun t => by
    rw [hμdef]
    exact (intervalIntegral.integral_hasDerivAt_right (hwc.intervalIntegrable _ _)
      (hwc.stronglyMeasurableAtFilter _ _) hwc.continuousAt).const_add s₁
  have hμs : ContDiff ℝ ∞ μ := by
    rw [contDiff_infty_iff_deriv]
    refine ⟨fun t => (hμ' t).differentiableAt, ?_⟩
    have e : deriv μ = w := funext fun t => (hμ' t).deriv
    rw [e]; exact hws
  refine ⟨μ, hμs, fun t => by rw [(hμ' t).deriv]; exact hwpos t, ?_, ?_, ?_, ?_⟩
  · rw [hμdef]; simp
  · rw [hμdef]; show s₁ + ∫ s in s₁..s₂, w s = s₂
    rw [hwint]; ring
  · rw [(hμ' s₁).deriv, hwt, hφ₁0 s₁ le_rfl, hφ₂0 s₁ (by linarith)]; ring
  · rw [(hμ' s₂).deriv, hwt, hφ₁1 s₂ (by linarith), hφ₂1 s₂ le_rfl]; ring

/-- The reparametrised model arc `G = Φ ∘ c ∘ σ̃` on the window of a cut-fit (sm-3:4033-4054 read on
the window): `σ̃` is an increasing smooth change of variable `[s₁, s₂] → [−2, 2]` whose end speeds
are chosen so that `G` has `F`'s velocity at both cuts (`r_exists_reparam`).  Exported: smoothness,
the cut data, containment in the disc, the transverse excess, the double point `q₁ < q₂` (later
branch over, negative) with `q₀` the `−u`-tangency between them, no other double point, and the sign
of the `v`-component of the velocity (positive before `q₀`, negative after, `−u` at `q₀`). -/
theorem r_exists_model {α' β' r : ℝ} (cf : CutFit S α' β' r) :
    ∃ G : ℝ → Plane, ∃ q₀ q₁ q₂ : ℝ, ContDiff ℝ ∞ G ∧
      G cf.s₁ = S.F.γ cf.s₁ ∧ G cf.s₂ = S.F.γ cf.s₂ ∧
      deriv G cf.s₁ = deriv S.F.γ cf.s₁ ∧ deriv G cf.s₂ = deriv S.F.γ cf.s₂ ∧
      (∀ t ∈ Icc cf.s₁ cf.s₂, G t ∈ disc S r) ∧
      (∀ t ∈ Ioo cf.s₁ cf.s₂, ξ S cf.s₁ < planeDot (G t - S.p) (vDir S)) ∧
      q₁ ∈ Ioo cf.s₁ cf.s₂ ∧ q₂ ∈ Ioo cf.s₁ cf.s₂ ∧ q₁ < q₀ ∧ q₀ < q₂ ∧
      G q₁ = G q₂ ∧ det (deriv G q₂) (deriv G q₁) < 0 ∧
      (∀ s ∈ Icc cf.s₁ cf.s₂, ∀ t ∈ Icc cf.s₁ cf.s₂, s ≠ t → G s = G t →
        (s = q₁ ∧ t = q₂) ∨ (s = q₂ ∧ t = q₁)) ∧
      (∀ t ∈ Icc cf.s₁ cf.s₂, t < q₀ → 0 < planeDot (deriv G t) (vDir S)) ∧
      (∀ t ∈ Icc cf.s₁ cf.s₂, q₀ < t → planeDot (deriv G t) (vDir S) < 0) ∧
      planeDot (deriv G q₀) (vDir S) = 0 ∧ planeDot (deriv G q₀) S.u < 0 ∧
      (∀ t ∈ Icc cf.s₁ cf.s₂, deriv G t ≠ 0) := by
  have hs : cf.s₁ < cf.s₂ := cf.s₁_lt.trans cf.lt_s₂
  have hs0 : cf.s₂ - cf.s₁ ≠ 0 := (sub_pos.mpr hs).ne'
  have hprops := inserted_arc_props S hs cf.ξ_eq cf.ℓ_pos cf.T_minus cf.T_plus cf.a_pos cf.b_pos
    cf.c_pos cf.d_pos
  dsimp only at hprops
  obtain ⟨hΦ₁, hΦ₂, ⟨r₁, hr₁, hΦ'₁⟩, ⟨r₂, hr₂, hΦ'₂⟩, hexc, hdbl, hsign, hinj, -⟩ := hprops
  set ℓ := η S cf.s₂ - η S cf.s₁ with hℓdef
  set x := xFit cf.a cf.b cf.c cf.d with hxdef
  set y := yFit cf.a cf.b cf.c cf.d with hydef
  set Φc := inserted (S.F.γ cf.s₁) ℓ S.u (vDir S) x y with hΦcdef
  have hℓ : 0 < ℓ := sub_pos.mpr cf.ℓ_pos
  have hℓ12 : 0 < ℓ / 12 := by positivity
  have hx : 0 < x := xFit_pos cf.a_pos cf.b_pos cf.c_pos cf.d_pos
  have hvv : planeDot (vDir S) (vDir S) = 1 := r_planeDot_vDir_vDir S
  have hvu : planeDot (vDir S) S.u = 0 := planeDot_vDir_u S
  have huv : planeDot S.u (vDir S) = 0 := by rw [r_planeDot_comm]; exact hvu
  have huu : planeDot S.u S.u = 1 := r_planeDot_u_u S
  have hΦ' : ∀ τ, HasDerivAt Φc ((ℓ / 12) • fitA S.u (vDir S) x y (2 * τ, 1 - 3 * τ ^ 2)) τ :=
    fun τ => r_hasDerivAt_inserted _ _ _ _ _ _ τ
  have hΦs : ContDiff ℝ ∞ Φc := by
    rw [hΦcdef]; unfold inserted fitA cModel bModel; fun_prop
  -- the velocity-matching reparametrisation
  have hF₁ : deriv S.F.γ cf.s₁ ≠ 0 := S.F.regular _
  have hF₂ : deriv S.F.γ cf.s₂ ≠ 0 := S.F.regular _
  have hL₁ : 0 < euclideanLength (deriv S.F.γ cf.s₁) := euclideanLength_pos hF₁
  have hL₂ : 0 < euclideanLength (deriv S.F.γ cf.s₂) := euclideanLength_pos hF₂
  obtain ⟨μ, hμs, hμ', hμ₁, hμ₂, hμ'₁, hμ'₂⟩ := r_exists_reparam hs
    (k₁ := euclideanLength (deriv S.F.γ cf.s₁) * (cf.s₂ - cf.s₁) / (4 * r₁))
    (k₂ := euclideanLength (deriv S.F.γ cf.s₂) * (cf.s₂ - cf.s₁) / (4 * r₂))
    (by have := sub_pos.mpr hs; positivity) (by have := sub_pos.mpr hs; positivity)
  have hμd : Differentiable ℝ μ := hμs.differentiable (by decide)
  obtain ⟨σ, hσdef⟩ : ∃ σ : ℝ → ℝ, σ = fun t => -2 + 4 * (μ t - cf.s₁) / (cf.s₂ - cf.s₁) :=
    ⟨_, rfl⟩
  have hσt : ∀ t, σ t = -2 + 4 * (μ t - cf.s₁) / (cf.s₂ - cf.s₁) := fun t => by rw [hσdef]
  have hσ' : ∀ t, HasDerivAt σ (4 / (cf.s₂ - cf.s₁) * deriv μ t) t := fun t => by
    rw [hσdef]
    have h := ((((hμd t).hasDerivAt.sub_const cf.s₁).const_mul 4).div_const
      (cf.s₂ - cf.s₁)).const_add (-2)
    exact h.congr_deriv (by ring)
  have hσpos : ∀ t, 0 < 4 / (cf.s₂ - cf.s₁) * deriv μ t := fun t =>
    mul_pos (div_pos four_pos (sub_pos.mpr hs)) (hμ' t)
  have hσs : ContDiff ℝ ∞ σ := by rw [hσdef]; fun_prop
  have hσ₁ : σ cf.s₁ = -2 := by rw [hσt, hμ₁, sub_self, mul_zero, zero_div, add_zero]
  have hσ₂ : σ cf.s₂ = 2 := by rw [hσt, hμ₂]; field_simp; ring
  have hσmono : StrictMonoOn σ (Icc cf.s₁ cf.s₂) :=
    r_strictMonoOn_of_deriv_pos (fun t => (hσ' t).differentiableAt) fun t _ => by
      rw [(hσ' t).deriv]; exact hσpos t
  have hσmem : ∀ t ∈ Icc cf.s₁ cf.s₂, σ t ∈ Icc (-2:ℝ) 2 := fun t ht =>
    ⟨by rw [← hσ₁]; exact hσmono.monotoneOn (left_mem_Icc.mpr hs.le) ht ht.1,
     by rw [← hσ₂]; exact hσmono.monotoneOn ht (right_mem_Icc.mpr hs.le) ht.2⟩
  have hσmem' : ∀ t ∈ Ioo cf.s₁ cf.s₂, σ t ∈ Ioo (-2:ℝ) 2 := fun t ht =>
    ⟨by rw [← hσ₁]; exact hσmono (left_mem_Icc.mpr hs.le) (Ioo_subset_Icc_self ht) ht.1,
     by rw [← hσ₂]; exact hσmono (Ioo_subset_Icc_self ht) (right_mem_Icc.mpr hs.le) ht.2⟩
  -- the model arc and its velocity
  obtain ⟨G, hGdef⟩ : ∃ G : ℝ → Plane, G = fun t => Φc (σ t) := ⟨_, rfl⟩
  have hGt : ∀ t, G t = Φc (σ t) := fun t => by rw [hGdef]
  have hGs : ContDiff ℝ ∞ G := by rw [hGdef]; exact hΦs.comp hσs
  have hG' : ∀ t, HasDerivAt G ((4 / (cf.s₂ - cf.s₁) * deriv μ t) •
      ((ℓ / 12) • fitA S.u (vDir S) x y (2 * σ t, 1 - 3 * (σ t) ^ 2))) t := fun t => by
    rw [hGdef]; exact (hΦ' (σ t)).scomp t (hσ' t)
  have hdG : ∀ t, deriv G t = (4 / (cf.s₂ - cf.s₁) * deriv μ t) •
      ((ℓ / 12) • fitA S.u (vDir S) x y (2 * σ t, 1 - 3 * (σ t) ^ 2)) := fun t => (hG' t).deriv
  have hdotv : ∀ t, planeDot (deriv G t) (vDir S) =
      (4 / (cf.s₂ - cf.s₁) * deriv μ t) * (ℓ / 12) * (2 * (-σ t) * x) := fun t => by
    rw [hdG, g_planeDot_smul_left, g_planeDot_smul_left, r_planeDot_fitA, hvv, huv]; ring
  -- the three distinguished parameters by the intermediate value theorem
  have hIVT : Icc (σ cf.s₁) (σ cf.s₂) ⊆ σ '' Icc cf.s₁ cf.s₂ :=
    intermediate_value_Icc hs.le hσs.continuous.continuousOn
  rw [hσ₁, hσ₂] at hIVT
  obtain ⟨q₁, hq₁mem, hq₁⟩ := hIVT (show (-1:ℝ) ∈ Icc (-2:ℝ) 2 by norm_num)
  obtain ⟨q₀, hq₀mem, hq₀⟩ := hIVT (show (0:ℝ) ∈ Icc (-2:ℝ) 2 by norm_num)
  obtain ⟨q₂, hq₂mem, hq₂⟩ := hIVT (show (1:ℝ) ∈ Icc (-2:ℝ) 2 by norm_num)
  have hq₁Ioo : q₁ ∈ Ioo cf.s₁ cf.s₂ := by
    refine ⟨lt_of_le_of_ne hq₁mem.1 fun h => ?_, lt_of_le_of_ne hq₁mem.2 fun h => ?_⟩
    · rw [← h, hσ₁] at hq₁; norm_num at hq₁
    · rw [h, hσ₂] at hq₁; norm_num at hq₁
  have hq₂Ioo : q₂ ∈ Ioo cf.s₁ cf.s₂ := by
    refine ⟨lt_of_le_of_ne hq₂mem.1 fun h => ?_, lt_of_le_of_ne hq₂mem.2 fun h => ?_⟩
    · rw [← h, hσ₁] at hq₂; norm_num at hq₂
    · rw [h, hσ₂] at hq₂; norm_num at hq₂
  have hq₁₀ : q₁ < q₀ := (hσmono.lt_iff_lt hq₁mem hq₀mem).mp (by rw [hq₁, hq₀]; norm_num)
  have hq₀₂ : q₀ < q₂ := (hσmono.lt_iff_lt hq₀mem hq₂mem).mp (by rw [hq₀, hq₂]; norm_num)
  have hσneg : ∀ t ∈ Icc cf.s₁ cf.s₂, t < q₀ → σ t < 0 := fun t ht h => by
    rw [← hq₀]; exact hσmono ht hq₀mem h
  have hσposq : ∀ t ∈ Icc cf.s₁ cf.s₂, q₀ < t → 0 < σ t := fun t ht h => by
    rw [← hq₀]; exact hσmono hq₀mem ht h
  refine ⟨G, q₀, q₁, q₂, hGs, ?_, ?_, ?_, ?_, ?_, ?_, hq₁Ioo, hq₂Ioo, hq₁₀, hq₀₂, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_⟩
  · rw [hGt, hσ₁]; exact hΦ₁
  · rw [hGt, hσ₂]; exact hΦ₂
  · rw [hdG, hσ₁, hμ'₁, ← (hΦ' (-2)).deriv, hΦ'₁, smul_smul]
    have e : 4 / (cf.s₂ - cf.s₁) * (euclideanLength (deriv S.F.γ cf.s₁) * (cf.s₂ - cf.s₁) /
        (4 * r₁)) * r₁ = euclideanLength (deriv S.F.γ cf.s₁) := by
      field_simp
    rw [e]; exact CornerRounding.X_smul_normalize hF₁
  · rw [hdG, hσ₂, hμ'₂, ← (hΦ' 2).deriv, hΦ'₂, smul_smul]
    have e : 4 / (cf.s₂ - cf.s₁) * (euclideanLength (deriv S.F.γ cf.s₂) * (cf.s₂ - cf.s₁) /
        (4 * r₂)) * r₂ = euclideanLength (deriv S.F.γ cf.s₂) := by
      field_simp
    rw [e]; exact CornerRounding.X_smul_normalize hF₂
  · intro t ht; rw [hGt]; exact cf.ins_in_disc _ (hσmem t ht)
  · intro t ht; rw [hGt]; exact hexc _ (hσmem' t ht)
  · rw [hGt, hGt, hq₁, hq₂]; exact hdbl
  · rw [hdG, hdG, hq₁, hq₂, CornerRounding.X_det_smul_smul]
    have h := hsign
    rw [(hΦ' 1).deriv, (hΦ' (-1)).deriv] at h
    have hc : 0 < 4 / (cf.s₂ - cf.s₁) * deriv μ q₂ * (4 / (cf.s₂ - cf.s₁) * deriv μ q₁) :=
      mul_pos (hσpos _) (hσpos _)
    exact mul_neg_of_pos_of_neg hc h
  · intro s hs' t ht hst hGst
    rw [hGt, hGt] at hGst
    have hne : σ s ≠ σ t := fun h => hst (hσmono.injOn hs' ht h)
    rcases hinj (σ s) (hσmem s hs') (σ t) (hσmem t ht) hne hGst with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨hσmono.injOn hs' hq₁mem (h1.trans hq₁.symm),
        hσmono.injOn ht hq₂mem (h2.trans hq₂.symm)⟩
    · exact Or.inr ⟨hσmono.injOn hs' hq₂mem (h1.trans hq₂.symm),
        hσmono.injOn ht hq₁mem (h2.trans hq₁.symm)⟩
  · intro t ht h
    rw [hdotv]
    have := hσneg t ht h
    exact mul_pos (mul_pos (hσpos t) hℓ12) (mul_pos (mul_pos two_pos (by linarith)) hx)
  · intro t ht h
    rw [hdotv]
    have := hσposq t ht h
    have : 0 < (4 / (cf.s₂ - cf.s₁) * deriv μ t) * (ℓ / 12) * (2 * σ t * x) :=
      mul_pos (mul_pos (hσpos t) hℓ12) (mul_pos (mul_pos two_pos this) hx)
    linarith
  · rw [hdotv, hq₀]; ring
  · rw [hdG, hq₀, g_planeDot_smul_left, g_planeDot_smul_left, r_planeDot_fitA, hvu, huu]
    have : 0 < 4 / (cf.s₂ - cf.s₁) * deriv μ q₀ * (ℓ / 12) := mul_pos (hσpos _) hℓ12
    nlinarith
  · intro t ht h0
    rcases lt_trichotomy t q₀ with hlt | heq | hgt
    · have := hσneg t ht hlt
      have : 0 < planeDot (deriv G t) (vDir S) := by
        rw [hdotv]
        exact mul_pos (mul_pos (hσpos t) hℓ12) (mul_pos (mul_pos two_pos (by linarith)) hx)
      rw [h0] at this; simp [planeDot] at this
    · subst heq
      have : planeDot (deriv G t) S.u < 0 := by
        rw [hdG, hq₀, g_planeDot_smul_left, g_planeDot_smul_left, r_planeDot_fitA, hvu, huu]
        have : 0 < 4 / (cf.s₂ - cf.s₁) * deriv μ t * (ℓ / 12) := mul_pos (hσpos _) hℓ12
        nlinarith
      rw [h0] at this; simp [planeDot] at this
    · have := hσposq t ht hgt
      have : planeDot (deriv G t) (vDir S) < 0 := by
        rw [hdotv]
        have : 0 < (4 / (cf.s₂ - cf.s₁) * deriv μ t) * (ℓ / 12) * (2 * σ t * x) :=
          mul_pos (mul_pos (hσpos t) hℓ12) (mul_pos (mul_pos two_pos this) hx)
        linarith
      rw [h0] at this; simp [planeDot] at this

/-! #### Unit R helpers for the glued arc: dot products, zones, the disc, the frame -/

theorem r_planeDot_neg_left (a w : Plane) : planeDot (-a) w = -planeDot a w := by
  simp only [planeDot, Prod.fst_neg, Prod.snd_neg]; ring
theorem r_planeDot_sub_left (a b w : Plane) : planeDot (a - b) w = planeDot a w - planeDot b w := by
  simp only [planeDot, Prod.fst_sub, Prod.snd_sub]; ring

/-- `|⟨w, z⟩| ≤ 2 ‖w‖` for a unit `z` (sup norm on the plane) -/
theorem r_abs_planeDot_le (w z : Plane) (hz : euclideanLength z = 1) : |planeDot w z| ≤ 2 * ‖w‖ := by
  rw [euclideanLength_formula, Real.sqrt_eq_one] at hz
  have hz1 : |z.1| ≤ 1 := abs_le.mpr ⟨by nlinarith [sq_nonneg (z.1 + 1), sq_nonneg z.2],
    by nlinarith [sq_nonneg (z.1 - 1), sq_nonneg z.2]⟩
  have hz2 : |z.2| ≤ 1 := abs_le.mpr ⟨by nlinarith [sq_nonneg (z.2 + 1), sq_nonneg z.1],
    by nlinarith [sq_nonneg (z.2 - 1), sq_nonneg z.1]⟩
  have hw1 : |w.1| ≤ ‖w‖ := by
    rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]; exact le_max_left _ _
  have hw2 : |w.2| ≤ ‖w‖ := by
    rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]; exact le_max_right _ _
  calc |planeDot w z| = |w.1 * z.1 + w.2 * z.2| := rfl
    _ ≤ |w.1 * z.1| + |w.2 * z.2| := abs_add_le _ _
    _ = |w.1| * |z.1| + |w.2| * |z.2| := by rw [abs_mul, abs_mul]
    _ ≤ ‖w‖ * 1 + ‖w‖ * 1 :=
      add_le_add (mul_le_mul hw1 hz1 (abs_nonneg _) (norm_nonneg _))
        (mul_le_mul hw2 hz2 (abs_nonneg _) (norm_nonneg _))
    _ = 2 * ‖w‖ := by ring

theorem r_continuous_planeDot {γ : ℝ → Plane} (h : Continuous γ) (w : Plane) :
    Continuous fun t => planeDot (γ t) w := by
  unfold planeDot; fun_prop

theorem r_hasDerivAt_planeDot {γ : ℝ → Plane} {γ' : Plane} {t : ℝ} (h : HasDerivAt γ γ' t)
    (w : Plane) : HasDerivAt (fun t => planeDot (γ t) w) (planeDot γ' w) t := by
  have h1 : HasDerivAt (fun t => (γ t).1) γ'.1 t :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt t h
  have h2 : HasDerivAt (fun t => (γ t).2) γ'.2 t :=
    (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt t h
  exact (h1.mul_const w.1).add (h2.mul_const w.2)

/-- a neighbourhood statement gives a closed zone -/
theorem r_zone_of_eventually {p : ℝ → Prop} {c : ℝ} (h : ∀ᶠ t in nhds c, p t) :
    ∃ ζ : ℝ, 0 < ζ ∧ ∀ t, |t - c| ≤ ζ → p t := by
  obtain ⟨ζ, hζ, hp⟩ := Metric.eventually_nhds_iff.mp h
  exact ⟨ζ / 2, by positivity, fun t ht => hp (by rw [Real.dist_eq]; linarith)⟩

theorem r_planeDot_normalize' (w z : Plane) :
    planeDot (normalize w) z = (euclideanLength w)⁻¹ * planeDot w z := by
  unfold normalize; exact g_planeDot_smul_left _ _ _

theorem r_euclideanLength_neg (w : Plane) : euclideanLength (-w) = euclideanLength w := by
  simp only [euclideanLength, planeComplex_neg, norm_neg]

theorem r_normalize_neg_u : normalize (-S.u) = -S.u := by
  unfold normalize; rw [r_euclideanLength_neg, S.u_unit, inv_one, one_smul]

/-- the orthonormal expansion in the frame `(v, u)` -/
theorem r_expand (w : Plane) : w = planeDot w (vDir S) • vDir S + planeDot w S.u • S.u := by
  have h := S.u_unit
  rw [euclideanLength_formula, Real.sqrt_eq_one] at h
  refine Prod.ext ?_ ?_ <;> simp only [vDir, J, planeDot, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
    Prod.smul_snd, smul_eq_mul, Prod.fst_neg, Prod.snd_neg, neg_neg]
  · linear_combination (-w.1) * h
  · linear_combination (-w.2) * h

/-- the closed Euclidean disc is convex (the convex-combination form used for the blend) -/
theorem r_disc_convex {r : ℝ} {a b : Plane} (ha : a ∈ disc S r) (hb : b ∈ disc S r) {θ : ℝ}
    (hθ : θ ∈ Icc (0:ℝ) 1) : a + θ • (b - a) ∈ disc S r := by
  have ha' : euclideanLength (a - S.p) ≤ r := ha
  have hb' : euclideanLength (b - S.p) ≤ r := hb
  show euclideanLength (a + θ • (b - a) - S.p) ≤ r
  have e : a + θ • (b - a) - S.p = (1 - θ) • (a - S.p) + θ • (b - S.p) := by
    simp only [sub_smul, one_smul, smul_sub]; abel
  rw [e]
  calc euclideanLength ((1 - θ) • (a - S.p) + θ • (b - S.p))
      ≤ euclideanLength ((1 - θ) • (a - S.p)) + euclideanLength (θ • (b - S.p)) :=
        r_euclideanLength_add_le _ _
    _ = (1 - θ) * euclideanLength (a - S.p) + θ * euclideanLength (b - S.p) := by
        rw [euclideanLength_smul, euclideanLength_smul, abs_of_nonneg (by linarith [hθ.2]),
          abs_of_nonneg hθ.1]
    _ ≤ (1 - θ) * r + θ * r :=
        add_le_add (mul_le_mul_of_nonneg_left ha' (by linarith [hθ.2]))
          (mul_le_mul_of_nonneg_left hb' hθ.1)
    _ = r := by ring

/-! #### Unit R: the pieces of the glued arc (small contexts, one fact each) -/

/-- the velocities of `F` at the cuts lie in the open quadrants `{⟨·,v⟩ > 0, ⟨·,u⟩ > 0}` and
`{⟨·,v⟩ < 0, ⟨·,u⟩ > 0}` -/
theorem r_cut_velocity {α' β' r : ℝ} (cf : CutFit S α' β' r) :
    0 < planeDot (deriv S.F.γ cf.s₁) (vDir S) ∧ 0 < planeDot (deriv S.F.γ cf.s₁) S.u ∧
    planeDot (deriv S.F.γ cf.s₂) (vDir S) < 0 ∧ 0 < planeDot (deriv S.F.γ cf.s₂) S.u := by
  have hvv : planeDot (vDir S) (vDir S) = 1 := r_planeDot_vDir_vDir S
  have hvu : planeDot (vDir S) S.u = 0 := planeDot_vDir_u S
  have huv : planeDot S.u (vDir S) = 0 := by rw [r_planeDot_comm]; exact hvu
  have huu : planeDot S.u S.u = 1 := r_planeDot_u_u S
  have hFT : ∀ t, deriv S.F.γ t = euclideanLength (deriv S.F.γ t) • S.T t := fun t =>
    (CornerRounding.X_smul_normalize (S.F.regular t)).symm
  have hL₁ : 0 < euclideanLength (deriv S.F.γ cf.s₁) := euclideanLength_pos (S.F.regular _)
  have hL₂ : 0 < euclideanLength (deriv S.F.γ cf.s₂) := euclideanLength_pos (S.F.regular _)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hFT, cf.T_minus, g_planeDot_smul_left, r_planeDot_add_left, g_planeDot_smul_left,
      g_planeDot_smul_left, hvv, huv]
    nlinarith [mul_pos hL₁ cf.a_pos]
  · rw [hFT, cf.T_minus, g_planeDot_smul_left, r_planeDot_add_left, g_planeDot_smul_left,
      g_planeDot_smul_left, hvu, huu]
    nlinarith [mul_pos hL₁ cf.b_pos]
  · rw [hFT, cf.T_plus, g_planeDot_smul_left, r_planeDot_add_left, r_planeDot_neg_left,
      g_planeDot_smul_left, g_planeDot_smul_left, hvv, huv]
    nlinarith [mul_pos hL₂ cf.c_pos]
  · rw [hFT, cf.T_plus, g_planeDot_smul_left, r_planeDot_add_left, r_planeDot_neg_left,
      g_planeDot_smul_left, g_planeDot_smul_left, hvu, huu]
    nlinarith [mul_pos hL₂ cf.d_pos]

/-- a vector within `ε` of `w` keeps the sign of `⟨w, z⟩` when `8ε` is below the margin -/
theorem r_collar_sign {w w' z : Plane} {m ε : ℝ} (hz : euclideanLength z = 1) (hb : ‖w' - w‖ ≤ ε)
    (hm : m / 2 < planeDot w z) (hε : 8 * ε ≤ m) : 0 < planeDot w' z := by
  have h1 := r_abs_planeDot_le (w' - w) z hz
  rw [r_planeDot_sub_left] at h1
  have := abs_le.mp h1
  linarith [norm_nonneg (w' - w)]
theorem r_collar_sign_neg {w w' z : Plane} {m ε : ℝ} (hz : euclideanLength z = 1)
    (hb : ‖w' - w‖ ≤ ε) (hm : planeDot w z < m / 2) (hε : 8 * ε ≤ -m) : planeDot w' z < 0 := by
  have h1 := r_abs_planeDot_le (w' - w) z hz
  rw [r_planeDot_sub_left] at h1
  have := abs_le.mp h1
  linarith [norm_nonneg (w' - w)]

/-- a convex combination of two numbers above `c` is above `c` -/
theorem r_convex_gt {a b c θ : ℝ} (ha : c < a) (hb : c < b) (hθ : θ ∈ Icc (0:ℝ) 1) :
    c < a + θ * (b - a) := by
  rcases le_or_gt θ (1 / 2) with h | h
  · nlinarith [mul_nonneg hθ.1 (sub_nonneg.mpr hb.le),
      mul_nonneg (by linarith : (0:ℝ) ≤ 1 / 2 - θ) (sub_nonneg.mpr ha.le)]
  · nlinarith [mul_nonneg (sub_nonneg.mpr hθ.2) (sub_nonneg.mpr ha.le),
      mul_nonneg (by linarith : (0:ℝ) ≤ θ - 1 / 2) (sub_nonneg.mpr hb.le)]

/-- a curve with `⟨N', u⟩ > 0` on an interval is injective there (`⟨N − p, u⟩` strictly increases) -/
theorem r_inj_of_dot_pos {N : ℝ → Plane} (hNd : Differentiable ℝ N) {a b : ℝ}
    (hpos : ∀ t ∈ Icc a b, 0 < planeDot (deriv N t) S.u) :
    ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, N s = N t → s = t := by
  have hη' : ∀ t, HasDerivAt (fun t => planeDot (N t - S.p) S.u) (planeDot (deriv N t) S.u) t :=
    fun t => r_hasDerivAt_planeDot ((hNd t).hasDerivAt.sub_const S.p) S.u
  have hmono : StrictMonoOn (fun t => planeDot (N t - S.p) S.u) (Icc a b) :=
    r_strictMonoOn_of_deriv_pos (fun t => (hη' t).differentiableAt) fun t ht => by
      rw [(hη' t).deriv]; exact hpos t ht
  intro s hs t ht h
  exact hmono.injOn hs ht (by show planeDot (N s - S.p) S.u = planeDot (N t - S.p) S.u; rw [h])

/-- (ii) on the window from the sign of `⟨N', v⟩`: never `u`, and `−u` exactly at `q₀` -/
theorem r_glued_tangent {N : ℝ → Plane} (hNreg : ∀ t, deriv N t ≠ 0) {s₁ s₂ q₀ : ℝ}
    (hq₀ : q₀ ∈ Icc s₁ s₂)
    (hbefore : ∀ t ∈ Icc s₁ s₂, t < q₀ → 0 < planeDot (deriv N t) (vDir S))
    (hafter : ∀ t ∈ Icc s₁ s₂, q₀ < t → planeDot (deriv N t) (vDir S) < 0)
    (hq₀v : planeDot (deriv N q₀) (vDir S) = 0) (hq₀u : planeDot (deriv N q₀) S.u < 0) :
    (∀ t ∈ Icc s₁ s₂, normalize (deriv N t) ≠ S.u) ∧
    (∃! t : ℝ, t ∈ Icc s₁ s₂ ∧ normalize (deriv N t) = -S.u) := by
  have huv : planeDot S.u (vDir S) = 0 := by rw [r_planeDot_comm]; exact planeDot_vDir_u S
  have huu : planeDot S.u S.u = 1 := r_planeDot_u_u S
  have hv_zero : ∀ t ∈ Icc s₁ s₂, planeDot (deriv N t) (vDir S) = 0 → t = q₀ := by
    intro t ht h0
    rcases lt_trichotomy t q₀ with h | h | h
    · exact absurd h0 (hbefore t ht h).ne'
    · exact h
    · exact absurd h0 (hafter t ht h).ne
  refine ⟨?_, ?_⟩
  · intro t ht h
    have h0 : planeDot (deriv N t) (vDir S) = 0 := by
      have := r_planeDot_normalize' (deriv N t) (vDir S)
      rw [h, huv] at this
      rcases mul_eq_zero.mp this.symm with h1 | h1
      · exact absurd h1 (inv_ne_zero (euclideanLength_pos (hNreg t)).ne')
      · exact h1
    have hq := hv_zero t ht h0
    subst hq
    have hu' : 0 < planeDot (deriv N t) S.u := by
      have := r_planeDot_normalize' (deriv N t) S.u
      rw [h, huu] at this
      have hinv : 0 < (euclideanLength (deriv N t))⁻¹ :=
        inv_pos.mpr (euclideanLength_pos (hNreg t))
      nlinarith
    linarith
  · have hneg_u : normalize (deriv N q₀) = -S.u := by
      have e : deriv N q₀ = planeDot (deriv N q₀) S.u • S.u := by
        conv_lhs => rw [r_expand S (deriv N q₀)]
        rw [hq₀v, zero_smul, zero_add]
      rw [e, ← neg_smul_neg, normalize_smul_of_pos (neg_pos.mpr hq₀u), r_normalize_neg_u S]
    refine ⟨q₀, ⟨hq₀, hneg_u⟩, fun t ⟨ht, h⟩ => ?_⟩
    apply hv_zero t ht
    have := r_planeDot_normalize' (deriv N t) (vDir S)
    rw [h, r_planeDot_neg_left, huv, neg_zero] at this
    rcases mul_eq_zero.mp this.symm with h1 | h1
    · exact absurd h1 (inv_ne_zero (euclideanLength_pos (hNreg t)).ne')
    · exact h1

/-- (iv) on the window: a lift of the new tangent whose increment is the old one minus `2π`
(sm-3:4226-4244, read directly on the sign of `⟨N', v⟩`: the angle relative to `u` starts in
`(−π/2, 0)`, stays in `(−π, 0)` before `q₀`, equals `−π` at `q₀`, stays in `(−2π, −π)` after,
and ends congruent to `θrel(s₂) ∈ (0, π/2)` modulo `2π`) -/
theorem r_glued_lift {α' β' : ℝ} (hα : S.α ≤ α') (hβ : β' ≤ S.β)
    (hθ : ∀ t ∈ Icc α' β', |θrel S t| < Real.pi / 2) {r : ℝ} (cf : CutFit S α' β' r)
    {N : ℝ → Plane} (hNs : ContDiff ℝ ∞ N) (hNreg : ∀ t, deriv N t ≠ 0)
    (hN'₁ : deriv N cf.s₁ = deriv S.F.γ cf.s₁) (hN'₂ : deriv N cf.s₂ = deriv S.F.γ cf.s₂)
    {q₀ : ℝ} (hq₀ : q₀ ∈ Ioo cf.s₁ cf.s₂)
    (hbefore : ∀ t ∈ Icc cf.s₁ cf.s₂, t < q₀ → 0 < planeDot (deriv N t) (vDir S))
    (hafter : ∀ t ∈ Icc cf.s₁ cf.s₂, q₀ < t → planeDot (deriv N t) (vDir S) < 0)
    (hq₀v : planeDot (deriv N q₀) (vDir S) = 0) (hq₀u : planeDot (deriv N q₀) S.u < 0) :
    ∃ θ' : ℝ → ℝ, IsLiftOn (fun t => normalize (deriv N t)) θ' cf.s₁ cf.s₂ ∧
      θ' cf.s₂ - θ' cf.s₁ = (S.θ cf.s₂ - S.θ cf.s₁) - 2 * Real.pi := by
  have hs : cf.s₁ < cf.s₂ := cf.s₁_lt.trans cf.lt_s₂
  have hq₀Icc : q₀ ∈ Icc cf.s₁ cf.s₂ := Ioo_subset_Icc_self hq₀
  have hN'c : Continuous (deriv N) := hNs.continuous_deriv (by exact_mod_cast le_top)
  have hT'c : Continuous (fun t => normalize (deriv N t)) := continuous_normalize_comp hN'c hNreg
  have hT'1 : ∀ t, euclideanLength (normalize (deriv N t)) = 1 := fun t =>
    euclideanLength_normalize (hNreg t)
  obtain ⟨Θ, hΘc, hΘ⟩ := exists_lift_of_unit hT'c hT'1
  have hlift0 : ∀ t, normalize (deriv N t) = (Real.cos (Θ t), Real.sin (Θ t)) := fun t => hΘ t
  have hs₁mem : cf.s₁ ∈ Icc S.α S.β :=
    ⟨hα.trans cf.α'_le, cf.s₁_lt.le.trans (cf.lt_s₂.le.trans (cf.le_β'.trans hβ))⟩
  have hs₂mem : cf.s₂ ∈ Icc S.α S.β :=
    ⟨hα.trans (cf.α'_le.trans (cf.s₁_lt.le.trans cf.lt_s₂.le)), cf.le_β'.trans hβ⟩
  have hθ₁ : S.T cf.s₁ = (Real.cos (S.θ cf.s₁), Real.sin (S.θ cf.s₁)) := S.lift.2 cf.s₁ hs₁mem
  have hθ₂ : S.T cf.s₂ = (Real.cos (S.θ cf.s₂), Real.sin (S.θ cf.s₂)) := S.lift.2 cf.s₂ hs₂mem
  have hT₁ : normalize (deriv N cf.s₁) = S.T cf.s₁ := by rw [hN'₁]; rfl
  have hT₂ : normalize (deriv N cf.s₂) = S.T cf.s₂ := by rw [hN'₂]; rfl
  obtain ⟨k, hk⟩ : ∃ k : ℤ, Θ cf.s₁ - S.θ cf.s₁ = 2 * Real.pi * k := by
    have h := hlift0 cf.s₁
    rw [hT₁, hθ₁] at h
    exact Real.Angle.angle_eq_iff_two_pi_dvd_sub.mp
      (Real.Angle.cos_sin_inj (congrArg Prod.fst h).symm (congrArg Prod.snd h).symm)
  obtain ⟨θ', hθ'def⟩ : ∃ θ' : ℝ → ℝ, θ' = fun t => Θ t - k * (2 * Real.pi) := ⟨_, rfl⟩
  have hθ't : ∀ t, θ' t = Θ t - k * (2 * Real.pi) := fun t => by rw [hθ'def]
  have hθ'c : Continuous θ' := by rw [hθ'def]; fun_prop
  have hlift' : ∀ t, normalize (deriv N t) = (Real.cos (θ' t), Real.sin (θ' t)) := fun t => by
    rw [hθ't, Real.cos_sub_int_mul_two_pi, Real.sin_sub_int_mul_two_pi]; exact hlift0 t
  have hlift : IsLiftOn (fun t => normalize (deriv N t)) θ' cf.s₁ cf.s₂ :=
    ⟨hθ'c.continuousOn, fun t _ => hlift' t⟩
  have hθ'₁ : θ' cf.s₁ = S.θ cf.s₁ := by rw [hθ't]; linarith
  obtain ⟨k', hk'⟩ : ∃ k' : ℤ, θ' cf.s₂ - S.θ cf.s₂ = 2 * Real.pi * k' := by
    have h := hlift' cf.s₂
    rw [hT₂, hθ₂] at h
    exact Real.Angle.angle_eq_iff_two_pi_dvd_sub.mp
      (Real.Angle.cos_sin_inj (congrArg Prod.fst h).symm (congrArg Prod.snd h).symm)
  -- the frame in terms of the angle `θ₀ = θ(t₀)` of `u`
  have hu_eq : S.u = (Real.cos (S.θ S.t₀), Real.sin (S.θ S.t₀)) := by
    rw [← S.tangent_at]; exact S.lift.2 S.t₀ ⟨S.α_lt.le, S.lt_β.le⟩
  have hv_eq : vDir S = (Real.sin (S.θ S.t₀), -Real.cos (S.θ S.t₀)) := by
    simp only [vDir, J, hu_eq, Prod.neg_mk, neg_neg]
  obtain ⟨Θr, hΘrdef⟩ : ∃ Θr : ℝ → ℝ, Θr = fun t => θ' t - S.θ S.t₀ := ⟨_, rfl⟩
  have hΘrt : ∀ t, Θr t = θ' t - S.θ S.t₀ := fun t => by rw [hΘrdef]
  have hΘrc : Continuous Θr := by rw [hΘrdef]; exact hθ'c.sub continuous_const
  have hsinΘ : ∀ t, Real.sin (Θr t) = -planeDot (normalize (deriv N t)) (vDir S) := by
    intro t; rw [hΘrt, hlift' t, hv_eq, Real.sin_sub]; simp only [planeDot]; ring
  have hcosΘ : ∀ t, Real.cos (Θr t) = planeDot (normalize (deriv N t)) S.u := by
    intro t; rw [hΘrt, hlift' t, hu_eq, Real.cos_sub]; simp only [planeDot]
  have hsin_before : ∀ t ∈ Icc cf.s₁ cf.s₂, t < q₀ → Real.sin (Θr t) < 0 := fun t ht h => by
    rw [hsinΘ, r_planeDot_normalize', neg_lt_zero]
    exact mul_pos (inv_pos.mpr (euclideanLength_pos (hNreg t))) (hbefore t ht h)
  have hsin_after : ∀ t ∈ Icc cf.s₁ cf.s₂, q₀ < t → 0 < Real.sin (Θr t) := fun t ht h => by
    rw [hsinΘ, r_planeDot_normalize', neg_pos]
    exact mul_neg_of_pos_of_neg (inv_pos.mpr (euclideanLength_pos (hNreg t))) (hafter t ht h)
  have hcos_q₀ : Real.cos (Θr q₀) < 0 := by
    rw [hcosΘ, r_planeDot_normalize']
    exact mul_neg_of_pos_of_neg (inv_pos.mpr (euclideanLength_pos (hNreg _))) hq₀u
  -- the start: `Θr s₁ = θrel s₁ ∈ (−π/2, 0)`
  have hΘr₁ : -(Real.pi / 2) < Θr cf.s₁ ∧ Θr cf.s₁ < 0 := by
    have habs : |Θr cf.s₁| < Real.pi / 2 := by
      rw [hΘrt, hθ'₁]
      exact hθ cf.s₁ ⟨cf.α'_le, cf.s₁_lt.le.trans (cf.lt_s₂.le.trans cf.le_β')⟩
    have hsin := hsin_before cf.s₁ ⟨le_rfl, hs.le⟩ hq₀.1
    refine ⟨(abs_lt.mp habs).1, ?_⟩
    by_contra h; push Not at h
    have := Real.sin_nonneg_of_nonneg_of_le_pi h
      (by linarith [(abs_lt.mp habs).2, Real.pi_pos])
    linarith
  -- step 1: before `q₀` the angle stays in `(−π, 0)`
  have hstep1 : ∀ t ∈ Ico cf.s₁ q₀, -Real.pi < Θr t ∧ Θr t < 0 := by
    intro t ht
    have hsin : ∀ t' ∈ Icc cf.s₁ t, Real.sin (Θr t') < 0 := fun t' ht' =>
      hsin_before t' ⟨ht'.1, by linarith [ht'.2, ht.2, hq₀Icc.2]⟩ (ht'.2.trans_lt ht.2)
    constructor
    · by_contra h; push Not at h
      have hmem : -Real.pi ∈ Icc (Θr t) (Θr cf.s₁) := ⟨h, by linarith [hΘr₁.1, Real.pi_pos]⟩
      obtain ⟨t', ht', he⟩ := intermediate_value_Icc' ht.1 hΘrc.continuousOn hmem
      have := hsin t' ht'; rw [he, Real.sin_neg, Real.sin_pi] at this; linarith
    · by_contra h; push Not at h
      have hmem : (0:ℝ) ∈ Icc (Θr cf.s₁) (Θr t) := ⟨hΘr₁.2.le, h⟩
      obtain ⟨t', ht', he⟩ := intermediate_value_Icc ht.1 hΘrc.continuousOn hmem
      have := hsin t' ht'; rw [he, Real.sin_zero] at this; linarith
  -- step 2: `Θr q₀ = −π`
  have hstep2 : Θr q₀ = -Real.pi := by
    have hmem : -Real.pi ≤ Θr q₀ ∧ Θr q₀ ≤ 0 := by
      constructor
      · by_contra h; push Not at h
        have hm : -Real.pi ∈ Icc (Θr q₀) (Θr cf.s₁) := ⟨h.le, by linarith [hΘr₁.1, Real.pi_pos]⟩
        obtain ⟨t', ht', he⟩ := intermediate_value_Icc' hq₀Icc.1 hΘrc.continuousOn hm
        have hne : t' ≠ q₀ := fun heq => by rw [heq] at he; linarith
        have := hsin_before t' ⟨ht'.1, ht'.2.trans hq₀Icc.2⟩ (lt_of_le_of_ne ht'.2 hne)
        rw [he, Real.sin_neg, Real.sin_pi] at this; linarith
      · by_contra h; push Not at h
        have hm : (0:ℝ) ∈ Icc (Θr cf.s₁) (Θr q₀) := ⟨hΘr₁.2.le, h.le⟩
        obtain ⟨t', ht', he⟩ := intermediate_value_Icc hq₀Icc.1 hΘrc.continuousOn hm
        have hne : t' ≠ q₀ := fun heq => by rw [heq] at he; linarith
        have := hsin_before t' ⟨ht'.1, ht'.2.trans hq₀Icc.2⟩ (lt_of_le_of_ne ht'.2 hne)
        rw [he, Real.sin_zero] at this; linarith
    have hsin0 : Real.sin (Θr q₀) = 0 := by
      rw [hsinΘ, r_planeDot_normalize', hq₀v, mul_zero, neg_zero]
    rcases lt_or_eq_of_le hmem.1 with hlt | heq
    · exfalso
      rcases lt_or_eq_of_le hmem.2 with hlt2 | heq2
      · have := Real.sin_neg_of_neg_of_neg_pi_lt hlt2 hlt; linarith
      · rw [heq2, Real.cos_zero] at hcos_q₀; linarith
    · exact heq.symm
  -- step 3: after `q₀` the angle stays in `(−2π, −π)`
  have hstep3 : ∀ t ∈ Ioc q₀ cf.s₂, -(2 * Real.pi) < Θr t ∧ Θr t < -Real.pi := by
    intro t ht
    have hsin : ∀ t' ∈ Ioc q₀ t, 0 < Real.sin (Θr t') := fun t' ht' =>
      hsin_after t' ⟨by linarith [hq₀Icc.1, ht'.1], ht'.2.trans ht.2⟩ ht'.1
    have hsint := hsin t ⟨ht.1, le_rfl⟩
    constructor
    · by_contra h; push Not at h
      have hm : -(2 * Real.pi) ∈ Icc (Θr t) (Θr q₀) :=
        ⟨h, by rw [hstep2]; linarith [Real.pi_pos]⟩
      obtain ⟨t', ht', he⟩ := intermediate_value_Icc' ht.1.le hΘrc.continuousOn hm
      have hne : t' ≠ q₀ := fun heq => by rw [heq, hstep2] at he; linarith [Real.pi_pos]
      have := hsin t' ⟨lt_of_le_of_ne ht'.1 (Ne.symm hne), ht'.2⟩
      rw [he, Real.sin_neg, Real.sin_two_pi] at this; linarith
    · rcases lt_trichotomy (Θr t) (-Real.pi) with h | h | h
      · exact h
      · exfalso; rw [h, Real.sin_neg, Real.sin_pi] at hsint; linarith
      · exfalso
        rcases lt_or_ge (Θr t) 0 with h2 | h2
        · have := Real.sin_neg_of_neg_of_neg_pi_lt h2 h; linarith
        · have hm : -(Real.pi / 2) ∈ Icc (Θr q₀) (Θr t) :=
            ⟨by rw [hstep2]; linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
          obtain ⟨t', ht', he⟩ := intermediate_value_Icc ht.1.le hΘrc.continuousOn hm
          have hne : t' ≠ q₀ := fun heq => by rw [heq, hstep2] at he; linarith [Real.pi_pos]
          have := hsin t' ⟨lt_of_le_of_ne ht'.1 (Ne.symm hne), ht'.2⟩
          rw [he, Real.sin_neg, Real.sin_pi_div_two] at this; linarith
  -- step 4: the end value and the increment
  have hΘr₂ := hstep3 cf.s₂ ⟨hq₀.2, le_rfl⟩
  have hθrel₂ : 0 < θrel S cf.s₂ ∧ θrel S cf.s₂ < Real.pi / 2 := by
    have habs : |θrel S cf.s₂| < Real.pi / 2 :=
      hθ cf.s₂ ⟨cf.α'_le.trans (cf.s₁_lt.le.trans cf.lt_s₂.le), cf.le_β'⟩
    have hsin : 0 < Real.sin (θrel S cf.s₂) := by
      have h := hsin_after cf.s₂ ⟨hs.le, le_rfl⟩ hq₀.2
      have e : Θr cf.s₂ = θrel S cf.s₂ + k' * (2 * Real.pi) := by
        rw [hΘrt, θrel]; linarith
      rw [e, Real.sin_add_int_mul_two_pi] at h; exact h
    refine ⟨?_, (abs_lt.mp habs).2⟩
    by_contra h; push Not at h
    have := Real.sin_nonneg_of_nonneg_of_le_pi (by linarith : 0 ≤ -θrel S cf.s₂)
      (by linarith [(abs_lt.mp habs).1, Real.pi_pos])
    rw [Real.sin_neg] at this
    linarith
  have hk'val : k' = -1 := by
    have e : Θr cf.s₂ = θrel S cf.s₂ + 2 * Real.pi * k' := by rw [hΘrt, θrel]; linarith
    have h1 : (k' : ℝ) < 0 := by nlinarith [Real.pi_pos, hΘr₂.2, hθrel₂.1]
    have h2 : (-2 : ℝ) < k' := by nlinarith [Real.pi_pos, hΘr₂.1, hθrel₂.2]
    have h1' : k' < 0 := by exact_mod_cast h1
    have h2' : -2 < k' := by exact_mod_cast h2
    omega
  refine ⟨θ', hlift, ?_⟩
  rw [hk'val] at hk'; push_cast at hk'
  rw [hθ'₁]; linarith

/-- the double points of the window: both parameters in an end zone (injective), both in the
model part (the model's double point), or one on a collar (separated by distance) -/
theorem r_glued_double {N G : ℝ → Plane} {s₁ s₂ lam lam₀ q₁ q₂ : ℝ} {pm pp : Plane}
    {ε dm dp ℓ' : ℝ} (hε : 0 < ε) (hlam_lam₀ : lam ≤ lam₀)
    (hq₁₂ : q₁ < q₂)
    (hinj₁ : ∀ s ∈ Icc s₁ (s₁ + lam₀), ∀ t ∈ Icc s₁ (s₁ + lam₀), N s = N t → s = t)
    (hinj₂ : ∀ s ∈ Icc (s₂ - lam₀) s₂, ∀ t ∈ Icc (s₂ - lam₀) s₂, N s = N t → s = t)
    (hNmid : ∀ t ∈ Icc (s₁ + lam) (s₂ - lam), N t = G t)
    (hpos₁ : ∀ t ∈ Icc s₁ (s₁ + lam), ‖N t - pm‖ < 2 * ε)
    (hpos₂ : ∀ t ∈ Icc (s₂ - lam) s₂, ‖N t - pp‖ < 2 * ε)
    (hdm : ∀ t ∈ Icc (s₁ + lam₀) s₂, dm ≤ ‖G t - pm‖) (hε₅ : 8 * ε ≤ dm)
    (hdp : ∀ t ∈ Icc s₁ (s₂ - lam₀), dp ≤ ‖G t - pp‖) (hε₆ : 8 * ε ≤ dp)
    (hℓ' : ℓ' = ‖pp - pm‖) (hε₇ : 8 * ε ≤ ℓ')
    (hGinj : ∀ s ∈ Icc s₁ s₂, ∀ t ∈ Icc s₁ s₂, s ≠ t → G s = G t →
      (s = q₁ ∧ t = q₂) ∨ (s = q₂ ∧ t = q₁)) :
    ∀ s ∈ Icc s₁ s₂, ∀ t ∈ Icc s₁ s₂, s ≠ t → N s = N t →
      (s = q₁ ∧ t = q₂) ∨ (s = q₂ ∧ t = q₁) := by
  have hkey : ∀ s ∈ Icc s₁ s₂, ∀ t ∈ Icc s₁ s₂, s < t → N s = N t → s = q₁ ∧ t = q₂ := by
    intro s hs' t ht hst hN
    by_cases hA : t ≤ s₁ + lam₀
    · exact absurd (hinj₁ s ⟨hs'.1, by linarith⟩ t ⟨ht.1, hA⟩ hN) hst.ne
    by_cases hB : s₂ - lam₀ ≤ s
    · exact absurd (hinj₂ s ⟨hB, hs'.2⟩ t ⟨by linarith, ht.2⟩ hN) hst.ne
    push Not at hA hB
    by_cases hC : s < s₁ + lam
    · exfalso
      have hsN := hpos₁ s ⟨hs'.1, hC.le⟩
      by_cases hD : t ≤ s₂ - lam
      · have hNt : N t = G t := hNmid t ⟨by linarith, hD⟩
        have := hdm t ⟨hA.le, ht.2⟩
        rw [← hNt, ← hN] at this
        linarith
      · push Not at hD
        have htN := hpos₂ t ⟨hD.le, ht.2⟩
        have : ℓ' ≤ ‖N t - pp‖ + ‖N s - pm‖ := by
          calc ℓ' = ‖(pp - N t) + (N s - pm)‖ := by rw [hℓ']; congr 1; rw [hN]; abel
            _ ≤ ‖pp - N t‖ + ‖N s - pm‖ := norm_add_le _ _
            _ = ‖N t - pp‖ + ‖N s - pm‖ := by rw [norm_sub_rev]
        linarith
    · push Not at hC
      have hsN : N s = G s := hNmid s ⟨hC, by linarith⟩
      by_cases hD : t ≤ s₂ - lam
      · have htN : N t = G t := hNmid t ⟨by linarith, hD⟩
        rw [hsN, htN] at hN
        rcases hGinj s hs' t ht hst.ne hN with h | h
        · exact h
        · exfalso; linarith [h.1, h.2]
      · push Not at hD
        exfalso
        have htN := hpos₂ t ⟨hD.le, ht.2⟩
        have := hdp s ⟨hs'.1, hB.le⟩
        rw [← hsN, hN] at this
        linarith
  intro s hs' t ht hst hN
  rcases lt_or_gt_of_ne hst with h | h
  · exact Or.inl (hkey s hs' t ht h hN)
  · obtain ⟨h1, h2⟩ := hkey t ht s hs' h hN.symm; exact Or.inr ⟨h2, h1⟩

/-- the window lies in the disc, and its open part is off the rest of the curve: every point of
the window has `ξ > ξ(s₁)` (a convex combination of the old arc and the inserted arc, both
strictly above the cut level), while the retained tails in the disc have `ξ ≤ ξ(s₁)` -/
theorem r_glued_off {α' β' : ℝ} (hα : S.α ≤ α') (hβ : β' ≤ S.β)
    (hθ : ∀ t ∈ Icc α' β', |θrel S t| < Real.pi / 2) {r : ℝ}
    (hmeets : ∀ t : ℝ, S.F.γ t ∈ disc S r → ∃ n : ℤ, t + n ∈ Icc α' β') (cf : CutFit S α' β' r)
    {N G : ℝ → Plane} (hGdisc : ∀ t ∈ Icc cf.s₁ cf.s₂, G t ∈ disc S r)
    (hGexc : ∀ t ∈ Ioo cf.s₁ cf.s₂, ξ S cf.s₁ < planeDot (G t - S.p) (vDir S))
    (hNconv : ∀ t, ∃ θ : ℝ, θ ∈ Icc (0:ℝ) 1 ∧ N t = S.F.γ t + θ • (G t - S.F.γ t)) :
    (∀ t ∈ Icc cf.s₁ cf.s₂, N t ∈ disc S r) ∧
    ∀ s ∈ Ioo cf.s₁ cf.s₂, ∀ t : ℝ, OffWindow cf.s₁ cf.s₂ t → N s ≠ S.F.γ t := by
  have hNdisc : ∀ t ∈ Icc cf.s₁ cf.s₂, N t ∈ disc S r := fun t ht => by
    obtain ⟨θc, hθc, hNt⟩ := hNconv t
    rw [hNt]; exact r_disc_convex S (cf.old_in_disc t ht) (hGdisc t ht) hθc
  refine ⟨hNdisc, ?_⟩
  have hξF : ∀ s ∈ Ioo cf.s₁ cf.s₂, ξ S cf.s₁ < ξ S s := by
    intro s hs'
    rcases le_or_gt s S.t₀ with h | h
    · exact g_ξ_strictMonoOn S hα (fun t ht => hθ t ⟨ht.1, ht.2.trans (cf.lt_s₂.trans_le cf.le_β').le⟩) ⟨cf.α'_le, cf.s₁_lt.le⟩
        ⟨by linarith [cf.α'_le, hs'.1], h⟩ hs'.1
    · rw [cf.ξ_eq]
      exact g_ξ_strictAntiOn S hβ (fun t ht => hθ t ⟨(cf.α'_le.trans_lt cf.s₁_lt).le.trans ht.1, ht.2⟩) ⟨h.le, by linarith [cf.le_β', hs'.2]⟩
        ⟨cf.lt_s₂.le, cf.le_β'⟩ hs'.2
  have hξN : ∀ s ∈ Ioo cf.s₁ cf.s₂, ξ S cf.s₁ < planeDot (N s - S.p) (vDir S) := by
    intro s hs'
    obtain ⟨θc, hθc, hNs'⟩ := hNconv s
    have h1 : ξ S cf.s₁ < planeDot (S.F.γ s - S.p) (vDir S) := hξF s hs'
    have h2 := hGexc s hs'
    have e : N s - S.p = (S.F.γ s - S.p) + θc • ((G s - S.p) - (S.F.γ s - S.p)) := by
      rw [hNs', sub_sub_sub_cancel_right]; abel
    rw [e, r_planeDot_add_left, g_planeDot_smul_left,
      r_planeDot_sub_left (G s - S.p) (S.F.γ s - S.p) (vDir S)]
    exact r_convex_gt h1 h2 hθc
  intro s hs' t ht hN
  by_cases hin : S.F.γ t ∈ disc S r
  · obtain ⟨n, hn⟩ := hmeets t hin
    have hnot := ht n
    have hper : S.F.γ (t + n) = S.F.γ t := S.F.eq_add_int n t
    have hle : ξ S (t + n) ≤ ξ S cf.s₁ := by
      rcases le_or_gt (t + n) cf.s₁ with h | h
      · exact (g_ξ_strictMonoOn S hα (fun t ht => hθ t ⟨ht.1, ht.2.trans (cf.lt_s₂.trans_le cf.le_β').le⟩)).monotoneOn ⟨hn.1, by linarith [cf.s₁_lt]⟩
          ⟨cf.α'_le, cf.s₁_lt.le⟩ h
      · have h2 : cf.s₂ ≤ t + n := by
          by_contra h2; push Not at h2; exact hnot ⟨h, h2⟩
        rw [cf.ξ_eq]
        exact (g_ξ_strictAntiOn S hβ (fun t ht => hθ t ⟨(cf.α'_le.trans_lt cf.s₁_lt).le.trans ht.1, ht.2⟩)).antitoneOn ⟨cf.lt_s₂.le, cf.le_β'⟩
          ⟨by linarith [cf.lt_s₂], hn.2⟩ h2
    have := hξN s hs'
    rw [hN] at this
    have e : planeDot (S.F.γ t - S.p) (vDir S) = ξ S (t + n) := by
      show _ = planeDot (S.F.γ (t + n) - S.p) (vDir S); rw [hper]
    linarith
  · have hNin := hNdisc s (Ioo_subset_Icc_self hs')
    rw [hN] at hNin; exact hin hNin

/-- "The replacement, and why the curve stays C^∞ regular" (sm-3:4056-4079): at the cuts and fit `cf`,
the new arc — old arc to the first collar, the collar graph, the inserted arc, the second collar, the
old arc — admits a `C^∞` regular parametrisation `N` on `[s₁, s₂]` agreeing with `F` off the window
(the collars are graphs over `η`, parametrised through `η ∘ F`; the model is reparametrised by a
smooth monotone change of variable equal to `η ∘ F` near its ends).  Packaged with the facts of
Units M, F, G, H read on `N`: inside the disc (collar points lie on the `v`-segments between a point of
the removed arc and a point of the inserted arc, both in the convex disc), the model's double point
`q₁ < q₂` (later branch over, negative), no other double point of the window, the open window off the
rest of the curve (transverse excess `ξ > ξ(s₁)` against the tails' `ξ < ξ(s₁)`), (ii) on the window,
the compatible lift with increment the old one minus `2π` (`glplus_increment_sub_invariant`). -/
theorem exists_glued_arc {α' β' : ℝ} (hα : S.α ≤ α') (hα' : α' < S.t₀) (hβ' : S.t₀ < β') (hβ : β' ≤ S.β)
    (hθ : ∀ t ∈ Icc α' β', |θrel S t| < Real.pi / 2) {r : ℝ} (hr : 0 < r)
    (hmeets : ∀ t : ℝ, S.F.γ t ∈ disc S r → ∃ n : ℤ, t + n ∈ Icc α' β') (cf : CutFit S α' β' r) :
    ∃ N : ℝ → Plane, ∃ q₁ q₂ : ℝ, ∃ θ' : ℝ → ℝ,
      ContDiff ℝ ∞ N ∧ (∀ t, deriv N t ≠ 0) ∧
      (∀ t, t ≤ cf.s₁ → N t = S.F.γ t) ∧ (∀ t, cf.s₂ ≤ t → N t = S.F.γ t) ∧
      (∀ t ∈ Icc cf.s₁ cf.s₂, N t ∈ disc S r) ∧
      q₁ ∈ Ioo cf.s₁ cf.s₂ ∧ q₂ ∈ Ioo cf.s₁ cf.s₂ ∧ q₁ < q₂ ∧ N q₁ = N q₂ ∧
      det (deriv N q₂) (deriv N q₁) < 0 ∧
      (∀ s ∈ Icc cf.s₁ cf.s₂, ∀ t ∈ Icc cf.s₁ cf.s₂, s ≠ t → N s = N t →
        (s = q₁ ∧ t = q₂) ∨ (s = q₂ ∧ t = q₁)) ∧
      (∀ s ∈ Ioo cf.s₁ cf.s₂, ∀ t : ℝ, OffWindow cf.s₁ cf.s₂ t → N s ≠ S.F.γ t) ∧
      (∀ t ∈ Icc cf.s₁ cf.s₂, normalize (deriv N t) ≠ S.u) ∧
      (∃! t : ℝ, t ∈ Icc cf.s₁ cf.s₂ ∧ normalize (deriv N t) = -S.u) ∧
      IsLiftOn (fun t => normalize (deriv N t)) θ' cf.s₁ cf.s₂ ∧
      θ' cf.s₂ - θ' cf.s₁ = (S.θ cf.s₂ - S.θ cf.s₁) - 2 * Real.pi := by
  -- ## 0. the frame and the velocities at the cuts
  have hs : cf.s₁ < cf.s₂ := cf.s₁_lt.trans cf.lt_s₂
  have hFs : ContDiff ℝ ∞ S.F.γ := S.F.smooth
  have hFc : Continuous S.F.γ := S.F.continuous
  have hF'c : Continuous (deriv S.F.γ) := S.F.continuous_deriv
  have hv1 : euclideanLength (vDir S) = 1 := r_euclideanLength_vDir S
  have hu1 : euclideanLength S.u = 1 := S.u_unit
  obtain ⟨hm₁, hm₂, hm₃, hm₄⟩ := r_cut_velocity S cf
  -- ## 1. the model arc
  obtain ⟨G, q₀, q₁, q₂, hGs, hG₁, hG₂, hG'₁, hG'₂, hGdisc, hGexc, hq₁, hq₂, hq₁₀, hq₀₂, hGq, hGdet,
    hGinj, hGv_neg, hGv_pos, hGq₀v, hGq₀u, hG'ne⟩ := r_exists_model S cf
  have hGc : Continuous G := hGs.continuous
  have hG'c : Continuous (deriv G) := hGs.continuous_deriv (by exact_mod_cast le_top)
  have hq₀Ioo : q₀ ∈ Ioo cf.s₁ cf.s₂ := ⟨hq₁.1.trans hq₁₀, hq₀₂.trans hq₂.2⟩
  have hq₀Icc : q₀ ∈ Icc cf.s₁ cf.s₂ := Ioo_subset_Icc_self hq₀Ioo
  -- ## 2. the zone `lam₀`
  have hev₁ : ∀ᶠ t in nhds cf.s₁,
      planeDot (deriv S.F.γ cf.s₁) (vDir S) / 2 < planeDot (deriv S.F.γ t) (vDir S) ∧
      planeDot (deriv S.F.γ cf.s₁) S.u / 2 < planeDot (deriv S.F.γ t) S.u ∧
      0 < planeDot (deriv G t) S.u := by
    refine Filter.Eventually.and ?_ (Filter.Eventually.and ?_ ?_)
    · exact continuousAt_const.eventually_lt (r_continuous_planeDot hF'c _).continuousAt
        (half_lt_self hm₁)
    · exact continuousAt_const.eventually_lt (r_continuous_planeDot hF'c _).continuousAt
        (half_lt_self hm₂)
    · exact continuousAt_const.eventually_lt (r_continuous_planeDot hG'c _).continuousAt
        (by rw [hG'₁]; exact hm₂)
  have hev₂ : ∀ᶠ t in nhds cf.s₂,
      planeDot (deriv S.F.γ t) (vDir S) < planeDot (deriv S.F.γ cf.s₂) (vDir S) / 2 ∧
      planeDot (deriv S.F.γ cf.s₂) S.u / 2 < planeDot (deriv S.F.γ t) S.u ∧
      0 < planeDot (deriv G t) S.u := by
    refine Filter.Eventually.and ?_ (Filter.Eventually.and ?_ ?_)
    · exact (r_continuous_planeDot hF'c _).continuousAt.eventually_lt continuousAt_const
        (by linarith)
    · exact continuousAt_const.eventually_lt (r_continuous_planeDot hF'c _).continuousAt
        (half_lt_self hm₄)
    · exact continuousAt_const.eventually_lt (r_continuous_planeDot hG'c _).continuousAt
        (by rw [hG'₂]; exact hm₄)
  obtain ⟨ζ₁, hζ₁, hzone₁⟩ := r_zone_of_eventually hev₁
  obtain ⟨ζ₂, hζ₂, hzone₂⟩ := r_zone_of_eventually hev₂
  obtain ⟨lam₀, hlam₀def⟩ : ∃ lam₀ : ℝ, lam₀ = min (min ζ₁ ζ₂)
      (min (min ((q₁ - cf.s₁) / 2) ((cf.s₂ - q₂) / 2)) ((cf.s₂ - cf.s₁) / 4)) := ⟨_, rfl⟩
  have hlam₀ : 0 < lam₀ := by
    rw [hlam₀def]
    exact lt_min (lt_min hζ₁ hζ₂) (lt_min (lt_min (by linarith [hq₁.1]) (by linarith [hq₂.2]))
      (by linarith))
  have hlam₀ζ₁ : lam₀ ≤ ζ₁ := by rw [hlam₀def]; exact (min_le_left _ _).trans (min_le_left _ _)
  have hlam₀ζ₂ : lam₀ ≤ ζ₂ := by rw [hlam₀def]; exact (min_le_left _ _).trans (min_le_right _ _)
  have hlam₀q₁ : cf.s₁ + lam₀ < q₁ := by
    have : lam₀ ≤ (q₁ - cf.s₁) / 2 := by
      rw [hlam₀def]; exact (min_le_right _ _).trans ((min_le_left _ _).trans (min_le_left _ _))
    linarith [hq₁.1]
  have hlam₀q₂ : q₂ < cf.s₂ - lam₀ := by
    have : lam₀ ≤ (cf.s₂ - q₂) / 2 := by
      rw [hlam₀def]; exact (min_le_right _ _).trans ((min_le_left _ _).trans (min_le_right _ _))
    linarith [hq₂.2]
  have hlam₀s : 4 * lam₀ ≤ cf.s₂ - cf.s₁ := by
    have : lam₀ ≤ (cf.s₂ - cf.s₁) / 4 := by
      rw [hlam₀def]; exact (min_le_right _ _).trans (min_le_right _ _)
    linarith
  have hZ₁ : ∀ t ∈ Icc cf.s₁ (cf.s₁ + lam₀),
      planeDot (deriv S.F.γ cf.s₁) (vDir S) / 2 < planeDot (deriv S.F.γ t) (vDir S) ∧
      planeDot (deriv S.F.γ cf.s₁) S.u / 2 < planeDot (deriv S.F.γ t) S.u ∧
      0 < planeDot (deriv G t) S.u := fun t ht =>
    hzone₁ t (by rw [abs_of_nonneg (by linarith [ht.1])]; linarith [ht.2])
  have hZ₂ : ∀ t ∈ Icc (cf.s₂ - lam₀) cf.s₂,
      planeDot (deriv S.F.γ t) (vDir S) < planeDot (deriv S.F.γ cf.s₂) (vDir S) / 2 ∧
      planeDot (deriv S.F.γ cf.s₂) S.u / 2 < planeDot (deriv S.F.γ t) S.u ∧
      0 < planeDot (deriv G t) S.u := fun t ht =>
    hzone₂ t (by rw [abs_of_nonpos (by linarith [ht.2])]; linarith [ht.1])
  -- ## 3. the separation distances
  have hu0 : S.u ≠ 0 := by
    intro h0; have := hu1; rw [h0] at this
    simp [euclideanLength, planeComplex_zero] at this
  have hp₁₂ : S.F.γ cf.s₂ ≠ S.F.γ cf.s₁ := by
    intro h
    have := cut_displacement S cf.ξ_eq
    rw [h, sub_self] at this
    exact smul_ne_zero (sub_pos.mpr cf.ℓ_pos).ne' hu0 this.symm
  have hGne₁ : ∀ t ∈ Icc (cf.s₁ + lam₀) cf.s₂, G t ≠ S.F.γ cf.s₁ := fun t ht h => by
    rcases lt_or_eq_of_le ht.2 with hlt | heq
    · have := hGexc t ⟨by linarith [ht.1], hlt⟩
      rw [h] at this; exact lt_irrefl _ this
    · rw [heq, hG₂] at h; exact hp₁₂ h
  have hGne₂ : ∀ t ∈ Icc cf.s₁ (cf.s₂ - lam₀), G t ≠ S.F.γ cf.s₂ := fun t ht h => by
    rcases lt_or_eq_of_le ht.1 with hlt | heq
    · have := hGexc t ⟨hlt, by linarith [ht.2]⟩
      rw [h, cf.ξ_eq] at this; exact lt_irrefl _ this
    · rw [← heq, hG₁] at h; exact hp₁₂ h.symm
  obtain ⟨tm, htmmem, htmmin⟩ := (isCompact_Icc (a := cf.s₁ + lam₀) (b := cf.s₂)).exists_isMinOn
    ⟨cf.s₂, by constructor <;> linarith⟩ ((hGc.sub continuous_const).norm.continuousOn)
  obtain ⟨dm, hdmdef⟩ : ∃ dm : ℝ, dm = ‖G tm - S.F.γ cf.s₁‖ := ⟨_, rfl⟩
  have hdm : 0 < dm := by rw [hdmdef]; exact norm_pos_iff.mpr (sub_ne_zero.mpr (hGne₁ tm htmmem))
  have hdmle : ∀ t ∈ Icc (cf.s₁ + lam₀) cf.s₂, dm ≤ ‖G t - S.F.γ cf.s₁‖ := fun t ht => by
    rw [hdmdef]; exact isMinOn_iff.mp htmmin t ht
  obtain ⟨tp, htpmem, htpmin⟩ := (isCompact_Icc (a := cf.s₁) (b := cf.s₂ - lam₀)).exists_isMinOn
    ⟨cf.s₁, by constructor <;> linarith⟩ ((hGc.sub continuous_const).norm.continuousOn)
  obtain ⟨dp, hdpdef⟩ : ∃ dp : ℝ, dp = ‖G tp - S.F.γ cf.s₂‖ := ⟨_, rfl⟩
  have hdp : 0 < dp := by rw [hdpdef]; exact norm_pos_iff.mpr (sub_ne_zero.mpr (hGne₂ tp htpmem))
  have hdple : ∀ t ∈ Icc cf.s₁ (cf.s₂ - lam₀), dp ≤ ‖G t - S.F.γ cf.s₂‖ := fun t ht => by
    rw [hdpdef]; exact isMinOn_iff.mp htpmin t ht
  obtain ⟨ℓ', hℓ'def⟩ : ∃ ℓ' : ℝ, ℓ' = ‖S.F.γ cf.s₂ - S.F.γ cf.s₁‖ := ⟨_, rfl⟩
  have hℓ' : 0 < ℓ' := by rw [hℓ'def]; exact norm_pos_iff.mpr (sub_ne_zero.mpr hp₁₂)
  -- ## 4. the tolerance `ε` and the position zones
  obtain ⟨ε, hεdef⟩ : ∃ ε : ℝ, ε = min (min (planeDot (deriv S.F.γ cf.s₁) (vDir S))
      (planeDot (deriv S.F.γ cf.s₁) S.u)) (min (min (-planeDot (deriv S.F.γ cf.s₂) (vDir S))
      (planeDot (deriv S.F.γ cf.s₂) S.u)) (min (min dm dp) ℓ')) / 8 := ⟨_, rfl⟩
  have hε : 0 < ε := by
    rw [hεdef]
    exact div_pos (lt_min (lt_min hm₁ hm₂) (lt_min (lt_min (neg_pos.mpr hm₃) hm₄)
      (lt_min (lt_min hdm hdp) hℓ'))) (by norm_num)
  have h8 : (8:ℝ) ≠ 0 := by norm_num
  have hε₁ : 8 * ε ≤ planeDot (deriv S.F.γ cf.s₁) (vDir S) := by
    rw [hεdef, mul_div_cancel₀ _ h8]; exact (min_le_left _ _).trans (min_le_left _ _)
  have hε₂ : 8 * ε ≤ planeDot (deriv S.F.γ cf.s₁) S.u := by
    rw [hεdef, mul_div_cancel₀ _ h8]; exact (min_le_left _ _).trans (min_le_right _ _)
  have hε₃ : 8 * ε ≤ -planeDot (deriv S.F.γ cf.s₂) (vDir S) := by
    rw [hεdef, mul_div_cancel₀ _ h8]
    exact (min_le_right _ _).trans ((min_le_left _ _).trans (min_le_left _ _))
  have hε₄ : 8 * ε ≤ planeDot (deriv S.F.γ cf.s₂) S.u := by
    rw [hεdef, mul_div_cancel₀ _ h8]
    exact (min_le_right _ _).trans ((min_le_left _ _).trans (min_le_right _ _))
  have hε₅ : 8 * ε ≤ dm := by
    rw [hεdef, mul_div_cancel₀ _ h8]
    exact (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_left _ _).trans
      (min_le_left _ _)))
  have hε₆ : 8 * ε ≤ dp := by
    rw [hεdef, mul_div_cancel₀ _ h8]
    exact (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_left _ _).trans
      (min_le_right _ _)))
  have hε₇ : 8 * ε ≤ ℓ' := by
    rw [hεdef, mul_div_cancel₀ _ h8]
    exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hevp₁ : ∀ᶠ t in nhds cf.s₁, ‖S.F.γ t - S.F.γ cf.s₁‖ < ε :=
    ((hFc.sub continuous_const).norm.continuousAt).eventually_lt continuousAt_const
      (by simp [hε])
  have hevp₂ : ∀ᶠ t in nhds cf.s₂, ‖S.F.γ t - S.F.γ cf.s₂‖ < ε :=
    ((hFc.sub continuous_const).norm.continuousAt).eventually_lt continuousAt_const
      (by simp [hε])
  obtain ⟨lam₁, hlam₁, hzp₁⟩ := r_zone_of_eventually hevp₁
  obtain ⟨lam₂, hlam₂, hzp₂⟩ := r_zone_of_eventually hevp₂
  -- ## 5. the blend
  obtain ⟨lam, hlam, hlamle, N, hNs, hNl, hNr, hN'l, hN'r, hN'₁, hN'₂, hNmid, hNconv, hNcol₁,
    hNcol₂⟩ := r_glue hFs hGs hG₁ hG'₁ hG₂ hG'₂ hε (lam₀ := min lam₀ (min lam₁ lam₂))
      (lt_min hlam₀ (lt_min hlam₁ hlam₂))
      (by have := min_le_left lam₀ (min lam₁ lam₂); linarith)
  have hlam_lam₀ : lam ≤ lam₀ := hlamle.trans (min_le_left _ _)
  have hlam_lam₁ : lam ≤ lam₁ := hlamle.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hlam_lam₂ : lam ≤ lam₂ := hlamle.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hNd : Differentiable ℝ N := hNs.differentiable (by decide)
  have hq₀mid : q₀ ∈ Icc (cf.s₁ + lam) (cf.s₂ - lam) :=
    ⟨by linarith [hlam₀q₁, hq₁₀], by linarith [hlam₀q₂, hq₀₂]⟩
  have hq₁mid : q₁ ∈ Icc (cf.s₁ + lam) (cf.s₂ - lam) :=
    ⟨by linarith [hlam₀q₁], by linarith [hlam₀q₂, hq₀₂, hq₁₀]⟩
  have hq₂mid : q₂ ∈ Icc (cf.s₁ + lam) (cf.s₂ - lam) :=
    ⟨by linarith [hlam₀q₁, hq₁₀, hq₀₂], by linarith [hlam₀q₂]⟩
  -- ## 6. the velocity of `N` on the collars and the zones
  have hcol₁v : ∀ t ∈ Icc cf.s₁ (cf.s₁ + lam), 0 < planeDot (deriv N t) (vDir S) := fun t ht =>
    r_collar_sign hv1 (hNcol₁ t ht).1 (hZ₁ t ⟨ht.1, by linarith [ht.2]⟩).1 hε₁
  have hcol₁u : ∀ t ∈ Icc cf.s₁ (cf.s₁ + lam), 0 < planeDot (deriv N t) S.u := fun t ht =>
    r_collar_sign hu1 (hNcol₁ t ht).1 (hZ₁ t ⟨ht.1, by linarith [ht.2]⟩).2.1 hε₂
  have hcol₂v : ∀ t ∈ Icc (cf.s₂ - lam) cf.s₂, planeDot (deriv N t) (vDir S) < 0 := fun t ht =>
    r_collar_sign_neg hv1 (hNcol₂ t ht).1 (hZ₂ t ⟨by linarith [ht.1], ht.2⟩).1 hε₃
  have hcol₂u : ∀ t ∈ Icc (cf.s₂ - lam) cf.s₂, 0 < planeDot (deriv N t) S.u := fun t ht =>
    r_collar_sign hu1 (hNcol₂ t ht).1 (hZ₂ t ⟨by linarith [ht.1], ht.2⟩).2.1 hε₄
  have hZu₁ : ∀ t ∈ Icc cf.s₁ (cf.s₁ + lam₀), 0 < planeDot (deriv N t) S.u := fun t ht => by
    rcases le_or_gt t (cf.s₁ + lam) with h | h
    · exact hcol₁u t ⟨ht.1, h⟩
    · rw [(hNmid t ⟨h.le, by linarith [ht.2]⟩).2]; exact (hZ₁ t ht).2.2
  have hZu₂ : ∀ t ∈ Icc (cf.s₂ - lam₀) cf.s₂, 0 < planeDot (deriv N t) S.u := fun t ht => by
    rcases le_or_gt (cf.s₂ - lam) t with h | h
    · exact hcol₂u t ⟨h, ht.2⟩
    · rw [(hNmid t ⟨by linarith [ht.1], h.le⟩).2]; exact (hZ₂ t ht).2.2
  have hinj₁ := r_inj_of_dot_pos S hNd hZu₁
  have hinj₂ := r_inj_of_dot_pos S hNd hZu₂
  -- ## 7. regularity everywhere
  have hNreg : ∀ t, deriv N t ≠ 0 := by
    intro t
    rcases lt_or_ge t cf.s₁ with h | h
    · rw [hN'l t h]; exact S.F.regular t
    rcases lt_or_ge cf.s₂ t with h' | h'
    · rw [hN'r t h']; exact S.F.regular t
    rcases le_or_gt t (cf.s₁ + lam) with h1 | h1
    · intro h0; have := hcol₁v t ⟨h, h1⟩; rw [h0] at this; simp [planeDot] at this
    rcases le_or_gt (cf.s₂ - lam) t with h2 | h2
    · intro h0; have := hcol₂v t ⟨h2, h'⟩; rw [h0] at this; simp [planeDot] at this
    · rw [(hNmid t ⟨h1.le, h2.le⟩).2]; exact hG'ne t ⟨h, h'⟩
  -- ## 8. positions on the collars
  have hpos₁ : ∀ t ∈ Icc cf.s₁ (cf.s₁ + lam), ‖N t - S.F.γ cf.s₁‖ < 2 * ε := fun t ht => by
    have h1 := (hNcol₁ t ht).2
    have h2 := hzp₁ t (by rw [abs_of_nonneg (by linarith [ht.1])]; linarith [ht.2, hlam_lam₁])
    calc ‖N t - S.F.γ cf.s₁‖ = ‖(N t - S.F.γ t) + (S.F.γ t - S.F.γ cf.s₁)‖ := by congr 1; abel
      _ ≤ ‖N t - S.F.γ t‖ + ‖S.F.γ t - S.F.γ cf.s₁‖ := norm_add_le _ _
      _ < 2 * ε := by linarith
  have hpos₂ : ∀ t ∈ Icc (cf.s₂ - lam) cf.s₂, ‖N t - S.F.γ cf.s₂‖ < 2 * ε := fun t ht => by
    have h1 := (hNcol₂ t ht).2
    have h2 := hzp₂ t (by rw [abs_of_nonpos (by linarith [ht.2])]; linarith [ht.1, hlam_lam₂])
    calc ‖N t - S.F.γ cf.s₂‖ = ‖(N t - S.F.γ t) + (S.F.γ t - S.F.γ cf.s₂)‖ := by congr 1; abel
      _ ≤ ‖N t - S.F.γ t‖ + ‖S.F.γ t - S.F.γ cf.s₂‖ := norm_add_le _ _
      _ < 2 * ε := by linarith
  -- ## 9-12. the clauses from the pieces
  have hdouble := r_glued_double hε hlam_lam₀ (hq₁₀.trans hq₀₂) hinj₁ hinj₂
    (fun t ht => (hNmid t ht).1) hpos₁ hpos₂ hdmle hε₅ hdple hε₆ hℓ'def hε₇ hGinj
  obtain ⟨hNdisc, hoff⟩ := r_glued_off S hα hβ hθ hmeets cf hGdisc hGexc hNconv
  have hNv_before : ∀ t ∈ Icc cf.s₁ cf.s₂, t < q₀ → 0 < planeDot (deriv N t) (vDir S) :=
    fun t ht h => by
      rcases le_or_gt t (cf.s₁ + lam) with h1 | h1
      · exact hcol₁v t ⟨ht.1, h1⟩
      · rw [(hNmid t ⟨h1.le, by linarith [hq₀mid.2]⟩).2]; exact hGv_neg t ht h
  have hNv_after : ∀ t ∈ Icc cf.s₁ cf.s₂, q₀ < t → planeDot (deriv N t) (vDir S) < 0 :=
    fun t ht h => by
      rcases le_or_gt (cf.s₂ - lam) t with h1 | h1
      · exact hcol₂v t ⟨h1, ht.2⟩
      · rw [(hNmid t ⟨by linarith [hq₀mid.1], h1.le⟩).2]; exact hGv_pos t ht h
  have hNv_q₀ : planeDot (deriv N q₀) (vDir S) = 0 := by rw [(hNmid q₀ hq₀mid).2]; exact hGq₀v
  have hNu_q₀ : planeDot (deriv N q₀) S.u < 0 := by rw [(hNmid q₀ hq₀mid).2]; exact hGq₀u
  obtain ⟨hno_u, hone_neg_u⟩ := r_glued_tangent S hNreg hq₀Icc hNv_before hNv_after hNv_q₀ hNu_q₀
  obtain ⟨θ', hlift, hincr⟩ := r_glued_lift S hα hβ hθ cf hNs hNreg hN'₁ hN'₂ hq₀Ioo hNv_before
    hNv_after hNv_q₀ hNu_q₀
  refine ⟨N, q₁, q₂, θ', hNs, hNreg, hNl, hNr, hNdisc, hq₁, hq₂, hq₁₀.trans hq₀₂, ?_, ?_,
    hdouble, hoff, hno_u, hone_neg_u, hlift, hincr⟩
  · rw [(hNmid q₁ hq₁mid).1, (hNmid q₂ hq₂mid).1]; exact hGq
  · rw [(hNmid q₁ hq₁mid).2, (hNmid q₂ hq₂mid).2]; exact hGdet

/-- the periodic extension of the new arc is a `SmoothRegularLoop` equal to `F` off the window -/
theorem exists_loop_of_arc {N : ℝ → Plane} (hN : ContDiff ℝ ∞ N) (hreg : ∀ t, deriv N t ≠ 0)
    {s₁ s₂ : ℝ} (hs : s₂ - s₁ < 1) (hl : ∀ t, t ≤ s₁ → N t = S.F.γ t) (hr : ∀ t, s₂ ≤ t → N t = S.F.γ t) :
    ∃ F' : SmoothRegularLoop, (∀ t ∈ Icc s₁ s₂, F'.γ t = N t) ∧
      (∀ t : ℝ, OffWindow s₁ s₂ t → F'.γ t = S.F.γ t) ∧
      (∀ t ∈ Icc s₁ s₂, deriv F'.γ t = deriv N t) := by
  -- the seam `m` in the dead zone `[s₂, s₁ + 1]` and its clearance `δ`
  obtain ⟨m, hmdef⟩ : ∃ m : ℝ, m = (s₁ + s₂ + 1) / 2 := ⟨_, rfl⟩
  have hm1 : m - 1 < s₁ := by rw [hmdef]; linarith
  have hm2 : s₂ < m := by rw [hmdef]; linarith
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = min (min (s₁ - (m - 1)) (m - s₂)) (1 / 2) := ⟨_, rfl⟩
  have hδ : 0 < δ := by rw [hδdef]; exact lt_min (lt_min (by linarith) (by linarith)) (by norm_num)
  have hδ1 : m - 1 + δ ≤ s₁ := by
    have : δ ≤ s₁ - (m - 1) := by rw [hδdef]; exact (min_le_left _ _).trans (min_le_left _ _)
    linarith
  have hδ2 : s₂ ≤ m - δ := by
    have : δ ≤ m - s₂ := by rw [hδdef]; exact (min_le_left _ _).trans (min_le_right _ _)
    linarith
  have hδh : δ ≤ 1 / 2 := by rw [hδdef]; exact min_le_right _ _
  -- the difference `D = N − F` (zero off the window) and the seam shift `w`
  obtain ⟨D, hDdef⟩ : ∃ D : ℝ → Plane, D = fun t => N t - S.F.γ t := ⟨_, rfl⟩
  have hDt : ∀ t, D t = N t - S.F.γ t := fun t => by rw [hDdef]
  have hD : ContDiff ℝ ∞ D := by rw [hDdef]; exact hN.sub S.F.smooth
  have hD0l : ∀ t, t ≤ s₁ → D t = 0 := fun t ht => by rw [hDt, hl t ht, sub_self]
  have hD0r : ∀ t, s₂ ≤ t → D t = 0 := fun t ht => by rw [hDt, hr t ht, sub_self]
  obtain ⟨w, hwdef⟩ : ∃ w : ℝ → ℝ, w = fun t => Int.fract (t - m) + (m - 1) := ⟨_, rfl⟩
  have hwt : ∀ t, w t = Int.fract (t - m) + (m - 1) := fun t => by rw [hwdef]
  have hw_mem : ∀ t, w t ∈ Ico (m - 1) m := fun t => by
    rw [hwt]; constructor
    · linarith [Int.fract_nonneg (t - m)]
    · linarith [Int.fract_lt_one (t - m)]
  have hw_int : ∀ t, ∃ n : ℤ, w t = t + n := fun t =>
    ⟨-⌊t - m⌋ - 1, by rw [hwt, Int.fract]; push_cast; ring⟩
  have hw_eq : ∀ t ∈ Ico (m - 1) m, w t = t := fun t ht => by
    rw [hwt, (Int.fract_eq_iff (b := t - m + 1)).mpr
      ⟨by linarith [ht.1], by linarith [ht.2], -1, by push_cast; ring⟩]
    ring
  -- `D ∘ w` is smooth: a translation of `D` away from the seam, zero near it
  have hDw : ContDiff ℝ ∞ (fun t => D (w t)) := by
    rw [contDiff_iff_contDiffAt]
    intro t
    obtain ⟨k, hk⟩ : ∃ k : ℤ, ⌊t - m⌋ = k := ⟨_, rfl⟩
    have hk1 : (k : ℝ) ≤ t - m := by rw [← hk]; exact Int.floor_le _
    have hk2 : t - m < k + 1 := by rw [← hk]; exact Int.lt_floor_add_one _
    rcases lt_or_eq_of_le hk1 with hlt | heq
    · have hev : (fun s => D (w s)) =ᶠ[nhds t] fun s => D (s - k - 1) :=
        Filter.eventually_of_mem (Ioo_mem_nhds (a := m + k) (b := m + k + 1)
          (by linarith) (by linarith)) fun s hs => by
          show D (w s) = D (s - k - 1)
          rw [hwt, Int.fract, Int.floor_eq_iff.mpr ⟨by linarith [hs.1], by linarith [hs.2]⟩]
          congr 1; ring
      refine ContDiffAt.congr_of_eventuallyEq ?_ hev
      exact (hD.comp ((contDiff_id.sub contDiff_const).sub contDiff_const)).contDiffAt
    · have hev : (fun s => D (w s)) =ᶠ[nhds t] fun _ => 0 := by
        refine Filter.eventually_of_mem (Ioo_mem_nhds (a := t - δ) (b := t + δ)
          (by linarith) (by linarith)) fun s hs => ?_
        show D (w s) = 0
        rcases le_or_gt t s with h | h
        · have : w s = s - k - 1 := by
            rw [hwt, Int.fract, Int.floor_eq_iff.mpr ⟨by linarith, by linarith [hs.2]⟩]; ring
          rw [this]; exact hD0l _ (by linarith [hs.2])
        · have : w s = s - k := by
            rw [hwt, Int.fract, (Int.floor_eq_iff (z := k - 1)).mpr
              ⟨by push_cast; linarith [hs.1], by push_cast; linarith⟩]
            push_cast; ring
          rw [this]; exact hD0r _ (by linarith [hs.1])
      exact ContDiffAt.congr_of_eventuallyEq contDiffAt_const hev
  -- the periodic curve
  obtain ⟨γ', hγdef⟩ : ∃ γ' : ℝ → Plane, γ' = fun t => S.F.γ t + D (w t) := ⟨_, rfl⟩
  have hγt : ∀ t, γ' t = S.F.γ t + D (w t) := fun t => by rw [hγdef]
  have hγs : ContDiff ℝ ∞ γ' := by rw [hγdef]; exact S.F.smooth.add hDw
  have hγper : Function.Periodic γ' 1 := fun t => by
    rw [hγt, hγt, S.F.periodic t]
    congr 2
    rw [hwt, hwt, show t + 1 - m = t - m + 1 by ring, Int.fract_add_one]
  have hγN : ∀ t ∈ Ioo (m - 1 - δ) m, γ' t = N t := fun t ht => by
    rcases lt_or_ge t (m - 1) with h | h
    · have hw : w t = t + 1 := by
        rw [hwt, (Int.fract_eq_iff (b := t - m + 2)).mpr
          ⟨by linarith [ht.1], by linarith, -2, by push_cast; ring⟩]
        ring
      rw [hγt, hw, hD0r _ (by linarith [ht.1]), add_zero, hl t (by linarith)]
    · rw [hγt, hw_eq t ⟨h, ht.2⟩, hDt]; abel
  have hIcc_sub : Icc s₁ s₂ ⊆ Ioo (m - 1 - δ) m := fun t ht =>
    ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hderivN : ∀ t ∈ Ioo (m - 1 - δ) m, deriv γ' t = deriv N t := fun t ht => by
    have hev : γ' =ᶠ[nhds t] N :=
      Filter.eventually_of_mem (Ioo_mem_nhds ht.1 ht.2) fun s hs => hγN s hs
    exact hev.deriv_eq
  let L : SmoothLoop := ⟨γ', hγs, hγper⟩
  have hLreg : ∀ t, deriv L.γ t ≠ 0 := fun t => by
    obtain ⟨n, hn⟩ := hw_int t
    have h1 : deriv L.γ (w t) = deriv L.γ t := by rw [hn]; exact L.deriv_eq_add_int n t
    have hmem : w t ∈ Ioo (m - 1 - δ) m := ⟨by linarith [(hw_mem t).1], (hw_mem t).2⟩
    rw [← h1]
    show deriv γ' (w t) ≠ 0
    rw [hderivN _ hmem]
    exact hreg _
  refine ⟨⟨L, hLreg⟩, fun t ht => hγN t (hIcc_sub ht), ?_, fun t ht => hderivN t (hIcc_sub ht)⟩
  intro t ht
  obtain ⟨n, hn⟩ := hw_int t
  have h0 : D (w t) = 0 := by
    have hnot := ht n
    rw [← hn] at hnot
    rcases le_or_gt (w t) s₁ with h | h
    · exact hD0l _ h
    · exact hD0r _ (by by_contra h'; push Not at h'; exact hnot ⟨h, h'⟩)
  show γ' t = S.F.γ t
  rw [hγt, h0, add_zero]

/-- The smooth curl exists inside any preassigned neighbourhood of `p` (the assembly of Units G, R:
`exists_chart`, `exists_disc_in_chart`, `exists_cutFit`, `exists_glued_arc`, `exists_loop_of_arc`;
`disc_isDisc`, `p_mem_interior_disc`; the tails clause from `tail_tangent_ne`; `s₂ − s₁ < 1` from
`short`). -/
theorem exists_smoothCurl (Δ₀ : Set Plane) (h₀ : S.p ∈ interior Δ₀) :
    ∃ Δ : Set Plane, Δ ⊆ Δ₀ ∧ Nonempty (SmoothCurl S Δ) := by
  obtain ⟨α', β', hα, hα', hβ', hβ, hθ⟩ := exists_chart S
  obtain ⟨r, hr, hsub, hmeets⟩ := exists_disc_in_chart S hα hα' hβ' hβ Δ₀ h₀
  obtain ⟨cf⟩ := exists_cutFit S hα hα' hβ' hβ hθ hr
  obtain ⟨N, q₁, q₂, θ', hNs, hNreg, hNl, hNr, hNdisc, hq₁, hq₂, hq₁₂, hNq, hNdet, hNinj, hNoff,
    hNu, hNnegu, hlift, hincr⟩ := exists_glued_arc S hα hα' hβ' hβ hθ hr hmeets cf
  have hs1 : cf.s₂ - cf.s₁ < 1 := by linarith [cf.α'_le, cf.le_β', hα, hβ, S.short]
  obtain ⟨F', hF'N, hF'F, hF'd⟩ := exists_loop_of_arc S hNs hNreg hs1 hNl hNr
  refine ⟨disc S r, hsub, ⟨?_⟩⟩
  exact
    { F' := F'
      s₁ := cf.s₁
      s₂ := cf.s₂
      s₁_lt := cf.s₁_lt
      lt_s₂ := cf.lt_s₂
      α_le := hα.trans cf.α'_le
      le_β := cf.le_β'.trans hβ
      unchanged := hF'F
      new_in_disc := fun t ht => by rw [hF'N t ht]; exact hNdisc t ht
      old_in_disc := cf.old_in_disc
      disc := disc_isDisc S hr
      p_mem := p_mem_interior_disc S hr
      meets_arc := fun t ht => by
        obtain ⟨n, hn⟩ := hmeets t ht
        exact ⟨n, ⟨hα.trans hn.1, hn.2.trans hβ⟩⟩
      q₁ := q₁
      q₂ := q₂
      q₁_mem := hq₁
      q₂_mem := hq₂
      q₁_lt := hq₁₂
      double := by
        rw [hF'N q₁ (Ioo_subset_Icc_self hq₁), hF'N q₂ (Ioo_subset_Icc_self hq₂)]; exact hNq
      double_neg := by
        rw [hF'd q₁ (Ioo_subset_Icc_self hq₁), hF'd q₂ (Ioo_subset_Icc_self hq₂)]; exact hNdet
      only_double := fun s hs t ht hst h =>
        hNinj s hs t ht hst (by rw [← hF'N s hs, ← hF'N t ht]; exact h)
      arc_off_rest := fun s hs t ht => by
        rw [hF'N s (Ioo_subset_Icc_self hs)]; exact hNoff s hs t ht
      new_no_u := fun t ht => by rw [hF'd t ht]; exact hNu t ht
      new_one_neg_u := by
        obtain ⟨t, ⟨ht, hNt⟩, huniq⟩ := hNnegu
        exact ⟨t, ⟨ht, by rw [hF'd t ht]; exact hNt⟩,
          fun y ⟨hy, hy'⟩ => huniq y ⟨hy, by rw [← hF'd y hy]; exact hy'⟩⟩
      tails_no_neg_u := fun t ht hoff => by
        obtain ⟨n, hn⟩ := hmeets t ht
        have hne : t + n ≠ S.t₀ := fun h => hoff n (by rw [h]; exact ⟨cf.s₁_lt, cf.lt_s₂⟩)
        have hT : S.T t = S.T (t + n) := by
          show normalize (deriv S.F.γ t) = normalize (deriv S.F.γ (t + n))
          rw [S.F.deriv_eq_add_int]
        rw [hT]
        exact (tail_tangent_ne S ⟨hα.trans hn.1, hn.2.trans hβ⟩ (hθ _ hn) hne).2
      θ' := θ'
      lift' := ⟨hlift.1, fun t ht => by
        show normalize (deriv F'.γ t) = _
        rw [hF'd t ht]; exact hlift.2 t ht⟩
      increment := hincr }

/-! ### Unit T — turning of the modified curve (sm-3:4226-4244), from the accepted cf:lem-turnlift (iii) -/

/-- the seam moved to `a` (curve level; `DirectionLoop.shift` at the direction level is accepted) -/
def shiftCurve (c : ClosedC1Curve) (a : ℝ) : ClosedC1Curve where
  γ := fun s => c.γ (s + a)
  γ' := fun s => c.γ' (s + a)
  hasDerivAt := fun s => by
    have := (c.hasDerivAt (s + a)).scomp s ((hasDerivAt_id' s).add_const a)
    simpa [Function.comp_def] using this
  continuous_deriv := c.continuous_deriv.comp (continuous_add_const a)
  regular := fun s => c.regular (s + a)
  periodic := fun s => by
    show c.γ (s + 1 + a) = c.γ (s + a)
    rw [add_right_comm]; exact c.periodic (s + a)

/-- `rot` does not depend on the seam (`tw_shift`) -/
theorem rot_shiftCurve (c : ClosedC1Curve) (a : ℝ) : (shiftCurve c a).rot = c.rot := by
  have h : (shiftCurve c a).tangentLoop = c.tangentLoop.shift a := rfl
  show tw (shiftCurve c a).tangentLoop = tw c.tangentLoop
  rw [h]
  exact tw_shift c.tangentLoop a

/-- two differentiable plane curves equal on a nondegenerate closed interval have equal derivatives
at every point of it, endpoints included (`uniqueDiffOn_Icc`) -/
theorem ht_deriv_eq_of_eqOn_Icc {F F' : ℝ → Plane} (hF : Differentiable ℝ F)
    (hF' : Differentiable ℝ F') {a b : ℝ} (hab : a < b) (h : ∀ t ∈ Icc a b, F' t = F t) {t : ℝ}
    (ht : t ∈ Icc a b) : deriv F' t = deriv F t := by
  have h1 : HasDerivWithinAt F' (deriv F' t) (Icc a b) t := (hF' t).hasDerivAt.hasDerivWithinAt
  have h2 : HasDerivWithinAt F' (deriv F t) (Icc a b) t :=
    (hF t).hasDerivAt.hasDerivWithinAt.congr h (h t ht)
  exact UniqueDiffWithinAt.eq_deriv _ (uniqueDiffOn_Icc hab t ht) h1 h2

/-- every parameter of `[s₂, s₁ + 1]` is off the open window `(s₁, s₂)` mod 1 (an integer strictly
between `−1` and `0` would be needed) -/
theorem ht_offWindow_of_mem_Icc {s₁ s₂ t : ℝ} (ht : t ∈ Icc s₂ (s₁ + 1)) : OffWindow s₁ s₂ t := by
  intro n hn
  have hn0 : (n : ℝ) < 0 := by linarith [ht.1, hn.2]
  have hn1 : (-1 : ℝ) < n := by linarith [ht.2, hn.1]
  have h0 : n < 0 := by exact_mod_cast hn0
  have h1 : -1 < n := by exact_mod_cast hn1
  omega

/-- Arc replacement in a window (the accepted `rot_sub_rot_of_replace`, seam moved to `s₁`): two
closed `C¹` regular curves that agree off the window `(s₁, s₂)` (mod 1), with tangent lifts on the
window, have `rot F' − rot F = (Δ' − Δ)/2π` -/
theorem rot_sub_rot_of_window (F F' : SmoothRegularLoop) {s₁ s₂ : ℝ} (hs : s₁ < s₂) (hs1 : s₂ - s₁ < 1)
    (hsame : ∀ t : ℝ, OffWindow s₁ s₂ t → F'.γ t = F.γ t) {θ θ' : ℝ → ℝ}
    (hθ : IsLiftOn (fun t => normalize (deriv F.γ t)) θ s₁ s₂)
    (hθ' : IsLiftOn (fun t => normalize (deriv F'.γ t)) θ' s₁ s₂) :
    F'.toClosedC1Curve.rot - F.toClosedC1Curve.rot = ((θ' s₂ - θ' s₁) - (θ s₂ - θ s₁)) / (2 * Real.pi) := by
  have hderiv : ∀ t ∈ Icc s₂ (s₁ + 1), deriv F'.γ t = deriv F.γ t := fun t ht =>
    ht_deriv_eq_of_eqOn_Icc F.differentiable F'.differentiable (by linarith)
      (fun t ht => hsame t (ht_offWindow_of_mem_Icc ht)) ht
  have hcompl : ∀ s ∈ Icc (s₂ - s₁) 1, (shiftCurve F.toClosedC1Curve s₁).tangentLoop.T s =
      (shiftCurve F'.toClosedC1Curve s₁).tangentLoop.T (id s) := by
    intro s hs'
    show normalize (deriv F.γ (s + s₁)) = normalize (deriv F'.γ (s + s₁))
    rw [hderiv (s + s₁) ⟨by linarith [hs'.1], by linarith [hs'.2]⟩]
  have hθb : IsLiftOn (shiftCurve F.toClosedC1Curve s₁).tangentLoop.T (fun s => θ (s + s₁))
      0 (s₂ - s₁) := by
    refine ⟨?_, ?_⟩
    · exact hθ.1.comp (continuous_add_const s₁).continuousOn
        (fun s hs' => ⟨by linarith [hs'.1], by linarith [hs'.2]⟩)
    · intro s hs'
      exact hθ.2 (s + s₁) ⟨by linarith [hs'.1], by linarith [hs'.2]⟩
  have hθc : IsLiftOn (shiftCurve F'.toClosedC1Curve s₁).tangentLoop.T (fun s => θ' (s + s₁))
      0 (s₂ - s₁) := by
    refine ⟨?_, ?_⟩
    · exact hθ'.1.comp (continuous_add_const s₁).continuousOn
        (fun s hs' => ⟨by linarith [hs'.1], by linarith [hs'.2]⟩)
    · intro s hs'
      exact hθ'.2 (s + s₁) ⟨by linarith [hs'.1], by linarith [hs'.2]⟩
  have h := rot_sub_rot_of_replace (shiftCurve F.toClosedC1Curve s₁)
    (shiftCurve F'.toClosedC1Curve s₁) (lam := s₂ - s₁) (mu := s₂ - s₁) (by linarith) (by linarith)
    (by linarith) (ψ := id) continuousOn_id rfl rfl hcompl hθb hθc
  rw [rot_shiftCurve, rot_shiftCurve] at h
  rw [h]
  simp only [sub_add_cancel, zero_add]

/-! ### Unit K — the polygonal kink: location and Reidemeister-I insertion (the accepted `RIData`) -/

/-! #### K1 helpers: the strict cyclic order `cycBetween` on the real line -/

/-- rotation invariance of the strict cyclic order -/
theorem k1_cyc_rot {a b c : ℝ} : cycBetween a b c ↔ cycBetween b c a := by
  unfold cycBetween; tauto

/-- three distinct points are in one of the two cyclic orders -/
theorem k1_cyc_total {a b c : ℝ} (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    cycBetween a b c ∨ cycBetween c b a := by
  unfold cycBetween
  rcases lt_or_gt_of_ne hab with h1 | h1 <;> rcases lt_or_gt_of_ne hbc with h2 | h2 <;>
    rcases lt_or_gt_of_ne hac with h3 | h3 <;>
    first
    | exact Or.inl (Or.inl ⟨by linarith, by linarith⟩)
    | exact Or.inl (Or.inr (Or.inl ⟨by linarith, by linarith⟩))
    | exact Or.inl (Or.inr (Or.inr ⟨by linarith, by linarith⟩))
    | exact Or.inr (Or.inl ⟨by linarith, by linarith⟩)
    | exact Or.inr (Or.inr (Or.inl ⟨by linarith, by linarith⟩))
    | exact Or.inr (Or.inr (Or.inr ⟨by linarith, by linarith⟩))

/-- `b ∈ (a, c)` and `d ∈ (b, c)` give `d ∈ (a, c)` -/
theorem k1_cyc_trans {a b c d : ℝ} (h1 : cycBetween a b c) (h2 : cycBetween b d c) :
    cycBetween a d c := by
  unfold cycBetween at *
  rcases h1 with ⟨h1, h1'⟩ | ⟨h1, h1'⟩ | ⟨h1, h1'⟩ <;>
    rcases h2 with ⟨h2, h2'⟩ | ⟨h2, h2'⟩ | ⟨h2, h2'⟩ <;>
    first
    | exact Or.inl ⟨by linarith, by linarith⟩
    | exact Or.inr (Or.inl ⟨by linarith, by linarith⟩)
    | exact Or.inr (Or.inr ⟨by linarith, by linarith⟩)

/-- The successor characterisation: if no point of a set lies strictly between `x` and `q` (`q`
is the cyclic successor of `x` in the set), then for set points `a ≠ c` the point `x` lies in the
open arc `(a, c)` iff `q = c` or `q` lies in it. -/
theorem k1_cyc_succ {x q a c : ℝ} (hac : a ≠ c) (hxa : x ≠ a) (hxc : x ≠ c) (hxq : x ≠ q)
    (ha : ¬ cycBetween x a q) (hc : ¬ cycBetween x c q) :
    cycBetween a x c ↔ (q = c ∨ cycBetween a q c) := by
  constructor
  · intro h
    by_cases hqc : q = c
    · exact Or.inl hqc
    · right
      have h' : cycBetween q c x := (k1_cyc_total hxc (Ne.symm hqc) hxq).resolve_left hc
      exact k1_cyc_trans h (k1_cyc_rot.mpr h')
  · rintro (hqc | h)
    · have hqa : q ≠ a := fun hqa => hac (hqa.symm.trans hqc)
      have h1 : cycBetween q a x := (k1_cyc_total hxa hqa.symm hxq).resolve_left ha
      rw [← hqc]
      exact k1_cyc_rot.mp h1
    · have hqa : q ≠ a := fun hqa => by subst hqa; exact not_cycBetween_self_left _ _ h
      have h1 : cycBetween q a x := (k1_cyc_total hxa hqa.symm hxq).resolve_left ha
      have h3 : cycBetween x q a := k1_cyc_rot.mp (k1_cyc_rot.mp h1)
      have h4 : cycBetween q c a := k1_cyc_rot.mp h
      exact k1_cyc_rot.mpr (k1_cyc_trans h3 h4)

/-- the cyclic successor of `x` among finitely many values: no value lies strictly between `x`
and `f q` -/
theorem k1_exists_succ {V : Type*} [Fintype V] [Nonempty V] (f : V → ℝ) (x : ℝ) :
    ∃ q : V, ∀ s : V, ¬ cycBetween x (f s) (f q) := by
  classical
  by_cases hA : (Finset.univ.filter fun v => x < f v).Nonempty
  · obtain ⟨q, hq, hmin⟩ := Finset.exists_min_image _ f hA
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq hmin
    refine ⟨q, fun s hs => ?_⟩
    unfold cycBetween at hs
    rcases hs with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact absurd h2 (not_lt.mpr (hmin s h1))
    · linarith
    · linarith
  · obtain ⟨q, -, hmin⟩ := Finset.exists_min_image Finset.univ f Finset.univ_nonempty
    rw [Finset.not_nonempty_iff_eq_empty, Finset.filter_eq_empty_iff] at hA
    refine ⟨q, fun s hs => ?_⟩
    have hs' : f s ≤ x := not_lt.mp (hA (Finset.mem_univ s))
    unfold cycBetween at hs
    rcases hs with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · linarith
    · exact absurd h1 (not_lt.mpr (hmin s (Finset.mem_univ s)))
    · linarith

/-! #### K1 helpers: a free interior point of an edge (off every other edge) in a prescribed
parameter window -/

/-- a strand adjacent to `e` is `e`, its successor or its predecessor -/
theorem k1_adjacent_cases {Γ : Shadow} {e s : Γ.Strand} (h : Γ.Adjacent e s) :
    s = e ∨ s = ⟨e.1, e.2 + 1⟩ ∨ s = ⟨e.1, e.2 - 1⟩ := by
  obtain ⟨i, a, b, rfl, rfl, hab⟩ := h
  rcases hab with h | h | h
  · right; right
    have : b = a - 1 := by linear_combination h
    subst this; rfl
  · left
    have : b = a := sub_eq_zero.mp h
    subst this; rfl
  · right; left
    have : b = a + 1 := by linear_combination h
    subst this; rfl

/-- a point of `e` with parameter in `[0, 1)` is not on the successor edge (`seg_inter_succ`) -/
theorem k1_not_mem_seg_succ {Γ : Shadow} (hΓ : Γ.Generic) (e : Γ.Strand) {t : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t < 1) : Γ.edgePt e t ∉ Γ.seg ⟨e.1, e.2 + 1⟩ := by
  intro hmem
  have h : Γ.edgePt e t ∈ Γ.seg e ∩ Γ.seg ⟨e.1, e.2 + 1⟩ := ⟨⟨t, ht0, ht1.le, rfl⟩, hmem⟩
  rw [hΓ.seg_inter_succ, Set.mem_singleton_iff, ← Γ.edgePt_one] at h
  exact ht1.ne (hΓ.edgePt_injective e h)

/-- a point of `e` with parameter in `(0, 1]` is not on the predecessor edge -/
theorem k1_not_mem_seg_pred {Γ : Shadow} (hΓ : Γ.Generic) (e : Γ.Strand) {t : ℝ} (ht0 : 0 < t)
    (ht1 : t ≤ 1) : Γ.edgePt e t ∉ Γ.seg ⟨e.1, e.2 - 1⟩ := by
  intro hmem
  have h : Γ.edgePt e t ∈ Γ.seg ⟨e.1, e.2 - 1⟩ ∩ Γ.seg ⟨e.1, e.2 - 1 + 1⟩ := by
    refine ⟨hmem, ?_⟩
    rw [Γ.mk_sub_one_add_one]
    exact ⟨t, ht0.le, ht1, rfl⟩
  rw [hΓ.seg_inter_succ, Set.mem_singleton_iff] at h
  have h2 : Γ.head ⟨e.1, e.2 - 1⟩ = Γ.edgePt e 0 := by
    rw [Γ.edgePt_zero, Γ.head_eq_tail_succ, Γ.mk_sub_one_add_one]
  rw [h2] at h
  exact ht0.ne' (hΓ.edgePt_injective e h)

/-- two interior parameters of `e` whose points lie on one other strand `s` coincide (adjacent
`s`: impossible; non-adjacent `s`: the segments are transverse, `intersection_parameters_unique`) -/
theorem k1_param_unique {Γ : Shadow} (hΓ : Γ.Generic) {e s : Γ.Strand} (hs : s ≠ e) {u u' : ℝ}
    (hu0 : 0 < u) (hu1 : u < 1) (hu : Γ.edgePt e u ∈ Γ.seg s) (hu' : Γ.edgePt e u' ∈ Γ.seg s) :
    u = u' := by
  by_cases hadj : Γ.Adjacent e s
  · exfalso
    rcases k1_adjacent_cases hadj with h | h | h
    · exact hs h
    · subst h; exact k1_not_mem_seg_succ hΓ e hu0.le hu1 hu
    · subst h; exact k1_not_mem_seg_pred hΓ e hu0 hu1.le hu
  · have hmeet : (Γ.seg e ∩ Γ.seg s).Nonempty := ⟨_, ⟨u, hu0.le, hu1.le, rfl⟩, hu⟩
    have hd := hΓ.transverse e s hadj hmeet
    obtain ⟨α, -, -, hα⟩ := hu
    obtain ⟨β, -, -, hβ⟩ := hu'
    have hα' : Γ.tail e + u • Γ.dir e = Γ.tail s + α • Γ.dir s := hα
    have hβ' : Γ.tail e + u' • Γ.dir e = Γ.tail s + β • Γ.dir s := hβ
    exact (intersection_parameters_unique hd hα' hβ').1

/-- the interior parameters of `e` whose point lies on another strand form a finite set (one per
other strand at most) -/
theorem k1_bad_finite (D : Diagram) (e : D.Γ.Strand) :
    {u : ℝ | 0 < u ∧ u < 1 ∧ ∃ s, s ≠ e ∧ D.Γ.edgePt e u ∈ D.Γ.seg s}.Finite := by
  have hsub : {u : ℝ | 0 < u ∧ u < 1 ∧ ∃ s, s ≠ e ∧ D.Γ.edgePt e u ∈ D.Γ.seg s} ⊆
      ⋃ s : D.Γ.Strand, {u : ℝ | 0 < u ∧ u < 1 ∧ s ≠ e ∧ D.Γ.edgePt e u ∈ D.Γ.seg s} := by
    rintro u ⟨h0, h1, s, hs, hm⟩
    exact Set.mem_iUnion.mpr ⟨s, h0, h1, hs, hm⟩
  refine Set.Finite.subset (Set.finite_iUnion fun s => Set.Subsingleton.finite ?_) hsub
  rintro u ⟨hu0, hu1, hs, hu⟩ u' ⟨-, -, -, hu'⟩
  exact k1_param_unique D.generic hs hu0 hu1 hu hu'

/-- in any window `(a, b) ⊆ [0, 1]` there is a parameter `t` such that every parameter of
`[t, b)` gives a point of `e` off every other strand -/
theorem k1_exists_param (D : Diagram) (e : D.Γ.Strand) {a b : ℝ} (hab : a < b) (ha : 0 ≤ a)
    (hb : b ≤ 1) :
    ∃ t, a < t ∧ t < b ∧ ∀ u, t ≤ u → u < b → ∀ s, s ≠ e → D.Γ.edgePt e u ∉ D.Γ.seg s := by
  have hfin : ({u : ℝ | 0 < u ∧ u < 1 ∧ ∃ s, s ≠ e ∧ D.Γ.edgePt e u ∈ D.Γ.seg s} ∩
      Set.Ioo a b).Finite :=
    (k1_bad_finite D e).subset Set.inter_subset_left
  obtain ⟨t₀, ht₀a, ht₀b, ht₀⟩ : ∃ t₀, a ≤ t₀ ∧ t₀ < b ∧
      ∀ u ∈ {u : ℝ | 0 < u ∧ u < 1 ∧ ∃ s, s ≠ e ∧ D.Γ.edgePt e u ∈ D.Γ.seg s} ∩ Set.Ioo a b,
        u ≤ t₀ := by
    by_cases hne : ({u : ℝ | 0 < u ∧ u < 1 ∧ ∃ s, s ≠ e ∧ D.Γ.edgePt e u ∈ D.Γ.seg s} ∩
        Set.Ioo a b).Nonempty
    · obtain ⟨m, hm, hmax⟩ := Set.exists_max_image _ id hfin hne
      exact ⟨m, hm.2.1.le, hm.2.2, hmax⟩
    · exact ⟨a, le_rfl, hab, fun u hu => (hne ⟨u, hu⟩).elim⟩
  refine ⟨(t₀ + b) / 2, by linarith, by linarith, fun u hu hub s hs hmem => ?_⟩
  have := ht₀ u ⟨⟨by linarith, by linarith, s, hs, hmem⟩, by linarith, hub⟩
  linarith

/-! #### K1 helpers: occurrences of a one-component diagram seen on the traversal circle -/

/-- two half-open traversal keys `edge + parameter` agree only when edge and parameter agree -/
theorem k1_key_eq {k : ℕ} [NeZero k] {e j : ZMod k} {t u : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1)
    (hu0 : 0 ≤ u) (hu1 : u < 1) (h : (e.val : ℝ) + t = (j.val : ℝ) + u) : j = e ∧ u = t := by
  have h1 : (e.val : ℝ) < j.val + 1 := by linarith
  have h2 : (j.val : ℝ) < e.val + 1 := by linarith
  have h1' : e.val < j.val + 1 := by exact_mod_cast h1
  have h2' : j.val < e.val + 1 := by exact_mod_cast h2
  have hv : j.val = e.val := by omega
  refine ⟨ZMod.val_injective k hv, ?_⟩
  have : (j.val : ℝ) = e.val := by exact_mod_cast hv
  linarith

/-- an occurrence of a one-component diagram, on the component `i`: its coordinate is
`edge + parameter`, and its point lies on the other strand of its crossing -/
theorem k1_visit_data (D : Diagram) (hc : D.Γ.c = 1) (i : Fin D.Γ.c) (s : D.Γ.Visit) :
    ∃ (j : ZMod (D.Γ.comp i).k) (u : ℝ), D.visitCoord s = (j.val : ℝ) + u ∧ 0 ≤ u ∧ u < 1 ∧
      ∃ s' : D.Γ.Strand, s' ≠ ⟨i, j⟩ ∧ D.Γ.edgePt ⟨i, j⟩ u ∈ D.Γ.seg s' := by
  obtain ⟨x, ⟨⟨j, a⟩, hs⟩⟩ := s
  have hji : j = i := Fin.ext (by have := j.2; have := i.2; omega)
  subst i
  refine ⟨a, D.crossingParam x hs, rfl, (D.crossingParam_spec x hs).1,
    D.crossingParam_lt_one x hs, D.Γ.other x hs, D.Γ.other_ne x hs, ?_⟩
  have h : D.Γ.crossingPoint x = D.Γ.edgePt ⟨j, a⟩ (D.crossingParam x hs) :=
    (D.crossingParam_spec x hs).2.2
  rw [← h]
  exact D.Γ.crossingPoint_mem x (D.Γ.other_mem x hs)

/-- the key of a free point of the edge `⟨i, e⟩` is the coordinate of no occurrence -/
theorem k1_key_ne_visitcoord (D : Diagram) (hc : D.Γ.c = 1) (i : Fin D.Γ.c)
    (e : ZMod (D.Γ.comp i).k) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1)
    (hoff : ∀ s' : D.Γ.Strand, s' ≠ ⟨i, e⟩ → D.Γ.edgePt ⟨i, e⟩ t ∉ D.Γ.seg s') (s : D.Γ.Visit) :
    (e.val : ℝ) + t ≠ D.visitCoord s := by
  intro h
  obtain ⟨j, u, hcoord, hu0, hu1, s', hs', hmem⟩ := k1_visit_data D hc i s
  rw [hcoord] at h
  obtain ⟨hje, hut⟩ := k1_key_eq ht0 ht1 hu0 hu1 h
  subst hje; subst hut
  exact hoff s' hs' hmem

/-- no occurrence has its coordinate strictly between the keys of two points of the edge
`⟨i, e⟩` whose parameter window `[t, t')` is free of other strands -/
theorem k1_no_visitcoord_between (D : Diagram) (hc : D.Γ.c = 1) (i : Fin D.Γ.c)
    (e : ZMod (D.Γ.comp i).k) {t t' : ℝ} (ht0 : 0 ≤ t) (htt' : t < t') (ht'1 : t' ≤ 1)
    (hfree : ∀ u, t ≤ u → u < t' → ∀ s' : D.Γ.Strand, s' ≠ ⟨i, e⟩ →
      D.Γ.edgePt ⟨i, e⟩ u ∉ D.Γ.seg s')
    (s : D.Γ.Visit) : ¬ cycBetween ((e.val : ℝ) + t) (D.visitCoord s) ((e.val : ℝ) + t') := by
  intro h
  obtain ⟨j, u, hcoord, hu0, hu1, s', hs', hmem⟩ := k1_visit_data D hc i s
  rw [hcoord] at h
  unfold cycBetween at h
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have h3 : (e.val : ℝ) < j.val + 1 := by linarith
    have h4 : (j.val : ℝ) < e.val + 1 := by linarith
    have h3' : e.val < j.val + 1 := by exact_mod_cast h3
    have h4' : j.val < e.val + 1 := by exact_mod_cast h4
    have hje : j = e := ZMod.val_injective _ (by omega)
    subst hje
    exact hfree u (by linarith) (by linarith) s' hs' hmem
  · linarith
  · linarith

/-- `Int.fract t₀` is the parameter of no occurrence: the arc `[α, β]` around `t₀` carries no
occurrence (`no_double`) -/
theorem k1_fract_ne (s : S.D.Γ.Visit) : Int.fract S.t₀ ≠ S.carried.τ s := by
  intro h
  apply S.no_double s ⌊S.t₀⌋
  rw [← h, Int.fract_add_floor]
  exact ⟨S.α_lt.le, S.lt_β.le⟩

/-- a location exists: the gap of `D`'s traversal circle between the occurrences around `t₀`
contains an interior edge point off every other edge -/
theorem exists_kinkLocation : Nonempty (KinkLocation S) := by
  classical
  have hc : S.D.Γ.c = 1 := S.one
  by_cases hV : Nonempty S.D.Γ.Visit
  · obtain ⟨q, hq⟩ := k1_exists_succ S.carried.τ (Int.fract S.t₀)
    obtain ⟨x, ⟨⟨i, e⟩, hs⟩⟩ := q
    set q : S.D.Γ.Visit := ⟨x, ⟨⟨i, e⟩, hs⟩⟩ with hqdef
    have htq0 : 0 < S.D.crossingParam x hs := S.D.crossingParam_pos x hs
    have htq1 : S.D.crossingParam x hs < 1 := S.D.crossingParam_lt_one x hs
    obtain ⟨t, ht0, httq, hgood⟩ :=
      k1_exists_param S.D ⟨i, e⟩ (a := 0) (b := S.D.crossingParam x hs) htq0 le_rfl htq1.le
    have ht1 : t < 1 := httq.trans htq1
    have hoff : ∀ s : S.D.Γ.Strand, s ≠ ⟨i, e⟩ → S.D.Γ.edgePt ⟨i, e⟩ t ∉ S.D.Γ.seg s :=
      hgood t le_rfl httq
    have hF4 : ∀ s, (e.val : ℝ) + t ≠ S.D.visitCoord s :=
      k1_key_ne_visitcoord S.D hc i e ht0.le ht1 hoff
    have hF2 : ∀ s, ¬ cycBetween ((e.val : ℝ) + t) (S.D.visitCoord s) (S.D.visitCoord q) :=
      k1_no_visitcoord_between S.D hc i e ht0.le httq htq1.le hgood
    have hF3 : ∀ s, Int.fract S.t₀ ≠ S.carried.τ s := k1_fract_ne S
    have hcomp : ∀ v w : S.D.Γ.Visit, S.D.compOf v = S.D.compOf w := fun v w =>
      Fin.ext (by have := (S.D.compOf v).2; have := (S.D.compOf w).2; omega)
    refine ⟨⟨⟨i, (e, ⟨t, ht0.le, ht1⟩)⟩, ht0, fun s hs' => hoff s hs', fun v w => ?_⟩⟩
    show cycBetween (S.D.visitCoord v) ((e.val : ℝ) + t) (S.D.visitCoord w) ↔
      cycBetween (S.carried.τ v) (Int.fract S.t₀) (S.carried.τ w)
    by_cases hvw : v = w
    · subst hvw
      exact iff_of_false (not_cycBetween_self_right _ _) (not_cycBetween_self_right _ _)
    · have hinjτ : S.carried.τ v ≠ S.carried.τ w := fun h => hvw (S.carried.τ_inj h)
      have hinjc : S.D.visitCoord v ≠ S.D.visitCoord w :=
        fun h => hvw (S.D.visitCoord_injOn (hcomp v w) h)
      rw [k1_cyc_succ hinjc (hF4 v) (hF4 w) (hF4 q) (hF2 v) (hF2 w),
        k1_cyc_succ hinjτ (hF3 v) (hF3 w) (hF3 q) (hq v) (hq w), ← S.carried.order]
      exact or_congr_left
        ⟨fun h => congrArg S.carried.τ (S.D.visitCoord_injOn (hcomp q w) h),
          fun h => congrArg S.D.visitCoord (S.carried.τ_inj h)⟩
  · obtain ⟨t, ht0, ht1, hgood⟩ :=
      k1_exists_param S.D ⟨⟨0, S.D.Γ.hc⟩, 0⟩ (a := 0) (b := 1) zero_lt_one le_rfl le_rfl
    exact ⟨⟨⟨⟨0, S.D.Γ.hc⟩, (0, ⟨t, ht0.le, ht1⟩)⟩, ht0, fun s hs => hgood t le_rfl ht1 s hs,
      fun v w => (hV ⟨v⟩).elim⟩⟩

/-! ### Unit K2 — the polygonal kink insertion: construction and helpers (all `k2_`-prefixed)

The kink of `D'` is a small clockwise monogon inserted into the edge `s₀ = ⟨L.r.1, L.r.2.1⟩` of `D`
at the free interior edge point `r₀ = eval L.r = P a + t • d` (`d` the edge vector).  Four new
vertices `A = r₀ − ε d`, `B = r₀ + ε d + ε n`, `C = r₀ − ε d + ε n`, `Dv = r₀ + ε d` with
`n = (d.2, −d.1)` (the clockwise normal, so the frame `(d, n)` is negatively oriented) replace the
edge `a` by the five edges `e1 = [P a, A]`, `e2 = [A, B]`, `e3 = [B, C]`, `e4 = [C, Dv]`,
`e5 = [Dv, P (a+1)]`; `e2` and `e4` cross at `K = r₀ + (ε/2) n`, the later branch `e4` is over,
`det (dir e4) (dir e2) = −4 ε² |d|² < 0`.  The disc is the sup-metric closed ball of radius `ρ` about
`r₀`, half the clearance of `r₀` from the other edges; `ε` is small against `t`, `1 − t` and `ρ/‖d‖`.
Labels of `D'` are values in `[0, k+4)`: `n < a` old edge `n`, `a … a+4` the five new edges,
`n ≥ a+5` old edge `n − 4`. -/

section K2

variable (L : KinkLocation S)

/-- the number of vertices of the (only) component -/
abbrev k2_k : ℕ := (S.D.Γ.comp L.r.1).k
/-- its vertex tuple -/
abbrev k2_P : LabelledTuple (k2_k S L) := (S.D.Γ.comp L.r.1).P
/-- the edge label of the location -/
abbrev k2_a : ZMod (k2_k S L) := L.r.2.1
/-- the edge parameter of the location -/
abbrev k2_t : ℝ := L.r.2.2.val
/-- the strand carrying the location -/
abbrev k2_s₀ : S.D.Γ.Strand := ⟨L.r.1, L.r.2.1⟩
/-- its edge vector `d` -/
abbrev k2_d : Plane := S.D.Γ.dir (k2_s₀ S L)
/-- the point `r₀` -/
abbrev k2_r₀ : Plane := S.D.Γ.eval L.r
/-- the clockwise normal `n = (d.2, −d.1)` -/
def k2_n : Plane := ((k2_d S L).2, -(k2_d S L).1)

theorem k2_fin_eq (i : Fin S.D.Γ.c) : i = L.r.1 := by
  apply Fin.ext
  have h1 : (i : ℕ) < S.D.Γ.c := i.2
  have h2 : (L.r.1 : ℕ) < S.D.Γ.c := L.r.1.2
  have h3 := S.one
  omega

theorem k2_three_le : 3 ≤ k2_k S L := (S.D.Γ.comp L.r.1).hk

theorem k2_t_pos : 0 < k2_t S L := L.interior
theorem k2_t_lt_one : k2_t S L < 1 := L.r.2.2.2.2

theorem k2_d_ne_zero : k2_d S L ≠ 0 := S.D.Γ.edge_ne_zero S.D.generic _

theorem k2_norm_d_pos : 0 < ‖k2_d S L‖ := norm_pos_iff.mpr (k2_d_ne_zero S L)

theorem k2_r₀_eq : k2_r₀ S L = k2_P S L (k2_a S L) + k2_t S L • k2_d S L := rfl

theorem k2_r₀_eq_edgePt : k2_r₀ S L = S.D.Γ.edgePt (k2_s₀ S L) (k2_t S L) := rfl

theorem k2_tail_s₀ : S.D.Γ.tail (k2_s₀ S L) = k2_P S L (k2_a S L) := rfl

theorem k2_d_eq : k2_d S L = k2_P S L (k2_a S L + 1) - k2_P S L (k2_a S L) := rfl

/-- every strand of `D` lies on the component of the location -/
theorem k2_strand_eq (s : S.D.Γ.Strand) : ∃ b : ZMod (k2_k S L), s = ⟨L.r.1, b⟩ := by
  obtain ⟨i, b⟩ := s
  obtain rfl := k2_fin_eq S L i
  exact ⟨b, rfl⟩

/-- `n` is orthogonal to `d`, of the same Euclidean length; `det d n = −|d|²` -/
theorem k2_dot_d_n : planeDot (k2_d S L) (k2_n S L) = 0 := by
  simp only [planeDot, k2_n]; ring

theorem k2_dot_n_n : planeDot (k2_n S L) (k2_n S L) = planeDot (k2_d S L) (k2_d S L) := by
  simp only [planeDot, k2_n]; ring

theorem k2_det_d_n : det (k2_d S L) (k2_n S L) = -planeDot (k2_d S L) (k2_d S L) := by
  simp only [det, planeDot, k2_n]; ring

theorem k2_dd_pos : 0 < planeDot (k2_d S L) (k2_d S L) := planeDot_self_pos (k2_d_ne_zero S L)

theorem k2_norm_n : ‖k2_n S L‖ = ‖k2_d S L‖ := by
  simp only [k2_n, Prod.norm_def, Real.norm_eq_abs, abs_neg, max_comm]

/-! #### The clearance and the two small parameters -/

/-- the strands other than `s₀` -/
def k2_others : Finset S.D.Γ.Strand := Finset.univ.filter (fun e => e ≠ k2_s₀ S L)

theorem k2_mem_others (e : S.D.Γ.Strand) : e ∈ k2_others S L ↔ e ≠ k2_s₀ S L := by
  simp [k2_others]

theorem k2_others_nonempty : (k2_others S L).Nonempty :=
  ⟨⟨L.r.1, L.r.2.1 - 1⟩, (k2_mem_others S L _).mpr (S.D.Γ.mk_sub_one_ne (k2_s₀ S L))⟩

/-- the clearance: the least distance from `r₀` to a strand other than `s₀` -/
def k2_clear : ℝ :=
  (k2_others S L).inf' (k2_others_nonempty S L) (fun e => Metric.infDist (k2_r₀ S L) (S.D.Γ.seg e))

theorem k2_clear_pos : 0 < k2_clear S L := by
  unfold k2_clear
  rw [Finset.lt_inf'_iff]
  intro e he
  rw [k2_mem_others] at he
  exact ((S.D.Γ.isClosed_seg e).notMem_iff_infDist_pos ⟨_, S.D.Γ.tail_mem_seg e⟩).mp
    (L.off_edges e he)

theorem k2_clear_le_dist {e : S.D.Γ.Strand} (he : e ≠ k2_s₀ S L) {q : Plane}
    (hq : q ∈ S.D.Γ.seg e) : k2_clear S L ≤ dist (k2_r₀ S L) q :=
  (Finset.inf'_le _ ((k2_mem_others S L e).mpr he)).trans (Metric.infDist_le_dist_of_mem hq)

/-- the disc radius: half the clearance -/
def k2_ρ : ℝ := k2_clear S L / 2

theorem k2_ρ_pos : 0 < k2_ρ S L := by unfold k2_ρ; linarith [k2_clear_pos S L]

theorem k2_ρ_lt_clear : k2_ρ S L < k2_clear S L := by unfold k2_ρ; linarith [k2_clear_pos S L]

/-- the tail `P a` lies on the strand `a − 1`, the head `P (a+1)` on `a + 1`, both other than `s₀` -/
theorem k2_clear_le_t_mul : k2_clear S L ≤ k2_t S L * ‖k2_d S L‖ := by
  have h := k2_clear_le_dist S L (e := ⟨L.r.1, L.r.2.1 - 1⟩) (S.D.Γ.mk_sub_one_ne (k2_s₀ S L))
    (S.D.Γ.tail_mem_seg_pred (k2_s₀ S L))
  rwa [← S.D.Γ.edgePt_zero, k2_r₀_eq_edgePt, S.D.Γ.dist_edgePt, sub_zero,
    abs_of_pos (k2_t_pos S L)] at h

theorem k2_clear_le_one_sub_t_mul : k2_clear S L ≤ (1 - k2_t S L) * ‖k2_d S L‖ := by
  have h := k2_clear_le_dist S L (e := ⟨L.r.1, L.r.2.1 + 1⟩) (S.D.Γ.mk_add_one_ne (k2_s₀ S L))
    (S.D.Γ.head_mem_seg_succ (k2_s₀ S L))
  rwa [← S.D.Γ.edgePt_one, k2_r₀_eq_edgePt, S.D.Γ.dist_edgePt, abs_sub_comm,
    abs_of_pos (sub_pos.mpr (k2_t_lt_one S L))] at h

/-- the kink parameter `ε` -/
def k2_ε : ℝ :=
  min (min (k2_t S L / 2) ((1 - k2_t S L) / 2)) (k2_ρ S L / (4 * ‖k2_d S L‖))

theorem k2_ε_pos : 0 < k2_ε S L := by
  unfold k2_ε
  have := k2_t_pos S L; have := k2_t_lt_one S L; have := k2_ρ_pos S L; have := k2_norm_d_pos S L
  refine lt_min (lt_min (by linarith) (by linarith)) (by positivity)

theorem k2_ε_le_t : k2_ε S L ≤ k2_t S L / 2 := (min_le_left _ _).trans (min_le_left _ _)
theorem k2_ε_le_one_sub_t : k2_ε S L ≤ (1 - k2_t S L) / 2 :=
  (min_le_left _ _).trans (min_le_right _ _)
theorem k2_ε_le_ρ : k2_ε S L ≤ k2_ρ S L / (4 * ‖k2_d S L‖) := min_le_right _ _

theorem k2_four_ε_norm_le : 4 * k2_ε S L * ‖k2_d S L‖ ≤ k2_ρ S L := by
  have h := k2_ε_le_ρ S L
  have hd := k2_norm_d_pos S L
  rw [le_div_iff₀ (by positivity)] at h
  linarith

theorem k2_ε_lt_t : k2_ε S L < k2_t S L := by linarith [k2_ε_le_t S L, k2_t_pos S L]
theorem k2_ε_lt_one_sub_t : k2_ε S L < 1 - k2_t S L := by
  linarith [k2_ε_le_one_sub_t S L, k2_t_lt_one S L]

/-- `ε ‖d‖ < ρ < t ‖d‖`, `ρ < (1 − t) ‖d‖`: the kink vertices and the disc lie strictly inside the edge -/
theorem k2_ε_norm_lt_ρ : k2_ε S L * ‖k2_d S L‖ < k2_ρ S L := by
  have := k2_four_ε_norm_le S L
  have := k2_ε_pos S L; have := k2_norm_d_pos S L
  nlinarith

theorem k2_two_ε_norm_lt_ρ : 2 * k2_ε S L * ‖k2_d S L‖ < k2_ρ S L := by
  have := k2_four_ε_norm_le S L
  have := k2_ε_pos S L; have := k2_norm_d_pos S L
  nlinarith

theorem k2_ρ_lt_t_mul : k2_ρ S L < k2_t S L * ‖k2_d S L‖ :=
  (k2_ρ_lt_clear S L).trans_le (k2_clear_le_t_mul S L)

theorem k2_ρ_lt_one_sub_t_mul : k2_ρ S L < (1 - k2_t S L) * ‖k2_d S L‖ :=
  (k2_ρ_lt_clear S L).trans_le (k2_clear_le_one_sub_t_mul S L)

/-- the frontier parameters of `s₀` through the disc -/
def k2_θIn : ℝ := k2_t S L - k2_ρ S L / ‖k2_d S L‖
def k2_θOut : ℝ := k2_t S L + k2_ρ S L / ‖k2_d S L‖

theorem k2_ρ_div_pos : 0 < k2_ρ S L / ‖k2_d S L‖ := div_pos (k2_ρ_pos S L) (k2_norm_d_pos S L)

theorem k2_ε_lt_ρ_div : k2_ε S L < k2_ρ S L / ‖k2_d S L‖ := by
  rw [lt_div_iff₀ (k2_norm_d_pos S L)]; exact k2_ε_norm_lt_ρ S L

theorem k2_θIn_pos : 0 < k2_θIn S L := by
  unfold k2_θIn
  have h := k2_ρ_lt_t_mul S L
  rw [sub_pos, div_lt_iff₀ (k2_norm_d_pos S L)]
  exact h

theorem k2_θOut_lt_one : k2_θOut S L < 1 := by
  unfold k2_θOut
  have h := k2_ρ_lt_one_sub_t_mul S L
  have : k2_ρ S L / ‖k2_d S L‖ < 1 - k2_t S L := by
    rw [div_lt_iff₀ (k2_norm_d_pos S L)]; exact h
  linarith

theorem k2_θIn_lt_θOut : k2_θIn S L < k2_θOut S L := by
  unfold k2_θIn k2_θOut; linarith [k2_ρ_div_pos S L]

theorem k2_θIn_lt : k2_θIn S L < k2_t S L - k2_ε S L := by
  unfold k2_θIn; linarith [k2_ε_lt_ρ_div S L]

theorem k2_lt_θOut : k2_t S L + k2_ε S L < k2_θOut S L := by
  unfold k2_θOut; linarith [k2_ε_lt_ρ_div S L]

/-! #### The four kink vertices, the double point and the new vertex tuple -/

def k2_A : Plane := k2_r₀ S L - k2_ε S L • k2_d S L
def k2_B : Plane := k2_r₀ S L + k2_ε S L • k2_d S L + k2_ε S L • k2_n S L
def k2_C : Plane := k2_r₀ S L - k2_ε S L • k2_d S L + k2_ε S L • k2_n S L
def k2_Dv : Plane := k2_r₀ S L + k2_ε S L • k2_d S L
/-- the kink double point `K = r₀ + (ε/2) n` (the midpoint of `e2` and of `e4`) -/
def k2_K : Plane := k2_r₀ S L + (k2_ε S L / 2) • k2_n S L

/-- the label value of the location's edge -/
abbrev k2_av : ℕ := (k2_a S L).val

theorem k2_av_lt : k2_av S L < k2_k S L := ZMod.val_lt _

/-- the new vertices by natural index -/
def k2_Q : ℕ → Plane := fun m =>
  if m ≤ k2_av S L then k2_P S L m
  else if m = k2_av S L + 1 then k2_A S L
  else if m = k2_av S L + 2 then k2_B S L
  else if m = k2_av S L + 3 then k2_C S L
  else if m = k2_av S L + 4 then k2_Dv S L
  else k2_P S L ((m - 4 : ℕ) : ZMod (k2_k S L))

def k2_tuple : LabelledTuple (k2_k S L + 4) := fun m => k2_Q S L m.val

abbrev k2_comp : PolyComp := ⟨k2_k S L + 4, by omega, k2_tuple S L⟩

/-- the shadow of `D'`: the same (single) component index set, the new tuple -/
abbrev k2_shadow : Shadow := ⟨S.D.Γ.c, S.D.Γ.hc, fun _ => k2_comp S L⟩

@[simp] theorem k2_shadow_c : (k2_shadow S L).c = S.D.Γ.c := rfl
@[simp] theorem k2_shadow_comp (i : Fin S.D.Γ.c) : (k2_shadow S L).comp i = k2_comp S L := rfl
theorem k2_comp_k : (k2_comp S L).k = k2_k S L + 4 := rfl
theorem k2_comp_P : (k2_comp S L).P = k2_tuple S L := rfl

/-- the edge vectors of `D'` by natural label -/
def k2_E : ℕ → Plane := fun m =>
  if m < k2_av S L then edge (k2_P S L) m
  else if m = k2_av S L then (k2_t S L - k2_ε S L) • k2_d S L
  else if m = k2_av S L + 1 then k2_B S L - k2_A S L
  else if m = k2_av S L + 2 then k2_C S L - k2_B S L
  else if m = k2_av S L + 3 then k2_Dv S L - k2_C S L
  else if m = k2_av S L + 4 then (1 - k2_t S L - k2_ε S L) • k2_d S L
  else edge (k2_P S L) ((m - 4 : ℕ) : ZMod (k2_k S L))

theorem k2_Q_of_le {m : ℕ} (h : m ≤ k2_av S L) : k2_Q S L m = k2_P S L m := by
  simp [k2_Q, h]
theorem k2_Q_a1 : k2_Q S L (k2_av S L + 1) = k2_A S L := by simp [k2_Q]
theorem k2_Q_a2 : k2_Q S L (k2_av S L + 2) = k2_B S L := by simp [k2_Q]
theorem k2_Q_a3 : k2_Q S L (k2_av S L + 3) = k2_C S L := by simp [k2_Q]
theorem k2_Q_a4 : k2_Q S L (k2_av S L + 4) = k2_Dv S L := by simp [k2_Q]
theorem k2_Q_of_ge {m : ℕ} (h : k2_av S L + 5 ≤ m) :
    k2_Q S L m = k2_P S L ((m - 4 : ℕ) : ZMod (k2_k S L)) := by
  have h1 : ¬ m ≤ k2_av S L := by omega
  have h2 : m ≠ k2_av S L + 1 := by omega
  have h3 : m ≠ k2_av S L + 2 := by omega
  have h4 : m ≠ k2_av S L + 3 := by omega
  have h5 : m ≠ k2_av S L + 4 := by omega
  simp [k2_Q, h1, h2, h3, h4, h5]

theorem k2_E_of_lt {m : ℕ} (h : m < k2_av S L) : k2_E S L m = edge (k2_P S L) m := by
  simp [k2_E, h]
theorem k2_E_a : k2_E S L (k2_av S L) = (k2_t S L - k2_ε S L) • k2_d S L := by simp [k2_E]
theorem k2_E_a1 : k2_E S L (k2_av S L + 1) = k2_B S L - k2_A S L := by simp [k2_E]
theorem k2_E_a2 : k2_E S L (k2_av S L + 2) = k2_C S L - k2_B S L := by simp [k2_E]
theorem k2_E_a3 : k2_E S L (k2_av S L + 3) = k2_Dv S L - k2_C S L := by simp [k2_E]
theorem k2_E_a4 : k2_E S L (k2_av S L + 4) = (1 - k2_t S L - k2_ε S L) • k2_d S L := by
  simp [k2_E]
theorem k2_E_of_ge {m : ℕ} (h : k2_av S L + 5 ≤ m) :
    k2_E S L m = edge (k2_P S L) ((m - 4 : ℕ) : ZMod (k2_k S L)) := by
  have h1 : ¬ m < k2_av S L := by omega
  have h2 : m ≠ k2_av S L := by omega
  have h3 : m ≠ k2_av S L + 1 := by omega
  have h4 : m ≠ k2_av S L + 2 := by omega
  have h5 : m ≠ k2_av S L + 3 := by omega
  have h6 : m ≠ k2_av S L + 4 := by omega
  simp [k2_E, h1, h2, h3, h4, h5, h6]

/-- the vertex identities `A − P a = (t − ε) d`, `P (a+1) − Dv = (1 − t − ε) d` -/
theorem k2_A_sub_Pa : k2_A S L - k2_P S L (k2_a S L) = (k2_t S L - k2_ε S L) • k2_d S L := by
  rw [k2_A, k2_r₀_eq, sub_smul]; abel

theorem k2_Pa1_sub_Dv :
    k2_P S L (k2_a S L + 1) - k2_Dv S L = (1 - k2_t S L - k2_ε S L) • k2_d S L := by
  rw [k2_Dv, k2_r₀_eq, sub_smul, sub_smul, one_smul, k2_d_eq]; abel

/-- the wrap identity `P (k − 1) + 1 = P 0` in the labels -/
theorem k2_cast_k_sub_one_add_one :
    ((k2_k S L - 1 : ℕ) : ZMod (k2_k S L)) + 1 = 0 := by
  have := k2_three_le S L
  rw [Smoothing.zcast_sub_self (by omega), Nat.cast_one, neg_add_cancel]

/-- **the edge vectors of the new tuple by label value** -/
theorem k2_edge_eq (m : ZMod (k2_k S L + 4)) : edge (k2_tuple S L) m = k2_E S L m.val := by
  have hk := k2_three_le S L
  have hav := k2_av_lt S L
  have hm := ZMod.val_lt m
  have hQ : ∀ j : ZMod (k2_k S L + 4), k2_tuple S L j = k2_Q S L j.val := fun _ => rfl
  unfold edge
  rw [hQ, hQ]
  by_cases hwrap : m.val + 1 = k2_k S L + 4
  · -- the last edge `k+3 → 0`
    rw [Smoothing.zval_add_one_of_eq m hwrap]
    have hm' : m.val = k2_k S L + 3 := by omega
    rw [hm', k2_Q_of_le S L (Nat.zero_le _)]
    by_cases ha : k2_av S L = k2_k S L - 1
    · -- `a = k − 1`: the last edge is `e5`
      have h4 : k2_k S L + 3 = k2_av S L + 4 := by omega
      rw [h4, k2_Q_a4, k2_E_a4, ← k2_Pa1_sub_Dv]
      congr 2
      rw [Nat.cast_zero, ← k2_cast_k_sub_one_add_one S L]
      congr 1
      rw [← ZMod.natCast_zmod_val (k2_a S L)]
      exact (congrArg (fun n : ℕ => (n : ZMod (k2_k S L))) ha).symm
    · have h5 : k2_av S L + 5 ≤ k2_k S L + 3 := by omega
      rw [k2_Q_of_ge S L h5, k2_E_of_ge S L h5]
      unfold edge
      rw [Nat.cast_zero, show k2_k S L + 3 - 4 = k2_k S L - 1 by omega,
        k2_cast_k_sub_one_add_one]
  · rw [Smoothing.zval_add_one_of_lt m (by omega)]
    rcases Nat.lt_or_ge m.val (k2_av S L) with h | h
    · rw [k2_Q_of_le S L (by omega), k2_Q_of_le S L h.le, k2_E_of_lt S L h]
      unfold edge
      rw [Nat.cast_succ]
    · rcases Nat.eq_or_lt_of_le h with h | h
      · rw [← h, k2_Q_a1, k2_Q_of_le S L le_rfl, k2_E_a, ← k2_A_sub_Pa]
        rw [ZMod.natCast_zmod_val]
      · rcases Nat.eq_or_lt_of_le (Nat.succ_le_of_lt h) with h | h
        · rw [← h, k2_Q_a2, k2_Q_a1, k2_E_a1]
        · rcases Nat.eq_or_lt_of_le (Nat.succ_le_of_lt h) with h | h
          · rw [← h, k2_Q_a3, k2_Q_a2, k2_E_a2]
          · rcases Nat.eq_or_lt_of_le (Nat.succ_le_of_lt h) with h | h
            · rw [← h, k2_Q_a4, k2_Q_a3, k2_E_a3]
            · rcases Nat.eq_or_lt_of_le (Nat.succ_le_of_lt h) with h | h
              · rw [← h, k2_Q_of_ge S L (by omega), k2_Q_a4, k2_E_a4, ← k2_Pa1_sub_Dv]
                congr 2
                rw [show k2_av S L + 4 + 1 - 4 = k2_av S L + 1 by omega, Nat.cast_succ,
                  ZMod.natCast_zmod_val]
              · rw [k2_Q_of_ge S L (by omega), k2_Q_of_ge S L (by omega), k2_E_of_ge S L (by omega)]
                unfold edge
                rw [show m.val + 1 - 4 = m.val - 4 + 1 by omega, Nat.cast_succ]

/-! #### Strands of `D'`: labels, kinds, tails, directions, segments -/

/-- the label of a strand of the new shadow, in `ZMod (k+4)` -/
abbrev k2_m (u : (k2_shadow S L).Strand) : ZMod (k2_k S L + 4) := u.2

/-- the label value of a strand of the new shadow -/
abbrev k2_lab (u : (k2_shadow S L).Strand) : ℕ := (k2_m S L u).val

theorem k2_lab_lt (u : (k2_shadow S L).Strand) : k2_lab S L u < k2_k S L + 4 := ZMod.val_lt _

theorem k2_dir' (u : (k2_shadow S L).Strand) : (k2_shadow S L).dir u = k2_E S L (k2_lab S L u) :=
  k2_edge_eq S L u.2

theorem k2_tail' (u : (k2_shadow S L).Strand) : (k2_shadow S L).tail u = k2_Q S L (k2_lab S L u) :=
  rfl

theorem k2_edgePt' (u : (k2_shadow S L).Strand) (θ : ℝ) :
    (k2_shadow S L).edgePt u θ = k2_Q S L (k2_lab S L u) + θ • k2_E S L (k2_lab S L u) := by
  rw [Shadow.edgePt_eq, k2_tail', k2_dir']

theorem k2_mem_seg' (u : (k2_shadow S L).Strand) (q : Plane) :
    q ∈ (k2_shadow S L).seg u ↔
      ∃ θ : ℝ, 0 ≤ θ ∧ θ ≤ 1 ∧ q = k2_Q S L (k2_lab S L u) + θ • k2_E S L (k2_lab S L u) := by
  rw [Shadow.mem_seg_iff]
  simp only [k2_edgePt']

theorem k2_mem_interior' (u : (k2_shadow S L).Strand) (q : Plane) :
    q ∈ (k2_shadow S L).interior u ↔
      ∃ θ : ℝ, 0 < θ ∧ θ < 1 ∧ q = k2_Q S L (k2_lab S L u) + θ • k2_E S L (k2_lab S L u) := by
  rw [Shadow.mem_interior_iff]
  simp only [k2_edgePt']

/-- the seven kinds of strands of `D'` -/
theorem k2_kind_cases (u : (k2_shadow S L).Strand) :
    k2_lab S L u < k2_av S L ∨ k2_lab S L u = k2_av S L ∨ k2_lab S L u = k2_av S L + 1 ∨
      k2_lab S L u = k2_av S L + 2 ∨ k2_lab S L u = k2_av S L + 3 ∨
      k2_lab S L u = k2_av S L + 4 ∨ k2_av S L + 5 ≤ k2_lab S L u := by
  omega

/-- old strands: label `< a` or `≥ a + 5` -/
def k2_IsOld (u : (k2_shadow S L).Strand) : Prop :=
  k2_lab S L u < k2_av S L ∨ k2_av S L + 5 ≤ k2_lab S L u

/-- the three middle kink edges `e2, e3, e4` -/
def k2_IsMid (u : (k2_shadow S L).Strand) : Prop :=
  k2_av S L + 1 ≤ k2_lab S L u ∧ k2_lab S L u ≤ k2_av S L + 3

/-- the original strand of `D` under a strand of `D'` (junk on the middle kink edges) -/
def k2_orig (u : (k2_shadow S L).Strand) : S.D.Γ.Strand :=
  ⟨u.1, ((if k2_lab S L u ≤ k2_av S L then k2_lab S L u else k2_lab S L u - 4 : ℕ) :
    ZMod (S.D.Γ.comp u.1).k)⟩

theorem k2_orig_fst (u : (k2_shadow S L).Strand) : (k2_orig S L u).1 = u.1 := rfl

theorem k2_orig_val_of_le {u : (k2_shadow S L).Strand} (h : k2_lab S L u ≤ k2_av S L) :
    (k2_orig S L u).2.val = k2_lab S L u := by
  obtain ⟨i, m⟩ := u
  obtain rfl := k2_fin_eq S L i
  have h' : m.val ≤ k2_av S L := h
  show ((if m.val ≤ k2_av S L then m.val else m.val - 4 : ℕ) : ZMod (k2_k S L)).val = m.val
  rw [ite_eq_left h', ZMod.val_natCast_of_lt (h'.trans_lt (k2_av_lt S L))]

theorem k2_orig_val_of_ge {u : (k2_shadow S L).Strand} (h : k2_av S L < k2_lab S L u) :
    (k2_orig S L u).2.val = k2_lab S L u - 4 := by
  obtain ⟨i, m⟩ := u
  obtain rfl := k2_fin_eq S L i
  have h' : k2_av S L < m.val := h
  show ((if m.val ≤ k2_av S L then m.val else m.val - 4 : ℕ) : ZMod (k2_k S L)).val = m.val - 4
  have hm : m.val < k2_k S L + 4 := ZMod.val_lt m
  have hk := k2_three_le S L
  rw [ite_eq_right (by omega), ZMod.val_natCast_of_lt (by omega)]

/-- the original of `e1` and of `e5` is `s₀` -/
theorem k2_orig_of_eq_a {u : (k2_shadow S L).Strand} (h : k2_lab S L u = k2_av S L) :
    k2_orig S L u = k2_s₀ S L := by
  obtain ⟨i, m⟩ := u
  obtain rfl := k2_fin_eq S L i
  have h' : m.val = k2_av S L := h
  show (⟨L.r.1, ((if m.val ≤ k2_av S L then m.val else m.val - 4 : ℕ) : ZMod (k2_k S L))⟩ :
    S.D.Γ.Strand) = ⟨L.r.1, k2_a S L⟩
  rw [ite_eq_left h'.le, h', ZMod.natCast_zmod_val]

theorem k2_orig_of_eq_a4 {u : (k2_shadow S L).Strand} (h : k2_lab S L u = k2_av S L + 4) :
    k2_orig S L u = k2_s₀ S L := by
  obtain ⟨i, m⟩ := u
  obtain rfl := k2_fin_eq S L i
  have h' : m.val = k2_av S L + 4 := h
  show (⟨L.r.1, ((if m.val ≤ k2_av S L then m.val else m.val - 4 : ℕ) : ZMod (k2_k S L))⟩ :
    S.D.Γ.Strand) = ⟨L.r.1, k2_a S L⟩
  rw [ite_eq_right (by omega), h', Nat.add_sub_cancel, ZMod.natCast_zmod_val]

/-- the original of an old strand, in the normal form `⟨L.r.1, label⟩` -/
theorem k2_orig_eq (u : (k2_shadow S L).Strand) :
    k2_orig S L u = ⟨L.r.1, ((if k2_lab S L u ≤ k2_av S L then k2_lab S L u
      else k2_lab S L u - 4 : ℕ) : ZMod (k2_k S L))⟩ := by
  obtain ⟨i, m⟩ := u
  obtain rfl := k2_fin_eq S L i
  rfl

/-- tails and directions of the old strands are those of their originals -/
theorem k2_tail_old {u : (k2_shadow S L).Strand} (h : k2_IsOld S L u) :
    (k2_shadow S L).tail u = S.D.Γ.tail (k2_orig S L u) := by
  rw [k2_tail', k2_orig_eq]
  show k2_Q S L (k2_lab S L u) = k2_P S L _
  rcases h with h | h
  · rw [k2_Q_of_le S L h.le, ite_eq_left h.le]
  · rw [k2_Q_of_ge S L h, ite_eq_right (by omega)]

theorem k2_dir_old {u : (k2_shadow S L).Strand} (h : k2_IsOld S L u) :
    (k2_shadow S L).dir u = S.D.Γ.dir (k2_orig S L u) := by
  rw [k2_dir', k2_orig_eq]
  show k2_E S L (k2_lab S L u) = edge (k2_P S L) _
  rcases h with h | h
  · rw [k2_E_of_lt S L h, ite_eq_left h.le]
  · rw [k2_E_of_ge S L h, ite_eq_right (by omega)]

theorem k2_edgePt_old {u : (k2_shadow S L).Strand} (h : k2_IsOld S L u) (θ : ℝ) :
    (k2_shadow S L).edgePt u θ = S.D.Γ.edgePt (k2_orig S L u) θ := by
  rw [Shadow.edgePt_eq, Shadow.edgePt_eq, k2_tail_old S L h, k2_dir_old S L h]

theorem k2_seg_old {u : (k2_shadow S L).Strand} (h : k2_IsOld S L u) :
    (k2_shadow S L).seg u = S.D.Γ.seg (k2_orig S L u) := by
  ext q
  rw [Shadow.mem_seg_iff, Shadow.mem_seg_iff]
  simp only [k2_edgePt_old S L h]

theorem k2_interior_old {u : (k2_shadow S L).Strand} (h : k2_IsOld S L u) :
    (k2_shadow S L).interior u = S.D.Γ.interior (k2_orig S L u) := by
  ext q
  rw [Shadow.mem_interior_iff, Shadow.mem_interior_iff]
  simp only [k2_edgePt_old S L h]

/-- the five kink edges: tails and directions -/
theorem k2_tail_e1 {u : (k2_shadow S L).Strand} (h : k2_lab S L u = k2_av S L) :
    (k2_shadow S L).tail u = k2_P S L (k2_a S L) := by
  rw [k2_tail', h, k2_Q_of_le S L le_rfl, ZMod.natCast_zmod_val]
theorem k2_dir_e1 {u : (k2_shadow S L).Strand} (h : k2_lab S L u = k2_av S L) :
    (k2_shadow S L).dir u = (k2_t S L - k2_ε S L) • k2_d S L := by
  rw [k2_dir', h, k2_E_a]
theorem k2_tail_e2 {u : (k2_shadow S L).Strand} (h : k2_lab S L u = k2_av S L + 1) :
    (k2_shadow S L).tail u = k2_A S L := by rw [k2_tail', h, k2_Q_a1]
theorem k2_dir_e2 {u : (k2_shadow S L).Strand} (h : k2_lab S L u = k2_av S L + 1) :
    (k2_shadow S L).dir u = (2 * k2_ε S L) • k2_d S L + k2_ε S L • k2_n S L := by
  rw [k2_dir', h, k2_E_a1, k2_B, k2_A, two_mul, add_smul]; abel
theorem k2_tail_e3 {u : (k2_shadow S L).Strand} (h : k2_lab S L u = k2_av S L + 2) :
    (k2_shadow S L).tail u = k2_B S L := by rw [k2_tail', h, k2_Q_a2]
theorem k2_dir_e3 {u : (k2_shadow S L).Strand} (h : k2_lab S L u = k2_av S L + 2) :
    (k2_shadow S L).dir u = (-(2 * k2_ε S L)) • k2_d S L := by
  rw [k2_dir', h, k2_E_a2, k2_B, k2_C, two_mul, neg_smul, add_smul]; abel
theorem k2_tail_e4 {u : (k2_shadow S L).Strand} (h : k2_lab S L u = k2_av S L + 3) :
    (k2_shadow S L).tail u = k2_C S L := by rw [k2_tail', h, k2_Q_a3]
theorem k2_dir_e4 {u : (k2_shadow S L).Strand} (h : k2_lab S L u = k2_av S L + 3) :
    (k2_shadow S L).dir u = (2 * k2_ε S L) • k2_d S L - k2_ε S L • k2_n S L := by
  rw [k2_dir', h, k2_E_a3, k2_Dv, k2_C, two_mul, add_smul]; abel
theorem k2_tail_e5 {u : (k2_shadow S L).Strand} (h : k2_lab S L u = k2_av S L + 4) :
    (k2_shadow S L).tail u = k2_Dv S L := by rw [k2_tail', h, k2_Q_a4]
theorem k2_dir_e5 {u : (k2_shadow S L).Strand} (h : k2_lab S L u = k2_av S L + 4) :
    (k2_shadow S L).dir u = (1 - k2_t S L - k2_ε S L) • k2_d S L := by
  rw [k2_dir', h, k2_E_a4]

/-! #### Coordinates in the frame `(d, n)` about `r₀`; the disc `U` -/

/-- the (unnormalised) coordinates of a point in the frame `(d, n)` about `r₀` -/
def k2_X (q : Plane) : ℝ := planeDot (q - k2_r₀ S L) (k2_d S L)
def k2_Y (q : Plane) : ℝ := planeDot (q - k2_r₀ S L) (k2_n S L)
/-- `|d|² = planeDot d d > 0` -/
abbrev k2_dd : ℝ := planeDot (k2_d S L) (k2_d S L)

theorem k2_X_frame (α β : ℝ) :
    k2_X S L (k2_r₀ S L + α • k2_d S L + β • k2_n S L) = α * k2_dd S L := by
  simp only [k2_X, k2_n, planeDot, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub,
    Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

theorem k2_Y_frame (α β : ℝ) :
    k2_Y S L (k2_r₀ S L + α • k2_d S L + β • k2_n S L) = β * k2_dd S L := by
  simp only [k2_Y, k2_n, planeDot, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub,
    Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

/-- two points with the same frame coordinates coincide -/
theorem k2_frame_ext {q q' : Plane} (hX : k2_X S L q = k2_X S L q') (hY : k2_Y S L q = k2_Y S L q') :
    q = q' := by
  have hd := k2_dd_pos S L
  simp only [k2_X, k2_Y, k2_n, planeDot, Prod.fst_sub, Prod.snd_sub] at hX hY
  simp only [planeDot] at hd
  apply Prod.ext
  · have : (q.1 - q'.1) * ((k2_d S L).1 * (k2_d S L).1 + (k2_d S L).2 * (k2_d S L).2) = 0 := by
      linear_combination (k2_d S L).1 * hX + (k2_d S L).2 * hY
    have := (mul_eq_zero.mp this).resolve_right hd.ne'
    linarith
  · have : (q.2 - q'.2) * ((k2_d S L).1 * (k2_d S L).1 + (k2_d S L).2 * (k2_d S L).2) = 0 := by
      linear_combination (k2_d S L).2 * hX - (k2_d S L).1 * hY
    have := (mul_eq_zero.mp this).resolve_right hd.ne'
    linarith

/-- every point has frame coordinates -/
theorem k2_eq_frame (q : Plane) :
    q = k2_r₀ S L + (k2_X S L q / k2_dd S L) • k2_d S L + (k2_Y S L q / k2_dd S L) • k2_n S L := by
  have hd := (k2_dd_pos S L).ne'
  apply k2_frame_ext S L
  · rw [k2_X_frame, div_mul_cancel₀ _ hd]
  · rw [k2_Y_frame, div_mul_cancel₀ _ hd]

/-- the kink points in the frame -/
theorem k2_A_frame : k2_A S L = k2_r₀ S L + (-k2_ε S L) • k2_d S L + (0:ℝ) • k2_n S L := by
  rw [k2_A]; module
theorem k2_B_frame : k2_B S L = k2_r₀ S L + k2_ε S L • k2_d S L + k2_ε S L • k2_n S L := rfl
theorem k2_C_frame : k2_C S L = k2_r₀ S L + (-k2_ε S L) • k2_d S L + k2_ε S L • k2_n S L := by
  rw [k2_C]; module
theorem k2_Dv_frame : k2_Dv S L = k2_r₀ S L + k2_ε S L • k2_d S L + (0:ℝ) • k2_n S L := by
  rw [k2_Dv]; module
theorem k2_K_frame : k2_K S L = k2_r₀ S L + (0:ℝ) • k2_d S L + (k2_ε S L / 2) • k2_n S L := by
  rw [k2_K]; module
theorem k2_Pa_frame : k2_P S L (k2_a S L) = k2_r₀ S L + (-k2_t S L) • k2_d S L + (0:ℝ) • k2_n S L := by
  rw [k2_r₀_eq]; module
theorem k2_Pa1_frame :
    k2_P S L (k2_a S L + 1) = k2_r₀ S L + (1 - k2_t S L) • k2_d S L + (0:ℝ) • k2_n S L := by
  have h : k2_P S L (k2_a S L + 1) = k2_P S L (k2_a S L) + k2_d S L := by rw [k2_d_eq]; abel
  rw [h, k2_r₀_eq]; module
theorem k2_edgePt_s₀_frame (θ : ℝ) :
    S.D.Γ.edgePt (k2_s₀ S L) θ = k2_r₀ S L + (θ - k2_t S L) • k2_d S L + (0:ℝ) • k2_n S L := by
  rw [Shadow.edgePt_eq, k2_tail_s₀, k2_r₀_eq]; module

/-- points of the five kink edges in the frame -/
theorem k2_pt_e1 (θ : ℝ) : k2_P S L (k2_a S L) + θ • ((k2_t S L - k2_ε S L) • k2_d S L) =
    k2_r₀ S L + (θ * (k2_t S L - k2_ε S L) - k2_t S L) • k2_d S L + (0:ℝ) • k2_n S L := by
  rw [k2_r₀_eq]; module
theorem k2_pt_e2 (θ : ℝ) : k2_A S L + θ • ((2 * k2_ε S L) • k2_d S L + k2_ε S L • k2_n S L) =
    k2_r₀ S L + (k2_ε S L * (2 * θ - 1)) • k2_d S L + (k2_ε S L * θ) • k2_n S L := by
  rw [k2_A]; module
theorem k2_pt_e3 (θ : ℝ) : k2_B S L + θ • ((-(2 * k2_ε S L)) • k2_d S L) =
    k2_r₀ S L + (k2_ε S L * (1 - 2 * θ)) • k2_d S L + k2_ε S L • k2_n S L := by
  rw [k2_B]; module
theorem k2_pt_e4 (θ : ℝ) : k2_C S L + θ • ((2 * k2_ε S L) • k2_d S L - k2_ε S L • k2_n S L) =
    k2_r₀ S L + (k2_ε S L * (2 * θ - 1)) • k2_d S L + (k2_ε S L * (1 - θ)) • k2_n S L := by
  rw [k2_C]; module
theorem k2_pt_e5 (θ : ℝ) : k2_Dv S L + θ • ((1 - k2_t S L - k2_ε S L) • k2_d S L) =
    k2_r₀ S L + (k2_ε S L + θ * (1 - k2_t S L - k2_ε S L)) • k2_d S L + (0:ℝ) • k2_n S L := by
  rw [k2_Dv]; module

/-- membership in the five kink edges through frame coordinates -/
theorem k2_mem_e1_iff {u : (k2_shadow S L).Strand} (hu : k2_lab S L u = k2_av S L) (q : Plane) :
    q ∈ (k2_shadow S L).seg u ↔ ∃ θ : ℝ, 0 ≤ θ ∧ θ ≤ 1 ∧
      q = k2_r₀ S L + (θ * (k2_t S L - k2_ε S L) - k2_t S L) • k2_d S L + (0:ℝ) • k2_n S L := by
  rw [Shadow.mem_seg_iff]
  simp only [Shadow.edgePt_eq, k2_tail_e1 S L hu, k2_dir_e1 S L hu, k2_pt_e1]
theorem k2_mem_e2_iff {u : (k2_shadow S L).Strand} (hu : k2_lab S L u = k2_av S L + 1) (q : Plane) :
    q ∈ (k2_shadow S L).seg u ↔ ∃ θ : ℝ, 0 ≤ θ ∧ θ ≤ 1 ∧
      q = k2_r₀ S L + (k2_ε S L * (2 * θ - 1)) • k2_d S L + (k2_ε S L * θ) • k2_n S L := by
  rw [Shadow.mem_seg_iff]
  simp only [Shadow.edgePt_eq, k2_tail_e2 S L hu, k2_dir_e2 S L hu, k2_pt_e2]
theorem k2_mem_e3_iff {u : (k2_shadow S L).Strand} (hu : k2_lab S L u = k2_av S L + 2) (q : Plane) :
    q ∈ (k2_shadow S L).seg u ↔ ∃ θ : ℝ, 0 ≤ θ ∧ θ ≤ 1 ∧
      q = k2_r₀ S L + (k2_ε S L * (1 - 2 * θ)) • k2_d S L + k2_ε S L • k2_n S L := by
  rw [Shadow.mem_seg_iff]
  simp only [Shadow.edgePt_eq, k2_tail_e3 S L hu, k2_dir_e3 S L hu, k2_pt_e3]
theorem k2_mem_e4_iff {u : (k2_shadow S L).Strand} (hu : k2_lab S L u = k2_av S L + 3) (q : Plane) :
    q ∈ (k2_shadow S L).seg u ↔ ∃ θ : ℝ, 0 ≤ θ ∧ θ ≤ 1 ∧
      q = k2_r₀ S L + (k2_ε S L * (2 * θ - 1)) • k2_d S L + (k2_ε S L * (1 - θ)) • k2_n S L := by
  rw [Shadow.mem_seg_iff]
  simp only [Shadow.edgePt_eq, k2_tail_e4 S L hu, k2_dir_e4 S L hu, k2_pt_e4]
theorem k2_mem_e5_iff {u : (k2_shadow S L).Strand} (hu : k2_lab S L u = k2_av S L + 4) (q : Plane) :
    q ∈ (k2_shadow S L).seg u ↔ ∃ θ : ℝ, 0 ≤ θ ∧ θ ≤ 1 ∧
      q = k2_r₀ S L + (k2_ε S L + θ * (1 - k2_t S L - k2_ε S L)) • k2_d S L + (0:ℝ) • k2_n S L := by
  rw [Shadow.mem_seg_iff]
  simp only [Shadow.edgePt_eq, k2_tail_e5 S L hu, k2_dir_e5 S L hu, k2_pt_e5]

theorem k2_mem_int_e1_iff {u : (k2_shadow S L).Strand} (hu : k2_lab S L u = k2_av S L) (q : Plane) :
    q ∈ (k2_shadow S L).interior u ↔ ∃ θ : ℝ, 0 < θ ∧ θ < 1 ∧
      q = k2_r₀ S L + (θ * (k2_t S L - k2_ε S L) - k2_t S L) • k2_d S L + (0:ℝ) • k2_n S L := by
  rw [Shadow.mem_interior_iff]
  simp only [Shadow.edgePt_eq, k2_tail_e1 S L hu, k2_dir_e1 S L hu, k2_pt_e1]
theorem k2_mem_int_e2_iff {u : (k2_shadow S L).Strand} (hu : k2_lab S L u = k2_av S L + 1) (q : Plane) :
    q ∈ (k2_shadow S L).interior u ↔ ∃ θ : ℝ, 0 < θ ∧ θ < 1 ∧
      q = k2_r₀ S L + (k2_ε S L * (2 * θ - 1)) • k2_d S L + (k2_ε S L * θ) • k2_n S L := by
  rw [Shadow.mem_interior_iff]
  simp only [Shadow.edgePt_eq, k2_tail_e2 S L hu, k2_dir_e2 S L hu, k2_pt_e2]
theorem k2_mem_int_e3_iff {u : (k2_shadow S L).Strand} (hu : k2_lab S L u = k2_av S L + 2) (q : Plane) :
    q ∈ (k2_shadow S L).interior u ↔ ∃ θ : ℝ, 0 < θ ∧ θ < 1 ∧
      q = k2_r₀ S L + (k2_ε S L * (1 - 2 * θ)) • k2_d S L + k2_ε S L • k2_n S L := by
  rw [Shadow.mem_interior_iff]
  simp only [Shadow.edgePt_eq, k2_tail_e3 S L hu, k2_dir_e3 S L hu, k2_pt_e3]
theorem k2_mem_int_e4_iff {u : (k2_shadow S L).Strand} (hu : k2_lab S L u = k2_av S L + 3) (q : Plane) :
    q ∈ (k2_shadow S L).interior u ↔ ∃ θ : ℝ, 0 < θ ∧ θ < 1 ∧
      q = k2_r₀ S L + (k2_ε S L * (2 * θ - 1)) • k2_d S L + (k2_ε S L * (1 - θ)) • k2_n S L := by
  rw [Shadow.mem_interior_iff]
  simp only [Shadow.edgePt_eq, k2_tail_e4 S L hu, k2_dir_e4 S L hu, k2_pt_e4]
theorem k2_mem_int_e5_iff {u : (k2_shadow S L).Strand} (hu : k2_lab S L u = k2_av S L + 4) (q : Plane) :
    q ∈ (k2_shadow S L).interior u ↔ ∃ θ : ℝ, 0 < θ ∧ θ < 1 ∧
      q = k2_r₀ S L + (k2_ε S L + θ * (1 - k2_t S L - k2_ε S L)) • k2_d S L + (0:ℝ) • k2_n S L := by
  rw [Shadow.mem_interior_iff]
  simp only [Shadow.edgePt_eq, k2_tail_e5 S L hu, k2_dir_e5 S L hu, k2_pt_e5]

/-- distances from `r₀` in the frame (sup norm; `‖n‖ = ‖d‖`) -/
theorem k2_dist_frame_le (α β : ℝ) :
    dist (k2_r₀ S L + α • k2_d S L + β • k2_n S L) (k2_r₀ S L) ≤ (|α| + |β|) * ‖k2_d S L‖ := by
  rw [dist_eq_norm, add_assoc, add_sub_cancel_left, add_mul]
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, k2_norm_n]

theorem k2_dist_frame_zero (α : ℝ) :
    dist (k2_r₀ S L + α • k2_d S L + (0:ℝ) • k2_n S L) (k2_r₀ S L) = |α| * ‖k2_d S L‖ := by
  rw [zero_smul, add_zero, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs]

/-- the disc `U` -/
def k2_U : Set Plane := Metric.closedBall (k2_r₀ S L) (k2_ρ S L)

theorem k2_isDisc_U : IsDisc (k2_U S L) := isDisc_closedBall _ (k2_ρ_pos S L)

theorem k2_interior_U : interior (k2_U S L) = Metric.ball (k2_r₀ S L) (k2_ρ S L) :=
  interior_closedBall _ (k2_ρ_pos S L).ne'

theorem k2_frontier_U : frontier (k2_U S L) = Metric.sphere (k2_r₀ S L) (k2_ρ S L) :=
  frontier_closedBall _ (k2_ρ_pos S L).ne'

theorem k2_r₀_mem_ball : k2_r₀ S L ∈ Metric.ball (k2_r₀ S L) (k2_ρ S L) :=
  Metric.mem_ball_self (k2_ρ_pos S L)

/-- frame points with small coordinates lie in the open ball -/
theorem k2_frame_mem_ball {α β : ℝ} (hα : |α| ≤ k2_ε S L) (hβ : |β| ≤ k2_ε S L) :
    k2_r₀ S L + α • k2_d S L + β • k2_n S L ∈ Metric.ball (k2_r₀ S L) (k2_ρ S L) := by
  rw [Metric.mem_ball]
  refine (k2_dist_frame_le S L α β).trans_lt ?_
  have h := k2_two_ε_norm_lt_ρ S L
  have hd := k2_norm_d_pos S L
  nlinarith

/-- no strand other than `s₀` meets the closed disc -/
theorem k2_not_mem_U_of_mem_seg {e : S.D.Γ.Strand} (he : e ≠ k2_s₀ S L) {q : Plane}
    (hq : q ∈ S.D.Γ.seg e) : q ∉ k2_U S L := by
  intro hU
  have h1 := k2_clear_le_dist S L he hq
  have h2 : dist (k2_r₀ S L) q ≤ k2_ρ S L := by rw [dist_comm]; exact Metric.mem_closedBall.mp hU
  linarith [k2_ρ_lt_clear S L]

/-- no vertex of `D` lies in the closed disc -/
theorem k2_tail_not_mem_U (e : S.D.Γ.Strand) : S.D.Γ.tail e ∉ k2_U S L := by
  by_cases he : e = k2_s₀ S L
  · subst he
    exact k2_not_mem_U_of_mem_seg S L (S.D.Γ.mk_sub_one_ne _) (S.D.Γ.tail_mem_seg_pred _)
  · exact k2_not_mem_U_of_mem_seg S L he (S.D.Γ.tail_mem_seg e)

/-- no crossing point of `D` lies in the closed disc (one of its strands is not `s₀`) -/
theorem k2_crossingPoint_not_mem_U (x : S.D.Γ.Crossing) : S.D.Γ.crossingPoint x ∉ k2_U S L := by
  obtain ⟨e, he, hes⟩ : ∃ e ∈ x.val, e ≠ k2_s₀ S L := by
    by_contra hcon
    simp only [not_exists, not_and, not_not] at hcon
    have h1 := hcon _ (S.D.over_mem x)
    have h2 := hcon _ (S.D.under_mem x)
    exact S.D.over_ne_under x (h1.trans h2.symm)
  exact k2_not_mem_U_of_mem_seg S L hes (S.D.Γ.crossingPoint_mem x he)

/-- points of `s₀` in the disc: the parameter window `[θIn, θOut]` -/
theorem k2_dist_edgePt_s₀ (θ : ℝ) :
    dist (S.D.Γ.edgePt (k2_s₀ S L) θ) (k2_r₀ S L) = |θ - k2_t S L| * ‖k2_d S L‖ := by
  rw [k2_r₀_eq_edgePt]; exact S.D.Γ.dist_edgePt _ θ _

theorem k2_edgePt_s₀_mem_U_iff (θ : ℝ) :
    S.D.Γ.edgePt (k2_s₀ S L) θ ∈ k2_U S L ↔ k2_θIn S L ≤ θ ∧ θ ≤ k2_θOut S L := by
  have hd := k2_norm_d_pos S L
  rw [k2_U, Metric.mem_closedBall, k2_dist_edgePt_s₀, ← le_div_iff₀ hd, abs_sub_le_iff, k2_θIn,
    k2_θOut]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

theorem k2_edgePt_s₀_mem_ball_iff (θ : ℝ) :
    S.D.Γ.edgePt (k2_s₀ S L) θ ∈ Metric.ball (k2_r₀ S L) (k2_ρ S L) ↔
      k2_θIn S L < θ ∧ θ < k2_θOut S L := by
  have hd := k2_norm_d_pos S L
  rw [Metric.mem_ball, k2_dist_edgePt_s₀, ← lt_div_iff₀ hd, abs_sub_lt_iff, k2_θIn, k2_θOut]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

theorem k2_edgePt_s₀_mem_sphere (θ : ℝ) (hθ : θ = k2_θIn S L ∨ θ = k2_θOut S L) :
    S.D.Γ.edgePt (k2_s₀ S L) θ ∈ Metric.sphere (k2_r₀ S L) (k2_ρ S L) := by
  have hd := k2_norm_d_pos S L
  have hρ := (k2_ρ_pos S L).le
  rw [Metric.mem_sphere, k2_dist_edgePt_s₀]
  rcases hθ with rfl | rfl
  · rw [k2_θIn, sub_sub_cancel_left, abs_neg, abs_of_nonneg (div_nonneg hρ hd.le),
      div_mul_cancel₀ _ hd.ne']
  · rw [k2_θOut, add_sub_cancel_left, abs_of_nonneg (div_nonneg hρ hd.le), div_mul_cancel₀ _ hd.ne']

/-- the crossing parameter of an occurrence on `s₀` lies outside the window -/
theorem k2_crossingParam_far (v : S.D.Γ.Visit) (hv : v.2.val = k2_s₀ S L) :
    S.D.crossingParam v.1 v.2.2 < k2_θIn S L ∨ k2_θOut S L < S.D.crossingParam v.1 v.2.2 := by
  have h1 := k2_crossingPoint_not_mem_U S L v.1
  have h2 : S.D.Γ.crossingPoint v.1 = S.D.Γ.edgePt (k2_s₀ S L) (S.D.crossingParam v.1 v.2.2) := by
    rw [← hv]; exact (S.D.crossingParam_spec v.1 v.2.2).2.2
  rw [h2, k2_edgePt_s₀_mem_U_iff, not_and_or, not_le, not_le] at h1
  exact h1

/-! #### Adjacency and incidence by label values -/

theorem k2_zmod_succ_val {n : ℕ} [NeZero n] (a : ZMod n) :
    (a + 1).val = if a.val + 1 < n then a.val + 1 else 0 := by
  split_ifs with h
  · exact Smoothing.zval_add_one_of_lt a h
  · exact Smoothing.zval_add_one_of_eq a (by have := ZMod.val_lt a; omega)

theorem k2_zmod_eq_iff {n : ℕ} [NeZero n] (a b : ZMod n) : a = b ↔ a.val = b.val :=
  ⟨fun h => by rw [h], fun h => ZMod.val_injective n h⟩

/-- `adjacent a b` in `ZMod n` by values -/
theorem k2_zmod_adjacent_iff {n : ℕ} [NeZero n] (a b : ZMod n) :
    adjacent a b ↔ b.val = a.val ∨ b.val = a.val + 1 ∨ a.val = b.val + 1 ∨
      (a.val + 1 = n ∧ b.val = 0) ∨ (b.val + 1 = n ∧ a.val = 0) := by
  have ha := ZMod.val_lt a
  have hb := ZMod.val_lt b
  have h1 : b - a = 0 ↔ b.val = a.val := by rw [sub_eq_zero, k2_zmod_eq_iff]
  have h2 : b - a = 1 ↔ b = a + 1 := by rw [sub_eq_iff_eq_add, add_comm]
  have h3 : b - a = -1 ↔ a = b + 1 := by
    rw [sub_eq_iff_eq_add, ← sub_eq_iff_eq_add', sub_neg_eq_add, eq_comm, add_comm]
  unfold adjacent
  rw [h1, h2, h3, k2_zmod_eq_iff b (a + 1), k2_zmod_eq_iff a (b + 1), k2_zmod_succ_val,
    k2_zmod_succ_val]
  split_ifs with h4 h5 h5 <;> omega

/-- `incident a b` in `ZMod n` by values -/
theorem k2_zmod_incident_iff {n : ℕ} [NeZero n] (a b : ZMod n) :
    incident a b ↔ b.val = a.val ∨ a.val = b.val + 1 ∨ (b.val + 1 = n ∧ a.val = 0) := by
  have ha := ZMod.val_lt a
  have hb := ZMod.val_lt b
  have h3 : b = a - 1 ↔ a = b + 1 := by rw [eq_sub_iff_add_eq, eq_comm]
  unfold incident
  rw [h3, k2_zmod_eq_iff b a, k2_zmod_eq_iff a (b + 1), k2_zmod_succ_val]
  split_ifs with h4 <;> omega

/-- adjacency in the new shadow is adjacency of the labels -/
theorem k2_adjacent_iff (u u' : (k2_shadow S L).Strand) :
    (k2_shadow S L).Adjacent u u' ↔ adjacent (k2_m S L u) (k2_m S L u') := by
  constructor
  · rintro ⟨i, a, b, rfl, rfl, h⟩; exact h
  · intro h
    obtain ⟨i, m⟩ := u
    obtain ⟨j, m'⟩ := u'
    obtain rfl := k2_fin_eq S L i
    obtain rfl := k2_fin_eq S L j
    exact ⟨L.r.1, m, m', rfl, rfl, h⟩

theorem k2_incidentTail_iff (u u' : (k2_shadow S L).Strand) :
    (k2_shadow S L).IncidentTail u u' ↔ incident (k2_m S L u) (k2_m S L u') := by
  constructor
  · rintro ⟨i, a, b, rfl, rfl, h⟩; exact h
  · intro h
    obtain ⟨i, m⟩ := u
    obtain ⟨j, m'⟩ := u'
    obtain rfl := k2_fin_eq S L i
    obtain rfl := k2_fin_eq S L j
    exact ⟨L.r.1, m, m', rfl, rfl, h⟩

/-- adjacency in `D` is adjacency of the labels (one component) -/
theorem k2_adjacent_iff_D (s s' : S.D.Γ.Strand) {b b' : ZMod (k2_k S L)} (hs : s = ⟨L.r.1, b⟩)
    (hs' : s' = ⟨L.r.1, b'⟩) : S.D.Γ.Adjacent s s' ↔ adjacent b b' := by
  subst hs; subst hs'
  exact S.D.Γ.adjacent_mk_iff _ _ _

theorem k2_incidentTail_iff_D (s s' : S.D.Γ.Strand) {b b' : ZMod (k2_k S L)} (hs : s = ⟨L.r.1, b⟩)
    (hs' : s' = ⟨L.r.1, b'⟩) : S.D.Γ.IncidentTail s s' ↔ incident b b' := by
  subst hs; subst hs'
  exact S.D.Γ.incidentTail_mk_iff _ _ _

/-- the label values of `D`-strands -/
theorem k2_val_lt_k (b : ZMod (k2_k S L)) : b.val < k2_k S L := ZMod.val_lt b

theorem k2_s₀_val : (k2_s₀ S L).2.val = k2_av S L := rfl

/-- **adjacency of two old strands of `D'` is that of their originals** -/
theorem k2_adjacent_old_iff {u u' : (k2_shadow S L).Strand} (hu : k2_IsOld S L u)
    (hu' : k2_IsOld S L u') :
    (k2_shadow S L).Adjacent u u' ↔ S.D.Γ.Adjacent (k2_orig S L u) (k2_orig S L u') := by
  rw [k2_adjacent_iff, k2_adjacent_iff_D S L _ _ (k2_orig_eq S L u) (k2_orig_eq S L u'),
    k2_zmod_adjacent_iff, k2_zmod_adjacent_iff]
  have h1 := k2_lab_lt S L u
  have h2 := k2_lab_lt S L u'
  have h3 := k2_av_lt S L
  have h4 := k2_three_le S L
  have e1 : ((if k2_lab S L u ≤ k2_av S L then k2_lab S L u else k2_lab S L u - 4 : ℕ) :
      ZMod (k2_k S L)).val = if k2_lab S L u ≤ k2_av S L then k2_lab S L u else k2_lab S L u - 4 := by
    rw [ZMod.val_natCast_of_lt]; split_ifs <;> omega
  have e2 : ((if k2_lab S L u' ≤ k2_av S L then k2_lab S L u' else k2_lab S L u' - 4 : ℕ) :
      ZMod (k2_k S L)).val = if k2_lab S L u' ≤ k2_av S L then k2_lab S L u' else k2_lab S L u' - 4 := by
    rw [ZMod.val_natCast_of_lt]; split_ifs <;> omega
  simp only [e1, e2]
  unfold k2_IsOld at hu hu'
  have hlu : k2_lab S L u = (k2_m S L u).val := rfl
  have hlu' : k2_lab S L u' = (k2_m S L u').val := rfl
  split_ifs <;> omega

/-- **incidence of two old strands of `D'` is that of their originals** -/
theorem k2_incidentTail_old_iff {u u' : (k2_shadow S L).Strand} (hu : k2_IsOld S L u)
    (hu' : k2_IsOld S L u') :
    (k2_shadow S L).IncidentTail u u' ↔ S.D.Γ.IncidentTail (k2_orig S L u) (k2_orig S L u') := by
  rw [k2_incidentTail_iff, k2_incidentTail_iff_D S L _ _ (k2_orig_eq S L u) (k2_orig_eq S L u'),
    k2_zmod_incident_iff, k2_zmod_incident_iff]
  have h1 := k2_lab_lt S L u
  have h2 := k2_lab_lt S L u'
  have h3 := k2_av_lt S L
  have h4 := k2_three_le S L
  have e1 : ((if k2_lab S L u ≤ k2_av S L then k2_lab S L u else k2_lab S L u - 4 : ℕ) :
      ZMod (k2_k S L)).val = if k2_lab S L u ≤ k2_av S L then k2_lab S L u else k2_lab S L u - 4 := by
    rw [ZMod.val_natCast_of_lt]; split_ifs <;> omega
  have e2 : ((if k2_lab S L u' ≤ k2_av S L then k2_lab S L u' else k2_lab S L u' - 4 : ℕ) :
      ZMod (k2_k S L)).val = if k2_lab S L u' ≤ k2_av S L then k2_lab S L u' else k2_lab S L u' - 4 := by
    rw [ZMod.val_natCast_of_lt]; split_ifs <;> omega
  simp only [e1, e2]
  unfold k2_IsOld at hu hu'
  have hlu : k2_lab S L u = (k2_m S L u).val := rfl
  have hlu' : k2_lab S L u' = (k2_m S L u').val := rfl
  split_ifs <;> omega

/-- the original of an old strand is not `s₀` -/
theorem k2_orig_ne_s₀ {u : (k2_shadow S L).Strand} (hu : k2_IsOld S L u) :
    k2_orig S L u ≠ k2_s₀ S L := by
  intro h
  have hv : (k2_orig S L u).2.val = (k2_s₀ S L).2.val :=
    congrArg (fun s : S.D.Γ.Strand => s.2.val) h
  have hav : (k2_s₀ S L).2.val = k2_av S L := rfl
  have hl := k2_lab_lt S L u
  rcases hu with hu | hu
  · rw [k2_orig_val_of_le S L hu.le] at hv; omega
  · rw [k2_orig_val_of_ge S L (by omega)] at hv; omega

/-- distinct old strands have distinct originals -/
theorem k2_orig_injOn {u u' : (k2_shadow S L).Strand} (hu : k2_IsOld S L u) (hu' : k2_IsOld S L u')
    (h : k2_orig S L u = k2_orig S L u') : u = u' := by
  have hv : (k2_orig S L u).2.val = (k2_orig S L u').2.val :=
    congrArg (fun s : S.D.Γ.Strand => s.2.val) h
  have h1 := k2_lab_lt S L u
  have h2 := k2_lab_lt S L u'
  have hlab : k2_lab S L u = k2_lab S L u' := by
    unfold k2_IsOld at hu hu'
    rcases hu with hu | hu <;> rcases hu' with hu' | hu'
    · rwa [k2_orig_val_of_le S L hu.le, k2_orig_val_of_le S L hu'.le] at hv
    · rw [k2_orig_val_of_le S L hu.le, k2_orig_val_of_ge S L (by omega)] at hv; omega
    · rw [k2_orig_val_of_ge S L (by omega), k2_orig_val_of_le S L hu'.le] at hv; omega
    · rw [k2_orig_val_of_ge S L (by omega), k2_orig_val_of_ge S L (by omega)] at hv; omega
  obtain ⟨i, m⟩ := u
  obtain ⟨j, m'⟩ := u'
  obtain rfl := k2_fin_eq S L i
  obtain rfl := k2_fin_eq S L j
  have : m = m' := ZMod.val_injective _ hlab
  rw [this]

/-! #### Normalised frame coordinates and the kink edges as coordinate constraints -/

/-- normalised coordinates: `q = r₀ + x q • d + y q • n` -/
def k2_x (q : Plane) : ℝ := k2_X S L q / k2_dd S L
def k2_y (q : Plane) : ℝ := k2_Y S L q / k2_dd S L

theorem k2_x_frame (α β : ℝ) : k2_x S L (k2_r₀ S L + α • k2_d S L + β • k2_n S L) = α := by
  rw [k2_x, k2_X_frame, mul_div_cancel_right₀ _ (k2_dd_pos S L).ne']

theorem k2_y_frame (α β : ℝ) : k2_y S L (k2_r₀ S L + α • k2_d S L + β • k2_n S L) = β := by
  rw [k2_y, k2_Y_frame, mul_div_cancel_right₀ _ (k2_dd_pos S L).ne']

theorem k2_eq_frame' (q : Plane) : q = k2_r₀ S L + k2_x S L q • k2_d S L + k2_y S L q • k2_n S L :=
  k2_eq_frame S L q

theorem k2_frame_ext' {q q' : Plane} (hx : k2_x S L q = k2_x S L q') (hy : k2_y S L q = k2_y S L q') :
    q = q' := by
  rw [k2_eq_frame' S L q, k2_eq_frame' S L q', hx, hy]

/-- a frame point equals `q` iff its coordinates are those of `q` -/
theorem k2_frame_eq_iff (q : Plane) (α β : ℝ) :
    q = k2_r₀ S L + α • k2_d S L + β • k2_n S L ↔ k2_x S L q = α ∧ k2_y S L q = β := by
  constructor
  · rintro rfl; exact ⟨k2_x_frame S L α β, k2_y_frame S L α β⟩
  · rintro ⟨hα, hβ⟩; rw [k2_eq_frame' S L q, hα, hβ]

theorem k2_mem_e1_iff' {u : (k2_shadow S L).Strand} (hu : k2_lab S L u = k2_av S L) (q : Plane) :
    q ∈ (k2_shadow S L).seg u ↔
      k2_y S L q = 0 ∧ -k2_t S L ≤ k2_x S L q ∧ k2_x S L q ≤ -k2_ε S L := by
  rw [k2_mem_e1_iff S L hu]
  have hε := k2_ε_lt_t S L
  constructor
  · rintro ⟨θ, h0, h1, rfl⟩
    rw [k2_x_frame, k2_y_frame]
    refine ⟨rfl, ?_, ?_⟩ <;> nlinarith
  · rintro ⟨hy, h1, h2⟩
    have hne : k2_t S L - k2_ε S L ≠ 0 := by linarith
    refine ⟨(k2_x S L q + k2_t S L) / (k2_t S L - k2_ε S L), ?_, ?_, ?_⟩
    · apply div_nonneg <;> linarith
    · rw [div_le_one (by linarith)]; linarith
    · rw [k2_frame_eq_iff, hy]
      refine ⟨?_, rfl⟩
      field_simp
      ring

theorem k2_mem_e5_iff' {u : (k2_shadow S L).Strand} (hu : k2_lab S L u = k2_av S L + 4) (q : Plane) :
    q ∈ (k2_shadow S L).seg u ↔
      k2_y S L q = 0 ∧ k2_ε S L ≤ k2_x S L q ∧ k2_x S L q ≤ 1 - k2_t S L := by
  rw [k2_mem_e5_iff S L hu]
  have hε := k2_ε_lt_one_sub_t S L
  constructor
  · rintro ⟨θ, h0, h1, rfl⟩
    rw [k2_x_frame, k2_y_frame]
    refine ⟨rfl, ?_, ?_⟩ <;> nlinarith
  · rintro ⟨hy, h1, h2⟩
    have hne : 1 - k2_t S L - k2_ε S L ≠ 0 := by linarith
    refine ⟨(k2_x S L q - k2_ε S L) / (1 - k2_t S L - k2_ε S L), ?_, ?_, ?_⟩
    · apply div_nonneg <;> linarith
    · rw [div_le_one (by linarith)]; linarith
    · rw [k2_frame_eq_iff, hy]
      refine ⟨?_, rfl⟩
      field_simp
      ring

theorem k2_mem_e2_iff' {u : (k2_shadow S L).Strand} (hu : k2_lab S L u = k2_av S L + 1) (q : Plane) :
    q ∈ (k2_shadow S L).seg u ↔
      0 ≤ k2_y S L q ∧ k2_y S L q ≤ k2_ε S L ∧ k2_x S L q = 2 * k2_y S L q - k2_ε S L := by
  rw [k2_mem_e2_iff S L hu]
  have hε := k2_ε_pos S L
  constructor
  · rintro ⟨θ, h0, h1, rfl⟩
    rw [k2_x_frame, k2_y_frame]
    refine ⟨by positivity, by nlinarith, by ring⟩
  · rintro ⟨h0, h1, hx⟩
    refine ⟨k2_y S L q / k2_ε S L, by positivity, (div_le_one hε).mpr h1, ?_⟩
    rw [k2_frame_eq_iff]
    constructor
    · rw [hx]; field_simp
    · field_simp

theorem k2_mem_e3_iff' {u : (k2_shadow S L).Strand} (hu : k2_lab S L u = k2_av S L + 2) (q : Plane) :
    q ∈ (k2_shadow S L).seg u ↔
      k2_y S L q = k2_ε S L ∧ -k2_ε S L ≤ k2_x S L q ∧ k2_x S L q ≤ k2_ε S L := by
  rw [k2_mem_e3_iff S L hu]
  have hε := k2_ε_pos S L
  constructor
  · rintro ⟨θ, h0, h1, rfl⟩
    rw [k2_x_frame, k2_y_frame]
    refine ⟨rfl, by nlinarith, by nlinarith⟩
  · rintro ⟨hy, h1, h2⟩
    have hne : 2 * k2_ε S L ≠ 0 := by linarith
    refine ⟨(k2_ε S L - k2_x S L q) / (2 * k2_ε S L), ?_, ?_, ?_⟩
    · apply div_nonneg <;> linarith
    · rw [div_le_one (by linarith)]; linarith
    · rw [k2_frame_eq_iff, hy]
      refine ⟨?_, rfl⟩
      field_simp
      ring

theorem k2_mem_e4_iff' {u : (k2_shadow S L).Strand} (hu : k2_lab S L u = k2_av S L + 3) (q : Plane) :
    q ∈ (k2_shadow S L).seg u ↔
      0 ≤ k2_y S L q ∧ k2_y S L q ≤ k2_ε S L ∧ k2_x S L q = k2_ε S L - 2 * k2_y S L q := by
  rw [k2_mem_e4_iff S L hu]
  have hε := k2_ε_pos S L
  constructor
  · rintro ⟨θ, h0, h1, rfl⟩
    rw [k2_x_frame, k2_y_frame]
    refine ⟨by nlinarith, by nlinarith, by ring⟩
  · rintro ⟨h0, h1, hx⟩
    refine ⟨1 - k2_y S L q / k2_ε S L, ?_, ?_, ?_⟩
    · have := (div_le_one hε).mpr h1; linarith
    · have : 0 ≤ k2_y S L q / k2_ε S L := by positivity
      linarith
    · rw [k2_frame_eq_iff]
      constructor
      · rw [hx]; field_simp; ring
      · field_simp; ring

/-- interiors of the five kink edges -/
theorem k2_mem_int_e1_iff' {u : (k2_shadow S L).Strand} (hu : k2_lab S L u = k2_av S L) (q : Plane) :
    q ∈ (k2_shadow S L).interior u ↔
      k2_y S L q = 0 ∧ -k2_t S L < k2_x S L q ∧ k2_x S L q < -k2_ε S L := by
  rw [k2_mem_int_e1_iff S L hu]
  have hε := k2_ε_lt_t S L
  constructor
  · rintro ⟨θ, h0, h1, rfl⟩
    rw [k2_x_frame, k2_y_frame]
    refine ⟨rfl, ?_, ?_⟩ <;> nlinarith
  · rintro ⟨hy, h1, h2⟩
    have hne : k2_t S L - k2_ε S L ≠ 0 := by linarith
    refine ⟨(k2_x S L q + k2_t S L) / (k2_t S L - k2_ε S L), ?_, ?_, ?_⟩
    · apply div_pos <;> linarith
    · rw [div_lt_one (by linarith)]; linarith
    · rw [k2_frame_eq_iff, hy]
      refine ⟨?_, rfl⟩
      field_simp
      ring

theorem k2_mem_int_e5_iff' {u : (k2_shadow S L).Strand} (hu : k2_lab S L u = k2_av S L + 4)
    (q : Plane) : q ∈ (k2_shadow S L).interior u ↔
      k2_y S L q = 0 ∧ k2_ε S L < k2_x S L q ∧ k2_x S L q < 1 - k2_t S L := by
  rw [k2_mem_int_e5_iff S L hu]
  have hε := k2_ε_lt_one_sub_t S L
  constructor
  · rintro ⟨θ, h0, h1, rfl⟩
    rw [k2_x_frame, k2_y_frame]
    refine ⟨rfl, ?_, ?_⟩ <;> nlinarith
  · rintro ⟨hy, h1, h2⟩
    have hne : 1 - k2_t S L - k2_ε S L ≠ 0 := by linarith
    refine ⟨(k2_x S L q - k2_ε S L) / (1 - k2_t S L - k2_ε S L), ?_, ?_, ?_⟩
    · apply div_pos <;> linarith
    · rw [div_lt_one (by linarith)]; linarith
    · rw [k2_frame_eq_iff, hy]
      refine ⟨?_, rfl⟩
      field_simp
      ring

theorem k2_mem_int_e2_iff' {u : (k2_shadow S L).Strand} (hu : k2_lab S L u = k2_av S L + 1)
    (q : Plane) : q ∈ (k2_shadow S L).interior u ↔
      0 < k2_y S L q ∧ k2_y S L q < k2_ε S L ∧ k2_x S L q = 2 * k2_y S L q - k2_ε S L := by
  rw [k2_mem_int_e2_iff S L hu]
  have hε := k2_ε_pos S L
  constructor
  · rintro ⟨θ, h0, h1, rfl⟩
    rw [k2_x_frame, k2_y_frame]
    refine ⟨by positivity, by nlinarith, by ring⟩
  · rintro ⟨h0, h1, hx⟩
    refine ⟨k2_y S L q / k2_ε S L, by positivity, (div_lt_one hε).mpr h1, ?_⟩
    rw [k2_frame_eq_iff]
    constructor
    · rw [hx]; field_simp
    · field_simp

theorem k2_mem_int_e3_iff' {u : (k2_shadow S L).Strand} (hu : k2_lab S L u = k2_av S L + 2)
    (q : Plane) : q ∈ (k2_shadow S L).interior u ↔
      k2_y S L q = k2_ε S L ∧ -k2_ε S L < k2_x S L q ∧ k2_x S L q < k2_ε S L := by
  rw [k2_mem_int_e3_iff S L hu]
  have hε := k2_ε_pos S L
  constructor
  · rintro ⟨θ, h0, h1, rfl⟩
    rw [k2_x_frame, k2_y_frame]
    refine ⟨rfl, by nlinarith, by nlinarith⟩
  · rintro ⟨hy, h1, h2⟩
    have hne : 2 * k2_ε S L ≠ 0 := by linarith
    refine ⟨(k2_ε S L - k2_x S L q) / (2 * k2_ε S L), ?_, ?_, ?_⟩
    · apply div_pos <;> linarith
    · rw [div_lt_one (by linarith)]; linarith
    · rw [k2_frame_eq_iff, hy]
      refine ⟨?_, rfl⟩
      field_simp
      ring

theorem k2_mem_int_e4_iff' {u : (k2_shadow S L).Strand} (hu : k2_lab S L u = k2_av S L + 3)
    (q : Plane) : q ∈ (k2_shadow S L).interior u ↔
      0 < k2_y S L q ∧ k2_y S L q < k2_ε S L ∧ k2_x S L q = k2_ε S L - 2 * k2_y S L q := by
  rw [k2_mem_int_e4_iff S L hu]
  have hε := k2_ε_pos S L
  constructor
  · rintro ⟨θ, h0, h1, rfl⟩
    rw [k2_x_frame, k2_y_frame]
    refine ⟨by nlinarith, by nlinarith, by ring⟩
  · rintro ⟨h0, h1, hx⟩
    refine ⟨1 - k2_y S L q / k2_ε S L, ?_, ?_, ?_⟩
    · have := (div_lt_one hε).mpr h1; linarith
    · have : 0 < k2_y S L q / k2_ε S L := by positivity
      linarith
    · rw [k2_frame_eq_iff]
      constructor
      · rw [hx]; field_simp; ring
      · field_simp; ring

/-- the strand `s₀` of `D` and its points in coordinates -/
theorem k2_mem_s₀_iff (q : Plane) :
    q ∈ S.D.Γ.seg (k2_s₀ S L) ↔ k2_y S L q = 0 ∧ -k2_t S L ≤ k2_x S L q ∧ k2_x S L q ≤ 1 - k2_t S L := by
  rw [Shadow.mem_seg_iff]
  simp only [k2_edgePt_s₀_frame]
  constructor
  · rintro ⟨θ, h0, h1, rfl⟩
    rw [k2_x_frame, k2_y_frame]
    exact ⟨rfl, by linarith, by linarith⟩
  · rintro ⟨hy, h1, h2⟩
    refine ⟨k2_x S L q + k2_t S L, by linarith, by linarith, ?_⟩
    rw [k2_frame_eq_iff, hy]
    exact ⟨by ring, rfl⟩

theorem k2_mem_int_s₀_iff (q : Plane) :
    q ∈ S.D.Γ.interior (k2_s₀ S L) ↔
      k2_y S L q = 0 ∧ -k2_t S L < k2_x S L q ∧ k2_x S L q < 1 - k2_t S L := by
  rw [Shadow.mem_interior_iff]
  simp only [k2_edgePt_s₀_frame]
  constructor
  · rintro ⟨θ, h0, h1, rfl⟩
    rw [k2_x_frame, k2_y_frame]
    exact ⟨rfl, by linarith, by linarith⟩
  · rintro ⟨hy, h1, h2⟩
    refine ⟨k2_x S L q + k2_t S L, by linarith, by linarith, ?_⟩
    rw [k2_frame_eq_iff, hy]
    exact ⟨by ring, rfl⟩

/-- the coordinates of the named points -/
theorem k2_xy_A : k2_x S L (k2_A S L) = -k2_ε S L ∧ k2_y S L (k2_A S L) = 0 := by
  rw [k2_A_frame, k2_x_frame, k2_y_frame]; exact ⟨rfl, rfl⟩
theorem k2_xy_B : k2_x S L (k2_B S L) = k2_ε S L ∧ k2_y S L (k2_B S L) = k2_ε S L := by
  rw [k2_B_frame, k2_x_frame, k2_y_frame]; exact ⟨rfl, rfl⟩
theorem k2_xy_C : k2_x S L (k2_C S L) = -k2_ε S L ∧ k2_y S L (k2_C S L) = k2_ε S L := by
  rw [k2_C_frame, k2_x_frame, k2_y_frame]; exact ⟨rfl, rfl⟩
theorem k2_xy_Dv : k2_x S L (k2_Dv S L) = k2_ε S L ∧ k2_y S L (k2_Dv S L) = 0 := by
  rw [k2_Dv_frame, k2_x_frame, k2_y_frame]; exact ⟨rfl, rfl⟩
theorem k2_xy_K : k2_x S L (k2_K S L) = 0 ∧ k2_y S L (k2_K S L) = k2_ε S L / 2 := by
  rw [k2_K_frame, k2_x_frame, k2_y_frame]; exact ⟨rfl, rfl⟩
theorem k2_xy_Pa : k2_x S L (k2_P S L (k2_a S L)) = -k2_t S L ∧ k2_y S L (k2_P S L (k2_a S L)) = 0 := by
  rw [k2_Pa_frame, k2_x_frame, k2_y_frame]; exact ⟨rfl, rfl⟩
theorem k2_xy_Pa1 : k2_x S L (k2_P S L (k2_a S L + 1)) = 1 - k2_t S L ∧
    k2_y S L (k2_P S L (k2_a S L + 1)) = 0 := by
  rw [k2_Pa1_frame, k2_x_frame, k2_y_frame]; exact ⟨rfl, rfl⟩

/-- points of the middle kink edges lie in the open disc -/
theorem k2_mid_mem_ball {u : (k2_shadow S L).Strand} (hu : k2_IsMid S L u) {q : Plane}
    (hq : q ∈ (k2_shadow S L).seg u) : q ∈ Metric.ball (k2_r₀ S L) (k2_ρ S L) := by
  have hε := k2_ε_pos S L
  rw [k2_eq_frame' S L q]
  apply k2_frame_mem_ball
  · rcases (by unfold k2_IsMid at hu; omega :
        k2_lab S L u = k2_av S L + 1 ∨ k2_lab S L u = k2_av S L + 2 ∨ k2_lab S L u = k2_av S L + 3)
      with h | h | h
    · rw [k2_mem_e2_iff' S L h] at hq; rw [abs_le]; constructor <;> linarith
    · rw [k2_mem_e3_iff' S L h] at hq; rw [abs_le]; constructor <;> linarith
    · rw [k2_mem_e4_iff' S L h] at hq; rw [abs_le]; constructor <;> linarith
  · rcases (by unfold k2_IsMid at hu; omega :
        k2_lab S L u = k2_av S L + 1 ∨ k2_lab S L u = k2_av S L + 2 ∨ k2_lab S L u = k2_av S L + 3)
      with h | h | h
    · rw [k2_mem_e2_iff' S L h] at hq; rw [abs_le]; constructor <;> linarith
    · rw [k2_mem_e3_iff' S L h] at hq; rw [abs_le]; constructor <;> linarith
    · rw [k2_mem_e4_iff' S L h] at hq; rw [abs_le]; constructor <;> linarith

theorem k2_mid_mem_U {u : (k2_shadow S L).Strand} (hu : k2_IsMid S L u) {q : Plane}
    (hq : q ∈ (k2_shadow S L).seg u) : q ∈ k2_U S L :=
  Metric.ball_subset_closedBall (k2_mid_mem_ball S L hu hq)

/-- points of old strands of `D'` lie outside the closed disc -/
theorem k2_old_not_mem_U {u : (k2_shadow S L).Strand} (hu : k2_IsOld S L u) {q : Plane}
    (hq : q ∈ (k2_shadow S L).seg u) : q ∉ k2_U S L := by
  rw [k2_seg_old S L hu] at hq
  exact k2_not_mem_U_of_mem_seg S L (k2_orig_ne_s₀ S L hu) hq

/-- the kink double point lies on `e2` and `e4` (as the midpoint), inside the open disc, on no
other kink edge -/
theorem k2_K_mem_e2 {u : (k2_shadow S L).Strand} (hu : k2_lab S L u = k2_av S L + 1) :
    k2_K S L ∈ (k2_shadow S L).seg u := by
  rw [k2_mem_e2_iff' S L hu, (k2_xy_K S L).1, (k2_xy_K S L).2]
  have := k2_ε_pos S L
  exact ⟨by linarith, by linarith, by ring⟩
theorem k2_K_mem_e4 {u : (k2_shadow S L).Strand} (hu : k2_lab S L u = k2_av S L + 3) :
    k2_K S L ∈ (k2_shadow S L).seg u := by
  rw [k2_mem_e4_iff' S L hu, (k2_xy_K S L).1, (k2_xy_K S L).2]
  have := k2_ε_pos S L
  exact ⟨by linarith, by linarith, by ring⟩
theorem k2_K_mem_int_e2 {u : (k2_shadow S L).Strand} (hu : k2_lab S L u = k2_av S L + 1) :
    k2_K S L ∈ (k2_shadow S L).interior u := by
  rw [k2_mem_int_e2_iff' S L hu, (k2_xy_K S L).1, (k2_xy_K S L).2]
  have := k2_ε_pos S L
  exact ⟨by linarith, by linarith, by ring⟩
theorem k2_K_mem_int_e4 {u : (k2_shadow S L).Strand} (hu : k2_lab S L u = k2_av S L + 3) :
    k2_K S L ∈ (k2_shadow S L).interior u := by
  rw [k2_mem_int_e4_iff' S L hu, (k2_xy_K S L).1, (k2_xy_K S L).2]
  have := k2_ε_pos S L
  exact ⟨by linarith, by linarith, by ring⟩
theorem k2_K_mem_ball : k2_K S L ∈ Metric.ball (k2_r₀ S L) (k2_ρ S L) := by
  rw [k2_K_frame]
  have := k2_ε_pos S L
  apply k2_frame_mem_ball <;> rw [abs_of_nonneg (by linarith)] <;> linarith

/-- the common points of `e2` and `e4`: only `K` -/
theorem k2_eq_K_of_mem_e2_e4 {u u' : (k2_shadow S L).Strand} (hu : k2_lab S L u = k2_av S L + 1)
    (hu' : k2_lab S L u' = k2_av S L + 3) {q : Plane} (hq : q ∈ (k2_shadow S L).seg u)
    (hq' : q ∈ (k2_shadow S L).seg u') : q = k2_K S L := by
  rw [k2_mem_e2_iff' S L hu] at hq
  rw [k2_mem_e4_iff' S L hu'] at hq'
  apply k2_frame_ext' S L
  · rw [(k2_xy_K S L).1]; linarith [hq.2.2, hq'.2.2]
  · rw [(k2_xy_K S L).2]; linarith [hq.2.2, hq'.2.2]

/-! #### Non-middle strands: segments inside the originals, directions positively proportional -/

theorem k2_lab_inj {u u' : (k2_shadow S L).Strand} (h : k2_lab S L u = k2_lab S L u') : u = u' := by
  obtain ⟨i, m⟩ := u
  obtain ⟨j, m'⟩ := u'
  obtain rfl := k2_fin_eq S L i
  obtain rfl := k2_fin_eq S L j
  have : m = m' := ZMod.val_injective _ h
  rw [this]

theorem k2_not_isMid_iff (u : (k2_shadow S L).Strand) :
    ¬ k2_IsMid S L u ↔ k2_IsOld S L u ∨ k2_lab S L u = k2_av S L ∨ k2_lab S L u = k2_av S L + 4 := by
  unfold k2_IsMid k2_IsOld; omega

theorem k2_isMid_cases {u : (k2_shadow S L).Strand} (hu : k2_IsMid S L u) :
    k2_lab S L u = k2_av S L + 1 ∨ k2_lab S L u = k2_av S L + 2 ∨ k2_lab S L u = k2_av S L + 3 := by
  unfold k2_IsMid at hu; omega

theorem k2_isOld_of_lt {u : (k2_shadow S L).Strand} (h : k2_lab S L u < k2_av S L) : k2_IsOld S L u :=
  Or.inl h
theorem k2_isOld_of_ge {u : (k2_shadow S L).Strand} (h : k2_av S L + 5 ≤ k2_lab S L u) :
    k2_IsOld S L u := Or.inr h

/-- the direction of a non-middle strand is a positive multiple of that of its original -/
theorem k2_dir_eq_smul_orig {u : (k2_shadow S L).Strand} (hu : ¬ k2_IsMid S L u) :
    ∃ l : ℝ, 0 < l ∧ (k2_shadow S L).dir u = l • S.D.Γ.dir (k2_orig S L u) := by
  rw [k2_not_isMid_iff] at hu
  rcases hu with hu | hu | hu
  · exact ⟨1, one_pos, by rw [one_smul, k2_dir_old S L hu]⟩
  · refine ⟨k2_t S L - k2_ε S L, by linarith [k2_ε_lt_t S L], ?_⟩
    rw [k2_dir_e1 S L hu, k2_orig_of_eq_a S L hu]
  · refine ⟨1 - k2_t S L - k2_ε S L, by linarith [k2_ε_lt_one_sub_t S L], ?_⟩
    rw [k2_dir_e5 S L hu, k2_orig_of_eq_a4 S L hu]

/-- the segment of a non-middle strand lies in that of its original -/
theorem k2_seg_subset_orig {u : (k2_shadow S L).Strand} (hu : ¬ k2_IsMid S L u) :
    (k2_shadow S L).seg u ⊆ S.D.Γ.seg (k2_orig S L u) := by
  rw [k2_not_isMid_iff] at hu
  intro q hq
  rcases hu with hu | hu | hu
  · rwa [k2_seg_old S L hu] at hq
  · rw [k2_orig_of_eq_a S L hu, k2_mem_s₀_iff]
    rw [k2_mem_e1_iff' S L hu] at hq
    have := k2_ε_pos S L; have := k2_t_lt_one S L
    exact ⟨hq.1, hq.2.1, by linarith [hq.2.2]⟩
  · rw [k2_orig_of_eq_a4 S L hu, k2_mem_s₀_iff]
    rw [k2_mem_e5_iff' S L hu] at hq
    have := k2_ε_pos S L; have := k2_t_pos S L
    exact ⟨hq.1, by linarith [hq.2.1], hq.2.2⟩

theorem k2_interior_subset_orig {u : (k2_shadow S L).Strand} (hu : ¬ k2_IsMid S L u) :
    (k2_shadow S L).interior u ⊆ S.D.Γ.interior (k2_orig S L u) := by
  rw [k2_not_isMid_iff] at hu
  intro q hq
  rcases hu with hu | hu | hu
  · rwa [k2_interior_old S L hu] at hq
  · rw [k2_orig_of_eq_a S L hu, k2_mem_int_s₀_iff]
    rw [k2_mem_int_e1_iff' S L hu] at hq
    have := k2_ε_pos S L; have := k2_t_lt_one S L
    exact ⟨hq.1, hq.2.1, by linarith [hq.2.2]⟩
  · rw [k2_orig_of_eq_a4 S L hu, k2_mem_int_s₀_iff]
    rw [k2_mem_int_e5_iff' S L hu] at hq
    have := k2_ε_pos S L; have := k2_t_pos S L
    exact ⟨hq.1, by linarith [hq.2.1], hq.2.2⟩

/-- two non-middle strands with the same original: equal, or `{e1, e5}` -/
theorem k2_eq_of_orig_eq {u u' : (k2_shadow S L).Strand} (hu : ¬ k2_IsMid S L u)
    (hu' : ¬ k2_IsMid S L u') (h : k2_orig S L u = k2_orig S L u') :
    u = u' ∨ (k2_lab S L u = k2_av S L ∧ k2_lab S L u' = k2_av S L + 4) ∨
      (k2_lab S L u = k2_av S L + 4 ∧ k2_lab S L u' = k2_av S L) := by
  rw [k2_not_isMid_iff] at hu hu'
  rcases hu with hu | hu | hu <;> rcases hu' with hu' | hu' | hu'
  · exact Or.inl (k2_orig_injOn S L hu hu' h)
  · exact absurd (h.trans (k2_orig_of_eq_a S L hu')) (k2_orig_ne_s₀ S L hu)
  · exact absurd (h.trans (k2_orig_of_eq_a4 S L hu')) (k2_orig_ne_s₀ S L hu)
  · exact absurd (h.symm.trans (k2_orig_of_eq_a S L hu)) (k2_orig_ne_s₀ S L hu')
  · exact Or.inl (k2_lab_inj S L (hu.trans hu'.symm))
  · exact Or.inr (Or.inl ⟨hu, hu'⟩)
  · exact absurd (h.symm.trans (k2_orig_of_eq_a4 S L hu)) (k2_orig_ne_s₀ S L hu')
  · exact Or.inr (Or.inr ⟨hu, hu'⟩)
  · exact Or.inl (k2_lab_inj S L (hu.trans hu'.symm))

/-! #### Which pairs of kink edges meet -/

/-- `e1` and `e5` are disjoint -/
theorem k2_e1_e5_disjoint {u u' : (k2_shadow S L).Strand} (hu : k2_lab S L u = k2_av S L)
    (hu' : k2_lab S L u' = k2_av S L + 4) {q : Plane} (hq : q ∈ (k2_shadow S L).seg u) :
    q ∉ (k2_shadow S L).seg u' := by
  rw [k2_mem_e1_iff' S L hu] at hq
  rw [k2_mem_e5_iff' S L hu']
  have := k2_ε_pos S L
  intro h; linarith [hq.2.2, h.2.1]

/-- `e1` meets neither `e3` nor `e4`; `e5` meets neither `e2` nor `e3` -/
theorem k2_e1_e3_disjoint {u u' : (k2_shadow S L).Strand} (hu : k2_lab S L u = k2_av S L)
    (hu' : k2_lab S L u' = k2_av S L + 2) {q : Plane} (hq : q ∈ (k2_shadow S L).seg u) :
    q ∉ (k2_shadow S L).seg u' := by
  rw [k2_mem_e1_iff' S L hu] at hq
  rw [k2_mem_e3_iff' S L hu']
  have := k2_ε_pos S L
  intro h; linarith [hq.1, h.1]

theorem k2_e1_e4_disjoint {u u' : (k2_shadow S L).Strand} (hu : k2_lab S L u = k2_av S L)
    (hu' : k2_lab S L u' = k2_av S L + 3) {q : Plane} (hq : q ∈ (k2_shadow S L).seg u) :
    q ∉ (k2_shadow S L).seg u' := by
  rw [k2_mem_e1_iff' S L hu] at hq
  rw [k2_mem_e4_iff' S L hu']
  have := k2_ε_pos S L
  intro h; linarith [hq.1, hq.2.2, h.2.2]

theorem k2_e2_e5_disjoint {u u' : (k2_shadow S L).Strand} (hu : k2_lab S L u = k2_av S L + 1)
    (hu' : k2_lab S L u' = k2_av S L + 4) {q : Plane} (hq : q ∈ (k2_shadow S L).seg u) :
    q ∉ (k2_shadow S L).seg u' := by
  rw [k2_mem_e2_iff' S L hu] at hq
  rw [k2_mem_e5_iff' S L hu']
  have := k2_ε_pos S L
  intro h; linarith [hq.2.2, h.1, h.2.1]

theorem k2_e3_e5_disjoint {u u' : (k2_shadow S L).Strand} (hu : k2_lab S L u = k2_av S L + 2)
    (hu' : k2_lab S L u' = k2_av S L + 4) {q : Plane} (hq : q ∈ (k2_shadow S L).seg u) :
    q ∉ (k2_shadow S L).seg u' := by
  rw [k2_mem_e3_iff' S L hu] at hq
  rw [k2_mem_e5_iff' S L hu']
  have := k2_ε_pos S L
  intro h; linarith [hq.1, h.1]

/-- old strands of `D'` meet no middle kink edge -/
theorem k2_old_mid_disjoint {u u' : (k2_shadow S L).Strand} (hu : k2_IsOld S L u)
    (hu' : k2_IsMid S L u') {q : Plane} (hq : q ∈ (k2_shadow S L).seg u) :
    q ∉ (k2_shadow S L).seg u' :=
  fun h => k2_old_not_mem_U S L hu hq (k2_mid_mem_U S L hu' h)

/-- **interior points of two kink edges**: the edges coincide or are `{e2, e4}` -/
theorem k2_kink_int_meet {u u' : (k2_shadow S L).Strand} (hu : ¬ k2_IsOld S L u)
    (hu' : ¬ k2_IsOld S L u') {q : Plane} (hq : q ∈ (k2_shadow S L).interior u)
    (hq' : q ∈ (k2_shadow S L).interior u') :
    u = u' ∨ (k2_lab S L u = k2_av S L + 1 ∧ k2_lab S L u' = k2_av S L + 3) ∨
      (k2_lab S L u = k2_av S L + 3 ∧ k2_lab S L u' = k2_av S L + 1) := by
  have hε := k2_ε_pos S L
  have c1 : k2_lab S L u = k2_av S L ∨ k2_lab S L u = k2_av S L + 1 ∨ k2_lab S L u = k2_av S L + 2 ∨
      k2_lab S L u = k2_av S L + 3 ∨ k2_lab S L u = k2_av S L + 4 := by unfold k2_IsOld at hu; omega
  have c2 : k2_lab S L u' = k2_av S L ∨ k2_lab S L u' = k2_av S L + 1 ∨ k2_lab S L u' = k2_av S L + 2 ∨
      k2_lab S L u' = k2_av S L + 3 ∨ k2_lab S L u' = k2_av S L + 4 := by unfold k2_IsOld at hu'; omega
  rcases c1 with h | h | h | h | h <;> rcases c2 with h' | h' | h' | h' | h'
  · exact Or.inl (k2_lab_inj S L (h.trans h'.symm))
  · rw [k2_mem_int_e1_iff' S L h] at hq; rw [k2_mem_int_e2_iff' S L h'] at hq'; exfalso; linarith [hq.1, hq'.1]
  · rw [k2_mem_int_e1_iff' S L h] at hq; rw [k2_mem_int_e3_iff' S L h'] at hq'; exfalso; linarith [hq.1, hq'.1]
  · rw [k2_mem_int_e1_iff' S L h] at hq; rw [k2_mem_int_e4_iff' S L h'] at hq'; exfalso; linarith [hq.1, hq'.1]
  · rw [k2_mem_int_e1_iff' S L h] at hq; rw [k2_mem_int_e5_iff' S L h'] at hq'; exfalso
    linarith [hq.2.2, hq'.2.1]
  · rw [k2_mem_int_e2_iff' S L h] at hq; rw [k2_mem_int_e1_iff' S L h'] at hq'; exfalso; linarith [hq.1, hq'.1]
  · exact Or.inl (k2_lab_inj S L (h.trans h'.symm))
  · rw [k2_mem_int_e2_iff' S L h] at hq; rw [k2_mem_int_e3_iff' S L h'] at hq'; exfalso
    linarith [hq.2.1, hq'.1]
  · exact Or.inr (Or.inl ⟨h, h'⟩)
  · rw [k2_mem_int_e2_iff' S L h] at hq; rw [k2_mem_int_e5_iff' S L h'] at hq'; exfalso; linarith [hq.1, hq'.1]
  · rw [k2_mem_int_e3_iff' S L h] at hq; rw [k2_mem_int_e1_iff' S L h'] at hq'; exfalso; linarith [hq.1, hq'.1]
  · rw [k2_mem_int_e3_iff' S L h] at hq; rw [k2_mem_int_e2_iff' S L h'] at hq'; exfalso
    linarith [hq.1, hq'.2.1]
  · exact Or.inl (k2_lab_inj S L (h.trans h'.symm))
  · rw [k2_mem_int_e3_iff' S L h] at hq; rw [k2_mem_int_e4_iff' S L h'] at hq'; exfalso
    linarith [hq.1, hq'.2.1]
  · rw [k2_mem_int_e3_iff' S L h] at hq; rw [k2_mem_int_e5_iff' S L h'] at hq'; exfalso; linarith [hq.1, hq'.1]
  · rw [k2_mem_int_e4_iff' S L h] at hq; rw [k2_mem_int_e1_iff' S L h'] at hq'; exfalso; linarith [hq.1, hq'.1]
  · exact Or.inr (Or.inr ⟨h, h'⟩)
  · rw [k2_mem_int_e4_iff' S L h] at hq; rw [k2_mem_int_e3_iff' S L h'] at hq'; exfalso
    linarith [hq.2.1, hq'.1]
  · exact Or.inl (k2_lab_inj S L (h.trans h'.symm))
  · rw [k2_mem_int_e4_iff' S L h] at hq; rw [k2_mem_int_e5_iff' S L h'] at hq'; exfalso; linarith [hq.1, hq'.1]
  · rw [k2_mem_int_e5_iff' S L h] at hq; rw [k2_mem_int_e1_iff' S L h'] at hq'; exfalso
    linarith [hq.2.1, hq'.2.2]
  · rw [k2_mem_int_e5_iff' S L h] at hq; rw [k2_mem_int_e2_iff' S L h'] at hq'; exfalso; linarith [hq.1, hq'.1]
  · rw [k2_mem_int_e5_iff' S L h] at hq; rw [k2_mem_int_e3_iff' S L h'] at hq'; exfalso; linarith [hq.1, hq'.1]
  · rw [k2_mem_int_e5_iff' S L h] at hq; rw [k2_mem_int_e4_iff' S L h'] at hq'; exfalso; linarith [hq.1, hq'.1]
  · exact Or.inl (k2_lab_inj S L (h.trans h'.symm))

/-- the determinant of the two kink branches: `det (dir e2) (dir e4) = 4 ε² |d|²` -/
theorem k2_det_e2_e4 {u u' : (k2_shadow S L).Strand} (hu : k2_lab S L u = k2_av S L + 1)
    (hu' : k2_lab S L u' = k2_av S L + 3) :
    det ((k2_shadow S L).dir u) ((k2_shadow S L).dir u') = 4 * k2_ε S L ^ 2 * k2_dd S L := by
  rw [k2_dir_e2 S L hu, k2_dir_e4 S L hu']
  simp only [det, planeDot, k2_n, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub,
    Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

theorem k2_det_e4_e2 {u u' : (k2_shadow S L).Strand} (hu : k2_lab S L u = k2_av S L + 3)
    (hu' : k2_lab S L u' = k2_av S L + 1) :
    det ((k2_shadow S L).dir u) ((k2_shadow S L).dir u') = -(4 * k2_ε S L ^ 2 * k2_dd S L) := by
  rw [k2_dir_e4 S L hu, k2_dir_e2 S L hu']
  simp only [det, planeDot, k2_n, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub,
    Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

theorem k2_four_ε_sq_dd_pos : 0 < 4 * k2_ε S L ^ 2 * k2_dd S L := by
  have := k2_ε_pos S L; have := k2_dd_pos S L; positivity

/-! #### The two neighbours of `s₀` in `D`; adjacency from labels; old strands against `e1`, `e5` -/

/-- `seg (a−1) ∩ seg a = {P a}`, `seg a ∩ seg (a+1) = {P (a+1)}` (generic `D`) -/
theorem k2_seg_pred_inter :
    S.D.Γ.seg ⟨L.r.1, k2_a S L - 1⟩ ∩ S.D.Γ.seg (k2_s₀ S L) = {k2_P S L (k2_a S L)} := by
  have h := S.D.generic.seg_inter_succ ⟨L.r.1, k2_a S L - 1⟩
  simp only [sub_add_cancel] at h
  rw [h]
  show ({S.D.Γ.tail ⟨L.r.1, k2_a S L - 1 + 1⟩} : Set Plane) = _
  simp only [sub_add_cancel]
  rfl

theorem k2_seg_succ_inter :
    S.D.Γ.seg (k2_s₀ S L) ∩ S.D.Γ.seg ⟨L.r.1, k2_a S L + 1⟩ = {k2_P S L (k2_a S L + 1)} :=
  S.D.generic.seg_inter_succ (k2_s₀ S L)

/-- adjacency and incidence in `D'` from label values -/
theorem k2_adjacent_of_lab {s t : (k2_shadow S L).Strand}
    (h : k2_lab S L t = k2_lab S L s ∨ k2_lab S L t = k2_lab S L s + 1 ∨
      k2_lab S L s = k2_lab S L t + 1 ∨ (k2_lab S L s + 1 = k2_k S L + 4 ∧ k2_lab S L t = 0) ∨
      (k2_lab S L t + 1 = k2_k S L + 4 ∧ k2_lab S L s = 0)) : (k2_shadow S L).Adjacent s t := by
  rw [k2_adjacent_iff, k2_zmod_adjacent_iff]; exact h

theorem k2_not_adjacent_lab {s t : (k2_shadow S L).Strand} (h : ¬ (k2_shadow S L).Adjacent s t) :
    ¬ (k2_lab S L t = k2_lab S L s ∨ k2_lab S L t = k2_lab S L s + 1 ∨
      k2_lab S L s = k2_lab S L t + 1 ∨ (k2_lab S L s + 1 = k2_k S L + 4 ∧ k2_lab S L t = 0) ∨
      (k2_lab S L t + 1 = k2_k S L + 4 ∧ k2_lab S L s = 0)) := by
  rwa [k2_adjacent_iff, k2_zmod_adjacent_iff] at h

theorem k2_incidentTail_of_lab {s t : (k2_shadow S L).Strand}
    (h : k2_lab S L t = k2_lab S L s ∨ k2_lab S L s = k2_lab S L t + 1 ∨
      (k2_lab S L t + 1 = k2_k S L + 4 ∧ k2_lab S L s = 0)) : (k2_shadow S L).IncidentTail s t := by
  rw [k2_incidentTail_iff, k2_zmod_incident_iff]; exact h

theorem k2_not_incidentTail_lab {s t : (k2_shadow S L).Strand}
    (h : ¬ (k2_shadow S L).IncidentTail s t) :
    ¬ (k2_lab S L t = k2_lab S L s ∨ k2_lab S L s = k2_lab S L t + 1 ∨
      (k2_lab S L t + 1 = k2_k S L + 4 ∧ k2_lab S L s = 0)) := by
  rwa [k2_incidentTail_iff, k2_zmod_incident_iff] at h

/-- adjacency / incidence of an original with `s₀`, by values -/
theorem k2_adjacent_orig_s₀_iff (u : (k2_shadow S L).Strand) :
    S.D.Γ.Adjacent (k2_orig S L u) (k2_s₀ S L) ↔
      k2_av S L = (k2_orig S L u).2.val ∨ k2_av S L = (k2_orig S L u).2.val + 1 ∨
      (k2_orig S L u).2.val = k2_av S L + 1 ∨
      ((k2_orig S L u).2.val + 1 = k2_k S L ∧ k2_av S L = 0) ∨
      (k2_av S L + 1 = k2_k S L ∧ (k2_orig S L u).2.val = 0) := by
  rw [k2_adjacent_iff_D S L _ _ (k2_orig_eq S L u) rfl, k2_zmod_adjacent_iff]
  rw [k2_orig_eq]

theorem k2_incidentTail_orig_s₀_iff (u : (k2_shadow S L).Strand) :
    S.D.Γ.IncidentTail (k2_orig S L u) (k2_s₀ S L) ↔
      k2_av S L = (k2_orig S L u).2.val ∨ (k2_orig S L u).2.val = k2_av S L + 1 ∨
      (k2_av S L + 1 = k2_k S L ∧ (k2_orig S L u).2.val = 0) := by
  rw [k2_incidentTail_iff_D S L _ _ (k2_orig_eq S L u) rfl, k2_zmod_incident_iff]
  rw [k2_orig_eq]

theorem k2_incidentTail_s₀_orig_iff (u : (k2_shadow S L).Strand) :
    S.D.Γ.IncidentTail (k2_s₀ S L) (k2_orig S L u) ↔
      (k2_orig S L u).2.val = k2_av S L ∨ k2_av S L = (k2_orig S L u).2.val + 1 ∨
      ((k2_orig S L u).2.val + 1 = k2_k S L ∧ k2_av S L = 0) := by
  rw [k2_incidentTail_iff_D S L _ _ rfl (k2_orig_eq S L u), k2_zmod_incident_iff]
  rw [k2_orig_eq]

/-- the value of the original of an old strand -/
theorem k2_orig_val_old {u : (k2_shadow S L).Strand} (hu : k2_IsOld S L u) :
    (k2_lab S L u < k2_av S L ∧ (k2_orig S L u).2.val = k2_lab S L u) ∨
      (k2_av S L + 5 ≤ k2_lab S L u ∧ (k2_orig S L u).2.val = k2_lab S L u - 4) := by
  rcases hu with hu | hu
  · exact Or.inl ⟨hu, k2_orig_val_of_le S L hu.le⟩
  · exact Or.inr ⟨hu, k2_orig_val_of_ge S L (by omega)⟩

/-- the value of an original, unfolded -/
theorem k2_orig_val_eq (u : (k2_shadow S L).Strand) :
    (k2_orig S L u).2.val = ((if k2_lab S L u ≤ k2_av S L then k2_lab S L u
      else k2_lab S L u - 4 : ℕ) : ZMod (k2_k S L)).val := by
  obtain ⟨i, m⟩ := u
  obtain rfl := k2_fin_eq S L i
  rfl

/-- an original with value `(a+1).val` is `⟨L.r.1, a + 1⟩`; with value `(a−1).val` is `⟨L.r.1, a − 1⟩` -/
theorem k2_orig_eq_succ {u : (k2_shadow S L).Strand}
    (h : (k2_orig S L u).2.val = k2_av S L + 1 ∨ (k2_av S L + 1 = k2_k S L ∧ (k2_orig S L u).2.val = 0)) :
    k2_orig S L u = ⟨L.r.1, k2_a S L + 1⟩ := by
  have hv := k2_orig_val_eq S L u
  have hav : k2_av S L = (k2_a S L).val := rfl
  have hl := k2_lab_lt S L u
  have := k2_av_lt S L
  rw [k2_orig_eq, Smoothing.Strand_mk_eq_mk_iff]
  apply ZMod.val_injective
  rw [← hv, k2_zmod_succ_val]
  rcases le_or_gt (k2_lab S L u) (k2_av S L) with hle | hlt
  · rw [k2_orig_val_of_le S L hle] at h ⊢
    split_ifs <;> omega
  · rw [k2_orig_val_of_ge S L hlt] at h ⊢
    split_ifs <;> omega

theorem k2_orig_eq_pred {u : (k2_shadow S L).Strand}
    (h : k2_av S L = (k2_orig S L u).2.val + 1 ∨ ((k2_orig S L u).2.val + 1 = k2_k S L ∧ k2_av S L = 0)) :
    k2_orig S L u = ⟨L.r.1, k2_a S L - 1⟩ := by
  have hv := k2_orig_val_eq S L u
  have hav : k2_av S L = (k2_a S L).val := rfl
  have hl := k2_lab_lt S L u
  have := k2_av_lt S L
  have := k2_three_le S L
  rw [k2_orig_eq, Smoothing.Strand_mk_eq_mk_iff]
  apply ZMod.val_injective
  rw [← hv]
  have hpred : (k2_a S L - 1).val = if k2_av S L = 0 then k2_k S L - 1 else k2_av S L - 1 := by
    split_ifs with h0
    · exact Smoothing.zval_sub_one_of_zero _ h0
    · exact Smoothing.zval_sub_one_of_pos _ (by omega)
  rw [hpred]
  rcases le_or_gt (k2_lab S L u) (k2_av S L) with hle | hlt
  · rw [k2_orig_val_of_le S L hle] at h ⊢
    split_ifs <;> omega
  · rw [k2_orig_val_of_ge S L hlt] at h ⊢
    split_ifs <;> omega

/-- an old strand through a point of `e1` is not `⟨a+1⟩`; through a point of `e5` not `⟨a−1⟩` -/
theorem k2_old_e1_ne_succ {u u' : (k2_shadow S L).Strand} (hu : k2_IsOld S L u)
    (hu' : k2_lab S L u' = k2_av S L) {q : Plane} (hq : q ∈ (k2_shadow S L).seg u)
    (hq' : q ∈ (k2_shadow S L).seg u') : k2_orig S L u ≠ ⟨L.r.1, k2_a S L + 1⟩ := by
  intro h
  rw [k2_seg_old S L hu, h] at hq
  have hs₀ : q ∈ S.D.Γ.seg (k2_s₀ S L) := by
    have := k2_seg_subset_orig S L ((k2_not_isMid_iff S L u').mpr (Or.inr (Or.inl hu'))) hq'
    rwa [k2_orig_of_eq_a S L hu'] at this
  have hmem : q ∈ S.D.Γ.seg (k2_s₀ S L) ∩ S.D.Γ.seg ⟨L.r.1, k2_a S L + 1⟩ := ⟨hs₀, hq⟩
  rw [k2_seg_succ_inter, Set.mem_singleton_iff] at hmem
  rw [k2_mem_e1_iff' S L hu'] at hq'
  have hx := (k2_xy_Pa1 S L).1
  rw [← hmem] at hx
  have := k2_ε_pos S L; have := k2_t_lt_one S L
  linarith [hq'.2.2]

theorem k2_old_e5_ne_pred {u u' : (k2_shadow S L).Strand} (hu : k2_IsOld S L u)
    (hu' : k2_lab S L u' = k2_av S L + 4) {q : Plane} (hq : q ∈ (k2_shadow S L).seg u)
    (hq' : q ∈ (k2_shadow S L).seg u') : k2_orig S L u ≠ ⟨L.r.1, k2_a S L - 1⟩ := by
  intro h
  rw [k2_seg_old S L hu, h] at hq
  have hs₀ : q ∈ S.D.Γ.seg (k2_s₀ S L) := by
    have := k2_seg_subset_orig S L ((k2_not_isMid_iff S L u').mpr (Or.inr (Or.inr hu'))) hq'
    rwa [k2_orig_of_eq_a4 S L hu'] at this
  have hmem : q ∈ S.D.Γ.seg ⟨L.r.1, k2_a S L - 1⟩ ∩ S.D.Γ.seg (k2_s₀ S L) := ⟨hq, hs₀⟩
  rw [k2_seg_pred_inter, Set.mem_singleton_iff] at hmem
  rw [k2_mem_e5_iff' S L hu'] at hq'
  have hx := (k2_xy_Pa S L).1
  rw [← hmem] at hx
  have := k2_ε_pos S L; have := k2_t_pos S L
  linarith [hq'.2.1]

/-- **an old strand meeting `e1` (resp. `e5`) without being adjacent to it in `D'` has its original
non-adjacent to `s₀` in `D`** -/
theorem k2_old_e1_not_adjacent {u u' : (k2_shadow S L).Strand} (hu : k2_IsOld S L u)
    (hu' : k2_lab S L u' = k2_av S L) (hna : ¬ (k2_shadow S L).Adjacent u u') {q : Plane}
    (hq : q ∈ (k2_shadow S L).seg u) (hq' : q ∈ (k2_shadow S L).seg u') :
    ¬ S.D.Γ.Adjacent (k2_orig S L u) (k2_s₀ S L) := by
  intro hadj
  rw [k2_adjacent_orig_s₀_iff] at hadj
  have hna' := k2_not_adjacent_lab S L hna
  have hval := k2_orig_val_old S L hu
  have hl := k2_lab_lt S L u
  have hav := k2_av_lt S L
  have hne := k2_old_e1_ne_succ S L hu hu' hq hq'
  rcases hadj with h | h | h | h | h
  · omega
  · omega
  · exact hne (k2_orig_eq_succ S L (Or.inl h))
  · omega
  · exact hne (k2_orig_eq_succ S L (Or.inr h))

theorem k2_old_e5_not_adjacent {u u' : (k2_shadow S L).Strand} (hu : k2_IsOld S L u)
    (hu' : k2_lab S L u' = k2_av S L + 4) (hna : ¬ (k2_shadow S L).Adjacent u u') {q : Plane}
    (hq : q ∈ (k2_shadow S L).seg u) (hq' : q ∈ (k2_shadow S L).seg u') :
    ¬ S.D.Γ.Adjacent (k2_orig S L u) (k2_s₀ S L) := by
  intro hadj
  rw [k2_adjacent_orig_s₀_iff] at hadj
  have hna' := k2_not_adjacent_lab S L hna
  have hval := k2_orig_val_old S L hu
  have hl := k2_lab_lt S L u
  have hav := k2_av_lt S L
  have hne := k2_old_e5_ne_pred S L hu hu' hq hq'
  rcases hadj with h | h | h | h | h
  · omega
  · exact hne (k2_orig_eq_pred S L (Or.inl h))
  · omega
  · exact hne (k2_orig_eq_pred S L (Or.inr h))
  · omega

/-- **non-adjacent non-middle strands meeting in `D'` have non-adjacent originals** -/
theorem k2_not_adjacent_orig {u u' : (k2_shadow S L).Strand} (hu : ¬ k2_IsMid S L u)
    (hu' : ¬ k2_IsMid S L u') (hna : ¬ (k2_shadow S L).Adjacent u u') {q : Plane}
    (hq : q ∈ (k2_shadow S L).seg u) (hq' : q ∈ (k2_shadow S L).seg u') :
    ¬ S.D.Γ.Adjacent (k2_orig S L u) (k2_orig S L u') := by
  rw [k2_not_isMid_iff] at hu hu'
  rcases hu with hu | hu | hu <;> rcases hu' with hu' | hu' | hu'
  · rwa [← k2_adjacent_old_iff S L hu hu']
  · rw [k2_orig_of_eq_a S L hu']; exact k2_old_e1_not_adjacent S L hu hu' hna hq hq'
  · rw [k2_orig_of_eq_a4 S L hu']; exact k2_old_e5_not_adjacent S L hu hu' hna hq hq'
  · rw [k2_orig_of_eq_a S L hu]
    exact fun h => k2_old_e1_not_adjacent S L hu' hu (fun h' => hna h'.symm) hq' hq h.symm
  · exact absurd (Shadow.Adjacent.refl _ _) (k2_lab_inj S L (hu.trans hu'.symm) ▸ hna)
  · exact absurd hq' (k2_e1_e5_disjoint S L hu hu' hq)
  · rw [k2_orig_of_eq_a4 S L hu]
    exact fun h => k2_old_e5_not_adjacent S L hu' hu (fun h' => hna h'.symm) hq' hq h.symm
  · exact absurd hq (k2_e1_e5_disjoint S L hu' hu hq')
  · exact absurd (Shadow.Adjacent.refl _ _) (k2_lab_inj S L (hu.trans hu'.symm) ▸ hna)

/-- the four kink vertices lie in the open disc -/
theorem k2_A_mem_ball : k2_A S L ∈ Metric.ball (k2_r₀ S L) (k2_ρ S L) := by
  rw [k2_A_frame]; have := k2_ε_pos S L
  apply k2_frame_mem_ball <;> simp [abs_of_pos this, this.le]
theorem k2_B_mem_ball : k2_B S L ∈ Metric.ball (k2_r₀ S L) (k2_ρ S L) := by
  rw [k2_B_frame]; have := k2_ε_pos S L
  apply k2_frame_mem_ball <;> simp [abs_of_pos this]
theorem k2_C_mem_ball : k2_C S L ∈ Metric.ball (k2_r₀ S L) (k2_ρ S L) := by
  rw [k2_C_frame]; have := k2_ε_pos S L
  apply k2_frame_mem_ball <;> simp [abs_of_pos this]
theorem k2_Dv_mem_ball : k2_Dv S L ∈ Metric.ball (k2_r₀ S L) (k2_ρ S L) := by
  rw [k2_Dv_frame]; have := k2_ε_pos S L
  apply k2_frame_mem_ball <;> simp [abs_of_pos this, this.le]

/-- the tail of a non-old strand lies in the open disc or is `P a` -/
theorem k2_tail_mem_U_of_not_old {u : (k2_shadow S L).Strand} (hu : ¬ k2_IsOld S L u)
    (hu' : k2_lab S L u ≠ k2_av S L) : (k2_shadow S L).tail u ∈ k2_U S L := by
  apply Metric.ball_subset_closedBall
  have c : k2_lab S L u = k2_av S L + 1 ∨ k2_lab S L u = k2_av S L + 2 ∨
      k2_lab S L u = k2_av S L + 3 ∨ k2_lab S L u = k2_av S L + 4 := by unfold k2_IsOld at hu; omega
  rcases c with h | h | h | h
  · rw [k2_tail_e2 S L h]; exact k2_A_mem_ball S L
  · rw [k2_tail_e3 S L h]; exact k2_B_mem_ball S L
  · rw [k2_tail_e4 S L h]; exact k2_C_mem_ball S L
  · rw [k2_tail_e5 S L h]; exact k2_Dv_mem_ball S L

/-! #### Genericity of the new shadow -/

/-- the regularity of `D`'s component, restated -/
theorem k2_reg (j : ZMod (k2_k S L)) :
    RegularPair (edge (k2_P S L) (j - 1)) (edge (k2_P S L) j) := S.D.generic.regular L.r.1 j

theorem k2_reg_smul {j : ZMod (k2_k S L)} {l m : ℝ} (hl : 0 < l) (hm : 0 < m) :
    RegularPair (l • edge (k2_P S L) (j - 1)) (m • edge (k2_P S L) j) :=
  regularPair_smul_pos hl hm (k2_reg S L j)

theorem k2_zero_sub_one : (0 : ZMod (k2_k S L)) - 1 = ((k2_k S L - 1 : ℕ) : ZMod (k2_k S L)) := by
  have := k2_three_le S L
  rw [Smoothing.zcast_sub_self (by omega), Nat.cast_one, zero_sub]

/-- the determinants at the four kink corners -/
theorem k2_det_e1_e2 : det ((k2_t S L - k2_ε S L) • k2_d S L)
    ((2 * k2_ε S L) • k2_d S L + k2_ε S L • k2_n S L) =
      -((k2_t S L - k2_ε S L) * k2_ε S L * k2_dd S L) := by
  simp only [det, planeDot, k2_n, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
    smul_eq_mul]
  ring
theorem k2_det_e2_e3 : det ((2 * k2_ε S L) • k2_d S L + k2_ε S L • k2_n S L)
    ((-(2 * k2_ε S L)) • k2_d S L) = -(2 * k2_ε S L ^ 2 * k2_dd S L) := by
  simp only [det, planeDot, k2_n, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
    smul_eq_mul]
  ring
theorem k2_det_e3_e4 : det ((-(2 * k2_ε S L)) • k2_d S L)
    ((2 * k2_ε S L) • k2_d S L - k2_ε S L • k2_n S L) = -(2 * k2_ε S L ^ 2 * k2_dd S L) := by
  simp only [det, planeDot, k2_n, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd,
    smul_eq_mul]
  ring
theorem k2_det_e4_e5 : det ((2 * k2_ε S L) • k2_d S L - k2_ε S L • k2_n S L)
    ((1 - k2_t S L - k2_ε S L) • k2_d S L) = -(k2_ε S L * (1 - k2_t S L - k2_ε S L) * k2_dd S L) := by
  simp only [det, planeDot, k2_n, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd,
    smul_eq_mul]
  ring

/-- **consecutive edges of the new tuple form regular pairs** (by label value) -/
theorem k2_regular_E (n : ℕ) (hn : n < k2_k S L + 4) :
    RegularPair (k2_E S L (if n = 0 then k2_k S L + 3 else n - 1)) (k2_E S L n) := by
  have hk := k2_three_le S L
  have hav := k2_av_lt S L
  have hε := k2_ε_pos S L
  have ht1 : 0 < k2_t S L - k2_ε S L := by linarith [k2_ε_lt_t S L]
  have ht2 : 0 < 1 - k2_t S L - k2_ε S L := by linarith [k2_ε_lt_one_sub_t S L]
  have hdd := k2_dd_pos S L
  have hd : k2_d S L = edge (k2_P S L) (k2_a S L) := rfl
  have hcast : ((k2_av S L : ℕ) : ZMod (k2_k S L)) = k2_a S L := ZMod.natCast_zmod_val _
  have e12 : k2_B S L - k2_A S L = (2 * k2_ε S L) • k2_d S L + k2_ε S L • k2_n S L := by
    rw [k2_B, k2_A, two_mul, add_smul]; abel
  have e23 : k2_C S L - k2_B S L = (-(2 * k2_ε S L)) • k2_d S L := by
    rw [k2_B, k2_C, two_mul, neg_smul, add_smul]; abel
  have e34 : k2_Dv S L - k2_C S L = (2 * k2_ε S L) • k2_d S L - k2_ε S L • k2_n S L := by
    rw [k2_Dv, k2_C, two_mul, add_smul]; abel
  by_cases h0 : n = 0
  · subst h0
    rw [ite_eq_left rfl]
    by_cases ha : k2_av S L = k2_k S L - 1
    · -- `a = k − 1`: the last edge is `e5`, the first edge is old `0`
      have h4 : k2_k S L + 3 = k2_av S L + 4 := by omega
      have h5 : (0 : ZMod (k2_k S L)) - 1 = k2_a S L := by
        rw [k2_zero_sub_one, ← hcast, ha]
      have hav0 : 0 < k2_av S L := by rw [ha]; exact Nat.sub_pos_of_lt (by omega)
      rw [h4, k2_E_a4, k2_E_of_lt S L hav0, Nat.cast_zero, hd, ← h5]
      have := k2_reg_smul S L (j := 0) ht2 one_pos
      rwa [one_smul] at this
    · have h5 : k2_k S L + 3 - 4 = k2_k S L - 1 := by omega
      rw [k2_E_of_ge S L (by omega), h5, ← k2_zero_sub_one]
      rcases Nat.eq_zero_or_pos (k2_av S L) with h0' | h0'
      · -- `a = 0`: the first edge is `e1`
        have hE0 := k2_E_a S L
        rw [h0'] at hE0
        rw [hE0, hd, ← hcast, h0', Nat.cast_zero]
        have := k2_reg_smul S L (j := 0) one_pos ht1
        rwa [one_smul] at this
      · rw [k2_E_of_lt S L h0', Nat.cast_zero]
        exact k2_reg S L 0
  · rw [ite_eq_right h0]
    rcases (by omega : n < k2_av S L ∨ n = k2_av S L ∨ n = k2_av S L + 1 ∨ n = k2_av S L + 2 ∨
        n = k2_av S L + 3 ∨ n = k2_av S L + 4 ∨ n = k2_av S L + 5 ∨ k2_av S L + 6 ≤ n)
      with h | h | h | h | h | h | h | h
    · -- old, old
      rw [k2_E_of_lt S L (by omega), k2_E_of_lt S L h, Smoothing.zcast_pred (v := n) (by omega)]
      exact k2_reg S L _
    · -- `n = a > 0`: old `a − 1`, then `e1`
      have e : ((k2_av S L - 1 : ℕ) : ZMod (k2_k S L)) = k2_a S L - 1 := by
        rw [Smoothing.zcast_pred (v := k2_av S L) (by omega), hcast]
      rw [h, k2_E_of_lt S L (by omega), k2_E_a, hd, e]
      have := k2_reg_smul S L (j := k2_a S L) one_pos ht1
      rwa [one_smul] at this
    · rw [h, Nat.add_sub_cancel, k2_E_a, k2_E_a1, e12]
      apply regularPair_of_det_ne_zero
      rw [k2_det_e1_e2]
      exact neg_ne_zero.mpr (mul_pos (mul_pos ht1 hε) hdd).ne'
    · rw [h, show k2_av S L + 2 - 1 = k2_av S L + 1 by omega, k2_E_a1, k2_E_a2, e12, e23]
      apply regularPair_of_det_ne_zero
      rw [k2_det_e2_e3]
      exact neg_ne_zero.mpr (by positivity)
    · rw [h, show k2_av S L + 3 - 1 = k2_av S L + 2 by omega, k2_E_a2, k2_E_a3, e23, e34]
      apply regularPair_of_det_ne_zero
      rw [k2_det_e3_e4]
      exact neg_ne_zero.mpr (by positivity)
    · rw [h, show k2_av S L + 4 - 1 = k2_av S L + 3 by omega, k2_E_a3, k2_E_a4, e34]
      apply regularPair_of_det_ne_zero
      rw [k2_det_e4_e5]
      exact neg_ne_zero.mpr (mul_pos (mul_pos hε ht2) hdd).ne'
    · -- `n = a + 5`: `e5`, then old `a + 1`
      rw [h, show k2_av S L + 5 - 1 = k2_av S L + 4 by omega, k2_E_a4, k2_E_of_ge S L le_rfl,
        show k2_av S L + 5 - 4 = k2_av S L + 1 by omega, Nat.cast_succ, hcast, hd]
      have := k2_reg_smul S L (j := k2_a S L + 1) ht2 one_pos
      rwa [one_smul, add_sub_cancel_right] at this
    · -- old, old (after the kink)
      rw [k2_E_of_ge S L (by omega), k2_E_of_ge S L (by omega),
        show n - 1 - 4 = n - 4 - 1 by omega, Smoothing.zcast_pred (v := n - 4) (by omega)]
      exact k2_reg S L _

theorem k2_regular : ∀ i : Fin (k2_shadow S L).c, Regular ((k2_shadow S L).comp i).P := by
  intro i
  show Regular (k2_tuple S L)
  intro m
  show RegularPair (edge (k2_tuple S L) (m - 1)) (edge (k2_tuple S L) m)
  rw [k2_edge_eq, k2_edge_eq]
  have hm : (m - 1).val = if m.val = 0 then k2_k S L + 3 else m.val - 1 := by
    split_ifs with h
    · rw [Smoothing.zval_sub_one_of_zero _ h]; omega
    · exact Smoothing.zval_sub_one_of_pos _ (by omega)
  rw [hm]
  exact k2_regular_E S L m.val (ZMod.val_lt m)

/-- **no vertex lies on a non-incident edge**, by the kind of the vertex's strand -/
theorem k2_tail_off_old {s t : (k2_shadow S L).Strand} (hs : k2_IsOld S L s)
    (h : ¬ (k2_shadow S L).IncidentTail s t) : (k2_shadow S L).tail s ∉ (k2_shadow S L).seg t := by
  have hnU := k2_tail_not_mem_U S L (k2_orig S L s)
  rw [k2_tail_old S L hs]
  have hlab := k2_lab_lt S L s
  have hlt := k2_lab_lt S L t
  have hav := k2_av_lt S L
  have hk := k2_three_le S L
  have hval := k2_orig_val_old S L hs
  have h' := k2_not_incidentTail_lab S L h
  have hε := k2_ε_pos S L
  have ht0 := k2_t_pos S L
  have ht1 := k2_t_lt_one S L
  -- the tail of an old strand on `e1` or `e5`: its original is incident to `s₀`
  have key : ∀ (ht : ¬ k2_IsMid S L t), S.D.Γ.tail (k2_orig S L s) ∈ (k2_shadow S L).seg t →
      k2_orig S L t = k2_s₀ S L → S.D.Γ.IncidentTail (k2_orig S L s) (k2_s₀ S L) := by
    intro ht hmem horig
    have hmem' := k2_seg_subset_orig S L ht hmem
    rw [horig] at hmem'
    by_contra hn
    exact S.D.generic.tail_off _ _ hn hmem'
  rcases k2_kind_cases S L t with ht | ht | ht | ht | ht | ht | ht
  · have ht' := k2_isOld_of_lt S L ht
    rw [k2_seg_old S L ht']
    exact S.D.generic.tail_off _ _ (fun hi => h ((k2_incidentTail_old_iff S L hs ht').mpr hi))
  · intro hmem
    have hinc := key ((k2_not_isMid_iff S L t).mpr (Or.inr (Or.inl ht))) hmem (k2_orig_of_eq_a S L ht)
    rw [k2_incidentTail_orig_s₀_iff] at hinc
    have hx : k2_x S L (S.D.Γ.tail ⟨L.r.1, k2_a S L + 1⟩) = 1 - k2_t S L := (k2_xy_Pa1 S L).1
    rcases hinc with hi | hi | hi
    · omega
    · rw [k2_orig_eq_succ S L (Or.inl hi), k2_mem_e1_iff' S L ht] at hmem
      linarith [hmem.2.2]
    · rw [k2_orig_eq_succ S L (Or.inr hi), k2_mem_e1_iff' S L ht] at hmem
      linarith [hmem.2.2]
  · exact fun hmem => hnU (k2_mid_mem_U S L ⟨by omega, by omega⟩ hmem)
  · exact fun hmem => hnU (k2_mid_mem_U S L ⟨by omega, by omega⟩ hmem)
  · exact fun hmem => hnU (k2_mid_mem_U S L ⟨by omega, by omega⟩ hmem)
  · intro hmem
    have hinc := key ((k2_not_isMid_iff S L t).mpr (Or.inr (Or.inr ht))) hmem (k2_orig_of_eq_a4 S L ht)
    rw [k2_incidentTail_orig_s₀_iff] at hinc
    rcases hinc with hi | hi | hi
    · omega
    · omega
    · omega
  · have ht' := k2_isOld_of_ge S L ht
    rw [k2_seg_old S L ht']
    exact S.D.generic.tail_off _ _ (fun hi => h ((k2_incidentTail_old_iff S L hs ht').mpr hi))

theorem k2_tail_off_e1 {s t : (k2_shadow S L).Strand} (hs : k2_lab S L s = k2_av S L)
    (h : ¬ (k2_shadow S L).IncidentTail s t) : (k2_shadow S L).tail s ∉ (k2_shadow S L).seg t := by
  rw [k2_tail_e1 S L hs]
  have hnU : k2_P S L (k2_a S L) ∉ k2_U S L := k2_tail_not_mem_U S L (k2_s₀ S L)
  have hlab := k2_lab_lt S L s
  have hlt := k2_lab_lt S L t
  have hav := k2_av_lt S L
  have hk := k2_three_le S L
  have h' := k2_not_incidentTail_lab S L h
  have hε := k2_ε_pos S L
  have ht0 := k2_t_pos S L
  have hx := (k2_xy_Pa S L).1
  rcases k2_kind_cases S L t with ht | ht | ht | ht | ht | ht | ht
  · have ht' := k2_isOld_of_lt S L ht
    rw [k2_seg_old S L ht']
    intro hmem
    have hval := k2_orig_val_old S L ht'
    have hinc : S.D.Γ.IncidentTail (k2_s₀ S L) (k2_orig S L t) := by
      by_contra hn; exact S.D.generic.tail_off _ _ hn hmem
    rw [k2_incidentTail_s₀_orig_iff] at hinc
    omega
  · exact absurd (k2_incidentTail_of_lab S L (by omega)) h
  · exact fun hmem => hnU (k2_mid_mem_U S L ⟨by omega, by omega⟩ hmem)
  · exact fun hmem => hnU (k2_mid_mem_U S L ⟨by omega, by omega⟩ hmem)
  · exact fun hmem => hnU (k2_mid_mem_U S L ⟨by omega, by omega⟩ hmem)
  · rw [k2_mem_e5_iff' S L ht]; intro hmem; linarith [hmem.2.1]
  · have ht' := k2_isOld_of_ge S L ht
    rw [k2_seg_old S L ht']
    intro hmem
    have hval := k2_orig_val_old S L ht'
    have hinc : S.D.Γ.IncidentTail (k2_s₀ S L) (k2_orig S L t) := by
      by_contra hn; exact S.D.generic.tail_off _ _ hn hmem
    rw [k2_incidentTail_s₀_orig_iff] at hinc
    omega

/-- the common pattern for the four kink vertices: not on old strands (they lie in the disc) -/
theorem k2_kink_vertex_not_mem_old {t : (k2_shadow S L).Strand} (ht : k2_IsOld S L t) {q : Plane}
    (hq : q ∈ Metric.ball (k2_r₀ S L) (k2_ρ S L)) : q ∉ (k2_shadow S L).seg t :=
  fun hmem => k2_old_not_mem_U S L ht hmem (Metric.ball_subset_closedBall hq)

theorem k2_tail_off_e2 {s t : (k2_shadow S L).Strand} (hs : k2_lab S L s = k2_av S L + 1)
    (h : ¬ (k2_shadow S L).IncidentTail s t) : (k2_shadow S L).tail s ∉ (k2_shadow S L).seg t := by
  rw [k2_tail_e2 S L hs]
  have hlab := k2_lab_lt S L s
  have hlt := k2_lab_lt S L t
  have hav := k2_av_lt S L
  have hk := k2_three_le S L
  have hε := k2_ε_pos S L
  have hxy := k2_xy_A S L
  rcases k2_kind_cases S L t with ht | ht | ht | ht | ht | ht | ht
  · exact k2_kink_vertex_not_mem_old S L (k2_isOld_of_lt S L ht) (k2_A_mem_ball S L)
  · exact absurd (k2_incidentTail_of_lab S L (by omega)) h
  · exact absurd (k2_incidentTail_of_lab S L (by omega)) h
  · rw [k2_mem_e3_iff' S L ht]; intro hmem; linarith [hmem.1]
  · rw [k2_mem_e4_iff' S L ht]; intro hmem; linarith [hmem.2.2]
  · rw [k2_mem_e5_iff' S L ht]; intro hmem; linarith [hmem.2.1]
  · exact k2_kink_vertex_not_mem_old S L (k2_isOld_of_ge S L ht) (k2_A_mem_ball S L)

theorem k2_tail_off_e3 {s t : (k2_shadow S L).Strand} (hs : k2_lab S L s = k2_av S L + 2)
    (h : ¬ (k2_shadow S L).IncidentTail s t) : (k2_shadow S L).tail s ∉ (k2_shadow S L).seg t := by
  rw [k2_tail_e3 S L hs]
  have hlab := k2_lab_lt S L s
  have hlt := k2_lab_lt S L t
  have hav := k2_av_lt S L
  have hk := k2_three_le S L
  have hε := k2_ε_pos S L
  have hxy := k2_xy_B S L
  rcases k2_kind_cases S L t with ht | ht | ht | ht | ht | ht | ht
  · exact k2_kink_vertex_not_mem_old S L (k2_isOld_of_lt S L ht) (k2_B_mem_ball S L)
  · rw [k2_mem_e1_iff' S L ht]; intro hmem; linarith [hmem.1]
  · exact absurd (k2_incidentTail_of_lab S L (by omega)) h
  · exact absurd (k2_incidentTail_of_lab S L (by omega)) h
  · rw [k2_mem_e4_iff' S L ht]; intro hmem; linarith [hmem.2.2]
  · rw [k2_mem_e5_iff' S L ht]; intro hmem; linarith [hmem.1]
  · exact k2_kink_vertex_not_mem_old S L (k2_isOld_of_ge S L ht) (k2_B_mem_ball S L)

theorem k2_tail_off_e4 {s t : (k2_shadow S L).Strand} (hs : k2_lab S L s = k2_av S L + 3)
    (h : ¬ (k2_shadow S L).IncidentTail s t) : (k2_shadow S L).tail s ∉ (k2_shadow S L).seg t := by
  rw [k2_tail_e4 S L hs]
  have hlab := k2_lab_lt S L s
  have hlt := k2_lab_lt S L t
  have hav := k2_av_lt S L
  have hk := k2_three_le S L
  have hε := k2_ε_pos S L
  have hxy := k2_xy_C S L
  rcases k2_kind_cases S L t with ht | ht | ht | ht | ht | ht | ht
  · exact k2_kink_vertex_not_mem_old S L (k2_isOld_of_lt S L ht) (k2_C_mem_ball S L)
  · rw [k2_mem_e1_iff' S L ht]; intro hmem; linarith [hmem.1]
  · rw [k2_mem_e2_iff' S L ht]; intro hmem; linarith [hmem.2.2]
  · exact absurd (k2_incidentTail_of_lab S L (by omega)) h
  · exact absurd (k2_incidentTail_of_lab S L (by omega)) h
  · rw [k2_mem_e5_iff' S L ht]; intro hmem; linarith [hmem.1]
  · exact k2_kink_vertex_not_mem_old S L (k2_isOld_of_ge S L ht) (k2_C_mem_ball S L)

theorem k2_tail_off_e5 {s t : (k2_shadow S L).Strand} (hs : k2_lab S L s = k2_av S L + 4)
    (h : ¬ (k2_shadow S L).IncidentTail s t) : (k2_shadow S L).tail s ∉ (k2_shadow S L).seg t := by
  rw [k2_tail_e5 S L hs]
  have hlab := k2_lab_lt S L s
  have hlt := k2_lab_lt S L t
  have hav := k2_av_lt S L
  have hk := k2_three_le S L
  have hε := k2_ε_pos S L
  have hxy := k2_xy_Dv S L
  rcases k2_kind_cases S L t with ht | ht | ht | ht | ht | ht | ht
  · exact k2_kink_vertex_not_mem_old S L (k2_isOld_of_lt S L ht) (k2_Dv_mem_ball S L)
  · rw [k2_mem_e1_iff' S L ht]; intro hmem; linarith [hmem.2.2]
  · rw [k2_mem_e2_iff' S L ht]; intro hmem; linarith [hmem.2.2]
  · rw [k2_mem_e3_iff' S L ht]; intro hmem; linarith [hmem.1]
  · exact absurd (k2_incidentTail_of_lab S L (by omega)) h
  · exact absurd (k2_incidentTail_of_lab S L (by omega)) h
  · exact k2_kink_vertex_not_mem_old S L (k2_isOld_of_ge S L ht) (k2_Dv_mem_ball S L)

theorem k2_tail_off : ∀ s t : (k2_shadow S L).Strand, ¬ (k2_shadow S L).IncidentTail s t →
    (k2_shadow S L).tail s ∉ (k2_shadow S L).seg t := by
  intro s t h
  rcases k2_kind_cases S L s with hs | hs | hs | hs | hs | hs | hs
  · exact k2_tail_off_old S L (k2_isOld_of_lt S L hs) h
  · exact k2_tail_off_e1 S L hs h
  · exact k2_tail_off_e2 S L hs h
  · exact k2_tail_off_e3 S L hs h
  · exact k2_tail_off_e4 S L hs h
  · exact k2_tail_off_e5 S L hs h
  · exact k2_tail_off_old S L (k2_isOld_of_ge S L hs) h

/-- **transversality**: non-adjacent meeting strands have independent directions -/
theorem k2_transverse : ∀ s t : (k2_shadow S L).Strand, ¬ (k2_shadow S L).Adjacent s t →
    ((k2_shadow S L).seg s ∩ (k2_shadow S L).seg t).Nonempty →
    det ((k2_shadow S L).dir s) ((k2_shadow S L).dir t) ≠ 0 := by
  intro s t hna hmeet
  obtain ⟨q, hqs, hqt⟩ := hmeet
  have hna' := k2_not_adjacent_lab S L hna
  have hlab := k2_lab_lt S L s
  have hlt := k2_lab_lt S L t
  have hav := k2_av_lt S L
  have hpos := k2_four_ε_sq_dd_pos S L
  by_cases hs : k2_IsMid S L s <;> by_cases ht : k2_IsMid S L t
  · rcases k2_isMid_cases S L hs with h1 | h1 | h1 <;> rcases k2_isMid_cases S L ht with h2 | h2 | h2
    · exact absurd (Or.inl (by omega)) hna'
    · exact absurd (Or.inr (Or.inl (by omega))) hna'
    · rw [k2_det_e2_e4 S L h1 h2]; exact hpos.ne'
    · exact absurd (Or.inr (Or.inr (Or.inl (by omega)))) hna'
    · exact absurd (Or.inl (by omega)) hna'
    · exact absurd (Or.inr (Or.inl (by omega))) hna'
    · rw [k2_det_e4_e2 S L h1 h2]; exact (neg_ne_zero.mpr hpos.ne')
    · exact absurd (Or.inr (Or.inr (Or.inl (by omega)))) hna'
    · exact absurd (Or.inl (by omega)) hna'
  · rw [k2_not_isMid_iff] at ht
    rcases ht with ht | ht | ht
    · exact absurd hqs (k2_old_mid_disjoint S L ht hs hqt)
    · rcases k2_isMid_cases S L hs with h1 | h1 | h1
      · exact absurd (Or.inr (Or.inr (Or.inl (by omega)))) hna'
      · exact absurd hqs (k2_e1_e3_disjoint S L ht h1 hqt)
      · exact absurd hqs (k2_e1_e4_disjoint S L ht h1 hqt)
    · rcases k2_isMid_cases S L hs with h1 | h1 | h1
      · exact absurd hqt (k2_e2_e5_disjoint S L h1 ht hqs)
      · exact absurd hqt (k2_e3_e5_disjoint S L h1 ht hqs)
      · exact absurd (Or.inr (Or.inl (by omega))) hna'
  · rw [k2_not_isMid_iff] at hs
    rcases hs with hs | hs | hs
    · exact absurd hqt (k2_old_mid_disjoint S L hs ht hqs)
    · rcases k2_isMid_cases S L ht with h1 | h1 | h1
      · exact absurd (Or.inr (Or.inl (by omega))) hna'
      · exact absurd hqt (k2_e1_e3_disjoint S L hs h1 hqs)
      · exact absurd hqt (k2_e1_e4_disjoint S L hs h1 hqs)
    · rcases k2_isMid_cases S L ht with h1 | h1 | h1
      · exact absurd hqs (k2_e2_e5_disjoint S L h1 hs hqt)
      · exact absurd hqs (k2_e3_e5_disjoint S L h1 hs hqt)
      · exact absurd (Or.inr (Or.inr (Or.inl (by omega)))) hna'
  · obtain ⟨l, hl, hds⟩ := k2_dir_eq_smul_orig S L hs
    obtain ⟨l', hl', hdt⟩ := k2_dir_eq_smul_orig S L ht
    rw [hds, hdt, det_smul_smul]
    refine mul_ne_zero (mul_pos hl hl').ne' ?_
    exact S.D.generic.transverse _ _ (k2_not_adjacent_orig S L hs ht hna hqs hqt)
      ⟨q, k2_seg_subset_orig S L hs hqs, k2_seg_subset_orig S L ht hqt⟩

/-- interior points of `e1` and `e5` never coincide -/
theorem k2_int_e1_e5_absurd {s t : (k2_shadow S L).Strand} (hs : k2_lab S L s = k2_av S L)
    (ht : k2_lab S L t = k2_av S L + 4) {q : Plane} (hqs : q ∈ (k2_shadow S L).interior s)
    (hqt : q ∈ (k2_shadow S L).interior t) : False := by
  rw [k2_mem_int_e1_iff' S L hs] at hqs
  rw [k2_mem_int_e5_iff' S L ht] at hqt
  have := k2_ε_pos S L
  linarith [hqs.2.2, hqt.2.1]

theorem k2_orig_ne_of_int {s t : (k2_shadow S L).Strand} (hs : ¬ k2_IsMid S L s)
    (ht : ¬ k2_IsMid S L t) (hne : s ≠ t) {q : Plane} (hqs : q ∈ (k2_shadow S L).interior s)
    (hqt : q ∈ (k2_shadow S L).interior t) : k2_orig S L s ≠ k2_orig S L t := by
  intro h
  rcases k2_eq_of_orig_eq S L hs ht h with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact hne h
  · exact k2_int_e1_e5_absurd S L h1 h2 hqs hqt
  · exact k2_int_e1_e5_absurd S L h2 h1 hqt hqs

/-- no triple point involving a middle kink edge -/
theorem k2_no_triple_mid {s t u : (k2_shadow S L).Strand} (hs : k2_IsMid S L s) (hst : s ≠ t)
    (htu : t ≠ u) (hsu : s ≠ u) {q : Plane} (hqs : q ∈ (k2_shadow S L).interior s)
    (hqt : q ∈ (k2_shadow S L).interior t) (hqu : q ∈ (k2_shadow S L).interior u) : False := by
  have hqU : q ∈ k2_U S L := k2_mid_mem_U S L hs ((k2_shadow S L).interior_subset_seg s hqs)
  have ht : ¬ k2_IsOld S L t :=
    fun h => k2_old_not_mem_U S L h ((k2_shadow S L).interior_subset_seg t hqt) hqU
  have hu : ¬ k2_IsOld S L u :=
    fun h => k2_old_not_mem_U S L h ((k2_shadow S L).interior_subset_seg u hqu) hqU
  have hs' : ¬ k2_IsOld S L s := by unfold k2_IsOld k2_IsMid at *; omega
  rcases k2_kink_int_meet S L hs' ht hqs hqt with h | h | h
  · exact hst h
  · rcases k2_kink_int_meet S L hs' hu hqs hqu with h' | h' | h'
    · exact hsu h'
    · exact htu (k2_lab_inj S L (by omega))
    · omega
  · rcases k2_kink_int_meet S L hs' hu hqs hqu with h' | h' | h'
    · exact hsu h'
    · omega
    · exact htu (k2_lab_inj S L (by omega))

theorem k2_no_triple : ¬ ∃ s t u : (k2_shadow S L).Strand, s ≠ t ∧ t ≠ u ∧ s ≠ u ∧
    ((k2_shadow S L).interior s ∩ (k2_shadow S L).interior t ∩ (k2_shadow S L).interior u).Nonempty := by
  rintro ⟨s, t, u, hst, htu, hsu, q, ⟨hqs, hqt⟩, hqu⟩
  by_cases hs : k2_IsMid S L s
  · exact k2_no_triple_mid S L hs hst htu hsu hqs hqt hqu
  by_cases ht : k2_IsMid S L t
  · exact k2_no_triple_mid S L ht hst.symm hsu htu hqt hqs hqu
  by_cases hu : k2_IsMid S L u
  · exact k2_no_triple_mid S L hu hsu.symm hst htu.symm hqu hqs hqt
  apply S.D.generic.no_triple
  refine ⟨k2_orig S L s, k2_orig S L t, k2_orig S L u, k2_orig_ne_of_int S L hs ht hst hqs hqt,
    k2_orig_ne_of_int S L ht hu htu hqt hqu, k2_orig_ne_of_int S L hs hu hsu hqs hqu, q,
    ⟨k2_interior_subset_orig S L hs hqs, k2_interior_subset_orig S L ht hqt⟩,
    k2_interior_subset_orig S L hu hqu⟩

/-- **the new shadow is generic** -/
theorem k2_generic : (k2_shadow S L).Generic :=
  ⟨k2_regular S L, k2_tail_off S L, k2_transverse S L, k2_no_triple S L⟩

/-! #### The kink crossing and the correspondence of the other crossings -/

/-- the five kink edges as strands: `k2_eS j` has label `a + j`, `j = 0 … 4` -/
def k2_eS (j : ℕ) : (k2_shadow S L).Strand :=
  ⟨L.r.1, ((k2_av S L + j : ℕ) : ZMod (k2_k S L + 4))⟩

theorem k2_lab_eS {j : ℕ} (hj : j ≤ 4) : k2_lab S L (k2_eS S L j) = k2_av S L + j :=
  ZMod.val_natCast_of_lt (by have := k2_av_lt S L; omega)

theorem k2_eq_eS {u : (k2_shadow S L).Strand} {j : ℕ} (hj : j ≤ 4) (h : k2_lab S L u = k2_av S L + j) :
    u = k2_eS S L j :=
  k2_lab_inj S L (h.trans (k2_lab_eS S L hj).symm)

theorem k2_not_adjacent_e2_e4 : ¬ (k2_shadow S L).Adjacent (k2_eS S L 1) (k2_eS S L 3) := by
  intro h
  have h' := k2_not_adjacent_lab S L (s := k2_eS S L 1) (t := k2_eS S L 3)
  rw [k2_adjacent_iff, k2_zmod_adjacent_iff] at h
  have h1 := k2_lab_eS S L (j := 1) (by norm_num)
  have h3 := k2_lab_eS S L (j := 3) (by norm_num)
  have := k2_three_le S L
  simp only [k2_lab] at h1 h3
  omega

/-- **the kink crossing** `{e2, e4}` -/
def k2_kink : (k2_shadow S L).Crossing :=
  ⟨{k2_eS S L 1, k2_eS S L 3}, (k2_shadow S L).isCrossing_pair (k2_not_adjacent_e2_e4 S L)
    ⟨k2_K S L, k2_K_mem_e2 S L (k2_lab_eS S L (by norm_num)),
      k2_K_mem_e4 S L (k2_lab_eS S L (by norm_num))⟩⟩

theorem k2_kink_val : (k2_kink S L).val = {k2_eS S L 1, k2_eS S L 3} := rfl

theorem k2_mem_kink_iff (u : (k2_shadow S L).Strand) :
    u ∈ (k2_kink S L).val ↔ k2_lab S L u = k2_av S L + 1 ∨ k2_lab S L u = k2_av S L + 3 := by
  rw [k2_kink_val, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro (rfl | rfl)
    · exact Or.inl (k2_lab_eS S L (by norm_num))
    · exact Or.inr (k2_lab_eS S L (by norm_num))
  · rintro (h | h)
    · exact Or.inl (k2_eq_eS S L (by norm_num) h)
    · exact Or.inr (k2_eq_eS S L (by norm_num) h)

theorem k2_crossingPoint_kink : (k2_shadow S L).crossingPoint (k2_kink S L) = k2_K S L :=
  k2_eq_K_of_mem_e2_e4 S L (k2_lab_eS S L (by norm_num)) (k2_lab_eS S L (by norm_num))
    ((k2_shadow S L).crossingPoint_mem (k2_kink S L) (by rw [k2_kink_val]; simp))
    ((k2_shadow S L).crossingPoint_mem (k2_kink S L) (by rw [k2_kink_val]; simp))

/-- **classification of a non-adjacent meeting pair**: both non-middle, or the kink pair -/
theorem k2_meet_classify {u u' : (k2_shadow S L).Strand} (hna : ¬ (k2_shadow S L).Adjacent u u')
    {q : Plane} (hqs : q ∈ (k2_shadow S L).seg u) (hqt : q ∈ (k2_shadow S L).seg u') :
    (¬ k2_IsMid S L u ∧ ¬ k2_IsMid S L u') ∨
      (k2_lab S L u = k2_av S L + 1 ∧ k2_lab S L u' = k2_av S L + 3) ∨
      (k2_lab S L u = k2_av S L + 3 ∧ k2_lab S L u' = k2_av S L + 1) := by
  have hna' := k2_not_adjacent_lab S L hna
  have hlab := k2_lab_lt S L u
  have hlt := k2_lab_lt S L u'
  have hav := k2_av_lt S L
  by_cases hs : k2_IsMid S L u <;> by_cases ht : k2_IsMid S L u'
  · rcases k2_isMid_cases S L hs with h1 | h1 | h1 <;> rcases k2_isMid_cases S L ht with h2 | h2 | h2
    · exact absurd (Or.inl (by omega)) hna'
    · exact absurd (Or.inr (Or.inl (by omega))) hna'
    · exact Or.inr (Or.inl ⟨h1, h2⟩)
    · exact absurd (Or.inr (Or.inr (Or.inl (by omega)))) hna'
    · exact absurd (Or.inl (by omega)) hna'
    · exact absurd (Or.inr (Or.inl (by omega))) hna'
    · exact Or.inr (Or.inr ⟨h1, h2⟩)
    · exact absurd (Or.inr (Or.inr (Or.inl (by omega)))) hna'
    · exact absurd (Or.inl (by omega)) hna'
  · exfalso
    rw [k2_not_isMid_iff] at ht
    rcases ht with ht | ht | ht
    · exact k2_old_mid_disjoint S L ht hs hqt hqs
    · rcases k2_isMid_cases S L hs with h1 | h1 | h1
      · exact hna' (Or.inr (Or.inr (Or.inl (by omega))))
      · exact k2_e1_e3_disjoint S L ht h1 hqt hqs
      · exact k2_e1_e4_disjoint S L ht h1 hqt hqs
    · rcases k2_isMid_cases S L hs with h1 | h1 | h1
      · exact k2_e2_e5_disjoint S L h1 ht hqs hqt
      · exact k2_e3_e5_disjoint S L h1 ht hqs hqt
      · exact hna' (Or.inr (Or.inl (by omega)))
  · exfalso
    rw [k2_not_isMid_iff] at hs
    rcases hs with hs | hs | hs
    · exact k2_old_mid_disjoint S L hs ht hqs hqt
    · rcases k2_isMid_cases S L ht with h1 | h1 | h1
      · exact hna' (Or.inr (Or.inl (by omega)))
      · exact k2_e1_e3_disjoint S L hs h1 hqs hqt
      · exact k2_e1_e4_disjoint S L hs h1 hqs hqt
    · rcases k2_isMid_cases S L ht with h1 | h1 | h1
      · exact k2_e2_e5_disjoint S L h1 hs hqt hqs
      · exact k2_e3_e5_disjoint S L h1 hs hqt hqs
      · exact hna' (Or.inr (Or.inr (Or.inl (by omega))))
  · exact Or.inl ⟨hs, ht⟩

/-- a crossing with a middle strand is the kink -/
theorem k2_eq_kink_of_mid {y : (k2_shadow S L).Crossing} {u : (k2_shadow S L).Strand}
    (hu : u ∈ y.val) (hmid : k2_IsMid S L u) : y = k2_kink S L := by
  have hmem := (k2_shadow S L).other_mem y hu
  have hne := (k2_shadow S L).other_ne y hu
  obtain ⟨hna, q, hq, hq'⟩ := (k2_shadow S L).crossing_pair_spec y hu hmem hne.symm
  rcases k2_meet_classify S L hna hq hq' with ⟨h, -⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact absurd hmid h
  · apply Subtype.ext
    have e1 : u = k2_eS S L 1 := k2_eq_eS S L (by norm_num) h1
    have e2 : (k2_shadow S L).other y hu = k2_eS S L 3 := k2_eq_eS S L (by norm_num) h2
    rw [(k2_shadow S L).eq_pair_other y hu, k2_kink_val, e2, e1]
  · apply Subtype.ext
    have e1 : u = k2_eS S L 3 := k2_eq_eS S L (by norm_num) h1
    have e2 : (k2_shadow S L).other y hu = k2_eS S L 1 := k2_eq_eS S L (by norm_num) h2
    rw [(k2_shadow S L).eq_pair_other y hu, k2_kink_val, e2, e1, Finset.pair_comm]

theorem k2_not_mid_of_ne_kink {y : (k2_shadow S L).Crossing} (hy : y ≠ k2_kink S L)
    {u : (k2_shadow S L).Strand} (hu : u ∈ y.val) : ¬ k2_IsMid S L u :=
  fun h => hy (k2_eq_kink_of_mid S L hu h)

/-- the strands of a non-kink crossing lie over a crossing of `D` -/
theorem k2_isCrossing_orig {y : (k2_shadow S L).Crossing} (hy : y ≠ k2_kink S L) :
    S.D.Γ.IsCrossing {k2_orig S L y.fst, k2_orig S L y.snd} := by
  have h1 := k2_not_mid_of_ne_kink S L hy y.fst_mem
  have h2 := k2_not_mid_of_ne_kink S L hy y.snd_mem
  obtain ⟨hna, q, hq, hq'⟩ :=
    (k2_shadow S L).crossing_pair_spec y y.fst_mem y.snd_mem ((k2_shadow S L).other_ne y y.fst_mem).symm
  exact S.D.Γ.isCrossing_pair (k2_not_adjacent_orig S L h1 h2 hna hq hq')
    ⟨q, k2_seg_subset_orig S L h1 hq, k2_seg_subset_orig S L h2 hq'⟩

/-- the crossing of `D` under a non-kink crossing of `D'` -/
def k2_origCrossing (y : (k2_shadow S L).Crossing) (hy : y ≠ k2_kink S L) : S.D.Γ.Crossing :=
  ⟨{k2_orig S L y.fst, k2_orig S L y.snd}, k2_isCrossing_orig S L hy⟩

theorem k2_origCrossing_val (y : (k2_shadow S L).Crossing) (hy : y ≠ k2_kink S L) :
    (k2_origCrossing S L y hy).val = {k2_orig S L y.fst, k2_orig S L y.snd} := rfl

theorem k2_orig_mem_origCrossing {y : (k2_shadow S L).Crossing} (hy : y ≠ k2_kink S L)
    {u : (k2_shadow S L).Strand} (hu : u ∈ y.val) :
    k2_orig S L u ∈ (k2_origCrossing S L y hy).val := by
  show k2_orig S L u ∈ ({k2_orig S L y.fst, k2_orig S L y.snd} : Finset S.D.Γ.Strand)
  rw [y.val_eq] at hu
  simp only [Finset.mem_insert, Finset.mem_singleton] at hu
  rcases hu with rfl | rfl <;> simp

/-- the crossing point of a non-kink crossing is that of its original -/
theorem k2_crossingPoint_orig (y : (k2_shadow S L).Crossing) (hy : y ≠ k2_kink S L) :
    (k2_shadow S L).crossingPoint y = S.D.Γ.crossingPoint (k2_origCrossing S L y hy) := by
  apply S.D.generic.common_point_unique
  intro f hf
  have hf' : f ∈ ({k2_orig S L y.fst, k2_orig S L y.snd} : Finset S.D.Γ.Strand) := hf
  simp only [Finset.mem_insert, Finset.mem_singleton] at hf'
  have key : ∀ u ∈ y.val, (k2_shadow S L).crossingPoint y ∈ S.D.Γ.seg (k2_orig S L u) := fun u hu =>
    k2_seg_subset_orig S L (k2_not_mid_of_ne_kink S L hy hu) ((k2_shadow S L).crossingPoint_mem y hu)
  rcases hf' with rfl | rfl
  · exact key _ y.fst_mem
  · exact key _ y.snd_mem

/-- two strands of crossings with the same crossing point and the same original coincide -/
theorem k2_eq_of_orig_eq_mem {y y' : (k2_shadow S L).Crossing} (hy : y ≠ k2_kink S L)
    (hy' : y' ≠ k2_kink S L)
    (hpt : (k2_shadow S L).crossingPoint y = (k2_shadow S L).crossingPoint y')
    {u u' : (k2_shadow S L).Strand} (hu : u ∈ y.val) (hu' : u' ∈ y'.val)
    (h : k2_orig S L u = k2_orig S L u') : u = u' := by
  rcases k2_eq_of_orig_eq S L (k2_not_mid_of_ne_kink S L hy hu) (k2_not_mid_of_ne_kink S L hy' hu') h
    with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact h
  · exact absurd (hpt ▸ (k2_shadow S L).crossingPoint_mem y' hu')
      (k2_e1_e5_disjoint S L h1 h2 ((k2_shadow S L).crossingPoint_mem y hu))
  · exact absurd ((k2_shadow S L).crossingPoint_mem y hu)
      (k2_e1_e5_disjoint S L h2 h1 (hpt ▸ (k2_shadow S L).crossingPoint_mem y' hu'))

theorem k2_orig_injOn_crossing (y : (k2_shadow S L).Crossing) (hy : y ≠ k2_kink S L)
    {u u' : (k2_shadow S L).Strand} (hu : u ∈ y.val) (hu' : u' ∈ y.val)
    (h : k2_orig S L u = k2_orig S L u') : u = u' :=
  k2_eq_of_orig_eq_mem S L hy hy rfl hu hu' h

theorem k2_origCrossing_injective {y y' : (k2_shadow S L).Crossing} (hy : y ≠ k2_kink S L)
    (hy' : y' ≠ k2_kink S L) (h : k2_origCrossing S L y hy = k2_origCrossing S L y' hy') : y = y' := by
  have hpt : (k2_shadow S L).crossingPoint y = (k2_shadow S L).crossingPoint y' := by
    rw [k2_crossingPoint_orig S L y hy, k2_crossingPoint_orig S L y' hy', h]
  have key : ∀ (y y' : (k2_shadow S L).Crossing) (hy : y ≠ k2_kink S L) (hy' : y' ≠ k2_kink S L),
      k2_origCrossing S L y hy = k2_origCrossing S L y' hy' →
      (k2_shadow S L).crossingPoint y = (k2_shadow S L).crossingPoint y' → y.val ⊆ y'.val := by
    intro y y' hy hy' h hpt u hu
    have h1 : k2_orig S L u ∈ (k2_origCrossing S L y' hy').val :=
      h ▸ k2_orig_mem_origCrossing S L hy hu
    have h2 : k2_orig S L u ∈ ({k2_orig S L y'.fst, k2_orig S L y'.snd} : Finset S.D.Γ.Strand) := h1
    simp only [Finset.mem_insert, Finset.mem_singleton] at h2
    rcases h2 with h2 | h2
    · rw [k2_eq_of_orig_eq_mem S L hy hy' hpt hu y'.fst_mem h2]; exact y'.fst_mem
    · rw [k2_eq_of_orig_eq_mem S L hy hy' hpt hu y'.snd_mem h2]; exact y'.snd_mem
  exact Subtype.ext (Finset.Subset.antisymm (key y y' hy hy' h hpt) (key y' y hy' hy h.symm hpt.symm))

/-! #### Lifting the crossings of `D` -/

/-- the new label of an old label value -/
def k2_ν (b : ℕ) : ℕ := if b < k2_av S L then b else b + 4

/-- the strand of `D'` carrying the passage of the strand `e ∈ x` of `D` through `x`: the old
strand, or the piece `e1` / `e5` of `s₀` containing the crossing point -/
def k2_liftStrand (x : S.D.Γ.Crossing) (e : S.D.Γ.Strand) (he : e ∈ x.val) : (k2_shadow S L).Strand :=
  if e = k2_s₀ S L then
    (if S.D.crossingParam x he < k2_t S L then k2_eS S L 0 else k2_eS S L 4)
  else ⟨e.1, ((k2_ν S L e.2.val : ℕ) : ZMod (k2_k S L + 4))⟩

theorem k2_val_ne_av_of_ne {e : S.D.Γ.Strand} (he : e ≠ k2_s₀ S L) : e.2.val ≠ k2_av S L := by
  intro h
  apply he
  obtain ⟨b, rfl⟩ := k2_strand_eq S L e
  exact congrArg _ (ZMod.val_injective _ h)

theorem k2_lab_liftStrand_of_ne (x : S.D.Γ.Crossing) {e : S.D.Γ.Strand} (he : e ∈ x.val)
    (hne : e ≠ k2_s₀ S L) : k2_lab S L (k2_liftStrand S L x e he) = k2_ν S L e.2.val := by
  unfold k2_liftStrand
  rw [ite_eq_right hne]
  obtain ⟨b, rfl⟩ := k2_strand_eq S L e
  have hb := ZMod.val_lt b
  show ((k2_ν S L b.val : ℕ) : ZMod (k2_k S L + 4)).val = k2_ν S L b.val
  apply ZMod.val_natCast_of_lt
  unfold k2_ν; split_ifs <;> omega

theorem k2_liftStrand_isOld (x : S.D.Γ.Crossing) {e : S.D.Γ.Strand} (he : e ∈ x.val)
    (hne : e ≠ k2_s₀ S L) : k2_IsOld S L (k2_liftStrand S L x e he) := by
  unfold k2_IsOld
  rw [k2_lab_liftStrand_of_ne S L x he hne]
  have := k2_val_ne_av_of_ne S L hne
  unfold k2_ν; split_ifs <;> omega

theorem k2_liftStrand_of_s₀ (x : S.D.Γ.Crossing) {e : S.D.Γ.Strand} (he : e ∈ x.val)
    (h : e = k2_s₀ S L) : k2_liftStrand S L x e he =
      if S.D.crossingParam x he < k2_t S L then k2_eS S L 0 else k2_eS S L 4 := by
  unfold k2_liftStrand; rw [ite_eq_left h]

theorem k2_liftStrand_not_mid (x : S.D.Γ.Crossing) {e : S.D.Γ.Strand} (he : e ∈ x.val) :
    ¬ k2_IsMid S L (k2_liftStrand S L x e he) := by
  rw [k2_not_isMid_iff]
  by_cases h : e = k2_s₀ S L
  · rw [k2_liftStrand_of_s₀ S L x he h]
    split_ifs
    · exact Or.inr (Or.inl ((k2_lab_eS S L (by norm_num)).trans (Nat.add_zero _)))
    · exact Or.inr (Or.inr (k2_lab_eS S L (by norm_num)))
  · exact Or.inl (k2_liftStrand_isOld S L x he h)

/-- the original of a lifted strand is the strand -/
theorem k2_orig_liftStrand (x : S.D.Γ.Crossing) {e : S.D.Γ.Strand} (he : e ∈ x.val) :
    k2_orig S L (k2_liftStrand S L x e he) = e := by
  by_cases h : e = k2_s₀ S L
  · subst h
    rw [k2_liftStrand_of_s₀ S L x he rfl]
    split_ifs
    · exact k2_orig_of_eq_a S L ((k2_lab_eS S L (by norm_num)).trans (Nat.add_zero _))
    · exact k2_orig_of_eq_a4 S L (k2_lab_eS S L (by norm_num))
  · have hl := k2_lab_liftStrand_of_ne S L x he h
    have hv := k2_val_ne_av_of_ne S L h
    obtain ⟨b, rfl⟩ := k2_strand_eq S L e
    have hlt := ZMod.val_lt b
    have e2 : (⟨L.r.1, b⟩ : S.D.Γ.Strand).2.val = b.val := rfl
    rw [e2] at hl hv
    rw [k2_orig_eq, hl]
    rw [Smoothing.Strand_mk_eq_mk_iff]
    apply ZMod.val_injective
    rw [ZMod.val_natCast_of_lt (by unfold k2_ν; split_ifs <;> omega)]
    show (if k2_ν S L b.val ≤ k2_av S L then k2_ν S L b.val else k2_ν S L b.val - 4) = b.val
    unfold k2_ν; split_ifs <;> omega

/-- the crossing point lies on the lifted strand -/
theorem k2_crossingPoint_mem_liftStrand (x : S.D.Γ.Crossing) {e : S.D.Γ.Strand} (he : e ∈ x.val) :
    S.D.Γ.crossingPoint x ∈ (k2_shadow S L).seg (k2_liftStrand S L x e he) := by
  by_cases h : e = k2_s₀ S L
  · have hfar := k2_crossingParam_far S L ⟨x, ⟨e, he⟩⟩ h
    have hpt : S.D.Γ.crossingPoint x = S.D.Γ.edgePt (k2_s₀ S L) (S.D.crossingParam x he) := by
      rw [← h]; exact (S.D.crossingParam_spec x he).2.2
    have hxy : k2_x S L (S.D.Γ.crossingPoint x) = S.D.crossingParam x he - k2_t S L ∧
        k2_y S L (S.D.Γ.crossingPoint x) = 0 := by
      rw [hpt, k2_edgePt_s₀_frame, k2_x_frame, k2_y_frame]; exact ⟨rfl, rfl⟩
    have h0 := (S.D.crossingParam_spec x he).1
    have h1 := (S.D.crossingParam_spec x he).2.1
    have hθIn := k2_θIn_lt S L
    have hθOut := k2_lt_θOut S L
    have hε := k2_ε_pos S L
    rw [k2_liftStrand_of_s₀ S L x he h]
    split_ifs with hlt
    · rw [k2_mem_e1_iff' S L (k2_lab_eS S L (by norm_num)), hxy.1, hxy.2]
      rcases hfar with hfar | hfar
      · exact ⟨rfl, by linarith, by linarith⟩
      · exfalso; linarith
    · rw [k2_mem_e5_iff' S L (k2_lab_eS S L (by norm_num)), hxy.1, hxy.2]
      rcases hfar with hfar | hfar
      · exfalso; linarith
      · exact ⟨rfl, by linarith, by linarith⟩
  · rw [k2_seg_old S L (k2_liftStrand_isOld S L x he h), k2_orig_liftStrand]
    exact S.D.Γ.crossingPoint_mem x he

/-- adjacency of two non-middle strands of `D'` forces adjacency of their originals -/
theorem k2_adjacent_orig_s₀_of_old_e1 {u u' : (k2_shadow S L).Strand} (hu : k2_IsOld S L u)
    (hu' : k2_lab S L u' = k2_av S L) (h : (k2_shadow S L).Adjacent u u') :
    S.D.Γ.Adjacent (k2_orig S L u) (k2_s₀ S L) := by
  rw [k2_adjacent_iff, k2_zmod_adjacent_iff] at h
  rw [k2_adjacent_orig_s₀_iff]
  have hval := k2_orig_val_old S L hu
  have hl := k2_lab_lt S L u
  have hav := k2_av_lt S L
  have hk := k2_three_le S L
  have hlu : k2_lab S L u = (k2_m S L u).val := rfl
  have hlu' : k2_lab S L u' = (k2_m S L u').val := rfl
  omega

theorem k2_adjacent_orig_s₀_of_old_e5 {u u' : (k2_shadow S L).Strand} (hu : k2_IsOld S L u)
    (hu' : k2_lab S L u' = k2_av S L + 4) (h : (k2_shadow S L).Adjacent u u') :
    S.D.Γ.Adjacent (k2_orig S L u) (k2_s₀ S L) := by
  rw [k2_adjacent_iff, k2_zmod_adjacent_iff] at h
  rw [k2_adjacent_orig_s₀_iff]
  have hval := k2_orig_val_old S L hu
  have hl := k2_lab_lt S L u
  have hav := k2_av_lt S L
  have hk := k2_three_le S L
  have hlu : k2_lab S L u = (k2_m S L u).val := rfl
  have hlu' : k2_lab S L u' = (k2_m S L u').val := rfl
  omega

theorem k2_adjacent_orig_of_adjacent {u u' : (k2_shadow S L).Strand} (hu : ¬ k2_IsMid S L u)
    (hu' : ¬ k2_IsMid S L u') (h : (k2_shadow S L).Adjacent u u') :
    S.D.Γ.Adjacent (k2_orig S L u) (k2_orig S L u') := by
  have hk := k2_three_le S L
  have hlab := k2_lab_lt S L u
  have hlt := k2_lab_lt S L u'
  have hav := k2_av_lt S L
  have hl := k2_adjacent_iff S L u u'
  rw [k2_zmod_adjacent_iff] at hl
  have hlu : k2_lab S L u = (k2_m S L u).val := rfl
  have hlu' : k2_lab S L u' = (k2_m S L u').val := rfl
  rw [k2_not_isMid_iff] at hu hu'
  rcases hu with hu | hu | hu <;> rcases hu' with hu' | hu' | hu'
  · exact (k2_adjacent_old_iff S L hu hu').mp h
  · rw [k2_orig_of_eq_a S L hu']; exact k2_adjacent_orig_s₀_of_old_e1 S L hu hu' h
  · rw [k2_orig_of_eq_a4 S L hu']; exact k2_adjacent_orig_s₀_of_old_e5 S L hu hu' h
  · rw [k2_orig_of_eq_a S L hu]; exact (k2_adjacent_orig_s₀_of_old_e1 S L hu' hu h.symm).symm
  · rw [k2_orig_of_eq_a S L hu, k2_orig_of_eq_a S L hu']; exact Shadow.Adjacent.refl _ _
  · exfalso; rw [hl] at h; omega
  · rw [k2_orig_of_eq_a4 S L hu]; exact (k2_adjacent_orig_s₀_of_old_e5 S L hu' hu h.symm).symm
  · exfalso; rw [hl] at h; omega
  · rw [k2_orig_of_eq_a4 S L hu, k2_orig_of_eq_a4 S L hu']; exact Shadow.Adjacent.refl _ _

/-- the lifted over and under strands of a crossing form a crossing of `D'` -/
theorem k2_isCrossing_lift (x : S.D.Γ.Crossing) :
    (k2_shadow S L).IsCrossing {k2_liftStrand S L x _ (S.D.over_mem x),
      k2_liftStrand S L x _ (S.D.under_mem x)} := by
  apply (k2_shadow S L).isCrossing_pair
  · intro h
    have := k2_adjacent_orig_of_adjacent S L (k2_liftStrand_not_mid S L x _)
      (k2_liftStrand_not_mid S L x _) h
    rw [k2_orig_liftStrand, k2_orig_liftStrand] at this
    exact S.D.not_adjacent_over_under x this
  · exact ⟨S.D.Γ.crossingPoint x, k2_crossingPoint_mem_liftStrand S L x _,
      k2_crossingPoint_mem_liftStrand S L x _⟩

/-- **the lift of a crossing of `D`** -/
def k2_liftCrossing (x : S.D.Γ.Crossing) : (k2_shadow S L).Crossing := ⟨_, k2_isCrossing_lift S L x⟩

theorem k2_liftCrossing_val (x : S.D.Γ.Crossing) : (k2_liftCrossing S L x).val =
    {k2_liftStrand S L x _ (S.D.over_mem x), k2_liftStrand S L x _ (S.D.under_mem x)} := rfl

theorem k2_liftStrand_mem (x : S.D.Γ.Crossing) {e : S.D.Γ.Strand} (he : e ∈ x.val) :
    k2_liftStrand S L x e he ∈ (k2_liftCrossing S L x).val := by
  rw [k2_liftCrossing_val]
  rcases (S.D.mem_iff x e).mp he with h | h
  · subst h; exact Finset.mem_insert_self _ _
  · subst h; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)

theorem k2_liftCrossing_ne_kink (x : S.D.Γ.Crossing) : k2_liftCrossing S L x ≠ k2_kink S L := by
  intro h
  have hmem : k2_liftStrand S L x _ (S.D.over_mem x) ∈ (k2_kink S L).val := by
    rw [← h]; exact k2_liftStrand_mem S L x _
  rw [k2_mem_kink_iff] at hmem
  apply k2_liftStrand_not_mid S L x (S.D.over_mem x)
  unfold k2_IsMid; omega

theorem k2_origCrossing_liftCrossing (x : S.D.Γ.Crossing) :
    k2_origCrossing S L (k2_liftCrossing S L x) (k2_liftCrossing_ne_kink S L x) = x := by
  apply Subtype.ext
  show ({k2_orig S L (k2_liftCrossing S L x).fst, k2_orig S L (k2_liftCrossing S L x).snd} :
    Finset S.D.Γ.Strand) = x.val
  have h1 := (k2_liftCrossing S L x).fst_mem
  have h2 := (k2_liftCrossing S L x).snd_mem
  have hne : (k2_liftCrossing S L x).snd ≠ (k2_liftCrossing S L x).fst :=
    (k2_shadow S L).other_ne _ (k2_liftCrossing S L x).fst_mem
  rw [k2_liftCrossing_val] at h1 h2
  simp only [Finset.mem_insert, Finset.mem_singleton] at h1 h2
  rw [S.D.val_eq_pair x]
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · exact absurd (h2.trans h1.symm) hne
  · rw [h1, h2, k2_orig_liftStrand, k2_orig_liftStrand]
  · rw [h1, h2, k2_orig_liftStrand, k2_orig_liftStrand, Finset.pair_comm]
  · exact absurd (h2.trans h1.symm) hne

/-- the lift of the original of a strand of a non-kink crossing is the strand -/
theorem k2_liftStrand_orig {y : (k2_shadow S L).Crossing} (hy : y ≠ k2_kink S L)
    {u : (k2_shadow S L).Strand} (hu : u ∈ y.val) :
    k2_liftStrand S L (k2_origCrossing S L y hy) (k2_orig S L u) (k2_orig_mem_origCrossing S L hy hu) =
      u := by
  have hnm := k2_not_mid_of_ne_kink S L hy hu
  have hpt := k2_crossingPoint_orig S L y hy
  have hmem := (k2_shadow S L).crossingPoint_mem y hu
  rw [k2_not_isMid_iff] at hnm
  rcases hnm with hnm | hnm | hnm
  · -- old strand
    have hne := k2_orig_ne_s₀ S L hnm
    apply k2_lab_inj S L
    rw [k2_lab_liftStrand_of_ne S L _ _ hne]
    have hval := k2_orig_val_old S L hnm
    unfold k2_ν
    split_ifs <;> omega
  · -- `e1`: the crossing parameter on `s₀` is `< t`
    have horig := k2_orig_of_eq_a S L hnm
    have hxy : k2_x S L ((k2_shadow S L).crossingPoint y) ≤ -k2_ε S L :=
      ((k2_mem_e1_iff' S L hnm _).mp hmem).2.2
    have hspec := S.D.crossingParam_spec (k2_origCrossing S L y hy) (k2_orig_mem_origCrossing S L hy hu)
    have hpt' : S.D.Γ.crossingPoint (k2_origCrossing S L y hy) = S.D.Γ.edgePt (k2_s₀ S L)
        (S.D.crossingParam (k2_origCrossing S L y hy) (k2_orig_mem_origCrossing S L hy hu)) := by
      rw [← horig]; exact hspec.2.2
    have hx' : k2_x S L (S.D.Γ.crossingPoint (k2_origCrossing S L y hy)) =
        S.D.crossingParam (k2_origCrossing S L y hy) (k2_orig_mem_origCrossing S L hy hu) - k2_t S L := by
      rw [hpt', k2_edgePt_s₀_frame, k2_x_frame]
    rw [hpt] at hxy
    have hε := k2_ε_pos S L
    rw [k2_liftStrand_of_s₀ S L _ _ horig, ite_eq_left (by linarith)]
    exact (k2_eq_eS S L (by norm_num) hnm).symm
  · -- `e5`: the crossing parameter on `s₀` is `> t`
    have horig := k2_orig_of_eq_a4 S L hnm
    have hxy : k2_ε S L ≤ k2_x S L ((k2_shadow S L).crossingPoint y) :=
      ((k2_mem_e5_iff' S L hnm _).mp hmem).2.1
    have hspec := S.D.crossingParam_spec (k2_origCrossing S L y hy) (k2_orig_mem_origCrossing S L hy hu)
    have hpt' : S.D.Γ.crossingPoint (k2_origCrossing S L y hy) = S.D.Γ.edgePt (k2_s₀ S L)
        (S.D.crossingParam (k2_origCrossing S L y hy) (k2_orig_mem_origCrossing S L hy hu)) := by
      rw [← horig]; exact hspec.2.2
    have hx' : k2_x S L (S.D.Γ.crossingPoint (k2_origCrossing S L y hy)) =
        S.D.crossingParam (k2_origCrossing S L y hy) (k2_orig_mem_origCrossing S L hy hu) - k2_t S L := by
      rw [hpt', k2_edgePt_s₀_frame, k2_x_frame]
    rw [hpt] at hxy
    have hε := k2_ε_pos S L
    rw [k2_liftStrand_of_s₀ S L _ _ horig, ite_eq_right (not_lt.mpr (by linarith))]
    exact (k2_eq_eS S L (by norm_num) hnm).symm

theorem k2_liftCrossing_origCrossing (y : (k2_shadow S L).Crossing) (hy : y ≠ k2_kink S L) :
    k2_liftCrossing S L (k2_origCrossing S L y hy) = y := by
  apply Subtype.ext
  have key : ∀ (e : S.D.Γ.Strand) (he : e ∈ (k2_origCrossing S L y hy).val),
      k2_liftStrand S L (k2_origCrossing S L y hy) e he ∈ y.val := by
    intro e he
    have he' : e ∈ ({k2_orig S L y.fst, k2_orig S L y.snd} : Finset S.D.Γ.Strand) := he
    simp only [Finset.mem_insert, Finset.mem_singleton] at he'
    rcases he' with rfl | rfl
    · rw [k2_liftStrand_orig S L hy y.fst_mem]; exact y.fst_mem
    · rw [k2_liftStrand_orig S L hy y.snd_mem]; exact y.snd_mem
  refine Finset.eq_of_subset_of_card_le ?_
    (by rw [(k2_shadow S L).crossing_card_two, (k2_shadow S L).crossing_card_two])
  intro w hw
  rw [k2_liftCrossing_val] at hw
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl
  · exact key _ _
  · exact key _ _

/-- **the correspondence of the old crossings** -/
def k2_old : S.D.Γ.Crossing ≃ {y : (k2_shadow S L).Crossing // y ≠ k2_kink S L} where
  toFun x := ⟨k2_liftCrossing S L x, k2_liftCrossing_ne_kink S L x⟩
  invFun y := k2_origCrossing S L y.1 y.2
  left_inv x := k2_origCrossing_liftCrossing S L x
  right_inv y := Subtype.ext (k2_liftCrossing_origCrossing S L y.1 y.2)

@[simp] theorem k2_old_apply (x : S.D.Γ.Crossing) : (k2_old S L x).1 = k2_liftCrossing S L x := rfl

/-! #### The diagram `D'`: over data pulled back through the originals, the kink later-branch-over -/

/-- the over strand of `D'`: `e4` at the kink, otherwise the strand over the over strand of `D` -/
def k2_over (y : (k2_shadow S L).Crossing) : (k2_shadow S L).Strand :=
  if hy : y = k2_kink S L then k2_eS S L 3
  else if k2_orig S L y.fst = S.D.overStrand (k2_origCrossing S L y hy) then y.fst else y.snd

theorem k2_over_mem (y : (k2_shadow S L).Crossing) : k2_over S L y ∈ y.val := by
  unfold k2_over
  split_ifs with hy h
  · rw [hy, k2_kink_val]; simp
  · exact y.fst_mem
  · exact y.snd_mem

theorem k2_over_kink : k2_over S L (k2_kink S L) = k2_eS S L 3 := by
  unfold k2_over; rw [dif_pos rfl]

theorem k2_orig_over {y : (k2_shadow S L).Crossing} (hy : y ≠ k2_kink S L) :
    k2_orig S L (k2_over S L y) = S.D.overStrand (k2_origCrossing S L y hy) := by
  unfold k2_over
  rw [dif_neg hy]
  split_ifs with h
  · exact h
  · have h1 : k2_orig S L y.fst = S.D.underStrand (k2_origCrossing S L y hy) :=
      S.D.eq_under_of_mem_of_ne _ (k2_orig_mem_origCrossing S L hy y.fst_mem) h
    apply S.D.eq_over_of_mem_of_ne _ (k2_orig_mem_origCrossing S L hy y.snd_mem)
    intro h2
    exact (k2_shadow S L).other_ne y y.fst_mem
      (k2_orig_injOn_crossing S L y hy y.snd_mem y.fst_mem (h2.trans h1.symm))

/-- **the diagram `D'`** -/
abbrev k2_D' : Diagram := ⟨k2_shadow S L, k2_generic S L, k2_over S L, k2_over_mem S L⟩

theorem k2_D'_Γ : (k2_D' S L).Γ = k2_shadow S L := rfl
theorem k2_D'_overStrand (y : (k2_shadow S L).Crossing) : (k2_D' S L).overStrand y = k2_over S L y := rfl

theorem k2_D'_overStrand_kink : (k2_D' S L).overStrand (k2_kink S L) = k2_eS S L 3 := k2_over_kink S L

theorem k2_D'_underStrand_kink : (k2_D' S L).underStrand (k2_kink S L) = k2_eS S L 1 := by
  have hmem : (k2_D' S L).underStrand (k2_kink S L) ∈ (k2_kink S L).val := (k2_D' S L).under_mem _
  have hne := (k2_D' S L).under_ne_over (k2_kink S L)
  rw [k2_D'_overStrand_kink] at hne
  have hmem' := (k2_mem_kink_iff S L ((k2_D' S L).underStrand (k2_kink S L))).mp hmem
  rcases hmem' with h | h
  · exact k2_eq_eS S L (by norm_num) h
  · exact absurd (k2_eq_eS S L (by norm_num) h) hne

theorem k2_orig_underStrand {y : (k2_shadow S L).Crossing} (hy : y ≠ k2_kink S L) :
    k2_orig S L ((k2_D' S L).underStrand y) = S.D.underStrand (k2_origCrossing S L y hy) := by
  have hmem := (k2_D' S L).under_mem y
  have hne := (k2_D' S L).under_ne_over y
  apply S.D.eq_under_of_mem_of_ne _ (k2_orig_mem_origCrossing S L hy hmem)
  intro h
  exact hne (k2_orig_injOn_crossing S L y hy hmem (k2_over_mem S L y)
    (h.trans (k2_orig_over S L hy).symm))

/-- **the kink is negative** (later branch over: `det (dir e4) (dir e2) = −4 ε² |d|² < 0`) -/
theorem k2_kink_neg : (k2_D' S L).sign (k2_kink S L) = -1 := by
  unfold Diagram.sign
  rw [k2_D'_overStrand_kink, k2_D'_underStrand_kink]
  show SignType.sign (det ((k2_shadow S L).dir (k2_eS S L 3)) ((k2_shadow S L).dir (k2_eS S L 1))) = -1
  rw [k2_det_e4_e2 S L (k2_lab_eS S L (by norm_num)) (k2_lab_eS S L (by norm_num))]
  exact sign_neg (neg_lt_zero.mpr (k2_four_ε_sq_dd_pos S L))

/-- the signs of the other crossings are inherited -/
theorem k2_sign_of_ne {y : (k2_shadow S L).Crossing} (hy : y ≠ k2_kink S L) :
    (k2_D' S L).sign y = S.D.sign (k2_origCrossing S L y hy) := by
  obtain ⟨l, hl, hdl⟩ := k2_dir_eq_smul_orig S L (k2_not_mid_of_ne_kink S L hy (k2_over_mem S L y))
  obtain ⟨m, hm, hdm⟩ :=
    k2_dir_eq_smul_orig S L (k2_not_mid_of_ne_kink S L hy ((k2_D' S L).under_mem y))
  unfold Diagram.sign
  show SignType.sign (det ((k2_shadow S L).dir (k2_over S L y))
    ((k2_shadow S L).dir ((k2_D' S L).underStrand y))) = _
  rw [hdl, hdm, det_smul_smul, sign_mul, sign_pos (mul_pos hl hm), one_mul, k2_orig_over S L hy,
    k2_orig_underStrand S L hy]

theorem k2_old_sign (x : S.D.Γ.Crossing) : (k2_D' S L).sign (k2_liftCrossing S L x) = S.D.sign x := by
  rw [k2_sign_of_ne S L (k2_liftCrossing_ne_kink S L x), k2_origCrossing_liftCrossing]

theorem k2_old_point (x : S.D.Γ.Crossing) :
    (k2_D' S L).Γ.crossingPoint (k2_liftCrossing S L x) = S.D.Γ.crossingPoint x := by
  show (k2_shadow S L).crossingPoint (k2_liftCrossing S L x) = _
  rw [k2_crossingPoint_orig S L _ (k2_liftCrossing_ne_kink S L x), k2_origCrossing_liftCrossing]

/-- **the writhe drops by one** -/
theorem k2_writhe : (k2_D' S L).writhe = S.D.writhe - 1 := by
  unfold Diagram.writhe
  rw [Fintype.sum_eq_add_sum_subtype_ne (fun y : (k2_D' S L).Γ.Crossing => ((k2_D' S L).sign y : ℤ))
    (k2_kink S L), k2_kink_neg]
  have h := Equiv.sum_comp (k2_old S L)
    (fun y : {y : (k2_shadow S L).Crossing // y ≠ k2_kink S L} => ((k2_D' S L).sign y.1 : ℤ))
  simp only [k2_old_apply, k2_old_sign] at h
  show ((-1 : SignType) : ℤ) + ∑ y : {y : (k2_shadow S L).Crossing // y ≠ k2_kink S L},
    ((k2_D' S L).sign y.1 : ℤ) = ∑ x, (S.D.sign x : ℤ) - 1
  rw [← h]
  have h1 : ((-1 : SignType) : ℤ) = -1 := rfl
  rw [h1]
  ring

/-! #### The occurrences of `D'` -/

theorem k2_visit_ext {Γ : Shadow} {v w : Γ.Visit} (h1 : v.1 = w.1)
    (h2 : v.2.val = w.2.val) : v = w := by
  obtain ⟨x, s, hs⟩ := v
  obtain ⟨y, t, ht⟩ := w
  simp only at h1 h2
  subst h1
  subst h2
  rfl

/-- the lift of an occurrence -/
def k2_liftVisit (v : S.D.Γ.Visit) : (k2_D' S L).Γ.Visit :=
  ⟨k2_liftCrossing S L v.1, ⟨k2_liftStrand S L v.1 v.2.val v.2.2, k2_liftStrand_mem S L v.1 v.2.2⟩⟩

theorem k2_liftVisit_fst (v : S.D.Γ.Visit) : (k2_liftVisit S L v).1 = k2_liftCrossing S L v.1 := rfl
theorem k2_liftVisit_strand (v : S.D.Γ.Visit) :
    (k2_liftVisit S L v).2.val = k2_liftStrand S L v.1 v.2.val v.2.2 := rfl

theorem k2_liftVisit_ne_kink (v : S.D.Γ.Visit) : (k2_liftVisit S L v).1 ≠ k2_kink S L :=
  k2_liftCrossing_ne_kink S L v.1

/-- the original of a non-kink occurrence -/
def k2_origVisit (w : (k2_D' S L).Γ.Visit) (hw : w.1 ≠ k2_kink S L) : S.D.Γ.Visit :=
  ⟨k2_origCrossing S L w.1 hw, ⟨k2_orig S L w.2.val, k2_orig_mem_origCrossing S L hw w.2.2⟩⟩

/-- **the correspondence of the old occurrences** -/
def k2_oldVisit : S.D.Γ.Visit ≃ {w : (k2_D' S L).Γ.Visit // w.1 ≠ k2_kink S L} where
  toFun v := ⟨k2_liftVisit S L v, k2_liftVisit_ne_kink S L v⟩
  invFun w := k2_origVisit S L w.1 w.2
  left_inv v := by
    apply k2_visit_ext
    · exact k2_origCrossing_liftCrossing S L v.1
    · exact k2_orig_liftStrand S L v.1 v.2.2
  right_inv w := by
    apply Subtype.ext
    apply k2_visit_ext
    · exact k2_liftCrossing_origCrossing S L w.1.1 w.2
    · exact k2_liftStrand_orig S L w.2 w.1.2.2

@[simp] theorem k2_oldVisit_apply (v : S.D.Γ.Visit) : (k2_oldVisit S L v).1 = k2_liftVisit S L v := rfl

theorem k2_oldVisit_over (x : S.D.Γ.Crossing) :
    (k2_oldVisit S L (S.D.overVisit x)).1 = (k2_D' S L).overVisit (k2_old S L x).1 := by
  refine k2_visit_ext rfl ?_
  show k2_liftStrand S L x _ (S.D.over_mem x) = k2_over S L (k2_liftCrossing S L x)
  apply k2_orig_injOn_crossing S L _ (k2_liftCrossing_ne_kink S L x) (k2_liftStrand_mem S L x _)
    (k2_over_mem S L _)
  rw [k2_orig_liftStrand, k2_orig_over S L (k2_liftCrossing_ne_kink S L x),
    k2_origCrossing_liftCrossing]

theorem k2_oldVisit_under (x : S.D.Γ.Crossing) :
    (k2_oldVisit S L (S.D.underVisit x)).1 = (k2_D' S L).underVisit (k2_old S L x).1 := by
  refine k2_visit_ext rfl ?_
  show k2_liftStrand S L x _ (S.D.under_mem x) = (k2_D' S L).underStrand (k2_liftCrossing S L x)
  apply k2_orig_injOn_crossing S L _ (k2_liftCrossing_ne_kink S L x) (k2_liftStrand_mem S L x _)
    ((k2_D' S L).under_mem _)
  rw [k2_orig_liftStrand, k2_orig_underStrand S L (k2_liftCrossing_ne_kink S L x),
    k2_origCrossing_liftCrossing]

theorem k2_oldVisit_twin (v : S.D.Γ.Visit) :
    (k2_oldVisit S L (S.D.twin v)).1 = (k2_D' S L).twin (k2_oldVisit S L v).1 := by
  refine k2_visit_ext rfl ?_
  show k2_liftStrand S L v.1 _ (S.D.Γ.other_mem v.1 v.2.2) =
    (k2_shadow S L).other (k2_liftCrossing S L v.1) (k2_liftStrand_mem S L v.1 v.2.2)
  have hy := k2_liftCrossing_ne_kink S L v.1
  have hmem := (k2_shadow S L).other_mem (k2_liftCrossing S L v.1) (k2_liftStrand_mem S L v.1 v.2.2)
  have hne := (k2_shadow S L).other_ne (k2_liftCrossing S L v.1) (k2_liftStrand_mem S L v.1 v.2.2)
  apply k2_orig_injOn_crossing S L _ hy (k2_liftStrand_mem S L v.1 _) hmem
  rw [k2_orig_liftStrand]
  symm
  apply S.D.Γ.eq_other_of_mem_of_ne v.1 v.2.2
  · have := k2_orig_mem_origCrossing S L hy hmem
    rwa [k2_origCrossing_liftCrossing] at this
  · intro h
    apply hne
    apply k2_orig_injOn_crossing S L _ hy hmem (k2_liftStrand_mem S L v.1 v.2.2)
    rw [h, k2_orig_liftStrand]

/-! #### The arc of `D` inside the disc; `D` meets the disc cleanly; no inner crossing -/

theorem k2_θIn_mem : k2_θIn S L ∈ Set.Ico (0:ℝ) 1 :=
  ⟨(k2_θIn_pos S L).le, (k2_θIn_lt_θOut S L).trans (k2_θOut_lt_one S L)⟩
theorem k2_θOut_mem : k2_θOut S L ∈ Set.Ico (0:ℝ) 1 :=
  ⟨((k2_θIn_pos S L).trans (k2_θIn_lt_θOut S L)).le, k2_θOut_lt_one S L⟩

/-- the arc of `D` through the disc: on `s₀`, from `θIn` to `θOut` -/
def k2_arc : S.D.Γ.Arc :=
  ⟨L.r.1, (k2_a S L, ⟨k2_θIn S L, k2_θIn_mem S L⟩), (k2_a S L, ⟨k2_θOut S L, k2_θOut_mem S L⟩)⟩

theorem k2_mem_arc_iff (q : S.D.Γ.Pt) :
    (k2_arc S L).Mem q ↔ (⟨q.1, q.2.1⟩ : S.D.Γ.Strand) = k2_s₀ S L ∧
      k2_θIn S L ≤ q.2.2.val ∧ q.2.2.val ≤ k2_θOut S L :=
  Smoothing.arc_mem_iff_of_same_edge (k2_arc S L) (k2_a S L) _ _ rfl rfl (k2_θIn_lt_θOut S L) q

theorem k2_inner_arc_iff (q : S.D.Γ.Pt) :
    (k2_arc S L).Inner q ↔ (⟨q.1, q.2.1⟩ : S.D.Γ.Strand) = k2_s₀ S L ∧
      k2_θIn S L < q.2.2.val ∧ q.2.2.val < k2_θOut S L :=
  Smoothing.arc_inner_iff_of_same_edge (k2_arc S L) (k2_a S L) _ _ rfl rfl (k2_θIn_lt_θOut S L) q

/-- a traversal point of `D` evaluating into the disc lies on `s₀` -/
theorem k2_strand_eq_s₀_of_mem_U (q : S.D.Γ.Pt) (hq : S.D.Γ.eval q ∈ k2_U S L) :
    (⟨q.1, q.2.1⟩ : S.D.Γ.Strand) = k2_s₀ S L := by
  by_contra h
  exact k2_not_mem_U_of_mem_seg S L h (Smoothing.eval_mem_seg q) hq

theorem k2_eval_arc_startPt : S.D.Γ.eval (k2_arc S L).startPt = S.D.Γ.edgePt (k2_s₀ S L) (k2_θIn S L) := rfl
theorem k2_eval_arc_stopPt : S.D.Γ.eval (k2_arc S L).stopPt = S.D.Γ.edgePt (k2_s₀ S L) (k2_θOut S L) := rfl

theorem k2_isArc_arc : S.D.Γ.IsArc (k2_U S L) (k2_arc S L) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h
    have := congrArg (fun r : TraversalPoint (S.D.Γ.comp (k2_arc S L).i).k => r.2.val) h
    exact (k2_θIn_lt_θOut S L).ne this
  · rw [k2_frontier_U, k2_eval_arc_startPt]
    exact k2_edgePt_s₀_mem_sphere S L _ (Or.inl rfl)
  · rw [k2_frontier_U, k2_eval_arc_stopPt]
    exact k2_edgePt_s₀_mem_sphere S L _ (Or.inr rfl)
  · intro q hq
    rw [k2_inner_arc_iff] at hq
    obtain ⟨hq1, hq2, hq3⟩ := hq
    rw [k2_interior_U , Smoothing.eval_eq_edgePt, hq1]
    exact (k2_edgePt_s₀_mem_ball_iff S L _).mpr ⟨hq2, hq3⟩

theorem k2_arcCover_D : S.D.Γ.ArcCover (k2_U S L) {k2_arc S L} := by
  have hclosed : IsClosed (k2_U S L) := Metric.isClosed_closedBall
  refine ⟨?_, ?_, ?_⟩
  · intro a ha
    rw [Set.mem_singleton_iff] at ha
    rw [ha]; exact k2_isArc_arc S L
  · intro q
    constructor
    · intro hq
      have hs := k2_strand_eq_s₀_of_mem_U S L q hq
      refine ⟨k2_arc S L, Set.mem_singleton _, ?_⟩
      rw [k2_mem_arc_iff]
      refine ⟨hs, ?_⟩
      rw  [Smoothing.eval_eq_edgePt, hs] at hq
      exact (k2_edgePt_s₀_mem_U_iff S L _).mp hq
    · rintro ⟨a, ha, hq⟩
      rw [Set.mem_singleton_iff] at ha
      subst ha
      exact Smoothing.isArc_eval_mem_of_mem (k2_isArc_arc S L) hclosed hq
  · intro a ha b hb hab
    rw [Set.mem_singleton_iff] at ha hb
    exact absurd (ha.trans hb.symm) hab

theorem k2_clean_D : Clean (k2_U S L) S.D := by
  refine ⟨?_, ?_⟩
  · intro q hq q' hq' heq
    have hq1 : S.D.Γ.eval q ∈ Metric.sphere (k2_r₀ S L) (k2_ρ S L) := by
      rw [← k2_frontier_U]; exact hq
    have hq1' : S.D.Γ.eval q' ∈ Metric.sphere (k2_r₀ S L) (k2_ρ S L) := by
      rw [← k2_frontier_U]; exact hq'
    have hs := k2_strand_eq_s₀_of_mem_U S L q (Metric.sphere_subset_closedBall hq1)
    have hs' := k2_strand_eq_s₀_of_mem_U S L q' (Metric.sphere_subset_closedBall hq1')
    refine Smoothing.Pt_ext (hs.trans hs'.symm) ?_
    rw  [Smoothing.eval_eq_edgePt , Smoothing.eval_eq_edgePt, hs, hs'] at heq
    exact S.D.generic.edgePt_injective _ heq
  · intro i
    refine ⟨(0, ⟨0, le_rfl, zero_lt_one⟩), ?_⟩
    have h0 : S.D.Γ.eval ⟨i, (0, ⟨0, le_rfl, zero_lt_one⟩)⟩ = S.D.Γ.tail ⟨i, 0⟩ :=
      S.D.Γ.edgePt_zero ⟨i, 0⟩
    rw [h0]
    exact k2_tail_not_mem_U S L _

theorem k2_no_inner (x : S.D.Γ.Crossing) : S.D.Γ.crossingPoint x ∉ interior (k2_U S L) :=
  fun h => k2_crossingPoint_not_mem_U S L x (interior_subset h)

/-! #### The kinked arc of `D'` inside the disc -/

/-- traversal betweenness across five consecutive edges `m, …, m + 4` (no wrap) -/
theorem k2_traversalBetween_span_four {n : ℕ} [NeZero n] (m : ZMod n) (hm : m.val + 4 < n)
    (θ₁ θ₂ : Set.Ico (0:ℝ) 1) (r : TraversalPoint n) :
    traversalBetween (m, θ₁) r (m + 4, θ₂) ↔
      (r.1 = m ∧ θ₁.val < r.2.val) ∨ r.1 = m + 1 ∨ r.1 = m + 2 ∨ r.1 = m + 3 ∨
        (r.1 = m + 4 ∧ r.2.val < θ₂.val) := by
  have hv : ∀ j : ℕ, j ≤ 4 → (m + j).val = m.val + j := by
    intro j hj
    have : m + j = ((m.val + j : ℕ) : ZMod n) := by rw [Nat.cast_add, ZMod.natCast_zmod_val]
    rw [this, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
  have h1 : (m + 1).val = m.val + 1 := by have := hv 1 (by norm_num); simpa using this
  have h2 : (m + 2).val = m.val + 2 := by have := hv 2 (by norm_num); simpa using this
  have h3 : (m + 3).val = m.val + 3 := by have := hv 3 (by norm_num); simpa using this
  have h4 : (m + 4).val = m.val + 4 := by have := hv 4 (by norm_num); simpa using this
  obtain ⟨b, θ⟩ := r
  have hθ1 := θ₁.2.1
  have hθ1' := θ₁.2.2
  have hθ2 := θ₂.2.1
  have hθ2' := θ₂.2.2
  have hθ := θ.2.1
  have hθ' := θ.2.2
  simp only [traversalBetween, traversalKey, h4]
  push_cast
  constructor
  · rintro (⟨h5, h6⟩ | ⟨h5, h6⟩ | ⟨h5, h6⟩)
    · have h7 : m.val < b.val + 1 := by
        have : (m.val : ℝ) < b.val + 1 := by linarith
        exact_mod_cast this
      have h8 : b.val < m.val + 5 := by
        have : (b.val : ℝ) < m.val + 5 := by linarith
        exact_mod_cast this
      rcases (by omega : b.val = m.val ∨ b.val = m.val + 1 ∨ b.val = m.val + 2 ∨ b.val = m.val + 3 ∨
          b.val = m.val + 4) with hb | hb | hb | hb | hb
      · have hab : b = m := ZMod.val_injective n hb
        subst hab
        exact Or.inl ⟨rfl, by linarith⟩
      · exact Or.inr (Or.inl (ZMod.val_injective n (hb.trans h1.symm)))
      · exact Or.inr (Or.inr (Or.inl (ZMod.val_injective n (hb.trans h2.symm))))
      · exact Or.inr (Or.inr (Or.inr (Or.inl (ZMod.val_injective n (hb.trans h3.symm)))))
      · have hab : b = m + 4 := ZMod.val_injective n (hb.trans h4.symm)
        subst hab
        refine Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, ?_⟩)))
        rw [h4] at h6
        push_cast at h6
        linarith
    · exfalso; linarith
    · exfalso; linarith
  · rintro (⟨rfl, h5⟩ | rfl | rfl | rfl | ⟨rfl, h5⟩)
    · exact Or.inl ⟨by linarith, by linarith⟩
    · rw [h1]; push_cast; exact Or.inl ⟨by linarith, by linarith⟩
    · rw [h2]; push_cast; exact Or.inl ⟨by linarith, by linarith⟩
    · rw [h3]; push_cast; exact Or.inl ⟨by linarith, by linarith⟩
    · rw [h4]; push_cast; exact Or.inl ⟨by linarith, by linarith⟩

/-- the entering parameter on `e1` and the exiting parameter on `e5` -/
def k2_θIn' : ℝ := k2_θIn S L / (k2_t S L - k2_ε S L)
def k2_θOut' : ℝ := (k2_θOut S L - k2_t S L - k2_ε S L) / (1 - k2_t S L - k2_ε S L)

theorem k2_t_sub_ε_pos : 0 < k2_t S L - k2_ε S L := by linarith [k2_ε_lt_t S L]
theorem k2_one_sub_t_sub_ε_pos : 0 < 1 - k2_t S L - k2_ε S L := by linarith [k2_ε_lt_one_sub_t S L]

theorem k2_θIn'_pos : 0 < k2_θIn' S L := div_pos (k2_θIn_pos S L) (k2_t_sub_ε_pos S L)
theorem k2_θIn'_lt_one : k2_θIn' S L < 1 := by
  rw [k2_θIn', div_lt_one (k2_t_sub_ε_pos S L)]; exact k2_θIn_lt S L
theorem k2_θOut'_pos : 0 < k2_θOut' S L :=
  div_pos (by linarith [k2_lt_θOut S L]) (k2_one_sub_t_sub_ε_pos S L)
theorem k2_θOut'_lt_one : k2_θOut' S L < 1 := by
  rw [k2_θOut', div_lt_one (k2_one_sub_t_sub_ε_pos S L)]; linarith [k2_θOut_lt_one S L]

theorem k2_θIn'_mul : k2_θIn' S L * (k2_t S L - k2_ε S L) = k2_θIn S L := by
  rw [k2_θIn', div_mul_cancel₀ _ (k2_t_sub_ε_pos S L).ne']
theorem k2_θOut'_mul : k2_t S L + k2_ε S L + k2_θOut' S L * (1 - k2_t S L - k2_ε S L) = k2_θOut S L := by
  rw [k2_θOut', div_mul_cancel₀ _ (k2_one_sub_t_sub_ε_pos S L).ne']; ring

theorem k2_θIn'_mem : k2_θIn' S L ∈ Set.Ico (0:ℝ) 1 := ⟨(k2_θIn'_pos S L).le, k2_θIn'_lt_one S L⟩
theorem k2_θOut'_mem : k2_θOut' S L ∈ Set.Ico (0:ℝ) 1 := ⟨(k2_θOut'_pos S L).le, k2_θOut'_lt_one S L⟩

/-- the label of `e1` in `ZMod (k+4)` -/
abbrev k2_mA : ZMod (k2_k S L + 4) := ((k2_av S L : ℕ) : ZMod (k2_k S L + 4))

theorem k2_mA_val : (k2_mA S L).val = k2_av S L :=
  ZMod.val_natCast_of_lt (by have := k2_av_lt S L; omega)

theorem k2_mA_add_val {j : ℕ} (hj : j ≤ 4) : (k2_mA S L + j).val = k2_av S L + j := by
  have := k2_av_lt S L
  rw [k2_mA, ← Nat.cast_add, ZMod.val_natCast_of_lt (by omega)]

theorem k2_eS_eq (j : ℕ) : k2_eS S L j = ⟨L.r.1, k2_mA S L + j⟩ := by
  unfold k2_eS k2_mA; rw [Nat.cast_add]

/-- the kinked arc of `D'` through the disc: from `θIn'` on `e1` to `θOut'` on `e5` -/
def k2_arc' : (k2_shadow S L).Arc :=
  ⟨L.r.1, (k2_mA S L, ⟨k2_θIn' S L, k2_θIn'_mem S L⟩),
    (k2_mA S L + 4, ⟨k2_θOut' S L, k2_θOut'_mem S L⟩)⟩

/-- points of the kinked arc: on `e1` after `θIn'`, on a middle edge, or on `e5` before `θOut'` -/
theorem k2_inner_arc'_iff (q : (k2_shadow S L).Pt) :
    (k2_arc' S L).Inner q ↔
      (q.2.1.val = k2_av S L ∧ k2_θIn' S L < q.2.2.val) ∨ q.2.1.val = k2_av S L + 1 ∨
      q.2.1.val = k2_av S L + 2 ∨ q.2.1.val = k2_av S L + 3 ∨
      (q.2.1.val = k2_av S L + 4 ∧ q.2.2.val < k2_θOut' S L) := by
  have hav := k2_av_lt S L
  have hm := k2_mA_val S L
  have key := k2_traversalBetween_span_four (n := k2_k S L + 4) (k2_mA S L) (by rw [hm]; omega)
    ⟨k2_θIn' S L, k2_θIn'_mem S L⟩ ⟨k2_θOut' S L, k2_θOut'_mem S L⟩
  have h1 : (k2_mA S L + 1).val = k2_av S L + 1 := by
    have := k2_mA_add_val S L (j := 1) (by norm_num); simpa using this
  have h2 : (k2_mA S L + 2).val = k2_av S L + 2 := by
    have := k2_mA_add_val S L (j := 2) (by norm_num); simpa using this
  have h3 : (k2_mA S L + 3).val = k2_av S L + 3 := by
    have := k2_mA_add_val S L (j := 3) (by norm_num); simpa using this
  have h4 : (k2_mA S L + 4).val = k2_av S L + 4 := by
    have := k2_mA_add_val S L (j := 4) (by norm_num); simpa using this
  constructor
  · rintro ⟨r, hr, rfl⟩
    show (r.1.val = k2_av S L ∧ k2_θIn' S L < r.2.val) ∨ r.1.val = k2_av S L + 1 ∨
      r.1.val = k2_av S L + 2 ∨ r.1.val = k2_av S L + 3 ∨
      (r.1.val = k2_av S L + 4 ∧ r.2.val < k2_θOut' S L)
    rcases (key r).mp hr with ⟨h, h'⟩ | h | h | h | ⟨h, h'⟩
    · exact Or.inl ⟨by rw [h, hm], h'⟩
    · exact Or.inr (Or.inl (by rw [h, h1]))
    · exact Or.inr (Or.inr (Or.inl (by rw [h, h2])))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (by rw [h, h3]))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨by rw [h, h4], h'⟩)))
  · intro h
    obtain ⟨i, m, θ⟩ := q
    obtain rfl := k2_fin_eq S L i
    simp only at h
    refine ⟨(m, θ), (key (m, θ)).mpr ?_, rfl⟩
    rcases h with ⟨h, h'⟩ | h | h | h | ⟨h, h'⟩
    · exact Or.inl ⟨ZMod.val_injective _ (h.trans hm.symm), h'⟩
    · exact Or.inr (Or.inl (ZMod.val_injective _ (h.trans h1.symm)))
    · exact Or.inr (Or.inr (Or.inl (ZMod.val_injective _ (h.trans h2.symm))))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (ZMod.val_injective _ (h.trans h3.symm)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨ZMod.val_injective _ (h.trans h4.symm), h'⟩)))

/-! #### Traversal points of `D'` in the disc; the kinked arc is an arc of the disc; `D'` is clean -/

/-- the label value of a traversal point's strand -/
abbrev k2_plab (q : (k2_shadow S L).Pt) : ℕ := q.2.1.val

theorem k2_lab_pt (q : (k2_shadow S L).Pt) : k2_lab S L ⟨q.1, q.2.1⟩ = k2_plab S L q := rfl

theorem k2_eval_pt (q : (k2_shadow S L).Pt) :
    (k2_shadow S L).eval q = (k2_shadow S L).edgePt ⟨q.1, q.2.1⟩ q.2.2.val := rfl

/-- points of `e1` and `e5` as points of `s₀` -/
theorem k2_eval_e1 (q : (k2_shadow S L).Pt) (h : k2_plab S L q = k2_av S L) :
    (k2_shadow S L).eval q = S.D.Γ.edgePt (k2_s₀ S L) (q.2.2.val * (k2_t S L - k2_ε S L)) := by
  rw [k2_eval_pt, Shadow.edgePt_eq, Shadow.edgePt_eq, k2_tail_e1 S L h, k2_dir_e1 S L h, k2_tail_s₀,
    smul_smul]

theorem k2_eval_e5 (q : (k2_shadow S L).Pt) (h : k2_plab S L q = k2_av S L + 4) :
    (k2_shadow S L).eval q =
      S.D.Γ.edgePt (k2_s₀ S L) (k2_t S L + k2_ε S L + q.2.2.val * (1 - k2_t S L - k2_ε S L)) := by
  rw [k2_eval_pt, Shadow.edgePt_eq, Shadow.edgePt_eq, k2_tail_e5 S L h, k2_dir_e5 S L h, k2_tail_s₀,
    k2_Dv, k2_r₀_eq]
  module

theorem k2_eval_mem_seg (q : (k2_shadow S L).Pt) :
    (k2_shadow S L).eval q ∈ (k2_shadow S L).seg ⟨q.1, q.2.1⟩ := Smoothing.eval_mem_seg q

/-- **the trace of `D'` in the closed disc** -/
theorem k2_eval_mem_U_iff (q : (k2_shadow S L).Pt) :
    (k2_shadow S L).eval q ∈ k2_U S L ↔
      (k2_plab S L q = k2_av S L ∧ k2_θIn' S L ≤ q.2.2.val) ∨ k2_plab S L q = k2_av S L + 1 ∨
      k2_plab S L q = k2_av S L + 2 ∨ k2_plab S L q = k2_av S L + 3 ∨
      (k2_plab S L q = k2_av S L + 4 ∧ q.2.2.val ≤ k2_θOut' S L) := by
  have hθ0 := q.2.2.2.1
  have hθ1 := q.2.2.2.2
  have hpos := k2_t_sub_ε_pos S L
  have hpos' := k2_one_sub_t_sub_ε_pos S L
  have hθIn := k2_θIn_lt S L
  have hθOut := k2_lt_θOut S L
  have hεpos := k2_ε_pos S L
  rcases k2_kind_cases S L ⟨q.1, q.2.1⟩ with h | h | h | h | h | h | h <;> rw [k2_lab_pt] at h
  · constructor
    · intro hU; exact absurd hU (k2_old_not_mem_U S L (k2_isOld_of_lt S L h) (k2_eval_mem_seg S L q))
    · intro hc; omega
  · rw [k2_eval_e1 S L q h, k2_edgePt_s₀_mem_U_iff]
    constructor
    · rintro ⟨h1, -⟩
      refine Or.inl ⟨h, ?_⟩
      rw [k2_θIn', div_le_iff₀ hpos]; exact h1
    · rintro (⟨-, h1⟩ | h1 | h1 | h1 | ⟨h1, -⟩)
      · rw [k2_θIn', div_le_iff₀ hpos] at h1
        exact ⟨h1, by nlinarith⟩
      all_goals omega
  · have hmid : k2_IsMid S L ⟨q.1, q.2.1⟩ := ⟨by rw [k2_lab_pt]; omega, by rw [k2_lab_pt]; omega⟩
    exact ⟨fun _ => Or.inr (Or.inl h), fun _ => k2_mid_mem_U S L hmid (k2_eval_mem_seg S L q)⟩
  · have hmid : k2_IsMid S L ⟨q.1, q.2.1⟩ := ⟨by rw [k2_lab_pt]; omega, by rw [k2_lab_pt]; omega⟩
    exact ⟨fun _ => Or.inr (Or.inr (Or.inl h)), fun _ => k2_mid_mem_U S L hmid (k2_eval_mem_seg S L q)⟩
  · have hmid : k2_IsMid S L ⟨q.1, q.2.1⟩ := ⟨by rw [k2_lab_pt]; omega, by rw [k2_lab_pt]; omega⟩
    exact ⟨fun _ => Or.inr (Or.inr (Or.inr (Or.inl h))),
      fun _ => k2_mid_mem_U S L hmid (k2_eval_mem_seg S L q)⟩
  · rw [k2_eval_e5 S L q h, k2_edgePt_s₀_mem_U_iff]
    constructor
    · rintro ⟨-, h1⟩
      refine Or.inr (Or.inr (Or.inr (Or.inr ⟨h, ?_⟩)))
      rw [k2_θOut', le_div_iff₀ hpos']; linarith
    · rintro (⟨h1, -⟩ | h1 | h1 | h1 | ⟨-, h1⟩)
      · omega
      · omega
      · omega
      · omega
      · rw [k2_θOut', le_div_iff₀ hpos'] at h1
        exact ⟨by nlinarith, by linarith⟩
  · constructor
    · intro hU; exact absurd hU (k2_old_not_mem_U S L (k2_isOld_of_ge S L h) (k2_eval_mem_seg S L q))
    · intro hc; omega

/-- **the trace of `D'` in the open disc** -/
theorem k2_eval_mem_ball_iff (q : (k2_shadow S L).Pt) :
    (k2_shadow S L).eval q ∈ Metric.ball (k2_r₀ S L) (k2_ρ S L) ↔
      (k2_plab S L q = k2_av S L ∧ k2_θIn' S L < q.2.2.val) ∨ k2_plab S L q = k2_av S L + 1 ∨
      k2_plab S L q = k2_av S L + 2 ∨ k2_plab S L q = k2_av S L + 3 ∨
      (k2_plab S L q = k2_av S L + 4 ∧ q.2.2.val < k2_θOut' S L) := by
  have hθ0 := q.2.2.2.1
  have hθ1 := q.2.2.2.2
  have hpos := k2_t_sub_ε_pos S L
  have hpos' := k2_one_sub_t_sub_ε_pos S L
  have hθIn := k2_θIn_lt S L
  have hθOut := k2_lt_θOut S L
  have hεpos := k2_ε_pos S L
  rcases k2_kind_cases S L ⟨q.1, q.2.1⟩ with h | h | h | h | h | h | h <;> rw [k2_lab_pt] at h
  · constructor
    · intro hU
      exact absurd (Metric.ball_subset_closedBall hU)
        (k2_old_not_mem_U S L (k2_isOld_of_lt S L h) (k2_eval_mem_seg S L q))
    · intro hc; omega
  · rw [k2_eval_e1 S L q h, k2_edgePt_s₀_mem_ball_iff]
    constructor
    · rintro ⟨h1, -⟩
      refine Or.inl ⟨h, ?_⟩
      rw [k2_θIn', div_lt_iff₀ hpos]; exact h1
    · rintro (⟨-, h1⟩ | h1 | h1 | h1 | ⟨h1, -⟩)
      · rw [k2_θIn', div_lt_iff₀ hpos] at h1
        exact ⟨h1, by nlinarith⟩
      all_goals omega
  · have hmid : k2_IsMid S L ⟨q.1, q.2.1⟩ := ⟨by rw [k2_lab_pt]; omega, by rw [k2_lab_pt]; omega⟩
    exact ⟨fun _ => Or.inr (Or.inl h), fun _ => k2_mid_mem_ball S L hmid (k2_eval_mem_seg S L q)⟩
  · have hmid : k2_IsMid S L ⟨q.1, q.2.1⟩ := ⟨by rw [k2_lab_pt]; omega, by rw [k2_lab_pt]; omega⟩
    exact ⟨fun _ => Or.inr (Or.inr (Or.inl h)),
      fun _ => k2_mid_mem_ball S L hmid (k2_eval_mem_seg S L q)⟩
  · have hmid : k2_IsMid S L ⟨q.1, q.2.1⟩ := ⟨by rw [k2_lab_pt]; omega, by rw [k2_lab_pt]; omega⟩
    exact ⟨fun _ => Or.inr (Or.inr (Or.inr (Or.inl h))),
      fun _ => k2_mid_mem_ball S L hmid (k2_eval_mem_seg S L q)⟩
  · rw [k2_eval_e5 S L q h, k2_edgePt_s₀_mem_ball_iff]
    constructor
    · rintro ⟨-, h1⟩
      refine Or.inr (Or.inr (Or.inr (Or.inr ⟨h, ?_⟩)))
      rw [k2_θOut', lt_div_iff₀ hpos']; linarith
    · rintro (⟨h1, -⟩ | h1 | h1 | h1 | ⟨-, h1⟩)
      · omega
      · omega
      · omega
      · omega
      · rw [k2_θOut', lt_div_iff₀ hpos'] at h1
        exact ⟨by nlinarith, by linarith⟩
  · constructor
    · intro hU
      exact absurd (Metric.ball_subset_closedBall hU)
        (k2_old_not_mem_U S L (k2_isOld_of_ge S L h) (k2_eval_mem_seg S L q))
    · intro hc; omega

theorem k2_arc'_startPt : (k2_arc' S L).startPt = ⟨L.r.1, (k2_mA S L, ⟨k2_θIn' S L, k2_θIn'_mem S L⟩)⟩ :=
  rfl
theorem k2_arc'_stopPt :
    (k2_arc' S L).stopPt = ⟨L.r.1, (k2_mA S L + 4, ⟨k2_θOut' S L, k2_θOut'_mem S L⟩)⟩ := rfl

theorem k2_eval_arc'_startPt :
    (k2_shadow S L).eval (k2_arc' S L).startPt = S.D.Γ.edgePt (k2_s₀ S L) (k2_θIn S L) := by
  rw [k2_arc'_startPt, k2_eval_e1 S L _ (k2_mA_val S L)]
  show S.D.Γ.edgePt (k2_s₀ S L) (k2_θIn' S L * (k2_t S L - k2_ε S L)) = _
  rw [k2_θIn'_mul]

theorem k2_eval_arc'_stopPt :
    (k2_shadow S L).eval (k2_arc' S L).stopPt = S.D.Γ.edgePt (k2_s₀ S L) (k2_θOut S L) := by
  rw [k2_arc'_stopPt, k2_eval_e5 S L _ (by
    show (k2_mA S L + 4).val = _
    have := k2_mA_add_val S L (j := 4) (by norm_num); simpa using this)]
  show S.D.Γ.edgePt (k2_s₀ S L) (k2_t S L + k2_ε S L + k2_θOut' S L * (1 - k2_t S L - k2_ε S L)) = _
  rw [k2_θOut'_mul]

/-- the same entering and exiting points -/
theorem k2_start_eq : (k2_shadow S L).eval (k2_arc' S L).startPt = S.D.Γ.eval (k2_arc S L).startPt := by
  rw [k2_eval_arc'_startPt, k2_eval_arc_startPt]
theorem k2_stop_eq : (k2_shadow S L).eval (k2_arc' S L).stopPt = S.D.Γ.eval (k2_arc S L).stopPt := by
  rw [k2_eval_arc'_stopPt, k2_eval_arc_stopPt]

theorem k2_isArc_arc' : (k2_shadow S L).IsArc (k2_U S L) (k2_arc' S L) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h
    have := congrArg (fun r : TraversalPoint (k2_k S L + 4) => r.1.val) h
    change (k2_mA S L).val = (k2_mA S L + 4).val at this
    rw [k2_mA_val] at this
    have h4 := k2_mA_add_val S L (j := 4) (by norm_num)
    simp only [Nat.cast_ofNat] at h4
    omega
  · rw [k2_frontier_U, k2_eval_arc'_startPt]
    exact k2_edgePt_s₀_mem_sphere S L _ (Or.inl rfl)
  · rw [k2_frontier_U, k2_eval_arc'_stopPt]
    exact k2_edgePt_s₀_mem_sphere S L _ (Or.inr rfl)
  · intro q hq
    rw [k2_interior_U, k2_eval_mem_ball_iff]
    exact (k2_inner_arc'_iff S L q).mp hq

/-- a traversal point with a given label value and parameter -/
theorem k2_pt_eq_of (q : (k2_shadow S L).Pt) {m : ZMod (k2_k S L + 4)} {θ : Set.Ico (0:ℝ) 1}
    (hm : k2_plab S L q = m.val) (hθ : q.2.2.val = θ.val) : q = ⟨L.r.1, (m, θ)⟩ := by
  obtain ⟨i, m', θ'⟩ := q
  obtain rfl := k2_fin_eq S L i
  have h1 : m' = m := ZMod.val_injective _ hm
  have h2 : θ' = θ := Subtype.ext hθ
  rw [h1, h2]

theorem k2_arcCover_D' : (k2_shadow S L).ArcCover (k2_U S L) {k2_arc' S L} := by
  have hclosed : IsClosed (k2_U S L) := Metric.isClosed_closedBall
  have h4 : (k2_mA S L + 4).val = k2_av S L + 4 := by
    have := k2_mA_add_val S L (j := 4) (by norm_num); simpa using this
  refine ⟨?_, ?_, ?_⟩
  · intro a ha
    rw [Set.mem_singleton_iff] at ha
    rw [ha]; exact k2_isArc_arc' S L
  · intro q
    constructor
    · intro hq
      refine ⟨k2_arc' S L, Set.mem_singleton _, ?_⟩
      rw [k2_eval_mem_U_iff] at hq
      unfold Shadow.Arc.Mem
      rw [k2_inner_arc'_iff]
      rcases hq with ⟨h1, h2⟩ | h | h | h | ⟨h1, h2⟩
      · rcases h2.lt_or_eq with h2 | h2
        · exact Or.inr (Or.inr (Or.inl ⟨h1, h2⟩))
        · left
          rw [k2_arc'_startPt]
          exact k2_pt_eq_of S L q (by rw [h1, k2_mA_val]) h2.symm
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
      · rcases h2.lt_or_eq with h2 | h2
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨h1, h2⟩)))))
        · right; left
          rw [k2_arc'_stopPt]
          exact k2_pt_eq_of S L q (by rw [h1, h4]) h2
    · rintro ⟨a, ha, hq⟩
      rw [Set.mem_singleton_iff] at ha
      subst ha
      exact Smoothing.isArc_eval_mem_of_mem (k2_isArc_arc' S L) hclosed hq
  · intro a ha b hb hab
    rw [Set.mem_singleton_iff] at ha hb
    exact absurd (ha.trans hb.symm) hab

/-- **`D'` meets the disc cleanly**: the frontier points are the two ends of the kinked arc -/
theorem k2_clean_D' : Clean (k2_U S L) (k2_D' S L) := by
  have h4 : (k2_mA S L + 4).val = k2_av S L + 4 := by
    have := k2_mA_add_val S L (j := 4) (by norm_num); simpa using this
  have hends : ∀ q : (k2_shadow S L).Pt, (k2_shadow S L).eval q ∈ frontier (k2_U S L) →
      q = (k2_arc' S L).startPt ∨ q = (k2_arc' S L).stopPt := by
    intro q hq
    rw [k2_frontier_U] at hq
    have hU := (k2_eval_mem_U_iff S L q).mp (Metric.sphere_subset_closedBall hq)
    have hB : ¬ (k2_shadow S L).eval q ∈ Metric.ball (k2_r₀ S L) (k2_ρ S L) :=
      fun h => (Metric.mem_ball.mp h).ne (Metric.mem_sphere.mp hq)
    rw [k2_eval_mem_ball_iff] at hB
    rcases hU with ⟨h1, h2⟩ | h | h | h | ⟨h1, h2⟩
    · left
      rw [k2_arc'_startPt]
      refine k2_pt_eq_of S L q (by rw [h1, k2_mA_val]) ?_
      by_contra hne
      exact hB (Or.inl ⟨h1, lt_of_le_of_ne h2 (Ne.symm hne)⟩)
    · exact absurd (Or.inr (Or.inl h)) hB
    · exact absurd (Or.inr (Or.inr (Or.inl h))) hB
    · exact absurd (Or.inr (Or.inr (Or.inr (Or.inl h)))) hB
    · right
      rw [k2_arc'_stopPt]
      refine k2_pt_eq_of S L q (by rw [h1, h4]) ?_
      by_contra hne
      exact hB (Or.inr (Or.inr (Or.inr (Or.inr ⟨h1, lt_of_le_of_ne h2 hne⟩))))
  refine ⟨?_, ?_⟩
  · intro q hq q' hq' heq
    have hne : (k2_shadow S L).eval (k2_arc' S L).startPt ≠ (k2_shadow S L).eval (k2_arc' S L).stopPt := by
      rw [k2_eval_arc'_startPt, k2_eval_arc'_stopPt]
      intro h
      exact (k2_θIn_lt_θOut S L).ne (S.D.generic.edgePt_injective _ h)
    rcases hends q hq with rfl | rfl <;> rcases hends q' hq' with rfl | rfl
    · rfl
    · exact absurd heq hne
    · exact absurd heq.symm hne
    · rfl
  · intro i
    refine ⟨(0, ⟨0, le_rfl, zero_lt_one⟩), ?_⟩
    have h0 : (k2_shadow S L).eval ⟨i, (0, ⟨0, le_rfl, zero_lt_one⟩)⟩ = (k2_shadow S L).tail ⟨i, 0⟩ :=
      (k2_shadow S L).edgePt_zero ⟨i, 0⟩
    show (k2_shadow S L).eval ⟨i, (0, ⟨0, le_rfl, zero_lt_one⟩)⟩ ∉ k2_U S L
    rw [h0, k2_tail']
    show k2_Q S L (0 : ZMod (k2_k S L + 4)).val ∉ k2_U S L
    rw [ZMod.val_zero, k2_Q_of_le S L (Nat.zero_le _), Nat.cast_zero]
    exact k2_tail_not_mem_U S L ⟨L.r.1, 0⟩

theorem k2_localFrame : LocalFrame (k2_U S L) S.D (k2_D' S L) :=
  ⟨k2_isDisc_U S L, k2_clean_D S L, k2_clean_D' S L⟩

/-- the kink is the only crossing of `D'` inside the disc -/
theorem k2_inner_iff' (y : (k2_shadow S L).Crossing) :
    (k2_shadow S L).crossingPoint y ∈ interior (k2_U S L) ↔ y = k2_kink S L := by
  constructor
  · intro h
    by_contra hy
    rw [k2_crossingPoint_orig S L y hy] at h
    exact k2_crossingPoint_not_mem_U S L _ (interior_subset h)
  · rintro rfl
    rw [k2_crossingPoint_kink, k2_interior_U]
    exact k2_K_mem_ball S L

/-! #### The outside correspondence: parameters, `origPt`, the bijection -/

/-- the parameter on the original strand of the point at parameter `θ` of a non-middle strand -/
def k2_lp (u : (k2_shadow S L).Strand) (θ : ℝ) : ℝ :=
  if k2_lab S L u = k2_av S L then θ * (k2_t S L - k2_ε S L)
  else if k2_lab S L u = k2_av S L + 4 then k2_t S L + k2_ε S L + θ * (1 - k2_t S L - k2_ε S L)
  else θ

/-- its inverse -/
def k2_lpinv (u : (k2_shadow S L).Strand) (θ : ℝ) : ℝ :=
  if k2_lab S L u = k2_av S L then θ / (k2_t S L - k2_ε S L)
  else if k2_lab S L u = k2_av S L + 4 then (θ - k2_t S L - k2_ε S L) / (1 - k2_t S L - k2_ε S L)
  else θ

theorem k2_lp_lpinv (u : (k2_shadow S L).Strand) (θ : ℝ) : k2_lp S L u (k2_lpinv S L u θ) = θ := by
  unfold k2_lp k2_lpinv
  have h1 := (k2_t_sub_ε_pos S L).ne'
  have h2 := (k2_one_sub_t_sub_ε_pos S L).ne'
  split_ifs
  · rw [div_mul_cancel₀ _ h1]
  · rw [div_mul_cancel₀ _ h2]; ring
  · rfl

theorem k2_lpinv_lp (u : (k2_shadow S L).Strand) (θ : ℝ) : k2_lpinv S L u (k2_lp S L u θ) = θ := by
  unfold k2_lp k2_lpinv
  have h1 := (k2_t_sub_ε_pos S L).ne'
  have h2 := (k2_one_sub_t_sub_ε_pos S L).ne'
  split_ifs
  · rw [mul_div_cancel_right₀ _ h1]
  · rw [show k2_t S L + k2_ε S L + θ * (1 - k2_t S L - k2_ε S L) - k2_t S L - k2_ε S L =
      θ * (1 - k2_t S L - k2_ε S L) by ring, mul_div_cancel_right₀ _ h2]
  · rfl

theorem k2_lp_old {u : (k2_shadow S L).Strand} (hu : k2_IsOld S L u) (θ : ℝ) : k2_lp S L u θ = θ := by
  unfold k2_lp; unfold k2_IsOld at hu; rw [ite_eq_right (by omega), ite_eq_right (by omega)]
theorem k2_lp_e1 {u : (k2_shadow S L).Strand} (hu : k2_lab S L u = k2_av S L) (θ : ℝ) :
    k2_lp S L u θ = θ * (k2_t S L - k2_ε S L) := by
  unfold k2_lp; rw [ite_eq_left hu]
theorem k2_lp_e5 {u : (k2_shadow S L).Strand} (hu : k2_lab S L u = k2_av S L + 4) (θ : ℝ) :
    k2_lp S L u θ = k2_t S L + k2_ε S L + θ * (1 - k2_t S L - k2_ε S L) := by
  unfold k2_lp; rw [ite_eq_right (by omega), ite_eq_left hu]
theorem k2_lpinv_old {u : (k2_shadow S L).Strand} (hu : k2_IsOld S L u) (θ : ℝ) :
    k2_lpinv S L u θ = θ := by
  unfold k2_lpinv; unfold k2_IsOld at hu; rw [ite_eq_right (by omega), ite_eq_right (by omega)]
theorem k2_lpinv_e1 {u : (k2_shadow S L).Strand} (hu : k2_lab S L u = k2_av S L) (θ : ℝ) :
    k2_lpinv S L u θ = θ / (k2_t S L - k2_ε S L) := by
  unfold k2_lpinv; rw [ite_eq_left hu]
theorem k2_lpinv_e5 {u : (k2_shadow S L).Strand} (hu : k2_lab S L u = k2_av S L + 4) (θ : ℝ) :
    k2_lpinv S L u θ = (θ - k2_t S L - k2_ε S L) / (1 - k2_t S L - k2_ε S L) := by
  unfold k2_lpinv; rw [ite_eq_right (by omega), ite_eq_left hu]

/-- **points of non-middle strands as points of their originals** -/
theorem k2_edgePt_orig {u : (k2_shadow S L).Strand} (hu : ¬ k2_IsMid S L u) (θ : ℝ) :
    (k2_shadow S L).edgePt u θ = S.D.Γ.edgePt (k2_orig S L u) (k2_lp S L u θ) := by
  rw [k2_not_isMid_iff] at hu
  rcases hu with hu | hu | hu
  · rw [k2_lp_old S L hu, k2_edgePt_old S L hu]
  · rw [k2_lp_e1 S L hu, k2_orig_of_eq_a S L hu, Shadow.edgePt_eq, Shadow.edgePt_eq, k2_tail_e1 S L hu,
      k2_dir_e1 S L hu, k2_tail_s₀, smul_smul]
  · rw [k2_lp_e5 S L hu, k2_orig_of_eq_a4 S L hu, Shadow.edgePt_eq, Shadow.edgePt_eq,
      k2_tail_e5 S L hu, k2_dir_e5 S L hu, k2_tail_s₀, k2_Dv, k2_r₀_eq]
    module

/-- the parameter on `s₀` of a point of `e1` / `e5` lies in `[0, 1)` -/
theorem k2_lp_mem {u : (k2_shadow S L).Strand} (hu : ¬ k2_IsMid S L u) {θ : ℝ}
    (hθ : θ ∈ Set.Ico (0:ℝ) 1) : k2_lp S L u θ ∈ Set.Ico (0:ℝ) 1 := by
  have h1 := k2_t_sub_ε_pos S L
  have h2 := k2_one_sub_t_sub_ε_pos S L
  have hε := k2_ε_pos S L
  have ht := k2_t_pos S L
  obtain ⟨hθ0, hθ1⟩ := hθ
  rw [k2_not_isMid_iff] at hu
  rcases hu with hu | hu | hu
  · rw [k2_lp_old S L hu]; exact ⟨hθ0, hθ1⟩
  · rw [k2_lp_e1 S L hu]; constructor <;> nlinarith
  · rw [k2_lp_e5 S L hu]; constructor <;> nlinarith

/-- the traversal point of `D` under a traversal point of `D'` -/
def k2_origPt (q : (k2_shadow S L).Pt) : S.D.Γ.Pt :=
  ⟨(k2_orig S L ⟨q.1, q.2.1⟩).1, ((k2_orig S L ⟨q.1, q.2.1⟩).2,
    clampIco (k2_lp S L ⟨q.1, q.2.1⟩ q.2.2.val))⟩

theorem k2_origPt_fst (q : (k2_shadow S L).Pt) : (k2_origPt S L q).1 = q.1 := rfl

theorem k2_origPt_strand (q : (k2_shadow S L).Pt) :
    (⟨(k2_origPt S L q).1, (k2_origPt S L q).2.1⟩ : S.D.Γ.Strand) = k2_orig S L ⟨q.1, q.2.1⟩ := rfl

theorem k2_origPt_param (q : (k2_shadow S L).Pt) (hq : ¬ k2_IsMid S L ⟨q.1, q.2.1⟩) :
    (k2_origPt S L q).2.2.val = k2_lp S L ⟨q.1, q.2.1⟩ q.2.2.val :=
  clampIco_val_of_mem (k2_lp_mem S L hq q.2.2.2)

/-- outside the open disc the strand of a traversal point is not a middle edge -/
theorem k2_not_mid_of_not_mem_interior (q : (k2_shadow S L).Pt)
    (hq : (k2_shadow S L).eval q ∉ interior (k2_U S L)) : ¬ k2_IsMid S L ⟨q.1, q.2.1⟩ := by
  intro h
  rw [k2_interior_U] at hq
  exact hq (k2_mid_mem_ball S L h (k2_eval_mem_seg S L q))

theorem k2_eval_origPt (q : (k2_shadow S L).Pt) (hq : (k2_shadow S L).eval q ∉ interior (k2_U S L)) :
    S.D.Γ.eval (k2_origPt S L q) = (k2_shadow S L).eval q := by
  have hnm := k2_not_mid_of_not_mem_interior S L q hq
  rw [Smoothing.eval_eq_edgePt, k2_origPt_strand, k2_origPt_param S L q hnm, k2_eval_pt,
    k2_edgePt_orig S L hnm]

theorem k2_origPt_outside (q : (k2_shadow S L).Pt) (hq : (k2_shadow S L).eval q ∉ interior (k2_U S L)) :
    S.D.Γ.eval (k2_origPt S L q) ∉ interior (k2_U S L) := by
  rw [k2_eval_origPt S L q hq]; exact hq

/-- the lift of an old strand of `D` -/
def k2_liftOld (e : S.D.Γ.Strand) : (k2_shadow S L).Strand :=
  ⟨e.1, ((k2_ν S L e.2.val : ℕ) : ZMod (k2_k S L + 4))⟩

theorem k2_lab_liftOld {e : S.D.Γ.Strand} (he : e ≠ k2_s₀ S L) :
    k2_lab S L (k2_liftOld S L e) = k2_ν S L e.2.val := by
  obtain ⟨b, rfl⟩ := k2_strand_eq S L e
  have hb := ZMod.val_lt b
  show ((k2_ν S L b.val : ℕ) : ZMod (k2_k S L + 4)).val = k2_ν S L b.val
  apply ZMod.val_natCast_of_lt
  unfold k2_ν; split_ifs <;> omega

theorem k2_liftOld_isOld {e : S.D.Γ.Strand} (he : e ≠ k2_s₀ S L) : k2_IsOld S L (k2_liftOld S L e) := by
  unfold k2_IsOld
  rw [k2_lab_liftOld S L he]
  have := k2_val_ne_av_of_ne S L he
  unfold k2_ν; split_ifs <;> omega

theorem k2_orig_liftOld {e : S.D.Γ.Strand} (he : e ≠ k2_s₀ S L) : k2_orig S L (k2_liftOld S L e) = e := by
  have hl := k2_lab_liftOld S L he
  have hv := k2_val_ne_av_of_ne S L he
  obtain ⟨b, rfl⟩ := k2_strand_eq S L e
  have hlt := ZMod.val_lt b
  have e2 : (⟨L.r.1, b⟩ : S.D.Γ.Strand).2.val = b.val := rfl
  rw [e2] at hl hv
  rw [k2_orig_eq, hl, Smoothing.Strand_mk_eq_mk_iff]
  apply ZMod.val_injective
  rw [ZMod.val_natCast_of_lt (by unfold k2_ν; split_ifs <;> omega)]
  show (if k2_ν S L b.val ≤ k2_av S L then k2_ν S L b.val else k2_ν S L b.val - 4) = b.val
  unfold k2_ν; split_ifs <;> omega

theorem k2_liftStrand_eq_liftOld (x : S.D.Γ.Crossing) {e : S.D.Γ.Strand} (he : e ∈ x.val)
    (hne : e ≠ k2_s₀ S L) : k2_liftStrand S L x e he = k2_liftOld S L e := by
  unfold k2_liftStrand; rw [ite_eq_right hne]; rfl

/-- **surjectivity of `origPt` onto the outside points of `D`** -/
theorem k2_exists_origPt_eq (p : S.D.Γ.Pt) (hp : S.D.Γ.eval p ∉ interior (k2_U S L)) :
    ∃ q : (k2_shadow S L).Pt, k2_origPt S L q = p ∧ (k2_shadow S L).eval q = S.D.Γ.eval p := by
  have h1 := k2_t_sub_ε_pos S L
  have h2 := k2_one_sub_t_sub_ε_pos S L
  have hε := k2_ε_pos S L
  obtain ⟨i, b, θ⟩ := p
  obtain rfl := k2_fin_eq S L i
  have hθ0 := θ.2.1
  have hθ1 := θ.2.2
  by_cases he : (⟨L.r.1, b⟩ : S.D.Γ.Strand) = k2_s₀ S L
  · have hb : b = k2_a S L := Smoothing.Strand_mk_eq_mk_iff.mp he
    subst hb
    have hp' : S.D.Γ.edgePt (k2_s₀ S L) θ.val ∉ Metric.ball (k2_r₀ S L) (k2_ρ S L) := by
      rw [← k2_interior_U]; exact hp
    rw [k2_edgePt_s₀_mem_ball_iff, not_and_or, not_lt, not_lt] at hp'
    rcases hp' with h | h
    · -- the point lies on `e1`
      have hl : k2_lab S L (k2_eS S L 0) = k2_av S L :=
        (k2_lab_eS S L (by norm_num)).trans (Nat.add_zero _)
      have hnm : ¬ k2_IsMid S L (k2_eS S L 0) := (k2_not_isMid_iff S L _).mpr (Or.inr (Or.inl hl))
      have hmem : θ.val / (k2_t S L - k2_ε S L) ∈ Set.Ico (0:ℝ) 1 := by
        constructor
        · positivity
        · rw [div_lt_one h1]; linarith [k2_θIn_lt S L]
      refine ⟨⟨(k2_eS S L 0).1, ((k2_eS S L 0).2, ⟨_, hmem⟩)⟩, ?_, ?_⟩
      · refine (Shadow.mk_eq_mk_iff (k2_orig S L (k2_eS S L 0)) (k2_s₀ S L) _ _).mpr
          ⟨k2_orig_of_eq_a S L hl, Subtype.ext ?_⟩
        show (clampIco (k2_lp S L (k2_eS S L 0) (θ.val / (k2_t S L - k2_ε S L)))).val = θ.val
        rw [clampIco_val_of_mem (k2_lp_mem S L hnm hmem), k2_lp_e1 S L hl, div_mul_cancel₀ _ h1.ne']
      · show (k2_shadow S L).edgePt (k2_eS S L 0) (θ.val / (k2_t S L - k2_ε S L)) =
          S.D.Γ.edgePt (k2_s₀ S L) θ.val
        rw [k2_edgePt_orig S L hnm, k2_orig_of_eq_a S L hl, k2_lp_e1 S L hl, div_mul_cancel₀ _ h1.ne']
    · -- the point lies on `e5`
      have hl : k2_lab S L (k2_eS S L 4) = k2_av S L + 4 := k2_lab_eS S L (by norm_num)
      have hnm : ¬ k2_IsMid S L (k2_eS S L 4) := (k2_not_isMid_iff S L _).mpr (Or.inr (Or.inr hl))
      have hmem : (θ.val - k2_t S L - k2_ε S L) / (1 - k2_t S L - k2_ε S L) ∈ Set.Ico (0:ℝ) 1 := by
        constructor
        · apply div_nonneg _ h2.le; linarith [k2_lt_θOut S L]
        · rw [div_lt_one h2]; linarith
      refine ⟨⟨(k2_eS S L 4).1, ((k2_eS S L 4).2, ⟨_, hmem⟩)⟩, ?_, ?_⟩
      · refine (Shadow.mk_eq_mk_iff (k2_orig S L (k2_eS S L 4)) (k2_s₀ S L) _ _).mpr
          ⟨k2_orig_of_eq_a4 S L hl, Subtype.ext ?_⟩
        show (clampIco (k2_lp S L (k2_eS S L 4)
          ((θ.val - k2_t S L - k2_ε S L) / (1 - k2_t S L - k2_ε S L)))).val = θ.val
        rw [clampIco_val_of_mem (k2_lp_mem S L hnm hmem), k2_lp_e5 S L hl, div_mul_cancel₀ _ h2.ne']
        ring
      · show (k2_shadow S L).edgePt (k2_eS S L 4)
          ((θ.val - k2_t S L - k2_ε S L) / (1 - k2_t S L - k2_ε S L)) = S.D.Γ.edgePt (k2_s₀ S L) θ.val
        rw [k2_edgePt_orig S L hnm, k2_orig_of_eq_a4 S L hl, k2_lp_e5 S L hl, div_mul_cancel₀ _ h2.ne']
        congr 1; ring
  · -- an old strand
    have hold := k2_liftOld_isOld S L he
    refine ⟨⟨(k2_liftOld S L ⟨L.r.1, b⟩).1, ((k2_liftOld S L ⟨L.r.1, b⟩).2, θ)⟩, ?_, ?_⟩
    · refine (Shadow.mk_eq_mk_iff (k2_orig S L (k2_liftOld S L ⟨L.r.1, b⟩)) ⟨L.r.1, b⟩ _ _).mpr
        ⟨k2_orig_liftOld S L he, Subtype.ext ?_⟩
      show (clampIco (k2_lp S L (k2_liftOld S L ⟨L.r.1, b⟩) θ.val)).val = θ.val
      rw [k2_lp_old S L hold, clampIco_val_of_mem θ.2]
    · show (k2_shadow S L).edgePt (k2_liftOld S L ⟨L.r.1, b⟩) θ.val = S.D.Γ.edgePt ⟨L.r.1, b⟩ θ.val
      rw [k2_edgePt_old S L hold, k2_orig_liftOld S L he]

/-- **injectivity of `origPt` on the outside points of `D'`** -/
theorem k2_origPt_injOn {q q' : (k2_shadow S L).Pt} (hq : (k2_shadow S L).eval q ∉ interior (k2_U S L))
    (hq' : (k2_shadow S L).eval q' ∉ interior (k2_U S L)) (h : k2_origPt S L q = k2_origPt S L q') :
    q = q' := by
  have hnm := k2_not_mid_of_not_mem_interior S L q hq
  have hnm' := k2_not_mid_of_not_mem_interior S L q' hq'
  obtain ⟨horig, hcl⟩ := (Shadow.mk_eq_mk_iff (k2_orig S L ⟨q.1, q.2.1⟩) (k2_orig S L ⟨q'.1, q'.2.1⟩)
    _ _).mp h
  have hp : k2_lp S L ⟨q.1, q.2.1⟩ q.2.2.val = k2_lp S L ⟨q'.1, q'.2.1⟩ q'.2.2.val := by
    rw [← k2_origPt_param S L q hnm, ← k2_origPt_param S L q' hnm']
    exact congrArg Subtype.val hcl
  have h1 := k2_t_sub_ε_pos S L
  have h2 := k2_one_sub_t_sub_ε_pos S L
  have hε := k2_ε_pos S L
  have hθ0 := q.2.2.2.1
  have hθ1 := q.2.2.2.2
  have hθ0' := q'.2.2.2.1
  have hθ1' := q'.2.2.2.2
  rcases k2_eq_of_orig_eq S L hnm hnm' horig with hu | ⟨ha, hb⟩ | ⟨ha, hb⟩
  · rw [hu] at hp
    have hθ : q.2.2.val = q'.2.2.val := by
      have := congrArg (k2_lpinv S L ⟨q'.1, q'.2.1⟩) hp
      rwa [k2_lpinv_lp, k2_lpinv_lp] at this
    exact (Shadow.mk_eq_mk_iff ⟨q.1, q.2.1⟩ ⟨q'.1, q'.2.1⟩ q.2.2 q'.2.2).mpr ⟨hu, Subtype.ext hθ⟩
  · exfalso
    rw [k2_lp_e1 S L ha, k2_lp_e5 S L hb] at hp
    nlinarith
  · exfalso
    rw [k2_lp_e5 S L ha, k2_lp_e1 S L hb] at hp
    nlinarith

theorem k2_origPt_bijective :
    Function.Bijective (fun q : (k2_shadow S L).Outside (k2_U S L) =>
      (⟨k2_origPt S L q.1, k2_origPt_outside S L q.1 q.2⟩ : S.D.Γ.Outside (k2_U S L))) := by
  constructor
  · rintro ⟨q, hq⟩ ⟨q', hq'⟩ h
    exact Subtype.ext (k2_origPt_injOn S L hq hq' (congrArg Subtype.val h))
  · rintro ⟨p, hp⟩
    obtain ⟨q, hq1, hq2⟩ := k2_exists_origPt_eq S L p hp
    exact ⟨⟨q, by rw [hq2]; exact hp⟩, Subtype.ext hq1⟩

/-- **the outside correspondence `φ`** -/
def k2_φ : S.D.Γ.Outside (k2_U S L) ≃ (k2_shadow S L).Outside (k2_U S L) :=
  (Equiv.ofBijective _ (k2_origPt_bijective S L)).symm

theorem k2_origPt_φ (p : S.D.Γ.Outside (k2_U S L)) : k2_origPt S L (k2_φ S L p).1 = p.1 :=
  congrArg Subtype.val (Equiv.ofBijective_apply_symm_apply _ (k2_origPt_bijective S L) p)

theorem k2_φ_eval (p : S.D.Γ.Outside (k2_U S L)) :
    (k2_shadow S L).eval (k2_φ S L p).1 = S.D.Γ.eval p.1 := by
  rw [← k2_eval_origPt S L _ (k2_φ S L p).2, k2_origPt_φ S L p]

theorem k2_φ_fst (p : S.D.Γ.Outside (k2_U S L)) : (k2_φ S L p).1.1 = p.1.1 := by
  rw [← k2_origPt_φ S L p]; rfl

theorem k2_φ_dir_pos (p : S.D.Γ.Outside (k2_U S L)) (_hp : S.D.Γ.eval p.1 ∉ k2_U S L) :
    ∃ l : ℝ, 0 < l ∧ (k2_shadow S L).dir ((k2_shadow S L).strandOf (k2_φ S L p).1) =
      l • S.D.Γ.dir (S.D.Γ.strandOf p.1) := by
  have hφ := k2_origPt_φ S L p
  have hout := (k2_φ S L p).2
  have hnm := k2_not_mid_of_not_mem_interior S L _ hout
  obtain ⟨l, hl, hdir⟩ := k2_dir_eq_smul_orig S L hnm
  refine ⟨l, hl, ?_⟩
  rw [← hφ]
  exact hdir

/-- the predecessor strand of a non-middle strand other than `e5` lies over the predecessor of the
original (positively), or is `e5` over `s₀` -/
theorem k2_dir_pred {u : (k2_shadow S L).Strand} (hu : ¬ k2_IsMid S L u) (hu4 : k2_lab S L u ≠ k2_av S L + 4) :
    ∃ l : ℝ, 0 < l ∧ (k2_shadow S L).dir ⟨u.1, u.2 - 1⟩ =
      l • S.D.Γ.dir ⟨(k2_orig S L u).1, (k2_orig S L u).2 - 1⟩ := by
  have hk := k2_three_le S L
  have hav := k2_av_lt S L
  have hlab := k2_lab_lt S L u
  have ht2 := k2_one_sub_t_sub_ε_pos S L
  have hd : k2_d S L = edge (k2_P S L) (k2_a S L) := rfl
  have hcast : ((k2_av S L : ℕ) : ZMod (k2_k S L)) = k2_a S L := ZMod.natCast_zmod_val _
  obtain ⟨i, m⟩ := u
  obtain rfl := k2_fin_eq S L i
  have hlm : k2_lab S L ⟨L.r.1, m⟩ = m.val := rfl
  have hn : ((k2_shadow S L).comp L.r.1).k = k2_k S L + 4 := rfl
  rw [k2_orig_eq]
  show ∃ l : ℝ, 0 < l ∧ edge (k2_tuple S L) (m - 1) = l • edge (k2_P S L) (_ - 1)
  rw [k2_edge_eq]
  have hpred : (m - 1).val = if m.val = 0 then k2_k S L + 3 else m.val - 1 := by
    split_ifs with h
    · rw [Smoothing.zval_sub_one_of_zero _ h]; omega
    · exact Smoothing.zval_sub_one_of_pos _ (by omega)
  rw [hpred]
  rw [k2_not_isMid_iff] at hu
  simp only [hlm] at hu hu4 ⊢
  rcases hu with hu | hu | hu
  · rcases hu with hu | hu
    · -- old strand before the kink
      rw [ite_eq_left hu.le]
      by_cases h0 : m.val = 0
      · rw [ite_eq_left h0, h0, Nat.cast_zero, k2_zero_sub_one]
        by_cases ha : k2_av S L = k2_k S L - 1
        · rw [show k2_k S L + 3 = k2_av S L + 4 by omega, k2_E_a4, hd, ← hcast, ha]
          exact ⟨_, ht2, rfl⟩
        · rw [k2_E_of_ge S L (by omega), show k2_k S L + 3 - 4 = k2_k S L - 1 by omega]
          exact ⟨1, one_pos, (one_smul _ _).symm⟩
      · rw [ite_eq_right h0, k2_E_of_lt S L (by omega), Smoothing.zcast_pred (v := m.val) (by omega)]
        exact ⟨1, one_pos, (one_smul _ _).symm⟩
    · -- old strand after the kink
      rw [ite_eq_right (by omega), ite_eq_right (by omega)]
      rcases Nat.eq_or_lt_of_le hu with h5 | h5
      · have h5' : m.val = k2_av S L + 5 := by rw [← hlm]; omega
        rw [h5', show k2_av S L + 5 - 1 = k2_av S L + 4 by omega, k2_E_a4,
          show k2_av S L + 5 - 4 = k2_av S L + 1 by omega, Nat.cast_succ, hcast, add_sub_cancel_right, hd]
        exact ⟨_, ht2, rfl⟩
      · rw [k2_E_of_ge S L (by omega), show m.val - 1 - 4 = m.val - 4 - 1 by omega,
          Smoothing.zcast_pred (v := m.val - 4) (by omega)]
        exact ⟨1, one_pos, (one_smul _ _).symm⟩
  · -- `e1`
    rw [ite_eq_left hu.le, hu, hcast]
    by_cases h0 : k2_av S L = 0
    · rw [ite_eq_left h0, k2_E_of_ge S L (by omega), show k2_k S L + 3 - 4 = k2_k S L - 1 by omega,
        ← k2_zero_sub_one, ← hcast, h0, Nat.cast_zero]
      exact ⟨1, one_pos, (one_smul _ _).symm⟩
    · rw [ite_eq_right h0, k2_E_of_lt S L (by omega), Smoothing.zcast_pred (v := k2_av S L) (by omega),
        hcast]
      exact ⟨1, one_pos, (one_smul _ _).symm⟩
  · exact absurd hu hu4

set_option maxHeartbeats 1000000 in
/-- the arriving direction at a point of `D'` strictly outside the disc -/
theorem k2_dir_strandBefore_origPt (q : (k2_shadow S L).Pt)
    (hout : (k2_shadow S L).eval q ∉ interior (k2_U S L)) (hq : (k2_shadow S L).eval q ∉ k2_U S L) :
    ∃ l : ℝ, 0 < l ∧ (k2_shadow S L).dir ((k2_shadow S L).strandBefore q) =
      l • S.D.Γ.dir (S.D.Γ.strandBefore (k2_origPt S L q)) := by
  have hnm := k2_not_mid_of_not_mem_interior S L q hout
  have hparam := k2_origPt_param S L q hnm
  have h1 := k2_t_sub_ε_pos S L
  have hε := k2_ε_pos S L
  have ht := k2_t_pos S L
  by_cases hθ : q.2.2.val = 0
  · have hne4 : k2_lab S L ⟨q.1, q.2.1⟩ ≠ k2_av S L + 4 := by
      intro h4
      apply hq
      rw [k2_eval_e5 S L q h4, hθ, zero_mul, add_zero, k2_edgePt_s₀_mem_U_iff]
      have := k2_θIn_lt S L
      have := k2_lt_θOut S L
      exact ⟨by linarith, by linarith⟩
    have hz : (k2_origPt S L q).2.2.val = 0 := by
      rw [hparam, hθ]
      rw [k2_not_isMid_iff] at hnm
      rcases hnm with hnm | hnm | hnm
      · rw [k2_lp_old S L hnm]
      · rw [k2_lp_e1 S L hnm, zero_mul]
      · exact absurd hnm hne4
    rw [(k2_shadow S L).strandBefore_of_zero _ hθ, S.D.Γ.strandBefore_of_zero _ hz]
    obtain ⟨l, hl, hd⟩ := k2_dir_pred S L hnm hne4
    refine ⟨l, hl, ?_⟩
    have e1 : (k2_origPt S L q).1 = (k2_orig S L ⟨q.1, q.2.1⟩).1 := rfl
    have e2 : (k2_origPt S L q).2.1 = (k2_orig S L ⟨q.1, q.2.1⟩).2 := rfl
    exact hd
  · have hz : (k2_origPt S L q).2.2.val ≠ 0 := by
      rw [hparam]
      have hθ0 := q.2.2.2.1
      have hθpos : 0 < q.2.2.val := lt_of_le_of_ne hθ0 (Ne.symm hθ)
      rw [k2_not_isMid_iff] at hnm
      rcases hnm with hnm | hnm | hnm
      · rw [k2_lp_old S L hnm]; exact hθ
      · rw [k2_lp_e1 S L hnm]; exact (mul_pos hθpos h1).ne'
      · rw [k2_lp_e5 S L hnm]
        exact (by nlinarith [k2_one_sub_t_sub_ε_pos S L] : (0:ℝ) <
          k2_t S L + k2_ε S L + q.2.2.val * (1 - k2_t S L - k2_ε S L)).ne'
    rw [(k2_shadow S L).strandBefore_of_ne_zero _ hθ, S.D.Γ.strandBefore_of_ne_zero _ hz]
    exact k2_dir_eq_smul_orig S L hnm

theorem k2_φ_dir_pos_before (p : S.D.Γ.Outside (k2_U S L)) (hp : S.D.Γ.eval p.1 ∉ k2_U S L) :
    ∃ l : ℝ, 0 < l ∧ (k2_shadow S L).dir ((k2_shadow S L).strandBefore (k2_φ S L p).1) =
      l • S.D.Γ.dir (S.D.Γ.strandBefore p.1) := by
  have hφ := k2_origPt_φ S L p
  have hout := (k2_φ S L p).2
  rw [← hφ] at hp ⊢
  rw [k2_eval_origPt S L _ hout] at hp
  exact k2_dir_strandBefore_origPt S L _ hout hp

/-! #### The correspondence of the outer crossings and of their occurrences -/

/-- every crossing of `D` is outer; the outer crossings of `D'` are those other than the kink -/
def k2_ψ : S.D.OuterCrossing (k2_U S L) ≃ (k2_D' S L).OuterCrossing (k2_U S L) :=
  ((Equiv.subtypeUnivEquiv (k2_no_inner S L)).trans (k2_old S L)).trans
    (Equiv.subtypeEquivRight (fun y => (not_congr (k2_inner_iff' S L y)).symm))

theorem k2_ψ_val (x : S.D.OuterCrossing (k2_U S L)) : (k2_ψ S L x).1 = k2_liftCrossing S L x.1 := rfl

/-- **the crossing parameters of a non-kink crossing of `D'` map to those of its original** -/
theorem k2_lp_crossingParam {y : (k2_shadow S L).Crossing} (hy : y ≠ k2_kink S L)
    {u : (k2_shadow S L).Strand} (hu : u ∈ y.val) :
    k2_lp S L u ((k2_D' S L).crossingParam y hu) =
      S.D.crossingParam (k2_origCrossing S L y hy) (k2_orig_mem_origCrossing S L hy hu) := by
  have hnm := k2_not_mid_of_ne_kink S L hy hu
  apply S.D.generic.edgePt_injective (k2_orig S L u)
  rw [← k2_edgePt_orig S L hnm]
  have h1 : (k2_shadow S L).crossingPoint y = (k2_shadow S L).edgePt u ((k2_D' S L).crossingParam y hu) :=
    ((k2_D' S L).crossingParam_spec y hu).2.2
  have h2 : S.D.Γ.crossingPoint (k2_origCrossing S L y hy) = S.D.Γ.edgePt (k2_orig S L u)
      (S.D.crossingParam (k2_origCrossing S L y hy) (k2_orig_mem_origCrossing S L hy hu)) :=
    (S.D.crossingParam_spec (k2_origCrossing S L y hy) (k2_orig_mem_origCrossing S L hy hu)).2.2
  rw [← h1, ← h2]
  exact k2_crossingPoint_orig S L y hy

theorem k2_crossingParam_lift (x : S.D.Γ.Crossing) {e : S.D.Γ.Strand} (he : e ∈ x.val) :
    (k2_D' S L).crossingParam (k2_liftCrossing S L x) (k2_liftStrand_mem S L x he) =
      k2_lpinv S L (k2_liftStrand S L x e he) (S.D.crossingParam x he) := by
  have h := k2_lp_crossingParam S L (k2_liftCrossing_ne_kink S L x) (k2_liftStrand_mem S L x he)
  rw [S.D.crossingParam_congr (k2_origCrossing_liftCrossing S L x) (k2_orig_liftStrand S L x he) _ he]
    at h
  rw [← h, k2_lpinv_lp]

theorem k2_φ_over_eq (x : S.D.OuterCrossing (k2_U S L)) :
    k2_φ S L (S.D.outerOverPt x) = (k2_D' S L).outerOverPt (k2_ψ S L x) := by
  have hy := k2_liftCrossing_ne_kink S L x.1
  have hmem := k2_over_mem S L (k2_liftCrossing S L x.1)
  have hs : k2_orig S L (k2_over S L (k2_liftCrossing S L x.1)) = S.D.overStrand x.1 := by
    rw [k2_orig_over S L hy, k2_origCrossing_liftCrossing]
  unfold k2_φ
  refine (Equiv.symm_apply_eq _).mpr ?_
  apply Subtype.ext
  show S.D.visitPt (S.D.overVisit x.1) = k2_origPt S L
    ((k2_D' S L).visitPt ((k2_D' S L).overVisit (k2_liftCrossing S L x.1)))
  refine (Shadow.mk_eq_mk_iff (S.D.overStrand x.1)
    (k2_orig S L (k2_over S L (k2_liftCrossing S L x.1))) _ _).mpr ⟨hs.symm, Subtype.ext ?_⟩
  show S.D.crossingParam x.1 (S.D.over_mem x.1) = (k2_origPt S L
    ((k2_D' S L).visitPt ((k2_D' S L).overVisit (k2_liftCrossing S L x.1)))).2.2.val
  rw [k2_origPt_param S L _ (k2_not_mid_of_ne_kink S L hy hmem)]
  show S.D.crossingParam x.1 (S.D.over_mem x.1) =
    k2_lp S L (k2_over S L (k2_liftCrossing S L x.1))
      ((k2_D' S L).crossingParam (k2_liftCrossing S L x.1) hmem)
  rw [k2_lp_crossingParam S L hy hmem]
  exact S.D.crossingParam_congr (k2_origCrossing_liftCrossing S L x.1).symm hs.symm _ _

theorem k2_φ_under_eq (x : S.D.OuterCrossing (k2_U S L)) :
    k2_φ S L (S.D.outerUnderPt x) = (k2_D' S L).outerUnderPt (k2_ψ S L x) := by
  have hy := k2_liftCrossing_ne_kink S L x.1
  have hmem := (k2_D' S L).under_mem (k2_liftCrossing S L x.1)
  have hs : k2_orig S L ((k2_D' S L).underStrand (k2_liftCrossing S L x.1)) = S.D.underStrand x.1 := by
    rw [k2_orig_underStrand S L hy, k2_origCrossing_liftCrossing]
  unfold k2_φ
  refine (Equiv.symm_apply_eq _).mpr ?_
  apply Subtype.ext
  show S.D.visitPt (S.D.underVisit x.1) = k2_origPt S L
    ((k2_D' S L).visitPt ((k2_D' S L).underVisit (k2_liftCrossing S L x.1)))
  refine (Shadow.mk_eq_mk_iff (S.D.underStrand x.1)
    (k2_orig S L ((k2_D' S L).underStrand (k2_liftCrossing S L x.1))) _ _).mpr ⟨hs.symm, Subtype.ext ?_⟩
  show S.D.crossingParam x.1 (S.D.under_mem x.1) = (k2_origPt S L
    ((k2_D' S L).visitPt ((k2_D' S L).underVisit (k2_liftCrossing S L x.1)))).2.2.val
  rw [k2_origPt_param S L _ (k2_not_mid_of_ne_kink S L hy hmem)]
  show S.D.crossingParam x.1 (S.D.under_mem x.1) =
    k2_lp S L ((k2_D' S L).underStrand (k2_liftCrossing S L x.1))
      ((k2_D' S L).crossingParam (k2_liftCrossing S L x.1) hmem)
  rw [k2_lp_crossingParam S L hy hmem]
  exact S.D.crossingParam_congr (k2_origCrossing_liftCrossing S L x.1).symm hs.symm _ _

/-- **the outside match and the move match** -/
def k2_outsideMatch : OutsideMatch (k2_U S L) S.D (k2_D' S L) where
  φ := k2_φ S L
  eval_eq := k2_φ_eval S L
  dir_pos := k2_φ_dir_pos S L
  dir_pos_before := k2_φ_dir_pos_before S L
  ψ := k2_ψ S L
  over_eq := k2_φ_over_eq S L
  under_eq := k2_φ_under_eq S L

def k2_moveMatch : MoveMatch (k2_U S L) S.D (k2_D' S L) where
  toOutsideMatch := k2_outsideMatch S L
  e := Equiv.refl _
  comp_eq := fun p => k2_φ_fst S L p

/-- **the Reidemeister-I site** -/
def k2_ri : RIData (k2_U S L) S.D (k2_D' S L) where
  frame := k2_localFrame S L
  out := k2_moveMatch S L
  a := k2_arc S L
  a' := k2_arc' S L
  cover := k2_arcCover_D S L
  cover' := k2_arcCover_D' S L
  start_eq := k2_start_eq S L
  stop_eq := k2_stop_eq S L
  no_inner := k2_no_inner S L
  kink := k2_kink S L
  inner_iff' := k2_inner_iff' S L

theorem k2_ri_kink : (k2_ri S L).kink = k2_kink S L := rfl

/-! #### The cyclic order of the occurrences: a strictly increasing coordinate map -/

theorem k2_e2_mem_kink : k2_eS S L 1 ∈ (k2_kink S L).val := by rw [k2_kink_val]; simp
theorem k2_e4_mem_kink : k2_eS S L 3 ∈ (k2_kink S L).val := by rw [k2_kink_val]; simp

/-- the crossing parameters of the kink: both branches pass through `K` at parameter `1/2` -/
theorem k2_crossingParam_kink_e2 :
    (k2_D' S L).crossingParam (k2_kink S L) (k2_e2_mem_kink S L) = 1 / 2 := by
  have hl : k2_lab S L (k2_eS S L 1) = k2_av S L + 1 := k2_lab_eS S L (by norm_num)
  apply (k2_generic S L).edgePt_injective (k2_eS S L 1)
  have h1 : (k2_shadow S L).crossingPoint (k2_kink S L) = (k2_shadow S L).edgePt (k2_eS S L 1)
      ((k2_D' S L).crossingParam (k2_kink S L) (k2_e2_mem_kink S L)) :=
    ((k2_D' S L).crossingParam_spec (k2_kink S L) _).2.2
  rw [← h1, k2_crossingPoint_kink, Shadow.edgePt_eq, k2_tail_e2 S L hl, k2_dir_e2 S L hl, k2_pt_e2,
    k2_K_frame]
  congr 1
  · rw [show k2_ε S L * (2 * (1 / 2) - 1) = (0:ℝ) by ring]
  · rw [show k2_ε S L * (1 / 2) = k2_ε S L / 2 by ring]

theorem k2_crossingParam_kink_e4 :
    (k2_D' S L).crossingParam (k2_kink S L) (k2_e4_mem_kink S L) = 1 / 2 := by
  have hl : k2_lab S L (k2_eS S L 3) = k2_av S L + 3 := k2_lab_eS S L (by norm_num)
  apply (k2_generic S L).edgePt_injective (k2_eS S L 3)
  have h1 : (k2_shadow S L).crossingPoint (k2_kink S L) = (k2_shadow S L).edgePt (k2_eS S L 3)
      ((k2_D' S L).crossingParam (k2_kink S L) (k2_e4_mem_kink S L)) :=
    ((k2_D' S L).crossingParam_spec (k2_kink S L) _).2.2
  rw [← h1, k2_crossingPoint_kink, Shadow.edgePt_eq, k2_tail_e4 S L hl, k2_dir_e4 S L hl, k2_pt_e4,
    k2_K_frame]
  congr 1
  · rw [show k2_ε S L * (2 * (1 / 2) - 1) = (0:ℝ) by ring]
  · rw [show k2_ε S L * (1 - 1 / 2) = k2_ε S L / 2 by ring]

/-- the coordinates of the two kink occurrences -/
theorem k2_visitCoord_under_kink :
    (k2_D' S L).visitCoord ((k2_D' S L).underVisit (k2_kink S L)) = k2_av S L + 1 + 1 / 2 := by
  rw [Diagram.visitCoord_eq]
  have hu := k2_D'_underStrand_kink S L
  have h1 : ((k2_D' S L).underVisit (k2_kink S L)).2.val.2.val = k2_av S L + 1 := by
    show ((k2_D' S L).underStrand (k2_kink S L)).2.val = _
    rw [hu]; exact k2_lab_eS S L (by norm_num)
  have h2 : (k2_D' S L).crossingParam ((k2_D' S L).underVisit (k2_kink S L)).1
      ((k2_D' S L).underVisit (k2_kink S L)).2.2 = 1 / 2 :=
    ((k2_D' S L).crossingParam_congr rfl hu _ (k2_e2_mem_kink S L)).trans (k2_crossingParam_kink_e2 S L)
  rw [h1, h2]; push_cast; ring

theorem k2_visitCoord_over_kink :
    (k2_D' S L).visitCoord ((k2_D' S L).overVisit (k2_kink S L)) = k2_av S L + 3 + 1 / 2 := by
  rw [Diagram.visitCoord_eq]
  have hu := k2_D'_overStrand_kink S L
  have h1 : ((k2_D' S L).overVisit (k2_kink S L)).2.val.2.val = k2_av S L + 3 := by
    show ((k2_D' S L).overStrand (k2_kink S L)).2.val = _
    rw [hu]; exact k2_lab_eS S L (by norm_num)
  have h2 : (k2_D' S L).crossingParam ((k2_D' S L).overVisit (k2_kink S L)).1
      ((k2_D' S L).overVisit (k2_kink S L)).2.2 = 1 / 2 :=
    ((k2_D' S L).crossingParam_congr rfl hu _ (k2_e4_mem_kink S L)).trans (k2_crossingParam_kink_e4 S L)
  rw [h1, h2]; push_cast; ring

/-- the coordinate of a lifted occurrence -/
theorem k2_visitCoord_lift (v : S.D.Γ.Visit) :
    (k2_D' S L).visitCoord (k2_liftVisit S L v) =
      (k2_lab S L (k2_liftStrand S L v.1 v.2.val v.2.2) : ℝ) +
        k2_lpinv S L (k2_liftStrand S L v.1 v.2.val v.2.2) (S.D.crossingParam v.1 v.2.2) := by
  rw [Diagram.visitCoord_eq]
  show (k2_lab S L (k2_liftStrand S L v.1 v.2.val v.2.2) : ℝ) +
    (k2_D' S L).crossingParam (k2_liftCrossing S L v.1) (k2_liftStrand_mem S L v.1 v.2.2) = _
  rw [k2_crossingParam_lift]

/-- the key of the location on the traversal circle of `D` -/
theorem k2_traversalKey_r : traversalKey L.r.2 = (k2_av S L : ℝ) + k2_t S L := rfl

/-- **the piecewise-linear coordinate map** from the circle of `D` to that of `D'` -/
def k2_f (c : ℝ) : ℝ :=
  if c < k2_av S L then c
  else if c < k2_av S L + k2_t S L then k2_av S L + (c - k2_av S L) / (k2_t S L - k2_ε S L)
  else if c < k2_av S L + 1 then
    k2_av S L + 4 + (c - k2_av S L - k2_t S L - k2_ε S L) / (1 - k2_t S L - k2_ε S L)
  else c + 4

/-- the four pieces of `k2_f` -/
theorem k2_f_pos_cases (x : ℝ) : x < k2_av S L ∨ ((k2_av S L : ℝ) ≤ x ∧ x < k2_av S L + k2_t S L) ∨
    ((k2_av S L : ℝ) + k2_t S L ≤ x ∧ x < k2_av S L + 1) ∨ (k2_av S L : ℝ) + 1 ≤ x := by
  rcases lt_or_ge x (k2_av S L) with h | h
  · exact Or.inl h
  rcases lt_or_ge x (k2_av S L + k2_t S L) with h' | h'
  · exact Or.inr (Or.inl ⟨h, h'⟩)
  rcases lt_or_ge x (k2_av S L + 1) with h'' | h''
  · exact Or.inr (Or.inr (Or.inl ⟨h', h''⟩))
  exact Or.inr (Or.inr (Or.inr h''))

theorem k2_f_1 {x : ℝ} (h : x < k2_av S L) : k2_f S L x = x := by
  unfold k2_f; rw [ite_eq_left h]
theorem k2_f_2 {x : ℝ} (h1 : (k2_av S L : ℝ) ≤ x) (h2 : x < k2_av S L + k2_t S L) :
    k2_f S L x = k2_av S L + (x - k2_av S L) / (k2_t S L - k2_ε S L) := by
  unfold k2_f; rw [ite_eq_right (not_lt.mpr h1), ite_eq_left h2]
theorem k2_f_3 {x : ℝ} (h1 : (k2_av S L : ℝ) + k2_t S L ≤ x) (h2 : x < k2_av S L + 1) :
    k2_f S L x = k2_av S L + 4 + (x - k2_av S L - k2_t S L - k2_ε S L) / (1 - k2_t S L - k2_ε S L) := by
  have ht := k2_t_pos S L
  unfold k2_f; rw [ite_eq_right (not_lt.mpr (by linarith)), ite_eq_right (not_lt.mpr h1), ite_eq_left h2]
theorem k2_f_4 {x : ℝ} (h : (k2_av S L : ℝ) + 1 ≤ x) : k2_f S L x = x + 4 := by
  have ht := k2_t_lt_one S L
  unfold k2_f
  rw [ite_eq_right (not_lt.mpr (by linarith)), ite_eq_right (not_lt.mpr (by linarith)),
    ite_eq_right (not_lt.mpr h)]

theorem k2_f_2_bounds {x : ℝ} (h1 : (k2_av S L : ℝ) ≤ x) (h2 : x < k2_av S L + k2_t S L) :
    (k2_av S L : ℝ) ≤ k2_f S L x ∧ k2_f S L x < k2_av S L + 2 := by
  have hp := k2_t_sub_ε_pos S L
  have hε1 : k2_ε S L ≤ k2_t S L - k2_ε S L := by linarith [k2_ε_le_t S L]
  rw [k2_f_2 S L h1 h2]
  constructor
  · have : 0 ≤ (x - k2_av S L) / (k2_t S L - k2_ε S L) := div_nonneg (by linarith) hp.le
    linarith
  · have : (x - k2_av S L) / (k2_t S L - k2_ε S L) < 2 := by rw [div_lt_iff₀ hp]; linarith
    linarith

theorem k2_f_3_bounds {x : ℝ} (h1 : (k2_av S L : ℝ) + k2_t S L ≤ x) (h2 : x < k2_av S L + 1) :
    (k2_av S L : ℝ) + 3 ≤ k2_f S L x ∧ k2_f S L x < k2_av S L + 5 := by
  have hp := k2_one_sub_t_sub_ε_pos S L
  have hε2 : k2_ε S L ≤ 1 - k2_t S L - k2_ε S L := by linarith [k2_ε_le_one_sub_t S L]
  rw [k2_f_3 S L h1 h2]
  constructor
  · have : -1 ≤ (x - k2_av S L - k2_t S L - k2_ε S L) / (1 - k2_t S L - k2_ε S L) := by
      rw [le_div_iff₀ hp]; linarith
    linarith
  · have : (x - k2_av S L - k2_t S L - k2_ε S L) / (1 - k2_t S L - k2_ε S L) < 1 := by
      rw [div_lt_one hp]; linarith
    linarith

theorem k2_f_strictMono : StrictMono (k2_f S L) := by
  intro c c' hcc'
  have hp1 := k2_t_sub_ε_pos S L
  have hp2 := k2_one_sub_t_sub_ε_pos S L
  have ht := k2_t_pos S L
  have ht1 := k2_t_lt_one S L
  rcases k2_f_pos_cases S L c with h | ⟨h1, h2⟩ | ⟨h1, h2⟩ | h <;>
    rcases k2_f_pos_cases S L c' with h' | ⟨h1', h2'⟩ | ⟨h1', h2'⟩ | h'
  · rw [k2_f_1 S L h, k2_f_1 S L h']; exact hcc'
  · rw [k2_f_1 S L h]; exact lt_of_lt_of_le h (k2_f_2_bounds S L h1' h2').1
  · rw [k2_f_1 S L h]; exact lt_of_lt_of_le (by linarith) (k2_f_3_bounds S L h1' h2').1
  · rw [k2_f_1 S L h, k2_f_4 S L h']; linarith
  · exfalso; linarith
  · rw [k2_f_2 S L h1 h2, k2_f_2 S L h1' h2']
    have := div_lt_div_of_pos_right (sub_lt_sub_right hcc' (k2_av S L : ℝ)) hp1
    linarith
  · exact lt_of_lt_of_le (k2_f_2_bounds S L h1 h2).2 (by linarith [(k2_f_3_bounds S L h1' h2').1])
  · exact lt_of_lt_of_le (k2_f_2_bounds S L h1 h2).2 (by rw [k2_f_4 S L h']; linarith)
  · exfalso; linarith
  · exfalso; linarith
  · rw [k2_f_3 S L h1 h2, k2_f_3 S L h1' h2']
    have := div_lt_div_of_pos_right (sub_lt_sub_right (sub_lt_sub_right
      (sub_lt_sub_right hcc' (k2_av S L : ℝ)) (k2_t S L)) (k2_ε S L)) hp2
    linarith
  · exact lt_of_lt_of_le (k2_f_3_bounds S L h1 h2).2 (by rw [k2_f_4 S L h']; linarith)
  · exfalso; linarith
  · exfalso; linarith
  · exfalso; linarith
  · rw [k2_f_4 S L h, k2_f_4 S L h']; linarith

/-- **the four positions of an old occurrence**: before the location's edge, on `s₀` before the
window, on `s₀` after the window, after the location's edge -/
theorem k2_coord_cases (v : S.D.Γ.Visit) :
    (S.D.visitCoord v < k2_av S L ∧
        (k2_D' S L).visitCoord (k2_liftVisit S L v) = S.D.visitCoord v) ∨
      (k2_av S L + 1 ≤ S.D.visitCoord v ∧
        (k2_D' S L).visitCoord (k2_liftVisit S L v) = S.D.visitCoord v + 4) ∨
      (k2_av S L < S.D.visitCoord v ∧ S.D.visitCoord v < k2_av S L + k2_θIn S L ∧
        (k2_D' S L).visitCoord (k2_liftVisit S L v) =
          k2_av S L + (S.D.visitCoord v - k2_av S L) / (k2_t S L - k2_ε S L)) ∨
      (k2_av S L + k2_θOut S L < S.D.visitCoord v ∧ S.D.visitCoord v < k2_av S L + 1 ∧
        (k2_D' S L).visitCoord (k2_liftVisit S L v) =
          k2_av S L + 4 + (S.D.visitCoord v - k2_av S L - k2_t S L - k2_ε S L) / (1 - k2_t S L - k2_ε S L)) := by
  rw [k2_visitCoord_lift, Diagram.visitCoord_eq]
  have hτ0 := S.D.crossingParam_pos v.1 v.2.2
  have hτ1 := S.D.crossingParam_lt_one v.1 v.2.2
  have hav := k2_av_lt S L
  by_cases he : v.2.val = k2_s₀ S L
  · have hfar := k2_crossingParam_far S L v he
    have hval : (v.2.val.2.val : ℝ) = k2_av S L := by rw [he]
    rw [k2_liftStrand_of_s₀ S L v.1 v.2.2 he]
    rcases hfar with h | h
    · have hlt : S.D.crossingParam v.1 v.2.2 < k2_t S L := h.trans (by linarith [k2_θIn_lt S L, k2_ε_pos S L])
      rw [ite_eq_left hlt]
      have hl : k2_lab S L (k2_eS S L 0) = k2_av S L := (k2_lab_eS S L (by norm_num)).trans (Nat.add_zero _)
      rw [k2_lpinv_e1 S L hl, hl, hval]
      refine Or.inr (Or.inr (Or.inl ⟨by linarith, by linarith, ?_⟩))
      ring_nf
    · have hlt : ¬ S.D.crossingParam v.1 v.2.2 < k2_t S L := by
        push Not; linarith [k2_lt_θOut S L, k2_ε_pos S L]
      rw [ite_eq_right hlt]
      have hl : k2_lab S L (k2_eS S L 4) = k2_av S L + 4 := k2_lab_eS S L (by norm_num)
      rw [k2_lpinv_e5 S L hl, hl, hval]
      refine Or.inr (Or.inr (Or.inr ⟨by linarith, by linarith, ?_⟩))
      push_cast; ring_nf
  · have hold := k2_liftStrand_isOld S L v.1 v.2.2 he
    rw [k2_lpinv_old S L hold, k2_lab_liftStrand_of_ne S L v.1 v.2.2 he]
    have hne := k2_val_ne_av_of_ne S L he
    have hlt := ZMod.val_lt v.2.val.2
    have hkk : (S.D.Γ.comp v.2.val.1).k = k2_k S L := by
      obtain ⟨b, hb⟩ := k2_strand_eq S L v.2.val
      rw [hb]
    unfold k2_ν
    split_ifs with h
    · left
      refine ⟨?_, rfl⟩
      have : (v.2.val.2.val : ℝ) + 1 ≤ k2_av S L := by exact_mod_cast h
      linarith
    · right; left
      refine ⟨?_, by push_cast; ring⟩
      have : (k2_av S L : ℝ) + 1 ≤ v.2.val.2.val := by
        have : k2_av S L + 1 ≤ v.2.val.2.val := by omega
        exact_mod_cast this
      linarith

/-- the coordinate of a lifted occurrence is `k2_f` of the old coordinate -/
theorem k2_visitCoord_lift_eq_f (v : S.D.Γ.Visit) :
    (k2_D' S L).visitCoord (k2_liftVisit S L v) = k2_f S L (S.D.visitCoord v) := by
  have hθIn := k2_θIn_lt S L
  have hθOut := k2_lt_θOut S L
  have hε := k2_ε_pos S L
  have ht := k2_t_pos S L
  have ht1 := k2_t_lt_one S L
  unfold k2_f
  rcases k2_coord_cases S L v with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h1', h2⟩ | ⟨h1, h1', h2⟩
  · rw [ite_eq_left h1, h2]
  · rw [ite_eq_right (by linarith), ite_eq_right (by linarith), ite_eq_right (by linarith), h2]
  · rw [ite_eq_right (by linarith), ite_eq_left (by linarith), h2]
  · rw [ite_eq_right (by linarith), ite_eq_right (by linarith), ite_eq_left h1', h2]

/-- **every old occurrence lies on one side of the location, and its lifted coordinate on the same
side of the kink gap `(a+1, a+4)`** -/
theorem k2_side (v : S.D.Γ.Visit) :
    (S.D.visitCoord v < traversalKey L.r.2 ∧ k2_f S L (S.D.visitCoord v) < k2_av S L + 1) ∨
      (traversalKey L.r.2 < S.D.visitCoord v ∧ k2_av S L + 4 ≤ k2_f S L (S.D.visitCoord v)) := by
  rw [k2_traversalKey_r, ← k2_visitCoord_lift_eq_f]
  have hθIn := k2_θIn_lt S L
  have hθOut := k2_lt_θOut S L
  have hε := k2_ε_pos S L
  have ht := k2_t_pos S L
  have ht1 := k2_t_lt_one S L
  have h1 := k2_t_sub_ε_pos S L
  have h2 := k2_one_sub_t_sub_ε_pos S L
  rcases k2_coord_cases S L v with ⟨hc, h⟩ | ⟨hc, h⟩ | ⟨hc, hc', h⟩ | ⟨hc, hc', h⟩
  · left; rw [h]; exact ⟨by linarith, by linarith⟩
  · right; rw [h]; exact ⟨by linarith, by linarith⟩
  · left
    rw [h]
    refine ⟨by linarith, ?_⟩
    have : (S.D.visitCoord v - k2_av S L) / (k2_t S L - k2_ε S L) < 1 := by
      rw [div_lt_one h1]; linarith
    linarith
  · right
    rw [h]
    refine ⟨by linarith, ?_⟩
    have : 0 ≤ (S.D.visitCoord v - k2_av S L - k2_t S L - k2_ε S L) / (1 - k2_t S L - k2_ε S L) :=
      div_nonneg (by linarith) h2.le
    linarith

/-- cyclic betweenness only depends on the three pairwise comparisons -/
theorem k2_cycBetween_congr {a b c a' b' c' : ℝ} (h1 : a < b ↔ a' < b') (h2 : b < c ↔ b' < c')
    (h3 : c < a ↔ c' < a') : cycBetween a b c ↔ cycBetween a' b' c' := by
  unfold cycBetween; rw [h1, h2, h3]

theorem k2_cycBetween_map {f : ℝ → ℝ} (hf : StrictMono f) (a b c : ℝ) :
    cycBetween (f a) (f b) (f c) ↔ cycBetween a b c :=
  k2_cycBetween_congr hf.lt_iff_lt hf.lt_iff_lt hf.lt_iff_lt

/-- **the cyclic order of the old occurrences is preserved** -/
theorem k2_order_old (v w z : S.D.Γ.Visit) :
    cycBetween ((k2_D' S L).visitCoord (k2_liftVisit S L v)) ((k2_D' S L).visitCoord (k2_liftVisit S L w))
        ((k2_D' S L).visitCoord (k2_liftVisit S L z)) ↔
      cycBetween (S.D.visitCoord v) (S.D.visitCoord w) (S.D.visitCoord z) := by
  rw [k2_visitCoord_lift_eq_f, k2_visitCoord_lift_eq_f, k2_visitCoord_lift_eq_f]
  exact k2_cycBetween_map (k2_f_strictMono S L) _ _ _

/-- a kink occurrence has coordinate in the gap `(a+1, a+4)` -/
theorem k2_kink_coord_mem (k : (k2_D' S L).Γ.Visit) (hk : k.1 = k2_kink S L) :
    k2_av S L + 1 < (k2_D' S L).visitCoord k ∧ (k2_D' S L).visitCoord k < k2_av S L + 4 := by
  rcases (k2_D' S L).visit_eq_over_or_under k with h | h
  · rw [h, hk, k2_visitCoord_over_kink]; constructor <;> linarith
  · rw [h, hk, k2_visitCoord_under_kink]; constructor <;> linarith

/-- **the kink occurrences sit in the gap of the location** -/
theorem k2_order_gap (v w : S.D.Γ.Visit) (k : (k2_D' S L).Γ.Visit) (hk : k.1 = k2_kink S L) :
    cycBetween ((k2_D' S L).visitCoord (k2_liftVisit S L v)) ((k2_D' S L).visitCoord k)
        ((k2_D' S L).visitCoord (k2_liftVisit S L w)) ↔
      cycBetween (S.D.visitCoord v) (traversalKey L.r.2) (S.D.visitCoord w) := by
  obtain ⟨hk1, hk2⟩ := k2_kink_coord_mem S L k hk
  rw [k2_visitCoord_lift_eq_f, k2_visitCoord_lift_eq_f]
  have hv := k2_side S L v
  have hw := k2_side S L w
  refine k2_cycBetween_congr ?_ ?_ ((k2_f_strictMono S L).lt_iff_lt)
  · rcases hv with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨fun _ => h1, fun _ => by linarith⟩
    · exact ⟨fun h => absurd h (by linarith), fun h => absurd h (by linarith)⟩
  · rcases hw with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨fun h => absurd h (by linarith), fun h => absurd h (by linarith)⟩
    · exact ⟨fun _ => h1, fun _ => by linarith⟩

/-- **the under occurrence of the kink is met first** -/
theorem k2_order_pair (v : S.D.Γ.Visit) :
    cycBetween ((k2_D' S L).visitCoord (k2_liftVisit S L v))
      ((k2_D' S L).visitCoord ((k2_D' S L).underVisit (k2_kink S L)))
      ((k2_D' S L).visitCoord ((k2_D' S L).overVisit (k2_kink S L))) := by
  rw [k2_visitCoord_lift_eq_f, k2_visitCoord_under_kink, k2_visitCoord_over_kink]
  rcases k2_side S L v with ⟨-, h⟩ | ⟨-, h⟩
  · exact Or.inl ⟨by linarith, by linarith⟩
  · exact Or.inr (Or.inl ⟨by linarith, by linarith⟩)

end K2


/-- the kink insertion: a small clockwise monogon (three new vertices) at `r`, later branch over;
generic shadow, `RIData` in a small disc `U` about `r`, crossing/occurrence correspondence,
cyclic-order clauses, writhe (a splice construction as in SM/Smoothing.lean, one strand cut) -/
theorem exists_kinkInsertion (L : KinkLocation S) : Nonempty (KinkInsertion S L) := by
  exact ⟨{ D' := k2_D' S L
           U := k2_U S L
           ri := k2_ri S L
           kink_neg := k2_kink_neg S L
           c_eq := rfl
           old := k2_old S L
           oldVisit := k2_oldVisit S L
           oldVisit_over := k2_oldVisit_over S L
           oldVisit_under := k2_oldVisit_under S L
           oldVisit_twin := k2_oldVisit_twin S L
           old_point := k2_old_point S L
           old_sign := k2_old_sign S L
           order_old := k2_order_old S L
           order_gap := k2_order_gap S L
           order_pair := k2_order_pair S L
           writhe := k2_writhe S L }⟩

/-- the outer crossings of a Reidemeister-I site keep their double points (accepted `OutsideMatch`:
`eval_eq` at the over occurrence, `over_eq`) — reusable helper for `KinkInsertion.old_point` -/
theorem _root_.SM.Link.RIData.crossingPoint_ψ {U : Set Plane} {D D' : Diagram} (h : RIData U D D')
    (x : D.OuterCrossing U) : D'.Γ.crossingPoint (h.out.ψ x).1 = D.Γ.crossingPoint x.1 := by
  have h2 := h.out.eval_eq (D.outerOverPt x)
  rw [h.out.over_eq, Diagram.outerOverPt_val, Diagram.outerOverPt_val, D'.eval_visitPt,
    D.eval_visitPt] at h2
  exact h2

/-- the outer crossings of a Reidemeister-I site keep their signs (`dir_pos` at both occurrences; the
crossing point is strictly outside `U`, a frontier point being traversed once by `Clean`) — reusable
helper for `KinkInsertion.old_sign` -/
theorem _root_.SM.Link.RIData.sign_ψ {U : Set Plane} {D D' : Diagram} (h : RIData U D D')
    (x : D.OuterCrossing U) : D'.sign (h.out.ψ x).1 = D.sign x.1 := by
  have hnot : D.Γ.crossingPoint x.1 ∉ U := fun hU =>
    h.frame.clean.crossingPoint_not_mem_frontier x.1 ⟨subset_closure hU, x.2⟩
  obtain ⟨l, hl, hdir⟩ := h.out.dir_pos (D.outerOverPt x)
    (by rw [Diagram.outerOverPt_val, D.eval_visitPt]; exact hnot)
  obtain ⟨m, hm, hdir'⟩ := h.out.dir_pos (D.outerUnderPt x)
    (by rw [Diagram.outerUnderPt_val, D.eval_visitPt]; exact hnot)
  rw [h.out.over_eq] at hdir
  rw [h.out.under_eq] at hdir'
  have e1 : D'.Γ.strandOf (D'.outerOverPt (h.out.ψ x)).1 = D'.overStrand (h.out.ψ x).1 := rfl
  have e2 : D.Γ.strandOf (D.outerOverPt x).1 = D.overStrand x.1 := rfl
  have e3 : D'.Γ.strandOf (D'.outerUnderPt (h.out.ψ x)).1 = D'.underStrand (h.out.ψ x).1 := rfl
  have e4 : D.Γ.strandOf (D.outerUnderPt x).1 = D.underStrand x.1 := rfl
  rw [e1, e2] at hdir
  rw [e3, e4] at hdir'
  unfold Diagram.sign
  rw [hdir, hdir']
  have hdet : det (l • D.Γ.dir (D.overStrand x.1)) (m • D.Γ.dir (D.underStrand x.1)) =
      (l * m) * det (D.Γ.dir (D.overStrand x.1)) (D.Γ.dir (D.underStrand x.1)) := by
    simp only [det, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring
  rw [hdet, sign_mul, sign_pos (mul_pos hl hm), one_mul]

/-- the crossings of `D` correspond to the crossings of `D'` other than the kink: every crossing
of `D` is outer (`no_inner`), the outer crossings match (`ψ`), and the outer crossings of `D'` are
exactly the non-kink ones (`inner_iff'`) — the shape of `KinkInsertion.old` -/
def k1_old_equiv {U : Set Plane} {D D' : Diagram} (h : RIData U D D') :
    D.Γ.Crossing ≃ {y : D'.Γ.Crossing // y ≠ h.kink} :=
  ((Equiv.subtypeUnivEquiv h.no_inner).symm.trans h.out.ψ).trans
    (Equiv.subtypeEquivRight fun y => not_congr (h.inner_iff' y))

theorem k1_old_equiv_val {U : Set Plane} {D D' : Diagram} (h : RIData U D D')
    (x : D.Γ.Crossing) : (k1_old_equiv h x).1 = (h.out.ψ ⟨x, h.no_inner x⟩).1 := rfl

theorem k1_old_equiv_point {U : Set Plane} {D D' : Diagram} (h : RIData U D D')
    (x : D.Γ.Crossing) : D'.Γ.crossingPoint (k1_old_equiv h x).1 = D.Γ.crossingPoint x := by
  rw [k1_old_equiv_val]
  exact h.crossingPoint_ψ ⟨x, h.no_inner x⟩

theorem k1_old_equiv_sign {U : Set Plane} {D D' : Diagram} (h : RIData U D D')
    (x : D.Γ.Crossing) : D'.sign (k1_old_equiv h x).1 = D.sign x := by
  rw [k1_old_equiv_val]
  exact h.sign_ψ ⟨x, h.no_inner x⟩

/-- the writhe of a Reidemeister-I site: the outer crossings correspond with the same signs
(`sign_ψ`), `D` has no inner crossing (`no_inner`) and the kink is the only inner one of `D'`
(`inner_iff'`) — reusable helper for `KinkInsertion.writhe` -/
theorem _root_.SM.Link.RIData.writhe_eq {U : Set Plane} {D D' : Diagram} (h : RIData U D D') :
    D'.writhe = D.writhe + (D'.sign h.kink : ℤ) := by
  classical
  unfold Diagram.writhe
  rw [← Fintype.sum_subtype_add_sum_subtype (fun y : D'.Γ.Crossing => y ≠ h.kink)
    (fun y => (D'.sign y : ℤ))]
  congr 1
  · exact (Fintype.sum_equiv (k1_old_equiv h) (fun x => (D.sign x : ℤ))
      (fun y => (D'.sign y.1 : ℤ)) fun x => by rw [k1_old_equiv_sign]).symm
  · rw [Fintype.sum_eq_single
      (f := fun y : {y : D'.Γ.Crossing // ¬ y ≠ h.kink} => (D'.sign y.1 : ℤ))
      ⟨h.kink, fun h' => h' rfl⟩ fun y hy => absurd (Subtype.ext (not_not.mp y.2)) hy]

/-! ### Unit C — the record of `D'` carried by `F'` (combinatorics of the cyclic order) -/

/-- cyclic betweenness is invariant under rotation of the triple -/
theorem ca_cycBetween_rot {a b c : ℝ} : cycBetween a b c ↔ cycBetween b c a := by
  unfold cycBetween; tauto

/-- for three distinct reals exactly one of the two cyclic orders holds -/
theorem ca_cycBetween_swap {a b c : ℝ} (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    cycBetween a c b ↔ ¬ cycBetween a b c := by
  unfold cycBetween
  rcases lt_or_gt_of_ne hab with h1 | h1 <;> rcases lt_or_gt_of_ne hbc with h2 | h2 <;>
    rcases lt_or_gt_of_ne hac with h3 | h3 <;>
    simp [h1, h2, h3, lt_asymm h1, lt_asymm h2, lt_asymm h3]

/-- an element other than the two inserted ones is *old* -/
theorem ca_old_or_inserted {X : Type*} (k₁ k₂ a : X) : (a ≠ k₁ ∧ a ≠ k₂) ∨ (a = k₁ ∨ a = k₂) := by
  by_cases h1 : a = k₁
  · exact Or.inr (Or.inl h1)
  by_cases h2 : a = k₂
  · exact Or.inr (Or.inr h2)
  exact Or.inl ⟨h1, h2⟩

/-- Two injective coordinates on a finite set induce the same cyclic order as soon as they agree on
the old elements, place the two inserted elements in the same gap, and order the inserted pair the
same way (all other triples are rotations/reversals of these or contain a repetition). -/
theorem cycBetween_ext_of_insert_pair {X : Type*} (κ₁ κ₂ : X → ℝ) (h₁ : Function.Injective κ₁)
    (h₂ : Function.Injective κ₂) (k₁ k₂ : X) (hk : k₁ ≠ k₂)
    (hold : ∀ a b c : X, a ≠ k₁ → a ≠ k₂ → b ≠ k₁ → b ≠ k₂ → c ≠ k₁ → c ≠ k₂ →
      (cycBetween (κ₁ a) (κ₁ b) (κ₁ c) ↔ cycBetween (κ₂ a) (κ₂ b) (κ₂ c)))
    (hgap : ∀ a c k : X, (k = k₁ ∨ k = k₂) → a ≠ k₁ → a ≠ k₂ → c ≠ k₁ → c ≠ k₂ →
      (cycBetween (κ₁ a) (κ₁ k) (κ₁ c) ↔ cycBetween (κ₂ a) (κ₂ k) (κ₂ c)))
    (hpair : ∀ a : X, a ≠ k₁ → a ≠ k₂ →
      cycBetween (κ₁ a) (κ₁ k₁) (κ₁ k₂) ∧ cycBetween (κ₂ a) (κ₂ k₁) (κ₂ k₂)) :
    ∀ a b c : X, cycBetween (κ₁ a) (κ₁ b) (κ₁ c) ↔ cycBetween (κ₂ a) (κ₂ b) (κ₂ c) := by
  -- the core: a distinct triple whose first entry is old
  have core : ∀ a b c : X, a ≠ k₁ → a ≠ k₂ → a ≠ b → b ≠ c → a ≠ c →
      (cycBetween (κ₁ a) (κ₁ b) (κ₁ c) ↔ cycBetween (κ₂ a) (κ₂ b) (κ₂ c)) := by
    intro a b c ha₁ ha₂ hab hbc hac
    rcases ca_old_or_inserted k₁ k₂ b with ⟨hb₁, hb₂⟩ | hbk
    · rcases ca_old_or_inserted k₁ k₂ c with ⟨hc₁, hc₂⟩ | hck
      · exact hold a b c ha₁ ha₂ hb₁ hb₂ hc₁ hc₂
      · -- `c` inserted: rotate to `(b, c, a)`
        exact ca_cycBetween_rot.trans ((hgap b a c hck hb₁ hb₂ ha₁ ha₂).trans ca_cycBetween_rot.symm)
    · rcases ca_old_or_inserted k₁ k₂ c with ⟨hc₁, hc₂⟩ | hck
      · exact hgap a c b hbk ha₁ ha₂ hc₁ hc₂
      · -- both `b`, `c` inserted and distinct: the pair in one of its two orders
        have hp := hpair a ha₁ ha₂
        rcases hbk with rfl | rfl <;> rcases hck with rfl | rfl
        · exact absurd rfl hbc
        · exact iff_of_true hp.1 hp.2
        · rw [ca_cycBetween_swap (h₁.ne hac) (h₁.ne hk) (h₁.ne hab),
            ca_cycBetween_swap (h₂.ne hac) (h₂.ne hk) (h₂.ne hab)]
          exact iff_of_false (not_not.mpr hp.1) (not_not.mpr hp.2)
        · exact absurd rfl hbc
  intro a b c
  -- triples with a repetition: both sides false
  by_cases hab : a = b
  · subst hab; exact iff_of_false (not_cycBetween_self_left _ _) (not_cycBetween_self_left _ _)
  by_cases hbc : b = c
  · subst hbc; exact iff_of_false (not_cycBetween_self_mid _ _) (not_cycBetween_self_mid _ _)
  by_cases hac : a = c
  · subst hac; exact iff_of_false (not_cycBetween_self_right _ _) (not_cycBetween_self_right _ _)
  -- a distinct triple has an old entry; rotate it to the front
  rcases ca_old_or_inserted k₁ k₂ a with ⟨ha₁, ha₂⟩ | hak
  · exact core a b c ha₁ ha₂ hab hbc hac
  rcases ca_old_or_inserted k₁ k₂ b with ⟨hb₁, hb₂⟩ | hbk
  · exact ca_cycBetween_rot.trans
      ((core b c a hb₁ hb₂ hbc (Ne.symm hac) (Ne.symm hab)).trans ca_cycBetween_rot.symm)
  rcases ca_old_or_inserted k₁ k₂ c with ⟨hc₁, hc₂⟩ | hck
  · exact ca_cycBetween_rot.symm.trans
      ((core c a b hc₁ hc₂ (Ne.symm hac) hab (Ne.symm hbc)).trans ca_cycBetween_rot)
  -- three distinct entries among two inserted ones: impossible
  exfalso
  rcases hak with rfl | rfl <;> rcases hbk with h | h <;> rcases hck with h' | h' <;>
    first | exact hab h.symm | exact hbc (h.trans h'.symm) | exact hac h'.symm

/-- the middle entry may move without crossing the two ends (both ends on one side of both
positions) -/
theorem ca_cycBetween_congr_mid {a b b' c : ℝ} (ha : (a < b ∧ a < b') ∨ (b < a ∧ b' < a))
    (hc : (c < b ∧ c < b') ∨ (b < c ∧ b' < c)) : cycBetween a b c ↔ cycBetween a b' c := by
  unfold cycBetween
  rcases ha with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hc with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;>
    constructor <;> rintro (⟨h5, h6⟩ | ⟨h5, h6⟩ | ⟨h5, h6⟩) <;>
    first
    | exact Or.inl ⟨by linarith, by linarith⟩
    | exact Or.inr (Or.inl ⟨by linarith, by linarith⟩)
    | exact Or.inr (Or.inr ⟨by linarith, by linarith⟩)

/-- `Int.fract` on a half-open unit interval is a rotation: it preserves cyclic betweenness -/
theorem ca_cycBetween_fract {C a b c : ℝ} (ha : a ∈ Ico C (C + 1)) (hb : b ∈ Ico C (C + 1))
    (hc : c ∈ Ico C (C + 1)) :
    cycBetween (Int.fract a) (Int.fract b) (Int.fract c) ↔ cycBetween a b c := by
  have key : ∀ x ∈ Ico C (C + 1),
      (Int.fract x = x - ⌊C⌋ ∧ x < ⌊C⌋ + 1) ∨ (Int.fract x = x - ⌊C⌋ - 1 ∧ (⌊C⌋ : ℝ) + 1 ≤ x) := by
    intro x hx
    have h1 : ⌊C⌋ ≤ ⌊x⌋ := Int.floor_le_floor hx.1
    have h2 : ⌊x⌋ ≤ ⌊C⌋ + 1 := by rw [← Int.floor_add_one]; exact Int.floor_le_floor hx.2.le
    have hx1 := Int.floor_le x
    have hx2 := Int.lt_floor_add_one x
    rcases (show ⌊x⌋ = ⌊C⌋ ∨ ⌊x⌋ = ⌊C⌋ + 1 by omega) with h3 | h3
    · left
      refine ⟨?_, ?_⟩
      · rw [← Int.self_sub_floor, h3]
      · rw [h3] at hx2; exact hx2
    · right
      refine ⟨?_, ?_⟩
      · rw [← Int.self_sub_floor, h3]; push_cast; ring
      · rw [h3] at hx1; push_cast at hx1; exact hx1
  have ka := key a ha
  have kb := key b hb
  have kc := key c hc
  obtain ⟨haC, haC1⟩ := ha
  obtain ⟨hbC, hbC1⟩ := hb
  obtain ⟨hcC, hcC1⟩ := hc
  rcases ka with ⟨ha1, ha2⟩ | ⟨ha1, ha2⟩ <;> rcases kb with ⟨hb1, hb2⟩ | ⟨hb1, hb2⟩ <;>
    rcases kc with ⟨hc1, hc2⟩ | ⟨hc1, hc2⟩ <;> rw [ha1, hb1, hc1] <;> unfold cycBetween <;>
    constructor <;> rintro (⟨h5, h6⟩ | ⟨h5, h6⟩ | ⟨h5, h6⟩) <;>
    first
    | exact Or.inl ⟨by linarith, by linarith⟩
    | exact Or.inr (Or.inl ⟨by linarith, by linarith⟩)
    | exact Or.inr (Or.inr ⟨by linarith, by linarith⟩)

/-- a parameter of the fundamental period off the closed window has a representative in the gap
`(s₂ − 1, s₁)` between the window and its next translate -/
theorem ca_exists_rep {s₁ s₂ τ : ℝ} (h12 : s₁ < s₂) (hτ : τ ∈ Ico (0 : ℝ) 1)
    (h : OffClosedWindow s₁ s₂ τ) : ∃ σ ∈ Ioo (s₂ - 1) s₁, Int.fract σ = τ := by
  set σ := s₂ - 1 + Int.fract (τ - (s₂ - 1)) with hσ
  have hσ0 : s₂ - 1 ≤ σ := by have := Int.fract_nonneg (τ - (s₂ - 1)); linarith
  have hσ1 : σ < s₂ := by have := Int.fract_lt_one (τ - (s₂ - 1)); linarith
  have hm : σ = τ - (⌊τ - (s₂ - 1)⌋ : ℝ) := by
    rw [hσ, ← Int.self_sub_floor]; ring
  have hfr : Int.fract σ = τ := by
    rw [Int.fract_eq_iff]
    exact ⟨hτ.1, hτ.2, -⌊τ - (s₂ - 1)⌋, by rw [hm]; push_cast; ring⟩
  refine ⟨σ, ⟨?_, ?_⟩, hfr⟩
  · rcases hσ0.lt_or_eq with h0 | h0
    · exact h0
    · exfalso
      apply h (-⌊τ - (s₂ - 1)⌋ + 1)
      have : τ + ((-⌊τ - (s₂ - 1)⌋ + 1 : ℤ) : ℝ) = s₂ := by push_cast; linarith
      rw [this]
      exact ⟨h12.le, le_rfl⟩
  · by_contra hcon
    push Not at hcon
    apply h (-⌊τ - (s₂ - 1)⌋)
    have : τ + ((-⌊τ - (s₂ - 1)⌋ : ℤ) : ℝ) = σ := by push_cast; linarith
    rw [this]
    exact ⟨hcon, hσ1.le⟩

/-- the window `(s₁, s₂)` lies in the unit interval `[s₂ − 1, s₂)` -/
theorem ca_mem_unit_of_window {s₁ s₂ u : ℝ} (hs : s₂ - s₁ < 1) (hu : u ∈ Ioo s₁ s₂) :
    u ∈ Ico (s₂ - 1) (s₂ - 1 + 1) :=
  ⟨by linarith [hu.1], by linarith [hu.2]⟩

/-- … and so does the gap `(s₂ − 1, s₁)` -/
theorem ca_mem_unit_of_gap {s₁ s₂ u : ℝ} (h12 : s₁ < s₂) (hu : u ∈ Ioo (s₂ - 1) s₁) :
    u ∈ Ico (s₂ - 1) (s₂ - 1 + 1) :=
  ⟨hu.1.le, by linarith [hu.2]⟩

/-- two parameters of a window (shorter than the period) that contains no occurrence parameter
(mod 1) occupy the same gap of the occurrences -/
theorem cycBetween_fract_gap {τ : ℝ} (hτ : τ ∈ Ico (0 : ℝ) 1) {τ' : ℝ} (hτ' : τ' ∈ Ico (0 : ℝ) 1)
    {s₁ s₂ x y : ℝ} (hs : s₂ - s₁ < 1) (hx : x ∈ Ioo s₁ s₂) (hy : y ∈ Ioo s₁ s₂)
    (h₁ : OffClosedWindow s₁ s₂ τ) (h₂ : OffClosedWindow s₁ s₂ τ') :
    cycBetween τ (Int.fract x) τ' ↔ cycBetween τ (Int.fract y) τ' := by
  have h12 : s₁ < s₂ := hx.1.trans hx.2
  obtain ⟨σ, hσ, rfl⟩ := ca_exists_rep h12 hτ h₁
  obtain ⟨σ', hσ', rfl⟩ := ca_exists_rep h12 hτ' h₂
  rw [ca_cycBetween_fract (ca_mem_unit_of_gap h12 hσ) (ca_mem_unit_of_window hs hx)
      (ca_mem_unit_of_gap h12 hσ'),
    ca_cycBetween_fract (ca_mem_unit_of_gap h12 hσ) (ca_mem_unit_of_window hs hy)
      (ca_mem_unit_of_gap h12 hσ')]
  exact ca_cycBetween_congr_mid (Or.inl ⟨by linarith [hσ.2, hx.1], by linarith [hσ.2, hy.1]⟩)
    (Or.inl ⟨by linarith [hσ'.2, hx.1], by linarith [hσ'.2, hy.1]⟩)

/-- two ordered parameters of such a window are met in that order after every occurrence -/
theorem cycBetween_fract_pair {τ : ℝ} (hτ : τ ∈ Ico (0 : ℝ) 1) {s₁ s₂ x y : ℝ} (hs : s₂ - s₁ < 1)
    (hx : x ∈ Ioo s₁ s₂) (hy : y ∈ Ioo s₁ s₂) (hxy : x < y) (h₁ : OffClosedWindow s₁ s₂ τ) :
    cycBetween τ (Int.fract x) (Int.fract y) := by
  have h12 : s₁ < s₂ := hx.1.trans hx.2
  obtain ⟨σ, hσ, rfl⟩ := ca_exists_rep h12 hτ h₁
  rw [ca_cycBetween_fract (ca_mem_unit_of_gap h12 hσ) (ca_mem_unit_of_window hs hx)
      (ca_mem_unit_of_window hs hy)]
  exact Or.inl ⟨by linarith [hσ.2, hx.1], hxy⟩

/-- `Int.fract x` is an integer shift of `x` -/
theorem ca_fract_eq_add_int (x : ℝ) : Int.fract x = x + ((-⌊x⌋ : ℤ) : ℝ) := by
  rw [← Int.self_sub_floor]; push_cast; ring

/-- a 1-periodic loop takes the same value at `x` and `Int.fract x` -/
theorem ca_loop_fract (L : SmoothLoop) (x : ℝ) : L.γ (Int.fract x) = L.γ x := by
  rw [ca_fract_eq_add_int, L.eq_add_int]

/-- … and the same velocity -/
theorem ca_deriv_loop_fract (L : SmoothLoop) (x : ℝ) : deriv L.γ (Int.fract x) = deriv L.γ x := by
  rw [ca_fract_eq_add_int, L.deriv_eq_add_int]

/-- a parameter of the fundamental period is the fractional part of each of its integer shifts -/
theorem ca_fract_add_int_eq {t : ℝ} (ht : t ∈ Ico (0 : ℝ) 1) (n : ℤ) : Int.fract (t + n) = t := by
  rw [Int.fract_eq_iff]; exact ⟨ht.1, ht.2, n, by ring⟩

/-- two parameters of the fundamental period with equal integer shifts coincide -/
theorem ca_eq_of_add_int_eq {s t : ℝ} (hs : s ∈ Ico (0 : ℝ) 1) (ht : t ∈ Ico (0 : ℝ) 1) {n m : ℤ}
    (h : s + n = t + m) : s = t := by
  rw [← ca_fract_add_int_eq hs n, h, ca_fract_add_int_eq ht m]

/-- fractional parts of two parameters at distance in `(0, 1)` differ -/
theorem ca_fract_ne_of_lt {x y : ℝ} (hxy : x < y) (h1 : y - x < 1) :
    Int.fract x ≠ Int.fract y := by
  intro h
  obtain ⟨z, hz⟩ := Int.fract_eq_fract.mp h
  have hz0 : (z : ℝ) < 0 := by linarith
  have hz1 : (-1 : ℝ) < z := by linarith
  have h0 : z < 0 := by exact_mod_cast hz0
  have h1 : -1 < z := by exact_mod_cast hz1
  omega

/-- either some integer shift lies in the closed window, or the parameter is off it -/
theorem ca_window_or_off (s₁ s₂ t : ℝ) :
    (∃ n : ℤ, t + n ∈ Icc s₁ s₂) ∨ OffClosedWindow s₁ s₂ t := by
  by_cases h : ∃ n : ℤ, t + n ∈ Icc s₁ s₂
  · exact Or.inl h
  · exact Or.inr fun n hn => h ⟨n, hn⟩

/-- either some integer shift lies in the open window, or the parameter is off it -/
theorem ca_open_or_off (s₁ s₂ t : ℝ) :
    (∃ n : ℤ, t + n ∈ Ioo s₁ s₂) ∨ OffWindow s₁ s₂ t := by
  by_cases h : ∃ n : ℤ, t + n ∈ Ioo s₁ s₂
  · exact Or.inl h
  · exact Or.inr fun n hn => h ⟨n, hn⟩

theorem ca_offWindow_of_offClosed {s₁ s₂ t : ℝ} (h : OffClosedWindow s₁ s₂ t) :
    OffWindow s₁ s₂ t :=
  fun n hn => h n (Ioo_subset_Icc_self hn)

/-- off the open window is invariant under integer shifts -/
theorem ca_offWindow_add_int {s₁ s₂ t : ℝ} (n : ℤ) (h : OffWindow s₁ s₂ t) :
    OffWindow s₁ s₂ (t + n) := by
  intro m hm
  apply h (n + m)
  push_cast
  rw [← add_assoc]
  exact hm

/-- every parameter has an integer shift in `[s₂ − 1, s₂)` -/
theorem ca_exists_shift_Ico (s₂ t : ℝ) : ∃ n : ℤ, t + n ∈ Ico (s₂ - 1) s₂ := by
  refine ⟨-⌊t - (s₂ - 1)⌋, ?_⟩
  have h0 := Int.fract_nonneg (t - (s₂ - 1))
  have h1 := Int.fract_lt_one (t - (s₂ - 1))
  rw [← Int.self_sub_floor] at h0 h1
  push_cast
  constructor <;> linarith

/-- every parameter of `[s₂ − 1, s₁]` is off the open window `(s₁, s₂)` mod 1 (an integer strictly
between `0` and `1` would be needed) -/
theorem ca_offWindow_of_mem_Icc {s₁ s₂ t : ℝ} (ht : t ∈ Icc (s₂ - 1) s₁) : OffWindow s₁ s₂ t := by
  intro n hn
  have hn0 : (0 : ℝ) < n := by linarith [ht.2, hn.1]
  have hn1 : (n : ℝ) < 1 := by linarith [ht.1, hn.2]
  have h0 : 0 < n := by exact_mod_cast hn0
  have h1 : n < 1 := by exact_mod_cast hn1
  omega

/-- `det` is antisymmetric -/
theorem ca_det_swap (a b : Plane) : det a b = -det b a := by
  simp only [det]; ring

/-- the window is shorter than the period: `s₂ − 1 < s₁` -/
theorem ca_window_short {Δ : Set Plane} (sc : SmoothCurl S Δ) : sc.s₂ - 1 < sc.s₁ := by
  linarith [sc.α_le, sc.le_β, S.short]

/-- off the open window (mod 1) the velocity of `F'` is that of `F`: shift the parameter into
`[s₂ − 1, s₁]`, on which `F' = F`, and compare derivatives there (endpoints included) -/
theorem ca_deriv_eq_of_offWindow {Δ : Set Plane} (sc : SmoothCurl S Δ) {t : ℝ}
    (ht : OffWindow sc.s₁ sc.s₂ t) : deriv sc.F'.γ t = deriv S.F.γ t := by
  obtain ⟨n, hn⟩ := ca_exists_shift_Ico sc.s₂ t
  have hn' : OffWindow sc.s₁ sc.s₂ (t + n) := ca_offWindow_add_int n ht
  have hmem : t + n ∈ Icc (sc.s₂ - 1) sc.s₁ := by
    refine ⟨hn.1, ?_⟩
    by_contra hlt
    push Not at hlt
    exact hn' 0 (by simpa using And.intro hlt hn.2)
  rw [← sc.F'.deriv_eq_add_int n t, ← S.F.deriv_eq_add_int n t]
  exact ht_deriv_eq_of_eqOn_Icc S.F.differentiable sc.F'.differentiable (ca_window_short S sc)
    (fun r hr => sc.unchanged r (ca_offWindow_of_mem_Icc hr)) hmem

/-- the occurrence parameters of `D` are off the closed window (the arc carries no double point) -/
theorem ca_τ_offClosedWindow {Δ : Set Plane} (sc : SmoothCurl S Δ) (v : S.D.Γ.Visit) :
    OffClosedWindow sc.s₁ sc.s₂ (S.carried.τ v) := fun n hn =>
  S.no_double v n ⟨le_trans sc.α_le hn.1, le_trans hn.2 sc.le_β⟩

/-- `F'` is `F` at every old occurrence -/
theorem ca_F'_τ {Δ : Set Plane} (sc : SmoothCurl S Δ) (v : S.D.Γ.Visit) :
    sc.F'.γ (S.carried.τ v) = S.F.γ (S.carried.τ v) :=
  sc.unchanged _ (ca_offWindow_of_offClosed (ca_τ_offClosedWindow S sc v))

/-- … with the velocity of `F` -/
theorem ca_deriv_F'_τ {Δ : Set Plane} (sc : SmoothCurl S Δ) (v : S.D.Γ.Visit) :
    deriv sc.F'.γ (S.carried.τ v) = deriv S.F.γ (S.carried.τ v) :=
  ca_deriv_eq_of_offWindow S sc (ca_offWindow_of_offClosed (ca_τ_offClosedWindow S sc v))

/-- an old occurrence parameter is not the fractional part of a window parameter -/
theorem ca_τ_ne_fract {Δ : Set Plane} (sc : SmoothCurl S Δ) (v : S.D.Γ.Visit) {x : ℝ}
    (hx : x ∈ Ioo sc.s₁ sc.s₂) : S.carried.τ v ≠ Int.fract x := by
  intro h
  apply ca_τ_offClosedWindow S sc v ⌊x⌋
  rw [h, Int.fract, sub_add_cancel]
  exact Ioo_subset_Icc_self hx

/-- the two parameters of the model's double point have distinct fractional parts -/
theorem ca_fract_q_ne {Δ : Set Plane} (sc : SmoothCurl S Δ) : Int.fract sc.q₁ ≠ Int.fract sc.q₂ :=
  ca_fract_ne_of_lt sc.q₁_lt (by linarith [sc.q₁_mem.1, sc.q₂_mem.2, ca_window_short S sc])

/-- the occurrence parameters of `D'` on `F'`: the old parameter on an old occurrence, `fract q₁`
on the kink's under occurrence (met first), `fract q₂` on its over occurrence -/
def ca_τ' {Δ : Set Plane} (sc : SmoothCurl S Δ) {L : KinkLocation S} (K : KinkInsertion S L)
    (v : K.D'.Γ.Visit) : ℝ :=
  if h : v.1 = K.ri.kink then
    (if v = K.D'.underVisit K.ri.kink then Int.fract sc.q₁ else Int.fract sc.q₂)
  else S.carried.τ (K.oldVisit.symm ⟨v, h⟩)

theorem ca_τ'_old {Δ : Set Plane} (sc : SmoothCurl S Δ) {L : KinkLocation S}
    (K : KinkInsertion S L) (v : S.D.Γ.Visit) :
    ca_τ' S sc K (K.oldVisit v).1 = S.carried.τ v := by
  unfold ca_τ'
  rw [dite_eq_right (K.oldVisit v).2]
  congr 1
  exact K.oldVisit.symm_apply_apply v

theorem ca_τ'_under {Δ : Set Plane} (sc : SmoothCurl S Δ) {L : KinkLocation S}
    (K : KinkInsertion S L) : ca_τ' S sc K (K.D'.underVisit K.ri.kink) = Int.fract sc.q₁ := by
  unfold ca_τ'
  have h : (K.D'.underVisit K.ri.kink).1 = K.ri.kink := rfl
  rw [dite_eq_left h, ite_eq_left rfl]

theorem ca_τ'_over {Δ : Set Plane} (sc : SmoothCurl S Δ) {L : KinkLocation S}
    (K : KinkInsertion S L) : ca_τ' S sc K (K.D'.overVisit K.ri.kink) = Int.fract sc.q₂ := by
  unfold ca_τ'
  have h : (K.D'.overVisit K.ri.kink).1 = K.ri.kink := rfl
  rw [dite_eq_left h, ite_eq_right (K.D'.overVisit_ne_underVisit _)]

/-- every occurrence of `D'` is an old occurrence or one of the two kink occurrences -/
theorem ca_visit_cases {L : KinkLocation S} (K : KinkInsertion S L) (v : K.D'.Γ.Visit) :
    (∃ w : S.D.Γ.Visit, v = (K.oldVisit w).1) ∨
      v = K.D'.underVisit K.ri.kink ∨ v = K.D'.overVisit K.ri.kink := by
  by_cases h : v.1 = K.ri.kink
  · right
    rcases K.D'.visit_eq_over_or_under v with hv | hv
    · exact Or.inr (hv.trans (congrArg K.D'.overVisit h))
    · exact Or.inl (hv.trans (congrArg K.D'.underVisit h))
  · left
    exact ⟨K.oldVisit.symm ⟨v, h⟩, by rw [Equiv.apply_symm_apply]⟩

/-- an occurrence other than the two kink occurrences is old -/
theorem ca_old_of_ne {L : KinkLocation S} (K : KinkInsertion S L) (v : K.D'.Γ.Visit)
    (h₁ : v ≠ K.D'.underVisit K.ri.kink) (h₂ : v ≠ K.D'.overVisit K.ri.kink) :
    ∃ w : S.D.Γ.Visit, v = (K.oldVisit w).1 := by
  rcases ca_visit_cases S K v with h | h | h
  · exact h
  · exact absurd h h₁
  · exact absurd h h₂

theorem ca_τ'_mem {Δ : Set Plane} (sc : SmoothCurl S Δ) {L : KinkLocation S}
    (K : KinkInsertion S L) (v : K.D'.Γ.Visit) : ca_τ' S sc K v ∈ Ico (0 : ℝ) 1 := by
  rcases ca_visit_cases S K v with ⟨w, rfl⟩ | rfl | rfl
  · rw [ca_τ'_old]; exact S.carried.τ_mem w
  · rw [ca_τ'_under]; exact ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩
  · rw [ca_τ'_over]; exact ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩

theorem ca_τ'_inj {Δ : Set Plane} (sc : SmoothCurl S Δ) {L : KinkLocation S}
    (K : KinkInsertion S L) : Function.Injective (ca_τ' S sc K) := by
  intro v w h
  rcases ca_visit_cases S K v with ⟨v₀, rfl⟩ | rfl | rfl <;>
    rcases ca_visit_cases S K w with ⟨w₀, rfl⟩ | rfl | rfl
  · rw [ca_τ'_old, ca_τ'_old] at h
    rw [S.carried.τ_inj h]
  · rw [ca_τ'_old, ca_τ'_under] at h
    exact absurd h (ca_τ_ne_fract S sc v₀ sc.q₁_mem)
  · rw [ca_τ'_old, ca_τ'_over] at h
    exact absurd h (ca_τ_ne_fract S sc v₀ sc.q₂_mem)
  · rw [ca_τ'_under, ca_τ'_old] at h
    exact absurd h.symm (ca_τ_ne_fract S sc w₀ sc.q₁_mem)
  · rfl
  · rw [ca_τ'_under, ca_τ'_over] at h
    exact absurd h (ca_fract_q_ne S sc)
  · rw [ca_τ'_over, ca_τ'_old] at h
    exact absurd h.symm (ca_τ_ne_fract S sc w₀ sc.q₂_mem)
  · rw [ca_τ'_over, ca_τ'_under] at h
    exact absurd h.symm (ca_fract_q_ne S sc)
  · rfl

theorem ca_twin_eval {Δ : Set Plane} (sc : SmoothCurl S Δ) {L : KinkLocation S}
    (K : KinkInsertion S L) (v : K.D'.Γ.Visit) :
    sc.F'.γ (ca_τ' S sc K v) = sc.F'.γ (ca_τ' S sc K (K.D'.twin v)) := by
  rcases ca_visit_cases S K v with ⟨w, rfl⟩ | rfl | rfl
  · rw [← K.oldVisit_twin, ca_τ'_old, ca_τ'_old, ca_F'_τ, ca_F'_τ]
    exact S.carried.twin_eval w
  · rw [Diagram.twin_underVisit, ca_τ'_under, ca_τ'_over, ca_loop_fract, ca_loop_fract]
    exact sc.double
  · rw [Diagram.twin_overVisit, ca_τ'_over, ca_τ'_under, ca_loop_fract, ca_loop_fract]
    exact sc.double.symm

/-- a double point of `F'` with one parameter off the closed window is an old double point -/
theorem ca_doubles_off {Δ : Set Plane} (sc : SmoothCurl S Δ) {L : KinkLocation S}
    (K : KinkInsertion S L) {s t : ℝ} (hs : s ∈ Ico (0 : ℝ) 1) (ht : t ∈ Ico (0 : ℝ) 1)
    (hst : s ≠ t) (hq : sc.F'.γ s = sc.F'.γ t) (hs_off : OffClosedWindow sc.s₁ sc.s₂ s) :
    ∃ v : K.D'.Γ.Visit, s = ca_τ' S sc K v ∧ t = ca_τ' S sc K (K.D'.twin v) := by
  have hFs : sc.F'.γ s = S.F.γ s := sc.unchanged s (ca_offWindow_of_offClosed hs_off)
  rcases ca_open_or_off sc.s₁ sc.s₂ t with ⟨m, hm⟩ | ht_off
  · exfalso
    apply sc.arc_off_rest (t + m) hm s (ca_offWindow_of_offClosed hs_off)
    rw [sc.F'.eq_add_int, ← hq, hFs]
  · have hFt : sc.F'.γ t = S.F.γ t := sc.unchanged t ht_off
    obtain ⟨w, hw, hw'⟩ := S.carried.doubles s t hs ht hst (by rw [← hFs, ← hFt]; exact hq)
    refine ⟨(K.oldVisit w).1, ?_, ?_⟩
    · rw [ca_τ'_old]; exact hw
    · rw [← K.oldVisit_twin, ca_τ'_old]; exact hw'

theorem ca_doubles {Δ : Set Plane} (sc : SmoothCurl S Δ) {L : KinkLocation S}
    (K : KinkInsertion S L) (s t : ℝ) (hs : s ∈ Ico (0 : ℝ) 1) (ht : t ∈ Ico (0 : ℝ) 1)
    (hst : s ≠ t) (hq : sc.F'.γ s = sc.F'.γ t) :
    ∃ v : K.D'.Γ.Visit, s = ca_τ' S sc K v ∧ t = ca_τ' S sc K (K.D'.twin v) := by
  rcases ca_window_or_off sc.s₁ sc.s₂ s with ⟨n, hn⟩ | hs_off
  · rcases ca_window_or_off sc.s₁ sc.s₂ t with ⟨m, hm⟩ | ht_off
    · have hne : s + n ≠ t + m := fun h => hst (ca_eq_of_add_int_eq hs ht h)
      have heq : sc.F'.γ (s + n) = sc.F'.γ (t + m) := by
        rw [sc.F'.eq_add_int, sc.F'.eq_add_int]; exact hq
      rcases sc.only_double _ hn _ hm hne heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · refine ⟨K.D'.underVisit K.ri.kink, ?_, ?_⟩
        · rw [ca_τ'_under, ← h1, ca_fract_add_int_eq hs]
        · rw [Diagram.twin_underVisit, ca_τ'_over, ← h2, ca_fract_add_int_eq ht]
      · refine ⟨K.D'.overVisit K.ri.kink, ?_, ?_⟩
        · rw [ca_τ'_over, ← h1, ca_fract_add_int_eq hs]
        · rw [Diagram.twin_overVisit, ca_τ'_under, ← h2, ca_fract_add_int_eq ht]
    · obtain ⟨v, hv, hv'⟩ := ca_doubles_off S sc K ht hs hst.symm hq.symm ht_off
      refine ⟨K.D'.twin v, hv', ?_⟩
      rw [Diagram.twin_twin]; exact hv
  · exact ca_doubles_off S sc K hs ht hst hq hs_off

theorem ca_transverse {Δ : Set Plane} (sc : SmoothCurl S Δ) {L : KinkLocation S}
    (K : KinkInsertion S L) (v : K.D'.Γ.Visit) :
    det (deriv sc.F'.γ (ca_τ' S sc K v)) (deriv sc.F'.γ (ca_τ' S sc K (K.D'.twin v))) ≠ 0 := by
  rcases ca_visit_cases S K v with ⟨w, rfl⟩ | rfl | rfl
  · rw [← K.oldVisit_twin, ca_τ'_old, ca_τ'_old, ca_deriv_F'_τ, ca_deriv_F'_τ]
    exact S.carried.transverse w
  · rw [Diagram.twin_underVisit, ca_τ'_under, ca_τ'_over, ca_deriv_loop_fract,
      ca_deriv_loop_fract, ca_det_swap]
    exact neg_ne_zero.mpr sc.double_neg.ne
  · rw [Diagram.twin_overVisit, ca_τ'_over, ca_τ'_under, ca_deriv_loop_fract,
      ca_deriv_loop_fract]
    exact sc.double_neg.ne

/-- one component: the traversal coordinate of `D'` is injective -/
theorem ca_visitCoord_inj {L : KinkLocation S} (K : KinkInsertion S L) :
    Function.Injective K.D'.visitCoord := by
  intro v w h
  have hc : K.D'.Γ.c = 1 := K.c_eq.trans S.carried.one
  apply K.D'.visitCoord_injOn _ h
  apply Fin.ext
  have h1 := (K.D'.compOf v).isLt
  have h2 := (K.D'.compOf w).isLt
  omega

/-- the cyclic order of `D'` along `F'`: `cycBetween_ext_of_insert_pair` with the old triples from
`carried.order` + `order_old`, the gap of `t₀` from the gap lemma + `KinkLocation.gap` + `order_gap`,
and the inserted pair (under first) from the pair lemma + `order_pair` -/
theorem ca_order {Δ : Set Plane} (sc : SmoothCurl S Δ) {L : KinkLocation S}
    (K : KinkInsertion S L) (v w z : K.D'.Γ.Visit) :
    cycBetween (ca_τ' S sc K v) (ca_τ' S sc K w) (ca_τ' S sc K z) ↔
      cycBetween (K.D'.visitCoord v) (K.D'.visitCoord w) (K.D'.visitCoord z) := by
  have hs : sc.s₂ - sc.s₁ < 1 := by linarith [ca_window_short S sc]
  refine cycBetween_ext_of_insert_pair (ca_τ' S sc K) K.D'.visitCoord (ca_τ'_inj S sc K)
    (ca_visitCoord_inj S K) (K.D'.underVisit K.ri.kink) (K.D'.overVisit K.ri.kink)
    (K.D'.overVisit_ne_underVisit _).symm ?_ ?_ ?_ v w z
  · -- old triples
    intro a b c ha₁ ha₂ hb₁ hb₂ hc₁ hc₂
    obtain ⟨a₀, rfl⟩ := ca_old_of_ne S K a ha₁ ha₂
    obtain ⟨b₀, rfl⟩ := ca_old_of_ne S K b hb₁ hb₂
    obtain ⟨c₀, rfl⟩ := ca_old_of_ne S K c hc₁ hc₂
    rw [ca_τ'_old, ca_τ'_old, ca_τ'_old, S.carried.order, K.order_old]
  · -- one inserted entry, in the gap of `t₀`
    intro a c k hk ha₁ ha₂ hc₁ hc₂
    obtain ⟨a₀, rfl⟩ := ca_old_of_ne S K a ha₁ ha₂
    obtain ⟨c₀, rfl⟩ := ca_old_of_ne S K c hc₁ hc₂
    have hkk : k.1 = K.ri.kink := by rcases hk with rfl | rfl <;> rfl
    rw [ca_τ'_old, ca_τ'_old, K.order_gap a₀ c₀ k hkk, L.gap]
    have ht₀ : S.t₀ ∈ Ioo sc.s₁ sc.s₂ := ⟨sc.s₁_lt, sc.lt_s₂⟩
    rcases hk with rfl | rfl
    · rw [ca_τ'_under]
      exact cycBetween_fract_gap (S.carried.τ_mem a₀) (S.carried.τ_mem c₀) hs sc.q₁_mem ht₀
        (ca_τ_offClosedWindow S sc a₀) (ca_τ_offClosedWindow S sc c₀)
    · rw [ca_τ'_over]
      exact cycBetween_fract_gap (S.carried.τ_mem a₀) (S.carried.τ_mem c₀) hs sc.q₂_mem ht₀
        (ca_τ_offClosedWindow S sc a₀) (ca_τ_offClosedWindow S sc c₀)
  · -- the inserted pair, under first
    intro a ha₁ ha₂
    obtain ⟨a₀, rfl⟩ := ca_old_of_ne S K a ha₁ ha₂
    refine ⟨?_, K.order_pair a₀⟩
    rw [ca_τ'_old, ca_τ'_under, ca_τ'_over]
    exact cycBetween_fract_pair (S.carried.τ_mem a₀) hs sc.q₁_mem sc.q₂_mem sc.q₁_lt
      (ca_τ_offClosedWindow S sc a₀)

/-- the signs: the kink from `double_neg` and `kink_neg`, the old crossings from `carried.sign_eq`
and `old_sign` (velocities of `F'` at old occurrences are those of `F`) -/
theorem ca_sign_eq {Δ : Set Plane} (sc : SmoothCurl S Δ) {L : KinkLocation S}
    (K : KinkInsertion S L) (x : K.D'.Γ.Crossing) :
    SignType.sign (det (deriv sc.F'.γ (ca_τ' S sc K (K.D'.overVisit x)))
      (deriv sc.F'.γ (ca_τ' S sc K (K.D'.underVisit x)))) = K.D'.sign x := by
  by_cases hx : x = K.ri.kink
  · subst hx
    rw [ca_τ'_over, ca_τ'_under, ca_deriv_loop_fract, ca_deriv_loop_fract,
      sign_neg sc.double_neg, K.kink_neg]
  · obtain ⟨x₀, rfl⟩ : ∃ x₀, x = (K.old x₀).1 := ⟨K.old.symm ⟨x, hx⟩, by simp⟩
    rw [← K.oldVisit_over, ← K.oldVisit_under, ca_τ'_old, ca_τ'_old, ca_deriv_F'_τ,
      ca_deriv_F'_τ, K.old_sign]
    exact S.carried.sign_eq x₀

/-- the record assembly: `τ'` = old parameters on the old occurrences, `fract q₁`/`fract q₂` on the
kink's under/over occurrence; the eight clauses of `RecordCarried` from `SmoothCurl`, `KinkInsertion`,
`cycBetween_ext_of_insert_pair` and the two gap lemmas -/
theorem exists_carriedAssembly {Δ : Set Plane} (sc : SmoothCurl S Δ) {L : KinkLocation S}
    (K : KinkInsertion S L) : Nonempty (CarriedAssembly S sc K) := by
  exact ⟨{ rc := { one := K.c_eq.trans S.carried.one
                   τ := ca_τ' S sc K
                   τ_mem := ca_τ'_mem S sc K
                   τ_inj := ca_τ'_inj S sc K
                   twin_eval := ca_twin_eval S sc K
                   doubles := ca_doubles S sc K
                   transverse := ca_transverse S sc K
                   order := ca_order S sc K
                   sign_eq := ca_sign_eq S sc K }
           τ_old := ca_τ'_old S sc K
           τ_under := ca_τ'_under S sc K
           τ_over := ca_τ'_over S sc K }⟩

/-! ### Unit A — assembly leaves (the smooth clauses read on the packages) -/

/-- off the open window (mod 1) the derivative is unchanged: off the closed window `F' = F` on a
neighbourhood; at an endpoint `s₁`, `s₂` (mod 1) `F' = F` on a one-sided neighbourhood (the window
is shorter than the period) and both are differentiable, so the derivatives agree -/
theorem deriv_eq_of_offWindow {Δ : Set Plane} (sc : SmoothCurl S Δ) {t : ℝ}
    (ht : OffWindow sc.s₁ sc.s₂ t) : deriv sc.F'.γ t = deriv S.F.γ t := by
  exact ca_deriv_eq_of_offWindow S sc ht

/-- off the closed window the derivative is unchanged -/
theorem deriv_eq_of_offClosedWindow {Δ : Set Plane} (sc : SmoothCurl S Δ) {t : ℝ}
    (ht : OffClosedWindow sc.s₁ sc.s₂ t) : deriv sc.F'.γ t = deriv S.F.γ t :=
  deriv_eq_of_offWindow S sc fun n hn => ht n (Set.Ioo_subset_Icc_self hn)

/-- (i) "has the same double points outside Δ" -/
theorem doublePoints_diff_eq {Δ : Set Plane} (sc : SmoothCurl S Δ) :
    SmoothRegularLoop.doublePoints sc.F'.γ \ Δ = SmoothRegularLoop.doublePoints S.F.γ \ Δ := by
  ext q
  constructor
  · rintro ⟨⟨s, t, hs, ht, hst, rfl, hq⟩, hΔ⟩
    have hs' : OffClosedWindow sc.s₁ sc.s₂ s := by
      rcases ca_window_or_off sc.s₁ sc.s₂ s with ⟨n, hn⟩ | h
      · exact absurd (by rw [← sc.F'.eq_add_int n s]; exact sc.new_in_disc _ hn) hΔ
      · exact h
    have ht' : OffClosedWindow sc.s₁ sc.s₂ t := by
      rcases ca_window_or_off sc.s₁ sc.s₂ t with ⟨n, hn⟩ | h
      · exact absurd (by rw [← hq, ← sc.F'.eq_add_int n t]; exact sc.new_in_disc _ hn) hΔ
      · exact h
    have hFs := sc.unchanged s (ca_offWindow_of_offClosed hs')
    have hFt := sc.unchanged t (ca_offWindow_of_offClosed ht')
    refine ⟨⟨s, t, hs, ht, hst, hFs.symm, ?_⟩, hΔ⟩
    rw [← hFt]; exact hq
  · rintro ⟨⟨s, t, hs, ht, hst, rfl, hq⟩, hΔ⟩
    have hs' : OffClosedWindow sc.s₁ sc.s₂ s := by
      rcases ca_window_or_off sc.s₁ sc.s₂ s with ⟨n, hn⟩ | h
      · exact absurd (by rw [← S.F.eq_add_int n s]; exact sc.old_in_disc _ hn) hΔ
      · exact h
    have ht' : OffClosedWindow sc.s₁ sc.s₂ t := by
      rcases ca_window_or_off sc.s₁ sc.s₂ t with ⟨n, hn⟩ | h
      · exact absurd (by rw [← hq, ← S.F.eq_add_int n t]; exact sc.old_in_disc _ hn) hΔ
      · exact h
    have hFs := sc.unchanged s (ca_offWindow_of_offClosed hs')
    have hFt := sc.unchanged t (ca_offWindow_of_offClosed ht')
    refine ⟨⟨s, t, hs, ht, hst, hFs, ?_⟩, hΔ⟩
    rw [hFt]; exact hq

/-- (ii) "exactly one [point of Δ] at which [the tangent] equals −u", in the fundamental period -/
theorem one_neg_u_of {Δ : Set Plane} (sc : SmoothCurl S Δ) :
    ∃! t : ℝ, t ∈ Ico (0 : ℝ) 1 ∧ sc.F'.γ t ∈ Δ ∧ normalize (deriv sc.F'.γ t) = -S.u := by
  obtain ⟨t₀, ⟨ht₀, hu₀⟩, huniq⟩ := sc.new_one_neg_u
  refine ⟨Int.fract t₀, ⟨⟨Int.fract_nonneg _, Int.fract_lt_one _⟩, ?_, ?_⟩, ?_⟩
  · rw [ca_loop_fract]; exact sc.new_in_disc _ ht₀
  · rw [ca_deriv_loop_fract]; exact hu₀
  · rintro t ⟨ht01, htΔ, htu⟩
    rcases ca_window_or_off sc.s₁ sc.s₂ t with ⟨n, hn⟩ | hoff
    · have h := huniq (t + n) ⟨hn, by rw [sc.F'.deriv_eq_add_int]; exact htu⟩
      rw [← h, ca_fract_add_int_eq ht01]
    · exfalso
      have hoff' := ca_offWindow_of_offClosed hoff
      have hF : S.F.γ t ∈ Δ := by rw [← sc.unchanged t hoff']; exact htΔ
      apply sc.tails_no_neg_u t hF hoff'
      show normalize (deriv S.F.γ t) = -S.u
      rw [← ca_deriv_eq_of_offWindow S sc hoff']
      exact htu

/-- a double point of `F'` in `Δ` cannot have a parameter off the closed window: the other
parameter is either on the inserted arc (`arc_off_rest`) or off it too, giving a double point of
`F` in `Δ`, hence on the embedded arc (`meets_arc`), which carries none (`no_double`) -/
theorem ca_no_double_off {Δ : Set Plane} (sc : SmoothCurl S Δ) {s t : ℝ} (hs : s ∈ Ico (0 : ℝ) 1)
    (ht : t ∈ Ico (0 : ℝ) 1) (hst : s ≠ t) (hq : sc.F'.γ s = sc.F'.γ t) (hΔ : sc.F'.γ s ∈ Δ)
    (hs_off : OffClosedWindow sc.s₁ sc.s₂ s) : False := by
  have hFs : sc.F'.γ s = S.F.γ s := sc.unchanged s (ca_offWindow_of_offClosed hs_off)
  rcases ca_open_or_off sc.s₁ sc.s₂ t with ⟨m, hm⟩ | ht_off
  · apply sc.arc_off_rest (t + m) hm s (ca_offWindow_of_offClosed hs_off)
    rw [sc.F'.eq_add_int, ← hq, hFs]
  · have hFt : sc.F'.γ t = S.F.γ t := sc.unchanged t ht_off
    obtain ⟨v, hv, -⟩ := S.carried.doubles s t hs ht hst (by rw [← hFs, ← hFt]; exact hq)
    obtain ⟨k, hk⟩ := sc.meets_arc s (by rw [← hFs]; exact hΔ)
    exact S.no_double v k (by rw [← hv]; exact hk)

/-- (iii) "exactly one double point inside Δ": every double point of `F'` in `Δ` is `F'(q₂)` -/
theorem one_double_of {Δ : Set Plane} (sc : SmoothCurl S Δ) :
    ∀ q ∈ SmoothRegularLoop.doublePoints sc.F'.γ ∩ Δ, q = sc.F'.γ sc.q₂ := by
  rintro q ⟨⟨s, t, hs, ht, hst, rfl, hq⟩, hΔ⟩
  rcases ca_window_or_off sc.s₁ sc.s₂ s with ⟨n, hn⟩ | hs_off
  · rcases ca_window_or_off sc.s₁ sc.s₂ t with ⟨m, hm⟩ | ht_off
    · have hne : s + n ≠ t + m := fun h => hst (ca_eq_of_add_int_eq hs ht h)
      have heq : sc.F'.γ (s + n) = sc.F'.γ (t + m) := by
        rw [sc.F'.eq_add_int, sc.F'.eq_add_int]; exact hq.symm
      rcases sc.only_double _ hn _ hm hne heq with ⟨h1, -⟩ | ⟨h1, -⟩
      · rw [← sc.F'.eq_add_int n s, h1, sc.double]
      · rw [← sc.F'.eq_add_int n s, h1]
    · exact (ca_no_double_off S sc ht hs hst.symm hq (hq ▸ hΔ) ht_off).elim
  · exact (ca_no_double_off S sc hs ht hst hq.symm hΔ hs_off).elim

end Curl

/-! ## 8. Assembly: the witness from the three packages (PROVED from the leaves) -/

namespace Curl

variable {S : CurlSite} {Δ : Set Plane} (sc : SmoothCurl S Δ) {L : KinkLocation S}
  (K : KinkInsertion S L) (ca : CarriedAssembly S sc K)

/-- a lift on `[a, b]` restricts to a lift on a sub-interval -/
theorem IsLiftOn.mono {u : ℝ → Plane} {θ : ℝ → ℝ} {a b a' b' : ℝ} (h : IsLiftOn u θ a b)
    (ha : a ≤ a') (hb : b' ≤ b) : IsLiftOn u θ a' b' :=
  ⟨h.1.mono (Set.Icc_subset_Icc ha hb), fun s hs => h.2 s (Set.Icc_subset_Icc ha hb hs)⟩

/-- the occurrence parameters of `D` are off the closed window (the arc carries no double point) -/
theorem τ_offClosedWindow (v : S.D.Γ.Visit) : OffClosedWindow sc.s₁ sc.s₂ (S.carried.τ v) := by
  intro n hn
  exact S.no_double v n ⟨le_trans sc.α_le hn.1, le_trans hn.2 sc.le_β⟩

theorem OffClosedWindow.offWindow {s₁ s₂ t : ℝ} (h : OffClosedWindow s₁ s₂ t) : OffWindow s₁ s₂ t :=
  fun n hn => h n (Set.Ioo_subset_Icc_self hn)

/-- `F'` is `F` at every old occurrence -/
theorem F'_τ (v : S.D.Γ.Visit) : sc.F'.γ (S.carried.τ v) = S.F.γ (S.carried.τ v) :=
  sc.unchanged _ (τ_offClosedWindow sc v).offWindow

/-- `F'` at the fractional part of a window parameter is `F'` there (periodicity) -/
theorem F'_fract (x : ℝ) : sc.F'.γ (Int.fract x) = sc.F'.γ x := by
  have h := sc.F'.eq_add_int (-⌊x⌋) x
  rw [Int.fract]
  simpa [sub_eq_add_neg] using h

/-- the move relation from the data -/
theorem ri_of : RI S.D K.D' := ⟨K.U, Or.inl ⟨K.ri⟩⟩

/-- (ii) no tangent `u` in `Δ`: on the window from the model and collars, off it from the isolation
of `p` (the tangent of `F` there) -/
theorem no_u_of (t : ℝ) (ht : sc.F'.γ t ∈ Δ) : normalize (deriv sc.F'.γ t) ≠ S.u := by
  by_cases hw : ∃ n : ℤ, t + n ∈ Set.Icc sc.s₁ sc.s₂
  · obtain ⟨n, hn⟩ := hw
    have hd : deriv sc.F'.γ t = deriv sc.F'.γ (t + n) := (sc.F'.deriv_eq_add_int n t).symm
    rw [hd]
    exact sc.new_no_u _ hn
  · push Not at hw
    have hoff : OffClosedWindow sc.s₁ sc.s₂ t := hw
    rw [deriv_eq_of_offClosedWindow S sc hoff]
    have hF : S.F.γ t ∈ Δ := by rw [← sc.unchanged t hoff.offWindow]; exact ht
    obtain ⟨n, hn⟩ := sc.meets_arc t hF
    intro hu
    have hu' : normalize (deriv S.F.γ (t + n)) = S.u := by
      rw [S.F.deriv_eq_add_int n t]; exact hu
    have := S.isolated (t + n) hn hu'
    apply hoff n
    rw [this]
    exact ⟨sc.s₁_lt.le, sc.lt_s₂.le⟩

/-- the witness assembled from the smooth curl, the polygonal kink and the record assembly -/
def curlWitness : CurlWitness S Δ where
  F' := sc.F'
  D' := K.D'
  carried' := ca.rc
  s₁ := sc.s₁
  s₂ := sc.s₂
  s₁_lt := sc.s₁_lt
  lt_s₂ := sc.lt_s₂
  α_le := sc.α_le
  le_β := sc.le_β
  unchanged := sc.unchanged
  unchanged_deriv := fun _ ht => deriv_eq_of_offWindow S sc ht
  new_in_disc := sc.new_in_disc
  old_in_disc := sc.old_in_disc
  disc := sc.disc
  p_mem := sc.p_mem
  disc_meets_arc := sc.meets_arc
  ri := ri_of K
  poly_eq := (P_reidemeister_I (ri_of K)).symm
  doubles_outside := doublePoints_diff_eq S sc
  kink := K.ri.kink
  old := K.old
  old_point := fun x => by
    rw [← K.oldVisit_over, ca.τ_old]
    exact F'_τ sc _
  old_sign := K.old_sign
  no_u := no_u_of sc
  one_neg_u := one_neg_u_of S sc
  kink_mem := by
    rw [ca.τ_over, F'_fract]
    exact sc.new_in_disc _ (Set.Ioo_subset_Icc_self sc.q₂_mem)
  one_double := fun q hq => by
    rw [ca.τ_over, F'_fract]
    exact one_double_of S sc q hq
  kink_neg := K.kink_neg
  rot_eq := by
    have h := rot_sub_rot_of_window S.F sc.F' (sc.s₁_lt.trans sc.lt_s₂)
      (by linarith [sc.α_le, sc.le_β, S.short]) sc.unchanged
      (IsLiftOn.mono S.lift sc.α_le sc.le_β) sc.lift'
    rw [sc.increment] at h
    have hpi : (2 * Real.pi) ≠ 0 := by positivity
    have : ((S.θ sc.s₂ - S.θ sc.s₁ - 2 * Real.pi) - (S.θ sc.s₂ - S.θ sc.s₁)) / (2 * Real.pi) = -1 := by
      field_simp; ring
    linarith [h, this]
  writhe_eq := K.writhe

end Curl

/-! ## 9. The row from the chain -/

open Curl in
/-- the existence sentence, assembled from the chain: the smooth curl (Unit R) in a disc inside the
preassigned neighbourhood, the polygonal kink (Unit K) at a location in the right gap, the record
assembly (Unit C) -/
theorem exists_curl_main (S : CurlSite) (Δ₀ : Set Plane) (h₀ : S.p ∈ interior Δ₀) :
    ∃ Δ : Set Plane, Δ ⊆ Δ₀ ∧ Nonempty (CurlWitness S Δ) := by
  obtain ⟨Δ, hΔ, ⟨sc⟩⟩ := exists_smoothCurl S Δ₀ h₀
  obtain ⟨L⟩ := exists_kinkLocation S
  obtain ⟨K⟩ := exists_kinkInsertion S L
  obtain ⟨ca⟩ := exists_carriedAssembly S sc K
  exact ⟨Δ, hΔ, ⟨curlWitness sc K ca⟩⟩

/-- cf:lem-curl, assembled from the chain; the clause fields are projections of `CurlWitness`. -/
theorem cf_lem_curl : CurlData where
  exists_curl := exists_curl_main
  exists_curl' := fun S => by
    obtain ⟨Δ, -, hW⟩ := exists_curl_main S Set.univ (by rw [interior_univ]; exact Set.mem_univ _)
    exact ⟨Δ, hW⟩
  disc := fun _ _ W => ⟨W.disc, W.p_mem, W.disc_meets_arc,
    fun t ht => ⟨W.unchanged t ht, W.unchanged_deriv t ht⟩, W.new_in_disc⟩
  i := fun _ _ W => ⟨W.smooth, W.periodic, W.regular, W.one, ⟨W.carried'⟩, W.ri, W.poly_eq,
    W.doubles_outside, fun x => ⟨W.old_point x, W.old_sign x⟩⟩
  ii := fun _ _ W => ⟨W.no_u, W.one_neg_u⟩
  iii := fun _ _ W => ⟨W.kink_mem, W.one_double, W.kink_neg, W.kink_smoothSign⟩
  iv := fun _ _ W => ⟨W.rot_eq, W.writhe_eq, W.smoothWrithe_eq⟩

end

end SM

#print axioms SM.cf_lem_curl
#print axioms SM.CurlData
#print axioms SM.Carried.toRecordCarried
