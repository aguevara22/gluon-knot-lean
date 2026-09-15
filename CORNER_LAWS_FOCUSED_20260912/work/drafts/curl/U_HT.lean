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
  sorry

/-- `b'(t) = (6t/11, −3)` -/
theorem hasDerivAt_bModel (t : ℝ) : HasDerivAt bModel (6 * t / 11, -3) t := by
  sorry

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
  sorry

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
  sorry
theorem fitA_smul (u v : Plane) (x y : ℝ) (r : ℝ) (z : Plane) :
    fitA u v x y (r • z) = r • fitA u v x y z := by
  sorry

/-- "det A = x > 0" (sm-3:4000-4001), for `(v, u)` positively oriented orthonormal -/
theorem det_fitA_pos (u v : Plane) (hvu : det v u = 1) {x y : ℝ} (hx : 0 < x) :
    0 < det (fitA u v x y v₀) (fitA u v x y u₀) := by
  sorry

/-- "A(q v₀ + u₀) = (H/a) T₋, A(−q v₀ + u₀) = (H/c) T₊" (sm-3:3998-3999), with `T₋ = a v + b u`,
`T₊ = −c v + d u`, `a, b, c, d > 0`, `H = 2ac/(bc+ad)` -/
theorem fitA_ray_minus (u v : Plane) {a b c d : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    fitA u v (xFit a b c d) (yFit a b c d) (qFit • v₀ + u₀) =
      (2 * a * c / (b * c + a * d) / a) • (a • v + b • u) := by
  sorry
theorem fitA_ray_plus (u v : Plane) {a b c d : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    fitA u v (xFit a b c d) (yFit a b c d) (-(qFit • v₀) + u₀) =
      (2 * a * c / (b * c + a * d) / c) • (-(c • v) + d • u) := by
  sorry

/-- "1 − (qy)² = 4abcd/(bc+ad)² > 0, so |y| < 1/q uniformly" (sm-3:4003-4006) -/
theorem yFit_bound {a b c d : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    |qFit * yFit a b c d| < 1 := by
  sorry

/-- `x > 0` -/
theorem xFit_pos {a b c d : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    0 < xFit a b c d := by
  sorry

/-- "The two outer determinants are det(q v₀ + u₀, −q v₀ + u₀) = 2q > 0 and det(T₋, T₊) = ad + bc > 0, so
the ordered-ray condition holds; it is computed, not inferred" (sm-3:3987-3990), for `(v, u)` positively
oriented orthonormal -/
theorem orderedRay_condition (u v : Plane) (hvu : det v u = 1) (a b c d : ℝ) :
    det (qFit • v₀ + u₀) (-(qFit • v₀) + u₀) = 2 * qFit ∧
      det (a • v + b • u) (-(c • v) + d • u) = a * d + b * c := by
  sorry

/-! ### Unit G — the positive-turn chart and the cuts (sm-3:3959-3976, 3981-3984) -/

variable (S : CurlSite)

/-- `(v, u)` is a positively oriented orthonormal basis -/
theorem det_vDir_u : det (vDir S) S.u = 1 := by
  sorry
theorem planeDot_vDir_u : planeDot (vDir S) S.u = 0 := by
  sorry

/-- the chart expansion `γ(s) − p = ξ(s) v + η(s) u` -/
theorem expansion (t : ℝ) : S.F.γ t = S.p + ξ S t • vDir S + η S t • S.u := by
  sorry

/-- "after shrinking the chart … |θ(s)| < π/2": a sub-arc `[α', β']` around `t₀` on which the
relative angle stays in `(−π/2, π/2)` -/
theorem exists_chart : ∃ α' β' : ℝ, S.α ≤ α' ∧ α' < S.t₀ ∧ S.t₀ < β' ∧ β' ≤ S.β ∧
    ∀ t ∈ Icc α' β', |θrel S t| < Real.pi / 2 := by
  sorry

/-- "ξ'(s) = −sin θ(s), η'(s) = cos θ(s)" up to the speed (the parameter is not arclength) -/
theorem hasDerivAt_η {t : ℝ} (ht : t ∈ Icc S.α S.β) :
    HasDerivAt (η S) (euclideanLength (deriv S.F.γ t) * Real.cos (θrel S t)) t := by
  sorry
theorem hasDerivAt_ξ {t : ℝ} (ht : t ∈ Icc S.α S.β) :
    HasDerivAt (ξ S) (-(euclideanLength (deriv S.F.γ t) * Real.sin (θrel S t))) t := by
  sorry

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
  sorry

/-- "For every level sufficiently close to ξ(0) from below, strict monotonicity and the intermediate
value theorem give unique cuts s₋ < 0 < s₊ with ξ(s₋) = ξ(s₊), and both tend to 0" (sm-3:3975-3977):
cuts within `δ` of `t₀` -/
theorem exists_cuts {α' β' : ℝ} (hα : S.α ≤ α') (hα' : α' < S.t₀) (hβ' : S.t₀ < β') (hβ : β' ≤ S.β)
    (hθ : ∀ t ∈ Icc α' β', |θrel S t| < Real.pi / 2) {δ : ℝ} (hδ : 0 < δ) :
    ∃ s₁ s₂ : ℝ, α' ≤ s₁ ∧ s₁ < S.t₀ ∧ S.t₀ < s₂ ∧ s₂ ≤ β' ∧ s₂ - s₁ < δ ∧ ξ S s₁ = ξ S s₂ := by
  sorry

/-- "p₊ − p₋ = ℓ u, ℓ > 0" (sm-3:3980-3981) -/
theorem cut_displacement {s₁ s₂ : ℝ} (h : ξ S s₁ = ξ S s₂) :
    S.F.γ s₂ - S.F.γ s₁ = (η S s₂ - η S s₁) • S.u := by
  sorry

/-- the endpoint tangents in the frame: `T₋ = a v + b u` with `a = −sin θ(s₋) > 0`, `b = cos θ(s₋) > 0`;
`T₊ = −c v + d u` with `c = sin θ(s₊) > 0`, `d = cos θ(s₊) > 0` (sm-3:3984-3987) -/
theorem endpoint_tangent {t : ℝ} (ht : t ∈ Icc S.α S.β) :
    S.T t = (-Real.sin (θrel S t)) • vDir S + Real.cos (θrel S t) • S.u := by
  sorry

/-- "the disc is fixed first": a closed Euclidean disc about `p` inside a preassigned neighbourhood
`Δ₀` whose intersection with the curve is contained in the chart arc (compactness of the rest of
the curve, which misses `p` since the arc is embedded and carries no double point) -/
theorem exists_disc_in_chart {α' β' : ℝ} (hα : S.α ≤ α') (hα' : α' < S.t₀) (hβ' : S.t₀ < β')
    (hβ : β' ≤ S.β) (Δ₀ : Set Plane) (h₀ : S.p ∈ interior Δ₀) :
    ∃ r : ℝ, 0 < r ∧ disc S r ⊆ Δ₀ ∧ ∀ t : ℝ, S.F.γ t ∈ disc S r → ∃ n : ℤ, t + n ∈ Icc α' β' := by
  sorry

/-- the closed Euclidean disc is an accepted disc with `p` in its interior -/
theorem disc_isDisc {r : ℝ} (hr : 0 < r) : IsDisc (disc S r) := by
  sorry
theorem p_mem_interior_disc {r : ℝ} (hr : 0 < r) : S.p ∈ interior (disc S r) := by
  sorry

/-- the retained tails: on the chart arc away from `t₀` the tangent is neither `u` nor `−u`
(sm-3:4216-4217) -/
theorem tail_tangent_ne {t : ℝ} (ht : t ∈ Icc S.α S.β) (hθ : |θrel S t| < Real.pi / 2) (hne : t ≠ S.t₀) :
    S.T t ≠ S.u ∧ S.T t ≠ -S.u := by
  sorry

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
  sorry

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

/-- the cuts and the fit exist at every disc about `p` (Unit G: `exists_cuts` with the cuts close to
`t₀`, `endpoint_tangent` for `a, b, c, d`, `η_strictMonoOn` for `ℓ > 0`, continuity of `F` for the removed
arc, and the diameter bound of `inserted_arc_props` with `x → 0`, `ℓ → 0` for the inserted arc) -/
theorem exists_cutFit {α' β' : ℝ} (hα : S.α ≤ α') (hα' : α' < S.t₀) (hβ' : S.t₀ < β') (hβ : β' ≤ S.β)
    (hθ : ∀ t ∈ Icc α' β', |θrel S t| < Real.pi / 2) {r : ℝ} (hr : 0 < r) :
    Nonempty (CutFit S α' β' r) := by
  sorry

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
  sorry

/-- the periodic extension of the new arc is a `SmoothRegularLoop` equal to `F` off the window -/
theorem exists_loop_of_arc {N : ℝ → Plane} (hN : ContDiff ℝ ∞ N) (hreg : ∀ t, deriv N t ≠ 0)
    {s₁ s₂ : ℝ} (hs : s₂ - s₁ < 1) (hl : ∀ t, t ≤ s₁ → N t = S.F.γ t) (hr : ∀ t, s₂ ≤ t → N t = S.F.γ t) :
    ∃ F' : SmoothRegularLoop, (∀ t ∈ Icc s₁ s₂, F'.γ t = N t) ∧
      (∀ t : ℝ, OffWindow s₁ s₂ t → F'.γ t = S.F.γ t) ∧
      (∀ t ∈ Icc s₁ s₂, deriv F'.γ t = deriv N t) := by
  sorry

/-- The smooth curl exists inside any preassigned neighbourhood of `p` (the assembly of Units G, R:
`exists_chart`, `exists_disc_in_chart`, `exists_cutFit`, `exists_glued_arc`, `exists_loop_of_arc`;
`disc_isDisc`, `p_mem_interior_disc`; the tails clause from `tail_tangent_ne`; `s₂ − s₁ < 1` from
`short`). -/
theorem exists_smoothCurl (Δ₀ : Set Plane) (h₀ : S.p ∈ interior Δ₀) :
    ∃ Δ : Set Plane, Δ ⊆ Δ₀ ∧ Nonempty (SmoothCurl S Δ) := by
  sorry

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

/-- a location exists: the gap of `D`'s traversal circle between the occurrences around `t₀`
contains an interior edge point off every other edge -/
theorem exists_kinkLocation : Nonempty (KinkLocation S) := by
  sorry

/-- the kink insertion: a small clockwise monogon (three new vertices) at `r`, later branch over;
generic shadow, `RIData` in a small disc `U` about `r`, crossing/occurrence correspondence,
cyclic-order clauses, writhe (a splice construction as in SM/Smoothing.lean, one strand cut) -/
theorem exists_kinkInsertion (L : KinkLocation S) : Nonempty (KinkInsertion S L) := by
  sorry

/-- the outer crossings of a Reidemeister-I site keep their double points (accepted `OutsideMatch`:
`eval_eq` at the over occurrence, `over_eq`) — reusable helper for `KinkInsertion.old_point` -/
theorem _root_.SM.Link.RIData.crossingPoint_ψ {U : Set Plane} {D D' : Diagram} (h : RIData U D D')
    (x : D.OuterCrossing U) : D'.Γ.crossingPoint (h.out.ψ x).1 = D.Γ.crossingPoint x.1 := by
  sorry

/-- the outer crossings of a Reidemeister-I site keep their signs (`dir_pos` at both occurrences; the
crossing point is strictly outside `U`, a frontier point being traversed once by `Clean`) — reusable
helper for `KinkInsertion.old_sign` -/
theorem _root_.SM.Link.RIData.sign_ψ {U : Set Plane} {D D' : Diagram} (h : RIData U D D')
    (x : D.OuterCrossing U) : D'.sign (h.out.ψ x).1 = D.sign x.1 := by
  sorry

/-- the writhe of a Reidemeister-I site: the outer crossings correspond with the same signs
(`sign_ψ`), `D` has no inner crossing (`no_inner`) and the kink is the only inner one of `D'`
(`inner_iff'`) — reusable helper for `KinkInsertion.writhe` -/
theorem _root_.SM.Link.RIData.writhe_eq {U : Set Plane} {D D' : Diagram} (h : RIData U D D') :
    D'.writhe = D.writhe + (D'.sign h.kink : ℤ) := by
  sorry

/-! ### Unit C — the record of `D'` carried by `F'` (combinatorics of the cyclic order) -/

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
  sorry

/-- two parameters of a window (shorter than the period) that contains no occurrence parameter
(mod 1) occupy the same gap of the occurrences -/
theorem cycBetween_fract_gap {τ : ℝ} (hτ : τ ∈ Ico (0 : ℝ) 1) {τ' : ℝ} (hτ' : τ' ∈ Ico (0 : ℝ) 1)
    {s₁ s₂ x y : ℝ} (hs : s₂ - s₁ < 1) (hx : x ∈ Ioo s₁ s₂) (hy : y ∈ Ioo s₁ s₂)
    (h₁ : OffClosedWindow s₁ s₂ τ) (h₂ : OffClosedWindow s₁ s₂ τ') :
    cycBetween τ (Int.fract x) τ' ↔ cycBetween τ (Int.fract y) τ' := by
  sorry

/-- two ordered parameters of such a window are met in that order after every occurrence -/
theorem cycBetween_fract_pair {τ : ℝ} (hτ : τ ∈ Ico (0 : ℝ) 1) {s₁ s₂ x y : ℝ} (hs : s₂ - s₁ < 1)
    (hx : x ∈ Ioo s₁ s₂) (hy : y ∈ Ioo s₁ s₂) (hxy : x < y) (h₁ : OffClosedWindow s₁ s₂ τ) :
    cycBetween τ (Int.fract x) (Int.fract y) := by
  sorry

/-- the record assembly: `τ'` = old parameters on the old occurrences, `fract q₁`/`fract q₂` on the
kink's under/over occurrence; the eight clauses of `RecordCarried` from `SmoothCurl`, `KinkInsertion`,
`cycBetween_ext_of_insert_pair` and the two gap lemmas -/
theorem exists_carriedAssembly {Δ : Set Plane} (sc : SmoothCurl S Δ) {L : KinkLocation S}
    (K : KinkInsertion S L) : Nonempty (CarriedAssembly S sc K) := by
  sorry

/-! ### Unit A — assembly leaves (the smooth clauses read on the packages) -/

/-- off the open window (mod 1) the derivative is unchanged: off the closed window `F' = F` on a
neighbourhood; at an endpoint `s₁`, `s₂` (mod 1) `F' = F` on a one-sided neighbourhood (the window
is shorter than the period) and both are differentiable, so the derivatives agree -/
theorem deriv_eq_of_offWindow {Δ : Set Plane} (sc : SmoothCurl S Δ) {t : ℝ}
    (ht : OffWindow sc.s₁ sc.s₂ t) : deriv sc.F'.γ t = deriv S.F.γ t := by
  sorry

/-- off the closed window the derivative is unchanged -/
theorem deriv_eq_of_offClosedWindow {Δ : Set Plane} (sc : SmoothCurl S Δ) {t : ℝ}
    (ht : OffClosedWindow sc.s₁ sc.s₂ t) : deriv sc.F'.γ t = deriv S.F.γ t :=
  deriv_eq_of_offWindow S sc fun n hn => ht n (Set.Ioo_subset_Icc_self hn)

/-- (i) "has the same double points outside Δ" -/
theorem doublePoints_diff_eq {Δ : Set Plane} (sc : SmoothCurl S Δ) :
    SmoothRegularLoop.doublePoints sc.F'.γ \ Δ = SmoothRegularLoop.doublePoints S.F.γ \ Δ := by
  sorry

/-- (ii) "exactly one [point of Δ] at which [the tangent] equals −u", in the fundamental period -/
theorem one_neg_u_of {Δ : Set Plane} (sc : SmoothCurl S Δ) :
    ∃! t : ℝ, t ∈ Ico (0 : ℝ) 1 ∧ sc.F'.γ t ∈ Δ ∧ normalize (deriv sc.F'.γ t) = -S.u := by
  sorry

/-- (iii) "exactly one double point inside Δ": every double point of `F'` in `Δ` is `F'(q₂)` -/
theorem one_double_of {Δ : Set Plane} (sc : SmoothCurl S Δ) :
    ∀ q ∈ SmoothRegularLoop.doublePoints sc.F'.γ ∩ Δ, q = sc.F'.γ sc.q₂ := by
  sorry

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
