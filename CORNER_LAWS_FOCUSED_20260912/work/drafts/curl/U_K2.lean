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

/-- "(1) It is C^∞": the blend of `C^∞` functions is `C^∞`, equals `f` on `(−∞, e₁]` and `g` on
`[e₁ + lam, ∞)` (the flat endpoint jets of `φ`, exact equality here) -/
theorem blend_smooth {f g : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) {e₁ lam : ℝ} (hlam : 0 < lam) :
    ContDiff ℝ ∞ (blend f g e₁ lam) := by
  sorry
theorem blend_eq_left {f g : ℝ → ℝ} {e₁ lam : ℝ} (hlam : 0 < lam) {η : ℝ} (h : η ≤ e₁) :
    blend f g e₁ lam η = f η := by
  sorry
theorem blend_eq_right {f g : ℝ → ℝ} {e₁ lam : ℝ} (hlam : 0 < lam) {η : ℝ} (h : e₁ + lam ≤ η) :
    blend f g e₁ lam η = g η := by
  sorry

/-- "g > f on (e₁, e₁+lam]" from `f(e₁) = g(e₁)` and `g' > f'` there (sm-3:4093-4095) -/
theorem sep_of_deriv {f g : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) {e₁ lam : ℝ} (hlam : 0 < lam)
    (h0 : f e₁ = g e₁) (hd : ∀ η ∈ Ioc e₁ (e₁ + lam), deriv f η < deriv g η) :
    ∀ η ∈ Ioc e₁ (e₁ + lam), f η < g η := by
  sorry

/-- "(2) No tangent of the collar equals u, and no smallness condition is needed": pointwise
`h' ≥ (1−φ_lam) f' + φ_lam g' ≥ f' > 0` (sm-3:4117-4133) -/
theorem deriv_blend_ge {f g : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) {e₁ lam : ℝ} (hlam : 0 < lam)
    (h0 : f e₁ = g e₁) (hpos : ∀ η ∈ Icc e₁ (e₁ + lam), 0 < deriv f η)
    (hd : ∀ η ∈ Ioc e₁ (e₁ + lam), deriv f η < deriv g η) :
    ∀ η ∈ Icc e₁ (e₁ + lam), deriv f η ≤ deriv (blend f g e₁ lam) η := by
  sorry

/-- "(3) … Pointwise f ≤ h ≤ g on the collar" (sm-3:4143-4144) -/
theorem blend_between {f g : ℝ → ℝ} {e₁ lam : ℝ} (hlam : 0 < lam) {η : ℝ} (hη : η ∈ Icc e₁ (e₁ + lam))
    (hfg : f η ≤ g η) : f η ≤ blend f g e₁ lam η ∧ blend f g e₁ lam η ≤ g η := by
  sorry

/-- the collar at `p₊`, "with its own signs printed" (sm-3:4166-4212): the mirrored blend
`h = (1 − χ) g + χ f` with `g' < m₊ < f' < 0` gives `h' ≤ f' < 0` -/
theorem deriv_blend_le {f g : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) {e₂ lam : ℝ} (hlam : 0 < lam)
    (h0 : f e₂ = g e₂) (hneg : ∀ η ∈ Icc (e₂ - lam) e₂, deriv f η < 0)
    (hd : ∀ η ∈ Ico (e₂ - lam) e₂, deriv g η < deriv f η) :
    ∀ η ∈ Icc (e₂ - lam) e₂, deriv (blend g f (e₂ - lam) lam) η ≤ deriv f η := by
  sorry

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
  sorry

/-- Arc replacement in a window (the accepted `rot_sub_rot_of_replace`, seam moved to `s₁`): two
closed `C¹` regular curves that agree off the window `(s₁, s₂)` (mod 1), with tangent lifts on the
window, have `rot F' − rot F = (Δ' − Δ)/2π` -/
theorem rot_sub_rot_of_window (F F' : SmoothRegularLoop) {s₁ s₂ : ℝ} (hs : s₁ < s₂) (hs1 : s₂ - s₁ < 1)
    (hsame : ∀ t : ℝ, OffWindow s₁ s₂ t → F'.γ t = F.γ t) {θ θ' : ℝ → ℝ}
    (hθ : IsLiftOn (fun t => normalize (deriv F.γ t)) θ s₁ s₂)
    (hθ' : IsLiftOn (fun t => normalize (deriv F'.γ t)) θ' s₁ s₂) :
    F'.toClosedC1Curve.rot - F.toClosedC1Curve.rot = ((θ' s₂ - θ' s₁) - (θ s₂ - θ s₁)) / (2 * Real.pi) := by
  sorry

/-! ### Unit K — the polygonal kink: location and Reidemeister-I insertion (the accepted `RIData`) -/

/-- a location exists: the gap of `D`'s traversal circle between the occurrences around `t₀`
contains an interior edge point off every other edge -/
theorem exists_kinkLocation : Nonempty (KinkLocation S) := by
  sorry

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
