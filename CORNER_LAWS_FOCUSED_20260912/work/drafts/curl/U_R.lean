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
theorem r_planeDot_smul_left (r : ℝ) (a w : Plane) : planeDot (r • a) w = r * planeDot a w := by
  simp only [planeDot, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring
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
    rw [e, r_planeDot_add_left, r_planeDot_smul_left, r_planeDot_fitA, hvv, huv, hz]
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

/-- the cuts and the fit exist at every disc about `p` (Unit G: `exists_cuts` with the cuts close to
`t₀`, `endpoint_tangent` for `a, b, c, d`, `η_strictMonoOn` for `ℓ > 0`, continuity of `F` for the removed
arc, and the diameter bound of `inserted_arc_props` with `x → 0`, `ℓ → 0` for the inserted arc) -/
theorem exists_cutFit {α' β' : ℝ} (hα : S.α ≤ α') (hα' : α' < S.t₀) (hβ' : S.t₀ < β') (hβ : β' ≤ S.β)
    (hθ : ∀ t ∈ Icc α' β', |θrel S t| < Real.pi / 2) {r : ℝ} (hr : 0 < r) :
    Nonempty (CutFit S α' β' r) := by
  sorry


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
    rw [hdG, r_planeDot_smul_left, r_planeDot_smul_left, r_planeDot_fitA, hvv, huv]; ring
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
  · rw [hdG, hq₀, r_planeDot_smul_left, r_planeDot_smul_left, r_planeDot_fitA, hvu, huu]
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
        rw [hdG, hq₀, r_planeDot_smul_left, r_planeDot_smul_left, r_planeDot_fitA, hvu, huu]
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
  unfold normalize; exact r_planeDot_smul_left _ _ _

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
  · rw [hFT, cf.T_minus, r_planeDot_smul_left, r_planeDot_add_left, r_planeDot_smul_left,
      r_planeDot_smul_left, hvv, huv]
    nlinarith [mul_pos hL₁ cf.a_pos]
  · rw [hFT, cf.T_minus, r_planeDot_smul_left, r_planeDot_add_left, r_planeDot_smul_left,
      r_planeDot_smul_left, hvu, huu]
    nlinarith [mul_pos hL₁ cf.b_pos]
  · rw [hFT, cf.T_plus, r_planeDot_smul_left, r_planeDot_add_left, r_planeDot_neg_left,
      r_planeDot_smul_left, r_planeDot_smul_left, hvv, huv]
    nlinarith [mul_pos hL₂ cf.c_pos]
  · rw [hFT, cf.T_plus, r_planeDot_smul_left, r_planeDot_add_left, r_planeDot_neg_left,
      r_planeDot_smul_left, r_planeDot_smul_left, hvu, huu]
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
    · exact ξ_strictMonoOn S hα hβ hθ ⟨cf.α'_le, cf.s₁_lt.le⟩
        ⟨by linarith [cf.α'_le, hs'.1], h⟩ hs'.1
    · rw [cf.ξ_eq]
      exact ξ_strictAntiOn S hα hβ hθ ⟨h.le, by linarith [cf.le_β', hs'.2]⟩
        ⟨cf.lt_s₂.le, cf.le_β'⟩ hs'.2
  have hξN : ∀ s ∈ Ioo cf.s₁ cf.s₂, ξ S cf.s₁ < planeDot (N s - S.p) (vDir S) := by
    intro s hs'
    obtain ⟨θc, hθc, hNs'⟩ := hNconv s
    have h1 : ξ S cf.s₁ < planeDot (S.F.γ s - S.p) (vDir S) := hξF s hs'
    have h2 := hGexc s hs'
    have e : N s - S.p = (S.F.γ s - S.p) + θc • ((G s - S.p) - (S.F.γ s - S.p)) := by
      rw [hNs', sub_sub_sub_cancel_right]; abel
    rw [e, r_planeDot_add_left, r_planeDot_smul_left,
      r_planeDot_sub_left (G s - S.p) (S.F.γ s - S.p) (vDir S)]
    exact r_convex_gt h1 h2 hθc
  intro s hs' t ht hN
  by_cases hin : S.F.γ t ∈ disc S r
  · obtain ⟨n, hn⟩ := hmeets t hin
    have hnot := ht n
    have hper : S.F.γ (t + n) = S.F.γ t := S.F.eq_add_int n t
    have hle : ξ S (t + n) ≤ ξ S cf.s₁ := by
      rcases le_or_gt (t + n) cf.s₁ with h | h
      · exact (ξ_strictMonoOn S hα hβ hθ).monotoneOn ⟨hn.1, by linarith [cf.s₁_lt]⟩
          ⟨cf.α'_le, cf.s₁_lt.le⟩ h
      · have h2 : cf.s₂ ≤ t + n := by
          by_contra h2; push Not at h2; exact hnot ⟨h, h2⟩
        rw [cf.ξ_eq]
        exact (ξ_strictAntiOn S hα hβ hθ).antitoneOn ⟨cf.lt_s₂.le, cf.le_β'⟩
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
