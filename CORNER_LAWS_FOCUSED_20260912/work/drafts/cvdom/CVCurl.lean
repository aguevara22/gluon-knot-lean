import SM.Curl
import CV.Rounding

/-! # CV lane, row 154 — CV:lem:curl, "exact negative-curl replacement"

Source: reference/R/CV/d3_floor.tex, `lem:curl` (statement lines 304–323: scoping sentence 305, the
objects and hypotheses 306–311, the existence sentence 311–313, clause (i) 315–317, clause (ii) 318–319,
clause (iii) 320, clause (iv) 321; printed proof 324–701, with the four conclusions read separately at
642–671 and "the polynomial conclusion, without a knot-category detour" at 673–701; the authorship remark
`rem:curlauthor` 703–733).  Consumer: CV:thm:carrierfloor (C) (d3:885–912; the curl is applied at
899–912 "Apply Lemma lem:curl at each of the R downward vertical tangencies … the R discs are disjoint
and each replacement leaves the others intact … P_T = P_{D̄}, T has no downward vertical tangency, and it
has writhe w(T) = −w − R … the R new [crossings are negative] by Lemma lem:curl(iii)").  Input class:
the rounded curve and its carried diagram of CV:lem:rounding (row 152, `CV.rounding`, d3:39–40 "a
diagram D_ε carried by it"), after the crossing switch of (C) (d3:897–899).

SM counterpart: `SM.cf_lem_curl : SM.CurlData` (work/lean/SM/Curl.lean, ACCEPTED 2026-09-14; fixed
statement work/drafts/curl/Statements_FINAL.lean + PORT_REPORT.md §3; sm-3-statesum.tex:3870–3891,
`\status` 3890 "transcribed from CV lem:curl (C032)").  CV's hypotheses (d3:306–311) are SM's
(sm-3:3873–3878) word for word; CV's existence sentence (311–313) is SM's (3878–3880) word for word;
CV's clauses (i)–(iv) (315–321) are SM's (3882–3888) word for word.  The two statements differ in exactly
one place: the scoping sentence — CV 305 "Here rot is as in Definition def:rot" (one definition,
d1_setup.tex:726–786, for polygons by the `ε_i` ray formula and for closed `C¹` regular curves by
`rot(γ) = tw(T_γ)`), SM 3871–3872 "as in Lemma lem:rot for polygons and Definition cf:def-turning for
closed C¹ regular curves".  In this lemma every `rot` is a curve `rot` (`F`, `F'` are `C^∞` immersed
circles; no polygon is named), and the curve notion is one definition under two names (decision F6,
CV/RotationSmooth.lean:57: `CV.rotCurve γ = γ.rot` by `rfl`).  So the CV row is the SM row on the same
objects, with (iv) read through `CV.rotCurve`; there is no polygon bridge to build (contrast row 152,
whose binder was CV's labelled polygon).  SM's `\status` line has no CV counterpart; CV's authorship
remark 703–733 is commentary (see "Readings" below).

Written 2026-09-14 by a Claude Code architect-prover subagent of the pod executor.  Checked with
`cd work/lean && lake env lean ../drafts/cvdom/CVCurl.lean` against the built library modules
`SM/Curl.olean` (2026-09-14 08:24 UTC) and `CV/Rounding.olean`.  No incomplete proofs; axioms of
`CV.curl`: `propext`, `Classical.choice`, `Quot.sound`, `SM.lp_lm` (the policy axiom of every consumer of
the accepted polynomial `P`, through `SM.cf_lem_curl`); the corollary `curl_homfly_eq` (the polynomial in
CV:def:homfly's letter `homfly`) adds `SM.lit_homfly` through `P_eq_homfly`.

## The printed statement (d3_floor.tex:305–321)

"Here rot is as in Definition def:rot.  Let F be a connected C^∞ immersed circle in the plane — one
component, with finitely many transverse double points and no triple points — given with an oriented
diagram, and let p be a point of F at which the tangent points in a fixed direction u, isolated among
such points, lying in an embedded arc of F that contains no double point and along which the tangent
turns strictly positively.  Then F may be modified inside a disc Δ meeting the rest of the diagram only
in that arc, so that the resulting diagram F'
(i) is again such an oriented diagram, satisfies P_{F'}(a,z) = P_F(a,z), and has the same double points
outside Δ, with the same signs;
(ii) has no point of Δ at which the tangent equals u, and exactly one at which it equals −u;
(iii) has exactly one double point inside Δ, and it is negative;
(iv) satisfies rot(F') = rot(F) − 1 and w(F') = w(F) − 1."

## Printed notion → Lean (CV's printed binder; the SM model of the accepted twin)

* "a connected C^∞ immersed circle in the plane — one component" (306–307): `F : SmoothRegularLoop`
  (the accepted `C^∞` 1-periodic regular class of SM/Rounding.lean §3, already CV's vocabulary for the
  rounded curve `L_ε` of row 152).
* "with finitely many transverse double points and no triple points — given with an oriented diagram"
  (307–308): `D : Diagram` with `carried : RecordCarried F D` — CV:def:record (d1_setup.tex:522–531,
  "the record of a link diagram … its traversal circle, the preimages of its crossings, the crossing
  correspondence, and the over/under and sign data") realised on the traversal circle of `F`: the
  occurrences of `D` at parameters `τ v` of `F`, twins at one point, the double points of `F` exactly the
  twin pairs, transverse, in `D`'s cyclic order, over/under by sign.  "Finitely many" and "no triple
  points" are theorems of the record (`CurlSite.doublePoints_finite`, `RecordCarried.no_triple`).  This
  is the record-level class of the accepted twin (FR-C1), which CV's own definition of a record is:
  CV:def:record names marked points on a circle and their data, not points of the plane.  The output of
  row 152 (`Carried`, which also ties each occurrence to the polygon's crossing point) enters through
  `Carried.toRecordCarried` (`CurlSite.ofCarried`).
* "a point p of F at which the tangent points in a fixed direction u" (308–309): `t₀ : ℝ`,
  `p = F.γ t₀` (`CurlSite.p`), `u : Plane`, `normalize (deriv F.γ t₀) = u`.
* "lying in an embedded arc of F that contains no double point" (309–310): the parameter interval
  `[α, β]` around `t₀`, shorter than the period (`β − α < 1`), `InjOn F.γ (Icc α β)`, no occurrence
  parameter `τ v` (mod 1) in `[α, β]`.
* "along which the tangent turns strictly positively" (310–311): a tangent-angle lift `θ` of `T = F'/|F'|`
  on `[α, β]` (the accepted `IsLiftOn`, CV:def:rot's "tangent-angle lift", d1_setup.tex:767–771) that is
  strictly increasing.
* "isolated among such points" (309): `p` is the only point of the arc with tangent `u`.
* "F may be modified inside a disc Δ meeting the rest of the diagram only in that arc, so that the
  resulting diagram F' …" (311–313): `SM.CurlWitness S.toSM Δ` — the accepted witness of the twin: `F'`
  equal to `F`, with its velocity, outside a parameter window `(s₁, s₂) ⊆ [α, β]` (mod 1), the window
  images inside `Δ`; `IsDisc Δ` (the accepted clean-disc vocabulary), `p ∈ interior Δ`, every point of
  `F` in `Δ` traversed on the arc; the diagram changes by one accepted Reidemeister-I move `RI D D'`.  The
  disc is existential as printed and may be taken inside any preassigned neighbourhood `Δ₀` of `p`
  (the proof's "the disc is fixed first and the cuts afterwards", d3:456–459; what the consumer (C) needs
  at 899–905 for "the R discs are disjoint").
* (i) "is again such an oriented diagram" (315): `F' : SmoothRegularLoop`, `D' : Diagram`,
  `RecordCarried F' D'`; "P_{F'}(a,z) = P_F(a,z)" (316): `P D' = P D` for the accepted polynomial of a
  diagram (`SM.P`, = CV:def:homfly's `homfly` by `P_eq_homfly`; `curl_homfly_eq`); "the same double
  points outside Δ, with the same signs" (316–317): `doublePoints F'.γ \ Δ = doublePoints F.γ \ Δ`, a
  bijection `old` of the crossings of `D` with those of `D'` other than the kink, realised by `F'`/`F` at
  the same points of the plane, with the same polygonal crossing points and the same signs.
* (ii) (318–319): no parameter with `F'.γ t ∈ Δ` has unit tangent `u`; exactly one parameter of the
  fundamental period has `F'.γ t ∈ Δ` and unit tangent `−u`.
* (iii) (320): the kink crossing of `D'` is realised in `Δ`, every double point of `F'` in `Δ` is that
  point, and its sign is `−1` (polygonal and smooth).
* (iv) (321): `rotCurve F'.toClosedC1Curve = rotCurve F.toClosedC1Curve − 1` (CV:def:rot for curves,
  d1_setup.tex:775–780, `CV.rotCurve`) and `D'.writhe = D.writhe − 1` (with the smooth writhe
  `smoothWrithe`, the sum of the smooth signs, dropping by one as well).

Row declaration: `CV.curl : CV.CVCurlData`, one field per printed sentence / clause, on the CV site
`CV.CurlSite` (the printed binder, d3:306–311) transported to the accepted twin by `CurlSite.toSM`
(a field-for-field repackaging; `ofSM_toSM`, `toSM_ofSM` are `rfl`). -/

namespace CV

open SM hiding CurlSite CurlData
open SM.Link
open scoped ContDiff

noncomputable section
open Classical

/-! ## 1. The site: CV's printed binder (d3:306–311) -/

/-- The objects and hypotheses of CV:lem:curl (d3:306–311): "Let F be a connected C^∞ immersed circle
in the plane — one component, with finitely many transverse double points and no triple points — given
with an oriented diagram, and let p be a point of F at which the tangent points in a fixed direction u,
isolated among such points, lying in an embedded arc of F that contains no double point and along which
the tangent turns strictly positively."  The arc is the parameter interval `[α, β]` (shorter than the
period), `p = F.γ t₀`; the oriented diagram is CV:def:record's record of `D` carried on the traversal
circle of `F` (`RecordCarried`).  Word for word the hypotheses of the accepted twin `SM.CurlSite`
(sm-3:3873–3878); `toSM` is the transport. -/
structure CurlSite where
  /-- "a connected C^∞ immersed circle in the plane — one component" (306–307) -/
  F : SmoothRegularLoop
  /-- "given with an oriented diagram" (308) … -/
  D : Diagram
  /-- … whose record (CV:def:record) `F` carries — "with finitely many transverse double points and no
  triple points" (307) are theorems of the record -/
  carried : RecordCarried F D
  /-- "a fixed direction u" (309) -/
  u : Plane
  /-- the parameter of "a point p of F" (308) … -/
  t₀ : ℝ
  /-- … "at which the tangent points in a fixed direction u" (308–309) -/
  tangent_at : normalize (deriv F.γ t₀) = u
  /-- "lying in an embedded arc of F" (309–310): the parameter interval `[α, β]` around `t₀`, shorter
  than the period … -/
  α : ℝ
  β : ℝ
  α_lt : α < t₀
  lt_β : t₀ < β
  short : β - α < 1
  /-- … on which the curve is embedded -/
  embedded : Set.InjOn F.γ (Set.Icc α β)
  /-- "that contains no double point" (310): no crossing occurrence is traversed on the arc -/
  no_double : ∀ v : D.Γ.Visit, ∀ n : ℤ, carried.τ v + n ∉ Set.Icc α β
  /-- "along which the tangent turns strictly positively" (310–311): a tangent-angle lift on the arc
  (CV:def:rot, d1_setup.tex:767–771) … -/
  θ : ℝ → ℝ
  lift : IsLiftOn (fun t => normalize (deriv F.γ t)) θ α β
  /-- … strictly increasing -/
  turns_pos : StrictMonoOn θ (Set.Icc α β)
  /-- "isolated among such points" (309): `p` is the only point of the arc with tangent `u` -/
  isolated : ∀ t ∈ Set.Icc α β, normalize (deriv F.γ t) = u → t = t₀

namespace CurlSite

variable (S : CurlSite)

/-- the point `p` (308) -/
def p : Plane := S.F.γ S.t₀

/-- the unit tangent `T = F'/|F'|` (CV:def:rot, d1_setup.tex:778) -/
def T : ℝ → Plane := fun t => normalize (deriv S.F.γ t)

/-- The transport of the CV site to the accepted twin's site (sm-3:3873–3878): the same objects,
field for field. -/
def toSM : SM.CurlSite :=
  ⟨S.F, S.D, S.carried, S.u, S.t₀, S.tangent_at, S.α, S.β, S.α_lt, S.lt_β, S.short, S.embedded,
    S.no_double, S.θ, S.lift, S.turns_pos, S.isolated⟩

/-- The CV site of an accepted twin's site. -/
def ofSM (S' : SM.CurlSite) : CurlSite :=
  ⟨S'.F, S'.D, S'.carried, S'.u, S'.t₀, S'.tangent_at, S'.α, S'.β, S'.α_lt, S'.lt_β, S'.short,
    S'.embedded, S'.no_double, S'.θ, S'.lift, S'.turns_pos, S'.isolated⟩

@[simp] theorem toSM_F : S.toSM.F = S.F := rfl
@[simp] theorem toSM_D : S.toSM.D = S.D := rfl
@[simp] theorem toSM_carried : S.toSM.carried = S.carried := rfl
@[simp] theorem toSM_u : S.toSM.u = S.u := rfl
@[simp] theorem toSM_t₀ : S.toSM.t₀ = S.t₀ := rfl
@[simp] theorem toSM_α : S.toSM.α = S.α := rfl
@[simp] theorem toSM_β : S.toSM.β = S.β := rfl
@[simp] theorem toSM_θ : S.toSM.θ = S.θ := rfl
@[simp] theorem toSM_p : S.toSM.p = S.p := rfl
@[simp] theorem toSM_T : S.toSM.T = S.T := rfl

/-- the transport is a repackaging: both round trips are the identity -/
@[simp] theorem ofSM_toSM : ofSM S.toSM = S := rfl
@[simp] theorem toSM_ofSM (S' : SM.CurlSite) : (ofSM S').toSM = S' := rfl

theorem u_unit : euclideanLength S.u = 1 := S.toSM.u_unit

/-- "one component" (307) -/
theorem one : S.D.Γ.c = 1 := S.carried.one

/-- "the tangent equals u" only at `p`: the printed isolation (309), on the arc -/
theorem T_eq_u_iff {t : ℝ} (ht : t ∈ Set.Icc S.α S.β) : S.T t = S.u ↔ t = S.t₀ :=
  S.toSM.T_eq_u_iff ht

/-- "finitely many transverse double points" (307): the double points of `F` are the finitely many
realised crossings of the record (`RecordCarried.doublePoints_eq`); transversality is the record's
`transverse` field. -/
theorem doublePoints_finite : (SmoothRegularLoop.doublePoints S.F.γ).Finite := by
  rw [S.carried.doublePoints_eq]
  have : {q : Plane | ∃ v : S.D.Γ.Visit, q = S.F.γ (S.carried.τ v)} =
      Set.range (fun v : S.D.Γ.Visit => S.F.γ (S.carried.τ v)) := by
    ext q; simp [eq_comm]
  rw [this]
  exact Set.finite_range _

/-- "no triple points" (307): a theorem of the record -/
theorem no_triple {r s t : ℝ} (hr : r ∈ Set.Ico (0 : ℝ) 1) (hs : s ∈ Set.Ico (0 : ℝ) 1)
    (ht : t ∈ Set.Ico (0 : ℝ) 1) (hrs : r ≠ s) (hrt : r ≠ t) (hrs' : S.F.γ r = S.F.γ s)
    (hrt' : S.F.γ r = S.F.γ t) : s = t :=
  S.carried.no_triple hr hs ht hrs hrt hrs' hrt'

/-- The site of the consumer CV:thm:carrierfloor (C) (d3:885–905): the output of CV:lem:rounding — a
`Carried` record, here the rounded curve `L_ε` carrying its diagram (`CV.rounding`, field
`smooth_regular_carried`; after the crossing switch of 897–899) — is a curl site through the accepted
`Carried.toRecordCarried`; the hypotheses are those of `CurlSite` with `τ` the parameters of the
`Carried` record.  Its transport is the accepted twin's `SM.CurlSite.ofCarried` (`ofCarried_toSM`). -/
def ofCarried (F : SmoothRegularLoop) (D : Diagram) (c : Carried F D) (u : Plane)
    (t₀ α β : ℝ) (θ : ℝ → ℝ) (tangent_at : normalize (deriv F.γ t₀) = u) (α_lt : α < t₀)
    (lt_β : t₀ < β) (short : β - α < 1) (embedded : Set.InjOn F.γ (Set.Icc α β))
    (no_double : ∀ v : D.Γ.Visit, ∀ n : ℤ, c.τ v + n ∉ Set.Icc α β)
    (lift : IsLiftOn (fun t => normalize (deriv F.γ t)) θ α β) (turns_pos : StrictMonoOn θ (Set.Icc α β))
    (isolated : ∀ t ∈ Set.Icc α β, normalize (deriv F.γ t) = u → t = t₀) : CurlSite :=
  ⟨F, D, c.toRecordCarried, u, t₀, tangent_at, α, β, α_lt, lt_β, short, embedded, no_double, θ, lift,
    turns_pos, isolated⟩

theorem ofCarried_toSM (F : SmoothRegularLoop) (D : Diagram) (c : Carried F D) (u : Plane)
    (t₀ α β : ℝ) (θ : ℝ → ℝ) (tangent_at : normalize (deriv F.γ t₀) = u) (α_lt : α < t₀)
    (lt_β : t₀ < β) (short : β - α < 1) (embedded : Set.InjOn F.γ (Set.Icc α β))
    (no_double : ∀ v : D.Γ.Visit, ∀ n : ℤ, c.τ v + n ∉ Set.Icc α β)
    (lift : IsLiftOn (fun t => normalize (deriv F.γ t)) θ α β) (turns_pos : StrictMonoOn θ (Set.Icc α β))
    (isolated : ∀ t ∈ Set.Icc α β, normalize (deriv F.γ t) = u → t = t₀) :
    (ofCarried F D c u t₀ α β θ tangent_at α_lt lt_β short embedded no_double lift turns_pos
      isolated).toSM =
    SM.CurlSite.ofCarried F D c u t₀ α β θ tangent_at α_lt lt_β short embedded no_double lift
      turns_pos isolated := rfl

end CurlSite

/-! ## 2. The witness, and the two clauses read in CV's own vocabulary

"Then F may be modified inside a disc Δ meeting the rest of the diagram only in that arc, so that the
resulting diagram F' [(i)–(iv)]" (d3:311–321): the witness at the disc `Δ` is the accepted twin's
`SM.CurlWitness S.toSM Δ` — the modified curve `F'`, its diagram `D'` with the record `F'` carries, the
modification window `[s₁, s₂] ⊆ [α, β]`, the kink crossing, the correspondence `old` of the other
crossings, and one field per printed sub-clause.  Its field list is the fixed content of (i)–(iv); the
CV bundle below re-reads each printed clause on it.  Two readings are CV's own: (i)'s polynomial in
CV:def:homfly's letter, and (iv)'s `rot` as CV:def:rot. -/

section Witness

variable {S : CurlSite} {Δ : Set Plane} (W : SM.CurlWitness S.toSM Δ)

/-- (iv) "rot(F') = rot(F) − 1" (d3:321), "Here rot is as in Definition def:rot" (305): the rotation
`rot(γ) = tw(T_γ)` of the closed `C¹` regular curve (`CV.rotCurve`, d1_setup.tex:775–780), on both sides.
`CV.rotCurve` is the accepted twin's `ClosedC1Curve.rot` by definition (decision F6), so this is the
witness field `rot_eq`. -/
theorem rotCurve_eq_sub_one : rotCurve W.curve = rotCurve S.F.toClosedC1Curve - 1 := W.rot_eq

/-- (i) "P_{F'}(a,z) = P_F(a,z)" (d3:316) in the letter of CV:def:homfly (`homfly`, the HOMFLY–PT
polynomial of lit:homfly; `CV.homfly_definition`): from the witness field `poly_eq` on the accepted
polynomial `P` and `P_eq_homfly` (lp:core).  Axioms: those of `curl` plus `SM.lit_homfly`. -/
theorem curl_homfly_eq : homfly W.D' = homfly S.D := by
  rw [← P_eq_homfly, ← P_eq_homfly]; exact W.poly_eq

end Witness

/-! ## 3. The row bundle: one field per printed sentence / clause -/

/-- CV:lem:curl (d3_floor.tex:304–323), one field per printed sentence or clause, on CV's printed
binder `CurlSite` (306–311).  The existence sentence (`exists_curl`) carries the theorem, in the form
the proof establishes ("the disc is fixed first and the cuts afterwards", d3:456–459) and the consumer
CV:thm:carrierfloor (C) reads (899–905: the curl discs lie in the pairwise disjoint rounding discs, "so
the R discs are disjoint and each replacement leaves the others intact"): the disc `Δ` may be taken
inside any preassigned neighbourhood `Δ₀` of `p`; the printed bare existence is `exists_curl'`.  The
clause fields state how each printed clause reads on a witness (projections of the accepted
`SM.CurlWitness` on the transported site), with (iv)'s `rot` in CV's vocabulary (`rotCurve`). -/
structure CVCurlData : Prop where
  /-- "Then F may be modified inside a disc Δ meeting the rest of the diagram only in that arc, so
  that the resulting diagram F' [has (i)–(iv)]" (d3:311–313) — with the disc inside any preassigned
  neighbourhood `Δ₀` of `p`. -/
  exists_curl : ∀ (S : CurlSite) (Δ₀ : Set Plane), S.p ∈ interior Δ₀ →
    ∃ Δ : Set Plane, Δ ⊆ Δ₀ ∧ Nonempty (SM.CurlWitness S.toSM Δ)
  /-- the printed existence sentence as printed (no preassigned neighbourhood) -/
  exists_curl' : ∀ S : CurlSite, ∃ Δ : Set Plane, Nonempty (SM.CurlWitness S.toSM Δ)
  /-- "a disc Δ meeting the rest of the diagram only in that arc" (311–312), the modification inside
  it: `Δ` is a disc about `p`, every point of `F` in `Δ` is traversed on the arc, `F'` is `F` — with its
  velocity — off the modification window, and the modified arc lies in `Δ`. -/
  disc : ∀ (S : CurlSite) (Δ : Set Plane) (W : SM.CurlWitness S.toSM Δ),
    IsDisc Δ ∧ S.p ∈ interior Δ ∧ (∀ t : ℝ, S.F.γ t ∈ Δ → ∃ n : ℤ, t + n ∈ Set.Icc S.α S.β) ∧
    (∀ t : ℝ, (∀ n : ℤ, t + n ∉ Set.Ioo W.s₁ W.s₂) →
      W.F'.γ t = S.F.γ t ∧ deriv W.F'.γ t = deriv S.F.γ t) ∧
    (∀ t ∈ Set.Icc W.s₁ W.s₂, W.F'.γ t ∈ Δ)
  /-- (i) "is again such an oriented diagram, satisfies P_{F'}(a,z) = P_F(a,z), and has the same
  double points outside Δ, with the same signs" (315–317): `F'` is a `C^∞` regular closed curve, one
  component, carrying the record of `D'`, which is `D` changed by one Reidemeister-I move; the accepted
  polynomial is unchanged (in CV:def:homfly's letter: `curl_homfly_eq`); the double points outside `Δ`
  are the same set; every old crossing corresponds to a crossing of `D'` other than the kink, realised
  by `F'` at the same point of the plane as before, at the same polygonal crossing point, with the same
  sign. -/
  i : ∀ (S : CurlSite) (Δ : Set Plane) (W : SM.CurlWitness S.toSM Δ),
    ContDiff ℝ ∞ W.F'.γ ∧ Function.Periodic W.F'.γ 1 ∧ (∀ t, deriv W.F'.γ t ≠ 0) ∧
    W.D'.Γ.c = 1 ∧ Nonempty (RecordCarried W.F' W.D') ∧ RI S.D W.D' ∧
    P W.D' = P S.D ∧
    SmoothRegularLoop.doublePoints W.F'.γ \ Δ = SmoothRegularLoop.doublePoints S.F.γ \ Δ ∧
    (∀ x : S.D.Γ.Crossing,
      W.F'.γ (W.carried'.τ (W.D'.overVisit (W.old x).1)) = S.F.γ (S.carried.τ (S.D.overVisit x)) ∧
      W.D'.Γ.crossingPoint (W.old x).1 = S.D.Γ.crossingPoint x ∧
      W.D'.sign (W.old x).1 = S.D.sign x)
  /-- (ii) "has no point of Δ at which the tangent equals u, and exactly one at which it equals −u"
  (318–319): no parameter with `F'(t) ∈ Δ` has unit tangent `u`; exactly one parameter of the
  fundamental period has `F'(t) ∈ Δ` and unit tangent `−u`. -/
  ii : ∀ (S : CurlSite) (Δ : Set Plane) (W : SM.CurlWitness S.toSM Δ),
    (∀ t, W.F'.γ t ∈ Δ → normalize (deriv W.F'.γ t) ≠ S.u) ∧
    (∃! t : ℝ, t ∈ Set.Ico (0 : ℝ) 1 ∧ W.F'.γ t ∈ Δ ∧ normalize (deriv W.F'.γ t) = -S.u)
  /-- (iii) "has exactly one double point inside Δ, and it is negative" (320): the kink crossing of
  `D'` is realised in `Δ`, every double point of `F'` in `Δ` is that point, and its sign is `−1` — the
  polygonal sign of `D'` and the smooth sign `sgn det(velocity_over, velocity_under)`. -/
  iii : ∀ (S : CurlSite) (Δ : Set Plane) (W : SM.CurlWitness S.toSM Δ),
    W.F'.γ (W.carried'.τ (W.D'.overVisit W.kink)) ∈ Δ ∧
    (∀ q ∈ SmoothRegularLoop.doublePoints W.F'.γ ∩ Δ,
      q = W.F'.γ (W.carried'.τ (W.D'.overVisit W.kink))) ∧
    W.D'.sign W.kink = -1 ∧ W.carried'.smoothSign W.kink = -1
  /-- (iv) "satisfies rot(F') = rot(F) − 1 and w(F') = w(F) − 1" (321), "Here rot is as in Definition
  def:rot" (305): `CV.rotCurve` of the closed `C¹` regular curves `F'` and `F`; the writhe of the
  carried diagram, and the smooth writhe (the sum of the smooth signs), both drop by one. -/
  iv : ∀ (S : CurlSite) (Δ : Set Plane) (W : SM.CurlWitness S.toSM Δ),
    rotCurve W.curve = rotCurve S.F.toClosedC1Curve - 1 ∧
    W.D'.writhe = S.D.writhe - 1 ∧ W.carried'.smoothWrithe = S.carried.smoothWrithe - 1

/-- CV:lem:curl, from the accepted twin `SM.cf_lem_curl` on the transported site `S.toSM`: every field
is the twin's field at `S.toSM` (the objects are the same, `toSM` being a repackaging), with (iv)'s
`rot` re-read as `CV.rotCurve` (`rotCurve_eq_sub_one`). -/
theorem curl : CVCurlData where
  exists_curl := fun S Δ₀ h₀ => SM.cf_lem_curl.exists_curl S.toSM Δ₀ h₀
  exists_curl' := fun S => SM.cf_lem_curl.exists_curl' S.toSM
  disc := fun S Δ W => SM.cf_lem_curl.disc S.toSM Δ W
  i := fun S Δ W => SM.cf_lem_curl.i S.toSM Δ W
  ii := fun S Δ W => SM.cf_lem_curl.ii S.toSM Δ W
  iii := fun S Δ W => SM.cf_lem_curl.iii S.toSM Δ W
  iv := fun _ _ W => ⟨rotCurve_eq_sub_one W, W.writhe_eq, W.smoothWrithe_eq⟩

/-! ## 4. The existence sentence in the consumer's form -/

/-- The existence sentence for a site given by a `Carried` record — the output of CV:lem:rounding
(`CV.rounding.smooth_regular_carried`), the form CV:thm:carrierfloor (C) starts from (d3:885–905) —
with the disc inside any preassigned neighbourhood of `p` (there: the rounding disc of the tangency's
corner, so that the `R` replacements have disjoint supports). -/
theorem curl_of_carried (F : SmoothRegularLoop) (D : Diagram) (c : Carried F D) (u : Plane)
    (t₀ α β : ℝ) (θ : ℝ → ℝ) (tangent_at : normalize (deriv F.γ t₀) = u) (α_lt : α < t₀)
    (lt_β : t₀ < β) (short : β - α < 1) (embedded : Set.InjOn F.γ (Set.Icc α β))
    (no_double : ∀ v : D.Γ.Visit, ∀ n : ℤ, c.τ v + n ∉ Set.Icc α β)
    (lift : IsLiftOn (fun t => normalize (deriv F.γ t)) θ α β) (turns_pos : StrictMonoOn θ (Set.Icc α β))
    (isolated : ∀ t ∈ Set.Icc α β, normalize (deriv F.γ t) = u → t = t₀)
    (Δ₀ : Set Plane) (h₀ : F.γ t₀ ∈ interior Δ₀) :
    ∃ Δ : Set Plane, Δ ⊆ Δ₀ ∧
      Nonempty (SM.CurlWitness (CurlSite.ofCarried F D c u t₀ α β θ tangent_at α_lt lt_β short
        embedded no_double lift turns_pos isolated).toSM Δ) :=
  curl.exists_curl _ Δ₀ h₀

/-- The next curl of the consumer's iteration (d3:899–905, "each replacement leaves the others
intact"): the output record `carried'` of a witness is a curl input again — the site of the second and
later curls is built from `W.F'`, `W.D'`, `W.carried'` directly (`RecordCarried` is the input class;
FR-C1), given a new tangency point with its arc.  This is the constructor of that site. -/
def CurlSite.next {S : CurlSite} {Δ : Set Plane} (W : SM.CurlWitness S.toSM Δ) (u : Plane)
    (t₀ α β : ℝ) (θ : ℝ → ℝ) (tangent_at : normalize (deriv W.F'.γ t₀) = u) (α_lt : α < t₀)
    (lt_β : t₀ < β) (short : β - α < 1) (embedded : Set.InjOn W.F'.γ (Set.Icc α β))
    (no_double : ∀ v : W.D'.Γ.Visit, ∀ n : ℤ, W.carried'.τ v + n ∉ Set.Icc α β)
    (lift : IsLiftOn (fun t => normalize (deriv W.F'.γ t)) θ α β)
    (turns_pos : StrictMonoOn θ (Set.Icc α β))
    (isolated : ∀ t ∈ Set.Icc α β, normalize (deriv W.F'.γ t) = u → t = t₀) : CurlSite :=
  ⟨W.F', W.D', W.carried', u, t₀, tangent_at, α, β, α_lt, lt_β, short, embedded, no_double, θ, lift,
    turns_pos, isolated⟩

end

end CV
