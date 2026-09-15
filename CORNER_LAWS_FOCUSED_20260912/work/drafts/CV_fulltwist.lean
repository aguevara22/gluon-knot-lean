import CV.Axioms
import CV.Rotation

/-! # CV lane, row 159 — CV:lem:fulltwist, "the abstract full-twist triple"

Source: reference/R/CV/d6_vertexedge.tex, `lem:fulltwist` (statement lines 1981–2031, the plan's row range being 1981–2040; printed proof
2032–2045; the preamble 1971–1979 and `rem:branchneutral` 2047–2056 are commentary).  Plan entry:
work/reports/cv-lane-plan-20260913.md §159.  Consumes CV:ax:homfly, which this project derives as
`CV.ax_homfly` (work/lean/CV/Axioms.lean), and CV:def:rot, built as `CV.rot` / `CV.rotAbs`
(work/lean/CV/Rotation.lean).  Written 2026-09-14 by a Claude Code prover subagent; checked with
`lake env lean` (sorry-free; the only non-standard axioms are those of `CV.ax_homfly`:
`SM.lit_homfly`, `SM.lp_lm`, `SM.lp_lm_uniqueness`).

## The printed statement (d6_vertexedge.tex:1981–2031)

"Let D_L, D_H, D_A be oriented diagrams and let q be a positive crossing of D_H such that
(T1) the oriented smoothing of D_H at q is D_A;
(T2) switching q in D_H gives a diagram carried to D_L by oriented Reidemeister-II moves.
[…] For any oriented diagram D — any number of components — put F_D = P_D, the HOMFLY–PT polynomial
of the link it presents (Axiom ax:homfly).  For a diagram D carried by a single closed plane curve
Γ_D, and only for such a diagram, put d(D) = 1 − w(D) − R(Γ_D), Ω(D) = [a^{d(D)} z^0] F_D, with w(D)
the writhe and R(Γ_D) = |rot(Γ_D)| the absolute rotation of that curve.  […] Abbreviate F_ν = F_{D_ν}
for ν ∈ {L, H, A}, and d_ν = d(D_ν), Ω_ν = Ω(D_ν) for ν ∈ {L, H} only.  […] Then
    F_H = a^{−2} F_L + a^{−1} z F_A.
If moreover d_H = d_L − 2, then
    Ω_H − Ω_L = [a^{d_L − 1} z^{−1}] F_A."

The lemma is an identity about THREE diagrams related at ONE crossing `q` (rem:branchneutral 2048–2049: "it is
an identity about three oriented diagrams related by one crossing").  The words "full twist" name
the application (lem:triplebridge: the two crossings of a twisted pair, `q` one of them, whose switch
creates an RII bigon whose deletion gives D_L); nothing about a second crossing or a "twisted pair"
is part of THIS statement, so none is rendered here.

## Notation map (every reading recorded)

* "oriented diagram": `Diagram` (SM/LinkDiagram.lean — polygonal oriented link diagrams; every
  `Diagram` is oriented).  "any number of components": no hypothesis on `componentCount`.
* "a positive crossing q of D_H": `q : D_H.Γ.Crossing` with `D_H.IsPositive q` (def:positive-lift,
  `det(u_o,u_u) > 0`).
* (T1) "the oriented smoothing of D_H at q is D_A": `IsOrientedSmoothing D_H q D_A` (SM/LinkMoves.lean;
  relational: D_A is a diagram obtained by the disc-local oriented reconnection at `q`).
* (T2) "switching q in D_H gives a diagram carried to D_L by oriented Reidemeister-II moves":
  `Relation.ReflTransGen RII (D_H.switch q) D_L` — `D_H.switch q` is the accepted switch (over and
  under strands exchanged at `q`), and "carried by RII moves" is a finite (possibly empty) sequence of
  accepted `RII` moves.  The plan (§159) wrote `Relation.EqvGen RII`; since `RII` is symmetric
  (`RII.symm`) the two closures coincide (`reflTransGen_RII_iff_eqvGen` below), so the two readings
  are the same statement.  All accepted `RII` moves are on oriented diagrams, so "oriented" is
  automatic.
* "F_D = P_D, the HOMFLY–PT polynomial (Axiom ax:homfly)": `homfly D` (SM/LinkInterfaces.lean, the map
  `CV.ax_homfly` is about).  `F` is a renaming, not a new operation, so no definition is made for it;
  the displays are stated with `homfly` directly.
* "a diagram D carried by a single closed plane curve Γ_D": `D.componentCount = 1`; `Γ_D` is the
  polygon of the unique component, `curveOf D hD` (`(D.Γ.comp i).P` for the unique `i : Fin D.Γ.c`).
* "w(D) the writhe": `D.writhe` (sum of crossing signs, def:positive-lift).
* "R(Γ_D) = |rot(Γ_D)| the absolute rotation of that curve (Definition def:rot)": CV's own def:rot
  (d1_setup.tex:726–787), built as `CV.rot` with `R(L) = |rot(L)|` = `CV.rotAbs`; here `absRot D hD =
  rotAbs (curveOf D hD) _`, the regularity of the component polygon being supplied by the diagram
  (`D.generic.regular`, through `CV.regular_iff_sm`).  (`rotAbs_cast_real` in CV/RotationSmooth.lean
  identifies it with SM's `polygonR = |rotationNumber|`, the plan's suggested rendering.)
* "d(D) = 1 − w(D) − R(Γ_D)": `d D hD : ℤ`; "Ω(D) = [a^{d(D)} z^0] F_D": `Omega D hD = coeffAt (d D hD) 0
  (homfly D)`.  Both take the one-component hypothesis `hD` as an argument: "and only for such a
  diagram" — they are not defined at `D_A`, and the statement never applies them there.
* "[a^{d_L−1} z^{−1}] F_A": `coeffAt (d D_L hL - 1) (-1) (homfly D_A)` (SM/LinkLaurentRing.lean).
* "a^{−2} F_L + a^{−1} z F_A": `R.aInv ^ 2 * homfly D_L + R.aInv * R.z * homfly D_A`.

## What is NOT a clause

The sentences about earlier revisions (2005–2007, 2016–2020), the sentence "The two bindings agree
wherever both apply, that definition [def:markeddata] computing d_ν and Ω_ν from these same grouped
diagrams" (2020–2022; def:markeddata is another row, not formalized here), and the remark that D_A
enters only through F_A and the coefficient (2009–2016) are commentary, not clauses.
The abbreviations F_ν, d_ν, Ω_ν are notation.

## Row declaration

`CV.fulltwist : CV.FullTwistData`, two fields (the two printed displays), proved from `CV.ax_homfly`
(skein at `q`, Reidemeister-II invariance) and Laurent-ring algebra, exactly as the printed proof.
The clauses are also available with their hypotheses as arguments: `CV.fulltwist_skein`,
`CV.fulltwist_coefficient`. -/

namespace CV

open SM SM.Link AddMonoidAlgebra

/-! ## The symbols the lemma binds (d6_vertexedge.tex:1990–2009) -/

/-- "a diagram D carried by a single closed plane curve Γ_D" (d6_vertexedge.tex:1997–1999): the polygon
`Γ_D` of the unique component of a one-component diagram. -/
def curveOf (D : Diagram) (hD : D.componentCount = 1) :
    LabelledTuple (D.Γ.comp (Fin.cast hD.symm 0)).k :=
  (D.Γ.comp (Fin.cast hD.symm 0)).P

/-- `Γ_D` lies in the regular locus of CV def:regular(B) (so CV def:rot applies to it): every component
polygon of a `Diagram` is regular (`Shadow.Generic.regular`), and CV's and SM's regularity agree
(`regular_iff_sm`). -/
theorem curveOf_regular (D : Diagram) (hD : D.componentCount = 1) : Regular (curveOf D hD) :=
  (regular_iff_sm _).mpr (D.generic.regular _)

/-- "R(Γ_D) = |rot(Γ_D)| the absolute rotation of that curve" (d6_vertexedge.tex:2004–2005), Definition
def:rot: `CV.rotAbs` of the single curve `Γ_D`, as an integer. -/
noncomputable def absRot (D : Diagram) (hD : D.componentCount = 1) : ℤ :=
  rotAbs (curveOf D hD) (curveOf_regular D hD)

theorem absRot_eq_abs_rot (D : Diagram) (hD : D.componentCount = 1) :
    absRot D hD = |rot (curveOf D hD) (curveOf_regular D hD)| :=
  rotAbs_cast _ _

/-- "d(D) = 1 − w(D) − R(Γ_D)" (d6_vertexedge.tex:2000–2003), "with w(D) the writhe" (2004) — defined "for
a diagram D carried by a single closed plane curve Γ_D, and only for such a diagram" (1997–1999): the
hypothesis `hD` is the printed domain. -/
noncomputable def d (D : Diagram) (hD : D.componentCount = 1) : ℤ :=
  1 - D.writhe - absRot D hD

/-- "Ω(D) = [a^{d(D)} z^0] F_D" (d6_vertexedge.tex:2000–2003), the `a^{d(D)} z^0` coefficient of the
HOMFLY–PT polynomial `F_D = P_D`; same domain as `d`. -/
noncomputable def Omega (D : Diagram) (hD : D.componentCount = 1) : ℤ :=
  coeffAt (d D hD) 0 (homfly D)

/-! ## Reidemeister-II sequences -/

/-- "carried … by oriented Reidemeister-II moves": the HOMFLY–PT polynomial is unchanged along any
finite sequence of `RII` moves (CV:ax:homfly, Reidemeister invariance, move II). -/
theorem homfly_eq_of_reflTransGen_RII {D D' : Diagram} (h : Relation.ReflTransGen RII D D') :
    homfly D = homfly D' := by
  induction h with
  | refl => rfl
  | tail _ hstep ih => exact ih.trans (ax_homfly.reidemeister.2.1 _ _ hstep)

/-- A finite sequence of `RII` moves can be run backwards (`RII` is symmetric, `RII.symm`). -/
theorem reflTransGen_RII_symm {D D' : Diagram} (h : Relation.ReflTransGen RII D D') :
    Relation.ReflTransGen RII D' D := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih => exact Relation.ReflTransGen.head hstep.symm ih

/-- Reading check: because `RII` is symmetric, "a finite sequence of RII moves" (`ReflTransGen`, used
here) and the plan's `EqvGen RII` (§159) are the same relation. -/
theorem reflTransGen_RII_iff_eqvGen (D D' : Diagram) :
    Relation.ReflTransGen RII D D' ↔ Relation.EqvGen RII D D' := by
  constructor
  · intro h
    induction h with
    | refl => exact Relation.EqvGen.refl _
    | tail _ hstep ih => exact Relation.EqvGen.trans _ _ _ ih (Relation.EqvGen.rel _ _ hstep)
  · intro h
    induction h with
    | rel _ _ h => exact Relation.ReflTransGen.single h
    | refl _ => exact Relation.ReflTransGen.refl
    | symm _ _ _ ih => exact reflTransGen_RII_symm ih
    | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-! ## Laurent-ring facts used by the printed proof -/

/-- `a^{−2} = single (−2, 0) 1` in `R`. -/
theorem R.aInv_sq : R.aInv ^ 2 = (single (-2, 0) 1 : R) := by
  rw [pow_two, R.aInv, single_mul_single]
  norm_num

/-- `a^{−1} z = single (−1, 1) 1` in `R`. -/
theorem R.aInv_mul_z : R.aInv * R.z = (single (-1, 1) 1 : R) := by
  rw [R.aInv, R.z, single_mul_single]
  norm_num

/-- Coefficient shift: `[a^d z^k] (c a^p z^q · f) = c · [a^{d−p} z^{k−q}] f` (the step
"[a^{d_L−2} z^0](a^{−2} F_L) = [a^{d_L} z^0] F_L" of the printed proof, d6_vertexedge.tex:2042–2043). -/
theorem coeffAt_single_mul (d k p q c : ℤ) (f : R) :
    coeffAt d k (single (p, q) c * f) = c * coeffAt (d - p) (k - q) f := by
  unfold coeffAt
  rw [coeff_single_mul_apply]
  congr 2
  ext <;> simp [neg_add_eq_sub]

/-! ## Row 159 — the two printed displays, with the hypotheses as arguments -/

/-- The skein triple the printed proof applies ax:homfly to: "its L₊ is D_H, its L₋ is the switched
diagram, and its L₀ is D_A by (T1)" (d6_vertexedge.tex:2033–2036). -/
theorem fulltwist_isSkeinTriple (D_H D_A : Diagram) (q : D_H.Γ.Crossing) (hq : D_H.IsPositive q)
    (T1 : IsOrientedSmoothing D_H q D_A) : IsSkeinTriple D_H (D_H.switch q) D_A :=
  ⟨q, hq, rfl, T1⟩

/-- First display of CV:lem:fulltwist (d6_vertexedge.tex:2022–2025): "F_H = a^{−2} F_L + a^{−1} z F_A"
for oriented diagrams D_L, D_H, D_A and a positive crossing q of D_H with (T1), (T2).  Proof as printed
(2033–2037): the skein of ax:homfly at q gives a F_H − a^{−1} F_{switch} = z F_A, the switched
diagram has polynomial F_L by (T2) and Reidemeister-II invariance, and multiplying by a^{−1} gives the
display. -/
theorem fulltwist_skein (D_L D_H D_A : Diagram) (q : D_H.Γ.Crossing) (hq : D_H.IsPositive q)
    (T1 : IsOrientedSmoothing D_H q D_A) (T2 : Relation.ReflTransGen RII (D_H.switch q) D_L) :
    homfly D_H = R.aInv ^ 2 * homfly D_L + R.aInv * R.z * homfly D_A := by
  have hsk : R.a * homfly D_H - R.aInv * homfly (D_H.switch q) = R.z * homfly D_A :=
    ax_homfly.skein D_H (D_H.switch q) D_A (fulltwist_isSkeinTriple D_H D_A q hq T1)
  rw [homfly_eq_of_reflTransGen_RII T2] at hsk
  have hinv : R.aInv * R.a = 1 := R.aInv_mul_a
  linear_combination R.aInv * hsk - homfly D_H * hinv

/-- Second display of CV:lem:fulltwist (d6_vertexedge.tex:2026–2030): for one-component D_L, D_H (the
domain of d and Ω), "if moreover d_H = d_L − 2, then Ω_H − Ω_L = [a^{d_L − 1} z^{−1}] F_A".  Proof as
printed (2039–2044): Ω_H = [a^{d_L−2} z^0] F_H; taking that coefficient of the first display, the first
term contributes [a^{d_L} z^0] F_L = Ω_L and the second [a^{d_L−1} z^{−1}] F_A. -/
theorem fulltwist_coefficient (D_L D_H D_A : Diagram) (q : D_H.Γ.Crossing) (hq : D_H.IsPositive q)
    (T1 : IsOrientedSmoothing D_H q D_A) (T2 : Relation.ReflTransGen RII (D_H.switch q) D_L)
    (hL : D_L.componentCount = 1) (hH : D_H.componentCount = 1)
    (hd : d D_H hH = d D_L hL - 2) :
    Omega D_H hH - Omega D_L hL = coeffAt (d D_L hL - 1) (-1) (homfly D_A) := by
  have h1 := fulltwist_skein D_L D_H D_A q hq T1 T2
  unfold Omega
  rw [hd, h1, coeffAt_add, R.aInv_sq, R.aInv_mul_z, coeffAt_single_mul, coeffAt_single_mul]
  have e1 : d D_L hL - 2 - -2 = d D_L hL := by ring
  have e2 : d D_L hL - 2 - -1 = d D_L hL - 1 := by ring
  rw [e1, e2]
  norm_num

/-! ## The row bundle -/

/-- The printed clauses of CV:lem:fulltwist (d6_vertexedge.tex:1981–2031), one field per printed
display, each under the printed hypotheses: D_L, D_H, D_A oriented diagrams, q a positive crossing of
D_H, (T1) `IsOrientedSmoothing D_H q D_A`, (T2) `Relation.ReflTransGen RII (D_H.switch q) D_L`.  See
the module docstring for every reading. -/
structure FullTwistData : Prop where
  /-- "Then F_H = a^{−2} F_L + a^{−1} z F_A" (2022–2025). -/
  skein_display : ∀ (D_L D_H D_A : Diagram) (q : D_H.Γ.Crossing), D_H.IsPositive q →
    IsOrientedSmoothing D_H q D_A → Relation.ReflTransGen RII (D_H.switch q) D_L →
    homfly D_H = R.aInv ^ 2 * homfly D_L + R.aInv * R.z * homfly D_A
  /-- "If moreover d_H = d_L − 2, then Ω_H − Ω_L = [a^{d_L − 1} z^{−1}] F_A" (2026–2030), for D_L, D_H
  each carried by a single closed plane curve (the domain of d and Ω, 1997–1999). -/
  coefficient_display : ∀ (D_L D_H D_A : Diagram) (q : D_H.Γ.Crossing), D_H.IsPositive q →
    IsOrientedSmoothing D_H q D_A → Relation.ReflTransGen RII (D_H.switch q) D_L →
    ∀ (hL : D_L.componentCount = 1) (hH : D_H.componentCount = 1),
      d D_H hH = d D_L hL - 2 →
      Omega D_H hH - Omega D_L hL = coeffAt (d D_L hL - 1) (-1) (homfly D_A)

/-- **CV:lem:fulltwist** (d6_vertexedge.tex:1981–2031), "the abstract full-twist triple", proved from
CV:ax:homfly (`CV.ax_homfly`: skein at q and Reidemeister-II invariance) and Laurent-ring algebra,
exactly as the printed proof. -/
theorem fulltwist : FullTwistData where
  skein_display := fulltwist_skein
  coefficient_display := fun D_L D_H D_A q hq T1 T2 hL hH hd =>
    fulltwist_coefficient D_L D_H D_A q hq T1 T2 hL hH hd

end CV

#print axioms CV.fulltwist
