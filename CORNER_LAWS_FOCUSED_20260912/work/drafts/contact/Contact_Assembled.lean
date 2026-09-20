import SM.TransverseFront
import SM.LinkingCalculusRow
import SM.NgBound
import SM.ContactPath
import SM.GenericFront
import SM.TransverseNeighborhood

/-! # src:contact (fifth literature interface), `SM.sl`, rows 94 / 161 / 162 — FINAL statements

Judge's synthesis of the contact panel (2026-09-15): DESIGN B (proof feasibility: the proof route of
fd:contact composed and kernel-checked from named unit Props) with the fidelity grafts of DESIGN A
(the axiom carries exactly the four printed formulas — the convention / consequence / provenance /
scope sentences are theorems or commentary, as for `SM.ng_finite_word`; `SM.sl` is the name of the
document's self-linking number; "an oriented Legendrian front" is one predicate
`IsLegendrianFrontOf` in row 87's vocabulary, the vocabulary of the axiom's only consumer; row 161
keeps its printed shape).  Plan: work/drafts/contact/PLAN_FINAL.md.

Everything typechecks against the accepted layer.  ONE `axiom` (`SM.src_contact`, policy name in
lean/axiom-policy.json).  `sorry` appears ONLY in the row theorems `SM.fd_contact` and
`CV.ax_slbound` (which wait for the prover units of PLAN_FINAL §6); `CV.ax_etnyre` (row 161) is
PROVED from the axiom.  The assembly `fd_contact_of_units` is proved: the printed proof of fd:contact
composes through rows 84 → 87 → src:contact → 93 → 91 on the accepted vocabulary.

Check: `cd work/lean && lake env lean ../drafts/contact/Statements_FINAL.lean`.
Registry text: blueprint/AXIOM_REGISTRY.md §src:contact = reference/SM/sm-3-statesum.tex:3341-3365.
-/

namespace SM

open SM.Link TransverseNeighborhood
open scoped ContDiff
open Set Function Real

noncomputable section
open Classical

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## 0. The three parametrization conventions of the accepted layer and their conversions

* def:transverse-front (row 92): `Space = ℝ × ℝ × ℝ`, 1-periodic `TransverseKnot`;
* rows 84 / 87 / 88: `E3 = EuclideanSpace ℝ (Fin 3)`, 2π-periodic circles (row 88 at period `P = 2π`,
  the document's `S¹ = ℝ/2πℤ` of the fd block, FR-LC-1);
* rows 89-91: `SpatialLink c` on `Space`, 1-periodic. -/

/-- `(x, y, z) ↦ !₂[x, y, z]`: the identity on coordinates. -/
def toE3 (p : Space) : E3 := (EuclideanSpace.equiv (Fin 3) ℝ).symm ![p.1, p.2.1, p.2.2]

/-- `p ↦ (p 0, p 1, p 2)`. -/
def toSpace (p : E3) : Space := (p 0, p 1, p 2)

@[simp] theorem toE3_apply0 (p : Space) : toE3 p 0 = p.1 := rfl
@[simp] theorem toE3_apply1 (p : Space) : toE3 p 1 = p.2.1 := rfl
@[simp] theorem toE3_apply2 (p : Space) : toE3 p 2 = p.2.2 := rfl

theorem toSpace_toE3 (p : Space) : toSpace (toE3 p) = p := rfl

theorem toE3_toSpace (q : E3) : toE3 (toSpace q) = q := by
  ext i; fin_cases i <;> rfl

theorem contDiff_toE3 : ContDiff ℝ ∞ toE3 := by
  unfold toE3
  refine (EuclideanSpace.equiv (Fin 3) ℝ).symm.contDiff.comp ?_
  rw [contDiff_pi]
  intro i
  fin_cases i
  · exact contDiff_fst
  · exact contDiff_snd.fst
  · exact contDiff_snd.snd

/-- The convention sentence of src:contact ("standard contact space `(ℝ³, ker(dz − y dx))`") is ONE
convention in every vocabulary of the accepted layer: the contact forms of rows 84 / 87 / 88 and of
def:transverse-front agree (`rfl`).  No field of the axiom (FR-SC-8). -/
theorem lcContactForm_toE3 (p v : Space) : lcContactForm (toE3 p) (toE3 v) = contactForm p v := rfl
theorem alpha_eq_lcContactForm : TransverseNeighborhood.alpha = lcContactForm := rfl
theorem gf_alpha_eq_lcContactForm : GenericFront.alpha = lcContactForm := rfl

/-- The convention sentence "with positive transverse orientation `z′ − y x′ > 0`" is the accepted
`IsPositiveTransverse` (`Iff.rfl`).  No field of the axiom (FR-SC-8). -/
theorem isPositiveTransverse_iff (T : ℝ → E3) :
    IsPositiveTransverse T ↔ ∀ θ, 0 < lcContactForm (T θ) (deriv T θ) := Iff.rfl

namespace TransverseKnot

variable (K : TransverseKnot)

/-- The knot of def:transverse-front as a 2π-periodic circle in oriented `ℝ³` (the object of rows
84, 87, 88): `θ ↦ T(θ / 2π)`. -/
def circle : ℝ → E3 := fun θ => toE3 (K.T (θ / (2 * π)))

/-- The knot as a one-component spatial link (the object of rows 89-91), same parametrization. -/
def spatial : SpatialLink 1 where
  T := fun _ => K.T
  smooth := fun _ => K.smooth
  periodic := fun _ => K.periodic
  embedded := fun i j s t h => ⟨Subsingleton.elim i j, K.embedded s t h⟩
  regular := fun _ t => K.deriv_T_ne_zero t

@[simp] theorem spatial_T (i : Fin 1) : K.spatial.T i = K.T := rfl

/-- The projection of the spatial link is the loop of the front. -/
theorem spatial_projLoop (i : Fin 1) : K.spatial.projLoop i = K.xz := by
  cases i; rfl

end TransverseKnot

/-! ## 1. `SM.sl`: the self-linking number of the document (fd:framed-linking, sm-3:2820-2824),
ε-free through the accepted row 88

`selfLinking P T ε = ℓ(T, T + ε∂_y)` (SM/LinkingCalculus.lean:574); row 88 gives one radius `ε₀ > 0`
for every transverse family (`transverse_uniform`) and independence of the radius and the family
parameter (`self_linking_invariant`).  The radius is fixed ONCE by `Classical.choose` on the constant
family `s ↦ T`, so `sl` is a function of `T` alone; unit U1a proves the choice immaterial. -/

/-- The constant transverse family of one positive transverse embedding (period `2π`). -/
theorem IsPositiveTransverseEmbedding.constFamily {T : ℝ → E3}
    (h : IsPositiveTransverseEmbedding (2 * π) T) : TransverseFamily (2 * π) (fun _ => T) where
  pos := by positivity
  smooth := by
    show ContDiff ℝ ∞ (fun p : ℝ × ℝ => T p.2)
    exact h.circle.smooth.comp contDiff_snd
  periodic := fun _ => h.circle.periodic
  embedded := fun _ _ u u' hu => h.embedded u u' hu
  positive := fun _ _ u => h.positive u

/-- **`sl` of fd:framed-linking, ε-free**, for a 2π-periodic positive transverse embedding
`T : S¹ → ℝ³`: `ℓ(T, T + ε₀ ∂_y)` at the radius `ε₀` of row 88's `transverse_uniform` for the constant
family; `0` off the class (never exercised: every clause applies it to a positive transverse
embedding, FR-SC-9).  Row 88's `self_linking_invariant` makes it the value at EVERY admissible radius
(unit U1a) and constant along transverse families (U1b). -/
def slCircle (T : ℝ → E3) : ℝ :=
  if h : IsPositiveTransverseEmbedding (2 * π) T then
    selfLinking (2 * π) T
      (Classical.choose (fd_linking_calculus.transverse_uniform (2 * π) (fun _ => T) h.constFamily))
  else 0

/-- **The document's self-linking number of a generic positive transverse knot** (def:transverse-front),
read on the fd block's circle `ℝ/2πℤ` through `TransverseKnot.circle`.  ℝ-valued; integrality is a
consequence of the axiom's transverse clause (`sl K = ↑writhe`), not a prerequisite (FR-SC-10). -/
def sl (K : TransverseKnot) : ℝ := slCircle K.circle

/-! ## 2. "An oriented Legendrian front": a front on ng:front-domain that is the `xz` projection of an
oriented Legendrian knot of rows 84 / 87 (parameter bridge `θ = 2π t`) -/

/-- `F` is the `xz` front of the oriented Legendrian knot `L` in the vocabulary of row 87, the axiom's
consumer: `GenericFrontHyp L` = smooth embedded 2π-periodic circle (orientation = parameter direction,
T-1) with `α(L′) = 0`; one parameter circle; and the loop of `F` is `t ↦ (x(2πt), z(2πt))`.  As a
`SmoothFront` (ng:front-domain, accepted row 73), `F` carries the front vocabulary of the printed
formulas: `D = F.downCount`, `U = F.upCount` ("traversed from its locally upper arm to its locally
lower arm", FR-2 = Etnyre's down cusp), `w = F.writhe` (over = smaller slope, sign `sgn det(u_O,u_U)`,
Etnyre §2.2 (3): "the positive y axis goes into the page"). -/
structure IsLegendrianFrontOf (L : ℝ → E3) (F : SmoothFront) : Prop where
  hyp : GenericFrontHyp L
  one : F.c = 1
  front : ∀ (i : Fin F.c) (t : ℝ), (F.comp i).γ t = GenericFront.front L (2 * π * t)

/-- The front of `L` is unique as a `SmoothFront` (data = `c`, `comp`; the rest is `Prop`). -/
theorem IsLegendrianFrontOf.unique {L : ℝ → E3} {F F' : SmoothFront}
    (h : IsLegendrianFrontOf L F) (h' : IsLegendrianFrontOf L F') : F = F' := by
  have hcomp : ∀ (i : Fin F.c) (j : Fin F'.c), (i : ℕ) = j → (F.comp i).γ = (F'.comp j).γ := by
    intro i j hij
    funext t
    rw [h.front i t, h'.front j t]
  obtain ⟨c, hc, comp, _, _, _, _, _, _, _, _⟩ := F
  obtain ⟨c', hc', comp', _, _, _, _, _, _, _, _⟩ := F'
  have hcc : c = c' := by
    have := h.one; have := h'.one; simp_all
  subst hcc
  have hcomp' : comp = comp' := by
    funext i
    exact SmoothLoop.ext' (hcomp i i rfl)
  subst hcomp'
  rfl

/-! ## 3. THE FIFTH LITERATURE INTERFACE — src:contact (AXIOM_REGISTRY.md §src:contact =
sm-3:3341-3365), one field per printed FORMULA, ∃-form over the literature's `r`, `tb`

Sentence → rendering (the table of PLAN_FINAL §2):
* 3342-3345 "Use standard contact space … positive transverse orientation z′ − yx′ > 0": conventions,
  theorems `lcContactForm_toE3`, `alpha_eq_lcContactForm`, `isPositiveTransverse_iff` — no field;
* 3345-3351 "for an oriented Legendrian front with downward and upward cusp counts D, U": the binder
  `∀ L F, IsLegendrianFrontOf L F →` with `D = F.downCount`, `U = F.upCount`, `w = F.writhe`;
* 3349-3351 "every cusp … either downward or upward, so the total cusp count in his tb formula is
  D+U": the accepted theorem `SmoothFront.downCount_add_upCount` — no field;
* 3352 `r = (D−U)/2`: field `rotation`;  `tb = w − (D+U)/2`: field `thurston_bennequin`;
* 3353 `sl(T₊(L)) = tb(L) − r(L)`: field `pushoff_self_linking`, `T₊(L)` = every positive transverse
  pushoff `GenericFront.IsPositivePushoff L T′` (the document's own notion, FR-TN-4), `sl = slCircle`;
* 3355-3357 provenance parenthesis — no field;
* 3358-3363 "For a generic positive transverse front, self-linking equals its front writhe": field
  `transverse_front_writhe` over `TransverseKnot` (row 92), `sl K = K.front.writhe`;
* 3363-3364 "These are the local front and pushoff source formulas only": scope — no field. -/

/-- The printed formulas of src:contact for candidate rotation number `r` and Thurston–Bennequin
invariant `tb` of the literature (neither is defined in the document; both are fixed by the first two
formulas, `src_contact_iff_consequence`). -/
structure SrcContactClauses (r tb : (ℝ → E3) → ℝ) : Prop where
  /-- sm-3:3352, first formula of display fd:contact-inputs: `r = (D − U)/2`. -/
  rotation : ∀ (L : ℝ → E3) (F : SmoothFront), IsLegendrianFrontOf L F →
    r L = ((F.downCount : ℝ) - F.upCount) / 2
  /-- sm-3:3352, second formula: `tb = w − (D + U)/2` ("the total cusp count in his tb formula is
  D + U", `downCount_add_upCount`). -/
  thurston_bennequin : ∀ (L : ℝ → E3) (F : SmoothFront), IsLegendrianFrontOf L F →
    tb L = (F.writhe : ℝ) - ((F.downCount : ℝ) + F.upCount) / 2
  /-- sm-3:3353, third formula: `sl(T₊(L)) = tb(L) − r(L)`, for every positive transverse pushoff
  `T₊(L)` of `L` in the document's sense (a positive circle of a pushoff annulus, row 84 / 87). -/
  pushoff_self_linking : ∀ (L : ℝ → E3) (F : SmoothFront), IsLegendrianFrontOf L F →
    ∀ T' : ℝ → E3, GenericFront.IsPositivePushoff L T' → slCircle T' = tb L - r L
  /-- sm-3:3358-3360: "For a generic positive transverse front (Definition def:transverse-front),
  self-linking equals its front writhe" — the knot `T` named separately (`K`), its front `K.front`
  (over = smaller `y`, sign `sgn det_xz(u_O, u_U)`, accepted row 92). -/
  transverse_front_writhe : ∀ K : TransverseKnot, sl K = (K.front.writhe : ℝ)

/-- **src:contact** (AXIOM_REGISTRY.md §src:contact, sm-3:3341-3365; policy name `SM.src_contact`):
"Use standard contact space (ℝ³, ker(dz − y dx)), with positive transverse orientation z′ − y x′ > 0.
Etnyre's front and pushoff statements give, for an oriented Legendrian front with downward and upward
cusp counts D, U — every cusp of an oriented front is traversed either downward or upward, so the
total cusp count in his tb formula is D+U — r = (D−U)/2, tb = w − (D+U)/2, sl(T₊(L)) = tb(L) − r(L).
(…)  For a generic positive transverse front (Definition def:transverse-front), self-linking equals
its front writhe (…).  These are the local front and pushoff source formulas only."  Existence of the
literature's `r`, `tb` in ∃-form (the pattern of `lit_homfly`, `lp_lm`); the formulas are the fields of
`SrcContactClauses`; `sl` is the document's fd:framed-linking number (rem:sl-convention, FR-SC-4).
AXIOM: interface review against the registry text required before any consumer cites it. -/
axiom src_contact : ∃ r tb : (ℝ → E3) → ℝ, SrcContactClauses r tb

/-- The literature's rotation number, one witness fixed by choice. -/
def rot : (ℝ → E3) → ℝ := Classical.choose src_contact
/-- The literature's Thurston–Bennequin invariant, one witness fixed by choice. -/
def tb : (ℝ → E3) → ℝ := Classical.choose (Classical.choose_spec src_contact)

theorem src_contact_spec : SrcContactClauses rot tb :=
  Classical.choose_spec (Classical.choose_spec src_contact)

/-! ### 3.1 Sanity: the axiom is exactly the printed formulas, no more -/

/-- The cusp calculation of fd:contact's proof (sm-3:3452-3457): `tb − r = w − (D+U)/2 − (D−U)/2 =
w − D = sl_Ng(F)` — the third formula with the first two substituted (`slNg` = the accepted `w − D` of
row 93). -/
theorem SrcContactClauses.pushoff_slNg {r tb : (ℝ → E3) → ℝ} (h : SrcContactClauses r tb)
    {L : ℝ → E3} {F : SmoothFront} (hF : IsLegendrianFrontOf L F) {T' : ℝ → E3}
    (hT : GenericFront.IsPositivePushoff L T') : slCircle T' = (F.slNg : ℝ) := by
  rw [h.pushoff_self_linking L F hF T' hT, h.thurston_bennequin L F hF, h.rotation L F hF,
    SmoothFront.slNg_def]
  push_cast
  ring

/-- The substituted form of the display (what the proof of fd:contact consumes) together with the
transverse-front clause. -/
structure SrcContactConsequence : Prop where
  pushoff_slNg : ∀ (L : ℝ → E3) (F : SmoothFront), IsLegendrianFrontOf L F →
    ∀ T' : ℝ → E3, GenericFront.IsPositivePushoff L T' → slCircle T' = (F.slNg : ℝ)
  transverse_front_writhe : ∀ K : TransverseKnot, sl K = (K.front.writhe : ℝ)

/-- **The ∃-form asserts precisely the two consequences** — `sl(T₊) = w − D` on the Legendrian class
and `sl = w` on the transverse class — and nothing about `r`, `tb` beyond the two defining formulas
(FR-SC-1).  → : the cusp calculation.  ← : define `r`, `tb` by the two printed formulas on the (unique)
front of `L`.  Standard axioms only. -/
theorem src_contact_iff_consequence :
    (∃ r tb : (ℝ → E3) → ℝ, SrcContactClauses r tb) ↔ SrcContactConsequence := by
  constructor
  · rintro ⟨r, tb, h⟩
    exact ⟨fun L F hF T' hT => h.pushoff_slNg hF hT, h.transverse_front_writhe⟩
  · intro h
    refine ⟨fun L => if hL : ∃ F, IsLegendrianFrontOf L F then
        ((hL.choose.downCount : ℝ) - hL.choose.upCount) / 2 else 0,
      fun L => if hL : ∃ F, IsLegendrianFrontOf L F then
        (hL.choose.writhe : ℝ) - ((hL.choose.downCount : ℝ) + hL.choose.upCount) / 2 else 0, ?_⟩
    have key : ∀ (L : ℝ → E3) (F : SmoothFront) (hF : IsLegendrianFrontOf L F),
        (⟨F, hF⟩ : ∃ F, IsLegendrianFrontOf L F).choose = F := fun L F hF =>
      (Classical.choose_spec (⟨F, hF⟩ : ∃ F, IsLegendrianFrontOf L F)).unique hF
    refine ⟨?_, ?_, ?_, h.transverse_front_writhe⟩
    · intro L F hF
      have hex : ∃ F, IsLegendrianFrontOf L F := ⟨F, hF⟩
      simp only [hex, ↓reduceDIte, key L F hF]
    · intro L F hF
      have hex : ∃ F, IsLegendrianFrontOf L F := ⟨F, hF⟩
      simp only [hex, ↓reduceDIte, key L F hF]
    · intro L F hF T' hT'
      have hex : ∃ F, IsLegendrianFrontOf L F := ⟨F, hF⟩
      simp only [hex, ↓reduceDIte, key L F hF]
      rw [h.pushoff_slNg L F hF T' hT', SmoothFront.slNg_def]
      push_cast
      ring

/-! ## 4. The rows -/

/-- **fd:contact** (sm-3:3404-3423), one field per printed clause.  "In the xz front page the smaller-y
branch is over, and its crossing sign is sgn det_xz(u_O, u_U)" = `over_rule_sign` (definitional on the
accepted class, row 92); display fd:front-writhe = `front_writhe`; "Let T be an individual smooth
positive transverse knot whose specified xz projection D_T is an ordinary finite regular generic
diagram [= every `TransverseKnot`, def:transverse-front]. With P_T denoting the original campaign
polynomial of this actual diagram, one has [fd:representative-bound]" = `representative_bound`,
`P_T = P X` for every polygonal reading `X` of `D_T` (FR-1: a `HeightMarking` of the one-component
spatial link `K.spatial`, over = smaller `y` — the reading row 91 takes for its endpoint `T`).  The two
closing sentences (3418-3421) are commentary on the hypotheses and have no field. -/
structure FdContactData : Prop where
  /-- sm-3:3406-3407, the first sentence (the front page convention, definitional on row 92). -/
  over_rule_sign : ∀ (K : TransverseKnot) (s t : ℝ), K.front.IsDouble s t →
    (K.front.isOver s t ↔ yOf K.T s < yOf K.T t) ∧
    K.front.crossSign s t = ((SignType.sign (det (K.front.vel s) (K.front.vel t)) : SignType) : ℤ)
  /-- display fd:front-writhe (sm-3:3409-3411): `sl(T) = Σ_q sgn det_xz(u_O(q), u_U(q))`. -/
  front_writhe : ∀ K : TransverseKnot, sl K = (K.front.writhe : ℝ)
  /-- display fd:representative-bound (sm-3:3412-3418): `sl(T) ≤ −max deg_a P_T(a,z) − 1`, for every
  polygonal reading `X` of the specified diagram `D_T`. -/
  representative_bound : ∀ (K : TransverseKnot) (X : Diagram),
    Nonempty (K.spatial.HeightMarking K.spatial.projLoop X) →
    sl K ≤ ((-degAZ (P X) - 1 : ℤ) : ℝ)

/-- The first field holds now (row 92, definitional). -/
theorem fdContact_over_rule_sign (K : TransverseKnot) (s t : ℝ) (h : K.front.IsDouble s t) :
    (K.front.isOver s t ↔ yOf K.T s < yOf K.T t) ∧
    K.front.crossSign s t = ((SignType.sign (det (K.front.vel s) (K.front.vel t)) : SignType) : ℤ) :=
  ⟨⟨fun h' => h'.2, fun h' => ⟨h, h'⟩⟩, K.front.crossSign_eq_sign h⟩

/-- The second field holds now (the axiom's transverse clause). -/
theorem fdContact_front_writhe (K : TransverseKnot) : sl K = (K.front.writhe : ℝ) :=
  src_contact_spec.transverse_front_writhe K

namespace CV

/-- **CV:ax:etnyre** (d10_axioms.tex:387-397): "Let T be a front diagram of a transverse knot with no
downward vertical tangency. Then sl(T) equals the writhe of T."  Printed shape kept: `D` is a front
diagram of the transverse knot `K` (`K.front = D`, def:transverse-front's class), "no downward vertical
tangency" is the explicit hypothesis on `D` (redundant on this class: `TransverseKnot.front_vertical_up`,
FR-FC-4); `sl(T)` is the SM's `sl` (the CV text never defines it: "presupposes the contact-geometric
definition of sl; this document never defines it"; rem:sl-convention). -/
structure AxEtnyreData : Prop where
  self_linking_eq_writhe : ∀ (D : SM.SmoothKnotDiagram) (K : SM.TransverseKnot), K.front = D →
    (∀ t : ℝ, (D.vel t).1 = 0 → 0 < (D.vel t).2) → SM.sl K = (D.writhe : ℝ)

/-- **CV:ax:slbound** (d10_axioms.tex:399-425): "Let T be a transverse knot in the standard contact ℝ³
and let P_T(a,z) be the HOMFLY–PT polynomial of the knot it presents, in the normalization of Axiom
ax:homfly. Then sl(T) ≤ −max deg_a P_T(a,z) − 1."  Recorded narrowing (FR-FC-5): `T` ranges over the
transverse knots with a generic front (`TransverseKnot`, SM fd:contact's own domain and the only
consumer's instance, thm:carrierfloor (C)); "the knot it presents" has polynomial `homfly X`
(`CV.ax_homfly`'s map = `SM.homfly`) for every polygonal reading `X` of its front (FR-1); the
source-fidelity paragraph is commentary (FR-FC-6). -/
structure AxSlboundData : Prop where
  bound : ∀ (K : SM.TransverseKnot) (X : Diagram),
    Nonempty (K.spatial.HeightMarking K.spatial.projLoop X) →
    SM.sl K ≤ ((-degAZ (homfly X) - 1 : ℤ) : ℝ)

/-- Row 161 from row 94's display fd:front-writhe (the printed hypothesis is unused). -/
theorem ax_etnyre_of (h : FdContactData) : AxEtnyreData :=
  ⟨fun D K hD _ => by subst hD; exact h.front_writhe K⟩

/-- Row 162 from row 94 (`P = homfly`, lp:core). -/
theorem ax_slbound_of (h : FdContactData) : AxSlboundData :=
  ⟨fun K X hX => by rw [← P_eq_homfly]; exact h.representative_bound K X hX⟩

end CV

/-! ## 5. The proof of fd:contact through rows 84 → 87 → src:contact → 93 → 91: the units (named
Props) and the assembly theorem (PLAN_FINAL §5-§6).  Each unit is one prover unit. -/

/-! ### 5.0 The verbatim copies of row 84's notions in row 87 (`SM.GenericFront.*`) are the same
predicates: eta bridges (unit U0, proved here) -/

theorem embeddedCircle_toGF {L : ℝ → E3} (h : IsEmbeddedCircle L) :
    GenericFront.IsEmbeddedCircle L :=
  ⟨h.smooth, h.periodic, h.injective, h.immersion⟩

theorem embeddedCircle_ofGF {L : ℝ → E3} (h : GenericFront.IsEmbeddedCircle L) :
    IsEmbeddedCircle L :=
  ⟨h.smooth, h.periodic, h.injective, h.immersion⟩

theorem legendrian_toGF {L : ℝ → E3} (h : IsLegendrian L) : GenericFront.IsLegendrian L := h
theorem legendrian_ofGF {L : ℝ → E3} (h : GenericFront.IsLegendrian L) : IsLegendrian L := h

theorem annulus_toGF {L : ℝ → E3} {ε b : ℝ} {B : ℝ × ℝ → E3} (h : IsPushoffAnnulus L ε b B) :
    GenericFront.IsPushoffAnnulus L ε b B :=
  ⟨h.eps_pos, h.b_pos, h.smooth, h.periodic, h.core, h.injective, h.immersion, h.transverse,
    h.positive⟩

theorem annulus_ofGF {L : ℝ → E3} {ε b : ℝ} {B : ℝ × ℝ → E3}
    (h : GenericFront.IsPushoffAnnulus L ε b B) : IsPushoffAnnulus L ε b B :=
  ⟨h.eps_pos, h.b_pos, h.smooth, h.periodic, h.core, h.injective, h.immersion, h.transverse,
    h.positive⟩

theorem pushoff_toGF {L T' : ℝ → E3} (h : IsPositivePushoff L T') :
    GenericFront.IsPositivePushoff L T' := by
  obtain ⟨ε, b, B, hB, s₀, h1, h2, h3⟩ := h
  exact ⟨ε, b, B, annulus_toGF hB, s₀, h1, h2, h3⟩

theorem pushoff_ofGF {L T' : ℝ → E3} (h : GenericFront.IsPositivePushoff L T') :
    IsPositivePushoff L T' := by
  obtain ⟨ε, b, B, hB, s₀, h1, h2, h3⟩ := h
  exact ⟨ε, b, B, annulus_ofGF hB, s₀, h1, h2, h3⟩

theorem circleReparam_ofGF {ρ : ℝ → ℝ} (h : GenericFront.IsCircleReparam ρ) : IsCircleReparam ρ :=
  ⟨h.smooth, h.deriv_pos, h.lift⟩

theorem transverselyIsotopic_ofGF {T₀ T₁ : ℝ → E3} (h : GenericFront.TransverselyIsotopic T₀ T₁) :
    TransverselyIsotopic T₀ T₁ := by
  obtain ⟨F, hF, hs, h0, ρ, hρ, h1⟩ := h
  exact ⟨F, hF, fun s hs' => ⟨embeddedCircle_ofGF (hs s hs').1, (hs s hs').2⟩, h0, ρ,
    circleReparam_ofGF hρ, h1⟩

/-! ### 5.1 The units -/

/-- U0: the knot of def:transverse-front is a row-84 input (2π-periodic embedded circle, `α(T′) > 0`);
chain rule through the continuous linear `toE3` and `θ ↦ θ/2π`. -/
def U_circle : Prop := ∀ K : TransverseKnot, TransverseNeighborhoodHyp K.circle

/-- U1: `sl` is a transverse-isotopy invariant (row 88's `self_linking_invariant` + `transverse_uniform`
on the strip family extended to `ℝ × ℝ` by the clock `Real.smoothTransition`, and reparametrization
invariance through the family `ρ_s = (1−s)·id + s·ρ`, U1c). -/
def U_sl_isotopy : Prop := ∀ T₀ T₁ : ℝ → E3, TransverselyIsotopic T₀ T₁ → slCircle T₀ = slCircle T₁

/-- U6a: the specified projection of a transverse knot is an ordinary finite regular generic diagram
in row 91's sense (heights distinct at double points from embeddedness, `y_ne_of_isDouble`). -/
def U_regular : Prop := ∀ K : TransverseKnot, K.spatial.RegularGenericProjection

/-- The data the printed proof extracts from `L_T = Φ₁ ∘ L` (units U2-U5): its spatial link, its front
`F_T` on ng:front-domain, the rounding `S(F_T)` as both a rounding of `F_T` (row 93's input) and a clean
cusp smoothing with a height reading (row 91's input).  Design point: build `F` FROM `sp` so that
`F.comp 0 = sp.projLoop 0` definitionally. -/
structure LegendrianPackage (Lc : ℝ → E3) where
  /-- the one-component spatial link of `L_T` (1-periodic, on `Space`) -/
  sp : SpatialLink 1
  sp_T : ∀ (i : Fin 1) (t : ℝ), sp.T i t = toSpace (Lc (2 * π * t))
  /-- the front `F_T` -/
  F : SmoothFront
  F_front : IsLegendrianFrontOf Lc F
  /-- row 91's input class for `L_T` -/
  cusped : sp.CuspedProjection
  /-- the rounded curves `S(F_T)` and one polygonal reading `S` -/
  G : Fin 1 → SmoothLoop
  S : Diagram
  clean : Nonempty (sp.CleanCuspSmoothing G)
  height_marking : Nonempty (sp.HeightMarking G S)
  rounding : F.IsRounding S

/-- U2-U5: every Legendrian embedded circle with a generic front (row 87's output) has such a package. -/
def U_package : Prop := ∀ Lc : ℝ → E3, GenericFront.IsEmbeddedCircle Lc → GenericFront.IsLegendrian Lc →
  GenericFront.IsGenericFront Lc → Nonempty (LegendrianPackage Lc)

/-- U6: the supplied family `G_t = Ψ_t ∘ Φ_{1−t} ∘ L` (display fd:contact-ambient-composition) as a
`SpatialFamily 1` from `L_T`'s spatial link to the knot's, time-clamped, with the endpoint reading
transported. -/
def U_family : Prop := ∀ (K : TransverseKnot) (L : ℝ → E3) (Ψ Φ : ℝ → E3 → E3)
    (pkg : LegendrianPackage (Φ 1 ∘ L)),
  IsCompactlySupportedAmbientIsotopy Ψ → (∀ θ, Ψ 1 (L θ) = K.circle θ) →
  GenericFront.IsContactIsotopy Φ →
  ∃ Fam : SpatialFamily 1, Fam.G 0 = pkg.sp ∧ (Fam.G 1).RegularGenericProjection ∧
    ∀ X : Diagram, Nonempty (K.spatial.HeightMarking K.spatial.projLoop X) →
      Nonempty ((Fam.G 1).HeightMarking (Fam.G 1).projLoop X)

/-! ### 5.2 The assembly: fd:contact from the units and the accepted rows -/

/-- **fd:contact from the units** — the printed proof (sm-3:3424-3492) composed on the accepted
vocabulary: row 84 gives `L`, `T′` (positive pushoff transversely isotopic to `T`) and `Ψ`; row 87 gives
`Φ`, `L_T = Φ₁ ∘ L` with generic front, and carries `T′` to a positive pushoff of `L_T` transversely
isotopic to it; row 88 (U1) transports `sl`; src:contact's cusp calculation gives
`sl(T₊(L_T)) = sl_Ng(F_T)`; row 93 bounds it by `−max deg_a P_{S(F_T)} − 1`; row 91 on the supplied
family (U6) gives `P_{S(F_T)} = P_{D_T}`. -/
theorem fd_contact_of_units (h0 : U_circle) (h1 : U_sl_isotopy) (h3 : U_package) (h4 : U_family) :
    FdContactData where
  over_rule_sign := fdContact_over_rule_sign
  front_writhe := fdContact_front_writhe
  representative_bound := by
    intro K X hX
    -- row 84 on T = K.circle
    obtain ⟨δ, H, hh, L, Ψ, c84⟩ := fd_transverse_neighborhood K.circle (h0 K)
    obtain ⟨T', hT', hiso⟩ := c84.pushoff_isotopic
    -- row 87 on L
    have hyp87 : GenericFrontHyp L := ⟨embeddedCircle_toGF c84.legendrian_circle, c84.legendrian⟩
    obtain ⟨Φ, c87⟩ := fd_generic_front L hyp87
    obtain ⟨ε, b, B, hB, s₀, hs₀, hs₀b, rfl⟩ := hT'
    obtain ⟨-, hpush⟩ := c87.pushoff ε b B (annulus_toGF hB)
    obtain ⟨hiso2, hpos2⟩ := hpush s₀ hs₀ hs₀b
    -- the front F_T, its rounding, the spatial link (U2-U5) and the supplied family (U6)
    obtain ⟨pkg⟩ := h3 (Φ 1 ∘ L) c87.legendrian_circle c87.legendrian c87.generic
    obtain ⟨Fam, hF0, hreg, hread⟩ := h4 K L Ψ Φ pkg c84.ambient c84.carries c87.isotopy
    -- sl(T) = sl(T′) = sl(T₊(L_T))            (row 88 through U1)
    have e1 : sl K = slCircle (fun θ => B (θ, s₀)) := (h1 _ _ hiso).symm
    have e2 : slCircle (fun θ => B (θ, s₀)) = slCircle (fun θ => Φ 1 (B (θ, s₀))) :=
      h1 _ _ (transverselyIsotopic_ofGF hiso2)
    -- sl(T₊(L_T)) = w(F_T) − D(F_T)             (src:contact, the cusp calculation)
    have e3 : slCircle (fun θ => Φ 1 (B (θ, s₀))) = (pkg.F.slNg : ℝ) :=
      src_contact_spec.pushoff_slNg pkg.F_front hpos2
    -- sl_Ng(F_T) ≤ −max deg_a P_{S(F_T)} − 1     (row 93)
    have e4 : pkg.F.slNg ≤ -degAZ (P pkg.S) - 1 := fd_ng_bound.ng_input pkg.F pkg.S pkg.rounding
    -- P_{S(F_T)} = P_{D_T}                        (row 91 on the supplied family)
    have e5 : P pkg.S = P X :=
      cp_finite_contact_path.endpoint_polynomial pkg.sp Nat.one_pos pkg.cusped Fam hF0 hreg X
        (hread X hX) pkg.G pkg.S pkg.clean pkg.height_marking
    rw [e1, e2, e3, ← e5]
    exact_mod_cast e4

/-! ### 5.3 The finer prover units behind `U_package` and `U_sl_isotopy` (PLAN_FINAL §6), and the
composition of `U_package` from them through the accepted row 89 (`ce_rounding`) -/

/-- U1a: `sl` is `ℓ(T, T + ε∂_y)` at EVERY admissible radius (row 88 `self_linking_invariant` on the
constant family, both radii compared with `min`). -/
def U_sl_radius : Prop := ∀ (T : ℝ → E3) (ε : ℝ), IsPositiveTransverseEmbedding (2 * π) T → 0 < ε →
  (∀ ε', 0 < ε' → ε' ≤ ε → ∀ u u', pushoff T (fun _ => ey) ε' u ≠ T u') →
  slCircle T = selfLinking (2 * π) T ε

/-- U1b: `sl` is constant along a transverse family (row 88 `transverse_uniform` +
`self_linking_invariant`, then U1a at both ends). -/
def U_sl_family : Prop := ∀ F : ℝ → ℝ → E3, TransverseFamily (2 * π) F →
  ∀ s ∈ Icc (0 : ℝ) 1, ∀ s' ∈ Icc (0 : ℝ) 1, slCircle (F s) = slCircle (F s')

/-- U1c: reparametrization invariance, through the family `ρ_s = (1 − s)·id + s·ρ` (`ρ_s′ > 0`, lift
by `2π`, `α((T∘ρ_s)′) = ρ_s′ · α(T′)`) and U1b — no change of variables in the Gauss integral. -/
def U_sl_reparam : Prop := ∀ (T : ℝ → E3) (ρ : ℝ → ℝ), IsPositiveTransverseEmbedding (2 * π) T →
  IsCircleReparam ρ → slCircle (T ∘ ρ) = slCircle T

/-- U2: the `xz` front of a Legendrian embedded circle with row 87's generic front is a front on
ng:front-domain with `IsLegendrianFrontOf` (the printed argument sm-3:3455-3462: exact germs give the
semicubical clauses, `z′ = y x′` gives "no vertical tangency on regular arcs"). -/
def U_legendrianFront : Prop := ∀ Lc : ℝ → E3, GenericFront.IsEmbeddedCircle Lc →
  GenericFront.IsLegendrian Lc → GenericFront.IsGenericFront Lc → ∃ F : SmoothFront, IsLegendrianFrontOf Lc F

/-- U3: the same curve as a one-component spatial link in row 91's input class (heights distinct at
double points from embeddedness; the exact germ on an interval from continuity of `y′`). -/
def U_spatialOf : Prop := ∀ Lc : ℝ → E3, GenericFront.IsEmbeddedCircle Lc →
  GenericFront.IsLegendrian Lc → GenericFront.IsGenericFront Lc →
  ∃ sp : SpatialLink 1, (∀ (i : Fin 1) (t : ℝ), sp.T i t = toSpace (Lc (2 * π * t))) ∧ sp.CuspedProjection

/-- U4 (THE RISK ITEM, FR-1): every front on ng:front-domain has a polygonal reading —
`S := (realize (oword F)).diagram`, `RecordIso (frontRecord F) S.record` from the sweep block
(`U8R.recordIso F`, `U2.realizeRecordIso (oword F) (word_ne_nil F)`), turned into a `Marking` by
`Marking.ofRecordIso` (the converse of `markingRecordIso`: on a finite cycle the successor determines
`cycBetween`; `record_succ_no_between`, `cycNext_no_between` are accepted). -/
def U_reading : Prop := ∀ F : SmoothFront, ∃ S : Diagram, Nonempty (F.Marking S)

/-- U5: a clean cusp smoothing of the spatial link is a clean-disc rounding of the front, and a
slope-rule marking of the front is a height-rule marking of the smoothing (`y = dz/dx` on a Legendrian
at its double points, `x′ ≠ 0` there; `CleanCuspSmoothing.occEquiv`, `crossSignOf_eq`). -/
def U_transport : Prop := ∀ (Lc : ℝ → E3) (sp : SpatialLink 1) (F : SmoothFront)
    (G : Fin 1 → SmoothLoop) (S : Diagram),
  (∀ (i : Fin 1) (t : ℝ), sp.T i t = toSpace (Lc (2 * π * t))) → IsLegendrianFrontOf Lc F →
  sp.CleanCuspSmoothing G → F.Marking S →
  Nonempty (sp.HeightMarking G S) ∧ F.IsRounding S

/-- `U_package` from U2-U5 and the accepted row 89: the rounded curves are the end of ce:rounding's
family (`CuspRoundingFamily.endSmoothing`, accepted in SM/CeSmoothingRecord.lean). -/
theorem U_package_of (u2 : U_legendrianFront) (u3 : U_spatialOf) (u4 : U_reading)
    (u5 : U_transport) : U_package := by
  intro Lc h1 h2 h3
  obtain ⟨F, hF⟩ := u2 Lc h1 h2 h3
  obtain ⟨sp, hsp, hcusp⟩ := u3 Lc h1 h2 h3
  obtain ⟨W⟩ := ce_rounding.exists_family sp Nat.one_pos hcusp
  obtain ⟨S, ⟨m⟩⟩ := u4 F
  obtain ⟨hm, hr⟩ := u5 Lc sp F _ S hsp hF W.toCuspRoundingFamily.endSmoothing m
  exact ⟨⟨sp, hsp, F, hF, hcusp, _, S, ⟨W.toCuspRoundingFamily.endSmoothing⟩, hm, hr⟩⟩

/-! ## 5.4 The unit theorems (leaves for the prover units; statements frozen) -/


/-! #### U0 helpers (unit CIRCLE, prefix `uc_`): the knot of def:transverse-front, read on `ℝ/2πℤ`
through `TransverseKnot.circle`, is a row-84 input.  Chain rule through the linear `toE3` and
`θ ↦ θ/2π`: `(K.circle)′(θ) = (1/2π) · toE3 (T′(θ/2π))`, so `α((K.circle)′) = (1/2π)·(z′ − y x′) > 0`;
the immersion clause is a corollary (`α_p(0) = 0`). -/

/-- `toE3` as a continuous linear map (for the chain rule). -/
def uc_toE3L : Space →L[ℝ] E3 :=
  LinearMap.toContinuousLinearMap
    { toFun := toE3
      map_add' := fun p q => by ext i; fin_cases i <;> rfl
      map_smul' := fun a p => by ext i; fin_cases i <;> rfl }

theorem uc_toE3L_apply (p : Space) : uc_toE3L p = toE3 p := rfl

/-- smooth: `toE3 ∘ T ∘ (·/2π)`. -/
theorem uc_smooth (K : TransverseKnot) : ContDiff ℝ ∞ K.circle :=
  contDiff_toE3.comp (K.smooth.comp (contDiff_id.div_const _))

/-- `2π`-periodic from the `1`-periodicity of `T`. -/
theorem uc_periodic (K : TransverseKnot) : Periodic K.circle (2 * π) := by
  intro θ
  show toE3 (K.T ((θ + 2 * π) / (2 * π))) = toE3 (K.T (θ / (2 * π)))
  have h : (θ + 2 * π) / (2 * π) = θ / (2 * π) + 1 := by
    rw [add_div, div_self (by positivity)]
  rw [h, K.periodic]

/-- injective modulo `2π` from `K.embedded` (injective modulo `1`) and `toSpace ∘ toE3 = id`. -/
theorem uc_injective (K : TransverseKnot) (θ θ' : ℝ) (h : K.circle θ = K.circle θ') :
    ∃ k : ℤ, θ' = θ + 2 * π * k := by
  have hT : K.T (θ / (2 * π)) = K.T (θ' / (2 * π)) := by
    have := congrArg toSpace h
    simpa [TransverseKnot.circle, toSpace_toE3] using this
  obtain ⟨n, hn⟩ := K.embedded _ _ hT
  refine ⟨n, ?_⟩
  have h2π : (2 * π) ≠ 0 := by positivity
  rw [div_eq_iff h2π] at hn
  rw [hn, add_mul, div_mul_cancel₀ _ h2π]
  ring

/-- the chain rule: `(K.circle)′(θ) = (1/2π) • toE3 (T′(θ/2π))`. -/
theorem uc_hasDerivAt_circle (K : TransverseKnot) (θ : ℝ) :
    HasDerivAt K.circle ((1 / (2 * π)) • toE3 (deriv K.T (θ / (2 * π)))) θ := by
  have h1 : HasDerivAt (fun θ : ℝ => θ / (2 * π)) (1 / (2 * π)) θ :=
    (hasDerivAt_id' θ).div_const (2 * π)
  have h2 : HasDerivAt K.T (deriv K.T (θ / (2 * π))) (θ / (2 * π)) :=
    ((K.smooth.differentiable (by decide)) _).hasDerivAt
  have h3 : HasDerivAt (fun θ : ℝ => K.T (θ / (2 * π)))
      ((1 / (2 * π)) • deriv K.T (θ / (2 * π))) θ := h2.scomp θ h1
  have h4 := uc_toE3L.hasFDerivAt.comp_hasDerivAt θ h3
  rw [map_smul, uc_toE3L_apply] at h4
  exact h4

theorem uc_deriv_circle (K : TransverseKnot) (θ : ℝ) :
    deriv K.circle θ = (1 / (2 * π)) • toE3 (deriv K.T (θ / (2 * π))) :=
  (uc_hasDerivAt_circle K θ).deriv

/-- `α((K.circle)′)(θ) = (1/2π) · (z′ − y x′)(θ/2π)`. -/
theorem uc_alpha_circle (K : TransverseKnot) (θ : ℝ) :
    alpha (K.circle θ) (deriv K.circle θ) =
      (1 / (2 * π)) * (deriv (zOf K.T) (θ / (2 * π)) -
        yOf K.T (θ / (2 * π)) * deriv (xOf K.T) (θ / (2 * π))) := by
  rw [uc_deriv_circle, K.deriv_T]
  simp only [alpha, TransverseKnot.circle, PiLp.smul_apply, toE3_apply0, toE3_apply1,
    toE3_apply2, smul_eq_mul, yOf_def]
  ring

/-- `α((K.circle)′) > 0` from `K.positive`. -/
theorem uc_transverse (K : TransverseKnot) : IsPositiveTransverse K.circle := by
  intro θ
  rw [uc_alpha_circle]
  exact mul_pos (by positivity) (K.positive _)

/-- immersion: a zero velocity would have `α = 0`. -/
theorem uc_immersion (K : TransverseKnot) (θ : ℝ) : deriv K.circle θ ≠ 0 := by
  intro h
  have := uc_transverse K θ
  rw [h] at this
  simp [alpha] at this

theorem u_circle : U_circle := fun K =>
  ⟨⟨uc_smooth K, uc_periodic K, uc_injective K, uc_immersion K⟩, uc_transverse K⟩
/-! #### Unit SL (helpers `usl_*`, PLAN_FINAL §6 U1): row 88 on the constant family, on a transverse
family, on the straight-line reparametrization family, and on the clocked strip of an isotopy. -/

/-- `slCircle` on its domain is `selfLinking` at the radius fixed by `Classical.choose`. -/
theorem usl_slCircle_eq {T : ℝ → E3} (hT : IsPositiveTransverseEmbedding (2 * π) T) :
    slCircle T = selfLinking (2 * π) T
      (Classical.choose (fd_linking_calculus.transverse_uniform (2 * π) (fun _ => T) hT.constFamily)) := by
  simp only [slCircle, hT, ↓reduceDIte]

/-- `α = dz − y dx` is linear in the vector. -/
theorem usl_contactForm_smul (p w : E3) (c : ℝ) :
    lcContactForm p (c • w) = c * lcContactForm p w := by
  simp [lcContactForm, smul_eq_mul]; ring

/-- The disjointness clause of `transverse_uniform` in the form `self_linking_invariant` consumes. -/
theorem usl_disjoint_of_uniform {P : ℝ} {F : ℝ → ℝ → E3} {ε₀ : ℝ}
    (h : ∀ s ∈ Icc (0:ℝ) 1, ∀ ε, 0 < ε → ε ≤ ε₀ →
      IsPositiveTransverseEmbedding P (F s) ∧
      IsPositiveTransverseEmbedding P (pushoff (F s) (fun _ => ey) ε) ∧
      DisjointPair P (F s) (pushoff (F s) (fun _ => ey) ε)) :
    ∀ s ∈ Icc (0:ℝ) 1, ∀ ε, 0 < ε → ε ≤ ε₀ → ∀ u u', pushoff (F s) (fun _ => ey) ε u ≠ F s u' :=
  fun s hs ε h1 h2 u u' => (h s hs ε h1 h2).2.2.disjoint u' u

theorem u_sl_radius : U_sl_radius := by
  intro T ε hT hε hdisj
  rw [usl_slCircle_eq hT]
  obtain ⟨hε₁, hunif⟩ := Classical.choose_spec
    (fd_linking_calculus.transverse_uniform (2 * π) (fun _ => T) hT.constFamily)
  set ε₁ := Classical.choose
    (fd_linking_calculus.transverse_uniform (2 * π) (fun _ => T) hT.constFamily) with hε₁def
  have hd₁ := usl_disjoint_of_uniform hunif
  have hd₂ : ∀ s ∈ Icc (0:ℝ) 1, ∀ ε', 0 < ε' → ε' ≤ ε → ∀ u u',
      pushoff ((fun _ => T) s) (fun _ => ey) ε' u ≠ (fun _ => T) s u' :=
    fun _ _ ε' h1 h2 u u' => hdisj ε' h1 h2 u u'
  have h01 : (0:ℝ) ∈ Icc (0:ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have e1 : selfLinking (2 * π) T ε₁ = selfLinking (2 * π) T (min ε ε₁) :=
    fd_linking_calculus.self_linking_invariant (2 * π) (fun _ => T) hT.constFamily ε₁ hε₁ hd₁
      0 h01 0 h01 ε₁ (min ε ε₁) hε₁ le_rfl (lt_min hε hε₁) (min_le_right _ _)
  have e2 : selfLinking (2 * π) T ε = selfLinking (2 * π) T (min ε ε₁) :=
    fd_linking_calculus.self_linking_invariant (2 * π) (fun _ => T) hT.constFamily ε hε hd₂
      0 h01 0 h01 ε (min ε ε₁) hε le_rfl (lt_min hε hε₁) (min_le_left _ _)
  rw [e1, e2]

theorem u_sl_family : U_sl_family := by
  intro F hF s hs s' hs'
  obtain ⟨ε₀, hε₀, hunif⟩ := fd_linking_calculus.transverse_uniform (2 * π) F hF
  have hd := usl_disjoint_of_uniform hunif
  have hr : ∀ s ∈ Icc (0:ℝ) 1, slCircle (F s) = selfLinking (2 * π) (F s) ε₀ := fun s hs =>
    u_sl_radius (F s) ε₀ (hunif s hs ε₀ hε₀ le_rfl).1 hε₀ (fun ε' h1 h2 => hd s hs ε' h1 h2)
  rw [hr s hs, hr s' hs']
  exact fd_linking_calculus.self_linking_invariant (2 * π) F hF ε₀ hε₀ hd s hs s' hs' ε₀ ε₀
    hε₀ le_rfl hε₀ le_rfl

/-- The lift property of a circle reparametrization for every integer: `ρ(θ + 2πk) = ρ(θ) + 2πk`
(`ρ − id` is `2π`-periodic). -/
theorem usl_reparam_lift_int {ρ : ℝ → ℝ} (hρ : IsCircleReparam ρ) (k : ℤ) (θ : ℝ) :
    ρ (θ + k * (2 * π)) = ρ θ + k * (2 * π) := by
  have hper : Periodic (fun θ => ρ θ - θ) (2 * π) := fun θ => by
    simp only [hρ.lift θ]; ring
  have h : ρ (θ + k * (2 * π)) - (θ + k * (2 * π)) = ρ θ - θ := hper.int_mul k θ
  linarith

/-- U1c's family: `ρ_s = (1 − s)·id + s·ρ` is a circle reparametrization for every `s ∈ [0,1]`
(`ρ_s′ = (1 − s) + s ρ′ > 0`, lift by `2π`), and `T ∘ ρ_s` is a transverse family of period `2π`
(`α((T∘ρ_s)′) = ρ_s′ · α(T′ ∘ ρ_s)`). -/
theorem usl_reparam_family {T : ℝ → E3} {ρ : ℝ → ℝ} (hT : IsPositiveTransverseEmbedding (2 * π) T)
    (hρ : IsCircleReparam ρ) :
    TransverseFamily (2 * π) (fun s θ => T ((1 - s) * θ + s * ρ θ)) := by
  have hρs_deriv : ∀ s θ, HasDerivAt (fun θ => (1 - s) * θ + s * ρ θ)
      ((1 - s) + s * deriv ρ θ) θ := by
    intro s θ
    have h1 : HasDerivAt (fun θ => (1 - s) * θ) ((1 - s) * 1) θ :=
      (hasDerivAt_id θ).const_mul (1 - s)
    have h2 : HasDerivAt (fun θ => s * ρ θ) (s * deriv ρ θ) θ :=
      (hρ.smooth.differentiable (by simp) θ).hasDerivAt.const_mul s
    have := h1.add h2
    rw [mul_one] at this
    exact this
  have hρs_pos : ∀ s ∈ Icc (0:ℝ) 1, ∀ θ, 0 < (1 - s) + s * deriv ρ θ := by
    intro s hs θ
    rcases eq_or_lt_of_le hs.1 with h | h
    · subst h; simp
    · exact add_pos_of_nonneg_of_pos (by linarith [hs.2]) (mul_pos h (hρ.deriv_pos θ))
  have hρs_lift : ∀ s (k : ℤ) θ, (1 - s) * (θ + k * (2 * π)) + s * ρ (θ + k * (2 * π)) =
      ((1 - s) * θ + s * ρ θ) + k * (2 * π) := by
    intro s k θ; rw [usl_reparam_lift_int hρ]; ring
  have hρs_mono : ∀ s ∈ Icc (0:ℝ) 1, StrictMono (fun θ => (1 - s) * θ + s * ρ θ) := fun s hs =>
    strictMono_of_deriv_pos fun θ => by rw [(hρs_deriv s θ).deriv]; exact hρs_pos s hs θ
  refine ⟨by positivity, ?_, ?_, ?_, ?_⟩
  · show ContDiff ℝ ∞ (T ∘ fun p : ℝ × ℝ => (1 - p.1) * p.2 + p.1 * ρ p.2)
    refine hT.circle.smooth.comp ?_
    have := hρ.smooth
    fun_prop
  · intro s θ
    show T ((1 - s) * (θ + 2 * π) + s * ρ (θ + 2 * π)) = T ((1 - s) * θ + s * ρ θ)
    have := hρs_lift s 1 θ
    simp only [Int.cast_one, one_mul] at this
    rw [this]
    exact hT.circle.periodic _
  · intro s hs u u' huu'
    obtain ⟨k, hk⟩ := hT.embedded _ _ huu'
    refine ⟨k, ?_⟩
    apply (hρs_mono s hs).injective
    show (1 - s) * u' + s * ρ u' = (1 - s) * (u + k * (2 * π)) + s * ρ (u + k * (2 * π))
    rw [hρs_lift]; exact hk
  · intro s hs u
    have hd : deriv (fun θ => T ((1 - s) * θ + s * ρ θ)) u =
        ((1 - s) + s * deriv ρ u) • deriv T ((1 - s) * u + s * ρ u) := by
      have := deriv.scomp (h := fun θ => (1 - s) * θ + s * ρ θ) (g₁ := T) u
        (hT.circle.smooth.differentiable (by simp) _) (hρs_deriv s u).differentiableAt
      rw [(hρs_deriv s u).deriv] at this
      exact this
    show 0 < lcContactForm (T ((1 - s) * u + s * ρ u))
      (deriv (fun θ => T ((1 - s) * θ + s * ρ θ)) u)
    rw [hd, usl_contactForm_smul]
    exact mul_pos (hρs_pos s hs u) (hT.positive _)

theorem u_sl_reparam : U_sl_reparam := by
  intro T ρ hT hρ
  have h := u_sl_family _ (usl_reparam_family hT hρ) 1 ⟨zero_le_one, le_rfl⟩ 0 ⟨le_rfl, zero_le_one⟩
  simp only [sub_self, zero_mul, one_mul, sub_zero, zero_add, add_zero] at h
  exact h

theorem usl_reparam_strictMono {ρ : ℝ → ℝ} (hρ : IsCircleReparam ρ) : StrictMono ρ :=
  strictMono_of_deriv_pos hρ.deriv_pos

/-- A circle reparametrization is onto `ℝ` (monotone, unbounded in both directions by the lift). -/
theorem usl_reparam_surjective {ρ : ℝ → ℝ} (hρ : IsCircleReparam ρ) : Surjective ρ := by
  have hmono := (usl_reparam_strictMono hρ).monotone
  have hpi : 0 < 2 * π := by positivity
  refine hρ.smooth.continuous.surjective (hmono.tendsto_atTop_atTop ?_)
    (hmono.tendsto_atBot_atBot ?_)
  · intro b
    obtain ⟨n, hn⟩ := exists_nat_ge ((b - ρ 0) / (2 * π))
    refine ⟨((n : ℤ) : ℝ) * (2 * π), ?_⟩
    have h := usl_reparam_lift_int hρ n 0
    rw [zero_add] at h
    rw [h, div_le_iff₀ hpi] at *
    push_cast
    linarith
  · intro b
    obtain ⟨n, hn⟩ := exists_nat_ge ((ρ 0 - b) / (2 * π))
    refine ⟨((-(n : ℤ) : ℤ) : ℝ) * (2 * π), ?_⟩
    have h := usl_reparam_lift_int hρ (-(n : ℤ)) 0
    rw [zero_add] at h
    rw [h, div_le_iff₀ hpi] at *
    push_cast
    linarith

/-- The inverse of a circle reparametrization is smooth (`Homeomorph.contDiff_symm_deriv`, `ρ′ ≠ 0`). -/
theorem usl_reparam_exists_inverse {ρ : ℝ → ℝ} (hρ : IsCircleReparam ρ) :
    ∃ σ : ℝ → ℝ, ContDiff ℝ ∞ σ ∧ (∀ θ, σ (ρ θ) = θ) ∧ (∀ θ, ρ (σ θ) = θ) := by
  have hmono := usl_reparam_strictMono hρ
  have hsurj := usl_reparam_surjective hρ
  obtain ⟨e, he⟩ : ∃ e : ℝ ≃ₜ ℝ, (e : ℝ → ℝ) = ρ :=
    ⟨(hmono.orderIsoOfSurjective ρ hsurj).toHomeomorph, by
      rw [OrderIso.coe_toHomeomorph, StrictMono.coe_orderIsoOfSurjective]⟩
  refine ⟨e.symm, ?_, ?_, ?_⟩
  · refine e.contDiff_symm_deriv (f' := deriv ρ) (fun x => (hρ.deriv_pos x).ne') ?_ ?_
    · intro x; rw [he]; exact (hρ.smooth.differentiable (by simp) x).hasDerivAt
    · rw [he]; exact hρ.smooth
  · intro θ; have := e.symm_apply_apply θ; rwa [he] at this
  · intro θ; have := e.apply_symm_apply θ; rwa [he] at this

/-- Row 84's "embedded positive transverse circle" is row 88's positive transverse embedding of period
`2π` (`2πk` versus `k·2π`). -/
theorem usl_embedding_of_circle {T : ℝ → E3} (h₁ : IsEmbeddedCircle T)
    (h₂ : IsPositiveTransverse T) : IsPositiveTransverseEmbedding (2 * π) T where
  circle := ⟨h₁.smooth, h₁.periodic⟩
  embedded := fun u u' huu' => by
    obtain ⟨k, hk⟩ := h₁.injective u u' huu'
    exact ⟨k, by rw [hk]; ring⟩
  positive := h₂

/-- If `T ∘ ρ` is a positive transverse embedding and `ρ` a circle reparametrization, so is `T`
(through the smooth inverse of `ρ`; `α((T∘ρ)′) = ρ′ · α(T′ ∘ ρ)`). -/
theorem usl_transverseEmbedding_of_comp {T : ℝ → E3} {ρ : ℝ → ℝ} (hρ : IsCircleReparam ρ)
    (h : IsPositiveTransverseEmbedding (2 * π) (T ∘ ρ)) :
    IsPositiveTransverseEmbedding (2 * π) T := by
  obtain ⟨σ, hσ, hσρ, hρσ⟩ := usl_reparam_exists_inverse hρ
  have hTeq : T = (T ∘ ρ) ∘ σ := by funext θ; simp [Function.comp, hρσ]
  have hTs : ContDiff ℝ ∞ T := by rw [hTeq]; exact h.circle.smooth.comp hσ
  refine ⟨⟨hTs, ?_⟩, ?_, ?_⟩
  · intro θ
    have h1 : θ + 2 * π = ρ (σ θ + 2 * π) := by rw [hρ.lift, hρσ]
    have h2 := h.circle.periodic (σ θ)
    simp only [Function.comp] at h2
    rw [h1, h2, hρσ]
  · intro u u' huu'
    have : (T ∘ ρ) (σ u) = (T ∘ ρ) (σ u') := by simp [Function.comp, hρσ, huu']
    obtain ⟨k, hk⟩ := h.embedded _ _ this
    refine ⟨k, ?_⟩
    calc u' = ρ (σ u') := (hρσ u').symm
      _ = ρ (σ u + k * (2 * π)) := by rw [hk]
      _ = u + k * (2 * π) := by rw [usl_reparam_lift_int hρ, hρσ]
  · intro u
    have hpos := h.positive (σ u)
    have hd : deriv (T ∘ ρ) (σ u) = deriv ρ (σ u) • deriv T (ρ (σ u)) :=
      deriv.scomp (σ u) (hTs.differentiable (by simp) _) (hρ.smooth.differentiable (by simp) _)
    rw [hd, Function.comp_apply, hρσ, usl_contactForm_smul] at hpos
    exact pos_of_mul_pos_right hpos (hρ.deriv_pos _).le

/-- U1's family: the strip family of a transverse isotopy composed with the clock
`η = Real.smoothTransition` (`η = 0` on `s ≤ 0`, `1` on `s ≥ 1`, `η ∈ [0,1]`) is a transverse family
of period `2π` on all of `ℝ × ℝ` (`ContDiffOn.comp_contDiff`). -/
theorem usl_isotopy_family {F : ℝ → ℝ → E3} (hF : ContDiffOn ℝ ∞ (uncurry F) (Icc 0 1 ×ˢ univ))
    (hs : ∀ s ∈ Icc (0 : ℝ) 1, IsEmbeddedCircle (F s) ∧ IsPositiveTransverse (F s)) :
    TransverseFamily (2 * π) (fun s => F (Real.smoothTransition s)) := by
  have hmem : ∀ s, Real.smoothTransition s ∈ Icc (0:ℝ) 1 := fun s =>
    ⟨Real.smoothTransition.nonneg s, Real.smoothTransition.le_one s⟩
  refine ⟨by positivity, ?_, ?_, ?_, ?_⟩
  · show ContDiff ℝ ∞ (uncurry F ∘ fun p : ℝ × ℝ => (Real.smoothTransition p.1, p.2))
    exact hF.comp_contDiff
      ((Real.smoothTransition.contDiff.comp contDiff_fst).prodMk contDiff_snd)
      (fun p => ⟨hmem p.1, mem_univ _⟩)
  · intro s; exact (hs _ (hmem s)).1.periodic
  · intro s _ u u' huu'
    obtain ⟨k, hk⟩ := (hs _ (hmem s)).1.injective u u' huu'
    exact ⟨k, by rw [hk]; ring⟩
  · intro s _ u; exact (hs _ (hmem s)).2 u

theorem u_sl_isotopy : U_sl_isotopy := by
  intro T₀ T₁ hiso
  obtain ⟨F, hF, hs, h0, ρ, hρ, h1⟩ := hiso
  have key := u_sl_family _ (usl_isotopy_family hF hs) 0 ⟨le_rfl, zero_le_one⟩ 1
    ⟨zero_le_one, le_rfl⟩
  simp only [Real.smoothTransition.zero, Real.smoothTransition.one, h0, h1] at key
  have hT₁ : IsPositiveTransverseEmbedding (2 * π) T₁ := by
    have h := hs 1 ⟨zero_le_one, le_rfl⟩
    rw [h1] at h
    exact usl_transverseEmbedding_of_comp hρ (usl_embedding_of_circle h.1 h.2)
  rw [key]
  exact u_sl_reparam T₁ ρ hT₁ hρ

/-! ### Unit LEG (U2 + U3) helpers, prefix `ulg_` -/

/-- The 1-periodic spatial curve of a 2π-periodic circle `Lc` in `E3`: `t ↦ toSpace (Lc (2πt))`. -/
def ulg_T (Lc : ℝ → E3) : ℝ → Space := fun t => toSpace (Lc (2 * π * t))

theorem ulg_T_def (Lc : ℝ → E3) (t : ℝ) : ulg_T Lc t = toSpace (Lc (2 * π * t)) := rfl

theorem ulg_contDiff_toSpace : ContDiff ℝ ∞ toSpace :=
  (ContactMotions.contDiff_coord 0).prodMk
    ((ContactMotions.contDiff_coord 1).prodMk (ContactMotions.contDiff_coord 2))

theorem ulg_toSpace_injective : Function.Injective toSpace := by
  intro p q h
  have h' := congrArg toE3 h
  rwa [toE3_toSpace, toE3_toSpace] at h'

theorem ulg_two_pi_pos : 0 < 2 * π := by positivity
theorem ulg_two_pi_ne : (2 * π) ≠ 0 := ulg_two_pi_pos.ne'

/-- chain rule through the scaling `t ↦ 2πt` -/
theorem ulg_hasDerivAt_scale {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℝ → F} {f' : F} {t : ℝ} (hf : HasDerivAt f f' (2 * π * t)) :
    HasDerivAt (fun s => f (2 * π * s)) ((2 * π) • f') t := by
  have h : HasDerivAt (fun s : ℝ => 2 * π * s) (2 * π) t := by
    simpa using (hasDerivAt_id t).const_mul (2 * π)
  exact hf.scomp t h

theorem ulg_smooth_scale {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : ℝ → F}
    (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (fun s => f (2 * π * s)) :=
  hf.comp (contDiff_const.mul contDiff_id)

theorem ulg_T_smooth {Lc : ℝ → E3} (hLc : ContDiff ℝ ∞ Lc) : ContDiff ℝ ∞ (ulg_T Lc) :=
  ulg_contDiff_toSpace.comp (ulg_smooth_scale hLc)

theorem ulg_T_periodic {Lc : ℝ → E3} (hper : Periodic Lc (2 * π)) : Periodic (ulg_T Lc) 1 := by
  intro t
  show toSpace (Lc (2 * π * (t + 1))) = toSpace (Lc (2 * π * t))
  rw [show 2 * π * (t + 1) = 2 * π * t + 2 * π by ring, hper]

/-- the coordinate functions of the curve are the coordinates of `Lc` at `2πt` (all `rfl`) -/
theorem ulg_xOf (Lc : ℝ → E3) : xOf (ulg_T Lc) = fun t => GenericFront.coordX Lc (2 * π * t) := rfl
theorem ulg_yOf (Lc : ℝ → E3) : yOf (ulg_T Lc) = fun t => GenericFront.coordY Lc (2 * π * t) := rfl
theorem ulg_zOf (Lc : ℝ → E3) : zOf (ulg_T Lc) = fun t => GenericFront.coordZ Lc (2 * π * t) := rfl
theorem ulg_xzOf (Lc : ℝ → E3) (t : ℝ) : xzOf (ulg_T Lc) t = GenericFront.front Lc (2 * π * t) := rfl

theorem ulg_hasDerivAt_coord {Lc : ℝ → E3} (hLc : ContDiff ℝ ∞ Lc) (θ : ℝ) (i : Fin 3) :
    HasDerivAt (fun θ => Lc θ i) (deriv Lc θ i) θ :=
  ContactMotions.hasDerivAt_coord ((hLc.differentiable (by simp) θ).hasDerivAt) i

theorem ulg_hasDerivAt_xOf {Lc : ℝ → E3} (hLc : ContDiff ℝ ∞ Lc) (t : ℝ) :
    HasDerivAt (xOf (ulg_T Lc)) (2 * π * deriv Lc (2 * π * t) 0) t := by
  have h := ulg_hasDerivAt_scale (ulg_hasDerivAt_coord hLc (2 * π * t) 0)
  rw [smul_eq_mul] at h
  exact h

theorem ulg_hasDerivAt_yOf {Lc : ℝ → E3} (hLc : ContDiff ℝ ∞ Lc) (t : ℝ) :
    HasDerivAt (yOf (ulg_T Lc)) (2 * π * deriv Lc (2 * π * t) 1) t := by
  have h := ulg_hasDerivAt_scale (ulg_hasDerivAt_coord hLc (2 * π * t) 1)
  rw [smul_eq_mul] at h
  exact h

theorem ulg_hasDerivAt_zOf {Lc : ℝ → E3} (hLc : ContDiff ℝ ∞ Lc) (t : ℝ) :
    HasDerivAt (zOf (ulg_T Lc)) (2 * π * deriv Lc (2 * π * t) 2) t := by
  have h := ulg_hasDerivAt_scale (ulg_hasDerivAt_coord hLc (2 * π * t) 2)
  rw [smul_eq_mul] at h
  exact h

theorem ulg_deriv_xOf {Lc : ℝ → E3} (hLc : ContDiff ℝ ∞ Lc) (t : ℝ) :
    deriv (xOf (ulg_T Lc)) t = 2 * π * deriv Lc (2 * π * t) 0 := (ulg_hasDerivAt_xOf hLc t).deriv
theorem ulg_deriv_yOf {Lc : ℝ → E3} (hLc : ContDiff ℝ ∞ Lc) (t : ℝ) :
    deriv (yOf (ulg_T Lc)) t = 2 * π * deriv Lc (2 * π * t) 1 := (ulg_hasDerivAt_yOf hLc t).deriv
theorem ulg_deriv_zOf {Lc : ℝ → E3} (hLc : ContDiff ℝ ∞ Lc) (t : ℝ) :
    deriv (zOf (ulg_T Lc)) t = 2 * π * deriv Lc (2 * π * t) 2 := (ulg_hasDerivAt_zOf hLc t).deriv

theorem ulg_hasDerivAt_xzOf {Lc : ℝ → E3} (hLc : ContDiff ℝ ∞ Lc) (t : ℝ) :
    HasDerivAt (xzOf (ulg_T Lc)) (2 * π * deriv Lc (2 * π * t) 0, 2 * π * deriv Lc (2 * π * t) 2) t :=
  (ulg_hasDerivAt_xOf hLc t).prodMk (ulg_hasDerivAt_zOf hLc t)

theorem ulg_deriv_xzOf {Lc : ℝ → E3} (hLc : ContDiff ℝ ∞ Lc) (t : ℝ) :
    deriv (xzOf (ulg_T Lc)) t = (2 * π * deriv Lc (2 * π * t) 0, 2 * π * deriv Lc (2 * π * t) 2) :=
  (ulg_hasDerivAt_xzOf hLc t).deriv

theorem ulg_hasDerivAt_T {Lc : ℝ → E3} (hLc : ContDiff ℝ ∞ Lc) (t : ℝ) :
    HasDerivAt (ulg_T Lc)
      (2 * π * deriv Lc (2 * π * t) 0, 2 * π * deriv Lc (2 * π * t) 1, 2 * π * deriv Lc (2 * π * t) 2) t :=
  (ulg_hasDerivAt_xOf hLc t).prodMk ((ulg_hasDerivAt_yOf hLc t).prodMk (ulg_hasDerivAt_zOf hLc t))

theorem ulg_deriv_T {Lc : ℝ → E3} (hLc : ContDiff ℝ ∞ Lc) (t : ℝ) :
    deriv (ulg_T Lc) t =
      (2 * π * deriv Lc (2 * π * t) 0, 2 * π * deriv Lc (2 * π * t) 1, 2 * π * deriv Lc (2 * π * t) 2) :=
  (ulg_hasDerivAt_T hLc t).deriv

/-- Legendrian: `z′ = y x′` -/
theorem ulg_z' {Lc : ℝ → E3} (h2 : GenericFront.IsLegendrian Lc) (θ : ℝ) :
    deriv Lc θ 2 = Lc θ 1 * deriv Lc θ 0 := by
  have h := h2 θ
  unfold GenericFront.alpha at h
  exact sub_eq_zero.mp h

/-- the projected velocity vanishes iff `x′ = 0` (`z′ = y x′`) -/
theorem ulg_deriv_xzOf_eq_zero_iff {Lc : ℝ → E3} (hLc : ContDiff ℝ ∞ Lc)
    (h2 : GenericFront.IsLegendrian Lc) (t : ℝ) :
    deriv (xzOf (ulg_T Lc)) t = 0 ↔ deriv Lc (2 * π * t) 0 = 0 := by
  rw [ulg_deriv_xzOf hLc t, ulg_z' h2]
  constructor
  · intro h
    have h' := congrArg Prod.fst h
    simpa [Real.pi_ne_zero] using h'
  · intro h
    rw [h]; simp

theorem ulg_deriv_T_ne_zero {Lc : ℝ → E3} (h1 : GenericFront.IsEmbeddedCircle Lc) (t : ℝ) :
    deriv (ulg_T Lc) t ≠ 0 := by
  intro h
  rw [ulg_deriv_T h1.smooth t] at h
  apply h1.immersion (2 * π * t)
  have h0 := congrArg Prod.fst h
  have h1' := congrArg (fun p : Space => p.2.1) h
  have h2' := congrArg (fun p : Space => p.2.2) h
  simp [Real.pi_ne_zero] at h0 h1' h2'
  ext i; fin_cases i
  · simpa using h0
  · simpa using h1'
  · simpa using h2'

theorem ulg_T_sameT {Lc : ℝ → E3} (h1 : GenericFront.IsEmbeddedCircle Lc) {s t : ℝ}
    (h : ulg_T Lc s = ulg_T Lc t) : SameT s t := by
  obtain ⟨k, hk⟩ := h1.injective _ _ (ulg_toSpace_injective h)
  refine ⟨k, ?_⟩
  apply mul_left_cancel₀ ulg_two_pi_ne
  rw [hk]; ring

theorem ulg_sameT_iff (s t : ℝ) : SameT s t ↔ GenericFront.SameParam (2 * π * s) (2 * π * t) := by
  constructor
  · rintro ⟨n, hn⟩; exact ⟨n, by rw [hn]; ring⟩
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    apply mul_left_cancel₀ ulg_two_pi_ne
    rw [hk]; ring

theorem ulg_mem_Ico_iff (t : ℝ) : t ∈ Ico (0 : ℝ) 1 ↔ 2 * π * t ∈ Ico 0 (2 * π) := by
  have hπ := ulg_two_pi_pos
  simp only [mem_Ico]
  constructor
  · rintro ⟨h0, h1⟩; exact ⟨by positivity, by nlinarith⟩
  · rintro ⟨h0, h1⟩; exact ⟨by nlinarith, by nlinarith⟩

theorem ulg_not_sameParam_of_ne {t s : ℝ} (ht : t ∈ Ico (0 : ℝ) 1) (hs : s ∈ Ico (0 : ℝ) 1)
    (hne : t ≠ s) : ¬ GenericFront.SameParam (2 * π * t) (2 * π * s) :=
  fun h => hne (SameT.eq_of_mem_Ico ht hs ((ulg_sameT_iff t s).2 h))

theorem ulg_abs_scale_lt {s t δ : ℝ} (h : |s - t| < δ / (2 * π)) :
    |2 * π * s - 2 * π * t| < δ := by
  have hπ := ulg_two_pi_pos
  rw [show 2 * π * s - 2 * π * t = 2 * π * (s - t) by ring, abs_mul, abs_of_pos hπ]
  have h' := mul_lt_mul_of_pos_left h hπ
  have e : 2 * π * (δ / (2 * π)) = δ := by field_simp
  rwa [e] at h'

theorem ulg_mem_cuspSet_iff {Lc : ℝ → E3} (hLc : ContDiff ℝ ∞ Lc) (θ : ℝ) :
    θ ∈ GenericFront.cuspSet Lc ↔ deriv Lc θ 0 = 0 := by
  show deriv (GenericFront.coordX Lc) θ = 0 ↔ _
  rw [(GenericFront.gp4_deriv_coord hLc θ).1]

/-! #### The spatial link of `Lc` (U3) -/

/-- the one-component spatial link `t ↦ toSpace (Lc (2πt))` -/
def ulg_sp {Lc : ℝ → E3} (h1 : GenericFront.IsEmbeddedCircle Lc) : SpatialLink 1 where
  T := fun _ => ulg_T Lc
  smooth := fun _ => ulg_T_smooth h1.smooth
  periodic := fun _ => ulg_T_periodic h1.periodic
  embedded := fun i j _ _ h => ⟨Subsingleton.elim i j, ulg_T_sameT h1 h⟩
  regular := fun _ t => ulg_deriv_T_ne_zero h1 t

theorem ulg_sp_T {Lc : ℝ → E3} (h1 : GenericFront.IsEmbeddedCircle Lc) (i : Fin 1) (t : ℝ) :
    (ulg_sp h1).T i t = toSpace (Lc (2 * π * t)) := rfl

theorem ulg_sp_projLoop_γ {Lc : ℝ → E3} (h1 : GenericFront.IsEmbeddedCircle Lc) (i : Fin 1) :
    ((ulg_sp h1).projLoop i).γ = xzOf (ulg_T Lc) := rfl

theorem ulg_isCusp_iff {Lc : ℝ → E3} (h1 : GenericFront.IsEmbeddedCircle Lc)
    (h2 : GenericFront.IsLegendrian Lc) (i : Fin 1) (t : ℝ) :
    (ulg_sp h1).IsCusp i t ↔ deriv Lc (2 * π * t) 0 = 0 :=
  ulg_deriv_xzOf_eq_zero_iff h1.smooth h2 t

theorem ulg_cuspSet_finite {Lc : ℝ → E3} (h1 : GenericFront.IsEmbeddedCircle Lc)
    (h2 : GenericFront.IsLegendrian Lc) (h3 : GenericFront.IsGenericFront Lc) :
    (ulg_sp h1).cuspSet.Finite := by
  refine (h3.finite_cusps.image (fun θ => ((0 : Fin 1), θ / (2 * π)))).subset ?_
  rintro ⟨i, t⟩ ⟨ht, hc⟩
  refine ⟨2 * π * t, ⟨(ulg_mem_cuspSet_iff h1.smooth _).2 ((ulg_isCusp_iff h1 h2 i t).1 hc),
    (ulg_mem_Ico_iff t).1 ht⟩, ?_⟩
  simp only [Prod.mk.injEq]
  exact ⟨Subsingleton.elim _ _, mul_div_cancel_left₀ t ulg_two_pi_ne⟩

theorem ulg_exact_germ {Lc : ℝ → E3} (h1 : GenericFront.IsEmbeddedCircle Lc)
    (h2 : GenericFront.IsLegendrian Lc) (h3 : GenericFront.IsGenericFront Lc) :
    ∀ p ∈ (ulg_sp h1).cuspSet, (ulg_sp h1).ExactCuspGerm p.1 p.2 := by
  rintro ⟨i, t₀⟩ ⟨-, hc⟩
  have hLc := h1.smooth
  have hθc : 2 * π * t₀ ∈ GenericFront.cuspSet Lc :=
    (ulg_mem_cuspSet_iff hLc _).2 ((ulg_isCusp_iff h1 h2 i t₀).1 hc)
  obtain ⟨A, hA, hy', ε, hε, hgerm⟩ := h3.exact_germ _ hθc
  -- `y′ ≠ 0` on a neighbourhood of the cusp parameter, by continuity
  have hycont : Continuous (deriv (GenericFront.coordY Lc)) :=
    ((ContactMotions.contDiff_coord 1).comp hLc).continuous_deriv (by simp)
  obtain ⟨δ₁, hδ₁, hball⟩ := Metric.eventually_nhds_iff.1 (hycont.continuousAt.eventually_ne hy')
  have hδ : 0 < min ε δ₁ / (2 * π) := by positivity
  refine ⟨A, min ε δ₁ / (2 * π), hA, hδ, ?_, ?_⟩
  · intro t ht
    have habs : |2 * π * t - 2 * π * t₀| < min ε δ₁ :=
      ulg_abs_scale_lt (abs_sub_lt_iff.2 ⟨by linarith [ht.1, ht.2], by linarith [ht.1, ht.2]⟩)
    show deriv (yOf (ulg_T Lc)) t ≠ 0
    rw [ulg_deriv_yOf hLc t]
    refine mul_ne_zero ulg_two_pi_ne ?_
    rw [← (GenericFront.gp4_deriv_coord hLc _).2.1]
    exact hball (by rw [Real.dist_eq]; exact lt_of_lt_of_le habs (min_le_right _ _))
  · intro t ht
    have habs : |2 * π * t - 2 * π * t₀| < min ε δ₁ :=
      ulg_abs_scale_lt (abs_sub_lt_iff.2 ⟨by linarith [ht.1, ht.2], by linarith [ht.1, ht.2]⟩)
    obtain ⟨hx, hz⟩ := hgerm _ (lt_of_lt_of_le habs (min_le_left _ _))
    refine Prod.ext hx (Prod.ext rfl ?_)
    show GenericFront.coordZ Lc (2 * π * t) = GenericFront.coordZ Lc (2 * π * t₀) +
      A * GenericFront.coordY Lc (2 * π * t₀) *
        (GenericFront.coordY Lc (2 * π * t) - GenericFront.coordY Lc (2 * π * t₀)) ^ 2 +
      2 * A / 3 * (GenericFront.coordY Lc (2 * π * t) - GenericFront.coordY Lc (2 * π * t₀)) ^ 3
    rw [hz]; ring

theorem ulg_isDoubleOf_iff {Lc : ℝ → E3} (h1 : GenericFront.IsEmbeddedCircle Lc) (p q : Fin 1 × ℝ) :
    SmoothFront.IsDoubleOf (ulg_sp h1).projLoop p q ↔
      (2 * π * p.2, 2 * π * q.2) ∈ GenericFront.doublePoints Lc := by
  obtain ⟨i, t⟩ := p
  obtain ⟨j, s⟩ := q
  show (¬ SameParam (i, t) (j, s) ∧ xzOf (ulg_T Lc) t = xzOf (ulg_T Lc) s) ↔
    (¬ GenericFront.SameParam (2 * π * t) (2 * π * s) ∧
      GenericFront.front Lc (2 * π * t) = GenericFront.front Lc (2 * π * s))
  rw [SameT.sameParam_iff, ulg_sameT_iff]
  exact Iff.rfl

theorem ulg_doubles_finite {Lc : ℝ → E3} (h1 : GenericFront.IsEmbeddedCircle Lc)
    (h3 : GenericFront.IsGenericFront Lc) :
    (SmoothFront.occSetOf (ulg_sp h1).projLoop).Finite := by
  refine (h3.finite_double.image (fun z : ℝ × ℝ => ((0 : Fin 1), z.1 / (2 * π)))).subset ?_
  rintro ⟨i, t⟩ ⟨ht, ⟨j, s⟩, hs, hne, heq⟩
  refine ⟨(2 * π * t, 2 * π * s),
    ⟨⟨ulg_not_sameParam_of_ne ht hs (fun h => hne (Prod.ext (Subsingleton.elim i j) h)), heq⟩,
      (ulg_mem_Ico_iff t).1 ht, (ulg_mem_Ico_iff s).1 hs⟩, ?_⟩
  simp only [Prod.mk.injEq]
  exact ⟨Subsingleton.elim _ _, mul_div_cancel_left₀ t ulg_two_pi_ne⟩

theorem ulg_pairs_finite {Lc : ℝ → E3} (h3 : GenericFront.IsGenericFront Lc) :
    {q : Param 1 × Param 1 | q.1.2 ∈ Ico (0 : ℝ) 1 ∧ q.2.2 ∈ Ico (0 : ℝ) 1 ∧ q.1 ≠ q.2 ∧
      xzOf (ulg_T Lc) q.1.2 = xzOf (ulg_T Lc) q.2.2}.Finite := by
  refine (h3.finite_double.image
    (fun z : ℝ × ℝ => (((0 : Fin 1), z.1 / (2 * π)), ((0 : Fin 1), z.2 / (2 * π))))).subset ?_
  rintro ⟨⟨i, t⟩, ⟨j, s⟩⟩ ⟨ht, hs, hne, heq⟩
  refine ⟨(2 * π * t, 2 * π * s),
    ⟨⟨ulg_not_sameParam_of_ne ht hs (fun h => hne (Prod.ext (Subsingleton.elim i j) h)), heq⟩,
      (ulg_mem_Ico_iff t).1 ht, (ulg_mem_Ico_iff s).1 hs⟩, ?_⟩
  simp only [Prod.mk.injEq]
  exact ⟨⟨Subsingleton.elim _ _, mul_div_cancel_left₀ t ulg_two_pi_ne⟩,
    ⟨Subsingleton.elim _ _, mul_div_cancel_left₀ s ulg_two_pi_ne⟩⟩

theorem ulg_transverse {Lc : ℝ → E3} (h1 : GenericFront.IsEmbeddedCircle Lc)
    (h3 : GenericFront.IsGenericFront Lc) :
    ∀ p q : Fin 1 × ℝ, SmoothFront.IsDoubleOf (ulg_sp h1).projLoop p q →
      det (deriv (xzOf ((ulg_sp h1).T p.1)) p.2) (deriv (xzOf ((ulg_sp h1).T q.1)) q.2) ≠ 0 := by
  intro p q hpq
  have hLc := h1.smooth
  have hd := h3.transverse_double _ ((ulg_isDoubleOf_iff h1 p q).1 hpq)
  unfold GenericFront.IsTransverseDouble at hd
  have e1 := GenericFront.gp4_deriv_coord hLc (2 * π * p.2)
  have e2 := GenericFront.gp4_deriv_coord hLc (2 * π * q.2)
  rw [e1.1, e1.2.2, e2.1, e2.2.2] at hd
  show det (deriv (xzOf (ulg_T Lc)) p.2) (deriv (xzOf (ulg_T Lc)) q.2) ≠ 0
  rw [ulg_deriv_xzOf hLc, ulg_deriv_xzOf hLc]
  have e : det (2 * π * deriv Lc (2 * π * p.2) 0, 2 * π * deriv Lc (2 * π * p.2) 2)
      (2 * π * deriv Lc (2 * π * q.2) 0, 2 * π * deriv Lc (2 * π * q.2) 2) =
      (2 * π) ^ 2 * (deriv Lc (2 * π * p.2) 0 * deriv Lc (2 * π * q.2) 2 -
        deriv Lc (2 * π * p.2) 2 * deriv Lc (2 * π * q.2) 0) := by
    simp only [det]; ring
  rw [e]
  exact mul_ne_zero (pow_ne_zero 2 ulg_two_pi_ne) hd

theorem ulg_no_triple {Lc : ℝ → E3} (h1 : GenericFront.IsEmbeddedCircle Lc)
    (h3 : GenericFront.IsGenericFront Lc) :
    ∀ p q r : Fin 1 × ℝ, SmoothFront.IsDoubleOf (ulg_sp h1).projLoop p q →
      SmoothFront.IsDoubleOf (ulg_sp h1).projLoop q r →
      SmoothFront.IsDoubleOf (ulg_sp h1).projLoop p r → False := by
  intro p q r hpq hqr hpr
  rw [ulg_isDoubleOf_iff] at hpq hqr hpr
  exact h3.no_triple _ _ _ hpq.1 hpr.1 hqr.1 ⟨hpq.2, hpr.2⟩

theorem ulg_heights_distinct {Lc : ℝ → E3} (h1 : GenericFront.IsEmbeddedCircle Lc) :
    ∀ p q : Fin 1 × ℝ, SmoothFront.IsDoubleOf (ulg_sp h1).projLoop p q →
      (ulg_sp h1).height p ≠ (ulg_sp h1).height q := by
  intro p q hpq hy
  have hd := (ulg_isDoubleOf_iff h1 p q).1 hpq
  apply hd.1
  have hfr : GenericFront.front Lc (2 * π * p.2) = GenericFront.front Lc (2 * π * q.2) := hd.2
  have h0 : Lc (2 * π * p.2) 0 = Lc (2 * π * q.2) 0 := congrArg Prod.fst hfr
  have h2 : Lc (2 * π * p.2) 2 = Lc (2 * π * q.2) 2 := congrArg Prod.snd hfr
  have hy' : Lc (2 * π * p.2) 1 = Lc (2 * π * q.2) 1 := hy
  have hLeq : Lc (2 * π * p.2) = Lc (2 * π * q.2) := by
    ext i; fin_cases i
    · simpa using h0
    · simpa using hy'
    · simpa using h2
  obtain ⟨k, hk⟩ := h1.injective _ _ hLeq
  exact ⟨k, hk⟩

theorem ulg_cusped {Lc : ℝ → E3} (h1 : GenericFront.IsEmbeddedCircle Lc)
    (h2 : GenericFront.IsLegendrian Lc) (h3 : GenericFront.IsGenericFront Lc) :
    (ulg_sp h1).CuspedProjection where
  cusps_finite := ulg_cuspSet_finite h1 h2 h3
  exact_germ := ulg_exact_germ h1 h2 h3
  doubles_finite := ulg_doubles_finite h1 h3
  transverse := ulg_transverse h1 h3
  no_triple := ulg_no_triple h1 h3
  heights_distinct := ulg_heights_distinct h1

/-! #### The front of `Lc` (U2): the cusp clauses under the nonlinear coordinate `u = y − y₀` -/

theorem ulg_iteratedDeriv_two {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (f : ℝ → F) :
    iteratedDeriv 2 f = deriv (deriv f) := by
  rw [iteratedDeriv_succ, iteratedDeriv_one]

theorem ulg_iteratedDeriv_three {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (f : ℝ → F) :
    iteratedDeriv 3 f = deriv (deriv (deriv f)) := by
  rw [iteratedDeriv_succ, ulg_iteratedDeriv_two]

/-- Chain rule to order 3 for `g ∘ u` at a point where `g′(u t) = 0`:
`(g∘u)″ = u′² g″(u)`, `(g∘u)‴ = 3u′u″ g″(u) + u′³ g‴(u)`. -/
theorem ulg_comp_derivs {g : ℝ → Plane} {u : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) (hu : ContDiff ℝ ∞ u)
    (t : ℝ) (h0 : deriv g (u t) = 0) :
    deriv (deriv (g ∘ u)) t = (deriv u t * deriv u t) • deriv (deriv g) (u t) ∧
    deriv (deriv (deriv (g ∘ u))) t =
      (3 * (deriv u t * deriv (deriv u) t)) • deriv (deriv g) (u t) +
        (deriv u t * deriv u t * deriv u t) • deriv (deriv (deriv g)) (u t) := by
  have hg1 : ContDiff ℝ ∞ (deriv g) := hg.iterate_deriv 1
  have hg2 : ContDiff ℝ ∞ (deriv (deriv g)) := hg.iterate_deriv 2
  have hu1 : ContDiff ℝ ∞ (deriv u) := hu.iterate_deriv 1
  have hu2 : ContDiff ℝ ∞ (deriv (deriv u)) := hu.iterate_deriv 2
  have dg : ∀ x, HasDerivAt g (deriv g x) x := fun x => (hg.differentiable (by simp) x).hasDerivAt
  have dg1 : ∀ x, HasDerivAt (deriv g) (deriv (deriv g) x) x :=
    fun x => (hg1.differentiable (by simp) x).hasDerivAt
  have dg2 : ∀ x, HasDerivAt (deriv (deriv g)) (deriv (deriv (deriv g)) x) x :=
    fun x => (hg2.differentiable (by simp) x).hasDerivAt
  have du : ∀ x, HasDerivAt u (deriv u x) x := fun x => (hu.differentiable (by simp) x).hasDerivAt
  have du1 : ∀ x, HasDerivAt (deriv u) (deriv (deriv u) x) x :=
    fun x => (hu1.differentiable (by simp) x).hasDerivAt
  have du2 : ∀ x, HasDerivAt (deriv (deriv u)) (deriv (deriv (deriv u)) x) x :=
    fun x => (hu2.differentiable (by simp) x).hasDerivAt
  -- first derivative, as a function
  have e1 : deriv (g ∘ u) = fun s => deriv u s • deriv g (u s) :=
    funext fun s => ((dg (u s)).scomp s (du s)).deriv
  -- second derivative, as a function
  have e2 : deriv (deriv (g ∘ u)) = fun s =>
      deriv (deriv u) s • deriv g (u s) + (deriv u s * deriv u s) • deriv (deriv g) (u s) := by
    rw [e1]
    funext s
    have h : HasDerivAt (fun s => deriv u s • deriv g (u s))
        (deriv u s • (deriv u s • deriv (deriv g) (u s)) + deriv (deriv u) s • deriv g (u s)) s :=
      (du1 s).smul ((dg1 (u s)).scomp s (du s))
    rw [h.deriv, smul_smul, add_comm]
  -- third derivative at `t`
  have h3 : HasDerivAt (fun s =>
      deriv (deriv u) s • deriv g (u s) + (deriv u s * deriv u s) • deriv (deriv g) (u s))
      ((deriv (deriv u) t • (deriv u t • deriv (deriv g) (u t)) +
          deriv (deriv (deriv u)) t • deriv g (u t)) +
        ((deriv u t * deriv u t) • (deriv u t • deriv (deriv (deriv g)) (u t)) +
          (deriv (deriv u) t * deriv u t + deriv u t * deriv (deriv u) t) • deriv (deriv g) (u t))) t :=
    ((du2 t).smul ((dg1 (u t)).scomp t (du t))).add
      (((du1 t).mul (du1 t)).smul ((dg2 (u t)).scomp t (du t)))
  refine ⟨?_, ?_⟩
  · rw [e2]
    simp only
    rw [h0, smul_zero, zero_add]
  · rw [e2, h3.deriv, h0, smul_zero, add_zero]
    refine Prod.ext ?_ ?_ <;>
      simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;> ring

/-- The cusp clauses of ng:front-domain for a loop that is, near `t`, the printed exact germ in a
smooth coordinate `u` with `u t = 0`, `u′ t ≠ 0`: `det(γ″, γ‴) = 8A² u′⁵ ≠ 0`, `x″ = 2A u′² ≠ 0`. -/
theorem ulg_germ_cusp {A y₀ x₀ z₀ : ℝ} (hA : A ≠ 0) {u : ℝ → ℝ} (hu : ContDiff ℝ ∞ u) {t : ℝ}
    (hu0 : u t = 0) (hu' : deriv u t ≠ 0) {γ : ℝ → Plane}
    (hγ : Filter.EventuallyEq (nhds t) γ (germFront A y₀ x₀ z₀ ∘ u)) :
    det (iteratedDeriv 2 γ t) (iteratedDeriv 3 γ t) ≠ 0 ∧ (iteratedDeriv 2 γ t).1 ≠ 0 := by
  rw [ulg_iteratedDeriv_two, ulg_iteratedDeriv_three, hγ.deriv.deriv_eq, hγ.deriv.deriv.deriv_eq]
  have hg : ContDiff ℝ ∞ (germFront A y₀ x₀ z₀) := germFront_smooth A y₀ x₀ z₀
  have h0 : deriv (germFront A y₀ x₀ z₀) (u t) = 0 := by
    rw [hu0, deriv_germFront]; simp
  obtain ⟨e2, e3⟩ := ulg_comp_derivs hg hu t h0
  rw [e2, e3, hu0]
  have g2 : deriv (deriv (germFront A y₀ x₀ z₀)) 0 = (2 * A, 2 * A * y₀) := by
    rw [← ulg_iteratedDeriv_two, iteratedDeriv_two_germFront]; simp
  have g3 : deriv (deriv (deriv (germFront A y₀ x₀ z₀))) 0 = (0, 4 * A) := by
    rw [← ulg_iteratedDeriv_three, iteratedDeriv_three_germFront]
  rw [g2, g3]
  constructor
  · have e : det ((deriv u t * deriv u t) • ((2 * A, 2 * A * y₀) : Plane))
        ((3 * (deriv u t * deriv (deriv u) t)) • ((2 * A, 2 * A * y₀) : Plane) +
          (deriv u t * deriv u t * deriv u t) • ((0, 4 * A) : Plane)) =
        8 * A ^ 2 * deriv u t ^ 5 := by
      simp only [det, Prod.smul_mk, smul_eq_mul, Prod.mk_add_mk]; ring
    rw [e]
    exact mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 hA)) (pow_ne_zero 5 hu')
  · simp only [Prod.smul_mk, smul_eq_mul]
    exact mul_ne_zero (mul_ne_zero hu' hu') (mul_ne_zero two_ne_zero hA)

/-- Near a cusp parameter the loop is the printed germ in the coordinate `u = y(2πs) − y(2πt)`. -/
theorem ulg_loop_eventually_germ {Lc : ℝ → E3} (h1 : GenericFront.IsEmbeddedCircle Lc)
    (h3 : GenericFront.IsGenericFront Lc) {t : ℝ} (hc : deriv Lc (2 * π * t) 0 = 0) :
    ∃ (A y₀ x₀ z₀ : ℝ) (u : ℝ → ℝ), A ≠ 0 ∧ ContDiff ℝ ∞ u ∧ u t = 0 ∧ deriv u t ≠ 0 ∧
      Filter.EventuallyEq (nhds t) (xzOf (ulg_T Lc)) (germFront A y₀ x₀ z₀ ∘ u) := by
  have hLc := h1.smooth
  have hθc : 2 * π * t ∈ GenericFront.cuspSet Lc := (ulg_mem_cuspSet_iff hLc _).2 hc
  obtain ⟨A, hA, hy', ε, hε, hgerm⟩ := h3.exact_germ _ hθc
  refine ⟨A, GenericFront.coordY Lc (2 * π * t), GenericFront.coordX Lc (2 * π * t),
    GenericFront.coordZ Lc (2 * π * t),
    fun s => GenericFront.coordY Lc (2 * π * s) - GenericFront.coordY Lc (2 * π * t),
    hA, ?_, sub_self _, ?_, ?_⟩
  · exact (ulg_smooth_scale ((ContactMotions.contDiff_coord 1).comp hLc)).sub contDiff_const
  · have hd : HasDerivAt
        (fun s => GenericFront.coordY Lc (2 * π * s) - GenericFront.coordY Lc (2 * π * t))
        (2 * π * deriv Lc (2 * π * t) 1) t := by
      have h := (ulg_hasDerivAt_scale (ulg_hasDerivAt_coord hLc (2 * π * t) 1)).sub_const
        (GenericFront.coordY Lc (2 * π * t))
      rw [smul_eq_mul] at h
      exact h
    rw [hd.deriv]
    refine mul_ne_zero ulg_two_pi_ne ?_
    rwa [← (GenericFront.gp4_deriv_coord hLc _).2.1]
  · have hball : Metric.ball t (ε / (2 * π)) ∈ nhds t := Metric.ball_mem_nhds t (by positivity)
    filter_upwards [hball] with s hs
    have hs' : |2 * π * s - 2 * π * t| < ε := by
      apply ulg_abs_scale_lt
      rw [← Real.dist_eq]; exact hs
    obtain ⟨hx, hz⟩ := hgerm _ hs'
    show (GenericFront.coordX Lc (2 * π * s), GenericFront.coordZ Lc (2 * π * s)) =
      germFront A (GenericFront.coordY Lc (2 * π * t)) (GenericFront.coordX Lc (2 * π * t))
        (GenericFront.coordZ Lc (2 * π * t))
        (GenericFront.coordY Lc (2 * π * s) - GenericFront.coordY Lc (2 * π * t))
    rw [hx, hz]
    unfold germFront
    refine Prod.ext rfl ?_
    simp only
    ring

theorem ulg_semicubical {Lc : ℝ → E3} (h1 : GenericFront.IsEmbeddedCircle Lc)
    (h2 : GenericFront.IsLegendrian Lc) (h3 : GenericFront.IsGenericFront Lc) (t : ℝ)
    (ht : deriv (xzOf (ulg_T Lc)) t = 0) :
    det (iteratedDeriv 2 (xzOf (ulg_T Lc)) t) (iteratedDeriv 3 (xzOf (ulg_T Lc)) t) ≠ 0 ∧
      (iteratedDeriv 2 (xzOf (ulg_T Lc)) t).1 ≠ 0 := by
  have hc := (ulg_deriv_xzOf_eq_zero_iff h1.smooth h2 t).1 ht
  obtain ⟨A, y₀, x₀, z₀, u, hA, hu, hu0, hu', hγ⟩ := ulg_loop_eventually_germ h1 h3 hc
  exact ulg_germ_cusp hA hu hu0 hu' hγ

/-- "no vertical tangencies on regular arcs": `z′ = y x′`, so `x′ = 0` forces `(x′, z′) = 0`. -/
theorem ulg_no_vertical {Lc : ℝ → E3} (hLc : ContDiff ℝ ∞ Lc) (h2 : GenericFront.IsLegendrian Lc)
    (t : ℝ) (ht : deriv (xzOf (ulg_T Lc)) t ≠ 0) : (deriv (xzOf (ulg_T Lc)) t).1 ≠ 0 := by
  intro hx
  apply ht
  rw [ulg_deriv_xzOf_eq_zero_iff hLc h2]
  rw [ulg_deriv_xzOf hLc] at hx
  simpa [Real.pi_ne_zero] using hx

theorem ulg_cusp_alone {Lc : ℝ → E3} (h1 : GenericFront.IsEmbeddedCircle Lc)
    (h2 : GenericFront.IsLegendrian Lc) (h3 : GenericFront.IsGenericFront Lc) (p q : Param 1)
    (hpq : ¬ SameParam p q) (hc : deriv (xzOf (ulg_T Lc)) p.2 = 0) :
    xzOf (ulg_T Lc) p.2 ≠ xzOf (ulg_T Lc) q.2 := by
  obtain ⟨i, t⟩ := p
  obtain ⟨j, s⟩ := q
  have hsp : ¬ GenericFront.SameParam (2 * π * t) (2 * π * s) :=
    fun h => hpq (SameT.sameParam_iff.2 ((ulg_sameT_iff t s).2 h))
  have hθc : 2 * π * t ∈ GenericFront.cuspSet Lc :=
    (ulg_mem_cuspSet_iff h1.smooth _).2 ((ulg_deriv_xzOf_eq_zero_iff h1.smooth h2 t).1 hc)
  intro heq
  exact h3.no_cusp_on_branch _ hθc _ hsp heq.symm

/-- The `xz` front of `Lc` on ng:front-domain, BUILT from the spatial link (`comp 0 = sp.projLoop 0`). -/
def ulg_front {Lc : ℝ → E3} (h1 : GenericFront.IsEmbeddedCircle Lc)
    (h2 : GenericFront.IsLegendrian Lc) (h3 : GenericFront.IsGenericFront Lc) : SmoothFront where
  c := 1
  hc := Nat.one_pos
  comp := fun _ => (ulg_sp h1).projLoop 0
  cusps_finite := ulg_cuspSet_finite h1 h2 h3
  cusp_semicubical := fun _ t ht => (ulg_semicubical h1 h2 h3 t ht).1
  cusp_nonvertical := fun _ t ht => (ulg_semicubical h1 h2 h3 t ht).2
  no_vertical := fun _ t ht => ulg_no_vertical h1.smooth h2 t ht
  doubles_finite := ulg_pairs_finite h3
  transverse := fun p q hpq heq => ulg_transverse h1 h3 p q ⟨hpq, heq⟩
  no_triple := fun p q r hpq hqr hpr e1 e2 =>
    ulg_no_triple h1 h3 p q r ⟨hpq, e1⟩ ⟨hqr, e2⟩ ⟨hpr, e1.trans e2⟩
  cusp_alone := fun p q hpq hc => ulg_cusp_alone h1 h2 h3 p q hpq hc

theorem ulg_front_comp {Lc : ℝ → E3} (h1 : GenericFront.IsEmbeddedCircle Lc)
    (h2 : GenericFront.IsLegendrian Lc) (h3 : GenericFront.IsGenericFront Lc) (i : Fin 1) :
    (ulg_front h1 h2 h3).comp i = (ulg_sp h1).projLoop 0 := rfl

theorem u_legendrianFront : U_legendrianFront := by
  intro Lc h1 h2 h3
  exact ⟨ulg_front h1 h2 h3, ⟨⟨h1, h2⟩, rfl, fun _ _ => rfl⟩⟩
theorem u_spatialOf : U_spatialOf := by
  intro Lc h1 h2 h3
  exact ⟨ulg_sp h1, fun _ _ => rfl, ulg_cusped h1 h2 h3⟩
/-! ### urd_: helpers for U4 (`u_reading`) -/

section urd_helpers

open FrontRows FrontRows.U8R

/-- the `n`-th entry of a nonempty list, indices modulo the length (`Diagram.ent` made generic) -/
def urd_ent {α : Type*} (l : List α) (hl : 0 < l.length) (n : ℕ) : α :=
  l[n % l.length]'(Nat.mod_lt _ hl)

theorem urd_ent_of_lt {α : Type*} (l : List α) (hl : 0 < l.length) (n : ℕ) (hn : n < l.length) :
    urd_ent l hl n = l[n]'hn := by
  simp only [urd_ent, Nat.mod_eq_of_lt hn]

theorem urd_ent_congr {α : Type*} (l : List α) (hl : 0 < l.length) {a b : ℕ}
    (h : a % l.length = b % l.length) : urd_ent l hl a = urd_ent l hl b := by
  simp only [urd_ent, h]

theorem urd_exists_ent {α : Type*} (l : List α) (hl : 0 < l.length) (x : α) (hx : x ∈ l) :
    ∃ a, a < l.length ∧ urd_ent l hl a = x := by
  obtain ⟨a, ha, hx'⟩ := List.getElem_of_mem hx
  exact ⟨a, ha, by rw [urd_ent_of_lt l hl a ha, hx']⟩

theorem urd_ent_add_sub {α : Type*} (l : List α) (hl : 0 < l.length) (a b : ℕ) (ha : a < l.length)
    (_hb : b < l.length) :
    urd_ent l hl (a + (b + l.length - a) % l.length) = urd_ent l hl b := by
  apply urd_ent_congr
  rw [Nat.add_mod_mod, show a + (b + l.length - a) = b + l.length by omega, Nat.add_mod_right]

theorem urd_iterate_ent {α : Type*} (l : List α) (hl : 0 < l.length) (s : α → α)
    (hs : ∀ n, s (urd_ent l hl n) = urd_ent l hl (n + 1)) (j n : ℕ) :
    s^[j] (urd_ent l hl n) = urd_ent l hl (n + j) := by
  induction j with
  | zero => simp
  | succ j ih => rw [Function.iterate_succ_apply', ih, hs, Nat.add_assoc]

theorem urd_iterate_comm {α β : Type*} (s : α → α) (s' : β → β) (Φ : α → β)
    (hΦ : ∀ x, Φ (s x) = s' (Φ x)) (j : ℕ) (x : α) : Φ (s^[j] x) = s'^[j] (Φ x) := by
  induction j with
  | zero => rfl
  | succ j ih => rw [Function.iterate_succ_apply', hΦ, ih, Function.iterate_succ_apply']

/-- betweenness along a key-sorted cyclic enumeration (`Diagram.visitBetween_ent_iff` made generic) -/
theorem urd_cycBetween_ent_iff {α : Type*} (l : List α) (hl : 0 < l.length) (k : α → ℝ)
    (hk : ∀ a b, k (urd_ent l hl a) < k (urd_ent l hl b) ↔ a % l.length < b % l.length)
    (a j j' : ℕ) (hj0 : 0 < j) (hj0' : 0 < j') (hjm : j < l.length) (hj'm : j' < l.length) :
    cycBetween (k (urd_ent l hl a)) (k (urd_ent l hl (a + j))) (k (urd_ent l hl (a + j'))) ↔ j < j' := by
  unfold cycBetween
  rw [hk, hk, hk]
  have e1 : (a + j) % l.length = (a % l.length + j) % l.length := (Nat.mod_add_mod a _ j).symm
  have e2 : (a + j') % l.length = (a % l.length + j') % l.length := (Nat.mod_add_mod a _ j').symm
  rw [e1, e2]
  exact cycIdx_iff l.length j j' _ _ _ hl (Nat.mod_lt _ hl) (Nat.mod_lt _ hl) hj0 hj0' hjm hj'm
    (add_mod_cases _ _ _ (Nat.mod_lt _ hl) hjm) (add_mod_cases _ _ _ (Nat.mod_lt _ hl) hj'm)

/-- THE STRUCTURAL LEMMA: a map between two key-sorted finite cycles commuting with the cyclic successors
preserves strict oriented cyclic betweenness of the keys (`Diagram.visitBetween_iff_of_nextVisit_comm`
made generic over two enumerated cycles of equal length). -/
theorem urd_cycBetween_iff_of_succ_comm {α β : Type*}
    (l : List α) (hl : 0 < l.length) (k : α → ℝ) (s : α → α)
    (hk : ∀ a b, k (urd_ent l hl a) < k (urd_ent l hl b) ↔ a % l.length < b % l.length)
    (hs : ∀ n, s (urd_ent l hl n) = urd_ent l hl (n + 1))
    (l' : List β) (hl' : 0 < l'.length) (k' : β → ℝ) (s' : β → β)
    (hk' : ∀ a b, k' (urd_ent l' hl' a) < k' (urd_ent l' hl' b) ↔ a % l'.length < b % l'.length)
    (hs' : ∀ n, s' (urd_ent l' hl' n) = urd_ent l' hl' (n + 1))
    (hlen : l'.length = l.length)
    (Φ : α → β) (hΦ : ∀ x, Φ (s x) = s' (Φ x)) (hΦl : ∀ x ∈ l, Φ x ∈ l')
    (x y z : α) (hx : x ∈ l) (hy : y ∈ l) (hz : z ∈ l) :
    cycBetween (k x) (k y) (k z) ↔ cycBetween (k' (Φ x)) (k' (Φ y)) (k' (Φ z)) := by
  by_cases hxy : x = y
  · subst hxy
    exact iff_of_false (not_cycBetween_self_left _ _) (not_cycBetween_self_left _ _)
  by_cases hxz : x = z
  · subst hxz
    exact iff_of_false (not_cycBetween_self_right _ _) (not_cycBetween_self_right _ _)
  by_cases hyz : y = z
  · subst hyz
    exact iff_of_false (not_cycBetween_self_mid _ _) (not_cycBetween_self_mid _ _)
  obtain ⟨a, ha, hax⟩ := urd_exists_ent l hl x hx
  obtain ⟨b, hb, hby⟩ := urd_exists_ent l hl y hy
  obtain ⟨c, hc, hcz⟩ := urd_exists_ent l hl z hz
  have hjy : urd_ent l hl (a + (b + l.length - a) % l.length) = y := by
    rw [urd_ent_add_sub l hl a b ha hb, hby]
  have hjz : urd_ent l hl (a + (c + l.length - a) % l.length) = z := by
    rw [urd_ent_add_sub l hl a c ha hc, hcz]
  have hjm := Nat.mod_lt (b + l.length - a) hl
  have hj'm := Nat.mod_lt (c + l.length - a) hl
  have hj0 : 0 < (b + l.length - a) % l.length := by
    apply Nat.pos_of_ne_zero
    intro h0
    rw [h0, Nat.add_zero, hax] at hjy
    exact hxy hjy
  have hj0' : 0 < (c + l.length - a) % l.length := by
    apply Nat.pos_of_ne_zero
    intro h0
    rw [h0, Nat.add_zero, hax] at hjz
    exact hxz hjz
  have hL := urd_cycBetween_ent_iff l hl k hk a _ _ hj0 hj0' hjm hj'm
  rw [hax, hjy, hjz] at hL
  -- transport to the second cycle
  obtain ⟨a', _ha', hax'⟩ := urd_exists_ent l' hl' (Φ x) (hΦl x hx)
  have hy' : Φ y = urd_ent l' hl' (a' + (b + l.length - a) % l.length) := by
    calc Φ y = Φ (s^[(b + l.length - a) % l.length] (urd_ent l hl a)) := by
          rw [urd_iterate_ent l hl s hs, hjy]
      _ = s'^[(b + l.length - a) % l.length] (Φ (urd_ent l hl a)) := urd_iterate_comm s s' Φ hΦ _ _
      _ = s'^[(b + l.length - a) % l.length] (urd_ent l' hl' a') := by rw [hax, hax']
      _ = _ := urd_iterate_ent l' hl' s' hs' _ a'
  have hz' : Φ z = urd_ent l' hl' (a' + (c + l.length - a) % l.length) := by
    calc Φ z = Φ (s^[(c + l.length - a) % l.length] (urd_ent l hl a)) := by
          rw [urd_iterate_ent l hl s hs, hjz]
      _ = s'^[(c + l.length - a) % l.length] (Φ (urd_ent l hl a)) := urd_iterate_comm s s' Φ hΦ _ _
      _ = s'^[(c + l.length - a) % l.length] (urd_ent l' hl' a') := by rw [hax, hax']
      _ = _ := urd_iterate_ent l' hl' s' hs' _ a'
  have hR := urd_cycBetween_ent_iff l' hl' k' hk' a' _ _ hj0 hj0' (hlen ▸ hjm) (hlen ▸ hj'm)
  rw [hax', ← hy', ← hz'] at hR
  exact hL.trans hR.symm

/-! #### The front side: `fibList` / `cycNext` of `U8R` in enumeration form -/

section fibList

variable {α ι : Type*} [Fintype α] [DecidableEq α] [LinearOrder ι]
variable (comp : α → ι) (key : α → ℝ)
variable (hkey : ∀ a b, comp a = comp b → key a = key b → a = b)

theorem urd_fibList_length (i : ι) : (fibList comp key hkey i).length = (fib comp i).card := by
  let _ := keyOrder comp key hkey
  exact Finset.length_sort _

/-- keys along the sorted fibre compare as the indices modulo the count -/
theorem urd_fibList_key_ent_lt_iff (i : ι) (hl : 0 < (fibList comp key hkey i).length) (a b : ℕ) :
    key (urd_ent (fibList comp key hkey i) hl a) < key (urd_ent (fibList comp key hkey i) hl b) ↔
      a % (fibList comp key hkey i).length < b % (fibList comp key hkey i).length := by
  let _ := keyOrder comp key hkey
  have hs : (fibList comp key hkey i).SortedLT := Finset.sortedLT_sort (fib comp i)
  have h := hs.getElem_lt_getElem_iff (hi := Nat.mod_lt a hl) (hj := Nat.mod_lt b hl)
  have hc : comp (urd_ent (fibList comp key hkey i) hl a) = comp (urd_ent (fibList comp key hkey i) hl b) := by
    unfold urd_ent
    rw [(mem_fibList comp key hkey i _).mp (List.getElem_mem _), (mem_fibList comp key hkey i _).mp (List.getElem_mem _)]
  rw [← keyOrder_lt_iff comp key hkey hc]
  exact h

/-- the cyclic successor advances the enumeration by one -/
theorem urd_cycNext_ent (i : ι) (hl : 0 < (fibList comp key hkey i).length) (n : ℕ) :
    cycNext comp key hkey (urd_ent (fibList comp key hkey i) hl n) =
      urd_ent (fibList comp key hkey i) hl (n + 1) := by
  unfold urd_ent
  rw [cycNext_getElem comp key hkey i]
  simp only [Nat.mod_add_mod]

end fibList

/-! #### The converse of `markingRecordIso` -/

variable {F : SmoothFront} {S : Diagram}

/-- the occurrence bijection of a record isomorphism `frontRecord F ≅ S.record`, typed on the front's
occurrences and the diagram's visits (`(frontRecord F).M = F.Occ`, `S.record.M = S.Γ.Visit` are `rfl`) -/
def urd_Φ (ι : RecordIso (frontRecord F) S.record) : F.Occ ≃ S.Γ.Visit := ι.Φ

/-- the circle bijection, typed on `Fin F.c ≃ Fin S.Γ.c` -/
def urd_e (ι : RecordIso (frontRecord F) S.record) : Fin F.c ≃ Fin S.Γ.c := ι.e

/-- the record clauses read on the front's own data (all `rfl`-unfoldings of the record fields) -/
theorem urd_compOf_Φ (ι : RecordIso (frontRecord F) S.record) (p : F.Occ) :
    S.compOf (urd_Φ ι p) = urd_e ι (occComp F p) := ι.comp_eq p

theorem urd_Φ_cycNext (ι : RecordIso (frontRecord F) S.record) (p : F.Occ) :
    urd_Φ ι (cycNext (occComp F) (occKey F) (occKey_inj F) p) = S.nextVisit (urd_Φ ι p) := ι.succ_eq p

theorem urd_Φ_partner (ι : RecordIso (frontRecord F) S.record) (p : F.Occ) :
    urd_Φ ι (partner F p) = S.twin (urd_Φ ι p) := ι.pair_eq p

theorem urd_overBit_Φ (ι : RecordIso (frontRecord F) S.record) (p : F.Occ) :
    S.overBit (urd_Φ ι p) = frontOver F p := ι.bit_eq p

theorem urd_sign_Φ (ι : RecordIso (frontRecord F) S.record) (p : F.Occ) :
    S.sign (urd_Φ ι p).1 = frontSgn F p := ι.sgn_eq p

/-- a record isomorphism carries the fibre of a circle onto the occurrence set of its image circle -/
theorem urd_fib_map_eq (ι : RecordIso (frontRecord F) S.record) (i : Fin F.c) :
    (fib (occComp F) i).map (urd_Φ ι).toEmbedding = S.compVisits (urd_e ι i) := by
  ext v
  rw [Finset.mem_map_equiv, mem_fib, S.mem_compVisits]
  have h : S.compOf v = urd_e ι (occComp F ((urd_Φ ι).symm v)) := by
    have := urd_compOf_Φ ι ((urd_Φ ι).symm v)
    rwa [Equiv.apply_symm_apply] at this
  rw [h, (urd_e ι).apply_eq_iff_eq]

theorem urd_compList_length_eq (ι : RecordIso (frontRecord F) S.record) (i : Fin F.c) :
    (S.compList (urd_e ι i)).length = (fibList (occComp F) (occKey F) (occKey_inj F) i).length := by
  rw [S.compList_length, urd_fibList_length, ← urd_fib_map_eq ι i, Finset.card_map]

/-- `between_iff` of the `Marking` from `succ_eq` of the record isomorphism: on a finite cycle the
successor determines the oriented cyclic order -/
theorem urd_between_iff (ι : RecordIso (frontRecord F) S.record) (p q r : F.Occ)
    (hpq : p.1.1 = q.1.1) (hqr : q.1.1 = r.1.1) :
    cycBetween p.1.2 q.1.2 r.1.2 ↔
      cycBetween (S.visitCoord (urd_Φ ι p)) (S.visitCoord (urd_Φ ι q)) (S.visitCoord (urd_Φ ι r)) := by
  have hp : p ∈ fibList (occComp F) (occKey F) (occKey_inj F) p.1.1 := (mem_fibList _ _ _ _ p).mpr rfl
  have hq : q ∈ fibList (occComp F) (occKey F) (occKey_inj F) p.1.1 := (mem_fibList _ _ _ _ q).mpr hpq.symm
  have hr : r ∈ fibList (occComp F) (occKey F) (occKey_inj F) p.1.1 :=
    (mem_fibList _ _ _ _ r).mpr (hqr.symm.trans hpq.symm)
  have hl : 0 < (fibList (occComp F) (occKey F) (occKey_inj F) p.1.1).length := List.length_pos_of_mem hp
  have hΦl : ∀ x ∈ fibList (occComp F) (occKey F) (occKey_inj F) p.1.1,
      urd_Φ ι x ∈ S.compList (urd_e ι p.1.1) := by
    intro x hx
    rw [S.mem_compList, urd_compOf_Φ ι x, (mem_fibList _ _ _ _ x).mp hx]
  have hl' : 0 < (S.compList (urd_e ι p.1.1)).length := List.length_pos_of_mem (hΦl p hp)
  exact urd_cycBetween_iff_of_succ_comm (fibList (occComp F) (occKey F) (occKey_inj F) p.1.1) hl (occKey F)
    (cycNext (occComp F) (occKey F) (occKey_inj F))
    (urd_fibList_key_ent_lt_iff (occComp F) (occKey F) (occKey_inj F) p.1.1 hl)
    (urd_cycNext_ent (occComp F) (occKey F) (occKey_inj F) p.1.1 hl)
    (S.compList (urd_e ι p.1.1)) hl' S.visitCoord S.nextVisit
    (fun a b => S.visitCoord_ent_lt_iff _ hl' a b) (fun n => S.nextVisit_ent _ hl' n)
    (urd_compList_length_eq ι p.1.1) (urd_Φ ι) (urd_Φ_cycNext ι) hΦl p q r hp hq hr

/-- THE CONVERSE OF `markingRecordIso`: a named record isomorphism `frontRecord F ≅ S.record` is a
polygonal reading (`Marking`) of `F` on `S` — `e`, `Φ`, `comp_eq`, `pair_eq` (`partner` ↔ `twin`),
`over_iff` (`frontOver` ↔ `overBit`), `sgn_eq` (`frontSgn` ↔ `sign`) are the record fields, `between_iff`
is `succ_eq` through `urd_between_iff`. -/
def urd_markingOfRecordIso (ι : RecordIso (frontRecord F) S.record) : F.Marking S where
  e := urd_e ι
  Φ := urd_Φ ι
  comp_eq p := urd_compOf_Φ ι p
  between_iff := urd_between_iff ι
  pair_eq p q hne he := by
    rw [eq_partner_of F hne he]
    exact urd_Φ_partner ι p
  over_iff p q hne he := by
    have hq : q = partner F p := eq_partner_of F hne he
    subst hq
    rw [urd_overBit_Φ ι p]
    exact decide_eq_true_iff
  sgn_eq p q hne he hs := by
    have hq : q = partner F p := eq_partner_of F hne he
    subst hq
    rw [urd_sign_Φ ι p, F.crossSign_eq_sign (isDouble_partner F p)]
    unfold frontSgn
    simp only [hs, ↓reduceIte]

end urd_helpers

theorem u_reading : U_reading := by
  intro F
  exact ⟨(realize (FrontRows.U8R.oword F)).diagram,
    ⟨urd_markingOfRecordIso ((FrontRows.U8R.recordIso F).trans
      (FrontRows.U2.realizeRecordIso (FrontRows.U8R.oword F) (FrontRows.U8R.word_ne_nil F)).symm)⟩⟩
/-! ### U5 helpers (`utr_`) -/

/-- U5: the front's cusp criterion is the spatial link's when the projection is the front. -/
theorem utr_isCusp_iff {F : SmoothFront} {sp : SpatialLink F.c}
    (hproj : ∀ i, xzOf (sp.T i) = (F.comp i).γ) (p : Param F.c) :
    F.IsCusp p ↔ sp.IsCusp p.1 p.2 := by
  unfold SmoothFront.IsCusp SpatialLink.IsCusp
  rw [SmoothFront.vel_def, hproj]

theorem utr_mem_cuspSet_iff {F : SmoothFront} {sp : SpatialLink F.c}
    (hproj : ∀ i, xzOf (sp.T i) = (F.comp i).γ) (p : Param F.c) :
    p ∈ F.cuspSet ↔ p ∈ sp.cuspSet := by
  rw [SmoothFront.mem_cuspSet]
  exact and_congr_right fun _ => utr_isCusp_iff hproj p

/-- U5: `F.Cusp ≃ sp.cuspSet`, the identity on parameters. -/
def utr_cuspEquiv {F : SmoothFront} {sp : SpatialLink F.c}
    (hproj : ∀ i, xzOf (sp.T i) = (F.comp i).γ) : F.Cusp ≃ sp.cuspSet :=
  Equiv.subtypeEquivRight (utr_mem_cuspSet_iff hproj)

@[simp] theorem utr_cuspEquiv_apply_val {F : SmoothFront} {sp : SpatialLink F.c}
    (hproj : ∀ i, xzOf (sp.T i) = (F.comp i).γ) (c : F.Cusp) :
    (utr_cuspEquiv hproj c).1 = c.1 := rfl

@[simp] theorem utr_cuspEquiv_symm_apply_val {F : SmoothFront} {sp : SpatialLink F.c}
    (hproj : ∀ i, xzOf (sp.T i) = (F.comp i).γ) (k : sp.cuspSet) :
    ((utr_cuspEquiv hproj).symm k).1 = k.1 := rfl

/-- U5: a clean cusp smoothing of the spatial link is a clean-disc rounding of the front (drop
`collar`; the cusps are the same parameters). -/
def utr_geomRounding {F : SmoothFront} {sp : SpatialLink F.c} {G : Fin F.c → SmoothLoop}
    (hproj : ∀ i, xzOf (sp.T i) = (F.comp i).γ) (r : sp.CleanCuspSmoothing G) :
    F.GeomRounding G where
  U c := r.U (utr_cuspEquiv hproj c)
  a c := r.a (utr_cuspEquiv hproj c)
  b c := r.b (utr_cuspEquiv hproj c)
  disc c := r.disc (utr_cuspEquiv hproj c)
  center c := by
    have h := r.center (utr_cuspEquiv hproj c)
    rw [hproj] at h
    exact h
  disjoint c c' h := r.disjoint _ _ fun h' => h ((utr_cuspEquiv hproj).injective h')
  a_lt c := r.a_lt (utr_cuspEquiv hproj c)
  lt_b c := r.lt_b (utr_cuspEquiv hproj c)
  len c := r.len (utr_cuspEquiv hproj c)
  clean c q hq := r.clean (utr_cuspEquiv hproj c) q (by rw [hproj]; exact hq)
  arc_in c t ht := by
    have h := r.arc_in (utr_cuspEquiv hproj c) t ht
    rw [hproj] at h
    exact h
  arc_simple c t ht q hq := by
    have h := r.arc_simple (utr_cuspEquiv hproj c) t ht q hq
    rw [hproj, hproj] at h
    exact h
  agree i t h := by
    rw [← hproj]
    refine r.agree i t fun k hk n hn => ?_
    have h' := h ((utr_cuspEquiv hproj).symm k) hk n
    rw [Equiv.apply_symm_apply] at h'
    exact h' hn
  inside c t ht := r.inside (utr_cuspEquiv hproj c) t ht
  regular c t ht := r.regular (utr_cuspEquiv hproj c) t ht
  simple c := r.simple (utr_cuspEquiv hproj c)
  no_crossing c t ht q hq := r.no_crossing (utr_cuspEquiv hproj c) t ht q hq

/-- U5: a slope-rule reading of loops is a height-rule reading when slope order = height order at
every double point (the analogue of `HeightMarking.ofHeightOrder`). -/
def utr_heightMarking_of_geomMarking {c : ℕ} {sp : SpatialLink c} {G : Fin c → SmoothLoop}
    {S : Diagram}
    (hh : ∀ p q : Param c, SmoothFront.IsDoubleOf G p q →
      (SmoothFront.slopeOf G p < SmoothFront.slopeOf G q ↔ sp.height p < sp.height q))
    (gm : SmoothFront.GeomMarking G S) : sp.HeightMarking G S where
  e := gm.e
  Φ := gm.Φ
  comp_eq := gm.comp_eq
  between_iff := gm.between_iff
  pair_eq := gm.pair_eq
  over_iff p q hne he :=
    (gm.over_iff p q hne he).trans (hh p.1 q.1 (SmoothFront.OccOf.isDoubleOf_of_ne hne he))
  sgn_eq p q hne he hs :=
    gm.sgn_eq p q hne he ((hh p.1 q.1 (SmoothFront.OccOf.isDoubleOf_of_ne hne he)).mpr hs)

/-- U5: on a Legendrian front (`z′ = y x′`) the slope at a double point is the height
(`x′ ≠ 0` there, cusps not being double points). -/
theorem utr_slope_eq_height {F : SmoothFront} {sp : SpatialLink F.c}
    (hleg : ∀ (i : Fin F.c) (t : ℝ),
      (deriv (F.comp i).γ t).2 = yOf (sp.T i) t * (deriv (F.comp i).γ t).1)
    {p q : Param F.c} (hd : F.IsDouble p q) : F.slope p = sp.height p := by
  have hx : (F.vel p).1 ≠ 0 := F.vel_fst_ne_zero_of_isDouble hd
  unfold SmoothFront.slope SpatialLink.height
  rw [SmoothFront.vel_def] at hx ⊢
  rw [hleg p.1 p.2]
  field_simp

/-- U5 in the natural generality (`sp : SpatialLink F.c`): the two conclusions of `U_transport`
from the projection identity and the Legendrian identity. -/
theorem utr_transport_of {F : SmoothFront} {sp : SpatialLink F.c} {G : Fin F.c → SmoothLoop}
    {S : Diagram} (hproj : ∀ i, xzOf (sp.T i) = (F.comp i).γ)
    (hleg : ∀ (i : Fin F.c) (t : ℝ),
      (deriv (F.comp i).γ t).2 = yOf (sp.T i) t * (deriv (F.comp i).γ t).1)
    (r : sp.CleanCuspSmoothing G) (m : F.Marking S) :
    Nonempty (sp.HeightMarking G S) ∧ F.IsRounding S := by
  have geom : F.GeomRounding G := utr_geomRounding hproj r
  refine ⟨⟨utr_heightMarking_of_geomMarking ?_ (SmoothFront.GeomMarking.ofMarking geom m)⟩, ⟨⟨G, geom, m⟩⟩⟩
  intro p q hd
  have hd' : F.IsDouble p q := (geom.isDoubleOf_iff p q).mp hd
  rw [geom.slopeOf_eq hd', geom.slopeOf_eq hd'.symm, utr_slope_eq_height hleg hd',
    utr_slope_eq_height hleg hd'.symm]

/-- U5: the derivative of the front loop `t ↦ (x(2πt), z(2πt))` of a smooth space curve. -/
theorem utr_hasDerivAt_front {Lc : ℝ → E3} (hs : ContDiff ℝ ∞ Lc) (t : ℝ) :
    HasDerivAt (fun t => GenericFront.front Lc (2 * π * t))
      (2 * π * deriv Lc (2 * π * t) 0, 2 * π * deriv Lc (2 * π * t) 2) t := by
  have hL : HasDerivAt Lc (deriv Lc (2 * π * t)) (2 * π * t) :=
    (hs.differentiable (by decide) _).hasDerivAt
  have hm : HasDerivAt (fun t : ℝ => 2 * π * t) (2 * π) t := by
    simpa using (hasDerivAt_id t).const_mul (2 * π)
  have hc : HasDerivAt (fun t => Lc (2 * π * t)) ((2 * π) • deriv Lc (2 * π * t)) t :=
    hL.scomp t hm
  have h0 := (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 3) 0).hasFDerivAt.comp_hasDerivAt t hc
  have h2 := (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 3) 2).hasFDerivAt.comp_hasDerivAt t hc
  have := h0.prodMk h2
  simpa [Function.comp_def, GenericFront.front] using this

theorem u_transport : U_transport := by
  intro Lc sp F G S hsp hF r m
  obtain ⟨hyp, hone, hfront⟩ := hF
  obtain ⟨c, hc, comp, cf, cs, cn, nv, df, tr, nt, ca⟩ := F
  have hone' : c = 1 := hone
  subst hone'
  have hγ : ∀ i : Fin 1, (comp i).γ = fun t => GenericFront.front Lc (2 * π * t) :=
    fun i => funext (hfront i)
  refine utr_transport_of (sp := sp) ?_ ?_ r m
  · intro i
    funext t
    show (xOf (sp.T i) t, zOf (sp.T i) t) = (comp i).γ t
    rw [hγ i]
    simp only [xOf, zOf, hsp i t]
    rfl
  · intro i t
    show (deriv (comp i).γ t).2 = yOf (sp.T i) t * (deriv (comp i).γ t).1
    rw [hγ i, (utr_hasDerivAt_front hyp.circle.smooth t).deriv]
    show 2 * π * deriv Lc (2 * π * t) 2 = (sp.T i t).2.1 * (2 * π * deriv Lc (2 * π * t) 0)
    rw [hsp i t]
    show 2 * π * deriv Lc (2 * π * t) 2 = Lc (2 * π * t) 1 * (2 * π * deriv Lc (2 * π * t) 0)
    have h := hyp.legendrian (2 * π * t)
    unfold GenericFront.alpha at h
    linear_combination (2 * π) * h
theorem u_regular : U_regular := by
  intro K
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i t
    exact K.immersion t
  · refine (K.doubles_finite.image (fun q : ℝ × ℝ => ((0 : Fin 1), q.1))).subset ?_
    rintro ⟨i, t⟩ ⟨ht, ⟨j, t'⟩, ht', hne, heq⟩
    refine ⟨(t, t'), ⟨ht, ht', ?_, heq⟩, ?_⟩
    · intro h
      exact hne (Prod.ext (Subsingleton.elim i j) h)
    · rw [Subsingleton.elim (0 : Fin 1) i]
  · rintro ⟨i, s⟩ ⟨j, t⟩ ⟨hne, heq⟩
    exact K.transverse s t (fun h => hne ⟨Subsingleton.elim i j, h⟩) heq
  · rintro ⟨i, r⟩ ⟨j, s⟩ ⟨k, t⟩ ⟨h1, e1⟩ ⟨h2, e2⟩ ⟨h3, e3⟩
    exact K.no_triple r s t (fun h => h1 ⟨Subsingleton.elim _ _, h⟩)
      (fun h => h2 ⟨Subsingleton.elim _ _, h⟩) (fun h => h3 ⟨Subsingleton.elim _ _, h⟩) e1 e2
  · rintro ⟨i, s⟩ ⟨j, t⟩ ⟨hne, heq⟩
    exact K.y_ne_of_isDouble ⟨fun h => hne ⟨Subsingleton.elim i j, h⟩, heq⟩
/-! #### FAM helpers (unit U6+U6a, prefix `ufm_`): the family `Ψ_{η t} ∘ Φ_{1−η t} ∘ L` of display
fd:contact-ambient-composition with the clock `η = Real.smoothTransition`; slices embedded through the
inverses of `diffeo`, regular through the chain rule on the inverse (`ufm_deriv_ne_zero_of_leftInverse`). -/

theorem ufm_contDiff_toSpace : ContDiff ℝ ∞ toSpace := by
  have h : ∀ i : Fin 3, ContDiff ℝ ∞ (fun p : E3 => p i) := fun i =>
    (contDiff_euclidean.mp contDiff_id) i
  exact (h 0).prodMk ((h 1).prodMk (h 2))

theorem ufm_clock_mem (x : ℝ) : Real.smoothTransition x ∈ Icc (0 : ℝ) 1 :=
  ⟨Real.smoothTransition.nonneg x, Real.smoothTransition.le_one x⟩

theorem ufm_clock_mem' (x : ℝ) : 1 - Real.smoothTransition x ∈ Icc (0 : ℝ) 1 :=
  ⟨by linarith [Real.smoothTransition.le_one x], by linarith [Real.smoothTransition.nonneg x]⟩

theorem ufm_contDiff_slice {Ψ : ℝ → E3 → E3} (h : ContDiffOn ℝ ∞ (uncurry Ψ) (Icc 0 1 ×ˢ univ))
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : ContDiff ℝ ∞ (Ψ t) :=
  h.comp_contDiff (contDiff_const.prodMk contDiff_id) (fun _ => ⟨ht, mem_univ _⟩)

theorem ufm_deriv_ne_zero_of_leftInverse {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} {finv : F → E}
    (hfinv : Differentiable ℝ finv) (hl : LeftInverse finv f) {γ : ℝ → E} {θ : ℝ}
    (hγ : DifferentiableAt ℝ (f ∘ γ) θ) (hne : deriv γ θ ≠ 0) : deriv (f ∘ γ) θ ≠ 0 := by
  intro h0
  have h1 : HasDerivAt (f ∘ γ) 0 θ := h0 ▸ hγ.hasDerivAt
  have h2 : HasDerivAt (finv ∘ (f ∘ γ)) (fderiv ℝ finv ((f ∘ γ) θ) 0) θ :=
    (hfinv _).hasFDerivAt.comp_hasDerivAt θ h1
  have h3 : finv ∘ (f ∘ γ) = γ := by funext s; simp [Function.comp, hl (γ s)]
  rw [h3, map_zero] at h2
  exact hne h2.deriv

theorem ufm_embeddedCircle_of_comp {f finv : E3 → E3} (hf : ContDiff ℝ ∞ f)
    (hfinv : ContDiff ℝ ∞ finv) (hl : LeftInverse finv f) {L : ℝ → E3}
    (h : GenericFront.IsEmbeddedCircle (f ∘ L)) : GenericFront.IsEmbeddedCircle L := by
  have hL : L = finv ∘ (f ∘ L) := by funext θ; simp [Function.comp, hl (L θ)]
  have hLs : ContDiff ℝ ∞ L := by rw [hL]; exact hfinv.comp h.smooth
  refine ⟨hLs, ?_, ?_, ?_⟩
  · intro θ
    have := h.periodic θ
    simp only [Function.comp] at this
    calc L (θ + 2 * π) = finv (f (L (θ + 2 * π))) := (hl _).symm
      _ = finv (f (L θ)) := by rw [this]
      _ = L θ := hl _
  · intro θ θ' hθ
    exact h.injective θ θ' (by simp [Function.comp, hθ])
  · intro θ hθ
    apply h.immersion θ
    have hLd : HasDerivAt L 0 θ := hθ ▸ ((hLs.differentiable (by decide)) θ).hasDerivAt
    have h2 : HasDerivAt (f ∘ L) (fderiv ℝ f (L θ) 0) θ :=
      ((hf.differentiable (by decide)) _).hasFDerivAt.comp_hasDerivAt θ hLd
    rw [map_zero] at h2
    exact h2.deriv

theorem ufm_deriv_comp_two_pi {L : ℝ → E3} (hL : GenericFront.IsEmbeddedCircle L) (s : ℝ) :
    deriv (fun s => L (2 * π * s)) s ≠ 0 := by
  have h1 : HasDerivAt (fun s : ℝ => 2 * π * s) (2 * π) s := by
    simpa using (hasDerivAt_id s).const_mul (2 * π)
  have h2 : HasDerivAt L (deriv L (2 * π * s)) (2 * π * s) :=
    ((hL.smooth.differentiable (by decide)) _).hasDerivAt
  have h3 := h2.scomp s h1
  have h4 : deriv (fun s => L (2 * π * s)) s = (2 * π) • deriv L (2 * π * s) := h3.deriv
  rw [h4]
  exact smul_ne_zero (by positivity) (hL.immersion _)

theorem ufm_spatialLink_ext {c : ℕ} {L L' : SpatialLink c} (h : L.T = L'.T) : L = L' := by
  cases L; cases L'; cases h; rfl

/-- ambient isotopy in row 87's copy → row 84's (eta) -/
theorem ufm_ambient_ofGF {Φ : ℝ → E3 → E3} (h : GenericFront.IsCompactlySupportedAmbientIsotopy Φ) :
    IsCompactlySupportedAmbientIsotopy Φ :=
  ⟨h.smooth, h.zero, h.diffeo, h.support⟩

/-- the map of display fd:contact-ambient-composition `Ψ_t ∘ Φ_{1−t} ∘ L`, on `Space`, 1-periodic
parameter, time through the clock `η = Real.smoothTransition` (`η = 0` on `t ≤ 0`, `1` on `t ≥ 1`) -/
def ufm_fam (Ψ Φ : ℝ → E3 → E3) (L : ℝ → E3) (t s : ℝ) : Space :=
  toSpace (Ψ (Real.smoothTransition t) (Φ (1 - Real.smoothTransition t) (L (2 * π * s))))

theorem ufm_fam_joint_smooth {Ψ Φ : ℝ → E3 → E3} {L : ℝ → E3}
    (hΨ : ContDiffOn ℝ ∞ (uncurry Ψ) (Icc 0 1 ×ˢ univ))
    (hΦ : ContDiffOn ℝ ∞ (uncurry Φ) (Icc 0 1 ×ˢ univ)) (hL : ContDiff ℝ ∞ L) :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ => ufm_fam Ψ Φ L p.1 p.2) := by
  have hη : ContDiff ℝ ∞ Real.smoothTransition := Real.smoothTransition.contDiff
  have h1 : ContDiff ℝ ∞
      (fun p : ℝ × ℝ => Φ (1 - Real.smoothTransition p.1) (L (2 * π * p.2))) :=
    hΦ.comp_contDiff (f := fun p : ℝ × ℝ => (1 - Real.smoothTransition p.1, L (2 * π * p.2)))
      ((contDiff_const.sub (hη.comp contDiff_fst)).prodMk
        (hL.comp (contDiff_const.mul contDiff_snd)))
      (fun p => ⟨ufm_clock_mem' p.1, mem_univ _⟩)
  have h2 : ContDiff ℝ ∞ (fun p : ℝ × ℝ =>
      Ψ (Real.smoothTransition p.1) (Φ (1 - Real.smoothTransition p.1) (L (2 * π * p.2)))) :=
    hΨ.comp_contDiff (f := fun p : ℝ × ℝ =>
        (Real.smoothTransition p.1, Φ (1 - Real.smoothTransition p.1) (L (2 * π * p.2))))
      ((hη.comp contDiff_fst).prodMk h1) (fun p => ⟨ufm_clock_mem p.1, mem_univ _⟩)
  exact ufm_contDiff_toSpace.comp h2

theorem ufm_fam_periodic {Ψ Φ : ℝ → E3 → E3} {L : ℝ → E3} (hL : Periodic L (2 * π)) (t s : ℝ) :
    ufm_fam Ψ Φ L t (s + 1) = ufm_fam Ψ Φ L t s := by
  unfold ufm_fam
  rw [show 2 * π * (s + 1) = 2 * π * s + 2 * π by ring, hL]

theorem ufm_fam_embedded {Ψ Φ : ℝ → E3 → E3} {L : ℝ → E3}
    (hΨ : IsCompactlySupportedAmbientIsotopy Ψ) (hΦ : IsCompactlySupportedAmbientIsotopy Φ)
    (hL : GenericFront.IsEmbeddedCircle L) (t s s' : ℝ)
    (h : ufm_fam Ψ Φ L t s = ufm_fam Ψ Φ L t s') : SameT s s' := by
  obtain ⟨Ψinv, -, hΨl, -⟩ := hΨ.diffeo _ (ufm_clock_mem t)
  obtain ⟨Φinv, -, hΦl, -⟩ := hΦ.diffeo _ (ufm_clock_mem' t)
  have h1 := congrArg toE3 h
  simp only [ufm_fam, toE3_toSpace] at h1
  obtain ⟨k, hk⟩ := hL.injective _ _ (hΦl.injective (hΨl.injective h1))
  refine ⟨k, ?_⟩
  have hπ : (2 * π : ℝ) ≠ 0 := by positivity
  exact mul_left_cancel₀ hπ (by rw [hk]; ring)

theorem ufm_fam_regular {Ψ Φ : ℝ → E3 → E3} {L : ℝ → E3}
    (hΨ : IsCompactlySupportedAmbientIsotopy Ψ) (hΦ : IsCompactlySupportedAmbientIsotopy Φ)
    (hL : GenericFront.IsEmbeddedCircle L) (t s : ℝ) : deriv (ufm_fam Ψ Φ L t) s ≠ 0 := by
  obtain ⟨Ψinv, hΨs, hΨl, -⟩ := hΨ.diffeo _ (ufm_clock_mem t)
  obtain ⟨Φinv, hΦs, hΦl, -⟩ := hΦ.diffeo _ (ufm_clock_mem' t)
  have hslice : ContDiff ℝ ∞ (ufm_fam Ψ Φ L t) :=
    (ufm_fam_joint_smooth hΨ.smooth hΦ.smooth hL.smooth).comp (contDiff_const.prodMk contDiff_id)
  have hfinv : Differentiable ℝ (fun p : Space => Φinv (Ψinv (toE3 p))) :=
    (hΦs.comp (hΨs.comp contDiff_toE3)).differentiable (by decide)
  have hl : LeftInverse (fun p : Space => Φinv (Ψinv (toE3 p)))
      (fun q : E3 => toSpace (Ψ (Real.smoothTransition t) (Φ (1 - Real.smoothTransition t) q))) := by
    intro q
    simp only [toE3_toSpace, hΨl _, hΦl _]
  exact ufm_deriv_ne_zero_of_leftInverse hfinv hl (γ := fun s => L (2 * π * s))
    (hslice.differentiable (by decide) s) (ufm_deriv_comp_two_pi hL s)

/-- a jointly smooth one-parameter family of embedded regular 1-periodic curves as a `SpatialFamily 1` -/
def ufm_familyOfSlices (F : ℝ → ℝ → Space) (hsmooth : ContDiff ℝ ∞ (fun p : ℝ × ℝ => F p.1 p.2))
    (hper : ∀ t s, F t (s + 1) = F t s) (hemb : ∀ t s s', F t s = F t s' → SameT s s')
    (hreg : ∀ t s, deriv (F t) s ≠ 0) : SpatialFamily 1 where
  G t :=
    { T := fun _ => F t
      smooth := fun _ => hsmooth.comp (contDiff_const.prodMk contDiff_id)
      periodic := fun _ s => hper t s
      embedded := fun i j s s' h => ⟨Subsingleton.elim i j, hemb t s s' h⟩
      regular := fun _ s => hreg t s }
  joint_smooth := fun _ => hsmooth

theorem ufm_familyOfSlices_T (F : ℝ → ℝ → Space) (hsmooth : ContDiff ℝ ∞ (fun p : ℝ × ℝ => F p.1 p.2))
    (hper : ∀ t s, F t (s + 1) = F t s) (hemb : ∀ t s s', F t s = F t s' → SameT s s')
    (hreg : ∀ t s, deriv (F t) s ≠ 0) (t : ℝ) :
    ((ufm_familyOfSlices F hsmooth hper hemb hreg).G t).T = fun _ => F t := rfl

theorem u_family : U_family := by
  intro K L Ψ Φ pkg hΨ hcar hΦ
  have hΦa : IsCompactlySupportedAmbientIsotopy Φ := ufm_ambient_ofGF hΦ.ambient
  have h01 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  obtain ⟨Φinv1, hΦinv1, hl1, -⟩ := hΦa.diffeo 1 h01
  have hL : GenericFront.IsEmbeddedCircle L :=
    ufm_embeddedCircle_of_comp (ufm_contDiff_slice hΦa.smooth h01) hΦinv1 hl1
      pkg.F_front.hyp.circle
  obtain ⟨Fam, hFam⟩ : ∃ Fam : SpatialFamily 1, ∀ t, (Fam.G t).T = fun _ => ufm_fam Ψ Φ L t :=
    ⟨ufm_familyOfSlices (ufm_fam Ψ Φ L) (ufm_fam_joint_smooth hΨ.smooth hΦa.smooth hL.smooth)
      (ufm_fam_periodic hL.periodic) (ufm_fam_embedded hΨ hΦa hL) (ufm_fam_regular hΨ hΦa hL),
      fun t => rfl⟩
  have h0 : Fam.G 0 = pkg.sp := by
    apply ufm_spatialLink_ext
    rw [hFam 0]
    funext i s
    rw [pkg.sp_T i s]
    simp only [ufm_fam, Real.smoothTransition.zero, sub_zero, hΨ.zero, Function.comp_apply]
  have h1 : Fam.G 1 = K.spatial := by
    apply ufm_spatialLink_ext
    rw [hFam 1]
    funext i s
    simp only [ufm_fam, Real.smoothTransition.one, sub_self, hΦa.zero, hcar,
      TransverseKnot.circle, TransverseKnot.spatial_T]
    rw [mul_div_cancel_left₀ s (by positivity : (2 * π : ℝ) ≠ 0)]
    rfl
  refine ⟨Fam, h0, ?_, ?_⟩
  · rw [h1]; exact u_regular K
  · intro X hX; rw [h1]; exact hX


/-! ## 6. The row theorems (names fixed: `SM.fd_contact`, `CV.ax_etnyre`, `CV.ax_slbound`) -/

/-- **Row 94 fd:contact.**  To be closed as
`fd_contact_of_units u_circle u_sl_isotopy (U_package_of u_legendrianFront u_spatialOf u_reading u_transport) u_family`
once the units of PLAN_FINAL §6 are proved. -/
theorem fd_contact : FdContactData :=
  fd_contact_of_units u_circle u_sl_isotopy (U_package_of u_legendrianFront u_spatialOf u_reading u_transport) u_family

/-- **Row 161 CV:ax:etnyre** — PROVED now from the axiom's transverse clause (closable immediately after
the interface review of `SM.src_contact`). -/
theorem CV.ax_etnyre : CV.AxEtnyreData :=
  ⟨fun D K hD _ => by subst hD; exact src_contact_spec.transverse_front_writhe K⟩

/-- **Row 162 CV:ax:slbound** — row 94 in CV notation (`P = homfly`, lp:core); waits on `fd_contact`. -/
theorem CV.ax_slbound : CV.AxSlboundData := CV.ax_slbound_of fd_contact

end

end SM

