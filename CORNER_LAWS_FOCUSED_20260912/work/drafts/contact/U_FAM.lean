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

theorem u_circle : U_circle := by
  sorry
theorem u_sl_radius : U_sl_radius := by
  sorry
theorem u_sl_family : U_sl_family := by
  sorry
theorem u_sl_reparam : U_sl_reparam := by
  sorry
theorem u_sl_isotopy : U_sl_isotopy := by
  sorry
theorem u_legendrianFront : U_legendrianFront := by
  sorry
theorem u_spatialOf : U_spatialOf := by
  sorry
theorem u_reading : U_reading := by
  sorry
theorem u_transport : U_transport := by
  sorry
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

