import SM.GenericFront
import SM.TransverseNeighborhood
import SM.LinkingCalculusRow
import SM.TransverseFront
import SM.ContactPath
import SM.NgBound

/-! # src:contact (fifth literature interface), `SM.sl`, rows 94 / 161 / 162 — design sketch A

Companion of work/drafts/contact/DESIGN_A.md (architect A, 2026-09-15).  Everything here is a
`def`, a `structure`, ONE `axiom` (the fifth literature interface, policy name `SM.src_contact`),
and theorems; the theorems marked `sorry` are the BRIDGE LEMMAS of the row-94 proof route
(DESIGN_A.md §4), stated so that the prover units have their targets fixed; nothing here is to
be ported before the interface review of the axiom.

Registry text: blueprint/AXIOM_REGISTRY.md §src:contact = reference/SM/sm-3-statesum.tex:3341-3365.
-/

namespace SM

open Link SmoothFront
open scoped ContDiff RealInnerProductSpace
open Set Function Real

noncomputable section
open Classical

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## 0. Coordinate bridges: `Space = ℝ × ℝ × ℝ` (def:transverse-front, rows 89-92) and
`E3 = EuclideanSpace ℝ (Fin 3)` (rows 84-88); periods `1` and `2π`. -/

/-- `(x, y, z) ↦ !₂[x, y, z]`: the identity on coordinates. -/
def toE3 (p : Space) : E3 := (EuclideanSpace.equiv (Fin 3) ℝ).symm ![p.1, p.2.1, p.2.2]

/-- `p ↦ (p 0, p 1, p 2)`. -/
def toSpace (p : E3) : Space := (p 0, p 1, p 2)

@[simp] theorem toE3_apply0 (p : Space) : toE3 p 0 = p.1 := rfl
@[simp] theorem toE3_apply1 (p : Space) : toE3 p 1 = p.2.1 := rfl
@[simp] theorem toE3_apply2 (p : Space) : toE3 p 2 = p.2.2 := rfl

theorem toSpace_toE3 (p : Space) : toSpace (toE3 p) = p := rfl

theorem contDiff_toE3 : ContDiff ℝ ∞ toE3 := by
  unfold toE3
  refine (EuclideanSpace.equiv (Fin 3) ℝ).symm.contDiff.comp ?_
  rw [contDiff_pi]
  intro i
  fin_cases i
  · exact contDiff_fst
  · exact contDiff_snd.fst
  · exact contDiff_snd.snd

/-- The contact form of rows 84-88 (`lcContactForm`, `GenericFront.alpha`) is the contact form of
def:transverse-front (`contactForm`) under the coordinate bridge — the convention sentence of
src:contact ("standard contact space (ℝ³, ker(dz − y dx))") is one convention in both
vocabularies. -/
theorem lcContactForm_toE3 (p v : Space) : lcContactForm (toE3 p) (toE3 v) = contactForm p v := rfl

theorem alpha_eq_lcContactForm (p v : E3) : GenericFront.alpha p v = lcContactForm p v := rfl

/-- The `2π`-periodic `E3` reading of a `1`-periodic `Space` curve: `θ ↦ toE3 (T (θ / 2π))`. -/
def toCircle2π (T : ℝ → Space) : ℝ → E3 := fun θ => toE3 (T (θ / (2 * π)))

/-! ## 1. The self-linking number of the document (fd:framed-linking, sm-3:2820-2824), ε-free -/

/-- One `ε₀` with `T` and `T + ε ∂_y` disjoint positive transverse embeddings for `0 < ε ≤ ε₀`
(row 88 `transverse_uniform` on the constant family). -/
theorem exists_uniform_radius {P : ℝ} (hP : 0 < P) {T : ℝ → E3}
    (h : IsPositiveTransverseEmbedding P T) :
    ∃ ε₀ > 0, ∀ ε, 0 < ε → ε ≤ ε₀ → DisjointPair P T (pushoff T (fun _ => ey) ε) := by
  have hfam : TransverseFamily P (fun _ => T) :=
    { pos := hP
      smooth := h.circle.smooth.comp contDiff_snd
      periodic := fun _ => h.circle.periodic
      embedded := fun _ _ => h.embedded
      positive := fun _ _ => h.positive }
  obtain ⟨ε₀, hε₀, hu⟩ := fd_linking_calculus.transverse_uniform P (fun _ => T) hfam
  exact ⟨ε₀, hε₀, fun ε hε hεε₀ => (hu 0 ⟨le_rfl, zero_le_one⟩ ε hε hεε₀).2.2⟩

/-- **`sl` of fd:framed-linking, ε-free**: the common value of `selfLinking P T ε` for all small
`ε > 0` (row 88 `self_linking_invariant`), read at one admissible radius fixed by choice; `0` on
curves that are not positive transverse embeddings (never exercised). -/
def slOf (P : ℝ) (T : ℝ → E3) : ℝ :=
  if h : 0 < P ∧ IsPositiveTransverseEmbedding P T then
    selfLinking P T (Classical.choose (exists_uniform_radius h.1 h.2))
  else 0

/-- `slOf` is the number of fd:framed-linking at EVERY admissible radius. -/
theorem slOf_eq_selfLinking {P : ℝ} (hP : 0 < P) {T : ℝ → E3}
    (h : IsPositiveTransverseEmbedding P T) {ε₀ : ℝ} (hε₀ : 0 < ε₀)
    (hd : ∀ ε, 0 < ε → ε ≤ ε₀ → DisjointPair P T (pushoff T (fun _ => ey) ε))
    {ε : ℝ} (hε : 0 < ε) (hεε₀ : ε ≤ ε₀) : slOf P T = selfLinking P T ε := by
  have hh : 0 < P ∧ IsPositiveTransverseEmbedding P T := ⟨hP, h⟩
  rw [slOf, dif_pos hh]
  set ε₁ := Classical.choose (exists_uniform_radius hh.1 hh.2) with hε₁def
  have hspec := Classical.choose_spec (exists_uniform_radius hh.1 hh.2)
  rw [← hε₁def] at hspec
  obtain ⟨hε₁, hd₁⟩ := hspec
  have hfam : TransverseFamily P (fun _ => T) :=
    { pos := hP
      smooth := h.circle.smooth.comp contDiff_snd
      periodic := fun _ => h.circle.periodic
      embedded := fun _ _ => h.embedded
      positive := fun _ _ => h.positive }
  -- both radii are compared with the common tiny radius `min ε ε₁`
  set δ := min ε ε₁ with hδ
  have hδpos : 0 < δ := lt_min hε hε₁
  have h1 : selfLinking P T ε₁ = selfLinking P T δ := by
    have := fd_linking_calculus.self_linking_invariant P (fun _ => T) hfam ε₁ hε₁
      (fun _ _ ε' hε' hε'₁ u u' => (hd₁ ε' hε' hε'₁).disjoint u' u)
      0 ⟨le_rfl, zero_le_one⟩ 0 ⟨le_rfl, zero_le_one⟩ ε₁ δ hε₁ le_rfl hδpos (min_le_right _ _)
    simpa using this
  have h2 : selfLinking P T ε = selfLinking P T δ := by
    have := fd_linking_calculus.self_linking_invariant P (fun _ => T) hfam ε₀ hε₀
      (fun _ _ ε' hε' hε'₀ u u' => (hd ε' hε' hε'₀).disjoint u' u)
      0 ⟨le_rfl, zero_le_one⟩ 0 ⟨le_rfl, zero_le_one⟩ ε δ hε hεε₀ hδpos
      ((min_le_left _ _).trans hεε₀)
    simpa using this
  rw [h1, h2]

/-- A transverse knot of def:transverse-front is a positive transverse embedding of period `1`
in the vocabulary of row 88 (bridge; the contact form agrees by `lcContactForm_toE3`). -/
theorem TransverseKnot.isPositiveTransverseEmbedding (K : TransverseKnot) :
    IsPositiveTransverseEmbedding 1 (fun t => toE3 (K.T t)) := by
  refine ⟨⟨contDiff_toE3.comp K.smooth, fun t => by simp [K.periodic t]⟩, ?_, ?_⟩
  · intro u u' h
    have h' : K.T u = K.T u' := by
      have := congrArg toSpace h
      simpa [toSpace_toE3] using this
    obtain ⟨k, hk⟩ := K.embedded u u' h'
    exact ⟨k, by rw [hk]; ring⟩
  · intro u
    -- B-0: the derivative passes through the continuous linear map `toE3`
    have hv : HasDerivAt (fun t => (![xOf K.T t, yOf K.T t, zOf K.T t] : Fin 3 → ℝ))
        ![deriv (xOf K.T) u, deriv (yOf K.T) u, deriv (zOf K.T) u] u := by
      rw [hasDerivAt_pi]
      intro i
      fin_cases i
      · exact K.hasDerivAt_x u
      · exact K.hasDerivAt_y u
      · exact K.hasDerivAt_z u
    have hT : HasDerivAt (fun t => toE3 (K.T t))
        ((EuclideanSpace.equiv (Fin 3) ℝ).symm
          ![deriv (xOf K.T) u, deriv (yOf K.T) u, deriv (zOf K.T) u]) u :=
      (EuclideanSpace.equiv (Fin 3) ℝ).symm.hasFDerivAt.comp_hasDerivAt u hv
    rw [hT.deriv]
    have := K.positive u
    simpa [lcContactForm, toE3, yOf] using this

/-- **The document's self-linking number of a transverse knot** (fd:framed-linking read on
def:transverse-front's class through the coordinate bridge, period `1`). -/
def sl (K : TransverseKnot) : ℝ := slOf 1 (fun t => toE3 (K.T t))

/-! ## 2. "an oriented Legendrian front": the accepted ng:front-domain class `SmoothFront` as the
`xz` front of a Legendrian knot of rows 84/87 -/

/-- `F` is the `xz` front of the oriented Legendrian knot `L` (rows 84/87 vocabulary: `2π`-periodic,
`GenericFrontHyp L` = smooth embedded circle + Legendrian): one parameter circle, and `F.comp 0`
is the front `θ ↦ (x, z)` of `L` on the `1`-periodic parameter (`t ↦ 2πt`).  `F : SmoothFront`
carries the front's cusp/crossing vocabulary (`downCount`, `upCount`, `writhe`, over = smaller
slope), which is Etnyre's front convention (source §2.2 (3), the observer at `y = −∞`). -/
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
sm-3:3341-3365), one field per printed formula, ∃-form over the literature's `r`, `tb` -/

/-- The printed formulas of src:contact for candidate rotation number `r` and Thurston–Bennequin
invariant `tb` of the literature (neither is defined in the document; both are fixed by the
first two formulas).  Domain of the Legendrian clauses: "an oriented Legendrian front" =
`IsLegendrianFrontOf L F` (§2; FR-SC-2).  `T₊(L)` = the accepted positive transverse pushoff
`GenericFront.IsPositivePushoff L T'` (row 87's notion; FR-SC-3), quantified over every pushoff.
`sl` = the document's fd:framed-linking number `slOf`/`sl` (§1; rem:sl-convention, FR-SC-4).
The convention sentence, the parenthetical provenance sentence and the closing scope sentence
have no field (FR-SC-8); "every cusp of an oriented front is traversed either downward or
upward, so the total cusp count in his tb formula is D+U" is the accepted theorem
`SmoothFront.downCount_add_upCount` (FR-SC-6). -/
structure SrcContactClauses (r tb : (ℝ → E3) → ℝ) : Prop where
  /-- sm-3:3352, first formula of display fd:contact-inputs: `r = (D − U)/2`. -/
  rotation : ∀ (L : ℝ → E3) (F : SmoothFront), IsLegendrianFrontOf L F →
    r L = ((F.downCount : ℝ) - F.upCount) / 2
  /-- sm-3:3352, second formula: `tb = w − (D + U)/2` ("the total cusp count in his tb formula
  is D + U"). -/
  thurston_bennequin : ∀ (L : ℝ → E3) (F : SmoothFront), IsLegendrianFrontOf L F →
    tb L = (F.writhe : ℝ) - ((F.downCount : ℝ) + F.upCount) / 2
  /-- sm-3:3353, third formula: `sl(T₊(L)) = tb(L) − r(L)`, for every positive transverse pushoff
  `T₊(L)` of `L` (the `2π`-periodic `E3` class of rows 84/87). -/
  pushoff_self_linking : ∀ (L : ℝ → E3) (F : SmoothFront), IsLegendrianFrontOf L F →
    ∀ T' : ℝ → E3, GenericFront.IsPositivePushoff L T' → slOf (2 * π) T' = tb L - r L
  /-- sm-3:3358-3360: "For a generic positive transverse front (Definition def:transverse-front),
  self-linking equals its front writhe" — the knot `T` named separately (`K`), its front
  `K.front` (over = smaller `y`, sign `sgn det_xz(u_O, u_U)`, accepted row 92). -/
  transverse_front_writhe : ∀ K : TransverseKnot, sl K = (K.front.writhe : ℝ)

/-- **src:contact** (AXIOM_REGISTRY.md §src:contact, sm-3:3341-3365; policy name
`SM.src_contact`): "Use standard contact space (ℝ³, ker(dz − y dx)), with positive transverse
orientation z′ − y x′ > 0.  Etnyre's front and pushoff statements give, for an oriented Legendrian
front with downward and upward cusp counts D, U — every cusp of an oriented front is traversed
either downward or upward, so the total cusp count in his tb formula is D+U —
r = (D−U)/2, tb = w − (D+U)/2, sl(T₊(L)) = tb(L) − r(L).  (…)  For a generic positive transverse
front (Definition def:transverse-front), self-linking equals its front writhe (…).  These are the
local front and pushoff source formulas only."  Existence of the literature's `r`, `tb` in ∃-form;
the formulas are the fields of `SrcContactClauses`.  AXIOM: interface review against the registry
text required before any consumer cites it. -/
axiom src_contact : ∃ r tb : (ℝ → E3) → ℝ, SrcContactClauses r tb

/-- The literature's rotation number, one witness fixed by choice. -/
def rot : (ℝ → E3) → ℝ := Classical.choose src_contact
/-- The literature's Thurston–Bennequin invariant, one witness fixed by choice. -/
def tb : (ℝ → E3) → ℝ := Classical.choose (Classical.choose_spec src_contact)

theorem src_contact_spec : SrcContactClauses rot tb :=
  Classical.choose_spec (Classical.choose_spec src_contact)

/-! ### Sanity theorems: the axiom is exactly the printed formulas, no more -/

/-- The cusp calculation of fd:contact's proof (sm-3:3452-3457): `tb − r = w − D = sl_Ng(F)`.
The third formula with the first two substituted. -/
theorem SrcContactClauses.pushoff_slNg {r tb : (ℝ → E3) → ℝ} (h : SrcContactClauses r tb)
    {L : ℝ → E3} {F : SmoothFront} (hF : IsLegendrianFrontOf L F) {T' : ℝ → E3}
    (hT : GenericFront.IsPositivePushoff L T') : slOf (2 * π) T' = (F.slNg : ℝ) := by
  rw [h.pushoff_self_linking L F hF T' hT, h.thurston_bennequin L F hF, h.rotation L F hF,
    SmoothFront.slNg_def]
  push_cast
  ring

/-- **The ∃-form asserts precisely the two consequences** — sl(T₊) = w − D on the Legendrian class
and sl = w on the transverse class — and nothing about `r`, `tb` beyond the two defining formulas
(FR-SC-1): conversely those two consequences yield witnesses `r`, `tb`. -/
theorem src_contact_iff_composite :
    (∃ r tb : (ℝ → E3) → ℝ, SrcContactClauses r tb) ↔
      (∀ (L : ℝ → E3) (F : SmoothFront), IsLegendrianFrontOf L F →
        ∀ T' : ℝ → E3, GenericFront.IsPositivePushoff L T' →
          slOf (2 * π) T' = (F.writhe : ℝ) - F.downCount) ∧
      (∀ K : TransverseKnot, sl K = (K.front.writhe : ℝ)) := by
  constructor
  · rintro ⟨r, tb, h⟩
    refine ⟨fun L F hF T' hT => ?_, h.transverse_front_writhe⟩
    have := h.pushoff_slNg hF hT
    rw [SmoothFront.slNg_def] at this
    push_cast at this
    exact this
  · rintro ⟨hL, hK⟩
    -- the witnesses: the formulas read on THE front of `L` (unique by `IsLegendrianFrontOf.unique`)
    let frontOf : (ℝ → E3) → Option SmoothFront := fun L =>
      if h : ∃ F, IsLegendrianFrontOf L F then some h.choose else none
    let r : (ℝ → E3) → ℝ := fun L =>
      match frontOf L with
      | some F => ((F.downCount : ℝ) - F.upCount) / 2
      | none => 0
    let tb : (ℝ → E3) → ℝ := fun L =>
      match frontOf L with
      | some F => (F.writhe : ℝ) - ((F.downCount : ℝ) + F.upCount) / 2
      | none => 0
    have hfront : ∀ (L : ℝ → E3) (F : SmoothFront), IsLegendrianFrontOf L F → frontOf L = some F := by
      intro L F hF
      have hex : ∃ F, IsLegendrianFrontOf L F := ⟨F, hF⟩
      simp only [frontOf, dif_pos hex]
      exact congrArg some (hex.choose_spec.unique hF)
    refine ⟨r, tb, ⟨fun L F hF => ?_, fun L F hF => ?_, fun L F hF T' hT => ?_, hK⟩⟩
    · simp only [r, hfront L F hF]
    · simp only [tb, hfront L F hF]
    · simp only [r, tb, hfront L F hF]
      rw [hL L F hF T' hT]
      ring

/-! ## 4. Row 94 fd:contact (sm-3:3404-3423): the statement with the real `sl` -/

/-- The transverse knot `T` of def:transverse-front as a one-component `SpatialLink` (rows 89-91
vocabulary; the same `Space`, the same period `1`). -/
def TransverseKnot.spatial (K : TransverseKnot) : SpatialLink 1 where
  T := fun _ => K.T
  smooth := fun _ => K.smooth
  periodic := fun _ => K.periodic
  embedded := fun i j s t h => ⟨Subsingleton.elim i j, K.embedded s t h⟩
  regular := fun _ t => K.deriv_T_ne_zero t

/-- "whose specified xz projection `D_T` is an ordinary finite regular generic diagram" — FR-1:
the polygonal `Diagram X` reads `D_T` with `T`'s own heights (over = smaller `y`), exactly the
reading rows 90/91 take for the endpoint `T` (`SpatialLink.HeightMarking`). -/
def TransverseKnot.Reads (K : TransverseKnot) (X : Diagram) : Prop :=
  Nonempty (K.spatial.HeightMarking K.spatial.projLoop X)

/-- `D_T` is regular generic in the sense of rows 89-91 (bridge; the heights at a double point are
distinct because `T` is embedded, `y_ne_of_isDouble`). -/
theorem TransverseKnot.spatial_regularGeneric (K : TransverseKnot) :
    K.spatial.RegularGenericProjection := by
  sorry -- BRIDGE B-1 (K's fields → `RegularGenericProjection`; `Fin 1` bookkeeping)

/-- **fd:contact** (sm-3:3404-3423), one field per printed clause.  "In the xz front page the
smaller-y branch is over, and its crossing sign is sgn det_xz(u_O, u_U)" = `over_rule_sign`
(definitional on the accepted class, row 92); display fd:front-writhe = `front_writhe`; "Let T be
an individual smooth positive transverse knot whose specified xz projection D_T is an ordinary
finite regular generic diagram. With P_T denoting the original campaign polynomial of this actual
diagram, one has [fd:representative-bound]" = `representative_bound`, `P_T = P X` for every
polygonal reading `X` of `D_T` (FR-1).  The two closing sentences ("The finite specified-diagram
hypothesis is part of this auxiliary bound; no assertion that every smooth knot has a generic
specified projection is required. The carrier-floor construction supplies such a diagram.") are
commentary on the hypotheses and have no field. -/
structure FdContactData : Prop where
  /-- sm-3:3406-3407, the first sentence (the front page convention, definitional on row 92). -/
  over_rule_sign : ∀ (K : TransverseKnot) (s t : ℝ), K.front.IsDouble s t →
    (K.front.isOver s t ↔ yOf K.T s < yOf K.T t) ∧
    K.front.crossSign s t = ((SignType.sign (det (K.front.vel s) (K.front.vel t)) : SignType) : ℤ)
  /-- display fd:front-writhe (sm-3:3409-3411): `sl(T) = Σ_q sgn det_xz(u_O(q), u_U(q))`. -/
  front_writhe : ∀ K : TransverseKnot, sl K = (K.front.writhe : ℝ)
  /-- display fd:representative-bound (sm-3:3412-3418): `sl(T) ≤ −max deg_a P_T(a,z) − 1`. -/
  representative_bound : ∀ (K : TransverseKnot) (X : Diagram), K.Reads X →
    sl K ≤ -((degAZ (P X) : ℤ) : ℝ) - 1

/-- The first two fields hold now (row 92 and the axiom's transverse clause). -/
theorem fdContact_over_rule_sign (K : TransverseKnot) (s t : ℝ) (h : K.front.IsDouble s t) :
    (K.front.isOver s t ↔ yOf K.T s < yOf K.T t) ∧
    K.front.crossSign s t = ((SignType.sign (det (K.front.vel s) (K.front.vel t)) : SignType) : ℤ) :=
  ⟨⟨fun h' => h'.2, fun h' => ⟨h, h'⟩⟩, K.front.crossSign_eq_sign h⟩

theorem fdContact_front_writhe (K : TransverseKnot) : sl K = (K.front.writhe : ℝ) :=
  src_contact_spec.transverse_front_writhe K

/-! ## 5. Rows 161 / 162 (CV axioms as theorems; free names, cv-lane plan §161/§162) -/

namespace CV

/-- **CV:ax:etnyre** (d10_axioms.tex:387-397): "Let T be a front diagram of a transverse knot with
no downward vertical tangency. Then sl(T) equals the writhe of T."  The front diagram `D` of the
transverse knot `K` (def:transverse-front's class, on which "no downward vertical tangency" is
automatic — the hypothesis is kept as printed); `sl(T)` is the document's `SM.sl`. -/
theorem ax_etnyre (D : SM.SmoothKnotDiagram) (K : SM.TransverseKnot) (hD : K.front = D)
    (_hvert : ∀ t : ℝ, (D.vel t).1 = 0 → 0 < (D.vel t).2) : SM.sl K = (D.writhe : ℝ) := by
  subst hD
  exact SM.src_contact_spec.transverse_front_writhe K

/-- **CV:ax:slbound** (d10_axioms.tex:399-425), the statement: "Let T be a transverse knot in the
standard contact ℝ³ and let P_T(a,z) be the HOMFLY–PT polynomial of the knot it presents, in the
normalization of Axiom ax:homfly. Then sl(T) ≤ −max deg_a P_T(a,z) − 1."  Domain narrowed to the
transverse knots with a generic front (fd:contact's own domain, memo §3(b)); "the knot it presents"
read as the polygonal reading `X` of the front (FR-1), its polynomial `homfly X` (ax:homfly's
normalization = `SM.lit_homfly`). -/
def AxSlboundStatement : Prop :=
  ∀ (K : SM.TransverseKnot) (X : SM.Link.Diagram), K.Reads X →
    SM.sl K ≤ -((SM.Link.degAZ (SM.homfly X) : ℤ) : ℝ) - 1

/-- Row 162 from row 94 (`P = homfly` by lp:core). -/
theorem ax_slbound_of (h : SM.FdContactData) : AxSlboundStatement := by
  intro K X hX
  have := h.representative_bound K X hX
  rwa [SM.P_eq_homfly] at this

end CV

/-! ## 6. The proof route of row 94 (DESIGN_A.md §4): the bridge lemmas, statements fixed -/

section Route

open GenericFront

/-- B-2 (period / coordinate bridge): the `2π`-periodic `E3` reading of `K` is a positive transverse
circle of row 84's hypothesis class. -/
theorem TransverseKnot.transverseNeighborhoodHyp (K : TransverseKnot) :
    TransverseNeighborhoodHyp (toCircle2π K.T) := by
  sorry

/-- B-3 (reparametrization invariance of fd:framed-linking): `slOf` is unchanged by an
orientation-preserving reparametrization of the circle (change of variables in the Gauss double
integral; NOT a clause of row 88). -/
theorem slOf_comp_reparam {T : ℝ → E3} (hT : IsPositiveTransverseEmbedding (2 * π) T)
    {ρ : ℝ → ℝ} (hρ : IsCircleReparam ρ) : slOf (2 * π) (T ∘ ρ) = slOf (2 * π) T := by
  sorry

/-- B-3′ (period rescaling): `sl K` is `slOf` of the `2π`-periodic reading. -/
theorem sl_eq_slOf_toCircle2π (K : TransverseKnot) : sl K = slOf (2 * π) (toCircle2π K.T) := by
  sorry

/-- B-4 (row 88 along a transverse isotopy): `slOf` is constant along `TransverselyIsotopic`
(time clamp `Real.smoothTransition` from the strip `[0,1] × ℝ` to `ℝ × ℝ`, then
`self_linking_invariant`, then B-3 for the end reparametrization). -/
theorem slOf_eq_of_transverselyIsotopic {T₀ T₁ : ℝ → E3}
    (h₀ : IsPositiveTransverseEmbedding (2 * π) T₀) (h₁ : IsPositiveTransverseEmbedding (2 * π) T₁)
    (h : TransverselyIsotopic T₀ T₁) : slOf (2 * π) T₀ = slOf (2 * π) T₁ := by
  sorry

/-- B-5 (the Legendrian front as a `SmoothFront`): a generic Legendrian front (row 87's output
class) is on ng:front-domain — semicubical cusps with `x″ ≠ 0` from the exact germ (chain rule
through `u = y − y₀`), no vertical tangency on regular arcs from `z′ = y x′`, the double-point and
cusp clauses verbatim. -/
theorem exists_legendrianFront {L : ℝ → E3} (hL : GenericFrontHyp L) (hg : IsGenericFront L) :
    ∃ F : SmoothFront, IsLegendrianFrontOf L F := by
  sorry

/-- B-6 (FR-1 reading existence for the rounding of a front): every `SmoothFront` has a polygonal
rounding — the geometric rounding from row 89 (`ce_rounding`, on the `SpatialLink 1` reading of `L`)
and the polygonal reading from the sweep of the certificate lane (`sweep_proof`, `realize`), the
`Marking` recovered from the record isomorphism (inverse of `markingRecordIso`). -/
theorem exists_isRounding_of_legendrianFront {L : ℝ → E3} {F : SmoothFront}
    (hF : IsLegendrianFrontOf L F) (hg : IsGenericFront L) :
    ∃ (S : Diagram) (L₁ : SpatialLink 1) (G : Fin 1 → SmoothLoop),
      F.IsRounding S ∧ L₁.CuspedProjection ∧ (∀ t, L₁.T 0 t = toSpace (L (2 * π * t))) ∧
      Nonempty (L₁.CleanCuspSmoothing G) ∧ Nonempty (L₁.HeightMarking G S) := by
  sorry

/-- B-7 (the supplied family `G_t = Ψ_t ∘ Φ_{1−t} ∘ L`, sm-3:3476-3488, as a `SpatialFamily 1` in
`Space`, period `1`, time-clamped): starts at the parametrized `L_T = Φ_1 ∘ L`, ends at `T`. -/
theorem exists_suppliedFamily {L T : ℝ → E3} {Φ Ψ : ℝ → E3 → E3}
    (hΦ : IsContactIsotopy Φ) (hΨ : IsCompactlySupportedAmbientIsotopy Ψ)
    (hL : IsEmbeddedCircle L) (hΨL : ∀ θ, Ψ 1 (L θ) = T θ)
    (L₁ : SpatialLink 1) (hL₁ : ∀ t, L₁.T 0 t = toSpace (Φ 1 (L (2 * π * t))))
    (K : TransverseKnot) (hK : ∀ t, toE3 (K.T t) = T (2 * π * t)) :
    ∃ Fam : SpatialFamily 1, Fam.G 0 = L₁ ∧ Fam.G 1 = K.spatial := by
  sorry

/-- **Row 94 from the bridges** (the printed proof, sm-3:3459-3499): rows 84 → 87 → 88 → 93 → 91
with the axiom's cusp calculation. -/
theorem fd_contact_of_bridges : FdContactData where
  over_rule_sign := fdContact_over_rule_sign
  front_writhe := fdContact_front_writhe
  representative_bound := by
    intro K X hX
    -- row 84 on T₂π := toCircle2π K.T
    obtain ⟨δ, H, h, L, Ψ, hTN⟩ := fd_transverse_neighborhood _ K.transverseNeighborhoodHyp
    -- row 87 on the helix L
    have hLhyp : GenericFrontHyp L := ⟨⟨hTN.legendrian_circle.1, hTN.legendrian_circle.2,
      hTN.legendrian_circle.3, hTN.legendrian_circle.4⟩, hTN.legendrian⟩
    obtain ⟨Φ, hGF⟩ := fd_generic_front L hLhyp
    -- the pushoff transversely isotopic to T, carried by Φ
    obtain ⟨T', ⟨ε, b, B, hB, s₀, hs₀, hs₀b, hT'⟩, hT'T⟩ := hTN.pushoff_isotopic
    have hB' : IsPushoffAnnulus L ε b B := ⟨hB.1, hB.2, hB.3, hB.4, hB.5, hB.6, hB.7, hB.8, hB.9⟩
    obtain ⟨_, hpush⟩ := hGF.pushoff ε b B hB'
    obtain ⟨hiso, hpos⟩ := hpush s₀ hs₀ hs₀b
    -- the front F_T of L_T := Φ 1 ∘ L and the cusp calculation
    obtain ⟨F, hF⟩ := exists_legendrianFront ⟨hGF.legendrian_circle, hGF.legendrian⟩ hGF.generic
    have hsl : slOf (2 * π) (fun θ => Φ 1 (B (θ, s₀))) = (F.slNg : ℝ) :=
      src_contact_spec.pushoff_slNg hF hpos
    -- sl transport (row 88): sl K = sl T₂π = sl T' = sl (Φ 1 ∘ T')
    sorry -- assembly: B-2/B-3/B-4 on `hT'T` and `hiso`, then B-5/B-6/B-7, row 93 `fd_ng_bound.ng_input`,
          -- row 91 `cp_finite_contact_path.endpoint_polynomial`, and `degAZ (P S) = degAZ (P X)`.

end Route

end

end SM
