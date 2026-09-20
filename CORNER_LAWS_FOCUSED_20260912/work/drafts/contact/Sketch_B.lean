import SM.TransverseFront
import SM.LinkingCalculusRow
import SM.NgBound
import SM.ContactPath
import SM.GenericFront
import SM.TransverseNeighborhood

/-! # src:contact / fd:contact / CV:ax:etnyre / CV:ax:slbound — design sketch B (proof feasibility)

Companion of work/drafts/contact/DESIGN_B.md (2026-09-15).  Everything here typechecks against the
accepted layer; the ONE `axiom` below (`SM.src_contact`) is the fifth literature interface with its
policy name (lean/axiom-policy.json).  The prover units U0-U7 of the design are stated as named
Props (§5) and the row theorem is PROVED from them (`fd_contact_of_units`), so the composition of the
printed proof of fd:contact through the accepted rows 84 → 87 → src:contact → 93 → 91 is
kernel-checked here; only the units remain.  Check: `cd work/lean && lake env lean ../drafts/contact/Sketch_B.lean`. -/

namespace SM

open SM.Link TransverseNeighborhood
open scoped ContDiff
open Set Function Real

noncomputable section
open Classical

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## 0. The three conventions and their conversions

* def:transverse-front (row 92): `Space = ℝ × ℝ × ℝ`, 1-periodic `TransverseKnot`;
* rows 84/87/88: `E3 = EuclideanSpace ℝ (Fin 3)`, 2π-periodic circles (period `P = 2π` in row 88);
* rows 89-91: `SpatialLink c` on `Space`, 1-periodic. -/

/-- `Space → ℝ³` (coordinates preserved) -/
def toE3 (p : Space) : E3 := !₂[p.1, p.2.1, p.2.2]
/-- `ℝ³ → Space` -/
def toSpace (q : E3) : Space := (q 0, q 1, q 2)

theorem toSpace_toE3 (p : Space) : toSpace (toE3 p) = p := by
  obtain ⟨x, y, z⟩ := p
  simp [toSpace, toE3]

theorem toE3_toSpace (q : E3) : toE3 (toSpace q) = q := by
  ext i; fin_cases i <;> simp [toSpace, toE3]

/-- the contact form is the same expression in all three modules -/
theorem alpha_eq_lcContactForm : TransverseNeighborhood.alpha = lcContactForm := rfl
theorem gf_alpha_eq_lcContactForm : GenericFront.alpha = lcContactForm := rfl

namespace TransverseKnot

variable (K : TransverseKnot)

/-- the knot of def:transverse-front as a 2π-periodic circle in oriented `ℝ³` (the object of rows
84, 87, 88): `θ ↦ T(θ / 2π)` -/
def circle : ℝ → E3 := fun θ => toE3 (K.T (θ / (2 * π)))

/-- the knot as a one-component spatial link (the object of rows 89-91), same parametrization -/
def spatial : SpatialLink 1 where
  T := fun _ => K.T
  smooth := fun _ => K.smooth
  periodic := fun _ => K.periodic
  embedded := fun i j s t h => ⟨Subsingleton.elim i j, K.embedded s t h⟩
  regular := fun _ t => K.deriv_T_ne_zero t

@[simp] theorem spatial_T (i : Fin 1) : K.spatial.T i = K.T := rfl

/-- the projection of the spatial link is the loop of the front -/
theorem spatial_projLoop (i : Fin 1) : K.spatial.projLoop i = K.xz := by
  cases i; rfl

end TransverseKnot

/-! ## 1. The self-linking number `sl` (fd:framed-linking, sm-3:2820-2824), from the accepted row 88

`selfLinking P T ε = ℓ(T, T + ε∂_y)`; row 88 gives one radius `ε₀ > 0` for every transverse family,
and independence of the radius and of the family parameter.  We fix the radius ONCE by
`Classical.choose` on the constant family `s ↦ T`, so that `sl` is a function of `T` alone. -/

/-- the constant transverse family of one positive transverse embedding (period `2π`) -/
theorem IsPositiveTransverseEmbedding.constFamily {T : ℝ → E3}
    (h : IsPositiveTransverseEmbedding (2 * π) T) : TransverseFamily (2 * π) (fun _ => T) where
  pos := by positivity
  smooth := by
    show ContDiff ℝ ∞ (fun p : ℝ × ℝ => T p.2)
    exact h.circle.smooth.comp contDiff_snd
  periodic := fun _ => h.circle.periodic
  embedded := fun _ _ u u' hu => h.embedded u u' hu
  positive := fun _ _ u => h.positive u

/-- `sl(T)` for a 2π-periodic positive transverse embedding `T : S¹ → ℝ³`: `ℓ(T, T + ε₀ ∂_y)` at the
radius `ε₀` of fd:linking-calculus (`transverse_uniform`) for the constant family; `0` off the class.
Row 88 (`self_linking_invariant`) makes it independent of the admissible radius (unit U1). -/
def slCircle (T : ℝ → E3) : ℝ :=
  if h : IsPositiveTransverseEmbedding (2 * π) T then
    selfLinking (2 * π) T
      (Classical.choose (fd_linking_calculus.transverse_uniform (2 * π) (fun _ => T) h.constFamily))
  else 0

/-- the document's self-linking number of a generic positive transverse knot (def:transverse-front),
read through the 2π-periodic circle -/
def TransverseKnot.sl (K : TransverseKnot) : ℝ := slCircle K.circle

/-! ## 2. "An oriented Legendrian front": a front on ng:front-domain that is the `xz` projection of a
Legendrian circle (parameter bridge `θ = 2π t`) -/

/-- `F` is the `xz` front of the 2π-periodic space curve `L`: one parameter circle, and the loop is
`t ↦ (x(2πt), z(2πt))` -/
def IsFrontOf (F : SmoothFront) (L : ℝ → E3) : Prop :=
  F.c = 1 ∧ ∀ (i : Fin F.c) (t : ℝ), (F.comp i).γ t = (L (2 * π * t) 0, L (2 * π * t) 2)

/-- a curve has at most one front on the class (the loop determines the `SmoothFront`) -/
theorem IsFrontOf.eq {F F' : SmoothFront} {L : ℝ → E3} (h : IsFrontOf F L) (h' : IsFrontOf F' L) :
    F = F' := by
  obtain ⟨hc, hF⟩ := h
  obtain ⟨hc', hF'⟩ := h'
  cases F with
  | mk c hc0 comp a1 a2 a3 a4 a5 a6 a7 a8 =>
  cases F' with
  | mk c' hc0' comp' b1 b2 b3 b4 b5 b6 b7 b8 =>
  simp only at hc hc' hF hF'
  subst hc; subst hc'
  have : comp = comp' := by
    funext i
    have hγ : (comp i).γ = (comp' i).γ := by
      funext t; rw [hF i t, hF' i t]
    cases hi : comp i with
    | mk γ s p =>
    cases hi' : comp' i with
    | mk γ' s' p' =>
    rw [hi, hi'] at hγ
    simp only at hγ
    subst hγ
    rfl
  subst this
  rfl

/-! ## 3. The fifth literature interface `SM.src_contact` (blueprint/AXIOM_REGISTRY.md §src:contact =
sm-3:3341-3365), one field per printed clause, ∃-form over the literature's `r`, `tb` (functions of
the Legendrian knot, never defined by the document), fixed below by `Classical.choose`. -/

/-- The printed clauses of src:contact for candidate rotation and Thurston–Bennequin functions
`r tb : (ℝ → ℝ³) → ℝ` on Legendrian circles.  "an oriented Legendrian front with downward and upward
cusp counts D, U" = a `SmoothFront` `F` (ng:front-domain) with `IsFrontOf F L` for an oriented
Legendrian embedded circle `L` (orientation = parameter direction), `D = F.downCount`,
`U = F.upCount`, `w = F.writhe`; "T₊(L)" = any positive transverse pushoff of `L` in the document's
sense (`IsPositivePushoff`, row 84, FR-TN-4); "sl" = the document's fd:framed-linking number
`slCircle` (rem:sl-convention identifies it with the literature's). -/
structure SrcContactClauses (r tb : (ℝ → E3) → ℝ) : Prop where
  /-- "Use standard contact space (ℝ³, ker(dz − y dx))" (3342-3343): the contact form is
  `α_p(v) = v_z − p_y v_x` (convention; `rfl` on the accepted `lcContactForm`). -/
  contact_space : ∀ p v : E3, lcContactForm p v = v 2 - p 1 * v 0
  /-- "with positive transverse orientation z′ − y x′ > 0" (3343-3344): a positive transverse circle is
  one with `α(T′) > 0` (convention; `Iff.rfl` on the accepted `IsPositiveTransverse`). -/
  positive_orientation : ∀ T : ℝ → E3,
    IsPositiveTransverse T ↔ ∀ θ, 0 < lcContactForm (T θ) (deriv T θ)
  /-- "every cusp of an oriented front is traversed either downward or upward, so the total cusp count
  in his tb formula is D+U" (3348-3350): `D + U = #cusps` (a theorem of the accepted class,
  `downCount_add_upCount`). -/
  cusps_down_or_up : ∀ F : SmoothFront, F.downCount + F.upCount = F.cuspSet.card
  /-- display fd:contact-inputs, first formula: "r = (D − U)/2" (3352). -/
  rotation : ∀ (L : ℝ → E3) (F : SmoothFront), IsEmbeddedCircle L → IsLegendrian L → IsFrontOf F L →
    r L = ((F.downCount : ℝ) - F.upCount) / 2
  /-- display fd:contact-inputs, second formula: "tb = w − (D + U)/2" (3352). -/
  thurston_bennequin : ∀ (L : ℝ → E3) (F : SmoothFront), IsEmbeddedCircle L → IsLegendrian L →
    IsFrontOf F L → tb L = (F.writhe : ℝ) - ((F.downCount : ℝ) + F.upCount) / 2
  /-- display fd:contact-inputs, third formula: "sl(T₊(L)) = tb(L) − r(L)" (3353), for every positive
  transverse pushoff `T₊(L)` of `L` in the document's sense. -/
  pushoff_self_linking : ∀ (L T' : ℝ → E3) (F : SmoothFront), IsEmbeddedCircle L → IsLegendrian L →
    IsFrontOf F L → IsPositivePushoff L T' → slCircle T' = tb L - r L
  /-- "For a generic positive transverse front (Definition def:transverse-front), self-linking equals
  its front writhe" (3359-3361): for the knot `T` of every generic positive transverse front
  (`TransverseKnot`, the class of row 92; "the knot T is named separately"), `sl(T) = w(front)`. -/
  transverse_front_writhe : ∀ K : TransverseKnot, K.sl = K.front.writhe

/-- **src:contact** (AXIOM_REGISTRY.md §src:contact, sm-3:3341-3365; policy name `SM.src_contact`):
"Use standard contact space (ℝ³, ker(dz − y dx)), with positive transverse orientation z′ − yx′ > 0.
Etnyre's front and pushoff statements give, for an oriented Legendrian front with downward and upward
cusp counts D, U — every cusp of an oriented front is traversed either downward or upward, so the
total cusp count in his tb formula is D+U — r = (D−U)/2, tb = w − (D+U)/2, sl(T₊(L)) = tb(L) − r(L).
… For a generic positive transverse front (Definition def:transverse-front), self-linking equals its
front writhe … These are the local front and pushoff source formulas only."  The parenthetical
provenance sentence (3354-3357), the citations and the closing scope sentence have no field.
Existence in ∃-form over the literature's `r`, `tb`. -/
axiom src_contact : ∃ r tb : (ℝ → E3) → ℝ, SrcContactClauses r tb

/-- the rotation number `r(L)` of the literature: one witness of `src_contact`, fixed once -/
def legRotation : (ℝ → E3) → ℝ := Classical.choose src_contact
/-- the Thurston–Bennequin invariant `tb(L)` of the literature: fixed once -/
def legTb : (ℝ → E3) → ℝ := Classical.choose (Classical.choose_spec src_contact)

theorem src_contact_clauses : SrcContactClauses legRotation legTb :=
  Classical.choose_spec (Classical.choose_spec src_contact)

/-! ### 3.1 Sanity: the convention fields are provable, the substituted consequence, and the ∃-form is
EQUIVALENT to the substituted form (so the axiom is neither stronger nor weaker than the printed
display read with `r`, `tb` eliminated) -/

theorem srcContact_contact_space : ∀ p v : E3, lcContactForm p v = v 2 - p 1 * v 0 := fun _ _ => rfl
theorem srcContact_positive_orientation : ∀ T : ℝ → E3,
    IsPositiveTransverse T ↔ ∀ θ, 0 < lcContactForm (T θ) (deriv T θ) := fun _ => Iff.rfl

/-- the printed cusp calculation of fd:contact's proof (sm-3:3441-3447): `tb − r = w − (D+U)/2 −
(D−U)/2 = w − D = sl_Ng(F)` -/
theorem SrcContactClauses.pushoff_slNg {r tb : (ℝ → E3) → ℝ} (h : SrcContactClauses r tb)
    (L T' : ℝ → E3) (F : SmoothFront) (hL : IsEmbeddedCircle L) (hleg : IsLegendrian L)
    (hF : IsFrontOf F L) (hT' : IsPositivePushoff L T') : slCircle T' = (F.slNg : ℝ) := by
  rw [h.pushoff_self_linking L T' F hL hleg hF hT', h.thurston_bennequin L F hL hleg hF,
    h.rotation L F hL hleg hF, SmoothFront.slNg_def]
  push_cast
  ring

/-- the substituted form of the display (what the proof of fd:contact consumes) together with the
transverse-front clause -/
structure SrcContactConsequence : Prop where
  pushoff_slNg : ∀ (L T' : ℝ → E3) (F : SmoothFront), IsEmbeddedCircle L → IsLegendrian L →
    IsFrontOf F L → IsPositivePushoff L T' → slCircle T' = (F.slNg : ℝ)
  transverse_front_writhe : ∀ K : TransverseKnot, K.sl = K.front.writhe

/-- the front of `L`, if any, chosen once (for the converse direction below) -/
def frontOf (L : ℝ → E3) : Option SmoothFront :=
  if h : ∃ F : SmoothFront, IsFrontOf F L then some h.choose else none

/-- **The ∃-form is equivalent to the substituted form.**  → : the cusp calculation.  ← : define `r`
and `tb` by the two printed formulas on the (unique) front of `L`. -/
theorem srcContact_iff_consequence :
    (∃ r tb : (ℝ → E3) → ℝ, SrcContactClauses r tb) ↔ SrcContactConsequence := by
  constructor
  · rintro ⟨r, tb, h⟩
    exact ⟨fun L T' F hL hleg hF hT' => h.pushoff_slNg L T' F hL hleg hF hT',
      h.transverse_front_writhe⟩
  · intro h
    refine ⟨fun L => if hL : ∃ F, IsFrontOf F L then ((hL.choose.downCount : ℝ) - hL.choose.upCount) / 2 else 0,
      fun L => if hL : ∃ F, IsFrontOf F L then
        (hL.choose.writhe : ℝ) - ((hL.choose.downCount : ℝ) + hL.choose.upCount) / 2 else 0, ?_⟩
    have key : ∀ (L : ℝ → E3) (F : SmoothFront) (hF : IsFrontOf F L),
        (⟨F, hF⟩ : ∃ F, IsFrontOf F L).choose = F := fun L F hF =>
      IsFrontOf.eq (Classical.choose_spec (⟨F, hF⟩ : ∃ F, IsFrontOf F L)) hF
    refine ⟨srcContact_contact_space, srcContact_positive_orientation,
      SmoothFront.downCount_add_upCount, ?_, ?_, ?_, h.transverse_front_writhe⟩
    · intro L F hL hleg hF
      have hex : ∃ F, IsFrontOf F L := ⟨F, hF⟩
      simp only [hex, ↓reduceDIte, key L F hF]
    · intro L F hL hleg hF
      have hex : ∃ F, IsFrontOf F L := ⟨F, hF⟩
      simp only [hex, ↓reduceDIte, key L F hF]
    · intro L T' F hL hleg hF hT'
      have hex : ∃ F, IsFrontOf F L := ⟨F, hF⟩
      simp only [hex, ↓reduceDIte, key L F hF]
      rw [h.pushoff_slNg L T' F hL hleg hF hT', SmoothFront.slNg_def]
      push_cast
      ring

/-! ## 4. The rows -/

/-- **fd:contact** (sm-3:3404-3423), one field per printed clause; `sl` is the document's
`TransverseKnot.sl` (fd:framed-linking through row 88); "whose specified xz projection D_T is an
ordinary finite regular generic diagram" is every `TransverseKnot` (def:transverse-front), the
diagram read polygonally by a `HeightMarking` of its one-component spatial link (FR-1, the reading
of row 91's endpoint); "P_T the original campaign polynomial of this actual diagram" is `P X`.  The
two closing sentences (3418-3421) are commentary on the hypothesis and have no field. -/
structure FdContactData : Prop where
  /-- "In the xz front page the smaller-y branch is over, and its crossing sign is sgn det_xz(u_O, u_U)"
  (3406-3407): definitional on the accepted class. -/
  over_rule_sign : ∀ (K : TransverseKnot) (s t : ℝ), K.front.IsDouble s t →
    (K.front.isOver s t ↔ yOf K.T s < yOf K.T t) ∧
    K.front.crossSign s t = ((SignType.sign (det (K.front.vel s) (K.front.vel t)) : SignType) : ℤ)
  /-- display fd:front-writhe (3409-3411): "sl(T) = Σ_q sgn det_xz(u_O(q), u_U(q))". -/
  front_writhe : ∀ K : TransverseKnot, K.sl = K.front.writhe
  /-- display fd:representative-bound (3412-3417): "sl(T) ≤ −max deg_a P_T(a,z) − 1" for every
  polygonal reading `X` of the specified diagram `D_T`. -/
  representative_bound : ∀ (K : TransverseKnot) (X : Diagram),
    Nonempty (K.spatial.HeightMarking K.spatial.projLoop X) →
    K.sl ≤ ((-degAZ (P X) - 1 : ℤ) : ℝ)

namespace CV

/-- **CV:ax:etnyre** (d10_axioms.tex:387-397): "Let T be a front diagram of a transverse knot with no
downward vertical tangency. Then sl(T) equals the writhe of T."  The front of a transverse knot is a
generic positive transverse front (`K.front`, def:transverse-front); the printed hypothesis is kept
as an explicit (redundant, `TransverseKnot.vertical_up`) hypothesis; `sl` is SM's fd:framed-linking
number (the CV text never defines it, "Why it is not proved here"). -/
structure AxEtnyreData : Prop where
  self_linking_eq_writhe : ∀ K : SM.TransverseKnot,
    (∀ t, deriv (xOf K.T) t = 0 → 0 < deriv (zOf K.T) t) → K.sl = K.front.writhe

/-- **CV:ax:slbound** (d10_axioms.tex:399-425): "Let T be a transverse knot in the standard contact ℝ³
and let P_T(a,z) be the HOMFLY–PT polynomial of the knot it presents, in the normalization of Axiom
ax:homfly. Then sl(T) ≤ −max deg_a P_T(a,z) − 1."  Recorded narrowing: `T` ranges over the transverse
knots with a generic front (`TransverseKnot`, SM fd:contact's own domain); "the knot it presents" has
polynomial `homfly X` (CV:ax:homfly's map) for any polygonal reading `X` of its front (FR-1). -/
structure AxSlboundData : Prop where
  bound : ∀ (K : SM.TransverseKnot) (X : Diagram),
    Nonempty (K.spatial.HeightMarking K.spatial.projLoop X) →
    K.sl ≤ ((-degAZ (homfly X) - 1 : ℤ) : ℝ)

/-- row 161 from row 94 (the printed hypothesis is discharged by `vertical_up`; unused) -/
theorem ax_etnyre_of (h : FdContactData) : AxEtnyreData :=
  ⟨fun K _ => h.front_writhe K⟩

/-- row 162 from row 94 (`P = homfly`, lp:core) -/
theorem ax_slbound_of (h : FdContactData) : AxSlboundData :=
  ⟨fun K X hX => by rw [← P_eq_homfly]; exact h.representative_bound K X hX⟩

end CV

/-! ## 5. The proof of fd:contact through rows 84 → 87 → src:contact → 93 → 91: the units (named
Props) and the assembly theorem.  Each unit is one prover unit of DESIGN_B.md §4. -/

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

/-- U0: the knot of def:transverse-front is a row-84 input (2π-periodic embedded, `α(T′) > 0`) -/
def U_circle : Prop := ∀ K : TransverseKnot, TransverseNeighborhoodHyp K.circle

/-- U1: `sl` is a transverse-isotopy invariant (row 88's `self_linking_invariant` +
`transverse_uniform` on the family extended to `ℝ × ℝ` by a smooth clock, and reparametrization
invariance through the family `(1−s)·id + s·ρ`) -/
def U_sl_isotopy : Prop := ∀ T₀ T₁ : ℝ → E3, TransverselyIsotopic T₀ T₁ → slCircle T₀ = slCircle T₁

/-- U6a: the specified projection of a transverse knot is an ordinary finite regular generic diagram
in row 91's sense -/
def U_regular : Prop := ∀ K : TransverseKnot, K.spatial.RegularGenericProjection

/-- The data the printed proof extracts from `L_T = Φ₁ ∘ L` (units U2-U5): its spatial link, its
front `F_T` on ng:front-domain, the rounding `S(F_T)` as both a rounding of `F_T` (row 93) and a
clean cusp smoothing with a height reading (row 91). -/
structure LegendrianPackage (Lc : ℝ → E3) where
  /-- the one-component spatial link of `L_T` (1-periodic, on `Space`) -/
  sp : SpatialLink 1
  sp_T : ∀ (i : Fin 1) (t : ℝ), sp.T i t = toSpace (Lc (2 * π * t))
  /-- the front `F_T` -/
  F : SmoothFront
  F_front : IsFrontOf F Lc
  /-- row 91's input class for `L_T` -/
  cusped : sp.CuspedProjection
  /-- the rounded curves `S(F_T)` and one polygonal reading `S` -/
  G : Fin 1 → SmoothLoop
  S : Diagram
  clean : Nonempty (sp.CleanCuspSmoothing G)
  height_marking : Nonempty (sp.HeightMarking G S)
  rounding : F.IsRounding S

/-- U2-U5: every Legendrian embedded circle with a generic front (row 87's output) has such a
package -/
def U_package : Prop := ∀ Lc : ℝ → E3, GenericFront.IsEmbeddedCircle Lc → GenericFront.IsLegendrian Lc →
  GenericFront.IsGenericFront Lc → Nonempty (LegendrianPackage Lc)

/-- U6: the supplied family `G_t = Ψ_t ∘ Φ_{1−t} ∘ L` (display fd:contact-ambient-composition) as a
`SpatialFamily 1` from `L_T`'s spatial link to the knot's, with the endpoint reading transported -/
def U_family : Prop := ∀ (K : TransverseKnot) (L : ℝ → E3) (Ψ Φ : ℝ → E3 → E3)
    (pkg : LegendrianPackage (Φ 1 ∘ L)),
  IsCompactlySupportedAmbientIsotopy Ψ → (∀ θ, Ψ 1 (L θ) = K.circle θ) →
  GenericFront.IsContactIsotopy Φ →
  ∃ Fam : SpatialFamily 1, Fam.G 0 = pkg.sp ∧ (Fam.G 1).RegularGenericProjection ∧
    ∀ X : Diagram, Nonempty (K.spatial.HeightMarking K.spatial.projLoop X) →
      Nonempty ((Fam.G 1).HeightMarking (Fam.G 1).projLoop X)

/-! ### 5.2 The assembly: fd:contact from the units and the accepted rows -/

/-- **fd:contact from the units** — the printed proof (sm-3:3424-3492) composed on the accepted
vocabulary: row 84 gives `L`, `T′` (positive pushoff transversely isotopic to `T`) and `Ψ`; row 87
gives `Φ`, `L_T = Φ₁ ∘ L` with generic front, and carries `T′` to a positive pushoff of `L_T`
transversely isotopic to it; row 88 (U1) transports `sl`; src:contact's cusp calculation gives
`sl(T₊(L_T)) = sl_Ng(F_T)`; row 93 bounds it by `−max deg_a P_{S(F_T)} − 1`; row 91 on the supplied
family (U6) gives `P_{S(F_T)} = P_{D_T}`. -/
theorem fd_contact_of_units (h0 : U_circle) (h1 : U_sl_isotopy) (h3 : U_package) (h4 : U_family) :
    FdContactData where
  over_rule_sign := fun K s t h =>
    ⟨by rw [K.front_isOver]; exact ⟨fun h' => h'.2, fun h' => ⟨h, h'⟩⟩, K.front.crossSign_eq_sign h⟩
  front_writhe := src_contact_clauses.transverse_front_writhe
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
    have e1 : K.sl = slCircle (fun θ => B (θ, s₀)) := (h1 _ _ hiso).symm
    have e2 : slCircle (fun θ => B (θ, s₀)) = slCircle (fun θ => Φ 1 (B (θ, s₀))) :=
      h1 _ _ (transverselyIsotopic_ofGF hiso2)
    -- sl(T₊(L_T)) = w(F_T) − D(F_T)             (src:contact, the cusp calculation)
    have e3 : slCircle (fun θ => Φ 1 (B (θ, s₀))) = (pkg.F.slNg : ℝ) :=
      src_contact_clauses.pushoff_slNg (Φ 1 ∘ L) _ pkg.F (embeddedCircle_ofGF c87.legendrian_circle)
        c87.legendrian pkg.F_front (pushoff_ofGF hpos2)
    -- sl_Ng(F_T) ≤ −max deg_a P_{S(F_T)} − 1     (row 93)
    have e4 : pkg.F.slNg ≤ -degAZ (P pkg.S) - 1 := fd_ng_bound.ng_input pkg.F pkg.S pkg.rounding
    -- P_{S(F_T)} = P_{D_T}                        (row 91 on the supplied family)
    have e5 : P pkg.S = P X :=
      cp_finite_contact_path.endpoint_polynomial pkg.sp Nat.one_pos pkg.cusped Fam hF0 hreg X
        (hread X hX) pkg.G pkg.S pkg.clean pkg.height_marking
    rw [e1, e2, e3, ← e5]
    exact_mod_cast e4

/-! ### 5.3 The finer prover units behind `U_package` and `U_sl_isotopy` (DESIGN_B.md §4), and the
composition of `U_package` from them through the accepted row 89 (`ce_rounding`) -/

/-- U1a: `sl` is `ℓ(T, T + ε∂_y)` at EVERY admissible radius (row 88 `self_linking_invariant` on the
constant family) -/
def U_sl_radius : Prop := ∀ (T : ℝ → E3) (ε : ℝ), IsPositiveTransverseEmbedding (2 * π) T → 0 < ε →
  (∀ ε', 0 < ε' → ε' ≤ ε → ∀ u u', pushoff T (fun _ => ey) ε' u ≠ T u') →
  slCircle T = selfLinking (2 * π) T ε

/-- U1b: `sl` is constant along a transverse family (row 88 `transverse_uniform` +
`self_linking_invariant`, then U1a at both ends) -/
def U_sl_family : Prop := ∀ F : ℝ → ℝ → E3, TransverseFamily (2 * π) F →
  ∀ s ∈ Icc (0 : ℝ) 1, ∀ s' ∈ Icc (0 : ℝ) 1, slCircle (F s) = slCircle (F s')

/-- U1c: reparametrization invariance, through the family `ρ_s = (1 − s)·id + s·ρ` and U1b -/
def U_sl_reparam : Prop := ∀ (T : ℝ → E3) (ρ : ℝ → ℝ), IsPositiveTransverseEmbedding (2 * π) T →
  IsCircleReparam ρ → slCircle (T ∘ ρ) = slCircle T

/-- U2: the `xz` front of a Legendrian embedded circle with row 87's generic front is a front on
ng:front-domain (the printed argument sm-3:3455-3462: exact germs give the semicubical clauses,
`z′ = y x′` gives "no vertical tangency on regular arcs") -/
def U_legendrianFront : Prop := ∀ Lc : ℝ → E3, GenericFront.IsEmbeddedCircle Lc →
  GenericFront.IsLegendrian Lc → GenericFront.IsGenericFront Lc → ∃ F : SmoothFront, IsFrontOf F Lc

/-- U3: the same curve as a one-component spatial link in row 91's input class (heights distinct at
double points from embeddedness; the exact germ on an interval from continuity of `y′`) -/
def U_spatialOf : Prop := ∀ Lc : ℝ → E3, GenericFront.IsEmbeddedCircle Lc →
  GenericFront.IsLegendrian Lc → GenericFront.IsGenericFront Lc →
  ∃ sp : SpatialLink 1, (∀ (i : Fin 1) (t : ℝ), sp.T i t = toSpace (Lc (2 * π * t))) ∧ sp.CuspedProjection

/-- U4: every front on ng:front-domain has a polygonal reading — `S := (realize (oword F)).diagram`
with the record isomorphism of the sweep block (`U8R.recordIso`, `realizeRecordIso`) turned into a
`Marking` (the converse of `markingRecordIso`: successor determines the cyclic order) -/
def U_reading : Prop := ∀ F : SmoothFront, ∃ S : Diagram, Nonempty (F.Marking S)

/-- U5: a clean cusp smoothing of the spatial link is a clean-disc rounding of the front, and a
slope-rule marking of the front is a height-rule marking of the smoothing (`y = dz/dx` on a
Legendrian at the double points; `CleanCuspSmoothing.occEquiv`) -/
def U_transport : Prop := ∀ (Lc : ℝ → E3) (sp : SpatialLink 1) (F : SmoothFront)
    (G : Fin 1 → SmoothLoop) (S : Diagram),
  (∀ (i : Fin 1) (t : ℝ), sp.T i t = toSpace (Lc (2 * π * t))) → IsFrontOf F Lc →
  GenericFront.IsLegendrian Lc → sp.CleanCuspSmoothing G → F.Marking S →
  Nonempty (sp.HeightMarking G S) ∧ F.IsRounding S

/-- `U_package` from U2-U5 and the accepted row 89: the rounded curves are the end of ce:rounding's
family (`CuspRoundingFamily.endSmoothing`, accepted in SM/CeSmoothingRecord.lean) -/
theorem U_package_of (u2 : U_legendrianFront) (u3 : U_spatialOf) (u4 : U_reading)
    (u5 : U_transport) : U_package := by
  intro Lc h1 h2 h3
  obtain ⟨F, hF⟩ := u2 Lc h1 h2 h3
  obtain ⟨sp, hsp, hcusp⟩ := u3 Lc h1 h2 h3
  obtain ⟨W⟩ := ce_rounding.exists_family sp Nat.one_pos hcusp
  obtain ⟨S, ⟨m⟩⟩ := u4 F
  obtain ⟨hm, hr⟩ := u5 Lc sp F _ S hsp hF h2 W.toCuspRoundingFamily.endSmoothing m
  exact ⟨⟨sp, hsp, F, hF, hcusp, _, S, ⟨W.toCuspRoundingFamily.endSmoothing⟩, hm, hr⟩⟩

/-- The row theorem's shape once the units are proved: `theorem fd_contact : FdContactData :=
fd_contact_of_units u_circle u_sl_isotopy u_package u_family`. -/
example (h0 : U_circle) (h1 : U_sl_isotopy) (h3 : U_package) (h4 : U_family) :
    CV.AxEtnyreData ∧ CV.AxSlboundData :=
  ⟨CV.ax_etnyre_of (fd_contact_of_units h0 h1 h3 h4), CV.ax_slbound_of (fd_contact_of_units h0 h1 h3 h4)⟩

end

end SM

#print axioms SM.fd_contact_of_units
#print axioms SM.srcContact_iff_consequence
