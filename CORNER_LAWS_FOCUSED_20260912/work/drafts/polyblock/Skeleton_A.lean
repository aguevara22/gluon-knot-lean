import SM.Smoothing
import SM.CoefficientTransport
import SM.LocalPolynomial
import SM.SingleCrossing

/-! # Skeleton A — the (N, b) skein induction and its five consumer rows
(rp:record-polynomial, lp:core, lp:split-circle, lc:presentations, mp:stack)

Architect tag A, 2026-09-13.  Plan: work/drafts/polyblock/PLAN_A.md.  Every chain lemma is stated
with `sorry`; the induction principle `Diagram.skein_induction`, the solved recursions, the
assembly theorems of lp:core and the FIVE ROW THEOREMS (`record_polynomial`, `lp_core`,
`split_circle`, `presentations`, `stack`) are PROVED from the chain.  The five bundles are copied
verbatim from work/drafts/*_statement.lean.

Design in one paragraph.  The printed proofs all run the same lexicographic induction on
`(N, b)`: `N` = crossings, `b` = "bad" crossings (first encounter OVER) for a chosen basing.  In
Lean the measure is diagram-level: outer strong induction on `N := Fintype.card D.Γ.Crossing`,
inner induction on `b := D.badCount B` for ONE basing `B` chosen by `exists_basing` (any basing
works because the outer step re-chooses).  A switch at ANY bad crossing lowers `badCount` by one
for the SAME basing (`Basing.switch`: the shadow is unchanged), the smoothing lowers `N` by one
(gate `exists_smoothing_record`).  This gives the reusable principle `Diagram.skein_induction`,
whose step receives the switch, an oriented smoothing `D₀` AND the record isomorphism
`D₀.record ≅ D.record.smooth (overVisit x)`.  The two solved recursions are `solvedT` (in `T`) and
`solvedR`/`solvedRG` (in `R`/`R_G`).  The second diagram of rp:record-polynomial (and of the
split-circle / stack motives) is carried along inside the motive (`∀ D', RecordIso … → …`), so
only the INITIALIZATION needs the transported basing: `underFirst_of_recordIso` builds a basing
of `D'` from one of `D` by placing each basepoint just before the image of the first occurrence
(`exists_basing_before`, generalising `exists_basing_first`) and proves the based-order
correspondence through `RecordIso.visitBetween_iff` (`offset_lt_iff_of_isFirst`). -/

namespace SM

open SM.Link

/-! ## 1. Ring layer: the two solved skein recursions -/

namespace Link

open scoped Classical in
/-- lp:lm solved at the chosen crossing (rp:positive-recursion / rp:negative-recursion,
sm-3:1279-1280, 1291-1292): `F_D = −l⁻² F_{D^sw} − l⁻¹ m F_{D⁰}` at a positive crossing,
`F_D = −l² F_{D^sw} − l m F_{D⁰}` at a negative one.  `pos` is the positivity of the crossing. -/
noncomputable def solvedT (pos : Prop) (u w : T) : T :=
  if pos then -(T.lInv * T.lInv) * u - T.lInv * T.m * w else -(T.l * T.l) * u - T.l * T.m * w

open scoped Classical in
/-- lp:positive / lp:negative (sm-3:1104-1113) in `R`: `a⁻² P^sw + a⁻¹ z P⁰` / `a² P^sw − a z P⁰`. -/
noncomputable def solvedR (pos : Prop) (u w : R) : R :=
  if pos then R.aInv * R.aInv * u + R.aInv * R.z * w else R.a * R.a * u - R.a * R.z * w

open scoped Classical in
/-- The same recursion in the Gaussian ring `R_G`. -/
noncomputable def solvedRG (pos : Prop) (u w : RG) : RG :=
  if pos then RG.aInv * RG.aInv * u + RG.aInv * RG.z * w else RG.a * RG.a * u - RG.a * RG.z * w

/-- The recursion is `R`-linear in the two smaller values (lp:split-circle proof: "the coefficients
are scalar elements of the commutative ring R … factor it out"). -/
theorem solvedR_mul_left (pos : Prop) (c u w : R) :
    solvedR pos (c * u) (c * w) = c * solvedR pos u w := by
  unfold solvedR; split_ifs <;> ring

/-- `R ⊂ R_G` carries `solvedR` to `solvedRG`. -/
theorem toRG_solvedR (pos : Prop) (u w : R) :
    R.toRG (solvedR pos u w) = solvedRG pos (R.toRG u) (R.toRG w) := by
  unfold solvedR solvedRG
  split_ifs <;> simp [map_add, map_sub, map_mul]

/-- `i` as an element of `R_G`, with `i² = −1` (sm-3:1065-1066 "Start in `R_G = ℤ[i][a^{±1},z^{±1}]`
with `i² = −1`"). -/
theorem RG.iota_mul_iota :
    algebraMap GaussianInt RG gaussI * algebraMap GaussianInt RG gaussI = -1 := by
  rw [← map_mul, gaussI_mul_gaussI, map_neg, map_one]

/-- `φ(l) = i a` (lp:gaussian) written with `i` as a ring element. -/
theorem phi_l_eq : phi TG.l = algebraMap GaussianInt RG gaussI * RG.a := by
  rw [phi_l', Algebra.smul_def]

/-- `φ(m) = −i z`. -/
theorem phi_m_eq : phi TG.m = -(algebraMap GaussianInt RG gaussI * RG.z) := by
  rw [phi_m', Algebra.smul_def]

/-- `φ(l⁻¹) = (ia)⁻¹ = −i a⁻¹` (sm-3:1071-1072). -/
theorem phi_lInv_eq : phi TG.lInv = -(algebraMap GaussianInt RG gaussI * RG.aInv) := by
  rw [phi_lInv, RG.aInv, ← Algebra.smul_def, AddMonoidAlgebra.smul_single, smul_eq_mul, mul_one,
    AddMonoidAlgebra.single_neg]

/-- `φ(m⁻¹) = (−iz)⁻¹ = i z⁻¹`. -/
theorem phi_mInv_eq : phi TG.mInv = algebraMap GaussianInt RG gaussI * RG.zInv := by
  rw [phi_mInv, RG.zInv, ← Algebra.smul_def, AddMonoidAlgebra.smul_single, smul_eq_mul, mul_one]

/-- `φ ∘ (T ⊂ T_G)` carries the source recursion `solvedT` to the campaign recursion `solvedRG`
(lp:gaussian-skein → lp:positive/lp:negative, sm-3:1073-1113): `φ(l) = ia`, `φ(l⁻¹) = −ia⁻¹`,
`φ(m) = −iz`, so `−φ(l⁻¹)² = a⁻²`, `−φ(l⁻¹)φ(m) = a⁻¹z`, `−φ(l)² = a²`, `−φ(l)φ(m) = −az`. -/
theorem phi_toTG_solvedT (pos : Prop) (u w : T) :
    phi (T.toTG (solvedT pos u w)) = solvedRG pos (phi (T.toTG u)) (phi (T.toTG w)) := by
  have hI := RG.iota_mul_iota
  unfold solvedT solvedRG
  split_ifs
  · simp only [map_sub, map_mul, map_neg, T.toTG_lInv, T.toTG_m, phi_lInv_eq, phi_m_eq]
    linear_combination
      (-(RG.aInv * RG.aInv * phi (T.toTG u) + RG.aInv * RG.z * phi (T.toTG w))) * hI
  · simp only [map_sub, map_mul, map_neg, T.toTG_l, T.toTG_m, phi_l_eq, phi_m_eq]
    linear_combination (RG.a * RG.z * phi (T.toTG w) - RG.a * RG.a * phi (T.toTG u)) * hI

/-- `φ(μ) = δ` in `R_G` (lp:core proof sm-3:1078-1081: "the numerator `l+l⁻¹` maps to `i(a−a⁻¹)`
and the denominator `m` maps to `−iz`. Their quotient with its preceding minus sign is
`(a−a⁻¹)/z`"). -/
theorem phi_toTG_mu : phi (T.toTG T.mu) = R.toRG R.delta := by
  have hI := RG.iota_mul_iota
  have hsum : phi (TG.l + TG.lInv) = algebraMap GaussianInt RG gaussI * (RG.a - RG.aInv) := by
    rw [phi_l_add_lInv, Algebra.smul_def]
  rw [T.mu, map_mul, map_neg, map_add, T.toTG_l, T.toTG_lInv, T.toTG_mInv, map_mul, map_neg, hsum,
    phi_mInv_eq, R.delta, map_mul, map_sub, R.toRG_a, R.toRG_aInv, R.toRG_zInv]
  linear_combination (-(RG.a - RG.aInv) * RG.zInv) * hI

/-- lp:self-support / lp:mixed-support (sm-3:1119-1132): the recursion keeps the support class
`M_c` when the switched value lies in `M_c` and the smoothed value in `M_{c±1}`. -/
theorem InSupportM.solvedR {c c₀ : ℕ} (pos : Prop) {u w : R} (hu : InSupportM c u)
    (hw : InSupportM c₀ w) (h : c₀ = c + 1 ∨ c₀ + 1 = c) : InSupportM c (solvedR pos u w) := by
  have hzw : InSupportM c (R.z * w) := by
    rcases h with h | h
    · subst h; exact hw.z_mul
    · have hc : 1 ≤ c := by omega
      have hc' : c₀ = c - 1 := by omega
      subst hc'; exact InSupportM.z_mul_of_pred hc hw
  unfold SM.Link.solvedR
  split_ifs
  · simp only [mul_assoc]; exact (hu.aInv_mul.aInv_mul).add hzw.aInv_mul
  · simp only [mul_assoc]; exact (hu.a_mul.a_mul).sub hzw.a_mul

/-- lp:nonzero-positive / lp:nonzero-negative (sm-3:1150-1160): under `z ↦ a − a⁻¹` both
recursions send `(1, 1)` to `1`. -/
theorem specQ_solvedR (pos : Prop) {u w : R} (hu : specQ u = 1) (hw : specQ w = 1) :
    specQ (solvedR pos u w) = 1 := by
  unfold solvedR
  split_ifs
  · have h := specQ_positive_identity
    simp only [map_add, map_mul] at h
    simp only [map_add, map_mul, hu, hw, mul_one]
    exact h
  · have h := specQ_negative_identity
    simp only [map_sub, map_mul] at h
    simp only [map_sub, map_mul, hu, hw, mul_one]
    exact h

/-! ## 2. Diagram layer: bad crossings of a basing, the switch keeps the basing -/

namespace Diagram

variable (D : Diagram)

/-- The same basing on the switched diagram (the shadow is unchanged: "A switch at the first bad
crossing keeps the parameter circles and their traversal order", sm-3:1085-1086). -/
def Basing.switch {D : Diagram} (B : D.Basing) (x : D.Γ.Crossing) : (D.switch x).Basing :=
  ⟨B.rank, B.base, B.nonsingular⟩

theorem basedRank_switch (B : D.Basing) (x : D.Γ.Crossing) (v : D.Γ.Visit) :
    (D.switch x).basedRank (B.switch x) v = D.basedRank B v := rfl

/-- A *bad* crossing of a based diagram: its first encounter is the OVER occurrence
(sm-3:1083-1084 "let b(D) count first encounters which are OVER"; rp sm-3:1237-1238). -/
def Bad (B : D.Basing) (x : D.Γ.Crossing) : Prop :=
  Prod.Lex (· < ·) (· < ·) (D.basedRank B (D.overVisit x)) (D.basedRank B (D.underVisit x))

open scoped Classical in
/-- `b(D)`, the number of bad crossings. -/
noncomputable def badCount (B : D.Basing) : ℕ := (Finset.univ.filter (fun x => D.Bad B x)).card

/-- Distinct occurrences have distinct based ranks (rank is injective; on one component the offset
from the basepoint is injective in the traversal coordinate). -/
theorem basedRank_injective (B : D.Basing) : Function.Injective (D.basedRank B) := by
  intro v w h
  rcases hpv : D.visitPt v with ⟨i, pv⟩
  rcases hpw : D.visitPt w with ⟨j, pw⟩
  simp only [basedRank] at h
  rw [hpv, hpw] at h
  dsimp only at h
  rw [Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  have hij : i = j := B.rank.injective (Fin.ext h1)
  subst hij
  have hk : traversalKey pv = traversalKey pw := by
    have ha0 := traversalKey_nonneg (B.base i)
    have hak := traversalKey_lt_card (B.base i)
    have hx0 := traversalKey_nonneg pv
    have hxk := traversalKey_lt_card pv
    have hy0 := traversalKey_nonneg pw
    have hyk := traversalKey_lt_card pw
    unfold cyclicOffset at h2
    split_ifs at h2 <;> linarith
  apply D.visitPt_injective
  rw [hpv, hpw, traversalKey_injective hk]

/-- Exactly one of the two encounters is first: not bad ↔ UNDER first at this crossing. -/
theorem not_bad_iff (B : D.Basing) (x : D.Γ.Crossing) :
    ¬ D.Bad B x ↔
      Prod.Lex (· < ·) (· < ·) (D.basedRank B (D.underVisit x)) (D.basedRank B (D.overVisit x)) := by
  have hne : D.basedRank B (D.underVisit x) ≠ D.basedRank B (D.overVisit x) :=
    fun h => D.overVisit_ne_underVisit x (D.basedRank_injective B h).symm
  unfold Bad
  rw [Prod.lex_def, Prod.lex_def]
  rcases hu : D.basedRank B (D.underVisit x) with ⟨ru, ou⟩
  rcases ho : D.basedRank B (D.overVisit x) with ⟨ro, oo⟩
  rw [hu, ho] at hne
  simp only [ne_eq, Prod.mk.injEq, not_and] at hne
  constructor
  · intro h
    rcases lt_trichotomy ru ro with h1 | h1 | h1
    · exact Or.inl h1
    · subst h1
      right
      refine ⟨rfl, ?_⟩
      have h2 : ¬ oo < ou := fun h' => h (Or.inr ⟨rfl, h'⟩)
      have h3 : ou ≠ oo := fun h' => hne rfl h'
      exact lt_of_le_of_ne (not_lt.mp h2) h3
    · exact absurd (Or.inl h1) h
  · rintro (h1 | ⟨h1, h2⟩) (h3 | ⟨h3, h4⟩)
    · exact lt_asymm h1 h3
    · exact absurd h3 (ne_of_gt h1)
    · exact absurd h1 (ne_of_gt h3)
    · exact lt_asymm h2 h4

open scoped Classical in
/-- "The initialization is exactly `b = 0`" (sm-3:1084-1085). -/
theorem underFirst_iff_badCount_eq_zero (B : D.Basing) : D.UnderFirst B ↔ D.badCount B = 0 := by
  unfold badCount UnderFirst
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  simp only [Finset.mem_univ, true_implies]
  exact forall_congr' fun x => (D.not_bad_iff B x).symm

open scoped Classical in
theorem exists_bad_of_badCount_pos (B : D.Basing) (h : 0 < D.badCount B) : ∃ x, D.Bad B x := by
  unfold badCount at h
  obtain ⟨x, hx⟩ := Finset.card_pos.mp h
  exact ⟨x, (Finset.mem_filter.mp hx).2⟩

/-- The switch flips badness at the switched crossing and nowhere else (same basing, same
ranks; `switch_overVisit_self`, `switch_underVisit_self`, `switch_overVisit_of_ne`). -/
theorem bad_switch_iff (B : D.Basing) (x y : D.Γ.Crossing) :
    (D.switch x).Bad (B.switch x) y ↔ (if y = x then ¬ D.Bad B x else D.Bad B y) := by
  unfold Bad
  split_ifs with hyx
  · subst hyx
    rw [D.switch_overVisit_self y, D.switch_underVisit_self y]
    exact (D.not_bad_iff B y).symm
  · rw [D.switch_overVisit_of_ne x hyx, D.switch_underVisit_of_ne x hyx]
    exact Iff.rfl

open scoped Classical in
/-- "Thus `D^sw` has complexity `(N, b − 1)`" (sm-3:1088). -/
theorem badCount_switch_of_bad (B : D.Basing) {x : D.Γ.Crossing} (hx : D.Bad B x) :
    (D.switch x).badCount (B.switch x) + 1 = D.badCount B := by
  have hset : (Finset.univ.filter (fun y : D.Γ.Crossing => (D.switch x).Bad (B.switch x) y)) =
      (Finset.univ.filter (fun y : D.Γ.Crossing => D.Bad B y)).erase x := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, D.bad_switch_iff B x y]
    split_ifs with hyx
    · subst hyx; simp [hx]
    · simp [hyx]
  show (Finset.univ.filter (fun y : D.Γ.Crossing => (D.switch x).Bad (B.switch x) y)).card + 1 =
    (Finset.univ.filter (fun y : D.Γ.Crossing => D.Bad B y)).card
  rw [hset, Finset.card_erase_add_one (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩)]

/-! ## 3. The (N, b) induction principle -/

/-- **The lexicographic `(N, b)` induction of lp:core / rp:record-polynomial** (sm-3:1083-1103,
1237-1243), diagram-level: to prove `motive D` for every diagram it suffices to prove it for every
UNDER-first based diagram and to propagate it from the switch and from ONE oriented smoothing
(with its record) at any single crossing.  Proof: strong induction on `N`, inner induction on
`badCount B` for a basing `B` of `D` (any basing; the outer step re-chooses). -/
theorem skein_induction (motive : Diagram → Prop)
    (init : ∀ (D : Diagram) (B : D.Basing), D.UnderFirst B → motive D)
    (step : ∀ (D : Diagram) (x : D.Γ.Crossing) (D₀ : Diagram), IsOrientedSmoothing D x D₀ →
      Nonempty (RecordIso D₀.record (D.record.smooth (D.overVisit x))) →
      motive (D.switch x) → motive D₀ → motive D) :
    ∀ D, motive D := by
  have key : ∀ N : ℕ, ∀ D : Diagram, Fintype.card D.Γ.Crossing = N → motive D := by
    intro N
    induction N using Nat.strong_induction_on with
    | _ N ihN =>
      have inner : ∀ b : ℕ, ∀ (D : Diagram) (B : D.Basing), Fintype.card D.Γ.Crossing = N →
          D.badCount B = b → motive D := by
        intro b
        induction b with
        | zero =>
          intro D B hN hb
          exact init D B ((D.underFirst_iff_badCount_eq_zero B).mpr hb)
        | succ b ihb =>
          intro D B hN hb
          obtain ⟨x, hx⟩ := D.exists_bad_of_badCount_pos B (by omega)
          obtain ⟨D₀, h₀, hι⟩ := exists_smoothing_record D x
          refine step D x D₀ h₀ hι ?_ ?_
          · refine ihb (D.switch x) (B.switch x) hN ?_
            have := D.badCount_switch_of_bad B hx
            omega
          · have hc := h₀.card_crossing
            exact ihN (Fintype.card D₀.Γ.Crossing) (by omega) D₀ rfl
      intro D hN
      obtain ⟨B⟩ := D.exists_basing
      exact inner _ D B hN rfl
  intro D
  exact key _ D rfl

end Diagram

end Link

/-! ## 4. The solved skein for functions on diagrams -/

/-- Any function with the source skein satisfies the solved recursion at every crossing, for
every oriented smoothing there.  At a negative crossing the triple is `(D^sw, D, D⁰)`
(`switch_isPositive_self`, `switch_switch`, `IsOrientedSmoothing.switch`). -/
theorem solvedT_of_skein (F : Diagram → T)
    (hF : ∀ Dp Dm D0 : Diagram, IsSkeinTriple Dp Dm D0 →
      T.l * F Dp + T.lInv * F Dm + T.m * F D0 = 0)
    (D : Diagram) (x : D.Γ.Crossing) (D₀ : Diagram) (h : IsOrientedSmoothing D x D₀) :
    F D = solvedT (D.IsPositive x) (F (D.switch x)) (F D₀) := by
  unfold solvedT
  split_ifs with hp
  · have hsk := hF D (D.switch x) D₀ ⟨x, hp, rfl, h⟩
    linear_combination T.lInv * hsk - F D * T.lInv_mul_l
  · have hp' : (D.switch x).IsPositive x := (D.switch_isPositive_self x).mpr hp
    have hsk := hF (D.switch x) D D₀ ⟨x, hp', (D.switch_switch x).symm, h.switch⟩
    linear_combination T.l * hsk - F D * T.l_mul_lInv

/-- The same for the campaign skein in `R`. -/
theorem solvedR_of_skein (Q : Diagram → R)
    (hQ : ∀ Dp Dm D0 : Diagram, IsSkeinTriple Dp Dm D0 →
      R.a * Q Dp - R.aInv * Q Dm = R.z * Q D0)
    (D : Diagram) (x : D.Γ.Crossing) (D₀ : Diagram) (h : IsOrientedSmoothing D x D₀) :
    Q D = solvedR (D.IsPositive x) (Q (D.switch x)) (Q D₀) := by
  unfold solvedR
  split_ifs with hp
  · have hsk := hQ D (D.switch x) D₀ ⟨x, hp, rfl, h⟩
    linear_combination R.aInv * hsk - Q D * R.aInv_mul_a
  · have hp' : (D.switch x).IsPositive x := (D.switch_isPositive_self x).mpr hp
    have hsk := hQ (D.switch x) D D₀ ⟨x, hp', (D.switch_switch x).symm, h.switch⟩
    linear_combination -R.a * hsk - Q D * R.a_mul_aInv

/-- rp:positive-recursion / rp:negative-recursion for the source function. -/
theorem lmF_solved (D : Diagram) (x : D.Γ.Crossing) (D₀ : Diagram) (h : IsOrientedSmoothing D x D₀) :
    lmF D = solvedT (D.IsPositive x) (lmF (D.switch x)) (lmF D₀) :=
  solvedT_of_skein lmF (fun _ _ _ h => lmF_sourceSkein h) D x D₀ h

/-! ## 5. lp:core — the Gaussian evaluation `G = φ(F)`, descent, uniqueness, nonvanishing -/

/-- `P_D^G = φ(F_D)` (eq. lp:gaussian). -/
noncomputable def G (D : Diagram) : RG := phi (T.toTG (lmF D))

theorem P_eq_reMap_G (D : Diagram) : P D = reMap (G D) := rfl

/-- lp:positive / lp:negative for `P^G`. -/
theorem G_solved (D : Diagram) (x : D.Γ.Crossing) (D₀ : Diagram) (h : IsOrientedSmoothing D x D₀) :
    G D = solvedRG (D.IsPositive x) (G (D.switch x)) (G D₀) := by
  unfold G
  rw [lmF_solved D x D₀ h, phi_toTG_solvedT]

/-- "Thus `P_D^G = δ^{c−1}` for every UNDER-first diagram" (sm-3:1081). -/
theorem G_underFirst (D : Diagram) (B : D.Basing) (h : D.UnderFirst B) :
    G D = R.toRG (R.delta ^ (D.componentCount - 1)) := by
  unfold G
  rw [lmF_underFirst_init B h, map_pow, map_pow, map_pow, phi_toTG_mu]

/-- The initialization of `P` needs no descent: `P = re φ(F)` and `φ(μ^{c−1}) = δ^{c−1}` is real. -/
theorem P_underFirst (D : Diagram) (B : D.Basing) (h : D.UnderFirst B) :
    P D = R.delta ^ (D.componentCount - 1) := by
  rw [P_eq_reMap_G, G_underFirst D B h, reMap_toRG]

/-- The component count of a smoothing with the record bridge: `c + 1` (self) or `c − 1` (mixed,
`c ≥ 2`) — sm-3:1089-1101. -/
theorem componentCount_of_smoothing_iso {D D₀ : Diagram} {v : D.Γ.Visit}
    (ι : RecordIso D₀.record (D.record.smooth v)) :
    D₀.componentCount = D.componentCount + 1 ∨ D₀.componentCount + 1 = D.componentCount := by
  have h := ι.componentCount_eq
  rw [D₀.record_componentCount, D.record.componentCount_smooth, D.record_componentCount] at h
  split_ifs at h with hs
  · exact Or.inl h
  · right
    have := D.record.two_le_componentCount_of_mixed v hs
    rw [D.record_componentCount] at this
    omega

/-- The skein in `R_G` (lp:gaussian-skein, sm-3:1073-1077): apply `φ ∘ (T ⊂ T_G)` to the source
skein and multiply by `−i`. -/
theorem G_skein {Dp Dm D0 : Diagram} (h : IsSkeinTriple Dp Dm D0) :
    RG.a * G Dp - RG.aInv * G Dm = RG.z * G D0 := by
  have hI := RG.iota_mul_iota
  have h1 := congrArg (fun t => phi (T.toTG t)) (lmF_sourceSkein h)
  simp only [map_add, map_mul, map_zero, T.toTG_l, T.toTG_lInv, T.toTG_m, phi_l_eq, phi_m_eq,
    phi_lInv_eq] at h1
  unfold G
  linear_combination (-(algebraMap GaussianInt RG gaussI)) * h1 +
    (RG.a * phi (T.toTG (lmF Dp)) - RG.aInv * phi (T.toTG (lmF Dm)) -
      RG.z * phi (T.toTG (lmF D0))) * hI

/-- **Integral descent** (sm-3:1119-1137), by the `(N, b)` induction: `P_D^G` is the image of an
element of `M_c = z^{1−c} ℤ[a^{±1}, z²]`. -/
theorem G_descent : ∀ D : Diagram, ∃ p : R, InSupportM D.componentCount p ∧ R.toRG p = G D := by
  refine Diagram.skein_induction _ ?_ ?_
  · intro D B hB
    refine ⟨R.delta ^ (D.componentCount - 1), ?_, (G_underFirst D B hB).symm⟩
    have h := InSupportM.delta_pow (D.componentCount - 1)
    rwa [Nat.sub_add_cancel D.componentCount_pos] at h
  · intro D x D₀ h₀ ⟨ι₀⟩ ⟨psw, hsw, hpsw⟩ ⟨p0, h0, hp0⟩
    refine ⟨solvedR (D.IsPositive x) psw p0, ?_, ?_⟩
    · exact InSupportM.solvedR _ hsw h0 (componentCount_of_smoothing_iso ι₀)
    · rw [toRG_solvedR, hpsw, hp0, G_solved D x D₀ h₀]

/-- lp:core `gaussian`: `P_D` is the element of `R` with image `φ(F_D)`. -/
theorem toRG_P (D : Diagram) : R.toRG (P D) = G D := by
  obtain ⟨p, -, hp⟩ := G_descent D
  have : P D = p := by rw [P_eq_reMap_G, ← hp, reMap_toRG]
  rw [this, hp]

/-- lp:support, first half. -/
theorem P_inSupportM (D : Diagram) : InSupportM D.componentCount (P D) := by
  obtain ⟨p, hs, hp⟩ := G_descent D
  have : P D = p := by rw [P_eq_reMap_G, ← hp, reMap_toRG]
  rwa [this]

/-- lp:skein in `R`, by injectivity of `R ⊂ R_G`. -/
theorem P_skein {Dp Dm D0 : Diagram} (h : IsSkeinTriple Dp Dm D0) :
    R.a * P Dp - R.aInv * P Dm = R.z * P D0 := by
  apply R.toRG_injective
  rw [map_sub, map_mul, map_mul, map_mul, R.toRG_a, R.toRG_aInv, R.toRG_z, toRG_P, toRG_P, toRG_P]
  exact G_skein h

/-- **Uniqueness** (sm-3:1139-1144) by the same induction. -/
theorem P_unique (Q : Diagram → R)
    (hsk : ∀ Dp Dm D0 : Diagram, IsSkeinTriple Dp Dm D0 → R.a * Q Dp - R.aInv * Q Dm = R.z * Q D0)
    (hinit : ∀ (D : Diagram) (B : D.Basing), D.UnderFirst B → Q D = R.delta ^ (D.componentCount - 1)) :
    Q = P := by
  funext D
  refine Diagram.skein_induction (fun D => Q D = P D) ?_ ?_ D
  · intro D B hB
    rw [hinit D B hB, P_underFirst D B hB]
  · intro D x D₀ h₀ _ ihsw ih₀
    rw [solvedR_of_skein Q hsk D x D₀ h₀, solvedR_of_skein P (fun _ _ _ h => P_skein h) D x D₀ h₀,
      ihsw, ih₀]

/-- **Nonvanishing** (sm-3:1145-1161): every diagram specializes to `1` under `z ↦ a − a⁻¹`. -/
theorem specQ_P : ∀ D : Diagram, specQ (P D) = 1 := by
  refine Diagram.skein_induction (fun D => specQ (P D) = 1) ?_ ?_
  · intro D B hB
    rw [P_underFirst D B hB, map_pow, specQ_delta, one_pow]
  · intro D x D₀ h₀ _ ihsw ih₀
    rw [solvedR_of_skein P (fun _ _ _ h => P_skein h) D x D₀ h₀]
    exact specQ_solvedR _ ihsw ih₀

theorem P_ne_zero (D : Diagram) : P D ≠ 0 := fun h => by
  have := specQ_P D
  rw [h, map_zero] at this
  exact zero_ne_one this

/-- `P` satisfies the hypotheses of lp:coefficient-transport (sm-3:1163-1168 "for P these
properties were proved above from Literature input lp:lm"). -/
theorem P_rcompetitor : RCompetitor P where
  planar D D' h := by unfold P; rw [lmF_planar h]
  reidemeister_I D D' h := by unfold P; rw [lmF_reidemeister_I h]
  reidemeister_II D D' h := by unfold P; rw [lmF_reidemeister_II h]
  reidemeister_III D D' h := by unfold P; rw [lmF_reidemeister_III h]
  circle D h := P_eq_one_of_lmF_eq_one (lmF_unknot h)
  skein _ _ _ h := P_skein h

/-- `H` satisfies them too ("the existence and invariance clauses of Literature input lit:homfly"). -/
theorem homfly_rcompetitor : RCompetitor homfly where
  planar _ _ h := homfly_planar h
  reidemeister_I _ _ h := homfly_reidemeister_I h
  reidemeister_II _ _ h := homfly_reidemeister_II h
  reidemeister_III _ _ h := homfly_reidemeister_III h
  circle _ h := homfly_circle h
  skein _ _ _ h := homfly_skein h

/-- "Lemma lp:coefficient-transport identifies two such maps, so `P_D = H_D`" (sm-3:1169-1170). -/
theorem P_eq_homfly (D : Diagram) : P D = homfly D :=
  congrFun (coefficient_transport P homfly P_rcompetitor homfly_rcompetitor) D

/-! ## 6. Transport of UNDER-first through a named record isomorphism
(rp:record-polynomial proof, sm-3:1230-1236: "Transfer the order to `D'`. On a component with
crossings, choose its new basepoint in the interval just preceding the image of the old first
crossing occurrence … These choices make the complete traversal orders of crossing occurrences
correspond.") -/

namespace Link.Diagram

variable (D : Diagram)

/-- `v` is the first occurrence met on its component from the basepoint of `B`. -/
def IsFirst (B : D.Basing) (v : D.Γ.Visit) : Prop :=
  ∀ w : D.Γ.Visit, D.compOf w = D.compOf v → w ≠ v → (D.basedRank B v).2 < (D.basedRank B w).2

/-- Every component carrying an occurrence has a first one (`Finset.exists_min_image` on
`compVisits`, strictness from `basedRank_injective`). -/
theorem exists_isFirst (B : D.Basing) (i : Fin D.Γ.c) (h : ∃ v : D.Γ.Visit, D.compOf v = i) :
    ∃ v : D.Γ.Visit, D.compOf v = i ∧ D.IsFirst B v := by
  sorry

theorem IsFirst.unique (B : D.Basing) {v w : D.Γ.Visit} (hv : D.IsFirst B v) (hw : D.IsFirst B w)
    (h : D.compOf w = D.compOf v) : w = v := by
  sorry

/-- The body of `exists_basing_first` (SingleCrossing), per component: a nonsingular point on
component `i` immediately before the occurrence `v` (via `exists_param_before`). -/
theorem exists_base_before (i : Fin D.Γ.c) (v : D.Γ.Visit) (hv : D.compOf v = i) :
    ∃ b : TraversalPoint (D.Γ.comp i).k, (∀ x, D.Γ.eval ⟨i, b⟩ ≠ D.Γ.crossingPoint x) ∧
      ∀ w : D.Γ.Visit, D.compOf w = i → w ≠ v →
        cyclicOffset (D.Γ.comp i).k (traversalKey b) (D.visitCoord v) <
          cyclicOffset (D.Γ.comp i).k (traversalKey b) (D.visitCoord w) := by
  sorry

/-- A basing with a prescribed component order whose basepoints lie immediately before the
designated occurrences (generalises `exists_basing_first` to all components at once). -/
theorem exists_basing_before (rank : Fin D.Γ.c ≃ Fin D.Γ.c)
    (f : ∀ i : Fin D.Γ.c, Option {v : D.Γ.Visit // D.compOf v = i}) :
    ∃ B : D.Basing, B.rank = rank ∧ ∀ i v, f i = some v → D.IsFirst B v.1 := by
  sorry

/-- Rotating the circle `[0, k)` by `x ↦ cyclicOffset k a x` preserves oriented cyclic order. -/
theorem cycBetween_cyclicOffset {k : ℕ} {a x y z : ℝ} (ha0 : 0 ≤ a) (hak : a < k)
    (hx0 : 0 ≤ x) (hxk : x < k) (hy0 : 0 ≤ y) (hyk : y < k) (hz0 : 0 ≤ z) (hzk : z < k) :
    cycBetween (cyclicOffset k a x) (cyclicOffset k a y) (cyclicOffset k a z) ↔ cycBetween x y z := by
  sorry

/-- **Based order versus cyclic order.** From a basepoint placed so that `v₁` is the first
occurrence on its component, the based order of two occurrences `u, o` of that component is their
oriented cyclic order seen from `v₁`. -/
theorem offset_lt_iff_of_isFirst (B : D.Basing) {v₁ u o : D.Γ.Visit} (h₁ : D.IsFirst B v₁)
    (hu : D.compOf u = D.compOf v₁) (ho : D.compOf o = D.compOf v₁) (huo : u ≠ o) :
    (D.basedRank B u).2 < (D.basedRank B o).2 ↔ (u = v₁ ∨ (o ≠ v₁ ∧ D.VisitBetween v₁ u o)) := by
  sorry

end Link.Diagram

/-- Signs are part of the record: the image crossing has the same sign (`RecordIso.sgn_eq`). -/
theorem isPositive_iff_of_recordIso {D D' : Diagram} (ι : RecordIso D.record D'.record)
    (v : D.Γ.Visit) : D'.IsPositive (ι.Φ v).1 ↔ D.IsPositive v.1 := by
  rw [D'.isPositive_iff_sign_eq_one, D.isPositive_iff_sign_eq_one,
    show D'.sign (ι.Φ v).1 = D.sign v.1 from ι.sgn_eq v]

/-- **UNDER-first transports along a named record isomorphism** when the ranks correspond and the
first occurrences correspond: the two encounters of the image crossing are the images of the two
encounters (`pair_eq`, `bit_eq`), rank comparison is `hrank`, and on one component the offset
comparison is `offset_lt_iff_of_isFirst` on both sides joined by `RecordIso.visitBetween_iff`. -/
theorem underFirst_of_recordIso_of_isFirst {D D' : Diagram} (ι : RecordIso D.record D'.record)
    (B : D.Basing) (B' : D'.Basing)
    (hrank : ∀ i k : Fin D.Γ.c, B'.rank (ι.e i) < B'.rank (ι.e k) ↔ B.rank i < B.rank k)
    (hfirst : ∀ v : D.Γ.Visit, D.IsFirst B v → D'.IsFirst B' (ι.Φ v))
    (h : D.UnderFirst B) : D'.UnderFirst B' := by
  sorry

/-- The transported basing exists: rank `ι.e.symm ≫ B.rank ≫ finCongr`, basepoints just before the
images of the first occurrences (`exists_isFirst`, `exists_basing_before`). -/
theorem underFirst_of_recordIso {D D' : Diagram} (ι : RecordIso D.record D'.record) (B : D.Basing)
    (h : D.UnderFirst B) : ∃ B' : D'.Basing, D'.UnderFirst B' := by
  sorry

/-! ## 7. rp:record-polynomial -/

/-- The switch bridge on both sides (`switchRecordIso`, `RecordIso.switch`): the switches at
corresponding crossings have isomorphic records (sm-3:1247-1250). -/
theorem switch_recordIso_transport {D D' : Diagram} (ι : RecordIso D.record D'.record)
    (x : D.Γ.Crossing) :
    Nonempty (RecordIso (D.switch x).record (D'.switch (ι.Φ (D.overVisit x)).1).record) :=
  ⟨(D.switchRecordIso x (D.overVisit x) rfl).trans
    ((ι.switch (D.overVisit x)).trans (D'.switchRecordIso _ (ι.Φ (D.overVisit x)) rfl).symm)⟩

/-- The smoothing bridge on both sides (gate `exists_smoothing_record_visit`, `RecordIso.smooth`):
some oriented smoothing of `D'` at the image crossing has record isomorphic to that of `D₀`
(sm-3:1252-1268). -/
theorem exists_smoothing_recordIso_transport {D D' : Diagram} (ι : RecordIso D.record D'.record)
    (x : D.Γ.Crossing) (D₀ : Diagram) (ι₀ : RecordIso D₀.record (D.record.smooth (D.overVisit x))) :
    ∃ D'₀ : Diagram, IsOrientedSmoothing D' (ι.Φ (D.overVisit x)).1 D'₀ ∧
      Nonempty (RecordIso D₀.record D'₀.record) := by
  obtain ⟨D'₀, h, ⟨ι'⟩⟩ :=
    exists_smoothing_record_visit D' (ι.Φ (D.overVisit x)).1 (ι.Φ (D.overVisit x)) rfl
  exact ⟨D'₀, h, ⟨ι₀.trans ((ι.smooth (D.overVisit x)).trans ι'.symm)⟩⟩

/-- **rp:record-polynomial, main clause** by `skein_induction` with the second diagram inside the
motive: initialization by `underFirst_of_recordIso`, step by the two bridges and `lmF_solved`
on both sides with the same sign (`isPositive_iff_of_recordIso`). -/
theorem lmF_eq_of_recordIso : ∀ D D' : Diagram, Nonempty (RecordIso D.record D'.record) →
    lmF D = lmF D' := by
  refine Diagram.skein_induction
    (fun D => ∀ D' : Diagram, Nonempty (RecordIso D.record D'.record) → lmF D = lmF D') ?_ ?_
  · intro D B hB D' ⟨ι⟩
    obtain ⟨B', hB'⟩ := underFirst_of_recordIso ι B hB
    rw [lmF_underFirst_init B hB, lmF_underFirst_init B' hB', ← D.record_componentCount,
      ← D'.record_componentCount, ι.componentCount_eq]
  · intro D x D₀ h₀ ⟨ι₀⟩ ihsw ih₀ D' ⟨ι⟩
    obtain ⟨ιsw⟩ := switch_recordIso_transport ι x
    obtain ⟨D'₀, h'₀, ⟨ι'₀⟩⟩ := exists_smoothing_recordIso_transport ι x D₀ ι₀
    rw [lmF_solved D x D₀ h₀, lmF_solved D' _ D'₀ h'₀, ihsw _ ⟨ιsw⟩, ih₀ _ ⟨ι'₀⟩,
      isPositive_iff_of_recordIso ι (D.overVisit x)]
    rfl

/-- rp:record-polynomial as printed (bundle copied verbatim from
work/drafts/RecordPolynomial_statement.lean). -/
structure RecordPolynomialData : Prop where
  /-- "Then `F_D(l, m) = F_{D'}(l, m)`." -/
  lmF_eq : ∀ D D' : Diagram, Nonempty (RecordIso D.record D'.record) → lmF D = lmF D'
  /-- "Consequently any common Laurent-ring substitution of these two source values ... agrees" -/
  subst_eq : ∀ D D' : Diagram, Nonempty (RecordIso D.record D'.record) →
    ∀ {A : Type} [CommRing A] (σ : T →+* A), σ (lmF D) = σ (lmF D')
  /-- in particular the Gaussian evaluation `P` agrees -/
  P_eq : ∀ D D' : Diagram, Nonempty (RecordIso D.record D'.record) → P D = P D'
  /-- "and every coefficient of the substituted values, agrees." -/
  coeff_eq : ∀ D D' : Diagram, Nonempty (RecordIso D.record D'.record) →
    ∀ d k : ℤ, coeffAt d k (P D) = coeffAt d k (P D')

theorem record_polynomial : RecordPolynomialData where
  lmF_eq := lmF_eq_of_recordIso
  subst_eq := by
    intro D D' h A _ σ
    rw [lmF_eq_of_recordIso D D' h]
  P_eq D D' h := by unfold P; rw [lmF_eq_of_recordIso D D' h]
  coeff_eq D D' h d k := by unfold P; rw [lmF_eq_of_recordIso D D' h]

/-! ## 8. lc:presentations -/

/-- lc:presentations as printed: "Their evaluations by the same local LM construction agree." -/
theorem presentations (D D' : Diagram) (h : Nonempty (RecordIso D.record D'.record)) : P D = P D' :=
  record_polynomial.P_eq D D' h

/-! ## 9. lp:core -/

/-- lp:core as printed, one field per printed sentence (bundle copied verbatim from
work/drafts/LpCore_statement.lean). -/
structure LpCoreData : Prop where
  /-- "The same source construction has an evaluation `P_D ∈ R`" (eq. lp:gaussian): `P_D` is the element
  of `R` whose image in `R_G` is the Gaussian evaluation `φ(F_D)` of the source value (integral descent). -/
  gaussian : ∀ D : Diagram, R.toRG (P D) = phi (T.toTG (lmF D))
  /-- eq. lp:skein: `a P_{D₊} − a⁻¹ P_{D₋} = z P_{D₀}` on every skein triple. -/
  skein : ∀ Dp Dm D0 : Diagram, IsSkeinTriple Dp Dm D0 → R.a * P Dp - R.aInv * P Dm = R.z * P D0
  /-- "Its value on every UNDER-first `c`-component diagram is `δ^{c−1}`", `δ = (a − a⁻¹) z⁻¹`. -/
  underFirst_init : ∀ (D : Diagram) (B : D.Basing), D.UnderFirst B → P D = R.delta ^ (D.componentCount - 1)
  /-- "It equals `H_D` of Literature input lit:homfly." -/
  eq_homfly : ∀ D : Diagram, P D = homfly D
  /-- "It is also the unique function on this exact diagram domain satisfying this skein and all these
  initialization values." (The uniqueness hypothesis includes the initialization values explicitly.) -/
  unique : ∀ Q : Diagram → R,
    (∀ Dp Dm D0 : Diagram, IsSkeinTriple Dp Dm D0 → R.a * Q Dp - R.aInv * Q Dm = R.z * Q D0) →
    (∀ (D : Diagram) (B : D.Basing), D.UnderFirst B → Q D = R.delta ^ (D.componentCount - 1)) →
    Q = P
  /-- eq. lp:support: "For every `c`-component diagram, `P_D ∈ z^{1−c} ℤ[a^{±1}, z²]`". -/
  support : ∀ D : Diagram, InSupportM D.componentCount (P D)
  /-- eq. lp:support: "`P_D ≠ 0`". -/
  ne_zero : ∀ D : Diagram, P D ≠ 0
  /-- "In particular `P_○ = 1`". -/
  circle : ∀ D : Diagram, D.IsCrossingFreeCircle → P D = 1
  /-- "and knot evaluations are polynomials in `z²`, with no negative `z` exponents": on a one-component
  diagram every monomial `a^d z^k` present has `k = 2j` for some `j : ℕ`. -/
  knot_support : ∀ D : Diagram, D.componentCount = 1 →
    ∀ d k : ℤ, coeffAt d k (P D) ≠ 0 → ∃ j : ℕ, k = 2 * (j : ℤ)
  /-- "All local invariances in Literature input lp:lm are retained": planar isotopy and the three
  Reidemeister moves. -/
  planar : ∀ D D' : Diagram, PlanarIsotopic D D' → P D = P D'
  reidemeister_I : ∀ D D' : Diagram, RI D D' → P D = P D'
  reidemeister_II : ∀ D D' : Diagram, RII D D' → P D = P D'
  reidemeister_III : ∀ D D' : Diagram, RIII D D' → P D = P D'

theorem lp_core : LpCoreData where
  gaussian := toRG_P
  skein _ _ _ h := P_skein h
  underFirst_init := P_underFirst
  eq_homfly := P_eq_homfly
  unique := P_unique
  support := P_inSupportM
  ne_zero := P_ne_zero
  circle _ h := P_eq_one_of_lmF_eq_one (lmF_unknot h)
  knot_support D hc d k hne := by
    have hs := P_inSupportM D
    rw [hc, inSupportM_iff] at hs
    by_contra hk
    apply hne
    apply hs d k
    rintro ⟨j, hj⟩
    exact hk ⟨j, by rw [hj]; push_cast; ring⟩
  planar := P_rcompetitor.planar
  reidemeister_I := P_rcompetitor.reidemeister_I
  reidemeister_II := P_rcompetitor.reidemeister_II
  reidemeister_III := P_rcompetitor.reidemeister_III

/-! ## 10. lp:split-circle

Reformulated through records (the printed "the switched pair and the smoothed pair are again related
by adding exactly that crossing-free component" is a record statement): for every diagram `E` with
a crossing-free component `j` and every `D'` whose record is that of `E` restricted to the other
components, `P E = δ P D'`.  The printed hypothesis `IsSplitCircleAddition D D'` gives exactly this
with `E := D'`, `D` planar-isotopic (a reparametrisation) to the restriction. -/

namespace Link.Record

variable (ρ : Record)

/-- On a record with a crossing-free circle `j` every occurrence is internal to the other circles. -/
theorem restrictKeep_of_free [DecidableEq ρ.comps] {j : ρ.comps} (hj : ∀ u, ρ.comp u ≠ j) (u : ρ.M) :
    ρ.RestrictKeep (Finset.univ.erase j) u :=
  ⟨Finset.mem_erase.mpr ⟨hj u, Finset.mem_univ _⟩, Finset.mem_erase.mpr ⟨hj _, Finset.mem_univ _⟩⟩

/-- Switching an internal crossing commutes with the block restriction at the record level
(identity on circles and occurrences; the bits and signs agree pointwise). -/
theorem restrictSwitchIso (B : Finset ρ.comps) (v : ρ.M) (hv : ρ.RestrictKeep B v) :
    Nonempty (RecordIso ((ρ.switch v).restrict B)
      ((ρ.restrict B).switch (⟨v, hv⟩ : {u : ρ.M // ρ.RestrictKeep B u}))) := by
  sorry

open scoped Classical in
/-- Smoothing then dropping a crossing-free circle `j` is dropping `j` then smoothing: every
occurrence is kept by both restrictions, the reconnected successors agree
(`restrict_succ_val_of_keep`, `firstReturn_map_val`), and the circles correspond
(`Sum.inl q ↦ Sum.inl q`, `Sum.inr f ↦ Sum.inr ⟨f, f ≠ j⟩`). -/
theorem restrictSmoothFreeIso {j : ρ.comps} (hj : ∀ u, ρ.comp u ≠ j) (v : ρ.M) :
    Nonempty (RecordIso
      ((ρ.smooth v).restrict (Finset.univ.erase (Sum.inr ⟨j, hj⟩ : ρ.SmoothComps v)))
      ((ρ.restrict (Finset.univ.erase j)).smooth
        (⟨v, ρ.restrictKeep_of_free hj v⟩ : {u : ρ.M // ρ.RestrictKeep (Finset.univ.erase j) u}))) := by
  sorry

end Link.Record

namespace Link.Diagram

variable (D : Diagram)

/-- **The restriction of an UNDER-first diagram is UNDER-first** (needed by the initialization of
lp:split-circle and mp:stack): rank = the order induced by `B.rank` on the block
(`Finset.orderIsoOfFin`), basepoints = the old ones (`restrict_visitPt_snd`: same traversal
coordinates, `visitCoord_restrictVisit`), under/over strands correspond
(`toFun_restrict_underStrand`). -/
theorem restrict_underFirst (B : D.Basing) (h : D.UnderFirst B) (S : Finset (Fin D.Γ.c))
    (hS : S.Nonempty) : ∃ B' : (D.restrict S hS).Basing, (D.restrict S hS).UnderFirst B' := by
  sorry

end Link.Diagram

/-- The split-circle motive: `E` with a crossing-free component `j`; `D'` any diagram whose record is
that of `E` without `j`. -/
def SplitMotive (E : Diagram) : Prop :=
  ∀ (j : Fin E.Γ.c), (∀ v : E.Γ.Visit, E.compOf v ≠ j) →
    ∀ (hne : (Finset.univ.erase j).Nonempty) (D' : Diagram),
      Nonempty (RecordIso D'.record (E.restrict (Finset.univ.erase j) hne).record) →
      P E = R.delta * P D'

/-- Initialization (sm-3:1195-1197 "If `b = 0`, the two source initialization values are `δ^{c−1}`
and `δ^c`"): `E` UNDER-first gives `P E = δ^{c−1}`; the restriction is UNDER-first
(`restrict_underFirst`), so `D'` is (`underFirst_of_recordIso`) with `c − 1` components. -/
theorem splitMotive_init (E : Diagram) (B : E.Basing) (h : E.UnderFirst B) : SplitMotive E := by
  sorry

/-- Step (sm-3:1197-1203): at the corresponding crossing of `D'`, the switch and the smoothing of
`D'` have records `≅ (E.switch x).restrict (erase j)` (`restrictSwitchIso`, `RecordIso.switch`,
`RecordIso.restrict`) and `≅ (E₀.restrict (erase j₀)).record` for the image `j₀ := ι₀.e.symm (inr j)`
of the free circle (`restrictSmoothFreeIso`, `RecordIso.smooth`, `RecordIso.restrict`,
`restrictRecordIso`); the sign agrees; `solvedR_mul_left` factors `δ`. -/
theorem splitMotive_step (E : Diagram) (x : E.Γ.Crossing) (E₀ : Diagram)
    (h₀ : IsOrientedSmoothing E x E₀) (ι₀ : RecordIso E₀.record (E.record.smooth (E.overVisit x)))
    (ihsw : SplitMotive (E.switch x)) (ih₀ : SplitMotive E₀) : SplitMotive E := by
  sorry

theorem splitMotive : ∀ E : Diagram, SplitMotive E :=
  Diagram.skein_induction SplitMotive splitMotive_init
    (fun E x E₀ h₀ hι ihsw ih₀ => splitMotive_step E x E₀ h₀ hι.some ihsw ih₀)

/-- lp:split-circle as printed (bundle copied verbatim from work/drafts/SplitCircle_statement.lean). -/
structure SplitCircleData : Prop where
  /-- eq. lp:split: `P_{D'} = δ P_D`. -/
  split : ∀ D D' : Diagram, IsSplitCircleAddition D D' → P D' = R.delta * P D
  /-- "In particular every crossing-free `c`-component diagram has value `δ^{c−1}`." -/
  crossing_free : ∀ D : Diagram, IsEmpty D.Γ.Crossing → P D = R.delta ^ (D.componentCount - 1)

theorem split_circle : SplitCircleData where
  split D D' h := by
    obtain ⟨j, hj, hne, hr⟩ := h
    have hfree : ∀ v : D'.Γ.Visit, D'.compOf v ≠ j := fun v => hj v.1 v.2.val v.2.2
    rw [splitMotive D' j hfree hne (D'.restrict (Finset.univ.erase j) hne) ⟨RecordIso.refl _⟩,
      P_rcompetitor.planar D _ (PlanarIsotopic.of_reparam hr)]
  crossing_free D h := by
    obtain ⟨B⟩ := D.exists_basing
    exact P_underFirst D B (D.underFirst_of_isEmpty h B)

/-! ## 11. mp:stack -/

/-- The restriction of `D` to the components of block `i` (the fibre of `blk` over `i`)
(copied verbatim from work/drafts/Stack_statement.lean). -/
noncomputable def blockRestrict (D : Diagram) {q : ℕ} (blk : Fin D.Γ.c → Fin q)
    (hblk : Function.Surjective blk) (i : Fin q) : Diagram :=
  D.restrict (Finset.univ.filter (fun c => blk c = i))
    (by obtain ⟨c, hc⟩ := hblk i; exact ⟨c, by simp [hc]⟩)

/-- "at every crossing between different blocks the smaller-index block is under the larger one"
(copied verbatim). -/
def BlockOrdered (D : Diagram) {q : ℕ} (blk : Fin D.Γ.c → Fin q) : Prop :=
  ∀ (x : D.Γ.Crossing) (s t : D.Γ.Strand), s ∈ x.val → t ∈ x.val → blk s.1 < blk t.1 →
    D.underStrand x = s

/-- mp:stack as printed (bundle copied verbatim). -/
structure StackData : Prop where
  /-- eq. mp:stack-value: `P_D = δ^{q−1} ∏_{i=1}^q P_{D_i}`. -/
  stack : ∀ (D : Diagram) (q : ℕ) (blk : Fin D.Γ.c → Fin q) (hblk : Function.Surjective blk),
    BlockOrdered D blk →
    P D = R.delta ^ (q - 1) * ∏ i : Fin q, P (blockRestrict D blk hblk i)
  /-- "In particular `P_{A ⊔ B} = δ P_A P_B` for two nonempty diagrams presented without mixed
  crossings": a diagram partitioned into two blocks with no crossing between the blocks. -/
  split_union : ∀ (D : Diagram) (blk : Fin D.Γ.c → Fin 2) (hblk : Function.Surjective blk),
    (∀ (x : D.Γ.Crossing) (s t : D.Γ.Strand), s ∈ x.val → t ∈ x.val → blk s.1 = blk t.1) →
    P D = R.delta * P (blockRestrict D blk hblk 0) * P (blockRestrict D blk hblk 1)

/-- The component set of block `i`. -/
abbrev blockSet (D : Diagram) {q : ℕ} (blk : Fin D.Γ.c → Fin q) (i : Fin q) : Finset (Fin D.Γ.c) :=
  Finset.univ.filter (fun c => blk c = i)

theorem blockSet_nonempty (D : Diagram) {q : ℕ} (blk : Fin D.Γ.c → Fin q)
    (hblk : Function.Surjective blk) (i : Fin q) : (blockSet D blk i).Nonempty := by
  obtain ⟨c, hc⟩ := hblk i; exact ⟨c, by simp [blockSet, hc]⟩

theorem blockRestrict_eq (D : Diagram) {q : ℕ} (blk : Fin D.Γ.c → Fin q)
    (hblk : Function.Surjective blk) (i : Fin q) :
    blockRestrict D blk hblk i = D.restrict (blockSet D blk i) (blockSet_nonempty D blk hblk i) := rfl

/-! ### 11.1 Block-compatible basings ("Order components block by block", sm-3:1514) -/

/-- A basing whose component order refines the block order. -/
def BlockCompatible (D : Diagram) {q : ℕ} (blk : Fin D.Γ.c → Fin q) (B : D.Basing) : Prop :=
  ∀ i k : Fin D.Γ.c, blk i < blk k → B.rank i < B.rank k

/-- Sort the components by `(blk i, i)` (`Finset.orderIsoOfFin` on the image of an injective key). -/
theorem exists_blockCompatible (D : Diagram) {q : ℕ} (blk : Fin D.Γ.c → Fin q) :
    ∃ B : D.Basing, BlockCompatible D blk B := by
  sorry

/-- "All between-block crossings are first encountered under" (sm-3:1515): a bad crossing of a
block-compatible basing of a block-ordered diagram is internal to one block. -/
theorem blk_eq_of_bad {D : Diagram} {q : ℕ} {blk : Fin D.Γ.c → Fin q} {B : D.Basing}
    (hB : BlockCompatible D blk B) (hord : BlockOrdered D blk) {x : D.Γ.Crossing} (hx : D.Bad B x) :
    blk (D.overStrand x).1 = blk (D.underStrand x).1 := by
  sorry

/-- Switching an internal crossing "preserves the block assignment and the between-block
hypothesis" (sm-3:1524-1525). -/
theorem BlockOrdered.switch_of_internal {D : Diagram} {q : ℕ} {blk : Fin D.Γ.c → Fin q}
    (hord : BlockOrdered D blk) {x : D.Γ.Crossing}
    (hx : blk (D.overStrand x).1 = blk (D.underStrand x).1) : BlockOrdered (D.switch x) blk := by
  sorry

/-! ### 11.2 The block restrictions of the switch -/

/-- The internal crossing `x` of block `i` as a crossing of the block restriction
(`restrict_mapCrossing_range_iff`). -/
theorem exists_blockCrossing (D : Diagram) {q : ℕ} (blk : Fin D.Γ.c → Fin q)
    (hblk : Function.Surjective blk) (x : D.Γ.Crossing)
    (hx : blk (D.overStrand x).1 = blk (D.underStrand x).1) :
    ∃ y : (blockRestrict D blk hblk (blk (D.overStrand x).1)).Γ.Crossing,
      (D.Γ.restrictMap (blockSet D blk (blk (D.overStrand x).1))
        (blockSet_nonempty D blk hblk _)).mapCrossing y = x := by
  sorry

/-- "is the same switch in its block restriction" (`switch_restrict_of_internal`). -/
theorem blockRestrict_switch_of_internal (D : Diagram) {q : ℕ} (blk : Fin D.Γ.c → Fin q)
    (hblk : Function.Surjective blk) (x : D.Γ.Crossing) (i : Fin q)
    (y : (blockRestrict D blk hblk i).Γ.Crossing)
    (hy : (D.Γ.restrictMap (blockSet D blk i) (blockSet_nonempty D blk hblk i)).mapCrossing y = x) :
    blockRestrict (D.switch x) blk hblk i = (blockRestrict D blk hblk i).switch y := by
  sorry

/-- "the other restrictions do not change" (`switch_restrict_of_external`). -/
theorem blockRestrict_switch_of_external (D : Diagram) {q : ℕ} (blk : Fin D.Γ.c → Fin q)
    (hblk : Function.Surjective blk) (x : D.Γ.Crossing) (i : Fin q)
    (hi : i ≠ blk (D.overStrand x).1) :
    blockRestrict (D.switch x) blk hblk i = blockRestrict D blk hblk i := by
  sorry

/-! ### 11.3 Record level: restriction versus smoothing (the block transport under smoothing,
sm-3:1526-1531 "The restriction of the smoothed diagram in that block is exactly the oriented
smoothing of the old block restriction; the other restrictions do not change") -/

namespace Link

/-- First return to `p` and then to `q` is first return to `p ∧ q`. -/
theorem firstReturn_firstReturn {α : Type*} [Fintype α] (f : Equiv.Perm α) (p q : α → Prop)
    [DecidablePred p] [DecidablePred q] (m : {m : {m // p m} // q m.1}) :
    ((firstReturn (firstReturn f p) (fun m => q m.1)) m).1.1 =
      ((firstReturn f (fun m => p m ∧ q m)) ⟨m.1.1, m.1.2, m.2⟩).1 := by
  sorry

/-- First return commutes with a transposition of two `p`-points. -/
theorem firstReturn_mul_swap {α : Type*} [Fintype α] [DecidableEq α] (f : Equiv.Perm α)
    (p : α → Prop) [DecidablePred p] (a b : α) (ha : p a) (hb : p b) :
    firstReturn (f * Equiv.swap a b) p =
      firstReturn f p * Equiv.swap (⟨a, ha⟩ : {m // p m}) ⟨b, hb⟩ := by
  sorry

namespace Record

variable (ρ : Record)

/-- "Every new component inherits the same block as the strands smoothed" (sm-3:1527): when both
occurrences of the smoothed crossing lie in `B` or both outside, membership of the carrying circle
in `B` is constant along the reconnected successor. -/
theorem comp_mem_iff_of_reconnect_sameCycle (v : ρ.M) (B : Finset ρ.comps)
    (hvB : ρ.comp v ∈ B ↔ ρ.comp (ρ.pair v) ∈ B) {u w : ρ.M}
    (h : (ρ.reconnect v).SameCycle u w) : ρ.comp u ∈ B ↔ ρ.comp w ∈ B := by
  sorry

open scoped Classical in
/-- The block of the smoothing corresponding to `B` (`Quotient.liftOn'` of `comp · ∈ B`, plus the
crossing-free circles of `B`). -/
theorem exists_smoothBlock (v : ρ.M) (B : Finset ρ.comps)
    (hvB : ρ.comp v ∈ B ↔ ρ.comp (ρ.pair v) ∈ B) :
    ∃ B' : Finset (ρ.smooth v).comps,
      (∀ u : ρ.M, (Sum.inl (Quotient.mk _ u) : ρ.SmoothComps v) ∈ B' ↔ ρ.comp u ∈ B) ∧
      (∀ f : ρ.FreeComp, (Sum.inr f : ρ.SmoothComps v) ∈ B' ↔ f.1 ∈ B) := by
  sorry

open scoped Classical in
/-- **Restriction of the smoothing = smoothing of the restriction** at an internal crossing.
Occurrences: `SmoothKeep v ∧ RestrictKeep B` on both sides; successor: both are the first return of
`s ∘ swap v (τ v)` to that set (`firstReturn_firstReturn`, `firstReturn_mul_swap`); circles: the
`s₁`-cycles meeting `B` plus the free circles in `B`. -/
theorem restrictSmoothIso (v : ρ.M) (B : Finset ρ.comps) (hv : ρ.RestrictKeep B v)
    (B' : Finset (ρ.smooth v).comps)
    (hB' : ∀ u : ρ.M, (Sum.inl (Quotient.mk _ u) : ρ.SmoothComps v) ∈ B' ↔ ρ.comp u ∈ B)
    (hB'' : ∀ f : ρ.FreeComp, (Sum.inr f : ρ.SmoothComps v) ∈ B' ↔ f.1 ∈ B) :
    Nonempty (RecordIso ((ρ.smooth v).restrict B')
      ((ρ.restrict B).smooth (⟨v, hv⟩ : {u : ρ.M // ρ.RestrictKeep B u}))) := by
  sorry

open scoped Classical in
/-- **Restriction of the smoothing at an external crossing = the old restriction**: no occurrence of
`B` is erased and `s₁` agrees with `s` along every `B`-circle (`comp` is `s`-invariant and
`comp v ∉ B`). -/
theorem restrictSmoothDisjointIso (v : ρ.M) (B : Finset ρ.comps) (hv : ρ.comp v ∉ B)
    (hv' : ρ.comp (ρ.pair v) ∉ B) (B' : Finset (ρ.smooth v).comps)
    (hB' : ∀ u : ρ.M, (Sum.inl (Quotient.mk _ u) : ρ.SmoothComps v) ∈ B' ↔ ρ.comp u ∈ B)
    (hB'' : ∀ f : ρ.FreeComp, (Sum.inr f : ρ.SmoothComps v) ∈ B' ↔ f.1 ∈ B) :
    Nonempty (RecordIso ((ρ.smooth v).restrict B') (ρ.restrict B)) := by
  sorry

end Record

end Link

/-! ### 11.4 The block structure of the smoothing and the stack step -/

/-- The blocks of the smoothed record: a cycle of `s₁` inherits the block of any occurrence it
carries (well defined by `comp_mem_iff_of_reconnect_sameCycle` applied to the fibres of `blk`), a
crossing-free circle keeps its block. -/
theorem exists_smoothBlk (D : Diagram) {q : ℕ} (blk : Fin D.Γ.c → Fin q) (x : D.Γ.Crossing)
    (hx : blk (D.overStrand x).1 = blk (D.underStrand x).1) :
    ∃ blkS : (D.record.smooth (D.overVisit x)).comps → Fin q,
      (∀ u : D.Γ.Visit, blkS (Sum.inl (Quotient.mk _ u)) = blk (D.compOf u)) ∧
      (∀ f : D.record.FreeComp, blkS (Sum.inr f) = blk f.1) := by
  sorry

/-- The transported blocks on `D₀` are surjective ("no block becomes empty"), block-ordered ("All
between-block crossing visits persist on their original strands, so their under/over relation still
has the required block order", via `bit_eq`/`pair_eq`/`comp_eq` of `ι₀`), and their fibres
correspond to the smoothed blocks of `D`. -/
theorem exists_blocks_of_smoothing (D : Diagram) {q : ℕ} (blk : Fin D.Γ.c → Fin q)
    (hblk : Function.Surjective blk) (hord : BlockOrdered D blk) (x : D.Γ.Crossing)
    (hx : blk (D.overStrand x).1 = blk (D.underStrand x).1) (D₀ : Diagram)
    (ι₀ : RecordIso D₀.record (D.record.smooth (D.overVisit x))) :
    ∃ blk₀ : Fin D₀.Γ.c → Fin q, ∃ hblk₀ : Function.Surjective blk₀, BlockOrdered D₀ blk₀ ∧
      ∀ i : Fin q, ∀ c : Fin D₀.Γ.c, blk₀ c = i ↔
        ((∀ u : D.Γ.Visit, (Sum.inl (Quotient.mk _ u) : D.record.SmoothComps (D.overVisit x)) = ι₀.e c →
            blk (D.compOf u) = i) ∧
          (∀ f : D.record.FreeComp, (Sum.inr f : D.record.SmoothComps (D.overVisit x)) = ι₀.e c →
            blk f.1 = i)) := by
  sorry

/-- "If `b = 0`, the full diagram is ascending … their product times `δ^{q−1}` has the same exponent
`q − 1 + Σ(c_i − 1) = Σ c_i − 1`" (sm-3:1519-1523): `P_underFirst` on `D` and on every block
restriction (`restrict_underFirst`), `Finset.prod_pow_eq_pow_sum`,
`Finset.card_eq_sum_card_fiberwise`. -/
theorem stack_init (D : Diagram) {q : ℕ} (blk : Fin D.Γ.c → Fin q) (hblk : Function.Surjective blk)
    (B : D.Basing) (h : D.UnderFirst B) :
    P D = R.delta ^ (q - 1) * ∏ i : Fin q, P (blockRestrict D blk hblk i) := by
  sorry

/-- The stack step (sm-3:1524-1533): with `i₀` the block of the resolved crossing, the switch and the
smoothing change only the factor `i₀` (`blockRestrict_switch_of_*`, `restrictSmoothIso`,
`restrictSmoothDisjointIso`, `restrictRecordIso`, `RecordIso.restrict`, `presentations`), that factor
obeys `solvedR_of_skein` at the corresponding crossing `y` of the block restriction with the same
sign (`restrict_isPositive_iff`), and `Finset.mul_prod_erase` isolates it. -/
theorem stack_step (D : Diagram) {q : ℕ} (blk : Fin D.Γ.c → Fin q) (hblk : Function.Surjective blk)
    (hord : BlockOrdered D blk) (x : D.Γ.Crossing)
    (hx : blk (D.overStrand x).1 = blk (D.underStrand x).1) (D₀ : Diagram)
    (h₀ : IsOrientedSmoothing D x D₀) (ι₀ : RecordIso D₀.record (D.record.smooth (D.overVisit x)))
    (ihsw : P (D.switch x) = R.delta ^ (q - 1) * ∏ i : Fin q, P (blockRestrict (D.switch x) blk hblk i))
    (ih₀ : ∀ (blk₀ : Fin D₀.Γ.c → Fin q) (hblk₀ : Function.Surjective blk₀), BlockOrdered D₀ blk₀ →
      P D₀ = R.delta ^ (q - 1) * ∏ i : Fin q, P (blockRestrict D₀ blk₀ hblk₀ i)) :
    P D = R.delta ^ (q - 1) * ∏ i : Fin q, P (blockRestrict D blk hblk i) := by
  sorry

/-- **mp:stack-value** by the `(N, b)` induction with a block-compatible basing (own scaffold: the
basing must refine the block order, so `skein_induction` is not applied directly; the switch and
count lemmas of §2 are reused). -/
theorem stack_value : ∀ (D : Diagram) (q : ℕ) (blk : Fin D.Γ.c → Fin q)
    (hblk : Function.Surjective blk), BlockOrdered D blk →
    P D = R.delta ^ (q - 1) * ∏ i : Fin q, P (blockRestrict D blk hblk i) := by
  have key : ∀ N : ℕ, ∀ D : Diagram, Fintype.card D.Γ.Crossing = N →
      ∀ (q : ℕ) (blk : Fin D.Γ.c → Fin q) (hblk : Function.Surjective blk), BlockOrdered D blk →
      P D = R.delta ^ (q - 1) * ∏ i : Fin q, P (blockRestrict D blk hblk i) := by
    intro N
    induction N using Nat.strong_induction_on with
    | _ N ihN =>
      have inner : ∀ b : ℕ, ∀ (D : Diagram) (q : ℕ) (blk : Fin D.Γ.c → Fin q)
          (hblk : Function.Surjective blk) (B : D.Basing), Fintype.card D.Γ.Crossing = N →
          BlockCompatible D blk B → BlockOrdered D blk → D.badCount B = b →
          P D = R.delta ^ (q - 1) * ∏ i : Fin q, P (blockRestrict D blk hblk i) := by
        intro b
        induction b with
        | zero =>
          intro D q blk hblk B hN _ _ hb
          exact stack_init D blk hblk B ((D.underFirst_iff_badCount_eq_zero B).mpr hb)
        | succ b ihb =>
          intro D q blk hblk B hN hB hord hb
          obtain ⟨x, hx⟩ := D.exists_bad_of_badCount_pos B (by omega)
          have hint := blk_eq_of_bad hB hord hx
          obtain ⟨D₀, h₀, ⟨ι₀⟩⟩ := exists_smoothing_record D x
          refine stack_step D blk hblk hord x hint D₀ h₀ ι₀ ?_ ?_
          · refine ihb (D.switch x) q blk hblk (B.switch x) hN hB (hord.switch_of_internal hint) ?_
            have := D.badCount_switch_of_bad B hx
            omega
          · intro blk₀ hblk₀ hord₀
            have hc := h₀.card_crossing
            exact ihN (Fintype.card D₀.Γ.Crossing) (by omega) D₀ rfl q blk₀ hblk₀ hord₀
      intro D hN q blk hblk hord
      obtain ⟨B, hB⟩ := exists_blockCompatible D blk
      exact inner _ D q blk hblk B hN hB hord rfl
  intro D q blk hblk hord
  exact key _ D rfl q blk hblk hord

theorem stack : StackData where
  stack := stack_value
  split_union D blk hblk h := by
    have hord : BlockOrdered D blk := by
      intro x s t hs ht hlt
      exact absurd (h x s t hs ht) (ne_of_lt hlt)
    rw [stack_value D 2 blk hblk hord, Fin.prod_univ_two, mul_assoc,
      show (2 : ℕ) - 1 = 1 from rfl, pow_one]

end SM
