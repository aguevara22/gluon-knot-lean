import SM.Smoothing
import SM.CoefficientTransport
import SM.LocalPolynomial
import SM.SingleCrossing

/-! Ported 2026-09-14 from work/drafts/polyblock/Skeleton_FINAL.lean §0-§5 and §7 (design panel, winner B grafted with A; PLAN_FINAL.md), i.e. the sorry-free part: the record-level (N, b) skein induction and the four rows lp:core (`SM.lp_core`), rp:record-polynomial (`SM.record_polynomial`), lc:presentations (`SM.presentations`), lp:split-circle (`SM.split_circle`); the mp:stack chain (§6, with open lemmas) stays in the draft until its units finish. Bundles verbatim from work/drafts/{LpCore,RecordPolynomial,Presentations,SplitCircle}_statement.lean. Only this header added. -/


/-! # Skeleton FINAL — the five polynomial rows by a RECORD-LEVEL `(N, b)` induction

Judge's synthesis (2026-09-14) of the two architect skeletons: the winning route is **B**
(record-level based order `Record.RBasing`, one induction principle `skein_induction_based`, the
partner diagram quantified inside the predicate), with three grafts from **A**:
(G1) lp:core's `gaussian`/`support` by the printed integral descent (`G_descent`, a
`skein_induction`) instead of through lp:coefficient-transport — `P_gaussian` now consumes `lp_lm`
only; (G2) the mp:stack record-level commutations `restrictSmoothIso` / `restrictSmoothDisjointIso`
stated with the target block characterised by hypotheses (A's form), on top of the two permutation
lemmas `firstReturn_firstReturn` / `firstReturn_mul_swap`, and the block function of the smoothing
as a transparent `Quotient.lift` (`smoothBlock`) whose only content is
`beta_comp_eq_of_reconnect_sameCycle`; (G3) the diagram-level `restrict_underFirst` for the
initialization of mp:stack (no first-return enumeration needed: `restrict_visitPt_snd`).
Plan of record: work/drafts/polyblock/PLAN_FINAL.md.

Status (`lake env lean`: no errors): the five row theorems `record_polynomial`, `lp_core`,
`split_circle`, `presentations`, `stack` (fixed bundles copied verbatim from
work/drafts/*_statement.lean) are PROVED from the chain; the chains of rp:record-polynomial,
lp:core, lp:split-circle and lc:presentations are PROVED (no `sorry` in §0-§5).  The `sorry`s are
exactly the mp:stack chain of §6: `beta_comp_eq_of_reconnect_sameCycle`, `firstReturn_firstReturn`,
`firstReturn_mul_swap`, `restrictSmoothIso`, `restrictSmoothDisjointIso`,
`rBlockOrdered_of_blockOrdered`, `BlockOrdered.switch_of_internal`,
`blockRestrict_switch_of_internal`, `blockRestrict_switch_of_external`, `blocks_of_smoothing`,
`restrict_underFirst`, `stack_init`, `stack_step`; `stack_formula` and `stack` are proved from them.

Architecture:
* §0 algebra in `T` and `R` (cancellation, the two solved recursions, `solvedR`) — no geometry;
* §1 the record-level based order `Record.RBasing`, `key`, `IsBad`, `badCount`, `RUnderFirst`; the
  switch step `badCount_switch` and the transport along a `RecordIso` (`RBasing.map`);
* §2 the diagram side: the ONE geometric bridge `exists_underFirst_of_rUnderFirst`, the count bridge
  `badCount_rbasingSwitch`, and the induction principles `skein_induction_based` / `skein_induction`;
* §3 lp:core: `G = φ(F)`, `G_skein`, `G_descent` (integral descent + support), `P_skein` via `reMap`,
  `P_eq_homfly` via the accepted lp:coefficient-transport, `unique`/`ne_zero` by `skein_induction`;
* §4 rp:record-polynomial / lc:presentations by `skein_induction_based`;
* §5 lp:split-circle by `skein_induction_based` on `Record.addFree`;
* §6 mp:stack: chain statements (unit list in PLAN_FINAL.md §6) and the proved assembly. -/

namespace SM

open SM.Link

/-! ## §0. Algebra: cancellation in `T`, the solved recursions in `R` -/

namespace Link

/-- Cancellation of the leading term of the source skein (rp:record-polynomial, sm-3:1274-1279): two
source skeins with equal switched and smoothed terms have equal positive terms (`l` is a unit). -/
theorem T.eq_of_skein_l {a a' b c : T} (h : T.l * a + T.lInv * b + T.m * c = 0)
    (h' : T.l * a' + T.lInv * b + T.m * c = 0) : a = a' := by
  have h1 : T.l * (a - a') = 0 := by linear_combination h - h'
  have h2 : a - a' = T.lInv * (T.l * (a - a')) := by rw [← mul_assoc, T.lInv_mul_l, one_mul]
  rw [h1, mul_zero] at h2
  exact sub_eq_zero.mp h2

/-- Cancellation of the `l⁻¹` term (rp:record-polynomial, sm-3:1280-1287, the negative case). -/
theorem T.eq_of_skein_lInv {a a' b c : T} (h : T.l * b + T.lInv * a + T.m * c = 0)
    (h' : T.l * b + T.lInv * a' + T.m * c = 0) : a = a' := by
  have h1 : T.lInv * (a - a') = 0 := by linear_combination h - h'
  have h2 : a - a' = T.l * (T.lInv * (a - a')) := by rw [← mul_assoc, T.l_mul_lInv, one_mul]
  rw [h1, mul_zero] at h2
  exact sub_eq_zero.mp h2

/-- Every crossing `x` of `D` with a smoothing `D₀` there lies in a skein triple: `(D, D^sw, D₀)` if
`x` is positive, `(D^sw, D, D₀)` if `x` is negative (lp:core sm-3:1104-1113; uses
`IsOrientedSmoothing.switch` and `switch_switch`). -/
theorem Diagram.skeinTriple_of_smoothing (D : Diagram) (x : D.Γ.Crossing) (D₀ : Diagram)
    (h : IsOrientedSmoothing D x D₀) :
    (D.IsPositive x ∧ IsSkeinTriple D (D.switch x) D₀) ∨
      (¬ D.IsPositive x ∧ IsSkeinTriple (D.switch x) D D₀) := by
  by_cases hp : D.IsPositive x
  · exact Or.inl ⟨hp, x, hp, rfl, h⟩
  · exact Or.inr ⟨hp, x, (D.switch_isPositive_self x).mpr hp, (D.switch_switch x).symm, h.switch⟩

/-- lp:positive (sm-3:1104-1106): `Q_D = a⁻² Q_{D^sw} + a⁻¹ z Q_{D⁰}` at a positive crossing, for any
`Q : Diagram → R` satisfying the campaign skein. -/
theorem skein_recursion_pos {Q : Diagram → R}
    (hQ : ∀ Dp Dm D0 : Diagram, IsSkeinTriple Dp Dm D0 → R.a * Q Dp - R.aInv * Q Dm = R.z * Q D0)
    {D : Diagram} {x : D.Γ.Crossing} {D₀ : Diagram} (h : IsOrientedSmoothing D x D₀)
    (hp : D.IsPositive x) :
    Q D = R.aInv * R.aInv * Q (D.switch x) + R.aInv * R.z * Q D₀ := by
  have hs := hQ _ _ _ ⟨x, hp, rfl, h⟩
  have u := R.aInv_mul_a
  linear_combination R.aInv * hs - Q D * u

/-- lp:negative (sm-3:1108-1113): `Q_D = a² Q_{D^sw} − a z Q_{D⁰}` at a negative crossing. -/
theorem skein_recursion_neg {Q : Diagram → R}
    (hQ : ∀ Dp Dm D0 : Diagram, IsSkeinTriple Dp Dm D0 → R.a * Q Dp - R.aInv * Q Dm = R.z * Q D0)
    {D : Diagram} {x : D.Γ.Crossing} {D₀ : Diagram} (h : IsOrientedSmoothing D x D₀)
    (hp : ¬ D.IsPositive x) :
    Q D = R.a * R.a * Q (D.switch x) - R.a * R.z * Q D₀ := by
  have hs := hQ _ _ _ (⟨x, (D.switch_isPositive_self x).mpr hp, (D.switch_switch x).symm, h.switch⟩ :
    IsSkeinTriple (D.switch x) D D₀)
  have u := R.a_mul_aInv
  linear_combination (-R.a) * hs - Q D * u


open scoped Classical in
/-- lp:positive / lp:negative (sm-3:1104-1113) as one function of the positivity `pos` of the
resolved crossing and the two smaller values: `a⁻² u + a⁻¹ z w` at a positive crossing,
`a² u − a z w` at a negative one (graft from Skeleton A §1; used by the mp:stack step). -/
noncomputable def solvedR (pos : Prop) (u w : R) : R :=
  if pos then R.aInv * R.aInv * u + R.aInv * R.z * w else R.a * R.a * u - R.a * R.z * w

/-- The recursion is `R`-linear in the two smaller values ("the coefficients are scalar elements of
the commutative ring `R` … factor it out", sm-3:1201-1203, 1532-1533). -/
theorem solvedR_mul_left (pos : Prop) (c u w : R) :
    solvedR pos (c * u) (c * w) = c * solvedR pos u w := by
  unfold solvedR; split_ifs <;> ring

/-- Any function with the campaign skein satisfies the solved recursion at every crossing, for every
oriented smoothing there (`skein_recursion_pos` / `skein_recursion_neg` under the classical `if`). -/
theorem solvedR_of_skein {Q : Diagram → R}
    (hQ : ∀ Dp Dm D0 : Diagram, IsSkeinTriple Dp Dm D0 → R.a * Q Dp - R.aInv * Q Dm = R.z * Q D0)
    {D : Diagram} {x : D.Γ.Crossing} {D₀ : Diagram} (h : IsOrientedSmoothing D x D₀) :
    Q D = solvedR (D.IsPositive x) (Q (D.switch x)) (Q D₀) := by
  unfold solvedR
  split_ifs with hp
  · exact skein_recursion_pos hQ h hp
  · exact skein_recursion_neg hQ h hp

/-! ## §1. The record-level based order (lp:lm sm-3:946-949 read on records; rp:record-polynomial
sm-3:1230-1244 "Choose an order on the components ... and one basepoint ... on each component") -/

namespace Record

variable (ρ : Record)

/-- A record-level *based order*: an injective rank of the parametrizing circles and a *base
occurrence* on every circle carrying occurrences (the first occurrence after the basepoint; the
basepoint itself is not part of the record).  `base v` is the base occurrence of the circle of `v`. -/
structure RBasing where
  /-- the auxiliary component order -/
  rank : ρ.comps → ℕ
  rank_inj : Function.Injective rank
  /-- the base occurrence of the circle carrying `v` -/
  base : ρ.M → ρ.M
  base_comp : ∀ v, ρ.comp (base v) = ρ.comp v
  base_const : ∀ v w, ρ.comp v = ρ.comp w → base v = base w

namespace RBasing

variable {ρ} (B : RBasing ρ)

/-- Every occurrence is a `succ`-iterate of the base occurrence of its circle (`succ_cycle`). -/
theorem exists_pow_base_eq (v : ρ.M) : ∃ n : ℕ, (ρ.succ ^ n) (B.base v) = v := by
  obtain ⟨n, -, hn⟩ := (ρ.succ_cycle _ _ (B.base_comp v)).exists_pow_eq'
  exact ⟨n, hn⟩

/-- The based position of an occurrence on its circle: the least number of forward steps from the
base occurrence ("from their basepoints and in their orientations", sm-3:948). -/
noncomputable def pos (v : ρ.M) : ℕ := Nat.find (B.exists_pow_base_eq v)

theorem pow_pos_base (v : ρ.M) : (ρ.succ ^ B.pos v) (B.base v) = v :=
  Nat.find_spec (B.exists_pow_base_eq v)

theorem pos_le {v : ρ.M} {n : ℕ} (h : (ρ.succ ^ n) (B.base v) = v) : B.pos v ≤ n :=
  Nat.find_min' _ h

theorem pos_eq_zero_iff (v : ρ.M) : B.pos v = 0 ↔ B.base v = v := by
  unfold pos
  rw [Nat.find_eq_zero]
  simp

/-- The based rank of an occurrence: component rank first, then position on the circle
(lexicographic, as `Diagram.basedRank`). -/
noncomputable def key (v : ρ.M) : ℕ ×ₗ ℕ := toLex (B.rank (ρ.comp v), B.pos v)

/-- Distinct occurrences have distinct based ranks. -/
theorem key_injective : Function.Injective B.key := by
  intro v w h
  simp only [key, toLex_inj, Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  have hc : ρ.comp v = ρ.comp w := B.rank_inj h1
  have hb : B.base v = B.base w := B.base_const v w hc
  calc v = (ρ.succ ^ B.pos v) (B.base v) := (B.pow_pos_base v).symm
    _ = (ρ.succ ^ B.pos w) (B.base w) := by rw [h2, hb]
    _ = w := B.pow_pos_base w

/-- A *bad* occurrence: an over occurrence met before its under partner ("Call a crossing bad if
its first encounter in this ordered traversal is the overpass", sm-3:1236-1237). -/
def IsBad (v : ρ.M) : Prop := ρ.isOver v = true ∧ B.key v < B.key (ρ.pair v)

/-- Record-level UNDER-first: every over occurrence is met after its under partner. -/
def RUnderFirst : Prop := ∀ v, ρ.isOver v = true → B.key (ρ.pair v) < B.key v

open scoped Classical in
/-- `b(D)`: the number of bad crossings (one over occurrence per crossing). -/
noncomputable def badCount : ℕ := (Finset.univ.filter B.IsBad).card

/-- "The initialization is exactly `b = 0`" (sm-3:1084-1085). -/
theorem badCount_eq_zero_iff : B.badCount = 0 ↔ B.RUnderFirst := by
  classical
  unfold badCount
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  constructor
  · intro h v hv
    have hnb : ¬ B.IsBad v := h (Finset.mem_univ v)
    rcases lt_trichotomy (B.key (ρ.pair v)) (B.key v) with hlt | heq | hgt
    · exact hlt
    · exact absurd (B.key_injective heq) (ρ.pair_ne v)
    · exact absurd ⟨hv, hgt⟩ hnb
  · intro h v _ hb
    exact lt_asymm (h v hb.1) hb.2

theorem exists_isBad_of_badCount_ne_zero (h : B.badCount ≠ 0) : ∃ v, B.IsBad v := by
  classical
  unfold badCount at h
  obtain ⟨v, hv⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero h)
  exact ⟨v, (Finset.mem_filter.mp hv).2⟩

/-- The based order survives a switch: same circles, occurrences and successor (sm-3:1085-1086 "A
switch at the first bad crossing keeps the parameter circles and their traversal order"). -/
def switch (x : ρ.M) : RBasing (ρ.switch x) :=
  ⟨B.rank, B.rank_inj, B.base, B.base_comp, B.base_const⟩

theorem key_switch (x v : ρ.M) : (B.switch x).key v = B.key v := rfl

/-- The switch step (sm-3:1086-1088): switching a bad crossing makes it good and changes no other
first-encounter designation, so `b` drops by exactly one.  (Any bad crossing works; the printed
"first" bad crossing is not needed for the lexicographic induction.) -/
theorem badCount_switch {x : ρ.M} (hx : B.IsBad x) : (B.switch x).badCount + 1 = B.badCount := by
  classical
  have hmem : x ∈ Finset.univ.filter B.IsBad := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩
  have hset : (Finset.univ.filter (fun v : ρ.M => (B.switch x).IsBad v)) =
      (Finset.univ.filter B.IsBad).erase x := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
    change ((ρ.switch x).isOver v = true ∧ B.key v < B.key (ρ.pair v)) ↔
      (v ≠ x ∧ (ρ.isOver v = true ∧ B.key v < B.key (ρ.pair v)))
    by_cases hvx : v = x
    · rw [hvx, Record.switch_isOver_self]
      constructor
      · rintro ⟨h1, -⟩
        rw [hx.1] at h1
        exact absurd h1 (by decide)
      · rintro ⟨h1, -⟩
        exact absurd rfl h1
    · by_cases hvp : v = ρ.pair x
      · rw [hvp, Record.switch_isOver_pair]
        constructor
        · rintro ⟨-, h2⟩
          rw [ρ.pair_invol] at h2
          exact absurd (lt_trans h2 hx.2) (lt_irrefl _)
        · rintro ⟨-, h1, -⟩
          rw [ρ.bit_pair, hx.1] at h1
          exact absurd h1 (by decide)
      · rw [Record.switch_isOver_of_ne ρ x hvx hvp]
        exact ⟨fun h => ⟨hvx, h⟩, fun h => h.2⟩
  have hcard : (B.switch x).badCount =
      (Finset.univ.filter (fun v : ρ.M => (B.switch x).IsBad v)).card := rfl
  have hB : B.badCount = (Finset.univ.filter B.IsBad).card := rfl
  rw [hcard, hset, Finset.card_erase_of_mem hmem, hB]
  have := Finset.card_pos.mpr ⟨x, hmem⟩
  omega

/-- Transport of a based order along a named record isomorphism (rp:record-polynomial sm-3:1231-1235
"Transfer the order to `D'` ... choose its new basepoint in the interval just preceding the image of
the old first crossing occurrence"). -/
def map {ρ' : Record} (ι : RecordIso ρ ρ') : RBasing ρ' where
  rank := B.rank ∘ ι.e.symm
  rank_inj := B.rank_inj.comp ι.e.symm.injective
  base := ι.Φ ∘ B.base ∘ ι.Φ.symm
  base_comp v := by
    show ρ'.comp (ι.Φ (B.base (ι.Φ.symm v))) = ρ'.comp v
    rw [ι.comp_eq, B.base_comp, ← ι.comp_eq, Equiv.apply_symm_apply]
  base_const v w h := by
    show ι.Φ (B.base (ι.Φ.symm v)) = ι.Φ (B.base (ι.Φ.symm w))
    congr 1
    apply B.base_const
    apply ι.e.injective
    rw [← ι.comp_eq, ← ι.comp_eq, Equiv.apply_symm_apply, Equiv.apply_symm_apply, h]

theorem key_map {ρ' : Record} (ι : RecordIso ρ ρ') (v : ρ.M) : (B.map ι).key (ι.Φ v) = B.key v := by
  unfold key
  rw [toLex_inj]
  refine Prod.ext ?_ ?_
  · show B.rank (ι.e.symm (ρ'.comp (ι.Φ v))) = B.rank (ρ.comp v)
    rw [ι.comp_eq, Equiv.symm_apply_apply]
  · show Nat.find _ = Nat.find _
    apply Nat.find_congr'
    intro n
    show (ρ'.succ ^ n) (ι.Φ (B.base (ι.Φ.symm (ι.Φ v)))) = ι.Φ v ↔ (ρ.succ ^ n) (B.base v) = v
    rw [Equiv.symm_apply_apply, ← ι.Φ_pow, ι.Φ.injective.eq_iff]

theorem isBad_map {ρ' : Record} (ι : RecordIso ρ ρ') (v : ρ.M) :
    (B.map ι).IsBad (ι.Φ v) ↔ B.IsBad v := by
  unfold IsBad
  rw [ι.bit_eq, ← ι.pair_eq, B.key_map ι v, B.key_map ι (ρ.pair v)]

theorem badCount_map {ρ' : Record} (ι : RecordIso ρ ρ') : (B.map ι).badCount = B.badCount := by
  classical
  unfold badCount
  conv_rhs => rw [← Finset.card_map ι.Φ.toEmbedding]
  congr 1
  ext w
  simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Equiv.coe_toEmbedding]
  constructor
  · intro hw
    obtain ⟨v, rfl⟩ := ι.Φ.surjective w
    exact ⟨v, (B.isBad_map ι v).mp hw, rfl⟩
  · rintro ⟨v, hv, rfl⟩
    exact (B.isBad_map ι v).mpr hv

theorem rUnderFirst_map {ρ' : Record} (ι : RecordIso ρ ρ') : (B.map ι).RUnderFirst ↔ B.RUnderFirst := by
  unfold RUnderFirst
  constructor
  · intro h v hv
    have := h (ι.Φ v) (by rw [ι.bit_eq]; exact hv)
    rwa [← ι.pair_eq, B.key_map ι, B.key_map ι] at this
  · intro h v' hv'
    obtain ⟨v, rfl⟩ := ι.Φ.surjective v'
    rw [← ι.pair_eq, B.key_map ι, B.key_map ι]
    exact h v (by rwa [ι.bit_eq] at hv')

/-- Every record has a based order (any injective rank; any occurrence of each circle as its base).
"New orders and basepoints can be chosen because the first complexity coordinate has decreased"
(sm-3:1099-1101). -/
noncomputable def default (ρ : Record) : RBasing ρ where
  rank c := (Fintype.equivFin ρ.comps c).val
  rank_inj := Fin.val_injective.comp (Fintype.equivFin ρ.comps).injective
  base v := Classical.choose (⟨v, rfl⟩ : ∃ w, ρ.comp w = ρ.comp v)
  base_comp v := Classical.choose_spec (⟨v, rfl⟩ : ∃ w, ρ.comp w = ρ.comp v)
  base_const v w h := by
    have key : ∀ (c : ρ.comps) (hc : ∃ u, ρ.comp u = c) (v : ρ.M) (hv : ρ.comp v = c),
        Classical.choose hc = Classical.choose (⟨v, rfl⟩ : ∃ u, ρ.comp u = ρ.comp v) := by
      intro c hc v hv
      subst hv
      rfl
    exact key (ρ.comp v) ⟨v, rfl⟩ w h.symm

end RBasing

end Record

/-! ## §2. The diagram side: the geometric bridge and the induction principles -/

/-- Sub-lemma of the bridge, pure real arithmetic on the circle `[0, k)`: if `c₀` has the least
forward offset from the basepoint `β` among `c₀, cu, co` and `cu` lies cyclically strictly between
`c₀` and `co`, then `cu` has a smaller offset than `co`.  Case analysis on `β ≤ c₀` and on the
position of `cu, co` relative to `β`; every case is `linarith` after unfolding `cyclicOffset` and
`cycBetween`. -/
theorem cyclicOffset_lt_of_cycBetween {k : ℕ} {β c₀ cu co : ℝ}
    (h0 : 0 ≤ c₀) (huk : cu < k) (ho0 : 0 ≤ co) (hok : co < k)
    (hu : Diagram.cyclicOffset k β c₀ < Diagram.cyclicOffset k β cu)
    (ho : Diagram.cyclicOffset k β c₀ < Diagram.cyclicOffset k β co)
    (hb : cycBetween c₀ cu co) : Diagram.cyclicOffset k β cu < Diagram.cyclicOffset k β co := by
  unfold Diagram.cyclicOffset at *
  unfold cycBetween at hb
  split_ifs at hu ho ⊢ <;> rcases hb with ⟨hb1, hb2⟩ | ⟨hb1, hb2⟩ | ⟨hb1, hb2⟩ <;> linarith

namespace Diagram

variable (D : Diagram)

/-- A record-level based order of `D.record` is one of `(D.switch x).record` (same shadow, hence the
same circles, occurrences and successor, definitionally). -/
noncomputable def rbasingSwitch (x : D.Γ.Crossing) (B : Record.RBasing D.record) :
    Record.RBasing (D.switch x).record :=
  ⟨B.rank, B.rank_inj, B.base, B.base_comp, B.base_const⟩

/-- The count bridge: through the accepted `switchRecordIso` (identity on occurrences and circles) the
record-level switch step reads on `(D.switch x).record`. -/
theorem badCount_rbasingSwitch (B : Record.RBasing D.record) {v : D.Γ.Visit} (hv : B.IsBad v) :
    (D.rbasingSwitch v.1 B).badCount + 1 = B.badCount := by
  have h1 : (D.rbasingSwitch v.1 B).badCount =
      ((D.rbasingSwitch v.1 B).map (D.switchRecordIso v.1 v rfl)).badCount :=
    ((D.rbasingSwitch v.1 B).badCount_map _).symm
  have h2 : (D.rbasingSwitch v.1 B).map (D.switchRecordIso v.1 v rfl) = B.switch v := rfl
  rw [h1, h2]
  exact B.badCount_switch hv

/-- Sub-lemma of the bridge: an injective ℕ-rank of the components sorts into a permutation of `Fin c`
(`Finset.orderIsoOfFin` on the image). -/
theorem exists_rank_equiv {c : ℕ} (rank : Fin c → ℕ) (h : Function.Injective rank) :
    ∃ r : Fin c ≃ Fin c, ∀ i j, r i < r j ↔ rank i < rank j := by
  classical
  set S : Finset ℕ := Finset.univ.image rank with hS
  have hcard : S.card = c := by
    rw [hS, Finset.card_image_of_injective _ h, Finset.card_univ, Fintype.card_fin]
  let f : Fin c ≃o S := S.orderIsoOfFin hcard
  let g : Fin c → Fin c := fun i => f.symm ⟨rank i, Finset.mem_image_of_mem rank (Finset.mem_univ i)⟩
  have hg : Function.Injective g := by
    intro i j hij
    have := f.symm.injective hij
    exact h (Subtype.ext_iff.mp this)
  refine ⟨Equiv.ofBijective g (Finite.injective_iff_bijective.mp hg), fun i j => ?_⟩
  show f.symm ⟨rank i, _⟩ < f.symm ⟨rank j, _⟩ ↔ rank i < rank j
  rw [f.symm.lt_iff_lt]
  exact Subtype.mk_lt_mk

/-- Sub-lemma of the bridge: a nonsingular basepoint immediately before a given occurrence — every
other occurrence of that circle has a strictly larger forward offset (`Diagram.exists_basing_first`,
read on one component). -/
theorem exists_base_before (v : D.Γ.Visit) :
    ∃ b : TraversalPoint (D.Γ.comp (D.visitPt v).1).k,
      (∀ x, D.Γ.eval ⟨(D.visitPt v).1, b⟩ ≠ D.Γ.crossingPoint x) ∧
      ∀ w : D.Γ.Visit, (D.visitPt w).1 = (D.visitPt v).1 → w ≠ v →
        cyclicOffset (D.Γ.comp (D.visitPt v).1).k (traversalKey b) (traversalKey (D.visitPt v).2) <
          cyclicOffset (D.Γ.comp (D.visitPt v).1).k (traversalKey b) (traversalKey (D.visitPt w).2) := by
  obtain ⟨B₁, hB₁⟩ := D.exists_basing_first v
  refine ⟨B₁.base (D.visitPt v).1, B₁.nonsingular _, fun w hw hne => ?_⟩
  have h := hB₁ w hw hne
  simp only [basedRank] at h
  have key : ∀ (i j : Fin D.Γ.c) (hij : j = i) (p : TraversalPoint (D.Γ.comp j).k),
      cyclicOffset (D.Γ.comp j).k (traversalKey (B₁.base j)) (traversalKey p) =
        cyclicOffset (D.Γ.comp i).k (traversalKey (B₁.base i)) (traversalKey p) := by
    intro i j hij p
    subst hij
    rfl
  rw [key (D.visitPt v).1 (D.visitPt w).1 hw (D.visitPt w).2] at h
  exact h

/-- `exists_base_before` with the component named. -/
theorem exists_base_before' (i : Fin D.Γ.c) (v : D.Γ.Visit) (hv : D.compOf v = i) :
    ∃ b : TraversalPoint (D.Γ.comp i).k,
      (∀ x, D.Γ.eval ⟨i, b⟩ ≠ D.Γ.crossingPoint x) ∧
      ∀ w : D.Γ.Visit, D.compOf w = i → w ≠ v →
        cyclicOffset (D.Γ.comp i).k (traversalKey b) (traversalKey (D.visitPt v).2) <
          cyclicOffset (D.Γ.comp i).k (traversalKey b) (traversalKey (D.visitPt w).2) := by
  subst hv
  exact D.exists_base_before v

/-- Sub-lemma of the bridge: succ-iterates from the base occurrence follow the oriented cyclic order
(`ent`, `visitSucc_pow_ent`, `exists_ent`, `ent_add_sub`, `visitBetween_ent_iff`). -/
theorem visitBetween_of_pos_lt (B : Record.RBasing D.record) {u o : D.Γ.Visit}
    (hc : D.compOf u = D.compOf o) (h0 : 0 < B.pos u) (h : B.pos u < B.pos o) :
    D.VisitBetween (B.base u) u o := by
  have hbu : D.compOf (B.base u) = D.compOf u := B.base_comp u
  have hbo : B.base o = B.base u := B.base_const o u hc.symm
  have hi : 0 < (D.compList (D.compOf u)).length := by
    rw [D.compList_length]
    exact Finset.card_pos.mpr ⟨u, (D.mem_compVisits _ u).mpr rfl⟩
  obtain ⟨a₀, ha₀, hea₀⟩ := D.exists_ent (D.compOf u) hi (B.base u) hbu
  have hpow : ∀ n, (D.record.succ ^ n) (B.base u) = D.ent (D.compOf u) hi (a₀ + n) := by
    intro n
    rw [← hea₀]
    exact D.visitSucc_pow_ent (D.compOf u) hi n a₀
  have hlt : ∀ w : D.Γ.Visit, D.compOf w = D.compOf u → B.base w = B.base u →
      B.pos w < (D.compList (D.compOf u)).length := by
    intro w hw hbw
    obtain ⟨b, hb, heb⟩ := D.exists_ent (D.compOf u) hi w hw
    have : (D.record.succ ^ ((b + (D.compList (D.compOf u)).length - a₀) %
        (D.compList (D.compOf u)).length)) (B.base w) = w := by
      rw [hbw, hpow, D.ent_add_sub _ hi a₀ b ha₀ hb, heb]
    exact lt_of_le_of_lt (B.pos_le this) (Nat.mod_lt _ hi)
  have hu : u = D.ent (D.compOf u) hi (a₀ + B.pos u) := by
    rw [← hpow, B.pow_pos_base]
  have ho : o = D.ent (D.compOf u) hi (a₀ + B.pos o) := by
    rw [← hpow, ← hbo, B.pow_pos_base]
  have key := D.visitBetween_ent_iff (D.compOf u) hi a₀ (B.pos u) (B.pos o) h0
    (lt_of_le_of_lt (Nat.zero_le _) h) (hlt u rfl rfl) (hlt o hc.symm hbo)
  rw [hea₀, ← hu, ← ho] at key
  exact key.mpr h

/-- THE geometric bridge (rp:record-polynomial sm-3:1230-1235, lp:lm sm-3:946-949): a record-level
UNDER-first based order of `D.record` yields a `Diagram.Basing` under which `D` is UNDER-first.  Rank:
sort the injective ℕ-rank into a permutation of `Fin c`.  Basepoints: on a circle with occurrences,
a nonsingular point immediately before its base occurrence (`Diagram.exists_basing_first`); then the
offset order from that basepoint is the succ-iterate order from the base occurrence
(`visitBetween_ent_iff`, `cyclicOffset_lt_of_cycBetween`). -/
theorem exists_underFirst_of_rUnderFirst (B : Record.RBasing D.record) (h : B.RUnderFirst) :
    ∃ B' : D.Basing, D.UnderFirst B' := by
  classical
  obtain ⟨r, hr⟩ := exists_rank_equiv B.rank B.rank_inj
  have hbase : ∀ i : Fin D.Γ.c, ∃ b : TraversalPoint (D.Γ.comp i).k,
      (∀ x, D.Γ.eval ⟨i, b⟩ ≠ D.Γ.crossingPoint x) ∧
      ∀ u w : D.Γ.Visit, D.compOf u = i → D.compOf w = i → B.pos u < B.pos w →
        cyclicOffset (D.Γ.comp i).k (traversalKey b) (traversalKey (D.visitPt u).2) <
          cyclicOffset (D.Γ.comp i).k (traversalKey b) (traversalKey (D.visitPt w).2) := by
    intro i
    by_cases hi : ∃ v : D.Γ.Visit, D.compOf v = i
    · obtain ⟨v, hv⟩ := hi
      have hm : D.compOf (B.base v) = i := (B.base_comp v).trans hv
      obtain ⟨b, hb, hfirst⟩ := D.exists_base_before' i (B.base v) hm
      refine ⟨b, hb, fun u w hu hw hpos => ?_⟩
      have hbu : B.base u = B.base v := B.base_const u v (hu.trans hv.symm)
      have hbw : B.base w = B.base v := B.base_const w v (hw.trans hv.symm)
      have hwv : w ≠ B.base v := by
        intro hwv
        have : B.pos w = 0 := (B.pos_eq_zero_iff w).mpr (hbw.trans hwv.symm)
        omega
      have h2 := hfirst w hw hwv
      by_cases hu0 : B.pos u = 0
      · have hu' : u = B.base v := (hbu.symm.trans ((B.pos_eq_zero_iff u).mp hu0)).symm
        rw [hu']
        exact h2
      · have hvb : D.VisitBetween (B.base u) u w :=
          D.visitBetween_of_pos_lt B (hu.trans hw.symm) (Nat.pos_of_ne_zero hu0) hpos
        rw [hbu] at hvb
        have huv : u ≠ B.base v := by
          intro huv
          exact hu0 ((B.pos_eq_zero_iff u).mpr (hbu.trans huv.symm))
        have h1 := hfirst u hu huv
        have hku : (D.Γ.comp (D.visitPt u).1).k = (D.Γ.comp i).k := by
          rw [show (D.visitPt u).1 = i from hu]
        have hkw : (D.Γ.comp (D.visitPt w).1).k = (D.Γ.comp i).k := by
          rw [show (D.visitPt w).1 = i from hw]
        have huk : traversalKey (D.visitPt u).2 < ((D.Γ.comp i).k : ℝ) := by
          rw [← hku]; exact traversalKey_lt_card _
        have hwk : traversalKey (D.visitPt w).2 < ((D.Γ.comp i).k : ℝ) := by
          rw [← hkw]; exact traversalKey_lt_card _
        exact cyclicOffset_lt_of_cycBetween (traversalKey_nonneg _) huk (traversalKey_nonneg _) hwk
          h1 h2 hvb
    · obtain ⟨b, hb⟩ := D.exists_nonsingular_base i
      exact ⟨b, hb, fun u _ hu _ _ => absurd ⟨u, hu⟩ hi⟩
  choose base hbns hoff using hbase
  have hcast : ∀ (i j : Fin D.Γ.c) (hij : j = i) (p : TraversalPoint (D.Γ.comp j).k),
      cyclicOffset (D.Γ.comp j).k (traversalKey (base j)) (traversalKey p) =
        cyclicOffset (D.Γ.comp i).k (traversalKey (base i)) (traversalKey p) := by
    intro i j hij p
    subst hij
    rfl
  refine ⟨⟨r, base, hbns⟩, fun x => ?_⟩
  have hx : B.key (D.underVisit x) < B.key (D.overVisit x) := h (D.overVisit x) (D.overBit_overVisit x)
  unfold Record.RBasing.key at hx
  rw [Prod.Lex.toLex_lt_toLex] at hx
  rw [Prod.lex_def]
  rcases hx with hlt | ⟨heq, hpos⟩
  · left
    show r (D.visitPt (D.underVisit x)).1 < r (D.visitPt (D.overVisit x)).1
    exact (hr _ _).mpr hlt
  · right
    have hc : D.compOf (D.underVisit x) = D.compOf (D.overVisit x) := B.rank_inj heq
    refine ⟨?_, ?_⟩
    · show ((r (D.visitPt (D.underVisit x)).1 : Fin D.Γ.c) : ℕ) =
        ((r (D.visitPt (D.overVisit x)).1 : Fin D.Γ.c) : ℕ)
      exact congrArg (fun i => ((r i : Fin D.Γ.c) : ℕ)) hc
    · have hoff' := hoff (D.compOf (D.overVisit x)) (D.underVisit x) (D.overVisit x) hc rfl hpos
      show cyclicOffset (D.Γ.comp (D.visitPt (D.underVisit x)).1).k
          (traversalKey (base (D.visitPt (D.underVisit x)).1))
          (traversalKey (D.visitPt (D.underVisit x)).2) <
        cyclicOffset (D.Γ.comp (D.visitPt (D.overVisit x)).1).k
          (traversalKey (base (D.visitPt (D.overVisit x)).1))
          (traversalKey (D.visitPt (D.overVisit x)).2)
      rw [hcast (D.compOf (D.overVisit x)) (D.visitPt (D.underVisit x)).1 hc]
      exact hoff'

/-- **The `(N, b)` induction principle, based form** (lp:core sm-3:1082-1101; rp:record-polynomial
sm-3:1236-1240): to prove `Φ D B` for every diagram with every record-level based order, prove it
for UNDER-first based orders (`b = 0`) and prove the step at a bad occurrence `v` from `Φ` of the
switch (same based order, `b − 1`) and of every oriented smoothing at `v` with every based order
(`N − 1`).  Outer strong induction on `N = card D.Γ.Crossing`, inner induction on `b = badCount`. -/
theorem skein_induction_based (Φ : ∀ D : Diagram, Record.RBasing D.record → Prop)
    (init : ∀ (D : Diagram) (B : Record.RBasing D.record), B.RUnderFirst → Φ D B)
    (step : ∀ (D : Diagram) (B : Record.RBasing D.record) (v : D.Γ.Visit), B.IsBad v →
      Φ (D.switch v.1) (D.rbasingSwitch v.1 B) →
      (∀ (D₀ : Diagram) (B₀ : Record.RBasing D₀.record), IsOrientedSmoothing D v.1 D₀ → Φ D₀ B₀) →
      Φ D B) :
    ∀ (D : Diagram) (B : Record.RBasing D.record), Φ D B := by
  suffices h : ∀ (N b : ℕ) (D : Diagram) (B : Record.RBasing D.record),
      Fintype.card D.Γ.Crossing = N → B.badCount = b → Φ D B from
    fun D B => h _ _ D B rfl rfl
  intro N
  refine Nat.strong_induction_on N ?_
  intro N ihN b
  induction b with
  | zero =>
    intro D B _ hb
    exact init D B (B.badCount_eq_zero_iff.mp hb)
  | succ b ihb =>
    intro D B hN hb
    obtain ⟨v, hv⟩ := B.exists_isBad_of_badCount_ne_zero (by omega)
    refine step D B v hv ?_ ?_
    · refine ihb (D.switch v.1) (D.rbasingSwitch v.1 B) hN ?_
      have := D.badCount_rbasingSwitch B hv
      omega
    · intro D₀ B₀ h₀
      refine ihN (Fintype.card D₀.Γ.Crossing) ?_ _ D₀ B₀ rfl rfl
      have := h₀.card_crossing
      omega

/-- **The `(N, b)` induction principle, plain form**: the `b = 0` case is handed over with a
`Diagram.Basing` under which `D` is UNDER-first (exactly the hypothesis of `lmF_underFirst_init`),
and the step is stated at an arbitrary crossing. -/
theorem skein_induction (Φ : Diagram → Prop)
    (init : ∀ (D : Diagram) (B : D.Basing), D.UnderFirst B → Φ D)
    (step : ∀ (D : Diagram) (x : D.Γ.Crossing), Φ (D.switch x) →
      (∀ D₀ : Diagram, IsOrientedSmoothing D x D₀ → Φ D₀) → Φ D) :
    ∀ D : Diagram, Φ D := fun D =>
  skein_induction_based (fun D _ => Φ D)
    (fun D B hB => by
      obtain ⟨B', hB'⟩ := D.exists_underFirst_of_rUnderFirst B hB
      exact init D B' hB')
    (fun D _ v _ h1 h2 => step D v.1 h1 fun D₀ h₀ => h2 D₀ (Record.RBasing.default _) h₀)
    D (Record.RBasing.default _)

end Diagram

end Link

/-! ## §3. lp:core: the pieces -/

theorem P_congr {D D' : Diagram} (h : lmF D = lmF D') : P D = P D' := by
  unfold P; rw [h]

theorem P_planar {D D' : Diagram} (h : PlanarIsotopic D D') : P D = P D' := P_congr (lmF_planar h)
theorem P_reidemeister_I {D D' : Diagram} (h : RI D D') : P D = P D' := P_congr (lmF_reidemeister_I h)
theorem P_reidemeister_II {D D' : Diagram} (h : RII D D') : P D = P D' := P_congr (lmF_reidemeister_II h)
theorem P_reidemeister_III {D D' : Diagram} (h : RIII D D') : P D = P D' := P_congr (lmF_reidemeister_III h)

theorem P_circle {D : Diagram} (h : D.IsCrossingFreeCircle) : P D = 1 :=
  P_eq_one_of_lmF_eq_one (lmF_unknot h)

/-- The Gaussian evaluation `P^G_D = φ(F_D)` (eq. lp:gaussian). -/
noncomputable def G (D : Diagram) : RG := phi (T.toTG (lmF D))

/-- eq. lp:gaussian-skein multiplied by `−i` (sm-3:1073-1077): `a G₊ − a⁻¹ G₋ = z G₀` in `R_G`.
From `lmF_sourceSkein` through `φ ∘ T.toTG` and `neg_gaussI_smul_phi_l/lInv/m`. -/
theorem gaussI_alg_sq : algebraMap GaussianInt RG gaussI * algebraMap GaussianInt RG gaussI = -1 := by
  rw [← map_mul, gaussI_mul_gaussI, map_neg, map_one]

theorem phi_lInv' : phi TG.lInv = -(gaussI • RG.aInv) := by
  rw [phi_lInv, RG.aInv, AddMonoidAlgebra.smul_single, smul_eq_mul, mul_one, AddMonoidAlgebra.single_neg]

theorem phi_mInv' : phi TG.mInv = gaussI • RG.zInv := by
  rw [phi_mInv, RG.zInv, AddMonoidAlgebra.smul_single, smul_eq_mul, mul_one]

theorem G_skein {Dp Dm D0 : Diagram} (h : IsSkeinTriple Dp Dm D0) :
    RG.a * G Dp - RG.aInv * G Dm = RG.z * G D0 := by
  have h1 := congrArg (fun t : T => phi (T.toTG t)) (lmF_sourceSkein h)
  simp only [map_add, map_mul, map_zero, T.toTG_l, T.toTG_lInv, T.toTG_m, phi_l', phi_m', phi_lInv',
    Algebra.smul_def] at h1
  unfold G
  linear_combination (-(algebraMap GaussianInt RG gaussI)) * h1 +
    (RG.a * phi (T.toTG (lmF Dp)) - RG.aInv * phi (T.toTG (lmF Dm)) - RG.z * phi (T.toTG (lmF D0))) *
      gaussI_alg_sq

/-- The campaign skein for `P = re G` (eq. lp:skein): `reMap` is additive and `R`-linear
(`reMap_toRG_mul`), so the skein in `R_G` gives the skein of the real parts — no descent needed. -/
theorem P_skein {Dp Dm D0 : Diagram} (h : IsSkeinTriple Dp Dm D0) :
    R.a * P Dp - R.aInv * P Dm = R.z * P D0 := by
  have h1 := G_skein h
  unfold G at h1
  have h2 := congrArg reMap h1
  rw [map_sub, ← R.toRG_a, ← R.toRG_aInv, ← R.toRG_z, reMap_toRG_mul, reMap_toRG_mul,
    reMap_toRG_mul] at h2
  exact h2

/-- `P` satisfies the hypotheses of lp:coefficient-transport. -/
theorem P_rcompetitor : RCompetitor P where
  planar := fun _ _ h => P_planar h
  reidemeister_I := fun _ _ h => P_reidemeister_I h
  reidemeister_II := fun _ _ h => P_reidemeister_II h
  reidemeister_III := fun _ _ h => P_reidemeister_III h
  circle := fun _ h => P_circle h
  skein := fun _ _ _ h => P_skein h

/-- `homfly` satisfies the hypotheses of lp:coefficient-transport (lit:homfly's clauses). -/
theorem homfly_rcompetitor : RCompetitor homfly where
  planar := homfly_spec.planar
  reidemeister_I := homfly_spec.reidemeister_I
  reidemeister_II := homfly_spec.reidemeister_II
  reidemeister_III := homfly_spec.reidemeister_III
  circle := homfly_spec.circle
  skein := homfly_spec.skein


/-- "It equals `H_D`": lp:coefficient-transport identifies `P` and `homfly` (sm-3:1163-1171). -/
theorem P_eq_homfly (D : Diagram) : P D = homfly D :=
  congrFun (coefficient_transport P homfly P_rcompetitor homfly_rcompetitor) D

/-- "the numerator `l+l⁻¹` maps to `i(a−a⁻¹)` and the denominator `m` maps to `−iz`. Their quotient
with its preceding minus sign is `(a−a⁻¹)/z`" (sm-3:1078-1081): `φ(μ) = δ` in `R_G`. -/
theorem phi_toTG_mu : phi (T.toTG T.mu) = R.toRG R.delta := by
  rw [T.mu, R.delta]
  simp only [map_mul, map_neg, map_add, map_sub, T.toTG_l, T.toTG_lInv, T.toTG_mInv, R.toRG_a,
    R.toRG_aInv, R.toRG_zInv, phi_l', phi_lInv', phi_mInv', Algebra.smul_def]
  linear_combination (-(RG.a - RG.aInv) * RG.zInv) * gaussI_alg_sq

theorem P_of_lmF_eq_mu_pow {D : Diagram} {n : ℕ} (h : lmF D = T.mu ^ n) : P D = R.delta ^ n := by
  unfold P
  rw [h, map_pow, map_pow, phi_toTG_mu, ← map_pow, reMap_toRG]

/-- "Thus `P^G_D = δ^{c−1}` for every UNDER-first diagram" (sm-3:1081). -/
theorem P_underFirst_init (D : Diagram) (B : D.Basing) (h : D.UnderFirst B) :
    P D = R.delta ^ (D.componentCount - 1) :=
  P_of_lmF_eq_mu_pow (lmF_underFirst_init B h)

/-- Crossing-free diagrams: `P_D = δ^{c−1}` (lp:split-circle's second sentence). -/
theorem P_crossingFree {D : Diagram} (h : IsEmpty D.Γ.Crossing) :
    P D = R.delta ^ (D.componentCount - 1) :=
  P_of_lmF_eq_mu_pow (lmF_crossingFree h)

/-- lp:positive / lp:negative for `P` (sm-3:1104-1113), packaged for the inductions. -/
theorem P_recursion_pos {D : Diagram} {x : D.Γ.Crossing} {D₀ : Diagram} (h : IsOrientedSmoothing D x D₀)
    (hp : D.IsPositive x) : P D = R.aInv * R.aInv * P (D.switch x) + R.aInv * R.z * P D₀ :=
  skein_recursion_pos (fun _ _ _ ht => P_skein ht) h hp

theorem P_recursion_neg {D : Diagram} {x : D.Γ.Crossing} {D₀ : Diagram} (h : IsOrientedSmoothing D x D₀)
    (hp : ¬ D.IsPositive x) : P D = R.a * R.a * P (D.switch x) - R.a * R.z * P D₀ :=
  skein_recursion_neg (fun _ _ _ ht => P_skein ht) h hp

/-- lp:positive for `P^G` (sm-3:1104-1106): `G_D = a⁻² G_{D^sw} + a⁻¹ z G_{D⁰}` at a positive
crossing. -/
theorem G_recursion_pos {D : Diagram} {x : D.Γ.Crossing} {D₀ : Diagram} (h : IsOrientedSmoothing D x D₀)
    (hp : D.IsPositive x) : G D = RG.aInv * RG.aInv * G (D.switch x) + RG.aInv * RG.z * G D₀ := by
  have hs := G_skein (⟨x, hp, rfl, h⟩ : IsSkeinTriple D (D.switch x) D₀)
  linear_combination RG.aInv * hs - G D * RG.a_mul_aInv

/-- lp:negative for `P^G` (sm-3:1108-1113): `G_D = a² G_{D^sw} − a z G_{D⁰}` at a negative crossing. -/
theorem G_recursion_neg {D : Diagram} {x : D.Γ.Crossing} {D₀ : Diagram} (h : IsOrientedSmoothing D x D₀)
    (hp : ¬ D.IsPositive x) : G D = RG.a * RG.a * G (D.switch x) - RG.a * RG.z * G D₀ := by
  have hs := G_skein (⟨x, (D.switch_isPositive_self x).mpr hp, (D.switch_switch x).symm, h.switch⟩ :
    IsSkeinTriple (D.switch x) D D₀)
  linear_combination (-RG.a) * hs - G D * RG.a_mul_aInv

/-- "Thus `P^G_D = δ^{c−1}` for every UNDER-first diagram" (sm-3:1081), in `R_G`. -/
theorem G_underFirst (D : Diagram) (B : D.Basing) (h : D.UnderFirst B) :
    G D = R.toRG (R.delta ^ (D.componentCount - 1)) := by
  unfold G
  rw [lmF_underFirst_init B h, map_pow, map_pow, phi_toTG_mu, map_pow]

/-- **Integral descent** (sm-3:1119-1137), by `skein_induction`: `P^G_D` is the image of an element
of `M_c = z^{1−c} ℤ[a^{±1}, z²]`.  Init: `δ^{c−1} ∈ M_c` (`InSupportM.delta_pow`).  Step: the
switched term keeps `c` (`a_mul`, `aInv_mul`); the smoothed term has `c ± 1`
(`exists_smoothing_counts`; `z_mul` / `z_mul_of_pred`, eqs. lp:self-support / lp:mixed-support). -/
theorem G_descent (D : Diagram) : ∃ p : R, InSupportM D.componentCount p ∧ R.toRG p = G D := by
  refine Diagram.skein_induction
    (fun D => ∃ p : R, InSupportM D.componentCount p ∧ R.toRG p = G D) ?_ ?_ D
  · intro D B hB
    refine ⟨R.delta ^ (D.componentCount - 1), ?_, (G_underFirst D B hB).symm⟩
    have h := InSupportM.delta_pow (D.componentCount - 1)
    rwa [Nat.sub_add_cancel D.componentCount_pos] at h
  · intro D x ihsw ih
    obtain ⟨psw, hsw, hpsw⟩ := ihsw
    obtain ⟨D₀, h₀, -, hc, -, -⟩ := exists_smoothing_counts D x
    obtain ⟨p0, h0, hp0⟩ := ih D₀ h₀
    have hz : InSupportM D.componentCount (R.z * p0) := by
      rw [hc] at h0
      split_ifs at h0 with hself
      · exact h0.z_mul
      · exact InSupportM.z_mul_of_pred D.componentCount_pos h0
    by_cases hp : D.IsPositive x
    · refine ⟨R.aInv * R.aInv * psw + R.aInv * R.z * p0, ?_, ?_⟩
      · rw [mul_assoc, mul_assoc]
        exact (hsw.aInv_mul.aInv_mul).add hz.aInv_mul
      · rw [map_add, map_mul, map_mul, map_mul, map_mul, R.toRG_aInv, R.toRG_z, hpsw, hp0,
          G_recursion_pos h₀ hp]
    · refine ⟨R.a * R.a * psw - R.a * R.z * p0, ?_, ?_⟩
      · rw [mul_assoc, mul_assoc]
        exact (hsw.a_mul.a_mul).sub hz.a_mul
      · rw [map_sub, map_mul, map_mul, map_mul, map_mul, R.toRG_a, R.toRG_z, hpsw, hp0,
          G_recursion_neg h₀ hp]

theorem P_eq_reMap_G (D : Diagram) : P D = reMap (G D) := rfl

/-- eq. lp:gaussian: "There is consequently one `P_D ∈ R` with image `P^G_D`" (sm-3:1133-1135) —
`P_D` is the element of `R` whose image in `R_G` is `φ(F_D)`.  Consumes `lp_lm` only. -/
theorem P_gaussian (D : Diagram) : R.toRG (P D) = phi (T.toTG (lmF D)) := by
  obtain ⟨p, -, hp⟩ := G_descent D
  have : P D = p := by rw [P_eq_reMap_G, ← hp, reMap_toRG]
  rw [this, hp]
  rfl

/-- eq. lp:support, first half: "This proves support and integral descent simultaneously"
(sm-3:1135). -/
theorem P_support (D : Diagram) : InSupportM D.componentCount (P D) := by
  obtain ⟨p, hs, hp⟩ := G_descent D
  have : P D = p := by rw [P_eq_reMap_G, ← hp, reMap_toRG]
  rwa [this]

/-- sm-3:1145-1160: "every nonempty diagram specializes to 1" under `z ↦ a − a⁻¹`; by
`skein_induction` with `Φ D := specQ (P D) = 1`; init `specQ_delta`; step
`specQ_positive_identity` / `specQ_negative_identity`. -/
theorem P_specQ (D : Diagram) : specQ (P D) = 1 := by
  refine Diagram.skein_induction (fun D => specQ (P D) = 1) ?_ ?_ D
  · intro D B hB
    rw [P_underFirst_init D B hB, map_pow, specQ_delta, one_pow]
  · intro D x ih0 ih
    obtain ⟨D₀, h₀⟩ := exists_smoothing D x
    have h1 := ih D₀ h₀
    by_cases hp : D.IsPositive x
    · rw [P_recursion_pos h₀ hp]
      have e : specQ (R.aInv * R.aInv * P (D.switch x) + R.aInv * R.z * P D₀) =
          specQ (R.aInv * R.aInv) * specQ (P (D.switch x)) + specQ (R.aInv * R.z) * specQ (P D₀) := by
        simp only [map_add, map_mul]
      rw [e, ih0, h1, mul_one, mul_one, ← map_add, specQ_positive_identity]
    · rw [P_recursion_neg h₀ hp]
      have e : specQ (R.a * R.a * P (D.switch x) - R.a * R.z * P D₀) =
          specQ (R.a * R.a) * specQ (P (D.switch x)) - specQ (R.a * R.z) * specQ (P D₀) := by
        simp only [map_sub, map_mul]
      rw [e, ih0, h1, mul_one, mul_one, ← map_sub, specQ_negative_identity]

/-- "A zero element of `R` would specialize to zero. This proves `P_D ≠ 0`" (sm-3:1160-1161). -/
theorem P_ne_zero (D : Diagram) : P D ≠ 0 := fun h => by
  have := P_specQ D
  rw [h, map_zero] at this
  exact zero_ne_one this

/-- Uniqueness (sm-3:1136-1144): by `skein_induction` with `Φ D := Q D = P D`; init: both are
`δ^{c−1}`; step: the same solved recurrence for `Q` (`skein_recursion_pos/neg`) and for `P`. -/
theorem P_unique (Q : Diagram → R)
    (hs : ∀ Dp Dm D0 : Diagram, IsSkeinTriple Dp Dm D0 → R.a * Q Dp - R.aInv * Q Dm = R.z * Q D0)
    (hi : ∀ (D : Diagram) (B : D.Basing), D.UnderFirst B → Q D = R.delta ^ (D.componentCount - 1)) :
    Q = P := by
  funext D
  refine Diagram.skein_induction (fun D => Q D = P D) ?_ ?_ D
  · intro D B hB
    rw [hi D B hB, P_underFirst_init D B hB]
  · intro D x ih0 ih
    obtain ⟨D₀, h₀⟩ := exists_smoothing D x
    by_cases hp : D.IsPositive x
    · rw [skein_recursion_pos hs h₀ hp, P_recursion_pos h₀ hp, ih0, ih D₀ h₀]
    · rw [skein_recursion_neg hs h₀ hp, P_recursion_neg h₀ hp, ih0, ih D₀ h₀]

/-- "knot evaluations are polynomials in `z²`, with no negative `z` exponents": `M_1 = ℤ[a^{±1}, z²]`. -/
theorem P_knot_support (D : Diagram) (hc : D.componentCount = 1) (d k : ℤ)
    (hk : coeffAt d k (P D) ≠ 0) : ∃ j : ℕ, k = 2 * (j : ℤ) := by
  have hs := P_support D
  rw [hc] at hs
  obtain ⟨j, hj⟩ := hs (d, k) (Finsupp.mem_support_iff.mpr hk)
  exact ⟨j, by simpa using hj⟩

/-! ## §4. rp:record-polynomial and lc:presentations -/

namespace Link.Diagram

variable {D D' : Diagram}

/-- Signs are part of the record: the crossing of `Φ v` has the sign of the crossing of `v`. -/
theorem sign_eq_of_recordIso (ι : RecordIso D.record D'.record) (v : D.Γ.Visit) :
    D'.sign (ι.Φ v).1 = D.sign v.1 :=
  ι.sgn_eq v

theorem isPositive_iff_of_recordIso (ι : RecordIso D.record D'.record) (v : D.Γ.Visit) :
    D'.IsPositive (ι.Φ v).1 ↔ D.IsPositive v.1 := by
  rw [D'.isPositive_iff_sign_eq_one, D.isPositive_iff_sign_eq_one, sign_eq_of_recordIso]

/-- "the switched diagrams ... still have isomorphic decorated records" (sm-3:1249-1252):
`switchRecordIso` on both sides around `RecordIso.switch`. -/
noncomputable def recordIso_switch (ι : RecordIso D.record D'.record) (v : D.Γ.Visit) :
    RecordIso (D.switch v.1).record (D'.switch (ι.Φ v).1).record :=
  ((D.switchRecordIso v.1 v rfl).trans (ι.switch v)).trans (D'.switchRecordIso (ι.Φ v).1 (ι.Φ v) rfl).symm

/-- "The resulting actual smoothed diagrams thus have isomorphic decorated records" (sm-3:1253-1262):
`exists_smoothing_record_visit` on both sides around `RecordIso.smooth`. -/
theorem exists_smoothing_pair (ι : RecordIso D.record D'.record) (v : D.Γ.Visit) :
    ∃ (D₀ D₀' : Diagram), IsOrientedSmoothing D v.1 D₀ ∧ IsOrientedSmoothing D' (ι.Φ v).1 D₀' ∧
      Nonempty (RecordIso D₀.record D₀'.record) := by
  obtain ⟨D₀, h₀, ⟨ι₀⟩⟩ := exists_smoothing_record_visit D v.1 v rfl
  obtain ⟨D₀', h₀', ⟨ι₀'⟩⟩ := exists_smoothing_record_visit D' (ι.Φ v).1 (ι.Φ v) rfl
  exact ⟨D₀, D₀', h₀, h₀', ⟨(ι₀.trans (ι.smooth v)).trans ι₀'.symm⟩⟩

/-- The `b = 0` case for a partner diagram: a record-level UNDER-first based order transports along
the record isomorphism (`rUnderFirst_map`) and the bridge gives a `Diagram.Basing` on `D'`. -/
theorem exists_underFirst_of_recordIso (ι : RecordIso D.record D'.record) (B : Record.RBasing D.record)
    (h : B.RUnderFirst) : ∃ B' : D'.Basing, D'.UnderFirst B' :=
  D'.exists_underFirst_of_rUnderFirst (B.map ι) ((B.rUnderFirst_map ι).mpr h)

theorem componentCount_eq_of_recordIso (ι : RecordIso D.record D'.record) :
    D.componentCount = D'.componentCount := by
  rw [← D.record_componentCount, ← D'.record_componentCount]
  exact ι.componentCount_eq

end Link.Diagram

/-- rp:record-polynomial, main clause (sm-3:1230-1290): by `skein_induction_based` with
`Φ D B := ∀ D', Nonempty (RecordIso D.record D'.record) → lmF D = lmF D'`.  Init: both values are
`μ^{c−1}` (`exists_underFirst_of_rUnderFirst`, `exists_underFirst_of_recordIso`,
`componentCount_eq_of_recordIso`).  Step at a bad `v`: `recordIso_switch` gives equal switched
values, `exists_smoothing_pair` equal smoothed values, `isPositive_iff_of_recordIso` the common sign
case, and `T.eq_of_skein_l` / `T.eq_of_skein_lInv` cancel the common terms of the two source skeins. -/
theorem lmF_eq_of_recordIso (D D' : Diagram) (h : Nonempty (RecordIso D.record D'.record)) :
    lmF D = lmF D' := by
  revert D' h
  refine Diagram.skein_induction_based
    (fun D _ => ∀ D' : Diagram, Nonempty (RecordIso D.record D'.record) → lmF D = lmF D') ?_ ?_ D
    (Record.RBasing.default _)
  · rintro D B hB D' ⟨ι⟩
    obtain ⟨B₁, hB₁⟩ := D.exists_underFirst_of_rUnderFirst B hB
    obtain ⟨B₂, hB₂⟩ := Diagram.exists_underFirst_of_recordIso ι B hB
    rw [lmF_underFirst_init B₁ hB₁, lmF_underFirst_init B₂ hB₂,
      Diagram.componentCount_eq_of_recordIso ι]
  · rintro D B v _ ihsw ihsm D' ⟨ι⟩
    have hsw : lmF (D.switch v.1) = lmF (D'.switch (ι.Φ v).1) :=
      ihsw (D'.switch (ι.Φ v).1) ⟨Diagram.recordIso_switch ι v⟩
    obtain ⟨D₀, D₀', h₀, h₀', hι₀⟩ := Diagram.exists_smoothing_pair ι v
    have hsm : lmF D₀ = lmF D₀' := ihsm D₀ (Record.RBasing.default _) h₀ D₀' hι₀
    by_cases hp : D.IsPositive v.1
    · have hp' : D'.IsPositive (ι.Φ v).1 := (Diagram.isPositive_iff_of_recordIso ι v).mpr hp
      have e1 := lmF_sourceSkein (⟨v.1, hp, rfl, h₀⟩ : IsSkeinTriple D (D.switch v.1) D₀)
      have e2 := lmF_sourceSkein
        (⟨(ι.Φ v).1, hp', rfl, h₀'⟩ : IsSkeinTriple D' (D'.switch (ι.Φ v).1) D₀')
      rw [← hsw, ← hsm] at e2
      exact T.eq_of_skein_l e1 e2
    · have hp' : ¬ D'.IsPositive (ι.Φ v).1 :=
        fun h' => hp ((Diagram.isPositive_iff_of_recordIso ι v).mp h')
      have e1 := lmF_sourceSkein (⟨v.1, (D.switch_isPositive_self v.1).mpr hp,
        (D.switch_switch v.1).symm, h₀.switch⟩ : IsSkeinTriple (D.switch v.1) D D₀)
      have e2 := lmF_sourceSkein (⟨(ι.Φ v).1, (D'.switch_isPositive_self _).mpr hp',
        (D'.switch_switch _).symm, h₀'.switch⟩ : IsSkeinTriple (D'.switch (ι.Φ v).1) D' D₀')
      rw [← hsw, ← hsm] at e2
      exact T.eq_of_skein_lInv e1 e2

/-! ## §5. lp:split-circle: adding a crossing-free circle at the record level -/

namespace Link.Record

variable (ρ : Record)

/-- The record with one crossing-free circle added ("adding one simple crossing-free component having
no crossings with `D`", sm-3:1181-1182): a new component `none`, everything else unchanged. -/
def addFree : Record where
  comps := Option ρ.comps
  M := ρ.M
  comp v := some (ρ.comp v)
  succ := ρ.succ
  pair := ρ.pair
  isOver := ρ.isOver
  sgn := ρ.sgn
  succ_comp v := congrArg some (ρ.succ_comp v)
  succ_cycle v w h := ρ.succ_cycle v w (Option.some_injective _ h)
  pair_ne := ρ.pair_ne
  pair_invol := ρ.pair_invol
  bit_pair := ρ.bit_pair
  sgn_pair := ρ.sgn_pair
  sgn_ne := ρ.sgn_ne

@[simp] theorem addFree_M : ρ.addFree.M = ρ.M := rfl
@[simp] theorem addFree_sgn (v : ρ.M) : ρ.addFree.sgn v = ρ.sgn v := rfl

theorem componentCount_addFree : ρ.addFree.componentCount = ρ.componentCount + 1 := by
  show Fintype.card (Option ρ.comps) = Fintype.card ρ.comps + 1
  exact Fintype.card_option

/-- "Switching ... does not touch the extra component" (sm-3:1198-1200). -/
theorem addFree_switch (x : ρ.M) : ρ.addFree.switch x = (ρ.switch x).addFree := rfl

/-- The crossing-free circles of `ρ.addFree`: the new circle and those of `ρ`. -/
def freeCompAddFreeEquiv : ρ.addFree.FreeComp ≃ Option ρ.FreeComp where
  toFun c := match c with
    | ⟨none, _⟩ => none
    | ⟨some c, h⟩ => some ⟨c, fun v hv => h v (congrArg some hv)⟩
  invFun c := match c with
    | none => ⟨none, fun _ h => Option.some_ne_none _ h⟩
    | some ⟨c, hc⟩ => ⟨some c, fun v h => hc v (Option.some_injective _ h)⟩
  left_inv := by rintro ⟨_ | c, h⟩ <;> rfl
  right_inv := by rintro (_ | ⟨c, hc⟩) <;> rfl

/-- "smoothing does not touch the extra component": the smoothing of `ρ.addFree` is the smoothing of
`ρ` with the free circle added (the added circle is a `FreeComp` of both). -/
noncomputable def addFreeSmoothIso (x : ρ.M) : RecordIso (ρ.addFree.smooth x) ((ρ.smooth x).addFree) where
  e := (Equiv.sumCongr (Equiv.refl _) (freeCompAddFreeEquiv ρ)).trans
    ((Equiv.sumCongr (Equiv.refl _) (Equiv.optionEquivSumPUnit.{0, 0} ρ.FreeComp)).trans
      ((Equiv.sumAssoc _ _ PUnit.{1}).symm.trans (Equiv.optionEquivSumPUnit.{0, 0} _).symm))
  Φ := Equiv.refl _
  comp_eq _ := rfl
  succ_eq _ := rfl
  pair_eq _ := rfl
  bit_eq _ := rfl
  sgn_eq _ := rfl

/-- A named record isomorphism extends to the records with a circle added. -/
def _root_.SM.Link.RecordIso.addFree {ρ ρ' : Record} (ι : RecordIso ρ ρ') :
    RecordIso ρ.addFree ρ'.addFree where
  e := Equiv.optionCongr ι.e
  Φ := ι.Φ
  comp_eq v := by
    show some (ρ'.comp (ι.Φ v)) = Equiv.optionCongr ι.e (some (ρ.comp v))
    simpa using ι.comp_eq v
  succ_eq := ι.succ_eq
  pair_eq := ι.pair_eq
  bit_eq := ι.bit_eq
  sgn_eq := ι.sgn_eq

/-- Erasing a crossing-free circle `j` and adding a free circle back gives an isomorphic record
(the bridge from `IsSplitCircleAddition` through `Diagram.restrictRecordIso`). -/
noncomputable def eraseFreeAddFreeIso [DecidableEq ρ.comps] {j : ρ.comps} (hj : ∀ v, ρ.comp v ≠ j) :
    RecordIso ρ ((ρ.restrict (Finset.univ.erase j)).addFree) :=
  have hkeep : ∀ w, ρ.RestrictKeep (Finset.univ.erase j) w := fun w =>
    ⟨Finset.mem_erase.mpr ⟨hj w, Finset.mem_univ _⟩,
      Finset.mem_erase.mpr ⟨hj (ρ.pair w), Finset.mem_univ _⟩⟩
  { e := (Equiv.optionSubtypeNe j).symm.trans
      (Equiv.optionCongr (Equiv.subtypeEquivRight (fun c => by simp [Finset.mem_erase])))
    Φ := (Equiv.subtypeUnivEquiv hkeep).symm
    comp_eq := fun v => by
      show some (⟨ρ.comp v, _⟩ : {c // c ∈ Finset.univ.erase j}) =
        Equiv.optionCongr (Equiv.subtypeEquivRight _) ((Equiv.optionSubtypeNe j).symm (ρ.comp v))
      rw [Equiv.optionSubtypeNe_symm_of_ne (hj v)]
      rfl
    succ_eq := fun v => by
      show (⟨ρ.succ v, hkeep _⟩ : {w // ρ.RestrictKeep (Finset.univ.erase j) w}) =
        (ρ.restrict (Finset.univ.erase j)).succ ⟨v, hkeep v⟩
      exact Subtype.ext (ρ.restrict_succ_val_of_keep _ ⟨v, hkeep v⟩ (hkeep _)).symm
    pair_eq := fun _ => rfl
    bit_eq := fun _ => rfl
    sgn_eq := fun _ => rfl }

/-- "put the added component last with any basepoint. This adds no crossing encounter, so `N` and `b`
are unchanged" (sm-3:1193-1195). -/
def RBasing.addFree {ρ : Record} (B : RBasing ρ) : RBasing ρ.addFree where
  rank := fun c => Option.elim c 0 (fun c => B.rank c + 1)
  rank_inj := by
    rintro (_ | c) (_ | c') h
    · rfl
    · exact absurd h (by simp)
    · exact absurd h (by simp)
    · simp only [Option.elim_some] at h
      exact congrArg some (B.rank_inj (Nat.succ_injective h))
  base := B.base
  base_comp v := congrArg some (B.base_comp v)
  base_const v w h := B.base_const v w (Option.some_injective _ h)

theorem RBasing.pos_addFree {ρ : Record} (B : RBasing ρ) (v : ρ.M) : B.addFree.pos v = B.pos v := rfl

theorem RBasing.key_addFree_lt_iff {ρ : Record} (B : RBasing ρ) (v w : ρ.M) :
    B.addFree.key v < B.addFree.key w ↔ B.key v < B.key w := by
  show toLex (B.rank (ρ.comp v) + 1, B.pos v) < toLex (B.rank (ρ.comp w) + 1, B.pos w) ↔
    toLex (B.rank (ρ.comp v), B.pos v) < toLex (B.rank (ρ.comp w), B.pos w)
  rw [Prod.Lex.toLex_lt_toLex, Prod.Lex.toLex_lt_toLex]
  omega

theorem RBasing.rUnderFirst_addFree {ρ : Record} (B : RBasing ρ) : B.addFree.RUnderFirst ↔ B.RUnderFirst := by
  constructor
  · intro h v hv
    exact (B.key_addFree_lt_iff (ρ.pair v) v).mp (h v hv)
  · intro h v hv
    exact (B.key_addFree_lt_iff (ρ.pair v) v).mpr (h v hv)

end Link.Record

/-- lp:split-circle, record form (sm-3:1191-1210): by `skein_induction_based` on `D` with
`Φ D B := ∀ D', Nonempty (RecordIso D'.record D.record.addFree) → P D' = δ P D`.  Init: `P D = δ^{c−1}`
and, transporting `B.addFree` (UNDER-first) along the iso, `P D' = δ^{c}`.  Step at a bad `v`: the
switch and the smoothing commute with `addFree` (`addFree_switch`, `addFreeSmoothIso`,
`RecordIso.addFree`), so the two smaller values of `D'` are `δ` times those of `D`; factor `δ` out of
the solved recurrence (`P_recursion_pos/neg`, signs equal by `addFree_sgn` and `sgn_eq`). -/
theorem P_addFree (D D' : Diagram) (h : Nonempty (RecordIso D'.record D.record.addFree)) :
    P D' = R.delta * P D := by
  revert D' h
  refine Diagram.skein_induction_based
    (fun D _ => ∀ D' : Diagram, Nonempty (RecordIso D'.record D.record.addFree) →
      P D' = R.delta * P D) ?_ ?_ D (Record.RBasing.default _)
  · rintro D B hB D' ⟨ι⟩
    obtain ⟨B₁, hB₁⟩ := D.exists_underFirst_of_rUnderFirst B hB
    have hB' : (B.addFree.map ι.symm).RUnderFirst :=
      (B.addFree.rUnderFirst_map ι.symm).mpr ((B.rUnderFirst_addFree).mpr hB)
    obtain ⟨B₂, hB₂⟩ := D'.exists_underFirst_of_rUnderFirst _ hB'
    rw [P_underFirst_init D B₁ hB₁, P_underFirst_init D' B₂ hB₂]
    have hc : D'.componentCount = D.componentCount + 1 := by
      rw [← D'.record_componentCount, ι.componentCount_eq, Record.componentCount_addFree,
        D.record_componentCount]
    rw [hc, Nat.add_sub_cancel, ← pow_succ', Nat.sub_add_cancel D.componentCount_pos]
  · rintro D B v _ ihsw ihsm D' ⟨ι⟩
    obtain ⟨v', hΦ⟩ : ∃ v' : D'.Γ.Visit, ι.Φ v' = v := ⟨ι.Φ.symm v, ι.Φ.apply_symm_apply v⟩
    have ιsw : RecordIso (D'.switch v'.1).record (D.switch v.1).record.addFree := by
      refine (D'.switchRecordIso v'.1 v' rfl).trans ?_
      refine (ι.switch v').trans ?_
      rw [hΦ, Record.addFree_switch]
      exact (D.switchRecordIso v.1 v rfl).symm.addFree
    have hsw : P (D'.switch v'.1) = R.delta * P (D.switch v.1) := ihsw _ ⟨ιsw⟩
    obtain ⟨D₀, h₀, ⟨ι₀⟩⟩ := exists_smoothing_record_visit D v.1 v rfl
    obtain ⟨D₀', h₀', ⟨ι₀'⟩⟩ := exists_smoothing_record_visit D' v'.1 v' rfl
    have ιsm : RecordIso D₀'.record D₀.record.addFree := by
      refine ι₀'.trans ?_
      refine (ι.smooth v').trans ?_
      rw [hΦ]
      exact (D.record.addFreeSmoothIso v).trans ι₀.symm.addFree
    have hsm : P D₀' = R.delta * P D₀ := ihsm D₀ (Record.RBasing.default _) h₀ D₀' ⟨ιsm⟩
    have hsign : D'.sign v'.1 = D.sign v.1 := by
      have := ι.sgn_eq v'
      rw [hΦ] at this
      exact this.symm
    by_cases hp : D.IsPositive v.1
    · have hp' : D'.IsPositive v'.1 := by
        rw [D'.isPositive_iff_sign_eq_one, hsign, ← D.isPositive_iff_sign_eq_one]; exact hp
      rw [P_recursion_pos h₀' hp', P_recursion_pos h₀ hp, hsw, hsm]
      ring
    · have hp' : ¬ D'.IsPositive v'.1 := by
        rw [D'.isPositive_iff_sign_eq_one, hsign, ← D.isPositive_iff_sign_eq_one]; exact hp
      rw [P_recursion_neg h₀' hp', P_recursion_neg h₀ hp, hsw, hsm]
      ring

/-- eq. lp:split for the relational `IsSplitCircleAddition`: the restriction to the other components
is a reparametrization of `D` (`P_planar`), and its record with a circle added is the record of `D'`
(`eraseFreeAddFreeIso`, `restrictRecordIso`). -/
theorem P_split_circle (D D' : Diagram) (h : IsSplitCircleAddition D D') : P D' = R.delta * P D := by
  obtain ⟨j, hj, hne, hr⟩ := h
  have h1 : P D = P (D'.restrict (Finset.univ.erase j) hne) := P_planar (PlanarIsotopic.of_reparam hr)
  have hj' : ∀ v : D'.Γ.Visit, D'.record.comp v ≠ j := fun v => hj v.1 v.2.val v.2.2
  have ι : RecordIso D'.record ((D'.restrict (Finset.univ.erase j) hne).record.addFree) :=
    (D'.record.eraseFreeAddFreeIso hj').trans (D'.restrictRecordIso _ hne).symm.addFree
  rw [P_addFree _ _ ⟨ι⟩, h1]

/-! ## §7. The four row theorems of this module (bundles verbatim from work/drafts/*_statement.lean); the fifth row of the block, mp:stack, lives in SM/Stack.lean -/

/-- rp:record-polynomial as printed. -/
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
  P_eq := fun D D' h => P_congr (lmF_eq_of_recordIso D D' h)
  coeff_eq := fun D D' h d k => by rw [P_congr (lmF_eq_of_recordIso D D' h)]

/-- lp:core as printed, one field per printed sentence. -/
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
  gaussian := P_gaussian
  skein := fun _ _ _ h => P_skein h
  underFirst_init := P_underFirst_init
  eq_homfly := P_eq_homfly
  unique := P_unique
  support := P_support
  ne_zero := P_ne_zero
  circle := fun _ h => P_circle h
  knot_support := P_knot_support
  planar := fun _ _ h => P_planar h
  reidemeister_I := fun _ _ h => P_reidemeister_I h
  reidemeister_II := fun _ _ h => P_reidemeister_II h
  reidemeister_III := fun _ _ h => P_reidemeister_III h

/-- lp:split-circle as printed. -/
structure SplitCircleData : Prop where
  /-- eq. lp:split: `P_{D'} = δ P_D`. -/
  split : ∀ D D' : Diagram, IsSplitCircleAddition D D' → P D' = R.delta * P D
  /-- "In particular every crossing-free `c`-component diagram has value `δ^{c−1}`." -/
  crossing_free : ∀ D : Diagram, IsEmpty D.Γ.Crossing → P D = R.delta ^ (D.componentCount - 1)

theorem split_circle : SplitCircleData where
  split := P_split_circle
  crossing_free := fun _ h => P_crossingFree h

/-- lc:presentations as printed: "Their evaluations by the same local LM construction agree." -/
theorem presentations (D D' : Diagram) (h : Nonempty (RecordIso D.record D'.record)) : P D = P D' :=
  P_congr (lmF_eq_of_recordIso D D' h)



end SM
