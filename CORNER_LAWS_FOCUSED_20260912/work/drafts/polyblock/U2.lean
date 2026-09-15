import SM.Smoothing
import SM.CoefficientTransport
import SM.LocalPolynomial
import SM.SingleCrossing

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

/-! ## §6. mp:stack (sm-3:1494-1536)

Design (PLAN_FINAL.md §6).  `skein_induction_based` with the predicate
`Φ D B := ∀ q blk hblk, BlockOrdered D blk → B.BlockCompatible blk → P D = δ^{q−1} ∏ P (D_i)`,
started at a block-compatible based order (`exists_blockCompatible_rbasing`), so that every bad
occurrence is internal to its block (`isBad_internal`; "All between-block crossings are first
encountered under", sm-3:1515).  Init (`stack_init`): the block restrictions of an UNDER-first
diagram are UNDER-first (`restrict_underFirst`, diagram level: same basepoints, same traversal
coordinates).  Step (`stack_step`): the switch is the same switch in its block restriction and
invisible to the other blocks (`blockRestrict_switch_of_internal/external`); the smoothing carries
the blocks (`smoothBlock`, `blocks_of_smoothing`) and its block restrictions are the smoothing of the
old block restriction (`restrictSmoothIso`) resp. unchanged (`restrictSmoothDisjointIso`), read
through `restrictRecordIso`, `RecordIso.restrict` and lc:presentations; `solvedR_of_skein` on `D`
and on the block restriction, `solvedR_mul_left` factors the common terms.  The record-level
commutations are stated with the target block `B'` characterised by two hypotheses (graft from
Skeleton A), so that they are provable independently of the block bookkeeping. -/

open SM.Link in
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

/-- The component set of block `i`. -/
abbrev blockSet (D : Diagram) {q : ℕ} (blk : Fin D.Γ.c → Fin q) (i : Fin q) : Finset (Fin D.Γ.c) :=
  Finset.univ.filter (fun c => blk c = i)

theorem mem_blockSet_iff (D : Diagram) {q : ℕ} (blk : Fin D.Γ.c → Fin q) (i : Fin q) (c : Fin D.Γ.c) :
    c ∈ blockSet D blk i ↔ blk c = i := by
  simp [blockSet]

theorem blockSet_nonempty (D : Diagram) {q : ℕ} (blk : Fin D.Γ.c → Fin q)
    (hblk : Function.Surjective blk) (i : Fin q) : (blockSet D blk i).Nonempty := by
  obtain ⟨c, hc⟩ := hblk i; exact ⟨c, by simp [blockSet, hc]⟩

theorem blockRestrict_eq (D : Diagram) {q : ℕ} (blk : Fin D.Γ.c → Fin q)
    (hblk : Function.Surjective blk) (i : Fin q) :
    blockRestrict D blk hblk i = D.restrict (blockSet D blk i) (blockSet_nonempty D blk hblk i) := rfl

/-! ### 6.1 Record level: block order, block-compatible based orders, bad crossings are internal
("Order components block by block", sm-3:1514) -/

namespace Link.Record

variable (ρ : Record)

/-- Record-level block order: at a crossing between different blocks the occurrence on the smaller
block is the under occurrence. -/
def RBlockOrdered {q : ℕ} (β : ρ.comps → Fin q) : Prop :=
  ∀ v, β (ρ.comp v) < β (ρ.comp (ρ.pair v)) → ρ.isOver v = false

/-- A based order compatible with a block function: earlier blocks come first (exists: rank
`β c * card comps + equivFin c`). -/
def RBasing.BlockCompatible {ρ : Record} {q : ℕ} (B : RBasing ρ) (β : ρ.comps → Fin q) : Prop :=
  ∀ c c', β c < β c' → B.rank c < B.rank c'

theorem exists_blockCompatible_rbasing {q : ℕ} (β : ρ.comps → Fin q) :
    ∃ B : RBasing ρ, B.BlockCompatible β := by
  set N := Fintype.card ρ.comps with hN
  let e := Fintype.equivFin ρ.comps
  have hlt : ∀ c c', β c < β c' → (β c).val * N + (e c).val < (β c').val * N + (e c').val := by
    intro c c' h
    have h1 : (β c).val * N + (e c).val < (β c).val * N + N := Nat.add_lt_add_left (e c).isLt _
    have h2 : (β c).val * N + N ≤ (β c').val * N := by
      rw [← Nat.succ_mul]
      exact Nat.mul_le_mul_right N h
    exact lt_of_lt_of_le h1 (h2.trans (Nat.le_add_right _ _))
  refine ⟨{ (RBasing.default ρ) with
    rank := fun c => (β c).val * N + (e c).val
    rank_inj := ?_ }, fun c c' h => hlt c c' h⟩
  intro c c' h
  rcases lt_trichotomy (β c) (β c') with hb | hb | hb
  · exact absurd h (ne_of_lt (hlt c c' hb))
  · have h' : (β c).val * N + (e c).val = (β c).val * N + (e c').val := by
      have : (β c').val = (β c).val := by rw [hb]
      simpa [this] using h
    exact e.injective (Fin.ext (Nat.add_left_cancel h'))
  · exact absurd h (ne_of_gt (hlt c' c hb))

/-- "All between-block crossings are first encountered under" (sm-3:1515): a bad occurrence of a
block-compatible based order of a block-ordered record is internal to its block. -/
theorem RBasing.isBad_internal {ρ : Record} {q : ℕ} {β : ρ.comps → Fin q} (hβ : ρ.RBlockOrdered β)
    {B : RBasing ρ} (hB : B.BlockCompatible β) {v : ρ.M} (hv : B.IsBad v) :
    β (ρ.comp v) = β (ρ.comp (ρ.pair v)) := by
  rcases lt_trichotomy (β (ρ.comp v)) (β (ρ.comp (ρ.pair v))) with h | h | h
  · have := hβ v h
    rw [hv.1] at this
    exact absurd this (by decide)
  · exact h
  · have hr : B.rank (ρ.comp (ρ.pair v)) < B.rank (ρ.comp v) := hB _ _ h
    have hk : B.key (ρ.pair v) < B.key v := by
      unfold RBasing.key
      rw [Prod.Lex.toLex_lt_toLex]
      exact Or.inl hr
    exact absurd (lt_trans hk hv.2) (lt_irrefl _)

/-! ### 6.2 Record level: the blocks of the smoothing ("Every new component inherits the same block
as the strands smoothed", sm-3:1527) -/

section U2Beta
open Equiv

/-- One step of the reconnected successor keeps any block function that agrees on the two circles
of the smoothed crossing. -/
theorem beta_comp_reconnect_eq {γ : Sort*} (β : ρ.comps → γ) (v : ρ.M)
    (hv : β (ρ.comp v) = β (ρ.comp (ρ.pair v))) (u : ρ.M) :
    β (ρ.comp (ρ.reconnect v u)) = β (ρ.comp u) := by
  by_cases h1 : u = v
  · subst h1; rw [reconnect_apply_self, ρ.succ_comp, hv]
  by_cases h2 : u = ρ.pair v
  · subst h2; rw [reconnect_apply_pair, ρ.succ_comp, hv]
  · rw [ρ.reconnect_apply_of_ne v h1 h2, ρ.succ_comp]

theorem beta_comp_reconnect_pow_eq {γ : Sort*} (β : ρ.comps → γ) (v : ρ.M)
    (hv : β (ρ.comp v) = β (ρ.comp (ρ.pair v))) (u : ρ.M) (n : ℕ) :
    β (ρ.comp (((ρ.reconnect v) ^ n) u)) = β (ρ.comp u) := by
  induction n with
  | zero => rw [pow_zero, Perm.one_apply]
  | succ n ih => rw [pow_succ', Perm.mul_apply, ρ.beta_comp_reconnect_eq β v hv, ih]

end U2Beta

/-- Any function of the circles that agrees on the two circles of the smoothed crossing is constant
along the cycles of the reconnected successor `s₁ = s ∘ swap v (τ v)`: one step is
`reconnect v u = succ (swap v (pair v) u)` (`u = v ↦ comp (succ (pair v)) = comp (pair v)`,
`u = pair v` symmetric, otherwise `comp (succ u) = comp u`), then `zpow` induction on
`Perm.SameCycle` (as `sameCycle_map_iff`). -/
theorem beta_comp_eq_of_reconnect_sameCycle {γ : Sort*} (β : ρ.comps → γ) (v : ρ.M)
    (hv : β (ρ.comp v) = β (ρ.comp (ρ.pair v))) {u w : ρ.M}
    (h : (ρ.reconnect v).SameCycle u w) : β (ρ.comp u) = β (ρ.comp w) := by
  obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
  rw [← hn, ρ.beta_comp_reconnect_pow_eq β v hv]

/-- The block function of the smoothing: a cycle of `s₁` inherits the block of any occurrence it
carries (well defined by `beta_comp_eq_of_reconnect_sameCycle`), a crossing-free circle keeps its
block.  Transparent `Quotient.lift`: both computation rules are `rfl`. -/
def smoothBlock {γ : Type*} (β : ρ.comps → γ) (v : ρ.M)
    (hv : β (ρ.comp v) = β (ρ.comp (ρ.pair v))) : (ρ.smooth v).comps → γ :=
  Sum.elim
    (Quotient.lift (fun u : ρ.M => β (ρ.comp u))
      (fun _ _ h => ρ.beta_comp_eq_of_reconnect_sameCycle β v hv h))
    (fun f => β f.1)

@[simp] theorem smoothBlock_inl {γ : Type*} (β : ρ.comps → γ) (v : ρ.M)
    (hv : β (ρ.comp v) = β (ρ.comp (ρ.pair v))) (u : ρ.M) :
    ρ.smoothBlock β v hv (Sum.inl (Quotient.mk _ u)) = β (ρ.comp u) := rfl

@[simp] theorem smoothBlock_inr {γ : Type*} (β : ρ.comps → γ) (v : ρ.M)
    (hv : β (ρ.comp v) = β (ρ.comp (ρ.pair v))) (f : ρ.FreeComp) :
    ρ.smoothBlock β v hv (Sum.inr f) = β f.1 := rfl

end Link.Record

/-! ### 6.3 Record level: restriction versus smoothing (sm-3:1528-1531 "The restriction of the
smoothed diagram in that block is exactly the oriented smoothing of the old block restriction; the
other restrictions do not change") -/

namespace Link

/-- First return to `p` and then to `q` is first return to `p ∧ q`.  Both sides are `(f ^ n) m` for
the least `n > 0` with `p ∧ q`; the `k`-th power of `firstReturn f p` is `f ^ (sum of return times)`
(`firstReturn_pow_of_pow`, `firstReturn_apply`, `returnTime_spec`, `returnTime_min`); minimality on
both sides via `returnTime_eq_iff`. -/
theorem firstReturn_firstReturn {α : Type*} [Fintype α] (f : Equiv.Perm α) (p q : α → Prop)
    [DecidablePred p] [DecidablePred q] (m : {m : {m // p m} // q m.1}) :
    ((firstReturn (firstReturn f p) (fun m => q m.1)) m).1.1 =
      ((firstReturn f (fun m => p m ∧ q m)) ⟨m.1.1, m.1.2, m.2⟩).1 := by
  sorry

/-- First return commutes with a transposition of two `p`-points.  Pointwise: for `u ∉ {a, b}`,
`(f * swap a b)^n u = f^n u` while no intermediate point is a `p`-point (`a, b` are `p`-points), so
the return times agree (`mul_swap_apply_of_ne_of_ne`); for `u = a`: `(f * swap a b) a = f b`, then
as before from `f b`, matching `firstReturn f p ⟨b⟩`; symmetric for `b`. -/
theorem firstReturn_mul_swap {α : Type*} [Fintype α] [DecidableEq α] (f : Equiv.Perm α)
    (p : α → Prop) [DecidablePred p] (a b : α) (ha : p a) (hb : p b) :
    firstReturn (f * Equiv.swap a b) p =
      firstReturn f p * Equiv.swap (⟨a, ha⟩ : {m // p m}) ⟨b, hb⟩ := by
  sorry

section U2Perm
open Equiv

/-- The value of a first return depends only on the predicate up to `↔` and on the powers of the
permutation along the orbit of the starting point (decidability instances by unification). -/
theorem firstReturn_val_congr {α : Type*} [Fintype α] (f g : Perm α) (p p' : α → Prop)
    {_ : DecidablePred p} {_ : DecidablePred p'} (hp : ∀ m, p m ↔ p' m) (m : {m // p m})
    (hfg : ∀ n : ℕ, (f ^ n) m.1 = (g ^ n) m.1) :
    (firstReturn f p m).1 = (firstReturn g p' ⟨m.1, (hp _).mp m.2⟩).1 := by
  rw [firstReturn_apply, firstReturn_apply]
  have : returnTime f p m.1 m.2 = returnTime g p' m.1 ((hp _).mp m.2) := by
    rw [returnTime_eq_iff]
    refine ⟨⟨returnTime_pos _ _ _ _, ?_⟩, ?_⟩
    · rw [hfg, hp]; exact returnTime_spec _ _ _ _
    · rintro j hj ⟨hj0, hpj⟩
      rw [hfg, hp] at hpj
      exact returnTime_min _ _ _ _ hj0 hj hpj
  rw [this, hfg]

end U2Perm

namespace Record

variable (ρ : Record)

section U2Record
open Equiv

/-- Away from the two circles of the smoothed crossing the reconnected successor is the old one,
power by power. -/
theorem reconnect_pow_eq_succ_pow (x u : ρ.M) (h1 : ρ.comp u ≠ ρ.comp x)
    (h2 : ρ.comp u ≠ ρ.comp (ρ.pair x)) (n : ℕ) :
    ((ρ.reconnect x) ^ n) u = (ρ.succ ^ n) u := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', Perm.mul_apply, ih, pow_succ', Perm.mul_apply]
    apply ρ.reconnect_apply_of_ne
    · intro hc; exact h1 (by rw [← hc, ρ.comp_pow])
    · intro hc; exact h2 (by rw [← hc, ρ.comp_pow])

/-- On the other circles the `s₁`-cycles are the old circles. -/
theorem reconnect_sameCycle_iff_of_comp_ne (x u : ρ.M) (h1 : ρ.comp u ≠ ρ.comp x)
    (h2 : ρ.comp u ≠ ρ.comp (ρ.pair x)) (w : ρ.M) :
    (ρ.reconnect x).SameCycle u w ↔ ρ.comp u = ρ.comp w := by
  constructor
  · intro h
    obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
    rw [← hn, ρ.reconnect_pow_eq_succ_pow x u h1 h2, ρ.comp_pow]
  · intro h
    obtain ⟨n, hn⟩ := (ρ.succ_cycle u w h).exists_nat_pow_eq
    exact ⟨n, by rw [zpow_natCast, ρ.reconnect_pow_eq_succ_pow x u h1 h2, hn]⟩

/-- An occurrence on one of the two circles of the smoothed crossing lies on the `s₁`-cycle of `x`
or on that of `τ x`. -/
theorem reconnect_sameCycle_self_or_pair (x u : ρ.M)
    (h : ρ.comp u = ρ.comp x ∨ ρ.comp u = ρ.comp (ρ.pair x)) :
    (ρ.reconnect x).SameCycle u x ∨ (ρ.reconnect x).SameCycle u (ρ.pair x) := by
  rcases h with h | h
  · exact ρ.reconnect_sameCycle_or x u h
  · have := ρ.reconnect_sameCycle_or (ρ.pair x) u h
    rw [ρ.reconnect_pair, ρ.pair_invol] at this
    exact this.symm

theorem reconnect_sameCycle_out (x u : ρ.M) :
    (ρ.reconnect x).SameCycle (Quotient.mk (Perm.SameCycle.setoid (ρ.reconnect x)) u).out u :=
  Quotient.mk_out (s := Perm.SameCycle.setoid (ρ.reconnect x)) u

/-! #### Shared bookkeeping for the restriction of a smoothing -/

section RestrictSmooth

variable (x : ρ.M) (B : Finset ρ.comps) (B' : Finset (ρ.smooth x).comps)
  (hB' : ∀ u : ρ.M, (Sum.inl (Quotient.mk _ u) : (ρ.smooth x).comps) ∈ B' ↔ ρ.comp u ∈ B)

include hB' in
/-- The kept occurrences of the restricted smoothing are the kept occurrences of `ρ`. -/
theorem smooth_restrictKeep_iff (w : (ρ.smooth x).M) :
    (ρ.smooth x).RestrictKeep B' w ↔ ρ.RestrictKeep B w.1 := by
  show (Sum.inl (Quotient.mk _ w.1) ∈ B' ∧ Sum.inl (Quotient.mk _ (ρ.pair w.1)) ∈ B') ↔ _
  rw [hB', hB']
  exact Iff.rfl

include hB' in
theorem mem_of_inl_mem {q : Quotient (Perm.SameCycle.setoid (ρ.reconnect x))}
    (h : (Sum.inl q : (ρ.smooth x).comps) ∈ B') : ρ.comp q.out ∈ B :=
  (hB' _).mp (by rw [Quotient.out_eq]; exact h)

end RestrictSmooth

/-! #### External crossing: restriction of the smoothing = old restriction -/

section Disjoint

variable (x : ρ.M) (B : Finset ρ.comps) (hx : ρ.comp x ∉ B) (hx' : ρ.comp (ρ.pair x) ∉ B)

include hx hx' in
theorem comp_ne_of_mem_disjoint {u : ρ.M} (hu : ρ.comp u ∈ B) :
    ρ.comp u ≠ ρ.comp x ∧ ρ.comp u ≠ ρ.comp (ρ.pair x) :=
  ⟨fun h => hx (h ▸ hu), fun h => hx' (h ▸ hu)⟩

include hx hx' in
theorem smoothKeep_of_comp_mem_disjoint {u : ρ.M} (hu : ρ.comp u ∈ B) : ρ.SmoothKeep x u := by
  rw [smoothKeep_iff]
  exact ⟨fun h => hx (h ▸ hu), fun h => hx' (h ▸ hu)⟩

include hx hx' in
/-- On a `B`-circle the `s₁`-cycles are the old circles. -/
theorem reconnect_sameCycle_iff_disjoint {u : ρ.M} (hu : ρ.comp u ∈ B) (w : ρ.M) :
    (ρ.reconnect x).SameCycle u w ↔ ρ.comp u = ρ.comp w :=
  ρ.reconnect_sameCycle_iff_of_comp_ne x u (ρ.comp_ne_of_mem_disjoint x B hx hx' hu).1
    (ρ.comp_ne_of_mem_disjoint x B hx hx' hu).2 w

include hx hx' in
theorem comp_out_eq_disjoint {u : ρ.M} (hu : ρ.comp u ∈ B) :
    ρ.comp (Quotient.mk (Perm.SameCycle.setoid (ρ.reconnect x)) u).out = ρ.comp u :=
  ((ρ.reconnect_sameCycle_iff_disjoint x B hx hx' hu _).mp
    (ρ.reconnect_sameCycle_out x u).symm).symm

end Disjoint

/-- Circles of the restricted smoothing → circles of the restriction (external crossing). -/
noncomputable def rdFwd (x : ρ.M) (B : Finset ρ.comps) (B' : Finset (ρ.smooth x).comps)
    (hB' : ∀ u : ρ.M, (Sum.inl (Quotient.mk _ u) : (ρ.smooth x).comps) ∈ B' ↔ ρ.comp u ∈ B)
    (hB'' : ∀ f : ρ.FreeComp, (Sum.inr f : (ρ.smooth x).comps) ∈ B' ↔ f.1 ∈ B)
    (s : ((ρ.smooth x).restrict B').comps) : (ρ.restrict B).comps :=
  match s with
  | ⟨Sum.inl q, h⟩ => ⟨ρ.comp q.out, ρ.mem_of_inl_mem x B B' hB' h⟩
  | ⟨Sum.inr f, h⟩ => ⟨f.1, (hB'' f).mp h⟩

open scoped Classical in
/-- Circles of the restriction → circles of the restricted smoothing (external crossing). -/
noncomputable def rdBwd (x : ρ.M) (B : Finset ρ.comps) (B' : Finset (ρ.smooth x).comps)
    (hB' : ∀ u : ρ.M, (Sum.inl (Quotient.mk _ u) : (ρ.smooth x).comps) ∈ B' ↔ ρ.comp u ∈ B)
    (hB'' : ∀ f : ρ.FreeComp, (Sum.inr f : (ρ.smooth x).comps) ∈ B' ↔ f.1 ∈ B)
    (c : (ρ.restrict B).comps) : ((ρ.smooth x).restrict B').comps :=
  if h : ∃ u, ρ.comp u = c.1 then
    ⟨Sum.inl (Quotient.mk _ (Classical.choose h)),
      (hB' _).mpr (by rw [Classical.choose_spec h]; exact c.2)⟩
  else ⟨Sum.inr ⟨c.1, fun u hu => h ⟨u, hu⟩⟩, (hB'' _).mpr c.2⟩

section Disjoint

variable (x : ρ.M) (B : Finset ρ.comps) (hx : ρ.comp x ∉ B) (hx' : ρ.comp (ρ.pair x) ∉ B)
  (B' : Finset (ρ.smooth x).comps)
  (hB' : ∀ u : ρ.M, (Sum.inl (Quotient.mk _ u) : (ρ.smooth x).comps) ∈ B' ↔ ρ.comp u ∈ B)
  (hB'' : ∀ f : ρ.FreeComp, (Sum.inr f : (ρ.smooth x).comps) ∈ B' ↔ f.1 ∈ B)

theorem rdBwd_pos (c : (ρ.restrict B).comps) (h : ∃ u, ρ.comp u = c.1) :
    ρ.rdBwd x B B' hB' hB'' c =
      ⟨Sum.inl (Quotient.mk _ (Classical.choose h)),
        (hB' _).mpr (by rw [Classical.choose_spec h]; exact c.2)⟩ :=
  dite_eq_left h

theorem rdBwd_neg (c : (ρ.restrict B).comps) (h : ¬ ∃ u, ρ.comp u = c.1) :
    ρ.rdBwd x B B' hB' hB'' c = ⟨Sum.inr ⟨c.1, fun u hu => h ⟨u, hu⟩⟩, (hB'' _).mpr c.2⟩ :=
  dite_eq_right h

include hx hx' in
theorem rdBwd_rdFwd (s : ((ρ.smooth x).restrict B').comps) :
    ρ.rdBwd x B B' hB' hB'' (ρ.rdFwd x B B' hB' hB'' s) = s := by
  rcases s with ⟨q | f, h⟩
  · have hmem : ρ.comp q.out ∈ B := ρ.mem_of_inl_mem x B B' hB' h
    have hex : ∃ u, ρ.comp u = ρ.comp q.out := ⟨q.out, rfl⟩
    refine (ρ.rdBwd_pos x B B' hB' hB'' ⟨ρ.comp q.out, hmem⟩ hex).trans ?_
    apply Subtype.ext
    apply congrArg Sum.inl
    refine (Quotient.sound ?_).trans (Quotient.out_eq q)
    exact ((ρ.reconnect_sameCycle_iff_disjoint x B hx hx' hmem _).mpr
      (Classical.choose_spec hex).symm).symm
  · have hex : ¬ ∃ u, ρ.comp u = f.1 := fun ⟨u, hu⟩ => f.2 u hu
    exact (ρ.rdBwd_neg x B B' hB' hB'' ⟨f.1, (hB'' f).mp h⟩ hex).trans rfl

include hx hx' in
theorem rdFwd_rdBwd (c : (ρ.restrict B).comps) :
    ρ.rdFwd x B B' hB' hB'' (ρ.rdBwd x B B' hB' hB'' c) = c := by
  by_cases hex : ∃ u, ρ.comp u = c.1
  · refine (congrArg (ρ.rdFwd x B B' hB' hB'') (ρ.rdBwd_pos x B B' hB' hB'' c hex)).trans ?_
    apply Subtype.ext
    exact (ρ.comp_out_eq_disjoint x B hx hx'
      (by rw [Classical.choose_spec hex]; exact c.2)).trans (Classical.choose_spec hex)
  · exact (congrArg (ρ.rdFwd x B B' hB' hB'') (ρ.rdBwd_neg x B B' hB' hB'' c hex)).trans rfl

end Disjoint

/-- The circle bijection of `restrictSmoothDisjointIso`. -/
noncomputable def rdCompsEquiv (x : ρ.M) (B : Finset ρ.comps) (hx : ρ.comp x ∉ B)
    (hx' : ρ.comp (ρ.pair x) ∉ B) (B' : Finset (ρ.smooth x).comps)
    (hB' : ∀ u : ρ.M, (Sum.inl (Quotient.mk _ u) : (ρ.smooth x).comps) ∈ B' ↔ ρ.comp u ∈ B)
    (hB'' : ∀ f : ρ.FreeComp, (Sum.inr f : (ρ.smooth x).comps) ∈ B' ↔ f.1 ∈ B) :
    ((ρ.smooth x).restrict B').comps ≃ (ρ.restrict B).comps where
  toFun := ρ.rdFwd x B B' hB' hB''
  invFun := ρ.rdBwd x B B' hB' hB''
  left_inv := ρ.rdBwd_rdFwd x B hx hx' B' hB' hB''
  right_inv := ρ.rdFwd_rdBwd x B hx hx' B' hB' hB''

/-- The occurrence bijection of `restrictSmoothDisjointIso`. -/
def rdOccEquiv (x : ρ.M) (B : Finset ρ.comps) (hx : ρ.comp x ∉ B)
    (hx' : ρ.comp (ρ.pair x) ∉ B) (B' : Finset (ρ.smooth x).comps)
    (hB' : ∀ u : ρ.M, (Sum.inl (Quotient.mk _ u) : (ρ.smooth x).comps) ∈ B' ↔ ρ.comp u ∈ B) :
    ((ρ.smooth x).restrict B').M ≃ (ρ.restrict B).M where
  toFun w := ⟨w.1.1, (ρ.smooth_restrictKeep_iff x B B' hB' w.1).mp w.2⟩
  invFun u := ⟨⟨u.1, ρ.smoothKeep_of_comp_mem_disjoint x B hx hx' u.2.1⟩,
    (ρ.smooth_restrictKeep_iff x B B' hB' _).mpr u.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- `restrictSmoothDisjointIso` with the block hypotheses stated on `(ρ.smooth x).comps`. -/
theorem restrictSmoothDisjointIso' (x : ρ.M) (B : Finset ρ.comps) (hx : ρ.comp x ∉ B)
    (hx' : ρ.comp (ρ.pair x) ∉ B) (B' : Finset (ρ.smooth x).comps)
    (hB' : ∀ u : ρ.M, (Sum.inl (Quotient.mk _ u) : (ρ.smooth x).comps) ∈ B' ↔ ρ.comp u ∈ B)
    (hB'' : ∀ f : ρ.FreeComp, (Sum.inr f : (ρ.smooth x).comps) ∈ B' ↔ f.1 ∈ B) :
    Nonempty (RecordIso ((ρ.smooth x).restrict B') (ρ.restrict B)) := by
  refine ⟨{ e := ρ.rdCompsEquiv x B hx hx' B' hB' hB''
            Φ := ρ.rdOccEquiv x B hx hx' B' hB'
            comp_eq := ?_, succ_eq := ?_, pair_eq := ?_, bit_eq := ?_, sgn_eq := ?_ }⟩
  · intro w
    apply Subtype.ext
    show ρ.comp w.1.1 = ρ.comp (Quotient.mk _ w.1.1).out
    exact (ρ.comp_out_eq_disjoint x B hx hx'
      ((ρ.smooth_restrictKeep_iff x B B' hB' w.1).mp w.2).1).symm
  · intro w
    apply Subtype.ext
    have hK : ρ.RestrictKeep B w.1.1 := (ρ.smooth_restrictKeep_iff x B B' hB' w.1).mp w.2
    have hne := ρ.comp_ne_of_mem_disjoint x B hx hx' hK.1
    show (firstReturn (ρ.smooth x).succ ((ρ.smooth x).RestrictKeep B') w).1.1 =
      (firstReturn ρ.succ (ρ.RestrictKeep B) ⟨w.1.1, hK⟩).1
    calc (firstReturn (ρ.smooth x).succ ((ρ.smooth x).RestrictKeep B') w).1.1
        = (firstReturn (ρ.smooth x).succ (fun m => ρ.RestrictKeep B m.1) ⟨w.1, hK⟩).1.1 :=
          congrArg Subtype.val (firstReturn_val_congr _ _ _ _
            (ρ.smooth_restrictKeep_iff x B B' hB') w (fun _ => rfl))
      _ = (firstReturn (ρ.reconnect x) (fun m => ρ.SmoothKeep x m ∧ ρ.RestrictKeep B m)
            ⟨w.1.1, w.1.2, hK⟩).1 :=
          firstReturn_firstReturn (ρ.reconnect x) (ρ.SmoothKeep x) (ρ.RestrictKeep B) ⟨w.1, hK⟩
      _ = (firstReturn ρ.succ (ρ.RestrictKeep B) ⟨w.1.1, hK⟩).1 :=
          firstReturn_val_congr _ _ _ _
            (fun m => ⟨fun h => h.2, fun h => ⟨ρ.smoothKeep_of_comp_mem_disjoint x B hx hx' h.1, h⟩⟩)
            ⟨w.1.1, w.1.2, hK⟩ (ρ.reconnect_pow_eq_succ_pow x w.1.1 hne.1 hne.2)
  · intro w; rfl
  · intro w; rfl
  · intro w; rfl

/-! #### Internal crossing: restriction of the smoothing = smoothing of the restriction.
The smoothed occurrence is a variable `v' : (ρ.restrict B).M` (so that every statement is
well typed without unfolding `restrict`); `v'.1` is the occurrence of `ρ`. -/

section Internal

variable (B : Finset ρ.comps) (v' : (ρ.restrict B).M)

theorem restrictKeep_pair_of_keep : ρ.RestrictKeep B (ρ.pair v'.1) :=
  (ρ.restrictKeep_pair_iff B v'.1).mpr v'.2

/-- `(restrict B).reconnect v'` is the first return of `reconnect v'.1` to the kept occurrences
(U1: `firstReturn_mul_swap`). -/
theorem restrict_reconnect_eq :
    (ρ.restrict B).reconnect v' = firstReturn (ρ.reconnect v'.1) (ρ.RestrictKeep B) := by
  unfold reconnect
  exact (firstReturn_mul_swap ρ.succ (ρ.RestrictKeep B) v'.1 (ρ.pair v'.1) v'.2
    (ρ.restrictKeep_pair_of_keep B v')).symm

theorem restrict_reconnect_sameCycle_iff (a b : (ρ.restrict B).M) :
    ((ρ.restrict B).reconnect v').SameCycle a b ↔ (ρ.reconnect v'.1).SameCycle a.1 b.1 := by
  rw [ρ.restrict_reconnect_eq B v']
  exact firstReturn_sameCycle_iff _ _ a b

theorem restrict_reconnect_sameCycle_out (a : (ρ.restrict B).M) :
    ((ρ.restrict B).reconnect v').SameCycle
      (Quotient.mk (Perm.SameCycle.setoid ((ρ.restrict B).reconnect v')) a).out a :=
  Quotient.mk_out (s := Perm.SameCycle.setoid ((ρ.restrict B).reconnect v')) a

/-- The retained occurrences of the smoothed restriction are the retained occurrences of `ρ`. -/
theorem restrict_smoothKeep_iff (w : (ρ.restrict B).M) :
    (ρ.restrict B).SmoothKeep v' w ↔ ρ.SmoothKeep v'.1 w.1 :=
  ((ρ.restrict B).smoothKeep_iff v' w).trans
    ((and_congr (not_congr Subtype.ext_iff) (not_congr Subtype.ext_iff)).trans
      (ρ.smoothKeep_iff v'.1 w.1).symm)

/-- An `s₁`-cycle without kept occurrence avoids the two circles of the smoothed crossing (those
carry the kept occurrences `v'`, `τ v'`). -/
theorem comp_ne_of_not_hasKept {u : ρ.M}
    (hk : ¬ ∃ u', (ρ.reconnect v'.1).SameCycle u u' ∧ ρ.RestrictKeep B u') :
    ρ.comp u ≠ ρ.comp v'.1 ∧ ρ.comp u ≠ ρ.comp (ρ.pair v'.1) := by
  have key : ¬ (ρ.comp u = ρ.comp v'.1 ∨ ρ.comp u = ρ.comp (ρ.pair v'.1)) := by
    intro h
    rcases ρ.reconnect_sameCycle_self_or_pair v'.1 u h with hc | hc
    · exact hk ⟨v'.1, hc, v'.2⟩
    · exact hk ⟨ρ.pair v'.1, hc, ρ.restrictKeep_pair_of_keep B v'⟩
  exact ⟨fun h => key (Or.inl h), fun h => key (Or.inr h)⟩

theorem sameCycle_iff_of_not_hasKept {u : ρ.M}
    (hk : ¬ ∃ u', (ρ.reconnect v'.1).SameCycle u u' ∧ ρ.RestrictKeep B u') (w : ρ.M) :
    (ρ.reconnect v'.1).SameCycle u w ↔ ρ.comp u = ρ.comp w :=
  ρ.reconnect_sameCycle_iff_of_comp_ne v'.1 u (ρ.comp_ne_of_not_hasKept B v' hk).1
    (ρ.comp_ne_of_not_hasKept B v' hk).2 w

/-- A crossing-free circle of the restriction is not one of the two circles of the (internal)
smoothed crossing. -/
theorem comp_ne_of_free (c : (ρ.restrict B).FreeComp) :
    c.1.1 ≠ ρ.comp v'.1 ∧ c.1.1 ≠ ρ.comp (ρ.pair v'.1) :=
  ⟨fun h => c.2 v' (Subtype.ext h.symm),
    fun h => c.2 ⟨ρ.pair v'.1, ρ.restrictKeep_pair_of_keep B v'⟩ (Subtype.ext h.symm)⟩

theorem sameCycle_iff_of_free (c : (ρ.restrict B).FreeComp) {u : ρ.M} (hu : ρ.comp u = c.1.1)
    (w : ρ.M) : (ρ.reconnect v'.1).SameCycle u w ↔ ρ.comp u = ρ.comp w :=
  ρ.reconnect_sameCycle_iff_of_comp_ne v'.1 u (hu ▸ (ρ.comp_ne_of_free B v' c).1)
    (hu ▸ (ρ.comp_ne_of_free B v' c).2) w

theorem not_hasKept_of_free (c : (ρ.restrict B).FreeComp) {u : ρ.M} (hu : ρ.comp u = c.1.1) :
    ¬ ∃ u', (ρ.reconnect v'.1).SameCycle u u' ∧ ρ.RestrictKeep B u' := by
  rintro ⟨u', hc, hk⟩
  have : ρ.comp u' = c.1.1 := ((ρ.sameCycle_iff_of_free B v' c hu u').mp hc).symm.trans hu
  exact c.2 ⟨u', hk⟩ (Subtype.ext this)

theorem comp_out_eq_of_free (c : (ρ.restrict B).FreeComp) {u : ρ.M} (hu : ρ.comp u = c.1.1) :
    ρ.comp (Quotient.mk (Perm.SameCycle.setoid (ρ.reconnect v'.1)) u).out = c.1.1 :=
  (((ρ.sameCycle_iff_of_free B v' c hu _).mp (ρ.reconnect_sameCycle_out v'.1 u).symm).symm).trans hu

/-- The circle of an `s₁`-cycle without kept occurrence, as a crossing-free circle of the
restriction. -/
noncomputable def rsFreeOfNotKept {u : ρ.M} (hu : ρ.comp u ∈ B)
    (hk : ¬ ∃ u', (ρ.reconnect v'.1).SameCycle u u' ∧ ρ.RestrictKeep B u') :
    (ρ.restrict B).FreeComp :=
  ⟨⟨ρ.comp u, hu⟩, fun w hw => hk ⟨w.1,
    (ρ.sameCycle_iff_of_not_hasKept B v' hk w.1).mpr (congrArg Subtype.val hw).symm, w.2⟩⟩

end Internal

/-- A crossing-free circle of `ρ` in `B` as a crossing-free circle of the restriction. -/
def rsFreeOfFree (B : Finset ρ.comps) (f : ρ.FreeComp) (hf : f.1 ∈ B) : (ρ.restrict B).FreeComp :=
  ⟨⟨f.1, hf⟩, fun w hw => f.2 w.1 (congrArg Subtype.val hw)⟩

open scoped Classical in
/-- Circles of the restricted smoothing → circles of the smoothed restriction (internal crossing):
an `s₁`-cycle carrying a kept occurrence goes to its cycle of the restricted `s₁`; one without
goes to the crossing-free circle it fills. -/
noncomputable def rsFwd (B : Finset ρ.comps) (v' : (ρ.restrict B).M)
    (B' : Finset (ρ.smooth v'.1).comps)
    (hB' : ∀ u : ρ.M, (Sum.inl (Quotient.mk _ u) : (ρ.smooth v'.1).comps) ∈ B' ↔ ρ.comp u ∈ B)
    (hB'' : ∀ f : ρ.FreeComp, (Sum.inr f : (ρ.smooth v'.1).comps) ∈ B' ↔ f.1 ∈ B)
    (s : ((ρ.smooth v'.1).restrict B').comps) : ((ρ.restrict B).smooth v').comps :=
  match s with
  | ⟨Sum.inl q, h⟩ =>
    if hk : ∃ u', (ρ.reconnect v'.1).SameCycle q.out u' ∧ ρ.RestrictKeep B u' then
      Sum.inl (Quotient.mk _
        (⟨Classical.choose hk, (Classical.choose_spec hk).2⟩ : (ρ.restrict B).M))
    else Sum.inr (ρ.rsFreeOfNotKept B v' (ρ.mem_of_inl_mem v'.1 B B' hB' h) hk)
  | ⟨Sum.inr f, h⟩ => Sum.inr (ρ.rsFreeOfFree B f ((hB'' f).mp h))

open scoped Classical in
/-- Circles of the smoothed restriction → circles of the restricted smoothing. -/
noncomputable def rsBwd (B : Finset ρ.comps) (v' : (ρ.restrict B).M)
    (B' : Finset (ρ.smooth v'.1).comps)
    (hB' : ∀ u : ρ.M, (Sum.inl (Quotient.mk _ u) : (ρ.smooth v'.1).comps) ∈ B' ↔ ρ.comp u ∈ B)
    (hB'' : ∀ f : ρ.FreeComp, (Sum.inr f : (ρ.smooth v'.1).comps) ∈ B' ↔ f.1 ∈ B)
    (c : ((ρ.restrict B).smooth v').comps) : ((ρ.smooth v'.1).restrict B').comps :=
  match c with
  | Sum.inl q => ⟨Sum.inl (Quotient.mk _ q.out.1), (hB' _).mpr q.out.2.1⟩
  | Sum.inr c =>
    if h : ∃ u, ρ.comp u = c.1.1 then
      ⟨Sum.inl (Quotient.mk _ (Classical.choose h)),
        (hB' _).mpr (by rw [Classical.choose_spec h]; exact c.1.2)⟩
    else ⟨Sum.inr ⟨c.1.1, fun u hu => h ⟨u, hu⟩⟩, (hB'' _).mpr c.1.2⟩

section Internal

variable (B : Finset ρ.comps) (v' : (ρ.restrict B).M) (B' : Finset (ρ.smooth v'.1).comps)
  (hB' : ∀ u : ρ.M, (Sum.inl (Quotient.mk _ u) : (ρ.smooth v'.1).comps) ∈ B' ↔ ρ.comp u ∈ B)
  (hB'' : ∀ f : ρ.FreeComp, (Sum.inr f : (ρ.smooth v'.1).comps) ∈ B' ↔ f.1 ∈ B)

theorem rsFwd_inl_pos (q : Quotient (Perm.SameCycle.setoid (ρ.reconnect v'.1)))
    (h : (Sum.inl q : (ρ.smooth v'.1).comps) ∈ B')
    (hk : ∃ u', (ρ.reconnect v'.1).SameCycle q.out u' ∧ ρ.RestrictKeep B u') :
    ρ.rsFwd B v' B' hB' hB'' ⟨Sum.inl q, h⟩ =
      Sum.inl (Quotient.mk _
        (⟨Classical.choose hk, (Classical.choose_spec hk).2⟩ : (ρ.restrict B).M)) :=
  dite_eq_left hk

theorem rsFwd_inl_neg (q : Quotient (Perm.SameCycle.setoid (ρ.reconnect v'.1)))
    (h : (Sum.inl q : (ρ.smooth v'.1).comps) ∈ B')
    (hk : ¬ ∃ u', (ρ.reconnect v'.1).SameCycle q.out u' ∧ ρ.RestrictKeep B u') :
    ρ.rsFwd B v' B' hB' hB'' ⟨Sum.inl q, h⟩ =
      Sum.inr (ρ.rsFreeOfNotKept B v' (ρ.mem_of_inl_mem v'.1 B B' hB' h) hk) :=
  dite_eq_right hk

theorem rsBwd_inr_pos (c : (ρ.restrict B).FreeComp) (h : ∃ u, ρ.comp u = c.1.1) :
    ρ.rsBwd B v' B' hB' hB'' (Sum.inr c) =
      ⟨Sum.inl (Quotient.mk _ (Classical.choose h)),
        (hB' _).mpr (by rw [Classical.choose_spec h]; exact c.1.2)⟩ :=
  dite_eq_left h

theorem rsBwd_inr_neg (c : (ρ.restrict B).FreeComp) (h : ¬ ∃ u, ρ.comp u = c.1.1) :
    ρ.rsBwd B v' B' hB' hB'' (Sum.inr c) =
      ⟨Sum.inr ⟨c.1.1, fun u hu => h ⟨u, hu⟩⟩, (hB'' _).mpr c.1.2⟩ :=
  dite_eq_right h

theorem rsBwd_rsFwd (s : ((ρ.smooth v'.1).restrict B').comps) :
    ρ.rsBwd B v' B' hB' hB'' (ρ.rsFwd B v' B' hB' hB'' s) = s := by
  rcases s with ⟨q | f, h⟩
  · have hmem : ρ.comp q.out ∈ B := ρ.mem_of_inl_mem v'.1 B B' hB' h
    by_cases hk : ∃ u', (ρ.reconnect v'.1).SameCycle q.out u' ∧ ρ.RestrictKeep B u'
    · rw [ρ.rsFwd_inl_pos B v' B' hB' hB'' q h hk]
      apply Subtype.ext
      apply congrArg Sum.inl
      refine (Quotient.sound ?_).trans (Quotient.out_eq q)
      have h1 := (ρ.restrict_reconnect_sameCycle_iff B v' _ _).mp
        (ρ.restrict_reconnect_sameCycle_out B v'
          ⟨Classical.choose hk, (Classical.choose_spec hk).2⟩)
      exact h1.trans (Classical.choose_spec hk).1.symm
    · rw [ρ.rsFwd_inl_neg B v' B' hB' hB'' q h hk]
      have hex : ∃ u, ρ.comp u = ρ.comp q.out := ⟨q.out, rfl⟩
      rw [ρ.rsBwd_inr_pos B v' B' hB' hB'' _ hex]
      apply Subtype.ext
      apply congrArg Sum.inl
      refine (Quotient.sound ?_).trans (Quotient.out_eq q)
      exact ((ρ.sameCycle_iff_of_not_hasKept B v' hk _).mpr
        (Classical.choose_spec hex).symm).symm
  · have hex : ¬ ∃ u, ρ.comp u = f.1 := fun ⟨u, hu⟩ => f.2 u hu
    exact (ρ.rsBwd_inr_neg B v' B' hB' hB'' (ρ.rsFreeOfFree B f ((hB'' f).mp h)) hex).trans rfl

theorem rsFwd_rsBwd (c : ((ρ.restrict B).smooth v').comps) :
    ρ.rsFwd B v' B' hB' hB'' (ρ.rsBwd B v' B' hB' hB'' c) = c := by
  rcases c with q | c
  · have hk : ∃ u', (ρ.reconnect v'.1).SameCycle
        (Quotient.mk (Perm.SameCycle.setoid (ρ.reconnect v'.1)) q.out.1).out u' ∧
          ρ.RestrictKeep B u' :=
      ⟨q.out.1, ρ.reconnect_sameCycle_out v'.1 _, q.out.2⟩
    refine (ρ.rsFwd_inl_pos B v' B' hB' hB'' _ ((hB' _).mpr q.out.2.1) hk).trans ?_
    apply congrArg Sum.inl
    refine (Quotient.sound ?_).trans (Quotient.out_eq q)
    refine (ρ.restrict_reconnect_sameCycle_iff B v' _ _).mpr ?_
    exact (Classical.choose_spec hk).1.symm.trans (ρ.reconnect_sameCycle_out v'.1 _)
  · by_cases hex : ∃ u, ρ.comp u = c.1.1
    · have hout : ρ.comp (Quotient.mk (Perm.SameCycle.setoid (ρ.reconnect v'.1))
          (Classical.choose hex)).out = c.1.1 :=
        ρ.comp_out_eq_of_free B v' c (Classical.choose_spec hex)
      have hk := ρ.not_hasKept_of_free B v' c hout
      rw [ρ.rsBwd_inr_pos B v' B' hB' hB'' c hex, ρ.rsFwd_inl_neg B v' B' hB' hB'' _ _ hk]
      apply congrArg Sum.inr
      apply Subtype.ext
      exact Subtype.ext hout
    · rw [ρ.rsBwd_inr_neg B v' B' hB' hB'' c hex]
      rfl

end Internal

/-- The circle bijection of `restrictSmoothIso`. -/
noncomputable def rsCompsEquiv (B : Finset ρ.comps) (v' : (ρ.restrict B).M)
    (B' : Finset (ρ.smooth v'.1).comps)
    (hB' : ∀ u : ρ.M, (Sum.inl (Quotient.mk _ u) : (ρ.smooth v'.1).comps) ∈ B' ↔ ρ.comp u ∈ B)
    (hB'' : ∀ f : ρ.FreeComp, (Sum.inr f : (ρ.smooth v'.1).comps) ∈ B' ↔ f.1 ∈ B) :
    ((ρ.smooth v'.1).restrict B').comps ≃ ((ρ.restrict B).smooth v').comps where
  toFun := ρ.rsFwd B v' B' hB' hB''
  invFun := ρ.rsBwd B v' B' hB' hB''
  left_inv := ρ.rsBwd_rsFwd B v' B' hB' hB''
  right_inv := ρ.rsFwd_rsBwd B v' B' hB' hB''

/-- The occurrence bijection of `restrictSmoothIso`. -/
def rsOccEquiv (B : Finset ρ.comps) (v' : (ρ.restrict B).M)
    (B' : Finset (ρ.smooth v'.1).comps)
    (hB' : ∀ u : ρ.M, (Sum.inl (Quotient.mk _ u) : (ρ.smooth v'.1).comps) ∈ B' ↔ ρ.comp u ∈ B) :
    ((ρ.smooth v'.1).restrict B').M ≃ ((ρ.restrict B).smooth v').M where
  toFun w := ⟨⟨w.1.1, (ρ.smooth_restrictKeep_iff v'.1 B B' hB' w.1).mp w.2⟩,
    (ρ.restrict_smoothKeep_iff B v' _).mpr w.1.2⟩
  invFun w := ⟨⟨w.1.1, (ρ.restrict_smoothKeep_iff B v' w.1).mp w.2⟩,
    (ρ.smooth_restrictKeep_iff v'.1 B B' hB' _).mpr w.1.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- `restrictSmoothIso` for a kept occurrence `v'` of the restriction, with the block hypotheses
stated on `(ρ.smooth v'.1).comps`. -/
theorem restrictSmoothIso' (B : Finset ρ.comps) (v' : (ρ.restrict B).M)
    (B' : Finset (ρ.smooth v'.1).comps)
    (hB' : ∀ u : ρ.M, (Sum.inl (Quotient.mk _ u) : (ρ.smooth v'.1).comps) ∈ B' ↔ ρ.comp u ∈ B)
    (hB'' : ∀ f : ρ.FreeComp, (Sum.inr f : (ρ.smooth v'.1).comps) ∈ B' ↔ f.1 ∈ B) :
    Nonempty (RecordIso ((ρ.smooth v'.1).restrict B') ((ρ.restrict B).smooth v')) := by
  refine ⟨{ e := ρ.rsCompsEquiv B v' B' hB' hB''
            Φ := ρ.rsOccEquiv B v' B' hB'
            comp_eq := ?_, succ_eq := ?_, pair_eq := ?_, bit_eq := ?_, sgn_eq := ?_ }⟩
  · intro w
    have hK : ρ.RestrictKeep B w.1.1 := (ρ.smooth_restrictKeep_iff v'.1 B B' hB' w.1).mp w.2
    have hk : ∃ u', (ρ.reconnect v'.1).SameCycle
        (Quotient.mk (Perm.SameCycle.setoid (ρ.reconnect v'.1)) w.1.1).out u' ∧
          ρ.RestrictKeep B u' :=
      ⟨w.1.1, ρ.reconnect_sameCycle_out v'.1 _, hK⟩
    refine Eq.trans ?_ (ρ.rsFwd_inl_pos B v' B' hB' hB'' _ ((hB' _).mpr hK.1) hk).symm
    apply congrArg Sum.inl
    apply Quotient.sound
    refine (ρ.restrict_reconnect_sameCycle_iff B v' _ _).mpr ?_
    exact (ρ.reconnect_sameCycle_out v'.1 _).symm.trans (Classical.choose_spec hk).1
  · intro w
    apply Subtype.ext
    apply Subtype.ext
    have hK : ρ.RestrictKeep B w.1.1 := (ρ.smooth_restrictKeep_iff v'.1 B B' hB' w.1).mp w.2
    have hP : (ρ.restrict B).SmoothKeep v' ⟨w.1.1, hK⟩ :=
      (ρ.restrict_smoothKeep_iff B v' _).mpr w.1.2
    show (firstReturn (ρ.smooth v'.1).succ ((ρ.smooth v'.1).RestrictKeep B') w).1.1 =
      (firstReturn ((ρ.restrict B).reconnect v') ((ρ.restrict B).SmoothKeep v')
        ⟨⟨w.1.1, hK⟩, hP⟩).1.1
    calc (firstReturn (ρ.smooth v'.1).succ ((ρ.smooth v'.1).RestrictKeep B') w).1.1
        = (firstReturn (ρ.smooth v'.1).succ (fun m => ρ.RestrictKeep B m.1) ⟨w.1, hK⟩).1.1 :=
          congrArg Subtype.val (firstReturn_val_congr _ _ _ _
            (ρ.smooth_restrictKeep_iff v'.1 B B' hB') w (fun _ => rfl))
      _ = (firstReturn (ρ.reconnect v'.1) (fun m => ρ.SmoothKeep v'.1 m ∧ ρ.RestrictKeep B m)
            ⟨w.1.1, w.1.2, hK⟩).1 :=
          firstReturn_firstReturn (ρ.reconnect v'.1) (ρ.SmoothKeep v'.1) (ρ.RestrictKeep B)
            ⟨w.1, hK⟩
      _ = (firstReturn (ρ.reconnect v'.1) (fun m => ρ.RestrictKeep B m ∧ ρ.SmoothKeep v'.1 m)
            ⟨w.1.1, hK, w.1.2⟩).1 :=
          firstReturn_val_congr _ _ _ _ (fun m => and_comm) ⟨w.1.1, w.1.2, hK⟩ (fun _ => rfl)
      _ = (firstReturn (firstReturn (ρ.reconnect v'.1) (ρ.RestrictKeep B))
            (fun m => ρ.SmoothKeep v'.1 m.1) ⟨⟨w.1.1, hK⟩, w.1.2⟩).1.1 :=
          (firstReturn_firstReturn (ρ.reconnect v'.1) (ρ.RestrictKeep B) (ρ.SmoothKeep v'.1)
            ⟨⟨w.1.1, hK⟩, w.1.2⟩).symm
      _ = (firstReturn ((ρ.restrict B).reconnect v') ((ρ.restrict B).SmoothKeep v')
            ⟨⟨w.1.1, hK⟩, hP⟩).1.1 :=
          congrArg Subtype.val (firstReturn_val_congr _ _ _ _
            (fun m => (ρ.restrict_smoothKeep_iff B v' m).symm) ⟨⟨w.1.1, hK⟩, w.1.2⟩
            (fun n => by rw [ρ.restrict_reconnect_eq B v']))
  · intro w; rfl
  · intro w; rfl
  · intro w; rfl

end U2Record

/-! #### The fixed statements of unit U2 -/

open scoped Classical in
/-- **Restriction of the smoothing = smoothing of the restriction** at an internal crossing.
Occurrences: `SmoothKeep v ∧ RestrictKeep B` on both sides (`smooth_comp`, `smoothKeep_iff`,
`Subtype.ext_iff`); successor: LHS = `firstReturn (firstReturn (reconnect v) SmoothKeep) (RestrictKeep B' ∘ val)`
= `firstReturn (reconnect v) (SmoothKeep ∧ RestrictKeep B)` (`firstReturn_firstReturn`); RHS =
`firstReturn ((restrict B).reconnect ⟨v⟩) SmoothKeep` with `(restrict B).reconnect ⟨v⟩ =
firstReturn succ (RestrictKeep B) * swap ⟨v⟩ ⟨pair v⟩ = firstReturn (reconnect v) (RestrictKeep B)`
(`firstReturn_mul_swap`), so RHS = `firstReturn (reconnect v) (RestrictKeep B ∧ SmoothKeep)`
(`firstReturn_firstReturn`, `and_comm`); circles: `inl ⟦u⟧ ↦ inl ⟦⟨u, _⟩⟧` for `comp u ∈ B`
(`sameCycle_map_iff` along the subtype inclusion), `inr f ↦ inr ⟨⟨f.1, _⟩, free⟩`; `comp_eq` by
`Quotient.ind`. -/
theorem restrictSmoothIso (v : ρ.M) (B : Finset ρ.comps) (hv : ρ.RestrictKeep B v)
    (B' : Finset (ρ.smooth v).comps)
    (hB' : ∀ u : ρ.M, (Sum.inl (Quotient.mk _ u) : ρ.SmoothComps v) ∈ B' ↔ ρ.comp u ∈ B)
    (hB'' : ∀ f : ρ.FreeComp, (Sum.inr f : ρ.SmoothComps v) ∈ B' ↔ f.1 ∈ B) :
    Nonempty (RecordIso ((ρ.smooth v).restrict B')
      ((ρ.restrict B).smooth (⟨v, hv⟩ : {u : ρ.M // ρ.RestrictKeep B u}))) :=
  ρ.restrictSmoothIso' B ⟨v, hv⟩ B' hB' hB''

open scoped Classical in
/-- **Restriction of the smoothing at an external crossing = the old restriction**: no occurrence of
`B` is erased (`RestrictKeep B u → u ≠ v, pair v`) and `s₁` agrees with `s` along every `B`-circle
(`(reconnect v)^n u = succ^n u` when `comp u ∈ B`, since all iterates keep `comp` (`comp_pow`) and
`comp v, comp (pair v) ∉ B`; hence equal return times, `returnTime_eq_iff`).  Circles:
`inl ⟦u⟧ ↦ ⟨comp u, _⟩` (well defined: on `B`-cycles `reconnect = succ`), `inr f ↦ ⟨f.1, _⟩`;
surjective since a `B`-circle either carries an occurrence or is free. -/
theorem restrictSmoothDisjointIso (v : ρ.M) (B : Finset ρ.comps) (hv : ρ.comp v ∉ B)
    (hv' : ρ.comp (ρ.pair v) ∉ B) (B' : Finset (ρ.smooth v).comps)
    (hB' : ∀ u : ρ.M, (Sum.inl (Quotient.mk _ u) : ρ.SmoothComps v) ∈ B' ↔ ρ.comp u ∈ B)
    (hB'' : ∀ f : ρ.FreeComp, (Sum.inr f : ρ.SmoothComps v) ∈ B' ↔ f.1 ∈ B) :
    Nonempty (RecordIso ((ρ.smooth v).restrict B') (ρ.restrict B)) :=
  ρ.restrictSmoothDisjointIso' v B hv hv' B' hB' hB''

end Record

end Link

/-! ### 6.4 Diagram level: block bookkeeping -/

namespace Link.Diagram

variable (D : Diagram)

/-- A diagram-level block order is a record-level one: for `v = ⟨x, s⟩`, `record.comp v = s.1`
(`record_comp`), `record.pair v = twin v` carries the other strand `t` (`record_pair_apply`,
`twin`), and `isOver v = false ↔ s ≠ overStrand x ↔ s = underStrand x` (`record_isOver_iff`,
`eq_under_of_mem_of_ne`); `hord x s t` gives `underStrand x = s`. -/
theorem rBlockOrdered_of_blockOrdered {q : ℕ} {blk : Fin D.Γ.c → Fin q} (hord : BlockOrdered D blk) :
    D.record.RBlockOrdered blk := by
  sorry

/-- **The restriction of an UNDER-first diagram is UNDER-first** (initialization of mp:stack,
sm-3:1519-1521 "If `b = 0`, the full diagram is ascending … Each factor has scalar `δ^{c_i−1}`").
Rank: the order induced by `B.rank` on the block (`exists_rank_equiv` on
`fun j => (B.rank (S.orderEmbOfFin rfl j)).val`); basepoints: the old ones
(`base' j := B.base (S.orderEmbOfFin rfl j)`, typechecks since `(D.restrict S hS).Γ.comp j =
D.Γ.comp (S.orderEmbOfFin rfl j)` is `rfl`), nonsingular by `crossingPoint_mapCrossing`;
UNDER-first: for a crossing `y` of the restriction with `x := mapCrossing y`, `restrict_visitPt_fst`
/ `restrict_visitPt_snd` give component and traversal coordinate of the mapped visits,
`toFun_restrict_underStrand` / `toFun_restrict_overStrand` identify `mapVisit (underVisit y) =
underVisit x`, and `h x` transfers through the monotone rank (`Prod.lex_def`). -/
theorem restrict_underFirst (B : D.Basing) (h : D.UnderFirst B) (S : Finset (Fin D.Γ.c))
    (hS : S.Nonempty) : ∃ B' : (D.restrict S hS).Basing, (D.restrict S hS).UnderFirst B' := by
  sorry

end Link.Diagram

/-- Switching an internal crossing "preserves the block assignment and the between-block hypothesis"
(sm-3:1524-1525): `switch_underStrand_self` / `switch_underStrand_of_ne`, `x.val` unchanged; at the
switched crossing both strands have equal `blk`, so the premise `blk s.1 < blk t.1` is false. -/
theorem BlockOrdered.switch_of_internal {D : Diagram} {q : ℕ} {blk : Fin D.Γ.c → Fin q}
    (hord : BlockOrdered D blk) {v : D.Γ.Visit}
    (hx : blk (D.compOf v) = blk (D.compOf (D.twin v))) : BlockOrdered (D.switch v.1) blk := by
  sorry

/-- "is the same switch in its block restriction" (`switch_restrict_of_internal` after `subst hy`). -/
theorem blockRestrict_switch_of_internal (D : Diagram) {q : ℕ} (blk : Fin D.Γ.c → Fin q)
    (hblk : Function.Surjective blk) (v : D.Γ.Visit) (i : Fin q)
    (y : (blockRestrict D blk hblk i).Γ.Crossing)
    (hy : (D.Γ.restrictMap (blockSet D blk i) (blockSet_nonempty D blk hblk i)).mapCrossing y = v.1) :
    blockRestrict (D.switch v.1) blk hblk i = (blockRestrict D blk hblk i).switch y := by
  sorry

/-- "the other restrictions do not change" (`switch_restrict_of_external`; the strand `v.2.val ∈
v.1.val` has component `compOf v` whose block is not `i`). -/
theorem blockRestrict_switch_of_external (D : Diagram) {q : ℕ} (blk : Fin D.Γ.c → Fin q)
    (hblk : Function.Surjective blk) (v : D.Γ.Visit) (i : Fin q) (hi : i ≠ blk (D.compOf v)) :
    blockRestrict (D.switch v.1) blk hblk i = blockRestrict D blk hblk i := by
  sorry

/-- The transported blocks `blk₀ := smoothBlock blk v ∘ ι₀.e` of a smoothing `D₀` are surjective
("no block becomes empty": for block `i` pick `k` with `blk k = i`; if some visit `u` has
`compOf u = k` take `ι₀.e.symm (inl ⟦u⟧)`, else `ι₀.e.symm (inr ⟨k, free⟩)`) and block-ordered
("All between-block crossing visits persist on their original strands, so their under/over relation
still has the required block order": for `y` with strands `s, t` and `blk₀ s.1 < blk₀ t.1`, put
`u := ι₀.Φ ⟨y, s⟩`; `ι₀.Φ ⟨y, t⟩ = pair u` (`pair_eq`), `ι₀.comp_eq` gives `inl ⟦u.1⟧ = ι₀.e s.1` so
`blk₀ s.1 = blk (compOf u.1)`; `hord` at `u.1.1` ⇒ `u.1 = underVisit _` ⇒ `isOver u.1 = false` ⇒
`D₀.record.isOver ⟨y, s⟩ = false` (`ι₀.bit_eq`, `smooth_isOver`) ⇒ `s = underStrand y`
(`record_isOver_iff`, `eq_under_of_mem_of_ne`)). -/
theorem blocks_of_smoothing (D : Diagram) {q : ℕ} (blk : Fin D.Γ.c → Fin q)
    (hblk : Function.Surjective blk) (hord : BlockOrdered D blk) (v : D.Γ.Visit)
    (hx : blk (D.compOf v) = blk (D.compOf (D.twin v))) (D₀ : Diagram)
    (ι₀ : RecordIso D₀.record (D.record.smooth v)) :
    Function.Surjective (D.record.smoothBlock blk v hx ∘ ι₀.e) ∧
      BlockOrdered D₀ (D.record.smoothBlock blk v hx ∘ ι₀.e) := by
  sorry

/-! ### 6.5 Initialization, step, assembly -/

/-- "If `b = 0`, the full diagram is ascending … their product times `δ^{q−1}` has the same exponent
`q − 1 + Σ(c_i − 1) = Σ c_i − 1`" (sm-3:1519-1523): `P_underFirst_init` on `D` and on every block
restriction (`restrict_underFirst`, value `δ^{c_i−1}` with `c_i = (blockSet i).card`,
`restrict_componentCount`), `Finset.prod_pow_eq_pow_sum`, `∑ c_i = c`
(`Finset.card_eq_sum_card_fiberwise`), `∑ (c_i − 1) = c − q` (each `c_i ≥ 1`), `pow_add`. -/
theorem stack_init (D : Diagram) {q : ℕ} (blk : Fin D.Γ.c → Fin q) (hblk : Function.Surjective blk)
    (B : D.Basing) (h : D.UnderFirst B) :
    P D = R.delta ^ (q - 1) * ∏ i : Fin q, P (blockRestrict D blk hblk i) := by
  sorry

/-- The stack step (sm-3:1524-1533) at an internal occurrence `v` of block `i₀ := blk (compOf v)`.
`P D = solvedR pos (P (D.switch v.1)) (P D₀)` (`solvedR_of_skein`).  `ihsw` is rewritten with
`blockRestrict_switch_of_internal` (factor `i₀`: `F.switch y`, where `F := blockRestrict D blk hblk i₀`,
`v' := (D.exists_restrictVisit _ _ v hv).choose`, `y := v'.1`, `hy` by `restrictVisit_fst`) and
`blockRestrict_switch_of_external` (others).  `blocks_of_smoothing` gives `blk₀`; `ih₀ blk₀`.
Factor `i ≠ i₀`: `(blockRestrict D₀ blk₀ _ i).record ≅ D₀.record.restrict (blockSet₀ i)`
(`restrictRecordIso`) `≅ (D.record.smooth v).restrict B'` with
`B' := univ.filter (smoothBlock blk v hx · = i)` (`ι₀.restrict`, `hB` by `mem_blockSet_iff`)
`≅ D.record.restrict (blockSet i)` (`restrictSmoothDisjointIso`; `hB'`/`hB''` by `smoothBlock_inl/inr`)
`≅ (blockRestrict D blk hblk i).record` ⇒ `P` equal by `presentations`.  Factor `i₀`:
`… ≅ (D.record.restrict (blockSet i₀)).smooth ⟨v, hv⟩` (`restrictSmoothIso`) `≅ F.record.smooth v'`
(`(D.restrictRecordIso _ _).symm.smooth`, `restrictVisitEquiv_apply_val`) `≅ F₀.record` for `F₀` from
`exists_smoothing_record_visit F y v' rfl`; so `P (blockRestrict D₀ blk₀ _ i₀) = P F₀`, and
`P F = solvedR pos' (P (F.switch y)) (P F₀)` with `pos' ↔ pos` (`restrict_isPositive_iff`, `hy`).
Finish: `Finset.mul_prod_erase` on the three products, `solvedR_mul_left`. -/
theorem stack_step (D : Diagram) {q : ℕ} (blk : Fin D.Γ.c → Fin q) (hblk : Function.Surjective blk)
    (hord : BlockOrdered D blk) (v : D.Γ.Visit)
    (hx : blk (D.compOf v) = blk (D.compOf (D.twin v))) (D₀ : Diagram)
    (h₀ : IsOrientedSmoothing D v.1 D₀) (ι₀ : RecordIso D₀.record (D.record.smooth v))
    (ihsw : P (D.switch v.1) =
      R.delta ^ (q - 1) * ∏ i : Fin q, P (blockRestrict (D.switch v.1) blk hblk i))
    (ih₀ : ∀ (blk₀ : Fin D₀.Γ.c → Fin q) (hblk₀ : Function.Surjective blk₀), BlockOrdered D₀ blk₀ →
      P D₀ = R.delta ^ (q - 1) * ∏ i : Fin q, P (blockRestrict D₀ blk₀ hblk₀ i)) :
    P D = R.delta ^ (q - 1) * ∏ i : Fin q, P (blockRestrict D blk hblk i) := by
  sorry

/-- eq. mp:stack-value (sm-3:1513-1535) by `skein_induction_based` at a block-compatible based
order: init `stack_init` (through the bridge), step `stack_step` at the bad — hence internal
(`isBad_internal`) — occurrence, with the smoothing of the gate `exists_smoothing_record_visit`. -/
theorem stack_formula (D : Diagram) (q : ℕ) (blk : Fin D.Γ.c → Fin q) (hblk : Function.Surjective blk)
    (h : BlockOrdered D blk) :
    P D = R.delta ^ (q - 1) * ∏ i : Fin q, P (blockRestrict D blk hblk i) := by
  obtain ⟨B, hB⟩ := D.record.exists_blockCompatible_rbasing blk
  refine Diagram.skein_induction_based
    (fun D B => ∀ (q : ℕ) (blk : Fin D.Γ.c → Fin q) (hblk : Function.Surjective blk),
      BlockOrdered D blk → B.BlockCompatible blk →
      P D = R.delta ^ (q - 1) * ∏ i : Fin q, P (blockRestrict D blk hblk i)) ?_ ?_ D B q blk hblk h hB
  · intro D B hB q blk hblk _ _
    obtain ⟨B', hB'⟩ := D.exists_underFirst_of_rUnderFirst B hB
    exact stack_init D blk hblk B' hB'
  · intro D B v hv ihsw ihsm q blk hblk hord hBc
    have hx : blk (D.compOf v) = blk (D.compOf (D.twin v)) :=
      Record.RBasing.isBad_internal (D.rBlockOrdered_of_blockOrdered hord) hBc hv
    obtain ⟨D₀, h₀, ⟨ι₀⟩⟩ := exists_smoothing_record_visit D v.1 v rfl
    refine stack_step D blk hblk hord v hx D₀ h₀ ι₀ ?_ ?_
    · exact ihsw q blk hblk (hord.switch_of_internal hx) (fun c c' hc => hBc c c' hc)
    · intro blk₀ hblk₀ hord₀
      obtain ⟨B₀, hB₀⟩ := D₀.record.exists_blockCompatible_rbasing blk₀
      exact ihsm D₀ B₀ h₀ q blk₀ hblk₀ hord₀ hB₀
/-! ## §7. The five row theorems (bundles verbatim from work/drafts/*_statement.lean) -/

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
  /-- eq. lp:support: "For every `c`-component diagram, `P_D ∈ z^{1−c} ℤ[a^{±1}, z^2]`". -/
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

/-- mp:stack as printed. -/
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

theorem stack : StackData where
  stack := stack_formula
  split_union := fun D blk hblk h => by
    have hbo : BlockOrdered D blk := fun x s t hs ht hlt => by
      rw [h x s t hs ht] at hlt
      exact absurd hlt (lt_irrefl _)
    rw [stack_formula D 2 blk hblk hbo, Fin.prod_univ_two, show (2 : ℕ) - 1 = 1 from rfl, pow_one,
      mul_assoc]

end SM
