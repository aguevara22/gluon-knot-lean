import SM.CornerStateSum

/-! Source lem:C-X1 (reference/SM/sm-3-statesum.tex:1787-1798, frame SM15): selector form of the carrier state
sum. Main declaration: `SM.C_X1`.

Notation (accepted rows def:uniform, lem:carriers, def:C; namespaces `SM.Carrier`, `SM.Link`): "a carrier `L` of
an independent support `S`" is `q : Component hn hP S` with `S ∈ independentSupports hn hP` (= Ind(G_P),
`IsDecomposition`); "its number of corners `k(L)`" is `ccpCornerCount hn hP S q`; its turns are
`turn (ccpCornerPolygon hn hP S q) j` (def:chirotope: `turn = sgn det(incoming, outgoing)`, a LEFT turn is `1`, a
RIGHT turn is `−1`; all carrier turns are nonzero by lem:carriers); "wt(L) = 1 if all its turns are right,
(−1)^{k(L)} if all are left, 0 if mixed" is `carrierWeight`; "wind(S) = ∏_L wt(L)" is `wind`; `C(P)` is
`cornerStateSum hn hP` and "c(L), the coefficient of the actual positive carrier lift in def:C" is
`cornerCoefficient hn hP S q hS` (their product over the carriers of `S` is `cornerProduct hn hP S hS`). -/

namespace SM

open Link Carrier

variable {n : ℕ} [NeZero n]

/-- "wt(L) = 1 if all its turns are right, (−1)^{k(L)} if all are left, and 0 if its turns are mixed." -/
noncomputable def carrierWeight (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) (q : Component hn hP S) : ℤ :=
  if ∀ j, turn (ccpCornerPolygon hn hP S q) j = -1 then 1
  else if ∀ j, turn (ccpCornerPolygon hn hP S q) j = 1 then (-1) ^ ccpCornerCount hn hP S q
  else 0

/-- "wind(S) = ∏_L wt(L)" over the carriers of `S`. -/
noncomputable def wind (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) : ℤ :=
  ∏ q : Component hn hP S, carrierWeight hn hP S q

/-! ### Helpers (draft B): the total number of left carrier corners

The printed proof counts left corners mark by mark: every original vertex is a true corner of
exactly one carrier and keeps its turn (`ccpCornerPolygon_turn_vertex`), and the two smoothing
corners of a selected crossing (`ccp_selected_crossing_two_corners`) have opposite signs. The corner
indices of a carrier `q` are in bijection with the true corners owned by `q`
(`ccpCornerMark_injective`, `ccpCornerMark_exists`, `ccpCornerMark_owner`), so a mark is a *left
corner mark* when it is the corner mark of some carrier at an index with turn `1`; summing over
carriers is counting these marks. -/

section Helpers

variable (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P) (S : Finset (Crossing P))

/-- A mark is a left corner mark when it is a corner of some carrier with turn `1`. -/
def IsLeftCornerMark (a : Mark P) : Prop :=
  ∃ (q : Component hn hP S) (j : ZMod (ccpCornerCount hn hP S q)),
    ccpCornerMark hn hP S q j = a ∧ turn (ccpCornerPolygon hn hP S q) j = 1

/-- The corner index of a corner mark is determined (owner, then injectivity), so being a left
corner mark is exactly having a left turn at that index. -/
theorem isLeftCornerMark_iff_of_mark {a : Mark P} {q : Component hn hP S}
    {j : ZMod (ccpCornerCount hn hP S q)} (hj : ccpCornerMark hn hP S q j = a) :
    IsLeftCornerMark hn hP S a ↔ turn (ccpCornerPolygon hn hP S q) j = 1 := by
  subst hj
  constructor
  · rintro ⟨q', j', h, ht⟩
    have hq : q' = q := by
      rw [← ccpCornerMark_owner hn hP S q' j', h, ccpCornerMark_owner]
    subst hq
    rw [← ccpCornerMark_injective hn hP S q' h]
    exact ht
  · intro ht
    exact ⟨q, j, rfl, ht⟩

open Classical in
/-- Summing the left-corner counts over the carriers counts the left corner marks. -/
theorem sum_leftCorners_eq_card_leftCornerMarks :
    ∑ q : Component hn hP S,
        (Finset.univ.filter fun j => turn (ccpCornerPolygon hn hP S q) j = 1).card =
      (Finset.univ.filter fun a : Mark P => IsLeftCornerMark hn hP S a).card := by
  rw [← Finset.card_sigma]
  refine Finset.card_bij (fun p _ => ccpCornerMark hn hP S p.1 p.2) ?_ ?_ ?_
  · intro p hp
    rw [Finset.mem_sigma, Finset.mem_filter] at hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, p.1, p.2, rfl, hp.2.2⟩
  · rintro ⟨q₁, j₁⟩ _ ⟨q₂, j₂⟩ _ h
    dsimp only at h
    have hq : q₁ = q₂ := by
      rw [← ccpCornerMark_owner hn hP S q₁ j₁, h, ccpCornerMark_owner]
    subst hq
    rw [ccpCornerMark_injective hn hP S q₁ h]
  · intro a ha
    obtain ⟨q, j, hj, ht⟩ := (Finset.mem_filter.mp ha).2
    exact ⟨⟨q, j⟩, Finset.mem_sigma.mpr ⟨Finset.mem_univ _,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht⟩⟩, hj⟩

open Classical in
/-- Split the left corner marks into original vertices and crossing visits. -/
theorem card_leftCornerMarks_split :
    (Finset.univ.filter fun a : Mark P => IsLeftCornerMark hn hP S a).card =
      (Finset.univ.filter fun i : ZMod n => IsLeftCornerMark hn hP S (Sum.inl i)).card +
        (Finset.univ.filter fun v : Visit P => IsLeftCornerMark hn hP S (Sum.inr v)).card := by
  rw [Finset.card_filter, Finset.card_filter, Finset.card_filter, Fintype.sum_sum_type]

/-- "Every original vertex belongs to exactly one carrier and retains its turn." -/
theorem isLeftCornerMark_inl_iff (hS : S ∈ independentSupports hn hP) (i : ZMod n) :
    IsLeftCornerMark hn hP S (Sum.inl i) ↔ turn P i = 1 := by
  obtain ⟨j, hj⟩ := ccpCornerMark_exists hn hP S (owner hn hP S (Sum.inl i)) (Sum.inl i) rfl
    (isTrueCorner_vertex S i)
  rw [isLeftCornerMark_iff_of_mark hn hP S hj, ccpCornerPolygon_turn_vertex hn hP hS _ j i hj]

open Classical in
/-- The left corner marks at original vertices are the left turns of `P`: `ℓ(P)` of them. -/
theorem card_leftCornerMarks_inl (hS : S ∈ independentSupports hn hP) :
    (Finset.univ.filter fun i : ZMod n => IsLeftCornerMark hn hP S (Sum.inl i)).card =
      leftTurns P := by
  unfold leftTurns
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact isLeftCornerMark_inl_iff hn hP S hS i

/-- A left corner mark at a visit is a selected visit (it is a true corner). -/
theorem mem_of_isLeftCornerMark_inr {v : Visit P} (h : IsLeftCornerMark hn hP S (Sum.inr v)) :
    v.1 ∈ S := by
  obtain ⟨q, j, hj, _⟩ := h
  have := ccpCornerMark_isTrueCorner hn hP S q j
  rw [hj] at this
  exact this

open Classical in
/-- "Every selected crossing contributes one left and one right smoothing corner": the left corner
marks at visits are counted by `S` (the map `v ↦ v.1` is a bijection onto `S`). -/
theorem card_leftCornerMarks_inr (hS : S ∈ independentSupports hn hP) :
    (Finset.univ.filter fun v : Visit P => IsLeftCornerMark hn hP S (Sum.inr v)).card =
      S.card := by
  refine Finset.card_bij (fun v _ => v.1) ?_ ?_ ?_
  · intro v hv
    exact mem_of_isLeftCornerMark_inr hn hP S (Finset.mem_filter.mp hv).2
  · intro v hv w hw hvw
    have hvS : v.1 ∈ S := mem_of_isLeftCornerMark_inr hn hP S (Finset.mem_filter.mp hv).2
    rcases visit_eq_or_twin v w hvw.symm with h | h
    · exact h.symm
    · exfalso
      subst h
      obtain ⟨_, j, j', hj, hj', _, _, hneg, _⟩ :=
        ccp_selected_crossing_two_corners hn hP hS v hvS
      have h1 := (isLeftCornerMark_iff_of_mark hn hP S hj).mp (Finset.mem_filter.mp hv).2
      have h2 := (isLeftCornerMark_iff_of_mark hn hP S hj').mp (Finset.mem_filter.mp hw).2
      rw [hneg, h1] at h2
      exact absurd h2 (by decide)
  · intro c hc
    obtain ⟨i, hi⟩ := Finset.card_pos.mp (by rw [crossing_card_two c]; omega : 0 < c.val.card)
    obtain ⟨_, j, j', hj, hj', _, _, _, hor⟩ :=
      ccp_selected_crossing_two_corners hn hP hS ⟨c, ⟨i, hi⟩⟩ hc
    rcases hor with ⟨h1, _⟩ | ⟨_, h2⟩
    · exact ⟨⟨c, ⟨i, hi⟩⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        (isLeftCornerMark_iff_of_mark hn hP S hj).mpr h1⟩, rfl⟩
    · exact ⟨visitTwin ⟨c, ⟨i, hi⟩⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        (isLeftCornerMark_iff_of_mark hn hP S hj').mpr h2⟩, rfl⟩

/-- **The total number of left carrier corners is `ℓ(P) + |S|`.** -/
theorem sum_leftCorners_eq (hS : S ∈ independentSupports hn hP) :
    ∑ q : Component hn hP S,
        (Finset.univ.filter fun j => turn (ccpCornerPolygon hn hP S q) j = 1).card =
      leftTurns P + S.card := by
  rw [sum_leftCorners_eq_card_leftCornerMarks hn hP S, card_leftCornerMarks_split hn hP S,
    card_leftCornerMarks_inl hn hP S hS, card_leftCornerMarks_inr hn hP S hS]

/-! ### The weight of a carrier -/

theorem carrierWeight_of_right (q : Component hn hP S)
    (h : ∀ j, turn (ccpCornerPolygon hn hP S q) j = -1) : carrierWeight hn hP S q = 1 := by
  unfold carrierWeight
  rw [ite_eq_left h]

theorem carrierWeight_of_left (q : Component hn hP S)
    (h : ∀ j, turn (ccpCornerPolygon hn hP S q) j = 1) :
    carrierWeight hn hP S q = (-1) ^ ccpCornerCount hn hP S q := by
  unfold carrierWeight
  have h' : ¬ ∀ j, turn (ccpCornerPolygon hn hP S q) j = -1 := by
    intro h'
    have := h 0
    rw [h' 0] at this
    exact absurd this (by decide)
  rw [ite_eq_right h', ite_eq_left h]

theorem carrierWeight_of_mixed (q : Component hn hP S)
    (h₁ : ¬ ∀ j, turn (ccpCornerPolygon hn hP S q) j = -1)
    (h₂ : ¬ ∀ j, turn (ccpCornerPolygon hn hP S q) j = 1) : carrierWeight hn hP S q = 0 := by
  unfold carrierWeight
  rw [ite_eq_right h₁, ite_eq_right h₂]

/-- def:uniform, read as "all right or all left". -/
theorem carrierUniform_iff (q : Component hn hP S) :
    CarrierUniform hn hP S q ↔
      (∀ j, turn (ccpCornerPolygon hn hP S q) j = -1) ∨
        (∀ j, turn (ccpCornerPolygon hn hP S q) j = 1) := by
  constructor
  · rintro ⟨τ, hτ, h⟩
    cases τ with
    | zero => exact absurd rfl hτ
    | neg => exact Or.inl h
    | pos => exact Or.inr h
  · rintro (h | h)
    · exact ⟨-1, by decide, h⟩
    · exact ⟨1, by decide, h⟩

/-- A uniform carrier weighs `(−1)^{number of its left corners}`: all of its `k` corners for an
all-left carrier, none for an all-right one. -/
theorem carrierWeight_of_uniform (q : Component hn hP S) (hq : CarrierUniform hn hP S q) :
    carrierWeight hn hP S q =
      (-1) ^ (Finset.univ.filter fun j => turn (ccpCornerPolygon hn hP S q) j = 1).card := by
  rcases (carrierUniform_iff hn hP S q).mp hq with h | h
  · rw [carrierWeight_of_right hn hP S q h, Finset.filter_eq_empty_iff.mpr ?_, Finset.card_empty,
      pow_zero]
    intro j _ hj
    rw [h j] at hj
    exact absurd hj (by decide)
  · rw [carrierWeight_of_left hn hP S q h, Finset.filter_true_of_mem (fun j _ => h j),
      Finset.card_univ, ZMod.card]

/-- "If `S` is uniform, precisely its all-left carriers contribute to this count. Their selector
product is therefore `(−1)^{ℓ(P)+|S|}`." -/
theorem wind_of_uniform (hS : S ∈ independentSupports hn hP) (hu : UniformDecomposition hn hP S) :
    wind hn hP S = (-1) ^ (leftTurns P + S.card) := by
  unfold wind
  rw [Finset.prod_congr rfl (fun q _ => carrierWeight_of_uniform hn hP S q (hu q)),
    Finset.prod_pow_eq_pow_sum, sum_leftCorners_eq hn hP S hS]

/-- "If `S` is not uniform, a mixed carrier makes its selector product zero." -/
theorem wind_of_not_uniform (hu : ¬ UniformDecomposition hn hP S) : wind hn hP S = 0 := by
  obtain ⟨q, hq⟩ := not_forall.mp (hu : ¬ ∀ q : Component hn hP S, CarrierUniform hn hP S q)
  have hm := (not_congr (carrierUniform_iff hn hP S q)).mp hq
  rw [not_or] at hm
  unfold wind
  exact Finset.prod_eq_zero (Finset.mem_univ q) (carrierWeight_of_mixed hn hP S q hm.1 hm.2)

end Helpers

/-- lem:C-X1 as printed. -/
structure CX1Data : Prop where
  /-- wt(L) = 1 if all turns of `L` are right -/
  weight_right : ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Generic P)
    (S : Finset (Crossing P)) (q : Component hn hP S),
    (∀ j, turn (ccpCornerPolygon hn hP S q) j = -1) → carrierWeight hn hP S q = 1
  /-- wt(L) = (−1)^{k(L)} if all turns of `L` are left -/
  weight_left : ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Generic P)
    (S : Finset (Crossing P)) (q : Component hn hP S),
    (∀ j, turn (ccpCornerPolygon hn hP S q) j = 1) →
    carrierWeight hn hP S q = (-1) ^ ccpCornerCount hn hP S q
  /-- wt(L) = 0 if the turns of `L` are mixed (neither all right nor all left) -/
  weight_mixed : ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Generic P)
    (S : Finset (Crossing P)) (q : Component hn hP S),
    (¬ ∀ j, turn (ccpCornerPolygon hn hP S q) j = -1) → (¬ ∀ j, turn (ccpCornerPolygon hn hP S q) j = 1) →
    carrierWeight hn hP S q = 0
  /-- "Set wind(S) = ∏_L wt(L)." -/
  wind_eq : ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Generic P)
    (S : Finset (Crossing P)), wind hn hP S = ∏ q : Component hn hP S, carrierWeight hn hP S q
  /-- eq. C-selector-form: `C(P) = Σ_{S ∈ Ind(G_P)} wind(S) ∏_L c(L)`, where c(L) remains the coefficient of
  the actual positive carrier lift of def:C. -/
  selector_form : ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Generic P),
    cornerStateSum hn hP =
      ∑ S ∈ (independentSupports hn hP).attach, wind hn hP S.1 * cornerProduct hn hP S.1 S.2

theorem C_X1 : CX1Data := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro n _ hn P hP S q h
    exact carrierWeight_of_right hn hP S q h
  · intro n _ hn P hP S q h
    exact carrierWeight_of_left hn hP S q h
  · intro n _ hn P hP S q h₁ h₂
    exact carrierWeight_of_mixed hn hP S q h₁ h₂
  · intro n _ hn P hP S
    rfl
  · intro n _ hn P hP
    rw [cornerStateSum_eq_sum_independentSupports, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun S _ => ?_)
    by_cases hu : UniformDecomposition hn hP S.1
    · rw [ite_eq_left hu, wind_of_uniform hn hP S.1 S.2 hu, pow_add]
      ring
    · rw [ite_eq_right hu, wind_of_not_uniform hn hP S.1 hu, mul_zero, zero_mul]

end SM

#print axioms SM.C_X1
