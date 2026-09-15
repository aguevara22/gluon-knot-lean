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


/-! ### Helpers for lem:C-X1

The turn contributed by a true corner, read off its mark alone: an original vertex `i` retains its
turn `τ_i(P)`; a selected visit `v` (arrived along its edge, left along the edge of its twin) turns
by `sgn det(d_{e(v)}, d_{e(twin v)}) = crossingSign …` (lem:carriers (ii),
`ccpCornerPolygon_turn_vertex`, `ccpCornerPolygon_turn_smoothing`). -/

/-- The turn of a true corner as a function of its mark. -/
noncomputable def markTurn (P : LabelledTuple n) : Mark P → SignType
  | Sum.inl i => turn P i
  | Sum.inr v => crossingSign P v.2.val (visitTwin v).2.val

omit [NeZero n] in
@[simp] theorem markTurn_inl (P : LabelledTuple n) (i : ZMod n) :
    markTurn P (Sum.inl i) = turn P i := rfl

omit [NeZero n] in
@[simp] theorem markTurn_inr (P : LabelledTuple n) (v : Visit P) :
    markTurn P (Sum.inr v) = crossingSign P v.2.val (visitTwin v).2.val := rfl

omit [NeZero n] in
/-- The two visits of a crossing turn oppositely. -/
theorem markTurn_visitTwin (P : LabelledTuple n) (v : Visit P) :
    markTurn P (Sum.inr (visitTwin v)) = - markTurn P (Sum.inr v) := by
  rw [markTurn_inr, markTurn_inr, visitTwin_involutive]
  exact crossingSign_swap P _ _

/-- "Every original vertex … retains its turn", and the smoothing corner at a selected visit turns
by the crossing sign: the turn of the carrier at its `j`-th corner is `markTurn` of that corner. -/
theorem turn_ccpCornerPolygon_eq_markTurn (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    {S : Finset (Crossing P)} (hS : S ∈ independentSupports hn hP) (q : Component hn hP S)
    (j : ZMod (ccpCornerCount hn hP S q)) :
    turn (ccpCornerPolygon hn hP S q) j = markTurn P (ccpCornerMark hn hP S q j) := by
  cases hm : ccpCornerMark hn hP S q j with
  | inl i => rw [ccpCornerPolygon_turn_vertex hn hP hS q j i hm, markTurn_inl]
  | inr v =>
    have hv : v.1 ∈ S := by
      have h := ccpCornerMark_isTrueCorner hn hP S q j
      rw [hm] at h
      exact h
    rw [ccpCornerPolygon_turn_smoothing hn hP hS q j v hm hv, markTurn_inr]

/-- A selected visit turns nonzero (lem:carriers (ii): all carrier turns are nonzero). -/
theorem markTurn_ne_zero (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    {S : Finset (Crossing P)} (hS : S ∈ independentSupports hn hP) (v : Visit P) (hv : v.1 ∈ S) :
    markTurn P (Sum.inr v) ≠ 0 := by
  obtain ⟨j, hj⟩ := ccpCornerMark_exists hn hP S (owner hn hP S (Sum.inr v)) (Sum.inr v) rfl hv
  have h := turn_ccpCornerPolygon_eq_markTurn hn hP hS (owner hn hP S (Sum.inr v)) j
  rw [hj] at h
  rw [← h]
  exact ccpCornerPolygon_turn_ne_zero hn hP hS _ j

/-! ### The selector weight of a carrier -/

/-- A uniform carrier has weight `(−1)^{#left corners}`: `(−1)^{k(L)}` if all-left (`ℓ_L = k(L)`),
`1` if all-right (`ℓ_L = 0`). -/
theorem carrierWeight_eq_of_uniform (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) (q : Component hn hP S) (hu : CarrierUniform hn hP S q) :
    carrierWeight hn hP S q = (-1) ^ carrierLeftTurns hn hP S q := by
  obtain ⟨τ, hτ, h⟩ := hu
  rcases SignType.trichotomy τ with rfl | rfl | rfl
  · -- all turns right
    unfold carrierWeight
    rw [ite_eq_left h]
    have h0 : carrierLeftTurns hn hP S q = 0 := by
      unfold carrierLeftTurns leftTurns
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro j _ hj
      rw [h j] at hj
      exact absurd hj (by decide)
    rw [h0, pow_zero]
  · exact absurd rfl hτ
  · -- all turns left
    have hne : ¬ ∀ j, turn (ccpCornerPolygon hn hP S q) j = -1 := fun h' => by
      have h0 := h' 0
      rw [h 0] at h0
      exact absurd h0 (by decide)
    unfold carrierWeight
    rw [ite_eq_right hne, ite_eq_left h]
    congr 1
    unfold carrierLeftTurns leftTurns
    rw [Finset.filter_true_of_mem (fun j _ => h j), Finset.card_univ, ZMod.card]

/-- "a mixed carrier makes its selector product zero" -/
theorem carrierWeight_eq_zero_of_not_uniform (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) (q : Component hn hP S) (hu : ¬ CarrierUniform hn hP S q) :
    carrierWeight hn hP S q = 0 := by
  have h1 : ¬ ∀ j, turn (ccpCornerPolygon hn hP S q) j = -1 := fun h => hu ⟨-1, by decide, h⟩
  have h2 : ¬ ∀ j, turn (ccpCornerPolygon hn hP S q) j = 1 := fun h => hu ⟨1, by decide, h⟩
  unfold carrierWeight
  rw [ite_eq_right h1, ite_eq_right h2]

theorem wind_eq_zero_of_not_uniform (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) (hu : ¬ UniformDecomposition hn hP S) : wind hn hP S = 0 := by
  obtain ⟨q, hq⟩ := not_forall.mp hu
  exact Finset.prod_eq_zero (Finset.mem_univ q) (carrierWeight_eq_zero_of_not_uniform hn hP S q hq)

/-- For a uniform support, `wind(S) = (−1)^{total number of left carrier corners}`. -/
theorem wind_eq_pow_of_uniform (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) (hu : UniformDecomposition hn hP S) :
    wind hn hP S = (-1) ^ ∑ q : Component hn hP S, carrierLeftTurns hn hP S q := by
  unfold wind
  rw [← Finset.prod_pow_eq_pow_sum]
  exact Finset.prod_congr rfl fun q _ => carrierWeight_eq_of_uniform hn hP S q (hu q)

/-! ### Counting the left carrier corners: `Σ_L ℓ_L = ℓ(P) + |S|` -/

open Classical in
/-- The left corners of the carrier `q` are its owned true corners of left `markTurn`
(the corner marks `ccpCornerMark hn hP S q` are a bijection onto the true corners owned by `q`). -/
theorem carrierLeftTurns_eq_card_marks (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    {S : Finset (Crossing P)} (hS : S ∈ independentSupports hn hP) (q : Component hn hP S) :
    carrierLeftTurns hn hP S q =
      (Finset.univ.filter fun m : Mark P =>
        owner hn hP S m = q ∧ IsTrueCorner S m ∧ markTurn P m = 1).card := by
  unfold carrierLeftTurns leftTurns
  refine Finset.card_bij (fun j _ => ccpCornerMark hn hP S q j) ?_ ?_ ?_
  · intro j hj
    rw [Finset.mem_filter] at hj ⊢
    refine ⟨Finset.mem_univ _, ccpCornerMark_owner hn hP S q j,
      ccpCornerMark_isTrueCorner hn hP S q j, ?_⟩
    rw [← turn_ccpCornerPolygon_eq_markTurn hn hP hS q j]
    exact hj.2
  · intro j₁ _ j₂ _ h
    exact ccpCornerMark_injective hn hP S q h
  · intro m hm
    rw [Finset.mem_filter] at hm
    obtain ⟨j, hj⟩ := ccpCornerMark_exists hn hP S q m hm.2.1 hm.2.2.1
    refine ⟨j, ?_, hj⟩
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [turn_ccpCornerPolygon_eq_markTurn hn hP hS q j, hj]
    exact hm.2.2.2

open Classical in
/-- "Every original vertex belongs to exactly one carrier": summing over the owners, the left
carrier corners are the true corners of left `markTurn`. -/
theorem sum_carrierLeftTurns_eq_card (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    {S : Finset (Crossing P)} (hS : S ∈ independentSupports hn hP) :
    ∑ q : Component hn hP S, carrierLeftTurns hn hP S q =
      (Finset.univ.filter fun m : Mark P => IsTrueCorner S m ∧ markTurn P m = 1).card := by
  symm
  rw [Finset.card_eq_sum_card_fiberwise (f := owner hn hP S) (t := Finset.univ)
    (fun m _ => Finset.mem_univ _)]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [carrierLeftTurns_eq_card_marks hn hP hS q, Finset.filter_filter]
  congr 1
  exact Finset.filter_congr fun m _ => and_comm

open Classical in
/-- "Every selected crossing contributes one left and one right smoothing corner": the selected
visits of left turn are in bijection with `S`. -/
theorem card_selected_left_visits (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    {S : Finset (Crossing P)} (hS : S ∈ independentSupports hn hP) :
    (Finset.univ.filter fun v : Visit P =>
      IsTrueCorner S (Sum.inr v) ∧ markTurn P (Sum.inr v) = 1).card = S.card := by
  refine Finset.card_bij (fun v _ => v.1) ?_ ?_ ?_
  · intro v hv
    rw [Finset.mem_filter] at hv
    exact hv.2.1
  · intro v hv w hw hvw
    rw [Finset.mem_filter] at hv hw
    rcases visit_eq_or_twin v w hvw.symm with h | h
    · exact h.symm
    · exfalso
      have h1 := hw.2.2
      rw [h, markTurn_visitTwin, hv.2.2] at h1
      exact absurd h1 (by decide)
  · intro c hc
    obtain ⟨i, hi⟩ := Finset.card_pos.mp (by rw [crossing_card_two c]; norm_num : 0 < c.val.card)
    have hv : ((⟨c, ⟨i, hi⟩⟩ : Visit P)).1 ∈ S := hc
    have hne := markTurn_ne_zero hn hP hS ⟨c, ⟨i, hi⟩⟩ hv
    rcases SignType.trichotomy (markTurn P (Sum.inr (⟨c, ⟨i, hi⟩⟩ : Visit P))) with h | h | h
    · refine ⟨visitTwin ⟨c, ⟨i, hi⟩⟩, ?_, rfl⟩
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, hv, ?_⟩
      rw [markTurn_visitTwin, h]
      rfl
    · exact absurd h hne
    · exact ⟨⟨c, ⟨i, hi⟩⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv, h⟩, rfl⟩

open Classical in
/-- "the total number of left carrier corners is `ℓ(P) + |S|`", as a count of true corners. -/
theorem card_trueCorner_left (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    {S : Finset (Crossing P)} (hS : S ∈ independentSupports hn hP) :
    (Finset.univ.filter fun m : Mark P => IsTrueCorner S m ∧ markTurn P m = 1).card =
      leftTurns P + S.card := by
  rw [Finset.card_filter, Fintype.sum_sum_type, ← Finset.card_filter, ← Finset.card_filter,
    card_selected_left_visits hn hP hS]
  congr 1
  unfold leftTurns
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, isTrueCorner_vertex, markTurn_inl]

/-- "Thus the total number of left carrier corners is `ℓ(P) + |S|`." -/
theorem sum_carrierLeftTurns (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    {S : Finset (Crossing P)} (hS : S ∈ independentSupports hn hP) :
    ∑ q : Component hn hP S, carrierLeftTurns hn hP S q = leftTurns P + S.card := by
  rw [sum_carrierLeftTurns_eq_card hn hP hS, card_trueCorner_left hn hP hS]

/-- "Their selector product is therefore `(−1)^{ℓ(P)+|S|}`": for a uniform decomposition. -/
theorem wind_eq_of_uniform (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    {S : Finset (Crossing P)} (hS : S ∈ independentSupports hn hP)
    (hu : UniformDecomposition hn hP S) :
    wind hn hP S = (-1) ^ (leftTurns P + S.card) := by
  rw [wind_eq_pow_of_uniform hn hP S hu, sum_carrierLeftTurns hn hP hS]

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

theorem C_X1 : CX1Data where
  weight_right := fun _ _ hn _ hP S q h => by
    unfold carrierWeight
    rw [ite_eq_left h]
  weight_left := fun _ _ hn _ hP S q h => by
    have hne : ¬ ∀ j, turn (ccpCornerPolygon hn hP S q) j = -1 := fun h' => by
      have h0 := h' 0
      rw [h 0] at h0
      exact absurd h0 (by decide)
    unfold carrierWeight
    rw [ite_eq_right hne, ite_eq_left h]
  weight_mixed := fun _ _ hn _ hP S q h1 h2 => by
    unfold carrierWeight
    rw [ite_eq_right h1, ite_eq_right h2]
  wind_eq := fun _ _ _ _ _ _ => rfl
  selector_form := fun _ _ hn _ hP => by
    rw [cornerStateSum_eq_sum_independentSupports, Finset.mul_sum]
    refine Finset.sum_congr rfl fun S _ => ?_
    by_cases hu : UniformDecomposition hn hP S.1
    · rw [ite_eq_left hu, wind_eq_of_uniform hn hP S.2 hu, pow_add]
      ring
    · rw [ite_eq_right hu, wind_eq_zero_of_not_uniform hn hP S.1 hu, mul_zero, zero_mul]

end SM

#print axioms SM.C_X1
