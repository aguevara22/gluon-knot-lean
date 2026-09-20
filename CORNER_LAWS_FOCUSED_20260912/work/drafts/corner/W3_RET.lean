-- W3_Skeleton.lean — corner wave 3 (row 110 thm:C-S7), 2026-09-15: the four open declarations of Corner_Assembled.lean
-- (s7_sliding_law_at 8656-8668, s7_bigon_law_at 9816-9834, thm_C_S7_of / thm_C_S7_of_floor 10008-10039) VERBATIM on top of the
-- ported library (SM.CornerChainUnits = waves 1-2a, SM.CS7Sliding = wave 2b, SM.BigonDeletion = the moves toolkit,
-- SM.CarrierFloorRows = thm_floor), plus the row theorem. Units APPEND prefixed material and may replace ONLY the two `sorry`
-- bodies; statements, names and docstrings are frozen (audit A-110-1, AUTHOR_NOTES 20:46Z).
import SM.CornerChainUnits
import SM.CS7Sliding
import SM.BigonDeletion
import SM.CarrierFloorRows

namespace SM

open Link Carrier

attribute [local instance] Classical.propDecidable

noncomputable section

section VertexEdge

variable {n : ℕ} [NeZero n]

/-! ### Unit RET (prefix `s7r_`; serving the leaf `s7_sliding_law_at`): the first-return law
`s7b_SlidingTransport.ret` (U_S7B_REPORT §2.1, W2_S7E_REPORT §2 item 2).
Part I — a generic first-return engine on any generic polygon: a mark is *transit* for `(S, ι)`
when it is off the image of `ι` and the smoothing successor acts on it as the plain successor;
if every mark cyclically between `u` and `m'` is transit, the `f`-iterates of `nextMark u` reach
`m'` without touching the image (descent on the number of marks between, `s7a_between_trans`).
Part II — the side polygon of a sliding wall with leg `M − 1` (`f = false`): the marks of `Q`
carried from the halves, their parameter order (the half laws `s7b_visitParameter_*` composed with
`VertexLocalData.visit_order`, and the side-of-`r` law), the non-image marks, and the first-return
law itself.  DEFECT (rule 4): on the side with leg `M` (`f = true`) `s7b_SlidingTransport.ret` is
FALSE as stated — there `nextMark μ_M = v_ℓ` (`s7e_owner_vl_eq_vertex`), so the first `f`-step from
`ι (inl (inl 0)) = μ_M` lands on `ι (inr (inl 0)) = v_ℓ`, an image mark of the OTHER half; the
correct mark map on that side sends `inl (inl 0) ↦ v_a` and `inr (inl 0) ↦ μ_M` (the leg visit is
the skipped extra corner).  It is stated as `s7r_SlidingTransport'` below. -/

section S7RReturn

variable (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)

/-- A mark is *transit* for `(S, ι)`: off the image of `ι`, and the smoothing successor of `S` acts
on it as the plain successor. -/
def s7r_Transit {β : Type*} (S : Finset (Crossing P)) (ι : β → Mark P) (w : Mark P) : Prop :=
  w ∉ Set.range ι ∧ smoothingSuccessor hn hP S w = nextMark hn hP w

omit [NeZero n] in
theorem s7r_not_between_self (p r : Mark P) :
    ¬ traversalBetween (markPosition hn hP.1 p) (markPosition hn hP.1 p) (markPosition hn hP.1 r) := by
  rw [s7e_between_iff hn hP]
  rintro (⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩) <;> linarith

/-- The successor of `u` lies cyclically between `u` and any third mark `m'`. -/
theorem s7r_between_nextMark (u m' : Mark P) (hne : u ≠ m') (hne' : nextMark hn hP u ≠ m') :
    traversalBetween (markPosition hn hP.1 u) (markPosition hn hP.1 (nextMark hn hP u))
      (markPosition hn hP.1 m') := by
  have hne2 : u ≠ nextMark hn hP u := (markSuccessor_ne_self hn hP u).symm
  rcases s7a_between_or hn hP u (nextMark hn hP u) m' hne2 hne' hne with h | h
  · exact h
  · exact absurd h (nextMark_no_mark_between hn hP rfl m')

/-- The marks between `nextMark u` and `m'` are strictly fewer than those between `u` and `m'`. -/
theorem s7r_card_lt (u m' : Mark P) (hne : u ≠ m') (hnext : nextMark hn hP u ≠ m') :
    (Finset.univ.filter fun w : Mark P => traversalBetween (markPosition hn hP.1 (nextMark hn hP u))
        (markPosition hn hP.1 w) (markPosition hn hP.1 m')).card <
    (Finset.univ.filter fun w : Mark P => traversalBetween (markPosition hn hP.1 u)
        (markPosition hn hP.1 w) (markPosition hn hP.1 m')).card := by
  have hb := s7r_between_nextMark hn hP u m' hne hnext
  apply Finset.card_lt_card
  have hsubset : (Finset.univ.filter fun w : Mark P => traversalBetween
        (markPosition hn hP.1 (nextMark hn hP u)) (markPosition hn hP.1 w) (markPosition hn hP.1 m')) ⊆
      (Finset.univ.filter fun w : Mark P => traversalBetween (markPosition hn hP.1 u)
        (markPosition hn hP.1 w) (markPosition hn hP.1 m')) := by
    intro w hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
    exact s7a_between_trans hn hP hb hw
  refine (Finset.ssubset_iff_of_subset hsubset).mpr ⟨nextMark hn hP u, ?_, ?_⟩
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hb
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact s7r_not_between_self hn hP _ _

/-- **The reach lemma**: if every mark cyclically between `u` and `m'` is transit, the iterates of
the smoothing successor starting at `nextMark u` reach `m'` while staying off the image. -/
theorem s7r_reach_of_transit {β : Type*} (S : Finset (Crossing P)) (ι : β → Mark P) (m' : Mark P) :
    ∀ (c : ℕ) (u : Mark P),
      (Finset.univ.filter fun w : Mark P => traversalBetween (markPosition hn hP.1 u)
        (markPosition hn hP.1 w) (markPosition hn hP.1 m')).card = c →
      u ≠ m' →
      (∀ w, traversalBetween (markPosition hn hP.1 u) (markPosition hn hP.1 w) (markPosition hn hP.1 m') →
        s7r_Transit hn hP S ι w) →
      ∃ k : ℕ, ((smoothingSuccessor hn hP S) ^ k) (nextMark hn hP u) = m' ∧
        ∀ j : ℕ, j < k → ((smoothingSuccessor hn hP S) ^ j) (nextMark hn hP u) ∉ Set.range ι := by
  intro c
  induction c using Nat.strong_induction_on with
  | _ c ih =>
    intro u hc hne htr
    by_cases hnext : nextMark hn hP u = m'
    · exact ⟨0, by simpa using hnext, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
    · have hb := s7r_between_nextMark hn hP u m' hne hnext
      have htrans := htr _ hb
      have hlt := s7r_card_lt hn hP u m' hne hnext
      rw [hc] at hlt
      obtain ⟨k, hk, hgap⟩ := ih _ hlt (nextMark hn hP u) rfl hnext
        (fun w hw => htr w (s7a_between_trans hn hP hb hw))
      refine ⟨k + 1, ?_, ?_⟩
      · rw [pow_succ, Equiv.Perm.mul_apply, htrans.2]; exact hk
      · intro j hj
        rcases Nat.eq_zero_or_pos j with rfl | hj0
        · simpa using htrans.1
        · obtain ⟨j', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj0.ne'
          rw [pow_succ, Equiv.Perm.mul_apply, htrans.2]
          exact hgap j' (by omega)

/-- **The hit lemma**: with one image mark `m'` as beacon, every mark reaches the image provided each
off-image mark either steps into the image or steps as the plain successor. -/
theorem s7r_hit_of_transit {β : Type*} (S : Finset (Crossing P)) (ι : β → Mark P) (m' : Mark P)
    (hm' : m' ∈ Set.range ι)
    (hstep : ∀ w : Mark P, w ∉ Set.range ι →
      (∃ j : ℕ, ((smoothingSuccessor hn hP S) ^ j) w ∈ Set.range ι) ∨
        smoothingSuccessor hn hP S w = nextMark hn hP w) :
    ∀ (c : ℕ) (u : Mark P),
      (Finset.univ.filter fun w : Mark P => traversalBetween (markPosition hn hP.1 u)
        (markPosition hn hP.1 w) (markPosition hn hP.1 m')).card = c →
      ∃ j : ℕ, ((smoothingSuccessor hn hP S) ^ j) u ∈ Set.range ι := by
  intro c
  induction c using Nat.strong_induction_on with
  | _ c ih =>
    intro u hc
    by_cases hu : u ∈ Set.range ι
    · exact ⟨0, by simpa using hu⟩
    · rcases hstep u hu with ⟨j, hj⟩ | h1
      · exact ⟨j, hj⟩
      · by_cases hne : u = m'
        · exact absurd (hne ▸ hm') hu
        · by_cases hnext : nextMark hn hP u = m'
          · exact ⟨1, by rw [pow_one, h1, hnext]; exact hm'⟩
          · have hlt := s7r_card_lt hn hP u m' hne hnext
            rw [hc] at hlt
            obtain ⟨j, hj⟩ := ih _ hlt (nextMark hn hP u) rfl
            exact ⟨j + 1, by rw [pow_succ, Equiv.Perm.mul_apply, h1]; exact hj⟩

/-- A reach from `ι b` through `u := selectedMarkPerm S (ι b)` is a `step` of `s7b_ReturnTransport`. -/
theorem s7r_step_of_reach {β : Type*} (S : Finset (Crossing P)) (ι : β → Mark P) (b : β) (m' u : Mark P)
    (hu : selectedMarkPerm S (ι b) = u)
    (hreach : ∃ k : ℕ, ((smoothingSuccessor hn hP S) ^ k) (nextMark hn hP u) = m' ∧
        ∀ j : ℕ, j < k → ((smoothingSuccessor hn hP S) ^ j) (nextMark hn hP u) ∉ Set.range ι) :
    ∃ k : ℕ, 0 < k ∧ ((smoothingSuccessor hn hP S) ^ k) (ι b) = m' ∧
      ∀ j : ℕ, 0 < j → j < k → ((smoothingSuccessor hn hP S) ^ j) (ι b) ∉ Set.range ι := by
  obtain ⟨k, hk, hgap⟩ := hreach
  have hf : smoothingSuccessor hn hP S (ι b) = nextMark hn hP u := by
    rw [← hu]; rfl
  refine ⟨k + 1, Nat.succ_pos k, ?_, ?_⟩
  · rw [pow_succ, Equiv.Perm.mul_apply, hf]; exact hk
  · intro j hj0 hjk
    obtain ⟨j', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj0.ne'
    rw [pow_succ, Equiv.Perm.mul_apply, hf]
    exact hgap j' (by omega)

/-- Composition of reaches through one off-image mark `w` (the contact `a`-visit, whose smoothing
successor is NOT its plain successor). -/
theorem s7r_reach_trans {β : Type*} (S : Finset (Crossing P)) (ι : β → Mark P) {v w m' : Mark P}
    (h1 : ∃ k : ℕ, ((smoothingSuccessor hn hP S) ^ k) v = w ∧
      ∀ j : ℕ, j < k → ((smoothingSuccessor hn hP S) ^ j) v ∉ Set.range ι)
    (hw : w ∉ Set.range ι)
    (h2 : ∃ k : ℕ, ((smoothingSuccessor hn hP S) ^ k) (smoothingSuccessor hn hP S w) = m' ∧
      ∀ j : ℕ, j < k → ((smoothingSuccessor hn hP S) ^ j) (smoothingSuccessor hn hP S w) ∉ Set.range ι) :
    ∃ k : ℕ, ((smoothingSuccessor hn hP S) ^ k) v = m' ∧
      ∀ j : ℕ, j < k → ((smoothingSuccessor hn hP S) ^ j) v ∉ Set.range ι := by
  obtain ⟨k₁, hk₁, hg₁⟩ := h1
  obtain ⟨k₂, hk₂, hg₂⟩ := h2
  have hstep : ∀ j : ℕ, ((smoothingSuccessor hn hP S) ^ (k₁ + 1 + j)) v =
      ((smoothingSuccessor hn hP S) ^ j) (smoothingSuccessor hn hP S w) := by
    intro j
    rw [show k₁ + 1 + j = j + (k₁ + 1) by omega, pow_add, Equiv.Perm.mul_apply, pow_succ',
      Equiv.Perm.mul_apply, hk₁]
  refine ⟨k₁ + 1 + k₂, ?_, ?_⟩
  · rw [hstep k₂]; exact hk₂
  · intro j hj
    rcases Nat.lt_or_ge j k₁ with hlt | hge
    · exact hg₁ j hlt
    · rcases Nat.eq_or_lt_of_le hge with heq | hgt
      · rw [← heq, hk₁]; exact hw
      · obtain ⟨j', rfl⟩ : ∃ j', j = k₁ + 1 + j' := ⟨j - (k₁ + 1), by omega⟩
        rw [hstep j']
        exact hg₂ j' (by omega)

/-- Key decoder (a): a mark cyclically between a mark `u` on edge `e` and the vertex `e + 1` lies on
edge `e` beyond `u` (wrap `e = −1` included). -/
theorem s7r_between_next_vertex (u w : Mark P) (e : ZMod n) (hu : s7e_mEdge u = e)
    (hb : traversalBetween (markPosition hn hP.1 u) (markPosition hn hP.1 w)
      (markPosition hn hP.1 (Sum.inl (e + 1)))) :
    s7e_mEdge w = e ∧ s7e_mParam u < s7e_mParam w := by
  rw [s7e_between_iff hn hP, markKey_vertex, s7e_markKey_eq hn hP u, s7e_markKey_eq hn hP w, hu] at hb
  have hpu0 := s7e_mParam_nonneg hn hP u
  have hpu1 := s7e_mParam_lt_one hn hP u
  have hpw0 := s7e_mParam_nonneg hn hP w
  have hpw1 := s7e_mParam_lt_one hn hP w
  have hw0 : (0 : ℝ) ≤ (s7e_mEdge w).val := Nat.cast_nonneg _
  have he0 : (0 : ℝ) ≤ e.val := Nat.cast_nonneg _
  rcases s7e_val_succ e with ⟨-, hval⟩ | ⟨-, hzero, hval⟩
  · rw [hval] at hb
    rcases hb with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have he := s7e_edge_eq_of_key_sandwich hpu0 hpw0 hpw1 h1 h2
      refine ⟨he, ?_⟩
      rw [he] at h1; linarith
    · linarith
    · linarith
  · rw [hzero, ZMod.val_zero, Nat.cast_zero, hval] at hb
    have h3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
    rcases hb with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · linarith
    · linarith
    · have h5 : n < (s7e_mEdge w).val + 2 := by
        have : ((n : ℝ)) < (s7e_mEdge w).val + 2 := by linarith
        exact_mod_cast this
      have h6 := ZMod.val_lt (s7e_mEdge w)
      have h7 : (s7e_mEdge w).val = n - 1 := by omega
      have h7' : ((s7e_mEdge w).val : ℝ) = (n : ℝ) - 1 := by
        rw [h7, Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
      have he : s7e_mEdge w = e := by
        apply ZMod.val_injective
        exact_mod_cast h7'.trans hval.symm
      refine ⟨he, ?_⟩
      rw [h7'] at h2; linarith

/-- Key decoder (b): a mark cyclically between two marks `u`, `m'` on one edge `e` with
`param u < param m'` lies on edge `e` with its parameter strictly between theirs. -/
theorem s7r_between_same_edge_of (u w m' : Mark P) (e : ZMod n) (hu : s7e_mEdge u = e)
    (hm' : s7e_mEdge m' = e) (hlt : s7e_mParam u < s7e_mParam m')
    (hb : traversalBetween (markPosition hn hP.1 u) (markPosition hn hP.1 w) (markPosition hn hP.1 m')) :
    s7e_mEdge w = e ∧ s7e_mParam u < s7e_mParam w ∧ s7e_mParam w < s7e_mParam m' := by
  rw [s7e_between_iff hn hP, s7e_markKey_eq hn hP u, s7e_markKey_eq hn hP w, s7e_markKey_eq hn hP m',
    hu, hm'] at hb
  have hpu0 := s7e_mParam_nonneg hn hP u
  have hpw0 := s7e_mParam_nonneg hn hP w
  have hpw1 := s7e_mParam_lt_one hn hP w
  have hpm1 := s7e_mParam_lt_one hn hP m'
  rcases hb with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have he : s7e_mEdge w = e := s7e_edge_eq_of_key_sandwich hpu0 hpw0 hpw1 h1 (by linarith)
    rw [he] at h1 h2
    exact ⟨he, by linarith, by linarith⟩
  · linarith
  · linarith

end S7RReturn

section S7RSide

/-! #### Part II: a side polygon `Q` of a sliding wall with leg `M − 1` (`f = false`), relative to
the centre `P` with contact parameter `r` and window half-width `η`.  `hord` is
`VertexLocalData.visit_order` (the same-edge parameter order of persistent visits agrees between `Q`
and the centre) and `hside` the side-of-`r` law on edge `a` (sign constancy through the centre,
`s7a2_pos_of_ne_zero` at `u = 0`). -/

variable (hn : 3 ≤ n) {P Q : LabelledTuple n} (hQ : Generic Q) {M a : ZMod n}
  (hsep : ContactSeparated M a) (hz : pointZeroTriples P = {contactSupport M a})
  (hm : P M ∈ edgeInterior P a) {r η : ℝ} (hr : P M = edgePoint P a r) (hr0 : 0 < r) (hr1 : r < 1)
  (hη : 0 < η)
  (hQC : ∀ s, ¬ ContactAffected M a s → (IsCrossing Q s ↔ IsCrossing P s))
  (hw : ContactParameterWindows P Q M a r η)
  (hord : ∀ (u u' : Visit P) (hu : ¬ ContactAffected M a u.1.val) (hu' : ¬ ContactAffected M a u'.1.val),
    u.2.val = u'.2.val →
    (visitParameter (s7a_visit hQC u hu) < visitParameter (s7a_visit hQC u' hu') ↔
      visitParameter u < visitParameter u'))
  (hside : ∀ (u : Visit P) (hu : ¬ ContactAffected M a u.1.val), u.2.val = a →
    (visitParameter (s7a_visit hQC u hu) < r ↔ visitParameter u < r))
  (h₁ : Generic (firstHalf P M a)) (h₂ : Generic (secondHalf P M a))

theorem s7r_firstVisitQ_eq (v : Visit (firstHalf P M a)) :
    s7b_firstVisitQ hn hsep hm hQC v =
      s7a_visit hQC (s7b_firstHalfVisit hn hsep hm v) (s7b_firstHalfCrossing_not_affected hn hsep hm v.1) :=
  rfl

theorem s7r_secondVisitQ_eq (v : Visit (secondHalf P M a)) :
    s7b_secondVisitQ hn hsep hm hQC v =
      s7a_visit hQC (s7b_secondHalfVisit hn hsep hm v) (s7b_secondHalfCrossing_not_affected hn hsep hm v.1) :=
  rfl

include hz hr hr0 hord in
/-- Same-edge order of the carried visits of `λ₁` on `Q` is the order on `λ₁` (equality of parameters
off the cut, the rescaling `r · t` on it, then `visit_order`). -/
theorem s7r_first_order (v v' : Visit (firstHalf P M a)) (he : v.2.val = v'.2.val) :
    visitParameter (s7b_firstVisitQ hn hsep hm hQC v) < visitParameter (s7b_firstVisitQ hn hsep hm hQC v') ↔
      visitParameter v < visitParameter v' := by
  rw [s7r_firstVisitQ_eq, s7r_firstVisitQ_eq,
    hord (s7b_firstHalfVisit hn hsep hm v) (s7b_firstHalfVisit hn hsep hm v')
      (s7b_firstHalfCrossing_not_affected hn hsep hm v.1) (s7b_firstHalfCrossing_not_affected hn hsep hm v'.1)
      (by rw [s7b_firstHalfVisit_edge hn hsep hm v, s7b_firstHalfVisit_edge hn hsep hm v', he])]
  by_cases hc : v.2.val = -1
  · have hc' : v'.2.val = -1 := he.symm.trans hc
    rw [s7b_visitParameter_firstHalfVisit_cut hn hsep hz hm hr v hc,
      s7b_visitParameter_firstHalfVisit_cut hn hsep hz hm hr v' hc']
    constructor
    · intro h; exact lt_of_not_ge fun h' => by nlinarith
    · intro h; nlinarith
  · have hc' : v'.2.val ≠ -1 := fun h => hc (he.trans h)
    rw [s7b_visitParameter_firstHalfVisit hn hsep hz hm v hc,
      s7b_visitParameter_firstHalfVisit hn hsep hz hm v' hc']

include hz hr hr1 hord in
theorem s7r_second_order (v v' : Visit (secondHalf P M a)) (he : v.2.val = v'.2.val) :
    visitParameter (s7b_secondVisitQ hn hsep hm hQC v) < visitParameter (s7b_secondVisitQ hn hsep hm hQC v') ↔
      visitParameter v < visitParameter v' := by
  rw [s7r_secondVisitQ_eq, s7r_secondVisitQ_eq,
    hord (s7b_secondHalfVisit hn hsep hm v) (s7b_secondHalfVisit hn hsep hm v')
      (s7b_secondHalfCrossing_not_affected hn hsep hm v.1) (s7b_secondHalfCrossing_not_affected hn hsep hm v'.1)
      (by rw [s7b_secondHalfVisit_edge hn hsep hm v, s7b_secondHalfVisit_edge hn hsep hm v', he])]
  by_cases hc : v.2.val = 0
  · have hc' : v'.2.val = 0 := he.symm.trans hc
    rw [s7b_visitParameter_secondHalfVisit_cut hn hsep hz hm hr v hc,
      s7b_visitParameter_secondHalfVisit_cut hn hsep hz hm hr v' hc']
    have h1r : 0 < 1 - r := by linarith
    constructor
    · intro h; exact lt_of_not_ge fun h' => by nlinarith
    · intro h; nlinarith
  · have hc' : v'.2.val ≠ 0 := fun h => hc (he.trans h)
    rw [s7b_visitParameter_secondHalfVisit hn hsep hz hm v hc,
      s7b_visitParameter_secondHalfVisit hn hsep hz hm v' hc']

include hQ hz hr hr0 hw hside h₁ in
/-- A carried cut visit of `λ₁` lies on edge `a` of `Q` below `r − 3η`. -/
theorem s7r_first_cut_lt (v : Visit (firstHalf P M a)) (hv : v.2.val = -1) :
    visitParameter (s7b_firstVisitQ hn hsep hm hQC v) < r - 3 * η := by
  have hlt : visitParameter (s7b_firstVisitQ hn hsep hm hQC v) < r := by
    rw [s7r_firstVisitQ_eq, hside (s7b_firstHalfVisit hn hsep hm v) (s7b_firstHalfCrossing_not_affected hn hsep hm v.1)
      (by rw [s7b_firstHalfVisit_edge hn hsep hm v, hv, firstHalfIndex_last]),
      s7b_visitParameter_firstHalfVisit_cut hn hsep hz hm hr v hv]
    have := s7e_visitParameter_lt_one (contactHalfSizes_bounds hn hsep).1.1 h₁ v
    nlinarith
  have hwin := s7e_persist_a hn hQ hw (s7b_firstVisitQ hn hsep hm hQC v)
    (s7b_firstCrossingQ_not_affected hn hsep hm hQC v.1) (by rw [s7b_firstVisitQ_edge, hv, firstHalfIndex_last])
  rw [abs_of_neg (by linarith)] at hwin
  linarith

include hQ hz hr hr1 hw hside h₂ in
/-- A carried cut visit of `λ₂` lies on edge `a` of `Q` above `r + 3η`. -/
theorem s7r_second_cut_gt (v : Visit (secondHalf P M a)) (hv : v.2.val = 0) :
    r + 3 * η < visitParameter (s7b_secondVisitQ hn hsep hm hQC v) := by
  have hle : r ≤ visitParameter (s7b_secondVisitQ hn hsep hm hQC v) := by
    rw [← not_lt, s7r_secondVisitQ_eq, hside (s7b_secondHalfVisit hn hsep hm v)
      (s7b_secondHalfCrossing_not_affected hn hsep hm v.1)
      (by rw [s7b_secondHalfVisit_edge hn hsep hm v, hv, secondHalfEdgeIndex_zero]),
      s7b_visitParameter_secondHalfVisit_cut hn hsep hz hm hr v hv]
    have := s7e_visitParameter_pos (contactHalfSizes_bounds hn hsep).2.1 h₂ v
    intro h; nlinarith
  have hwin := s7e_persist_a hn hQ hw (s7b_secondVisitQ hn hsep hm hQC v)
    (s7b_secondCrossingQ_not_affected hn hsep hm hQC v.1)
    (by rw [s7b_secondVisitQ_edge, hv, secondHalfEdgeIndex_zero])
  rcases lt_or_eq_of_le hle with h | h
  · rw [abs_of_pos (by linarith)] at hwin; linarith
  · rw [← h, sub_self, abs_zero] at hwin; linarith

/-! ##### The contact crossing `{a, M − 1}` on `Q` and the non-image marks -/

variable (hc : IsCrossing Q {a, contactLeg false M})
  (huniq : ∀ y : Crossing Q, ContactAffected M a y.val → y.val = {a, contactLeg false M})

omit [NeZero n] in
theorem s7r_leg_false : contactLeg false M = M - 1 := by simp [contactLeg]

theorem s7r_vl_affected : ContactAffected M a (s7e_vl hc).1.val := by
  rw [s7e_vl_fst]; exact (contactAffected_iff_leg _).mpr ⟨false, rfl⟩

theorem s7r_va_affected : ContactAffected M a (s7e_va hc).1.val :=
  (contactAffected_iff_leg _).mpr ⟨false, rfl⟩

/-- Which visits of `Q` are image marks of the sliding mark map. -/
theorem s7r_inr_mem_range_iff (vm w : Visit Q) :
    (Sum.inr w : Mark Q) ∈ Set.range (s7b_slidingMark hn hsep hm hQC vm) ↔
      w = vm ∨ (∃ v, s7b_firstVisitQ hn hsep hm hQC v = w) ∨ (∃ v, s7b_secondVisitQ hn hsep hm hQC v = w) := by
  constructor
  · rintro ⟨b, hb⟩
    rcases b with (i | v) | (i | v)
    · rw [s7b_slidingMark_inl_inl] at hb; exact absurd hb Sum.inl_ne_inr
    · rw [s7b_slidingMark_inl_inr] at hb; exact Or.inr (Or.inl ⟨v, Sum.inr_injective hb⟩)
    · by_cases hi : i = 0
      · subst hi; rw [s7b_slidingMark_inr_inl_zero] at hb; exact Or.inl (Sum.inr_injective hb).symm
      · rw [s7b_slidingMark_inr_inl hn hsep hm hQC vm hi] at hb; exact absurd hb Sum.inl_ne_inr
    · rw [s7b_slidingMark_inr_inr] at hb; exact Or.inr (Or.inr ⟨v, Sum.inr_injective hb⟩)
  · rintro (rfl | ⟨v, rfl⟩ | ⟨v, rfl⟩)
    · exact ⟨Sum.inr (Sum.inl 0), s7b_slidingMark_inr_inl_zero hn hsep hm hQC _⟩
    · exact ⟨Sum.inl (Sum.inr v), rfl⟩
    · exact ⟨Sum.inr (Sum.inr v), rfl⟩

include hsep in
/-- The contact `a`-visit is not an image mark. -/
theorem s7r_va_not_mem_range :
    (Sum.inr (s7e_va hc) : Mark Q) ∉ Set.range (s7b_slidingMark hn hsep hm hQC (s7e_vl hc)) := by
  rw [s7r_inr_mem_range_iff]
  rintro (h | ⟨v, hv⟩ | ⟨v, hv⟩)
  · exact s7e_vl_ne_va hc (s7e_a_ne_leg false hsep) h.symm
  · exact s7b_firstCrossingQ_not_affected hn hsep hm hQC v.1
      (by rw [← s7b_firstVisitQ_fst hn hsep hm hQC v, hv]; exact s7r_va_affected hc)
  · exact s7b_secondCrossingQ_not_affected hn hsep hm hQC v.1
      (by rw [← s7b_secondVisitQ_fst hn hsep hm hQC v, hv]; exact s7r_va_affected hc)

variable (S : Finset (Crossing Q)) (hxS : (s7e_va hc).1 ∈ S)
  (hSimg : ∀ y ∈ S, y ≠ (s7e_va hc).1 →
    y ∈ Set.range (s7b_firstCrossingQ hn hsep hm hQC) ∪ Set.range (s7b_secondCrossingQ hn hsep hm hQC))

include hsep hSimg in
/-- A visit that is neither contact visit and is carried from neither half is transit. -/
theorem s7r_transit_of (w : Visit Q) (h0 : w ≠ s7e_vl hc)
    (h1 : ∀ v, s7b_firstVisitQ hn hsep hm hQC v ≠ w) (h2 : ∀ v, s7b_secondVisitQ hn hsep hm hQC v ≠ w)
    (ha : w ≠ s7e_va hc) :
    s7r_Transit hn hQ S (s7b_slidingMark hn hsep hm hQC (s7e_vl hc)) (Sum.inr w) := by
  have hnr : (Sum.inr w : Mark Q) ∉ Set.range (s7b_slidingMark hn hsep hm hQC (s7e_vl hc)) := by
    rw [s7r_inr_mem_range_iff]
    rintro (h | ⟨v, hv⟩ | ⟨v, hv⟩)
    · exact h0 h
    · exact h1 v hv
    · exact h2 v hv
  refine ⟨hnr, ?_⟩
  have hwS : w.1 ∉ S := by
    intro hwS
    by_cases hwx : w.1 = (s7e_va hc).1
    · rcases s7e_visit_of_fst hc w (by rw [hwx]; rfl) (s7e_a_ne_leg false hsep) with h | h
      · exact ha h
      · exact h0 h
    · rcases hSimg w.1 hwS hwx with ⟨c, hcw⟩ | ⟨c, hcw⟩
      · obtain ⟨v, -, hv⟩ := s7b_visit_of_firstCrossingQ hn hsep hm hQC w c hcw.symm
        exact h1 v hv
      · obtain ⟨v, -, hv⟩ := s7b_visit_of_secondCrossingQ hn hsep hm hQC w c hcw.symm
        exact h2 v hv
  exact smoothingSuccessor_visit_of_not_mem hn hQ S w hwS

include hsep hSimg in
/-- **The window lemma**: the marks cyclically between `u` (on edge `e`) and a target `m'` — the next
vertex `e + 1`, or a mark on edge `e` beyond `u` — are all transit as soon as every visit of `Q` in the
parameter window is neither contact visit and carried from neither half. -/
theorem s7r_transit_window (u m' : Mark Q) (e : ZMod n) (hu : s7e_mEdge u = e)
    (hm' : m' = Sum.inl (e + 1) ∨ (s7e_mEdge m' = e ∧ s7e_mParam u < s7e_mParam m'))
    (hex : ∀ w' : Visit Q, w'.2.val = e → s7e_mParam u < visitParameter w' →
      (m' = Sum.inl (e + 1) ∨ visitParameter w' < s7e_mParam m') →
      w' ≠ s7e_vl hc ∧ (∀ v, s7b_firstVisitQ hn hsep hm hQC v ≠ w') ∧
        (∀ v, s7b_secondVisitQ hn hsep hm hQC v ≠ w') ∧ w' ≠ s7e_va hc) :
    ∀ w, traversalBetween (markPosition hn hQ.1 u) (markPosition hn hQ.1 w) (markPosition hn hQ.1 m') →
      s7r_Transit hn hQ S (s7b_slidingMark hn hsep hm hQC (s7e_vl hc)) w := by
  intro w hb
  have hdec : s7e_mEdge w = e ∧ s7e_mParam u < s7e_mParam w ∧
      (m' = Sum.inl (e + 1) ∨ s7e_mParam w < s7e_mParam m') := by
    rcases hm' with rfl | ⟨hme, hlt⟩
    · obtain ⟨h1, h2⟩ := s7r_between_next_vertex hn hQ u w e hu hb
      exact ⟨h1, h2, Or.inl rfl⟩
    · obtain ⟨h1, h2, h3⟩ := s7r_between_same_edge_of hn hQ u w m' e hu hme hlt hb
      exact ⟨h1, h2, Or.inr h3⟩
  have hpos : 0 < s7e_mParam w := lt_of_le_of_lt (s7e_mParam_nonneg hn hQ u) hdec.2.1
  obtain ⟨w', rfl⟩ := s7e_mark_visit_of_param_pos w hpos
  obtain ⟨h0, h1, h2, ha⟩ := hex w' hdec.1 hdec.2.1 hdec.2.2
  exact s7r_transit_of hn hQ hsep hm hQC hc S hSimg w' h0 h1 h2 ha

include hQ hsep hη hw huniq in
/-- On the leg-`M−1` side the leg visit is the last mark on edge `M − 1`: `nextMark v_ℓ = μ_M`. -/
theorem s7r_nextMark_vl : nextMark hn hQ (Sum.inr (s7e_vl hc)) = Sum.inl M := by
  have hnext : nextMark hn hQ (Sum.inr (s7e_vl hc)) = Sum.inl ((s7e_vl hc).2.val + 1) := by
    apply s7e_nextMark_inr_eq_inl hn hQ
    intro u hu
    by_cases hul : u = s7e_vl hc
    · rw [hul]
    · have hup := s7e_persistent_of_edge_leg false hsep hc huniq u (hu.trans (s7e_vl_edge hc)) hul
      have h1 := s7e_persist_M_sub_one hn hQ hw u hup (by rw [hu, s7e_vl_edge, s7r_leg_false])
      have h2 := s7e_vl_param_false hn hQ hw hc
      linarith
  rw [hnext, s7e_vl_edge, s7r_leg_false, sub_add_cancel]

include hQ hsep hη hw huniq hxS in
/-- The smoothing successor of the contact `a`-visit in a sliding row is `μ_M`. -/
theorem s7r_succ_va : smoothingSuccessor hn hQ S (Sum.inr (s7e_va hc)) = Sum.inl M := by
  rw [smoothingSuccessor_visit_of_mem hn hQ S _ hxS, s7e_twin_va hc (s7e_a_ne_leg false hsep)]
  exact s7r_nextMark_vl hn hQ hsep hη hw hc huniq

/-! ##### Generic facts about `nextMark` on a half, and the Q-marks of the half marks -/

/-- The successor of a mark on edge `i` is the vertex `i + 1` or a later visit on edge `i`. -/
theorem s7r_nextMark_shape {k : ℕ} [NeZero k] (hk : 3 ≤ k) {L : LabelledTuple k} (hL : Generic L)
    (m₁ : Mark L) :
    nextMark hk hL m₁ = Sum.inl (s7e_mEdge m₁ + 1) ∨
      ∃ w : Visit L, nextMark hk hL m₁ = Sum.inr w ∧ w.2.val = s7e_mEdge m₁ ∧
        s7e_mParam m₁ < visitParameter w := by
  cases m₁ with
  | inl i =>
    rcases s7e_nextMark_inl hk hL i with h | ⟨w, h, hw⟩
    · exact Or.inl h
    · exact Or.inr ⟨w, h, hw, s7e_visitParameter_pos hk hL w⟩
  | inr v =>
    rcases s7e_nextMark_inr hk hL v with h | ⟨w, h, hw, hp⟩
    · exact Or.inl h
    · exact Or.inr ⟨w, h, hw, hp⟩

/-- No visit of a half lies on its edge `i` strictly between a mark `m₁` on edge `i` and `nextMark m₁`. -/
theorem s7r_no_half_between {k : ℕ} [NeZero k] (hk : 3 ≤ k) {L : LabelledTuple k} (hL : Generic L)
    (m₁ : Mark L) (i : ZMod k) (hi : s7e_mEdge m₁ = i) (v' : Visit L) (hv' : v'.2.val = i)
    (hlo : s7e_mParam m₁ < visitParameter v')
    (hhi : nextMark hk hL m₁ = Sum.inl (i + 1) ∨
      (s7e_mEdge (nextMark hk hL m₁) = i ∧ visitParameter v' < s7e_mParam (nextMark hk hL m₁))) :
    False := by
  rcases hhi with h | ⟨he, hlt⟩
  · have hb := s7e_between_mark_mark_inl hk hL m₁ (Sum.inr v')
      (by rw [hi, s7e_mEdge_inr, hv']) hlo
    rw [hi] at hb
    exact nextMark_no_mark_between hk hL h (Sum.inr v') hb
  · have hb := s7e_between_same_edge hk hL m₁ (Sum.inr v') (nextMark hk hL m₁)
      (by rw [hi, s7e_mEdge_inr, hv']) (by rw [s7e_mEdge_inr, hv', he]) hlo hlt
    exact nextMark_no_mark_between hk hL rfl (Sum.inr v') hb

theorem s7r_edge_first (m₁ : Mark (firstHalf P M a)) :
    s7e_mEdge (s7b_slidingMark hn hsep hm hQC (s7e_vl hc) (Sum.inl m₁)) = firstHalfIndex M a (s7e_mEdge m₁) := by
  cases m₁ <;> rfl

include hQ hz hr hr0 hord h₁ in
/-- Parameter transfer for the first half: the Q-parameter order between the Q-mark of `m₁` and a
carried visit on the same edge is the `λ₁`-order. -/
theorem s7r_param_first (m₁ : Mark (firstHalf P M a)) (v' : Visit (firstHalf P M a))
    (he : v'.2.val = s7e_mEdge m₁) :
    s7e_mParam (s7b_slidingMark hn hsep hm hQC (s7e_vl hc) (Sum.inl m₁)) <
        visitParameter (s7b_firstVisitQ hn hsep hm hQC v') ↔
      s7e_mParam m₁ < visitParameter v' := by
  cases m₁ with
  | inl i =>
    exact iff_of_true (s7e_visitParameter_pos hn hQ _)
      (s7e_visitParameter_pos (contactHalfSizes_bounds hn hsep).1.1 h₁ v')
  | inr v => exact s7r_first_order hn hsep hz hm hr hr0 hQC hord v v' he.symm

/-! ##### The first-half reach and step -/

include hQ hz hr hr0 hr1 hη hw hord hside huniq hxS hSimg h₂ in
/-- **First-half reach**: from the Q-mark of `m₁ : Mark λ₁`, the smoothing successor of a sliding row
reaches the Q-mark of `nextMark m₁` through transit marks only (the cut edge closes through the
contact `a`-visit, whose smoothing successor is `μ_M`). -/
theorem s7r_reach_first (hn₁ : 3 ≤ firstHalfSize M a) (m₁ : Mark (firstHalf P M a)) :
    ∃ k : ℕ, ((smoothingSuccessor hn hQ S) ^ k)
        (nextMark hn hQ (s7b_slidingMark hn hsep hm hQC (s7e_vl hc) (Sum.inl m₁))) =
      s7b_slidingMark hn hsep hm hQC (s7e_vl hc) (Sum.inl (nextMark hn₁ h₁ m₁)) ∧
      ∀ j : ℕ, j < k → ((smoothingSuccessor hn hQ S) ^ j)
        (nextMark hn hQ (s7b_slidingMark hn hsep hm hQC (s7e_vl hc) (Sum.inl m₁))) ∉
          Set.range (s7b_slidingMark hn hsep hm hQC (s7e_vl hc)) := by
  have hedge_u : s7e_mEdge (s7b_slidingMark hn hsep hm hQC (s7e_vl hc) (Sum.inl m₁)) =
      firstHalfIndex M a (s7e_mEdge m₁) := s7r_edge_first hn hsep hm hQC hc m₁
  have hinj := s7b_slidingMark_injective hn hsep hm hQC (s7e_vl hc) (s7r_vl_affected hc)
  have hne_u : s7b_slidingMark hn hsep hm hQC (s7e_vl hc) (Sum.inl m₁) ≠
      s7b_slidingMark hn hsep hm hQC (s7e_vl hc) (Sum.inl (nextMark hn₁ h₁ m₁)) := fun h =>
    markSuccessor_ne_self hn₁ h₁ m₁ (Sum.inl.inj (hinj h)).symm
  have hva_near := s7e_va_param_near hn hQ false hw hc
  have hva1 := (abs_lt.mp hva_near).1
  have hva2 := (abs_lt.mp hva_near).2
  -- a carried first-half visit on the edge of `m₁`: its `λ₁`-edge, and the transferred lower bound
  have hfirst : ∀ (w' : Visit Q), w'.2.val = firstHalfIndex M a (s7e_mEdge m₁) →
      ∀ v' : Visit (firstHalf P M a), s7b_firstVisitQ hn hsep hm hQC v' = w' →
      v'.2.val = s7e_mEdge m₁ ∧
        (s7e_mParam (s7b_slidingMark hn hsep hm hQC (s7e_vl hc) (Sum.inl m₁)) < visitParameter w' ↔
          s7e_mParam m₁ < visitParameter v') := by
    intro w' he v' hv'
    have hv'e : v'.2.val = s7e_mEdge m₁ := by
      apply firstHalfIndex_injective M a
      rw [← s7b_firstVisitQ_edge hn hsep hm hQC v', hv', he]
    refine ⟨hv'e, ?_⟩
    rw [← hv']
    exact s7r_param_first hn hQ hsep hz hm hr hr0 hQC hord h₁ hc m₁ v' hv'e
  -- the exclusions shared by every window on a first-half edge other than the cut
  have hoff : ∀ (_ : s7e_mEdge m₁ ≠ -1) (w' : Visit Q), w'.2.val = firstHalfIndex M a (s7e_mEdge m₁) →
      w' ≠ s7e_vl hc ∧ (∀ v, s7b_secondVisitQ hn hsep hm hQC v ≠ w') ∧ w' ≠ s7e_va hc := by
    intro hi1 w' he
    refine ⟨?_, ?_, ?_⟩
    · intro h; rw [h, s7e_vl_edge, s7r_leg_false] at he
      exact s7b_firstHalfIndex_ne_pred hn hsep _ he.symm
    · intro v h; rw [← h, s7b_secondVisitQ_edge] at he
      exact hi1 (s7b_firstHalfIndex_eq_secondHalfEdgeIndex hn hsep he.symm).1
    · intro h; rw [h, s7e_va_edge] at he
      exact hi1 (firstHalfIndex_injective M a (he.symm.trans (firstHalfIndex_last M a).symm))
  -- the exclusions on the cut edge `a`, for a window bounded above by `p' < r + η`
  have hcut : ∀ (_ : s7e_mEdge m₁ = -1) (p' : ℝ) (_ : p' < r + η) (w' : Visit Q), w'.2.val = a →
      visitParameter w' < p' →
      w' ≠ s7e_vl hc ∧ (∀ v, s7b_secondVisitQ hn hsep hm hQC v ≠ w') := by
    intro _ p' hp' w' he hlt
    refine ⟨?_, ?_⟩
    · intro h; rw [h, s7e_vl_edge, s7r_leg_false] at he
      exact s7e_a_ne_M_sub_one hsep he.symm
    · intro v h
      have hv0 : v.2.val = 0 := by
        rw [← h, s7b_secondVisitQ_edge] at he
        exact (s7b_firstHalfIndex_eq_secondHalfEdgeIndex hn hsep
          (by rw [firstHalfIndex_last]; exact he.symm)).2
      have := s7r_second_cut_gt hn hQ hsep hz hm hr hr1 hQC hw hside h₂ v hv0
      rw [h] at this
      linarith
  rcases s7r_nextMark_shape hn₁ h₁ m₁ with hnx | ⟨w, hnx, hwe, hwp⟩
  · by_cases hi1 : s7e_mEdge m₁ = -1
    · -- the cut, vertex target `inl 0 ↦ μ_M`: through the contact `a`-visit
      have hm' : s7b_slidingMark hn hsep hm hQC (s7e_vl hc) (Sum.inl (nextMark hn₁ h₁ m₁)) = Sum.inl M := by
        rw [hnx, hi1, neg_add_cancel, s7b_slidingMark_inl_inl, firstHalfIndex_zero]
      rw [hm']
      have hea : firstHalfIndex M a (s7e_mEdge m₁) = a := by rw [hi1, firstHalfIndex_last]
      have hlt_u : s7e_mParam (s7b_slidingMark hn hsep hm hQC (s7e_vl hc) (Sum.inl m₁)) <
          visitParameter (s7e_va hc) := by
        cases m₁ with
        | inl j => exact s7e_visitParameter_pos hn hQ _
        | inr v =>
          have := s7r_first_cut_lt hn hQ hsep hz hm hr hr0 hQC hw hside h₁ v hi1
          show visitParameter (s7b_firstVisitQ hn hsep hm hQC v) < _
          linarith
      have hne_va : s7b_slidingMark hn hsep hm hQC (s7e_vl hc) (Sum.inl m₁) ≠ Sum.inr (s7e_va hc) :=
        fun h => s7r_va_not_mem_range hn hsep hm hQC hc ⟨_, h⟩
      have hreach₁ := s7r_reach_of_transit hn hQ S _ (Sum.inr (s7e_va hc)) _ _ rfl hne_va
        (s7r_transit_window hn hQ hsep hm hQC hc S hSimg _ _ a (hedge_u.trans hea)
          (Or.inr ⟨s7e_va_edge hc, hlt_u⟩) ?_)
      · refine s7r_reach_trans hn hQ S _ hreach₁ (s7r_va_not_mem_range hn hsep hm hQC hc) ?_
        rw [s7r_succ_va hn hQ hsep hη hw hc huniq S hxS]
        exact ⟨0, by simp, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
      · intro w' he hlo hhi
        have hhi' : visitParameter w' < visitParameter (s7e_va hc) := by
          rcases hhi with h | h
          · exact absurd h Sum.inr_ne_inl
          · exact h
        obtain ⟨h0, h2⟩ := hcut hi1 (visitParameter (s7e_va hc)) (by linarith) w' he hhi'
        refine ⟨h0, ?_, h2, fun h => by rw [h] at hhi'; exact lt_irrefl _ hhi'⟩
        intro v' hv'
        obtain ⟨hv'e, hiff⟩ := hfirst w' (by rw [he, hea]) v' hv'
        exact s7r_no_half_between hn₁ h₁ m₁ _ rfl v' hv'e (hiff.mp hlo) (Or.inl hnx)
    · -- off the cut, vertex target `inl (i + 1) ↦ μ_{firstHalfIndex i + 1}`
      have hm' : s7b_slidingMark hn hsep hm hQC (s7e_vl hc) (Sum.inl (nextMark hn₁ h₁ m₁)) =
          Sum.inl (firstHalfIndex M a (s7e_mEdge m₁) + 1) := by
        rw [hnx, s7b_slidingMark_inl_inl, firstHalfIndex_next M a hi1]
      rw [hm'] at hne_u ⊢
      refine s7r_reach_of_transit hn hQ S _ _ _ _ rfl hne_u
        (s7r_transit_window hn hQ hsep hm hQC hc S hSimg _ _ _ hedge_u (Or.inl rfl) ?_)
      intro w' he hlo _
      obtain ⟨h0, h2, ha⟩ := hoff hi1 w' he
      refine ⟨h0, ?_, h2, ha⟩
      intro v' hv'
      obtain ⟨hv'e, hiff⟩ := hfirst w' he v' hv'
      exact s7r_no_half_between hn₁ h₁ m₁ _ rfl v' hv'e (hiff.mp hlo) (Or.inl hnx)
  · -- target: a visit `w` of `λ₁` on the edge of `m₁`, `↦ firstVisitQ w`
    have hm' : s7b_slidingMark hn hsep hm hQC (s7e_vl hc) (Sum.inl (nextMark hn₁ h₁ m₁)) =
        Sum.inr (s7b_firstVisitQ hn hsep hm hQC w) := by rw [hnx, s7b_slidingMark_inl_inr]
    rw [hm'] at hne_u ⊢
    have hwQe : (s7b_firstVisitQ hn hsep hm hQC w).2.val = firstHalfIndex M a (s7e_mEdge m₁) := by
      rw [s7b_firstVisitQ_edge, hwe]
    have hlt_u : s7e_mParam (s7b_slidingMark hn hsep hm hQC (s7e_vl hc) (Sum.inl m₁)) <
        visitParameter (s7b_firstVisitQ hn hsep hm hQC w) :=
      (s7r_param_first hn hQ hsep hz hm hr hr0 hQC hord h₁ hc m₁ w hwe).mpr hwp
    refine s7r_reach_of_transit hn hQ S _ _ _ _ rfl hne_u
      (s7r_transit_window hn hQ hsep hm hQC hc S hSimg _ _ _ hedge_u (Or.inr ⟨hwQe, hlt_u⟩) ?_)
    intro w' he hlo hhi
    have hhi' : visitParameter w' < visitParameter (s7b_firstVisitQ hn hsep hm hQC w) := by
      rcases hhi with h | h
      · exact absurd h Sum.inr_ne_inl
      · exact h
    have hex1 : ∀ v', s7b_firstVisitQ hn hsep hm hQC v' ≠ w' := by
      intro v' hv'
      obtain ⟨hv'e, hiff⟩ := hfirst w' he v' hv'
      have hup : visitParameter v' < visitParameter w := by
        rw [← hv'] at hhi'
        exact (s7r_first_order hn hsep hz hm hr hr0 hQC hord v' w (hv'e.trans hwe.symm)).mp hhi'
      exact s7r_no_half_between hn₁ h₁ m₁ _ rfl v' hv'e (hiff.mp hlo)
        (Or.inr ⟨by rw [hnx]; exact hwe, by rw [hnx]; exact hup⟩)
    by_cases hi1 : s7e_mEdge m₁ = -1
    · have hea : firstHalfIndex M a (s7e_mEdge m₁) = a := by rw [hi1, firstHalfIndex_last]
      have hwlt := s7r_first_cut_lt hn hQ hsep hz hm hr hr0 hQC hw hside h₁ w (hwe.trans hi1)
      obtain ⟨h0, h2⟩ := hcut hi1 _ (by linarith) w' (by rw [he, hea]) hhi'
      refine ⟨h0, hex1, h2, ?_⟩
      intro h; rw [h] at hhi'; linarith
    · obtain ⟨h0, h2, ha⟩ := hoff hi1 w' he
      exact ⟨h0, hex1, h2, ha⟩

include hQ hz hr hr0 hr1 hη hw hord hside huniq hxS hSimg h₂ in
/-- **First-half step** of the first-return law: for `b = inl m`. -/
theorem s7r_step_first (hn₁ : 3 ≤ firstHalfSize M a) (S₁ : Finset (Crossing (firstHalf P M a)))
    (hS₁ : S₁ = s7b_pre (s7b_firstCrossingQ hn hsep hm hQC) S) (m : Mark (firstHalf P M a)) :
    ∃ k : ℕ, 0 < k ∧ ((smoothingSuccessor hn hQ S) ^ k)
        (s7b_slidingMark hn hsep hm hQC (s7e_vl hc) (Sum.inl m)) =
      s7b_slidingMark hn hsep hm hQC (s7e_vl hc) (Sum.inl (smoothingSuccessor hn₁ h₁ S₁ m)) ∧
      ∀ j : ℕ, 0 < j → j < k → ((smoothingSuccessor hn hQ S) ^ j)
        (s7b_slidingMark hn hsep hm hQC (s7e_vl hc) (Sum.inl m)) ∉
          Set.range (s7b_slidingMark hn hsep hm hQC (s7e_vl hc)) := by
  have hu : selectedMarkPerm S (s7b_slidingMark hn hsep hm hQC (s7e_vl hc) (Sum.inl m)) =
      s7b_slidingMark hn hsep hm hQC (s7e_vl hc) (Sum.inl (selectedMarkPerm S₁ m)) := by
    cases m with
    | inl i => rfl
    | inr v =>
      rw [s7b_slidingMark_inl_inr, selectedMarkPerm_visit, selectedMarkPerm_visit, s7b_slidingMark_inl_inr]
      congr 1
      by_cases hv : v.1 ∈ S₁
      · have hvQ : (s7b_firstVisitQ hn hsep hm hQC v).1 ∈ S := by
          rw [s7b_firstVisitQ_fst]; rw [hS₁, s7b_mem_pre] at hv; exact hv
        rw [selectedVisitTwin_of_mem S₁ v hv, selectedVisitTwin_of_mem S _ hvQ, s7b_firstVisitQ_visitTwin]
      · have hvQ : (s7b_firstVisitQ hn hsep hm hQC v).1 ∉ S := by
          rw [s7b_firstVisitQ_fst]; rw [hS₁, s7b_mem_pre] at hv; exact hv
        rw [selectedVisitTwin_of_not_mem S₁ v hv, selectedVisitTwin_of_not_mem S _ hvQ]
  exact s7r_step_of_reach hn hQ S _ (Sum.inl m) _ _ hu
    (s7r_reach_first hn hQ hsep hz hm hr hr0 hr1 hη hQC hw hord hside h₁ h₂ hc huniq S hxS hSimg hn₁
      (selectedMarkPerm S₁ m))

/-! ##### The second half: its Q-marks (the vertex `0` starts its chain at the contact `a`-visit) -/

/-- The Q-mark from which the chain of a second-half mark starts: the vertex `0 = μ_M` of `λ₂` is
carried to the leg visit `v_ℓ`, whose smoothing successor is that of its twin `v_a`. -/
def s7r_qmark₂ (m₂ : Mark (secondHalf P M a)) : Mark Q :=
  if m₂ = Sum.inl 0 then Sum.inr (s7e_va hc) else s7b_slidingMark hn hsep hm hQC (s7e_vl hc) (Sum.inr m₂)

theorem s7r_qmark₂_zero : s7r_qmark₂ hn hsep hm hQC hc (Sum.inl 0) = Sum.inr (s7e_va hc) := by
  simp [s7r_qmark₂]

theorem s7r_qmark₂_of_ne (m₂ : Mark (secondHalf P M a)) (h : m₂ ≠ Sum.inl 0) :
    s7r_qmark₂ hn hsep hm hQC hc m₂ = s7b_slidingMark hn hsep hm hQC (s7e_vl hc) (Sum.inr m₂) := by
  simp [s7r_qmark₂, h]

theorem s7r_qmark₂_inl {j : ZMod (secondHalfSize M a)} (hj : j ≠ 0) :
    s7r_qmark₂ hn hsep hm hQC hc (Sum.inl j) = Sum.inl (secondHalfEdgeIndex M a j) := by
  rw [s7r_qmark₂_of_ne hn hsep hm hQC hc _ (fun h => hj (Sum.inl.inj h)),
    s7b_slidingMark_inr_inl hn hsep hm hQC _ hj, secondHalfIndex_nonzero M a hj]

theorem s7r_qmark₂_inr (v : Visit (secondHalf P M a)) :
    s7r_qmark₂ hn hsep hm hQC hc (Sum.inr v) = Sum.inr (s7b_secondVisitQ hn hsep hm hQC v) := by
  rw [s7r_qmark₂_of_ne hn hsep hm hQC hc _ Sum.inr_ne_inl, s7b_slidingMark_inr_inr]

theorem s7r_edge_second (m₂ : Mark (secondHalf P M a)) :
    s7e_mEdge (s7r_qmark₂ hn hsep hm hQC hc m₂) = secondHalfEdgeIndex M a (s7e_mEdge m₂) := by
  cases m₂ with
  | inl j =>
    by_cases hj : j = 0
    · subst hj; rw [s7r_qmark₂_zero]
      exact (s7e_va_edge hc).trans (secondHalfEdgeIndex_zero M a).symm
    · rw [s7r_qmark₂_inl hn hsep hm hQC hc hj]; rfl
  | inr v => rw [s7r_qmark₂_inr]; rfl

include hQ hz hr hr1 hη hw hside h₂ in
/-- On the cut (`j = 0`) the Q-mark of `m₂` is at or beyond the contact `a`-visit. -/
theorem s7r_qmark₂_param_zero (m₂ : Mark (secondHalf P M a)) (h0 : s7e_mEdge m₂ = 0) :
    visitParameter (s7e_va hc) ≤ s7e_mParam (s7r_qmark₂ hn hsep hm hQC hc m₂) := by
  cases m₂ with
  | inl j =>
    have hj : j = 0 := h0
    subst hj; rw [s7r_qmark₂_zero]; exact le_rfl
  | inr v =>
    rw [s7r_qmark₂_inr]
    have := s7r_second_cut_gt hn hQ hsep hz hm hr hr1 hQC hw hside h₂ v h0
    have hva := (abs_lt.mp (s7e_va_param_near hn hQ false hw hc)).2
    show visitParameter (s7e_va hc) ≤ visitParameter (s7b_secondVisitQ hn hsep hm hQC v)
    linarith

include hQ hz hr hr1 hη hw hord hside h₂ in
/-- Parameter transfer for the second half. -/
theorem s7r_param_second (hn₂ : 3 ≤ secondHalfSize M a) (m₂ : Mark (secondHalf P M a))
    (v' : Visit (secondHalf P M a)) (he : v'.2.val = s7e_mEdge m₂) :
    s7e_mParam (s7r_qmark₂ hn hsep hm hQC hc m₂) < visitParameter (s7b_secondVisitQ hn hsep hm hQC v') ↔
      s7e_mParam m₂ < visitParameter v' := by
  cases m₂ with
  | inl j =>
    refine iff_of_true ?_ (s7e_visitParameter_pos hn₂ h₂ v')
    by_cases hj : j = 0
    · subst hj; rw [s7r_qmark₂_zero]
      have := s7r_second_cut_gt hn hQ hsep hz hm hr hr1 hQC hw hside h₂ v' he
      have hva := (abs_lt.mp (s7e_va_param_near hn hQ false hw hc)).2
      show visitParameter (s7e_va hc) < _
      linarith
    · rw [s7r_qmark₂_inl hn hsep hm hQC hc hj]; exact s7e_visitParameter_pos hn hQ _
  | inr v => rw [s7r_qmark₂_inr]; exact s7r_second_order hn hsep hz hm hr hr1 hQC hord v v' he.symm

include hQ hz hr hr0 hr1 hη hw hord hside hSimg h₁ in
/-- **Second-half reach**: from the Q-mark of `m₂ : Mark λ₂` the smoothing successor reaches the
Q-mark of `nextMark m₂` through transit marks only (the vertex `0` of `λ₂` is entered from edge
`M − 1` at the leg visit `v_ℓ`, and left through the contact `a`-visit). -/
theorem s7r_reach_second (hn₂ : 3 ≤ secondHalfSize M a) (m₂ : Mark (secondHalf P M a)) :
    ∃ k : ℕ, ((smoothingSuccessor hn hQ S) ^ k) (nextMark hn hQ (s7r_qmark₂ hn hsep hm hQC hc m₂)) =
      s7b_slidingMark hn hsep hm hQC (s7e_vl hc) (Sum.inr (nextMark hn₂ h₂ m₂)) ∧
      ∀ j : ℕ, j < k → ((smoothingSuccessor hn hQ S) ^ j)
        (nextMark hn hQ (s7r_qmark₂ hn hsep hm hQC hc m₂)) ∉
          Set.range (s7b_slidingMark hn hsep hm hQC (s7e_vl hc)) := by
  have hedge_u := s7r_edge_second hn hsep hm hQC hc m₂
  have hinj := s7b_slidingMark_injective hn hsep hm hQC (s7e_vl hc) (s7r_vl_affected hc)
  have hva_near := s7e_va_param_near hn hQ false hw hc
  have hva1 := (abs_lt.mp hva_near).1
  have hva2 := (abs_lt.mp hva_near).2
  have hvl := s7e_vl_param_false hn hQ hw hc
  have hne_u : s7r_qmark₂ hn hsep hm hQC hc m₂ ≠
      s7b_slidingMark hn hsep hm hQC (s7e_vl hc) (Sum.inr (nextMark hn₂ h₂ m₂)) := by
    by_cases h0 : m₂ = Sum.inl 0
    · subst h0; rw [s7r_qmark₂_zero]; intro h
      exact s7r_va_not_mem_range hn hsep hm hQC hc ⟨_, h.symm⟩
    · rw [s7r_qmark₂_of_ne hn hsep hm hQC hc m₂ h0]; intro h
      exact markSuccessor_ne_self hn₂ h₂ m₂ (Sum.inr.inj (hinj h)).symm
  have hsecond : ∀ (w' : Visit Q), w'.2.val = secondHalfEdgeIndex M a (s7e_mEdge m₂) →
      ∀ v' : Visit (secondHalf P M a), s7b_secondVisitQ hn hsep hm hQC v' = w' →
      v'.2.val = s7e_mEdge m₂ ∧ (s7e_mParam (s7r_qmark₂ hn hsep hm hQC hc m₂) < visitParameter w' ↔
        s7e_mParam m₂ < visitParameter v') := by
    intro w' he v' hv'
    have hv'e : v'.2.val = s7e_mEdge m₂ := by
      apply secondHalfEdgeIndex_injective M a
      rw [← s7b_secondVisitQ_edge hn hsep hm hQC v', hv', he]
    refine ⟨hv'e, ?_⟩
    rw [← hv']
    exact s7r_param_second hn hQ hsep hz hm hr hr1 hη hQC hw hord hside h₂ hc hn₂ m₂ v' hv'e
  have hfirst : ∀ (w' : Visit Q), w'.2.val = secondHalfEdgeIndex M a (s7e_mEdge m₂) →
      s7e_mParam (s7r_qmark₂ hn hsep hm hQC hc m₂) < visitParameter w' →
      ∀ v', s7b_firstVisitQ hn hsep hm hQC v' ≠ w' := by
    intro w' he hlo v' hv'
    rw [← hv', s7b_firstVisitQ_edge] at he
    obtain ⟨hv'1, hj0⟩ := s7b_firstHalfIndex_eq_secondHalfEdgeIndex hn hsep he
    have h1 := s7r_first_cut_lt hn hQ hsep hz hm hr hr0 hQC hw hside h₁ v' hv'1
    have h2 := s7r_qmark₂_param_zero hn hQ hsep hz hm hr hr1 hη hQC hw hside h₂ hc m₂ hj0
    rw [← hv'] at hlo
    linarith
  have hva_ex : ∀ (w' : Visit Q), w'.2.val = secondHalfEdgeIndex M a (s7e_mEdge m₂) →
      s7e_mParam (s7r_qmark₂ hn hsep hm hQC hc m₂) < visitParameter w' → w' ≠ s7e_va hc := by
    intro w' he hlo h
    rw [h, s7e_va_edge] at he
    have hj0 : s7e_mEdge m₂ = 0 :=
      secondHalfEdgeIndex_injective M a (by rw [← he, secondHalfEdgeIndex_zero])
    have h2 := s7r_qmark₂_param_zero hn hQ hsep hz hm hr hr1 hη hQC hw hside h₂ hc m₂ hj0
    rw [h] at hlo
    linarith
  have hvl_edge : ∀ (w' : Visit Q), w'.2.val = secondHalfEdgeIndex M a (s7e_mEdge m₂) →
      w' = s7e_vl hc → s7e_mEdge m₂ = -1 := by
    intro w' he h
    rw [h, s7e_vl_edge, s7r_leg_false, ← secondHalfEdgeIndex_last M a] at he
    exact (secondHalfEdgeIndex_injective M a he).symm
  have : Fact (1 < secondHalfSize M a) := ⟨by omega⟩
  rcases s7r_nextMark_shape hn₂ h₂ m₂ with hnx | ⟨w, hnx, hwe, hwp⟩
  · by_cases hj1 : s7e_mEdge m₂ = -1
    · -- `j = −1`: `nextMark m₂ = inl 0 ↦ v_ℓ`, the last mark on edge `M − 1`
      have hm' : s7b_slidingMark hn hsep hm hQC (s7e_vl hc) (Sum.inr (nextMark hn₂ h₂ m₂)) =
          Sum.inr (s7e_vl hc) := by
        rw [hnx, hj1, neg_add_cancel, s7b_slidingMark_inr_inl_zero]
      rw [hm'] at hne_u ⊢
      have hem : secondHalfEdgeIndex M a (s7e_mEdge m₂) = M - 1 := by rw [hj1, secondHalfEdgeIndex_last]
      have hlt_u : s7e_mParam (s7r_qmark₂ hn hsep hm hQC hc m₂) < visitParameter (s7e_vl hc) := by
        cases m₂ with
        | inl j =>
          have hj : j ≠ 0 := by
            intro h; rw [h] at hj1
            exact absurd hj1.symm (neg_ne_zero.mpr one_ne_zero)
          rw [s7r_qmark₂_inl hn hsep hm hQC hc hj]; exact s7e_visitParameter_pos hn hQ _
        | inr v =>
          rw [s7r_qmark₂_inr]
          have hp := s7e_persist_M_sub_one hn hQ hw (s7b_secondVisitQ hn hsep hm hQC v)
            (s7b_secondCrossingQ_not_affected hn hsep hm hQC v.1)
            (by rw [s7b_secondVisitQ_edge]; exact hem)
          show visitParameter (s7b_secondVisitQ hn hsep hm hQC v) < _
          linarith
      refine s7r_reach_of_transit hn hQ S _ _ _ _ rfl hne_u
        (s7r_transit_window hn hQ hsep hm hQC hc S hSimg _ _ _ (hedge_u.trans hem)
          (Or.inr ⟨(s7e_vl_edge hc).trans s7r_leg_false, hlt_u⟩) ?_)
      intro w' he hlo hhi
      have hhi' : visitParameter w' < visitParameter (s7e_vl hc) := by
        rcases hhi with h | h
        · exact absurd h Sum.inr_ne_inl
        · exact h
      have he' : w'.2.val = secondHalfEdgeIndex M a (s7e_mEdge m₂) := he.trans hem.symm
      refine ⟨fun h => by rw [h] at hhi'; exact lt_irrefl _ hhi', hfirst w' he' hlo, ?_, hva_ex w' he' hlo⟩
      intro v' hv'
      obtain ⟨hv'e, hiff⟩ := hsecond w' he' v' hv'
      exact s7r_no_half_between hn₂ h₂ m₂ _ rfl v' hv'e (hiff.mp hlo) (Or.inl hnx)
    · by_cases hj0 : s7e_mEdge m₂ = 0
      · -- `j = 0`: `nextMark m₂ = inl 1 ↦ μ_{a+1}`, entered from the contact `a`-visit
        have hm' : s7b_slidingMark hn hsep hm hQC (s7e_vl hc) (Sum.inr (nextMark hn₂ h₂ m₂)) =
            Sum.inl (a + 1) := by
          rw [hnx, hj0, zero_add, s7b_slidingMark_inr_inl hn hsep hm hQC _ one_ne_zero,
            secondHalfIndex_one hn hsep]
        rw [hm'] at hne_u ⊢
        have hem : secondHalfEdgeIndex M a (s7e_mEdge m₂) = a := by rw [hj0, secondHalfEdgeIndex_zero]
        refine s7r_reach_of_transit hn hQ S _ _ _ _ rfl hne_u
          (s7r_transit_window hn hQ hsep hm hQC hc S hSimg _ _ _ (hedge_u.trans hem) (Or.inl rfl) ?_)
        intro w' he hlo _
        have he' : w'.2.val = secondHalfEdgeIndex M a (s7e_mEdge m₂) := he.trans hem.symm
        refine ⟨fun h => ?_, hfirst w' he' hlo, ?_, hva_ex w' he' hlo⟩
        · have := hvl_edge w' he' h
          rw [hj0] at this
          exact absurd this.symm (neg_ne_zero.mpr one_ne_zero)
        · intro v' hv'
          obtain ⟨hv'e, hiff⟩ := hsecond w' he' v' hv'
          exact s7r_no_half_between hn₂ h₂ m₂ _ rfl v' hv'e (hiff.mp hlo) (Or.inl hnx)
      · -- `j ≠ 0, −1`: `nextMark m₂ = inl (j+1) ↦ μ_{secondHalfEdgeIndex j + 1}`
        have hj1' : s7e_mEdge m₂ + 1 ≠ 0 := fun h => hj1 (eq_neg_of_add_eq_zero_left h)
        have hm' : s7b_slidingMark hn hsep hm hQC (s7e_vl hc) (Sum.inr (nextMark hn₂ h₂ m₂)) =
            Sum.inl (secondHalfEdgeIndex M a (s7e_mEdge m₂) + 1) := by
          rw [hnx, s7b_slidingMark_inr_inl hn hsep hm hQC _ hj1', secondHalfIndex_next M a hj0]
        rw [hm'] at hne_u ⊢
        refine s7r_reach_of_transit hn hQ S _ _ _ _ rfl hne_u
          (s7r_transit_window hn hQ hsep hm hQC hc S hSimg _ _ _ hedge_u (Or.inl rfl) ?_)
        intro w' he hlo _
        refine ⟨fun h => hj1 (hvl_edge w' he h), hfirst w' he hlo, ?_, hva_ex w' he hlo⟩
        intro v' hv'
        obtain ⟨hv'e, hiff⟩ := hsecond w' he v' hv'
        exact s7r_no_half_between hn₂ h₂ m₂ _ rfl v' hv'e (hiff.mp hlo) (Or.inl hnx)
  · -- target: a visit `w` of `λ₂` on the edge of `m₂`, `↦ secondVisitQ w`
    have hm' : s7b_slidingMark hn hsep hm hQC (s7e_vl hc) (Sum.inr (nextMark hn₂ h₂ m₂)) =
        Sum.inr (s7b_secondVisitQ hn hsep hm hQC w) := by rw [hnx, s7b_slidingMark_inr_inr]
    rw [hm'] at hne_u ⊢
    have hwQe : (s7b_secondVisitQ hn hsep hm hQC w).2.val = secondHalfEdgeIndex M a (s7e_mEdge m₂) := by
      rw [s7b_secondVisitQ_edge, hwe]
    have hlt_u : s7e_mParam (s7r_qmark₂ hn hsep hm hQC hc m₂) <
        visitParameter (s7b_secondVisitQ hn hsep hm hQC w) :=
      (s7r_param_second hn hQ hsep hz hm hr hr1 hη hQC hw hord hside h₂ hc hn₂ m₂ w hwe).mpr hwp
    refine s7r_reach_of_transit hn hQ S _ _ _ _ rfl hne_u
      (s7r_transit_window hn hQ hsep hm hQC hc S hSimg _ _ _ hedge_u (Or.inr ⟨hwQe, hlt_u⟩) ?_)
    intro w' he hlo hhi
    have hhi' : visitParameter w' < visitParameter (s7b_secondVisitQ hn hsep hm hQC w) := by
      rcases hhi with h | h
      · exact absurd h Sum.inr_ne_inl
      · exact h
    refine ⟨?_, hfirst w' he hlo, ?_, hva_ex w' he hlo⟩
    · intro h
      have hj1 := hvl_edge w' he h
      have hp := s7e_persist_M_sub_one hn hQ hw (s7b_secondVisitQ hn hsep hm hQC w)
        (s7b_secondCrossingQ_not_affected hn hsep hm hQC w.1)
        (by rw [hwQe, hj1, secondHalfEdgeIndex_last])
      rw [h] at hhi'
      linarith
    · intro v' hv'
      obtain ⟨hv'e, hiff⟩ := hsecond w' he v' hv'
      have hup : visitParameter v' < visitParameter w := by
        rw [← hv'] at hhi'
        exact (s7r_second_order hn hsep hz hm hr hr1 hQC hord v' w (hv'e.trans hwe.symm)).mp hhi'
      exact s7r_no_half_between hn₂ h₂ m₂ _ rfl v' hv'e (hiff.mp hlo)
        (Or.inr ⟨by rw [hnx]; exact hwe, by rw [hnx]; exact hup⟩)

include hQ hz hr hr0 hr1 hη hw hord hside hxS hSimg h₁ in
/-- **Second-half step** of the first-return law: for `b = inr m`. -/
theorem s7r_step_second (hn₂ : 3 ≤ secondHalfSize M a) (S₂ : Finset (Crossing (secondHalf P M a)))
    (hS₂ : S₂ = s7b_pre (s7b_secondCrossingQ hn hsep hm hQC) S) (m : Mark (secondHalf P M a)) :
    ∃ k : ℕ, 0 < k ∧ ((smoothingSuccessor hn hQ S) ^ k)
        (s7b_slidingMark hn hsep hm hQC (s7e_vl hc) (Sum.inr m)) =
      s7b_slidingMark hn hsep hm hQC (s7e_vl hc) (Sum.inr (smoothingSuccessor hn₂ h₂ S₂ m)) ∧
      ∀ j : ℕ, 0 < j → j < k → ((smoothingSuccessor hn hQ S) ^ j)
        (s7b_slidingMark hn hsep hm hQC (s7e_vl hc) (Sum.inr m)) ∉
          Set.range (s7b_slidingMark hn hsep hm hQC (s7e_vl hc)) := by
  have hu : selectedMarkPerm S (s7b_slidingMark hn hsep hm hQC (s7e_vl hc) (Sum.inr m)) =
      s7r_qmark₂ hn hsep hm hQC hc (selectedMarkPerm S₂ m) := by
    cases m with
    | inl j =>
      by_cases hj : j = 0
      · subst hj
        rw [s7b_slidingMark_inr_inl_zero, selectedMarkPerm_visit, selectedMarkPerm_vertex, s7r_qmark₂_zero,
          selectedVisitTwin_of_mem S _ (by rw [s7e_vl_fst]; exact hxS), s7e_twin_vl hc (s7e_a_ne_leg false hsep)]
      · rw [s7b_slidingMark_inr_inl hn hsep hm hQC _ hj, selectedMarkPerm_vertex, selectedMarkPerm_vertex,
          s7r_qmark₂_inl hn hsep hm hQC hc hj, secondHalfIndex_nonzero M a hj]
    | inr v =>
      rw [s7b_slidingMark_inr_inr, selectedMarkPerm_visit, selectedMarkPerm_visit, s7r_qmark₂_inr]
      congr 1
      by_cases hv : v.1 ∈ S₂
      · have hvQ : (s7b_secondVisitQ hn hsep hm hQC v).1 ∈ S := by
          rw [s7b_secondVisitQ_fst]; rw [hS₂, s7b_mem_pre] at hv; exact hv
        rw [selectedVisitTwin_of_mem S₂ v hv, selectedVisitTwin_of_mem S _ hvQ, s7b_secondVisitQ_visitTwin]
      · have hvQ : (s7b_secondVisitQ hn hsep hm hQC v).1 ∉ S := by
          rw [s7b_secondVisitQ_fst]; rw [hS₂, s7b_mem_pre] at hv; exact hv
        rw [selectedVisitTwin_of_not_mem S₂ v hv, selectedVisitTwin_of_not_mem S _ hvQ]
  exact s7r_step_of_reach hn hQ S _ (Sum.inr m) _ _ hu
    (s7r_reach_second hn hQ hsep hz hm hr hr0 hr1 hη hQC hw hord hside h₁ h₂ hc S hSimg hn₂
      (selectedMarkPerm S₂ m))

include hQ hη hw huniq hxS hSimg in
/-- **Hit**: every mark of `Q` reaches the image (beacon `μ_M`; off-image visits are either the
contact `a`-visit, which steps to `μ_M`, or visits of crossings off `S`). -/
theorem s7r_hit (u : Mark Q) :
    ∃ j : ℕ, ((smoothingSuccessor hn hQ S) ^ j) u ∈ Set.range (s7b_slidingMark hn hsep hm hQC (s7e_vl hc)) := by
  refine s7r_hit_of_transit hn hQ S _ (Sum.inl M)
    ⟨Sum.inl (Sum.inl 0), by rw [s7b_slidingMark_inl_inl, firstHalfIndex_zero]⟩ ?_ _ u rfl
  intro w hwr
  cases w with
  | inl i => exact Or.inr (smoothingSuccessor_vertex hn hQ S i)
  | inr w' =>
    by_cases hwS : w'.1 ∈ S
    · by_cases hwx : w'.1 = (s7e_va hc).1
      · rcases s7e_visit_of_fst hc w' (by rw [hwx]; rfl) (s7e_a_ne_leg false hsep) with h | h
        · subst h; left; refine ⟨1, ?_⟩
          rw [pow_one, s7r_succ_va hn hQ hsep hη hw hc huniq S hxS]
          exact ⟨Sum.inl (Sum.inl 0), by rw [s7b_slidingMark_inl_inl, firstHalfIndex_zero]⟩
        · exact absurd ((s7r_inr_mem_range_iff hn hsep hm hQC _ w').mpr (Or.inl h)) hwr
      · exfalso; apply hwr
        rcases hSimg w'.1 hwS hwx with ⟨c, hcw⟩ | ⟨c, hcw⟩
        · obtain ⟨v, -, hv⟩ := s7b_visit_of_firstCrossingQ hn hsep hm hQC w' c hcw.symm
          exact (s7r_inr_mem_range_iff hn hsep hm hQC _ w').mpr (Or.inr (Or.inl ⟨v, hv⟩))
        · obtain ⟨v, -, hv⟩ := s7b_visit_of_secondCrossingQ hn hsep hm hQC w' c hcw.symm
          exact (s7r_inr_mem_range_iff hn hsep hm hQC _ w').mpr (Or.inr (Or.inr ⟨v, hv⟩))
    · exact Or.inr (smoothingSuccessor_visit_of_not_mem hn hQ S w' hwS)

include hz hr hr0 hr1 hη hw hord hside huniq hxS hSimg in
/-- **`s7b_SlidingTransport.ret` on the leg-`M−1` side, PROVED**: the first-return law of the smoothing
successor of a sliding row on the marks of `λ₁ ⊕ λ₂` under `s7b_slidingMark` at the leg visit. -/
theorem s7r_slidingTransport_of_leg_false :
    s7b_SlidingTransport hn hsep hm hQC hQ h₁ h₂ S (s7b_pre (s7b_firstCrossingQ hn hsep hm hQC) S)
      (s7b_pre (s7b_secondCrossingQ hn hsep hm hQC) S) (s7e_vl hc) where
  affected := s7r_vl_affected hc
  pivot_mem := by rw [s7e_vl_fst]; exact hxS
  first_pre := rfl
  second_pre := rfl
  ret :=
    { inj := s7b_slidingMark_injective hn hsep hm hQC (s7e_vl hc) (s7r_vl_affected hc)
      step := fun b => by
        rcases b with m | m
        · exact s7r_step_first hn hQ hsep hz hm hr hr0 hr1 hη hQC hw hord hside h₁ h₂ hc huniq S hxS hSimg
            (contactHalfSizes_bounds hn hsep).1.1 _ rfl m
        · exact s7r_step_second hn hQ hsep hz hm hr hr0 hr1 hη hQC hw hord hside h₁ h₂ hc S hxS hSimg
            (contactHalfSizes_bounds hn hsep).2.1 _ rfl m
      hit := s7r_hit hn hQ hsep hm hη hQC hw hc huniq S hxS hSimg }

/-- The image hypothesis of a sliding row from the pivot split and independence (part IV):
every crossing of a decomposition `S ∋ x` other than `x` is carried from a half. -/
theorem s7r_img_of_decomposition (x : Crossing Q)
    (hsplit : s7b_PivotSplit (Interlaces hn hQ) (Interlaces (contactHalfSizes_bounds hn hsep).1.1 h₁)
      (Interlaces (contactHalfSizes_bounds hn hsep).2.1 h₂) (s7b_firstCrossingQ hn hsep hm hQC)
      (s7b_secondCrossingQ hn hsep hm hQC) x)
    (hS : IsDecomposition hn hQ S) (hx : x ∈ S) :
    ∀ y ∈ S, y ≠ x → y ∈ Set.range (s7b_firstCrossingQ hn hsep hm hQC) ∪
      Set.range (s7b_secondCrossingQ hn hsep hm hQC) := by
  intro y hy hyx
  have hind := (s7b_isDecomposition_iff_indep hn hQ S).mp hS
  exact hsplit.x_split y hyx (hind x hx y hy hyx.symm) (hind y hy x hx hyx)

/-! ##### The leg-`M` side: the CORRECTED mark map and transport (rule 4).  With `x = {a, M}` the
smoothing at `x` sends `v_ℓ ↦ nextMark v_a` and `v_a ↦ nextMark v_ℓ`, and `nextMark μ_M = v_ℓ`
(`s7e_owner_vl_eq_vertex`, `f = true`): the carrier through `μ_M` is `μ_M, v_ℓ, [E_a > r], μ_{a+1}, …,
μ_{M−1}, [E_{M−1}]` — the closed SECOND half, with `v_ℓ` the extra corner — and the closed FIRST half is
`[E_M], μ_{M+1}, …, μ_a, [E_a < r], v_a` with `v_a` in the place of `λ₁`'s vertex `0`.  So the vertex `0`
of `λ₁` must be carried to `v_a` and the vertex `0` of `λ₂` to `μ_M`; `s7b_slidingMark` (which fixes
`inl (inl 0) ↦ μ_M`) makes `s7b_SlidingTransport.ret` FALSE on this side: `f (ι (inl (inl 0))) =
nextMark μ_M = v_ℓ = ι (inr (inl 0))` is an image mark of the other half at the first step. -/

/-- The mark map of a sliding row on the leg-`M` side: `λ₁`'s vertex `0` is the contact `a`-visit
`va`, `λ₂`'s vertex `0` is `μ_M`; the leg visit is the skipped extra corner. -/
def s7r_slidingMark' (va : Visit Q) :
    Mark (firstHalf P M a) ⊕ Mark (secondHalf P M a) → Mark Q
  | Sum.inl (Sum.inl i) => if i = 0 then Sum.inr va else Sum.inl (firstHalfIndex M a i)
  | Sum.inl (Sum.inr v) => Sum.inr (s7b_firstVisitQ hn hsep hm hQC v)
  | Sum.inr (Sum.inl i) => Sum.inl (secondHalfIndex M a i)
  | Sum.inr (Sum.inr v) => Sum.inr (s7b_secondVisitQ hn hsep hm hQC v)

/-- The transport structure of a sliding row on the leg-`M` side (the corrected form of
`s7b_SlidingTransport` there; `va` is the contact `a`-visit of `x = {a, M}`). -/
structure s7r_SlidingTransport' (S₁ : Finset (Crossing (firstHalf P M a)))
    (S₂ : Finset (Crossing (secondHalf P M a))) (va : Visit Q) : Prop where
  affected : ContactAffected M a va.1.val
  pivot_mem : va.1 ∈ S
  first_pre : S₁ = s7b_pre (s7b_firstCrossingQ hn hsep hm hQC) S
  second_pre : S₂ = s7b_pre (s7b_secondCrossingQ hn hsep hm hQC) S
  ret : s7b_ReturnTransport (smoothingSuccessor hn hQ S)
    (Equiv.Perm.sumCongr (smoothingSuccessor (contactHalfSizes_bounds hn hsep).1.1 h₁ S₁)
      (smoothingSuccessor (contactHalfSizes_bounds hn hsep).2.1 h₂ S₂))
    (s7r_slidingMark' hn hsep hm hQC va)

end S7RSide

section S7RLegTrue

variable (hn : 3 ≤ n) {P Q : LabelledTuple n} (hQ : Generic Q) {M a : ZMod n}
  (hsep : ContactSeparated M a) (hz : pointZeroTriples P = {contactSupport M a})
  (hm : P M ∈ edgeInterior P a) {r η : ℝ} (hr : P M = edgePoint P a r) (hr0 : 0 < r) (hr1 : r < 1)
  (hη : 0 < η)
  (hQC : ∀ s, ¬ ContactAffected M a s → (IsCrossing Q s ↔ IsCrossing P s))
  (hw : ContactParameterWindows P Q M a r η)
  (hord : ∀ (u u' : Visit P) (hu : ¬ ContactAffected M a u.1.val) (hu' : ¬ ContactAffected M a u'.1.val),
    u.2.val = u'.2.val →
    (visitParameter (s7a_visit hQC u hu) < visitParameter (s7a_visit hQC u' hu') ↔
      visitParameter u < visitParameter u'))
  (hside : ∀ (u : Visit P) (hu : ¬ ContactAffected M a u.1.val), u.2.val = a →
    (visitParameter (s7a_visit hQC u hu) < r ↔ visitParameter u < r))
  (h₁ : Generic (firstHalf P M a)) (h₂ : Generic (secondHalf P M a))
  (hc : IsCrossing Q {a, contactLeg true M})
  (huniq : ∀ y : Crossing Q, ContactAffected M a y.val → y.val = {a, contactLeg true M})
  (S : Finset (Crossing Q)) (hxS : (s7e_va hc).1 ∈ S)
  (hSimg : ∀ y ∈ S, y ≠ (s7e_va hc).1 →
    y ∈ Set.range (s7b_firstCrossingQ hn hsep hm hQC) ∪ Set.range (s7b_secondCrossingQ hn hsep hm hQC))

/-! ##### The corrected map is the `s7b_` map at `v_a` composed with the swap `μ_M ↔ v_a`. -/

omit [NeZero n] in
theorem s7r_leg_true : contactLeg true M = M := by simp [contactLeg]

include hn hsep in
/-- `secondHalfIndex (j + 1) = secondHalfEdgeIndex j + 1` for every `j` (the wrap `j = −1` gives `μ_M`). -/
theorem s7r_secondHalfIndex_succ (j : ZMod (secondHalfSize M a)) :
    secondHalfIndex M a (j + 1) = secondHalfEdgeIndex M a j + 1 := by
  by_cases hj : j = 0
  · subst hj; rw [zero_add, secondHalfIndex_one hn hsep, secondHalfEdgeIndex_zero]
  · exact secondHalfIndex_next M a hj

theorem s7r_va_affected' : ContactAffected M a (s7e_va hc).1.val :=
  (contactAffected_iff_leg _).mpr ⟨true, rfl⟩

theorem s7r_slidingMark'_inl_inl_zero :
    s7r_slidingMark' hn hsep hm hQC (s7e_va hc) (Sum.inl (Sum.inl 0)) = Sum.inr (s7e_va hc) := by
  simp [s7r_slidingMark']

theorem s7r_slidingMark'_inl_inl {i : ZMod (firstHalfSize M a)} (hi : i ≠ 0) :
    s7r_slidingMark' hn hsep hm hQC (s7e_va hc) (Sum.inl (Sum.inl i)) = Sum.inl (firstHalfIndex M a i) := by
  simp [s7r_slidingMark', hi]

theorem s7r_slidingMark'_inl_inr (v : Visit (firstHalf P M a)) :
    s7r_slidingMark' hn hsep hm hQC (s7e_va hc) (Sum.inl (Sum.inr v)) =
      Sum.inr (s7b_firstVisitQ hn hsep hm hQC v) := rfl

theorem s7r_slidingMark'_inr_inl (i : ZMod (secondHalfSize M a)) :
    s7r_slidingMark' hn hsep hm hQC (s7e_va hc) (Sum.inr (Sum.inl i)) = Sum.inl (secondHalfIndex M a i) := rfl

theorem s7r_slidingMark'_inr_inr (v : Visit (secondHalf P M a)) :
    s7r_slidingMark' hn hsep hm hQC (s7e_va hc) (Sum.inr (Sum.inr v)) =
      Sum.inr (s7b_secondVisitQ hn hsep hm hQC v) := rfl

theorem s7r_slidingMark'_eq :
    s7r_slidingMark' hn hsep hm hQC (s7e_va hc) =
      Equiv.swap (Sum.inl M) (Sum.inr (s7e_va hc)) ∘ s7b_slidingMark hn hsep hm hQC (s7e_va hc) := by
  have h1 : ∀ v : Visit (firstHalf P M a), s7b_firstVisitQ hn hsep hm hQC v ≠ s7e_va hc := fun v h =>
    s7b_firstCrossingQ_not_affected hn hsep hm hQC v.1
      (by rw [← s7b_firstVisitQ_fst hn hsep hm hQC v, h]; exact s7r_va_affected' hc)
  have h2 : ∀ v : Visit (secondHalf P M a), s7b_secondVisitQ hn hsep hm hQC v ≠ s7e_va hc := fun v h =>
    s7b_secondCrossingQ_not_affected hn hsep hm hQC v.1
      (by rw [← s7b_secondVisitQ_fst hn hsep hm hQC v, h]; exact s7r_va_affected' hc)
  funext b
  rcases b with (i | v) | (i | v)
  · rw [Function.comp_apply, s7b_slidingMark_inl_inl]
    by_cases hi : i = 0
    · subst hi; rw [s7r_slidingMark'_inl_inl_zero, firstHalfIndex_zero, Equiv.swap_apply_left]
    · rw [s7r_slidingMark'_inl_inl hn hsep hm hQC hc hi]
      refine (Equiv.swap_apply_of_ne_of_ne ?_ Sum.inl_ne_inr).symm
      intro h; apply hi
      exact firstHalfIndex_injective M a ((Sum.inl.inj h).trans (firstHalfIndex_zero M a).symm)
  · rw [Function.comp_apply, s7b_slidingMark_inl_inr, s7r_slidingMark'_inl_inr]
    exact (Equiv.swap_apply_of_ne_of_ne Sum.inr_ne_inl (fun h => h1 v (Sum.inr_injective h))).symm
  · rw [Function.comp_apply, s7r_slidingMark'_inr_inl]
    by_cases hi : i = 0
    · subst hi; rw [s7b_slidingMark_inr_inl_zero, secondHalfIndex_zero, Equiv.swap_apply_right]
    · rw [s7b_slidingMark_inr_inl hn hsep hm hQC _ hi]
      refine (Equiv.swap_apply_of_ne_of_ne ?_ Sum.inl_ne_inr).symm
      intro h; apply hi
      exact secondHalfIndex_injective M a ((Sum.inl.inj h).trans (secondHalfIndex_zero M a).symm)
  · rw [Function.comp_apply, s7b_slidingMark_inr_inr, s7r_slidingMark'_inr_inr]
    exact (Equiv.swap_apply_of_ne_of_ne Sum.inr_ne_inl (fun h => h2 v (Sum.inr_injective h))).symm

theorem s7r_slidingMark'_injective : Function.Injective (s7r_slidingMark' hn hsep hm hQC (s7e_va hc)) := by
  rw [s7r_slidingMark'_eq]
  exact (Equiv.swap _ _).injective.comp (s7b_slidingMark_injective hn hsep hm hQC _ (s7r_va_affected' hc))

theorem s7r_inr_mem_range_iff' (w : Visit Q) :
    (Sum.inr w : Mark Q) ∈ Set.range (s7r_slidingMark' hn hsep hm hQC (s7e_va hc)) ↔
      w = s7e_va hc ∨ (∃ v, s7b_firstVisitQ hn hsep hm hQC v = w) ∨
        (∃ v, s7b_secondVisitQ hn hsep hm hQC v = w) := by
  rw [s7r_slidingMark'_eq]
  by_cases hwa : w = s7e_va hc
  · subst hwa
    refine iff_of_true ⟨Sum.inl (Sum.inl 0), ?_⟩ (Or.inl rfl)
    rw [Function.comp_apply, s7b_slidingMark_inl_inl, firstHalfIndex_zero, Equiv.swap_apply_left]
  · have hfix : Equiv.swap (Sum.inl M) (Sum.inr (s7e_va hc)) (Sum.inr w) = Sum.inr w :=
      Equiv.swap_apply_of_ne_of_ne Sum.inr_ne_inl (fun h => hwa (Sum.inr_injective h))
    constructor
    · rintro ⟨b, hb⟩
      have hb' : s7b_slidingMark hn hsep hm hQC (s7e_va hc) b = Sum.inr w := by
        have := congrArg (Equiv.swap (Sum.inl M) (Sum.inr (s7e_va hc))) hb
        rwa [Function.comp_apply, Equiv.swap_apply_self, hfix] at this
      exact (s7r_inr_mem_range_iff hn hsep hm hQC _ w).mp ⟨b, hb'⟩
    · intro h
      obtain ⟨b, hb⟩ := (s7r_inr_mem_range_iff hn hsep hm hQC _ w).mpr h
      exact ⟨b, by rw [Function.comp_apply, hb, hfix]⟩

include hsep in
theorem s7r_vl_not_mem_range' :
    (Sum.inr (s7e_vl hc) : Mark Q) ∉ Set.range (s7r_slidingMark' hn hsep hm hQC (s7e_va hc)) := by
  rw [s7r_inr_mem_range_iff']
  rintro (h | ⟨v, hv⟩ | ⟨v, hv⟩)
  · exact s7e_vl_ne_va hc (s7e_a_ne_leg true hsep) h
  · exact s7b_firstCrossingQ_not_affected hn hsep hm hQC v.1
      (by rw [← s7b_firstVisitQ_fst hn hsep hm hQC v, hv, s7e_vl_fst]; exact s7r_va_affected' hc)
  · exact s7b_secondCrossingQ_not_affected hn hsep hm hQC v.1
      (by rw [← s7b_secondVisitQ_fst hn hsep hm hQC v, hv, s7e_vl_fst]; exact s7r_va_affected' hc)

theorem s7r_va_mem_range' :
    (Sum.inr (s7e_va hc) : Mark Q) ∈ Set.range (s7r_slidingMark' hn hsep hm hQC (s7e_va hc)) :=
  ⟨Sum.inl (Sum.inl 0), s7r_slidingMark'_inl_inl_zero hn hsep hm hQC hc⟩

include hsep hSimg in
theorem s7r_transit_of' (w : Visit Q) (h0 : w ≠ s7e_va hc)
    (h1 : ∀ v, s7b_firstVisitQ hn hsep hm hQC v ≠ w) (h2 : ∀ v, s7b_secondVisitQ hn hsep hm hQC v ≠ w)
    (hl : w ≠ s7e_vl hc) :
    s7r_Transit hn hQ S (s7r_slidingMark' hn hsep hm hQC (s7e_va hc)) (Sum.inr w) := by
  have hnr : (Sum.inr w : Mark Q) ∉ Set.range (s7r_slidingMark' hn hsep hm hQC (s7e_va hc)) := by
    rw [s7r_inr_mem_range_iff']
    rintro (h | ⟨v, hv⟩ | ⟨v, hv⟩)
    · exact h0 h
    · exact h1 v hv
    · exact h2 v hv
  refine ⟨hnr, ?_⟩
  have hwS : w.1 ∉ S := by
    intro hwS
    by_cases hwx : w.1 = (s7e_va hc).1
    · rcases s7e_visit_of_fst hc w (by rw [hwx]; rfl) (s7e_a_ne_leg true hsep) with h | h
      · exact h0 h
      · exact hl h
    · rcases hSimg w.1 hwS hwx with ⟨c, hcw⟩ | ⟨c, hcw⟩
      · obtain ⟨v, -, hv⟩ := s7b_visit_of_firstCrossingQ hn hsep hm hQC w c hcw.symm
        exact h1 v hv
      · obtain ⟨v, -, hv⟩ := s7b_visit_of_secondCrossingQ hn hsep hm hQC w c hcw.symm
        exact h2 v hv
  exact smoothingSuccessor_visit_of_not_mem hn hQ S w hwS

include hsep hSimg in
theorem s7r_transit_window' (u m' : Mark Q) (e : ZMod n) (hu : s7e_mEdge u = e)
    (hm' : m' = Sum.inl (e + 1) ∨ (s7e_mEdge m' = e ∧ s7e_mParam u < s7e_mParam m'))
    (hex : ∀ w' : Visit Q, w'.2.val = e → s7e_mParam u < visitParameter w' →
      (m' = Sum.inl (e + 1) ∨ visitParameter w' < s7e_mParam m') →
      w' ≠ s7e_va hc ∧ (∀ v, s7b_firstVisitQ hn hsep hm hQC v ≠ w') ∧
        (∀ v, s7b_secondVisitQ hn hsep hm hQC v ≠ w') ∧ w' ≠ s7e_vl hc) :
    ∀ w, traversalBetween (markPosition hn hQ.1 u) (markPosition hn hQ.1 w) (markPosition hn hQ.1 m') →
      s7r_Transit hn hQ S (s7r_slidingMark' hn hsep hm hQC (s7e_va hc)) w := by
  intro w hb
  have hdec : s7e_mEdge w = e ∧ s7e_mParam u < s7e_mParam w ∧
      (m' = Sum.inl (e + 1) ∨ s7e_mParam w < s7e_mParam m') := by
    rcases hm' with rfl | ⟨hme, hlt⟩
    · obtain ⟨h1, h2⟩ := s7r_between_next_vertex hn hQ u w e hu hb
      exact ⟨h1, h2, Or.inl rfl⟩
    · obtain ⟨h1, h2, h3⟩ := s7r_between_same_edge_of hn hQ u w m' e hu hme hlt hb
      exact ⟨h1, h2, Or.inr h3⟩
  have hpos : 0 < s7e_mParam w := lt_of_le_of_lt (s7e_mParam_nonneg hn hQ u) hdec.2.1
  obtain ⟨w', rfl⟩ := s7e_mark_visit_of_param_pos w hpos
  obtain ⟨h0, h1, h2, hl⟩ := hex w' hdec.1 hdec.2.1 hdec.2.2
  exact s7r_transit_of' hn hQ hsep hm hQC hc S hSimg w' h0 h1 h2 hl

include hQ hsep hη hw huniq in
/-- On the leg-`M` side the leg visit is the first mark on edge `M`: `nextMark μ_M = v_ℓ`. -/
theorem s7r_nextMark_M : nextMark hn hQ (Sum.inl M) = Sum.inr (s7e_vl hc) := by
  apply s7e_nextMark_inl_eq_inr hn hQ M (s7e_vl hc) (by rw [s7e_vl_edge, s7r_leg_true])
  intro u hu
  by_cases hul : u = s7e_vl hc
  · rw [hul]
  · have hup := s7e_persistent_of_edge_leg true hsep hc huniq u (by rw [hu, s7r_leg_true]) hul
    have h1 := s7e_persist_M hn hQ hw u hup hu
    have h2 := s7e_vl_param_true hn hQ hw hc
    linarith

include hsep hxS in
theorem s7r_succ_va' : smoothingSuccessor hn hQ S (Sum.inr (s7e_va hc)) = nextMark hn hQ (Sum.inr (s7e_vl hc)) := by
  rw [smoothingSuccessor_visit_of_mem hn hQ S _ hxS, s7e_twin_va hc (s7e_a_ne_leg true hsep)]; rfl

include hsep hxS in
theorem s7r_succ_vl' : smoothingSuccessor hn hQ S (Sum.inr (s7e_vl hc)) = nextMark hn hQ (Sum.inr (s7e_va hc)) := by
  rw [smoothingSuccessor_visit_of_mem hn hQ S _ (by rw [s7e_vl_fst]; exact hxS),
    s7e_twin_vl hc (s7e_a_ne_leg true hsep)]; rfl

/-! ##### The first half on the leg-`M` side: its chain starts at `v_ℓ` for the vertex `0` -/

/-- The Q-mark from which the chain of a first-half mark starts: `λ₁`'s vertex `0` is carried to
`v_a`, whose smoothing successor is that of its twin `v_ℓ`. -/
def s7r_qmark₁' (m₁ : Mark (firstHalf P M a)) : Mark Q :=
  if m₁ = Sum.inl 0 then Sum.inr (s7e_vl hc) else s7r_slidingMark' hn hsep hm hQC (s7e_va hc) (Sum.inl m₁)

theorem s7r_qmark₁'_zero : s7r_qmark₁' hn hsep hm hQC hc (Sum.inl 0) = Sum.inr (s7e_vl hc) := by
  simp [s7r_qmark₁']

theorem s7r_qmark₁'_of_ne (m₁ : Mark (firstHalf P M a)) (h : m₁ ≠ Sum.inl 0) :
    s7r_qmark₁' hn hsep hm hQC hc m₁ = s7r_slidingMark' hn hsep hm hQC (s7e_va hc) (Sum.inl m₁) := by
  simp [s7r_qmark₁', h]

theorem s7r_qmark₁'_inl {i : ZMod (firstHalfSize M a)} (hi : i ≠ 0) :
    s7r_qmark₁' hn hsep hm hQC hc (Sum.inl i) = Sum.inl (firstHalfIndex M a i) := by
  rw [s7r_qmark₁'_of_ne hn hsep hm hQC hc _ (fun h => hi (Sum.inl.inj h)), s7r_slidingMark'_inl_inl hn hsep hm hQC hc hi]

theorem s7r_qmark₁'_inr (v : Visit (firstHalf P M a)) :
    s7r_qmark₁' hn hsep hm hQC hc (Sum.inr v) = Sum.inr (s7b_firstVisitQ hn hsep hm hQC v) := by
  rw [s7r_qmark₁'_of_ne hn hsep hm hQC hc _ Sum.inr_ne_inl, s7r_slidingMark'_inl_inr]

theorem s7r_edge_first' (m₁ : Mark (firstHalf P M a)) :
    s7e_mEdge (s7r_qmark₁' hn hsep hm hQC hc m₁) = firstHalfIndex M a (s7e_mEdge m₁) := by
  cases m₁ with
  | inl i =>
    by_cases hi : i = 0
    · subst hi; rw [s7r_qmark₁'_zero]
      exact ((s7e_vl_edge hc).trans s7r_leg_true).trans (firstHalfIndex_zero M a).symm
    · rw [s7r_qmark₁'_inl hn hsep hm hQC hc hi]; rfl
  | inr v => rw [s7r_qmark₁'_inr]; rfl

include hQ hη hw in
/-- On edge `0` of `λ₁` (Q-edge `M`) the Q-mark of `m₁` is at or beyond the leg visit. -/
theorem s7r_qmark₁'_param_zero (m₁ : Mark (firstHalf P M a)) (h0 : s7e_mEdge m₁ = 0) :
    visitParameter (s7e_vl hc) ≤ s7e_mParam (s7r_qmark₁' hn hsep hm hQC hc m₁) := by
  cases m₁ with
  | inl i =>
    have hi : i = 0 := h0
    subst hi; rw [s7r_qmark₁'_zero]; exact le_rfl
  | inr v =>
    rw [s7r_qmark₁'_inr]
    have hp := s7e_persist_M hn hQ hw (s7b_firstVisitQ hn hsep hm hQC v)
      (s7b_firstCrossingQ_not_affected hn hsep hm hQC v.1)
      (by rw [s7b_firstVisitQ_edge]; exact (congrArg (firstHalfIndex M a) h0).trans (firstHalfIndex_zero M a))
    have hl := s7e_vl_param_true hn hQ hw hc
    show visitParameter (s7e_vl hc) ≤ visitParameter (s7b_firstVisitQ hn hsep hm hQC v)
    linarith

include hQ hz hr hr0 hη hw hord h₁ in
theorem s7r_param_first' (hn₁ : 3 ≤ firstHalfSize M a) (m₁ : Mark (firstHalf P M a))
    (v' : Visit (firstHalf P M a)) (he : v'.2.val = s7e_mEdge m₁) :
    s7e_mParam (s7r_qmark₁' hn hsep hm hQC hc m₁) < visitParameter (s7b_firstVisitQ hn hsep hm hQC v') ↔
      s7e_mParam m₁ < visitParameter v' := by
  cases m₁ with
  | inl i =>
    refine iff_of_true ?_ (s7e_visitParameter_pos hn₁ h₁ v')
    by_cases hi : i = 0
    · subst hi; rw [s7r_qmark₁'_zero]
      have hp := s7e_persist_M hn hQ hw (s7b_firstVisitQ hn hsep hm hQC v')
        (s7b_firstCrossingQ_not_affected hn hsep hm hQC v'.1)
        (by rw [s7b_firstVisitQ_edge]; exact (congrArg (firstHalfIndex M a) he).trans (firstHalfIndex_zero M a))
      have hl := s7e_vl_param_true hn hQ hw hc
      show visitParameter (s7e_vl hc) < _
      linarith
    · rw [s7r_qmark₁'_inl hn hsep hm hQC hc hi]; exact s7e_visitParameter_pos hn hQ _
  | inr v => rw [s7r_qmark₁'_inr]; exact s7r_first_order hn hsep hz hm hr hr0 hQC hord v v' he.symm

include hQ hz hr hr0 hr1 hη hw hord hside hSimg h₂ in
/-- **First-half reach on the leg-`M` side.** -/
theorem s7r_reach_first' (hn₁ : 3 ≤ firstHalfSize M a) (m₁ : Mark (firstHalf P M a)) :
    ∃ k : ℕ, ((smoothingSuccessor hn hQ S) ^ k) (nextMark hn hQ (s7r_qmark₁' hn hsep hm hQC hc m₁)) =
      s7r_slidingMark' hn hsep hm hQC (s7e_va hc) (Sum.inl (nextMark hn₁ h₁ m₁)) ∧
      ∀ j : ℕ, j < k → ((smoothingSuccessor hn hQ S) ^ j)
        (nextMark hn hQ (s7r_qmark₁' hn hsep hm hQC hc m₁)) ∉
          Set.range (s7r_slidingMark' hn hsep hm hQC (s7e_va hc)) := by
  have hedge_u := s7r_edge_first' hn hsep hm hQC hc m₁
  have hinj := s7r_slidingMark'_injective hn hsep hm hQC hc
  have : Fact (1 < firstHalfSize M a) := ⟨by omega⟩
  have hva_near := s7e_va_param_near hn hQ true hw hc
  have hva1 := (abs_lt.mp hva_near).1
  have hva2 := (abs_lt.mp hva_near).2
  have hvl := s7e_vl_param_true hn hQ hw hc
  have hne_u : s7r_qmark₁' hn hsep hm hQC hc m₁ ≠
      s7r_slidingMark' hn hsep hm hQC (s7e_va hc) (Sum.inl (nextMark hn₁ h₁ m₁)) := by
    by_cases h0 : m₁ = Sum.inl 0
    · subst h0; rw [s7r_qmark₁'_zero]; intro h
      exact s7r_vl_not_mem_range' hn hsep hm hQC hc ⟨_, h.symm⟩
    · rw [s7r_qmark₁'_of_ne hn hsep hm hQC hc m₁ h0]; intro h
      exact markSuccessor_ne_self hn₁ h₁ m₁ (Sum.inl.inj (hinj h)).symm
  have hfirst : ∀ (w' : Visit Q), w'.2.val = firstHalfIndex M a (s7e_mEdge m₁) →
      ∀ v' : Visit (firstHalf P M a), s7b_firstVisitQ hn hsep hm hQC v' = w' →
      v'.2.val = s7e_mEdge m₁ ∧ (s7e_mParam (s7r_qmark₁' hn hsep hm hQC hc m₁) < visitParameter w' ↔
        s7e_mParam m₁ < visitParameter v') := by
    intro w' he v' hv'
    have hv'e : v'.2.val = s7e_mEdge m₁ := by
      apply firstHalfIndex_injective M a
      rw [← s7b_firstVisitQ_edge hn hsep hm hQC v', hv', he]
    refine ⟨hv'e, ?_⟩
    rw [← hv']
    exact s7r_param_first' hn hQ hsep hz hm hr hr0 hη hQC hw hord h₁ hc hn₁ m₁ v' hv'e
  -- the leg visit lies on a first-half edge only for `i = 0`, where `u` is at or beyond it
  have hvl_ex : ∀ (w' : Visit Q), w'.2.val = firstHalfIndex M a (s7e_mEdge m₁) →
      s7e_mParam (s7r_qmark₁' hn hsep hm hQC hc m₁) < visitParameter w' → w' ≠ s7e_vl hc := by
    intro w' he hlo h
    rw [h, s7e_vl_edge, s7r_leg_true] at he
    have hi0 : s7e_mEdge m₁ = 0 :=
      firstHalfIndex_injective M a (by rw [← he, firstHalfIndex_zero])
    have h2 := s7r_qmark₁'_param_zero hn hQ hsep hm hη hQC hw hc m₁ hi0
    rw [h] at hlo
    linarith
  -- the contact `a`-visit and second-half visits lie on a first-half edge only on the cut
  have hcutedge : ∀ (w' : Visit Q), w'.2.val = firstHalfIndex M a (s7e_mEdge m₁) → w'.2.val = a →
      s7e_mEdge m₁ = -1 := by
    intro w' he hea
    rw [hea] at he
    exact firstHalfIndex_injective M a (by rw [← he, firstHalfIndex_last])
  have hsecond_cut : ∀ (w' : Visit Q), w'.2.val = firstHalfIndex M a (s7e_mEdge m₁) →
      ∀ v', s7b_secondVisitQ hn hsep hm hQC v' = w' → r + 3 * η < visitParameter w' := by
    intro w' he v' hv'
    have hv'0 : v'.2.val = 0 := by
      rw [← hv', s7b_secondVisitQ_edge] at he
      exact (s7b_firstHalfIndex_eq_secondHalfEdgeIndex hn hsep he.symm).2
    rw [← hv']
    exact s7r_second_cut_gt hn hQ hsep hz hm hr hr1 hQC hw hside h₂ v' hv'0
  rcases s7r_nextMark_shape hn₁ h₁ m₁ with hnx | ⟨w, hnx, hwe, hwp⟩
  · by_cases hi1 : s7e_mEdge m₁ = -1
    · -- the cut, vertex target `inl 0 ↦ v_a` directly
      have hm' : s7r_slidingMark' hn hsep hm hQC (s7e_va hc) (Sum.inl (nextMark hn₁ h₁ m₁)) =
          Sum.inr (s7e_va hc) := by
        rw [hnx, hi1, neg_add_cancel, s7r_slidingMark'_inl_inl_zero]
      rw [hm'] at hne_u ⊢
      have hea : firstHalfIndex M a (s7e_mEdge m₁) = a := by rw [hi1, firstHalfIndex_last]
      have hlt_u : s7e_mParam (s7r_qmark₁' hn hsep hm hQC hc m₁) < visitParameter (s7e_va hc) := by
        cases m₁ with
        | inl j =>
          have hj : j ≠ 0 := by
            intro h; rw [h] at hi1
            exact absurd hi1.symm (neg_ne_zero.mpr one_ne_zero)
          rw [s7r_qmark₁'_inl hn hsep hm hQC hc hj]; exact s7e_visitParameter_pos hn hQ _
        | inr v =>
          rw [s7r_qmark₁'_inr]
          have := s7r_first_cut_lt hn hQ hsep hz hm hr hr0 hQC hw hside h₁ v hi1
          show visitParameter (s7b_firstVisitQ hn hsep hm hQC v) < _
          linarith
      refine s7r_reach_of_transit hn hQ S _ _ _ _ rfl hne_u
        (s7r_transit_window' hn hQ hsep hm hQC hc S hSimg _ _ a (hedge_u.trans hea)
          (Or.inr ⟨s7e_va_edge hc, hlt_u⟩) ?_)
      intro w' he hlo hhi
      have hhi' : visitParameter w' < visitParameter (s7e_va hc) := by
        rcases hhi with h | h
        · exact absurd h Sum.inr_ne_inl
        · exact h
      have he' : w'.2.val = firstHalfIndex M a (s7e_mEdge m₁) := he.trans hea.symm
      refine ⟨fun h => by rw [h] at hhi'; exact lt_irrefl _ hhi', ?_, ?_, hvl_ex w' he' hlo⟩
      · intro v' hv'
        obtain ⟨hv'e, hiff⟩ := hfirst w' he' v' hv'
        exact s7r_no_half_between hn₁ h₁ m₁ _ rfl v' hv'e (hiff.mp hlo) (Or.inl hnx)
      · intro v' hv'
        have := hsecond_cut w' he' v' hv'
        linarith
    · -- off the cut, vertex target `inl (i + 1) ↦ μ_{firstHalfIndex i + 1}`
      have hi1' : s7e_mEdge m₁ + 1 ≠ 0 := fun h => hi1 (eq_neg_of_add_eq_zero_left h)
      have hm' : s7r_slidingMark' hn hsep hm hQC (s7e_va hc) (Sum.inl (nextMark hn₁ h₁ m₁)) =
          Sum.inl (firstHalfIndex M a (s7e_mEdge m₁) + 1) := by
        rw [hnx, s7r_slidingMark'_inl_inl hn hsep hm hQC hc hi1', firstHalfIndex_next M a hi1]
      rw [hm'] at hne_u ⊢
      refine s7r_reach_of_transit hn hQ S _ _ _ _ rfl hne_u
        (s7r_transit_window' hn hQ hsep hm hQC hc S hSimg _ _ _ hedge_u (Or.inl rfl) ?_)
      intro w' he hlo _
      refine ⟨fun h => hi1 (hcutedge w' he (by rw [h]; rfl)), ?_, ?_, hvl_ex w' he hlo⟩
      · intro v' hv'
        obtain ⟨hv'e, hiff⟩ := hfirst w' he v' hv'
        exact s7r_no_half_between hn₁ h₁ m₁ _ rfl v' hv'e (hiff.mp hlo) (Or.inl hnx)
      · intro v' hv'
        rw [← hv', s7b_secondVisitQ_edge] at he
        exact hi1 (s7b_firstHalfIndex_eq_secondHalfEdgeIndex hn hsep he.symm).1
  · -- target: a visit `w` of `λ₁` on the edge of `m₁`, `↦ firstVisitQ w`
    have hm' : s7r_slidingMark' hn hsep hm hQC (s7e_va hc) (Sum.inl (nextMark hn₁ h₁ m₁)) =
        Sum.inr (s7b_firstVisitQ hn hsep hm hQC w) := by rw [hnx, s7r_slidingMark'_inl_inr]
    rw [hm'] at hne_u ⊢
    have hwQe : (s7b_firstVisitQ hn hsep hm hQC w).2.val = firstHalfIndex M a (s7e_mEdge m₁) := by
      rw [s7b_firstVisitQ_edge, hwe]
    have hlt_u : s7e_mParam (s7r_qmark₁' hn hsep hm hQC hc m₁) <
        visitParameter (s7b_firstVisitQ hn hsep hm hQC w) :=
      (s7r_param_first' hn hQ hsep hz hm hr hr0 hη hQC hw hord h₁ hc hn₁ m₁ w hwe).mpr hwp
    refine s7r_reach_of_transit hn hQ S _ _ _ _ rfl hne_u
      (s7r_transit_window' hn hQ hsep hm hQC hc S hSimg _ _ _ hedge_u (Or.inr ⟨hwQe, hlt_u⟩) ?_)
    intro w' he hlo hhi
    have hhi' : visitParameter w' < visitParameter (s7b_firstVisitQ hn hsep hm hQC w) := by
      rcases hhi with h | h
      · exact absurd h Sum.inr_ne_inl
      · exact h
    refine ⟨?_, ?_, ?_, hvl_ex w' he hlo⟩
    · intro h
      have hi1 := hcutedge w' he (by rw [h]; rfl)
      have hwlt := s7r_first_cut_lt hn hQ hsep hz hm hr hr0 hQC hw hside h₁ w (hwe.trans hi1)
      rw [h] at hhi'
      linarith
    · intro v' hv'
      obtain ⟨hv'e, hiff⟩ := hfirst w' he v' hv'
      have hup : visitParameter v' < visitParameter w := by
        rw [← hv'] at hhi'
        exact (s7r_first_order hn hsep hz hm hr hr0 hQC hord v' w (hv'e.trans hwe.symm)).mp hhi'
      exact s7r_no_half_between hn₁ h₁ m₁ _ rfl v' hv'e (hiff.mp hlo)
        (Or.inr ⟨by rw [hnx]; exact hwe, by rw [hnx]; exact hup⟩)
    · intro v' hv'
      have h1 := hsecond_cut w' he v' hv'
      have hi1 : s7e_mEdge m₁ = -1 := by
        rw [← hv', s7b_secondVisitQ_edge] at he
        exact (s7b_firstHalfIndex_eq_secondHalfEdgeIndex hn hsep he.symm).1
      have hwlt := s7r_first_cut_lt hn hQ hsep hz hm hr hr0 hQC hw hside h₁ w (hwe.trans hi1)
      linarith

include hQ hz hr hr0 hr1 hη hw hord hside hxS hSimg h₂ in
/-- **First-half step on the leg-`M` side.** -/
theorem s7r_step_first' (hn₁ : 3 ≤ firstHalfSize M a) (S₁ : Finset (Crossing (firstHalf P M a)))
    (hS₁ : S₁ = s7b_pre (s7b_firstCrossingQ hn hsep hm hQC) S) (m : Mark (firstHalf P M a)) :
    ∃ k : ℕ, 0 < k ∧ ((smoothingSuccessor hn hQ S) ^ k)
        (s7r_slidingMark' hn hsep hm hQC (s7e_va hc) (Sum.inl m)) =
      s7r_slidingMark' hn hsep hm hQC (s7e_va hc) (Sum.inl (smoothingSuccessor hn₁ h₁ S₁ m)) ∧
      ∀ j : ℕ, 0 < j → j < k → ((smoothingSuccessor hn hQ S) ^ j)
        (s7r_slidingMark' hn hsep hm hQC (s7e_va hc) (Sum.inl m)) ∉
          Set.range (s7r_slidingMark' hn hsep hm hQC (s7e_va hc)) := by
  have hu : selectedMarkPerm S (s7r_slidingMark' hn hsep hm hQC (s7e_va hc) (Sum.inl m)) =
      s7r_qmark₁' hn hsep hm hQC hc (selectedMarkPerm S₁ m) := by
    cases m with
    | inl i =>
      by_cases hi : i = 0
      · subst hi
        rw [s7r_slidingMark'_inl_inl_zero, selectedMarkPerm_visit, selectedMarkPerm_vertex, s7r_qmark₁'_zero,
          selectedVisitTwin_of_mem S _ hxS, s7e_twin_va hc (s7e_a_ne_leg true hsep)]
      · rw [s7r_slidingMark'_inl_inl hn hsep hm hQC hc hi, selectedMarkPerm_vertex, selectedMarkPerm_vertex,
          s7r_qmark₁'_inl hn hsep hm hQC hc hi]
    | inr v =>
      rw [s7r_slidingMark'_inl_inr, selectedMarkPerm_visit, selectedMarkPerm_visit, s7r_qmark₁'_inr]
      congr 1
      by_cases hv : v.1 ∈ S₁
      · have hvQ : (s7b_firstVisitQ hn hsep hm hQC v).1 ∈ S := by
          rw [s7b_firstVisitQ_fst]; rw [hS₁, s7b_mem_pre] at hv; exact hv
        rw [selectedVisitTwin_of_mem S₁ v hv, selectedVisitTwin_of_mem S _ hvQ, s7b_firstVisitQ_visitTwin]
      · have hvQ : (s7b_firstVisitQ hn hsep hm hQC v).1 ∉ S := by
          rw [s7b_firstVisitQ_fst]; rw [hS₁, s7b_mem_pre] at hv; exact hv
        rw [selectedVisitTwin_of_not_mem S₁ v hv, selectedVisitTwin_of_not_mem S _ hvQ]
  exact s7r_step_of_reach hn hQ S _ (Sum.inl m) _ _ hu
    (s7r_reach_first' hn hQ hsep hz hm hr hr0 hr1 hη hQC hw hord hside h₁ h₂ hc S hSimg hn₁
      (selectedMarkPerm S₁ m))

/-! ##### The second half on the leg-`M` side: the vertex `0 ↦ μ_M` leaves through `v_ℓ` then `v_a` -/

theorem s7r_edge_second' (m₂ : Mark (secondHalf P M a)) (h0 : m₂ ≠ Sum.inl 0) :
    s7e_mEdge (s7r_slidingMark' hn hsep hm hQC (s7e_va hc) (Sum.inr m₂)) =
      secondHalfEdgeIndex M a (s7e_mEdge m₂) := by
  cases m₂ with
  | inl j =>
    have hj : j ≠ 0 := fun h => h0 (by rw [h])
    rw [s7r_slidingMark'_inr_inl, secondHalfIndex_nonzero M a hj]; rfl
  | inr v => rw [s7r_slidingMark'_inr_inr]; rfl

include hQ hz hr hr1 hord h₂ in
theorem s7r_param_second' (hn₂ : 3 ≤ secondHalfSize M a) (m₂ : Mark (secondHalf P M a)) (h0 : m₂ ≠ Sum.inl 0)
    (v' : Visit (secondHalf P M a)) (he : v'.2.val = s7e_mEdge m₂) :
    s7e_mParam (s7r_slidingMark' hn hsep hm hQC (s7e_va hc) (Sum.inr m₂)) <
        visitParameter (s7b_secondVisitQ hn hsep hm hQC v') ↔
      s7e_mParam m₂ < visitParameter v' := by
  cases m₂ with
  | inl j =>
    rw [s7r_slidingMark'_inr_inl]
    exact iff_of_true (s7e_visitParameter_pos hn hQ _) (s7e_visitParameter_pos hn₂ h₂ v')
  | inr v => rw [s7r_slidingMark'_inr_inr]; exact s7r_second_order hn hsep hz hm hr hr1 hQC hord v v' he.symm

include hQ hz hr hr0 hr1 hη hw hord hside hSimg h₁ in
/-- **The chain out of the contact `a`-visit** (the exit of `λ₂`'s vertex `0`): the iterates from
`nextMark v_a` reach the Q-mark of `nextMark (inl 0)` on `λ₂` through transit marks. -/
theorem s7r_reach_from_va' (hn₂ : 3 ≤ secondHalfSize M a) :
    ∃ k : ℕ, ((smoothingSuccessor hn hQ S) ^ k) (nextMark hn hQ (Sum.inr (s7e_va hc))) =
      s7r_slidingMark' hn hsep hm hQC (s7e_va hc) (Sum.inr (nextMark hn₂ h₂ (Sum.inl 0))) ∧
      ∀ j : ℕ, j < k → ((smoothingSuccessor hn hQ S) ^ j) (nextMark hn hQ (Sum.inr (s7e_va hc))) ∉
          Set.range (s7r_slidingMark' hn hsep hm hQC (s7e_va hc)) := by
  have hva_near := s7e_va_param_near hn hQ true hw hc
  have hva1 := (abs_lt.mp hva_near).1
  have hva2 := (abs_lt.mp hva_near).2
  have hfirst : ∀ (w' : Visit Q), w'.2.val = a → visitParameter (s7e_va hc) < visitParameter w' →
      ∀ v', s7b_firstVisitQ hn hsep hm hQC v' ≠ w' := by
    intro w' he hlo v' hv'
    have hv'1 : v'.2.val = -1 := by
      rw [← hv', s7b_firstVisitQ_edge] at he
      exact firstHalfIndex_injective M a (by rw [he, firstHalfIndex_last])
    have h1 := s7r_first_cut_lt hn hQ hsep hz hm hr hr0 hQC hw hside h₁ v' hv'1
    rw [← hv'] at hlo
    linarith
  have hvl_ex : ∀ (w' : Visit Q), w'.2.val = a → w' ≠ s7e_vl hc := by
    intro w' he h; rw [h, s7e_vl_edge, s7r_leg_true] at he; exact s7e_a_ne_M hsep he.symm
  have hsecond : ∀ (w' : Visit Q), w'.2.val = a → ∀ v', s7b_secondVisitQ hn hsep hm hQC v' = w' →
      v'.2.val = 0 := by
    intro w' he v' hv'
    rw [← hv', s7b_secondVisitQ_edge] at he
    exact secondHalfEdgeIndex_injective M a (by rw [he, secondHalfEdgeIndex_zero])
  rcases s7r_nextMark_shape hn₂ h₂ (Sum.inl 0) with hnx | ⟨w, hnx, hwe, hwp⟩
  · have hm' : s7r_slidingMark' hn hsep hm hQC (s7e_va hc) (Sum.inr (nextMark hn₂ h₂ (Sum.inl 0))) =
        Sum.inl (a + 1) := by
      rw [hnx, s7r_slidingMark'_inr_inl]
      show Sum.inl (secondHalfIndex M a (0 + 1)) = _
      rw [zero_add, secondHalfIndex_one hn hsep]
    rw [hm']
    refine s7r_reach_of_transit hn hQ S _ _ _ _ rfl Sum.inr_ne_inl
      (s7r_transit_window' hn hQ hsep hm hQC hc S hSimg _ _ a (s7e_va_edge hc) (Or.inl rfl) ?_)
    intro w' he hlo _
    refine ⟨fun h => by rw [h] at hlo; exact lt_irrefl _ hlo, hfirst w' he hlo, ?_, hvl_ex w' he⟩
    intro v' hv'
    have hv'0 := hsecond w' he v' hv'
    have hb := s7e_between_inl_mark_inl hn₂ h₂ 0 (Sum.inr v') hv'0 (s7e_visitParameter_pos hn₂ h₂ v')
    exact nextMark_no_mark_between hn₂ h₂ hnx (Sum.inr v') hb
  · have hm' : s7r_slidingMark' hn hsep hm hQC (s7e_va hc) (Sum.inr (nextMark hn₂ h₂ (Sum.inl 0))) =
        Sum.inr (s7b_secondVisitQ hn hsep hm hQC w) := by rw [hnx, s7r_slidingMark'_inr_inr]
    rw [hm']
    have hwe0 : w.2.val = 0 := hwe
    have hwgt := s7r_second_cut_gt hn hQ hsep hz hm hr hr1 hQC hw hside h₂ w hwe0
    have hne : (Sum.inr (s7e_va hc) : Mark Q) ≠ Sum.inr (s7b_secondVisitQ hn hsep hm hQC w) := by
      intro h
      exact s7b_secondCrossingQ_not_affected hn hsep hm hQC w.1
        (by rw [← s7b_secondVisitQ_fst hn hsep hm hQC w, ← Sum.inr_injective h]; exact s7r_va_affected' hc)
    refine s7r_reach_of_transit hn hQ S _ _ _ _ rfl hne
      (s7r_transit_window' hn hQ hsep hm hQC hc S hSimg _ _ a (s7e_va_edge hc)
        (Or.inr ⟨by show (s7b_secondVisitQ hn hsep hm hQC w).2.val = a; rw [s7b_secondVisitQ_edge, hwe0, secondHalfEdgeIndex_zero], by
          show visitParameter (s7e_va hc) < visitParameter (s7b_secondVisitQ hn hsep hm hQC w); linarith⟩) ?_)
    intro w' he hlo hhi
    have hhi' : visitParameter w' < visitParameter (s7b_secondVisitQ hn hsep hm hQC w) := by
      rcases hhi with h | h
      · exact absurd h Sum.inr_ne_inl
      · exact h
    refine ⟨fun h => by rw [h] at hlo; exact lt_irrefl _ hlo, hfirst w' he hlo, ?_, hvl_ex w' he⟩
    intro v' hv'
    have hv'0 := hsecond w' he v' hv'
    have hup : visitParameter v' < visitParameter w := by
      rw [← hv'] at hhi'
      exact (s7r_second_order hn hsep hz hm hr hr1 hQC hord v' w (hv'0.trans hwe0.symm)).mp hhi'
    have hb := s7e_between_same_edge hn₂ h₂ (Sum.inl 0) (Sum.inr v') (Sum.inr w) hv'0.symm
      (by rw [s7e_mEdge_inr, s7e_mEdge_inr, hv'0, hwe0]) (s7e_visitParameter_pos hn₂ h₂ v') hup
    exact nextMark_no_mark_between hn₂ h₂ hnx (Sum.inr v') hb

include hQ hz hr hr0 hr1 hη hw hord hside huniq hxS hSimg h₁ in
/-- **Second-half reach on the leg-`M` side.** -/
theorem s7r_reach_second' (hn₂ : 3 ≤ secondHalfSize M a) (m₂ : Mark (secondHalf P M a)) :
    ∃ k : ℕ, ((smoothingSuccessor hn hQ S) ^ k)
        (nextMark hn hQ (s7r_slidingMark' hn hsep hm hQC (s7e_va hc) (Sum.inr m₂))) =
      s7r_slidingMark' hn hsep hm hQC (s7e_va hc) (Sum.inr (nextMark hn₂ h₂ m₂)) ∧
      ∀ j : ℕ, j < k → ((smoothingSuccessor hn hQ S) ^ j)
        (nextMark hn hQ (s7r_slidingMark' hn hsep hm hQC (s7e_va hc) (Sum.inr m₂))) ∉
          Set.range (s7r_slidingMark' hn hsep hm hQC (s7e_va hc)) := by
  have hinj := s7r_slidingMark'_injective hn hsep hm hQC hc
  have hva_near := s7e_va_param_near hn hQ true hw hc
  have hva1 := (abs_lt.mp hva_near).1
  have hva2 := (abs_lt.mp hva_near).2
  by_cases h0 : m₂ = Sum.inl 0
  · -- the vertex `0 ↦ μ_M`: `nextMark μ_M = v_ℓ`, `f v_ℓ = nextMark v_a`, then the chain out of `v_a`
    subst h0
    rw [s7r_slidingMark'_inr_inl, secondHalfIndex_zero, s7r_nextMark_M hn hQ hsep hη hw hc huniq]
    refine s7r_reach_trans hn hQ S _ ⟨0, by simp, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
      (s7r_vl_not_mem_range' hn hsep hm hQC hc) ?_
    rw [s7r_succ_vl' hn hQ hsep hc S hxS]
    exact s7r_reach_from_va' hn hQ hsep hz hm hr hr0 hr1 hη hQC hw hord hside h₁ h₂ hc S hSimg hn₂
  · have hedge_u := s7r_edge_second' hn hsep hm hQC hc m₂ h0
    have hne_u : s7r_slidingMark' hn hsep hm hQC (s7e_va hc) (Sum.inr m₂) ≠
        s7r_slidingMark' hn hsep hm hQC (s7e_va hc) (Sum.inr (nextMark hn₂ h₂ m₂)) := fun h =>
      markSuccessor_ne_self hn₂ h₂ m₂ (Sum.inr.inj (hinj h)).symm
    have hsecond : ∀ (w' : Visit Q), w'.2.val = secondHalfEdgeIndex M a (s7e_mEdge m₂) →
        ∀ v' : Visit (secondHalf P M a), s7b_secondVisitQ hn hsep hm hQC v' = w' →
        v'.2.val = s7e_mEdge m₂ ∧
          (s7e_mParam (s7r_slidingMark' hn hsep hm hQC (s7e_va hc) (Sum.inr m₂)) < visitParameter w' ↔
            s7e_mParam m₂ < visitParameter v') := by
      intro w' he v' hv'
      have hv'e : v'.2.val = s7e_mEdge m₂ := by
        apply secondHalfEdgeIndex_injective M a
        rw [← s7b_secondVisitQ_edge hn hsep hm hQC v', hv', he]
      refine ⟨hv'e, ?_⟩
      rw [← hv']
      exact s7r_param_second' hn hQ hsep hz hm hr hr1 hQC hord h₂ hc hn₂ m₂ h0 v' hv'e
    -- on the cut (`j = 0`, forced by `m₂ = inr v`) the Q-mark is beyond `r + 3η`
    have hlow0 : s7e_mEdge m₂ = 0 →
        r + 3 * η < s7e_mParam (s7r_slidingMark' hn hsep hm hQC (s7e_va hc) (Sum.inr m₂)) := by
      intro hj0
      cases m₂ with
      | inl j => exact absurd (by rw [show j = 0 from hj0]) h0
      | inr v =>
        rw [s7r_slidingMark'_inr_inr]
        exact s7r_second_cut_gt hn hQ hsep hz hm hr hr1 hQC hw hside h₂ v hj0
    have hfirst : ∀ (w' : Visit Q), w'.2.val = secondHalfEdgeIndex M a (s7e_mEdge m₂) →
        s7e_mParam (s7r_slidingMark' hn hsep hm hQC (s7e_va hc) (Sum.inr m₂)) < visitParameter w' →
        ∀ v', s7b_firstVisitQ hn hsep hm hQC v' ≠ w' := by
      intro w' he hlo v' hv'
      rw [← hv', s7b_firstVisitQ_edge] at he
      obtain ⟨hv'1, hj0⟩ := s7b_firstHalfIndex_eq_secondHalfEdgeIndex hn hsep he
      have h1 := s7r_first_cut_lt hn hQ hsep hz hm hr hr0 hQC hw hside h₁ v' hv'1
      have h2 := hlow0 hj0
      rw [← hv'] at hlo
      linarith
    have hva_ex : ∀ (w' : Visit Q), w'.2.val = secondHalfEdgeIndex M a (s7e_mEdge m₂) →
        s7e_mParam (s7r_slidingMark' hn hsep hm hQC (s7e_va hc) (Sum.inr m₂)) < visitParameter w' →
        w' ≠ s7e_va hc := by
      intro w' he hlo h
      rw [h, s7e_va_edge] at he
      have hj0 : s7e_mEdge m₂ = 0 :=
        secondHalfEdgeIndex_injective M a (by rw [← he, secondHalfEdgeIndex_zero])
      have h2 := hlow0 hj0
      rw [h] at hlo
      linarith
    have hvl_ex : ∀ (w' : Visit Q), w'.2.val = secondHalfEdgeIndex M a (s7e_mEdge m₂) → w' ≠ s7e_vl hc := by
      intro w' he h
      rw [h, s7e_vl_edge, s7r_leg_true] at he
      exact s7b_secondHalfEdgeIndex_ne hn hsep _ he.symm
    rcases s7r_nextMark_shape hn₂ h₂ m₂ with hnx | ⟨w, hnx, hwe, hwp⟩
    · -- vertex target `inl (j+1) ↦ μ_{secondHalfEdgeIndex j + 1}` (for `j = −1` this is `μ_M`)
      have hm' : s7r_slidingMark' hn hsep hm hQC (s7e_va hc) (Sum.inr (nextMark hn₂ h₂ m₂)) =
          Sum.inl (secondHalfEdgeIndex M a (s7e_mEdge m₂) + 1) := by
        rw [hnx, s7r_slidingMark'_inr_inl, s7r_secondHalfIndex_succ hn hsep]
      rw [hm'] at hne_u ⊢
      refine s7r_reach_of_transit hn hQ S _ _ _ _ rfl hne_u
        (s7r_transit_window' hn hQ hsep hm hQC hc S hSimg _ _ _ hedge_u (Or.inl rfl) ?_)
      intro w' he hlo _
      refine ⟨hva_ex w' he hlo, hfirst w' he hlo, ?_, hvl_ex w' he⟩
      intro v' hv'
      obtain ⟨hv'e, hiff⟩ := hsecond w' he v' hv'
      exact s7r_no_half_between hn₂ h₂ m₂ _ rfl v' hv'e (hiff.mp hlo) (Or.inl hnx)
    · have hm' : s7r_slidingMark' hn hsep hm hQC (s7e_va hc) (Sum.inr (nextMark hn₂ h₂ m₂)) =
          Sum.inr (s7b_secondVisitQ hn hsep hm hQC w) := by rw [hnx, s7r_slidingMark'_inr_inr]
      rw [hm'] at hne_u ⊢
      have hwQe : (s7b_secondVisitQ hn hsep hm hQC w).2.val = secondHalfEdgeIndex M a (s7e_mEdge m₂) := by
        rw [s7b_secondVisitQ_edge, hwe]
      have hlt_u : s7e_mParam (s7r_slidingMark' hn hsep hm hQC (s7e_va hc) (Sum.inr m₂)) <
          visitParameter (s7b_secondVisitQ hn hsep hm hQC w) :=
        (s7r_param_second' hn hQ hsep hz hm hr hr1 hQC hord h₂ hc hn₂ m₂ h0 w hwe).mpr hwp
      refine s7r_reach_of_transit hn hQ S _ _ _ _ rfl hne_u
        (s7r_transit_window' hn hQ hsep hm hQC hc S hSimg _ _ _ hedge_u (Or.inr ⟨hwQe, hlt_u⟩) ?_)
      intro w' he hlo hhi
      have hhi' : visitParameter w' < visitParameter (s7b_secondVisitQ hn hsep hm hQC w) := by
        rcases hhi with h | h
        · exact absurd h Sum.inr_ne_inl
        · exact h
      refine ⟨hva_ex w' he hlo, hfirst w' he hlo, ?_, hvl_ex w' he⟩
      intro v' hv'
      obtain ⟨hv'e, hiff⟩ := hsecond w' he v' hv'
      have hup : visitParameter v' < visitParameter w := by
        rw [← hv'] at hhi'
        exact (s7r_second_order hn hsep hz hm hr hr1 hQC hord v' w (hv'e.trans hwe.symm)).mp hhi'
      exact s7r_no_half_between hn₂ h₂ m₂ _ rfl v' hv'e (hiff.mp hlo)
        (Or.inr ⟨by rw [hnx]; exact hwe, by rw [hnx]; exact hup⟩)

include hQ hz hr hr0 hr1 hη hw hord hside huniq hxS hSimg h₁ in
/-- **Second-half step on the leg-`M` side.** -/
theorem s7r_step_second' (hn₂ : 3 ≤ secondHalfSize M a) (S₂ : Finset (Crossing (secondHalf P M a)))
    (hS₂ : S₂ = s7b_pre (s7b_secondCrossingQ hn hsep hm hQC) S) (m : Mark (secondHalf P M a)) :
    ∃ k : ℕ, 0 < k ∧ ((smoothingSuccessor hn hQ S) ^ k)
        (s7r_slidingMark' hn hsep hm hQC (s7e_va hc) (Sum.inr m)) =
      s7r_slidingMark' hn hsep hm hQC (s7e_va hc) (Sum.inr (smoothingSuccessor hn₂ h₂ S₂ m)) ∧
      ∀ j : ℕ, 0 < j → j < k → ((smoothingSuccessor hn hQ S) ^ j)
        (s7r_slidingMark' hn hsep hm hQC (s7e_va hc) (Sum.inr m)) ∉
          Set.range (s7r_slidingMark' hn hsep hm hQC (s7e_va hc)) := by
  have hu : selectedMarkPerm S (s7r_slidingMark' hn hsep hm hQC (s7e_va hc) (Sum.inr m)) =
      s7r_slidingMark' hn hsep hm hQC (s7e_va hc) (Sum.inr (selectedMarkPerm S₂ m)) := by
    cases m with
    | inl j => rfl
    | inr v =>
      rw [s7r_slidingMark'_inr_inr, selectedMarkPerm_visit, selectedMarkPerm_visit, s7r_slidingMark'_inr_inr]
      congr 1
      by_cases hv : v.1 ∈ S₂
      · have hvQ : (s7b_secondVisitQ hn hsep hm hQC v).1 ∈ S := by
          rw [s7b_secondVisitQ_fst]; rw [hS₂, s7b_mem_pre] at hv; exact hv
        rw [selectedVisitTwin_of_mem S₂ v hv, selectedVisitTwin_of_mem S _ hvQ, s7b_secondVisitQ_visitTwin]
      · have hvQ : (s7b_secondVisitQ hn hsep hm hQC v).1 ∉ S := by
          rw [s7b_secondVisitQ_fst]; rw [hS₂, s7b_mem_pre] at hv; exact hv
        rw [selectedVisitTwin_of_not_mem S₂ v hv, selectedVisitTwin_of_not_mem S _ hvQ]
  exact s7r_step_of_reach hn hQ S _ (Sum.inr m) _ _ hu
    (s7r_reach_second' hn hQ hsep hz hm hr hr0 hr1 hη hQC hw hord hside h₁ h₂ hc huniq S hxS hSimg hn₂
      (selectedMarkPerm S₂ m))

include hQ hz hr hr0 hr1 hη hw hord hside hxS hSimg h₁ h₂ in
/-- **Hit on the leg-`M` side** (beacon `μ_M`; the leg visit exits through `v_a`'s chain). -/
theorem s7r_hit' (u : Mark Q) :
    ∃ j : ℕ, ((smoothingSuccessor hn hQ S) ^ j) u ∈ Set.range (s7r_slidingMark' hn hsep hm hQC (s7e_va hc)) := by
  refine s7r_hit_of_transit hn hQ S _ (Sum.inl M)
    ⟨Sum.inr (Sum.inl 0), by rw [s7r_slidingMark'_inr_inl, secondHalfIndex_zero]⟩ ?_ _ u rfl
  intro w hwr
  cases w with
  | inl i => exact Or.inr (smoothingSuccessor_vertex hn hQ S i)
  | inr w' =>
    by_cases hwS : w'.1 ∈ S
    · by_cases hwx : w'.1 = (s7e_va hc).1
      · rcases s7e_visit_of_fst hc w' (by rw [hwx]; rfl) (s7e_a_ne_leg true hsep) with h | h
        · exact absurd (h ▸ s7r_va_mem_range' hn hsep hm hQC hc) hwr
        · subst h; left
          obtain ⟨k, hk, -⟩ := s7r_reach_from_va' hn hQ hsep hz hm hr hr0 hr1 hη hQC hw hord hside h₁ h₂ hc S hSimg
            (contactHalfSizes_bounds hn hsep).2.1
          refine ⟨k + 1, ?_⟩
          rw [pow_succ, Equiv.Perm.mul_apply, s7r_succ_vl' hn hQ hsep hc S hxS, hk]
          exact ⟨_, rfl⟩
      · exfalso; apply hwr
        rcases hSimg w'.1 hwS hwx with ⟨c, hcw⟩ | ⟨c, hcw⟩
        · obtain ⟨v, -, hv⟩ := s7b_visit_of_firstCrossingQ hn hsep hm hQC w' c hcw.symm
          exact (s7r_inr_mem_range_iff' hn hsep hm hQC hc w').mpr (Or.inr (Or.inl ⟨v, hv⟩))
        · obtain ⟨v, -, hv⟩ := s7b_visit_of_secondCrossingQ hn hsep hm hQC w' c hcw.symm
          exact (s7r_inr_mem_range_iff' hn hsep hm hQC hc w').mpr (Or.inr (Or.inr ⟨v, hv⟩))
    · exact Or.inr (smoothingSuccessor_visit_of_not_mem hn hQ S w' hwS)

include hz hr hr0 hr1 hη hw hord hside huniq hxS hSimg in
/-- **The first-return law on the leg-`M` side, PROVED for the corrected mark map** (the corrected
form of `s7b_SlidingTransport.ret` there, rule 4). -/
theorem s7r_slidingTransport_of_leg_true :
    s7r_SlidingTransport' hn hQ hsep hm hQC h₁ h₂ S (s7b_pre (s7b_firstCrossingQ hn hsep hm hQC) S)
      (s7b_pre (s7b_secondCrossingQ hn hsep hm hQC) S) (s7e_va hc) where
  affected := s7r_va_affected' hc
  pivot_mem := hxS
  first_pre := rfl
  second_pre := rfl
  ret :=
    { inj := s7r_slidingMark'_injective hn hsep hm hQC hc
      step := fun b => by
        rcases b with m | m
        · exact s7r_step_first' hn hQ hsep hz hm hr hr0 hr1 hη hQC hw hord hside h₁ h₂ hc S hxS hSimg
            (contactHalfSizes_bounds hn hsep).1.1 _ rfl m
        · exact s7r_step_second' hn hQ hsep hz hm hr hr0 hr1 hη hQC hw hord hside h₁ h₂ hc huniq S hxS hSimg
            (contactHalfSizes_bounds hn hsep).2.1 _ rfl m
      hit := s7r_hit' hn hQ hsep hz hm hr hr0 hr1 hη hQC hw hord hside h₁ h₂ hc S hxS hSimg }

end S7RLegTrue

section S7RTransportConsequences

/-! ##### The consequences of `s7r_SlidingTransport'` (the leg-`M` side): the port of the
`s7b_SlidingTransport` namespace (owners, `componentEquiv`, carrier crossings and `m_Q`) to the corrected
mark map — part I is generic in `ι`, so the proofs are those of SM/CornerChainUnits verbatim; only the two
contact-carrier lemmas exchange their halves. -/

variable {hn : 3 ≤ n} {M a : ZMod n} {hsep : ContactSeparated M a} {P Q : LabelledTuple n}
  {hm : P M ∈ edgeInterior P a}
  {hQC : ∀ s, ¬ ContactAffected M a s → (IsCrossing Q s ↔ IsCrossing P s)}
  {hQ : Generic Q} {h₁ : Generic (firstHalf P M a)} {h₂ : Generic (secondHalf P M a)}
  {S : Finset (Crossing Q)} {S₁ : Finset (Crossing (firstHalf P M a))}
  {S₂ : Finset (Crossing (secondHalf P M a))} {va : Visit Q}

namespace s7r_SlidingTransport'

variable {hn : 3 ≤ n} {M a : ZMod n} {hsep : ContactSeparated M a} {P Q : LabelledTuple n}
  {hm : P M ∈ edgeInterior P a}
  {hQC : ∀ s, ¬ ContactAffected M a s → (IsCrossing Q s ↔ IsCrossing P s)}
  {hQ : Generic Q} {h₁ : Generic (firstHalf P M a)} {h₂ : Generic (secondHalf P M a)}
  {S : Finset (Crossing Q)} {S₁ : Finset (Crossing (firstHalf P M a))}
  {S₂ : Finset (Crossing (secondHalf P M a))} {va : Visit Q}

/-- Two marks of `λ₁` have one owner iff their images have one owner on `Q`. -/
theorem owner_inl_iff (h : s7r_SlidingTransport' hn hQ hsep hm hQC h₁ h₂ S S₁ S₂ va)
    (m m' : Mark (firstHalf P M a)) :
    owner hn hQ S (s7r_slidingMark' hn hsep hm hQC va (Sum.inl m)) =
        owner hn hQ S (s7r_slidingMark' hn hsep hm hQC va (Sum.inl m')) ↔
      owner (contactHalfSizes_bounds hn hsep).1.1 h₁ S₁ m =
        owner (contactHalfSizes_bounds hn hsep).1.1 h₁ S₁ m' := by
  rw [owner_eq_iff, owner_eq_iff, h.ret.sameCycle_iff, s7b_sumCongr_sameCycle_inl]

theorem owner_inr_iff (h : s7r_SlidingTransport' hn hQ hsep hm hQC h₁ h₂ S S₁ S₂ va)
    (m m' : Mark (secondHalf P M a)) :
    owner hn hQ S (s7r_slidingMark' hn hsep hm hQC va (Sum.inr m)) =
        owner hn hQ S (s7r_slidingMark' hn hsep hm hQC va (Sum.inr m')) ↔
      owner (contactHalfSizes_bounds hn hsep).2.1 h₂ S₂ m =
        owner (contactHalfSizes_bounds hn hsep).2.1 h₂ S₂ m' := by
  rw [owner_eq_iff, owner_eq_iff, h.ret.sameCycle_iff, s7b_sumCongr_sameCycle_inr]

/-- Marks of the two different halves never share an owner on `Q`. -/
theorem owner_inl_ne_inr (h : s7r_SlidingTransport' hn hQ hsep hm hQC h₁ h₂ S S₁ S₂ va)
    (m : Mark (firstHalf P M a)) (m' : Mark (secondHalf P M a)) :
    owner hn hQ S (s7r_slidingMark' hn hsep hm hQC va (Sum.inl m)) ≠
      owner hn hQ S (s7r_slidingMark' hn hsep hm hQC va (Sum.inr m')) := by
  rw [Ne, owner_eq_iff, h.ret.sameCycle_iff]
  exact s7b_sumCongr_not_sameCycle _ _ m m'

/-- **The carrier correspondence of a sliding row**: the carriers of `S` on `Q` are the carriers of
`S₁` on `λ₁` together with those of `S₂` on `λ₂` (eq. s7c:sliding-residual). -/
def componentEquiv (h : s7r_SlidingTransport' hn hQ hsep hm hQC h₁ h₂ S S₁ S₂ va) :
    Component hn hQ S ≃
      Component (contactHalfSizes_bounds hn hsep).1.1 h₁ S₁ ⊕
        Component (contactHalfSizes_bounds hn hsep).2.1 h₂ S₂ :=
  h.ret.cycleEquiv.symm.trans (s7b_sumCongr_cycleEquiv _ _)

theorem componentEquiv_owner_inl (h : s7r_SlidingTransport' hn hQ hsep hm hQC h₁ h₂ S S₁ S₂ va)
    (m : Mark (firstHalf P M a)) :
    h.componentEquiv (owner hn hQ S (s7r_slidingMark' hn hsep hm hQC va (Sum.inl m))) =
      Sum.inl (owner (contactHalfSizes_bounds hn hsep).1.1 h₁ S₁ m) := by
  have he : owner hn hQ S (s7r_slidingMark' hn hsep hm hQC va (Sum.inl m)) =
      h.ret.cycleEquiv (Quotient.mk _ (Sum.inl m)) := rfl
  show s7b_sumCongr_cycleEquiv _ _
    (h.ret.cycleEquiv.symm (owner hn hQ S (s7r_slidingMark' hn hsep hm hQC va (Sum.inl m)))) = _
  rw [he, Equiv.symm_apply_apply]
  rfl

theorem componentEquiv_owner_inr (h : s7r_SlidingTransport' hn hQ hsep hm hQC h₁ h₂ S S₁ S₂ va)
    (m : Mark (secondHalf P M a)) :
    h.componentEquiv (owner hn hQ S (s7r_slidingMark' hn hsep hm hQC va (Sum.inr m))) =
      Sum.inr (owner (contactHalfSizes_bounds hn hsep).2.1 h₂ S₂ m) := by
  have he : owner hn hQ S (s7r_slidingMark' hn hsep hm hQC va (Sum.inr m)) =
      h.ret.cycleEquiv (Quotient.mk _ (Sum.inr m)) := rfl
  show s7b_sumCongr_cycleEquiv _ _
    (h.ret.cycleEquiv.symm (owner hn hQ S (s7r_slidingMark' hn hsep hm hQC va (Sum.inr m)))) = _
  rw [he, Equiv.symm_apply_apply]
  rfl

/-- The owner on `Q` of a visit carried from `λ₁`, in terms of the half owner. -/
theorem componentEquiv_owner_firstVisit
    (h : s7r_SlidingTransport' hn hQ hsep hm hQC h₁ h₂ S S₁ S₂ va) (w : Visit (firstHalf P M a)) :
    h.componentEquiv (owner hn hQ S (Sum.inr (s7b_firstVisitQ hn hsep hm hQC w))) =
      Sum.inl (owner (contactHalfSizes_bounds hn hsep).1.1 h₁ S₁ (Sum.inr w)) :=
  h.componentEquiv_owner_inl (Sum.inr w)

theorem componentEquiv_owner_secondVisit
    (h : s7r_SlidingTransport' hn hQ hsep hm hQC h₁ h₂ S S₁ S₂ va) (w : Visit (secondHalf P M a)) :
    h.componentEquiv (owner hn hQ S (Sum.inr (s7b_secondVisitQ hn hsep hm hQC w))) =
      Sum.inr (owner (contactHalfSizes_bounds hn hsep).2.1 h₂ S₂ (Sum.inr w)) :=
  h.componentEquiv_owner_inr (Sum.inr w)

/-- On the leg-`M` side the carrier through the contact vertex `μ_M` on `Q` corresponds to `λ₂`'s
carrier through its vertex `0 = μ_M` (the roles of the two contact carriers are exchanged with respect
to the leg-`M−1` side, `s7b_SlidingTransport.componentEquiv_owner_vertexM`). -/
theorem componentEquiv_owner_vertexM (h : s7r_SlidingTransport' hn hQ hsep hm hQC h₁ h₂ S S₁ S₂ va) :
    h.componentEquiv (owner hn hQ S (Sum.inl M)) =
      Sum.inr (owner (contactHalfSizes_bounds hn hsep).2.1 h₂ S₂ (Sum.inl 0)) := by
  have he : (Sum.inl M : Mark Q) = s7r_slidingMark' hn hsep hm hQC va (Sum.inr (Sum.inl 0)) := by
    show _ = Sum.inl (secondHalfIndex M a 0)
    rw [secondHalfIndex_zero]
  rw [he, h.componentEquiv_owner_inr]

/-- On the leg-`M` side the carrier through the contact `a`-visit `va` on `Q` corresponds to `λ₁`'s
carrier through its vertex `0 = μ_M`. -/
theorem componentEquiv_owner_pivot (h : s7r_SlidingTransport' hn hQ hsep hm hQC h₁ h₂ S S₁ S₂ va) :
    h.componentEquiv (owner hn hQ S (Sum.inr va)) =
      Sum.inl (owner (contactHalfSizes_bounds hn hsep).1.1 h₁ S₁ (Sum.inl 0)) := by
  have he : (Sum.inr va : Mark Q) = s7r_slidingMark' hn hsep hm hQC va (Sum.inl (Sum.inl 0)) := by
    simp [s7r_slidingMark']
  rw [he, h.componentEquiv_owner_inl]

/-- A carried crossing of `λ₁` is a crossing of the carrier `q` of `S` iff it is a crossing of the
corresponding half carrier. -/
theorem firstCrossingQ_mem_carrierCrossings_iff
    (h : s7r_SlidingTransport' hn hQ hsep hm hQC h₁ h₂ S S₁ S₂ va) (c : Crossing (firstHalf P M a))
    (q : Component hn hQ S) (q₁ : Component (contactHalfSizes_bounds hn hsep).1.1 h₁ S₁)
    (hq : h.componentEquiv q = Sum.inl q₁) :
    s7b_firstCrossingQ hn hsep hm hQC c ∈ carrierCrossings hn hQ S q ↔
      c ∈ carrierCrossings (contactHalfSizes_bounds hn hsep).1.1 h₁ S₁ q₁ := by
  rw [mem_carrierCrossings, mem_carrierCrossings]
  have hmem : s7b_firstCrossingQ hn hsep hm hQC c ∈ S ↔ c ∈ S₁ := by
    rw [h.first_pre, s7b_mem_pre]
  rw [hmem]
  refine and_congr Iff.rfl ⟨fun hall w hw => ?_, fun hall v hv => ?_⟩
  · have hv := hall (s7b_firstVisitQ hn hsep hm hQC w) (by
      rw [s7b_firstVisitQ_fst, hw])
    have := h.componentEquiv_owner_firstVisit w
    rw [hv, hq] at this
    exact (Sum.inl.inj this).symm
  · obtain ⟨w, hw, rfl⟩ := s7b_visit_of_firstCrossingQ hn hsep hm hQC v c hv
    apply h.componentEquiv.injective
    rw [h.componentEquiv_owner_firstVisit, hall w hw, hq]

theorem secondCrossingQ_mem_carrierCrossings_iff
    (h : s7r_SlidingTransport' hn hQ hsep hm hQC h₁ h₂ S S₁ S₂ va) (c : Crossing (secondHalf P M a))
    (q : Component hn hQ S) (q₂ : Component (contactHalfSizes_bounds hn hsep).2.1 h₂ S₂)
    (hq : h.componentEquiv q = Sum.inr q₂) :
    s7b_secondCrossingQ hn hsep hm hQC c ∈ carrierCrossings hn hQ S q ↔
      c ∈ carrierCrossings (contactHalfSizes_bounds hn hsep).2.1 h₂ S₂ q₂ := by
  rw [mem_carrierCrossings, mem_carrierCrossings]
  have hmem : s7b_secondCrossingQ hn hsep hm hQC c ∈ S ↔ c ∈ S₂ := by
    rw [h.second_pre, s7b_mem_pre]
  rw [hmem]
  refine and_congr Iff.rfl ⟨fun hall w hw => ?_, fun hall v hv => ?_⟩
  · have hv := hall (s7b_secondVisitQ hn hsep hm hQC w) (by
      rw [s7b_secondVisitQ_fst, hw])
    have := h.componentEquiv_owner_secondVisit w
    rw [hv, hq] at this
    exact (Sum.inr.inj this).symm
  · obtain ⟨w, hw, rfl⟩ := s7b_visit_of_secondCrossingQ hn hsep hm hQC v c hv
    apply h.componentEquiv.injective
    rw [h.componentEquiv_owner_secondVisit, hall w hw, hq]

/-- A carried crossing of `λ₂` is never a crossing of a carrier corresponding to a carrier of `λ₁`
(and symmetrically). -/
theorem secondCrossingQ_notMem_carrierCrossings
    (h : s7r_SlidingTransport' hn hQ hsep hm hQC h₁ h₂ S S₁ S₂ va) (c : Crossing (secondHalf P M a))
    (q : Component hn hQ S) (q₁ : Component (contactHalfSizes_bounds hn hsep).1.1 h₁ S₁)
    (hq : h.componentEquiv q = Sum.inl q₁) :
    s7b_secondCrossingQ hn hsep hm hQC c ∉ carrierCrossings hn hQ S q := by
  intro hc
  rw [mem_carrierCrossings] at hc
  obtain ⟨i, j, hs, -, -⟩ := c.property
  have hi : i ∈ c.val := by rw [hs]; simp
  have hv := hc.2 (s7b_secondVisitQ hn hsep hm hQC ⟨c, ⟨i, hi⟩⟩) rfl
  have := h.componentEquiv_owner_secondVisit ⟨c, ⟨i, hi⟩⟩
  rw [hv, hq] at this
  exact Sum.inl_ne_inr this

theorem firstCrossingQ_notMem_carrierCrossings
    (h : s7r_SlidingTransport' hn hQ hsep hm hQC h₁ h₂ S S₁ S₂ va) (c : Crossing (firstHalf P M a))
    (q : Component hn hQ S) (q₂ : Component (contactHalfSizes_bounds hn hsep).2.1 h₂ S₂)
    (hq : h.componentEquiv q = Sum.inr q₂) :
    s7b_firstCrossingQ hn hsep hm hQC c ∉ carrierCrossings hn hQ S q := by
  intro hc
  rw [mem_carrierCrossings] at hc
  obtain ⟨i, j, hs, -, -⟩ := c.property
  have hi : i ∈ c.val := by rw [hs]; simp
  have hv := hc.2 (s7b_firstVisitQ hn hsep hm hQC ⟨c, ⟨i, hi⟩⟩) rfl
  have := h.componentEquiv_owner_firstVisit ⟨c, ⟨i, hi⟩⟩
  rw [hv, hq] at this
  exact Sum.inr_ne_inl this

/-- Under the pivot split (part IV: the crossings of `Q` off the two images are `x₋` and the
crossings interlacing it), every carrier crossing of `S` is carried from a half: a crossing
interlacing `x₋ ∈ S` has its visits on two different carriers (lem:carriers (iii)). -/
theorem carrierCrossings_mem_range
    (h : s7r_SlidingTransport' hn hQ hsep hm hQC h₁ h₂ S S₁ S₂ va)
    (hsplit : s7b_PivotSplit (Interlaces hn hQ) (Interlaces (contactHalfSizes_bounds hn hsep).1.1 h₁)
      (Interlaces (contactHalfSizes_bounds hn hsep).2.1 h₂) (s7b_firstCrossingQ hn hsep hm hQC)
      (s7b_secondCrossingQ hn hsep hm hQC) va.1)
    (hS : IsDecomposition hn hQ S) (q : Component hn hQ S) {y : Crossing Q}
    (hy : y ∈ carrierCrossings hn hQ S q) :
    y ∈ Set.range (s7b_firstCrossingQ hn hsep hm hQC) ∪
      Set.range (s7b_secondCrossingQ hn hsep hm hQC) := by
  rw [mem_carrierCrossings] at hy
  have hyx : y ≠ va.1 := fun he => hy.1 (he ▸ h.pivot_mem)
  have hnot : ∀ z : Crossing Q, Interlaces hn hQ y z → z ∈ S → False := by
    intro z hz hzS
    have hN : y ∈ supportNeighbors hn hQ S := (mem_supportNeighbors hn hQ S y).mpr ⟨z, hzS, hz⟩
    obtain ⟨i, j, hs, -, -⟩ := y.property
    have hi : i ∈ y.val := by rw [hs]; simp
    have hsep' := (carriers_lemma hn hQ hS).neighbor_visits_separated y hN ⟨y, ⟨i, hi⟩⟩ rfl
    exact hsep' ((hy.2 ⟨y, ⟨i, hi⟩⟩ rfl).trans (hy.2 (visitTwin ⟨y, ⟨i, hi⟩⟩) rfl).symm)
  exact hsplit.x_split y hyx (fun hI => hnot _ (interlaces_symm hn hQ hI) h.pivot_mem)
    (fun hI => hnot _ hI h.pivot_mem)

/-- **`m_Q` of a carrier corresponding to a carrier of `λ₁`**: its crossings are exactly the carried
crossings of the half carrier, so the counts agree (eq. s7c:sliding-residual for the self-crossings;
the input to the coefficient transport of U110-D and to the slot `d_Q`). -/
theorem carrierCrossings_eq_img_first
    (h : s7r_SlidingTransport' hn hQ hsep hm hQC h₁ h₂ S S₁ S₂ va)
    (hsplit : s7b_PivotSplit (Interlaces hn hQ) (Interlaces (contactHalfSizes_bounds hn hsep).1.1 h₁)
      (Interlaces (contactHalfSizes_bounds hn hsep).2.1 h₂) (s7b_firstCrossingQ hn hsep hm hQC)
      (s7b_secondCrossingQ hn hsep hm hQC) va.1)
    (hS : IsDecomposition hn hQ S) (q : Component hn hQ S)
    (q₁ : Component (contactHalfSizes_bounds hn hsep).1.1 h₁ S₁) (hq : h.componentEquiv q = Sum.inl q₁) :
    carrierCrossings hn hQ S q =
      s7b_img (s7b_firstCrossingQ_injective hn hsep hm hQC)
        (carrierCrossings (contactHalfSizes_bounds hn hsep).1.1 h₁ S₁ q₁) := by
  ext y
  rw [s7b_mem_img]
  constructor
  · intro hy
    rcases h.carrierCrossings_mem_range hsplit hS q hy with ⟨c, rfl⟩ | ⟨c, rfl⟩
    · exact ⟨c, (h.firstCrossingQ_mem_carrierCrossings_iff c q q₁ hq).mp hy, rfl⟩
    · exact absurd hy (h.secondCrossingQ_notMem_carrierCrossings c q q₁ hq)
  · rintro ⟨c, hc, rfl⟩
    exact (h.firstCrossingQ_mem_carrierCrossings_iff c q q₁ hq).mpr hc

theorem carrierCrossings_eq_img_second
    (h : s7r_SlidingTransport' hn hQ hsep hm hQC h₁ h₂ S S₁ S₂ va)
    (hsplit : s7b_PivotSplit (Interlaces hn hQ) (Interlaces (contactHalfSizes_bounds hn hsep).1.1 h₁)
      (Interlaces (contactHalfSizes_bounds hn hsep).2.1 h₂) (s7b_firstCrossingQ hn hsep hm hQC)
      (s7b_secondCrossingQ hn hsep hm hQC) va.1)
    (hS : IsDecomposition hn hQ S) (q : Component hn hQ S)
    (q₂ : Component (contactHalfSizes_bounds hn hsep).2.1 h₂ S₂) (hq : h.componentEquiv q = Sum.inr q₂) :
    carrierCrossings hn hQ S q =
      s7b_img (s7b_secondCrossingQ_injective hn hsep hm hQC)
        (carrierCrossings (contactHalfSizes_bounds hn hsep).2.1 h₂ S₂ q₂) := by
  ext y
  rw [s7b_mem_img]
  constructor
  · intro hy
    rcases h.carrierCrossings_mem_range hsplit hS q hy with ⟨c, rfl⟩ | ⟨c, rfl⟩
    · exact absurd hy (h.firstCrossingQ_notMem_carrierCrossings c q q₂ hq)
    · exact ⟨c, (h.secondCrossingQ_mem_carrierCrossings_iff c q q₂ hq).mp hy, rfl⟩
  · rintro ⟨c, hc, rfl⟩
    exact (h.secondCrossingQ_mem_carrierCrossings_iff c q q₂ hq).mpr hc

theorem carrierCrossingCount_eq_first
    (h : s7r_SlidingTransport' hn hQ hsep hm hQC h₁ h₂ S S₁ S₂ va)
    (hsplit : s7b_PivotSplit (Interlaces hn hQ) (Interlaces (contactHalfSizes_bounds hn hsep).1.1 h₁)
      (Interlaces (contactHalfSizes_bounds hn hsep).2.1 h₂) (s7b_firstCrossingQ hn hsep hm hQC)
      (s7b_secondCrossingQ hn hsep hm hQC) va.1)
    (hS : IsDecomposition hn hQ S) (q : Component hn hQ S)
    (q₁ : Component (contactHalfSizes_bounds hn hsep).1.1 h₁ S₁) (hq : h.componentEquiv q = Sum.inl q₁) :
    carrierCrossingCount hn hQ S q =
      carrierCrossingCount (contactHalfSizes_bounds hn hsep).1.1 h₁ S₁ q₁ := by
  unfold carrierCrossingCount
  rw [h.carrierCrossings_eq_img_first hsplit hS q q₁ hq, s7b_img, Finset.card_map]

theorem carrierCrossingCount_eq_second
    (h : s7r_SlidingTransport' hn hQ hsep hm hQC h₁ h₂ S S₁ S₂ va)
    (hsplit : s7b_PivotSplit (Interlaces hn hQ) (Interlaces (contactHalfSizes_bounds hn hsep).1.1 h₁)
      (Interlaces (contactHalfSizes_bounds hn hsep).2.1 h₂) (s7b_firstCrossingQ hn hsep hm hQC)
      (s7b_secondCrossingQ hn hsep hm hQC) va.1)
    (hS : IsDecomposition hn hQ S) (q : Component hn hQ S)
    (q₂ : Component (contactHalfSizes_bounds hn hsep).2.1 h₂ S₂) (hq : h.componentEquiv q = Sum.inr q₂) :
    carrierCrossingCount hn hQ S q =
      carrierCrossingCount (contactHalfSizes_bounds hn hsep).2.1 h₂ S₂ q₂ := by
  unfold carrierCrossingCount
  rw [h.carrierCrossings_eq_img_second hsplit hS q q₂ hq, s7b_img, Finset.card_map]

end s7r_SlidingTransport'

end S7RTransportConsequences

section S7RGerm

/-! ##### Instantiation at a sliding wall germ: the local data of lem:wall-sides (V) supplies every
hypothesis of `s7r_slidingTransport_of_leg_false` below the interval radius. -/

variable (hn : 3 ≤ n) (g : WallGerm n) {M a : ZMod n} {r η δ : ℝ}

/-- **Sign constancy between a side and the centre**: the `u = 0` case of `s7a2_pos_of_ne_zero`
(W2_S7E_REPORT §2: "sign constancy on the interval replaces the approach clause"). -/
theorem s7r_sign_const_center (h : g.SlidingAt M a) (hloc : s7a2_IntervalLocal hn g M a r η δ)
    (hη : 0 < η) (t : g.SideParameter) (ht : t.val < δ) (b : Bool) (j : ZMod n)
    (hc : IsCrossing g.center {a, j}) (hnot : ¬ ContactAffected M a {a, j}) :
    edgeParameter (g.curve (g.sideTime b t)) a j < r ↔ edgeParameter g.center a j < r := by
  have hcont : ∀ u : g.Parameter, |u.val| < δ →
      ContinuousAt (fun w : g.Parameter => edgeParameter (g.curve w) a j - r) u :=
    fun u hu => (s7a2_continuousAt_edgeParameter hn g h.1 hloc hu hc hnot).sub continuousAt_const
  have hne : ∀ u : g.Parameter, |u.val| < δ → edgeParameter (g.curve u) a j - r ≠ 0 := by
    intro u hu h0
    have hcr : IsCrossing (g.curve u) {a, j} := (s7a2_crossing_iff hn g hloc hu {a, j} hnot).mpr hc
    have hw := (hloc u hu).windows.2.1 none j hcr hnot
    simp only [contactWindowEdge, contactWindowCenter] at hw
    rw [h0, abs_zero] at hw
    linarith
  have hcont' : ∀ u : g.Parameter, |u.val| < δ →
      ContinuousAt (fun w : g.Parameter => -(edgeParameter (g.curve w) a j - r)) u :=
    fun u hu => (hcont u hu).neg
  have hne' : ∀ u : g.Parameter, |u.val| < δ → -(edgeParameter (g.curve u) a j - r) ≠ 0 :=
    fun u hu => neg_ne_zero.mpr (hne u hu)
  have hlt : |(g.sideTime b t).val| < δ := by rw [g.sideTime_val_abs]; exact ht
  have h0 : (g.zeroParameter).val = 0 := rfl
  have h0abs : |(g.zeroParameter).val| ≤ t.val := by rw [h0, abs_zero]; exact t.property.1.le
  have hcenter : g.center = g.curve g.zeroParameter := rfl
  constructor
  · intro h1
    by_contra h2
    have hpos : 0 < -(edgeParameter (g.curve (g.sideTime b t)) a j - r) := by linarith
    have := s7a2_pos_of_ne_zero g ht hcont' hne' b hpos g.zeroParameter h0abs
    rw [← hcenter] at this
    linarith
  · intro h1
    by_contra h2
    have hpos : 0 < edgeParameter (g.curve (g.sideTime b t)) a j - r :=
      lt_of_le_of_ne (by linarith) (hne _ hlt).symm
    have := s7a2_pos_of_ne_zero g ht hcont hne b hpos g.zeroParameter h0abs
    rw [← hcenter] at this
    linarith

/-- The side-of-`r` law on edge `a` for a side, relative to the centre. -/
theorem s7r_hside (h : g.SlidingAt M a) (hloc : s7a2_IntervalLocal hn g M a r η δ) (hη : 0 < η)
    (t : g.SideParameter) (ht : t.val < δ) (b : Bool) :
    ∀ (u : Visit g.center) (hu : ¬ ContactAffected M a u.1.val), u.2.val = a →
      (visitParameter (s7a_visit (s7e_hQC hn g h t b) u hu) < r ↔ visitParameter u < r) := by
  intro u hu he
  obtain ⟨j, -, hj⟩ := crossing_support_partner u.1 u.2.val u.2.property
  have hz : pointZeroTriples g.center = {contactSupport M a} := h.1.2.1
  have h1 : visitParameter u = edgeParameter g.center a j := by
    rw [contact_visitParameter_eq_of_support_pair hn h.1.1 hz u hu j hj, he]
  have h2 : visitParameter (s7a_visit (s7e_hQC hn g h t b) u hu) =
      edgeParameter (g.curve (g.sideTime b t)) a j := by
    rw [visitParameter_eq_of_support_pair hn (s7a_sideGeneric g b).1 (s7a_visit (s7e_hQC hn g h t b) u hu) j hj,
      s7a_visit_edge, he]
  have hj' : u.1.val = {a, j} := by rw [hj, he]
  have hnot : ¬ ContactAffected M a {a, j} := by rw [← hj']; exact hu
  have hc : IsCrossing g.center {a, j} := by rw [← hj']; exact u.1.property
  rw [h1, h2]
  exact s7r_sign_const_center hn g h hloc hη t ht b j hc hnot

/-- The same-edge order law for a side, relative to the centre (`VertexLocalData.visit_order`). -/
theorem s7r_hord (h : g.SlidingAt M a) (hloc : s7a2_IntervalLocal hn g M a r η δ)
    (t : g.SideParameter) (ht : t.val < δ) (b : Bool) :
    ∀ (u u' : Visit g.center) (hu : ¬ ContactAffected M a u.1.val) (hu' : ¬ ContactAffected M a u'.1.val),
      u.2.val = u'.2.val →
      (visitParameter (s7a_visit (s7e_hQC hn g h t b) u hu) <
          visitParameter (s7a_visit (s7e_hQC hn g h t b) u' hu') ↔
        visitParameter u < visitParameter u') :=
  fun u u' hu hu' he =>
    (hloc (g.sideTime b t) (by rw [g.sideTime_val_abs]; exact ht)).visit_order (s7a_sideGeneric g b).1
      ⟨u, hu⟩ ⟨u', hu'⟩ he

include hn in
/-- On a side carrying `{a, M − 1}`, that is the only contact-affected crossing (the sliding pattern). -/
theorem s7r_huniq (h : g.SlidingAt M a) (t : g.SideParameter) (b : Bool)
    (hc : IsCrossing (g.curve (g.sideTime b t)) {a, contactLeg false M}) :
    ∀ y : Crossing (g.curve (g.sideTime b t)), ContactAffected M a y.val → y.val = {a, contactLeg false M} := by
  intro y hy
  obtain ⟨f', hf'⟩ := (contactAffected_iff_leg _).mp hy
  cases f'
  · exact hf'
  · exfalso
    have hp := s7e_pattern hn h t
    have hy' : IsCrossing (g.curve (g.sideTime b t)) {a, contactLeg true M} := hf' ▸ y.property
    cases b <;> cases hl : s7e_leg g M a <;> simp only [hl, Bool.not_true, Bool.not_false] at hp
    · exact hp.2.1 hy'
    · exact hp.2.1 hc
    · exact hp.2.2.2 hc
    · exact hp.2.2.2 hy'

/-- **The sliding transport instances below a radius** (U_S7B §2.1, the `s7b_SlidingTransport.ret`
deliverable): on any side `b` of a sliding wall carrying the contact crossing `{a, M − 1}` (so
`b = false` when `s7e_leg g M a = false`, `b = true` when it is `true`), every sliding row `S ∋ x`
whose other crossings are carried from the halves is a `s7b_SlidingTransport` at the leg visit; hence
`componentEquiv`, `carrierCrossings_eq_img_first/_second`, `carrierCrossingCount_eq_*` apply (with
`hSimg` from `s7r_img_of_decomposition` on a decomposition and the pivot split).  The OTHER side
(leg `M`) is `s7r_slidingTransport_of_leg_true` (black box, corrected mark map). -/
theorem s7r_slidingTransport_side (h : g.SlidingAt M a) (h₁ : Generic (firstHalf g.center M a))
    (h₂ : Generic (secondHalf g.center M a)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : g.SideParameter, t.val < δ → ∀ b : Bool,
      ∀ (hc : IsCrossing (g.curve (g.sideTime b t)) {a, contactLeg false M})
        (S : Finset (Crossing (g.curve (g.sideTime b t)))), (s7e_va hc).1 ∈ S →
        (∀ y ∈ S, y ≠ (s7e_va hc).1 →
          y ∈ Set.range (s7b_firstCrossingQ hn h.1.1 h.1.2.2.2.1 (s7e_hQC hn g h t b)) ∪
            Set.range (s7b_secondCrossingQ hn h.1.1 h.1.2.2.2.1 (s7e_hQC hn g h t b))) →
        s7b_SlidingTransport hn h.1.1 h.1.2.2.2.1 (s7e_hQC hn g h t b) (s7a_sideGeneric g b) h₁ h₂ S
          (s7b_pre (s7b_firstCrossingQ hn h.1.1 h.1.2.2.2.1 (s7e_hQC hn g h t b)) S)
          (s7b_pre (s7b_secondCrossingQ hn h.1.1 h.1.2.2.2.1 (s7e_hQC hn g h t b)) S) (s7e_vl hc) := by
  obtain ⟨r, η, hr0, hr1, hr, hη, -, -, δ, hδ, -, hloc⟩ := s7a2_exists_intervalLocal hn g M a h.1
  refine ⟨δ, hδ, fun t ht b hc S hxS hSimg => ?_⟩
  have hz : pointZeroTriples g.center = {contactSupport M a} := h.1.2.1
  exact s7r_slidingTransport_of_leg_false hn (s7a_sideGeneric g b) h.1.1 hz h.1.2.2.2.1 hr hr0 hr1 hη
    (s7e_hQC hn g h t b) (s7e_hw hn g hloc t ht b) (s7r_hord hn g h hloc t ht b)
    (s7r_hside hn g h hloc hη t ht b) h₁ h₂ hc (s7r_huniq hn g h t b hc) S hxS hSimg


include hn in
/-- On a side carrying `{a, M}`, that is the only contact-affected crossing (the sliding pattern). -/
theorem s7r_huniq' (h : g.SlidingAt M a) (t : g.SideParameter) (b : Bool)
    (hc : IsCrossing (g.curve (g.sideTime b t)) {a, contactLeg true M}) :
    ∀ y : Crossing (g.curve (g.sideTime b t)), ContactAffected M a y.val → y.val = {a, contactLeg true M} := by
  intro y hy
  obtain ⟨f', hf'⟩ := (contactAffected_iff_leg _).mp hy
  cases f'
  · exfalso
    have hp := s7e_pattern hn h t
    have hy' : IsCrossing (g.curve (g.sideTime b t)) {a, contactLeg false M} := hf' ▸ y.property
    cases b <;> cases hl : s7e_leg g M a <;> simp only [hl, Bool.not_true, Bool.not_false] at hp
    · exact hp.2.1 hc
    · exact hp.2.1 hy'
    · exact hp.2.2.2 hy'
    · exact hp.2.2.2 hc
  · exact hf'

/-- **The sliding transport instances below a radius on the leg-`M` side** (the corrected structure
`s7r_SlidingTransport'`; the side `b = true` when `s7e_leg g M a = false`, `b = false` when it is `true`). -/
theorem s7r_slidingTransport_side' (h : g.SlidingAt M a) (h₁ : Generic (firstHalf g.center M a))
    (h₂ : Generic (secondHalf g.center M a)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : g.SideParameter, t.val < δ → ∀ b : Bool,
      ∀ (hc : IsCrossing (g.curve (g.sideTime b t)) {a, contactLeg true M})
        (S : Finset (Crossing (g.curve (g.sideTime b t)))), (s7e_va hc).1 ∈ S →
        (∀ y ∈ S, y ≠ (s7e_va hc).1 →
          y ∈ Set.range (s7b_firstCrossingQ hn h.1.1 h.1.2.2.2.1 (s7e_hQC hn g h t b)) ∪
            Set.range (s7b_secondCrossingQ hn h.1.1 h.1.2.2.2.1 (s7e_hQC hn g h t b))) →
        s7r_SlidingTransport' hn (s7a_sideGeneric g b) h.1.1 h.1.2.2.2.1 (s7e_hQC hn g h t b) h₁ h₂ S
          (s7b_pre (s7b_firstCrossingQ hn h.1.1 h.1.2.2.2.1 (s7e_hQC hn g h t b)) S)
          (s7b_pre (s7b_secondCrossingQ hn h.1.1 h.1.2.2.2.1 (s7e_hQC hn g h t b)) S) (s7e_va hc) := by
  obtain ⟨r, η, hr0, hr1, hr, hη, -, -, δ, hδ, -, hloc⟩ := s7a2_exists_intervalLocal hn g M a h.1
  refine ⟨δ, hδ, fun t ht b hc S hxS hSimg => ?_⟩
  have hz : pointZeroTriples g.center = {contactSupport M a} := h.1.2.1
  exact s7r_slidingTransport_of_leg_true hn (s7a_sideGeneric g b) h.1.1 hz h.1.2.2.2.1 hr hr0 hr1 hη
    (s7e_hQC hn g h t b) (s7e_hw hn g hloc t ht b) (s7r_hord hn g h hloc t ht b)
    (s7r_hside hn g h hloc hη t ht b) h₁ h₂ hc (s7r_huniq' hn g h t b hc) S hxS hSimg

end S7RGerm


/-- The sliding branch (sm-4:300-406): relocation bijection `φ(x₋) = x₊`, the support bijection
eq. s7c:sliding-bijection with the halves, equal coefficient products eq. s7c:sliding-coefficients, and
the exact selector difference eq. s7c:sliding-selector-difference.  NO floor, NO singleton. -/
theorem s7_sliding_law_at (hn : 3 ≤ n) (g : WallGerm n) (M a : ZMod n) (h : g.SlidingAt M a)
    (h₁ : Generic (firstHalf g.center M a)) (h₂ : Generic (secondHalf g.center M a)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : g.SideParameter, t.val < δ →
      cornerStateSum hn (g.sideTuple true t).property -
          cornerStateSum hn (g.sideTuple false t).property =
        (g.contactSign M a : ℤ) *
          (cornerStateSum (contactHalfSizes_bounds hn h.1.1).1.1 h₁ *
            cornerStateSum (contactHalfSizes_bounds hn h.1.1).2.1 h₂) := by
  sorry


/-- The bigon branch (sm-4:407-874): two-newborn sector `B = (1−ε)J` (contact triangle: a crossing-free
uniform carrier, `corner_values_i`), universal skein extraction eq. s7c:universal-extraction (lp:core
skein, R-II deletion, oriented smoothing), lem:homflyrows two-component row, the rotation ledger, and the
two floor-dependent branches (interlacing: `Ω_H − Ω_L = −ω₁ω₂`; noninterlacing: every returned row zero,
the one-newborn rows by cb:singleton).  `a_floor` enters at the two half contact carriers (uniform for
`ε = 1`, one-dissent for `ε = 0`), read as carriers of the decompositions `T_i` of the generic halves
`λ_i` (sm-4:800-835); cb:singleton enters at the one-newborn rows (sm-4:777-783) — both printed
dependencies are explicit parameters. -/
theorem s7_bigon_law_at (hF : FloorTheoremData) (hsing : CbSingletonData) (hn : 3 ≤ n)
    (g : WallGerm n) (M a : ZMod n) (h : g.BigonAt M a)
    (h₁ : Generic (firstHalf g.center M a)) (h₂ : Generic (secondHalf g.center M a)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : g.SideParameter, t.val < δ →
      cornerStateSum hn (g.sideTuple true t).property -
          cornerStateSum hn (g.sideTuple false t).property =
        (g.contactSign M a : ℤ) *
          (cornerStateSum (contactHalfSizes_bounds hn h.1.1).1.1 h₁ *
            cornerStateSum (contactHalfSizes_bounds hn h.1.1).2.1 h₂) := by
  sorry


end VertexEdge

/-- **Row 110, conditional on thm:floor AND cb:singleton** (the printed dependency list of
tools/claims.py; library material).  PROVED from the two branch leaves: the wall is of bigon or sliding
type (`vertexEdge_bigon_or_sliding`); both side parameters are moved below the branch radius by chamber
constancy along each side (`cornerStateSum_side_eq`). -/
theorem thm_C_S7_of (hF : FloorTheoremData) (hsing : CbSingletonData) : CS7Data := by
  refine ⟨?_⟩
  intro n _ hn g M a h h₁ h₂ tp tm
  obtain ⟨δ, hδ, hlaw⟩ : ∃ δ : ℝ, 0 < δ ∧ ∀ t : g.SideParameter, t.val < δ →
      cornerStateSum hn (g.sideTuple true t).property -
          cornerStateSum hn (g.sideTuple false t).property =
        (g.contactSign M a : ℤ) *
          (cornerStateSum (contactHalfSizes_bounds hn h.1).1.1 h₁ *
            cornerStateSum (contactHalfSizes_bounds hn h.1).2.1 h₂) := by
    rcases g.vertexEdge_bigon_or_sliding h with hb | hs
    · exact s7_bigon_law_at hF hsing hn g M a hb h₁ h₂
    · exact s7_sliding_law_at hn g M a hs h₁ h₂
  have hr := g.radius_pos
  let t : g.SideParameter := ⟨min δ g.radius / 2, by
    constructor
    · have := lt_min hδ hr; linarith
    · have := min_le_right δ g.radius; linarith⟩
  have ht : t.val < δ := by
    show min δ g.radius / 2 < δ
    have := min_le_left δ g.radius; linarith
  rw [cornerStateSum_side_eq hn g true tp t, cornerStateSum_side_eq hn g false tm t]
  exact hlaw t ht

/-- **Row 110, conditional on the floor alone** (the row theorem `SM.thm_C_S7 := thm_C_S7_of_floor
SM.thm_floor` once row 100 lands). -/
theorem thm_C_S7_of_floor (hF : FloorTheoremData) : CS7Data :=
  thm_C_S7_of hF (cb_singleton_of_floor hF)


/-- Row 110 thm:C-S7 (FIXED target name, axiom-policy.json): the assembly on thm:floor (row 100). -/
theorem thm_C_S7 : CS7Data := thm_C_S7_of_floor thm_floor

end

end SM
