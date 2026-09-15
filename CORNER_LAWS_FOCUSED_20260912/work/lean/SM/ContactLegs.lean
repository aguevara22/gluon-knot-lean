import SM.ContactCenter
import SM.ContactLine

/-! Both actual incident legs of a vertex contact, in the source tail indexing.
The base segment's second strict separation test holds at the centre. -/

namespace SM

variable {n : ℕ} [NeZero n] {P : LabelledTuple n} {M a : ZMod n}

def contactLeg (forward : Bool) (M : ZMod n) : ZMod n := if forward then M else M - 1

def contactNeighbour (forward : Bool) (M : ZMod n) : ZMod n :=
  if forward then M + 1 else M - 1

theorem contactLeg_remote (h : ContactSeparated M a) (forward : Bool) :
    remote a (contactLeg forward M) := by
  intro hadj
  cases forward
  · change (M - 1) - a = -1 ∨ (M - 1) - a = 0 ∨ (M - 1) - a = 1 at hadj
    rcases hadj with he | he | he
    · exact h.2.1 (by linear_combination he)
    · exact h.2.2.1 (by linear_combination he)
    · exact h.2.2.2 (by linear_combination he)
  · change M - a = -1 ∨ M - a = 0 ∨ M - a = 1 at hadj
    rcases hadj with he | he | he
    · exact h.1 (by linear_combination he)
    · exact h.2.1 (by linear_combination he)
    · exact h.2.2.1 (by linear_combination he)

theorem contactNeighbour_distinct (hn : 3 ≤ n) (h : ContactSeparated M a) (forward : Bool) :
    contactNeighbour forward M ≠ a ∧ contactNeighbour forward M ≠ a + 1 ∧
    contactNeighbour forward M ≠ M := by
  letI : Fact (1 < n) := ⟨by omega⟩
  cases forward
  · refine ⟨?_, ?_, prev_ne_self M⟩
    · intro he
      exact h.2.2.1 (by change M - 1 = a at he; linear_combination he)
    · intro he
      exact h.2.2.2 (by change M - 1 = a + 1 at he; linear_combination he)
  · refine ⟨?_, ?_, next_ne_self M⟩
    · intro he
      exact h.1 (by change M + 1 = a at he; linear_combination he)
    · intro he
      exact h.2.1 (by change M + 1 = a + 1 at he; linear_combination he)

theorem contactNeighbour_chi_nonzero (hn : 3 ≤ n) (hsep : ContactSeparated M a)
    (hz : pointZeroTriples P = {contactSupport M a}) (forward : Bool) :
    chi P a (a + 1) (contactNeighbour forward M) ≠ 0 := by
  letI : Fact (1 < n) := ⟨by omega⟩
  have hd := contactNeighbour_distinct hn hsep forward
  apply chi_nonzero_outside_singleton hz (next_ne_self a).symm hd.2.1.symm hd.1.symm
  intro he
  exact hd.2.2 (contactSupport_vertex_edge hn hsep hd.1 hd.2.1 he).2

theorem contactNeighbour_height_nonzero (hn : 3 ≤ n) (hsep : ContactSeparated M a)
    (hz : pointZeroTriples P = {contactSupport M a}) (forward : Bool) :
    contactHeight (P a) (P (a + 1)) (P (contactNeighbour forward M)) ≠ 0 := by
  have h := contactNeighbour_chi_nonzero hn hsep hz forward
  exact sign_ne_zero.mp h

theorem contact_strictBetween (hn : 3 ≤ n) (hsep : ContactSeparated M a)
    (hz : pointZeroTriples P = {contactSupport M a}) (hm : P M ∈ edgeInterior P a) :
    StrictBetween (P a) (P M) (P (a + 1)) := by
  have hn5 := contactSeparated_size hn hsep
  have hedge := singlePointTriple_edge_ne_zero (by omega) hz a
  refine ⟨(sub_ne_zero.mp hedge).symm, ?_⟩
  exact hm

noncomputable def baseLegSideProduct (P : LabelledTuple n) (a l : ZMod n) : ℝ :=
  det (edge P l) (P a - P l) * det (edge P l) (P (a + 1) - P l)

theorem contact_baseLegSideProduct_neg (hn : 3 ≤ n) (hsep : ContactSeparated M a)
    (hz : pointZeroTriples P = {contactSupport M a}) (hm : P M ∈ edgeInterior P a)
    (forward : Bool) : baseLegSideProduct P a (contactLeg forward M) < 0 := by
  have hb := contact_strictBetween hn hsep hz hm
  have hp := contact_base_separation hb (contactNeighbour_height_nonzero hn hsep hz forward)
  cases forward
  · have he := reverse_line_side_product (P a) (P (a + 1)) (P M) (P (M - 1))
    simpa only [baseLegSideProduct, contactLeg, Bool.false_eq_true, ↓reduceIte,
      edge, sub_add_cancel] using he.trans_lt hp
  · exact hp

end SM
