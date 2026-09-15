import SM.ContactVertices
import SM.ContactApproach
import Mathlib.Data.Finset.Max

/-! One strictly positive gap for every persistent crossing on the three
contact edges. The finite minimum includes a sentinel, so empty crossing
universes are covered. Slots name the actual base and the two actual legs. -/

namespace SM

variable {n : ℕ} [NeZero n] {P : LabelledTuple n} {M a : ZMod n}

def contactWindowEdge (M a : ZMod n) : Option Bool → ZMod n
  | none => a
  | some forward => contactLeg forward M

def contactWindowCenter (r : ℝ) : Option Bool → ℝ
  | none => r
  | some forward => contactEndpoint forward

theorem finite_positive_lower_bound {α : Type*} [Fintype α]
    (f : α → ℝ) (hf : ∀ x, 0 < f x) : ∃ d : ℝ, 0 < d ∧ ∀ x, d ≤ f x := by
  classical
  let s : Finset ℝ := insert 1 (Finset.univ.image f)
  have hs : s.Nonempty := ⟨1, Finset.mem_insert_self _ _⟩
  refine ⟨s.min' hs, ?_, ?_⟩
  · apply (Finset.lt_min'_iff s hs).mpr
    intro y hy
    rcases Finset.mem_insert.mp hy with rfl | hy
    · norm_num
    · obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hy
      exact hf x
  · intro x
    exact s.min'_le (f x) (Finset.mem_insert_of_mem
      (Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩))

theorem contact_window_parameter_ne (hn : 3 ≤ n) (hsep : ContactSeparated M a)
    (hz : pointZeroTriples P = {contactSupport M a})
    (r : ℝ) (hr : P M = edgePoint P a r) (slot : Option Bool) (j : ZMod n)
    (hc : IsCrossing P {contactWindowEdge M a slot, j})
    (hnc : ¬ ContactAffected M a {contactWindowEdge M a slot, j}) :
    edgeParameter P (contactWindowEdge M a slot) j ≠ contactWindowCenter r slot := by
  cases slot with
  | none => exact contact_parameter_ne_contact hn hsep hz hc hnc r hr
  | some forward =>
    have hd := (contact_pair_data hn hsep hz hc hnc).parameter_interior
    cases forward
    · exact hd.2.ne
    · exact hd.1.ne'

theorem contact_window_gap (hn : 3 ≤ n) (hsep : ContactSeparated M a)
    (hz : pointZeroTriples P = {contactSupport M a})
    (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) (hr : P M = edgePoint P a r) :
    ∃ η : ℝ, 0 < η ∧ 4 * η < r ∧ 4 * η < 1 - r ∧
      ∀ slot : Option Bool, ∀ j : ZMod n,
        IsCrossing P {contactWindowEdge M a slot, j} →
        ¬ ContactAffected M a {contactWindowEdge M a slot, j} →
        4 * η < |edgeParameter P (contactWindowEdge M a slot) j - contactWindowCenter r slot| := by
  classical
  let f : Option Bool × ZMod n → ℝ := fun x =>
    if IsCrossing P {contactWindowEdge M a x.1, x.2} ∧
        ¬ ContactAffected M a {contactWindowEdge M a x.1, x.2}
    then |edgeParameter P (contactWindowEdge M a x.1) x.2 - contactWindowCenter r x.1|
    else 1
  have hf : ∀ x, 0 < f x := by
    intro x
    dsimp [f]
    split_ifs with h
    · exact abs_pos.mpr (sub_ne_zero.mpr (contact_window_parameter_ne hn hsep hz r hr x.1 x.2 h.1 h.2))
    · norm_num
  obtain ⟨d, hd, hdf⟩ := finite_positive_lower_bound f hf
  let b := min r (min (1 - r) d)
  have hb : 0 < b := lt_min hr0 (lt_min (sub_pos.mpr hr1) hd)
  have hbr : b ≤ r := min_le_left _ _
  have hbr1 : b ≤ 1 - r := (min_le_right _ _).trans (min_le_left _ _)
  have hbd : b ≤ d := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨b / 8, by positivity, by linarith, by linarith, ?_⟩
  intro slot j hc hnc
  have hfval := hdf (slot, j)
  simp only [f, if_pos (And.intro hc hnc)] at hfval
  linarith

end SM
