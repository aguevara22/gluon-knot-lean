import SM.PrincipalAngles
import SM.G1Consequences

/-! The actual regular locus and principal turns of labelled polygons.
The inherited labelled formalization is accompanied by cyclic equivariance.
Positive collinear consecutive edges are retained in the regular domain. -/

namespace SM

variable {n : ℕ}

def Regular (P : LabelledTuple n) : Prop :=
  ∀ i, RegularPair (edge P (i - 1)) (edge P i)

noncomputable def principalTurn (P : LabelledTuple n) (i : ZMod n) : ℝ :=
  principalAngle (edge P (i - 1)) (edge P i)

theorem regular_iff_edges (P : LabelledTuple n) : Regular P ↔
    ∀ i, edge P i ≠ 0 ∧ ¬ ∃ r : ℝ, r < 0 ∧ edge P i = r • edge P (i - 1) := by
  constructor
  · intro h i
    exact ⟨(h i).2.1, (h i).2.2⟩
  · intro h i
    exact ⟨(h (i - 1)).1, (h i).1, (h i).2⟩

theorem regular_iff_principalTurns_exist (P : LabelledTuple n) : Regular P ↔
    ∀ i, ∃! θ, PrincipalAngleSpec (edge P (i - 1)) (edge P i) θ := by
  exact forall_congr' (fun _ => (principalAngle_existsUnique_iff _ _).symm)

theorem g1_regular (hn : 3 ≤ n) {P : LabelledTuple n} (h : G1 P) : Regular P := by
  have hg := g1 hn P h
  apply (regular_iff_edges P).mpr
  intro i
  refine ⟨hg.2.1 i, ?_⟩
  rintro ⟨r, _, hr⟩
  exact hg.2.2.2.2.1 i r hr

theorem generic_regular (hn : 3 ≤ n) {P : LabelledTuple n} (h : Generic P) :
    Regular P := g1_regular hn h.1

theorem principalTurn_spec {P : LabelledTuple n} {i : ZMod n}
    (h : RegularPair (edge P (i - 1)) (edge P i)) :
    PrincipalAngleSpec (edge P (i - 1)) (edge P i) (principalTurn P i) :=
  principalAngle_spec h

theorem principalTurn_unique {P : LabelledTuple n} {i : ZMod n} {θ : ℝ}
    (h : PrincipalAngleSpec (edge P (i - 1)) (edge P i) θ) :
    θ = principalTurn P i :=
  principalAngleSpec_unique h (principalTurn_spec (regularPair_of_principalAngleSpec h))

theorem principalTurn_eq_zero_iff {P : LabelledTuple n} {i : ZMod n}
    (h : RegularPair (edge P (i - 1)) (edge P i)) :
    principalTurn P i = 0 ↔ ∃ r : ℝ, 0 < r ∧ edge P i = r • edge P (i - 1) :=
  principalAngle_eq_zero_iff h.1 h.2.1

theorem regular_shift_forward (a : ZMod n) {P : LabelledTuple n} (h : Regular P) :
    Regular (shift a P) := by
  intro i
  simpa only [edge_shift, sub_add_eq_add_sub] using h (i + a)

theorem regular_shift (a : ZMod n) (P : LabelledTuple n) :
    Regular (shift a P) ↔ Regular P := by
  constructor
  · intro h
    simpa only [shift_add, neg_add_cancel, shift_zero] using regular_shift_forward (-a) h
  · exact regular_shift_forward a

theorem principalTurn_shift (a : ZMod n) (P : LabelledTuple n) (i : ZMod n) :
    principalTurn (shift a P) i = principalTurn P (i + a) := by
  simp only [principalTurn, edge_shift, sub_add_eq_add_sub]

end SM
