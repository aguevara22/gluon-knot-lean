import SM.FibreExistence

/-! Full source lem:fibres: exact existence on the complete integer parameter
domain and full Generic density in the actual labelled tuple space. The
integer-domain existence predicate uses the actual cyclic quotient and retains
the source's at-least-three-vertices restriction explicitly. -/

namespace SM

theorem genericFibre_nonempty_iff {n : ℕ} [NeZero n] (hn : 3 ≤ n) (r : ℤ) :
    (genericFibre (n := n) r).Nonempty ↔ Admissible (n : ℤ) r := by
  rw [← generic_rotation_exists_iff hn r]
  constructor
  · rintro ⟨Q, hQ⟩
    obtain ⟨P, rfl⟩ := Quotient.exists_rep Q
    exact ⟨P.val, P.property, hQ⟩
  · rintro ⟨P, hP, hr⟩
    exact ⟨polygonProjection ⟨P, hP⟩, hr⟩

def HasGenericPolygonRotation (n r : ℤ) : Prop :=
  ∃ m : ℕ, ∃ hm : NeZero m, 3 ≤ m ∧ (m : ℤ) = n ∧
    (@genericFibre m hm r).Nonempty

theorem hasGenericPolygonRotation_iff (n r : ℤ) :
    HasGenericPolygonRotation n r ↔ Admissible n r := by
  constructor
  · rintro ⟨m, hm, hm3, hmn, hP⟩
    letI : NeZero m := hm
    have ha := (genericFibre_nonempty_iff hm3 r).mp hP
    simpa only [hmn] using ha
  · intro ha
    let m := n.toNat
    have hmn : (m : ℤ) = n := Int.toNat_of_nonneg (by have := ha.1; omega)
    have hm3Z : (3 : ℤ) ≤ (m : ℤ) := by rw [hmn]; exact ha.1
    have hm3 : 3 ≤ m := by exact_mod_cast hm3Z
    letI : NeZero m := ⟨by omega⟩
    refine ⟨m, inferInstance, hm3, hmn, (genericFibre_nonempty_iff hm3 r).mpr ?_⟩
    simpa only [hmn] using ha

/-- Both printed clauses, including every integer parameter pair and every
nonempty open set of full labelled n-tuples. Existence uses actual polygons,
principal-turn rotation and the full G1/G2 genericity definition. -/
theorem nonempty_fibres :
    (∀ n r : ℤ, HasGenericPolygonRotation n r ↔
      3 ≤ n ∧ 2 * |r| < n ∧ (n, r) ≠ (3, 0)) ∧
    (∀ n : ℕ, 3 ≤ n → ∀ U : Set (LabelledTuple n), IsOpen U → U.Nonempty →
      ∃ P ∈ U, Generic P) := by
  refine ⟨hasGenericPolygonRotation_iff, ?_⟩
  intro n hn U hU hne
  exact generic_in_nonempty_open hn U hU hne

end SM
