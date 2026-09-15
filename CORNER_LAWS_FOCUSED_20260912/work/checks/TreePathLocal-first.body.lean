namespace SM

open Set Filter Topology
noncomputable section
variable {n : ℕ} [NeZero n]

/-- At an actual G1 tuple every chi value persists simultaneously; repeated
labels are proved zero separately, rather than included in the G1 premise. -/
theorem g1_all_chi_persists {P : LabelledTuple n} (hP : G1 P) :
    ∀ᶠ Q in 𝓝 P, ∀ i j k : ZMod n, chi Q i j k = chi P i j k := by
  filter_upwards [finite_nonzero_chi_persists (P := P)] with Q hQ
  intro i j k
  by_cases hij : i = j
  · subst j; simp
  by_cases hjk : j = k
  · subst k; simp
  by_cases hik : i = k
  · subst k; simp
  exact hQ i j k (hP i j k hij hjk hik)

/-- Generic path values have pairwise constancy in an actual open parameter
neighborhood of any G1 point, with every physical root retained. -/
theorem tree_path_pair_near_generic {X : Type*} [TopologicalSpace X]
    (p : X → LabelledTuple n) (hp : Continuous p) (x : X) (hxG : G1 (p x))
    (g : ZMod n) (hn : 3 ≤ n) :
    ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      ∀ a b : {t : X // Generic (p t)}, a.val ∈ U → b.val ∈ U →
        treeCoefficient (p a.val) a.property.1 g hn =
          treeCoefficient (p b.val) b.property.1 g hn := by
  have hnear := hp.continuousAt.eventually (g1_all_chi_persists hxG)
  obtain ⟨U, hsub, hU, hxU⟩ := mem_nhds_iff.mp hnear
  refine ⟨U, hU, hxU, ?_⟩
  intro a b ha hb
  apply treeCoefficient_eq_of_chi a.property.1 b.property.1
  intro i j k
  exact (hsub ha i j k).trans (hsub hb i j k).symm

/-- Actual generic side constancy, with the same physical root. -/
theorem WallGerm.tree_coefficient_same_side (w : WallGerm n)
    (g : ZMod n) (hn : 3 ≤ n) (b : Bool) (s t : w.SideParameter) :
    treeCoefficient (w.sideTuple b s).val (w.sideTuple b s).property.1 g hn =
      treeCoefficient (w.sideTuple b t).val (w.sideTuple b t).property.1 g hn :=
  treeCoefficient_eq_of_chi (w.sideTuple b s).property.1 (w.sideTuple b t).property.1
    (fun i j k => generic_family_chi_constant (w.continuous_sideTuple b) s t i j k) g hn

/-- A proved equality across the two full sides identifies any punctured
parameter value with the positive-side value. The cross-side premise is
explicit here and must be proved from the named wall in applications. -/
theorem WallGerm.tree_parameter_eq_positive_of_sides_equal (w : WallGerm n)
    (g : ZMod n) (hn : 3 ≤ n)
    (hsides : ∀ s t : w.SideParameter,
      treeCoefficient (w.sideTuple true t).val (w.sideTuple true t).property.1 g hn =
        treeCoefficient (w.sideTuple false s).val (w.sideTuple false s).property.1 g hn)
    (u : w.Parameter) (hu : u.val ≠ 0) (t : w.SideParameter) :
    treeCoefficient (w.curve u) (w.generic_punctured u hu).1 g hn =
      treeCoefficient (w.sideTuple true t).val (w.sideTuple true t).property.1 g hn := by
  by_cases hp : 0 < u.val
  · let q : w.SideParameter := ⟨u.val, hp, u.property.2⟩
    have he := w.tree_coefficient_same_side g hn true q t
    have htime : w.sideTime true q = u := Subtype.ext rfl
    have hval : (w.sideTuple true q).val = w.curve u := congrArg w.curve htime
    rw [hval] at he
    exact he
  · have hnz : u.val < 0 := lt_of_le_of_ne (le_of_not_gt hp) hu
    let q : w.SideParameter := ⟨-u.val, by constructor <;> linarith [u.property.1]⟩
    have he := (hsides q t).symm
    have htime : w.sideTime false q = u := by
      apply Subtype.ext
      change -(-u.val) = u.val
      ring
    have hval : (w.sideTuple false q).val = w.curve u := congrArg w.curve htime
    rw [hval] at he
    exact he

end
end SM
