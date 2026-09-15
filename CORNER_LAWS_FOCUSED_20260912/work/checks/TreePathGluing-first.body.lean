namespace SM

open Set
noncomputable section
variable {n : ℕ} [NeZero n]

/-- Every actual silent wall has a common value at all punctured parameters.
The cross-side law is derived from the named E/C predicates here. -/
theorem WallGerm.silent_tree_parameter_value (w : WallGerm n)
    (g : ZMod n) (hn : 3 ≤ n) (hs : w.Silent)
    (u : w.Parameter) (hu : u.val ≠ 0) (t : w.SideParameter) :
    treeCoefficient (w.curve u) (w.generic_punctured u hu).1 g hn =
      treeCoefficient (w.sideTuple true t).val (w.sideTuple true t).property.1 g hn := by
  apply w.tree_parameter_eq_positive_of_sides_equal g hn ?_ u hu t
  intro a b
  rcases hs with ⟨M, e, he⟩ | ⟨i, j, k, hc⟩
  · exact w.extension_tree_silent M e hn he g a b
  · exact w.pure_cut_tree_silent i j k hn hc g a b

/-- The actual shifted silent germ gives pairwise equality of generic path
values in a full open parameter neighborhood of the event. -/
theorem tree_path_pair_near_silent_event (p : unitInterval → LabelledTuple n)
    (x : unitInterval) (w : WallGerm n) (hcenter : w.center = p x)
    (hcurve : ∀ s : w.Parameter, ∃ hs : (x : ℝ) + s.val ∈ Icc (0 : ℝ) 1,
      w.curve s = p ⟨(x : ℝ) + s.val, hs⟩)
    (hs : w.Silent) (g : ZMod n) (hn : 3 ≤ n) :
    ∃ U : Set unitInterval, IsOpen U ∧ x ∈ U ∧
      ∀ a b : {t : unitInterval // Generic (p t)}, a.val ∈ U → b.val ∈ U →
        treeCoefficient (p a.val) a.property.1 g hn =
          treeCoefficient (p b.val) b.property.1 g hn := by
  have hxNG : ¬ Generic (p x) := by rw [← hcenter]; exact w.nongeneric_center
  have hvalue : ∀ a : {t : unitInterval // Generic (p t)}, a.val ∈ Metric.ball x w.radius →
      treeCoefficient (p a.val) a.property.1 g hn =
        treeCoefficient (w.sideTuple true w.sideBase).val
          (w.sideTuple true w.sideBase).property.1 g hn := by
    intro a ha
    have hdist : |(a.val : ℝ) - (x : ℝ)| < w.radius := by
      simpa only [Metric.mem_ball, Subtype.dist_eq, Real.dist_eq] using ha
    let u : w.Parameter := ⟨(a.val : ℝ) - (x : ℝ), abs_lt.mp hdist⟩
    have hu : u.val ≠ 0 := by
      intro he
      have hax : a.val = x := Subtype.ext (sub_eq_zero.mp he)
      apply hxNG
      rw [← hax]
      exact a.property
    have he := w.silent_tree_parameter_value g hn hs u hu w.sideBase
    have hpath : w.curve u = p a.val := w.shifted_curve_eq_path p x hcurve a.val hdist
    have htuple : (⟨w.curve u, w.generic_punctured u hu⟩ : GenericTuple n) =
        ⟨p a.val, a.property⟩ := Subtype.ext hpath
    have hcoeff := congrArg (fun P : GenericTuple n => treeCoefficient P.val P.property.1 g hn) htuple
    exact hcoeff.symm.trans he
  refine ⟨Metric.ball x w.radius, Metric.isOpen_ball, Metric.mem_ball_self w.radius_pos, ?_⟩
  intro a b ha hb
  exact (hvalue a ha).trans (hvalue b hb).symm

/-- The generic values of an actual continuous path agree when every
nongeneric parameter has its actual shifted silent germ. Density and
local-pair constancy are proved, not supplied as abstract placeholders. -/
theorem tree_path_constant_of_silent_germs (p : unitInterval → LabelledTuple n)
    (hp : Continuous p)
    (hevent : ∀ x : unitInterval, ¬ Generic (p x) → ∃ w : WallGerm n,
      w.center = p x ∧
      (∀ s : w.Parameter, ∃ hs : (x : ℝ) + s.val ∈ Icc (0 : ℝ) 1,
        w.curve s = p ⟨(x : ℝ) + s.val, hs⟩) ∧ w.Silent)
    (g : ZMod n) (hn : 3 ≤ n)
    (a b : {t : unitInterval // Generic (p t)}) :
    treeCoefficient (p a.val) a.property.1 g hn =
      treeCoefficient (p b.val) b.property.1 g hn := by
  let S : Set unitInterval := {t | Generic (p t)}
  let f : S → ℤ := fun t => treeCoefficient (p t.val) t.property.1 g hn
  have hd : Dense S := generic_path_dense_of_germs p (by
    intro x hx
    obtain ⟨w, hc, hcurve, hs⟩ := hevent x hx
    exact ⟨w, hcurve⟩)
  have hlocal : ∀ x : unitInterval, ∃ U : Set unitInterval, IsOpen U ∧ x ∈ U ∧
      ∀ a b : S, a.val ∈ U → b.val ∈ U → f a = f b := by
    intro x
    by_cases hx : Generic (p x)
    · exact tree_path_pair_near_generic p hp x hx.1 g hn
    · obtain ⟨w, hc, hcurve, hs⟩ := hevent x hx
      exact tree_path_pair_near_silent_event p x w hc hcurve hs g hn
  exact dense_local_pairs_constant S hd f hlocal a b

/-- Any actual weak-locus path with generic endpoints preserves the rooted
coefficient. Relative general position, weak membership and E/C classification
are all derived, with no R, silent-response or path-certificate premise. -/
theorem tree_coefficient_eq_along_weak_path (hn : 3 ≤ n)
    (γ : unitInterval → LabelledTuple n) (hγ : Continuous γ)
    (hw : ∀ t, WeakGeneric (γ t)) (hfirst : Generic (γ 0)) (hlast : Generic (γ 1))
    (g : ZMod n) :
    treeCoefficient (γ 0) hfirst.1 g hn = treeCoefficient (γ 1) hlast.1 g hn := by
  obtain ⟨δ, hδ, D, hDw⟩ := weak_relative_general_position hn γ hγ hw hfirst hlast
  have hfirstD : Generic (D.path 0) := by rw [D.first]; exact hfirst
  have hlastD : Generic (D.path 1) := by rw [D.last]; exact hlast
  have he := tree_path_constant_of_silent_germs D.path D.continuous (by
    intro x hx
    obtain ⟨w, hc, hcurve, hs, hkind⟩ := D.event x hx
    have hw : WeakGeneric w.center := by rw [hc]; exact hDw x
    exact ⟨w, hc, hcurve, w.silent_of_simple_weak_center hn hs hw⟩)
    g hn ⟨0, hfirstD⟩ ⟨1, hlastD⟩
  have htuple0 : (⟨D.path 0, hfirstD⟩ : GenericTuple n) = ⟨γ 0, hfirst⟩ := Subtype.ext D.first
  have htuple1 : (⟨D.path 1, hlastD⟩ : GenericTuple n) = ⟨γ 1, hlast⟩ := Subtype.ext D.last
  have hc0 := congrArg (fun P : GenericTuple n => treeCoefficient P.val P.property.1 g hn) htuple0
  have hc1 := congrArg (fun P : GenericTuple n => treeCoefficient P.val P.property.1 g hn) htuple1
  exact hc0.symm.trans (he.trans hc1)

end
end SM
