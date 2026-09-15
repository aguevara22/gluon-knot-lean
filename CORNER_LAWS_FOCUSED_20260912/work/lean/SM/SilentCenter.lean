import SM.NamedWallPredicates

/-! Exterior-extension and pure-cut centres lie in the actual weak locus.
All weak properties are derived from the named source predicates. -/

namespace SM

variable {n : ℕ} [NeZero n] {P : LabelledTuple n}

theorem weak_of_geometry_turns_vertices (hg : CrossingGeometry P)
    (ht : ∀ i, turn P i ≠ 0)
    (hv : ∀ k i, ¬ incident k i → P k ∉ edgeSegment P i) : WeakGeneric P := by
  refine ⟨hg.1, ht, hv, ?_, hg.2.2⟩
  intro i j hr
  constructor
  · intro x hi hj
    exact (hg.2.1 i j hr x hi hj).2.2
  · intro x y hxi hxj hyi hyj
    exact transverse_segments_unique (hg.2.1 i j hr x hxi hxj).2.2 hxi hxj hyi hyj

namespace WallGerm

def Silent (g : WallGerm n) : Prop :=
  (∃ M a, g.ExtensionAt M a) ∨ ∃ i j k, g.PureCutAt i j k

theorem extension_center_weak (hn : 3 ≤ n) (g : WallGerm n)
    {M a : ZMod n} (h : g.ExtensionAt M a) : WeakGeneric g.center :=
  weak_of_geometry_turns_vertices
    (extension_crossingGeometry hn h.1 h.2.1 h.2.2.2.2.1 h.2.2.1)
    (contact_turns_nonzero hn h.1 h.2.1)
    (extension_vertex_exclusion hn h.1 h.2.1 h.2.2.2.2.1)

theorem pureCut_center_weak (g : WallGerm n)
    {i j k : ZMod n} (h : g.PureCutAt i j k) : WeakGeneric g.center := by
  have hn := noConsecutive_size (singlePointTriple_data h.2.1).1 h.1
  exact weak_of_geometry_turns_vertices (pureCut_crossingGeometry h.2.1 h.1 h.2.2.1)
    (singlePointTriple_all_turns_nonzero (by omega) h.2.1 (noConsecutive_ne_turnSupport h.1))
    (noConsecutive_vertex_exclusion (by omega) h.2.1 h.1)

theorem silent_center_weak (hn : 3 ≤ n) (g : WallGerm n)
    (h : g.Silent) : WeakGeneric g.center := by
  rcases h with ⟨M, a, h⟩ | ⟨i, j, k, h⟩
  · exact extension_center_weak hn g h
  · exact pureCut_center_weak g h

theorem silent_curve_weak (hn : 3 ≤ n) (g : WallGerm n)
    (h : g.Silent) (t : g.Parameter) : WeakGeneric (g.curve t) := by
  by_cases ht : t.val = 0
  · have he : t = g.zeroParameter := Subtype.ext ht
    subst t
    exact silent_center_weak hn g h
  · exact generic_implies_weak hn (g.generic_punctured t ht)

theorem silent_center_in_silentLocus (hn : 3 ≤ n) (g : WallGerm n)
    (h : g.Silent) : g.center ∈ silentLocus n :=
  ⟨silent_center_weak hn g h, g.nongeneric_center⟩

end WallGerm
end SM
