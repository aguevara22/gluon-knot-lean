import SM.ContactCrossingPatterns

/-! Complete V-wall crossing-set exchange, with fixed bigon/sliding behavior
on the actual connected sides. Visit-order localization is a separate task. -/

namespace SM

open scoped symmDiff

variable {n : ℕ} [NeZero n]

def VertexCrossingData (C P Q : LabelledTuple n) (M a : ZMod n) : Prop :=
  crossingSet P ∆ crossingSet Q = {{a, M - 1}, {a, M}} ∧
  (chi C a (a + 1) (M - 1) = chi C a (a + 1) (M + 1) → BigonCrossingPattern P Q M a) ∧
  (chi C a (a + 1) (M - 1) ≠ chi C a (a + 1) (M + 1) → SlidingCrossingPattern P Q M a) ∧
  ∀ s : Finset (ZMod n), ¬ ContactAffected M a s →
    (IsCrossing P s ↔ IsCrossing C s) ∧ (IsCrossing Q s ↔ IsCrossing C s)

theorem vertexCrossingData_congr {C P Q P' Q' : LabelledTuple n} {M a : ZMod n}
    (hP : ∀ s, IsCrossing P' s ↔ IsCrossing P s)
    (hQ : ∀ s, IsCrossing Q' s ↔ IsCrossing Q s) :
    VertexCrossingData C P' Q' M a ↔ VertexCrossingData C P Q M a := by
  have hp : crossingSet P' = crossingSet P := by
    ext s
    simpa only [mem_crossingSet] using hP s
  have hq : crossingSet Q' = crossingSet Q := by
    ext s
    simpa only [mem_crossingSet] using hQ s
  simp only [VertexCrossingData, hp, hq, BigonCrossingPattern, SlidingCrossingPattern, hP, hQ]

namespace WallGerm

theorem vertex_crossing_sides_local (hn : 3 ≤ n) (g : WallGerm n)
    {M a : ZMod n} (h : g.VertexEdgeAt M a) :
    Regular g.center ∧ ({a, M - 1} : Finset (ZMod n)) ≠ {a, M} ∧
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ g.radius ∧ ∀ t : g.SideParameter, t.val < δ →
      VertexCrossingData g.center (g.sideTuple true t).val (g.sideTuple false t).val M a := by
  refine ⟨g.vertexEdge_regular hn h, contact_pairs_distinct hn h.1, ?_⟩
  obtain ⟨δc, hδc, hδcr, hcross⟩ := g.vertexEdge_contact_tests hn h
  obtain ⟨δo, hδo, _, hother⟩ := g.vertexEdge_unaffected_crossings hn h
  obtain ⟨δs, hδs, _, hsign⟩ := h.2.2.2.2
  let δ := min δc (min δo δs)
  have hdc : δ ≤ δc := min_le_left _ _
  have hdo : δ ≤ δo := (min_le_right _ _).trans (min_le_left _ _)
  have hds : δ ≤ δs := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨δ, lt_min hδc (lt_min hδo hδs), hdc.trans hδcr, ?_⟩
  intro t ht
  have habs (b : Bool) : |(g.sideTime b t).val| = t.val := by
    cases b <;> simp [sideTime, abs_of_pos t.property.1]
  have htests (b : Bool) : ContactTests g.center (g.sideTuple b t).val M a :=
    hcross (g.sideTime b t) (by rw [habs]; exact lt_of_lt_of_le ht hdc)
      (g.sideTime_ne_zero b t)
  have hrest (b : Bool) (s : Finset (ZMod n)) (hs : ¬ ContactAffected M a s) :
      IsCrossing (g.sideTuple b t).val s ↔ IsCrossing g.center s :=
    hother (g.sideTime b t) (by rw [habs]; exact lt_of_lt_of_le ht hdo) s hs
  have hsc := hsign t (lt_of_lt_of_le ht hds)
  have hne := contactNeighbour_chi_nonzero hn h.1 h.2.1
  have hf := contact_pair_flips (htests true) (htests false) hsc hne
  refine ⟨contact_symmDiff_of_flips hf
    (fun s hs => (hrest true s hs).trans (hrest false s hs).symm), ?_, ?_, ?_⟩
  · intro he
    exact contact_bigon_of_tests (htests true) (htests false) hsc (hne false) he
  · intro he
    exact contact_sliding_of_tests (htests true) (htests false) hsc (hne false) (hne true) he
  · intro s hs
    exact ⟨hrest true s hs, hrest false s hs⟩

/-- The two sides are genuine connected generic families, so a crossing
pattern proved near zero is fixed on each entire side. The two evaluation
parameters below are independent. -/
theorem vertex_crossing_sides (hn : 3 ≤ n) (g : WallGerm n)
    {M a : ZMod n} (h : g.VertexEdgeAt M a) :
    Regular g.center ∧ ({a, M - 1} : Finset (ZMod n)) ≠ {a, M} ∧
    ∀ s t : g.SideParameter,
      VertexCrossingData g.center (g.sideTuple true s).val (g.sideTuple false t).val M a := by
  obtain ⟨hreg, hpair, δ, hδ, hδr, hlocal⟩ := g.vertex_crossing_sides_local hn h
  let t₀ : g.SideParameter := ⟨δ / 2, by constructor <;> linarith⟩
  have ht₀ : t₀.val < δ := by dsimp [t₀]; linarith
  have hd := hlocal t₀ ht₀
  refine ⟨hreg, hpair, ?_⟩
  intro s t
  exact (vertexCrossingData_congr
    (generic_family_crossing_constant hn (g.continuous_sideTuple true) s t₀)
    (generic_family_crossing_constant hn (g.continuous_sideTuple false) t t₀)).mpr hd

end WallGerm
end SM
