import SM.FusionCrossings
import SM.GeometricVisits

/-! Actual visit bijection under fusion, preserving each crossing's two-visit
pairing. The actual intersection parameter satisfies the affine fusion formula. -/

namespace SM

variable {n : ℕ} [NeZero n] {P : LabelledTuple (n + 1)} {j : ZMod (n + 1)}

theorem fusionIndex_injective_on_crossing (c : Crossing P)
    {a b : ZMod (n + 1)} (ha : a ∈ c.val) (hb : b ∈ c.val)
    (he : fusionIndex j a = fusionIndex j b) : a = b := by
  obtain ⟨i, k, hs, hr, _⟩ := c.property
  rw [hs] at ha hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · rfl
  · exact (fusionIndex_ne_of_remote hr he).elim
  · exact (fusionIndex_ne_of_remote hr he.symm).elim
  · rfl

noncomputable def fusionVisitEdgeEquiv (hn : 3 ≤ n)
    (hz : pointZeroTriples P = {turnSupport j})
    (hb : StrictBetween (P (j - 1)) (P j) (P (j + 1)))
    (hc : concurrenceTriples P = ∅) (c : Crossing P) :
    {i // i ∈ c.val} ≃ {i // i ∈ (fusionCrossing hn hz hb hc c).val} := by
  let f : {i // i ∈ c.val} → {i // i ∈ (fusionCrossing hn hz hb hc c).val} :=
    fun i => ⟨fusionIndex j i.val, Finset.mem_image.mpr ⟨i.val, i.property, rfl⟩⟩
  apply Equiv.ofBijective f
  constructor
  · intro a b he
    apply Subtype.ext
    exact fusionIndex_injective_on_crossing c a.property b.property (congrArg Subtype.val he)
  · intro k
    obtain ⟨i, hi, he⟩ := Finset.mem_image.mp k.property
    exact ⟨⟨i, hi⟩, Subtype.ext he⟩

noncomputable def fusionVisitEquiv (hn : 3 ≤ n)
    (hz : pointZeroTriples P = {turnSupport j})
    (hb : StrictBetween (P (j - 1)) (P j) (P (j + 1)))
    (hc : concurrenceTriples P = ∅) : Visit P ≃ Visit (deleteVertex P j) :=
  Equiv.sigmaCongr (fusionCrossingEquiv hn hz hb hc) (fusionVisitEdgeEquiv hn hz hb hc)

theorem fusionVisit_crossing (hn : 3 ≤ n)
    (hz : pointZeroTriples P = {turnSupport j})
    (hb : StrictBetween (P (j - 1)) (P j) (P (j + 1)))
    (hc : concurrenceTriples P = ∅) (v : Visit P) :
    (fusionVisitEquiv hn hz hb hc v).1 = fusionCrossingEquiv hn hz hb hc v.1 := rfl

theorem fusionVisit_edge (hn : 3 ≤ n)
    (hz : pointZeroTriples P = {turnSupport j})
    (hb : StrictBetween (P (j - 1)) (P j) (P (j + 1)))
    (hc : concurrenceTriples P = ∅) (v : Visit P) :
    (fusionVisitEquiv hn hz hb hc v).2.val = fusionIndex j v.2.val := rfl

theorem fusionVisit_pairing (hn : 3 ≤ n)
    (hz : pointZeroTriples P = {turnSupport j})
    (hb : StrictBetween (P (j - 1)) (P j) (P (j + 1)))
    (hc : concurrenceTriples P = ∅) (v w : Visit P) :
    (fusionVisitEquiv hn hz hb hc v).1 = (fusionVisitEquiv hn hz hb hc w).1 ↔ v.1 = w.1 :=
  (fusionCrossingEquiv hn hz hb hc).injective.eq_iff

theorem visitParameter_fusion (hn : 3 ≤ n)
    (hz : pointZeroTriples P = {turnSupport j})
    (hb : StrictBetween (P (j - 1)) (P j) (P (j + 1)))
    (hc : concurrenceTriples P = ∅) {r : ℝ}
    (hm : P j = P (j - 1) + r • (P (j + 1) - P (j - 1))) (v : Visit P) :
    visitParameter (fusionVisitEquiv hn hz hb hc v) =
      fusionParameter r j v.2.val (visitParameter v) := by
  have hgeom := generic_crossingGeometry hn (generic_deleteVertex hn hz hb hc)
  apply edgePoint_injective (hgeom.1 (fusionIndex j v.2.val))
  calc
    _ = crossingPoint (fusionCrossing hn hz hb hc v.1) :=
      (crossingParameter_spec (fusionVisitEquiv hn hz hb hc v).1
        (fusionVisitEquiv hn hz hb hc v).2.val
        (fusionVisitEquiv hn hz hb hc v).2.property).2.2.symm
    _ = crossingPoint v.1 := crossingPoint_fusion hn hz hb hc v.1
    _ = edgePoint P v.2.val (visitParameter v) :=
      (crossingParameter_spec v.1 v.2.val v.2.property).2.2
    _ = _ := edgePoint_fusion P hm v.2.val (visitParameter v)

end SM
