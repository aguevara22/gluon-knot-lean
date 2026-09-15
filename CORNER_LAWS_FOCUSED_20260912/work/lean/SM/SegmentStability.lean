import SM.ContinuousGeometry
import Mathlib.Topology.UnitInterval
import Mathlib.Topology.Maps.Proper.Basic

/-! Actual closed-segment stability, for source lem:wall-segment-stability.
The compact parameter square makes the set of intersecting configurations
closed; pulling back its open complement proves persistence of disjointness.
No separation estimate or choice of norm on the plane is needed. -/

namespace SM

open Filter Topology

/-- A point lies on the closed segment with initial point `a` and direction `u`. -/
def onSegment (a u x : Plane) : Prop :=
  ∃ s : ℝ, 0 ≤ s ∧ s ≤ 1 ∧ x = a + s • u

/-- The two actual closed segments intersect. -/
def segmentsMeet (a b u v : Plane) : Prop :=
  ∃ s r : ℝ, 0 ≤ s ∧ s ≤ 1 ∧ 0 ≤ r ∧ r ≤ 1 ∧ a + s • u = b + r • v

theorem segmentsMeet_iff (a b u v : Plane) :
    segmentsMeet a b u v ↔ ∃ x, onSegment a u x ∧ onSegment b v x := by
  constructor
  · rintro ⟨s, r, hs0, hs1, hr0, hr1, heq⟩
    exact ⟨a + s • u, ⟨s, hs0, hs1, rfl⟩, ⟨r, hr0, hr1, heq⟩⟩
  · rintro ⟨x, ⟨s, hs0, hs1, hs⟩, ⟨r, hr0, hr1, hr⟩⟩
    exact ⟨s, r, hs0, hs1, hr0, hr1, hs.symm.trans hr⟩

abbrev SegmentConfiguration := (Plane × Plane) × (Plane × Plane)

theorem isClosed_segmentsMeet :
    IsClosed {c : SegmentConfiguration | segmentsMeet c.1.1 c.1.2 c.2.1 c.2.2} := by
  let E : Set (SegmentConfiguration × (unitInterval × unitInterval)) :=
    {p | p.1.1.1 + (p.2.1 : ℝ) • p.1.2.1 =
      p.1.1.2 + (p.2.2 : ℝ) • p.1.2.2}
  have hE : IsClosed E := by
    apply isClosed_eq <;> fun_prop
  have hproj := isClosedMap_fst_of_compactSpace E hE
  convert hproj using 1
  ext c
  constructor
  · rintro ⟨s, r, hs0, hs1, hr0, hr1, heq⟩
    exact ⟨(c, (⟨s, hs0, hs1⟩, ⟨r, hr0, hr1⟩)), heq, rfl⟩
  · rintro ⟨⟨c', s, r⟩, heq, hc⟩
    dsimp at hc
    subst c'
    exact ⟨s, r, s.property.1, s.property.2, r.property.1, r.property.2, heq⟩

variable {α : Type*} [TopologicalSpace α] {t₀ : α}

theorem disjoint_segments_persist {a b u v : α → Plane}
    (ha : ContinuousAt a t₀) (hb : ContinuousAt b t₀)
    (hu : ContinuousAt u t₀) (hv : ContinuousAt v t₀)
    (hd : ¬ segmentsMeet (a t₀) (b t₀) (u t₀) (v t₀)) :
    ∀ᶠ t in 𝓝 t₀, ¬ segmentsMeet (a t) (b t) (u t) (v t) := by
  exact ((ha.prodMk hb).prodMk (hu.prodMk hv)).eventually
    (isClosed_segmentsMeet.isOpen_compl.mem_nhds hd)

end SM
