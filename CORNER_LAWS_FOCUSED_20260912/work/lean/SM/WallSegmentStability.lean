import SM.SegmentStability

/-! Full finite-family assembly for source lem:wall-segment-stability.
Continuity is required only on a supplied open neighborhood of the centre.
Every conclusion is on one common smaller open neighborhood. -/

namespace SM

open Filter Topology

/-- Actual transverse intersection in the two relative interiors. -/
def TransverseInterior (a b u v : Plane) : Prop :=
  det u v ≠ 0 ∧ ∃ s r : ℝ, 0 < s ∧ s < 1 ∧ 0 < r ∧ r < 1 ∧
    a + s • u = b + r • v

/-- Cramer's parameters are interior and specify the unique actual common point. -/
def TransverseIntersection (a b u v : Plane) : Prop :=
  det u v ≠ 0 ∧
  (0 < cramerFirst a b u v ∧ cramerFirst a b u v < 1) ∧
  (0 < cramerSecond a b u v ∧ cramerSecond a b u v < 1) ∧
  a + cramerFirst a b u v • u = b + cramerSecond a b u v • v ∧
  ∃! x, onSegment a u x ∧ onSegment b v x

theorem transverseIntersection_of_interior {a b u v : Plane}
    (h : TransverseInterior a b u v) : TransverseIntersection a b u v := by
  rcases h with ⟨hd, s, r, hs0, hs1, hr0, hr1, heq⟩
  have hs : cramerFirst a b u v = s :=
    (div_eq_iff hd).mpr (intersection_parameter_identity heq)
  have hr : cramerSecond a b u v = r :=
    (div_eq_iff hd).mpr (intersection_second_parameter_identity heq)
  refine ⟨hd, by simpa [hs] using And.intro hs0 hs1,
    by simpa [hr] using And.intro hr0 hr1, ?_, ?_⟩
  · simpa [hs, hr] using heq
  · refine ⟨a + s • u, ⟨⟨s, hs0.le, hs1.le, rfl⟩, ⟨r, hr0.le, hr1.le, heq⟩⟩, ?_⟩
    rintro x ⟨⟨s', _, _, hx⟩, ⟨r', _, _, hx'⟩⟩
    have hp := intersection_parameters_unique hd (hx.symm.trans hx') heq
    simpa [hp.1] using hx

variable {α : Type*} [TopologicalSpace α] {t₀ : α}

/-- The two conditional branches leave singular central pairs unrestricted. -/
def SegmentPairPersists (a b u v : α → Plane) (t₀ t : α) : Prop :=
  (¬ segmentsMeet (a t₀) (b t₀) (u t₀) (v t₀) →
    ¬ segmentsMeet (a t) (b t) (u t) (v t)) ∧
  (TransverseInterior (a t₀) (b t₀) (u t₀) (v t₀) →
    TransverseIntersection (a t) (b t) (u t) (v t))

theorem segmentPair_persists {a b u v : α → Plane}
    (ha : ContinuousAt a t₀) (hb : ContinuousAt b t₀)
    (hu : ContinuousAt u t₀) (hv : ContinuousAt v t₀) :
    ∀ᶠ t in 𝓝 t₀, SegmentPairPersists a b u v t₀ t := by
  classical
  have hdis : ∀ᶠ t in 𝓝 t₀,
      ¬ segmentsMeet (a t₀) (b t₀) (u t₀) (v t₀) →
        ¬ segmentsMeet (a t) (b t) (u t) (v t) := by
    by_cases h : ¬ segmentsMeet (a t₀) (b t₀) (u t₀) (v t₀)
    · exact (disjoint_segments_persist ha hb hu hv h).mono (fun _ ht _ => ht)
    · exact Eventually.of_forall (fun _ ht => (h ht).elim)
  have htrans : ∀ᶠ t in 𝓝 t₀,
      TransverseInterior (a t₀) (b t₀) (u t₀) (v t₀) →
        TransverseIntersection (a t) (b t) (u t) (v t) := by
    by_cases h : TransverseInterior (a t₀) (b t₀) (u t₀) (v t₀)
    · rcases h with ⟨hd, s, r, hs0, hs1, hr0, hr1, heq⟩
      have hp := transverse_intersection_persists ha hb hu hv hd hs0 hs1 hr0 hr1 heq
      filter_upwards [hp] with t ht _
      rcases ht with ⟨s', r', hs'0, hs'1, hr'0, hr'1, heq', hd'⟩
      exact transverseIntersection_of_interior ⟨hd', s', r', hs'0, hs'1, hr'0, hr'1, heq'⟩
    · exact Eventually.of_forall (fun _ ht => (h ht).elim)
  exact hdis.and htrans

/-- Ordered parameter comparison, excluding equality only at the centre. -/
theorem continuousAt_preserves_parameter_order {f g : α → ℝ}
    (hf : ContinuousAt f t₀) (hg : ContinuousAt g t₀) (hne : f t₀ ≠ g t₀) :
    ∀ᶠ t in 𝓝 t₀, (f t < g t ↔ f t₀ < g t₀) := by
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact (continuousAt_preserves_strict_order hf hg hlt).mono
      (fun _ ht => iff_of_true ht hlt)
  · exact (continuousAt_preserves_strict_order hg hf hgt).mono
      (fun _ ht => iff_of_false (not_lt.mpr ht.le) (not_lt.mpr hgt.le))

/-- The first parameters are measured on the common first segment, in its orientation. -/
def CrossingOrderPersists (a u : ι → α → Plane) (t₀ t : α) (i j k : ι) : Prop :=
  TransverseInterior (a i t₀) (a j t₀) (u i t₀) (u j t₀) →
  TransverseInterior (a i t₀) (a k t₀) (u i t₀) (u k t₀) →
  cramerFirst (a i t₀) (a j t₀) (u i t₀) (u j t₀) ≠
    cramerFirst (a i t₀) (a k t₀) (u i t₀) (u k t₀) →
  (cramerFirst (a i t) (a j t) (u i t) (u j t) <
    cramerFirst (a i t) (a k t) (u i t) (u k t) ↔
   cramerFirst (a i t₀) (a j t₀) (u i t₀) (u j t₀) <
    cramerFirst (a i t₀) (a k t₀) (u i t₀) (u k t₀))

theorem crossingOrder_persists {a u : ι → α → Plane}
    (ha : ∀ i, ContinuousAt (a i) t₀) (hu : ∀ i, ContinuousAt (u i) t₀)
    (i j k : ι) : ∀ᶠ t in 𝓝 t₀, CrossingOrderPersists a u t₀ t i j k := by
  classical
  by_cases hij : TransverseInterior (a i t₀) (a j t₀) (u i t₀) (u j t₀)
  · by_cases hik : TransverseInterior (a i t₀) (a k t₀) (u i t₀) (u k t₀)
    · by_cases hne : cramerFirst (a i t₀) (a j t₀) (u i t₀) (u j t₀) ≠
          cramerFirst (a i t₀) (a k t₀) (u i t₀) (u k t₀)
      · exact (continuousAt_preserves_parameter_order
          (continuousAt_cramerFirst (ha i) (ha j) (hu i) (hu j) hij.1)
          (continuousAt_cramerFirst (ha i) (ha k) (hu i) (hu k) hik.1) hne).mono
          (fun _ ht _ _ _ => ht)
      · exact Eventually.of_forall (fun _ _ _ hn => (hne hn).elim)
    · exact Eventually.of_forall (fun _ _ ht => (hik ht).elim)
  · exact Eventually.of_forall (fun _ ht => (hij ht).elim)

/-- Pair persistence plus continuity of both actual intersection parameters. -/
def SegmentPairStableOn (a b u v : α → Plane) (t₀ : α) (U : Set α) : Prop :=
  (∀ t ∈ U, SegmentPairPersists a b u v t₀ t) ∧
  (TransverseInterior (a t₀) (b t₀) (u t₀) (v t₀) →
    ContinuousOn (fun t => cramerFirst (a t) (b t) (u t) (v t)) U ∧
    ContinuousOn (fun t => cramerSecond (a t) (b t) (u t) (v t)) U)

/-- Source lem:wall-segment-stability, with one neighborhood for the finite family.
An open local parameter domain permits arbitrary continuous wall germs. The
finite type may be empty; no implicit nonemptiness assumption is used. -/
theorem wall_segment_stability {ι : Type*} [Finite ι]
    (a u : ι → α → Plane) {V : Set α} (hV : IsOpen V) (ht₀ : t₀ ∈ V)
    (ha : ∀ i, ContinuousOn (a i) V) (hu : ∀ i, ContinuousOn (u i) V)
    (hnz : ∀ i, u i t₀ ≠ 0) :
    ∃ U : Set α, IsOpen U ∧ t₀ ∈ U ∧ U ⊆ V ∧
      (∀ i, ∀ t ∈ U, u i t ≠ 0) ∧
      (∀ i j, SegmentPairStableOn (a i) (a j) (u i) (u j) t₀ U) ∧
      (∀ t ∈ U, ∀ i j k, CrossingOrderPersists a u t₀ t i j k) := by
  have ha₀ (i) : ContinuousAt (a i) t₀ := (ha i t₀ ht₀).continuousAt (hV.mem_nhds ht₀)
  have hu₀ (i) : ContinuousAt (u i) t₀ := (hu i t₀ ht₀).continuousAt (hV.mem_nhds ht₀)
  have hp : ∀ᶠ t in 𝓝 t₀, ∀ i j,
      SegmentPairPersists (a i) (a j) (u i) (u j) t₀ t :=
    eventually_all.mpr fun i => eventually_all.mpr fun j =>
      segmentPair_persists (ha₀ i) (ha₀ j) (hu₀ i) (hu₀ j)
  have ho : ∀ᶠ t in 𝓝 t₀, ∀ i j k, CrossingOrderPersists a u t₀ t i j k :=
    eventually_all.mpr fun i => eventually_all.mpr fun j => eventually_all.mpr fun k =>
      crossingOrder_persists ha₀ hu₀ i j k
  have hn : ∀ᶠ t in 𝓝 t₀, ∀ i, u i t ≠ 0 :=
    eventually_all.mpr fun i => (hu₀ i).eventually
      (isOpen_compl_singleton.mem_nhds (hnz i))
  have hve : ∀ᶠ t in 𝓝 t₀, t ∈ V := hV.mem_nhds ht₀
  have hall := hve.and (hn.and (hp.and ho))
  obtain ⟨U, hsub, hU, htU⟩ := mem_nhds_iff.mp hall
  have hUV : U ⊆ V := fun t ht => (hsub ht).1
  refine ⟨U, hU, htU, hUV, ?_, ?_, ?_⟩
  · exact fun i t ht => (hsub ht).2.1 i
  · intro i j
    refine ⟨fun t ht => (hsub ht).2.2.1 i j, ?_⟩
    intro hij
    have hd (t) (ht : t ∈ U) : det (u i t) (u j t) ≠ 0 :=
      ((hsub ht).2.2.1 i j).2 hij |>.1
    have hac (i) (t) (ht : t ∈ U) : ContinuousAt (a i) t :=
      (ha i t (hUV ht)).continuousAt (hV.mem_nhds (hUV ht))
    have huc (i) (t) (ht : t ∈ U) : ContinuousAt (u i) t :=
      (hu i t (hUV ht)).continuousAt (hV.mem_nhds (hUV ht))
    exact ⟨fun t ht => (continuousAt_cramerFirst (hac i t ht) (hac j t ht)
      (huc i t ht) (huc j t ht) (hd t ht)).continuousWithinAt,
      fun t ht => (continuousAt_cramerSecond (hac i t ht) (hac j t ht)
      (huc i t ht) (huc j t ht) (hd t ht)).continuousWithinAt⟩
  · exact fun t ht => (hsub ht).2.2.2

end SM
