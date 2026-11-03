import DirectGLSSW.CapCriticalEventGeometry
import DirectGLSSW.ActualEventGeometry
import DirectGLSSW.GlobalCapIntertwining
import DirectGLSSW.GlobalCapAlgebra
import DirectGLSSW.TriangularInverse
import Lean.Elab.Tactic.Omega

set_option autoImplicit false

namespace DirectGLSSW.OrderedCapEvents

open DirectGLSSW
open DirectGLSSW.CapCriticalEventGeometry
open DirectGLSSW.CapCriticalTimes
open DirectGLSSW.ActualEventGeometry
open DirectGLSSW.CapCrossingEvent
open DirectGLSSW.GlobalCapIntertwining
open DirectGLSSW.GlobalCapAlgebra
open scoped BigOperators

noncomputable def actualPairs (q : ℕ → PlanarPoint ℝ) (n : ℕ) : Finset (ℕ × ℕ) :=
  (criticalPairs q n).filter (fun p =>
    p.2 = p.1 + 1 ∧ (q p.1).2 / (q p.2).2 < 0)

noncomputable def actualTimes (q : ℕ → PlanarPoint ℝ) (n : ℕ) : Finset ℝ :=
  (actualPairs q n).image (criticalRoot q)

abbrev EventIndex (q : ℕ → PlanarPoint ℝ) (n : ℕ) := Fin (actualTimes q n).card

noncomputable def eventTime (q : ℕ → PlanarPoint ℝ) (n : ℕ) (c : EventIndex q n) : ℝ :=
  (actualTimes q n).orderEmbOfFin rfl c

theorem eventTime_mem_actualTimes (q : ℕ → PlanarPoint ℝ) (n : ℕ) (c : EventIndex q n) :
    eventTime q n c ∈ actualTimes q n := by
  exact Finset.orderEmbOfFin_mem (actualTimes q n) rfl c

theorem eventTime_strictMono (q : ℕ → PlanarPoint ℝ) (n : ℕ) :
    StrictMono (eventTime q n) := by
  exact (actualTimes q n).orderEmbOfFin rfl |>.strictMono

theorem exists_pair_at_time (q : ℕ → PlanarPoint ℝ) (n : ℕ)
    (c : EventIndex q n) :
    ∃ p, p ∈ actualPairs q n ∧ criticalRoot q p = eventTime q n c := by
  have hmem := eventTime_mem_actualTimes q n c
  change eventTime q n c ∈ (actualPairs q n).image (criticalRoot q) at hmem
  rcases Finset.mem_image.mp hmem with ⟨p, hp, hroot⟩
  exact ⟨p, hp, hroot⟩

noncomputable def eventPair (q : ℕ → PlanarPoint ℝ) (n : ℕ) (c : EventIndex q n) : ℕ × ℕ :=
  Classical.choose (exists_pair_at_time q n c)

theorem eventPair_spec (q : ℕ → PlanarPoint ℝ) (n : ℕ) (c : EventIndex q n) :
    eventPair q n c ∈ actualPairs q n ∧ criticalRoot q (eventPair q n c) = eventTime q n c := by
  exact Classical.choose_spec (exists_pair_at_time q n c)

theorem eventPair_bounds (q : ℕ → PlanarPoint ℝ) (n : ℕ) (c : EventIndex q n) :
    0 < (eventPair q n c).1 ∧ (eventPair q n c).1 < n ∧
    (eventPair q n c).2 = (eventPair q n c).1 + 1 ∧
    (q (eventPair q n c).1).2 / (q (eventPair q n c).2).2 < 0 ∧
    planarDet (q (eventPair q n c).1 - q (eventPair q n c).2) (1, 0) ≠ 0 := by
  have hactual := (eventPair_spec q n c).1
  have hparts : eventPair q n c ∈ criticalPairs q n ∧
      (eventPair q n c).2 = (eventPair q n c).1 + 1 ∧
      (q (eventPair q n c).1).2 / (q (eventPair q n c).2).2 < 0 := by
    simpa [actualPairs, Finset.mem_filter] using hactual
  rcases hparts with ⟨hcritical, hadj, hnegative⟩
  have hcritical' := hcritical
  simp only [criticalPairs, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hcritical'
  rcases hcritical' with ⟨⟨hleftRange, hrightRange⟩, hleft, hlt, hright, hslope⟩
  refine ⟨hleft, ?_, hadj, hnegative, hslope⟩
  omega

theorem eventPair_criticalPairs_mem (q : ℕ → PlanarPoint ℝ) (n : ℕ)
    (c : EventIndex q n) : eventPair q n c ∈ criticalPairs q n := by
  have hactual := (eventPair_spec q n c).1
  have hfilter : eventPair q n c ∈
      (criticalPairs q n).filter (fun p =>
        p.2 = p.1 + 1 ∧ (q p.1).2 / (q p.2).2 < 0) := by
    simpa [actualPairs] using hactual
  exact (Finset.mem_filter.mp hfilter).1

theorem eventTime_mem_criticalTimes (q : ℕ → PlanarPoint ℝ) (n : ℕ)
    (c : EventIndex q n) : eventTime q n c ∈ criticalTimes q n := by
  apply (mem_criticalTimes_iff q n (eventTime q n c)).2
  have hb := eventPair_bounds q n c
  have hp := eventPair_spec q n c
  refine ⟨(eventPair q n c).1, (eventPair q n c).2, hb.1, ?_, ?_, hb.2.2.2.2, ?_⟩
  · omega
  · omega
  · simpa [criticalRoot] using hp.2.symm

noncomputable def eventSign (q : ℕ → PlanarPoint ℝ) (n : ℕ) (c : EventIndex q n) : ℚ :=
  scalarSignValue (q (eventPair q n c).2).2

noncomputable def eventRow (q : ℕ → PlanarPoint ℝ) (n : ℕ) (c : EventIndex q n) : Fin n → ℚ :=
  fun j => lineCapF (horizontalMove q (eventTime q n c)) n
    ⟨(eventPair q n c).1, (eventPair_bounds q n c).2.1⟩ j

noncomputable def eventColumn (q : ℕ → PlanarPoint ℝ) (n : ℕ) (c : EventIndex q n) : Fin n → ℚ :=
  fun i => lineCapU (horizontalMove q (eventTime q n c)) n i
    ⟨(eventPair q n c).1 - 1, by have hb := eventPair_bounds q n c; omega⟩

noncomputable def eventPairing (q : ℕ → PlanarPoint ℝ) (n : ℕ)
    (c d : EventIndex q n) : ℚ :=
  ∑ i : Fin n, eventRow q n c i * eventColumn q n d i

noncomputable def eventMatrix (q : ℕ → PlanarPoint ℝ) (n : ℕ) :
    Matrix (EventIndex q n) (EventIndex q n) ℚ :=
  fun c d => if c < d then eventPairing q n c d else 0

noncomputable def eventSignMatrix (q : ℕ → PlanarPoint ℝ) (n : ℕ) :
    Matrix (EventIndex q n) (EventIndex q n) ℚ :=
  Matrix.diagonal (eventSign q n)

theorem eventMatrix_strictUpper (q : ℕ → PlanarPoint ℝ) (n : ℕ) :
    StrictUpper (eventMatrix q n) := by
  intro c d hdc
  change (if c < d then eventPairing q n c d else 0) = 0
  have hnot : ¬ c < d := by
    intro h
    exact (not_lt_of_ge hdc) (Fin.lt_iff_val_lt_val.mpr h)
  simp [hnot]

theorem eventPair_is_open_segment_crossing (q : ℕ → PlanarPoint ℝ) (n : ℕ)
    (hzero : (q 0).2 = 0) (c : EventIndex q n) :
    OnOpenSegment (q (eventPair q n c).1) (q (eventPair q n c).2)
      (horizontalMove q (eventTime q n c) 0) := by
  have hb := eventPair_bounds q n c
  have hkpos := hb.1
  have hadj := hb.2.2.1
  have hratio := hb.2.2.2.1
  have hroot := (eventPair_spec q n c).2
  have hne : (q (eventPair q n c).1).2 ≠ 0 ∧
      (q (eventPair q n c).2).2 ≠ 0 := by
    have hr := div_neg_iff.mp hratio
    rcases hr with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · exact ⟨ne_of_gt ha, ne_of_lt hb⟩
    · exact ⟨ne_of_lt ha, ne_of_gt hb⟩
  have hpair : eventPair q n c =
      ((eventPair q n c).1, (eventPair q n c).1 + 1) := by
    apply Prod.ext
    · rfl
    · exact hadj
  have hneNext : (q ((eventPair q n c).1 + 1)).2 ≠ 0 := by
    simpa only [hadj] using hne.2
  have hratioNext :
      (q (eventPair q n c).1).2 / (q ((eventPair q n c).1 + 1)).2 < 0 := by
    simpa only [hadj] using hratio
  have hcross := criticalRoot_event_onOpenSegment_iff_negative_height_ratio
    q (eventPair q n c).1 hkpos hzero hne.1 hneNext
  rw [hpair] at hroot ⊢
  rw [← hroot]
  exact hcross.mpr hratioNext





















end DirectGLSSW.OrderedCapEvents
