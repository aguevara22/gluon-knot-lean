import SM.GaussCyclicGap
import SM.GaussFamily
import SM.GaussRelabel

/-! The actual cyclic successor commutes with injective maps, including
wraparound. Hence the two-visit adjacency test is preserved by the canonical
Gauss transports in a generic family and under cyclic relabelling. -/

namespace SM

theorem list_next_map_injective {α β : Type*} [DecidableEq α] [DecidableEq β]
    (f : α → β) (hf : Function.Injective f) (l : List α) (hl : l.Nodup)
    (v : α) (hv : v ∈ l) :
    (l.map f).next (f v) (List.mem_map.mpr ⟨v, hv, rfl⟩) = f (l.next v hv) := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hv
  have him : i < (l.map f).length := by simpa using hi
  have hh := List.next_getElem (l.map f) (hl.map hf) i him
  rw [List.next_getElem l hl i hi]
  simpa only [List.getElem_map, List.length_map] using hh

theorem cycle_next_map_injective {α β : Type*} [DecidableEq α] [DecidableEq β]
    (f : α → β) (hf : Function.Injective f) (c : Cycle α) (hc : c.Nodup)
    (hm : (c.map f).Nodup) (v : α) (hv : v ∈ c) :
    (c.map f).next hm (f v) (Cycle.mem_map.mpr ⟨v, hv, rfl⟩) = f (c.next hc v hv) := by
  induction c using Quotient.inductionOn' with
  | _ l => exact list_next_map_injective f hf l hc v hv

variable {n : ℕ} [NeZero n] {P Q : LabelledTuple n}

theorem nextGaussVisit_equiv (hn : 3 ≤ n) (hP : Generic P) (hQ : Generic Q)
    (e : Visit P ≃ Visit Q) (he : (gaussCycle hn hP).map e = gaussCycle hn hQ)
    (v : Visit P) : nextGaussVisit hn hQ (e v) = e (nextGaussVisit hn hP v) := by
  classical
  have hm : ((gaussCycle hn hP).map e).Nodup := he.symm ▸ gaussCycle_nodup hn hQ
  have hh := cycle_next_map_injective e e.injective (gaussCycle hn hP)
    (gaussCycle_nodup hn hP) hm v (mem_gaussCycle hn hP v)
  simpa only [he, nextGaussVisit] using hh

theorem gaussVisitsAdjacent_equiv (hn : 3 ≤ n) (hP : Generic P) (hQ : Generic Q)
    (e : Visit P ≃ Visit Q) (he : (gaussCycle hn hP).map e = gaussCycle hn hQ)
    (v w : Visit P) :
    GaussVisitsAdjacent hn hQ (e v) (e w) ↔ GaussVisitsAdjacent hn hP v w := by
  unfold GaussVisitsAdjacent
  rw [nextGaussVisit_equiv hn hP hQ e he v, nextGaussVisit_equiv hn hP hQ e he w]
  simp only [e.injective.eq_iff]

theorem generic_family_gaussVisitsAdjacent {α : Type*} [TopologicalSpace α]
    [PreconnectedSpace α] (hn : 3 ≤ n) {F : α → GenericTuple n}
    (hF : Continuous F) (s t : α) (v w : Visit (F s).val) :
    GaussVisitsAdjacent hn (F t).property
      (visitTransport (generic_family_crossing_constant hn hF s t) v)
      (visitTransport (generic_family_crossing_constant hn hF s t) w) ↔
    GaussVisitsAdjacent hn (F s).property v w :=
  gaussVisitsAdjacent_equiv hn (F s).property (F t).property _
    (generic_family_gaussCycle hn hF s t) v w

theorem gaussVisitsAdjacent_shift (hn : 3 ≤ n) (hP : Generic P) (a : ZMod n)
    (v w : Visit P) :
    GaussVisitsAdjacent hn ((generic_shift a P).mpr hP)
      (visitShift a v) (visitShift a w) ↔ GaussVisitsAdjacent hn hP v w :=
  gaussVisitsAdjacent_equiv hn hP _ (visitShiftEquiv a P) (gaussCycle_shift hn hP a) v w

end SM
