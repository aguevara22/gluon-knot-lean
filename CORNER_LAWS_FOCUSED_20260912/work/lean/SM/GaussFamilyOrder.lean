import SM.CrossingTransport
import SM.GaussDefinition

/-! Actual visit comparisons in continuous preconnected generic families.
Crossings and edge labels are transported canonically; comparison of parameters
on a common edge is the already proved geometric chamber theorem. -/

namespace SM

variable {n : ℕ} {α : Type*} [TopologicalSpace α] [PreconnectedSpace α]

theorem generic_family_visitParameterOrder (hn : 3 ≤ n) {F : α → GenericTuple n}
    (hF : Continuous F) (s t : α) (v w : Visit (F s).val) (he : v.2.val = w.2.val) :
    visitParameter v < visitParameter w ↔
      visitParameter (visitTransport (generic_family_crossing_constant hn hF s t) v) <
      visitParameter (visitTransport (generic_family_crossing_constant hn hF s t) w) := by
  obtain ⟨j, _, hv⟩ := crossing_support_partner v.1 v.2.val v.2.property
  obtain ⟨k, _, hw⟩ := crossing_support_partner w.1 w.2.val w.2.property
  have hij : IsCrossing (F s).val {v.2.val, j} := by
    simpa only [hv] using v.1.property
  have hik : IsCrossing (F s).val {v.2.val, k} := by
    simpa only [hw, he] using w.1.property
  rw [visitParameter_eq_of_support_pair hn (F s).property.1 v j hv,
    visitParameter_eq_of_support_pair hn (F s).property.1 w k hw,
    visitParameter_eq_of_support_pair hn (F t).property.1
      (visitTransport (generic_family_crossing_constant hn hF s t) v) j hv,
    visitParameter_eq_of_support_pair hn (F t).property.1
      (visitTransport (generic_family_crossing_constant hn hF s t) w) k hw,
    visitTransport_edge, visitTransport_edge, ← he]
  exact generic_family_crossingOrder_constant hn hF s v.2.val j k hij hik s t

theorem generic_family_visitKey_lt (hn : 3 ≤ n) {F : α → GenericTuple n}
    (hF : Continuous F) (s t : α) (v w : Visit (F s).val) :
    visitKey hn (F s).property.1 v < visitKey hn (F s).property.1 w ↔
      visitKey hn (F t).property.1
        (visitTransport (generic_family_crossing_constant hn hF s t) v) <
      visitKey hn (F t).property.1
        (visitTransport (generic_family_crossing_constant hn hF s t) w) := by
  haveI : NeZero n := ⟨by omega⟩
  unfold visitKey
  rw [traversalKey_lt_iff, traversalKey_lt_iff]
  change (v.2.val.val < w.2.val.val ∨ v.2.val = w.2.val ∧
    visitParameter v < visitParameter w) ↔
    (v.2.val.val < w.2.val.val ∨ v.2.val = w.2.val ∧
      visitParameter (visitTransport (generic_family_crossing_constant hn hF s t) v) <
      visitParameter (visitTransport (generic_family_crossing_constant hn hF s t) w))
  exact or_congr Iff.rfl (and_congr_right (generic_family_visitParameterOrder hn hF s t v w))

theorem generic_family_visitKey_le (hn : 3 ≤ n) {F : α → GenericTuple n}
    (hF : Continuous F) (s t : α) (v w : Visit (F s).val) :
    visitKey hn (F s).property.1 v ≤ visitKey hn (F s).property.1 w ↔
      visitKey hn (F t).property.1
        (visitTransport (generic_family_crossing_constant hn hF s t) v) ≤
      visitKey hn (F t).property.1
        (visitTransport (generic_family_crossing_constant hn hF s t) w) := by
  simpa only [not_lt] using not_congr (generic_family_visitKey_lt hn hF s t w v)

end SM
