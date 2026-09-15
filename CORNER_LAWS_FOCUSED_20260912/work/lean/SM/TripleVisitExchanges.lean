import SM.TripleSideExchanges
import SM.CrossingTransport

/-! Every same-edge comparison of actual visits is accounted for: exactly
the triangle pairs reverse, and every other pair retains its order. -/

namespace SM

variable {n : ℕ} [NeZero n]

def ExactTriangleParameterOrders (P Q : LabelledTuple n) (e f g : ZMod n) : Prop :=
  ∀ i j k : ZMod n, IsCrossing P {i, j} → IsCrossing P {i, k} →
    (({i, j, k} : Finset (ZMod n)) = {e, f, g} →
      (edgeParameter P i j < edgeParameter P i k ↔ edgeParameter Q i k < edgeParameter Q i j)) ∧
    (({i, j, k} : Finset (ZMod n)) ≠ {e, f, g} →
      (edgeParameter P i j < edgeParameter P i k ↔ edgeParameter Q i j < edgeParameter Q i k))

def ExactTriangleVisitOrders (P Q : LabelledTuple n) (e f g : ZMod n)
    (hs : ∀ s, IsCrossing P s ↔ IsCrossing Q s) : Prop :=
  ∀ v w : Visit P, v.2.val = w.2.val →
    (v.1.val ∪ w.1.val = {e, f, g} →
      (visitParameter v < visitParameter w ↔
        visitParameter (visitTransport hs w) < visitParameter (visitTransport hs v))) ∧
    (v.1.val ∪ w.1.val ≠ {e, f, g} →
      (visitParameter v < visitParameter w ↔
        visitParameter (visitTransport hs v) < visitParameter (visitTransport hs w)))

theorem exactTriangleVisitOrders_of_parameters (hn : 3 ≤ n)
    {P Q : LabelledTuple n} (hP : G1 P) (hQ : G1 Q) {e f g : ZMod n}
    (hs : ∀ s, IsCrossing P s ↔ IsCrossing Q s)
    (ho : ExactTriangleParameterOrders P Q e f g) : ExactTriangleVisitOrders P Q e f g hs := by
  intro v w he
  obtain ⟨j, _, hv⟩ := crossing_support_partner v.1 v.2.val v.2.property
  obtain ⟨k, _, hw⟩ := crossing_support_partner w.1 w.2.val w.2.property
  have hij : IsCrossing P {v.2.val, j} := by simpa only [hv] using v.1.property
  have hik : IsCrossing P {v.2.val, k} := by simpa only [hw, he] using w.1.property
  have hu : v.1.val ∪ w.1.val = {v.2.val, j, k} := by
    calc
      v.1.val ∪ w.1.val = {v.2.val, j} ∪ {w.2.val, k} :=
        congrArg₂ (fun x y : Finset (ZMod n) => x ∪ y) hv hw
      _ = {v.2.val, j, k} := by
        rw [← he]
        ext x
        simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
        tauto
  rw [visitParameter_eq_of_support_pair hn hP v j hv,
    visitParameter_eq_of_support_pair hn hP w k hw,
    visitParameter_eq_of_support_pair hn hQ (visitTransport hs v) j hv,
    visitParameter_eq_of_support_pair hn hQ (visitTransport hs w) k hw,
    visitTransport_edge, visitTransport_edge, ← he, hu]
  exact ho _ j k hij hik

namespace WallGerm

theorem triple_sides_crossing_equiv (hn : 3 ≤ n) (g : WallGerm n) {e f k : ZMod n}
    (h : g.TripleAt e f k) (s t : g.SideParameter) :
    ∀ c, IsCrossing (g.sideTuple true s).val c ↔ IsCrossing (g.sideTuple false t).val c := by
  intro c
  have hG1 : G1 g.center := (g.pointZeros_empty_iff).mp h.1
  exact (g.g1_center_side_crossings hn hG1 true s c).trans
    (g.g1_center_side_crossings hn hG1 false t c).symm

theorem triple_exact_parameter_orders (hn : 3 ≤ n) (g : WallGerm n) {e f k : ZMod n}
    (h : g.TripleAt e f k) (s t : g.SideParameter) :
    ExactTriangleParameterOrders (g.sideTuple true s).val (g.sideTuple false t).val e f k := by
  have hG1 : G1 g.center := (g.pointZeros_empty_iff).mp h.1
  have hswap := g.triple_order_exchanges hn h s t
  have hplus := g.triple_other_orders_sides hn h true s
  have hminus := g.triple_other_orders_sides hn h false t
  have hm : ({e, f, k} : Finset (ZMod n)) ∈ concurrenceTriples g.center := by
    have hc : concurrenceTriples g.center = {{e, f, k}} := h.2.1
    rw [hc]; simp
  have hcard := ((mem_concurrenceTriples g.center _).mp hm).1
  intro i j l hij hil
  constructor
  · intro heq
    have hd : i ≠ j ∧ i ≠ l ∧ j ≠ l :=
      Finset.card_triple_eq_three_iff.mp (by rw [heq]; exact hcard)
    exact triangleOrderExchanges_all hswap hd.1 hd.2.1 hd.2.2 heq
  · intro hnot
    have hij0 := (g.g1_center_side_crossings hn hG1 true s _).mp hij
    have hil0 := (g.g1_center_side_crossings hn hG1 true s _).mp hil
    exact (hplus i j l hij0 hil0 hnot).trans (hminus i j l hij0 hil0 hnot).symm

theorem triple_exact_visit_orders (hn : 3 ≤ n) (g : WallGerm n) {e f k : ZMod n}
    (h : g.TripleAt e f k) (s t : g.SideParameter) :
    ExactTriangleVisitOrders (g.sideTuple true s).val (g.sideTuple false t).val e f k
      (g.triple_sides_crossing_equiv hn h s t) :=
  exactTriangleVisitOrders_of_parameters hn (g.sideTuple true s).property.1
    (g.sideTuple false t).property.1 (g.triple_sides_crossing_equiv hn h s t)
    (g.triple_exact_parameter_orders hn h s t)

end WallGerm
end SM
