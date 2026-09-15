import SM.GermRelabel
import SM.ZeroTripleRelabel

/-! Full source def:germ, its actual central degeneracy sets and cyclic
compatibility. No named-wall, transversality or differentiability hypothesis
is included in the basic germ domain. -/

namespace SM.WallGerm

variable {n : ℕ} [NeZero n] (g : WallGerm n)

noncomputable def pointZeros : Finset (Finset (ZMod n)) := pointZeroTriples g.center

noncomputable def concurrences : Finset (Finset (ZMod n)) := concurrenceTriples g.center

theorem mem_pointZeros (s : Finset (ZMod n)) :
    s ∈ g.pointZeros ↔ PointZeroTriple g.center s := mem_pointZeroTriples _ _

theorem mem_pointZeros_triple {i j k : ZMod n}
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    ({i, j, k} : Finset (ZMod n)) ∈ g.pointZeros ↔ chi g.center i j k = 0 := by
  rw [mem_pointZeros, pointZeroTriple_iff hij hjk hik]

theorem pointZeros_empty_iff : g.pointZeros = ∅ ↔ G1 g.center :=
  pointZeroTriples_empty_iff _

theorem mem_concurrences (s : Finset (ZMod n)) :
    s ∈ g.concurrences ↔ s.card = 3 ∧ (s : Set (ZMod n)).Pairwise remote ∧
      ∃ x : Plane, ∀ i ∈ s, x ∈ edgeInterior g.center i :=
  mem_concurrenceTriples _ _

theorem mem_concurrences_triple {i j k : ZMod n}
    (hij : remote i j) (hjk : remote j k) (hik : remote i k) :
    ({i, j, k} : Finset (ZMod n)) ∈ g.concurrences ↔
      ∃ x : Plane, x ∈ edgeInterior g.center i ∧ x ∈ edgeInterior g.center j ∧
        x ∈ edgeInterior g.center k :=
  (mem_concurrenceTriples g.center {i, j, k}).trans (concurrenceTriple_iff hij hjk hik)

theorem pointZeros_relabel (a : ZMod n) :
    (g.relabel a).pointZeros = g.pointZeros.image (translateSupport (-a)) :=
  pointZeroTriples_shift a _

theorem concurrences_relabel (a : ZMod n) :
    (g.relabel a).concurrences = g.concurrences.image (translateSupport (-a)) :=
  concurrenceTriples_shift a _

end WallGerm

variable {n : ℕ} [NeZero n]

/-- All clauses of the definition, including both actual chamber sides,
well-defined chamber-constant values, unordered central sets, local sign change
and the source's permitted labelled/equivariant interpretation. -/
theorem wall_germ_definition (hn : 3 ≤ n) (g : WallGerm n) :
    0 < g.radius ∧ Continuous g.curve ∧
    (∀ t : g.Parameter, t.val ≠ 0 → Generic (g.curve t)) ∧ ¬ Generic g.center ∧
    (∀ b : Bool, IsConnected (Set.range (g.sideTuple b)) ∧
      IsConnected (Set.range (g.sidePolygon b)) ∧
      (∀ t : g.SideParameter, g.sidePolygon b t ∈ g.side b) ∧
      (∀ t : g.SideParameter, g.side b = chamber (g.sidePolygon b t)) ∧
      (∀ Q : GenericPolygon n, (∀ t, g.sidePolygon b t ∈ chamber Q) → chamber Q = g.side b) ∧
      polygonProjection '' g.labelledSide b = g.side b) ∧
    (∀ {α : Type*} (F : GenericPolygon n → α), WallGerm.ConstantOnChambers F →
      ∀ b : Bool, ∀ t : g.SideParameter, g.sideValue F b = F (g.sidePolygon b t)) ∧
    (∀ s : Finset (ZMod n), s ∈ g.pointZeros ↔ PointZeroTriple g.center s) ∧
    (∀ i j k : ZMod n, i ≠ j → j ≠ k → i ≠ k →
      (({i, j, k} : Finset (ZMod n)) ∈ g.pointZeros ↔ chi g.center i j k = 0)) ∧
    (∀ s : Finset (ZMod n), s ∈ g.concurrences ↔
      s.card = 3 ∧ (s : Set (ZMod n)).Pairwise remote ∧
        ∃ x : Plane, ∀ i ∈ s, x ∈ edgeInterior g.center i) ∧
    (∀ φ : LabelledTuple n → ℝ, g.SignChanges φ ↔
      ∃ δ : ℝ, 0 < δ ∧ ∀ t : g.SideParameter, t.val < δ →
        φ (g.sideTuple true t).val * φ (g.sideTuple false t).val < 0) ∧
    (∀ a : ZMod n, (g.relabel a).center = shift a g.center ∧
      (∀ b : Bool, (g.relabel a).side b = g.side b) ∧
      (g.relabel a).pointZeros = g.pointZeros.image (translateSupport (-a)) ∧
      (g.relabel a).concurrences = g.concurrences.image (translateSupport (-a)) ∧
      (∀ φ : LabelledTuple n → ℝ, (g.relabel a).SignChanges φ ↔
        g.SignChanges (fun P => φ (shift a P)))) := by
  refine ⟨g.radius_pos, g.continuous_curve, g.generic_punctured, g.center_not_generic,
    ?_, ?_, g.mem_pointZeros, ?_, g.mem_concurrences, g.signChanges_iff_local, ?_⟩
  · intro b
    exact ⟨g.labelledSideRange_connected b, g.sideRange_connected b,
      g.sidePolygon_mem_side b, g.side_eq_at b, g.side_unique b, g.side_projection hn b⟩
  · intro α F hF b t
    exact g.sideValue_eq_at hF b t
  · intro i j k hij hjk hik
    exact g.mem_pointZeros_triple hij hjk hik
  · intro a
    exact ⟨g.center_relabel a, g.side_relabel a, g.pointZeros_relabel a,
      g.concurrences_relabel a, g.signChanges_relabel a⟩

end SM
