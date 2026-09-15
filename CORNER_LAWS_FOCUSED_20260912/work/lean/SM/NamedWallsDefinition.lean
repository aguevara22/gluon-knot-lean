import SM.WallKindRelabel

/-! Full source def:walls, sm-1-polygons.tex:710–750. The exact central
conditions, real sign changes, named sides and actual Gauss-word convention
are bound together with proved exclusivity and representative independence.
This does not classify arbitrary singularities or assert polynomial wall laws. -/

namespace SM

variable {n : ℕ} [NeZero n]

structure NamedWallsData (hn : 3 ≤ n) (g : WallGerm n) : Prop where
  flat_predicate : ∀ j, g.FlatAt j ↔ FlatCenterAt g.center j ∧
    g.SignChanges (fun P => (turn P j : ℝ))
  cusp_predicate : ∀ j, g.CuspAt j ↔ CuspCenterAt g.center j ∧
    g.SignChanges (fun P => (turn P j : ℝ))
  vertex_predicate : ∀ M a, g.VertexEdgeAt M a ↔ VertexCenterAt g.center M a ∧
    g.SignChanges (fun P => (chi P a (a + 1) M : ℝ))
  triple_predicate : ∀ e f k, g.TripleAt e f k ↔ TripleCenterAt g.center e f k ∧
    g.SignChanges (fun P => edgeParameter P e f - edgeParameter P e k) ∧
    g.SignChanges (fun P => edgeParameter P f e - edgeParameter P f k) ∧
    g.SignChanges (fun P => edgeParameter P k e - edgeParameter P k f)
  extension_predicate : ∀ M a, g.ExtensionAt M a ↔ ExtensionCenterAt g.center M a ∧
    g.SignChanges (fun P => (chi P a (a + 1) M : ℝ))
  cut_predicate : ∀ i j k, g.PureCutAt i j k ↔ CutCenterAt g.center i j k ∧
    g.SignChanges (fun P => (chi P i j k : ℝ))
  simplicity : g.Simple ↔ ∃ kind : WallKind, g.HasWallKind kind
  exclusivity : ∀ a b : WallKind, g.HasWallKind a → g.HasWallKind b → a = b
  unique_kind : g.Simple → ∃! kind : WallKind, g.HasWallKind kind
  centre_determination : ∀ g' : WallGerm n, g.center = g'.center →
    ∀ a b : WallKind, g.HasWallKind a → g'.HasWallKind b → a = b
  flat_sides : ∀ j, g.FlatAt j →
    ∃! b : Bool, g.FlatRightSide j b ∧ g.FlatLeftSide j (!b)
  flat_right : ∀ j b, ∀ t : g.SideParameter,
    g.FlatRightSide j b ↔ turn (g.sideTuple b t).val j = -1
  flat_left : ∀ j b, ∀ t : g.SideParameter,
    g.FlatLeftSide j b ↔ turn (g.sideTuple b t).val j = 1
  cusp_collinear : ∀ j, g.CuspAt j → turn g.center j = 0
  cusp_case : ∀ j, g.CuspAt j → ∃! b : Bool, CuspCase g.center j b
  newborn_A : ∀ j : ZMod n, cuspFirst true j = j - 1 ∧ cuspLast true j = j + 1
  newborn_B : ∀ j : ZMod n, cuspFirst false j = j - 2 ∧ cuspLast false j = j
  cusp_loop : ∀ j, ∀ h : g.CuspAt j, ∀ b : Bool, CuspCase g.center j b →
    ∀ side : Bool, ∀ t : g.SideParameter,
      IsCrossing (g.sideTuple side t).val {cuspFirst b j, cuspLast b j} ↔ side = g.cuspLoopSide b j
  cusp_no_loop : ∀ j, ∀ h : g.CuspAt j, ∀ b : Bool, CuspCase g.center j b →
    ∀ t : g.SideParameter,
      ¬ IsCrossing (g.sideTuple (!(g.cuspLoopSide b j)) t).val {cuspFirst b j, cuspLast b j}
  cusp_empty : ∀ j, ∀ h : g.CuspAt j, ∀ b : Bool, ∀ hc : CuspCase g.center j b,
    ∀ t : g.SideParameter, g.CuspEmptyAt j ↔
      GaussVisitsAdjacent hn (g.sideTuple (g.cuspLoopSide b j) t).property
        (twoStepFirstVisit (g.cusp_loop_crossing h hc t))
        (twoStepLastVisit (g.cusp_loop_crossing h hc t))
  vertex_subtypes : ∀ M a, g.VertexEdgeAt M a →
    (g.BigonAt M a ∨ g.SlidingAt M a) ∧ ¬ (g.BigonAt M a ∧ g.SlidingAt M a)
  vertex_subtype_centre : ∀ g' : WallGerm n, g.center = g'.center →
    ∀ M a N b, g.VertexEdgeAt M a → g'.VertexEdgeAt N b →
      (M = N ∧ a = b) ∧ (g.BigonAt M a ↔ g'.BigonAt N b) ∧
        (g.SlidingAt M a ↔ g'.SlidingAt N b)
  contact_sign : ∀ M a, g.VertexEdgeAt M a → ∀ s t : g.SideParameter,
    g.contactSign M a ≠ 0 ∧
      chi (g.sideTuple false s).val a (a + 1) M = g.contactSign M a ∧
      chi (g.sideTuple true t).val a (a + 1) M = -g.contactSign M a
  silent : g.Silent ↔ g.HasWallKind .extension ∨ g.HasWallKind .cut
  unordered_triple : ∀ e f k i j l,
    ({i, j, l} : Finset (ZMod n)) = {e, f, k} → (g.TripleAt i j l ↔ g.TripleAt e f k)
  unordered_cut : ∀ e f k i j l,
    ({i, j, l} : Finset (ZMod n)) = {e, f, k} → (g.PureCutAt i j l ↔ g.PureCutAt e f k)
  relabel_flat : ∀ r j, (g.relabel r).FlatAt (j - r) ↔ g.FlatAt j
  relabel_cusp : ∀ r j, (g.relabel r).CuspAt (j - r) ↔ g.CuspAt j
  relabel_vertex : ∀ r M a, (g.relabel r).VertexEdgeAt (M - r) (a - r) ↔ g.VertexEdgeAt M a
  relabel_triple : ∀ r e f k, (g.relabel r).TripleAt (e - r) (f - r) (k - r) ↔ g.TripleAt e f k
  relabel_extension : ∀ r M a, (g.relabel r).ExtensionAt (M - r) (a - r) ↔ g.ExtensionAt M a
  relabel_cut : ∀ r i j k, (g.relabel r).PureCutAt (i - r) (j - r) (k - r) ↔ g.PureCutAt i j k
  relabel_right : ∀ r j b, (g.relabel r).FlatRightSide (j - r) b ↔ g.FlatRightSide j b
  relabel_left : ∀ r j b, (g.relabel r).FlatLeftSide (j - r) b ↔ g.FlatLeftSide j b
  relabel_case : ∀ r j b, CuspCase (g.relabel r).center (j - r) b ↔ CuspCase g.center j b
  relabel_newborn : ∀ r j : ZMod n, ∀ b : Bool, cuspFirst b (j - r) = cuspFirst b j - r ∧
    cuspLast b (j - r) = cuspLast b j - r
  relabel_loop : ∀ r j b, (g.relabel r).cuspLoopSide b (j - r) = g.cuspLoopSide b j
  relabel_empty : ∀ r j, (g.relabel r).CuspEmptyAt (j - r) ↔ g.CuspEmptyAt j
  relabel_bigon : ∀ r M a, (g.relabel r).BigonAt (M - r) (a - r) ↔ g.BigonAt M a
  relabel_sliding : ∀ r M a, (g.relabel r).SlidingAt (M - r) (a - r) ↔ g.SlidingAt M a
  relabel_sign : ∀ r M a, (g.relabel r).contactSign (M - r) (a - r) = g.contactSign M a
  relabel_kind : ∀ r kind, (g.relabel r).HasWallKind kind ↔ g.HasWallKind kind
  relabel_simple : ∀ r, (g.relabel r).Simple ↔ g.Simple
  relabel_silent : ∀ r, (g.relabel r).Silent ↔ g.Silent

theorem named_walls_data (hn : 3 ≤ n) (g : WallGerm n) : NamedWallsData hn g where
  flat_predicate := by
    intro j
    simp only [WallGerm.FlatAt, FlatCenterAt, WallGerm.pointZeros, WallGerm.concurrences, and_assoc]
  cusp_predicate := by
    intro j
    simp only [WallGerm.CuspAt, CuspCenterAt, WallGerm.pointZeros, WallGerm.concurrences, and_assoc]
  vertex_predicate := by
    intro M a
    simp only [WallGerm.VertexEdgeAt, VertexCenterAt, WallGerm.pointZeros, WallGerm.concurrences, and_assoc]
  triple_predicate := by
    intro e f k
    simp only [WallGerm.TripleAt, TripleCenterAt, WallGerm.pointZeros, WallGerm.concurrences, and_assoc]
  extension_predicate := by
    intro M a
    simp only [WallGerm.ExtensionAt, ExtensionCenterAt, WallGerm.pointZeros, WallGerm.concurrences, and_assoc]
  cut_predicate := by
    intro i j k
    simp only [WallGerm.PureCutAt, CutCenterAt, WallGerm.pointZeros, WallGerm.concurrences, and_assoc]
  simplicity := Iff.rfl
  exclusivity := fun _ _ ha hb => g.wallKinds_mutually_exclusive hn ha hb
  unique_kind := g.simple_has_unique_kind hn
  centre_determination := fun _ he _ _ ha hb => WallGerm.wallKind_determined_by_center hn he ha hb
  flat_sides := fun _ h => g.flat_named_sides h
  flat_right := g.flatRightSide_iff_at
  flat_left := g.flatLeftSide_iff_at
  cusp_collinear := fun _ h => singlePointTriple_turn_zero h.2.1
  cusp_case := fun _ h => g.cusp_case_existsUnique h
  newborn_A := fun j => ⟨(cusp_indices_A j).1, (cusp_indices_A j).2.1⟩
  newborn_B := fun j => ⟨(cusp_indices_B j).1, (cusp_indices_B j).2.1⟩
  cusp_loop := fun _ h _ hc side t => g.cusp_side_crossing_iff_loop h hc side t
  cusp_no_loop := fun _ h _ hc t => g.cusp_no_loop_crossing h hc t
  cusp_empty := fun _ h _ hc t => g.cuspEmptyAt_iff_at h hc t
  vertex_subtypes := fun _ _ h => ⟨g.vertexEdge_bigon_or_sliding h,
    fun hh => g.bigon_not_sliding hh.1 hh.2⟩
  vertex_subtype_centre := fun _ he _ _ _ _ h h' =>
    ⟨g.vertex_marks_determined_by_center hn he h h', g.vertex_subtype_determined_by_center hn he h h'⟩
  contact_sign := fun _ _ h s t => g.vertex_contact_signs h s t
  silent := Iff.rfl
  unordered_triple := fun _ _ _ _ _ _ he => g.tripleAt_support_iff he
  unordered_cut := fun _ _ _ _ _ _ he => g.pureCutAt_support_iff he
  relabel_flat := g.flatAt_relabel
  relabel_cusp := g.cuspAt_relabel
  relabel_vertex := g.vertexEdgeAt_relabel
  relabel_triple := g.tripleAt_relabel
  relabel_extension := g.extensionAt_relabel
  relabel_cut := g.pureCutAt_relabel
  relabel_right := g.flatRightSide_relabel
  relabel_left := g.flatLeftSide_relabel
  relabel_case := g.cuspCase_relabel
  relabel_newborn := fun r j b => ⟨cuspFirst_sub r j b, cuspLast_sub r j b⟩
  relabel_loop := g.cuspLoopSide_relabel
  relabel_empty := g.cuspEmptyAt_relabel
  relabel_bigon := g.bigonAt_relabel
  relabel_sliding := g.slidingAt_relabel
  relabel_sign := g.contactSign_relabel
  relabel_kind := g.hasWallKind_relabel
  relabel_simple := g.simple_relabel
  relabel_silent := g.silent_relabel

def NamedWallsDefinitionData : Prop :=
  ∀ n : ℕ, ∀ _ : NeZero n, ∀ hn : 3 ≤ n, ∀ g : WallGerm n, NamedWallsData hn g

theorem named_walls_definition : NamedWallsDefinitionData :=
  fun _ _ hn g => named_walls_data hn g

end SM
