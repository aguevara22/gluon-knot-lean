import SM.WallRelabelGeometry

/-! Every printed named-wall predicate and the F/V side conventions are
equivariant under the actual parent cyclic shift, with marks translated by -r. -/

namespace SM.WallGerm

variable {n : ℕ} [NeZero n] (g : WallGerm n)

theorem flatAt_relabel (r j : ZMod n) :
    (g.relabel r).FlatAt (j - r) ↔ g.FlatAt j := by
  have hz := g.pointZeros_relabel_singleton r (turnSupport j)
  rw [translateSupport_turn] at hz
  simp only [FlatAt, hz, g.concurrences_relabel_empty, g.center_relabel,
    g.signChanges_relabel, turn_shift, sub_add_cancel]
  simp only [shift, sub_add_cancel, wall_sub_add_cancel_right, wall_sub_sub_cancel_right]

theorem cuspAt_relabel (r j : ZMod n) :
    (g.relabel r).CuspAt (j - r) ↔ g.CuspAt j := by
  have hz := g.pointZeros_relabel_singleton r (turnSupport j)
  rw [translateSupport_turn] at hz
  simp only [CuspAt, hz, g.concurrences_relabel_empty, g.center_relabel,
    g.signChanges_relabel, turn_shift, sub_add_cancel]
  simp only [shift, sub_add_cancel, wall_sub_add_cancel_right, wall_sub_sub_cancel_right]

theorem vertexEdgeAt_relabel (r M a : ZMod n) :
    (g.relabel r).VertexEdgeAt (M - r) (a - r) ↔ g.VertexEdgeAt M a := by
  have hz := g.pointZeros_relabel_singleton r (contactSupport M a)
  rw [translateSupport_contact] at hz
  simp only [VertexEdgeAt, contactSeparated_sub, hz, g.concurrences_relabel_empty,
    g.center_relabel, g.signChanges_relabel, edgeInterior_shift, chi_shift, sub_add_cancel]
  simp only [shift, sub_add_cancel, wall_sub_add_cancel_right, wall_sub_sub_cancel_right]

theorem extensionAt_relabel (r M a : ZMod n) :
    (g.relabel r).ExtensionAt (M - r) (a - r) ↔ g.ExtensionAt M a := by
  have hz := g.pointZeros_relabel_singleton r (contactSupport M a)
  rw [translateSupport_contact] at hz
  simp only [ExtensionAt, contactSeparated_sub, hz, g.concurrences_relabel_empty,
    g.center_relabel, g.signChanges_relabel, edgePoint_shift, edgeSegment_shift,
    chi_shift, sub_add_cancel]
  simp only [shift, sub_add_cancel, wall_sub_add_cancel_right, wall_sub_sub_cancel_right]

theorem tripleAt_relabel (r e f k : ZMod n) :
    (g.relabel r).TripleAt (e - r) (f - r) (k - r) ↔ g.TripleAt e f k := by
  have hz := g.concurrences_relabel_singleton r {e, f, k}
  rw [translateSupport_three] at hz
  simp only [TripleAt, g.pointZeros_relabel_empty, hz, g.signChanges_relabel,
    edgeParameter_shift, sub_add_cancel]

theorem pureCutAt_relabel (r i j k : ZMod n) :
    (g.relabel r).PureCutAt (i - r) (j - r) (k - r) ↔ g.PureCutAt i j k := by
  have hz := g.pointZeros_relabel_singleton r {i, j, k}
  rw [translateSupport_three] at hz
  have hno := noConsecutive_translate (-r) ({i, j, k} : Finset (ZMod n))
  rw [translateSupport_three] at hno
  simp only [PureCutAt, hno, hz, g.concurrences_relabel_empty, g.signChanges_relabel,
    chi_shift, sub_add_cancel]

theorem bigonAt_relabel (r M a : ZMod n) :
    (g.relabel r).BigonAt (M - r) (a - r) ↔ g.BigonAt M a := by
  simp only [BigonAt, g.vertexEdgeAt_relabel, g.center_relabel, chi_shift, sub_add_cancel]
  simp only [wall_sub_add_cancel_right, wall_sub_sub_cancel_right]

theorem slidingAt_relabel (r M a : ZMod n) :
    (g.relabel r).SlidingAt (M - r) (a - r) ↔ g.SlidingAt M a := by
  simp only [SlidingAt, g.vertexEdgeAt_relabel, g.center_relabel, chi_shift, sub_add_cancel]
  simp only [wall_sub_add_cancel_right, wall_sub_sub_cancel_right]

theorem flatRightSide_relabel (r j : ZMod n) (b : Bool) :
    (g.relabel r).FlatRightSide (j - r) b ↔ g.FlatRightSide j b := by
  change (∀ t : g.SideParameter, turn (shift r (g.sideTuple b t).val) (j - r) = -1) ↔ _
  simp only [turn_shift, sub_add_cancel, FlatRightSide]

theorem flatLeftSide_relabel (r j : ZMod n) (b : Bool) :
    (g.relabel r).FlatLeftSide (j - r) b ↔ g.FlatLeftSide j b := by
  change (∀ t : g.SideParameter, turn (shift r (g.sideTuple b t).val) (j - r) = 1) ↔ _
  simp only [turn_shift, sub_add_cancel, FlatLeftSide]

theorem contactSign_relabel (r M a : ZMod n) :
    (g.relabel r).contactSign (M - r) (a - r) = g.contactSign M a := by
  change chi (shift r (g.sideTuple false g.sideBase).val) (a - r) (a - r + 1) (M - r) = _
  simp only [chi_shift, sub_add_cancel, wall_sub_add_cancel_right, contactSign]

end SM.WallGerm
