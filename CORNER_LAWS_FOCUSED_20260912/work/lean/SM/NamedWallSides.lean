import SM.WallCenterClassification
import SM.GermTurnSigns

/-! The printed F-side and V-contact-sign conventions are independent of
the point chosen on a germ side. V subtypes are determined by the centre. -/

namespace SM.WallGerm

variable {n : ℕ} [NeZero n] (g : WallGerm n)

def FlatRightSide (j : ZMod n) (b : Bool) : Prop :=
  ∀ t : g.SideParameter, turn (g.sideTuple b t).val j = -1

def FlatLeftSide (j : ZMod n) (b : Bool) : Prop :=
  ∀ t : g.SideParameter, turn (g.sideTuple b t).val j = 1

theorem flatRightSide_iff_at (j : ZMod n) (b : Bool) (t : g.SideParameter) :
    g.FlatRightSide j b ↔ turn (g.sideTuple b t).val j = -1 := by
  constructor
  · exact fun h => h t
  · intro h s
    exact (g.side_turn_constant b s t j).trans h

theorem flatLeftSide_iff_at (j : ZMod n) (b : Bool) (t : g.SideParameter) :
    g.FlatLeftSide j b ↔ turn (g.sideTuple b t).val j = 1 := by
  constructor
  · exact fun h => h t
  · intro h s
    exact (g.side_turn_constant b s t j).trans h

theorem flat_named_sides {j : ZMod n} (h : g.FlatAt j) :
    ∃! b : Bool, g.FlatRightSide j b ∧ g.FlatLeftSide j (!b) := by
  have hc := g.turn_signChanges_opposite h.2.2.2.2 g.sideBase g.sideBase
  have ho : turn (g.sideTuple false g.sideBase).val j =
      -turn (g.sideTuple true g.sideBase).val j := by rw [hc.1]; simp
  rcases signType_nonzero_cases hc.2 with hr | hl
  · have hr' := (g.flatRightSide_iff_at j true g.sideBase).mpr hr
    have hl' : g.FlatLeftSide j false :=
      (g.flatLeftSide_iff_at j false g.sideBase).mpr (by rw [ho, hr]; norm_num)
    refine ⟨true, ⟨hr', hl'⟩, ?_⟩
    intro b hb
    cases b
    · have hh := hb.1 g.sideBase
      rw [hl' g.sideBase] at hh
      norm_num at hh
    · rfl
  · have hl' := (g.flatLeftSide_iff_at j true g.sideBase).mpr hl
    have hr' : g.FlatRightSide j false :=
      (g.flatRightSide_iff_at j false g.sideBase).mpr (by rw [ho, hl])
    refine ⟨false, ⟨hr', hl'⟩, ?_⟩
    intro b hb
    cases b
    · rfl
    · have hh := hb.1 g.sideBase
      rw [hl' g.sideBase] at hh
      norm_num at hh

noncomputable def contactSign (M a : ZMod n) : SignType :=
  chi (g.sideTuple false g.sideBase).val a (a + 1) M

theorem contactSign_eq_at (M a : ZMod n) (t : g.SideParameter) :
    g.contactSign M a = chi (g.sideTuple false t).val a (a + 1) M :=
  generic_family_chi_constant (g.continuous_sideTuple false) g.sideBase t a (a + 1) M

theorem vertex_contact_signs {M a : ZMod n} (h : g.VertexEdgeAt M a)
    (s t : g.SideParameter) :
    g.contactSign M a ≠ 0 ∧
    chi (g.sideTuple false s).val a (a + 1) M = g.contactSign M a ∧
    chi (g.sideTuple true t).val a (a + 1) M = -g.contactSign M a := by
  obtain ⟨δ, hδ, hδr, hchange⟩ := h.2.2.2.2
  let t₀ : g.SideParameter := ⟨δ / 2, by constructor <;> linarith⟩
  have ht₀ : t₀.val < δ := by dsimp [t₀]; linarith
  have hc := (signType_cast_product_neg_iff _ _).mp (hchange t₀ ht₀)
  have hn : g.contactSign M a ≠ 0 := by
    intro hz
    have hf : chi (g.sideTuple false t₀).val a (a + 1) M = 0 :=
      (g.contactSign_eq_at M a t₀).symm.trans hz
    exact hc.2 (by rw [hc.1, hf]; simp)
  refine ⟨hn, (g.contactSign_eq_at M a s).symm, ?_⟩
  rw [generic_family_chi_constant (g.continuous_sideTuple true) t t₀ a (a + 1) M,
    hc.1, ← g.contactSign_eq_at M a t₀]

theorem vertex_marks_determined_by_center (hn : 3 ≤ n) {g' : WallGerm n}
    (he : g.center = g'.center) {M a N b : ZMod n}
    (h : g.VertexEdgeAt M a) (h' : g'.VertexEdgeAt N b) : M = N ∧ a = b := by
  apply contactSupport_marks_unique hn h.1 h'.1
  apply Finset.singleton_inj.mp
  calc
    {contactSupport M a} = pointZeroTriples g.center := h.2.1.symm
    _ = pointZeroTriples g'.center := congrArg pointZeroTriples he
    _ = {contactSupport N b} := h'.2.1

theorem vertex_subtype_determined_by_center (hn : 3 ≤ n) {g' : WallGerm n}
    (he : g.center = g'.center) {M a N b : ZMod n}
    (h : g.VertexEdgeAt M a) (h' : g'.VertexEdgeAt N b) :
    (g.BigonAt M a ↔ g'.BigonAt N b) ∧ (g.SlidingAt M a ↔ g'.SlidingAt N b) := by
  obtain ⟨rfl, rfl⟩ := g.vertex_marks_determined_by_center hn he h h'
  simp only [BigonAt, SlidingAt, h, h', true_and, he]

end SM.WallGerm
