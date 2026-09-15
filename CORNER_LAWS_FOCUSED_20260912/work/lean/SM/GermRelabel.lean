import SM.GermSignChange

/-! Fixed cyclic relabelling of the actual germ, its two genuine chambers,
and its real observables. The parameter interval is unchanged. -/

namespace SM.WallGerm

variable {n : ℕ} (g : WallGerm n)

def relabel (a : ZMod n) : WallGerm n where
  radius := g.radius
  radius_pos := g.radius_pos
  curve := fun t => shift a (g.curve t)
  continuous_curve := continuous_pi fun i => (continuous_apply (i + a)).comp g.continuous_curve
  generic_punctured := fun t ht => (generic_shift a _).mpr (g.generic_punctured t ht)
  nongeneric_center := fun h => g.nongeneric_center ((generic_shift a _).mp h)

theorem center_relabel (a : ZMod n) : (g.relabel a).center = shift a g.center := rfl

theorem relabel_zero_curve (t : g.Parameter) : (g.relabel 0).curve t = g.curve t :=
  shift_zero _

theorem relabel_add_curve (a b : ZMod n) (t : g.Parameter) :
    ((g.relabel b).relabel a).curve t = (g.relabel (a + b)).curve t :=
  shift_add a b _

theorem sideTuple_relabel (a : ZMod n) (positive : Bool) (t : g.SideParameter) :
    (g.relabel a).sideTuple positive t = genericShift a (g.sideTuple positive t) := rfl

theorem sidePolygon_relabel (a : ZMod n) (positive : Bool) (t : g.SideParameter) :
    (g.relabel a).sidePolygon positive t = g.sidePolygon positive t := by
  unfold sidePolygon
  rw [sideTuple_relabel, projection_genericShift]

theorem labelledSide_relabel (a : ZMod n) (positive : Bool) :
    genericShift a '' g.labelledSide positive = (g.relabel a).labelledSide positive := by
  unfold labelledSide
  rw [genericShift_labelledChamber]
  rfl

theorem side_relabel (a : ZMod n) (positive : Bool) :
    (g.relabel a).side positive = g.side positive :=
  congrArg chamber (g.sidePolygon_relabel a positive g.sideBase)

theorem sideValue_relabel {α : Type*} (F : GenericPolygon n → α)
    (a : ZMod n) (positive : Bool) :
    (g.relabel a).sideValue F positive = g.sideValue F positive :=
  congrArg F (g.sidePolygon_relabel a positive g.sideBase)

theorem signChanges_relabel (a : ZMod n) (φ : LabelledTuple n → ℝ) :
    (g.relabel a).SignChanges φ ↔ g.SignChanges (fun P => φ (shift a P)) := Iff.rfl

end SM.WallGerm
