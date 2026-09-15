import SM.ChamberPaths
import SM.CyclicChambers
import Mathlib.Topology.Order.IntermediateValue

/-! Actual continuous germs on their open parameter interval. Both punctured
sides use a positive distance parameter, with the negative side evaluated at
its negative. No global extension or differentiability is required. -/

namespace SM

open Set Topology

structure WallGerm (n : ℕ) where
  radius : ℝ
  radius_pos : 0 < radius
  curve : Set.Ioo (-radius) radius → LabelledTuple n
  continuous_curve : Continuous curve
  generic_punctured : ∀ t, t.val ≠ 0 → Generic (curve t)
  nongeneric_center : ¬ Generic (curve ⟨0, by constructor <;> linarith [radius_pos]⟩)

namespace WallGerm

variable {n : ℕ} (g : WallGerm n)

abbrev Parameter := Set.Ioo (-g.radius) g.radius
abbrev SideParameter := Set.Ioo 0 g.radius

def zeroParameter : g.Parameter := ⟨0, by constructor <;> linarith [g.radius_pos]⟩

def center : LabelledTuple n := g.curve g.zeroParameter

theorem center_not_generic : ¬ Generic g.center := g.nongeneric_center

def sideTime (positive : Bool) (t : g.SideParameter) : g.Parameter :=
  if positive then ⟨t.val, by constructor <;> linarith [t.property.1, t.property.2, g.radius_pos]⟩
  else ⟨-t.val, by constructor <;> linarith [t.property.1, t.property.2, g.radius_pos]⟩

theorem sideTime_ne_zero (positive : Bool) (t : g.SideParameter) :
    (g.sideTime positive t).val ≠ 0 := by
  cases positive <;> simp only [sideTime, Bool.false_eq_true, ↓reduceIte]
  · exact neg_ne_zero.mpr t.property.1.ne'
  · exact t.property.1.ne'

theorem continuous_sideTime (positive : Bool) : Continuous (g.sideTime positive) := by
  cases positive
  · exact continuous_subtype_val.neg.subtype_mk _
  · exact continuous_subtype_val.subtype_mk _

def sideTuple (positive : Bool) (t : g.SideParameter) : GenericTuple n :=
  ⟨g.curve (g.sideTime positive t), g.generic_punctured _ (g.sideTime_ne_zero positive t)⟩

theorem continuous_sideTuple (positive : Bool) : Continuous (g.sideTuple positive) :=
  (g.continuous_curve.comp (g.continuous_sideTime positive)).subtype_mk _

def sidePolygon (positive : Bool) (t : g.SideParameter) : GenericPolygon n :=
  polygonProjection (g.sideTuple positive t)

theorem continuous_sidePolygon (positive : Bool) : Continuous (g.sidePolygon positive) :=
  continuous_quot_mk.comp (g.continuous_sideTuple positive)

noncomputable def sideBase : g.SideParameter :=
  ⟨g.radius / 2, by constructor <;> linarith [g.radius_pos]⟩

/-- The actual half interval is covered, including every negative parameter. -/
theorem sideTime_surjective_punctured (t : g.Parameter) (ht : t.val ≠ 0) :
    ∃ positive : Bool, ∃ s : g.SideParameter, g.sideTime positive s = t := by
  rcases lt_or_gt_of_ne ht with hn | hp
  · refine ⟨false, ⟨-t.val, by constructor <;> linarith [t.property.1]⟩, ?_⟩
    apply Subtype.ext
    simp [sideTime]
  · refine ⟨true, ⟨t.val, hp, t.property.2⟩, ?_⟩
    rfl

end WallGerm
end SM
