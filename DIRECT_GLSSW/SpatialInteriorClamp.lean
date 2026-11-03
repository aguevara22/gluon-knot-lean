import SplitEndpointGerms
import ActualSplitAvoidance

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.DescendingSpatial
open HOMFLY

/-- Literal clipping to an interior interval, with no geometric conclusions stored. -/
def interiorClamp (a : ℝ) (ha : 0 < a) (ha' : a < 1/2) : C(unitInterval,unitInterval) where
  toFun t := ⟨min (max t.val a) (1-a),by
    constructor
    · exact le_min (le_trans ha.le (le_max_right _ _)) (by linarith)
    · exact (min_le_right _ _).trans (by linarith)⟩
  continuous_toFun := by fun_prop

theorem interiorClamp_apply (a : ℝ) (ha : 0 < a) (ha' : a < 1/2)
    (t : unitInterval) : (interiorClamp a ha ha' t).val = min (max t.val a) (1-a) := rfl

theorem interiorClamp_bounds (a : ℝ) (ha : 0 < a) (ha' : a < 1/2)
    (t : unitInterval) : a ≤ (interiorClamp a ha ha' t).val ∧
      (interiorClamp a ha ha' t).val ≤ 1-a := by
  constructor
  · exact le_min (le_max_right _ _) (by linarith)
  · exact min_le_right _ _

theorem interiorClamp_left (a : ℝ) (ha : 0 < a) (ha' : a < 1/2)
    (t : unitInterval) (ht : t.val ≤ a) : (interiorClamp a ha ha' t).val = a := by
  rw [interiorClamp_apply,max_eq_right ht,min_eq_left (by linarith : a ≤ 1-a)]

theorem interiorClamp_right (a : ℝ) (ha : 0 < a) (ha' : a < 1/2)
    (t : unitInterval) (ht : 1-a ≤ t.val) : (interiorClamp a ha ha' t).val = 1-a := by
  rw [interiorClamp_apply,max_eq_left (by linarith : a ≤ t.val),min_eq_right ht]

theorem interiorClamp_middle (a : ℝ) (ha : 0 < a) (ha' : a < 1/2)
    (t : unitInterval) (ht : a ≤ t.val) (ht' : t.val ≤ 1-a) :
    interiorClamp a ha ha' t = t := by
  apply Subtype.ext
  rw [interiorClamp_apply,max_eq_left ht,min_eq_left ht']

def splitClampWidth (D : PLLinkDiagram) (e : Fin D.nArc) : ℝ :=
  1/(2*((componentArcLength D e:ℝ)+1))

theorem splitClampWidth_eq_literal (D : PLLinkDiagram) (e : Fin D.nArc) :
    splitClampWidth D e = 1/(2*((componentArcLength D e:ℝ)+1)) := rfl

theorem splitClampWidth_bounds (D : PLLinkDiagram) (e : Fin D.nArc) :
    0 < splitClampWidth D e ∧ splitClampWidth D e < 1/2 ∧
      ((componentArcLength D e:ℝ)+1)*splitClampWidth D e = 1/2 := by
  have hm : (0:ℝ) < componentArcLength D e := by exact_mod_cast componentArcLength_pos D e
  have hn : ((componentArcLength D e:ℝ)+1) ≠ 0 := by positivity
  unfold splitClampWidth
  refine ⟨by positivity,?_,?_⟩
  · apply (div_lt_iff₀ (by positivity)).mpr
    linarith
  · field_simp
    ring

def splitClamp (D : PLLinkDiagram) (e : Fin D.nArc) : C(unitInterval,unitInterval) :=
  interiorClamp (splitClampWidth D e) (splitClampWidth_bounds D e).1 (splitClampWidth_bounds D e).2.1

theorem splitClamp_apply (D : PLLinkDiagram) (e : Fin D.nArc) (t : unitInterval) :
    (splitClamp D e t).val = min (max t.val (splitClampWidth D e)) (1-splitClampWidth D e) := rfl

theorem splitClamp_interior (D : PLLinkDiagram) (e : Fin D.nArc) (t : unitInterval) :
    0 < (splitClamp D e t).val ∧ (splitClamp D e t).val < 1 := by
  have h := interiorClamp_bounds (splitClampWidth D e) (splitClampWidth_bounds D e).1
    (splitClampWidth_bounds D e).2.1 t
  change splitClampWidth D e ≤ (splitClamp D e t).val ∧
    (splitClamp D e t).val ≤ 1-splitClampWidth D e at h
  have ha := (splitClampWidth_bounds D e).1
  constructor <;> linarith

end DirectGLSSW.DescendingSpatial









