import PhysicalSuffixCrossingData
import ActiveArcParentParameters
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.Split
open Cursor
attribute [local instance] Classical.propDecidable
variable {A a b : ℕ} (q : Fin (A+(a+b)+2) → PlanarPoint ℝ) (hR : Regular q)
    (θ : ℝ) (h0 : 0≤θ) (h1 : θ<1)
    (hM : Regular (moveStart (suffixWord q A (a+b) rfl) θ))
    (d : Crossing (moveStart (suffixWord q A (a+b) rfl) θ))
    (hdcut : d.val.2.val=a)

/-- Cutting the actual moved suffix leaves the literal original right-carrier
suffix with its head moved to the original right parameter. No closed diagram
is identified with this open physical word. -/
theorem physical_parent_eq_original_suffix :
    parent (moveStart (suffixWord q A (a+b) rfl) θ) d hdcut =
      moveStart (suffixWord q (A+a) b (by omega))
        (rightParameter q (suffixWordCrossingEquiv q hR A (a+b) rfl θ h0 h1 d).val) := by
  let z := (suffixWordCrossingEquiv q hR A (a+b) rfl θ h0 h1 d).val
  have hz : z.val.2.val=A+a := by
    rw [suffixWordCrossingEquiv_right_label,hdcut]
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rw [parent_zero,moveStart_zero]
    rw [← suffixWordCrossingEquiv_point q hR A (a+b) rfl θ h0 h1 d]
    change crossingPoint q z = _
    have he0 : suffixWord q (A+a) b (by omega) 0=q z.val.2.castSucc := by
      rw [suffixWord_vertex]
      congr 1
      apply Fin.ext
      simp [hz]
    have he1 : suffixWord q (A+a) b (by omega) 1=q z.val.2.succ := by
      rw [suffixWord_vertex]
      congr 1
      apply Fin.ext
      simp [hz]
    rw [he0,he1]
    exact (rightParameter_spec q z).2.2
  · rw [parent_succ,moveStart_succ]
    have ha : 0<a := by have := d.property.1;change d.val.1.val<d.val.2.val at this;omega
    have hne : vertex (a:=a) (b:=b) j.succ ≠ 0 := by
      intro he
      have hv := congrArg Fin.val he
      change a+(j.val+1)=0 at hv
      omega
    simp only [moveStart,Function.update_of_ne hne]
    rw [suffixWord_vertex,suffixWord_vertex]
    congr 1
    apply Fin.ext
    simp only [vertex,Fin.val_succ]
    omega

include hM hdcut in
/-- The right-carrier suffix is actual Regular, transported from the actual
physical parent; no Regular or word correspondence premise is added. -/
theorem original_right_suffix_regular :
    Regular (moveStart (suffixWord q (A+a) b (by omega))
      (rightParameter q (suffixWordCrossingEquiv q hR A (a+b) rfl θ h0 h1 d).val)) := by
  rw [← physical_parent_eq_original_suffix q hR θ h0 h1 d hdcut]
  exact regular_parent _ hM d hdcut
end DirectGLSSW.ActiveArc.Split
