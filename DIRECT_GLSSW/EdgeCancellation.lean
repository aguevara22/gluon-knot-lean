import TriangleOriginBalance
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Logic.Equiv.Fin.Rotate

set_option autoImplicit false

namespace DirectGLSSW.HOMFLY.PrincipalTurning

theorem segment_arg_reverse (a b : ℂ)
    (h : (0 : ℂ) ∉ segment ℝ a b) :
    Complex.arg (a / b) = -Complex.arg (b / a) := by
  have ha : a ≠ 0 := fun he => h (he ▸ left_mem_segment ℝ a b)
  have hb : b ≠ 0 := fun he => h (he ▸ right_mem_segment ℝ a b)
  have hlt : Complex.arg (b / a) < Real.pi :=
    segment_avoids_zero_arg_lt_pi a b h
  have hratio : a / b = (b / a)⁻¹ := by
    field_simp [ha, hb]
  rw [hratio, Complex.arg_inv, if_neg (ne_of_lt hlt)]

abbrev TriangleEdgeIndex (T : Type) := T × Fin 3

def triangleEdgeStart {T : Type} (p : T → Fin 3 → ℂ)
    (e : TriangleEdgeIndex T) : ℂ := p e.1 e.2

def triangleEdgeFinish {T : Type} (p : T → Fin 3 → ℂ)
    (e : TriangleEdgeIndex T) : ℂ := p e.1 (finRotate 3 e.2)

noncomputable def triangleEdgeIncrement {T : Type} (p : T → Fin 3 → ℂ)
    (e : TriangleEdgeIndex T) : ℝ :=
  Complex.arg (triangleEdgeFinish p e / triangleEdgeStart p e)

theorem nonfixed_edge_angles_cancel {T : Type} [Fintype T] [DecidableEq T]
    (p : T → Fin 3 → ℂ)
    (rev : TriangleEdgeIndex T → TriangleEdgeIndex T)
    (hinv : ∀ e, rev (rev e) = e)
    (hstart : ∀ e, rev e ≠ e →
      triangleEdgeStart p (rev e) = triangleEdgeFinish p e)
    (hfinish : ∀ e, rev e ≠ e →
      triangleEdgeFinish p (rev e) = triangleEdgeStart p e)
    (havoid : ∀ e, (0 : ℂ) ∉ segment ℝ (triangleEdgeStart p e)
      (triangleEdgeFinish p e)) :
    ∑ e ∈ (Finset.univ.filter (fun e : TriangleEdgeIndex T => rev e ≠ e)),
      triangleEdgeIncrement p e = 0 := by
  classical
  let S : Finset (TriangleEdgeIndex T) :=
    Finset.univ.filter (fun e => rev e ≠ e)
  have hreverse : ∀ e, e ∈ S →
      triangleEdgeIncrement p (rev e) = -triangleEdgeIncrement p e := by
    intro e he
    have hne : rev e ≠ e := by simpa [S] using he
    unfold triangleEdgeIncrement
    rw [hfinish e hne, hstart e hne]
    exact segment_arg_reverse _ _ (havoid e)
  have hcancel : ∀ e, e ∈ S →
      triangleEdgeIncrement p e + triangleEdgeIncrement p (rev e) = 0 := by
    intro e he
    rw [hreverse e he]
    exact add_neg_cancel _
  change ∑ e ∈ S, triangleEdgeIncrement p e = 0
  refine Finset.sum_involution (s := S) (f := triangleEdgeIncrement p)
    (g := fun e _ => rev e) ?_ ?_ ?_ ?_
  · intro e he
    exact hcancel e he
  · intro e he _
    have hne : rev e ≠ e := by simpa [S] using he
    exact hne
  · intro e he
    have hne : rev e ≠ e := by simpa [S] using he
    change rev e ∈ S
    simpa [S, hinv e] using Ne.symm hne
  · intro e he
    exact hinv e

open scoped Classical

theorem triangle_origin_chain_boundary_balance {T : Type} [Fintype T] [DecidableEq T]
    (p : T → Fin 3 → ℂ)
    (rev : TriangleEdgeIndex T → TriangleEdgeIndex T)
    (hinv : ∀ e, rev (rev e) = e)
    (hstart : ∀ e, rev e ≠ e →
      triangleEdgeStart p (rev e) = triangleEdgeFinish p e)
    (hfinish : ∀ e, rev e ≠ e →
      triangleEdgeFinish p (rev e) = triangleEdgeStart p e)
    (havoid : ∀ e, (0 : ℂ) ∉ segment ℝ (triangleEdgeStart p e)
      (triangleEdgeFinish p e)) :
    (∑ t, if (0 : PlanarPoint ℝ) ∈ convexHull ℝ
        {Complex.equivRealProd (p t 0), Complex.equivRealProd (p t 1),
          Complex.equivRealProd (p t 2)}
      then if 0 < complexDet (p t 1 - p t 0) (p t 2 - p t 0) then 2 * Real.pi
        else if complexDet (p t 1 - p t 0) (p t 2 - p t 0) < 0 then -(2 * Real.pi)
        else 0
      else 0) =
    ∑ e ∈ (Finset.univ.filter (fun e : TriangleEdgeIndex T => rev e = e)),
      triangleEdgeIncrement p e := by
  classical
  have htriangle : ∀ t, (∑ i : Fin 3, triangleEdgeIncrement p (t, i)) =
      if (0 : PlanarPoint ℝ) ∈ convexHull ℝ
        {Complex.equivRealProd (p t 0), Complex.equivRealProd (p t 1),
          Complex.equivRealProd (p t 2)}
      then if 0 < complexDet (p t 1 - p t 0) (p t 2 - p t 0) then 2 * Real.pi
        else if complexDet (p t 1 - p t 0) (p t 2 - p t 0) < 0 then -(2 * Real.pi)
        else 0
      else 0 := by
    intro t
    have h0 := havoid (t, (0 : Fin 3))
    have h1 := havoid (t, (1 : Fin 3))
    have h2 := havoid (t, (2 : Fin 3))
    simp only [triangleEdgeStart, triangleEdgeFinish, finRotate_succ_apply] at h0 h1 h2
    simpa [Fin.sum_univ_three, triangleEdgeIncrement, triangleEdgeStart,
      triangleEdgeFinish, finRotate_succ_apply] using
      triangle_origin_angle_balance (p t 0) (p t 1) (p t 2) h0 h1 h2
  have hnonfixed := nonfixed_edge_angles_cancel p rev hinv hstart hfinish havoid
  have hsplit := Finset.sum_filter_add_sum_filter_not
    (Finset.univ : Finset (TriangleEdgeIndex T)) (fun e => rev e = e)
    (triangleEdgeIncrement p)
  rw [hnonfixed, add_zero] at hsplit
  rw [hsplit, Fintype.sum_prod_type]
  exact Finset.sum_congr rfl (fun t _ => (htriangle t).symm)

end DirectGLSSW.HOMFLY.PrincipalTurning





