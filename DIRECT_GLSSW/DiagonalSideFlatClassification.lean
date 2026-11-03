import DiagonalVertexPosition
import DiagonalShortWindows
import FlatSecantSide
import DiagonalVertexIdentification

set_option autoImplicit false
namespace DirectGLSSW.HOMFLY.PrincipalTurning
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Every literal diagonal side is one of the two actual vertex witnesses,
or has zero increment on a single actual affine arc. -/
theorem rectangleDiagonalNeighbour_vertex_or_zero {D : PLLinkDiagram} (T : BasedTraversal D)
    (C : diagramComponent D) (e : RetainedRectangleSide T C)
    (hdiag : rectangleDiagonalNeighbour e) :
    (∃ x, e=actualDiagonalVertexSide T C x) ∨ rectangleSideIncrement e=0 := by
  have hc := retainedRectangle_axis_cells e.1
  have hclass := (rectangleDiagonalNeighbour_exact T C e).mp hdiag
  have hm := hclass.2
  let a := e.1.val.1.1
  let b := e.1.val.1.2
  let u := e.1.val.2.1
  let v := e.1.val.2.2
  let k : ℤ := Int.floor (a+1/2)
  let p : ℝ := (k : ℝ)+1/2
  have hx : a<b := hc.1.2.2.1
  have hmid : b<u := hm.2.2.1
  have hy : u<v := hc.2.2.2.1
  have ha0 := (secantAxisCuts_bounds T C a hc.1.1).1
  have hvm := (secantAxisCuts_bounds T C v hc.2.2.1).2
  have halow : (k : ℝ)-1/2≤a := by
    have hf := Int.floor_le (a+1/2)
    dsimp only [k]
    linarith
  have hap : a<p := by
    have hf := Int.lt_floor_add_one (a+1/2)
    dsimp only [p,k]
    linarith
  have hvnext : v≤((k+1 : ℤ) : ℝ)+1/2 := by
    have hw := rectangleDiagonalNeighbour_short T C e hdiag
    change v-a≤3/4 at hw
    push_cast
    dsimp only [p] at hap
    linarith
  push_cast at hvnext
  have hindex (hpb : p=b ∨ p=u) :
      ∃ n : Fin (componentArcLength D (T.baseArc C).val), (n.val : ℝ)+1/2=p := by
    have hk0 : 0≤k := Int.floor_nonneg.mpr (by linarith)
    let n : ℕ := k.toNat
    have hncast : (n : ℝ)=(k : ℝ) := by
      have hc : (n : ℤ)=k := Int.toNat_of_nonneg hk0
      exact_mod_cast hc
    have hnm : n<componentArcLength D (T.baseArc C).val := by
      have hnr : (n : ℝ)<(componentArcLength D (T.baseArc C).val : ℝ) := by
        rw [hncast]
        dsimp only [p] at hpb
        rcases hpb with hpb | hpu <;> linarith
      exact_mod_cast hnr
    exact ⟨⟨n,hnm⟩,by change (n : ℝ)+1/2=p;rw [hncast]⟩
  have hposition : v≤p ∨ p=b ∨ p=u :=
    diagonalStaircase_next_vertex_position T C a b u v hc.1 hm hc.2
  dsimp only [a,b,u,v] at *
  rcases hclass.1 with hs | hs
  · rcases hposition with hvp | hpb | hpu
    · right
      apply rectangleSideIncrement_zero_of_arc_cell T C e k <;>
        simp only [rectangleSideStart,rectangleSideFinish,hs,ite_true,Set.mem_Icc] <;>
        constructor <;> dsimp only [p] at hvp <;> linarith
    · obtain ⟨n,hn⟩ := hindex (Or.inl hpb)
      left
      exact ⟨(n,1),diagonalBottomSide_eq_vertex T C e hdiag hs n (hpb.symm.trans hn.symm)⟩
    · right
      apply rectangleSideIncrement_zero_of_arc_cell T C e k <;>
        simp only [rectangleSideStart,rectangleSideFinish,hs,ite_true,Set.mem_Icc] <;>
        constructor <;> dsimp only [p] at hpu <;> linarith
  · rcases hposition with hvp | hpb | hpu
    · right
      apply rectangleSideIncrement_zero_of_arc_cell T C e k <;>
        simp only [rectangleSideStart,rectangleSideFinish,hs,show (1 : Fin 4)≠0 by decide,ite_false,ite_true,Set.mem_Icc] <;>
        constructor <;> dsimp only [p] at hvp <;> linarith
    · right
      apply rectangleSideIncrement_zero_of_arc_cell T C e (k+1) <;>
        simp only [rectangleSideStart,rectangleSideFinish,hs,show (1 : Fin 4)≠0 by decide,ite_false,ite_true,Set.mem_Icc] <;>
        constructor <;> push_cast <;> dsimp only [p] at hpb <;> linarith
    · obtain ⟨n,hn⟩ := hindex (Or.inr hpu)
      left
      exact ⟨(n,0),diagonalRightSide_eq_vertex T C e hdiag hs n (hpu.symm.trans hn.symm)⟩

end
end DirectGLSSW.HOMFLY.PrincipalTurning

