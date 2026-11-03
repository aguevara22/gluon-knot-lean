import ActiveArcParentFarFamily
import ActiveArcParentPrefixSign

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.OpenCarrier
open DirectGLSSW ActiveArc RetainedWords Split Primitive

/-- The actual all-parent carrier locus supplies precisely the prefix far rows
consumed by the short-first projector. It does not assert that the original
carrier assignment lies in this dense locus. -/
theorem parentFarLocus_prefix_far {a b : ℕ}
    (q : Fin (a+b+2) → PlanarPoint ℝ) (hR : Regular q)
    (c : Crossing q) (hcut : c.val.2.val=a) (hG1 : cyclicNoncollinear q)
    (hL : parentFarLocus q hR c hcut (parentChartLines q)) :
    ∀ T : Primitive.Support (parent q c hcut) (regular_parent q hR c hcut),
      ∀ k j, 1<k → k<j → j≤openCount (parent q c hcut)
        (regular_parent q hR c hcut) T.val →
        polygonHDet (fun k => if k=0 then q 0 else
          rootedPolygonWord (Primitive.OpenVertex (parent q c hcut)
            (regular_parent q hR c hcut) T)
            (openLast (parent q c hcut) (regular_parent q hR c hcut) T.val)
            (k-1)) 1 k j ≠ 0 := by
  intro T k j hk hkj hj
  let p := parent q c hcut
  let hp := regular_parent q hR c hcut
  let m := openCount p hp T.val
  have hk' : k-1<m := by dsimp [m,p,hp]; omega
  have hj' : j-1<m := by dsimp [m,p,hp]; omega
  let i : Fin m := ⟨k-1,hk'⟩
  let l : Fin m := ⟨j-1,hj'⟩
  have hd : planarDet (Primitive.OpenVertex p hp T i-crossingPoint q c)
      (Primitive.OpenVertex p hp T l-crossingPoint q c) ≠ 0 := by
    intro hz
    exact hL T i l (by dsimp [i]; omega) (by dsimp [i,l]; omega)
      ((parent_far_numerator_zero_iff q hR c hcut hG1 T i l).mpr hz)
  let w : ℕ → PlanarPoint ℝ := fun k => if k=0 then q 0 else
    rootedPolygonWord (Primitive.OpenVertex p hp T) (openLast p hp T.val) (k-1)
  have h1 : w 1=crossingPoint q c := by
    simp only [w,show (1:ℕ)≠0 by decide,ite_false,Nat.sub_self]
    rw [Primitive.openCurrent_word p hp T 0
      (lt_of_lt_of_le (by decide : 0<2) (open_count_ge_two p hp T.val))]
    rw [Primitive.openVertex_zero]
    exact parent_zero q c hcut
  have hwk : w k=Primitive.OpenVertex p hp T i := by
    simp only [w,show k≠0 by omega,ite_false]
    exact Primitive.openCurrent_word p hp T (k-1) hk'
  have hwj : w j=Primitive.OpenVertex p hp T l := by
    simp only [w,show j≠0 by omega,ite_false]
    exact Primitive.openCurrent_word p hp T (j-1) hj'
  change polygonHDet w 1 k j ≠ 0
  have heq : polygonHDet w 1 k j =
      -planarDet (Primitive.OpenVertex p hp T i-crossingPoint q c)
        (Primitive.OpenVertex p hp T l-crossingPoint q c) := by
    rw [polygonHDet,h1,hwk,hwj]
    simp only [planarDet,Prod.fst_sub,Prod.snd_sub]
    ring
  rw [heq]
  exact neg_ne_zero.mpr hd


end DirectGLSSW.ActiveArc.OpenCarrier
