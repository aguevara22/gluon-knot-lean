import ActiveArcRegularGeometry
import DirectGLSSW.ShortEdgeCyclicRelabel

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.ExposedChart
open DirectGLSSW
variable {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ) (e : Fin (n+2))

/-- The actual complementary arc starts after the deleted edge and ends at its source. -/
def cutArc (i : Fin (n+2)) : PlanarPoint ℝ := q (cyclicVertexEquiv e i)

def edgeLabel (f : Fin (n+1)) : Fin (n+2) := cyclicVertexEquiv e f.castSucc

theorem successor_castSucc (f : Fin (n+1)) : cyclicSuccessor f.castSucc=f.succ := by
  apply Fin.ext
  change (f.val+1+0)%(n+2)=f.val+1
  exact Nat.mod_eq_of_lt (by have := f.isLt;omega)

theorem edgeLabel_successor (f : Fin (n+1)) :
    cyclicVertexEquiv e f.succ=cyclicSuccessor (edgeLabel e f) := by
  rw [← successor_castSucc f]
  exact cyclicVertexEquiv_commutes_successor e f.castSucc

theorem cutArc_first : cutArc q e ⟨0,by omega⟩=q (cyclicSuccessor e) := rfl

theorem cutArc_last : cutArc q e ⟨n+1,by omega⟩=q e := by
  change q (cyclicVertexIndex e (n+1))=q e
  rw [show n+1=(n+2)-1 by omega,cyclicVertexIndex_last]

theorem cutArc_eq_rootedWord (i : Fin (n+2)) :
    cutArc q e i=rootedPolygonWord q e i.val := rfl

theorem edgeLabel_injective : Function.Injective (edgeLabel e) := by
  intro f g hh
  have he := (cyclicVertexEquiv e).injective hh
  have hv : f.val=g.val := congrArg (fun z : Fin (n+2) => z.val) he
  exact Fin.ext hv

theorem edgeLabel_ne_deleted (f : Fin (n+1)) : edgeLabel e f≠e := by
  intro hh
  have he : cyclicVertexIndex e f.val=cyclicVertexIndex e ((n+2)-1) :=
    hh.trans (cyclicVertexIndex_last e).symm
  have hval := cyclicVertexIndex_injective e (by have := f.isLt;omega) (by omega) he
  have := f.isLt
  omega

theorem exists_edgeLabel (f : Fin (n+2)) (hf : f≠e) : ∃ i : Fin (n+1), edgeLabel e i=f := by
  let j := (cyclicVertexEquiv e).symm f
  have hj : j.val<n+1 := by
    have hjb := j.isLt
    by_contra hh
    have hjv : j.val=n+1 := by omega
    have he : j=(⟨n+1,by omega⟩ : Fin (n+2)) := Fin.ext hjv
    apply hf
    have hz := (cyclicVertexEquiv e).apply_symm_apply f
    change cyclicVertexEquiv e j=f at hz
    rw [he] at hz
    change cyclicVertexIndex e (n+1)=f at hz
    rw [show n+1=(n+2)-1 by omega,cyclicVertexIndex_last] at hz
    exact hz.symm
  refine ⟨⟨j.val,hj⟩,?_⟩
  exact (cyclicVertexEquiv e).apply_symm_apply f

/-- Physical edges are exactly the original edges other than the deleted one. -/
def edgeEquiv : Fin (n+1) ≃ {f : Fin (n+2) // f≠e} :=
  Equiv.ofBijective (fun f => ⟨edgeLabel e f,edgeLabel_ne_deleted e f⟩)
    ⟨fun _ _ h => edgeLabel_injective e (congrArg Subtype.val h),by
      intro f
      obtain ⟨i,hi⟩ := exists_edgeLabel e f.val f.property
      exact ⟨i,Subtype.ext hi⟩⟩

theorem cut_edgeInterior_iff (f : Fin (n+1)) (x : PlanarPoint ℝ) :
    ActiveArc.edgeInterior (cutArc q e) f x ↔ DirectGLSSW.edgeInterior q (edgeLabel e f) x := by
  unfold ActiveArc.edgeInterior DirectGLSSW.edgeInterior OnOpenSegment
  simp only [cutArc,edgeLabel_successor,edgeLabel]

theorem cut_tangent (f : Fin (n+1)) :
    cutArc q e f.succ-cutArc q e f.castSucc=cyclicTangent q (edgeLabel e f) := by
  simp only [cutArc,edgeLabel_successor,cyclicTangent,edgeLabel]

/-- G1--G2 of the genuine parent discharges all physical regularity of its cut arc. -/
theorem cutArc_regular (hq : CyclicGeneric q) : Regular (cutArc q e) := by
  refine ⟨?_,?_,?_,?_⟩
  · intro f
    rw [cut_tangent]
    exact cyclicTangent_ne_zero hq.size_ge_three q hq.g1 _
  · intro f g hfg x hf hg
    rw [cut_tangent,cut_tangent]
    exact cyclicTangent_det_ne_zero_of_intersection hq.size_ge_three q hq.g1 _ _
      (fun hh => hfg (edgeLabel_injective e hh)) x
      ((cut_edgeInterior_iff q e f x).mp hf) ((cut_edgeInterior_iff q e g x).mp hg)
  · intro f g h x hfg hgh hhf ⟨hf,hg,hh⟩
    exact hq.g2 _ _ _ x
      (fun he => hfg (edgeLabel_injective e he))
      (fun he => hgh (edgeLabel_injective e he))
      (fun he => hhf (edgeLabel_injective e he.symm))
      ⟨(cut_edgeInterior_iff q e f x).mp hf,(cut_edgeInterior_iff q e g x).mp hg,
        (cut_edgeInterior_iff q e h x).mp hh⟩
  · intro f i hif his hi
    apply cyclic_vertex_not_in_nonincident_edge hq.size_ge_three q hq.g1
      (edgeLabel e f) (cyclicVertexEquiv e i)
    · exact fun hh => hif ((cyclicVertexEquiv e).injective hh)
    · intro hh
      rw [← edgeLabel_successor e f] at hh
      exact his ((cyclicVertexEquiv e).injective hh)
    · exact (cut_edgeInterior_iff q e f (cutArc q e i)).mp hi

end DirectGLSSW.ActiveArc.ExposedChart
