import SplitMainRange

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.DescendingSpatial
open HOMFLY HOMFLY.PrincipalTurning

theorem splitClosure_planar_parameter (D : PLLinkDiagram) (e : Fin D.nArc)
    (t : ℝ) : affinePoint (splitBaseB D e) (splitBaseA D e) t =
      affinePoint (D.vertexPoint (D.arcSource e)) (D.vertexPoint (D.arcTarget e)) (1/4+t/2) := by
  apply Prod.ext <;> simp [splitBaseA,splitBaseB,affinePoint] <;> ring

/-- The projected split trace is exactly the literal finite continuation
arc union; neither an arc nor the omitted base subsegment is lost. -/
theorem split_planar_trace_iff (D : PLLinkDiagram) (e : Fin D.nArc) (x : PlanarPoint ℝ) :
    (x ∈ Set.range (splitMainPlanar D e) ∨
      ∃ t : unitInterval, affinePoint (splitBaseB D e) (splitBaseA D e) t.val = x) ↔
    ∃ k : Fin (componentArcLength D e), ∃ u : unitInterval,
      affinePoint (D.vertexPoint (D.arcSource ((D.continuation ^ k.val) e)))
        (D.vertexPoint (D.arcTarget ((D.continuation ^ k.val) e))) u.val = x := by
  have hm : (1:ℝ) ≤ componentArcLength D e := by exact_mod_cast componentArcLength_pos D e
  constructor
  · rintro (hx | ⟨t,rfl⟩)
    · rw [splitMainPlanar_range] at hx
      obtain ⟨s,hs,rfl⟩ := hx
      by_cases hsm : s < (componentArcLength D e:ℝ)
      · obtain ⟨k,u,he⟩ := uniform_first_period_cell D e s (by linarith [hs.1]) hsm
        exact ⟨k,u,he.symm⟩
      · have hu0 : 0 ≤ s-(componentArcLength D e:ℝ) := by linarith
        have hu1 : s-(componentArcLength D e:ℝ) ≤ 1 := by linarith [hs.2]
        refine ⟨⟨0,componentArcLength_pos D e⟩,⟨s-componentArcLength D e,⟨hu0,hu1⟩⟩,?_⟩
        have hc := uniformPLCurve_arc_cell D e 0 (s-componentArcLength D e) ⟨hu0,hu1⟩
        have hp := uniformPLCurve_periodic D e (s-componentArcLength D e)
        have hh : s-(componentArcLength D e:ℝ)+componentArcLength D e=s := by ring
        rw [hh] at hp
        simp only [Int.cast_zero,zero_add,zpow_zero,Equiv.Perm.one_apply] at hc
        simpa using hc.symm.trans hp.symm
    · refine ⟨⟨0,componentArcLength_pos D e⟩,
        ⟨1/4+t.val/2,by constructor <;> linarith [t.property.1,t.property.2]⟩,?_⟩
      simpa using (splitClosure_planar_parameter D e t.val).symm
  · rintro ⟨k,u,rfl⟩
    have hc := uniformPLCurve_arc_cell D e (k.val:ℤ) u.val u.property
    simp only [Int.cast_natCast,zpow_natCast] at hc
    by_cases hv : (3:ℝ)/4 ≤ (k.val:ℝ)+u.val
    · left
      rw [splitMainPlanar_range]
      refine ⟨(k.val:ℝ)+u.val,⟨hv,?_⟩,hc⟩
      have hk : (k.val:ℝ)+1 ≤ componentArcLength D e := by exact_mod_cast k.isLt
      linarith [u.property.2]
    · have hkz : k.val = 0 := by
        have hk : (k.val:ℝ) < 1 := by linarith [u.property.1]
        have hk' : k.val < 1 := by exact_mod_cast hk
        omega
      simp only [hkz,pow_zero,Equiv.Perm.one_apply] at hc ⊢
      by_cases hu : (1:ℝ)/4 ≤ u.val
      · right
        refine ⟨⟨2*(u.val-1/4),by constructor <;> simp only [hkz,Nat.cast_zero,zero_add] at hv <;> linarith⟩,?_⟩
        rw [splitClosure_planar_parameter]
        congr 1
        ring
      · left
        rw [splitMainPlanar_range]
        refine ⟨(componentArcLength D e:ℝ)+u.val,⟨by linarith [u.property.1],by linarith⟩,?_⟩
        rw [add_comm,uniformPLCurve_periodic]
        simpa using hc

/-- Exact spatial projection onto all actual component arcs. -/
theorem splitSpatialTrace_projection_iff (D : PLLinkDiagram) (e : Fin D.nArc)
    (H : ℝ) (z : ℂ) : z ∈ Prod.fst '' splitSpatialTrace D e H ↔
    ∃ k : Fin (componentArcLength D e), ∃ u : unitInterval,
      Complex.equivRealProd.symm
        (affinePoint (D.vertexPoint (D.arcSource ((D.continuation ^ k.val) e)))
          (D.vertexPoint (D.arcTarget ((D.continuation ^ k.val) e))) u.val) = z := by
  constructor
  · rintro ⟨y,hy,hz⟩
    rcases hy with ⟨t,rfl⟩ | ⟨t,rfl⟩
    · obtain ⟨k,u,he⟩ := (split_planar_trace_iff D e (splitMainPlanar D e t)).mp
        (Or.inl ⟨t,rfl⟩)
      refine ⟨k,u,?_⟩
      rw [he]
      exact hz
    · obtain ⟨k,u,he⟩ := (split_planar_trace_iff D e
        (affinePoint (splitBaseB D e) (splitBaseA D e) t.val)).mp (Or.inr ⟨t,rfl⟩)
      refine ⟨k,u,?_⟩
      rw [he]
      exact hz
  · rintro ⟨k,u,rfl⟩
    have hp := (split_planar_trace_iff D e _).mpr ⟨k,u,rfl⟩
    rcases hp with ⟨t,ht⟩ | ⟨t,ht⟩
    · refine ⟨descendingMain D e H t,Or.inl ⟨t,rfl⟩,?_⟩
      change Complex.equivRealProd.symm (splitMainPlanar D e t) = _
      rw [ht]
    · refine ⟨ascendingClosure D e H t,Or.inr ⟨t,rfl⟩,?_⟩
      change Complex.equivRealProd.symm (affinePoint (splitBaseB D e) (splitBaseA D e) t.val) = _
      rw [ht]

end DirectGLSSW.DescendingSpatial




