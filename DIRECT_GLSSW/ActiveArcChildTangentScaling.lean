import ActiveArcPositiveFirstCrossing

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.Split
open DirectGLSSW Cursor

/-- Every child side is a positively shortened original physical side;
the two endpoint sides use the actual crossing parameters. -/
theorem child_tangent_positive_scaling
    {a b : ℕ} (q : Fin (a+b+2) → PlanarPoint ℝ) (hR : Regular q)
    (c : Crossing q) (hfirst : c.val.1=0) (hcut : c.val.2.val=a)
    (e : Fin (a+1)) :
    ∃ s : ℝ, 0<s ∧ cyclicTangent (child q hR c hfirst hcut) e =
      s • (q (childEdge (b:=b) e).succ-q (childEdge (b:=b) e).castSucc) := by
  have ha := cut_positive q c hcut
  by_cases he0 : e=0
  · subst e
    refine ⟨1-leftParameter q c,sub_pos.mpr (leftParameter_spec q c).2.1,?_⟩
    have hs := child_successor_val (0 : Fin (a+1)) (by simpa using ha)
    have hs0 : cyclicSuccessor (0 : Fin (a+1))≠0 := by
      intro hh
      have hv := congrArg Fin.val hh
      simp only [Fin.val_zero] at hv
      omega
    have hv : childVertex (b:=b) (cyclicSuccessor (0 : Fin (a+1)))=1 := Fin.ext hs
    unfold cyclicTangent
    rw [child_nonzero q hR c hfirst hcut _ hs0, child_zero, hv]
    have hp := (leftParameter_spec q c).2.2
    rw [hfirst] at hp
    rw [hp]
    change q 1-affinePoint (q 0) (q 1) (leftParameter q c)=
      (1-leftParameter q c) • (q 1-q 0)
    apply Prod.ext <;> simp [affinePoint] <;> ring
  · by_cases hea : e.val=a
    · refine ⟨rightParameter q c,(rightParameter_spec q c).1,?_⟩
      have hv : childVertex (b:=b) e=c.val.2.castSucc := Fin.ext (hea.trans hcut.symm)
      have he : childEdge (b:=b) e=c.val.2 := Fin.ext (hea.trans hcut.symm)
      unfold cyclicTangent
      rw [child_last_successor e hea,child_zero,child_nonzero q hR c hfirst hcut e he0,hv,he,
        (rightParameter_spec q c).2.2]
      apply Prod.ext <;> simp [affinePoint] <;> ring
    · have hel : e.val<a := by have := e.isLt;omega
      refine ⟨1,by norm_num,?_⟩
      have hs := child_successor_val e hel
      have hs0 : cyclicSuccessor e≠0 := by
        intro hh
        have hv := congrArg Fin.val hh
        simp only [Fin.val_zero] at hv
        omega
      have hv : childVertex (b:=b) (cyclicSuccessor e)=(childEdge (b:=b) e).succ := Fin.ext hs
      unfold cyclicTangent
      rw [child_nonzero q hR c hfirst hcut _ hs0, child_nonzero q hR c hfirst hcut e he0,hv]
      exact (one_smul ℝ _).symm


end DirectGLSSW.ActiveArc.Split
