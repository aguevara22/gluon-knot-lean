import ActualTriangleSimilarity

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.DescendingSpatial
open HOMFLY

/-- The tent is exactly the two straight triangle edges, with explicit
surjective affine changes of parameter. -/
theorem tent_range_eq_two_segments (b : ℂ) (H : ℝ) :
    Set.range (fun t : unitInterval => (b+(min t.val (1-t.val)/2:ℝ),H+1-t.val)) =
      Set.range (fun u : unitInterval => (b+(u.val/4:ℝ),H+1-u.val/2)) ∪
      Set.range (fun u : unitInterval => (b+((1-u.val)/4:ℝ),H+1/2-u.val/2)) := by
  ext x
  constructor
  · rintro ⟨t,rfl⟩
    by_cases ht : t.val ≤ 1/2
    · left
      refine ⟨⟨2*t.val,by constructor <;> linarith [t.property.1]⟩,?_⟩
      dsimp only
      rw [min_eq_left (by linarith : t.val ≤ 1-t.val)]
      apply Prod.ext
      · apply Complex.ext <;> simp <;> ring
      · dsimp
        ring
    · right
      refine ⟨⟨2*t.val-1,by constructor <;> linarith [t.property.2]⟩,?_⟩
      dsimp only
      rw [min_eq_right (by linarith : 1-t.val ≤ t.val)]
      apply Prod.ext
      · apply Complex.ext <;> simp <;> ring
      · dsimp
        ring
  · rintro (⟨u,rfl⟩ | ⟨u,rfl⟩)
    · refine ⟨⟨u.val/2,by constructor <;> linarith [u.property.1,u.property.2]⟩,?_⟩
      change (b+(min (u.val/2) (1-u.val/2)/2:ℝ),H+1-u.val/2)=_
      rw [min_eq_left (by linarith [u.property.2] : u.val/2 ≤ 1-u.val/2)]
      apply Prod.ext
      · apply Complex.ext <;> simp <;> ring
      · rfl
    · refine ⟨⟨(u.val+1)/2,by constructor <;> linarith [u.property.1,u.property.2]⟩,?_⟩
      change (b+(min ((u.val+1)/2) (1-(u.val+1)/2)/2:ℝ),H+1-(u.val+1)/2)=_
      rw [min_eq_right (by linarith [u.property.1] : 1-(u.val+1)/2 ≤ (u.val+1)/2)]
      apply Prod.ext
      · apply Complex.ext <;> simp <;> ring
      · dsimp
        ring

/-- An actual component trace is carried by a supported ambient family to
three literal straight segments, with vertices (b,H), (b+1/4,H+1/2), (b,H+1).
The target has not been defined to mean an unlink. -/
theorem exists_actual_triangle_image (D : PLLinkDiagram) (e : Fin D.nArc)
    (b : ℂ) (H : ℝ) :
    ∃ F : unitInterval → ((ℂ × ℝ) ≃ₜ (ℂ × ℝ)),
      F 0 = Homeomorph.refl (ℂ × ℝ) ∧
      Continuous (fun p : unitInterval × (ℂ × ℝ) => F p.1 p.2) ∧
      Continuous (fun p : unitInterval × (ℂ × ℝ) => (F p.1).symm p.2) ∧
      (∀ s x, (F s x).2 = x.2) ∧
      (∀ s x, x.2 ≤ H-1/2 ∨ H+3/2 ≤ x.2 → F s x = x) ∧
      F 1 '' splitSpatialTrace D e H =
        (Set.range (fun u : unitInterval => (b+(u.val/4:ℝ),H+1-u.val/2)) ∪
         Set.range (fun u : unitInterval => (b+((1-u.val)/4:ℝ),H+1/2-u.val/2))) ∪
         Set.range (fun u : unitInterval => (b,H+u.val)) := by
  obtain ⟨F,h0,hCont,hInvCont,hHeight,hOutside,hMain,hClose⟩ := exists_actual_triangle_similarity D e b H
  refine ⟨F,h0,hCont,hInvCont,hHeight,hOutside,?_⟩
  rw [← tent_range_eq_two_segments]
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    rcases hy with ⟨t,rfl⟩ | ⟨t,rfl⟩
    · rw [hMain]
      exact Or.inl ⟨t,rfl⟩
    · rw [hClose]
      exact Or.inr ⟨t,rfl⟩
  · rintro (⟨t,rfl⟩ | ⟨t,rfl⟩)
    · exact ⟨descendingMain D e H t,Or.inl ⟨t,rfl⟩,hMain t⟩
    · exact ⟨ascendingClosure D e H t,Or.inr ⟨t,rfl⟩,hClose t⟩

end DirectGLSSW.DescendingSpatial


