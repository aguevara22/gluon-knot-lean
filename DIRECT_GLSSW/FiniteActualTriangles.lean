import ActualTriangleImage
import DescendingRankHeights
import FiniteAmbientComposition

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.DescendingSpatial
open HOMFLY

/-- One ambient family straightens every actual component simultaneously.
The literal index set is the diagram component count. -/
theorem exists_finite_actual_triangles {D : PLLinkDiagram} (T : BasedTraversal D) :
    ∃ Φ : unitInterval → ((ℂ × ℝ) ≃ₜ (ℂ × ℝ)),
      Φ 0 = Homeomorph.refl (ℂ × ℝ) ∧
      Continuous (fun p : unitInterval × (ℂ × ℝ) => Φ p.1 p.2) ∧
      Continuous (fun p : unitInterval × (ℂ × ℝ) => (Φ p.1).symm p.2) ∧
      (∀ s x, (Φ s x).2 = x.2) ∧
      ∀ i : Fin (diagramComponentCount D),
        let H : ℝ := 3*((diagramComponentCount D:ℝ)-1-i.val)
        Φ 1 '' splitSpatialTrace D (T.baseArc (T.componentIndex.symm i)).val H =
          (Set.range (fun u : unitInterval => (((u.val/4:ℝ):ℂ),H+1-u.val/2)) ∪
           Set.range (fun u : unitInterval => ((((1-u.val)/4:ℝ):ℂ),H+1/2-u.val/2))) ∪
           Set.range (fun u : unitInterval => ((0:ℂ),H+u.val)) := by
  classical
  let H : Fin (diagramComponentCount D) → ℝ := fun i =>
    3*((diagramComponentCount D:ℝ)-1-i.val)
  have hlocal := fun i : Fin (diagramComponentCount D) =>
    exists_actual_triangle_image D (T.baseArc (T.componentIndex.symm i)).val 0 (H i)
  choose F h0 hc hi hh ho ht using hlocal
  let S : Fin (diagramComponentCount D) → Set ℝ := fun i => Set.Ioo (H i-1/2) (H i+3/2)
  have hd : Pairwise (fun i j => Disjoint (S i) (S j)) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro z hz hz'
    change H i-1/2 < z ∧ z < H i+3/2 at hz
    change H j-1/2 < z ∧ z < H j+3/2 at hz'
    rcases lt_or_gt_of_ne hij with h | h
    · have h' : (i.val:ℝ)+1 ≤ j.val := by exact_mod_cast h
      dsimp [H] at hz hz'
      linarith
    · have h' : (j.val:ℝ)+1 ≤ i.val := by exact_mod_cast h
      dsimp [H] at hz hz'
      linarith
  have hf : ∀ i s x, x.2 ∉ S i → F i s x = x := by
    intro i s x hx
    apply ho i s x
    change ¬ (H i-1/2 < x.2 ∧ x.2 < H i+3/2) at hx
    by_cases hl : H i-1/2 < x.2
    · right
      exact le_of_not_gt (fun hu => hx ⟨hl,hu⟩)
    · exact Or.inl (le_of_not_gt hl)
  obtain ⟨Φ,hΦ0,hΦc,hΦi,hΦh,hΦs,hΦout⟩ :=
    exists_finite_disjoint_height_supported_ambient _ F S hd h0 hc hi hh hf
  refine ⟨Φ,hΦ0,hΦc,hΦi,hΦh,?_⟩
  intro i
  have heq : Φ 1 '' splitSpatialTrace D (T.baseArc (T.componentIndex.symm i)).val (H i) =
      F i 1 '' splitSpatialTrace D (T.baseArc (T.componentIndex.symm i)).val (H i) := by
    apply Set.image_congr
    intro x hx
    apply hΦs i 1 x
    have hb := splitSpatialTrace_height_bounds D (T.baseArc (T.componentIndex.symm i)).val (H i) x hx
    change H i-1/2 < x.2 ∧ x.2 < H i+3/2
    constructor <;> linarith
  exact heq.trans (by simpa only [zero_add] using ht i)

end DirectGLSSW.DescendingSpatial

