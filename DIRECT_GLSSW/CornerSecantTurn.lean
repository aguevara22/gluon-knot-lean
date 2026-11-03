import CornerConeTwoIncrement
import CornerSecantCombination

set_option autoImplicit false
namespace DirectGLSSW.HOMFLY.PrincipalTurning
open PermutationOrbits

/-- The two literal secant increments adjacent to one source vertex give
its actual principal turn. No rotation or collar-balance premise is used. -/
theorem basedUniformSecant_two_corner_increments {D : PLLinkDiagram} (T : BasedTraversal D)
    (C : diagramComponent D) (k : ℤ) (a b : ℝ)
    (ha : a ∈ Set.Ico ((k : ℝ)-1/2) ((k : ℝ)+1/2))
    (hb : b ∈ Set.Ioc ((k : ℝ)+1/2) ((k : ℝ)+3/2)) :
    Complex.arg (basedUniformSecant T C a b / basedUniformSecant T C a ((k : ℝ)+1/2)) +
    Complex.arg (basedUniformSecant T C ((k : ℝ)+1/2) b / basedUniformSecant T C a b) =
      turn D ((D.continuation ^ k) (T.baseArc C).val) := by
  let p : ℝ := (k : ℝ)+1/2
  let α : ℝ := (k : ℝ)+1/2-a
  let β : ℝ := b-(k : ℝ)-1/2
  have hα : 0<α := by dsimp only [α];linarith [ha.2]
  have hβ : 0<β := by dsimp only [β];linarith [hb.1]
  have hpnext : p ∈ Set.Icc ((k : ℝ)+1/2) ((k : ℝ)+3/2) := by
    dsimp only [p];constructor <;> linarith
  have hpprev : p ∈ Set.Icc ((k : ℝ)-1/2) ((k : ℝ)+1/2) := by
    dsimp only [p];constructor <;> linarith
  have hAraw := basedUniformSecant_one_corner T C k a p ⟨ha.1,ha.2.le⟩ hpnext
  have hX := basedUniformSecant_one_corner T C k a b ⟨ha.1,ha.2.le⟩ ⟨hb.1.le,hb.2⟩
  have hZraw := basedUniformSecant_one_corner T C k p b hpprev ⟨hb.1.le,hb.2⟩
  have hz1 : p-(k : ℝ)-1/2=0 := by dsimp only [p];ring
  have hz2 : (k : ℝ)+1/2-p=0 := by dsimp only [p];ring
  have hA : basedUniformSecant T C a p =
      (α : ℂ)*arcVector D ((D.continuation ^ k) (T.baseArc C).val) := by
    simpa only [hz1,Complex.ofReal_zero,zero_mul,add_zero] using hAraw
  have hZ : basedUniformSecant T C p b =
      (β : ℂ)*arcVector D (D.continuation ((D.continuation ^ k) (T.baseArc C).val)) := by
    simpa only [hz2,Complex.ofReal_zero,zero_mul,zero_add] using hZraw
  change Complex.arg (basedUniformSecant T C a b/basedUniformSecant T C a p) +
    Complex.arg (basedUniformSecant T C p b/basedUniformSecant T C a b) = _
  rw [hA,hZ,hX]
  exact cornerCone_two_increment D ((D.continuation ^ k) (T.baseArc C).val) α β hα hβ

end DirectGLSSW.HOMFLY.PrincipalTurning

