import ActiveArcSuffix
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.Split
attribute [local instance] Classical.propDecidable
variable {a b : ℕ} (q : Fin (a+b+2) → PlanarPoint ℝ) (hR : Regular q)
include hR

theorem suffixCrossing_leftParameter (d : Crossing (suffix q)) :
    leftParameter q (suffixCrossingToOriginal q d) = leftParameter (suffix q) d := by
  apply edge_parameter_unique q hR (edge d.val.1)
  have hp := (leftParameter_spec q (suffixCrossingToOriginal q d)).2.2
  have hs := (leftParameter_spec (suffix q) d).2.2
  simp only [suffix,vertex_castSucc,vertex_succ] at hs
  exact hp.symm.trans ((suffixCrossingToOriginal_point q hR d).trans hs)

theorem suffixCrossing_survives_iff (θ : ℝ) (d : Crossing (suffix q)) :
    Cursor.Survives (suffix q) θ d ↔
      (suffixCrossingToOriginal q d).val.1.val = a →
        θ < leftParameter q (suffixCrossingToOriginal q d) := by
  rw [suffixCrossing_leftParameter q hR]
  have he : d.val.1 = 0 ↔ (suffixCrossingToOriginal q d).val.1.val = a := by
    change d.val.1 = 0 ↔ a + d.val.1.val = a
    constructor
    · intro hh;rw [hh];simp
    · intro hh;apply Fin.ext;change d.val.1.val=0;omega
  exact imp_congr he Iff.rfl

/-- Actual regularity of a moved literal suffix, from exclusion of its original
first-carrier crossing parameters. Final history use must produce that exclusion. -/
theorem suffix_moveStart_regular (θ : ℝ) (h0 : 0 ≤ θ) (h1 : θ < 1)
    (havoid : ∀ d : Crossing q, d.val.1.val = a → leftParameter q d ≠ θ) :
    Regular (Cursor.moveStart (suffix q) θ) := by
  apply Cursor.regular_moveStart (suffix q) (regular_suffix q hR) θ h0 h1
  intro hh
  obtain ⟨d,hd,hθ⟩ := (Cursor.mem_criticalParameters (suffix q) θ).mp hh
  apply havoid (suffixCrossingToOriginal q d)
  · change a+d.val.1.val=a;rw [hd];simp
  · rw [suffixCrossing_leftParameter q hR]
    exact hθ

/-- The actual moved suffix has precisely the original later-edge crossings
whose first-edge parameter lies strictly beyond the cursor. -/
def suffixCursorCrossingEquiv (θ : ℝ) (h0 : 0 ≤ θ) (h1 : θ < 1) :
    Crossing (Cursor.moveStart (suffix q) θ) ≃
      {d : Crossing q // a ≤ d.val.1.val ∧ (d.val.1.val = a → θ < leftParameter q d)} := by
  let E := Cursor.crossingEquiv (suffix q) (regular_suffix q hR) θ h0 h1
  let F : {d : Crossing (suffix q) // Cursor.Survives (suffix q) θ d} →
      {d : Crossing q // a ≤ d.val.1.val ∧ (d.val.1.val = a → θ < leftParameter q d)} :=
    fun d => ⟨suffixCrossingToOriginal q d.val,
      (suffixCrossing_range q _).mp ⟨d.val,rfl⟩,
      (suffixCrossing_survives_iff q hR θ d.val).mp d.property⟩
  refine E.trans (Equiv.ofBijective F ⟨?_,?_⟩)
  · intro d e hh
    apply Subtype.ext
    exact suffixCrossingToOriginal_injective q (congrArg Subtype.val hh)
  · intro d
    obtain ⟨e,he⟩ := (suffixCrossing_range q d.val).mpr d.property.1
    have hs : Cursor.Survives (suffix q) θ e := by
      apply (suffixCrossing_survives_iff q hR θ e).mpr
      rw [he]
      exact d.property.2
    exact ⟨⟨e,hs⟩,Subtype.ext he⟩

end DirectGLSSW.ActiveArc.Split
