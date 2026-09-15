import SM.CuspSides

/-! The source begins with an arbitrary continuous curve on an open interval.
Its sole collinear triple proves the nongeneric-centre field of WallGerm, so
using that representation adds no hypothesis to the original cusp lemma. -/

namespace SM

variable {n : ℕ} [NeZero n]

def cuspCurveGerm (ε : ℝ) (hε : 0 < ε)
    (P : Set.Ioo (-ε) ε → LabelledTuple n) (hP : Continuous P)
    (hg : ∀ t, t.val ≠ 0 → Generic (P t)) (j : ZMod n)
    (hz : pointZeroTriples (P ⟨0, by constructor <;> linarith⟩) = {turnSupport j}) : WallGerm n where
  radius := ε
  radius_pos := hε
  curve := P
  continuous_curve := hP
  generic_punctured := hg
  nongeneric_center := by
    intro h
    have he := (pointZeroTriples_empty_iff _).mpr h.1
    rw [hz] at he
    exact Finset.singleton_ne_empty _ he

theorem cusp_sides_of_continuous_curve (hn : 4 ≤ n) (ε : ℝ) (hε : 0 < ε)
    (P : Set.Ioo (-ε) ε → LabelledTuple n) (hP : Continuous P)
    (hg : ∀ t, t.val ≠ 0 → Generic (P t)) (j : ZMod n)
    (hz : pointZeroTriples (P ⟨0, by constructor <;> linarith⟩) = {turnSupport j})
    (hconc : concurrenceTriples (P ⟨0, by constructor <;> linarith⟩) = ∅)
    (hout : ¬ ∃ r : ℝ, 0 ≤ r ∧ r ≤ 1 ∧
      P ⟨0, by constructor <;> linarith⟩ j =
        P ⟨0, by constructor <;> linarith⟩ (j - 1) +
          r • (P ⟨0, by constructor <;> linarith⟩ (j + 1) -
            P ⟨0, by constructor <;> linarith⟩ (j - 1)))
    (hchange : ∃ δ : ℝ, 0 < δ ∧ ∀ t : Set.Ioo 0 ε, t.val < δ →
      (turn (P ⟨t.val, by constructor <;> linarith [t.property.1, t.property.2]⟩) j : ℝ) *
        (turn (P ⟨-t.val, by constructor <;> linarith [t.property.1, t.property.2]⟩) j : ℝ) < 0) :
    let g := cuspCurveGerm ε hε P hP hg j hz
    ∃ h : g.CuspAt j, ∃ b : Bool, ∃ hc : CuspCase g.center j b, CuspSidesData g j h b hc := by
  let g := cuspCurveGerm ε hε P hP hg j hz
  have h : g.CuspAt j := by
    refine ⟨hn, hz, hconc, hout, ?_⟩
    apply (g.signChanges_iff_local (fun Q => (turn Q j : ℝ))).mpr
    exact hchange
  exact ⟨h, cusp_sides g h⟩

end SM
