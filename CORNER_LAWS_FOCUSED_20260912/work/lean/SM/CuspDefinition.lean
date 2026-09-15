import SM.CuspBetweenness
import SM.GermDefinition
import SM.TurnSupports

/-! The exact source cusp hypotheses and the proved unique central case.
Loop/no-loop and empty conventions are deliberately not assumed here. -/

namespace SM

variable {n : ℕ} [NeZero n]

def CuspCase (P : LabelledTuple n) (j : ZMod n) (caseA : Bool) : Prop :=
  if caseA then StrictBetween (P (j - 1)) (P (j + 1)) (P j)
  else StrictBetween (P j) (P (j - 1)) (P (j + 1))

def cuspFirst (caseA : Bool) (j : ZMod n) : ZMod n := if caseA then j - 1 else j - 2

def cuspLast (caseA : Bool) (j : ZMod n) : ZMod n := cuspFirst caseA j + 2

def cuspCorner₁ (caseA : Bool) (j : ZMod n) : ZMod n := cuspFirst caseA j + 1

def cuspCorner₂ (caseA : Bool) (j : ZMod n) : ZMod n := cuspLast caseA j

def cuspDelta (P : LabelledTuple n) (caseA : Bool) (j : ZMod n) : ℝ :=
  det (edge P (cuspFirst caseA j)) (edge P (cuspLast caseA j))

theorem cusp_indices_A (j : ZMod n) :
    cuspFirst true j = j - 1 ∧ cuspLast true j = j + 1 ∧
    cuspCorner₁ true j = j ∧ cuspCorner₂ true j = j + 1 := by
  simp [cuspFirst, cuspLast, cuspCorner₁, cuspCorner₂]
  ring

theorem cusp_indices_B (j : ZMod n) :
    cuspFirst false j = j - 2 ∧ cuspLast false j = j ∧
    cuspCorner₁ false j = j - 1 ∧ cuspCorner₂ false j = j := by
  simp [cuspFirst, cuspLast, cuspCorner₁, cuspCorner₂]
  ring

namespace WallGerm

def CuspAt (g : WallGerm n) (j : ZMod n) : Prop :=
  4 ≤ n ∧ g.pointZeros = {turnSupport j} ∧ g.concurrences = ∅ ∧
  (¬ ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧
    g.center j = g.center (j - 1) + t • (g.center (j + 1) - g.center (j - 1))) ∧
  g.SignChanges (fun P => (turn P j : ℝ))

theorem cusp_cases (g : WallGerm n) {j : ZMod n} (h : g.CuspAt j) :
    (CuspCase g.center j true ∨ CuspCase g.center j false) ∧
      ¬ (CuspCase g.center j true ∧ CuspCase g.center j false) := by
  have hi := singlePointTriple_vertices_injective h.1 h.2.1
  have hAB : g.center (j - 1) ≠ g.center (j + 1) :=
    fun he => prev_ne_next (by have hn := h.1; omega) j (hi he)
  have hz := singlePointTriple_turn_zero h.2.1
  have hd : det (g.center j - g.center (j - 1))
      (g.center (j + 1) - g.center (j - 1)) = 0 := sign_eq_zero_iff.mp hz
  have hd' : det (g.center (j + 1) - g.center (j - 1))
      (g.center j - g.center (j - 1)) = 0 := by rw [det_swap, hd, neg_zero]
  exact collinear_exterior_cases hAB hd' h.2.2.2.1

theorem cusp_case_existsUnique (g : WallGerm n) {j : ZMod n} (h : g.CuspAt j) :
    ∃! b : Bool, CuspCase g.center j b := by
  have hc := g.cusp_cases h
  rcases hc.1 with hA | hB
  · refine ⟨true, hA, ?_⟩
    intro b hb
    cases b
    · exact (hc.2 ⟨hA, hb⟩).elim
    · rfl
  · refine ⟨false, hB, ?_⟩
    intro b hb
    cases b
    · rfl
    · exact (hc.2 ⟨hb, hB⟩).elim

end WallGerm
end SM
