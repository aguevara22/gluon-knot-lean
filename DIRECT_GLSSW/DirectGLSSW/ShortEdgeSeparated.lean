import DirectGLSSW.ShortEdgeGenericity

namespace DirectGLSSW.ShortEdgeGenericity

def SeparatedTriple {n : ℕ} (e f g : Fin n) : Prop :=
  e ≠ f ∧ f ≠ g ∧ e ≠ g ∧
  cyclicSuccessor e ≠ f ∧ cyclicSuccessor f ≠ e ∧
  cyclicSuccessor f ≠ g ∧ cyclicSuccessor g ≠ f ∧
  cyclicSuccessor e ≠ g ∧ cyclicSuccessor g ≠ e

end DirectGLSSW.ShortEdgeGenericity
