import DirectGLSSW.ShortEdgeCyclicAdapter
import DirectGLSSW.RealPolygons

namespace DirectGLSSW.TruncationDirection
open DirectGLSSW.ShortEdgeCyclicAdapter

def truncateCyclicCorner {n : ℕ} (q : Fin n → PlanarPoint ℝ)
    (a p : Fin n) (scale ε : ℝ) : Fin (n + 1) → PlanarPoint ℝ :=
  insertCyclicAfter (Function.update q a (q a + ε • (q p - q a))) a ε
    (scale • (q (cyclicSuccessor a) - q a) - (q p - q a))

theorem truncateCyclicCorner_anchor {n : ℕ} (q : Fin n → PlanarPoint ℝ)
    (a p : Fin n) (scale ε : ℝ) :
    truncateCyclicCorner q a p scale ε ⟨a.val, by omega⟩ =
      q a + ε • (q p - q a) := by
  simp [truncateCyclicCorner, insertCyclicAfter]

theorem truncateCyclicCorner_new {n : ℕ} (q : Fin n → PlanarPoint ℝ)
    (a p : Fin n) (scale ε : ℝ) :
    truncateCyclicCorner q a p scale ε ⟨a.val + 1, by omega⟩ =
      q a + (ε * scale) • (q (cyclicSuccessor a) - q a) := by
  simp [truncateCyclicCorner, insertCyclicAfter]
  ext <;> simp <;> ring

end DirectGLSSW.TruncationDirection
