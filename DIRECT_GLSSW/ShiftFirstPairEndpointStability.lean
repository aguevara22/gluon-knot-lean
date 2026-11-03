import ContinuousWordStability
import ShiftFirstPair
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.CursorEndpointStability
open EndpointEventGeometry CursorWallTransport ShortEdgeSignStability
/-- The literal two-point translation preserves a generic fixed cursor
endpoint's complete finite sign data and actual open current. -/
theorem exists_shiftFirstPair_endpoint_radius
    (W : ℕ → PlanarPoint ℝ) (v w : PlanarPoint ℝ) (N : ℕ) (a : ℝ)
    (hN : 0<N) (hcore : CoreHGeneric (moveEndpoint W v a) N) :
    ∃ δ : ℝ, 0<δ ∧ ∀ η : ℝ, |η|<δ →
      CoreHGeneric (moveEndpoint (shiftFirstPair W w η) v a) N ∧
      (∀ i k j, i<k → k<j → j≤N →
        polygonSignArray (moveEndpoint (shiftFirstPair W w η) v a) i k j =
          polygonSignArray (moveEndpoint W v a) i k j) ∧
      OpenMarkedCurrent.entry (polygonSignArray (moveEndpoint (shiftFirstPair W w η) v a)) 0 N =
        OpenMarkedCurrent.entry (polygonSignArray (moveEndpoint W v a)) 0 N := by
  let P := fun η => moveEndpoint (shiftFirstPair W w η) v a
  have hzero : P 0 = moveEndpoint W v a := by
    funext i
    simp [P,moveEndpoint,shiftFirstPair]
  have hc (i : ℕ) (_hi : i≤N) : Continuous (fun η => P η i) := by
    dsimp [P]
    unfold moveEndpoint shiftFirstPair
    split_ifs <;> fun_prop
  have hbase : CoreHGeneric (P 0) N := by rw [hzero]; exact hcore
  have hh := exists_continuous_word_current_radius P N hN hc hbase
  simpa only [hzero] using hh
end DirectGLSSW.CursorEndpointStability


