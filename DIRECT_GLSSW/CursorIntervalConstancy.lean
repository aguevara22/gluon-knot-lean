import ShiftedSecantIsolation
import ShiftedSideSeparation
import ShiftFirstPairEndpointStability
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.CursorWallTransport
open EndpointEventGeometry ShortEdgeSignStability

/-- An open current is constant along a compact piece of its first-side line
which misses all later closed sides, provided the two endpoint words are generic.
No isolated-event or distinct-secant-root hypothesis is supplied: a small
parallel translation resolves simultaneous auxiliary walls and is removed by
endpoint sign stability. -/
theorem openCurrent_constancy_on_first_line
    (W : ℕ → PlanarPoint ℝ) (v : PlanarPoint ℝ) (N : ℕ) (hN : 0<N)
    (b : ℝ) (hb : 0≤b) (hcore : CoreHGeneric W N)
    (hcoreb : CoreHGeneric (moveEndpoint W v b) N)
    (hfirst : planarDet (W 1-W 0) v=0)
    (hno : ∀ t : ℝ, 0≤t → t≤b → ∀ r : ℕ, 0<r → r<N →
      ∀ u : ℝ, 0≤u → u≤1 → W 0+t • v≠affinePoint (W r) (W (r+1)) u) :
    OpenMarkedCurrent.entry (polygonSignArray W) 0 N =
      OpenMarkedCurrent.entry (polygonSignArray (moveEndpoint W v b)) 0 N := by
  have hzero : moveEndpoint W v 0=W := by
    funext i
    by_cases hi : i=0
    · subst i;simp [moveEndpoint]
    · simp [moveEndpoint,hi]
  by_cases hv : v=0
  · have he : moveEndpoint W v b=W := by
      funext i
      by_cases hi : i=0
      · subst i;simp [moveEndpoint,hv]
      · simp [moveEndpoint,hi,hv]
    rw [he]
  · have hww : ∃ w : PlanarPoint ℝ, planarDet v w≠0 := by
      by_cases hvx : v.1=0
      · have hvy : v.2≠0 := by
          intro hh
          apply hv
          apply Prod.ext <;> simp [hvx,hh]
        exact ⟨(1,0),by simpa [planarDet] using neg_ne_zero.mpr hvy⟩
      · exact ⟨(0,1),by simpa [planarDet] using hvx⟩
    obtain ⟨w,hw⟩ := hww
    obtain ⟨δ0,hδ0,hend0⟩ := CursorEndpointStability.exists_shiftFirstPair_endpoint_radius W v w N 0 hN (by rwa [hzero])
    obtain ⟨δb,hδb,hendb⟩ := CursorEndpointStability.exists_shiftFirstPair_endpoint_radius W v w N b hN hcoreb
    obtain ⟨δs,hδs,hside⟩ := exists_shiftFirstPair_side_radius W v w N 0 b hno
    obtain ⟨η,hη,hηδ,hsep⟩ := exists_small_tail_secant_separation W v w (W 0) N hcore hw
      (min δ0 (min δb δs)) (lt_min hδ0 (lt_min hδb hδs))
    have hη0 : |η|<δ0 := by rw [abs_of_pos hη];exact lt_of_lt_of_le hηδ (min_le_left _ _)
    have hηb : |η|<δb := by rw [abs_of_pos hη];exact lt_of_lt_of_le hηδ (le_trans (min_le_right _ _) (min_le_left _ _))
    have hηs : η<δs := lt_of_lt_of_le hηδ (le_trans (min_le_right _ _) (min_le_right _ _))
    obtain ⟨hC0,hS0,hM0⟩ := hend0 η hη0
    obtain ⟨hCb,hSb,hMb⟩ := hendb η hηb
    have hnos := hside η hη hηs
    have hseps := shifted_secants_isolated W v w η N 0 b hC0 hfirst hnos hsep
    have hfirst' : planarDet (shiftFirstPair W w η 1-shiftFirstPair W w η 0) v=0 := by
      have he : planarDet (shiftFirstPair W w η 1-shiftFirstPair W w η 0) v=planarDet (W 1-W 0) v := by
        dsimp [shiftFirstPair,planarDet]
        ring
      exact he.trans hfirst
    have hM := isolated_interval_openCurrent_eq (shiftFirstPair W w η) v N hN 0 b hb hC0 hCb hfirst' hnos hseps
    rw [hzero] at hM0
    exact hM0.symm.trans (hM.trans hMb)

end DirectGLSSW.CursorWallTransport
