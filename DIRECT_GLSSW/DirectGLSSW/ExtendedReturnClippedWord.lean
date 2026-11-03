import DirectGLSSW.ExtendedReturnArcGeometry
import DirectGLSSW.CrossingCapPairing
import DirectGLSSW.DaughterRootAmplitude

set_option autoImplicit false

namespace DirectGLSSW.ExtendedReturnClippedWord
open ExtendedReturnArcGeometry CrossingCapPairing CapCrossingEvent

theorem horizontalMove_extendedArc_zero
    {n : ℕ} (hn : 3 ≤ n) (P : Fin n → PlanarPoint ℝ)
    (hU : (P (zeroIndex hn)).2 = 0) (ε t : ℝ) :
    horizontalMove (extendedArc hn P ε) t 0 = ((P (zeroIndex hn)).1 + t, 0) := by
  ext <;> simp [horizontalMove, EndpointEventGeometry.moveEndpoint, extendedArc_zero, hU]

/-- The clipped extended return arc has exactly the original interior vertex slice. -/
theorem clipped_list_eq_original_slice
    {n : ℕ} (hn : 3 ≤ n) (P : Fin n → PlanarPoint ℝ)
    (hU : (P (zeroIndex hn)).2 = 0) (ε c d : ℝ)
    (k l : ℕ) (hk : 0 < k) (hkl : k < l) (hln : l < n) :
    List.ofFn (crossingClippedCapWord (extendedArc hn P ε) c d k l) =
      ((P (zeroIndex hn)).1 + c, 0) ::
        ((((List.ofFn P).drop k).take (l-k)) ++
          [((P (zeroIndex hn)).1 + d, 0)]) := by
  have hm : (l - 1) - k + 1 = l-k := by omega
  have hlen : (((List.ofFn P).drop k).take (l-k)).length = l-k := by
    simp only [List.length_take, List.length_drop, List.length_ofFn]
    omega
  apply List.ext_getElem
  · simp only [List.length_ofFn, List.length_cons, List.length_append,
      List.length_singleton, List.length_nil, hlen]
    omega
  · intro i hi hj
    cases i with
    | zero =>
      simp only [List.getElem_ofFn, List.getElem_cons_zero]
      rw [crossingClippedCapWord_start, horizontalMove_extendedArc_zero hn P hU]
    | succ i =>
      simp only [List.getElem_ofFn, List.getElem_cons_succ]
      by_cases hinner : i < l-k
      · rw [List.getElem_append_left (by simpa only [hlen] using hinner)]
        simp only [List.getElem_take, List.getElem_drop, List.getElem_ofFn]
        rw [crossingClippedCapWord_internal _ _ _ _ _ _
          (by change 0 < i+1; omega)
          (by change i+1 < ((l-1)-k+1)+1; omega)]
        have hid : k + (i+1) = (k+i)+1 := by omega
        rw [hid]
        exact extendedArc_interior hn P ε ⟨k+i, by omega⟩
          (by change 0 < k+i; omega) (by change k+i+1 < n; omega)
      · have hi' : i+1 < ((l-1)-k+1)+2 := by simpa only [List.length_ofFn] using hi
        have hieq : i = l-k := by omega
        rw [List.getElem_append_right (by simp only [hlen]; omega)]
        have hindex : i - (((List.ofFn P).drop k).take (l-k)).length = 0 := by omega
        simp only [hindex, List.getElem_cons_zero]
        have hfin : (⟨i+1, hi'⟩ : Fin (((l-1)-k+1)+2)) =
            ⟨((l-1)-k+1)+1, by omega⟩ := by apply Fin.ext; simp only [Fin.val_mk]; omega
        rw [hfin, crossingClippedCapWord_end, horizontalMove_extendedArc_zero hn P hU]

/-- The cap between the two original endpoints is the original polygon word. -/
theorem whole_cap_list
    {n : ℕ} (hn : 3 ≤ n) (P : Fin n → PlanarPoint ℝ)
    (hU : (P (zeroIndex hn)).2 = 0)
    (hV : (P (lastIndex hn)).2 = 0) (ε : ℝ) :
    List.ofFn (crossingClippedCapWord (extendedArc hn P ε) 0
      ((P (lastIndex hn)).1 - (P (zeroIndex hn)).1) 1 (n-1)) = List.ofFn P := by
  rw [clipped_list_eq_original_slice hn P hU ε 0 _ 1 (n-1)
    (by norm_num) (by omega) (by omega)]
  have hlen : (((List.ofFn P).drop 1).take (n-1-1)).length = n-2 := by
    simp only [List.length_take, List.length_drop, List.length_ofFn]
    omega
  apply List.ext_getElem
  · simp only [List.length_cons, List.length_append, List.length_nil,
      List.length_ofFn, hlen]
    omega
  · intro i hi hj
    have hin : i < n := by simpa only [List.length_ofFn] using hj
    cases i with
    | zero =>
      simp only [List.getElem_cons_zero, List.getElem_ofFn]
      change ((P (zeroIndex hn)).1 + 0, 0) = P (zeroIndex hn)
      ext <;> simp [hU]
    | succ i =>
      simp only [List.getElem_cons_succ, List.getElem_ofFn]
      by_cases hinner : i < n-2
      · rw [List.getElem_append_left (by simpa only [hlen] using hinner)]
        simp only [List.getElem_take, List.getElem_drop, List.getElem_ofFn]
        congr 1
        apply Fin.ext
        simp only [Fin.val_mk]
        omega
      · rw [List.getElem_append_right (by simp only [hlen]; omega)]
        have hindex : i - (((List.ofFn P).drop 1).take (n-1-1)).length = 0 := by omega
        simp only [hindex, List.getElem_cons_zero]
        have hfin : (⟨i+1, hin⟩ : Fin n) = lastIndex hn := by
          apply Fin.ext
          simp only [Fin.val_mk, lastIndex]
          omega
        rw [hfin]
        ext <;> simp [hV]

/-- Whole-cap genericity is inherited from the original polygon. -/
theorem whole_cap_generic
    {n : ℕ} (hn : 3 ≤ n) (P : Fin n → PlanarPoint ℝ) (hP : CyclicGeneric P)
    (hU : (P (zeroIndex hn)).2 = 0)
    (hV : (P (lastIndex hn)).2 = 0) (ε : ℝ) :
    CyclicGeneric (crossingClippedCapWord (extendedArc hn P ε) 0
      ((P (lastIndex hn)).1 - (P (zeroIndex hn)).1) 1 (n-1)) := by
  apply DaughterRootAmplitude.cyclicGeneric_ofFn_isRotated _ hP
  refine ⟨0, ?_⟩
  simpa using (whole_cap_list hn P hU hV ε).symm

/-- The actual whole-cap amplitude is the original polygon amplitude. -/
theorem whole_cap_amplitude (hRI : GLSSWRootIndependence)
    {n : ℕ} (hn : 3 ≤ n) (P : Fin n → PlanarPoint ℝ) (hP : CyclicGeneric P)
    (hU : (P (zeroIndex hn)).2 = 0)
    (hV : (P (lastIndex hn)).2 = 0) (ε : ℝ) :
    polygonAmplitude (crossingClippedCapWord (extendedArc hn P ε) 0
      ((P (lastIndex hn)).1 - (P (zeroIndex hn)).1) 1 (n-1))
      (whole_cap_generic hn P hP hU hV ε) = polygonAmplitude P hP := by
  have hrot : List.IsRotated (List.ofFn P)
      (List.ofFn (crossingClippedCapWord (extendedArc hn P ε) 0
        ((P (lastIndex hn)).1 - (P (zeroIndex hn)).1) 1 (n-1))) := by
    refine ⟨0, ?_⟩
    simpa using (whole_cap_list hn P hU hV ε).symm
  exact (DaughterRootAmplitude.polygonAmplitude_ofFn_isRotated hRI hP hrot).symm

end DirectGLSSW.ExtendedReturnClippedWord






