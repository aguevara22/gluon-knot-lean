import DaughterOpenParameter

set_option autoImplicit false
namespace DirectGLSSW.DaughterPrefixParameters
open DaughterFirstReturn EventSegmentGeometry
noncomputable section

variable {n : ℕ} (P : Fin n → PlanarPoint ℝ) (hG2 : cyclicNoTripleIntersections P)
variable (S : Finset (PolygonCrossing P)) (hn : 3 ≤ n)
variable (root : PolygonEvent P) (hroot : retainedCorner P S root)
include hn hroot

/-- Strict-step strengthening of canonical orbitPrefix_edge_parameter: its
first-return exclusion makes this actual dart step an unswitched original step. -/
theorem orbitPrefix_parameter_step (c : CornerCoord P hG2 S root) (k : ℕ)
    (hk : k+1 < cornerGap P hG2 S root c.val (cornerSuccessor P hG2 S root c).val) :
    polygonEventParameter P ((DartPerm P hG2 S ^ k) (orbitEventAt P hG2 S root c.val)) <
      polygonEventParameter P ((DartPerm P hG2 S ^ (k+1)) (orbitEventAt P hG2 S root c.val)) := by
  let x := (DartPerm P hG2 S ^ k) (orbitEventAt P hG2 S root c.val)
  have hno := (cornerSuccessor_is_firstReturn P hG2 S hn root hroot c).2.2.2.2.2
  have hdestNC : ¬ retainedCorner P S (DartPerm P hG2 S x) := by
    simpa only [x,pow_succ',Equiv.Perm.mul_apply] using hno (k+1) (by omega) hk
  have hterminalNC : ¬ retainedCorner P S (polygonEventSuccessor P hG2 x) := by
    intro h
    exact hdestNC ((pairing_preserves_retained P S _).mpr h)
  have hstep : DartPerm P hG2 S x = polygonEventSuccessor P hG2 x :=
    pairing_fixes_noncorner P S _ hterminalNC
  have hlt : polygonEventParameter P x <
      polygonEventParameter P (polygonEventSuccessor P hG2 x) := by
    rcases polygonEventSuccessor_sameEdge_next_or_nextAnchor P hG2 hn x with h | h
    · exact h.2.1
    · exact (hterminalNC (h.1 ▸ True.intro)).elim
  simpa only [pow_succ',Equiv.Perm.mul_apply,← hstep] using hlt

theorem orbitPrefix_parameter_mono (c : CornerCoord P hG2 S root) (k l : ℕ)
    (hkl : k ≤ l)
    (hl : l < cornerGap P hG2 S root c.val (cornerSuccessor P hG2 S root c).val) :
    polygonEventParameter P ((DartPerm P hG2 S ^ k) (orbitEventAt P hG2 S root c.val)) ≤
      polygonEventParameter P ((DartPerm P hG2 S ^ l) (orbitEventAt P hG2 S root c.val)) := by
  induction hkl with
  | refl => exact le_rfl
  | @step l hkl ih =>
    exact (ih (by omega)).trans (orbitPrefix_parameter_step P hG2 S hn root hroot c l hl).le

/-- Every strict first-return prefix is inside the actual daughter parameter interval. -/
theorem orbitPrefix_parameter_bounds (c : CornerCoord P hG2 S root) (k : ℕ)
    (hk0 : 0 < k)
    (hk : k < cornerGap P hG2 S root c.val (cornerSuccessor P hG2 S root c).val) :
    polygonEventParameter P (orbitEventAt P hG2 S root c.val) <
      polygonEventParameter P ((DartPerm P hG2 S ^ k) (orbitEventAt P hG2 S root c.val)) ∧
    polygonEventParameter P ((DartPerm P hG2 S ^ k) (orbitEventAt P hG2 S root c.val)) <
      polygonEventParameter P (orbitEventAt P hG2 S root c.val) + daughterSideScale P hG2 S root c := by
  let d := cornerGap P hG2 S root c.val (cornerSuccessor P hG2 S root c).val
  let x := orbitEventAt P hG2 S root c.val
  let z := lastDartStart P hG2 S root c
  have hd : 0 < d := (cornerSuccessor_is_firstReturn P hG2 S hn root hroot c).1
  have hlast : d-1 < d := by omega
  have hpref := orbitPrefix_edge_parameter P hG2 S hn root hroot c (d-1) hlast
  have hedge : polygonEventEdge P z = polygonEventEdge P x := hpref.1
  constructor
  · have hfirst := orbitPrefix_parameter_step P hG2 S hn root hroot c 0 (by omega)
    have hmono := orbitPrefix_parameter_mono P hG2 S hn root hroot c 1 k (by omega) hk
    have hfirst' : polygonEventParameter P x < polygonEventParameter P ((DartPerm P hG2 S ^ 1) x) := by
      simpa only [pow_zero,Equiv.Perm.one_apply] using hfirst
    exact hfirst'.trans_le hmono
  · have hmono := orbitPrefix_parameter_mono P hG2 S hn root hroot c k (d-1) (by omega) hlast
    have hstep := (polygonEventSuccessor_positive_elementary_step P hG2 hn z).1
    have hterm : terminalParameterOn P (polygonEventEdge P x) (terminalEvent P hG2 z) =
        polygonEventSuccessorTerminalParameter P hG2 hn z := by
      rw [← hedge]
      exact terminalParameterOn_successor P hG2 hn z
    have hscale : daughterSideScale P hG2 S root c =
        polygonEventSuccessorTerminalParameter P hG2 hn z - polygonEventParameter P x := by
      change terminalParameterOn P (polygonEventEdge P x) (terminalEvent P hG2 z) -
        polygonEventParameter P x = _
      rw [hterm]
    change polygonEventParameter P ((DartPerm P hG2 S ^ k) x) ≤ polygonEventParameter P z at hmono
    change polygonEventParameter P ((DartPerm P hG2 S ^ k) x) <
      polygonEventParameter P x + daughterSideScale P hG2 S root c
    rw [hscale]
    linarith




end
end DirectGLSSW.DaughterPrefixParameters
