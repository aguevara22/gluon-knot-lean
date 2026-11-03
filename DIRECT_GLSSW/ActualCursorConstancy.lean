import CursorIntervalConstancy
import ActualCursorClosedSides
import ActiveArcPhysicalCurrentTransport
import GammaMReindex
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.Primitive
open Cursor RetainedWords EndpointEventGeometry
variable {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ) (hR : Regular q)
variable (c : Crossing q) (hc : FirstCrossing q c)
include hc

/-- Exact event-centered and original-endpoint parameterizations of the same
physical retained word. No word equality is supplied. -/
theorem before_first_event_word_eq_move_root (U : Support q hR) (t : ℝ) :
    moveEndpoint (eventOpenWord q hR U c) (q 1-q 0) (t-leftParameter q c) =
      moveEndpoint (rootedPolygonWord (OpenVertex q hR U) (openLast q hR U.val)) (q 1-q 0) t := by
  have hn := open_count_ge_two q hR U.val
  have hx := (leftParameter_spec q c).2.2
  rw [hc.1] at hx
  have hz : rootedPolygonWord (OpenVertex q hR U) (openLast q hR U.val) 0=q 0 := by
    rw [openCurrent_word q hR U 0 (by omega),openVertex_zero]
  funext i
  by_cases hi : i=0
  · subst i
    simp only [moveEndpoint,if_pos rfl,eventOpenWord_zero,hz,hx]
    ext <;> dsimp [affinePoint] <;> ring
  · simp only [moveEndpoint,eventOpenWord,if_neg hi]

/-- Actual support-current transport through the entire no-crossing cursor
interval. Only the two endpoint finite sign domains are supplied; all virtual
walls, support geometry and word transport are discharged. -/
theorem before_first_openCurrent_constancy
    (t : ℝ) (ht0 : 0≤t) (htc : t<leftParameter q c) (U : Support q hR)
    (hcore : ShortEdgeSignStability.CoreHGeneric
      (rootedPolygonWord (OpenVertex q hR U) (openLast q hR U.val)) (openCount q hR U.val-1))
    (hcoret : ShortEdgeSignStability.CoreHGeneric
      (moveEndpoint (rootedPolygonWord (OpenVertex q hR U) (openLast q hR U.val)) (q 1-q 0) t)
      (openCount q hR U.val-1)) :
    openCurrent (moveStart q t) (before_first_regular (a:=n) (b:=0) q hR c hc t ht0 htc)
      ((BeforeFirst.supportEquiv q hR c hc t ht0 htc).symm U) = openCurrent q hR U := by
  have hn := open_count_ge_two q hR U.val
  have hval := CursorWallTransport.openCurrent_constancy_on_first_line
    (rootedPolygonWord (OpenVertex q hR U) (openLast q hR U.val)) (q 1-q 0)
    (openCount q hR U.val-1) (by omega) t ht0 hcore hcoret
    (open_word_first_direction q hR U).1
    (before_first_cursor_closed_side_avoidance q hR c hc t ht0 htc U hcore)
  rw [before_first_openCurrent_eq_event q hR c hc t ht0 htc U,
    before_first_event_word_eq_move_root q hR c hc U t]
  exact hval.symm

/-- Full physical ΓM transport on the explicit endpoint auxiliary sign domain.
The same actual support equivalence and all closed factors are transported by
the accepted before-first geometric/weight APIs. -/
theorem before_first_GammaM_constancy
    (hRI : GLSSWRootIndependence) (hAux : ClosedAuxiliary q hR)
    (t : ℝ) (ht0 : 0≤t) (htc : t<leftParameter q c)
    (hcore : ∀ U : Support q hR, ShortEdgeSignStability.CoreHGeneric
      (rootedPolygonWord (OpenVertex q hR U) (openLast q hR U.val)) (openCount q hR U.val-1))
    (hcoret : ∀ U : Support q hR, ShortEdgeSignStability.CoreHGeneric
      (moveEndpoint (rootedPolygonWord (OpenVertex q hR U) (openLast q hR U.val)) (q 1-q 0) t)
      (openCount q hR U.val-1)) :
    GammaM (moveStart q t) (before_first_regular (a:=n) (b:=0) q hR c hc t ht0 htc)
      (BeforeFirst.closedAuxiliary q hR c hc t ht0 htc hAux) = GammaM q hR hAux := by
  classical
  rw [BeforeFirst.GammaM_eq_reindexed_original_support q hR c hc t ht0 htc hRI hAux]
  unfold GammaM
  apply Finset.sum_congr rfl
  intro U hU
  rw [before_first_openCurrent_constancy q hR c hc t ht0 htc U (hcore U) (hcoret U)]

/-- The actual list length is unchanged during a cursor motion, so the same
transport holds for the manuscript's vertex-parity normalized ΓM. -/
theorem before_first_normalized_GammaM_constancy
    (hRI : GLSSWRootIndependence) (hAux : ClosedAuxiliary q hR)
    (t : ℝ) (ht0 : 0≤t) (htc : t<leftParameter q c)
    (hcore : ∀ U : Support q hR, ShortEdgeSignStability.CoreHGeneric
      (rootedPolygonWord (OpenVertex q hR U) (openLast q hR U.val)) (openCount q hR U.val-1))
    (hcoret : ∀ U : Support q hR, ShortEdgeSignStability.CoreHGeneric
      (moveEndpoint (rootedPolygonWord (OpenVertex q hR U) (openLast q hR U.val)) (q 1-q 0) t)
      (openCount q hR U.val-1)) :
    (-1 : ℚ)^(List.ofFn (moveStart q t)).length *
      GammaM (moveStart q t) (before_first_regular (a:=n) (b:=0) q hR c hc t ht0 htc)
        (BeforeFirst.closedAuxiliary q hR c hc t ht0 htc hAux) =
      (-1 : ℚ)^(List.ofFn q).length * GammaM q hR hAux := by
  rw [before_first_GammaM_constancy q hR c hc hRI hAux t ht0 htc hcore hcoret]
  simp only [List.length_ofFn]

end DirectGLSSW.ActiveArc.Primitive
