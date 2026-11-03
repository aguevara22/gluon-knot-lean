import FreeCursorClosedSides
import ActiveArcCornerMovingGammaM
import CursorIntervalConstancy
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace DirectGLSSW.ActiveArc.CornerProjector
open Cursor Split Primitive RetainedWords EndpointEventGeometry OpenFirstEdgeGeometry
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {b : ℕ} (q : Fin (1+b+2) → PlanarPoint ℝ) (hR : Regular q)
variable (hfree : ∀ c : Crossing q, c.val.1≠0)

theorem corner_approach_word_eq_move_root_on
    (T : Support (suffix q) (regular_suffix q hR)) (t : ℝ)
    (k : ℕ) (hk : k≤openCount (suffix q) (regular_suffix q hR) T.val) :
    approach (fun j => if j=0 then q 0 else rootedPolygonWord
      (OpenVertex (suffix q) (regular_suffix q hR) T)
      (openLast (suffix q) (regular_suffix q hR) T.val) (j-1)) (1-t) k =
    moveEndpoint (rootedPolygonWord (OpenVertex q hR (firstEdgeFreeSupportEquiv q hfree hR T))
      (openLast q hR (firstEdgeFreeSupportEquiv q hfree hR T).val)) (q 1-q 0) t k := by
  have hcount := corner_openCount q hR hfree T
  have hk' : k<openCount q hR (firstEdgeFreeSupportEquiv q hfree hR T).val := by omega
  by_cases hz : k=0
  · subst k
    rw [approach_zero]
    simp only [moveEndpoint,if_pos rfl,show (1:ℕ)≠0 by decide,if_false,Nat.sub_self]
    rw [corner_rootedWord_zero q hR hfree T]
    have hw := openCurrent_word (suffix q) (regular_suffix q hR) T 0
      (lt_of_lt_of_le (by decide : 0<2) (open_count_ge_two _ _ T.val))
    rw [openVertex_zero] at hw
    have hs : suffix q 0=q 1 := by simp [suffix,Split.vertex]
    rw [hw,hs]
    ext <;> dsimp [affinePoint] <;> ring
  · rw [approach_pos _ (1-t) (Nat.pos_of_ne_zero hz)]
    simp only [moveEndpoint,if_neg hz]
    simpa only [if_neg hz] using (corner_rootedWord_prefix q hR hfree T k hk').symm

/-- No-crossing first-edge ΓM constancy, using the actual unchanged suffix
support/closed-factor transport. Endpoint Core is explicit at this stage. -/
theorem firstEdgeFree_GammaM_constancy_pos (hRI : GLSSWRootIndependence)
    (hAux : ClosedAuxiliary q hR) (t : ℝ) (ht : 0<t) (ht1 : t<1)
    (hcore : ∀ U : Support q hR, ShortEdgeSignStability.CoreHGeneric
      (rootedPolygonWord (OpenVertex q hR U) (openLast q hR U.val)) (openCount q hR U.val-1))
    (hcoret : ∀ U : Support q hR, ShortEdgeSignStability.CoreHGeneric
      (moveEndpoint (rootedPolygonWord (OpenVertex q hR U) (openLast q hR U.val)) (q 1-q 0) t)
      (openCount q hR U.val-1)) :
    GammaM (moveStart q t) (firstEdgeFree_regular_moveStart q hR hfree t (le_of_lt ht) ht1)
      (firstEdgeFree_closedAuxiliary_moveStart q hR hfree hAux t (le_of_lt ht) ht1) = GammaM q hR hAux := by
  have hm := firstEdgeFree_moving_GammaM_eq_weighted_approach q hR hfree hAux hRI (1-t) (by linarith) (by linarith)
  dsimp only at hm
  have ht' : 1-(1-t)=t := by ring
  simp only [ht'] at hm
  rw [hm,firstEdgeFree_GammaM_eq_weighted_suffix q hR hfree hRI hAux]
  apply Finset.sum_congr rfl
  intro T _
  let U := firstEdgeFreeSupportEquiv q hfree hR T
  let W := rootedPolygonWord (OpenVertex q hR U) (openLast q hR U.val)
  let P := fun k => if k=0 then q 0 else rootedPolygonWord
    (OpenVertex (suffix q) (regular_suffix q hR) T) (openLast (suffix q) (regular_suffix q hR) T.val) (k-1)
  let N := openCount (suffix q) (regular_suffix q hR) T.val
  have hN : openCount q hR U.val-1=N := by
    dsimp [U,N]
    rw [corner_openCount q hR hfree T]
    omega
  have hNpos : 0<N := lt_of_lt_of_le (by decide : 0<2) (open_count_ge_two _ _ T.val)
  have hv := CursorWallTransport.openCurrent_constancy_on_first_line W (q 1-q 0)
    (openCount q hR U.val-1) (by rw [hN];exact hNpos) t (le_of_lt ht) (hcore U) (hcoret U)
    (open_word_first_direction q hR U).1
    (firstEdgeFree_closed_side_avoidance q hR hfree t (le_of_lt ht) ht1 U (hcore U))
  rw [hN] at hv
  have he : OpenMarkedCurrent.entry (polygonSignArray (approach P (1-t))) 0 N =
      OpenMarkedCurrent.entry (polygonSignArray (moveEndpoint W (q 1-q 0) t)) 0 N := by
    apply openMarkedCurrent_entry_congr_of_word_eq _ _ hNpos
    intro k hk
    exact corner_approach_word_eq_move_root_on q hR hfree T t k hk
  have hb : OpenMarkedCurrent.entry (polygonSignArray W) 0 N =
      OpenMarkedCurrent.entry (polygonSignArray P) 0 N := by
    apply openMarkedCurrent_entry_congr_of_word_eq _ _ hNpos
    intro k hk
    exact corner_rootedWord_prefix q hR hfree T k (by rw [corner_openCount q hR hfree T];change k < N+1;omega)
  have hh := he.trans (hv.symm.trans hb)
  change (-1:ℚ)^T.val.card * (OpenMarkedCurrent.entry (polygonSignArray (approach P (1-t))) 0 N * _) =
    (-1:ℚ)^T.val.card * (OpenMarkedCurrent.entry (polygonSignArray P) 0 N * _)
  rw [hh]
end DirectGLSSW.ActiveArc.CornerProjector
