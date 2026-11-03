import ActiveArcCutCrossings
import ActiveArcPhysicalWords

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.ExposedChart
open DirectGLSSW ExposedOpenPrimitive
variable {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ) (e : Fin (n+2))
variable (hq : CyclicGeneric q) (he : LeftExposed q e)

theorem active_visitBool_injective (c : ActiveArc.Crossing (cutArc q e)) :
    Function.Injective (fun b : Bool => ActiveArc.visitEdge (cutArc q e) (c,b)) := by
  intro a b hab
  cases a <;> cases b
  · rfl
  · exact False.elim ((ne_of_lt c.property.1) hab)
  · exact False.elim ((ne_of_lt c.property.1) hab.symm)
  · rfl

theorem original_visitBool_injective (c : PolygonCrossing q) :
    Function.Injective (fun b : Bool => crossingVisitEdge q (c,b)) := by
  intro a b hab
  cases a <;> cases b
  · rfl
  · exact False.elim ((crossing_edges_ne q c) hab)
  · exact False.elim ((crossing_edges_ne q c) hab.symm)
  · rfl

/-- The target Boolean tag is determined by the actual incident edge, not copied. -/
theorem exists_visitBool (c : ActiveArc.Crossing (cutArc q e)) (b : Bool) :
    ∃ a : Bool, crossingVisitEdge q (exposedCrossingEquiv q e hq he c,a)=
      edgeLabel e (ActiveArc.visitEdge (cutArc q e) (c,b)) := by
  rcases crossingEquiv_visit_edge q e hq c b with hl|hr
  · exact ⟨false,hl.symm⟩
  · exact ⟨true,hr.symm⟩

def visitBool (c : ActiveArc.Crossing (cutArc q e)) (b : Bool) : Bool :=
  Classical.choose (exists_visitBool q e hq he c b)

theorem visitBool_edge (c : ActiveArc.Crossing (cutArc q e)) (b : Bool) :
    crossingVisitEdge q (exposedCrossingEquiv q e hq he c,visitBool q e hq he c b)=
      edgeLabel e (ActiveArc.visitEdge (cutArc q e) (c,b)) :=
  Classical.choose_spec (exists_visitBool q e hq he c b)

theorem visitBool_injective (c : ActiveArc.Crossing (cutArc q e)) :
    Function.Injective (visitBool q e hq he c) := by
  intro a b hab
  apply active_visitBool_injective q e c
  apply edgeLabel_injective e
  rw [← visitBool_edge q e hq he c a,← visitBool_edge q e hq he c b,hab]

def visitBoolEquiv (c : ActiveArc.Crossing (cutArc q e)) : Bool ≃ Bool :=
  Equiv.ofBijective (visitBool q e hq he c)
    (Finite.injective_iff_bijective.mp (visitBool_injective q e hq he c))

/-- The actual visit equivalence includes the uniquely derived per-crossing swap. -/
def visitEquiv : ActiveArc.Visit (cutArc q e) ≃ CrossingVisit q where
  toFun v := (exposedCrossingEquiv q e hq he v.1,visitBoolEquiv q e hq he v.1 v.2)
  invFun v := ((exposedCrossingEquiv q e hq he).symm v.1,
    (visitBoolEquiv q e hq he ((exposedCrossingEquiv q e hq he).symm v.1)).symm v.2)
  left_inv v := by simp
  right_inv v := by simp

theorem visitEquiv_crossing (v : ActiveArc.Visit (cutArc q e)) :
    (visitEquiv q e hq he v).1=exposedCrossingEquiv q e hq he v.1 := rfl

theorem visitEquiv_edge (v : ActiveArc.Visit (cutArc q e)) :
    crossingVisitEdge q (visitEquiv q e hq he v)=edgeLabel e (ActiveArc.visitEdge (cutArc q e) v) :=
  visitBool_edge q e hq he v.1 v.2

theorem visitEquiv_point (v : ActiveArc.Visit (cutArc q e)) :
    crossingVisitPoint q (visitEquiv q e hq he v)=ActiveArc.crossingPoint (cutArc q e) v.1 :=
  crossingEquiv_point q e hq v.1

theorem boolEquiv_not (E : Bool ≃ Bool) (b : Bool) : E (!b)=!(E b) := by
  have hn : E (!b)≠E b := fun hh => Bool.not_ne_self b (E.injective hh)
  cases hb : E b <;> cases hnb : E (!b) <;> simp_all

theorem visitEquiv_flip (c : ActiveArc.Crossing (cutArc q e)) (b : Bool) :
    visitEquiv q e hq he (c,!b)=crossingVisitFlip q (visitEquiv q e hq he (c,b)) := by
  apply Prod.ext
  · rfl
  · exact boolEquiv_not (visitBoolEquiv q e hq he c) b

theorem visitEquiv_parameter (v : ActiveArc.Visit (cutArc q e)) :
    crossingVisitParameter q (visitEquiv q e hq he v)=ActiveArc.visitParameter (cutArc q e) v := by
  have ho := (crossingVisitParameter_spec q (visitEquiv q e hq he v)).2.2
  rw [visitEquiv_point,visitEquiv_edge] at ho
  have ha := (ActiveArc.visitParameter_spec (cutArc q e) v).2.2
  simp only [cutArc,edgeLabel_successor] at ha
  have heq : affinePoint ((cutArc q e) (ActiveArc.visitEdge (cutArc q e) v).castSucc)
      ((cutArc q e) (ActiveArc.visitEdge (cutArc q e) v).succ)
      (crossingVisitParameter q (visitEquiv q e hq he v))=
    affinePoint ((cutArc q e) (ActiveArc.visitEdge (cutArc q e) v).castSucc)
      ((cutArc q e) (ActiveArc.visitEdge (cutArc q e) v).succ)
      (ActiveArc.visitParameter (cutArc q e) v) := by
    rw [cutArc,cutArc,edgeLabel_successor]
    exact ho.symm.trans ha
  exact edge_parameter_unique _ (cutArc_regular q e hq) _ _ _ heq

end DirectGLSSW.ActiveArc.ExposedChart
