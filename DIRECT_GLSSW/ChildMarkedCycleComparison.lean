import MarkedNextOrder
import FirstDetachedChildRestrictionPortOrder
import ComponentRestrictionConnected
import FirstDetachedChildRestrictionSigns

set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
namespace DirectGLSSW.HOMFLY
attribute [local instance] Classical.propDecidable

/-- The two incoming ports at every distinct actual crossing are all distinct. -/
theorem incomingMark_injective (D : PLLinkDiagram) :
    Function.Injective (fun m : Fin D.nCrossing × Fin 2 => D.incoming m.1 m.2) := by
  rintro ⟨c,i⟩ ⟨d,j⟩ h
  change D.incoming c i=D.incoming d j at h
  have hcd : c=d := D.crossingVertex_injective (by
    rw [← D.incoming_target c i,← D.incoming_target d j,h])
  subst d
  have hij : i=j := by
    fin_cases i <;> fin_cases j
    · rfl
    · exact False.elim ((D.four_ports_distinct c).1 h)
    · exact False.elim ((D.four_ports_distinct c).1 h.symm)
    · rfl
  subst j
  rfl

namespace PolygonDrawingBridge
variable {n : ℕ} (q : Fin n → PlanarPoint ℝ) (hQ : CyclicGeneric q)

/-- The actual positive diagram's arcs carry their original increasing event coordinates. -/
def positivePolygonArcRank : Fin (positivePolygonEventDiagram q hQ).nArc ≃
    Fin (Fintype.card (PolygonEvent q)) :=
  (eventFin q).symm.trans (polygonEventEnumeration q hQ.g2).toEquiv.symm

theorem positivePolygonArcRank_step (x : Fin (positivePolygonEventDiagram q hQ).nArc) :
    positivePolygonArcRank q hQ ((positivePolygonEventDiagram q hQ).continuation x)=
      cyclicSuccessorPerm _ (positivePolygonArcRank q hQ x) := by
  letI:=polygonEventOrder q hQ.g2
  simp only [positivePolygonArcRank,Equiv.trans_apply,positivePolygonEventDiagram,positiveDiagram,
    polygonEventDiagram,successorArc,eventSuccessor,Equiv.symm_apply_apply]
  change (polygonEventEnumeration q hQ.g2).symm
    (polygonEventSuccessor q hQ.g2 ((eventFin q).symm x)) = _
  rw [polygonEventSuccessor_apply]
  simp only [OrderIso.symm_apply_apply]
  rfl

theorem positivePolygonArcRank_incoming_lt_iff (d e : PolygonCrossing q) (i j : Fin 2) :
    positivePolygonArcRank q hQ ((positivePolygonEventDiagram q hQ).incoming (crossingFin q d) i)<
      positivePolygonArcRank q hQ ((positivePolygonEventDiagram q hQ).incoming (crossingFin q e) j) ↔
    (polygonEventOrder q hQ.g2).lt (PolygonDrawing.visit q d i) (PolygonDrawing.visit q e j) := by
  letI:=polygonEventOrder q hQ.g2
  simp only [positivePolygonArcRank,Equiv.trans_apply,positivePolygonEventDiagram,positiveDiagram,
    polygonEventDiagram,incomingIndex,Equiv.symm_apply_apply]
  exact ((polygonEventEnumeration q hQ.g2).symm.lt_iff_lt).trans
    (polygon_incoming_lt_iff_visit_lt q hQ d e i j)
end PolygonDrawingBridge
end DirectGLSSW.HOMFLY

namespace DirectGLSSW.ActiveArc.Split
open HOMFLY HOMFLY.PolygonDrawingBridge HOMFLY.LowestRowContract PermutationOrbits MarkedCycleGaps
attribute [local instance] Classical.propDecidable
variable {a b : ℕ} (q : Fin (a+b+2) → PlanarPoint ℝ) (hQ : CyclicGeneric q) (hR : Regular q)
variable (c : Crossing q) (hfirst : c.val.1=0) (hcut : c.val.2.val=a)
variable (R : ComponentRestriction
  (smoothCrossing (positivePolygonEventDiagram q hQ) (crossingFin q (polygonCrossingOfArc q c)))
  (positiveSmoothedChildComponent q hQ (polygonCrossingOfArc q c)))
variable (hChild : CyclicGeneric (child q hR c hfirst hcut))

/-- Common actual crossing-port labels, independent of the two diagrams' arc counts. -/
abbrev FirstChildMark := PolygonCrossing (child q hR c hfirst hcut) × Fin 2

/-- Actual incoming restriction arcs labelled by physical child crossing and branch. -/
def firstChildRestrictionMark (m : FirstChildMark q hR c hfirst hcut) : Fin R.diagram.nArc :=
  R.diagram.incoming
    (R.crossingEquiv.symm (firstDetachedChildCrossingEquiv q hQ hR c hfirst hcut m.1)) m.2

/-- Actual incoming positive child diagram arcs with exactly the same labels. -/
def firstChildPolygonMark (m : FirstChildMark q hR c hfirst hcut) :
    Fin (positivePolygonEventDiagram (child q hR c hfirst hcut) hChild).nArc :=
  (positivePolygonEventDiagram (child q hR c hfirst hcut) hChild).incoming
    (crossingFin (child q hR c hfirst hcut) m.1) m.2

theorem firstChildRestrictionMark_injective :
    Function.Injective (firstChildRestrictionMark q hQ hR c hfirst hcut R) := by
  intro x y h
  have he:=@incomingMark_injective R.diagram
    (R.crossingEquiv.symm (firstDetachedChildCrossingEquiv q hQ hR c hfirst hcut x.1),x.2)
    (R.crossingEquiv.symm (firstDetachedChildCrossingEquiv q hQ hR c hfirst hcut y.1),y.2) h
  apply Prod.ext
  · exact (firstDetachedChildCrossingEquiv q hQ hR c hfirst hcut).injective
      (R.crossingEquiv.symm.injective (congrArg Prod.fst he))
  · exact congrArg (fun z : Fin R.diagram.nCrossing × Fin 2=>z.2) he

theorem firstChildPolygonMark_injective :
    Function.Injective (firstChildPolygonMark q hR c hfirst hcut hChild) := by
  intro x y h
  have he:=@incomingMark_injective (positivePolygonEventDiagram (child q hR c hfirst hcut) hChild)
    (crossingFin (child q hR c hfirst hcut) x.1,x.2)
    (crossingFin (child q hR c hfirst hcut) y.1,y.2) h
  exact Prod.ext ((crossingFin _).injective (congrArg Prod.fst he)) (congrArg (fun z : Fin (positivePolygonEventDiagram (child q hR c hfirst hcut) hChild).nCrossing × Fin 2=>z.2) he)

/-- Connectedness is derived from the exact full-component restriction. -/
theorem firstChildRestriction_isCycleOn : R.diagram.continuation.IsCycleOn Set.univ := by
  refine ⟨R.diagram.continuation.bijective.bijOn_univ,?_⟩
  intro x _ y _
  exact R.continuation_sameCycle x y

/-- The two actual diagrams have the same rooted order of marked incoming ports. -/
theorem firstChildMark_rank_lt_iff (m n : FirstChildMark q hR c hfirst hcut) :
    fullOrbitRank R.diagram.continuation (firstChildRestriction_isCycleOn q hQ c R)
      (firstDetachedChildRestrictionRoot q hQ c R) (firstChildRestrictionMark q hQ hR c hfirst hcut R m)<
    fullOrbitRank R.diagram.continuation (firstChildRestriction_isCycleOn q hQ c R)
      (firstDetachedChildRestrictionRoot q hQ c R) (firstChildRestrictionMark q hQ hR c hfirst hcut R n) ↔
    positivePolygonArcRank (child q hR c hfirst hcut) hChild (firstChildPolygonMark q hR c hfirst hcut hChild m)<
    positivePolygonArcRank (child q hR c hfirst hcut) hChild (firstChildPolygonMark q hR c hfirst hcut hChild n) := by
  unfold firstChildPolygonMark
  rw [positivePolygonArcRank_incoming_lt_iff]
  have h:=firstDetachedChildRestriction_incoming_orbitPosition_lt_iff q hQ hR c hfirst hcut R m.1 n.1 m.2 n.2
  change ((orbitEnumeration R.diagram.continuation (firstDetachedChildRestrictionRoot q hQ c R)).symm _).val <
    ((orbitEnumeration R.diagram.continuation (firstDetachedChildRestrictionRoot q hQ c R)).symm _).val ↔ _
  exact h

/-- Through-pairing, over-branch and determinant-derived sign agree on each common label. -/
theorem firstChild_marked_crossing_data (d : PolygonCrossing (child q hR c hfirst hcut)) :
    R.diagram.through (R.crossingEquiv.symm (firstDetachedChildCrossingEquiv q hQ hR c hfirst hcut d)) =
      (positivePolygonEventDiagram (child q hR c hfirst hcut) hChild).through (crossingFin _ d) ∧
    R.diagram.overBranch (R.crossingEquiv.symm (firstDetachedChildCrossingEquiv q hQ hR c hfirst hcut d)) =
      (positivePolygonEventDiagram (child q hR c hfirst hcut) hChild).overBranch (crossingFin _ d) ∧
    crossingSign R.diagram (R.crossingEquiv.symm (firstDetachedChildCrossingEquiv q hQ hR c hfirst hcut d)) =
      crossingSign (positivePolygonEventDiagram (child q hR c hfirst hcut) hChild) (crossingFin _ d) :=
  ⟨firstDetachedChildRestriction_through q hQ hR c hfirst hcut R hChild d,
    firstDetachedChildRestriction_overBranch q hQ hR c hfirst hcut R hChild d,
    firstDetachedChildRestriction_sign_correspondence q hQ hR c hfirst hcut R hChild d⟩

/-- The actual restriction and physical child have identical next crossing-port labels;
no unmarked gap-length inequality or permutation equality is assumed. -/
theorem firstChild_marked_next_eq :
    next R.diagram.continuation (firstChildRestrictionMark q hQ hR c hfirst hcut R)
      (firstChildRestrictionMark_injective q hQ hR c hfirst hcut R)=
    next (positivePolygonEventDiagram (child q hR c hfirst hcut) hChild).continuation
      (firstChildPolygonMark q hR c hfirst hcut hChild)
      (firstChildPolygonMark_injective q hR c hfirst hcut hChild) := by
  exact next_eq_of_coordinate_order _ _
    (fullOrbitRank R.diagram.continuation (firstChildRestriction_isCycleOn q hQ c R)
      (firstDetachedChildRestrictionRoot q hQ c R))
    (positivePolygonArcRank (child q hR c hfirst hcut) hChild)
    (fullOrbitRank_step _ _ _) (positivePolygonArcRank_step _ _)
    _ _ _ _ (firstChildMark_rank_lt_iff q hQ hR c hfirst hcut R hChild)
end DirectGLSSW.ActiveArc.Split
