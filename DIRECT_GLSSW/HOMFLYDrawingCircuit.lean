import HOMFLYPLArcIntersections
import Mathlib.Logic.Equiv.Fin.Rotate

/-! Actual finite simple circuits in the embedded drawing. The fields specify
only the selected vertices, arcs and their directions. No bounded region,
Jordan theorem, local move or evaluator identity is included in this data. -/

set_option autoImplicit false
namespace DirectGLSSW.HOMFLY
noncomputable section

def directedArcStart (D : PLLinkDiagram) (e : Fin D.nArc) (forward : Bool) :
    Fin D.nVertex := if forward then D.arcSource e else D.arcTarget e

def directedArcEnd (D : PLLinkDiagram) (e : Fin D.nArc) (forward : Bool) :
    Fin D.nVertex := if forward then D.arcTarget e else D.arcSource e

structure DrawingCircuit (D : PLLinkDiagram) where
  size : ℕ
  size_ge_three : 3 ≤ size
  vertex : Fin size ↪ Fin D.nVertex
  arc : Fin size ↪ Fin D.nArc
  forward : Fin size → Bool
  start_eq : ∀ i, directedArcStart D (arc i) (forward i) = vertex i
  end_eq : ∀ i, directedArcEnd D (arc i) (forward i) = vertex (finRotate size i)

namespace DrawingCircuit

def boundary {D : PLLinkDiagram} (P : DrawingCircuit D) : Set (PlanarPoint ℝ) :=
  ⋃ i : Fin P.size, Set.range (diagramArcPath D (P.arc i))

def followsContinuation {D : PLLinkDiagram} (P : DrawingCircuit D)
    (i : Fin P.size) : Prop :=
  (P.forward i = true ∧ P.forward (finRotate P.size i) = true ∧
    D.continuation (P.arc i) = P.arc (finRotate P.size i)) ∨
  (P.forward i = false ∧ P.forward (finRotate P.size i) = false ∧
    D.continuation (P.arc (finRotate P.size i)) = P.arc i)

/-- Counts switches between link strands, not ordinary polygonal bends. -/
def cornerCount {D : PLLinkDiagram} (P : DrawingCircuit D) : ℕ := by
  classical
  exact (Finset.univ.filter (fun i => ¬ P.followsContinuation i)).card

theorem vertexPoint_injective {D : PLLinkDiagram} (P : DrawingCircuit D) :
    Function.Injective (fun i => D.vertexPoint (P.vertex i)) :=
  D.vertexPoint_injective.comp P.vertex.injective

theorem mem_boundary_iff {D : PLLinkDiagram} (P : DrawingCircuit D)
    (z : PlanarPoint ℝ) : z ∈ P.boundary ↔
      ∃ i : Fin P.size, z ∈ Set.range (diagramArcPath D (P.arc i)) := by
  simp only [boundary, Set.mem_iUnion]

theorem vertex_mem_boundary {D : PLLinkDiagram} (P : DrawingCircuit D)
    (i : Fin P.size) : D.vertexPoint (P.vertex i) ∈ P.boundary := by
  apply (P.mem_boundary_iff _).2
  refine ⟨i,?_⟩
  have hs := P.start_eq i
  cases hforward : P.forward i with
  | false =>
      have he : D.arcTarget (P.arc i) = P.vertex i := by
        simpa only [directedArcStart, hforward, Bool.false_eq_true, if_false] using hs
      exact ⟨1, (diagramArcPath D (P.arc i)).target.trans (congrArg D.vertexPoint he)⟩
  | true =>
      have he : D.arcSource (P.arc i) = P.vertex i := by
        simpa only [directedArcStart, hforward, if_true] using hs
      exact ⟨0, (diagramArcPath D (P.arc i)).source.trans (congrArg D.vertexPoint he)⟩

theorem arc_endpoint_iff {D : PLLinkDiagram} (P : DrawingCircuit D)
    (i : Fin P.size) (v : Fin D.nVertex) :
    (D.arcSource (P.arc i) = v ∨ D.arcTarget (P.arc i) = v) ↔
      (P.vertex i = v ∨ P.vertex (finRotate P.size i) = v) := by
  have hs := P.start_eq i
  have he := P.end_eq i
  cases hforward : P.forward i with
  | false =>
      simp only [directedArcStart, directedArcEnd, hforward,
        Bool.false_eq_true, if_false] at hs he
      rw [hs, he]
      exact or_comm
  | true =>
      simp only [directedArcStart, directedArcEnd, hforward, if_true] at hs he
      rw [hs, he]

theorem nonadjacent_arc_ranges_disjoint {D : PLLinkDiagram} (P : DrawingCircuit D)
    (i j : Fin P.size) (hij : i ≠ j)
    (hnext : finRotate P.size i ≠ j) (hprev : finRotate P.size j ≠ i) :
    Disjoint (Set.range (diagramArcPath D (P.arc i)))
      (Set.range (diagramArcPath D (P.arc j))) := by
  apply Set.disjoint_left.2
  intro z hzi hzj
  have ha : P.arc i ≠ P.arc j := fun h => hij (P.arc.injective h)
  obtain ⟨v,hz,hiv,hjv⟩ :=
    (diagramArcPath_intersection_iff D (P.arc i) (P.arc j) ha z).1 ⟨hzi,hzj⟩
  rcases (P.arc_endpoint_iff i v).1 hiv with hi | hi <;>
    rcases (P.arc_endpoint_iff j v).1 hjv with hj | hj
  · exact hij (P.vertex.injective (hi.trans hj.symm))
  · exact hprev (P.vertex.injective (hj.trans hi.symm))
  · exact hnext (P.vertex.injective (hi.trans hj.symm))
  · exact hij ((finRotate P.size).injective (P.vertex.injective (hi.trans hj.symm)))

theorem boundary_isCompact {D : PLLinkDiagram} (P : DrawingCircuit D) :
    IsCompact P.boundary := by
  exact isCompact_iUnion (fun i => isCompact_range (diagramArcPath D (P.arc i)).continuous)

end DrawingCircuit
end
end DirectGLSSW.HOMFLY








