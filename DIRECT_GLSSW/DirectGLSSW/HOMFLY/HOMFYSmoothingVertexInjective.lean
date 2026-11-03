import DirectGLSSW.HOMFLY.HOMFYSmoothingCutpointInteriors
import Mathlib.Tactic.FinCases

namespace DirectGLSSW.HOMFLY

/-- Geometric point assignment for cutpoint labels: right cut label `j` is
placed on the outgoing arc `j`, using the strand matched to it by `through`. -/
def smoothVertexPointGeometryCode (D : PLLinkDiagram) (c : Fin D.nCrossing) (ε : ℝ) :
    SmoothVertexCode D → PlanarPoint ℝ
  | Sum.inl v => if v = D.crossingVertex c then incomingCutPoint D c ε 0 else D.vertexPoint v
  | Sum.inr i => if i = 0 then incomingCutPoint D c ε 1 else
      if i = 1 then outgoingCutPoint D c ε ((D.through c).symm 0) else
        outgoingCutPoint D c ε ((D.through c).symm 1)

def smoothCutLabelCode (D : PLLinkDiagram) (c : Fin D.nCrossing) : Fin 4 → SmoothVertexCode D
  | 0 => Sum.inl (D.crossingVertex c)
  | 1 => Sum.inr ⟨0, by omega⟩
  | 2 => Sum.inr ⟨1, by omega⟩
  | 3 => Sum.inr ⟨2, by omega⟩

def smoothCutLabelArc (D : PLLinkDiagram) (c : Fin D.nCrossing) : Fin 4 → Fin D.nArc
  | 0 => D.incoming c 0
  | 1 => D.incoming c 1
  | 2 => D.outgoing c 0
  | 3 => D.outgoing c 1

theorem smoothCutLabelCode_injective (D : PLLinkDiagram) (c : Fin D.nCrossing) :
    Function.Injective (smoothCutLabelCode D c) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [smoothCutLabelCode]

theorem smoothCutLabelArc_injective (D : PLLinkDiagram) (c : Fin D.nCrossing) :
    Function.Injective (smoothCutLabelArc D c) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [smoothCutLabelArc]
  all_goals
    first
    | exact False.elim ((D.four_ports_distinct c).1 hij)
    | exact False.elim ((D.four_ports_distinct c).1 hij.symm)
    | exact False.elim ((D.four_ports_distinct c).2.1 hij)
    | exact False.elim ((D.four_ports_distinct c).2.1 hij.symm)
    | exact False.elim (((D.four_ports_distinct c).2.2 0 0) hij)
    | exact False.elim (((D.four_ports_distinct c).2.2 0 0) hij.symm)
    | exact False.elim (((D.four_ports_distinct c).2.2 0 1) hij)
    | exact False.elim (((D.four_ports_distinct c).2.2 0 1) hij.symm)
    | exact False.elim (((D.four_ports_distinct c).2.2 1 0) hij)
    | exact False.elim (((D.four_ports_distinct c).2.2 1 0) hij.symm)
    | exact False.elim (((D.four_ports_distinct c).2.2 1 1) hij)
    | exact False.elim (((D.four_ports_distinct c).2.2 1 1) hij.symm)

theorem smoothCutLabel_interior (D : PLLinkDiagram) (c : Fin D.nCrossing)
    (ε : ℝ) (hε : 0 < ε) (hεr : ε < crossingCutoffRadius D c) (k : Fin 4) :
    ∃ t, 0 < t ∧ t < 1 ∧
      smoothVertexPointGeometryCode D c ε (smoothCutLabelCode D c k) =
        DirectGLSSW.affinePoint (D.vertexPoint (D.arcSource (smoothCutLabelArc D c k)))
          (D.vertexPoint (D.arcTarget (smoothCutLabelArc D c k))) t := by
  fin_cases k
  · simpa [smoothCutLabelCode, smoothCutLabelArc, smoothVertexPointGeometryCode,
      smoothingCenter, D.incoming_target] using
      smoothIncomingCutPoint_interior D c ε hε hεr 0
  · simpa [smoothCutLabelCode, smoothCutLabelArc, smoothVertexPointGeometryCode,
      smoothingCenter, D.incoming_target] using
      smoothIncomingCutPoint_interior D c ε hε hεr 1
  · let i := (D.through c).symm 0
    have hi : D.through c i = 0 := Equiv.apply_symm_apply (D.through c) 0
    simpa [smoothCutLabelCode, smoothCutLabelArc, smoothVertexPointGeometryCode, i, hi,
      smoothingCenter, D.outgoing_source] using
      smoothOutgoingCutPoint_interior D c ε hε hεr i
  · let i := (D.through c).symm 1
    have hi : D.through c i = 1 := Equiv.apply_symm_apply (D.through c) 1
    simpa [smoothCutLabelCode, smoothCutLabelArc, smoothVertexPointGeometryCode, i, hi,
      smoothingCenter, D.outgoing_source] using
      smoothOutgoingCutPoint_interior D c ε hε hεr i

theorem smoothVertexPointGeometryCode_cutpoint_or_old (D : PLLinkDiagram) (c : Fin D.nCrossing)
    (x : SmoothVertexCode D) :
    (∃ k, x = smoothCutLabelCode D c k) ∨
      (∃ v, x = Sum.inl v ∧ v ≠ D.crossingVertex c) := by
  rcases x with v | i
  · by_cases hv : v = D.crossingVertex c
    · left
      exact ⟨0, by simp [smoothCutLabelCode, hv]⟩
    · exact Or.inr ⟨v, rfl, hv⟩
  · fin_cases i
    · exact Or.inl ⟨1, rfl⟩
    · exact Or.inl ⟨2, rfl⟩
    · exact Or.inl ⟨3, rfl⟩

theorem smoothVertexPointGeometryCode_injective (D : PLLinkDiagram) (c : Fin D.nCrossing)
    (ε : ℝ) (hε : 0 < ε) (hεr : ε < crossingCutoffRadius D c) :
    Function.Injective (smoothVertexPointGeometryCode D c ε) := by
  classical
  intro x y hxy
  have hx := smoothVertexPointGeometryCode_cutpoint_or_old D c x
  have hy := smoothVertexPointGeometryCode_cutpoint_or_old D c y
  rcases hx with ⟨k, hx⟩ | ⟨v, hx, hvc⟩
  · rcases hy with ⟨l, hy⟩ | ⟨w, hy, hwc⟩
    · subst x
      subst y
      rcases smoothCutLabel_interior D c ε hε hεr k with ⟨s, hs0, hs1, hs⟩
      rcases smoothCutLabel_interior D c ε hε hεr l with ⟨t, ht0, ht1, ht⟩
      by_cases he : smoothCutLabelArc D c k = smoothCutLabelArc D c l
      · have hkl := smoothCutLabelArc_injective D c he
        subst l
        rfl
      · have hpoints := hs.symm.trans (hxy.trans ht)
        exact False.elim ((D.arc_interiors_disjoint (smoothCutLabelArc D c k)
          (smoothCutLabelArc D c l) he s t hs0 hs1 ht0 ht1) hpoints)
    · subst x
      subst y
      rcases smoothCutLabel_interior D c ε hε hεr k with ⟨t, ht0, ht1, ht⟩
      have hpoint : D.vertexPoint w =
          DirectGLSSW.affinePoint (D.vertexPoint (D.arcSource (smoothCutLabelArc D c k)))
            (D.vertexPoint (D.arcTarget (smoothCutLabelArc D c k))) t := by
        simpa [smoothVertexPointGeometryCode, hwc] using hxy.symm.trans ht
      exact False.elim (D.vertices_avoid_arc_interiors w (smoothCutLabelArc D c k) t ht0 ht1 hpoint)
  · rcases hy with ⟨l, hy⟩ | ⟨w, hy, hwc⟩
    · subst x
      subst y
      rcases smoothCutLabel_interior D c ε hε hεr l with ⟨t, ht0, ht1, ht⟩
      have hpoint : D.vertexPoint v =
          DirectGLSSW.affinePoint (D.vertexPoint (D.arcSource (smoothCutLabelArc D c l)))
            (D.vertexPoint (D.arcTarget (smoothCutLabelArc D c l))) t := by
        simpa [smoothVertexPointGeometryCode, hvc] using hxy.trans ht
      exact False.elim (D.vertices_avoid_arc_interiors v (smoothCutLabelArc D c l) t ht0 ht1 hpoint)
    · subst x
      subst y
      have hpoint : D.vertexPoint v = D.vertexPoint w := by
        simpa [smoothVertexPointGeometryCode, hvc, hwc] using hxy
      have hvw := D.vertexPoint_injective hpoint
      subst w
      rfl

end DirectGLSSW.HOMFLY
