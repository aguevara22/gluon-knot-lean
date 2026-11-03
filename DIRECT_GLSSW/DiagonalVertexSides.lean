import DiagonalCornerExistence

set_option autoImplicit false
namespace DirectGLSSW.HOMFLY.PrincipalTurning
noncomputable section
attribute [local instance] Classical.propDecidable

structure DiagonalCornerData {D : PLLinkDiagram} (T : BasedTraversal D)
    (C : diagramComponent D) (k : Fin (componentArcLength D (T.baseArc C).val)) where
  a0 : ℝ
  a : ℝ
  b : ℝ
  b1 : ℝ
  h0 : secantAxisAdjacent T C a0 a
  ha : secantAxisAdjacent T C a ((k.val : ℝ)+1/2)
  hb : secantAxisAdjacent T C ((k.val : ℝ)+1/2) b
  h1 : secantAxisAdjacent T C b b1

def actualDiagonalCornerData {D : PLLinkDiagram} (T : BasedTraversal D)
    (C : diagramComponent D) (k : Fin (componentArcLength D (T.baseArc C).val)) :
    DiagonalCornerData T C k := Classical.choice (by
  obtain ⟨a0,a,b,b1,h0,ha,hb,h1⟩ := diagonalCorner_neighbours_exist T C k
  exact ⟨⟨a0,a,b,b1,h0,ha,hb,h1⟩⟩)

def actualDiagonalVertexSide {D : PLLinkDiagram} (T : BasedTraversal D)
    (C : diagramComponent D)
    (x : Fin (componentArcLength D (T.baseArc C).val) × Fin 2) : RetainedRectangleSide T C :=
  let q := actualDiagonalCornerData T C x.1
  if x.2=0 then diagonalCornerRightSide T C q.a0 q.a ((x.1.val : ℝ)+1/2) q.b q.h0 q.ha q.hb
  else diagonalCornerBottomSide T C q.a ((x.1.val : ℝ)+1/2) q.b q.b1 q.ha q.hb q.h1

theorem actualDiagonalVertexSide_diagonal {D : PLLinkDiagram} (T : BasedTraversal D)
    (C : diagramComponent D)
    (x : Fin (componentArcLength D (T.baseArc C).val) × Fin 2) :
    rectangleDiagonalNeighbour (actualDiagonalVertexSide T C x) := by
  have h := diagonalCornerSides_diagonal T C _ _ _ _ _
    (actualDiagonalCornerData T C x.1).h0 (actualDiagonalCornerData T C x.1).ha
    (actualDiagonalCornerData T C x.1).hb (actualDiagonalCornerData T C x.1).h1
  dsimp only [actualDiagonalVertexSide]
  split_ifs
  · exact h.1
  · exact h.2

theorem actualDiagonalVertexSide_injective {D : PLLinkDiagram} (T : BasedTraversal D)
    (C : diagramComponent D) : Function.Injective (actualDiagonalVertexSide T C) := by
  rintro ⟨k,s⟩ ⟨l,t⟩ he
  have hs := congrArg Prod.snd he
  have hc := congrArg (fun e : RetainedRectangleSide T C => e.1.val) he
  fin_cases s <;> fin_cases t
  · have hp := congrArg (fun r : (ℝ×ℝ)×(ℝ×ℝ) => r.2.1) hc
    simp [actualDiagonalVertexSide,diagonalCornerRightSide] at hp
    have hkl : k=l := Fin.ext hp
    subst l
    rfl
  · simp [actualDiagonalVertexSide,diagonalCornerRightSide,diagonalCornerBottomSide] at hs
  · simp [actualDiagonalVertexSide,diagonalCornerRightSide,diagonalCornerBottomSide] at hs
  · have hp := congrArg (fun r : (ℝ×ℝ)×(ℝ×ℝ) => r.1.2) hc
    simp [actualDiagonalVertexSide,diagonalCornerBottomSide] at hp
    have hkl : k=l := Fin.ext hp
    subst l
    rfl

theorem actualDiagonalVertexSide_pair_sum {D : PLLinkDiagram} (T : BasedTraversal D)
    (C : diagramComponent D) (k : Fin (componentArcLength D (T.baseArc C).val)) :
    (∑ s : Fin 2, rectangleSideIncrement (actualDiagonalVertexSide T C (k,s))) =
      turn D ((D.continuation ^ (k.val : ℤ)) (T.baseArc C).val) := by
  rw [Fin.sum_univ_two]
  have h := diagonalCornerSides_sum T C (k.val : ℤ) _ _ _ _
    (actualDiagonalCornerData T C k).h0 (actualDiagonalCornerData T C k).ha
    (actualDiagonalCornerData T C k).hb (actualDiagonalCornerData T C k).h1
  simpa [actualDiagonalVertexSide] using h

end
end DirectGLSSW.HOMFLY.PrincipalTurning



