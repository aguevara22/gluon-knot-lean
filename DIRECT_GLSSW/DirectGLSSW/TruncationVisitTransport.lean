import DirectGLSSW.PolygonEvents
import DirectGLSSW.TruncationCrossingEquivalence

namespace DirectGLSSW.TruncationDirection

open DirectGLSSW
open DirectGLSSW.TruncationEdgeLift

noncomputable def crossingVisit_mapEquiv {n m : ℕ}
    {q : Fin n → PlanarPoint ℝ} {Q : Fin m → PlanarPoint ℝ}
    (E : PolygonCrossing q ≃ PolygonCrossing Q) :
    CrossingVisit q ≃ CrossingVisit Q :=
  { toFun := fun v => (E v.1, v.2)
    invFun := fun v => (E.symm v.1, v.2)
    left_inv := by rintro ⟨c, b⟩; simp
    right_inv := by rintro ⟨c, b⟩; simp }

theorem crossingVisit_mapEquiv_edge {n : ℕ}
    (q : Fin n → PlanarPoint ℝ) (a p : Fin n) (scale ε : ℝ)
    (E : PolygonCrossing q ≃
      PolygonCrossing (truncateCyclicCorner q a p scale ε))
    (hleft : ∀ c, (E c).val.1 = edgeLift a c.val.1)
    (hright : ∀ c, (E c).val.2 = edgeLift a c.val.2)
    (v : CrossingVisit q) :
    crossingVisitEdge (truncateCyclicCorner q a p scale ε)
      (crossingVisit_mapEquiv E v) = edgeLift a (crossingVisitEdge q v) := by
  rcases v with ⟨c, b⟩
  cases b <;> simp [crossingVisitEdge, crossingVisit_mapEquiv] <;>
    first | exact hleft c | exact hright c

theorem crossingVisit_mapEquiv_point {n m : ℕ}
    {q : Fin n → PlanarPoint ℝ} {Q : Fin m → PlanarPoint ℝ}
    (E : PolygonCrossing q ≃ PolygonCrossing Q)
    (hpoint : ∀ c, crossingPoint Q (E c) = crossingPoint q c)
    (v : CrossingVisit q) :
    crossingVisitPoint Q (crossingVisit_mapEquiv E v) = crossingVisitPoint q v := by
  rcases v with ⟨c, b⟩
  exact hpoint c

theorem crossingVisit_mapEquiv_flip {n m : ℕ}
    {q : Fin n → PlanarPoint ℝ} {Q : Fin m → PlanarPoint ℝ}
    (E : PolygonCrossing q ≃ PolygonCrossing Q) (v : CrossingVisit q) :
    crossingVisit_mapEquiv E (crossingVisitFlip q v) =
      crossingVisitFlip Q (crossingVisit_mapEquiv E v) := by
  rcases v with ⟨c, b⟩
  cases b <;> rfl

theorem crossingVisit_parameter_transport {n : ℕ}
    (hn : 3 ≤ n) (q : Fin n → PlanarPoint ℝ) (a p : Fin n)
    (hp : cyclicSuccessor p = a) (scale ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hscale : 0 < ε * scale)
    (hscale1 : ε * scale < 1) (hq : CyclicGeneric q)
    (E : PolygonCrossing q ≃
      PolygonCrossing (truncateCyclicCorner q a p scale ε))
    (hleft : ∀ c, (E c).val.1 = edgeLift a c.val.1)
    (hright : ∀ c, (E c).val.2 = edgeLift a c.val.2)
    (hpoint : ∀ c, crossingPoint (truncateCyclicCorner q a p scale ε) (E c) =
      crossingPoint q c) (v : CrossingVisit q) :
    oldEdgeParameter a p (crossingVisitEdge q v) ε scale
      (crossingVisitParameter (truncateCyclicCorner q a p scale ε)
        (crossingVisit_mapEquiv E v)) = crossingVisitParameter q v := by
  let Q : Fin (n + 1) → PlanarPoint ℝ := truncateCyclicCorner q a p scale ε
  let v' := crossingVisit_mapEquiv E v
  let e := crossingVisitEdge q v
  let tp := crossingVisitParameter Q v'
  have he : crossingVisitEdge Q v' = edgeLift a e := by
    dsimp [Q, v', e]
    exact crossingVisit_mapEquiv_edge q a p scale ε E hleft hright v
  have hpt : crossingVisitPoint Q v' = crossingVisitPoint q v := by
    dsimp [Q, v']
    exact crossingVisit_mapEquiv_point E hpoint v
  have hpspec := crossingVisitParameter_spec Q v'
  have hqspec := crossingVisitParameter_spec q v
  have hgeom := truncateCyclicCorner_edge_affineParameter
    (by omega) q a p hp scale ε hε hε1 hscale hscale1 e tp
  have hsame : affinePoint (q e) (q (cyclicSuccessor e))
      (oldEdgeParameter a p e ε scale tp) =
      affinePoint (q e) (q (cyclicSuccessor e)) (crossingVisitParameter q v) := by
    calc
      affinePoint (q e) (q (cyclicSuccessor e))
          (oldEdgeParameter a p e ε scale tp) =
          affinePoint (Q (edgeLift a e))
            (Q (cyclicSuccessor (edgeLift a e))) tp := by
              symm
              simpa [Q, e, tp, he] using hgeom
      _ = crossingVisitPoint Q v' := by
            have hspec' : crossingVisitPoint Q v' =
                affinePoint (Q (edgeLift a e))
                  (Q (cyclicSuccessor (edgeLift a e))) tp := by
              simpa [tp, he] using hpspec.2.2
            exact hspec'.symm
      _ = crossingVisitPoint q v := hpt
      _ = affinePoint (q e) (q (cyclicSuccessor e))
            (crossingVisitParameter q v) := hqspec.2.2
  have hnondeg : q e ≠ q (cyclicSuccessor e) := by
    intro h
    have ht := cyclic_turn_det_ne_zero hn q hq.g1 e
    have htan : cyclicTangent q e = (0 : PlanarPoint ℝ) := by
      simp [cyclicTangent, h]
    rw [htan] at ht
    simp [planarDet] at ht
  exact (affinePoint_injective (q e) (q (cyclicSuccessor e)) hnondeg) hsame

end DirectGLSSW.TruncationDirection
