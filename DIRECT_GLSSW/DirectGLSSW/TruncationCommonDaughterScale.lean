import DirectGLSSW.DaughterFirstReturn
import DirectGLSSW.TruncationCommonScale

namespace DirectGLSSW.TruncationCommonDaughterScale

open DirectGLSSW
open DirectGLSSW.DaughterFirstReturn
open DirectGLSSW.TruncationCommonScale

theorem exists_positive_turn_scale_avoiding_all_daughter_vertex_lines
    {n : ℕ} (q : Fin n → PlanarPoint ℝ) (a p : Fin n)
    (hturn : 0 < planarDet (q a - q p)
      (q (cyclicSuccessor a) - q a)) :
    ∃ scale : ℝ, 0 < scale ∧
      (∀ e : PolygonEvent q, polygonEventPoint q e ≠ q a →
        planarDet (scale • (q (cyclicSuccessor a) - q a) - (q p - q a))
          (polygonEventPoint q e - q a) ≠ 0) ∧
      ∀ (S : Finset (PolygonCrossing q))
        (hG2 : cyclicNoTripleIntersections q) (root : PolygonEvent q)
        (i : Fin (Fintype.card (DaughterFirstReturn.CornerCoord q hG2 S root))),
        DaughterFirstReturn.daughterVertex q hG2 S root i ≠ q a →
          planarDet (scale • (q (cyclicSuccessor a) - q a) - (q p - q a))
            (DaughterFirstReturn.daughterVertex q hG2 S root i - q a) ≠ 0 := by
  let U : PlanarPoint ℝ := q p - q a
  let D : PlanarPoint ℝ := q (cyclicSuccessor a) - q a
  have hturnDet : planarDet (q a - q p) D = -planarDet U D := by
    simp [U, D, planarDet]
    ring
  have hUD : planarDet U D ≠ 0 := by
    intro hzero
    rw [hturnDet, hzero] at hturn
    norm_num at hturn
  obtain ⟨scale, hscale, havoid⟩ :=
    exists_positive_scale_avoiding_finite_point_lines (q a) U D hUD
      (fun e : PolygonEvent q => polygonEventPoint q e)
  refine ⟨scale, hscale, ?_, ?_⟩
  · intro e he
    exact havoid e he
  · intro S hG2 root i hi
    change polygonEventPoint q
      (orbitEventAt q hG2 S root (cornerEnumeration q hG2 S root i).val) ≠ q a at hi
    exact havoid _ hi



end DirectGLSSW.TruncationCommonDaughterScale
