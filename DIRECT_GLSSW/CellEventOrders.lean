import SelectedCellClippedWord

set_option autoImplicit false
namespace DirectGLSSW.CellEventOrders
open SelectedCellClippedWord MixedConsecutiveCapWord InteriorEdgeEvents OrderedCapEvents

variable {n : ℕ}

/-- Actual endpoint and crossing specifications force both orders of each selected cell,
including the sole cell of empty support. -/
theorem actual_cell_orders (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (e : Fin n) (hU : (q (cyclicSuccessor e)).2 = 0) (hV : (q e).2 = 0)
    (hleft : (q (cyclicSuccessor e)).1 < (q e).1)
    (Q : ℕ → PlanarPoint ℝ) (N : ℕ) (cU cV : EventIndex Q N)
    (F : DirectGLSSW.EdgeChord q e → EventIndex Q N)
    (htU : eventTime Q N cU = 0)
    (htV : eventTime Q N cV = (q e).1-(q (cyclicSuccessor e)).1)
    (hpU : eventPair Q N cU = (1,2)) (hpV : eventPair Q N cV = (n-1,n))
    (hF : ∀ z, eventTime Q N (F z) = (crossingPoint q z.val).1-(q (cyclicSuccessor e)).1 ∧
      eventPair Q N (F z) = (returnRank q e z+1,returnRank q e z+2))
    (L : List (DirectGLSSW.EdgeChord q e)) (hL : OrderedEdgeSupport q hq e L)
    (i : Fin (L.length+1)) :
    let a := leftBoundary cU F L i
    let b := rightBoundary cV F L i
    a < b ∧ (eventPair Q N a).1 < (eventPair Q N b).1 := by
  dsimp only
  have ht : eventTime Q N (leftBoundary cU F L i) <
      eventTime Q N (rightBoundary cV F L i) := by
    by_cases hi0 : i.val=0
    · simp only [leftBoundary,dif_pos hi0]
      rw [htU]
      by_cases hiL : i.val < L.length
      · simp only [rightBoundary,dif_pos hiL,(hF _).1]
        exact sub_pos.mpr (edgeChord_point_bounds q e hU hV hleft _).2.1
      · simp only [rightBoundary,dif_neg hiL,htV]
        exact sub_pos.mpr hleft
    · by_cases hiL : i.val < L.length
      · simp only [leftBoundary,rightBoundary,dif_neg hi0,dif_pos hiL,(hF _).1]
        apply sub_lt_sub_right
        exact ((List.pairwise_iff_get.mp hL.2) ⟨i.val-1,by omega⟩ ⟨i.val,hiL⟩
          (by change i.val-1 < i.val; omega)).1
      · simp only [leftBoundary,rightBoundary,dif_neg hi0,dif_neg hiL,(hF _).1,htV]
        apply sub_lt_sub_right
        exact (edgeChord_point_bounds q e hU hV hleft _).2.2
  have hpa : (eventPair Q N (leftBoundary cU F L i)).1 =
      leftBoundary 1 (fun z => returnRank q e z+1) L i := by
    unfold leftBoundary
    split
    · exact congrArg Prod.fst hpU
    · exact congrArg Prod.fst (hF _).2
  have hpb : (eventPair Q N (rightBoundary cV F L i)).1 =
      rightBoundary (n-1) (fun z => returnRank q e z+1) L i := by
    unfold rightBoundary
    split
    · exact congrArg Prod.fst (hF _).2
    · exact congrArg Prod.fst hpV
  refine ⟨(eventTime_strictMono Q N).lt_iff_lt.mp ht,?_⟩
  rw [hpa,hpb]
  exact (cell_anchor_interval q hq e L hL i).2.1

end DirectGLSSW.CellEventOrders

