import DirectGLSSW.ShortEdgeSignStability
import DirectGLSSW.ShortEdgeWeighted
import DirectGLSSW.SpinorVertices
import DirectGLSSW.SpinorGates

namespace DirectGLSSW.ShortEdgeSignRealization

open DirectGLSSW
open DirectGLSSW.ShortEdgeCutFibers

noncomputable def coreHSign (q : ℕ → PlanarPoint ℝ) : ℕ → ℕ → ℕ → Sign :=
  fun i k j => if polygonHDet q i k j < 0 then .neg else .pos

noncomputable def shortSign (q : ℕ → PlanarPoint ℝ) (a : ℕ) (v : PlanarPoint ℝ) : ℕ → Sign :=
  fun x => if -planarDet v (q x - q a) < 0 then .neg else .pos

theorem coreHSign_value_eq_polygonSignArray
    (q : ℕ → PlanarPoint ℝ) (N : ℕ)
    (hcore : ShortEdgeSignStability.CoreHGeneric q N)
    (i k j : ℕ) (hik : i < k) (hkj : k < j) (hj : j ≤ N) :
    ShortEdgeWeighted.H0 (coreHSign q) i k j = polygonSignArray q i k j := by
  have hdet : polygonHDet q i k j ≠ 0 := hcore i k j hik hkj hj
  unfold ShortEdgeWeighted.H0 polygonSignArray coreHSign
  rw [scalarSignValue_eq_nonzeroScalarSign (polygonHDet q i k j) hdet]
  simp [nonzeroScalarSign]

theorem shortSign_value_eq_scaled_det
    (q : ℕ → PlanarPoint ℝ) (N a : ℕ) (v : PlanarPoint ℝ)
    (ε : ℝ) (hε : 0 < ε)
    (hdir : ShortEdgeSignStability.DirectionGeneric q N a v)
    (x : ℕ) (hx : x ≤ N) (hxa : x ≠ a) :
    (shortSign q a v x).value =
      scalarSignValue (-ε * planarDet v (q x - q a)) := by
  let d := planarDet v (q x - q a)
  have hd : d ≠ 0 := hdir x hx hxa
  have hprod : -ε * d ≠ 0 := mul_ne_zero (neg_ne_zero.mpr (ne_of_gt hε)) hd
  have hscale : (-ε * d < 0) ↔ (-d < 0) := by
    rw [show -ε * d = ε * (-d) by ring]
    constructor
    · intro h
      by_contra hn
      have hnonneg : 0 ≤ -d := le_of_not_gt hn
      have hproduct : 0 ≤ ε * (-d) := mul_nonneg (le_of_lt hε) hnonneg
      linarith
    · exact mul_neg_of_pos_of_neg hε
  have hsign : shortSign q a v x = nonzeroScalarSign (-ε * d) hprod := by
    unfold shortSign nonzeroScalarSign
    change (if -d < 0 then Sign.neg else Sign.pos) =
      (if -ε * d < 0 then Sign.neg else Sign.pos)
    exact if_congr hscale.symm rfl rfl
  rw [hsign, (scalarSignValue_eq_nonzeroScalarSign (-ε * d) hprod).symm]

theorem H1_eq_inserted_polygonSignArray
    (q : ℕ → PlanarPoint ℝ) (N a : ℕ) (v : PlanarPoint ℝ)
    (ε : ℝ) (hε : 0 < ε) (ha : a ≤ N)
    (hcore : ShortEdgeSignStability.CoreHGeneric q N)
    (hdir : ShortEdgeSignStability.DirectionGeneric q N a v)
    (hst : ShortEdgeSignStability.ShortEdgeStability q N a v ε ha hcore hdir)
    (i k j : ℕ) (hik : i < k) (hkj : k < j) (hj : j ≤ N + 1) :
    ShortEdgeWeighted.H1 a (shortSign q a v) (coreHSign q) i k j =
      polygonSignArray (ShortEdgeSignStability.insertAfter q a ε v) i k j := by
  by_cases hleft : k = a ∧ j = a + 1
  · have hi : i < a := by omega
    have hcollapse : collapseAfter a i = i := collapseAfter_eq_of_le a i (by omega)
    have hpair := hst.pairLeft i hi
    rw [ShortEdgeWeighted.H1]
    simp [hleft, hcollapse, polygonSignArray]
    rw [hpair]
    exact shortSign_value_eq_scaled_det q N a v ε hε hdir i (by omega) (by omega)
  · by_cases hright : i = a ∧ k = a + 1
    · have hy : a < j - 1 := by omega
      have hyN : j - 1 ≤ N := by omega
      have hcollapse : collapseAfter a j = j - 1 :=
        collapseAfter_eq_sub_one_of_lt a j (by omega)
      have hidx : j = (j - 1) + 1 := by omega
      have hpair := hst.pairRight (j - 1) hy hyN
      rw [ShortEdgeWeighted.H1]
      simp [hleft, hright, hcollapse, polygonSignArray]
      rw [hidx, hpair]
      exact shortSign_value_eq_scaled_det q N a v ε hε hdir (j - 1) hyN (by omega)
    · have hfar : ShortEdgeCutFibers.avoidsInsertedPair a i k j := by
        intro h
        rcases h with ⟨hA, hB⟩
        unfold ShortEdgeCutFibers.containsIndex at hA hB
        rcases hA with hiA | hkA | hjA <;>
          rcases hB with hiB | hkB | hjB <;> simp_all <;> omega
      have ho := ShortEdgeSignStability.collapseAfter_triple_order_bounded
        a i k j N ha hik hkj hj hfar
      let ci := collapseAfter a i
      let ck := collapseAfter a k
      let cj := collapseAfter a j
      have hc : polygonHDet q ci ck cj ≠ 0 := hcore ci ck cj ho.1 ho.2.1 ho.2.2
      have hp : polygonHDet (ShortEdgeSignStability.insertAfter q a ε v) i k j ≠ 0 :=
        hst.insertedG1 i k j hik hkj hj
      have hsign := hst.farSigns i k j hik hkj hj hfar
      have hsignVal := congrArg Sign.value hsign
      have hcoreVal :
          (polygonHSign q ci ck cj hc).value = polygonSignArray q ci ck cj := by
        unfold polygonHSign polygonSignArray
        exact (scalarSignValue_eq_nonzeroScalarSign (polygonHDet q ci ck cj) hc).symm
      have hparentVal :
          (polygonHSign (ShortEdgeSignStability.insertAfter q a ε v) i k j hp).value =
            polygonSignArray (ShortEdgeSignStability.insertAfter q a ε v) i k j := by
        unfold polygonHSign polygonSignArray
        exact (scalarSignValue_eq_nonzeroScalarSign
          (polygonHDet (ShortEdgeSignStability.insertAfter q a ε v) i k j) hp).symm
      have hvalues : polygonSignArray q ci ck cj =
          polygonSignArray (ShortEdgeSignStability.insertAfter q a ε v) i k j := by
        rw [← hcoreVal, ← hsignVal, hparentVal]
      rw [ShortEdgeWeighted.H1]
      simp only [if_neg hleft, if_neg hright]
      change ShortEdgeWeighted.H0 (coreHSign q) ci ck cj =
        polygonSignArray (ShortEdgeSignStability.insertAfter q a ε v) i k j
      rw [coreHSign_value_eq_polygonSignArray q N hcore ci ck cj
        ho.1 ho.2.1 ho.2.2]
      exact hvalues

end DirectGLSSW.ShortEdgeSignRealization
