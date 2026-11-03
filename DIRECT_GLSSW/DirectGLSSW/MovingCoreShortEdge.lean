
import DirectGLSSW.ShortEdgeSignStability
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

set_option maxHeartbeats 1000000

namespace DirectGLSSW.ShortEdgeSignStability

open DirectGLSSW
open DirectGLSSW.ShortEdgeCutFibers
open DirectGLSSW.ShortEdgeSignStability

private theorem nonzeroScalarSign_eq_of_negative_iff {x y : ℝ}
    (hx : x ≠ 0) (hy : y ≠ 0) (hneg : x < 0 ↔ y < 0) :
    nonzeroScalarSign x hx = nonzeroScalarSign y hy := by
  by_cases hxn : x < 0
  · have hyn : y < 0 := hneg.mp hxn
    simp [nonzeroScalarSign, hxn, hyn]
  · have hyn : ¬ y < 0 := fun h => hxn (hneg.mpr h)
    simp [nonzeroScalarSign, hxn, hyn]

private theorem notfar_triple_pair_cases (a i k j : ℕ)
    (hik : i < k) (hkj : k < j)
    (hboth : (i = a ∨ k = a ∨ j = a) ∧
      (i = a + 1 ∨ k = a + 1 ∨ j = a + 1)) :
    (i < a ∧ k = a ∧ j = a + 1) ∨
      (i = a ∧ k = a + 1 ∧ a + 1 < j) := by
  rcases hboth with ⟨⟨ha | ha | ha⟩, ⟨hb | hb | hb⟩⟩ <;>
    subst_vars <;> omega

private theorem exists_continuous_det_sign_radius (f : ℝ → ℝ)
    (hf : Continuous f) (hf0 : f 0 ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε < δ →
      f ε ≠ 0 ∧ (f ε < 0 ↔ f 0 < 0) := by
  by_cases hpos : 0 < f 0
  · let S : Set ℝ := {x | 0 < f x}
    have hopen : IsOpen S := isOpen_Ioi.preimage hf
    have hmem : 0 ∈ S := hpos
    obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp (hopen.mem_nhds hmem)
    refine ⟨δ, hδ, ?_⟩
    intro ε hε hεδ
    have hεpos : 0 < f ε := hball (by
      simpa [Metric.mem_ball, Real.dist_eq, abs_of_pos hε] using hεδ)
    refine ⟨ne_of_gt hεpos, ?_⟩
    simp [hεpos.not_lt, hpos.not_lt]
  · have hneg : f 0 < 0 := lt_of_le_of_ne (le_of_not_gt hpos) hf0
    let S : Set ℝ := {x | f x < 0}
    have hopen : IsOpen S := isOpen_Iio.preimage hf
    have hmem : 0 ∈ S := hneg
    obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp (hopen.mem_nhds hmem)
    refine ⟨δ, hδ, ?_⟩
    intro ε hε hεδ
    have hεneg : f ε < 0 := hball (by
      simpa [Metric.mem_ball, Real.dist_eq, abs_of_pos hε] using hεδ)
    exact ⟨ne_of_lt hεneg, ⟨fun _ => hneg, fun _ => hεneg⟩⟩

private theorem continuous_insertAfter_moving
    (Q : ℝ → ℕ → PlanarPoint ℝ) (N a : ℕ)
    (hQ : ∀ i, i ≤ N → Continuous (fun ε : ℝ => Q ε i))
    (haNlt : a < N) (v : PlanarPoint ℝ) (i : ℕ) (hi : i ≤ N + 1) :
    Continuous (fun ε : ℝ => insertAfter (Q ε) a ε v i) := by
  by_cases hle : i ≤ a
  · have hidx : i ≤ N := by omega
    simpa [insertAfter, hle] using hQ i hidx
  · by_cases hmid : i = a + 1
    · simp only [insertAfter, if_neg hle, if_pos hmid]
      have hQa := hQ a (by omega)
      exact (hQa.fst.add (continuous_id.mul continuous_const)).prodMk
        (hQa.snd.add (continuous_id.mul continuous_const))
    · have hidx : i - 1 ≤ N := by omega
      simpa [insertAfter, hle, hmid] using hQ (i - 1) hidx

theorem exists_moving_core_shortEdge_stability
    (Q : ℝ → ℕ → PlanarPoint ℝ) (N a : ℕ) (v : PlanarPoint ℝ)
    (hQ : ∀ i, i ≤ N → Continuous (fun ε : ℝ => Q ε i))
    (ha : 0 < a) (haNlt : a < N)
    (hcore0 : CoreHGeneric (Q 0) N)
    (hdir0 : DirectionGeneric (Q 0) N a v) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε < δ →
      ∃ hcore : CoreHGeneric (Q ε) N,
        ∃ hdir : DirectionGeneric (Q ε) N a v,
          ShortEdgeStability (Q ε) N a v ε (le_of_lt haNlt) hcore hdir := by
  classical
  let sCore : Finset (ℕ × ℕ × ℕ) :=
    Finset.range (N + 1) ×ˢ (Finset.range (N + 1) ×ˢ Finset.range (N + 1))
  let Pcore (tr : ℕ × ℕ × ℕ) (ε : ℝ) : Prop :=
    tr.1 < tr.2.1 → tr.2.1 < tr.2.2 → tr.2.2 ≤ N →
      polygonHDet (Q ε) tr.1 tr.2.1 tr.2.2 ≠ 0
  have hcorelocal : ∀ tr, tr ∈ sCore →
      ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε < δ → Pcore tr ε := by
    intro tr _
    by_cases hvalid : tr.1 < tr.2.1 ∧ tr.2.1 < tr.2.2 ∧ tr.2.2 ≤ N
    · let f : ℝ → ℝ := fun ε => polygonHDet (Q ε) tr.1 tr.2.1 tr.2.2
      have hiN : tr.1 ≤ N := by omega
      have hkN : tr.2.1 ≤ N := by omega
      have hjN : tr.2.2 ≤ N := by omega
      have hQi := hQ tr.1 hiN
      have hQk := hQ tr.2.1 hkN
      have hQj := hQ tr.2.2 hjN
      have hf : Continuous f := by
        dsimp [f, polygonHDet, planarDet]
        have hQi1 := hQi.fst
        have hQi2 := hQi.snd
        have hQk1 := hQk.fst
        have hQk2 := hQk.snd
        have hQj1 := hQj.fst
        have hQj2 := hQj.snd
        continuity
      have hf0 : f 0 ≠ 0 := hcore0 tr.1 tr.2.1 tr.2.2 hvalid.1 hvalid.2.1 hvalid.2.2
      obtain ⟨δ, hδ, hgood⟩ := exists_continuous_det_sign_radius f hf hf0
      exact ⟨δ, hδ, fun ε hε hεδ _ _ _ => (hgood ε hε hεδ).1⟩
    · refine ⟨1, by norm_num, ?_⟩
      intro ε hε hεδ hi hk hj
      exact False.elim (hvalid ⟨hi, hk, hj⟩)
  obtain ⟨δcore, hδcore, hcoredata⟩ := exists_finset_common_radius sCore Pcore hcorelocal

  let sDir : Finset ℕ := Finset.range (N + 1)
  let Pdir (x : ℕ) (ε : ℝ) : Prop :=
    x ≠ a → planarDet v (Q ε x - Q ε a) ≠ 0
  have hdirlocal : ∀ x, x ∈ sDir →
      ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε < δ → Pdir x ε := by
    intro x hxmem
    have hxN : x ≤ N := by
      have := Finset.mem_range.mp (by simpa [sDir] using hxmem)
      omega
    by_cases hxa : x ≠ a
    · let f : ℝ → ℝ := fun ε => planarDet v (Q ε x - Q ε a)
      have hQx := hQ x hxN
      have hQa := hQ a (by omega)
      have hf : Continuous f := by
        dsimp [f, planarDet]
        have hv1 : Continuous (fun _ : ℝ => v.1) := continuous_const
        have hv2 : Continuous (fun _ : ℝ => v.2) := continuous_const
        continuity
      have hf0 : f 0 ≠ 0 := hdir0 x hxN hxa
      obtain ⟨δ, hδ, hgood⟩ := exists_continuous_det_sign_radius f hf hf0
      exact ⟨δ, hδ, fun ε hε hεδ _ => (hgood ε hε hεδ).1⟩
    · refine ⟨1, by norm_num, ?_⟩
      intro ε hε hεδ hx
      exact False.elim (hxa hx)
  obtain ⟨δdir, hδdir, hdirdata⟩ := exists_finset_common_radius sDir Pdir hdirlocal

  let sFar := boundedTriples N
  let Pfar (tr : ℕ × ℕ × ℕ) (ε : ℝ) : Prop :=
    FarTriple N a tr.1 tr.2.1 tr.2.2 →
      polygonHDet (insertAfter (Q ε) a ε v) tr.1 tr.2.1 tr.2.2 ≠ 0 ∧
        (polygonHDet (insertAfter (Q ε) a ε v) tr.1 tr.2.1 tr.2.2 < 0 ↔
          polygonHDet (Q ε) (collapseAfter a tr.1) (collapseAfter a tr.2.1)
            (collapseAfter a tr.2.2) < 0)
  have hfarLocal : ∀ tr, tr ∈ sFar →
      ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε < δ → Pfar tr ε := by
    intro tr _
    by_cases hfar : FarTriple N a tr.1 tr.2.1 tr.2.2
    · rcases hfar with ⟨hik, hkj, hj, hAvoid⟩
      have ho := collapseAfter_triple_order_bounded a tr.1 tr.2.1 tr.2.2 N
        (le_of_lt haNlt) hik hkj hj hAvoid
      have hbase : polygonHDet (Q 0) (collapseAfter a tr.1)
          (collapseAfter a tr.2.1) (collapseAfter a tr.2.2) ≠ 0 :=
        hcore0 _ _ _ ho.1 ho.2.1 ho.2.2
      let fParent : ℝ → ℝ := fun t =>
        polygonHDet (insertAfter (Q t) a t v) tr.1 tr.2.1 tr.2.2
      let fCore : ℝ → ℝ := fun t =>
        polygonHDet (Q t) (collapseAfter a tr.1)
          (collapseAfter a tr.2.1) (collapseAfter a tr.2.2)
      have hParentCont : Continuous fParent := by
        have hi := continuous_insertAfter_moving Q N a hQ haNlt v tr.1 (by omega)
        have hk := continuous_insertAfter_moving Q N a hQ haNlt v tr.2.1 (by omega)
        have hj' := continuous_insertAfter_moving Q N a hQ haNlt v tr.2.2 (by omega)
        dsimp [fParent, polygonHDet, planarDet]
        have hi1 := hi.fst
        have hi2 := hi.snd
        have hk1 := hk.fst
        have hk2 := hk.snd
        have hj1 := hj'.fst
        have hj2 := hj'.snd
        continuity
      have hCoreCont : Continuous fCore := by
        dsimp [fCore, polygonHDet]
        have hiBound : collapseAfter a tr.1 ≤ N := by
          by_cases hle : tr.1 ≤ a
          · rw [collapseAfter_eq_of_le a tr.1 hle]
            omega
          · rw [collapseAfter_eq_sub_one_of_lt a tr.1 (by omega)]
            omega
        have hkBound : collapseAfter a tr.2.1 ≤ N := by
          by_cases hle : tr.2.1 ≤ a
          · rw [collapseAfter_eq_of_le a tr.2.1 hle]
            omega
          · rw [collapseAfter_eq_sub_one_of_lt a tr.2.1 (by omega)]
            omega
        have hjBound : collapseAfter a tr.2.2 ≤ N := by
          by_cases hle : tr.2.2 ≤ a
          · rw [collapseAfter_eq_of_le a tr.2.2 hle]
            omega
          · rw [collapseAfter_eq_sub_one_of_lt a tr.2.2 (by omega)]
            omega
        have hi := hQ (collapseAfter a tr.1) hiBound
        have hk := hQ (collapseAfter a tr.2.1) hkBound
        have hj' := hQ (collapseAfter a tr.2.2) hjBound
        dsimp [planarDet]
        have hi1 := hi.fst
        have hi2 := hi.snd
        have hk1 := hk.fst
        have hk2 := hk.snd
        have hj1 := hj'.fst
        have hj2 := hj'.snd
        continuity
      have hP0 : fParent 0 = fCore 0 := by
        change polygonHDet (insertAfter (Q 0) a 0 v) tr.1 tr.2.1 tr.2.2 =
          polygonHDet (Q 0) (collapseAfter a tr.1)
            (collapseAfter a tr.2.1) (collapseAfter a tr.2.2)
        have hq : insertAfter (Q 0) a 0 v =
            fun x => Q 0 (collapseAfter a x) := by
          funext x
          exact ShortEdgeSignStability.insertAfter_zero (Q 0) a x v
        rw [hq]
        rfl
      have hP0ne : fParent 0 ≠ 0 := by rw [hP0]; exact hbase
      obtain ⟨δp, hδp, hpsign⟩ :=
        exists_continuous_det_sign_radius fParent hParentCont hP0ne
      obtain ⟨δc, hδc, hcsign⟩ :=
        exists_continuous_det_sign_radius fCore hCoreCont hbase
      let δ := min δp δc
      have hδ : 0 < δ := lt_min hδp hδc
      refine ⟨δ, hδ, ?_⟩
      intro ε hε hεδ hf
      rcases hf with ⟨_, _, _, hFar⟩
      have hp := hpsign ε hε (lt_of_lt_of_le hεδ (min_le_left _ _))
      have hc := hcsign ε hε (lt_of_lt_of_le hεδ (min_le_right _ _))
      have hp0 : fParent 0 = fCore 0 := hP0
      refine ⟨?_, ?_⟩
      · exact hp.1
      · rw [show polygonHDet (insertAfter (Q ε) a ε v) tr.1 tr.2.1 tr.2.2 = fParent ε by rfl,
          show polygonHDet (Q ε) (collapseAfter a tr.1) (collapseAfter a tr.2.1)
            (collapseAfter a tr.2.2) = fCore ε by rfl]
        constructor
        · intro hpn
          have : fParent 0 < 0 := hp.2.mp hpn
          have : fCore 0 < 0 := by rw [← hp0]; exact this
          exact hc.2.mpr this
        · intro hcn
          have : fCore 0 < 0 := hc.2.mp hcn
          have : fParent 0 < 0 := by rw [hp0]; exact this
          exact hp.2.mpr this
    · refine ⟨1, by norm_num, ?_⟩
      intro ε hε hεδ hf
      exact False.elim (hfar hf)
  obtain ⟨δfar, hδfar, hfarData⟩ := exists_finset_common_radius sFar Pfar hfarLocal

  let δ := min (min δcore δdir) δfar
  have hδ : 0 < δ := by dsimp [δ]; positivity
  refine ⟨δ, hδ, ?_⟩
  intro ε hε hεδ
  have hδcore' : ε < δcore := lt_of_lt_of_le hεδ (le_trans (min_le_left _ _) (min_le_left _ _))
  have hδdir' : ε < δdir := lt_of_lt_of_le hεδ (le_trans (min_le_left _ _) (min_le_right _ _))
  have hδfar' : ε < δfar := lt_of_lt_of_le hεδ (min_le_right _ _)
  have hcore : CoreHGeneric (Q ε) N := by
    intro i k j hik hkj hj
    have hmem : (i, k, j) ∈ sCore := by
      simp only [sCore, Finset.mem_product, Finset.mem_range]
      omega
    exact hcoredata ε hε hδcore' (i, k, j) hmem hik hkj hj
  have hdir : DirectionGeneric (Q ε) N a v := by
    intro x hx hxa
    have hmem : x ∈ sDir := by
      simpa [sDir] using (Finset.mem_range.mpr (show x < N + 1 by omega))
    exact hdirdata ε hε hδdir' x hmem hxa
  let hfarAt (i k j : ℕ) (hik : i < k) (hkj : k < j)
      (hj : j ≤ N + 1) (hfar : avoidsInsertedPair a i k j) :=
    hfarData ε hε hδfar' (i, k, j) (by
      simp [sFar, boundedTriples]
      omega) ⟨hik, hkj, hj, hfar⟩
  refine ⟨hcore, hdir, ?_⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i k j hik hkj hj
    by_cases hfar : avoidsInsertedPair a i k j
    · exact (hfarAt i k j hik hkj hj hfar).1
    · have hboth :
          (i = a ∨ k = a ∨ j = a) ∧ (i = a + 1 ∨ k = a + 1 ∨ j = a + 1) := by
        apply not_not.mp
        simpa [avoidsInsertedPair, containsIndex] using hfar
      rcases hboth with ⟨hA, hB⟩
      have hpair := notfar_triple_pair_cases a i k j hik hkj ⟨hA, hB⟩
      rcases hpair with ⟨hleft, hk, hj'⟩ | ⟨hi', hk', hright⟩
      · subst k; subst j
        rw [polygonHDet_insertedPair_left (Q ε) a ε v i hleft]
        apply mul_ne_zero
        · exact neg_ne_zero.mpr (ne_of_gt hε)
        · exact hdir i (by omega) (by omega)
      · subst i; subst k
        have hidx : j = (j - 1) + 1 := by omega
        rw [hidx, polygonHDet_insertedPair_right (Q ε) a ε v (j - 1) (by omega)]
        apply mul_ne_zero
        · exact neg_ne_zero.mpr (ne_of_gt hε)
        · exact hdir (j - 1) (by omega) (by omega)
  · intro i k j hik hkj hj hfar
    have hData := hfarAt i k j hik hkj hj hfar
    have ho := collapseAfter_triple_order_bounded a i k j N
      (le_of_lt haNlt) hik hkj hj hfar
    have hCore := hcore _ _ _ ho.1 ho.2.1 ho.2.2
    have hNew := hData.1
    have hsign := nonzeroScalarSign_eq_of_negative_iff hNew hCore hData.2
    simpa [polygonHSign] using hsign
  · exact polygonHDet_insertedPair_left (Q ε) a ε v
  · exact fun y hy hyN => polygonHDet_insertedPair_right (Q ε) a ε v y hy

end DirectGLSSW.ShortEdgeSignStability
