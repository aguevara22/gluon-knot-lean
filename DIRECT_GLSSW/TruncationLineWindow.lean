import DirectGLSSW.TruncationPointGeometry
import PolygonGermStability
import LocalCarrierLineAlgebra
import ExposedEdgeGeometry

set_option autoImplicit false
noncomputable section

namespace DirectGLSSW.SourceTruncationLineWindow

open DirectGLSSW DirectGLSSW.TruncationDirection DirectGLSSW.ExposedOpenPrimitive
  DirectGLSSW.AuxiliaryCarrierChart DirectGLSSW.ShortEdgeCyclicAdapter
  DirectGLSSW.ShortEdgeCutFibers Filter Topology

/-- Near the actual supported truncation carrier, the line's intersections
with the two original incident rays recover a positive truncation scale and
parameter. These recovered truncations retain the actual G1/G2 and supporting
short-edge properties on a nonempty open carrier window. -/
theorem exists_open_supported_truncation_line_window {n : ℕ}
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (a p : Fin n) (hp : cyclicSuccessor p = a)
    (hturn : 0 < planarDet (q a-q p) (q (cyclicSuccessor a)-q a))
    (scale0 eps0 : ℝ) (hs0 : 0 < scale0) (he0 : 0 < eps0)
    (he01 : eps0 < 1) (hes0 : eps0 * scale0 < 1)
    (hQ0 : CyclicGeneric (truncateCyclicCorner q a p scale0 eps0))
    (hleft0 : LeftExposed (truncateCyclicCorner q a p scale0 eps0) a.castSucc) :
    let U : PlanarPoint ℝ := q p-q a
    let D : PlanarPoint ℝ := q (cyclicSuccessor a)-q a
    let v0 : PlanarPoint ℝ := scale0 • D-U
    let K0 : CarrierLine :=
      (v0, -planarDet v0 (q a+eps0 • U))
    let recoveredEpsilon : CarrierLine → ℝ := fun K =>
      -lineValue K (q a) / planarDet K.1 U
    let recoveredScale : CarrierLine → ℝ := fun K =>
      planarDet K.1 U / planarDet K.1 D
    let truncation : CarrierLine → Fin (n+1) → PlanarPoint ℝ := fun K =>
      truncateCyclicCorner q a p (recoveredScale K) (recoveredEpsilon K)
    ∃ W : Set CarrierLine, IsOpen W ∧ K0 ∈ W ∧
      ∀ K ∈ W,
        0 < recoveredEpsilon K ∧ recoveredEpsilon K < 1 ∧
        0 < recoveredScale K ∧ 0 < recoveredEpsilon K*recoveredScale K ∧
        recoveredEpsilon K*recoveredScale K < 1 ∧
        CyclicGeneric (truncation K) ∧
        LeftExposed (truncation K) a.castSucc ∧
        lineValue K (truncation K a.castSucc)=0 ∧
        lineValue K (truncation K ⟨a.val+1, by have := a.isLt; omega⟩)=0 := by
  classical
  dsimp only
  let U : PlanarPoint ℝ := q p-q a
  let D : PlanarPoint ℝ := q (cyclicSuccessor a)-q a
  let v0 : PlanarPoint ℝ := scale0 • D-U
  let K0 : CarrierLine := (v0,-planarDet v0 (q a+eps0 • U))
  let recoveredEpsilon : CarrierLine → ℝ := fun K =>
    -lineValue K (q a) / planarDet K.1 U
  let recoveredScale : CarrierLine → ℝ := fun K =>
    planarDet K.1 U / planarDet K.1 D
  let truncation : CarrierLine → Fin (n+1) → PlanarPoint ℝ := fun K =>
    truncateCyclicCorner q a p (recoveredScale K) (recoveredEpsilon K)

  have hUD : 0 < planarDet D U := by
    have heq : planarDet D U = planarDet (q a-q p) (q (cyclicSuccessor a)-q a) := by
      simp [D,U,planarDet]
      ring
    rw [heq]
    exact hturn
  have hdetU : planarDet v0 U = scale0*planarDet D U := by
    simp [v0,planarDet]
    ring
  have hdetD : planarDet v0 D = planarDet D U := by
    simp [v0,planarDet]
    ring
  have hu0 : 0 < planarDet v0 U := by rw [hdetU]; exact mul_pos hs0 hUD
  have hd0 : 0 < planarDet v0 D := by rw [hdetD]; exact hUD
  have hline_affine (K : CarrierLine) (t : ℝ) (X : PlanarPoint ℝ) :
      lineValue K (q a+t • X) = lineValue K (q a)+t*planarDet K.1 X := by
    simp [AuxiliaryCarrierChart.lineValue,planarDet,Prod.fst_add,Prod.snd_add,
      Prod.smul_fst,Prod.smul_snd]
    ring
  have hline0 : lineValue K0 (q a) = -(eps0*planarDet v0 U) := by
    have hzero : lineValue K0 (q a+eps0 • U)=0 := by
      simp [K0,AuxiliaryCarrierChart.lineValue]
    have hformula := hline_affine K0 eps0 U
    rw [hzero] at hformula
    linarith
  have heps0 : recoveredEpsilon K0 = eps0 := by
    change -lineValue K0 (q a) / planarDet K0.1 U = eps0
    have hnum : -lineValue K0 (q a) = eps0*planarDet K0.1 U := by
      rw [hline0]
      ring
    rw [hnum]
    field_simp [ne_of_gt hu0]
  have hscale0 : recoveredScale K0 = scale0 := by
    change planarDet v0 U / planarDet v0 D = scale0
    rw [hdetU,hdetD]
    field_simp [ne_of_gt hUD]
  have htrunc0 : truncation K0 = truncateCyclicCorner q a p scale0 eps0 := by
    simp [truncation,heps0,hscale0]

  have huCont : ContinuousAt (fun K : CarrierLine => planarDet K.1 U) K0 := by
    unfold planarDet
    fun_prop
  have hdCont : ContinuousAt (fun K : CarrierLine => planarDet K.1 D) K0 := by
    unfold planarDet
    fun_prop

  have hepsCont : ContinuousAt recoveredEpsilon K0 := by
    have hn : ContinuousAt (fun K : CarrierLine => -lineValue K (q a)) K0 := by
      unfold AuxiliaryCarrierChart.lineValue planarDet
      fun_prop
    exact ContinuousAt.div hn huCont (ne_of_gt hu0)

  have hscaleCont : ContinuousAt recoveredScale K0 := by
    unfold recoveredScale
    apply ContinuousAt.div
    · exact huCont
    · exact hdCont
    · exact ne_of_gt hd0

  have hpointCont (i : Fin (n+1)) :
      ContinuousAt (fun K : CarrierLine => truncation K i) K0 := by
    have hnew : cyclicSuccessor a.castSucc =
        (⟨a.val+1, by have := a.isLt; omega⟩ : Fin (n+1)) :=
      cyclicSuccessor_shortEdge a
    by_cases hi : i=a.castSucc
    · subst i
      have hval (K : CarrierLine) :
          truncateCyclicCorner q a p (recoveredScale K) (recoveredEpsilon K) a.castSucc =
            q a+recoveredEpsilon K • U := by
        simpa [U] using truncateCyclicCorner_anchor q a p
          (recoveredScale K) (recoveredEpsilon K)
      have hfun : (fun K : CarrierLine => truncation K a.castSucc) =
          (fun K => q a+recoveredEpsilon K • U) := funext hval
      rw [hfun]
      fun_prop
    · by_cases hj : i=⟨a.val+1, by have := a.isLt; omega⟩
      · subst i
        have hval (K : CarrierLine) :
            truncateCyclicCorner q a p (recoveredScale K) (recoveredEpsilon K)
              ⟨a.val+1, by have := a.isLt; omega⟩ =
                q a+(recoveredEpsilon K*recoveredScale K) • D := by
          simpa [D] using truncateCyclicCorner_new q a p
            (recoveredScale K) (recoveredEpsilon K)
        have hfun : (fun K : CarrierLine =>
            truncation K ⟨a.val+1, by have := a.isLt; omega⟩) =
          (fun K => q a+(recoveredEpsilon K*recoveredScale K) • D) := funext hval
        rw [hfun]
        fun_prop
      · have hcollapse : collapseFin a i ≠ a := by
          intro hc
          rcases (collapseFin_eq_a_iff a i).mp hc with hc | hc
          · exact hi hc
          · exact hj hc
        have hval (K : CarrierLine) :
            truncateCyclicCorner q a p (recoveredScale K) (recoveredEpsilon K) i =
              q (collapseFin a i) :=
          truncateCyclicCorner_of_collapse_ne q a p (recoveredScale K)
            (recoveredEpsilon K) i hcollapse
        have hfun : (fun K : CarrierLine => truncation K i) =
            (fun _ => q (collapseFin a i)) := funext hval
        rw [hfun]
        exact continuousAt_const

  have hgenEvent : ∀ᶠ K : CarrierLine in 𝓝 K0, CyclicGeneric (truncation K) :=
    PolygonGermStability.eventually_cyclicGeneric truncation hpointCont
      (by simpa [htrunc0] using hQ0)

  have hleftEvent : ∀ᶠ K : CarrierLine in 𝓝 K0,
      LeftExposed (truncation K) a.castSucc := by
    unfold LeftExposed
    apply Filter.eventually_all.mpr
    intro i
    apply Filter.eventually_all.mpr
    intro hi
    apply Filter.eventually_all.mpr
    intro his
    have htangent : ContinuousAt
        (fun K : CarrierLine => cyclicTangent (truncation K) a.castSucc) K0 := by
      change ContinuousAt (fun K => truncation K (cyclicSuccessor a.castSucc)-
        truncation K a.castSucc) K0
      exact (hpointCont (cyclicSuccessor a.castSucc)).sub (hpointCont a.castSucc)
    have hdiff : ContinuousAt
        (fun K : CarrierLine => truncation K i-truncation K a.castSucc) K0 :=
      (hpointCont i).sub (hpointCont a.castSucc)
    have hdetCont : ContinuousAt
        (fun K : CarrierLine => planarDet (cyclicTangent (truncation K) a.castSucc)
          (truncation K i-truncation K a.castSucc)) K0 := by
      unfold planarDet
      exact ((htangent.fst.mul hdiff.snd).sub (htangent.snd.mul hdiff.fst))
    have hpos : 0 < planarDet (cyclicTangent (truncation K0) a.castSucc)
        (truncation K0 i-truncation K0 a.castSucc) := by
      simpa [htrunc0] using hleft0 i hi his
    exact hdetCont.eventually (isOpen_Ioi.mem_nhds hpos)

  have hepsEvent : ∀ᶠ K : CarrierLine in 𝓝 K0,
      0 < recoveredEpsilon K ∧ recoveredEpsilon K < 1 := by
    have hI : recoveredEpsilon K0 ∈ Set.Ioo (0:ℝ) 1 := by
      rw [heps0]
      exact ⟨he0,he01⟩
    exact hepsCont.eventually (isOpen_Ioo.mem_nhds hI)

  have hscaleEvent : ∀ᶠ K : CarrierLine in 𝓝 K0,
      0 < recoveredScale K := by
    have hI : recoveredScale K0 ∈ Set.Ioi (0:ℝ) := by rw [hscale0]; exact hs0
    exact hscaleCont.eventually (isOpen_Ioi.mem_nhds hI)

  have huEvent : ∀ᶠ K : CarrierLine in 𝓝 K0, 0 < planarDet K.1 U :=
    huCont.eventually (isOpen_Ioi.mem_nhds hu0)
  have hdEvent : ∀ᶠ K : CarrierLine in 𝓝 K0, 0 < planarDet K.1 D :=
    hdCont.eventually (isOpen_Ioi.mem_nhds hd0)

  have hproductCont : ContinuousAt
      (fun K : CarrierLine => recoveredEpsilon K*recoveredScale K) K0 :=
    hepsCont.mul hscaleCont
  have hproductEvent : ∀ᶠ K : CarrierLine in 𝓝 K0,
      0 < recoveredEpsilon K*recoveredScale K ∧
        recoveredEpsilon K*recoveredScale K < 1 := by
    have hprod0 : 0 < recoveredEpsilon K0*recoveredScale K0 ∧
        recoveredEpsilon K0*recoveredScale K0 < 1 := by
      rw [heps0,hscale0]
      exact ⟨mul_pos he0 hs0,hes0⟩
    exact hproductCont.eventually (isOpen_Ioo.mem_nhds hprod0)

  have hgood : ∀ᶠ K : CarrierLine in 𝓝 K0,
      0 < recoveredEpsilon K ∧ recoveredEpsilon K < 1 ∧
      0 < recoveredScale K ∧
      0 < recoveredEpsilon K*recoveredScale K ∧
      recoveredEpsilon K*recoveredScale K < 1 ∧
      0 < planarDet K.1 U ∧ 0 < planarDet K.1 D ∧
      CyclicGeneric (truncation K) ∧ LeftExposed (truncation K) a.castSucc := by
    filter_upwards [hepsEvent,hscaleEvent,hproductEvent,huEvent,hdEvent,hgenEvent,hleftEvent]
      with K he hs hp huK hdK hg hl
    exact ⟨he.1,he.2,hs,hp.1,hp.2,huK,hdK,hg,hl⟩

  have hwindow : ∀ᶠ K : CarrierLine in 𝓝 K0,
      0 < recoveredEpsilon K ∧ recoveredEpsilon K < 1 ∧
      0 < recoveredScale K ∧ 0 < recoveredEpsilon K*recoveredScale K ∧
      recoveredEpsilon K*recoveredScale K < 1 ∧
      0 < planarDet K.1 U ∧ 0 < planarDet K.1 D ∧
      CyclicGeneric (truncation K) ∧ LeftExposed (truncation K) a.castSucc ∧
      lineValue K (truncation K a.castSucc)=0 ∧
      lineValue K (truncation K ⟨a.val+1, by have := a.isLt; omega⟩)=0 := by
    filter_upwards [hgood] with K hK
    rcases hK with ⟨hE,hE1,hS,hP,hP1,huK,hdK,hg,hl⟩
    refine ⟨hE,hE1,hS,hP,hP1,huK,hdK,hg,hl,?_,?_⟩
    · have hanchor : truncateCyclicCorner q a p (recoveredScale K)
          (recoveredEpsilon K) a.castSucc = q a+recoveredEpsilon K • U := by
        simpa [U] using truncateCyclicCorner_anchor q a p
          (recoveredScale K) (recoveredEpsilon K)
      change lineValue K (truncateCyclicCorner q a p
        (recoveredScale K) (recoveredEpsilon K) a.castSucc)=0
      rw [hanchor]
      rw [hline_affine K (recoveredEpsilon K) U]
      simp only [recoveredEpsilon]
      field_simp [ne_of_gt huK]
    · have hnew : truncateCyclicCorner q a p (recoveredScale K)
          (recoveredEpsilon K) ⟨a.val+1, by have := a.isLt; omega⟩ =
            q a+(recoveredEpsilon K*recoveredScale K) • D := by
        simpa [D] using truncateCyclicCorner_new q a p
          (recoveredScale K) (recoveredEpsilon K)
      change lineValue K (truncateCyclicCorner q a p (recoveredScale K)
        (recoveredEpsilon K) ⟨a.val+1, by have := a.isLt; omega⟩)=0
      rw [hnew]
      rw [hline_affine K (recoveredEpsilon K*recoveredScale K) D]
      simp only [recoveredEpsilon,recoveredScale]
      field_simp [ne_of_gt huK,ne_of_gt hdK]
      ring

  obtain ⟨W,hSubset,hWopen,hK0⟩ := mem_nhds_iff.mp hwindow
  refine ⟨W,hWopen,hK0,?_⟩
  intro K hK
  rcases hSubset hK with ⟨hE,hE1,hS,hP,hP1,huK,hdK,hg,hl,hA,hB⟩
  exact ⟨hE,hE1,hS,hP,hP1,hg,hl,hA,hB⟩

end DirectGLSSW.SourceTruncationLineWindow
