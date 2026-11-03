import DirectGLSSW.DaughterPhysicalTruncation
import DirectGLSSW.TruncationDaughterPointTransport
import DirectGLSSW.DaughterAnchorScales

set_option autoImplicit false

namespace DirectGLSSW.TruncationDaughterAmplitude

open DaughterFirstReturn TruncationDirection TruncationEdgeLift

theorem exists_affected_daughter_truncation_amplitude
    (hRI : GLSSWRootIndependence) {n : ℕ}
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (a p : Fin n) (hp : cyclicSuccessor p = a)
    (hturn : 0 < planarDet (q a - q p) (q (cyclicSuccessor a) - q a))
    (scale : ℝ) (hscale : 0 < scale)
    (havoid : ∀ x : PolygonEvent q, polygonEventPoint q x ≠ q a →
      planarDet (scale • (q (cyclicSuccessor a) - q a) - (q p - q a))
        (polygonEventPoint q x - q a) ≠ 0)
    (S : Finset (PolygonCrossing q))
    (hD : CyclicGeneric (daughterVertex q hq.g2 S (Sum.inl a))) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε < δ →
      ∀ (hQ : CyclicGeneric (truncateCyclicCorner q a p scale ε))
        (E : PolygonCrossing q ≃ PolygonCrossing (truncateCyclicCorner q a p scale ε)),
        (∀ c, (E c).val.1 = edgeLift a c.val.1) →
        (∀ c, (E c).val.2 = edgeLift a c.val.2) →
        (∀ c, crossingPoint (truncateCyclicCorner q a p scale ε) (E c) = crossingPoint q c) →
        ∃ hNew : CyclicGeneric (daughterVertex (truncateCyclicCorner q a p scale ε)
          hQ.g2 (S.map E.toEmbedding) (Sum.inl a.castSucc)),
          polygonAmplitude (daughterVertex (truncateCyclicCorner q a p scale ε)
            hQ.g2 (S.map E.toEmbedding) (Sum.inl a.castSucc)) hNew =
          -polygonAmplitude (daughterVertex q hq.g2 S (Sum.inl a)) hD
 := by
  classical
  let A : PolygonEvent q := Sum.inl a
  let D := daughterVertex q hq.g2 S A
  let m := Fintype.card (CornerCoord q hq.g2 S A)
  have hm : 0 < m := lt_of_lt_of_le (by decide : 0 < 3) hD.size_ge_three
  let z : Fin m := ⟨0, hm⟩
  let pD : Fin m := (cyclicSuccessorPerm m)⁻¹ z
  have hpD : cyclicSuccessor pD = z := Equiv.apply_symm_apply (cyclicSuccessorPerm m) z
  have hroot : retainedCorner q S A := trivial
  have hhere : orbitEventAt q hq.g2 S A (cornerEnumeration q hq.g2 S A z).val = Sum.inl a := by
    simp [z, cornerEnumeration_zero_eq_rootcoord, hroot, orbitEventAt, A]
  obtain ⟨α, hα, β, hβ, hA, hP, hN⟩ :=
    DaughterAnchorScales.exists_daughter_anchor_incident_scales
      q hq.g2 S hq.size_ge_three A hroot z a p hp hhere
  have havoidD (j : Fin m) (hj : j ≠ z) :
      planarDet (scale • (q (cyclicSuccessor a) - q a) - (q p - q a))
        (D j - q a) ≠ 0 := by
    have hne : D j ≠ q a := by
      intro heq
      apply hj
      exact (cyclicNoncollinear_injective hD.size_ge_three D hD.g1) (heq.trans hA.symm)
    exact havoid (orbitEventAt q hq.g2 S A (cornerEnumeration q hq.g2 S A j).val) hne
  obtain ⟨δ, hδ, hphys⟩ :=
    DaughterPhysicalTruncation.exists_physical_truncation_amplitude_at_zero
      hRI D hD z pD rfl hpD (q a) (q p) (q (cyclicSuccessor a))
      α β scale hα hβ hscale hA hP hN hturn havoidD
  refine ⟨min δ (min 1 (1 / scale)), lt_min hδ (lt_min zero_lt_one (one_div_pos.mpr hscale)), ?_⟩
  intro ε hε hεδ hQ E hleft hright hpoint
  have hεδ' : ε < δ := lt_of_lt_of_le hεδ (min_le_left _ _)
  have hεbounds : ε < min 1 (1 / scale) := lt_of_lt_of_le hεδ (min_le_right _ _)
  have hε1 : ε < 1 := lt_of_lt_of_le hεbounds (min_le_left _ _)
  have hεscale1 : ε * scale < 1 :=
    (lt_div_iff₀ hscale).mp (lt_of_lt_of_le hεbounds (min_le_right _ _))
  apply hphys ε hε hεδ'
    (daughterVertex (truncateCyclicCorner q a p scale ε) hQ.g2
      (S.map E.toEmbedding) (Sum.inl a.castSucc))
  exact TruncationDaughterPointTransport.truncationDaughterPointList_affected
    hq.size_ge_three q a p hp scale ε hε hε1 (mul_pos hε hscale) hεscale1
    hq hQ E hleft hright hpoint S

theorem unaffected_daughter_truncation_amplitude {n : ℕ}
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (a p : Fin n) (hp : cyclicSuccessor p = a) (scale ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hscale : 0 < ε * scale)
    (hscale1 : ε * scale < 1)
    (hQ : CyclicGeneric (truncateCyclicCorner q a p scale ε))
    (E : PolygonCrossing q ≃ PolygonCrossing (truncateCyclicCorner q a p scale ε))
    (hleft : ∀ c, (E c).val.1 = edgeLift a c.val.1)
    (hright : ∀ c, (E c).val.2 = edgeLift a c.val.2)
    (hpoint : ∀ c, crossingPoint (truncateCyclicCorner q a p scale ε) (E c) = crossingPoint q c)
    (S : Finset (PolygonCrossing q)) (x : PolygonEvent q)
    (hx : ¬ (smoothingDartPermutation q hq.g2 S).SameCycle x (Sum.inl a))
    (hD : CyclicGeneric (daughterVertex q hq.g2 S x)) :
    ∃ hNew : CyclicGeneric (daughterVertex (truncateCyclicCorner q a p scale ε)
      hQ.g2 (S.map E.toEmbedding) (TruncationEventOrder.truncationPolygonEventMap q a p scale ε E x)),
      polygonAmplitude (daughterVertex (truncateCyclicCorner q a p scale ε)
        hQ.g2 (S.map E.toEmbedding) (TruncationEventOrder.truncationPolygonEventMap q a p scale ε E x)) hNew =
      polygonAmplitude (daughterVertex q hq.g2 S x) hD
 := by
  have hlist := TruncationDaughterPointTransport.truncationDaughterPointList_unaffected
    hq.size_ge_three q a p hp scale ε hε hε1 hscale hscale1 hq hQ E hleft hright hpoint S x hx
  let hNew := TruncationPointListAdapter.cyclicGeneric_of_pointList_eq _ _ hD hlist.symm
  exact ⟨hNew, (TruncationPointListAdapter.polygonAmplitude_eq_of_pointList_eq _ _ hD hNew hlist.symm).symm⟩

end DirectGLSSW.TruncationDaughterAmplitude
