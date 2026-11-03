import UniversalCarrierTransverse
import LocalCarrierPolygonRecovery
import Mathlib.Tactic.FieldSimp

set_option autoImplicit false
namespace DirectGLSSW.CarrierScaleTransport
open AuxiliaryCarrierChart UniversalCarrierDomain

theorem lineValue_smul (s : ℝ) (L : CarrierLine) (x : PlanarPoint ℝ) :
    lineValue (s • L) x = s * lineValue L x := by
  simp [lineValue, planarDet]
  ring

theorem lineDenominator_smul (s t : ℝ) (L M : CarrierLine) :
    lineDenominator (s • L) (t • M) = s * t * lineDenominator L M := by
  simp [lineDenominator, planarDet]
  ring

theorem lineIntersection_smul (s t : ℝ) (L M : CarrierLine)
    (hs : s ≠ 0) (ht : t ≠ 0) (hd : lineDenominator L M ≠ 0) :
    lineIntersection (s • L) (t • M) = lineIntersection L M := by
  symm
  apply lineIntersection_unique
  · rw [lineDenominator_smul]
    exact mul_ne_zero (mul_ne_zero hs ht) hd
  · rw [lineValue_smul, lineValue_intersection_left L M hd, mul_zero]
  · rw [lineValue_smul, lineValue_intersection_right L M hd, mul_zero]

theorem exists_smul_of_det_zero (u v : PlanarPoint ℝ)
    (hv : v ≠ 0) (hdet : planarDet u v = 0) :
    ∃ s : ℝ, u = s • v := by
  simp only [planarDet] at hdet
  by_cases hvx : v.1 = 0
  · have hvy : v.2 ≠ 0 := by
      intro h
      apply hv
      exact Prod.ext hvx h
    have hux : u.1 = 0 := by
      rw [hvx, mul_zero, sub_zero] at hdet
      exact (mul_eq_zero.mp hdet).resolve_right hvy
    refine ⟨u.2 / v.2, ?_⟩
    apply Prod.ext
    · simp [hvx, hux]
    · change u.2 = (u.2 / v.2) * v.2
      field_simp
  · refine ⟨u.1 / v.1, ?_⟩
    apply Prod.ext
    · change u.1 = (u.1 / v.1) * v.1
      field_simp
    · change u.2 = (u.1 / v.1) * v.2
      field_simp
      nlinarith [hdet]

theorem exists_nonzero_scale_of_incident (L : CarrierLine)
    (a b : PlanarPoint ℝ) (hab : b - a ≠ 0) (hL : L.1 ≠ 0)
    (ha : lineValue L a = 0) (hb : lineValue L b = 0) :
    ∃ s : ℝ, s ≠ 0 ∧ L = s • (b-a, -planarDet (b-a) a) := by
  have hd : planarDet L.1 (b-a) = 0 := by
    simp only [lineValue, planarDet, Prod.fst_sub, Prod.snd_sub] at *
    nlinarith
  obtain ⟨s, hs⟩ := exists_smul_of_det_zero L.1 (b-a) hab hd
  have hsn : s ≠ 0 := by
    intro hz
    rw [hz, zero_smul] at hs
    exact hL hs
  refine ⟨s, hsn, Prod.ext hs ?_⟩
  change L.2 = s * (-planarDet (b-a) a)
  rw [lineValue, hs] at ha
  simp only [planarDet, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at ha ⊢
  nlinarith [ha]

theorem exists_supplied_scales {n : ℕ} (q : Fin n → PlanarPoint ℝ)
    (hq : CyclicGeneric q) (L : Fin n → CarrierLine)
    (hT : PairTransverse L)
    (hinc : ∀ i, lineValue (L i) (q i) = 0 ∧
      lineValue (L i) (q (cyclicSuccessor i)) = 0) :
    ∃ s : Fin n → ℝ, (∀ i, s i ≠ 0) ∧
      L = fun i => s i • polygonCarrierCoordinates q i := by
  classical
  have each (i : Fin n) : ∃ s : ℝ, s ≠ 0 ∧
      L i = s • polygonCarrierCoordinates q i := by
    have hLi : (L i).1 ≠ 0 := by
      intro hz
      have hd := hT i (cyclicSuccessor i)
        (Ne.symm (cyclicSuccessor_ne_self (by have hn := hq.size_ge_three; omega) i))
      apply hd
      simp [lineDenominator, hz, planarDet]
    exact exists_nonzero_scale_of_incident (L i) (q i) (q (cyclicSuccessor i))
      (cyclicTangent_ne_zero hq.size_ge_three q hq.g1 i) hLi (hinc i).1 (hinc i).2
  choose s hs heq using each
  exact ⟨s, hs, funext heq⟩

theorem carrierTripleNumerator_smul (a b c d e f : ℝ)
    (A B C D E F : CarrierLine) :
    carrierTripleNumerator (a • A) (b • B) (c • C) (d • D) (e • E) (f • F) =
      (a*b*c*d*e*f) * carrierTripleNumerator A B C D E F := by
  simp only [carrierTripleNumerator, lineNumerator, lineDenominator, planarDet,
    Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

theorem universalLocus_of_smul {α : Type*} [DecidableEq α]
    (L : α → CarrierLine) (s : α → ℝ)
    (h : UniversalLocus (fun i => s i • L i)) : UniversalLocus L := by
  intro p q r hp
  have hnum := h p q r hp
  rw [carrierTripleNumerator_smul] at hnum
  exact (mul_ne_zero_iff.mp hnum).2

theorem pairTransverse_of_smul {α : Type*} (L : α → CarrierLine) (s : α → ℝ)
    (h : PairTransverse (fun i => s i • L i)) : PairTransverse L := by
  intro a b hab
  have hd := h a b hab
  rw [lineDenominator_smul] at hd
  exact (mul_ne_zero_iff.mp hd).2

theorem canonical_universal_of_supplied {n : ℕ}
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (L : Fin n → CarrierLine) (hU : UniversalLocus L) (hT : PairTransverse L)
    (hinc : ∀ i, lineValue (L i) (q i) = 0 ∧
      lineValue (L i) (q (cyclicSuccessor i)) = 0) :
    UniversalLocus (polygonCarrierCoordinates q) ∧
      PairTransverse (polygonCarrierCoordinates q) := by
  obtain ⟨s, hs, hLs⟩ := exists_supplied_scales q hq L hT hinc
  rw [hLs] at hU hT
  exact ⟨universalLocus_of_smul _ s hU, pairTransverse_of_smul _ s hT⟩

end DirectGLSSW.CarrierScaleTransport
