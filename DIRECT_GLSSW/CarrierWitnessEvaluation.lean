import ThreeCarrierWitness
import CarrierIntersectionNumerator

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 800000

noncomputable section

namespace DirectGLSSW.CarrierWitnessEvaluation

open DirectGLSSW
open DirectGLSSW.AuxiliaryCarrierPairs
open DirectGLSSW.AuxiliaryDeterminants
open DirectGLSSW.AuxiliaryCarrierChart

/-- The six lines `y = t*x + t^2` at the fixed integer witness parameters. -/
def witnessCarrierLine (i : Fin 6) : CarrierLine :=
  ((1, (witnessParameter i : ℝ)), -((witnessParameter i : ℝ)^2))

def castWitnessPoint (e : Fin 15) : PlanarPoint ℝ :=
  ((witnessPoint e).1, (witnessPoint e).2)

theorem witnessCarrierLine_denominator_ne {i j : Fin 6} (hij : i ≠ j) :
    lineDenominator (witnessCarrierLine i) (witnessCarrierLine j) ≠ 0 := by
  have hparamZ : witnessParameter i ≠ witnessParameter j := by
    intro h
    exact hij (witnessParameter_injective h)
  have hparam : (witnessParameter i : ℝ) ≠ (witnessParameter j : ℝ) := by
    exact_mod_cast hparamZ
  have hreal : (witnessParameter j : ℝ) - (witnessParameter i : ℝ) ≠ 0 :=
    sub_ne_zero.mpr hparam.symm
  simpa [witnessCarrierLine, lineDenominator, planarDet] using hreal

theorem castWitnessPoint_on_incident_line (e : Fin 15) (i : Fin 6)
    (hi : witnessIncident e i) :
    lineValue (witnessCarrierLine i) (castWitnessPoint e) = 0 := by
  have hZ := witnessPoint_on_incident_line e i hi
  have hR : ((witnessPoint e).2 : ℝ) = (witnessParameter i : ℝ) *
      ((witnessPoint e).1 : ℝ) + (witnessParameter i : ℝ) * (witnessParameter i : ℝ) := by
    exact_mod_cast hZ
  simp only [lineValue, witnessCarrierLine, castWitnessPoint, planarDet]
  rw [hR]
  ring

theorem witnessCarrierLine_intersection {e : Fin 15} {i j : Fin 6}
    (hij : i ≠ j) (hi : witnessIncident e i) (hj : witnessIncident e j) :
    lineIntersection (witnessCarrierLine i) (witnessCarrierLine j) = castWitnessPoint e := by
  have hden := witnessCarrierLine_denominator_ne hij
  have hi' := castWitnessPoint_on_incident_line e i hi
  have hj' := castWitnessPoint_on_incident_line e j hj
  exact (lineIntersection_unique (witnessCarrierLine i) (witnessCarrierLine j)
    (castWitnessPoint e) hden hi' hj').symm

theorem planarDet_castWitness_difference (a b c : Fin 15) :
    planarDet (castWitnessPoint b - castWitnessPoint a)
      (castWitnessPoint c - castWitnessPoint a) = (witnessTripleDet a b c : ℝ) := by
  simp [planarDet, castWitnessPoint, witnessTripleDet]
  push_cast
  ring

private theorem witnessPair_endpoints_ne (e : Fin 15) :
    (witnessPair e).1 ≠ (witnessPair e).2 := by
  have hp : ∀ e : Fin 15, (witnessPair e).1 ≠ (witnessPair e).2 := by decide
  exact hp e

private theorem image_pair_member_incident {α : Type*} [DecidableEq α]
    (f : α → Fin 6) (s : Finset α) (e : Fin 15)
    (himage : s.image f = {(witnessPair e).1, (witnessPair e).2})
    {x : α} (hx : x ∈ s) : witnessIncident e (f x) := by
  have hfx : f x ∈ s.image f := Finset.mem_image.mpr ⟨x, hx, rfl⟩
  rw [himage] at hfx
  simpa [witnessIncident] using hfx

private theorem map_pair_endpoints_ne {α : Type*} [DecidableEq α]
    (f : α → Fin 6) (hf : Function.Injective f) (x y : α)
    (hxy : x ≠ y) : f x ≠ f y := by
  intro h
  exact hxy (hf h)

/-- A concrete line assignment makes the division-free numerator of every
actual daughter triple nonzero. The finite witness data are constructed from
G1, G2, nonalternation, retention, and the three distinct daughter indices. -/
theorem daughterCarrierTriple_has_nonzero_numerator
    {n : ℕ} (q : Fin n → PlanarPoint ℝ)
    (hG2 : cyclicNoTripleIntersections q)
    (S : Finset (PolygonCrossing q))
    (hn : 3 ≤ n) (hG1 : cyclicNoncollinear q)
    (hNA : PolygonNonalternation.polygonNonalternating q hG2 S)
    (root : PolygonEvent q) (hroot : DaughterFirstReturn.retainedCorner q S root)
    (i j k : Fin (Fintype.card (DaughterFirstReturn.CornerCoord q hG2 S root)))
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    ∃ L : Fin n → CarrierLine,
      let m := Fintype.card (DaughterFirstReturn.CornerCoord q hG2 S root)
      let prev : Fin m → Fin m := fun u => (cyclicSuccessorPerm m)⁻¹ u
      carrierTripleNumerator
        (L (DaughterFirstReturn.daughterCarrier q hG2 S root (prev i)))
        (L (DaughterFirstReturn.daughterCarrier q hG2 S root i))
        (L (DaughterFirstReturn.daughterCarrier q hG2 S root (prev j)))
        (L (DaughterFirstReturn.daughterCarrier q hG2 S root j))
        (L (DaughterFirstReturn.daughterCarrier q hG2 S root (prev k)))
        (L (DaughterFirstReturn.daughterCarrier q hG2 S root k)) ≠ 0 := by
  let m := Fintype.card (DaughterFirstReturn.CornerCoord q hG2 S root)
  let prev : Fin m → Fin m := fun u => (cyclicSuccessorPerm m)⁻¹ u
  let x₁ := DaughterFirstReturn.daughterCarrier q hG2 S root (prev i)
  let x₂ := DaughterFirstReturn.daughterCarrier q hG2 S root i
  let x₃ := DaughterFirstReturn.daughterCarrier q hG2 S root (prev j)
  let x₄ := DaughterFirstReturn.daughterCarrier q hG2 S root j
  let x₅ := DaughterFirstReturn.daughterCarrier q hG2 S root (prev k)
  let x₆ := DaughterFirstReturn.daughterCarrier q hG2 S root k
  let s := daughterCarrierPair q hG2 S root i
  let t := daughterCarrierPair q hG2 S root j
  let u := daughterCarrierPair q hG2 S root k
  obtain ⟨f, hf, a, b, c, hsa, htb, huc, hdet⟩ :=
    DirectGLSSW.ThreeCarrierWitness.daughter_three_carrier_witness
      q hG2 S hn hG1 hNA root hroot i j k hij hjk hik
  let L : Fin n → CarrierLine := fun x => witnessCarrierLine (f x)
  have hm : 3 ≤ m := DaughterTurns.daughterVertexCount_ge_three q hG2 S hn hG1 root hroot
  have hinjCarrier := DaughterFirstReturn.daughterCarrier_injective q hG2 S hn hNA root
  have hprevI : prev i ≠ i := by
    exact cyclicSuccessorPerm_symm_ne_self hm i
  have hprevJ : prev j ≠ j := by
    exact cyclicSuccessorPerm_symm_ne_self hm j
  have hprevK : prev k ≠ k := by
    exact cyclicSuccessorPerm_symm_ne_self hm k
  have hx₁x₂ : x₁ ≠ x₂ := by
    intro h
    apply hprevI
    exact hinjCarrier (by simpa [x₁, x₂] using h)
  have hx₃x₄ : x₃ ≠ x₄ := by
    intro h
    apply hprevJ
    exact hinjCarrier (by simpa [x₃, x₄] using h)
  have hx₅x₆ : x₅ ≠ x₆ := by
    intro h
    apply hprevK
    exact hinjCarrier (by simpa [x₅, x₆] using h)
  have hx₁mem : x₁ ∈ s := by change x₁ ∈ ({x₁, x₂} : Finset (Fin n)); simp
  have hx₂mem : x₂ ∈ s := by change x₂ ∈ ({x₁, x₂} : Finset (Fin n)); simp
  have hx₃mem : x₃ ∈ t := by change x₃ ∈ ({x₃, x₄} : Finset (Fin n)); simp
  have hx₄mem : x₄ ∈ t := by change x₄ ∈ ({x₃, x₄} : Finset (Fin n)); simp
  have hx₅mem : x₅ ∈ u := by change x₅ ∈ ({x₅, x₆} : Finset (Fin n)); simp
  have hx₆mem : x₆ ∈ u := by change x₆ ∈ ({x₅, x₆} : Finset (Fin n)); simp
  have hx₁U : x₁ ∈ s ∪ t ∪ u := by simp [hx₁mem]
  have hx₂U : x₂ ∈ s ∪ t ∪ u := by simp [hx₂mem]
  have hx₃U : x₃ ∈ s ∪ t ∪ u := by simp [hx₃mem]
  have hx₄U : x₄ ∈ s ∪ t ∪ u := by simp [hx₄mem]
  have hx₅U : x₅ ∈ s ∪ t ∪ u := by simp [hx₅mem]
  have hx₆U : x₆ ∈ s ∪ t ∪ u := by simp [hx₆mem]
  have hfx₁x₂ : f x₁ ≠ f x₂ := by
    intro h
    exact hx₁x₂ (hf hx₁U hx₂U h)
  have hfx₃x₄ : f x₃ ≠ f x₄ := by
    intro h
    exact hx₃x₄ (hf hx₃U hx₄U h)
  have hfx₅x₆ : f x₅ ≠ f x₆ := by
    intro h
    exact hx₅x₆ (hf hx₅U hx₆U h)
  have hIa : witnessIncident a (f x₁) := image_pair_member_incident f s a hsa hx₁mem
  have hIa' : witnessIncident a (f x₂) := image_pair_member_incident f s a hsa hx₂mem
  have hIb : witnessIncident b (f x₃) := image_pair_member_incident f t b htb hx₃mem
  have hIb' : witnessIncident b (f x₄) := image_pair_member_incident f t b htb hx₄mem
  have hIc : witnessIncident c (f x₅) := image_pair_member_incident f u c huc hx₅mem
  have hIc' : witnessIncident c (f x₆) := image_pair_member_incident f u c huc hx₆mem
  have hden₁ := witnessCarrierLine_denominator_ne hfx₁x₂
  have hden₂ := witnessCarrierLine_denominator_ne hfx₃x₄
  have hden₃ := witnessCarrierLine_denominator_ne hfx₅x₆
  have hInt₁ := witnessCarrierLine_intersection hfx₁x₂ hIa hIa'
  have hInt₂ := witnessCarrierLine_intersection hfx₃x₄ hIb hIb'
  have hInt₃ := witnessCarrierLine_intersection hfx₅x₆ hIc hIc'
  have hdetR : (witnessTripleDet a b c : ℝ) ≠ 0 := by exact_mod_cast hdet
  have hplanar := planarDet_castWitness_difference a b c
  refine ⟨L, ?_⟩
  change carrierTripleNumerator
    (witnessCarrierLine (f x₁)) (witnessCarrierLine (f x₂))
    (witnessCarrierLine (f x₃)) (witnessCarrierLine (f x₄))
    (witnessCarrierLine (f x₅)) (witnessCarrierLine (f x₆)) ≠ 0
  have hnum := carrierTripleNumerator_eq_scaled_det
    (witnessCarrierLine (f x₁)) (witnessCarrierLine (f x₂))
    (witnessCarrierLine (f x₃)) (witnessCarrierLine (f x₄))
    (witnessCarrierLine (f x₅)) (witnessCarrierLine (f x₆)) hden₁ hden₂ hden₃
  rw [hInt₁, hInt₂, hInt₃, hplanar] at hnum
  intro hz
  rw [hnum] at hz
  have hscale : (lineDenominator (witnessCarrierLine (f x₁)) (witnessCarrierLine (f x₂)) *
      lineDenominator (witnessCarrierLine (f x₃)) (witnessCarrierLine (f x₄)) *
      lineDenominator (witnessCarrierLine (f x₅)) (witnessCarrierLine (f x₆))) ≠ 0 :=
    mul_ne_zero (mul_ne_zero hden₁ hden₂) hden₃
  rcases mul_eq_zero.mp hz with hzero | hzero
  · exact hscale hzero
  · exact hdetR hzero

end DirectGLSSW.CarrierWitnessEvaluation






