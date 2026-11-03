import ThreeCarrierWitness
import CarrierWitnessEvaluation
import CarrierDensity

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace DirectGLSSW.CarrierTriplePairProperness
open AuxiliaryCarrierPairs AuxiliaryCarrierChart AuxiliaryDeterminants CarrierWitnessEvaluation

private theorem image_pair_member_incident {α : Type*} [DecidableEq α]
    (g : α → Fin 6) (s : Finset α) (e : Fin 15)
    (himage : s.image g = {(witnessPair e).1, (witnessPair e).2})
    {x : α} (hx : x ∈ s) : witnessIncident e (g x) := by
  have hfx : g x ∈ s.image g := Finset.mem_image.mpr ⟨x, hx, rfl⟩
  rw [himage] at hfx
  simpa [witnessIncident] using hfx

/-- Three distinct nondegenerate carrier pairs with no common carrier admit
an actual line assignment with nonzero intersection determinant numerator.
The finite witness comes from the existing three-carrier enumeration. -/
theorem triple_pairs_numerator_nonzero_witness
    {α : Type*} [DecidableEq α]
    (p₀ p₁ q₀ q₁ r₀ r₁ : α)
    (hp : p₀≠p₁) (hq : q₀≠q₁) (hr : r₀≠r₁)
    (hpq : ({p₀,p₁} : Finset α)≠{q₀,q₁})
    (hqr : ({q₀,q₁} : Finset α)≠{r₀,r₁})
    (hpr : ({p₀,p₁} : Finset α)≠{r₀,r₁})
    (hno : ¬∃ x : α, x∈({p₀,p₁} : Finset α) ∧ x∈({q₀,q₁} : Finset α) ∧ x∈({r₀,r₁} : Finset α)) :
    ∃ L : α → CarrierLine,
      carrierTripleNumerator (L p₀) (L p₁) (L q₀) (L q₁) (L r₀) (L r₁)≠0 := by
  classical
  let s : Finset α := {p₀,p₁}
  let t : Finset α := {q₀,q₁}
  let u : Finset α := {r₀,r₁}
  have hs : s.card=2 := by simp [s,hp]
  have ht : t.card=2 := by simp [t,hq]
  have hu : u.card=2 := by simp [u,hr]
  obtain ⟨g,hg,a,b,c,hsa,htb,huc,hdet⟩ :=
    ThreeCarrierWitness.three_carrier_witness s t u hs ht hu hpq hqr hpr hno
  let L : α → CarrierLine := fun x => witnessCarrierLine (g x)
  have hleft_mem : p₀ ∈ s := by simp [s]
  have hright_mem : p₁ ∈ s := by simp [s]
  have hleftj_mem : q₀ ∈ t := by simp [t]
  have hrightj_mem : q₁ ∈ t := by simp [t]
  have hleftk_mem : r₀ ∈ u := by simp [u]
  have hrightk_mem : r₁ ∈ u := by simp [u]
  have hleftU : p₀ ∈ s ∪ t ∪ u := by simp [hleft_mem]
  have hrightU : p₁ ∈ s ∪ t ∪ u := by simp [hright_mem]
  have hleftjU : q₀ ∈ s ∪ t ∪ u := by simp [hleftj_mem]
  have hrightjU : q₁ ∈ s ∪ t ∪ u := by simp [hrightj_mem]
  have hleftkU : r₀ ∈ s ∪ t ∪ u := by simp [hleftk_mem]
  have hrightkU : r₁ ∈ s ∪ t ∪ u := by simp [hrightk_mem]
  have hden₁ : lineDenominator (witnessCarrierLine (g (p₀)))
      (witnessCarrierLine (g (p₁))) ≠ 0 := by
    apply witnessCarrierLine_denominator_ne
    intro heq
    exact hp (hg hleftU hrightU heq)
  have hden₂ : lineDenominator (witnessCarrierLine (g (q₀)))
      (witnessCarrierLine (g (q₁))) ≠ 0 := by
    apply witnessCarrierLine_denominator_ne
    intro heq
    exact hq (hg hleftjU hrightjU heq)
  have hden₃ : lineDenominator (witnessCarrierLine (g (r₀)))
      (witnessCarrierLine (g (r₁))) ≠ 0 := by
    apply witnessCarrierLine_denominator_ne
    intro heq
    exact hr (hg hleftkU hrightkU heq)
  have hIa := image_pair_member_incident g s a hsa hleft_mem
  have hIa' := image_pair_member_incident g s a hsa hright_mem
  have hIb := image_pair_member_incident g t b htb hleftj_mem
  have hIb' := image_pair_member_incident g t b htb hrightj_mem
  have hIc := image_pair_member_incident g u c huc hleftk_mem
  have hIc' := image_pair_member_incident g u c huc hrightk_mem
  have hg₁ : g (p₀) ≠ g (p₁) := by
    intro h
    exact hp (hg hleftU hrightU h)
  have hg₂ : g (q₀) ≠ g (q₁) := by
    intro h
    exact hq (hg hleftjU hrightjU h)
  have hg₃ : g (r₀) ≠ g (r₁) := by
    intro h
    exact hr (hg hleftkU hrightkU h)
  have hInt₁ := witnessCarrierLine_intersection hg₁ hIa hIa'
  have hInt₂ := witnessCarrierLine_intersection hg₂ hIb hIb'
  have hInt₃ := witnessCarrierLine_intersection hg₃ hIc hIc'
  have hdetR : (witnessTripleDet a b c : ℝ) ≠ 0 := by exact_mod_cast hdet
  have hplanar := planarDet_castWitness_difference a b c
  refine ⟨L, ?_⟩
  change carrierTripleNumerator
    (witnessCarrierLine (g (p₀))) (witnessCarrierLine (g (p₁)))
    (witnessCarrierLine (g (q₀))) (witnessCarrierLine (g (q₁)))
    (witnessCarrierLine (g (r₀))) (witnessCarrierLine (g (r₁))) ≠ 0
  have hnum := carrierTripleNumerator_eq_scaled_det
    (witnessCarrierLine (g (p₀))) (witnessCarrierLine (g (p₁)))
    (witnessCarrierLine (g (q₀))) (witnessCarrierLine (g (q₁)))
    (witnessCarrierLine (g (r₀))) (witnessCarrierLine (g (r₁)))
    hden₁ hden₂ hden₃
  rw [hInt₁, hInt₂, hInt₃, hplanar] at hnum
  intro hz
  rw [hnum] at hz
  have hscale :
      (lineDenominator (witnessCarrierLine (g (p₀))) (witnessCarrierLine (g (p₁))) *
       lineDenominator (witnessCarrierLine (g (q₀))) (witnessCarrierLine (g (q₁))) *
       lineDenominator (witnessCarrierLine (g (r₀))) (witnessCarrierLine (g (r₁)))) ≠ 0 :=
    mul_ne_zero (mul_ne_zero hden₁ hden₂) hden₃
  rcases mul_eq_zero.mp hz with hzero | hzero
  · exact hscale hzero
  · exact hdetR hzero

/-- Density is inherited from the proved polynomial numerator witness, not
inferred from openness of a nonvanishing condition. This is carrier-coordinate
density only; actual configuration reconstruction is a separate consumer. -/
theorem triple_pairs_numerator_nonzero_dense
    {α : Type*} [DecidableEq α]
    (p₀ p₁ q₀ q₁ r₀ r₁ : α)
    (hp : p₀≠p₁) (hq : q₀≠q₁) (hr : r₀≠r₁)
    (hpq : ({p₀,p₁} : Finset α)≠{q₀,q₁})
    (hqr : ({q₀,q₁} : Finset α)≠{r₀,r₁})
    (hpr : ({p₀,p₁} : Finset α)≠{r₀,r₁})
    (hno : ¬∃ x : α, x∈({p₀,p₁} : Finset α) ∧ x∈({q₀,q₁} : Finset α) ∧ x∈({r₀,r₁} : Finset α)) :
    Dense {L : α → CarrierLine |
      carrierTripleNumerator (L p₀) (L p₁) (L q₀) (L q₁) (L r₀) (L r₁)≠0} := by
  obtain ⟨L,hL⟩ := triple_pairs_numerator_nonzero_witness p₀ p₁ q₀ q₁ r₀ r₁ hp hq hr hpq hqr hpr hno
  exact CarrierDensity.dense_assignmentNumerator_ne_zero p₀ p₁ q₀ q₁ r₀ r₁ L hL



end DirectGLSSW.CarrierTriplePairProperness
