import ThreeCarrierWitness
import CarrierWitnessEvaluation
import CarrierDensity

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 800000

noncomputable section

namespace DirectGLSSW.OpenCarrierChain

open DirectGLSSW.AuxiliaryCarrierPairs
open DirectGLSSW.AuxiliaryCarrierChart
open DirectGLSSW.AuxiliaryDeterminants
open DirectGLSSW.CarrierWitnessEvaluation

private def edgePair {α : Type*} [DecidableEq α] {m : ℕ} (f : Fin (m + 1) → α)
    (i : Fin m) : Finset α := {f i.castSucc, f i.succ}

private theorem castSucc_ne_succ {m : ℕ} (i : Fin m) : i.castSucc ≠ i.succ := by
  intro h
  have hh := congrArg Fin.val h
  simp at hh

private theorem edgePair_card {α : Type*} [DecidableEq α] {m : ℕ}
    (f : Fin (m + 1) → α) (hf : Function.Injective f) (i : Fin m) :
    (edgePair f i).card = 2 := by
  have hne : f i.castSucc ≠ f i.succ := by
    intro h
    exact castSucc_ne_succ i (hf h)
  simp [edgePair, hne]

private theorem fin_three_distinct_edges_no_common {m : ℕ}
    (i j k : Fin m) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (v : Fin (m + 1))
    (hi : v = i.castSucc ∨ v = i.succ)
    (hj : v = j.castSucc ∨ v = j.succ)
    (hk : v = k.castSucc ∨ v = k.succ) : False := by
  have hijv : i.val ≠ j.val := fun h => hij (Fin.ext h)
  have hjkv : j.val ≠ k.val := fun h => hjk (Fin.ext h)
  have hikv : i.val ≠ k.val := fun h => hik (Fin.ext h)
  rcases hi with hi | hi <;> rcases hj with hj | hj <;> rcases hk with hk | hk
  all_goals
    have hi' := congrArg Fin.val hi
    have hj' := congrArg Fin.val hj
    have hk' := congrArg Fin.val hk
    simp at hi' hj' hk'
    omega

private theorem edgePairs_ne {α : Type*} [DecidableEq α] {m : ℕ}
    (f : Fin (m + 1) → α) (hf : Function.Injective f)
    {i j : Fin m} (hij : i ≠ j) : edgePair f i ≠ edgePair f j := by
  intro h
  have hleft : f i.castSucc ∈ edgePair f j := by
    rw [← h]
    simp [edgePair]
  have hright : f i.succ ∈ edgePair f j := by
    rw [← h]
    simp [edgePair]
  simp only [edgePair, Finset.mem_insert, Finset.mem_singleton] at hleft hright
  rcases hleft with hleft | hleft <;> rcases hright with hright | hright
  · exact castSucc_ne_succ i ((hf hleft).trans (hf hright).symm)
  · have hidx : i.castSucc = j.castSucc := hf hleft
    exact hij (Fin.ext (by simpa using congrArg Fin.val hidx))
  · have hi := congrArg Fin.val (hf hleft)
    have hj := congrArg Fin.val (hf hright)
    simp at hi hj
    omega
  · exact castSucc_ne_succ i ((hf hleft).trans (hf hright).symm)

private theorem edgePairs_no_three_common {α : Type*} [DecidableEq α]
    {m : ℕ} (f : Fin (m + 1) → α) (hf : Function.Injective f)
    (i j k : Fin m) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    ¬ ∃ x : α, x ∈ edgePair f i ∧ x ∈ edgePair f j ∧ x ∈ edgePair f k := by
  rintro ⟨x, hxi, hxj, hxk⟩
  have hxi' : x = f i.castSucc ∨ x = f i.succ := by
    simpa [edgePair, Finset.mem_insert, Finset.mem_singleton] using hxi
  rcases hxi' with hxi' | hxi'
  · subst x
    have hj' : f i.castSucc = f j.castSucc ∨ f i.castSucc = f j.succ := by
      simpa [edgePair, Finset.mem_insert, Finset.mem_singleton] using hxj
    have hk' : f i.castSucc = f k.castSucc ∨ f i.castSucc = f k.succ := by
      simpa [edgePair, Finset.mem_insert, Finset.mem_singleton] using hxk
    have hji : i.castSucc = j.castSucc ∨ i.castSucc = j.succ :=
      hj'.elim (fun h => Or.inl (hf h)) (fun h => Or.inr (hf h))
    have hki : i.castSucc = k.castSucc ∨ i.castSucc = k.succ :=
      hk'.elim (fun h => Or.inl (hf h)) (fun h => Or.inr (hf h))
    exact fin_three_distinct_edges_no_common i j k hij hjk hik i.castSucc
      (Or.inl rfl) (by simpa [eq_comm] using hji) (by simpa [eq_comm] using hki)
  · subst x
    have hj' : f i.succ = f j.castSucc ∨ f i.succ = f j.succ := by
      simpa [edgePair, Finset.mem_insert, Finset.mem_singleton] using hxj
    have hk' : f i.succ = f k.castSucc ∨ f i.succ = f k.succ := by
      simpa [edgePair, Finset.mem_insert, Finset.mem_singleton] using hxk
    have hji : i.succ = j.castSucc ∨ i.succ = j.succ :=
      hj'.elim (fun h => Or.inl (hf h)) (fun h => Or.inr (hf h))
    have hki : i.succ = k.castSucc ∨ i.succ = k.succ :=
      hk'.elim (fun h => Or.inl (hf h)) (fun h => Or.inr (hf h))
    exact fin_three_distinct_edges_no_common i j k hij hjk hik i.succ
      (Or.inr rfl) (by simpa [eq_comm] using hji) (by simpa [eq_comm] using hki)

private theorem image_pair_member_incident {α : Type*} [DecidableEq α]
    (g : α → Fin 6) (s : Finset α) (e : Fin 15)
    (himage : s.image g = {(witnessPair e).1, (witnessPair e).2})
    {x : α} (hx : x ∈ s) : witnessIncident e (g x) := by
  have hfx : g x ∈ s.image g := Finset.mem_image.mpr ⟨x, hx, rfl⟩
  rw [himage] at hfx
  simpa [witnessIncident] using hfx

theorem triple_numerator_nonzero_witness {α : Type*} [DecidableEq α]
    {m : ℕ} (f : Fin (m + 1) → α) (hf : Function.Injective f)
    (i j k : Fin m) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    ∃ L : α → CarrierLine,
      carrierTripleNumerator
        (L (f i.castSucc)) (L (f i.succ))
        (L (f j.castSucc)) (L (f j.succ))
        (L (f k.castSucc)) (L (f k.succ)) ≠ 0 := by
  classical
  let s := edgePair f i
  let t := edgePair f j
  let u := edgePair f k
  have hs := edgePair_card f hf i
  have ht := edgePair_card f hf j
  have hu := edgePair_card f hf k
  have hst : s ≠ t := by
    exact edgePairs_ne f hf hij
  have htu : t ≠ u := by
    exact edgePairs_ne f hf hjk
  have hsu : s ≠ u := by
    exact edgePairs_ne f hf hik
  have hno : ¬ ∃ x : α, x ∈ s ∧ x ∈ t ∧ x ∈ u := by
    simpa [s, t, u] using edgePairs_no_three_common f hf i j k hij hjk hik
  obtain ⟨g, hg, a, b, c, hsa, htb, huc, hdet⟩ :=
    DirectGLSSW.ThreeCarrierWitness.three_carrier_witness s t u hs ht hu hst htu hsu hno
  let L : α → CarrierLine := fun x => witnessCarrierLine (g x)
  have hleft_mem : f i.castSucc ∈ s := by simp [s, edgePair]
  have hright_mem : f i.succ ∈ s := by simp [s, edgePair]
  have hleftj_mem : f j.castSucc ∈ t := by simp [t, edgePair]
  have hrightj_mem : f j.succ ∈ t := by simp [t, edgePair]
  have hleftk_mem : f k.castSucc ∈ u := by simp [u, edgePair]
  have hrightk_mem : f k.succ ∈ u := by simp [u, edgePair]
  have hleftU : f i.castSucc ∈ s ∪ t ∪ u := by simp [hleft_mem]
  have hrightU : f i.succ ∈ s ∪ t ∪ u := by simp [hright_mem]
  have hleftjU : f j.castSucc ∈ s ∪ t ∪ u := by simp [hleftj_mem]
  have hrightjU : f j.succ ∈ s ∪ t ∪ u := by simp [hrightj_mem]
  have hleftkU : f k.castSucc ∈ s ∪ t ∪ u := by simp [hleftk_mem]
  have hrightkU : f k.succ ∈ s ∪ t ∪ u := by simp [hrightk_mem]
  have hden₁ : lineDenominator (witnessCarrierLine (g (f i.castSucc)))
      (witnessCarrierLine (g (f i.succ))) ≠ 0 := by
    apply witnessCarrierLine_denominator_ne
    intro heq
    exact castSucc_ne_succ i (hf (hg hleftU hrightU heq))
  have hden₂ : lineDenominator (witnessCarrierLine (g (f j.castSucc)))
      (witnessCarrierLine (g (f j.succ))) ≠ 0 := by
    apply witnessCarrierLine_denominator_ne
    intro heq
    exact castSucc_ne_succ j (hf (hg hleftjU hrightjU heq))
  have hden₃ : lineDenominator (witnessCarrierLine (g (f k.castSucc)))
      (witnessCarrierLine (g (f k.succ))) ≠ 0 := by
    apply witnessCarrierLine_denominator_ne
    intro heq
    exact castSucc_ne_succ k (hf (hg hleftkU hrightkU heq))
  have hIa := image_pair_member_incident g s a hsa hleft_mem
  have hIa' := image_pair_member_incident g s a hsa hright_mem
  have hIb := image_pair_member_incident g t b htb hleftj_mem
  have hIb' := image_pair_member_incident g t b htb hrightj_mem
  have hIc := image_pair_member_incident g u c huc hleftk_mem
  have hIc' := image_pair_member_incident g u c huc hrightk_mem
  have hg₁ : g (f i.castSucc) ≠ g (f i.succ) := by
    intro h
    exact castSucc_ne_succ i (hf (hg hleftU hrightU h))
  have hg₂ : g (f j.castSucc) ≠ g (f j.succ) := by
    intro h
    exact castSucc_ne_succ j (hf (hg hleftjU hrightjU h))
  have hg₃ : g (f k.castSucc) ≠ g (f k.succ) := by
    intro h
    exact castSucc_ne_succ k (hf (hg hleftkU hrightkU h))
  have hInt₁ := witnessCarrierLine_intersection hg₁ hIa hIa'
  have hInt₂ := witnessCarrierLine_intersection hg₂ hIb hIb'
  have hInt₃ := witnessCarrierLine_intersection hg₃ hIc hIc'
  have hdetR : (witnessTripleDet a b c : ℝ) ≠ 0 := by exact_mod_cast hdet
  have hplanar := planarDet_castWitness_difference a b c
  refine ⟨L, ?_⟩
  change carrierTripleNumerator
    (witnessCarrierLine (g (f i.castSucc))) (witnessCarrierLine (g (f i.succ)))
    (witnessCarrierLine (g (f j.castSucc))) (witnessCarrierLine (g (f j.succ)))
    (witnessCarrierLine (g (f k.castSucc))) (witnessCarrierLine (g (f k.succ))) ≠ 0
  have hnum := carrierTripleNumerator_eq_scaled_det
    (witnessCarrierLine (g (f i.castSucc))) (witnessCarrierLine (g (f i.succ)))
    (witnessCarrierLine (g (f j.castSucc))) (witnessCarrierLine (g (f j.succ)))
    (witnessCarrierLine (g (f k.castSucc))) (witnessCarrierLine (g (f k.succ)))
    hden₁ hden₂ hden₃
  rw [hInt₁, hInt₂, hInt₃, hplanar] at hnum
  intro hz
  rw [hnum] at hz
  have hscale :
      (lineDenominator (witnessCarrierLine (g (f i.castSucc))) (witnessCarrierLine (g (f i.succ))) *
       lineDenominator (witnessCarrierLine (g (f j.castSucc))) (witnessCarrierLine (g (f j.succ))) *
       lineDenominator (witnessCarrierLine (g (f k.castSucc))) (witnessCarrierLine (g (f k.succ)))) ≠ 0 :=
    mul_ne_zero (mul_ne_zero hden₁ hden₂) hden₃
  rcases mul_eq_zero.mp hz with hzero | hzero
  · exact hscale hzero
  · exact hdetR hzero

theorem triple_numerator_nonzero_dense {α : Type*} [DecidableEq α]
    {m : ℕ} (f : Fin (m + 1) → α) (hf : Function.Injective f)
    (i j k : Fin m) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    Dense {L : α → CarrierLine |
      carrierTripleNumerator
        (L (f i.castSucc)) (L (f i.succ))
        (L (f j.castSucc)) (L (f j.succ))
        (L (f k.castSucc)) (L (f k.succ)) ≠ 0} := by
  obtain ⟨L, hL⟩ := triple_numerator_nonzero_witness f hf i j k hij hjk hik
  exact DirectGLSSW.CarrierDensity.dense_assignmentNumerator_ne_zero
    (f i.castSucc) (f i.succ) (f j.castSucc) (f j.succ) (f k.castSucc) (f k.succ) L hL

end DirectGLSSW.OpenCarrierChain



