import DirectGLSSW.CutSplit
import DirectGLSSW.EndpointDirectSource

/-!
# Sign-dependent factorization of the direct endpoint source

The actual cut-sum split and direct ordinary-current jump identify three
bounded far-sign cases. This module makes no claim about a geometric event or
propagation to larger endpoints.
-/

namespace DirectGLSSW
open scoped BigOperators

/-- A weighted cut sum is the ordinary or marked interval amplitude when the
subinterval far data differ from the parent far data by a sign. -/
theorem weightedCutSum_eq_phi_of_scaled_far (d : ℕ → ℚ) (Hsub Hparent : TripleArray)
    (b : IntervalArray) {a c i j : ℕ} (hac : a < c) (σ : ℚ)
    (hσ : σ = 1 ∨ σ = -1)
    (hfar : ∀ l, a < l → l < c → Hsub a l c = σ * Hparent i l j) :
    (∑ S ∈ (Finset.Ioo a c).powerset,
      (∏ l ∈ S, (d l - Hparent i l j) / 2) * branchProduct b (cutVertices a c S)) =
      phi (fun _ l _ => d l) (fun x l y => σ * Hsub x l y) b a c := by
  classical
  have hσσ : σ * σ = 1 := by
    rcases hσ with h | h
    · rw [h]
      norm_num
    · rw [h]
      norm_num
  unfold phi
  apply Finset.sum_congr rfl
  intro S hS
  have hSsub : S ⊆ Finset.Ioo a c := Finset.mem_powerset.mp hS
  rw [cutContribution,
    gateProduct_middleNear_eq_prod d (fun x l y => σ * Hsub x l y) hac hSsub]
  have hprod :
      (∏ l ∈ S, (d l - σ * Hsub a l c) / 2) =
        ∏ l ∈ S, (d l - Hparent i l j) / 2 := by
    apply Finset.prod_congr rfl
    intro l hl
    have hlI : l ∈ Finset.Ioo a c := hSsub hl
    have hbounds := Finset.mem_Ioo.mp hlI
    rw [hfar l hbounds.1 hbounds.2]
    have hmul : σ * (σ * Hparent i l j) = Hparent i l j := by
      calc
        _ = (σ * σ) * Hparent i l j := by ring
        _ = Hparent i l j := by rw [hσσ, one_mul]
    rw [hmul]
  rw [hprod]

/-- Under two bounded far-sign identities, the direct endpoint jump factors
into the corresponding ordinary or marked interval amplitudes. -/
theorem ordinaryCurrent_middle_single_far_gate_factorization
    (d : ℕ → ℚ) (H₀ H₁ : TripleArray) {i j : ℕ} (hij : i < j)
    {k : ℕ} (hik : i < k) (hkj : k < j) (δ σL σR : ℚ)
    (hσL : σL = 1 ∨ σL = -1) (hσR : σR = 1 ∨ σR = -1)
    (hother : ∀ a b c, i ≤ a → a < b → b < c → c ≤ j →
      (a ≠ i ∨ b ≠ k ∨ c ≠ j) → H₁ a b c = H₀ a b c)
    (hchange : H₁ i k j - H₀ i k j = 2 * δ)
    (hleft : ∀ l, i < l → l < k → H₀ i l k = σL * H₀ i l j)
    (hright : ∀ l, k < l → l < j → H₀ k l j = σR * H₀ i l j) :
    ordinaryCurrent (fun _ l _ => d l) H₁ i j -
        ordinaryCurrent (fun _ l _ => d l) H₀ i j =
      δ * phi (fun _ l _ => d l) (fun a l c => σL * H₀ a l c)
          (ordinaryCurrent (fun _ l _ => d l) H₀) i k *
        phi (fun _ l _ => d l) (fun a l c => σR * H₀ a l c)
          (ordinaryCurrent (fun _ l _ => d l) H₀) k j := by
  let D : TripleArray := fun _ l _ => d l
  let b₀ : IntervalArray := ordinaryCurrent D H₀
  let w : ℕ → ℚ := fun l => (d l - H₀ i l j) / 2
  have hleftSum := weightedCutSum_eq_phi_of_scaled_far d H₀ H₀ b₀ hik σL hσL hleft
  have hrightSum := weightedCutSum_eq_phi_of_scaled_far d H₀ H₀ b₀ hkj σR hσR hright
  have hsplit := weightedCutSum_split_at w b₀ hik hkj
  have hjump :=
    ordinaryCurrent_middle_single_far_gate_change d H₀ H₁ hij hik hkj δ hother hchange
  calc
    _ = δ * (∑ S ∈ (Finset.Ioo i j).powerset.filter (fun S => k ∈ S),
        (∏ l ∈ S.erase k, (d l - H₀ i l j) / 2) *
          branchProduct b₀ (cutVertices i j S)) := by
          simpa [D, b₀] using hjump
    _ = δ *
        ((∑ L ∈ (Finset.Ioo i k).powerset,
            (∏ l ∈ L, w l) * branchProduct b₀ (cutVertices i k L)) *
          (∑ R ∈ (Finset.Ioo k j).powerset,
            (∏ l ∈ R, w l) * branchProduct b₀ (cutVertices k j R))) := by
          rw [hsplit]
    _ = δ *
        (phi D (fun a l c => σL * H₀ a l c) b₀ i k *
          phi D (fun a l c => σR * H₀ a l c) b₀ k j) := by
          rw [← hleftSum, ← hrightSum]
    _ = _ := by
          simp only [D, b₀]
          ring

/-- Positive far signs on both sides give the product of the two ordinary
sources. -/
theorem ordinaryCurrent_middle_single_far_gate_positive_positive
    (d : ℕ → ℚ) (H₀ H₁ : TripleArray) {i j : ℕ} (hij : i < j)
    {k : ℕ} (hik : i < k) (hkj : k < j) (δ : ℚ)
    (hother : ∀ a b c, i ≤ a → a < b → b < c → c ≤ j →
      (a ≠ i ∨ b ≠ k ∨ c ≠ j) → H₁ a b c = H₀ a b c)
    (hchange : H₁ i k j - H₀ i k j = 2 * δ)
    (hleft : ∀ l, i < l → l < k → H₀ i l k = H₀ i l j)
    (hright : ∀ l, k < l → l < j → H₀ k l j = H₀ i l j) :
    ordinaryCurrent (fun _ l _ => d l) H₁ i j -
        ordinaryCurrent (fun _ l _ => d l) H₀ i j =
      δ * source i k * source k j := by
  have hleft' : ∀ l, i < l → l < k → H₀ i l k = (1 : ℚ) * H₀ i l j := by
    intro l hil hlk
    simpa using hleft l hil hlk
  have hright' : ∀ l, k < l → l < j → H₀ k l j = (1 : ℚ) * H₀ i l j := by
    intro l hkl hlj
    simpa using hright l hkl hlj
  have hfac := ordinaryCurrent_middle_single_far_gate_factorization
    d H₀ H₁ hij hik hkj δ 1 1 (Or.inl rfl) (Or.inl rfl)
    hother hchange hleft' hright'
  let D : TripleArray := fun _ l _ => d l
  let b₀ : IntervalArray := ordinaryCurrent D H₀
  have hleftPhi : phi D (fun a l c => (1 : ℚ) * H₀ a l c) b₀ i k = source i k := by
    have hf : (fun a l c => (1 : ℚ) * H₀ a l c) = H₀ := by
      funext a l c
      simp
    rw [hf]
    exact ordinaryCurrent_phi D H₀ hik
  have hrightPhi : phi D (fun a l c => (1 : ℚ) * H₀ a l c) b₀ k j = source k j := by
    have hf : (fun a l c => (1 : ℚ) * H₀ a l c) = H₀ := by
      funext a l c
      simp
    rw [hf]
    exact ordinaryCurrent_phi D H₀ hkj
  rw [hleftPhi, hrightPhi] at hfac
  simpa [D] using hfac

/-- A negative prefix sign gives a marked prefix amplitude and an ordinary
suffix source. -/
theorem ordinaryCurrent_middle_single_far_gate_negative_positive
    (d : ℕ → ℚ) (H₀ H₁ : TripleArray) {i j : ℕ} (hij : i < j)
    {k : ℕ} (hik : i < k) (hkj : k < j) (δ : ℚ)
    (hother : ∀ a b c, i ≤ a → a < b → b < c → c ≤ j →
      (a ≠ i ∨ b ≠ k ∨ c ≠ j) → H₁ a b c = H₀ a b c)
    (hchange : H₁ i k j - H₀ i k j = 2 * δ)
    (hleft : ∀ l, i < l → l < k → H₀ i l k = -H₀ i l j)
    (hright : ∀ l, k < l → l < j → H₀ k l j = H₀ i l j) :
    ordinaryCurrent (fun _ l _ => d l) H₁ i j -
        ordinaryCurrent (fun _ l _ => d l) H₀ i j =
      δ * markedAmplitude (fun _ l _ => d l) H₀ i k * source k j := by
  have hleft' : ∀ l, i < l → l < k → H₀ i l k = (-1 : ℚ) * H₀ i l j := by
    intro l hil hlk
    simpa using hleft l hil hlk
  have hright' : ∀ l, k < l → l < j → H₀ k l j = (1 : ℚ) * H₀ i l j := by
    intro l hkl hlj
    simpa using hright l hkl hlj
  have hfac := ordinaryCurrent_middle_single_far_gate_factorization
    d H₀ H₁ hij hik hkj δ (-1) 1 (Or.inr rfl) (Or.inl rfl)
    hother hchange hleft' hright'
  let D : TripleArray := fun _ l _ => d l
  let b₀ : IntervalArray := ordinaryCurrent D H₀
  have hleftPhi : phi D (fun a l c => (-1 : ℚ) * H₀ a l c) b₀ i k =
      markedAmplitude D H₀ i k := by
    have hf : (fun a l c => (-1 : ℚ) * H₀ a l c) =
        (fun a l c => -H₀ a l c) := by
      funext a l c
      ring
    rw [hf]
    rfl
  have hrightPhi : phi D (fun a l c => (1 : ℚ) * H₀ a l c) b₀ k j = source k j := by
    have hf : (fun a l c => (1 : ℚ) * H₀ a l c) = H₀ := by
      funext a l c
      simp
    rw [hf]
    exact ordinaryCurrent_phi D H₀ hkj
  rw [hleftPhi, hrightPhi] at hfac
  simpa [D] using hfac

/-- A negative suffix sign gives an ordinary prefix source and a marked
suffix amplitude. -/
theorem ordinaryCurrent_middle_single_far_gate_positive_negative
    (d : ℕ → ℚ) (H₀ H₁ : TripleArray) {i j : ℕ} (hij : i < j)
    {k : ℕ} (hik : i < k) (hkj : k < j) (δ : ℚ)
    (hother : ∀ a b c, i ≤ a → a < b → b < c → c ≤ j →
      (a ≠ i ∨ b ≠ k ∨ c ≠ j) → H₁ a b c = H₀ a b c)
    (hchange : H₁ i k j - H₀ i k j = 2 * δ)
    (hleft : ∀ l, i < l → l < k → H₀ i l k = H₀ i l j)
    (hright : ∀ l, k < l → l < j → H₀ k l j = -H₀ i l j) :
    ordinaryCurrent (fun _ l _ => d l) H₁ i j -
        ordinaryCurrent (fun _ l _ => d l) H₀ i j =
      δ * source i k * markedAmplitude (fun _ l _ => d l) H₀ k j := by
  have hleft' : ∀ l, i < l → l < k → H₀ i l k = (1 : ℚ) * H₀ i l j := by
    intro l hil hlk
    simpa using hleft l hil hlk
  have hright' : ∀ l, k < l → l < j → H₀ k l j = (-1 : ℚ) * H₀ i l j := by
    intro l hkl hlj
    simpa using hright l hkl hlj
  have hfac := ordinaryCurrent_middle_single_far_gate_factorization
    d H₀ H₁ hij hik hkj δ 1 (-1) (Or.inl rfl) (Or.inr rfl)
    hother hchange hleft' hright'
  let D : TripleArray := fun _ l _ => d l
  let b₀ : IntervalArray := ordinaryCurrent D H₀
  have hleftPhi : phi D (fun a l c => (1 : ℚ) * H₀ a l c) b₀ i k = source i k := by
    have hf : (fun a l c => (1 : ℚ) * H₀ a l c) = H₀ := by
      funext a l c
      simp
    rw [hf]
    exact ordinaryCurrent_phi D H₀ hik
  have hrightPhi : phi D (fun a l c => (-1 : ℚ) * H₀ a l c) b₀ k j =
      markedAmplitude D H₀ k j := by
    have hf : (fun a l c => (-1 : ℚ) * H₀ a l c) =
        (fun a l c => -H₀ a l c) := by
      funext a l c
      ring
    rw [hf]
    rfl
  rw [hleftPhi, hrightPhi] at hfac
  simpa [D, b₀] using hfac

end DirectGLSSW
