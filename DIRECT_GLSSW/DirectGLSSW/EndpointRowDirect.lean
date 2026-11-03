import DirectGLSSW.EndpointCurrent
import DirectGLSSW.EndpointDirectFactor
import DirectGLSSW.ShortEdgeBoundedCongruence

set_option autoImplicit false

namespace DirectGLSSW.EndpointCurrent
open DirectGLSSW

/-- The marked current on the endpoint word beginning at row `a`. -/
noncomputable def endpointMarked (d : ℕ → ℚ) (H : TripleArray) (a i : ℕ) : ℚ :=
  if a ≤ i then markedAmplitude (fun _ l _ => d l) (endpointFar a H) a (i + 1) else 0

/-- The diagonal endpoint word has marked amplitude one. -/
theorem endpointMarked_diagonal (d : ℕ → ℚ) (H : TripleArray) (a : ℕ) :
    endpointMarked d H a a = 1 := by
  rw [endpointMarked, if_pos (le_rfl)]
  unfold markedAmplitude
  rw [phi_eq_unary_add]
  have hIoo : Finset.Ioo a (a + 1) = ∅ := by
    apply Finset.eq_empty_iff_forall_not_mem.mpr
    intro x hx
    rcases Finset.mem_Ioo.mp hx with ⟨hax, hxsucc⟩
    omega
  simp [nonUnary, hIoo, ordinaryCurrent_adjacent]

private theorem endpointFar_row_event_other (H0 H1 : TripleArray)
    {N k j a : ℕ} (ha : a < k) (hjN : j ≤ N)
    (hother : ∀ x y z, x < y → y < z → z ≤ N →
      (x ≠ 0 ∨ y ≠ k ∨ z ≠ j) → H1 x y z = H0 x y z) :
    ∀ x y z, a ≤ x → x < y → y < z → z ≤ j →
      (x ≠ a ∨ y ≠ k ∨ z ≠ j) →
        endpointFar a H1 x y z = endpointFar a H0 x y z := by
  intro x y z hax hxy hyz hzj hnot
  by_cases hxa : x = a
  · have hnotYZ : y ≠ k ∨ z ≠ j := by simpa [hxa] using hnot
    have heq := hother 0 y z (by omega) hyz (by omega) (Or.inr hnotYZ)
    simp [endpointFar, hxa, heq]
  · have hx0 : x ≠ 0 := by omega
    have heq := hother x y z hxy hyz (by omega) (Or.inl hx0)
    simp [endpointFar, hxa, heq]

private theorem endpointFar_row_agree (H0 H1 : TripleArray)
    {N k j a : ℕ} (hk : 0 < k) (hka : k ≤ a) (hjN : j ≤ N)
    (hother : ∀ x y z, x < y → y < z → z ≤ N →
      (x ≠ 0 ∨ y ≠ k ∨ z ≠ j) → H1 x y z = H0 x y z) :
    ∀ x y z, a ≤ x → x < y → y < z → z ≤ j →
      endpointFar a H1 x y z = endpointFar a H0 x y z := by
  intro x y z hax hxy hyz hzj
  by_cases hxa : x = a
  · have hyk : y ≠ k := by omega
    have heq := hother 0 y z (by omega) hyz (by omega) (Or.inr (Or.inl hyk))
    simp [endpointFar, hxa, heq]
  · have hx0 : x ≠ 0 := by omega
    have heq := hother x y z hxy hyz (by omega) (Or.inl hx0)
    simp [endpointFar, hxa, heq]

private theorem endpointCurrent_row_factor
    (d : ℕ → ℚ) (H0 H1 : TripleArray) {N k j : ℕ}
    (hk : 0 < k) (hkj : k < j) (hjN : j ≤ N) (δ σL σR : ℚ)
    (hσL : σL = 1 ∨ σL = -1) (hσR : σR = 1 ∨ σR = -1)
    (hother : ∀ x y z, x < y → y < z → z ≤ N →
      (x ≠ 0 ∨ y ≠ k ∨ z ≠ j) → H1 x y z = H0 x y z)
    (hchange : H1 0 k j - H0 0 k j = 2 * δ)
    (hleft : ∀ l, 0 < l → l < k → H0 0 l k = σL * H0 0 l j)
    (hright : ∀ l, k < l → l < j → H0 k l j = σR * H0 0 l j)
    {a : ℕ} (ha : a < k) :
    endpointCurrent d H1 a (j - 1) - endpointCurrent d H0 a (j - 1) =
      δ * phi (fun _ l _ => d l)
          (fun x l z => σL * endpointFar a H0 x l z)
          (ordinaryCurrent (fun _ l _ => d l) (endpointFar a H0)) a k *
        phi (fun _ l _ => d l)
          (fun x l z => σR * endpointFar a H0 x l z)
          (ordinaryCurrent (fun _ l _ => d l) (endpointFar a H0)) k j := by
  let D : TripleArray := fun _ l _ => d l
  let H0a : TripleArray := endpointFar a H0
  let H1a : TripleArray := endpointFar a H1
  have hja : a ≤ j - 1 := by omega
  have hsub : j - 1 + 1 = j := by omega
  have hlocalOther : ∀ x y z, a ≤ x → x < y → y < z → z ≤ j →
      (x ≠ a ∨ y ≠ k ∨ z ≠ j) → H1a x y z = H0a x y z :=
    endpointFar_row_event_other H0 H1 ha hjN hother
  have hlocalChange : H1a a k j - H0a a k j = 2 * δ := by
    simp [H1a, H0a, endpointFar, hchange]
  have hlocalLeft : ∀ l, a < l → l < k → H0a a l k = σL * H0a a l j := by
    intro l hal hlk
    have hl0 : 0 < l := by omega
    simpa [H0a, endpointFar] using hleft l hl0 hlk
  have hlocalRight : ∀ l, k < l → l < j → H0a k l j = σR * H0a a l j := by
    intro l hkl hlj
    have hka : a < k := ha
    simpa [H0a, endpointFar, ne_of_gt hka] using hright l hkl hlj
  have hfactor := ordinaryCurrent_middle_single_far_gate_factorization
    d H0a H1a (i := a) (j := j) (hij := by omega) (k := k)
    (hik := ha) (hkj := hkj) δ σL σR hσL hσR hlocalOther hlocalChange
    hlocalLeft hlocalRight
  rw [endpointCurrent, if_pos hja, endpointCurrent, if_pos hja]
  simpa [D, H0a, H1a, hsub] using hfactor

theorem endpointCurrent_row_positive_positive
    (d : ℕ → ℚ) (H0 H1 : TripleArray) {N k j : ℕ}
    (hk : 0 < k) (hkj : k < j) (hjN : j ≤ N) (δ : ℚ)
    (hother : ∀ x y z, x < y → y < z → z ≤ N →
      (x ≠ 0 ∨ y ≠ k ∨ z ≠ j) → H1 x y z = H0 x y z)
    (hchange : H1 0 k j - H0 0 k j = 2 * δ)
    (hleft : ∀ l, 0 < l → l < k → H0 0 l k = H0 0 l j)
    (hright : ∀ l, k < l → l < j → H0 k l j = H0 0 l j) :
    ∀ a, a < k →
      endpointCurrent d H1 a (j - 1) - endpointCurrent d H0 a (j - 1) =
        δ * source a k * source k j := by
  intro a ha
  have hleft' : ∀ l, 0 < l → l < k → H0 0 l k = (1 : ℚ) * H0 0 l j := by
    intro l hl0 hlk
    simpa using hleft l hl0 hlk
  have hright' : ∀ l, k < l → l < j → H0 k l j = (1 : ℚ) * H0 0 l j := by
    intro l hkl hlj
    simpa using hright l hkl hlj
  have h := endpointCurrent_row_factor d H0 H1 hk hkj hjN δ 1 1
    (Or.inl rfl) (Or.inl rfl) hother hchange hleft' hright' ha
  let D : TripleArray := fun _ l _ => d l
  let H0a : TripleArray := endpointFar a H0
  have hleftPhi : phi D (fun x l z => (1 : ℚ) * H0a x l z)
      (ordinaryCurrent D H0a) a k = source a k := by
    simpa [D, H0a] using ordinaryCurrent_phi D H0a (by omega)
  have hrightPhi : phi D (fun x l z => (1 : ℚ) * H0a x l z)
      (ordinaryCurrent D H0a) k j = source k j := by
    simpa [D, H0a] using ordinaryCurrent_phi D H0a hkj
  rw [hleftPhi, hrightPhi] at h
  simpa [D, H0a] using h

theorem endpointCurrent_row_negative_positive
    (d : ℕ → ℚ) (H0 H1 : TripleArray) {N k j : ℕ}
    (hk : 0 < k) (hkj : k < j) (hjN : j ≤ N) (δ : ℚ)
    (hother : ∀ x y z, x < y → y < z → z ≤ N →
      (x ≠ 0 ∨ y ≠ k ∨ z ≠ j) → H1 x y z = H0 x y z)
    (hchange : H1 0 k j - H0 0 k j = 2 * δ)
    (hleft : ∀ l, 0 < l → l < k → H0 0 l k = -H0 0 l j)
    (hright : ∀ l, k < l → l < j → H0 k l j = H0 0 l j) :
    ∀ a, a < k →
      endpointCurrent d H1 a (j - 1) - endpointCurrent d H0 a (j - 1) =
        δ * endpointMarked d H0 a (k - 1) * source k j := by
  intro a ha
  have hleft' : ∀ l, 0 < l → l < k → H0 0 l k = (-1 : ℚ) * H0 0 l j := by
    intro l hl0 hlk
    simpa using hleft l hl0 hlk
  have hright' : ∀ l, k < l → l < j → H0 k l j = (1 : ℚ) * H0 0 l j := by
    intro l hkl hlj
    simpa using hright l hkl hlj
  have h := endpointCurrent_row_factor d H0 H1 hk hkj hjN δ (-1) 1
    (Or.inr rfl) (Or.inl rfl) hother hchange hleft' hright' ha
  let D : TripleArray := fun _ l _ => d l
  let H0a : TripleArray := endpointFar a H0
  have hneg : (fun x l z => (-1 : ℚ) * H0a x l z) =
      (fun x l z => -H0a x l z) := by
    funext x l z
    ring
  have hleftPhi : phi D (fun x l z => (-1 : ℚ) * H0a x l z)
      (ordinaryCurrent D H0a) a k = endpointMarked d H0 a (k - 1) := by
    rw [hneg]
    change markedAmplitude D H0a a k = endpointMarked d H0 a (k - 1)
    rw [endpointMarked, if_pos (by omega)]
    have hkSub : k - 1 + 1 = k := by omega
    rw [hkSub]
  have hrightPhi : phi D (fun x l z => (1 : ℚ) * H0a x l z)
      (ordinaryCurrent D H0a) k j = source k j := by
    simpa [D, H0a] using ordinaryCurrent_phi D H0a hkj
  rw [hleftPhi, hrightPhi] at h
  simpa [D, H0a] using h

theorem endpointCurrent_row_positive_negative
    (d : ℕ → ℚ) (H0 H1 : TripleArray) {N k j : ℕ}
    (hk : 0 < k) (hkj : k < j) (hjN : j ≤ N) (δ : ℚ)
    (hother : ∀ x y z, x < y → y < z → z ≤ N →
      (x ≠ 0 ∨ y ≠ k ∨ z ≠ j) → H1 x y z = H0 x y z)
    (hchange : H1 0 k j - H0 0 k j = 2 * δ)
    (hleft : ∀ l, 0 < l → l < k → H0 0 l k = H0 0 l j)
    (hright : ∀ l, k < l → l < j → H0 k l j = -H0 0 l j) :
    ∀ a, a < k →
      endpointCurrent d H1 a (j - 1) - endpointCurrent d H0 a (j - 1) =
        δ * source a k * markedAmplitude (fun _ l _ => d l) H0 k j := by
  intro a ha
  have hleft' : ∀ l, 0 < l → l < k → H0 0 l k = (1 : ℚ) * H0 0 l j := by
    intro l hl0 hlk
    simpa using hleft l hl0 hlk
  have hright' : ∀ l, k < l → l < j → H0 k l j = (-1 : ℚ) * H0 0 l j := by
    intro l hkl hlj
    simpa using hright l hkl hlj
  have h := endpointCurrent_row_factor d H0 H1 hk hkj hjN δ 1 (-1)
    (Or.inl rfl) (Or.inr rfl) hother hchange hleft' hright' ha
  let D : TripleArray := fun _ l _ => d l
  let H0a : TripleArray := endpointFar a H0
  have hleftPhi : phi D (fun x l z => (1 : ℚ) * H0a x l z)
      (ordinaryCurrent D H0a) a k = source a k := by
    simpa [D, H0a] using ordinaryCurrent_phi D H0a (by omega)
  have hHlocal : ∀ x y z, k ≤ x → x < y → y < z → z ≤ j → H0a x y z = H0 x y z := by
    intro x y z hkx hxy hyz hzj
    have hxa : x ≠ a := by omega
    simp [H0a, endpointFar, hxa]
  have hneg : (fun x l z => (-1 : ℚ) * H0a x l z) =
      (fun x l z => -H0a x l z) := by
    funext x l z
    ring
  have hrightPhi : phi D (fun x l z => (-1 : ℚ) * H0a x l z)
      (ordinaryCurrent D H0a) k j = markedAmplitude D H0 k j := by
    rw [hneg]
    calc
      _ = markedAmplitude D H0a k j := rfl
      _ = markedAmplitude D H0 k j :=
        markedAmplitude_congr_interval D D H0a H0 hkj hHlocal
  rw [hleftPhi, hrightPhi] at h
  simpa [D, H0a] using h

theorem endpointCurrent_rows_zero_from
    (d : ℕ → ℚ) (H0 H1 : TripleArray) {N k j : ℕ}
    (hk : 0 < k) (hkj : k < j) (hjN : j ≤ N)
    (hother : ∀ x y z, x < y → y < z → z ≤ N →
      (x ≠ 0 ∨ y ≠ k ∨ z ≠ j) → H1 x y z = H0 x y z) :
    ∀ a, k ≤ a →
      endpointCurrent d H1 a (j - 1) - endpointCurrent d H0 a (j - 1) = 0 := by
  intro a hka
  by_cases hproper : a < j - 1
  · let D : TripleArray := fun _ l _ => d l
    have hsub : j - 1 + 1 = j := by omega
    have hagree := endpointFar_row_agree H0 H1 hk hka hjN hother
    have hinterval : ordinaryCurrent D (endpointFar a H1) a j =
        ordinaryCurrent D (endpointFar a H0) a j := by
      apply ordinaryCurrent_congr_interval_fixed_near D (endpointFar a H1)
        (endpointFar a H0) (by omega)
      intro x y z hax hxy hyz hzj
      exact hagree x y z hax hxy hyz hzj
    rw [endpointCurrent, if_pos (by omega : a ≤ j - 1),
      endpointCurrent, if_pos (by omega : a ≤ j - 1)]
    rw [hsub]
    rw [hinterval]
    ring
  · by_cases hdiag : a = j - 1
    · subst a
      rw [endpointCurrent_diagonal, endpointCurrent_diagonal]
      ring
    · have hbelow : j - 1 < a := by omega
      rw [endpointCurrent_below d H1 hbelow, endpointCurrent_below d H0 hbelow]
      ring










end DirectGLSSW.EndpointCurrent
