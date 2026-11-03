import DirectGLSSW.EndpointActualRecurrence
import DirectGLSSW.OpenMarkedCurrent
import DirectGLSSW.RealPolygons
import ActiveArcGammaM

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW
open DirectGLSSW.EndpointCurrent

/-- Equal indexed vertices through N give the same signed open marked current. -/
theorem openMarkedCurrent_entry_congr_of_word_eq
    (W₁ W₂ : ℕ → PlanarPoint ℝ) {N : ℕ} (hN : 0 < N)
    (hword : ∀ i, i ≤ N → W₁ i = W₂ i) :
    OpenMarkedCurrent.entry (polygonSignArray W₁) 0 N =
      OpenMarkedCurrent.entry (polygonSignArray W₂) 0 N := by
  have hsign (a b c : ℕ) (ha : 0 ≤ a) (hab : a < b)
      (hbc : b < c) (hc : c ≤ N) :
      polygonSignArray W₁ a b c = polygonSignArray W₂ a b c := by
    have haN : a ≤ N := by omega
    have hbN : b ≤ N := by omega
    have hdet : polygonHDet W₁ a b c = polygonHDet W₂ a b c := by
      simp [polygonHDet, planarDet, hword a haN, hword b hbN, hword c hc]
    exact congrArg scalarSignValue hdet
  have hcurrent (i j : ℕ) (hij : i < j) (hj : j ≤ N) :
      ordinaryCurrent (fun _ _ _ => -1) (polygonSignArray W₁) i j =
        ordinaryCurrent (fun _ _ _ => -1) (polygonSignArray W₂) i j := by
    apply ordinaryCurrent_congr_interval_fixed_near _ _ _ hij
    intro a b c hia hab hbc hcj
    exact hsign a b c (by omega) hab hbc (by omega)
  change weightedCutSum (fun _ : ℕ => -1)
      (ordinaryCurrent (fun _ _ _ => -1) (polygonSignArray W₁)) 0 N =
    weightedCutSum (fun _ : ℕ => -1)
      (ordinaryCurrent (fun _ _ _ => -1) (polygonSignArray W₂)) 0 N
  apply EndpointCurrent.weightedCutSum_congr_of_branch_eq (fun _ => -1) hN
  intro a b ha hab hb
  exact hcurrent a b (by omega) hb

namespace ActiveArc.Primitive

/-- The actual retained open current is unchanged when a word W agrees, on the
used index range, with its retained open-vertex sequence. -/
theorem openCurrent_eq_entry_of_word_eq
    {n : ℕ} (q : Fin (n + 2) → PlanarPoint ℝ) (hR : Regular q)
    (S : Support q hR) (W : ℕ → PlanarPoint ℝ)
    (hW : ∀ (k : ℕ) (hk : k < RetainedWords.openCount q hR S.val),
      W k = OpenVertex q hR S ⟨k, hk⟩) :
    openCurrent q hR S =
      OpenMarkedCurrent.entry (polygonSignArray W) 0
        (RetainedWords.openCount q hR S.val - 1) := by
  let N := RetainedWords.openCount q hR S.val - 1
  have hcount := RetainedWords.open_count_ge_two q hR S.val
  have hN : 0 < N := by dsimp [N]; omega
  have hword (k : ℕ) (hk : k ≤ N) :
      rootedPolygonWord (OpenVertex q hR S) (RetainedWords.openLast q hR S.val) k = W k := by
    have hklt : k < RetainedWords.openCount q hR S.val := by
      dsimp [N] at hk
      omega
    exact (openCurrent_word q hR S k hklt).trans (hW k hklt).symm
  change OpenMarkedCurrent.entry
      (polygonSignArray (rootedPolygonWord (OpenVertex q hR S)
        (RetainedWords.openLast q hR S.val))) 0 N =
      OpenMarkedCurrent.entry (polygonSignArray W) 0 N
  exact openMarkedCurrent_entry_congr_of_word_eq _ _ hN hword

end ActiveArc.Primitive




end DirectGLSSW
