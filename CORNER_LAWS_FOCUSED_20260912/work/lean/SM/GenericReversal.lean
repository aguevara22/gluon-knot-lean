import SM.Reversal
import SM.Generic

/-! Reversal transports actual closed and open edge segments and the full
G1/G2 generic locus. No nonzero-turn counting premise is hidden here. -/

namespace SM

variable {n : ℕ}

theorem chi_reversal (P : LabelledTuple n) (i j k : ZMod n) :
    chi (reversal P) i j k = chi P (2 - i) (2 - j) (2 - k) := rfl

theorem edgePoint_reversal (P : LabelledTuple n) (i : ZMod n) (t : ℝ) :
    edgePoint (reversal P) i t = edgePoint P (1 - i) (1 - t) := by
  have hi : (1 : ZMod n) - i + 1 = 2 - i := by ring
  rw [edgePoint, edge_reversal]
  simp only [reversal, edgePoint, edge, hi]
  apply Prod.ext <;> dsimp <;> ring

theorem edgeSegment_reversal (P : LabelledTuple n) (i : ZMod n) :
    edgeSegment (reversal P) i = edgeSegment P (1 - i) := by
  ext x
  constructor
  · rintro ⟨t, ht0, ht1, rfl⟩
    exact ⟨1 - t, by linarith, by linarith, edgePoint_reversal P i t⟩
  · rintro ⟨t, ht0, ht1, rfl⟩
    refine ⟨1 - t, by linarith, by linarith, ?_⟩
    rw [edgePoint_reversal]
    congr 1
    ring

theorem edgeInterior_reversal (P : LabelledTuple n) (i : ZMod n) :
    edgeInterior (reversal P) i = edgeInterior P (1 - i) := by
  ext x
  constructor
  · rintro ⟨t, ht0, ht1, rfl⟩
    exact ⟨1 - t, by linarith, by linarith, edgePoint_reversal P i t⟩
  · rintro ⟨t, ht0, ht1, rfl⟩
    refine ⟨1 - t, by linarith, by linarith, ?_⟩
    rw [edgePoint_reversal]
    congr 1
    ring

theorem g1_reversal_forward {P : LabelledTuple n} (h : G1 P) : G1 (reversal P) := by
  intro i j k hij hjk hik
  rw [chi_reversal]
  apply h
  · exact fun he => hij ((Equiv.subLeft (2 : ZMod n)).injective he)
  · exact fun he => hjk ((Equiv.subLeft (2 : ZMod n)).injective he)
  · exact fun he => hik ((Equiv.subLeft (2 : ZMod n)).injective he)

theorem g2_reversal_forward {P : LabelledTuple n} (h : G2 P) : G2 (reversal P) := by
  rintro ⟨i, j, k, x, hij, hjk, hik, hi, hj, hk⟩
  apply h
  refine ⟨1 - i, 1 - j, 1 - k, x, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun he => hij ((Equiv.subLeft (1 : ZMod n)).injective he)
  · exact fun he => hjk ((Equiv.subLeft (1 : ZMod n)).injective he)
  · exact fun he => hik ((Equiv.subLeft (1 : ZMod n)).injective he)
  · simpa only [edgeInterior_reversal] using hi
  · simpa only [edgeInterior_reversal] using hj
  · simpa only [edgeInterior_reversal] using hk

theorem generic_reversal (P : LabelledTuple n) : Generic (reversal P) ↔ Generic P := by
  have hf : ∀ Q : LabelledTuple n, Generic Q → Generic (reversal Q) :=
    fun _ h => ⟨g1_reversal_forward h.1, g2_reversal_forward h.2⟩
  constructor
  · intro h
    simpa only [reversal_involutive P] using hf (reversal P) h
  · exact hf P

end SM
