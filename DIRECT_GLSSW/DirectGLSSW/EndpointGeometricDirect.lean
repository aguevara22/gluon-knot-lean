import DirectGLSSW.EndpointEventGeometry
import DirectGLSSW.EndpointCollinearity
import DirectGLSSW.EndpointDirectFactor

/-!
# Geometric realization of the direct endpoint source

An isolated transverse event at (0,k,j) gives the direct ordinary-current
jump for the three sign cases. The conclusions concern one endpoint pair and
do not propagate an endpoint matrix or a whole source row.
-/

namespace DirectGLSSW
open DirectGLSSW.EndpointEventGeometry

/-- The common event radius supplies generic nearby sign arrays, the unique
sign jump, and the signed far identities at the event. -/
theorem exists_endpoint_event_sign_data
    (q : ℕ → PlanarPoint ℝ) (v : PlanarPoint ℝ) (N : ℕ)
    {k j : ℕ} (hk : 0 < k) (hkj : k < j) (hjN : j ≤ N) (τ : ℝ)
    (hcollinear : q k = q 0 + τ • (q j - q 0))
    (htransverse : planarDet (q k - q j) v ≠ 0)
    (hisolated : ∀ a b c, a < b → b < c → c ≤ N →
      (a ≠ 0 ∨ b ≠ k ∨ c ≠ j) → polygonHDet q a b c ≠ 0)
    (hτ : τ ≠ 0) (hτ1 : 1 - τ ≠ 0) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ ε : ℝ, 0 < ε → ε < ρ →
      ShortEdgeSignStability.CoreHGeneric
          (EndpointEventGeometry.moveEndpoint q v ε) N ∧
      ShortEdgeSignStability.CoreHGeneric
          (EndpointEventGeometry.moveEndpoint q v (-ε)) N ∧
      (∀ a b c, a < b → b < c → c ≤ N →
        (a ≠ 0 ∨ b ≠ k ∨ c ≠ j) →
        polygonSignArray (EndpointEventGeometry.moveEndpoint q v ε) a b c =
          polygonSignArray (EndpointEventGeometry.moveEndpoint q v (-ε)) a b c) ∧
      (polygonSignArray (EndpointEventGeometry.moveEndpoint q v ε) 0 k j -
        polygonSignArray (EndpointEventGeometry.moveEndpoint q v (-ε)) 0 k j =
          2 * scalarSignValue (planarDet (q k - q j) v)) ∧
      (∀ l, 0 < l → l < k →
        polygonSignArray (EndpointEventGeometry.moveEndpoint q v (-ε)) 0 l k =
          scalarSignValue τ *
            polygonSignArray (EndpointEventGeometry.moveEndpoint q v (-ε)) 0 l j) ∧
      (∀ l, k < l → l < j →
        polygonSignArray (EndpointEventGeometry.moveEndpoint q v (-ε)) k l j =
          scalarSignValue (1 - τ) *
            polygonSignArray (EndpointEventGeometry.moveEndpoint q v (-ε)) 0 l j) := by
  have hzero : polygonHDet q 0 k j = 0 := by
    simp [polygonHDet, planarDet, hcollinear]; ring
  obtain ⟨ρ, hρ, hgood⟩ := EndpointEventGeometry.exists_endpoint_event_radius
    q v N hk hkj hjN hzero htransverse hisolated
  refine ⟨ρ, hρ, ?_⟩
  intro ε hε hερ
  obtain ⟨hgenericPlus, hgenericMinus, hstable, hjump⟩ := hgood ε hε hερ
  have hleft : ∀ l, 0 < l → l < k →
      polygonSignArray (EndpointEventGeometry.moveEndpoint q v (-ε)) 0 l k =
        scalarSignValue τ *
          polygonSignArray (EndpointEventGeometry.moveEndpoint q v (-ε)) 0 l j := by
    intro l h0l hlk
    have hparent : polygonHDet q 0 l j ≠ 0 :=
      hisolated 0 l j (by omega) (by omega) hjN (by omega)
    obtain ⟨hprefix, _, hprefixSign, _⟩ :=
      EndpointCollinearity.collinear_far_sign_identities q 0 l k j τ hcollinear
        hτ hτ1 hparent
    have hsign : polygonSignArray q 0 l k =
        scalarSignValue τ * polygonSignArray q 0 l j := by
      change scalarSignValue (polygonHDet q 0 l k) =
        scalarSignValue τ * scalarSignValue (polygonHDet q 0 l j)
      rw [scalarSignValue_eq_nonzeroScalarSign _ hprefix,
        scalarSignValue_eq_nonzeroScalarSign τ hτ,
        scalarSignValue_eq_nonzeroScalarSign _ hparent]
      exact hprefixSign
    have hleftStable := hstable 0 l k (by omega) (by omega) (by omega) (by omega)
    have hparentStable := hstable 0 l j (by omega) (by omega) (by omega) (by omega)
    calc
      _ = polygonSignArray q 0 l k := hleftStable.2
      _ = scalarSignValue τ * polygonSignArray q 0 l j := hsign
      _ = _ := by rw [hparentStable.2]
  have hright : ∀ l, k < l → l < j →
      polygonSignArray (EndpointEventGeometry.moveEndpoint q v (-ε)) k l j =
        scalarSignValue (1 - τ) *
          polygonSignArray (EndpointEventGeometry.moveEndpoint q v (-ε)) 0 l j := by
    intro l hkl hlj
    have hparent : polygonHDet q 0 l j ≠ 0 :=
      hisolated 0 l j (by omega) (by omega) hjN (by omega)
    obtain ⟨_, hsuffix, _, hsuffixSign⟩ :=
      EndpointCollinearity.collinear_far_sign_identities q 0 l k j τ hcollinear
        hτ hτ1 hparent
    have hsign : polygonSignArray q k l j =
        scalarSignValue (1 - τ) * polygonSignArray q 0 l j := by
      change scalarSignValue (polygonHDet q k l j) =
        scalarSignValue (1 - τ) * scalarSignValue (polygonHDet q 0 l j)
      rw [scalarSignValue_eq_nonzeroScalarSign _ hsuffix,
        scalarSignValue_eq_nonzeroScalarSign _ hτ1,
        scalarSignValue_eq_nonzeroScalarSign _ hparent]
      exact hsuffixSign
    have hleftStable := hstable k l j (by omega) (by omega) (by omega) (by omega)
    have hparentStable := hstable 0 l j (by omega) (by omega) (by omega) (by omega)
    calc
      _ = polygonSignArray q k l j := hleftStable.2
      _ = scalarSignValue (1 - τ) * polygonSignArray q 0 l j := hsign
      _ = _ := by rw [hparentStable.2]
  refine ⟨hgenericPlus, hgenericMinus, ?_, hjump, hleft, hright⟩
  intro a b c hab hbc hc he
  have hstable' := hstable a b c hab hbc hc he
  exact hstable'.1.trans hstable'.2.symm

/-- For 0<τ<1 both direct factors are ordinary sources. -/
theorem exists_endpoint_direct_positive_positive
    (q : ℕ → PlanarPoint ℝ) (v : PlanarPoint ℝ) (d : ℕ → ℚ) (N : ℕ)
    {k j : ℕ} (hk : 0 < k) (hkj : k < j) (hjN : j ≤ N) (τ : ℝ)
    (hcollinear : q k = q 0 + τ • (q j - q 0))
    (htransverse : planarDet (q k - q j) v ≠ 0)
    (hisolated : ∀ a b c, a < b → b < c → c ≤ N →
      (a ≠ 0 ∨ b ≠ k ∨ c ≠ j) → polygonHDet q a b c ≠ 0)
    (hτ : 0 < τ) (hτ1 : 0 < 1 - τ) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ ε : ℝ, 0 < ε → ε < ρ →
      ShortEdgeSignStability.CoreHGeneric
          (EndpointEventGeometry.moveEndpoint q v ε) N ∧
      ShortEdgeSignStability.CoreHGeneric
          (EndpointEventGeometry.moveEndpoint q v (-ε)) N ∧
      ordinaryCurrent (fun _ l _ => d l)
          (polygonSignArray (EndpointEventGeometry.moveEndpoint q v ε)) 0 j -
        ordinaryCurrent (fun _ l _ => d l)
          (polygonSignArray (EndpointEventGeometry.moveEndpoint q v (-ε))) 0 j =
        scalarSignValue (planarDet (q k - q j) v) * source 0 k * source k j := by
  have hτnz : τ ≠ 0 := ne_of_gt hτ
  have hτ1nz : 1 - τ ≠ 0 := ne_of_gt hτ1
  obtain ⟨ρ, hρ, hdata⟩ := exists_endpoint_event_sign_data q v N hk hkj hjN τ
    hcollinear htransverse hisolated hτnz hτ1nz
  refine ⟨ρ, hρ, ?_⟩
  intro ε hε hερ
  obtain ⟨hgenericPlus, hgenericMinus, hother, hchange, hleft, hright⟩ :=
    hdata ε hε hερ
  have hotherLocal : ∀ a b c, 0 ≤ a → a < b → b < c → c ≤ j →
      (a ≠ 0 ∨ b ≠ k ∨ c ≠ j) →
      polygonSignArray (EndpointEventGeometry.moveEndpoint q v ε) a b c =
        polygonSignArray (EndpointEventGeometry.moveEndpoint q v (-ε)) a b c := by
    intro a b c _ hab hbc hc he
    exact hother a b c hab hbc (le_trans hc hjN) he
  have hσL : scalarSignValue τ = 1 := by
    simp [scalarSignValue, ne_of_gt hτ, not_lt_of_gt hτ]
  have hσR : scalarSignValue (1 - τ) = 1 := by
    simp [scalarSignValue, ne_of_gt hτ1, not_lt_of_gt hτ1]
  have hleft' : ∀ l, 0 < l → l < k →
      polygonSignArray (EndpointEventGeometry.moveEndpoint q v (-ε)) 0 l k =
        polygonSignArray (EndpointEventGeometry.moveEndpoint q v (-ε)) 0 l j := by
    intro l h0l hlk
    simpa [hσL] using hleft l h0l hlk
  have hright' : ∀ l, k < l → l < j →
      polygonSignArray (EndpointEventGeometry.moveEndpoint q v (-ε)) k l j =
        polygonSignArray (EndpointEventGeometry.moveEndpoint q v (-ε)) 0 l j := by
    intro l hkl hlj
    simpa [hσR] using hright l hkl hlj
  have hdirect := ordinaryCurrent_middle_single_far_gate_positive_positive d
    (polygonSignArray (EndpointEventGeometry.moveEndpoint q v (-ε)))
    (polygonSignArray (EndpointEventGeometry.moveEndpoint q v ε)) (by omega) hk hkj
    (scalarSignValue (planarDet (q k - q j) v)) hotherLocal hchange hleft' hright'
  exact ⟨hgenericPlus, hgenericMinus, hdirect⟩

/-- For τ<0 the prefix factor is marked and the suffix factor ordinary. -/
theorem exists_endpoint_direct_negative_positive
    (q : ℕ → PlanarPoint ℝ) (v : PlanarPoint ℝ) (d : ℕ → ℚ) (N : ℕ)
    {k j : ℕ} (hk : 0 < k) (hkj : k < j) (hjN : j ≤ N) (τ : ℝ)
    (hcollinear : q k = q 0 + τ • (q j - q 0))
    (htransverse : planarDet (q k - q j) v ≠ 0)
    (hisolated : ∀ a b c, a < b → b < c → c ≤ N →
      (a ≠ 0 ∨ b ≠ k ∨ c ≠ j) → polygonHDet q a b c ≠ 0)
    (hτ : τ < 0) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ ε : ℝ, 0 < ε → ε < ρ →
      ShortEdgeSignStability.CoreHGeneric
          (EndpointEventGeometry.moveEndpoint q v ε) N ∧
      ShortEdgeSignStability.CoreHGeneric
          (EndpointEventGeometry.moveEndpoint q v (-ε)) N ∧
      ordinaryCurrent (fun _ l _ => d l)
          (polygonSignArray (EndpointEventGeometry.moveEndpoint q v ε)) 0 j -
        ordinaryCurrent (fun _ l _ => d l)
          (polygonSignArray (EndpointEventGeometry.moveEndpoint q v (-ε))) 0 j =
        scalarSignValue (planarDet (q k - q j) v) *
          markedAmplitude (fun _ l _ => d l)
            (polygonSignArray (EndpointEventGeometry.moveEndpoint q v (-ε))) 0 k * source k j := by
  have hτnz : τ ≠ 0 := ne_of_lt hτ
  have hτ1pos : 0 < 1 - τ := by linarith
  have hτ1nz : 1 - τ ≠ 0 := ne_of_gt hτ1pos
  obtain ⟨ρ, hρ, hdata⟩ := exists_endpoint_event_sign_data q v N hk hkj hjN τ
    hcollinear htransverse hisolated hτnz hτ1nz
  refine ⟨ρ, hρ, ?_⟩
  intro ε hε hερ
  obtain ⟨hgenericPlus, hgenericMinus, hother, hchange, hleft, hright⟩ :=
    hdata ε hε hερ
  have hotherLocal : ∀ a b c, 0 ≤ a → a < b → b < c → c ≤ j →
      (a ≠ 0 ∨ b ≠ k ∨ c ≠ j) →
      polygonSignArray (EndpointEventGeometry.moveEndpoint q v ε) a b c =
        polygonSignArray (EndpointEventGeometry.moveEndpoint q v (-ε)) a b c := by
    intro a b c _ hab hbc hc he
    exact hother a b c hab hbc (le_trans hc hjN) he
  have hσL : scalarSignValue τ = -1 := by
    simp [scalarSignValue, hτnz, hτ]
  have hσR : scalarSignValue (1 - τ) = 1 := by
    simp [scalarSignValue, hτ1nz, ne_of_gt hτ1pos, not_lt_of_gt hτ1pos]
  have hleft' : ∀ l, 0 < l → l < k →
      polygonSignArray (EndpointEventGeometry.moveEndpoint q v (-ε)) 0 l k =
        -polygonSignArray (EndpointEventGeometry.moveEndpoint q v (-ε)) 0 l j := by
    intro l h0l hlk
    simpa [hσL] using hleft l h0l hlk
  have hright' : ∀ l, k < l → l < j →
      polygonSignArray (EndpointEventGeometry.moveEndpoint q v (-ε)) k l j =
        polygonSignArray (EndpointEventGeometry.moveEndpoint q v (-ε)) 0 l j := by
    intro l hkl hlj
    simpa [hσR] using hright l hkl hlj
  have hdirect := ordinaryCurrent_middle_single_far_gate_negative_positive d
    (polygonSignArray (EndpointEventGeometry.moveEndpoint q v (-ε)))
    (polygonSignArray (EndpointEventGeometry.moveEndpoint q v ε)) (by omega) hk hkj
    (scalarSignValue (planarDet (q k - q j) v)) hotherLocal hchange hleft' hright'
  exact ⟨hgenericPlus, hgenericMinus, hdirect⟩

/-- For τ>1 the prefix factor is ordinary and the suffix factor marked. -/
theorem exists_endpoint_direct_positive_negative
    (q : ℕ → PlanarPoint ℝ) (v : PlanarPoint ℝ) (d : ℕ → ℚ) (N : ℕ)
    {k j : ℕ} (hk : 0 < k) (hkj : k < j) (hjN : j ≤ N) (τ : ℝ)
    (hcollinear : q k = q 0 + τ • (q j - q 0))
    (htransverse : planarDet (q k - q j) v ≠ 0)
    (hisolated : ∀ a b c, a < b → b < c → c ≤ N →
      (a ≠ 0 ∨ b ≠ k ∨ c ≠ j) → polygonHDet q a b c ≠ 0)
    (hτ : 1 < τ) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ ε : ℝ, 0 < ε → ε < ρ →
      ShortEdgeSignStability.CoreHGeneric
          (EndpointEventGeometry.moveEndpoint q v ε) N ∧
      ShortEdgeSignStability.CoreHGeneric
          (EndpointEventGeometry.moveEndpoint q v (-ε)) N ∧
      ordinaryCurrent (fun _ l _ => d l)
          (polygonSignArray (EndpointEventGeometry.moveEndpoint q v ε)) 0 j -
        ordinaryCurrent (fun _ l _ => d l)
          (polygonSignArray (EndpointEventGeometry.moveEndpoint q v (-ε))) 0 j =
        scalarSignValue (planarDet (q k - q j) v) * source 0 k *
          markedAmplitude (fun _ l _ => d l)
            (polygonSignArray (EndpointEventGeometry.moveEndpoint q v (-ε))) k j := by
  have hτpos : 0 < τ := by linarith
  have hτnz : τ ≠ 0 := ne_of_gt hτpos
  have hτ1 : 1 - τ < 0 := by linarith
  have hτ1nz : 1 - τ ≠ 0 := ne_of_lt hτ1
  obtain ⟨ρ, hρ, hdata⟩ := exists_endpoint_event_sign_data q v N hk hkj hjN τ
    hcollinear htransverse hisolated hτnz hτ1nz
  refine ⟨ρ, hρ, ?_⟩
  intro ε hε hερ
  obtain ⟨hgenericPlus, hgenericMinus, hother, hchange, hleft, hright⟩ :=
    hdata ε hε hερ
  have hotherLocal : ∀ a b c, 0 ≤ a → a < b → b < c → c ≤ j →
      (a ≠ 0 ∨ b ≠ k ∨ c ≠ j) →
      polygonSignArray (EndpointEventGeometry.moveEndpoint q v ε) a b c =
        polygonSignArray (EndpointEventGeometry.moveEndpoint q v (-ε)) a b c := by
    intro a b c _ hab hbc hc he
    exact hother a b c hab hbc (le_trans hc hjN) he
  have hσL : scalarSignValue τ = 1 := by
    simp [scalarSignValue, ne_of_gt hτpos, not_lt_of_gt hτpos]
  have hσR : scalarSignValue (1 - τ) = -1 := by
    simp [scalarSignValue, hτ1nz, hτ1]
  have hleft' : ∀ l, 0 < l → l < k →
      polygonSignArray (EndpointEventGeometry.moveEndpoint q v (-ε)) 0 l k =
        polygonSignArray (EndpointEventGeometry.moveEndpoint q v (-ε)) 0 l j := by
    intro l h0l hlk
    simpa [hσL] using hleft l h0l hlk
  have hright' : ∀ l, k < l → l < j →
      polygonSignArray (EndpointEventGeometry.moveEndpoint q v (-ε)) k l j =
        -polygonSignArray (EndpointEventGeometry.moveEndpoint q v (-ε)) 0 l j := by
    intro l hkl hlj
    simpa [hσR] using hright l hkl hlj
  have hdirect := ordinaryCurrent_middle_single_far_gate_positive_negative d
    (polygonSignArray (EndpointEventGeometry.moveEndpoint q v (-ε)))
    (polygonSignArray (EndpointEventGeometry.moveEndpoint q v ε)) (by omega) hk hkj
    (scalarSignValue (planarDet (q k - q j) v)) hotherLocal hchange hleft' hright'
  exact ⟨hgenericPlus, hgenericMinus, hdirect⟩

end DirectGLSSW
