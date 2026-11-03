import DirectGLSSW.EndpointGeometricDirect
import DirectGLSSW.EndpointActualPropagation
import DirectGLSSW.EndpointRowDirect

set_option autoImplicit false

namespace DirectGLSSW.EndpointCurrent
open DirectGLSSW DirectGLSSW.EndpointEventGeometry
open scoped BigOperators

/-- An actual row event formula propagates through the compiled endpoint
matrix recurrence to every column. -/
theorem endpointCurrent_propagate_row_formula
    (d : ℕ → ℚ) (H0 H1 : TripleArray) (n k : ℕ) (jFin : Fin n)
    (hother : ∀ x y z, x < y → y < z → z ≤ n →
      (x ≠ 0 ∨ y ≠ k ∨ z ≠ jFin.val + 1) → H1 x y z = H0 x y z)
    (g : ℕ → ℚ)
    (hrow : ∀ a, a < k →
      endpointCurrent d H1 a jFin.val - endpointCurrent d H0 a jFin.val = g a)
    (hzero : ∀ a, k ≤ a →
      endpointCurrent d H1 a jFin.val - endpointCurrent d H0 a jFin.val = 0)
    (hgzero : ∀ a, k ≤ a → g a = 0) :
    ∀ a i : Fin n,
      endpointCurrent d H1 a.val i.val - endpointCurrent d H0 a.val i.val =
        g a.val * endpointCurrent d H0 jFin.val i.val := by
  intro a i
  have hprop := endpointCurrent_single_far_event_propagation
    d H0 H1 n k jFin hother a i
  by_cases hak : a.val < k
  · rw [hrow a.val hak] at hprop
    exact hprop
  · have hka : k ≤ a.val := by omega
    rw [hzero a.val hka] at hprop
    rw [hgzero a.val hka]
    simpa using hprop

/-- A transverse event with τ<0 gives the marked prefix row propagated
through every column of the actual endpoint matrix. -/
theorem exists_endpoint_current_matrix_event_negative_positive
    (q : ℕ → PlanarPoint ℝ) (v : PlanarPoint ℝ) (d : ℕ → ℚ) (n : ℕ)
    {k j : ℕ} (hk : 0 < k) (hkj : k < j) (hjn : j ≤ n) (τ : ℝ)
    (hcollinear : q k = q 0 + τ • (q j - q 0))
    (htransverse : planarDet (q k - q j) v ≠ 0)
    (hisolated : ∀ a b c, a < b → b < c → c ≤ n →
      (a ≠ 0 ∨ b ≠ k ∨ c ≠ j) → polygonHDet q a b c ≠ 0)
    (hτ : τ < 0) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ ε : ℝ, 0 < ε → ε < ρ →
      ShortEdgeSignStability.CoreHGeneric (moveEndpoint q v ε) n ∧
      ShortEdgeSignStability.CoreHGeneric (moveEndpoint q v (-ε)) n ∧
      ∀ a i : Fin n,
        endpointCurrent d (polygonSignArray (moveEndpoint q v ε)) a.val i.val -
          endpointCurrent d (polygonSignArray (moveEndpoint q v (-ε))) a.val i.val =
          scalarSignValue (planarDet (q k - q j) v) *
            endpointMarked d (polygonSignArray (moveEndpoint q v (-ε))) a.val (k - 1) *
            source k j * endpointCurrent d (polygonSignArray (moveEndpoint q v (-ε)))
              (j - 1) i.val := by
  have hτnz : τ ≠ 0 := ne_of_lt hτ
  have hτ1pos : 0 < 1 - τ := by linarith
  have hτ1nz : 1 - τ ≠ 0 := ne_of_gt hτ1pos
  obtain ⟨ρ, hρ, hdata⟩ := exists_endpoint_event_sign_data
    q v n hk hkj hjn τ hcollinear htransverse hisolated hτnz hτ1nz
  refine ⟨ρ, hρ, ?_⟩
  intro ε hε hερ
  obtain ⟨hgenericPlus, hgenericMinus, hother, hchange, hleft, hright⟩ :=
    hdata ε hε hερ
  let Hminus := polygonSignArray (moveEndpoint q v (-ε))
  let Hplus := polygonSignArray (moveEndpoint q v ε)
  let jFin : Fin n := ⟨j - 1, by omega⟩
  have hotherProp : ∀ x y z, x < y → y < z → z ≤ n →
      (x ≠ 0 ∨ y ≠ k ∨ z ≠ jFin.val + 1) → Hplus x y z = Hminus x y z := by
    intro x y z hxy hyz hzn he
    have he' : x ≠ 0 ∨ y ≠ k ∨ z ≠ j := by
      simpa [jFin, Nat.sub_add_cancel (show 1 ≤ j by omega)] using he
    exact hother x y z hxy hyz hzn he'
  have hzero : ∀ a, k ≤ a →
      endpointCurrent d Hplus a jFin.val - endpointCurrent d Hminus a jFin.val = 0 := by
    intro a hak
    simpa [Hplus, Hminus, jFin, Nat.sub_add_cancel (show 1 ≤ j by omega)] using
      (endpointCurrent_rows_zero_from d Hminus Hplus hk hkj hjn hother a hak)
  have hσL : scalarSignValue τ = -1 := by
    simp [scalarSignValue, hτnz, hτ]
  have hσR : scalarSignValue (1 - τ) = 1 := by
    simp [scalarSignValue, hτ1nz, ne_of_gt hτ1pos, not_lt_of_gt hτ1pos]
  have hleft' : ∀ l, 0 < l → l < k → Hminus 0 l k = -Hminus 0 l j := by
    intro l h0l hlk
    simpa [Hminus, hσL] using hleft l h0l hlk
  have hright' : ∀ l, k < l → l < j → Hminus k l j = Hminus 0 l j := by
    intro l hkl hlj
    simpa [Hminus, hσR] using hright l hkl hlj
  let g : ℕ → ℚ := fun a =>
    scalarSignValue (planarDet (q k - q j) v) * endpointMarked d Hminus a (k - 1) * source k j
  have hrow : ∀ a, a < k →
      endpointCurrent d Hplus a jFin.val - endpointCurrent d Hminus a jFin.val = g a := by
    intro a hak
    have h := endpointCurrent_row_negative_positive d Hminus Hplus hk hkj hjn
      (scalarSignValue (planarDet (q k - q j) v)) hother hchange hleft' hright' a hak
    simpa [Hminus, Hplus, jFin, g, Nat.sub_add_cancel (show 1 ≤ j by omega)] using h
  have hgzero : ∀ a, k ≤ a → g a = 0 := by
    intro a hak
    have hbelow : ¬ a ≤ k - 1 := by omega
    simp [g, endpointMarked, hbelow]
  have hmat := endpointCurrent_propagate_row_formula d Hminus Hplus n k jFin
    hotherProp g hrow hzero hgzero
  refine ⟨hgenericPlus, hgenericMinus, ?_⟩
  simpa [Hminus, Hplus, g, jFin, Nat.sub_add_cancel (show 1 ≤ j by omega), mul_assoc] using hmat

/-- A transverse event with 0<τ<1 gives the ordinary-source prefix row
propagated through every column of the actual endpoint matrix. -/
theorem exists_endpoint_current_matrix_event_positive_positive
    (q : ℕ → PlanarPoint ℝ) (v : PlanarPoint ℝ) (d : ℕ → ℚ) (n : ℕ)
    {k j : ℕ} (hk : 0 < k) (hkj : k < j) (hjn : j ≤ n) (τ : ℝ)
    (hcollinear : q k = q 0 + τ • (q j - q 0))
    (htransverse : planarDet (q k - q j) v ≠ 0)
    (hisolated : ∀ a b c, a < b → b < c → c ≤ n →
      (a ≠ 0 ∨ b ≠ k ∨ c ≠ j) → polygonHDet q a b c ≠ 0)
    (hτ : 0 < τ) (hτ1 : 0 < 1 - τ) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ ε : ℝ, 0 < ε → ε < ρ →
      ShortEdgeSignStability.CoreHGeneric (moveEndpoint q v ε) n ∧
      ShortEdgeSignStability.CoreHGeneric (moveEndpoint q v (-ε)) n ∧
      ∀ a i : Fin n,
        endpointCurrent d (polygonSignArray (moveEndpoint q v ε)) a.val i.val -
          endpointCurrent d (polygonSignArray (moveEndpoint q v (-ε))) a.val i.val =
          scalarSignValue (planarDet (q k - q j) v) * source a.val k * source k j *
            endpointCurrent d (polygonSignArray (moveEndpoint q v (-ε))) (j - 1) i.val := by
  have hτnz : τ ≠ 0 := ne_of_gt hτ
  have hτ1nz : 1 - τ ≠ 0 := ne_of_gt hτ1
  obtain ⟨ρ, hρ, hdata⟩ := exists_endpoint_event_sign_data
    q v n hk hkj hjn τ hcollinear htransverse hisolated hτnz hτ1nz
  refine ⟨ρ, hρ, ?_⟩
  intro ε hε hερ
  obtain ⟨hgenericPlus, hgenericMinus, hother, hchange, hleft, hright⟩ :=
    hdata ε hε hερ
  let Hminus := polygonSignArray (moveEndpoint q v (-ε))
  let Hplus := polygonSignArray (moveEndpoint q v ε)
  let jFin : Fin n := ⟨j - 1, by omega⟩
  have hotherProp : ∀ x y z, x < y → y < z → z ≤ n →
      (x ≠ 0 ∨ y ≠ k ∨ z ≠ jFin.val + 1) → Hplus x y z = Hminus x y z := by
    intro x y z hxy hyz hzn he
    have he' : x ≠ 0 ∨ y ≠ k ∨ z ≠ j := by
      simpa [jFin, Nat.sub_add_cancel (show 1 ≤ j by omega)] using he
    exact hother x y z hxy hyz hzn he'
  have hzero : ∀ a, k ≤ a →
      endpointCurrent d Hplus a jFin.val - endpointCurrent d Hminus a jFin.val = 0 := by
    intro a hak
    simpa [Hplus, Hminus, jFin, Nat.sub_add_cancel (show 1 ≤ j by omega)] using
      (endpointCurrent_rows_zero_from d Hminus Hplus hk hkj hjn hother a hak)
  have hσL : scalarSignValue τ = 1 := by
    simp [scalarSignValue, ne_of_gt hτ, not_lt_of_gt hτ]
  have hσR : scalarSignValue (1 - τ) = 1 := by
    simp [scalarSignValue, hτ1nz, ne_of_gt hτ1, not_lt_of_gt hτ1]
  have hleft' : ∀ l, 0 < l → l < k → Hminus 0 l k = Hminus 0 l j := by
    intro l h0l hlk
    simpa [Hminus, hσL] using hleft l h0l hlk
  have hright' : ∀ l, k < l → l < j → Hminus k l j = Hminus 0 l j := by
    intro l hkl hlj
    simpa [Hminus, hσR] using hright l hkl hlj
  let g : ℕ → ℚ := fun a =>
    scalarSignValue (planarDet (q k - q j) v) * source a k * source k j
  have hrow : ∀ a, a < k →
      endpointCurrent d Hplus a jFin.val - endpointCurrent d Hminus a jFin.val = g a := by
    intro a hak
    have h := endpointCurrent_row_positive_positive d Hminus Hplus hk hkj hjn
      (scalarSignValue (planarDet (q k - q j) v)) hother hchange hleft' hright' a hak
    simpa [Hminus, Hplus, jFin, g, Nat.sub_add_cancel (show 1 ≤ j by omega)] using h
  have hgzero : ∀ a, k ≤ a → g a = 0 := by
    intro a hak
    have hsource : source a k = 0 := by
      simp [source, show k ≠ a + 1 by omega]
    simp [g, hsource]
  have hmat := endpointCurrent_propagate_row_formula d Hminus Hplus n k jFin
    hotherProp g hrow hzero hgzero
  refine ⟨hgenericPlus, hgenericMinus, ?_⟩
  simpa [Hminus, Hplus, g, jFin, Nat.sub_add_cancel (show 1 ≤ j by omega), mul_assoc] using hmat

/-- A transverse event with τ>1 gives the ordinary-source prefix and marked
suffix row propagated through every column of the actual endpoint matrix. -/
theorem exists_endpoint_current_matrix_event_positive_negative
    (q : ℕ → PlanarPoint ℝ) (v : PlanarPoint ℝ) (d : ℕ → ℚ) (n : ℕ)
    {k j : ℕ} (hk : 0 < k) (hkj : k < j) (hjn : j ≤ n) (τ : ℝ)
    (hcollinear : q k = q 0 + τ • (q j - q 0))
    (htransverse : planarDet (q k - q j) v ≠ 0)
    (hisolated : ∀ a b c, a < b → b < c → c ≤ n →
      (a ≠ 0 ∨ b ≠ k ∨ c ≠ j) → polygonHDet q a b c ≠ 0)
    (hτ : 1 < τ) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ ε : ℝ, 0 < ε → ε < ρ →
      ShortEdgeSignStability.CoreHGeneric (moveEndpoint q v ε) n ∧
      ShortEdgeSignStability.CoreHGeneric (moveEndpoint q v (-ε)) n ∧
      ∀ a i : Fin n,
        endpointCurrent d (polygonSignArray (moveEndpoint q v ε)) a.val i.val -
          endpointCurrent d (polygonSignArray (moveEndpoint q v (-ε))) a.val i.val =
          scalarSignValue (planarDet (q k - q j) v) * source a.val k *
            markedAmplitude (fun _ l _ => d l)
              (polygonSignArray (moveEndpoint q v (-ε))) k j *
            endpointCurrent d (polygonSignArray (moveEndpoint q v (-ε))) (j - 1) i.val := by
  have hτpos : 0 < τ := by linarith
  have hτnz : τ ≠ 0 := ne_of_gt hτpos
  have hτ1 : 1 - τ < 0 := by linarith
  have hτ1nz : 1 - τ ≠ 0 := ne_of_lt hτ1
  obtain ⟨ρ, hρ, hdata⟩ := exists_endpoint_event_sign_data
    q v n hk hkj hjn τ hcollinear htransverse hisolated hτnz hτ1nz
  refine ⟨ρ, hρ, ?_⟩
  intro ε hε hερ
  obtain ⟨hgenericPlus, hgenericMinus, hother, hchange, hleft, hright⟩ :=
    hdata ε hε hερ
  let Hminus := polygonSignArray (moveEndpoint q v (-ε))
  let Hplus := polygonSignArray (moveEndpoint q v ε)
  let jFin : Fin n := ⟨j - 1, by omega⟩
  have hotherProp : ∀ x y z, x < y → y < z → z ≤ n →
      (x ≠ 0 ∨ y ≠ k ∨ z ≠ jFin.val + 1) → Hplus x y z = Hminus x y z := by
    intro x y z hxy hyz hzn he
    have he' : x ≠ 0 ∨ y ≠ k ∨ z ≠ j := by
      simpa [jFin, Nat.sub_add_cancel (show 1 ≤ j by omega)] using he
    exact hother x y z hxy hyz hzn he'
  have hzero : ∀ a, k ≤ a →
      endpointCurrent d Hplus a jFin.val - endpointCurrent d Hminus a jFin.val = 0 := by
    intro a hak
    simpa [Hplus, Hminus, jFin, Nat.sub_add_cancel (show 1 ≤ j by omega)] using
      (endpointCurrent_rows_zero_from d Hminus Hplus hk hkj hjn hother a hak)
  have hσL : scalarSignValue τ = 1 := by
    simp [scalarSignValue, ne_of_gt hτpos, not_lt_of_gt hτpos]
  have hσR : scalarSignValue (1 - τ) = -1 := by
    simp [scalarSignValue, hτ1nz, hτ1]
  have hleft' : ∀ l, 0 < l → l < k → Hminus 0 l k = Hminus 0 l j := by
    intro l h0l hlk
    simpa [Hminus, hσL] using hleft l h0l hlk
  have hright' : ∀ l, k < l → l < j → Hminus k l j = -Hminus 0 l j := by
    intro l hkl hlj
    simpa [Hminus, hσR] using hright l hkl hlj
  let g : ℕ → ℚ := fun a =>
    scalarSignValue (planarDet (q k - q j) v) * source a k *
      markedAmplitude (fun _ l _ => d l) Hminus k j
  have hrow : ∀ a, a < k →
      endpointCurrent d Hplus a jFin.val - endpointCurrent d Hminus a jFin.val = g a := by
    intro a hak
    have h := endpointCurrent_row_positive_negative d Hminus Hplus hk hkj hjn
      (scalarSignValue (planarDet (q k - q j) v)) hother hchange hleft' hright' a hak
    simpa [Hminus, Hplus, jFin, g, Nat.sub_add_cancel (show 1 ≤ j by omega)] using h
  have hgzero : ∀ a, k ≤ a → g a = 0 := by
    intro a hak
    have hsource : source a k = 0 := by
      simp [source, show k ≠ a + 1 by omega]
    simp [g, hsource]
  have hmat := endpointCurrent_propagate_row_formula d Hminus Hplus n k jFin
    hotherProp g hrow hzero hgzero
  refine ⟨hgenericPlus, hgenericMinus, ?_⟩
  simpa [Hminus, Hplus, g, jFin, Nat.sub_add_cancel (show 1 ≤ j by omega), mul_assoc] using hmat






end DirectGLSSW.EndpointCurrent
