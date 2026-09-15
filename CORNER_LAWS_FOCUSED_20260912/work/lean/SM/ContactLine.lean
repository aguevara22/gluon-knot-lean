import SM.StrictBetween
import SM.ContinuousGeometry

/-! Exact finite-line geometry at a vertex contact. These real identities
retain both segment parameters, rather than using only line straddling. -/

namespace SM

noncomputable def contactHeight (a b x : Plane) : ℝ := det (b - a) (x - a)

noncomputable def contactRatio (a b m u : Plane) : ℝ :=
  -contactHeight a b m / (contactHeight a b u - contactHeight a b m)

noncomputable def contactFoot (a b m u : Plane) : Plane :=
  m + contactRatio a b m u • (u - m)

theorem contact_height_affine (a b m u : Plane) (r : ℝ) :
    contactHeight a b (m + r • (u - m)) =
      contactHeight a b m + r * (contactHeight a b u - contactHeight a b m) := by
  dsimp [contactHeight, det]
  ring

theorem contact_direction_det (a b m u : Plane) :
    det (b - a) (u - m) = contactHeight a b u - contactHeight a b m := by
  dsimp [contactHeight, det]
  ring

theorem contactFoot_height_zero {a b m u : Plane}
    (hd : contactHeight a b u - contactHeight a b m ≠ 0) :
    contactHeight a b (contactFoot a b m u) = 0 := by
  rw [contactFoot, contact_height_affine, contactRatio, div_mul_cancel₀ _ hd]
  exact add_neg_cancel _

theorem contactRatio_interior_iff {a b m u : Plane}
    (hd : contactHeight a b u - contactHeight a b m ≠ 0) :
    (0 < contactRatio a b m u ∧ contactRatio a b m u < 1) ↔
      contactHeight a b m * contactHeight a b u < 0 := by
  rw [contactRatio, ratio_between_iff hd]
  have he : -contactHeight a b m *
      (-contactHeight a b m - (contactHeight a b u - contactHeight a b m)) =
      contactHeight a b m * contactHeight a b u := by ring
  rw [he]

theorem strictBetween_contactHeight_zero {a m b : Plane} (hb : StrictBetween a m b) :
    contactHeight a b m = 0 := by
  obtain ⟨_, t, _, _, rfl⟩ := hb
  dsimp [contactHeight, det]
  ring

theorem contact_base_separation {a b m u : Plane} (hb : StrictBetween a m b)
    (hu : contactHeight a b u ≠ 0) :
    det (u - m) (a - m) * det (u - m) (b - m) < 0 := by
  obtain ⟨_, t, ht0, ht1, rfl⟩ := hb
  have hleft : det (u - (a + t • (b - a))) (a - (a + t • (b - a))) =
      t * contactHeight a b u := by dsimp [contactHeight, det]; ring
  have hright : det (u - (a + t • (b - a))) (b - (a + t • (b - a))) =
      (t - 1) * contactHeight a b u := by dsimp [contactHeight, det]; ring
  rw [hleft, hright]
  have hn := mul_neg_of_pos_of_neg ht0 (sub_neg.mpr ht1)
  have hp := mul_self_pos.mpr hu
  have he : (t * contactHeight a b u) * ((t - 1) * contactHeight a b u) =
      (t * (t - 1)) * (contactHeight a b u * contactHeight a b u) := by ring
  rw [he]
  exact mul_neg_of_neg_of_pos hn hp

theorem reverse_line_side_product (a b m u : Plane) :
    det (m - u) (a - u) * det (m - u) (b - u) =
      det (u - m) (a - m) * det (u - m) (b - m) := by
  dsimp [det]
  ring

theorem contact_cramer_parameters {a b m u : Plane} (hb : StrictBetween a m b)
    (hu : contactHeight a b u ≠ 0) :
    (0 < cramerFirst a m (b - a) (u - m) ∧ cramerFirst a m (b - a) (u - m) < 1) ∧
    cramerSecond a m (b - a) (u - m) = 0 ∧
    a + cramerFirst a m (b - a) (u - m) • (b - a) = m := by
  have hm := strictBetween_contactHeight_zero hb
  have hd : det (b - a) (u - m) ≠ 0 := by
    rw [contact_direction_det, hm, sub_zero]
    exact hu
  obtain ⟨_, t, ht0, ht1, ht⟩ := hb
  have he : a + t • (b - a) = m + (0 : ℝ) • (u - m) := by simpa using ht.symm
  have hfirst : cramerFirst a m (b - a) (u - m) = t :=
    (div_eq_iff hd).mpr (intersection_parameter_identity he)
  have hsecond : cramerSecond a m (b - a) (u - m) = 0 :=
    (div_eq_iff hd).mpr (intersection_second_parameter_identity he)
  exact ⟨by simpa only [hfirst] using And.intro ht0 ht1, hsecond, by rw [hfirst]; exact ht.symm⟩

end SM
