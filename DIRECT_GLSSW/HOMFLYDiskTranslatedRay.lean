import HOMFLYTriangleTranslatedRay
import HOMFLYDiskAttachmentParity

set_option autoImplicit false
namespace DirectGLSSW.HOMFLY
noncomputable section
attribute [local instance] Classical.propDecidable

def TriangleGenericHorizontalAt (T : TrianglePatch) (q : PlanarPoint ℝ) : Prop :=
  T.a.2 ≠ q.2 ∧ T.b.2 ≠ q.2 ∧ T.c.2 ≠ q.2 ∧ q ∉ T.boundary

namespace FiniteDiskCertificate

/-- The explicit finite geometric exclusions for a ray from a query point. -/
def GenericHorizontalAt {K B : Set (PlanarPoint ℝ)}
    (W : FiniteDiskCertificate K B) (q : PlanarPoint ℝ) : Prop :=
  match W with
  | .triangle T => TriangleGenericHorizontalAt T q
  | .attach previous T _ _ => previous.GenericHorizontalAt q ∧ TriangleGenericHorizontalAt T q

/-- Actual membership of a certified region is computed by its actual generic
horizontal boundary crossings, at any query point. -/
theorem translated_ray_parity {K B : Set (PlanarPoint ℝ)}
    (W : FiniteDiskCertificate K B) (q : PlanarPoint ℝ) (hgeneric : W.GenericHorizontalAt q) :
    (B ∩ horizontalRayFrom q).Finite ∧
    (B ∩ horizontalRayFrom q).ncard % 2 = if q ∈ K then 1 else 0 := by
  induction W with
  | triangle T =>
      obtain ⟨ha,hb,hc,hq⟩ := hgeneric
      exact triangle_translated_ray_parity T q ha hb hc hq
  | @attach K B previous T boundary_edge exact_intersection ih =>
      obtain ⟨hprev,ha,hb,hc,hq⟩ := hgeneric
      obtain ⟨hfinite,hparity⟩ := ih hprev
      obtain ⟨hTfinite,hTparity⟩ := triangle_translated_ray_parity T q ha hb hc hq
      have haR : T.a ∉ horizontalRayFrom q := fun h => ha h.1
      have hbR : T.b ∉ horizontalRayFrom q := fun h => hb h.1
      constructor
      · apply (hfinite.union hTfinite).subset
        rintro z ⟨(hz | hz) | hz,hR⟩
        · exact Or.inl ⟨hz.1,hR⟩
        · exact Or.inr ⟨Or.inl (Or.inr hz),hR⟩
        · exact Or.inr ⟨Or.inr hz,hR⟩
      · have hcount := previous.attach_boundary_ncard_parity T boundary_edge
          exact_intersection (horizontalRayFrom q) haR hbR hfinite hTfinite
        rw [Nat.add_mod,hparity,hTparity] at hcount
        have hqedge : q ∉ segment ℝ T.a T.b := fun h => hq (Or.inl (Or.inl h))
        have hresult := hcount.trans
          (previous.attach_region_indicator T exact_intersection q hqedge).symm
        by_cases hu : q ∈ K ∪ T.fill
        · simpa only [if_pos hu] using hresult
        · simpa only [if_neg hu] using hresult

theorem generic_membership_eq_of_boundary {K L B : Set (PlanarPoint ℝ)}
    (W : FiniteDiskCertificate K B) (V : FiniteDiskCertificate L B)
    (q : PlanarPoint ℝ) (hW : W.GenericHorizontalAt q) (hV : V.GenericHorizontalAt q) :
    q ∈ K ↔ q ∈ L := by
  have h := W.translated_ray_parity q hW
  have h' := V.translated_ray_parity q hV
  have he := h.2.symm.trans h'.2
  by_cases hK : q ∈ K <;> by_cases hL : q ∈ L <;>
    simp only [hK,hL,ite_true,ite_false] at he ⊢ <;> tauto

end FiniteDiskCertificate
end
end DirectGLSSW.HOMFLY



