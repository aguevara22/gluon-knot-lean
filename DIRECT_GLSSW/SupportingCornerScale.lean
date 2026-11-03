import Mathlib.Tactic.FieldSimp
import DirectGLSSW.TruncationCommonScale
import DirectGLSSW.TruncationCoordinates
import DirectGLSSW.OrderedEventSuccessor
import DirectGLSSW.RealPolygons
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.TruncationDirection
open TruncationCommonScale
attribute [local instance] Classical.propDecidable

/-- A finite injective point configuration has an actual strictly supporting vertex. -/
theorem exists_strict_support_vertex {n : ℕ} (hn : 0 < n)
    (q : Fin n → PlanarPoint ℝ) (hq : Function.Injective q) :
    ∃ a : Fin n, ∃ v : PlanarPoint ℝ, ∀ x : Fin n, x ≠ a → 0 < planarDet v (q x-q a) := by
  letI : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  obtain ⟨scale,hs,ha⟩ := exists_positive_scale_avoiding_finite_vectors
    (1,0) (0,1) (by norm_num [planarDet]) (fun z : Fin n × Fin n => q z.1-q z.2)
  let v : PlanarPoint ℝ := scale • (0,1) - (1,0)
  let f : Fin n → ℝ := fun x => planarDet v (q x)
  obtain ⟨a,_,hmin⟩ := Finset.univ.exists_min_image f Finset.univ_nonempty
  refine ⟨a,v,?_⟩
  intro x hxa
  have hne : q x-q a ≠ 0 := sub_ne_zero.mpr (fun h => hxa (hq h))
  have hd : planarDet v (q x-q a) ≠ 0 := ha (x,a) hne
  have hm : f a ≤ f x := hmin x (Finset.mem_univ x)
  have he : planarDet v (q x-q a) = f x-f a := by simp [f,planarDet];ring
  rw [he] at hd ⊢
  exact lt_of_le_of_ne (sub_nonneg.mpr hm) hd.symm

/-- At a left corner, a strict supporting direction selects a positive
truncation scale; the canonical short-side direction is itself strictly supporting. -/
theorem positive_scale_of_strict_support (A P N v : PlanarPoint ℝ)
    (hturn : 0 < planarDet (A-P) (N-A))
    (hp : 0 < planarDet v (P-A)) (hn : 0 < planarDet v (N-A)) :
    ∃ scale : ℝ, 0 < scale ∧ ∀ X : PlanarPoint ℝ,
      0 < planarDet v (X-A) →
      0 < planarDet (scale • (N-A) - (P-A)) (X-A) := by
  let u := A-P
  let d := N-A
  let scale := planarDet u v / planarDet v d
  have hu : 0 < planarDet u v := by
    have he : planarDet u v = planarDet v (P-A) := by simp [u,planarDet];ring
    rw [he];exact hp
  refine ⟨scale,div_pos hu hn,?_⟩
  intro X hX
  have hd : planarDet v d ≠ 0 := ne_of_gt hn
  have he : planarDet v d * planarDet (scale • (N-A)-(P-A)) (X-A) =
      planarDet u d * planarDet v (X-A) := by
    have hd' : v.1*(N.2-A.2)-v.2*(N.1-A.1) ≠ 0 := hd
    simp [scale,u,d,planarDet,Prod.smul_fst,Prod.smul_snd,smul_eq_mul]
    field_simp [hd']
    <;> ring
  have hpos : 0 < planarDet u d * planarDet v (X-A) := mul_pos hturn hX
  rw [←he] at hpos
  exact (mul_pos_iff_of_pos_left hn).mp hpos

/-- The actual original uniformly left polygon supplies the corner, predecessor
and strictly supporting positive truncation scale; no hull/exposure witness is assumed. -/
theorem exists_supporting_left_corner_scale {n : ℕ}
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (hleft : ∀ i, 0 < planarDet (cyclicTangent q i) (cyclicTangent q (cyclicSuccessor i))) :
    ∃ a p : Fin n, cyclicSuccessor p = a ∧ ∃ scale : ℝ, 0 < scale ∧
      (∀ x : Fin n, x ≠ a →
        0 < planarDet (scale • (q (cyclicSuccessor a)-q a)-(q p-q a)) (q x-q a)) := by
  obtain ⟨a,v,hv⟩ := exists_strict_support_vertex (by have := hq.size_ge_three;omega)
    q (cyclicNoncollinear_injective hq.size_ge_three q hq.g1)
  let p := (cyclicSuccessorPerm n).symm a
  have hp : cyclicSuccessor p = a := (cyclicSuccessorPerm n).apply_symm_apply a
  have hpa : p ≠ a := by
    intro he
    exact cyclicSuccessor_ne_self (by have := hq.size_ge_three;omega) p (hp.trans he.symm)
  have hna : cyclicSuccessor a ≠ a := cyclicSuccessor_ne_self (by have := hq.size_ge_three;omega) a
  have ht : 0 < planarDet (q a-q p) (q (cyclicSuccessor a)-q a) := by
    simpa only [cyclicTangent,hp] using hleft p
  obtain ⟨scale,hs,hscale⟩ := positive_scale_of_strict_support (q a) (q p) (q (cyclicSuccessor a)) v
    ht (hv p hpa) (hv _ hna)
  exact ⟨a,p,hp,scale,hs,fun x hx => hscale (q x) (hv x hx)⟩
end DirectGLSSW.TruncationDirection
