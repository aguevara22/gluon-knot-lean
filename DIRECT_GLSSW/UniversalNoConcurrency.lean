import UniversalCarrierTransverse
import IsolatedCursorInterval
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.UniversalCarrierDomain
open AuxiliaryCarrierChart

/-- The universal proper-triple locus rules out three concurrent distinct
supplied carriers, including intersections outside every physical segment. -/
theorem no_three_concurrent {α : Type*} [DecidableEq α]
    (L : α → CarrierLine) (hL : UniversalLocus L) (hT : PairTransverse L)
    (a b c : α) (hab : a≠b) (hac : a≠c) (hbc : b≠c)
    (x : PlanarPoint ℝ) (ha : lineValue (L a) x=0)
    (hb : lineValue (L b) x=0) : lineValue (L c) x≠0 := by
  intro hc
  have hp : ProperPairs (a,b) (b,c) (a,c) := by
    simp only [ProperPairs]
    refine ⟨hab,hbc,hac,?_,?_,?_,?_⟩
    · intro he
      have hh : a∈({b,c} : Finset α) := by rw [←he];simp
      simp only [Finset.mem_insert,Finset.mem_singleton] at hh
      exact hh.elim hab hac
    · intro he
      have hh : b∈({a,c} : Finset α) := by rw [←he];simp
      simp only [Finset.mem_insert,Finset.mem_singleton] at hh
      exact hh.elim (Ne.symm hab) hbc
    · intro he
      have hh : b∈({a,c} : Finset α) := by rw [←he];simp
      simp only [Finset.mem_insert,Finset.mem_singleton] at hh
      exact hh.elim (Ne.symm hab) hbc
    · simp only [Finset.mem_insert,Finset.mem_singleton]
      rintro ⟨y,hy,hy',hy''⟩
      rcases hy with rfl|rfl
      · exact hy'.elim hab hac
      · exact hy''.elim (Ne.symm hab) hbc
  apply hL (a,b) (b,c) (a,c) hp
  apply (carrierTripleNumerator_zero_iff _ _ _ _ _ _ (hT a b hab) (hT b c hbc) (hT a c hac)).2
  rw [←lineIntersection_unique _ _ x (hT a b hab) ha hb,
    ←lineIntersection_unique _ _ x (hT b c hbc) hb hc,
    ←lineIntersection_unique _ _ x (hT a c hac) ha hc]
  simp [planarDet]

/-- Two distinct points on the first physical line cannot have an identically
vanishing moving-head determinant against a secant with an off-line endpoint. -/
theorem moving_head_affine_proper (p v A B : PlanarPoint ℝ)
    (hAB : A≠B) (hoff : planarDet v (B-p)≠0) :
    planarDet (A-B) v≠0 ∨ planarDet (A-B) (p-B)≠0 := by
  by_contra hh
  push_neg at hh
  rcases hh with ⟨hv,hp⟩
  have hp' : planarDet (p-A) (B-A)=0 := by
    convert hp using 1 <;> simp only [planarDet,Prod.fst_sub,Prod.snd_sub] <;> ring
  obtain ⟨s,hs⟩ := CursorWallTransport.collinear_parameter B p A hAB hp'
  have he : planarDet v (B-p)=s*planarDet (A-B) v := by
    rw [hs]
    dsimp [planarDet]
    ring
  exact hoff (by rw [he,hv,mul_zero])
end DirectGLSSW.UniversalCarrierDomain
