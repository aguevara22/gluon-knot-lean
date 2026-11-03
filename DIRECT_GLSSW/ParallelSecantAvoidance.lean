import FiniteCursorWallGluing
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.CursorWallTransport

/-- A finite family of nonzero affine polynomials is simultaneously nonzero
at arbitrarily small positive parameters.  No density conclusion is assumed. -/
theorem exists_small_affine_avoidance {ι : Type*} [Fintype ι]
    (A B : ι → ℝ) (hproper : ∀ i, A i≠0 ∨ B i≠0)
    (ε : ℝ) (hε : 0<ε) :
    ∃ η : ℝ, 0<η ∧ η<ε ∧ ∀ i, A i*η+B i≠0 := by
  classical
  let S : Finset ℝ := Finset.univ.image (fun i => -B i/A i)
  obtain ⟨δ,hδ,hd⟩ := finite_punctured_radius S 0
  let η := min δ ε / 2
  have hη : 0<η := half_pos (lt_min hδ hε)
  have hηm : η<min δ ε := half_lt_self (lt_min hδ hε)
  have hηδ : η<δ := lt_of_lt_of_le hηm (min_le_left _ _)
  refine ⟨η,hη,lt_of_lt_of_le hηm (min_le_right _ _),?_⟩
  intro i hz
  by_cases hA : A i=0
  · exact (hproper i).resolve_left (not_ne_iff.mpr hA) (by simpa only [hA,zero_mul,zero_add] using hz)
  · have hroot : η= -B i/A i := (eq_div_iff hA).mpr (by nlinarith [hz])
    have hh : η∉S := by simpa only [zero_add] using (hd η hη hηδ).2
    apply hh
    exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,hroot.symm⟩

/-- Distinct fixed secants cannot have identically coincident intersection
parameters for a transversely translated line.  The off-line endpoint is the
geometric fact supplied by fixed-tail triple genericity. -/
theorem secant_collision_affine_proper
    (p v w A B C D : PlanarPoint ℝ)
    (hbasis : planarDet v w≠0)
    (htrans : planarDet (C-D) v≠0)
    (hoff : planarDet (A-B) (C-B)≠0) :
    planarDet (A-B) w*planarDet (C-D) v-
        planarDet (C-D) w*planarDet (A-B) v≠0 ∨
      planarDet (A-B) (p-B)*planarDet (C-D) v-
        planarDet (C-D) (p-D)*planarDet (A-B) v≠0 := by
  by_contra hh
  push_neg at hh
  obtain ⟨hη,hp⟩ := hh
  have hid : planarDet (A-B) w*planarDet (C-D) v-
      planarDet (C-D) w*planarDet (A-B) v =
      -(planarDet (A-B) (C-D)*planarDet v w) := by
    simp only [planarDet,Prod.fst_sub,Prod.snd_sub]
    ring
  have huv : planarDet (A-B) (C-D)=0 := by
    have hm : planarDet (A-B) (C-D)*planarDet v w=0 := by rw [hη] at hid; linarith
    exact (mul_eq_zero.mp hm).resolve_right hbasis
  have hc : planarDet (A-B) (C-B)*planarDet (C-D) v =
      (planarDet (A-B) (p-B)*planarDet (C-D) v-
        planarDet (C-D) (p-D)*planarDet (A-B) v)+
        planarDet (A-B) (C-D)*planarDet (C-p) v := by
    simp only [planarDet,Prod.fst_sub,Prod.snd_sub]
    ring
  rw [hp,huv,zero_mul,add_zero] at hc
  exact hoff ((mul_eq_zero.mp hc).resolve_right htrans)

end DirectGLSSW.CursorWallTransport
