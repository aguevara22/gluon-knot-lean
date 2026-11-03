import SourceBoundaryPhysicalOrdinary
import DirectGLSSW.HorizontalShortEdge

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.SourceBoundaryCurrent
open DirectGLSSW
open EndpointEventGeometry

/-- Boundary transport in any proved positive parametrization of the actual
first-side direction, with a uniform rescaled physical interval. -/
theorem exists_ordinary_boundary_positive_direction
    (hRI : GLSSWRootIndependence) (W : ℕ → PlanarPoint ℝ)
    (v : PlanarPoint ℝ) (β : ℝ) (hβ : 0<β)
    (hdir : W 1-W 0=β • v)
    (N k : ℕ) (hKN : k<N) (s : ℝ) (hs0 : 0<s) (hs1 : s<1)
    (hcross : W 0=affinePoint (W k) (W (k+1)) s)
    (htrans : planarDet v (W (k+1)-W k)≠0)
    (hisolated : ∀ a b d, a<b → b<d → d≤N →
      (a≠0 ∨ b≠k ∨ d≠k+1) → polygonHDet W a b d≠0)
    (hQ : CyclicGeneric (fun i : Fin (k+1) => W i.val)) :
    ∃ ρ : ℝ, 0<ρ ∧ ∀ ε : ℝ, 0<ε → ε<ρ →
      ShortEdgeSignStability.CoreHGeneric (moveEndpoint W v ε) N ∧
      ShortEdgeSignStability.CoreHGeneric (moveEndpoint W v (-ε)) N ∧
      ∀ j, k<j → j≤N →
      ordinaryCurrent (fun _ _ _ => -1) (polygonSignArray (moveEndpoint W v ε)) 0 j -
        ordinaryCurrent (fun _ _ _ => -1) (polygonSignArray (moveEndpoint W v (-ε))) 0 j =
      scalarSignValue (planarDet v (W (k+1)-W k)) *
        polygonAmplitude (fun i : Fin (k+1) => W i.val) hQ *
        ordinaryCurrent (fun _ _ _ => -1)
          (polygonSignArray (fun i => if i=0 then W 0 else W (k+i))) 0 (j-k) := by
  have hdet : planarDet (W 1-W 0) (W (k+1)-W k)=
      β*planarDet v (W (k+1)-W k) := by
    rw [hdir]
    simp only [planarDet,Prod.smul_fst,Prod.smul_snd,smul_eq_mul]
    ring
  have htr : planarDet (W 1-W 0) (W (k+1)-W k)≠0 := by
    rw [hdet]
    exact mul_ne_zero (ne_of_gt hβ) htrans
  have hsign : scalarSignValue (planarDet (W 1-W 0) (W (k+1)-W k))=
      scalarSignValue (planarDet v (W (k+1)-W k)) := by
    rw [hdet]
    exact HorizontalShortEdge.scalarSignValue_positive_mul _ _ hβ
  obtain ⟨r,hr,hr1,hjump⟩ := exists_physical_ordinary_boundary_jump hRI W N k hKN s
    hs0 hs1 hcross htr hisolated hQ
  have hmove (x : ℝ) : moveEndpoint W (W 1-W 0) (x/β)=moveEndpoint W v x := by
    funext i
    by_cases hi : i=0
    · simp only [moveEndpoint,if_pos hi,hdir,smul_smul,div_mul_cancel₀ x (ne_of_gt hβ)]
    · simp only [moveEndpoint,if_neg hi]
  refine ⟨β*r,mul_pos hβ hr,?_⟩
  intro ε he her
  have hsmall : ε/β<r := (div_lt_iff₀ hβ).mpr (by simpa only [mul_comm] using her)
  obtain ⟨hp,hm,hvalue⟩ := hjump (ε/β) (div_pos he hβ) hsmall
  rw [← neg_div,hmove ε,hmove (-ε),hsign] at hvalue
  rw [hmove ε] at hp
  rw [← neg_div,hmove (-ε)] at hm
  exact ⟨hp,hm,hvalue⟩


end DirectGLSSW.SourceBoundaryCurrent
