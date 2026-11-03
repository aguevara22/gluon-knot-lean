import OpenCurrentBoundaryPolygon
import DirectGLSSW.AffineSegments

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW
open EndpointEventGeometry

/-- Boundary crossing transport on its explicit isolated auxiliary domain.
The point W0 lies strictly inside the crossed physical side; both endpoint
curves move along the first side toward W1. The secant parameter required
by the matrix theorem is derived from that actual interior crossing. -/
theorem exists_genuine_boundary_polygon_jump
    (hRI : GLSSWRootIndependence) (W : ℕ → PlanarPoint ℝ)
    (N k : ℕ) (hKN : k<N) (s : ℝ) (hs0 : 0<s) (hs1 : s<1)
    (hcross : W 0=affinePoint (W k) (W (k+1)) s)
    (htrans : planarDet (W 1-W 0) (W (k+1)-W k)≠0)
    (hisolated : ∀ a b d, a<b → b<d → d≤N →
      (a≠0 ∨ b≠k ∨ d≠k+1) → polygonHDet W a b d≠0)
    (hQ : CyclicGeneric (fun i : Fin (k+1) => W i.val)) :
    ∃ ρ : ℝ, 0<ρ ∧ ρ≤1 ∧ ∀ ε : ℝ, 0<ε → ε<ρ →
      ShortEdgeSignStability.CoreHGeneric (moveEndpoint W (W 1-W 0) ε) N ∧
      ShortEdgeSignStability.CoreHGeneric (moveEndpoint W (W 1-W 0) (-ε)) N ∧
      OpenMarkedCurrent.entry (polygonSignArray (moveEndpoint W (W 1-W 0) ε)) 0 N -
        OpenMarkedCurrent.entry (polygonSignArray (moveEndpoint W (W 1-W 0) (-ε))) 0 N =
      scalarSignValue (planarDet (W 1-W 0) (W (k+1)-W k)) *
        polygonAmplitude (fun i : Fin (k+1) => W i.val) hQ *
        OpenMarkedCurrent.entry
          (polygonSignArray (fun i => if i=0 then W 0 else W (k+i))) 0 (N-k) := by
  have hd : 0<1-s := by linarith
  have hτ : -s/(1-s)<0 := div_neg_of_neg_of_pos (neg_neg_of_pos hs0) hd
  have hcol : W k=W 0+(-s/(1-s)) • (W (k+1)-W 0) := by
    have hx := congrArg Prod.fst hcross
    have hy := congrArg Prod.snd hcross
    change (W 0).1=(W k).1+s*((W (k+1)).1-(W k).1) at hx
    change (W 0).2=(W k).2+s*((W (k+1)).2-(W k).2) at hy
    apply Prod.ext
    · change (W k).1=(W 0).1+(-s/(1-s))*((W (k+1)).1-(W 0).1)
      field_simp
      nlinarith [hx]
    · change (W k).2=(W 0).2+(-s/(1-s))*((W (k+1)).2-(W 0).2)
      field_simp
      nlinarith [hy]
  have hdet : planarDet (W k-W (k+1)) (W 1-W 0) =
      planarDet (W 1-W 0) (W (k+1)-W k) := by
    simp only [planarDet,Prod.fst_sub,Prod.snd_sub]
    ring
  obtain ⟨ρ,hρ,hjump⟩ := exists_isolated_boundary_polygon_jump hRI W
    (W 1-W 0) N k hKN (-s/(1-s)) hcol (by rwa [hdet]) hisolated hτ hQ
  refine ⟨min ρ 1,lt_min hρ (by norm_num),min_le_right _ _,?_⟩
  intro ε he her
  exact hjump ε he (lt_of_lt_of_le her (min_le_left _ _))


end DirectGLSSW
