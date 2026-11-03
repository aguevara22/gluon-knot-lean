import DiagonalStaircaseRetention

set_option autoImplicit false
namespace DirectGLSSW.HOMFLY.PrincipalTurning
noncomputable section
attribute [local instance] Classical.propDecidable

/-- The first original vertex after the leftmost cut of a staircase lies
at one of its two internal cuts, or at/after its right endpoint. -/
theorem diagonalStaircase_next_vertex_position {D : PLLinkDiagram} (T : BasedTraversal D)
    (C : diagramComponent D) (a b u v : ℝ)
    (hx : secantAxisAdjacent T C a b) (hm : secantAxisAdjacent T C b u)
    (hy : secantAxisAdjacent T C u v) :
    let p : ℝ := (Int.floor (a+1/2) : ℝ)+1/2
    v≤p ∨ p=b ∨ p=u := by
  dsimp only
  let k : ℤ := Int.floor (a+1/2)
  let p : ℝ := (k : ℝ)+1/2
  change v≤p ∨ p=b ∨ p=u
  by_cases hvp : v≤p
  · exact Or.inl hvp
  have hpv : p<v := lt_of_not_ge hvp
  have hpa : a<p := by
    have hf := Int.lt_floor_add_one (a+1/2)
    dsimp only [p,k]
    linarith
  have ha0 := (secantAxisCuts_bounds T C a hx.1).1
  have hvm := (secantAxisCuts_bounds T C v hy.2.1).2
  have hk0 : 0≤k := Int.floor_nonneg.mpr (by linarith)
  let n : ℕ := k.toNat
  have hncast : (n : ℝ)=(k : ℝ) := by
    have hc : (n : ℤ)=k := Int.toNat_of_nonneg hk0
    exact_mod_cast hc
  have hnm : n<componentArcLength D (T.baseArc C).val := by
    have hnr : (n : ℝ)<(componentArcLength D (T.baseArc C).val : ℝ) := by
      rw [hncast];dsimp only [p] at hpv;linarith
    exact_mod_cast hnr
  have hpcut : p ∈ secantAxisCuts T C := by
    simpa only [hncast] using secantAxisCuts_original_knot T C n hnm
  rcases lt_trichotomy p b with hpb | hpb | hbp
  · exact False.elim (hx.2.2.2 p hpcut hpa hpb)
  · exact Or.inr (Or.inl hpb)
  · rcases lt_trichotomy p u with hpu | hpu | hup
    · exact False.elim (hm.2.2.2 p hpcut hbp hpu)
    · exact Or.inr (Or.inr hpu)
    · exact False.elim (hy.2.2.2 p hpcut hup hpv)

end
end DirectGLSSW.HOMFLY.PrincipalTurning

