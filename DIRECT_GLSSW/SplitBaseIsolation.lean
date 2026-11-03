import ActualSplitBasePath

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.DescendingSpatial
open HOMFLY HOMFLY.PrincipalTurning PermutationOrbits

theorem continuation_no_early_return (D : PLLinkDiagram) (e : Fin D.nArc)
    (k : ℕ) (hk : k < componentArcLength D e)
    (he : (D.continuation ^ k) e = e) : k = 0 := by
  let i : Fin (componentArcLength D e) := ⟨k,hk⟩
  let z : Fin (componentArcLength D e) := ⟨0,componentArcLength_pos D e⟩
  have h : orbitEnumeration D.continuation e i = orbitEnumeration D.continuation e z := by
    apply Subtype.ext
    simpa [i,z] using he
  exact congrArg Fin.val ((orbitEnumeration D.continuation e).injective h)

/-- An interior point of the actual base arc is visited only on that arc,
with its literal affine parameter, in the first continuation period. -/
theorem uniform_base_interior_preimage (D : PLLinkDiagram) (e : Fin D.nArc)
    (s r : ℝ) (hs : 0 ≤ s) (hs' : s < componentArcLength D e)
    (hr : 0 < r) (hr' : r < 1)
    (heq : uniformPLCurve D e s =
      affinePoint (D.vertexPoint (D.arcSource e)) (D.vertexPoint (D.arcTarget e)) r) :
    s = r := by
  have hk0 : 0 ≤ Int.floor s := Int.floor_nonneg.mpr hs
  have hklt : Int.floor s < (componentArcLength D e : ℤ) := by
    exact_mod_cast (lt_of_le_of_lt (Int.floor_le s) hs')
  have hkNat : (Int.floor s).toNat < componentArcLength D e := by omega
  have hf0 := Int.fract_nonneg s
  have hf1 := Int.fract_lt_one s
  by_cases hf : Int.fract s = 0
  · have hv : D.vertexPoint (D.arcSource ((D.continuation ^ Int.floor s) e)) =
        affinePoint (D.vertexPoint (D.arcSource e)) (D.vertexPoint (D.arcTarget e)) r := by
      simpa only [uniformPLCurve, hf, affinePoint_zero] using heq
    exact False.elim (D.vertices_avoid_arc_interiors _ e r hr hr' hv)
  · have hfp : 0 < Int.fract s := lt_of_le_of_ne hf0 (Ne.symm hf)
    have ha : (D.continuation ^ Int.floor s) e = e := by
      by_contra hne
      exact D.arc_interiors_disjoint _ e hne (Int.fract s) r hfp hf1 hr hr' heq
    have haNat : (D.continuation ^ (Int.floor s).toNat) e = e := by
      rw [← Int.toNat_of_nonneg hk0, zpow_natCast] at ha
      exact ha
    have hz : (Int.floor s).toNat = 0 := continuation_no_early_return D e _ hkNat haNat
    have hkz : Int.floor s = 0 := by omega
    have hfr : Int.fract s = s := by simp [Int.fract, hkz]
    have he : affinePoint (D.vertexPoint (D.arcSource e)) (D.vertexPoint (D.arcTarget e)) s =
        affinePoint (D.vertexPoint (D.arcSource e)) (D.vertexPoint (D.arcTarget e)) r := by
      simpa [uniformPLCurve, hkz, hfr] using heq
    exact affinePoint_injective _ _
      (fun h => D.arc_endpoints_distinct e (D.vertexPoint_injective h)) he

end DirectGLSSW.DescendingSpatial


