import ActualSpatialEmbedding
import Mathlib.Topology.Order.IntermediateValue

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.DescendingSpatial
open HOMFLY HOMFLY.PrincipalTurning

theorem splitTraversalTime_surjective_interval (m : ℕ) (hm : 0 < m)
    (s : ℝ) (hs : s ∈ Set.Icc (3/4:ℝ) ((m:ℝ)+1/4)) :
    ∃ t : unitInterval, splitTraversalTime m t.val = s := by
  have ht := splitTraversalTime_endpoints m hm
  have hs' : s ∈ Set.Icc (splitTraversalTime m 0) (splitTraversalTime m 1) := by
    simpa only [ht.1,ht.2] using hs
  obtain ⟨t,ht',he⟩ := intermediate_value_Icc (by norm_num : (0:ℝ) ≤ 1)
    (splitTraversalTime_continuous m).continuousOn hs'
  exact ⟨⟨t,ht'⟩,he⟩

theorem splitMainPlanar_range (D : PLLinkDiagram) (e : Fin D.nArc) :
    Set.range (splitMainPlanar D e) =
      uniformPLCurve D e '' Set.Icc (3/4:ℝ) ((componentArcLength D e:ℝ)+1/4) := by
  ext x
  constructor
  · rintro ⟨t,rfl⟩
    exact ⟨_,splitTraversalTime_bounds _ (componentArcLength_pos D e) t,rfl⟩
  · rintro ⟨s,hs,rfl⟩
    obtain ⟨t,ht⟩ := splitTraversalTime_surjective_interval _ (componentArcLength_pos D e) s hs
    exact ⟨t,by rw [splitMainPlanar_apply,ht]⟩

theorem uniform_first_period_cell (D : PLLinkDiagram) (e : Fin D.nArc)
    (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s < componentArcLength D e) :
    ∃ k : Fin (componentArcLength D e), ∃ u : unitInterval,
      uniformPLCurve D e s = affinePoint
        (D.vertexPoint (D.arcSource ((D.continuation ^ k.val) e)))
        (D.vertexPoint (D.arcTarget ((D.continuation ^ k.val) e))) u.val := by
  have hk0 : 0 ≤ Int.floor s := Int.floor_nonneg.mpr hs0
  have hk1 : Int.floor s < (componentArcLength D e:ℤ) := by
    exact_mod_cast (lt_of_le_of_lt (Int.floor_le s) hs1)
  refine ⟨⟨(Int.floor s).toNat,by omega⟩,
    ⟨Int.fract s,⟨Int.fract_nonneg s,(Int.fract_lt_one s).le⟩⟩,?_⟩
  simp only [uniformPLCurve]
  rw [← Int.toNat_of_nonneg hk0,zpow_natCast]
  simp [max_eq_left hk0]

end DirectGLSSW.DescendingSpatial



