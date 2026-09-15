import SM.GermNeighborhood

/-! A continuous tuple-valued curve through a Generic point stays in its actual
connected-component chamber on one full smaller interval, including zero. -/

namespace SM

open Set Filter Topology

theorem generic_curve_local_chamber {m n : ℕ} (hn : 3 ≤ n) (g : WallGerm m)
    (F : g.Parameter → LabelledTuple n) (hF : Continuous F)
    (h0 : Generic (F g.zeroParameter)) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ g.radius ∧ ∀ t : g.Parameter, |t.val| < δ →
      ∃ ht : Generic (F t),
        (⟨F t, ht⟩ : GenericTuple n) ∈ labelledChamber ⟨F g.zeroParameter, h0⟩ ∧
        polygonProjection ⟨F t, ht⟩ ∈ chamber (polygonProjection ⟨F g.zeroParameter, h0⟩) := by
  have hnear : ∀ᶠ t in 𝓝 g.zeroParameter, Generic (F t) :=
    hF.continuousAt.eventually (generic_persists hn h0)
  obtain ⟨δ, hδ, hδε, hgen⟩ := (g.eventually_center_iff_radius _).mp hnear
  let embed : Ioo (-δ) δ → g.Parameter := fun t =>
    ⟨t.val, by constructor <;> linarith [t.property.1, t.property.2]⟩
  have hembed : Continuous embed := continuous_subtype_val.subtype_mk _
  let H : Ioo (-δ) δ → GenericTuple n := fun t =>
    ⟨F (embed t), hgen (embed t) (abs_lt.mpr t.property)⟩
  have hH : Continuous H := (hF.comp hembed).subtype_mk _
  let zero : Ioo (-δ) δ := ⟨0, by constructor <;> linarith⟩
  have hzero : H zero = (⟨F g.zeroParameter, h0⟩ : GenericTuple n) := by
    apply Subtype.ext
    rfl
  letI : ConnectedSpace (Ioo (-δ) δ) :=
    isConnected_iff_connectedSpace.mp (isConnected_Ioo (by linarith : -δ < δ))
  have hrange := isConnected_range hH
  have hproj := isConnected_range (continuous_polygonProjection.comp hH)
  refine ⟨δ, hδ, hδε, ?_⟩
  intro t ht
  let t' : Ioo (-δ) δ := ⟨t.val, abs_lt.mp ht⟩
  have he : embed t' = t := Subtype.ext rfl
  have hm : H t' ∈ labelledChamber (H zero) :=
    hrange.subset_connectedComponent (mem_range_self zero) (mem_range_self t')
  have hp : polygonProjection (H t') ∈ chamber (polygonProjection (H zero)) :=
    hproj.subset_connectedComponent (mem_range_self zero) (mem_range_self t')
  refine ⟨hgen t ht, ?_, ?_⟩
  · simpa only [hzero, H, he] using hm
  · simpa only [hzero, H, he] using hp

end SM
