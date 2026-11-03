import DirectGLSSW.NonincidentEdgeClearance
import DirectGLSSW.PolygonCrossings

namespace DirectGLSSW.ShortEdgeGenericity

theorem exists_crossing_free_vertex_ball {n : ℕ} (hn : 3 ≤ n)
    (q : Fin n → PlanarPoint ℝ) (hq : cyclicNoncollinear q) (a : Fin n) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x : PlanarPoint ℝ, dist x (q a) < δ →
      ¬ IsCrossingPoint q x
  := by
  obtain ⟨δ, hδ, hclear⟩ := exists_nonincident_edge_clearance hn q hq a
  refine ⟨δ, hδ, ?_⟩
  intro x hx hcross
  rcases hcross with ⟨e, f, hef, he, hf⟩
  obtain ⟨te, hte0, hte1, hxe⟩ := he
  obtain ⟨tf, htf0, htf1, hxf⟩ := hf
  have heInterior : edgeInterior q e x := ⟨te, hte0, hte1, hxe⟩
  have hfInterior : edgeInterior q f x := ⟨tf, htf0, htf1, hxf⟩
  have hclosedE : edgeClosed q e x :=
    ⟨te, le_of_lt hte0, le_of_lt hte1, hxe⟩
  have hclosedF : edgeClosed q f x :=
    ⟨tf, le_of_lt htf0, le_of_lt htf1, hxf⟩
  have hincidentE : e = a ∨ cyclicSuccessor e = a := by
    by_cases hea : e = a
    · exact Or.inl hea
    · by_cases hsea : cyclicSuccessor e = a
      · exact Or.inr hsea
      · exact False.elim (hclear e hea hsea x hx hclosedE)
  have hincidentF : f = a ∨ cyclicSuccessor f = a := by
    by_cases hfa : f = a
    · exact Or.inl hfa
    · by_cases hsfa : cyclicSuccessor f = a
      · exact Or.inr hsfa
      · exact False.elim (hclear f hfa hsfa x hx hclosedF)
  rcases hincidentE with hea | hsea
  · rcases hincidentF with hfa | hsfa
    · exact hef (hea.trans hfa.symm)
    · have hdisjoint := DirectGLSSW.cyclic_adjacent_interiors_disjoint hn q hq f x hfInterior
      exact hdisjoint (hsfa.symm ▸ (hea ▸ heInterior))
  · rcases hincidentF with hfa | hsfa
    · have hdisjoint := DirectGLSSW.cyclic_adjacent_interiors_disjoint hn q hq e x heInterior
      exact hdisjoint (hsea.symm ▸ (hfa ▸ hfInterior))
    · have heq : e = f :=
        (cyclicSuccessor_bijective (n := n)).injective (hsea.trans hsfa.symm)
      exact hef heq

end DirectGLSSW.ShortEdgeGenericity
