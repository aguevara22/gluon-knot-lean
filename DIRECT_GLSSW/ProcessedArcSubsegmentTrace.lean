import ProcessedArcSubsegmentStep
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.HOMFLY
open PermutationOrbits LowestRowContract SmoothingCornerGeometry
attribute [local instance] Classical.propDecidable

/-- Affine composition retains the strict orientation and the closed interval bounds. -/
theorem affine_subsegment_comp (P Q : PlanarPoint ℝ) (u v r s : ℝ)
    (hu : 0 ≤ u) (huv : u < v) (hv : v ≤ 1)
    (hr : 0 ≤ r) (hrs : r < s) (hs : s ≤ 1) :
    0 ≤ u+(v-u)*r ∧ u+(v-u)*r < u+(v-u)*s ∧ u+(v-u)*s ≤ 1 ∧
    affinePoint (affinePoint P Q u) (affinePoint P Q v) r = affinePoint P Q (u+(v-u)*r) ∧
    affinePoint (affinePoint P Q u) (affinePoint P Q v) s = affinePoint P Q (u+(v-u)*s) := by
  have hdiff : 0 < v-u := sub_pos.mpr huv
  refine ⟨add_nonneg hu (mul_nonneg hdiff.le hr),?_,?_,?_,?_⟩
  · exact add_lt_add_left (mul_lt_mul_of_pos_left hrs hdiff) u
  · have hb := mul_le_mul_of_nonneg_left hs hdiff.le
    nlinarith
  · ext <;> simp [affinePoint] <;> ring
  · ext <;> simp [affinePoint] <;> ring

/-- A surviving actual arc has endpoints on one positively oriented subsegment
of its original ancestor after any finite literal parent history. -/
theorem MarkedParentTrace.arcOrigin_subsegment {s t : MarkedParentState}
    (h : MarkedParentTrace s t) :
    ∀ (e : Fin t.1.nArc) (a : Fin s.1.nArc), h.arcOrigin e = some a →
    ∃ u v : ℝ, 0 ≤ u ∧ u < v ∧ v ≤ 1 ∧
      t.1.vertexPoint (t.1.arcSource e) =
        affinePoint (s.1.vertexPoint (s.1.arcSource a)) (s.1.vertexPoint (s.1.arcTarget a)) u ∧
      t.1.vertexPoint (t.1.arcTarget e) =
        affinePoint (s.1.vertexPoint (s.1.arcSource a)) (s.1.vertexPoint (s.1.arcTarget a)) v := by
  induction h with
  | nil s =>
    intro e a ha
    have hea : e=a := Option.some.inj ha
    subst a
    refine ⟨0,1,le_rfl,zero_lt_one,le_rfl,?_,?_⟩ <;> simp [affinePoint]
  | @cons state t w step tail ih =>
    intro e a ha
    cases htail : tail.arcOrigin e with
    | none => simp [MarkedParentTrace.arcOrigin,htail] at ha
    | some b =>
      have hb : step.arcOrigin b = some a := by
        simpa only [MarkedParentTrace.arcOrigin,htail,Option.some_bind] using ha
      obtain ⟨u,v,hu,huv,hv,hbs,hbt⟩ := step.arcOrigin_subsegment b a hb
      obtain ⟨r,s,hr,hrs,hs,hes,het⟩ := ih e b htail
      obtain ⟨h0,hlt,h1,hcs,hct⟩ := affine_subsegment_comp
        (state.1.vertexPoint (state.1.arcSource a)) (state.1.vertexPoint (state.1.arcTarget a)) u v r s hu huv hv hr hrs hs
      refine ⟨u+(v-u)*r,u+(v-u)*s,h0,hlt,h1,?_,?_⟩
      · rw [hes,hbs,hbt]
        exact hcs
      · rw [het,hbs,hbt]
        exact hct

end DirectGLSSW.HOMFLY
