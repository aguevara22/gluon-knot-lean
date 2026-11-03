import ActualSplitBasePath

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.DescendingSpatial
open HOMFLY HOMFLY.PrincipalTurning PermutationOrbits

theorem visitPosition_of_base_iterate {D : PLLinkDiagram} (T : BasedTraversal D)
    (C : diagramComponent D) (k : ℕ)
    (hk : k < componentArcLength D (T.baseArc C).val) :
    visitPosition T ((D.continuation ^ k) (T.baseArc C).val) = k := by
  have hC : componentOf D.continuation ((D.continuation ^ k) (T.baseArc C).val) = C :=
    (componentOf_pow_apply _ _ _).trans (T.baseArc C).property
  have hb : (T.baseArc (componentOf D.continuation
      ((D.continuation ^ k) (T.baseArc C).val))).val = (T.baseArc C).val :=
    congrArg (fun X => (T.baseArc X).val) hC
  have hp : visitPosition T ((D.continuation ^ k) (T.baseArc C).val) <
      componentArcLength D (T.baseArc (componentOf D.continuation
        ((D.continuation ^ k) (T.baseArc C).val))).val := by
    unfold visitPosition
    exact Fin.isLt _
  rw [hb] at hp
  have hr := visitPosition_reconstruct T ((D.continuation ^ k) (T.baseArc C).val)
  rw [hb] at hr
  have he : orbitEnumeration D.continuation (T.baseArc C).val
      ⟨visitPosition T ((D.continuation ^ k) (T.baseArc C).val),hp⟩ =
      orbitEnumeration D.continuation (T.baseArc C).val ⟨k,hk⟩ := by
    apply Subtype.ext
    simpa only [orbitEnumeration_apply_val] using hr
  exact congrArg Fin.val ((orbitEnumeration D.continuation (T.baseArc C).val).injective he)

theorem splitTraversalTime_visit (m : ℕ) (hm : 0 < m) (k : ℕ) (hk : k < m) :
    splitTraversalTime m (((k:ℝ)+1)/((m:ℝ)+1)) = (k:ℝ)+1 := by
  have hn : ((m:ℝ)+1) ≠ 0 := by positivity
  have hc : ((m:ℝ)+1)*(((k:ℝ)+1)/((m:ℝ)+1)) = (k:ℝ)+1 := by field_simp
  rw [splitTraversalTime_middle m _ (by rw [hc]; have h := Nat.cast_nonneg (α := ℝ) k; linarith)
    (by rw [hc]; exact_mod_cast hk), hc]

theorem splitMainPlanar_visit (D : PLLinkDiagram) (e : Fin D.nArc)
    (k : ℕ) (hk : k < componentArcLength D e)
    (t : unitInterval) (ht : t.val = ((k:ℝ)+1)/((componentArcLength D e:ℝ)+1)) :
    splitMainPlanar D e t = D.vertexPoint (D.arcTarget ((D.continuation ^ k) e)) := by
  rw [splitMainPlanar_apply, ht,
    splitTraversalTime_visit _ (componentArcLength_pos D e) k hk]
  have hc := uniformPLCurve_arc_cell D e (k:ℤ) 1 (by norm_num)
  simpa only [Int.cast_natCast, zpow_natCast, affinePoint_one] using hc

end DirectGLSSW.DescendingSpatial



