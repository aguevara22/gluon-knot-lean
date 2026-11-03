import SplitCircleCodes

set_option autoImplicit false
namespace DirectGLSSW.HOMFLY.SplitCircleConstructor
open DirectGLSSW
open scoped Classical

private theorem filter_card_equiv {α β : Type*} [Fintype α] [Fintype β]
    (E : α ≃ β) (p : α → Prop) :
    (Finset.univ.filter (fun b : β => p (E.symm b))).card =
      (Finset.univ.filter p).card := by
  classical
  have h : (Finset.univ.filter (fun b : β => p (E.symm b))) =
      (Finset.univ.filter p).map E.toEmbedding := by
    ext b
    simp
  rw [h, Finset.card_map]

/-- Actual finite PL diagram obtained by adjoining the translated triangle.
All crossing labels remain those of D and every new arc is a whole triangle
edge; the x-separation premises are discharged by `exists_right_triangle_clearance`
when the final constructor chooses R. -/
noncomputable def joinedDiagram (D : PLLinkDiagram) (R : ℝ)
    (hleft : ∀ v : Fin D.nVertex, (D.vertexPoint v).1 < R)
    (hright : ∀ v : Fin (rightTriangle R).nVertex,
      R < ((rightTriangle R).vertexPoint v).1) : PLLinkDiagram := by
  classical
  let V := vertexEquiv D R
  let A := arcEquiv D R
  refine {
    nVertex := D.nVertex + (rightTriangle R).nVertex
    nArc := D.nArc + (rightTriangle R).nArc
    nCrossing := D.nCrossing
    vertexPoint := fun v => vertexPointCode D R (V.symm v)
    arcSource := fun e => V (sourceCode D R (A.symm e))
    arcTarget := fun e => V (targetCode D R (A.symm e))
    crossingVertex := fun c => V (.inl (D.crossingVertex c))
    crossingVertex_injective := ?_
    incoming := fun c i => A (.inl (D.incoming c i))
    outgoing := fun c i => A (.inl (D.outgoing c i))
    incoming_target := ?_
    outgoing_source := ?_
    four_ports_distinct := ?_
    crossing_incidence_complete := ?_
    regular_degree_one := ?_
    through := D.through
    continuation := A.symm.trans ((continuationCode D R).trans A)
    continuation_incidence := ?_
    continuation_crossing := ?_
    overBranch := D.overBranch
    vertexPoint_injective := ?_
    arc_endpoints_distinct := ?_
    arc_interiors_disjoint := ?_
    vertices_avoid_arc_interiors := ?_
    through_tangents_positive_collinear := ?_
    crossing_transverse := ?_ }
  · intro c d h
    exact D.crossingVertex_injective
      (Sum.inl.inj (V.injective h))
  · intro c i
    simp only [A.symm_apply_apply]
    change V (targetCode D R (.inl (D.incoming c i))) =
      V (.inl (D.crossingVertex c))
    exact congrArg (fun v => V (.inl v)) (D.incoming_target c i)
  · intro c i
    simp only [A.symm_apply_apply]
    change V (sourceCode D R (.inl (D.outgoing c i))) =
      V (.inl (D.crossingVertex c))
    exact congrArg (fun v => V (.inl v)) (D.outgoing_source c i)
  · intro c
    obtain ⟨h01, ho01, hmix⟩ := D.four_ports_distinct c
    constructor
    · exact fun h => h01 (Sum.inl.inj (A.injective h))
    constructor
    · exact fun h => ho01 (Sum.inl.inj (A.injective h))
    · intro i j h
      exact hmix i j (Sum.inl.inj (A.injective h))
  · intro c e
    rcases hx : A.symm e with a | a
    · have he : e = A (.inl a) := by
        calc e = A (A.symm e) := (A.apply_symm_apply e).symm
             _ = A (.inl a) := congrArg A hx
      subst e
      simpa only [A.apply_symm_apply, A.symm_apply_apply,
        sourceCode, targetCode, Sum.inl.injEq, V.injective.eq_iff,
        A.injective.eq_iff] using D.crossing_incidence_complete c a
    · have he : e = A (.inr a) := by
        calc e = A (A.symm e) := (A.apply_symm_apply e).symm
             _ = A (.inr a) := congrArg A hx
      subst e
      simp [sourceCode, targetCode]
  · intro v hv
    let x := V.symm v
    have hvcode : ∀ c : Fin D.nCrossing,
        Sum.inl (D.crossingVertex c) ≠ x := by
      intro c h
      exact hv c (by simpa only [x, V.apply_symm_apply] using congrArg V h)
    have hdeg := code_regular_degree_one D R x hvcode
    constructor
    · change (Finset.univ.filter (fun e : Fin (D.nArc + (rightTriangle R).nArc) =>
          V (targetCode D R (A.symm e)) = v)).card = 1
      have hcard := filter_card_equiv A
        (fun e : ArcCode D R => targetCode D R e = x)
      have hgoal : (Finset.univ.filter (fun e : Fin (D.nArc + (rightTriangle R).nArc) =>
          targetCode D R (A.symm e) = x)).card = 1 := by
        calc
          _ = (Finset.univ.filter (fun e : ArcCode D R => targetCode D R e = x)).card := by
            convert hcard using 1 <;> congr 1 <;> ext e <;>
              simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          _ = 1 := by
            convert hdeg.1 using 1 <;> congr 1 <;> ext e <;>
              simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have hfilters : (Finset.univ.filter (fun e : Fin (D.nArc + (rightTriangle R).nArc) =>
          V (targetCode D R (A.symm e)) = v)) =
          (Finset.univ.filter (fun e : Fin (D.nArc + (rightTriangle R).nArc) =>
            targetCode D R (A.symm e) = x)) := by
        ext e
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · intro h
          exact V.injective (h.trans (V.apply_symm_apply v).symm)
        · intro h
          simpa only [x, h, V.apply_symm_apply]
      rw [hfilters]
      exact hgoal
    · change (Finset.univ.filter (fun e : Fin (D.nArc + (rightTriangle R).nArc) =>
          V (sourceCode D R (A.symm e)) = v)).card = 1
      have hcard := filter_card_equiv A
        (fun e : ArcCode D R => sourceCode D R e = x)
      have hgoal : (Finset.univ.filter (fun e : Fin (D.nArc + (rightTriangle R).nArc) =>
          sourceCode D R (A.symm e) = x)).card = 1 := by
        calc
          _ = (Finset.univ.filter (fun e : ArcCode D R => sourceCode D R e = x)).card := by
            convert hcard using 1 <;> congr 1 <;> ext e <;>
              simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          _ = 1 := by
            convert hdeg.2 using 1 <;> congr 1 <;> ext e <;>
              simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have hfilters : (Finset.univ.filter (fun e : Fin (D.nArc + (rightTriangle R).nArc) =>
          V (sourceCode D R (A.symm e)) = v)) =
          (Finset.univ.filter (fun e : Fin (D.nArc + (rightTriangle R).nArc) =>
            sourceCode D R (A.symm e) = x)) := by
        ext e
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · intro h
          exact V.injective (h.trans (V.apply_symm_apply v).symm)
        · intro h
          simpa only [x, h, V.apply_symm_apply]
      rw [hfilters]
      exact hgoal
  · intro e
    change V (targetCode D R (A.symm e)) =
      V (sourceCode D R (A.symm (A ((continuationCode D R) (A.symm e)))))
    simpa only [A.symm_apply_apply] using
      congrArg V (continuationCode_incidence D R (A.symm e))
  · intro c i
    simp only [Equiv.trans_apply, A.symm_apply_apply]
    change A (continuationCode D R (.inl (D.incoming c i))) =
      A (.inl (D.outgoing c (D.through c i)))
    exact congrArg (fun e => A (.inl e)) (D.continuation_crossing c i)
  · intro v w h
    apply V.symm.injective
    exact vertexPointCode_injective D R hleft hright h
  · intro e h
    exact sourceCode_ne_targetCode D R (A.symm e) (V.injective h)
  · intro e f hef s t hs0 hs1 ht0 ht1 h
    have he : A.symm e ≠ A.symm f := fun h' => hef (A.symm.injective h')
    apply arcPointCode_interiors_disjoint D R hleft hright
      (A.symm e) (A.symm f) he s t hs0 hs1 ht0 ht1
    simpa only [arcPointCode, V.symm_apply_apply] using h
  · intro v e t ht0 ht1 h
    apply vertexPointCode_avoid_arc_interiors D R hleft hright
      (V.symm v) (A.symm e) t ht0 ht1
    simpa only [arcPointCode, V.symm_apply_apply] using h
  · intro c i
    simpa only [Prod.fst_sub, Prod.snd_sub, V.symm_apply_apply,
      A.symm_apply_apply, vertexPointCode, sourceCode, targetCode] using
      D.through_tangents_positive_collinear c i
  · intro c
    simpa only [strandTangent, V.symm_apply_apply, A.symm_apply_apply,
      vertexPointCode, sourceCode] using D.crossing_transverse c

end DirectGLSSW.HOMFLY.SplitCircleConstructor

