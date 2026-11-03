import HOMFLYTriangleTranslatedRay

set_option autoImplicit false
namespace DirectGLSSW.HOMFLY
noncomputable section

 theorem permutation_sign_changes_even {α : Type*} [Fintype α] [DecidableEq α]
    (p : Equiv.Perm α) (f : α → Bool) :
    (Finset.univ.filter (fun a => f a ≠ f (p a))).card % 2 = 0 := by
  classical
  let S := Finset.univ.filter (fun a => f a = true)
  let T := Finset.univ.filter (fun a => f (p a) = true)
  have he : T.image p = S := by
    ext a
    simp only [Finset.mem_image,Finset.mem_filter,Finset.mem_univ,true_and,S,T]
    constructor
    · rintro ⟨b,hb,rfl⟩; exact hb
    · intro ha
      exact ⟨p.symm a,by simpa using ha,p.apply_symm_apply a⟩
  have hcard : T.card=S.card := by
    rw [← he,Finset.card_image_of_injective _ p.injective]
  have hcut : Finset.univ.filter (fun a => f a ≠ f (p a)) = (S \ T) ∪ (T \ S) := by
    ext a
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_union,Finset.mem_sdiff,S,T]
    cases f a <;> cases f (p a) <;> simp
  have hd : Disjoint (S \ T) (T \ S) := by
    apply Finset.disjoint_left.2
    intro a ha hb
    exact (Finset.mem_sdiff.mp ha).2 (Finset.mem_sdiff.mp hb).1
  rw [hcut,Finset.card_union_of_disjoint hd]
  have h1 := Finset.card_sdiff_add_card S T
  have h2 := Finset.card_sdiff_add_card T S
  rw [Finset.union_comm T S] at h2
  omega

theorem diagramArcPath_range_segment (D : PLLinkDiagram) (e : Fin D.nArc) :
    Set.range (diagramArcPath D e) =
      segment ℝ (D.vertexPoint (D.arcSource e)) (D.vertexPoint (D.arcTarget e)) := by
  ext z
  constructor
  · rintro ⟨t,rfl⟩
    refine ⟨1-t.val,t.val,by linarith [t.property.2],t.property.1,by ring,?_⟩
    ext <;> dsimp [diagramArcPath,affinePoint] <;> ring
  · rintro ⟨u,v,hu,hv,hs,hz⟩
    refine ⟨⟨v,hv,by linarith⟩,?_⟩
    change affinePoint (D.vertexPoint (D.arcSource e)) (D.vertexPoint (D.arcTarget e)) v=z
    have hue : u=1-v := by linarith
    rw [← hz,hue]
    ext <;> dsimp [diagramArcPath,affinePoint] <;> ring

namespace DrawingCircuit

def horizontalCrossingEdges {D : PLLinkDiagram} (P : DrawingCircuit D) (h : ℝ) : Finset (Fin P.size) :=
  Finset.univ.filter (fun i => decide ((D.vertexPoint (P.vertex i)).2 < h) ≠
    decide ((D.vertexPoint (P.vertex (finRotate P.size i))).2 < h))

theorem horizontalCrossingEdges_even {D : PLLinkDiagram} (P : DrawingCircuit D) (h : ℝ) :
    (P.horizontalCrossingEdges h).card % 2=0 :=
  permutation_sign_changes_even (finRotate P.size) (fun i => decide ((D.vertexPoint (P.vertex i)).2 < h))

theorem arc_range_eq_edge_segment {D : PLLinkDiagram} (P : DrawingCircuit D) (i : Fin P.size) :
    Set.range (diagramArcPath D (P.arc i)) =
      segment ℝ (D.vertexPoint (P.vertex i)) (D.vertexPoint (P.vertex (finRotate P.size i))) := by
  rw [diagramArcPath_range_segment]
  have hs := P.start_eq i
  have he := P.end_eq i
  cases hf : P.forward i with
  | false =>
      simp only [directedArcStart,directedArcEnd,hf,Bool.false_eq_true,if_false] at hs he
      rw [hs,he]
      exact segment_symm ℝ _ _
  | true =>
      simp only [directedArcStart,directedArcEnd,hf,if_true] at hs he
      rw [hs,he]

/-- Distinct actual drawing arcs cannot share a generic horizontal cut point. -/
theorem horizontal_arc_cuts_disjoint {D : PLLinkDiagram} (P : DrawingCircuit D) (h : ℝ)
    (hgeneric : ∀ i, (D.vertexPoint (P.vertex i)).2 ≠ h)
    (i j : Fin P.size) (hij : i ≠ j) :
    Disjoint (Set.range (diagramArcPath D (P.arc i)) ∩ {z | z.2=h})
      (Set.range (diagramArcPath D (P.arc j)) ∩ {z | z.2=h}) := by
  apply Set.disjoint_left.2
  rintro z ⟨hi,hy⟩ ⟨hj,_⟩
  have ha : P.arc i ≠ P.arc j := fun he => hij (P.arc.injective he)
  obtain ⟨v,hz,hiv,_⟩ := (diagramArcPath_intersection_iff D (P.arc i) (P.arc j) ha z).mp ⟨hi,hj⟩
  rcases (P.arc_endpoint_iff i v).mp hiv with he | he
  · exact hgeneric i (by rw [he,← hz]; exact hy)
  · exact hgeneric (finRotate P.size i) (by rw [he,← hz]; exact hy)

end DrawingCircuit
end
end DirectGLSSW.HOMFLY




