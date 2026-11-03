import CrossingRationalParameters

set_option autoImplicit false
namespace DirectGLSSW.CrossingIncidenceNeighborhood
open CrossingRationalParameters ShortEdgeGenericity
open Filter Topology
noncomputable section
attribute [local instance] Classical.propDecidable

def CoordClose {n : ℕ} (η : ℝ) (Q P : Configuration n) : Prop :=
  ∀ i, |(Q i).1-(P i).1| < η ∧ |(Q i).2-(P i).2| < η

theorem exists_coordBox_subset {n : ℕ} (P : Configuration n) (S : Set (Configuration n))
    (hS : S ∈ 𝓝 P) :
    ∃ η : ℝ, 0 < η ∧ ∀ Q, CoordClose η Q P → Q ∈ S := by
  obtain ⟨η,hη,hball⟩ := Metric.mem_nhds_iff.mp hS
  refine ⟨η,hη,?_⟩
  intro Q hQ
  apply hball
  rw [Metric.mem_ball,dist_pi_lt_iff hη]
  intro i
  rw [Prod.dist_eq,Real.dist_eq,Real.dist_eq,max_lt_iff]
  exact hQ i

theorem isClosed_two_closed_edges {n : ℕ} (e f : Fin n) :
    IsClosed {Q : Configuration n | ∃ x : Point, edgeClosed Q e x ∧ edgeClosed Q f x} := by
  let I := Set.Icc (0 : ℝ) 1
  let T := I × I
  let A : Configuration n × T → Point := fun z =>
    affinePoint (z.1 e) (z.1 (cyclicSuccessor e)) z.2.1
  let B : Configuration n × T → Point := fun z =>
    affinePoint (z.1 f) (z.1 (cyclicSuccessor f)) z.2.2
  have hA : Continuous A := by dsimp [A,T,affinePoint]; fun_prop
  have hB : Continuous B := by dsimp [B,T,affinePoint]; fun_prop
  let C : Set (Configuration n × T) := {z | A z=B z}
  have hC : IsClosed C := isClosed_eq hA hB
  have hclosed : IsClosed (Prod.fst '' C) := isClosedMap_fst_of_compactSpace C hC
  have heq : Prod.fst '' C =
      {Q : Configuration n | ∃ x : Point, edgeClosed Q e x ∧ edgeClosed Q f x} := by
    ext Q
    constructor
    · rintro ⟨⟨Q',s,t⟩,hz,hQ⟩
      change Q'=Q at hQ
      subst Q'
      exact ⟨affinePoint (Q e) (Q (cyclicSuccessor e)) s,
        ⟨s,s.property.1,s.property.2,rfl⟩,
        ⟨t,t.property.1,t.property.2,hz⟩⟩
    · rintro ⟨x,⟨s,hs0,hs1,hxs⟩,⟨t,ht0,ht1,hxt⟩⟩
      exact ⟨(Q,⟨s,hs0,hs1⟩,⟨t,ht0,ht1⟩),hxs.symm.trans hxt,rfl⟩
  rw [← heq]
  exact hclosed

theorem no_closed_intersection_of_nonincident {n : ℕ} (P : Configuration n)
    (hP : CyclicGeneric P) (e f : Fin n) (hef : e≠f)
    (hes : cyclicSuccessor e≠f) (hfs : cyclicSuccessor f≠e)
    (hno : ¬ edgeIntersection P e f) :
    ¬ ∃ x : Point, edgeClosed P e x ∧ edgeClosed P f x := by
  rintro ⟨x,he,hf⟩
  have hxv : ∀ v : Fin n, x≠P v := by
    intro v hv
    have hve := edgeClosed_vertex_incident P hP e v (hv ▸ he)
    have hvf := edgeClosed_vertex_incident P hP f v (hv ▸ hf)
    rcases hve with hve|hve <;> rcases hvf with hvf|hvf
    · exact hef (hve.symm.trans hvf)
    · exact hfs (hvf.symm.trans hve)
    · exact hes (hve.symm.trans hvf)
    · exact hef (cyclicSuccessor_bijective.injective (hve.symm.trans hvf))
  exact hno ⟨x,edgeClosed_open_of_not_vertex P e x he hxv,
    edgeClosed_open_of_not_vertex P f x hf hxv⟩

theorem eventually_intersection_of_intersection {n : ℕ} (P : Configuration n)
    (hP : CyclicGeneric P) (e f : Fin n) (hef : e≠f)
    (hx : edgeIntersection P e f) :
    ∀ᶠ Q in 𝓝 P, edgeIntersection Q e f ∧ denominator Q e f≠0 := by
  obtain ⟨x,he,hf⟩ := hx
  have hD : denominator P e f≠0 := cyclicTangent_det_ne_zero_of_intersection
    hP.size_ge_three P hP.g1 e f hef x he hf
  have hpar := (edgeIntersection_iff_parameters P e f hD).mp ⟨x,he,hf⟩
  have hL : ∀ᶠ Q in 𝓝 P, leftParameter Q e f ∈ Set.Ioo 0 1 :=
    (continuousAt_leftParameter P e f hD).eventually (Ioo_mem_nhds hpar.1 hpar.2.1)
  have hR : ∀ᶠ Q in 𝓝 P, rightParameter Q e f ∈ Set.Ioo 0 1 :=
    (continuousAt_rightParameter P e f hD).eventually (Ioo_mem_nhds hpar.2.2.1 hpar.2.2.2)
  have hDen : ∀ᶠ Q in 𝓝 P, denominator Q e f≠0 :=
    (continuous_denominator e f).continuousAt.eventually (eventually_ne_nhds hD)
  filter_upwards [hL,hR,hDen] with Q hL hR hDen
  exact ⟨(edgeIntersection_iff_parameters Q e f hDen).mpr ⟨hL.1,hL.2,hR.1,hR.2⟩,hDen⟩

theorem eventually_edgeIntersection_iff {n : ℕ} (P : Configuration n)
    (hP : CyclicGeneric P) (e f : Fin n) :
    ∀ᶠ Q in 𝓝 P, cyclicNoncollinear Q →
      (edgeIntersection Q e f ↔ edgeIntersection P e f) := by
  by_cases hef : e=f
  · subst f
    apply Filter.Eventually.of_forall
    intro Q _
    have hx (R : Configuration n) : edgeIntersection R e e :=
      ⟨affinePoint (R e) (R (cyclicSuccessor e)) (1/2),
        ⟨1/2,by norm_num,by norm_num,rfl⟩,⟨1/2,by norm_num,by norm_num,rfl⟩⟩
    exact iff_of_true (hx Q) (hx P)
  by_cases hes : cyclicSuccessor e=f
  · apply Filter.Eventually.of_forall
    intro Q hQ
    subst f
    have hno (R : Configuration n) (hR : cyclicNoncollinear R) :
        ¬ edgeIntersection R e (cyclicSuccessor e) := by
      rintro ⟨x,he,hf⟩
      exact cyclic_adjacent_interiors_disjoint hP.size_ge_three R hR e x he hf
    exact iff_of_false (hno Q hQ) (hno P hP.g1)
  by_cases hfs : cyclicSuccessor f=e
  · apply Filter.Eventually.of_forall
    intro Q hQ
    subst e
    have hno (R : Configuration n) (hR : cyclicNoncollinear R) :
        ¬ edgeIntersection R (cyclicSuccessor f) f := by
      rintro ⟨x,he,hf⟩
      exact cyclic_adjacent_interiors_disjoint hP.size_ge_three R hR f x hf he
    exact iff_of_false (hno Q hQ) (hno P hP.g1)
  by_cases hx : edgeIntersection P e f
  · filter_upwards [eventually_intersection_of_intersection P hP e f hef hx] with Q hQ
    exact fun _ => iff_of_true hQ.1 hx
  · have hclosed := isClosed_two_closed_edges e f
    have hPno := no_closed_intersection_of_nonincident P hP e f hef hes hfs hx
    have hloc : ∀ᶠ Q in 𝓝 P, ¬ ∃ x : Point, edgeClosed Q e x ∧ edgeClosed Q f x :=
      hclosed.isOpen_compl.mem_nhds hPno
    filter_upwards [hloc] with Q hQ
    intro _
    apply iff_of_false _ hx
    rintro ⟨x,⟨s,hs0,hs1,hxs⟩,⟨t,ht0,ht1,hxt⟩⟩
    exact hQ ⟨x,⟨s,hs0.le,hs1.le,hxs⟩,⟨t,ht0.le,ht1.le,hxt⟩⟩

theorem exists_incidence_box_of_g1 {n : ℕ} (P : Configuration n)
    (hP : CyclicGeneric P) :
    ∃ η : ℝ, 0 < η ∧ ∀ Q, CoordClose η Q P →
      (cyclicNoncollinear Q → ∀ e f, edgeIntersection Q e f ↔ edgeIntersection P e f) ∧
      ∀ c : PolygonCrossing P, denominator Q c.val.1 c.val.2≠0 := by
  have hinc : ∀ᶠ Q in 𝓝 P, ∀ e f : Fin n,
      cyclicNoncollinear Q → (edgeIntersection Q e f ↔ edgeIntersection P e f) :=
    Filter.eventually_all.mpr (fun e => Filter.eventually_all.mpr
      (fun f => eventually_edgeIntersection_iff P hP e f))
  have hden : ∀ᶠ Q in 𝓝 P, ∀ c : PolygonCrossing P, denominator Q c.val.1 c.val.2≠0 := by
    apply Filter.eventually_all.mpr
    intro c
    exact (eventually_intersection_of_intersection P hP c.val.1 c.val.2
      (crossing_edges_ne P c) c.property.2).mono (fun _ h => h.2)
  have hgood := hinc.and hden
  obtain ⟨η,hη,hbox⟩ := exists_coordBox_subset P _ hgood
  refine ⟨η,hη,?_⟩
  intro Q hQ
  have h := hbox Q hQ
  exact ⟨fun hG e f => h.1 e f hG,h.2⟩








end
end DirectGLSSW.CrossingIncidenceNeighborhood
