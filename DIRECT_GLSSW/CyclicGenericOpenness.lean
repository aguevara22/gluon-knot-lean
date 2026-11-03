import DirectGLSSW.ShortEdgeGenericity
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Instances.Real.Lemmas
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.CyclicGenericLocality
open DirectGLSSW ShortEdgeGenericity Filter Topology
variable {m : ℕ} (q : Fin m → PlanarPoint ℝ)

private theorem continuous_affinePoint {α : Type*} [TopologicalSpace α]
    (a b : α → PlanarPoint ℝ) (t : α → ℝ)
    (ha : Continuous a) (hb : Continuous b) (ht : Continuous t) :
    Continuous (fun x => affinePoint (a x) (b x) (t x)) := by
  exact (ha.fst.add (ht.mul (hb.fst.sub ha.fst))).prodMk
    (ha.snd.add (ht.mul (hb.snd.sub ha.snd)))

/-- Nonincidence of three closed physical segments is an open configuration condition. -/
private theorem eventually_no_three_closed (e f g : Fin m)
    (h : ¬ ∃ x, edgeClosed q e x ∧ edgeClosed q f x ∧ edgeClosed q g x) :
    ∀ᶠ q' in 𝓝 q, ¬ ∃ x, edgeClosed q' e x ∧ edgeClosed q' f x ∧ edgeClosed q' g x := by
  let I := Set.Icc (0 : ℝ) 1
  let T := I × (I × I)
  let X := Fin m → PlanarPoint ℝ
  let P : X × T → PlanarPoint ℝ := fun z => affinePoint (z.1 e) (z.1 (cyclicSuccessor e)) z.2.1
  let F : X × T → PlanarPoint ℝ := fun z => affinePoint (z.1 f) (z.1 (cyclicSuccessor f)) z.2.2.1
  let G : X × T → PlanarPoint ℝ := fun z => affinePoint (z.1 g) (z.1 (cyclicSuccessor g)) z.2.2.2
  have hP : Continuous P := by
    dsimp only [P,T,X,I]
    apply continuous_affinePoint <;> fun_prop
  have hF : Continuous F := by
    dsimp only [F,T,X,I]
    apply continuous_affinePoint <;> fun_prop
  have hG : Continuous G := by
    dsimp only [G,T,X,I]
    apply continuous_affinePoint <;> fun_prop
  let B : Set (X × T) := {z | P z=F z ∧ F z=G z}
  have hB : IsClosed B := (isClosed_eq hP hF).inter (isClosed_eq hF hG)
  have hproj : IsClosed (Prod.fst '' B) := isClosedMap_fst_of_compactSpace B hB
  have hmem (q' : X) : q'∈Prod.fst '' B ↔
      ∃ x, edgeClosed q' e x ∧ edgeClosed q' f x ∧ edgeClosed q' g x := by
    constructor
    · rintro ⟨⟨q'',s,t,u⟩,⟨hst,htu⟩,heq⟩
      change q''=q' at heq
      subst q''
      exact ⟨_,⟨s,s.property.1,s.property.2,rfl⟩,
        ⟨t,t.property.1,t.property.2,hst⟩,
        ⟨u,u.property.1,u.property.2,hst.trans htu⟩⟩
    · rintro ⟨x,⟨s,hs0,hs1,hs⟩,⟨t,ht0,ht1,ht⟩,⟨u,hu0,hu1,hu⟩⟩
      exact ⟨(q',(⟨s,hs0,hs1⟩,⟨t,ht0,ht1⟩,⟨u,hu0,hu1⟩)),⟨hs.symm.trans ht,ht.symm.trans hu⟩,rfl⟩
  have hq : q∈(Prod.fst '' B)ᶜ := fun hq => h ((hmem q).mp hq)
  filter_upwards [hproj.isOpen_compl.mem_nhds hq] with q' hq'
  exact fun hx => hq' ((hmem q').mpr hx)

/-- Vertex G1 persists near the actual finite configuration. -/
private theorem eventually_vertex_G1 (hG1 : cyclicNoncollinear q) :
    ∀ᶠ q' in 𝓝 q, cyclicNoncollinear q' := by
  apply Filter.eventually_all.mpr
  intro i
  apply Filter.eventually_all.mpr
  intro j
  apply Filter.eventually_all.mpr
  intro k
  by_cases hij : i=j
  · exact Filter.Eventually.of_forall (fun _ h => False.elim (h hij))
  · by_cases hjk : j=k
    · exact Filter.Eventually.of_forall (fun _ _ h => False.elim (h hjk))
    · by_cases hki : i=k
      · exact Filter.Eventually.of_forall (fun _ _ _ h => False.elim (h hki))
      · have hc : Continuous (fun q' : Fin m → PlanarPoint ℝ =>
            planarDet (q' j-q' k) (q' i-q' k)) := by
          unfold planarDet
          fun_prop
        exact (hc.continuousAt.eventually_ne (hG1 i j k hij hjk hki)).mono
          (fun _ h _ _ _ => h)

/-- Exactly cyclic G1/G2 genericity persists under arbitrary finite vertex perturbations. -/
theorem eventually_cyclicGeneric (hq : CyclicGeneric q) :
    ∀ᶠ r in 𝓝 q, CyclicGeneric r := by
  have ht : ∀ᶠ r in 𝓝 q, ∀ e f g : Fin m, e≠f → f≠g → e≠g →
      ¬ ∃ x, edgeClosed r e x ∧ edgeClosed r f x ∧ edgeClosed r g x := by
    apply Filter.eventually_all.mpr
    intro e
    apply Filter.eventually_all.mpr
    intro f
    apply Filter.eventually_all.mpr
    intro g
    by_cases hef : e=f
    · exact Filter.Eventually.of_forall (fun _ h => False.elim (h hef))
    · by_cases hfg : f=g
      · exact Filter.Eventually.of_forall (fun _ _ h => False.elim (h hfg))
      · by_cases heg : e=g
        · exact Filter.Eventually.of_forall (fun _ _ _ h => False.elim (h heg))
        · have hbase : ¬ ∃ x, edgeClosed q e x ∧ edgeClosed q f x ∧ edgeClosed q g x := by
            rintro ⟨x,hx⟩
            exact cyclic_no_three_closed_edges q hq e f g x hef hfg heg hx
          exact (eventually_no_three_closed q e f g hbase).mono
            (fun _ h _ _ _ => h)
  filter_upwards [eventually_vertex_G1 q hq.g1,ht] with r hG1 hclosed
  refine ⟨hq.size_ge_three,hG1,?_⟩
  intro e f g x hef hfg heg ⟨⟨s,hs0,hs1,hs⟩,⟨t,ht0,ht1,ht⟩,⟨u,hu0,hu1,hu⟩⟩
  exact hclosed e f g hef hfg heg ⟨x,⟨s,hs0.le,hs1.le,hs⟩,
    ⟨t,ht0.le,ht1.le,ht⟩,⟨u,hu0.le,hu1.le,hu⟩⟩

/-- Arbitrary continuous parameter spaces inherit the finite configuration result. -/
theorem eventually_cyclicGeneric_of_continuousAt
    {α : Type*} [TopologicalSpace α] (Q : α → Fin m → PlanarPoint ℝ) (x : α)
    (hQ : ContinuousAt Q x) (hq : CyclicGeneric (Q x)) :
    ∀ᶠ y in 𝓝 x, CyclicGeneric (Q y) :=
  hQ.eventually (eventually_cyclicGeneric (Q x) hq)



end DirectGLSSW.CyclicGenericLocality
