import ActiveArcOpenReconstructionIncidence
import Mathlib.Topology.Algebra.Order.Field

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.ConfigurationLocality
open DirectGLSSW ActiveArc OpenCarrier Filter Topology
variable {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ)

/-- Closed segments of actual physical edges only. -/
def physicalClosed (e : Fin (n+1)) (x : PlanarPoint ℝ) : Prop :=
  ∃ t : ℝ, 0≤t ∧ t≤1 ∧ x=affinePoint (q e.castSucc) (q e.succ) t

theorem vertex_closed_incident (hG1 : cyclicNoncollinear q)
    (e : Fin (n+1)) (i : Fin (n+2)) (hi : physicalClosed q e (q i)) :
    i=e.castSucc ∨ i=e.succ := by
  by_contra hh
  push_neg at hh
  obtain ⟨t,_,_,ht⟩ := hi
  apply hG1 i e.castSucc e.succ hh.1
    (by intro h; have := congrArg Fin.val h; simp only [Fin.coe_castSucc,Fin.val_succ] at this; omega) hh.2
  rw [ht]
  simp only [affinePoint,planarDet,Prod.fst_sub,Prod.snd_sub]
  ring

private theorem closed_interior_of_not_endpoints (e : Fin (n+1)) (x : PlanarPoint ℝ)
    (hx : physicalClosed q e x) (h0 : x≠q e.castSucc) (h1 : x≠q e.succ) :
    edgeInterior q e x := by
  obtain ⟨t,ht0,ht1,hx⟩ := hx
  have hn0 : t≠0 := by intro h; subst t; exact h0 (hx.trans (affinePoint_zero _ _))
  have hn1 : t≠1 := by intro h; subst t; exact h1 (hx.trans (affinePoint_one _ _))
  exact ⟨t,lt_of_le_of_ne ht0 (Ne.symm hn0),lt_of_le_of_ne ht1 hn1,hx⟩

/-- Three distinct physical closed edges cannot meet at an anchor under G1. -/
theorem closed_triple_no_anchor (hG1 : cyclicNoncollinear q)
    (e f g : Fin (n+1)) (hef : e≠f) (hfg : f≠g) (hge : g≠e)
    (i : Fin (n+2)) (he : physicalClosed q e (q i))
    (hf : physicalClosed q f (q i)) (hg : physicalClosed q g (q i)) : False := by
  have he' := vertex_closed_incident q hG1 e i he
  have hf' := vertex_closed_incident q hG1 f i hf
  have hg' := vertex_closed_incident q hG1 g i hg
  have hefv : e.val≠f.val := fun h => hef (Fin.ext h)
  have hfgv : f.val≠g.val := fun h => hfg (Fin.ext h)
  have hgev : g.val≠e.val := fun h => hge (Fin.ext h)
  have heval : i.val=e.val ∨ i.val=e.val+1 := by
    rcases he' with h|h <;> rw [h] <;> simp
  have hfval : i.val=f.val ∨ i.val=f.val+1 := by
    rcases hf' with h|h <;> rw [h] <;> simp
  have hgval : i.val=g.val ∨ i.val=g.val+1 := by
    rcases hg' with h|h <;> rw [h] <;> simp
  omega

theorem no_three_physical_closed (hR : Regular q) (hG1 : cyclicNoncollinear q)
    (e f g : Fin (n+1)) (hef : e≠f) (hfg : f≠g) (hge : g≠e) :
    ¬ ∃ x, physicalClosed q e x ∧ physicalClosed q f x ∧ physicalClosed q g x := by
  rintro ⟨x,he,hf,hg⟩
  have hanchor : ∀ i : Fin (n+2), x≠q i := by
    intro i hi
    rw [hi] at he hf hg
    exact closed_triple_no_anchor q hG1 e f g hef hfg hge i he hf hg
  exact hR.noTriple e f g x hef hfg hge
    ⟨closed_interior_of_not_endpoints q e x he (hanchor _) (hanchor _),
     closed_interior_of_not_endpoints q f x hf (hanchor _) (hanchor _),
     closed_interior_of_not_endpoints q g x hg (hanchor _) (hanchor _)⟩

private theorem continuous_affinePoint {α : Type*} [TopologicalSpace α]
    (a b : α → PlanarPoint ℝ) (t : α → ℝ)
    (ha : Continuous a) (hb : Continuous b) (ht : Continuous t) :
    Continuous (fun x => affinePoint (a x) (b x) (t x)) := by
  exact (ha.fst.add (ht.mul (hb.fst.sub ha.fst))).prodMk
    (ha.snd.add (ht.mul (hb.snd.sub ha.snd)))

/-- Nonincidence of three closed physical segments is an open configuration condition. -/
theorem eventually_no_three_closed (e f g : Fin (n+1))
    (h : ¬ ∃ x, physicalClosed q e x ∧ physicalClosed q f x ∧ physicalClosed q g x) :
    ∀ᶠ q' in 𝓝 q, ¬ ∃ x, physicalClosed q' e x ∧ physicalClosed q' f x ∧ physicalClosed q' g x := by
  let I := Set.Icc (0 : ℝ) 1
  let T := I × (I × I)
  let X := Fin (n+2) → PlanarPoint ℝ
  let P : X × T → PlanarPoint ℝ := fun z => affinePoint (z.1 e.castSucc) (z.1 e.succ) z.2.1
  let F : X × T → PlanarPoint ℝ := fun z => affinePoint (z.1 f.castSucc) (z.1 f.succ) z.2.2.1
  let G : X × T → PlanarPoint ℝ := fun z => affinePoint (z.1 g.castSucc) (z.1 g.succ) z.2.2.2
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
      ∃ x, physicalClosed q' e x ∧ physicalClosed q' f x ∧ physicalClosed q' g x := by
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
theorem eventually_vertex_G1 (hG1 : cyclicNoncollinear q) :
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
      · have hc : Continuous (fun q' : Fin (n+2) → PlanarPoint ℝ =>
            planarDet (q' j-q' k) (q' i-q' k)) := by
          unfold planarDet
          fun_prop
        exact (hc.continuousAt.eventually_ne (hG1 i j k hij hjk hki)).mono
          (fun _ h _ _ _ => h)

/-- Regularity and vertex G1 persist without adding a closing edge to the arc. -/
theorem eventually_regular_G1 (hR : Regular q) (hG1 : cyclicNoncollinear q) :
    ∀ᶠ q' in 𝓝 q, Regular q' ∧ cyclicNoncollinear q' := by
  have he : ∀ᶠ q' in 𝓝 q, ∀ e : Fin (n+1), q' e.succ-q' e.castSucc≠0 := by
    apply Filter.eventually_all.mpr
    intro e
    exact ((continuous_apply e.succ).sub (continuous_apply e.castSucc)).continuousAt.eventually_ne
      (hR.edge_nonzero e)
  have ht : ∀ᶠ q' in 𝓝 q, NoTriple q' := by
    have hc : ∀ᶠ q' in 𝓝 q, ∀ e f g : Fin (n+1), e≠f → f≠g → g≠e →
        ¬ ∃ x, physicalClosed q' e x ∧ physicalClosed q' f x ∧ physicalClosed q' g x := by
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
        · by_cases hge : g=e
          · exact Filter.Eventually.of_forall (fun _ _ _ h => False.elim (h hge))
          · exact (eventually_no_three_closed q e f g
              (no_three_physical_closed q hR hG1 e f g hef hfg hge)).mono
              (fun _ h _ _ _ => h)
    filter_upwards [hc] with q' hq'
    intro e f g x hef hfg hge ⟨⟨s,hs0,hs1,hs⟩,⟨t,ht0,ht1,ht⟩,⟨u,hu0,hu1,hu⟩⟩
    exact hq' e f g hef hfg hge ⟨x,⟨s,hs0.le,hs1.le,hs⟩,
      ⟨t,ht0.le,ht1.le,ht⟩,⟨u,hu0.le,hu1.le,hu⟩⟩
  filter_upwards [he,ht,eventually_vertex_G1 q hG1] with q' he ht hG1'
  refine ⟨⟨he,?_,ht,?_⟩,hG1'⟩
  · intro e f hef x hx hy
    obtain ⟨s,_,_,hs⟩ := hx
    obtain ⟨t,_,_,ht⟩ := hy
    exact physicalLine_denominator_ne q' hG1' e f hef s t (hs.symm.trans ht)
  · intro e i hi0 hi1 h
    obtain ⟨t,ht0,ht1,ht⟩ := h
    exact (vertex_closed_incident q' hG1' e i ⟨t,ht0.le,ht1.le,ht⟩).elim hi0 hi1





end DirectGLSSW.ActiveArc.ConfigurationLocality
