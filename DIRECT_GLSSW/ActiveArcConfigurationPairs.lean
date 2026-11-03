import ActiveArcOpenRegularNeighborhood
import ActiveArcParameterFormula
import DirectGLSSW.PolygonGeometry
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic.FunProp

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 1200000

noncomputable section

namespace DirectGLSSW.ActiveArc.ConfigurationLocality

open DirectGLSSW ActiveArc Filter Topology

variable {n : ℕ} (q : Fin (n + 2) → PlanarPoint ℝ)

private def physicalEdgesAdjacent (e f : Fin (n + 1)) : Prop :=
  e.succ = f.castSucc ∨ f.succ = e.castSucc

private theorem shared_physical_endpoint_adjacent (e f : Fin (n + 1))
    (hef : e ≠ f) (i : Fin (n + 2))
    (hi : i = e.castSucc ∨ i = e.succ)
    (hj : i = f.castSucc ∨ i = f.succ) : physicalEdgesAdjacent e f := by
  rcases hi with hi | hi <;> rcases hj with hj | hj
  · have h : e = f := by
      apply Fin.ext
      have hv := congrArg Fin.val (hi.symm.trans hj)
      simpa using hv
    exact False.elim (hef h)
  · exact Or.inr (hj.symm.trans hi)
  · exact Or.inl (hi.symm.trans hj)
  · have h : e = f := by
      apply Fin.ext
      have hv := congrArg Fin.val (hi.symm.trans hj)
      simpa using hv
    exact False.elim (hef h)

private theorem physicalClosed_open_of_not_endpoints
    (hR : ActiveArc.Regular q) (e : Fin (n + 1)) (x : PlanarPoint ℝ)
    (hx : physicalClosed q e x) (hleft : x ≠ q e.castSucc)
    (hright : x ≠ q e.succ) : ActiveArc.edgeInterior q e x := by
  obtain ⟨t, ht0, ht1, hxe⟩ := hx
  have hends : q e.castSucc ≠ q e.succ := by
    intro h
    apply hR.edge_nonzero e
    rw [h]
    exact sub_self _
  have htne0 : t ≠ 0 := by
    intro ht
    subst t
    exact hleft (hxe.trans (affinePoint_zero _ _))
  have htne1 : t ≠ 1 := by
    intro ht
    subst t
    exact hright (hxe.trans (affinePoint_one _ _))
  exact ⟨t, lt_of_le_of_ne ht0 (Ne.symm htne0),
    lt_of_le_of_ne ht1 htne1, hxe⟩

private theorem no_closed_pair_of_no_crossing
    (hR : ActiveArc.Regular q) (hG1 : cyclicNoncollinear q)
    (e f : Fin (n + 1)) (hef : e ≠ f)
    (hadj : ¬ physicalEdgesAdjacent e f)
    (hno : ¬ ∃ x, ActiveArc.edgeInterior q e x ∧ ActiveArc.edgeInterior q f x) :
    ¬ ∃ x, physicalClosed q e x ∧ physicalClosed q f x := by
  rintro ⟨x, he, hf⟩
  by_cases he0 : x = q e.castSucc
  · have hf' : physicalClosed q f (q e.castSucc) := by simpa [he0] using hf
    have hi := vertex_closed_incident q hG1 f e.castSucc hf'
    exact hadj (shared_physical_endpoint_adjacent e f hef e.castSucc
      (Or.inl rfl) hi)
  · by_cases he1 : x = q e.succ
    · have hf' : physicalClosed q f (q e.succ) := by simpa [he1] using hf
      have hi := vertex_closed_incident q hG1 f e.succ hf'
      exact hadj (shared_physical_endpoint_adjacent e f hef e.succ
        (Or.inr rfl) hi)
    · have heI := physicalClosed_open_of_not_endpoints q hR e x he he0 he1
      by_cases hf0 : x = q f.castSucc
      · have he' : physicalClosed q e (q f.castSucc) := by simpa [hf0] using he
        have hi := vertex_closed_incident q hG1 e f.castSucc he'
        exact hadj (shared_physical_endpoint_adjacent e f hef f.castSucc
          (by simpa using hi) (Or.inl rfl))
      · by_cases hf1 : x = q f.succ
        · have he' : physicalClosed q e (q f.succ) := by simpa [hf1] using he
          have hi := vertex_closed_incident q hG1 e f.succ he'
          exact hadj (shared_physical_endpoint_adjacent e f hef f.succ
            (by simpa using hi) (Or.inr rfl))
        · have hfI := physicalClosed_open_of_not_endpoints q hR f x hf hf0 hf1
          exact hno ⟨x, heI, hfI⟩

private theorem eventually_no_two_physical_closed (e f : Fin (n + 1))
    (hzero : ¬ ∃ x, physicalClosed q e x ∧ physicalClosed q f x) :
    ∀ᶠ r in 𝓝 q, ¬ ∃ x, physicalClosed r e x ∧ physicalClosed r f x := by
  let I := Set.Icc (0 : ℝ) 1
  let X := Fin (n + 2) → PlanarPoint ℝ
  let P : X × (I × I) → PlanarPoint ℝ := fun z =>
    affinePoint (z.1 e.castSucc) (z.1 e.succ) z.2.1
  let F : X × (I × I) → PlanarPoint ℝ := fun z =>
    affinePoint (z.1 f.castSucc) (z.1 f.succ) z.2.2
  have hP : Continuous P := by
    dsimp [P, X, I, affinePoint]
    fun_prop
  have hF : Continuous F := by
    dsimp [F, X, I, affinePoint]
    fun_prop
  let B : Set (X × (I × I)) := {z | P z = F z}
  have hB : IsClosed B := isClosed_eq hP hF
  have hprojected : IsClosed (Prod.fst '' B) := isClosedMap_fst_of_compactSpace B hB
  have hmem (r : X) : r ∈ Prod.fst '' B ↔
      ∃ x, physicalClosed r e x ∧ physicalClosed r f x := by
    constructor
    · rintro ⟨⟨r', s, t⟩, hz, hr⟩
      change r' = r at hr
      subst r'
      change affinePoint (r e.castSucc) (r e.succ) s =
        affinePoint (r f.castSucc) (r f.succ) t at hz
      exact ⟨affinePoint (r e.castSucc) (r e.succ) s,
        ⟨s, s.property.1, s.property.2, rfl⟩,
        ⟨t, t.property.1, t.property.2, hz⟩⟩
    · rintro ⟨x, ⟨s, hs0, hs1, hxs⟩, ⟨t, ht0, ht1, hxt⟩⟩
      exact ⟨(r, (⟨s, hs0, hs1⟩, ⟨t, ht0, ht1⟩)), hxs.symm.trans hxt, rfl⟩
  have hq : q ∈ (Prod.fst '' B)ᶜ := fun hh => hzero ((hmem q).mp hh)
  filter_upwards [hprojected.isOpen_compl.mem_nhds hq] with r hr
  exact fun hx => hr ((hmem r).mpr hx)

private theorem configuration_det_continuousAt
    (a b c d : Fin (n + 2)) :
    ContinuousAt (fun r : Fin (n + 2) → PlanarPoint ℝ =>
      planarDet (r b - r a) (r d - r c)) q := by
  unfold planarDet
  fun_prop

private theorem eventually_crossing_of_crossing
    (hR : ActiveArc.Regular q) (e f : Fin (n + 1)) (hef : e ≠ f)
    (hx : ∃ x, ActiveArc.edgeInterior q e x ∧ ActiveArc.edgeInterior q f x) :
    ∀ᶠ r in 𝓝 q, ∃ x, ActiveArc.edgeInterior r e x ∧ ActiveArc.edgeInterior r f x := by
  obtain ⟨x, he, hf⟩ := hx
  obtain ⟨s, hs0, hs1, hxs⟩ := he
  obtain ⟨t, ht0, ht1, hxt⟩ := hf
  have he0 : ActiveArc.edgeInterior q e x := ⟨s, hs0, hs1, hxs⟩
  have hf0 : ActiveArc.edgeInterior q f x := ⟨t, ht0, ht1, hxt⟩
  have hdet : planarDet (q e.succ - q e.castSucc) (q f.succ - q f.castSucc) ≠ 0 :=
    ActiveArc.Regular.transverse hR e f hef x he0 hf0
  let L : (Fin (n + 2) → PlanarPoint ℝ) → ℝ := fun r =>
    LocalCrossingTransport.leftParameter (r e.castSucc) (r e.succ)
      (r f.castSucc) (r f.succ)
  let U : (Fin (n + 2) → PlanarPoint ℝ) → ℝ := fun r =>
    LocalCrossingTransport.rightParameter (r e.castSucc) (r e.succ)
      (r f.castSucc) (r f.succ)
  have hL : ContinuousAt L q := by
    dsimp [L, LocalCrossingTransport.leftParameter]
    apply ContinuousAt.div
    · unfold planarDet; fun_prop
    · unfold planarDet; fun_prop
    · exact hdet
  have hU : ContinuousAt U q := by
    dsimp [U, LocalCrossingTransport.rightParameter]
    apply ContinuousAt.div
    · unfold planarDet; fun_prop
    · unfold planarDet; fun_prop
    · exact hdet
  have hL0 : L q = s := by
    dsimp [L]
    exact LocalCrossingTransport.leftParameter_eq _ _ _ _ s t hdet (hxs.symm.trans hxt)
  have hU0 : U q = t := by
    dsimp [U]
    exact LocalCrossingTransport.rightParameter_eq _ _ _ _ s t hdet (hxs.symm.trans hxt)
  have hs' : ∀ᶠ r in 𝓝 q, L r ∈ Set.Ioo (0 : ℝ) 1 :=
    hL.eventually (isOpen_Ioo.mem_nhds (by rw [hL0]; exact ⟨hs0, hs1⟩))
  have ht' : ∀ᶠ r in 𝓝 q, U r ∈ Set.Ioo (0 : ℝ) 1 :=
    hU.eventually (isOpen_Ioo.mem_nhds (by rw [hU0]; exact ⟨ht0, ht1⟩))
  let D : (Fin (n + 2) → PlanarPoint ℝ) → ℝ := fun r =>
    planarDet (r e.succ - r e.castSucc) (r f.succ - r f.castSucc)
  have hD : ContinuousAt D q := by dsimp [D]; unfold planarDet; fun_prop
  have hD' : ∀ᶠ r in 𝓝 q, D r ≠ 0 := hD.eventually_ne hdet
  filter_upwards [hs', ht', hD'] with r hsr htr hdr
  refine ⟨affinePoint (r e.castSucc) (r e.succ) (L r),
    ⟨L r, hsr.1, hsr.2, rfl⟩,
    ⟨U r, htr.1, htr.2, ?_⟩⟩
  exact LocalCrossingTransport.carrier_parameter_equation _ _ _ _ hdr

private theorem cyclic_successor_castSucc (e : Fin (n + 1)) :
    DirectGLSSW.cyclicSuccessor (e.castSucc : Fin (n + 2)) = e.succ := by
  apply Fin.ext
  simp [DirectGLSSW.cyclicSuccessor, DirectGLSSW.cyclicVertexIndex]

private theorem adjacent_interiors_disjoint_forward
    (hG1 : cyclicNoncollinear q) (e f : Fin (n + 1))
    (hEF : e.succ = f.castSucc) (x : PlanarPoint ℝ)
    (he : ActiveArc.edgeInterior q e x) (hf : ActiveArc.edgeInterior q f x) : False := by
  have hcyc := cyclic_successor_castSucc (n := n) e
  have hnext := hcyc.trans hEF
  have he' : DirectGLSSW.edgeInterior q e.castSucc x := by
    rcases he with ⟨t, ht0, ht1, hxe⟩
    exact ⟨t, ht0, ht1, by simpa [hcyc] using hxe⟩
  have hf' : DirectGLSSW.edgeInterior q f.castSucc x := by
    rcases hf with ⟨t, ht0, ht1, hxf⟩
    refine ⟨t, ht0, ht1, ?_⟩
    rw [cyclic_successor_castSucc (n := n) f]
    exact hxf
  have hdis := cyclic_adjacent_interiors_disjoint (by
    have hv := congrArg Fin.val hEF
    simp at hv
    have := e.isLt
    omega) q hG1 e.castSucc x he'
  apply hdis
  rw [hnext]
  exact hf'

private theorem adjacent_interiors_disjoint_reverse
    (hG1 : cyclicNoncollinear q) (e f : Fin (n + 1))
    (hFE : f.succ = e.castSucc) (x : PlanarPoint ℝ)
    (hf : ActiveArc.edgeInterior q f x) (he : ActiveArc.edgeInterior q e x) : False := by
  exact adjacent_interiors_disjoint_forward q hG1 f e hFE x hf he

/-- For a fixed pair of distinct actual physical-edge labels, interior crossing
is unchanged in a full configuration-space neighborhood of a Regular G1 arc. -/
theorem eventually_crossing_iff (hR : ActiveArc.Regular q) (hG1 : cyclicNoncollinear q)
    (e f : Fin (n + 1)) (hef : e ≠ f) :
    ∀ᶠ r in 𝓝 q,
      (∃ x, ActiveArc.edgeInterior q e x ∧ ActiveArc.edgeInterior q f x) ↔
      (∃ x, ActiveArc.edgeInterior r e x ∧ ActiveArc.edgeInterior r f x) := by
  by_cases hx : ∃ x, ActiveArc.edgeInterior q e x ∧ ActiveArc.edgeInterior q f x
  · filter_upwards [eventually_crossing_of_crossing q hR e f hef hx] with r hr
    exact ⟨fun _ => hr, fun _ => hx⟩
  · by_cases hadj : physicalEdgesAdjacent e f
    · filter_upwards [eventually_regular_G1 q hR hG1] with r hnear
      refine ⟨fun hh => False.elim (hx hh), ?_⟩
      rintro ⟨x, he, hf⟩
      rcases hadj with hef' | hfe'
      · exact False.elim (adjacent_interiors_disjoint_forward r hnear.2 e f hef' x he hf)
      · exact False.elim (adjacent_interiors_disjoint_reverse r hnear.2 e f hfe' x hf he)
    · have hzero := no_closed_pair_of_no_crossing q hR hG1 e f hef hadj hx
      filter_upwards [eventually_no_two_physical_closed q e f hzero] with r hr
      refine ⟨fun hh => False.elim (hx hh), ?_⟩
      rintro ⟨x, he, hf⟩
      obtain ⟨s, hs0, hs1, hxs⟩ := he
      obtain ⟨t, ht0, ht1, hxt⟩ := hf
      exact False.elim (hr ⟨x, ⟨s, le_of_lt hs0, le_of_lt hs1, hxs⟩,
        ⟨t, le_of_lt ht0, le_of_lt ht1, hxt⟩⟩)

/-- A single neighborhood works for all distinct physical edge pairs. -/
theorem eventually_all_crossing_iff (hR : ActiveArc.Regular q) (hG1 : cyclicNoncollinear q) :
    ∀ᶠ r in 𝓝 q, ∀ e f : Fin (n + 1), e ≠ f →
      ((∃ x, ActiveArc.edgeInterior q e x ∧ ActiveArc.edgeInterior q f x) ↔
        (∃ x, ActiveArc.edgeInterior r e x ∧ ActiveArc.edgeInterior r f x)) := by
  apply Filter.eventually_all.mpr
  intro e
  apply Filter.eventually_all.mpr
  intro f
  by_cases hef : e = f
  · exact Filter.Eventually.of_forall (fun _ h => False.elim (h hef))
  · filter_upwards [eventually_crossing_iff q hR hG1 e f hef] with r hr
    exact fun _ => hr

end DirectGLSSW.ActiveArc.ConfigurationLocality



