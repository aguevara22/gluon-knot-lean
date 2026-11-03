import LocalCrossingAlgebra

namespace DirectGLSSW.LocalCrossingTransport
open DirectGLSSW
open DirectGLSSW.ShortEdgeGenericity
open Filter Topology

private theorem continuous_affinePoint {α : Type*} [TopologicalSpace α]
    (a b : α → PlanarPoint ℝ) (t : α → ℝ)
    (ha : Continuous a) (hb : Continuous b) (ht : Continuous t) :
    Continuous (fun x => affinePoint (a x) (b x) (t x)) := by
  exact (ha.fst.add (ht.mul (hb.fst.sub ha.fst))).prodMk
    (ha.snd.add (ht.mul (hb.snd.sub ha.snd)))

/-- Absence of intersection of two closed edges persists locally. -/
theorem eventually_no_two_closed {n : ℕ}
    (Q : ℝ → Fin n → PlanarPoint ℝ) (e f : Fin n)
    (hQ : ∀ v, Continuous (fun t => Q t v))
    (hzero : ¬ ∃ x, edgeClosed (Q 0) e x ∧ edgeClosed (Q 0) f x) :
    ∀ᶠ t in 𝓝 (0 : ℝ), ¬ ∃ x, edgeClosed (Q t) e x ∧ edgeClosed (Q t) f x := by
  let I := Set.Icc (0 : ℝ) 1
  let T := I × I
  let P : ℝ × T → PlanarPoint ℝ := fun z =>
    affinePoint (Q z.1 e) (Q z.1 (cyclicSuccessor e)) z.2.1
  let F : ℝ × T → PlanarPoint ℝ := fun z =>
    affinePoint (Q z.1 f) (Q z.1 (cyclicSuccessor f)) z.2.2
  have hP : Continuous P := continuous_affinePoint _ _ _
    ((hQ e).comp continuous_fst) ((hQ (cyclicSuccessor e)).comp continuous_fst)
    (continuous_subtype_val.comp (continuous_fst.comp continuous_snd))
  have hF : Continuous F := continuous_affinePoint _ _ _
    ((hQ f).comp continuous_fst) ((hQ (cyclicSuccessor f)).comp continuous_fst)
    (continuous_subtype_val.comp (continuous_snd.comp continuous_snd))
  let B : Set (ℝ × T) := {z | P z = F z}
  have hB : IsClosed B := isClosed_eq hP hF
  have hprojected : IsClosed (Prod.fst '' B) := isClosedMap_fst_of_compactSpace B hB
  have hmem (t : ℝ) : t ∈ Prod.fst '' B ↔
      ∃ x, edgeClosed (Q t) e x ∧ edgeClosed (Q t) f x := by
    constructor
    · rintro ⟨⟨t', s, u⟩, hz, heps⟩
      change t' = t at heps
      subst t'
      change affinePoint (Q t e) (Q t (cyclicSuccessor e)) s =
        affinePoint (Q t f) (Q t (cyclicSuccessor f)) u at hz
      exact ⟨_, ⟨s, s.property.1, s.property.2, rfl⟩,
        ⟨u, u.property.1, u.property.2, hz⟩⟩
    · rintro ⟨x, ⟨s, hs0, hs1, hxs⟩, ⟨u, hu0, hu1, hxu⟩⟩
      exact ⟨(t, (⟨s, hs0, hs1⟩, ⟨u, hu0, hu1⟩)), hxs.symm.trans hxu, rfl⟩
  have hzero' : (0 : ℝ) ∈ (Prod.fst '' B)ᶜ := fun h => hzero ((hmem 0).mp h)
  filter_upwards [hprojected.isOpen_compl.mem_nhds hzero'] with t ht
  exact fun hx => ht ((hmem t).mpr hx)

/-- Strictly transverse open-segment intersection persists under any continuous motion. -/
theorem eventually_crossing_of_crossing {n : ℕ}
    (Q : ℝ → Fin n → PlanarPoint ℝ) (e f : Fin n)
    (hQ : ∀ v, Continuous (fun t => Q t v)) (h0 : CyclicGeneric (Q 0))
    (hef : e ≠ f)
    (hx : ∃ x, edgeInterior (Q 0) e x ∧ edgeInterior (Q 0) f x) :
    ∀ᶠ t in 𝓝 (0 : ℝ), ∃ x, edgeInterior (Q t) e x ∧ edgeInterior (Q t) f x := by
  obtain ⟨x, he, hf⟩ := hx
  have hD := cyclicTangent_det_ne_zero_of_intersection h0.size_ge_three (Q 0) h0.g1 e f hef x he hf
  obtain ⟨s, hs0, hs1, hxs⟩ := he
  obtain ⟨u, hu0, hu1, hxu⟩ := hf
  let S : ℝ → ℝ := fun t => leftParameter (Q t e) (Q t (cyclicSuccessor e))
    (Q t f) (Q t (cyclicSuccessor f))
  let U : ℝ → ℝ := fun t => rightParameter (Q t e) (Q t (cyclicSuccessor e))
    (Q t f) (Q t (cyclicSuccessor f))
  have hD' : planarDet (Q 0 (cyclicSuccessor e)-Q 0 e)
      (Q 0 (cyclicSuccessor f)-Q 0 f) ≠ 0 := hD
  have hS := leftParameter_continuousAt _ _ _ _ (hQ e) (hQ _) (hQ f) (hQ _) hD'
  have hU := rightParameter_continuousAt _ _ _ _ (hQ e) (hQ _) (hQ f) (hQ _) hD'
  have hS0 : S 0 = s := leftParameter_eq _ _ _ _ s u hD' (hxs.symm.trans hxu)
  have hU0 : U 0 = u := rightParameter_eq _ _ _ _ s u hD' (hxs.symm.trans hxu)
  have hs : ∀ᶠ t in 𝓝 (0 : ℝ), S t ∈ Set.Ioo (0 : ℝ) 1 :=
    hS.eventually (isOpen_Ioo.mem_nhds (by change 0 < S 0 ∧ S 0 < 1; rw [hS0]; exact ⟨hs0, hs1⟩))
  have hu : ∀ᶠ t in 𝓝 (0 : ℝ), U t ∈ Set.Ioo (0 : ℝ) 1 :=
    hU.eventually (isOpen_Ioo.mem_nhds (by change 0 < U 0 ∧ U 0 < 1; rw [hU0]; exact ⟨hu0, hu1⟩))
  have hDc : Continuous (fun t => planarDet (Q t (cyclicSuccessor e)-Q t e)
      (Q t (cyclicSuccessor f)-Q t f)) := by dsimp [planarDet]; fun_prop
  have hd : ∀ᶠ t in 𝓝 (0 : ℝ), planarDet (Q t (cyclicSuccessor e)-Q t e)
      (Q t (cyclicSuccessor f)-Q t f) ≠ 0 := hDc.continuousAt.eventually_ne hD'
  filter_upwards [hs, hu, hd] with t hst hut hdt
  exact ⟨affinePoint (Q t e) (Q t (cyclicSuccessor e)) (S t),
    ⟨S t, hst.1, hst.2, rfl⟩,
    ⟨U t, hut.1, hut.2, carrier_parameter_equation _ _ _ _ hdt⟩⟩

private theorem vertex_not_closed {n : ℕ} (q : Fin n → PlanarPoint ℝ)
    (hq : CyclicGeneric q) (e v : Fin n) (hve : v ≠ e)
    (hvs : v ≠ cyclicSuccessor e) : ¬ edgeClosed q e (q v) := by
  rintro ⟨s, _, _, hxs⟩
  apply cyclic_vertex_carrier_det_ne_zero hq.size_ge_three q hq.g1 e v hve hvs
  rw [hxs]
  exact affinePoint_carrier_det_zero _ _ _

private theorem closed_interior_of_not_endpoints {n : ℕ}
    (q : Fin n → PlanarPoint ℝ) (e : Fin n) (x : PlanarPoint ℝ)
    (hx : edgeClosed q e x) (hleft : x ≠ q e)
    (hright : x ≠ q (cyclicSuccessor e)) : edgeInterior q e x := by
  obtain ⟨s, hs0, hs1, hxs⟩ := hx
  have hsne0 : s ≠ 0 := by intro h; subst s; exact hleft (hxs.trans (affinePoint_zero _ _))
  have hsne1 : s ≠ 1 := by intro h; subst s; exact hright (hxs.trans (affinePoint_one _ _))
  exact ⟨s, lt_of_le_of_ne hs0 (Ne.symm hsne0), lt_of_le_of_ne hs1 hsne1, hxs⟩

/-- For nonincident edges, G1 converts closed intersection to open intersection. -/
theorem closed_crossing_implies_open {n : ℕ}
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q) (e f : Fin n)
    (hef : e ≠ f) (hesf : e ≠ cyclicSuccessor f)
    (hsef : cyclicSuccessor e ≠ f)
    (hx : ∃ x, edgeClosed q e x ∧ edgeClosed q f x) :
    ∃ x, edgeInterior q e x ∧ edgeInterior q f x := by
  obtain ⟨x, he, hf⟩ := hx
  have hss : cyclicSuccessor e ≠ cyclicSuccessor f :=
    fun h => hef (cyclicSuccessor_bijective.injective h)
  refine ⟨x, closed_interior_of_not_endpoints q e x he ?_ ?_,
    closed_interior_of_not_endpoints q f x hf ?_ ?_⟩
  · intro h; exact vertex_not_closed q hq f e hef hesf (h ▸ hf)
  · intro h; exact vertex_not_closed q hq f (cyclicSuccessor e) hsef hss (h ▸ hf)
  · intro h; exact vertex_not_closed q hq e f hef.symm hsef.symm (h ▸ he)
  · intro h; exact vertex_not_closed q hq e (cyclicSuccessor f) hesf.symm hss.symm (h ▸ he)

/-- G1 and G2 are preserved in a neighborhood of any generic labelled polygon. -/
theorem eventually_generic {n : ℕ}
    (Q : ℝ → Fin n → PlanarPoint ℝ)
    (hQ : ∀ v, Continuous (fun t => Q t v)) (h0 : CyclicGeneric (Q 0)) :
    ∀ᶠ t in 𝓝 (0 : ℝ), CyclicGeneric (Q t) := by
  obtain ⟨δ, hδ, hg⟩ := exists_local_cyclicGeneric_and_orderedSign_stability Q hQ h0
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hδ] with t ht
  exact (hg t (by simpa [Metric.mem_ball, Real.dist_eq] using ht)).1

/-- The truth of actual open-edge intersection is locally unchanged for each pair. -/
theorem eventually_crossing_iff {n : ℕ}
    (Q : ℝ → Fin n → PlanarPoint ℝ)
    (hQ : ∀ v, Continuous (fun t => Q t v)) (h0 : CyclicGeneric (Q 0))
    (e f : Fin n) (hef : e ≠ f) :
    ∀ᶠ t in 𝓝 (0 : ℝ),
      (∃ x, edgeInterior (Q 0) e x ∧ edgeInterior (Q 0) f x) ↔
      (∃ x, edgeInterior (Q t) e x ∧ edgeInterior (Q t) f x) := by
  by_cases hx : ∃ x, edgeInterior (Q 0) e x ∧ edgeInterior (Q 0) f x
  · filter_upwards [eventually_crossing_of_crossing Q e f hQ h0 hef hx] with t ht
    exact ⟨fun _ => ht, fun _ => hx⟩
  · by_cases hsf : cyclicSuccessor e = f
    · filter_upwards [eventually_generic Q hQ h0] with t ht
      refine ⟨fun h => False.elim (hx h), ?_⟩
      rintro ⟨x, he, hf⟩
      exact False.elim (cyclic_adjacent_interiors_disjoint h0.size_ge_three (Q t) ht.g1 e x he (hsf ▸ hf))
    · by_cases hse : cyclicSuccessor f = e
      · filter_upwards [eventually_generic Q hQ h0] with t ht
        refine ⟨fun h => False.elim (hx h), ?_⟩
        rintro ⟨x, he, hf⟩
        exact False.elim (cyclic_adjacent_interiors_disjoint h0.size_ge_three (Q t) ht.g1 f x hf (hse ▸ he))
      · have hclosed : ¬ ∃ x, edgeClosed (Q 0) e x ∧ edgeClosed (Q 0) f x :=
          fun h => hx (closed_crossing_implies_open (Q 0) h0 e f hef (Ne.symm hse) hsf h)
        filter_upwards [eventually_no_two_closed Q e f hQ hclosed] with t ht
        refine ⟨fun h => False.elim (hx h), ?_⟩
        rintro ⟨x, ⟨s, hs0, hs1, hxs⟩, ⟨u, hu0, hu1, hxu⟩⟩
        exact False.elim (ht ⟨x, ⟨s, hs0.le, hs1.le, hxs⟩, ⟨u, hu0.le, hu1.le, hxu⟩⟩)

/-- Actual crossing equivalence constructed from geometry, preserving both labels. -/
theorem exists_local_crossing_equiv {n : ℕ}
    (Q : ℝ → Fin n → PlanarPoint ℝ)
    (hQ : ∀ v, Continuous (fun t => Q t v)) (h0 : CyclicGeneric (Q 0)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t, |t| < δ →
      CyclicGeneric (Q t) ∧ ∃ E : PolygonCrossing (Q 0) ≃ PolygonCrossing (Q t),
        ∀ c, (E c).val = c.val := by
  classical
  have hpairs : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ e f : Fin n, e ≠ f →
      ((∃ x, edgeInterior (Q 0) e x ∧ edgeInterior (Q 0) f x) ↔
      (∃ x, edgeInterior (Q t) e x ∧ edgeInterior (Q t) f x)) := by
    apply Filter.eventually_all.mpr
    intro e
    apply Filter.eventually_all.mpr
    intro f
    by_cases hef : e = f
    · exact Filter.Eventually.of_forall (fun _ h => False.elim (h hef))
    · exact (eventually_crossing_iff Q hQ h0 e f hef).mono (fun _ h _ => h)
  have hall := (eventually_generic Q hQ h0).and hpairs
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hall
  refine ⟨δ, hδ, ?_⟩
  intro t ht
  obtain ⟨hgt, hp⟩ := hball (by simpa [Metric.mem_ball, Real.dist_eq] using ht)
  let f : PolygonCrossing (Q 0) → PolygonCrossing (Q t) := fun c =>
    ⟨c.val, c.property.1, (hp c.val.1 c.val.2 (ne_of_lt c.property.1)).mp c.property.2⟩
  let g : PolygonCrossing (Q t) → PolygonCrossing (Q 0) := fun c =>
    ⟨c.val, c.property.1, (hp c.val.1 c.val.2 (ne_of_lt c.property.1)).mpr c.property.2⟩
  exact ⟨hgt, ⟨f, g, fun c => Subtype.ext rfl, fun c => Subtype.ext rfl⟩, fun _ => rfl⟩






end DirectGLSSW.LocalCrossingTransport
