import DirectGLSSW.PolygonLocalAmplitude

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace DirectGLSSW.PolygonGermStability
open Filter
open DirectGLSSW.ShortEdgeGenericity
open scoped Topology

private theorem continuous_affinePoint {α : Type*} [TopologicalSpace α]
    (a b : α → PlanarPoint ℝ) (t : α → ℝ)
    (ha : Continuous a) (hb : Continuous b) (ht : Continuous t) :
    Continuous (fun x => affinePoint (a x) (b x) (t x)) := by
  exact (ha.fst.add (ht.mul (hb.fst.sub ha.fst))).prodMk
    (ha.snd.add (ht.mul (hb.snd.sub ha.snd)))

theorem isOpen_no_three_closed {n : ℕ} (e f g : Fin n) :
    IsOpen {q : Fin n → PlanarPoint ℝ | ¬ ∃ x,
      edgeClosed q e x ∧ edgeClosed q f x ∧ edgeClosed q g x} := by
  let I := Set.Icc (0 : ℝ) 1
  let T := I × I × I
  let C := Fin n → PlanarPoint ℝ
  let P : C × T → PlanarPoint ℝ := fun z =>
    affinePoint (z.1 e) (z.1 (cyclicSuccessor e)) z.2.1
  let F : C × T → PlanarPoint ℝ := fun z =>
    affinePoint (z.1 f) (z.1 (cyclicSuccessor f)) z.2.2.1
  let G : C × T → PlanarPoint ℝ := fun z =>
    affinePoint (z.1 g) (z.1 (cyclicSuccessor g)) z.2.2.2
  have hP : Continuous P := continuous_affinePoint _ _ _
    ((continuous_apply e).comp continuous_fst)
    ((continuous_apply (cyclicSuccessor e)).comp continuous_fst)
    (continuous_subtype_val.comp (continuous_fst.comp continuous_snd))
  have hF : Continuous F := continuous_affinePoint _ _ _
    ((continuous_apply f).comp continuous_fst)
    ((continuous_apply (cyclicSuccessor f)).comp continuous_fst)
    (continuous_subtype_val.comp (continuous_fst.comp (continuous_snd.comp continuous_snd)))
  have hG : Continuous G := continuous_affinePoint _ _ _
    ((continuous_apply g).comp continuous_fst)
    ((continuous_apply (cyclicSuccessor g)).comp continuous_fst)
    (continuous_subtype_val.comp (continuous_snd.comp (continuous_snd.comp continuous_snd)))
  let B : Set (C × T) := {z | P z = F z ∧ P z = G z}
  have hB : IsClosed B := (isClosed_eq hP hF).inter (isClosed_eq hP hG)
  have hp : IsClosed (Prod.fst '' B) := isClosedMap_fst_of_compactSpace B hB
  have hmem (q : C) : q ∈ Prod.fst '' B ↔ ∃ x,
      edgeClosed q e x ∧ edgeClosed q f x ∧ edgeClosed q g x := by
    constructor
    · rintro ⟨⟨q', s, t, u⟩, hz, hq⟩
      change q' = q at hq
      subst q'
      change affinePoint (q e) (q (cyclicSuccessor e)) s =
          affinePoint (q f) (q (cyclicSuccessor f)) t ∧
        affinePoint (q e) (q (cyclicSuccessor e)) s =
          affinePoint (q g) (q (cyclicSuccessor g)) u at hz
      exact ⟨affinePoint (q e) (q (cyclicSuccessor e)) s,
        ⟨s, s.property.1, s.property.2, rfl⟩,
        ⟨t, t.property.1, t.property.2, hz.1⟩,
        ⟨u, u.property.1, u.property.2, hz.2⟩⟩
    · rintro ⟨x, ⟨s, hs0, hs1, hxs⟩, ⟨t, ht0, ht1, hxt⟩, ⟨u, hu0, hu1, hxu⟩⟩
      refine ⟨(q, (⟨s, hs0, hs1⟩, ⟨t, ht0, ht1⟩, ⟨u, hu0, hu1⟩)), ?_, rfl⟩
      exact ⟨hxs.symm.trans hxt, hxs.symm.trans hxu⟩
  have heq : {q : C | ¬ ∃ x, edgeClosed q e x ∧ edgeClosed q f x ∧
      edgeClosed q g x} = (Prod.fst '' B)ᶜ := by
    ext q
    exact not_congr (hmem q).symm
  rw [heq]
  exact hp.isOpen_compl

theorem eventually_cyclicGeneric {α : Type*} [TopologicalSpace α] {a : α} {n : ℕ}
    (Q : α → Fin n → PlanarPoint ℝ)
    (hQ : ∀ v, ContinuousAt (fun x => Q x v) a) (h0 : CyclicGeneric (Q a)) :
    ∀ᶠ x in 𝓝 a, CyclicGeneric (Q x) := by
  classical
  have hQall : ContinuousAt Q a := continuousAt_pi.mpr hQ
  have hg1 : ∀ i k j : Fin n, ∀ᶠ x in 𝓝 a,
      i ≠ k → k ≠ j → i ≠ j →
      planarDet (Q x k - Q x j) (Q x i - Q x j) ≠ 0 := by
    intro i k j
    by_cases hd : i ≠ k ∧ k ≠ j ∧ i ≠ j
    · have hc : ContinuousAt (fun x => planarDet (Q x k - Q x j) (Q x i - Q x j)) a := by
        unfold planarDet
        exact (((hQ k).fst.sub (hQ j).fst).mul ((hQ i).snd.sub (hQ j).snd)).sub
          (((hQ k).snd.sub (hQ j).snd).mul ((hQ i).fst.sub (hQ j).fst))
      have he := hc.eventually (isOpen_compl_singleton.mem_nhds (h0.g1 i k j hd.1 hd.2.1 hd.2.2))
      exact he.mono (fun x hx _ _ _ => hx)
    · exact Filter.Eventually.of_forall (fun _ hi hk hj => False.elim (hd ⟨hi,hk,hj⟩))
  have hG1 : ∀ᶠ x in 𝓝 a, cyclicNoncollinear (Q x) :=
    Filter.eventually_all.mpr (fun i => Filter.eventually_all.mpr (fun k =>
      Filter.eventually_all.mpr (fun j => hg1 i k j)))
  have hc : ∀ e f g : Fin n, ∀ᶠ x in 𝓝 a, ShortEdgeGenericity.SeparatedTriple e f g →
      ¬ ∃ y, edgeClosed (Q x) e y ∧ edgeClosed (Q x) f y ∧ edgeClosed (Q x) g y := by
    intro e f g
    by_cases hs : ShortEdgeGenericity.SeparatedTriple e f g
    · have hbase : ¬ ∃ y, edgeClosed (Q a) e y ∧ edgeClosed (Q a) f y ∧ edgeClosed (Q a) g y := by
        rintro ⟨y, he, hf, hg⟩
        exact ShortEdgeGenericity.cyclic_no_three_closed_edges (Q a) h0 e f g y
          hs.1 hs.2.1 hs.2.2.1 ⟨he, hf, hg⟩
      have he := hQall.eventually ((isOpen_no_three_closed e f g).mem_nhds hbase)
      exact he.mono (fun x hx _ => hx)
    · exact Filter.Eventually.of_forall (fun _ h => False.elim (hs h))
  have hClosed : ∀ᶠ x in 𝓝 a, ∀ e f g : Fin n, ShortEdgeGenericity.SeparatedTriple e f g →
      ¬ ∃ y, edgeClosed (Q x) e y ∧ edgeClosed (Q x) f y ∧ edgeClosed (Q x) g y :=
    Filter.eventually_all.mpr (fun e => Filter.eventually_all.mpr (fun f =>
      Filter.eventually_all.mpr (fun g => hc e f g)))
  filter_upwards [hG1, hClosed] with x hG1 hClosed
  refine ⟨h0.size_ge_three, hG1, ?_⟩
  intro e f g y hef hfg heg hbad
  rcases hbad with ⟨he,hf,hg⟩
  have hnonadj : ∀ i j : Fin n, edgeInterior (Q x) i y → edgeInterior (Q x) j y →
      cyclicSuccessor i ≠ j := by
    intro i j hi hj hij
    subst j
    exact cyclic_adjacent_interiors_disjoint h0.size_ge_three (Q x) hG1 i y hi hj
  have hsep : ShortEdgeGenericity.SeparatedTriple e f g :=
    ⟨hef,hfg,heg,hnonadj e f he hf,hnonadj f e hf he,hnonadj f g hf hg,
      hnonadj g f hg hf,hnonadj e g he hg,hnonadj g e hg he⟩
  have hclosed : ∀ i, edgeInterior (Q x) i y → edgeClosed (Q x) i y := by
    intro i hi
    obtain ⟨t,ht0,ht1,hxt⟩ := hi
    exact ⟨t,le_of_lt ht0,le_of_lt ht1,hxt⟩
  exact hClosed e f g hsep ⟨y,hclosed e he,hclosed f hf,hclosed g hg⟩

end DirectGLSSW.PolygonGermStability



