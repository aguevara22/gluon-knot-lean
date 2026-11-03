import DirectGLSSW.ShortEdgeGenericity
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

namespace DirectGLSSW.ShortEdgeGenericity

private theorem continuous_affinePoint {α : Type*} [TopologicalSpace α]
    (a b : α → PlanarPoint ℝ) (t : α → ℝ)
    (ha : Continuous a) (hb : Continuous b) (ht : Continuous t) :
    Continuous (fun x => affinePoint (a x) (b x) (t x)) := by
  exact (ha.fst.add (ht.mul (hb.fst.sub ha.fst))).prodMk
    (ha.snd.add (ht.mul (hb.snd.sub ha.snd)))

theorem exists_no_three_closed_radius {n : ℕ}
    (Q : ℝ → Fin n → PlanarPoint ℝ) (e f g : Fin n)
    (hQ : ∀ v : Fin n, Continuous (fun ε => Q ε v))
    (hzero : ¬ ∃ x : PlanarPoint ℝ,
      edgeClosed (Q 0) e x ∧ edgeClosed (Q 0) f x ∧ edgeClosed (Q 0) g x) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, |ε| < δ →
      ¬ ∃ x : PlanarPoint ℝ,
        edgeClosed (Q ε) e x ∧ edgeClosed (Q ε) f x ∧ edgeClosed (Q ε) g x := by
  let I := Set.Icc (0 : ℝ) 1
  let T := I × I × I
  let P : ℝ × T → PlanarPoint ℝ := fun z =>
    affinePoint (Q z.1 e) (Q z.1 (cyclicSuccessor e)) z.2.1
  let F : ℝ × T → PlanarPoint ℝ := fun z =>
    affinePoint (Q z.1 f) (Q z.1 (cyclicSuccessor f)) z.2.2.1
  let G : ℝ × T → PlanarPoint ℝ := fun z =>
    affinePoint (Q z.1 g) (Q z.1 (cyclicSuccessor g)) z.2.2.2
  have hP : Continuous P := continuous_affinePoint _ _ _
    ((hQ e).comp continuous_fst) ((hQ (cyclicSuccessor e)).comp continuous_fst)
    (continuous_subtype_val.comp (continuous_fst.comp continuous_snd))
  have hF : Continuous F := continuous_affinePoint _ _ _
    ((hQ f).comp continuous_fst) ((hQ (cyclicSuccessor f)).comp continuous_fst)
    (continuous_subtype_val.comp (continuous_fst.comp (continuous_snd.comp continuous_snd)))
  have hG : Continuous G := continuous_affinePoint _ _ _
    ((hQ g).comp continuous_fst) ((hQ (cyclicSuccessor g)).comp continuous_fst)
    (continuous_subtype_val.comp (continuous_snd.comp (continuous_snd.comp continuous_snd)))
  let B : Set (ℝ × T) := {z | P z = F z ∧ P z = G z}
  have hB : IsClosed B := (isClosed_eq hP hF).inter (isClosed_eq hP hG)
  have hprojected : IsClosed (Prod.fst '' B) := isClosedMap_fst_of_compactSpace B hB
  have hmem (ε : ℝ) : ε ∈ Prod.fst '' B ↔
      ∃ x : PlanarPoint ℝ,
        edgeClosed (Q ε) e x ∧ edgeClosed (Q ε) f x ∧ edgeClosed (Q ε) g x := by
    constructor
    · rintro ⟨⟨ε', s, t, u⟩, hz, heps⟩
      change ε' = ε at heps
      subst ε'
      change affinePoint (Q ε e) (Q ε (cyclicSuccessor e)) s =
          affinePoint (Q ε f) (Q ε (cyclicSuccessor f)) t ∧
        affinePoint (Q ε e) (Q ε (cyclicSuccessor e)) s =
          affinePoint (Q ε g) (Q ε (cyclicSuccessor g)) u at hz
      exact ⟨affinePoint (Q ε e) (Q ε (cyclicSuccessor e)) s,
        ⟨s, s.property.1, s.property.2, rfl⟩,
        ⟨t, t.property.1, t.property.2, hz.1⟩,
        ⟨u, u.property.1, u.property.2, hz.2⟩⟩
    · rintro ⟨x, ⟨s, hs0, hs1, hxs⟩, ⟨t, ht0, ht1, hxt⟩, ⟨u, hu0, hu1, hxu⟩⟩
      refine ⟨(ε, (⟨s, hs0, hs1⟩, ⟨t, ht0, ht1⟩, ⟨u, hu0, hu1⟩)), ?_, rfl⟩
      exact ⟨hxs.symm.trans hxt, hxs.symm.trans hxu⟩
  have hzero' : (0 : ℝ) ∈ (Prod.fst '' B)ᶜ := by
    intro h
    exact hzero ((hmem 0).mp h)
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp (hprojected.isOpen_compl.mem_nhds hzero')
  refine ⟨δ, hδ, ?_⟩
  intro ε hε hbad
  have hεball : ε ∈ Metric.ball (0 : ℝ) δ := by
    simpa [Metric.mem_ball, Real.dist_eq] using hε
  exact hball hεball ((hmem ε).mpr hbad)

end DirectGLSSW.ShortEdgeGenericity
