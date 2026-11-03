import DirectGLSSW.ShortEdgeGenericity
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

namespace DirectGLSSW.ShortEdgeGenericity

theorem exists_nonincident_edge_clearance {n : ℕ} (hn : 3 ≤ n)
    (q : Fin n → PlanarPoint ℝ) (hq : cyclicNoncollinear q) (a : Fin n) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ e : Fin n, e ≠ a → cyclicSuccessor e ≠ a →
      ∀ x : PlanarPoint ℝ, dist x (q a) < δ → ¬ edgeClosed q e x
  := by
  let I : Set ℝ := Set.Icc 0 1
  let E := {e : Fin n // e ≠ a ∧ cyclicSuccessor e ≠ a}
  let edgePoint : (E × ℝ) → PlanarPoint ℝ := fun z =>
    affinePoint (q z.1.1) (q (cyclicSuccessor z.1.1)) z.2
  have hI : IsCompact I := isCompact_Icc
  have hparams : IsCompact ((Set.univ : Set E) ×ˢ I) :=
    Set.finite_univ.isCompact.prod hI
  have hqleft : Continuous (fun z : E × ℝ => q z.1.1) := by
    exact (continuous_of_discreteTopology (f := q)).comp
      (continuous_subtype_val.comp continuous_fst)
  have hqright : Continuous (fun z : E × ℝ => q (cyclicSuccessor z.1.1)) := by
    exact (continuous_of_discreteTopology
      (f := fun e : Fin n => q (cyclicSuccessor e))).comp
      (continuous_subtype_val.comp continuous_fst)
  have hparam : Continuous (fun z : E × ℝ => z.2) := continuous_snd
  have hedgePoint : Continuous edgePoint := by
    dsimp [edgePoint]
    exact (hqleft.fst.add (hparam.mul (hqright.fst.sub hqleft.fst))).prodMk
      (hqleft.snd.add (hparam.mul (hqright.snd.sub hqleft.snd)))
  let K : Set (PlanarPoint ℝ) := edgePoint '' ((Set.univ : Set E) ×ˢ I)
  have hK : IsCompact K := by
    exact hparams.image hedgePoint
  have hcenter : q a ∉ K := by
    rintro ⟨⟨e, t⟩, ⟨_, ht⟩, hEq⟩
    rcases e with ⟨e, he, hs⟩
    have hclosed : edgeClosed q e (q a) :=
      ⟨t, ht.1, ht.2, hEq.symm⟩
    have hdet := cyclic_vertex_carrier_det_ne_zero hn q hq e a he.symm hs.symm
    rcases hclosed with ⟨u, hu0, hu1, huEq⟩
    apply hdet
    rw [huEq]
    simpa [cyclicTangent] using
      affinePoint_carrier_det_zero (q e) (q (cyclicSuccessor e)) u
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp
    (hK.isClosed.isOpen_compl.mem_nhds hcenter)
  refine ⟨δ, hδ, ?_⟩
  intro e he hs x hx hclosed
  have hxK : x ∈ K := by
    rcases hclosed with ⟨t, ht0, ht1, hEq⟩
    refine ⟨((⟨e, he, hs⟩ : E), t), ⟨trivial, ⟨ht0, ht1⟩⟩, ?_⟩
    exact hEq.symm
  have hnotK : x ∉ K := hball (Metric.mem_ball.mpr hx)
  exact hnotK hxK

end DirectGLSSW.ShortEdgeGenericity
