import DirectGLSSW.ShortEdgeContinuity
import DirectGLSSW.ShortEdgeGenericity
import DirectGLSSW.PolygonLocalMotion
import DirectGLSSW.PolygonSignExtensionality
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.Topology.MetricSpace.Pseudo.Constructions

namespace DirectGLSSW

open DirectGLSSW.ShortEdgeGenericity

private abbrev Config (n : ℕ) := Fin n → PlanarPoint ℝ
private abbrev Unit := Set.Icc (0 : ℝ) 1
private abbrev Triple (n : ℕ) := Fin n × Fin n × Fin n

private theorem continuous_affinePoint_cfg {α : Type*} [TopologicalSpace α]
    (a b : α → PlanarPoint ℝ) (t : α → ℝ)
    (ha : Continuous a) (hb : Continuous b) (ht : Continuous t) :
    Continuous (fun x => affinePoint (a x) (b x) (t x)) := by
  exact (ha.fst.add (ht.mul (hb.fst.sub ha.fst))).prodMk
    (ha.snd.add (ht.mul (hb.snd.sub ha.snd)))

private theorem no_three_closed_edges_open {n : ℕ} (e f g : Fin n)
    (hef : e ≠ f) (hfg : f ≠ g) (heg : e ≠ g) :
    IsOpen {q : Config n | ¬ ∃ x : PlanarPoint ℝ,
      edgeClosed q e x ∧ edgeClosed q f x ∧ edgeClosed q g x} := by
  let T := Unit × Unit × Unit
  let A : Config n × T → PlanarPoint ℝ := fun z =>
    affinePoint (z.1 e) (z.1 (cyclicSuccessor e)) z.2.1
  let B : Config n × T → PlanarPoint ℝ := fun z =>
    affinePoint (z.1 f) (z.1 (cyclicSuccessor f)) z.2.2.1
  let C : Config n × T → PlanarPoint ℝ := fun z =>
    affinePoint (z.1 g) (z.1 (cyclicSuccessor g)) z.2.2.2
  have hA : Continuous A := continuous_affinePoint_cfg _ _ _
    ((continuous_apply e).comp continuous_fst)
    ((continuous_apply (cyclicSuccessor e)).comp continuous_fst)
    (continuous_subtype_val.comp (continuous_fst.comp continuous_snd))
  have hB : Continuous B := continuous_affinePoint_cfg _ _ _
    ((continuous_apply f).comp continuous_fst)
    ((continuous_apply (cyclicSuccessor f)).comp continuous_fst)
    (continuous_subtype_val.comp (continuous_fst.comp (continuous_snd.comp continuous_snd)))
  have hC : Continuous C := continuous_affinePoint_cfg _ _ _
    ((continuous_apply g).comp continuous_fst)
    ((continuous_apply (cyclicSuccessor g)).comp continuous_fst)
    (continuous_subtype_val.comp (continuous_snd.comp (continuous_snd.comp continuous_snd)))
  let Bad : Set (Config n × T) := {z | A z = B z ∧ A z = C z}
  have hBad : IsClosed Bad := (isClosed_eq hA hB).inter (isClosed_eq hA hC)
  have hproj : IsClosed (Prod.fst '' Bad) := isClosedMap_fst_of_compactSpace Bad hBad
  have hmem (q : Config n) : q ∈ Prod.fst '' Bad ↔
      ∃ x : PlanarPoint ℝ, edgeClosed q e x ∧ edgeClosed q f x ∧ edgeClosed q g x := by
    constructor
    · rintro ⟨⟨q', s, t, u⟩, hbad, hq⟩
      change q' = q at hq
      subst q'
      change affinePoint (q e) (q (cyclicSuccessor e)) s =
          affinePoint (q f) (q (cyclicSuccessor f)) t ∧
        affinePoint (q e) (q (cyclicSuccessor e)) s =
          affinePoint (q g) (q (cyclicSuccessor g)) u at hbad
      exact ⟨affinePoint (q e) (q (cyclicSuccessor e)) s,
        ⟨s, s.property.1, s.property.2, rfl⟩,
        ⟨t, t.property.1, t.property.2, hbad.1⟩,
        ⟨u, u.property.1, u.property.2, hbad.2⟩⟩
    · rintro ⟨x, ⟨s, hs0, hs1, hxs⟩, ⟨t, ht0, ht1, hxt⟩, ⟨u, hu0, hu1, hxu⟩⟩
      refine ⟨(q, (⟨s, hs0, hs1⟩, ⟨t, ht0, ht1⟩, ⟨u, hu0, hu1⟩)), ?_, rfl⟩
      change affinePoint (q e) (q (cyclicSuccessor e)) s =
          affinePoint (q f) (q (cyclicSuccessor f)) t ∧
        affinePoint (q e) (q (cyclicSuccessor e)) s =
          affinePoint (q g) (q (cyclicSuccessor g)) u
      exact ⟨hxs.symm.trans hxt, hxs.symm.trans hxu⟩
  have heq : {q : Config n | ¬ ∃ x : PlanarPoint ℝ, edgeClosed q e x ∧ edgeClosed q f x ∧ edgeClosed q g x} =
      (Prod.fst '' Bad)ᶜ := by
    ext q
    simp [hmem]
  rw [heq]
  exact isOpen_compl_iff.mpr hproj

private def signGood {n : ℕ} (P : Config n) (tr : Triple n) : Set (Config n) :=
  if h : tr.1 ≠ tr.2.1 ∧ tr.2.1 ≠ tr.2.2 ∧ tr.1 ≠ tr.2.2 then
    let f : Config n → ℝ := fun q => planarDet (q tr.2.1 - q tr.2.2) (q tr.1 - q tr.2.2)
    if 0 < f P then f ⁻¹' Set.Ioi (0 : ℝ) else f ⁻¹' Set.Iio (0 : ℝ)
  else Set.univ

private theorem signGood_open {n : ℕ} (P : Config n) (tr : Triple n)
    (hP : CyclicGeneric P) : IsOpen (signGood P tr) := by
  classical
  by_cases h : tr.1 ≠ tr.2.1 ∧ tr.2.1 ≠ tr.2.2 ∧ tr.1 ≠ tr.2.2
  · let f : Config n → ℝ := fun q => planarDet (q tr.2.1 - q tr.2.2) (q tr.1 - q tr.2.2)
    have hf : Continuous f := by
      dsimp [f, planarDet]
      fun_prop
    have hf0 : f P ≠ 0 := hP.g1 tr.1 tr.2.1 tr.2.2 h.1 h.2.1 h.2.2
    dsimp [signGood]
    split_ifs with hp
    all_goals first
      | exact isOpen_Ioi.preimage hf
      | exact isOpen_Iio.preimage hf
      | exact False.elim (hp h)
  · simp [signGood, h]

private theorem signGood_mem {n : ℕ} (P Q : Config n) (tr : Triple n)
    (hP : CyclicGeneric P) (hQ : Q ∈ signGood P tr) :
    tr.1 ≠ tr.2.1 → tr.2.1 ≠ tr.2.2 → tr.1 ≠ tr.2.2 →
      scalarSignValue (planarDet (Q tr.2.1 - Q tr.2.2) (Q tr.1 - Q tr.2.2)) =
      scalarSignValue (planarDet (P tr.2.1 - P tr.2.2) (P tr.1 - P tr.2.2)) := by
  classical
  intro h1 h2 h3
  let f : Config n → ℝ := fun q => planarDet (q tr.2.1 - q tr.2.2) (q tr.1 - q tr.2.2)
  have h0 : f P ≠ 0 := hP.g1 tr.1 tr.2.1 tr.2.2 h1 h2 h3
  have hmem : Q ∈ (if 0 < f P then f ⁻¹' Set.Ioi (0 : ℝ) else f ⁻¹' Set.Iio (0 : ℝ)) := by
    simpa [signGood, h1, h2, h3, f] using hQ
  by_cases hp : 0 < f P
  · have hq : 0 < f Q := by simpa only [if_pos hp, Set.mem_preimage, Set.mem_Ioi] using hmem
    change scalarSignValue (f Q) = scalarSignValue (f P)
    simp [scalarSignValue, ne_of_gt hp, ne_of_gt hq, not_lt_of_gt hp, not_lt_of_gt hq]
  · have hn : f P < 0 := lt_of_le_of_ne (le_of_not_gt hp) h0
    have hq : f Q < 0 := by simpa [hp] using hmem
    change scalarSignValue (f Q) = scalarSignValue (f P)
    simp [scalarSignValue, ne_of_lt hn, ne_of_lt hq, hn, hq]

theorem exists_configurationNeighborhood_cyclicGeneric_and_signs_amplitude
    {n : ℕ} (P : Fin n → PlanarPoint ℝ) (hP : CyclicGeneric P) :
    ∃ η : ℝ, 0 < η ∧ ∀ Q : Fin n → PlanarPoint ℝ,
      (∀ i : Fin n,
        |(Q i).1 - (P i).1| < η ∧ |(Q i).2 - (P i).2| < η) →
      ∃ hQ : CyclicGeneric Q,
        (∀ i k j : Fin n, i ≠ k → k ≠ j → i ≠ j →
          scalarSignValue (planarDet (Q k - Q j) (Q i - Q j)) =
            scalarSignValue (planarDet (P k - P j) (P i - P j))) ∧
        polygonAmplitude Q hQ = polygonAmplitude P hP := by
  classical
  let triples : Finset (Triple n) := Finset.univ
  let Good (tr : Triple n) : Set (Config n) :=
    signGood P tr ∩ if h : tr.1 ≠ tr.2.1 ∧ tr.2.1 ≠ tr.2.2 ∧ tr.1 ≠ tr.2.2 then
      {q | ¬ ∃ x : PlanarPoint ℝ,
        edgeClosed q tr.1 x ∧ edgeClosed q tr.2.1 x ∧ edgeClosed q tr.2.2 x}
    else Set.univ
  let O : Set (Config n) := ⋂ tr ∈ triples, Good tr
  have hOopen : IsOpen O := isOpen_biInter_finset fun tr _ => by
    dsimp [Good]
    by_cases h : tr.1 ≠ tr.2.1 ∧ tr.2.1 ≠ tr.2.2 ∧ tr.1 ≠ tr.2.2
    · simpa [Good, h] using (signGood_open P tr hP).inter
        (no_three_closed_edges_open tr.1 tr.2.1 tr.2.2 h.1 h.2.1 h.2.2)
    · simpa [Good, h] using (signGood_open P tr hP).inter isOpen_univ
  have hPmem : P ∈ O := by
    simp only [O, Set.mem_iInter]
    intro tr _
    change P ∈ signGood P tr ∧ P ∈ (if h : tr.1 ≠ tr.2.1 ∧ tr.2.1 ≠ tr.2.2 ∧ tr.1 ≠ tr.2.2 then
      {q | ¬ ∃ x : PlanarPoint ℝ, edgeClosed q tr.1 x ∧ edgeClosed q tr.2.1 x ∧ edgeClosed q tr.2.2 x} else Set.univ)
    constructor
    · by_cases h : tr.1 ≠ tr.2.1 ∧ tr.2.1 ≠ tr.2.2 ∧ tr.1 ≠ tr.2.2
      · let f : Config n → ℝ := fun q => planarDet (q tr.2.1 - q tr.2.2) (q tr.1 - q tr.2.2)
        have h0 : f P ≠ 0 := hP.g1 tr.1 tr.2.1 tr.2.2 h.1 h.2.1 h.2.2
        by_cases hp : 0 < f P
        · simp [signGood, h, f, hp]
        · have hn : f P < 0 := lt_of_le_of_ne (le_of_not_gt hp) h0
          simp [signGood, h, f, hp, hn]
      · simp [signGood, h]
    · by_cases h : tr.1 ≠ tr.2.1 ∧ tr.2.1 ≠ tr.2.2 ∧ tr.1 ≠ tr.2.2
      · have hNo : ¬ ∃ x : PlanarPoint ℝ,
            edgeClosed P tr.1 x ∧ edgeClosed P tr.2.1 x ∧ edgeClosed P tr.2.2 x := by
          intro hbad
          rcases hbad with ⟨x, he, hf, hg⟩
          exact cyclic_no_three_closed_edges P hP tr.1 tr.2.1 tr.2.2 x h.1 h.2.1 h.2.2 ⟨he, hf, hg⟩
        simpa [h] using hNo
      · simp [h]
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp (hOopen.mem_nhds hPmem)
  let η := δ / 2
  have hη : 0 < η := by dsimp [η]; linarith
  refine ⟨η, hη, ?_⟩
  intro Q hcoords
  have hdistPoint (i : Fin n) : dist (Q i) (P i) < η := by
    have h := hcoords i
    rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
    rw [max_lt_iff]
    exact ⟨by simpa [abs_sub_comm] using h.1, by simpa [abs_sub_comm] using h.2⟩
  have hdist : dist Q P < δ := by
    rw [dist_pi_lt_iff (by linarith : 0 < δ)]
    intro i
    exact lt_trans (hdistPoint i) (by dsimp [η]; linarith)
  have hQmem : Q ∈ O := hball (by simpa [Metric.mem_ball, Real.dist_eq] using hdist)
  have hQmem' : ∀ tr ∈ triples, Q ∈ Good tr := by simpa [O] using hQmem
  have hQgood (tr : Triple n) : Q ∈ Good tr := hQmem' tr (Finset.mem_univ _)
  have hG1 : cyclicNoncollinear Q := by
    intro i k j hik hkj hij hzero
    have hsign := signGood_mem P Q (i, k, j) hP (hQgood (i, k, j)).1 hik hkj hij
    have hbase : planarDet (P k - P j) (P i - P j) ≠ 0 := hP.g1 i k j hik hkj hij
    have hs0 : scalarSignValue (planarDet (P k - P j) (P i - P j)) ≠ 0 := by
      rw [scalarSignValue_eq_nonzeroScalarSign _ hbase]
      cases nonzeroScalarSign (planarDet (P k - P j) (P i - P j)) hbase <;> simp [Sign.value]
    apply hs0
    rw [← hsign]
    simp [hzero, scalarSignValue]
  have hG2 : cyclicNoTripleIntersections Q := by
    intro e f g x hef hfg heg hbad
    rcases hbad with ⟨he, hf, hg⟩
    have hclosed (i : Fin n) (x : PlanarPoint ℝ) (hi : edgeInterior Q i x) : edgeClosed Q i x := by
      obtain ⟨t, ht0, ht1, htx⟩ := hi
      exact ⟨t, le_of_lt ht0, le_of_lt ht1, htx⟩
    have hNo : ¬ ∃ y : PlanarPoint ℝ,
        edgeClosed Q e y ∧ edgeClosed Q f y ∧ edgeClosed Q g y := by
      simpa [Good, hef, hfg, heg] using (hQgood (e, f, g)).2
    exact hNo ⟨x, hclosed e x he, hclosed f x hf, hclosed g x hg⟩
  let hQ : CyclicGeneric Q := ⟨hP.size_ge_three, hG1, hG2⟩
  have hsign : ∀ i k j, i ≠ k → k ≠ j → i ≠ j →
      scalarSignValue (planarDet (Q k - Q j) (Q i - Q j)) =
        scalarSignValue (planarDet (P k - P j) (P i - P j)) := by
    intro i k j hik hkj hij
    exact signGood_mem P Q (i, k, j) hP
      ((hQgood (i, k, j)).1) hik hkj hij
  exact ⟨hQ, hsign, (polygonAmplitude_eq_of_oriented_triple_signs P Q hP hQ (by
    intro i k j hik hkj hij
    exact (hsign i k j hik hkj hij).symm)).symm⟩



end DirectGLSSW
