import SM.SingleControlCenters
import SM.UnorderedWallTriples
import SM.TripleCenter
import SM.GermNeighborhood

namespace SM

open MvPolynomial Filter Topology

noncomputable section

variable {n : ℕ} [NeZero n]

theorem concurrenceDet_order_identity (P : LabelledTuple n) (e f k : ZMod n)
    (hef : det (edge P e) (edge P f) ≠ 0) (hek : det (edge P e) (edge P k) ≠ 0) :
    concurrenceDet P e f k = -(edgeParameter P e f - edgeParameter P e k) *
      det (edge P e) (edge P f) * det (edge P e) (edge P k) := by
  have heq : -(edgeParameter P e f - edgeParameter P e k) *
        det (edge P e) (edge P f) * det (edge P e) (edge P k) =
      -det (P f - P e) (edge P f) * det (edge P e) (edge P k) +
        det (P k - P e) (edge P k) * det (edge P e) (edge P f) := by
    dsimp [edgeParameter, cramerFirst]
    field_simp [hef, hek] <;> ring
  rw [heq, concurrenceDet_formula]
  dsimp [edgeLineA, edgeLineB, edgeLineC, edge, det]
  ring

namespace WallGerm

variable (g : WallGerm n)

theorem signChanges_of_nonzero_factor {F ψ χ : LabelledTuple n → ℝ}
    (hF : g.SignChanges F) (hχ : ContinuousAt χ g.center) (hc : χ g.center ≠ 0)
    (hid : ∀ P, χ P ≠ 0 → F P = ψ P * χ P) : g.SignChanges ψ := by
  have hcont : ContinuousAt (fun t : g.Parameter => χ (g.curve t) * χ g.center)
      g.zeroParameter := (hχ.comp (f := g.curve) (x := g.zeroParameter) g.continuous_curve.continuousAt).mul continuousAt_const
  have hcc : 0 < χ g.center * χ g.center := mul_self_pos.mpr hc
  have hev : ∀ᶠ t in 𝓝 g.zeroParameter, 0 < χ (g.curve t) * χ g.center :=
    hcont.eventually (isOpen_Ioi.mem_nhds hcc)
  obtain ⟨η, hη, hηr, hηχ⟩ := (g.eventually_center_iff_radius _).mp hev
  obtain ⟨δ, hδ, hδr, hδF⟩ := hF
  refine ⟨min δ η, lt_min hδ hη, (min_le_left _ _).trans hδr, ?_⟩
  intro t ht
  have htδ := lt_of_lt_of_le ht (min_le_left δ η)
  have htη := lt_of_lt_of_le ht (min_le_right δ η)
  have hp := hηχ (g.sideTime true t) (by simpa [sideTime, abs_of_pos t.property.1] using htη)
  have hm := hηχ (g.sideTime false t) (by simpa [sideTime, abs_of_pos t.property.1] using htη)
  change 0 < χ (g.sideTuple true t).val * χ g.center at hp
  change 0 < χ (g.sideTuple false t).val * χ g.center at hm
  have hpne : χ (g.sideTuple true t).val ≠ 0 := (mul_ne_zero_iff.mp hp.ne').1
  have hmne : χ (g.sideTuple false t).val ≠ 0 := (mul_ne_zero_iff.mp hm.ne').1
  have hprod : 0 < χ (g.sideTuple true t).val * χ (g.sideTuple false t).val := by
    have hh := mul_pos hp hm
    have he : (χ (g.sideTuple true t).val * χ g.center) *
        (χ (g.sideTuple false t).val * χ g.center) =
        (χ (g.sideTuple true t).val * χ (g.sideTuple false t).val) *
          (χ g.center * χ g.center) := by ring
    rw [he] at hh
    exact (mul_pos_iff_of_pos_right hcc).mp hh
  have hh := hδF t htδ
  rw [hid _ hpne, hid _ hmne] at hh
  have he : (ψ (g.sideTuple true t).val * χ (g.sideTuple true t).val) *
      (ψ (g.sideTuple false t).val * χ (g.sideTuple false t).val) =
      (ψ (g.sideTuple true t).val * ψ (g.sideTuple false t).val) *
        (χ (g.sideTuple true t).val * χ (g.sideTuple false t).val) := by ring
  rw [he] at hh
  rcases mul_neg_iff.mp hh with hbad | hgood
  · exact (not_lt_of_gt hprod hbad.2).elim
  · exact hgood.1

theorem edge_control_signChanges_concurrence (v : EdgeControlName n)
    (h : g.SignChanges (fun P => eval (scalarCoordinates P) (namedControlPolynomial (.inr v))))
    (e f k : ZMod n) (hs : ({e, f, k} : Finset (ZMod n)) = v.val) :
    g.SignChanges (fun P => concurrenceDet P e f k) := by
  have hcard : ({e, f, k} : Finset (ZMod n)).card = 3 := by rw [hs]; exact v.property.1
  obtain ⟨hef, hek, hfk⟩ := Finset.card_triple_eq_three_iff.mp hcard
  let r := edgeRepresentative v
  rcases triple_value_eq_or_neg concurrencePolynomial concurrencePolynomial_cyclic
    concurrencePolynomial_swap_last r.first r.second r.third e f k hef hek hfk
    (hs.trans r.support_eq) with hF | hF
  · have he : (fun P : LabelledTuple n => concurrenceDet P e f k) =
        (fun P => eval (scalarCoordinates P) (namedControlPolynomial (.inr v))) := by
      funext P
      rw [← eval_concurrencePolynomial, hF]
      rfl
    rw [he]
    exact h
  · have he : (fun P : LabelledTuple n => concurrenceDet P e f k) =
        (fun P => -eval (scalarCoordinates P) (namedControlPolynomial (.inr v))) := by
      funext P
      rw [← eval_concurrencePolynomial, hF, map_neg]
      rfl
    rw [he]
    exact (g.signChanges_neg _).mpr h

theorem concurrence_signChanges_parameter_order (e f k : ZMod n)
    (hef : det (edge g.center e) (edge g.center f) ≠ 0)
    (hek : det (edge g.center e) (edge g.center k) ≠ 0)
    (h : g.SignChanges (fun P => concurrenceDet P e f k)) :
    g.SignChanges (fun P => edgeParameter P e f - edgeParameter P e k) := by
  let χ : LabelledTuple n → ℝ := fun P =>
    -det (edge P e) (edge P f) * det (edge P e) (edge P k)
  have hχ : ContinuousAt χ g.center :=
    (continuousAt_det (continuous_edge e).continuousAt (continuous_edge f).continuousAt).neg.mul
      (continuousAt_det (continuous_edge e).continuousAt (continuous_edge k).continuousAt)
  have hc : χ g.center ≠ 0 := mul_ne_zero (neg_ne_zero.mpr hef) hek
  apply g.signChanges_of_nonzero_factor h hχ hc
  intro P hP
  have hp : -det (edge P e) (edge P f) ≠ 0 ∧ det (edge P e) (edge P k) ≠ 0 :=
    mul_ne_zero_iff.mp hP
  rw [concurrenceDet_order_identity P e f k (neg_ne_zero.mp hp.1) hp.2]
  dsimp [χ]
  ring

theorem active_edge_control_tripleAt (hn : 3 ≤ n) (v : EdgeControlName n)
    (hz : g.pointZeros = ∅) (hc : g.concurrences = {v.val})
    (h : g.SignChanges (fun P => eval (scalarCoordinates P) (namedControlPolynomial (.inr v)))) :
    ∃ e f k, ({e, f, k} : Finset (ZMod n)) = v.val ∧ g.TripleAt e f k := by
  let r := edgeRepresentative v
  let e := r.first
  let f := r.second
  let k := r.third
  have hs : ({e, f, k} : Finset (ZMod n)) = v.val := r.support_eq.symm
  have hc' : concurrenceTriples g.center = {{e, f, k}} := by rwa [hs]
  have h1 : G1 g.center := (g.pointZeros_empty_iff).mp hz
  obtain ⟨hremEF, hremFK, hremEK, q, hqE, hqF, hqK⟩ := uniqueTriple_data hc'
  have hef := crossing_edgeParameter_det_ne_zero hn h1
    (isCrossing_of_common_interiors hremEF hqE hqF)
  have hek := crossing_edgeParameter_det_ne_zero hn h1
    (isCrossing_of_common_interiors hremEK hqE hqK)
  have hfk := crossing_edgeParameter_det_ne_zero hn h1
    (isCrossing_of_common_interiors hremFK hqF hqK)
  have hfe : det (edge g.center f) (edge g.center e) ≠ 0 := by rw [det_swap]; exact neg_ne_zero.mpr hef
  have hke : det (edge g.center k) (edge g.center e) ≠ 0 := by rw [det_swap]; exact neg_ne_zero.mpr hek
  have hkf : det (edge g.center k) (edge g.center f) ≠ 0 := by rw [det_swap]; exact neg_ne_zero.mpr hfk
  have hsf : ({f, e, k} : Finset (ZMod n)) = v.val := by
    rw [← hs]
    ext i
    simp [or_comm, or_left_comm]
  have hsk : ({k, e, f} : Finset (ZMod n)) = v.val := by
    rw [← hs]
    ext i
    simp [or_comm, or_left_comm]
  refine ⟨e, f, k, hs, hz, hc', ?_, ?_, ?_⟩
  · exact g.concurrence_signChanges_parameter_order e f k hef hek
      (g.edge_control_signChanges_concurrence v h e f k hs)
  · exact g.concurrence_signChanges_parameter_order f e k hfe hfk
      (g.edge_control_signChanges_concurrence v h f e k hsf)
  · exact g.concurrence_signChanges_parameter_order k e f hke hkf
      (g.edge_control_signChanges_concurrence v h k e f hsk)

end WallGerm

namespace CurveCubeSubdivision.TimedEventCertificate

variable {γ : unitInterval → LabelledTuple n} {δ : ℝ}
    {d : CurveCubeSubdivision γ δ} {W : d.InternalWaypoint × ScalarCoordinate n → ℝ}
    {A : d.CubeCoordinateApproximation W} {hn : 3 ≤ n} {t : unitInterval}

theorem triple_wall (E : TimedEventCertificate A hn t)
    (v : EdgeControlName n) (he : E.control = .inr v) :
    ∃ e f k, ({e, f, k} : Finset (ZMod n)) = v.val ∧ E.germ.TripleAt e f k := by
  have hng : ¬ Generic (A.path t) := by rw [← E.germ_center]; exact E.germ.center_not_generic
  have hsets := E.center_sets hng
  simp only [he] at hsets
  have hs : E.germ.SignChanges
      (fun P => eval (scalarCoordinates P) (namedControlPolynomial (.inr v))) := by
    simpa only [he] using E.signChanges
  exact E.germ.active_edge_control_tripleAt hn v hsets.1 hsets.2 hs

end CurveCubeSubdivision.TimedEventCertificate

end

end SM
