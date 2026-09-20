-- Ported <HH:MM>Z 2026-09-16 from work/drafts/moves/R176W2_Assembled.lean lines 2-8972 (verbatim) by the row-176 wave-2
-- assembler: the row-176 site and units — Site_176 `s176_` (the `j`-corner bigon site of carrierDiagram q₀' and the weak
-- re-base of the est_ ledger), HSUCC `r176h_` (the RII port), SMOOTH `r176s_` (the smoothing D_A, arcs of a self crossing,
-- the lift/liftBlock readings), LEDGER `r176l_` (the wind(S)-uniform rotation ledger and the labelled-corner geometry),
-- the wave-1 composition `r176_` (the interface Props r176s_curl_removal / r176_outer_carriers_L / r176_mixed_bridge and
-- the conditional row r176_extreme_transport_of_curl_outer_mixed), and the wave-2 units — CURL `r176c_`
-- (r176c_curl_removal_proof : r176s_curl_removal), OUTER `r176o_` (r176o_outer_carriers_L_corrected_proof; the frozen
-- Prop r176_outer_carriers_L is FALSE at y = lift v' and is never asserted — it stays a definition whose consumers are
-- conditional theorems; the corrected split and the replayed composition r176o_extreme_transport_of_curl_mixed replace
-- it), MIXED `r176m_` (r176m_mixed_bridge_proof : r176_mixed_bridge), and the assembler's `r176a_`
-- (r176a_mixed_bridge'_proof : r176o_mixed_bridge', r176a_extreme_transport_rowShape : RowShape @ExtremeTransportData),
-- all in namespace RProof.  LIBRARY MATERIAL, no row theorem: the row theorem RProof.extreme_transport is in
-- RProof/ExtremeTransport.lean.  Body verbatim except this header (the assembled file's one header line replaced).
-- Every declaration is proved on the standard and literature axioms (r176c_curl_removal_proof, r176m_mixed_bridge_proof,
-- r176a_mixed_bridge'_proof, r176o_outer_carriers_L_corrected_proof on the standard three alone); no placeholder anywhere.
-- The units' docstring phrases "BLACK BOX (OPEN)" / "OPEN" / "nothing above is modified" are the units' own drafting
-- notes, written before the wave-2 proofs: every interface Prop below is discharged as listed above.
import SM.Smoothing
import SM.MarkedProducts
import SM.SingleCrossing
import CV.FullTwist
import RProof.GenericTransport
import RProof.RALedgers
import SM.BigonDeletion


/-! # Site_176 — row 176 (R:extreme_transport), the `j`-corner bigon site of `carrierDiagram q₀'` switched at `y`

APPENDED by the I-176 prover, 2026-09-15, to `Skeleton_W1.lean` (byte-identical above this line except the
added `import RProof.RALedgers`).  Companion report: `Site_176_REPORT.md`.  All names carry the prefix
`s176_`; nothing above is modified; the frozen leaves (`exists_bigonData_of_triangle`, …) are used as black
boxes.  Sections: §A the abstract `j`-corner site on a positive diagram and its `BigonData` through the frozen
leaf (`same_over` PROVED from the corner identity, `hk` from genericity); §B the row-176 ledger re-based on the
weak port (F-176-1: `s176_PortDataWeak`, `s176_est_omega1_eq_of_port_weak`, `s176_est_port_relation_weak`,
`s176_est_ledger_weak`); §C the carrier-level realisation of the site (`s176_cornerSite_of_carrier`, PROVED:
the corner structure `s176_corner_case1`, the cyclicity `s176_cyclic`, the closed-triangle clearance
`s176_clear_case1`); §D the event-level site in the binders of `est_port_relation` (`s176_site_of_event`,
PROVED); §E the record identification `hrec` (`s176_hrec_of_site`, STATED) and the compositions
(`s176_port_weak_of_event`, `s176_est_port_relation_weak_of`); §F the switch drops out of `hrec`
(`s176_switchRestrictIso`, PROVED); §G the wall occurrence bijection `s176_wallΦ` and the `RecordIso` modulo the
successor clause (`s176_hrec_unswitched_of_succ`, PROVED); §H the event-level wall data and the closure of the
chain: `s176_hrec_wall_of_succ`, `s176_site_of_event'`, `s176_port_weak_of_event'`,
`s176_est_port_relation_weak_of'` — the ONE remaining obligation of the move is the successor clause `hsucc`. -/

namespace RProof

open SM SM.GeoCarrier SM.Carrier SM.Link

noncomputable section

/-! ## §A. The abstract `j`-corner site (row 176, PLAN_FINAL §4.3) -/

/-- **The `j`-corner site on a diagram `D`** (positive at the two crossings): the corner vertex
`M₁ = P (a+1)` of component `i`, its two incident edges `e_in = ⟨i, a⟩`, `e_out = ⟨i, a+1⟩`, one
straight remote strand `s` crossing both (`y₁` on `e_in`, `y₂` on `e_out`), and the printed
emptiness of the closed contact triangle.  For row 176: `D = carrierDiagram q₀'`, `M₁` = the
`j`-corner, `{y₁, y₂}` = the lifts of `u', v'`, `s` = the third triangle strand. -/
structure s176_CornerSite (D : Diagram) where
  i : Fin D.Γ.c
  a : ZMod (D.Γ.comp i).k
  hk : 4 ≤ (D.Γ.comp i).k
  s : D.Γ.Strand
  y₁ : D.Γ.Crossing
  y₂ : D.Γ.Crossing
  hy₁ : y₁.val = {⟨i, a⟩, s}
  hy₂ : y₂.val = {⟨i, a + 1⟩, s}
  pos₁ : D.IsPositive y₁
  pos₂ : D.IsPositive y₂
  clear : ∀ u : D.Γ.Strand, u ≠ ⟨i, a⟩ → u ≠ ⟨i, a + 1⟩ → u ≠ s →
    Disjoint (D.Γ.seg u)
      (convexHull ℝ {D.Γ.crossingPoint y₁, (D.Γ.comp i).P (a + 1), D.Γ.crossingPoint y₂})

namespace s176_CornerSite

variable {D : Diagram} (T : s176_CornerSite D)

/-- the entering edge `e_in = (M₀, M₁)` -/
def eIn : D.Γ.Strand := ⟨T.i, T.a⟩
/-- the exiting edge `e_out = (M₁, M₂)` -/
def eOut : D.Γ.Strand := ⟨T.i, T.a + 1⟩

theorem eIn_mem : T.eIn ∈ T.y₁.val := by
  rw [T.hy₁]; exact Finset.mem_insert_self _ _
theorem s_mem₁ : T.s ∈ T.y₁.val := by
  rw [T.hy₁]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
theorem eOut_mem : T.eOut ∈ T.y₂.val := by
  rw [T.hy₂]; exact Finset.mem_insert_self _ _
theorem s_mem₂ : T.s ∈ T.y₂.val := by
  rw [T.hy₂]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)

theorem eIn_ne_s : T.eIn ≠ T.s := by
  intro h
  have h2 := D.Γ.crossing_card_two T.y₁
  rw [T.hy₁, show (⟨T.i, T.a⟩ : D.Γ.Strand) = T.eIn from rfl, h,
    Finset.insert_eq_of_mem (Finset.mem_singleton_self _), Finset.card_singleton] at h2
  exact absurd h2 (by norm_num)

theorem eOut_ne_s : T.eOut ≠ T.s := by
  intro h
  have h2 := D.Γ.crossing_card_two T.y₂
  rw [T.hy₂, show (⟨T.i, T.a + 1⟩ : D.Γ.Strand) = T.eOut from rfl, h,
    Finset.insert_eq_of_mem (Finset.mem_singleton_self _), Finset.card_singleton] at h2
  exact absurd h2 (by norm_num)

theorem one_ne_zero_k : (1 : ZMod (D.Γ.comp T.i).k) ≠ 0 := by
  intro h
  have h' : (D.Γ.comp T.i).k ∣ 1 :=
    (ZMod.natCast_eq_zero_iff 1 (D.Γ.comp T.i).k).mp (by rw [Nat.cast_one]; exact h)
  have := Nat.le_of_dvd one_pos h'
  have := T.hk
  omega

theorem eIn_ne_eOut : T.eIn ≠ T.eOut := by
  intro h
  have h'' : T.a = T.a + 1 := eq_of_heq (Sigma.mk.inj_iff.mp h).2
  exact T.one_ne_zero_k (by linear_combination -h'')

theorem y₁_ne_y₂ : T.y₁ ≠ T.y₂ := by
  intro h
  have hmem : T.eIn ∈ T.y₂.val := h ▸ T.eIn_mem
  rw [T.hy₂, Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with h1 | h1
  · exact T.eIn_ne_eOut h1
  · exact T.eIn_ne_s h1

/-- transversality of `e_in` and `s` -/
theorem det_in_ne_zero : det (D.Γ.dir T.eIn) (D.Γ.dir T.s) ≠ 0 :=
  D.generic.transverse _ _ (D.Γ.crossing_pair_spec T.y₁ T.eIn_mem T.s_mem₁ T.eIn_ne_s).1
    (D.Γ.crossing_pair_spec T.y₁ T.eIn_mem T.s_mem₁ T.eIn_ne_s).2

/-- transversality of `e_out` and `s` -/
theorem det_out_ne_zero : det (D.Γ.dir T.eOut) (D.Γ.dir T.s) ≠ 0 :=
  D.generic.transverse _ _ (D.Γ.crossing_pair_spec T.y₂ T.eOut_mem T.s_mem₂ T.eOut_ne_s).1
    (D.Γ.crossing_pair_spec T.y₂ T.eOut_mem T.s_mem₂ T.eOut_ne_s).2

/-- **The corner identity**: the straight strand `s` through `y₁ ∈ e_in` and `y₂ ∈ e_out` crosses the
two edges of the corner `M₁` with OPPOSITE orientations — `(1 − t₁) det(e_in, s) + t₂ det(e_out, s) = 0`
with `t₁ < 1`, `0 < t₂`, so the two determinants have opposite signs.  This is the whole geometric
content of `same_over` (sm-4:614-618's sign table). -/
theorem det_mul_det_neg :
    det (D.Γ.dir T.eIn) (D.Γ.dir T.s) * det (D.Γ.dir T.eOut) (D.Γ.dir T.s) < 0 := by
  -- the four parametrisations of the two crossing points
  obtain ⟨-, -, h₁⟩ := D.crossingParam_spec T.y₁ T.eIn_mem
  obtain ⟨-, -, h₁'⟩ := D.crossingParam_spec T.y₁ T.s_mem₁
  obtain ⟨-, -, h₂⟩ := D.crossingParam_spec T.y₂ T.eOut_mem
  obtain ⟨-, -, h₂'⟩ := D.crossingParam_spec T.y₂ T.s_mem₂
  have ht₁ : D.crossingParam T.y₁ T.eIn_mem < 1 := D.crossingParam_lt_one T.y₁ T.eIn_mem
  have ht₂ : 0 < D.crossingParam T.y₂ T.eOut_mem := D.crossingParam_pos T.y₂ T.eOut_mem
  set t₁ := D.crossingParam T.y₁ T.eIn_mem
  set u₁ := D.crossingParam T.y₁ T.s_mem₁
  set t₂ := D.crossingParam T.y₂ T.eOut_mem
  set u₂ := D.crossingParam T.y₂ T.s_mem₂
  set A := D.Γ.dir T.eIn with hA
  set B := D.Γ.dir T.eOut with hB
  set S := D.Γ.dir T.s with hS
  set O := D.Γ.tail T.s with hO
  set Pa := (D.Γ.comp T.i).P T.a with hPa
  have e₁ : Pa + t₁ • A = O + u₁ • S := by
    have := h₁.symm.trans h₁'
    exact this
  have e₂ : (Pa + A) + t₂ • B = O + u₂ • S := by
    have := h₂.symm.trans h₂'
    have hPa1 : (D.Γ.comp T.i).P (T.a + 1) = Pa + A := by
      show _ = _ + edge (D.Γ.comp T.i).P T.a
      unfold edge; abel
    rw [show edgePoint (D.Γ.comp T.eOut.1).P T.eOut.2 t₂ = (D.Γ.comp T.i).P (T.a + 1) + t₂ • B from rfl,
      hPa1] at this
    exact this
  -- the linear relation `(1 − t₁) det(A, S) + t₂ det(B, S) = 0`
  have hlin : (1 - t₁) * det A S + t₂ * det B S = 0 := by
    have c1 := congrArg Prod.fst e₁
    have c2 := congrArg Prod.snd e₁
    have c3 := congrArg Prod.fst e₂
    have c4 := congrArg Prod.snd e₂
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at c1 c2 c3 c4
    unfold det
    linear_combination S.2 * (c3 - c1) - S.1 * (c4 - c2)
  have hA0 : det A S ≠ 0 := T.det_in_ne_zero
  have hB0 : det B S ≠ 0 := T.det_out_ne_zero
  have hB2 : 0 < det B S * det B S := mul_self_pos.mpr hB0
  have h1t : 0 < 1 - t₁ := by linarith
  have key : (1 - t₁) * (det A S * det B S) = -(t₂ * (det B S * det B S)) := by
    linear_combination det B S * hlin
  by_contra hcon
  have hcon' : 0 ≤ det A S * det B S := not_lt.mp hcon
  nlinarith [mul_nonneg h1t.le hcon', mul_pos ht₂ hB2]

/-- On the positive diagram, `s` is over at `y₁` iff `det(e_in, s) < 0`. -/
theorem over₁_eq_s_iff : D.overStrand T.y₁ = T.s ↔ det (D.Γ.dir T.eIn) (D.Γ.dir T.s) < 0 := by
  have hpos := T.pos₁
  unfold Diagram.IsPositive at hpos
  constructor
  · intro h
    have hu : T.eIn = D.underStrand T.y₁ :=
      D.eq_under_of_mem_of_ne T.y₁ T.eIn_mem (by rw [h]; exact T.eIn_ne_s)
    rw [h, ← hu, det_swap] at hpos
    linarith
  · intro hlt
    by_contra h
    have ho : T.eIn = D.overStrand T.y₁ := by
      have hs : T.s = D.underStrand T.y₁ := D.eq_under_of_mem_of_ne T.y₁ T.s_mem₁ (Ne.symm h)
      exact D.eq_over_of_mem_of_ne T.y₁ T.eIn_mem (by rw [← hs]; exact T.eIn_ne_s)
    have hs : T.s = D.underStrand T.y₁ := D.eq_under_of_mem_of_ne T.y₁ T.s_mem₁ (Ne.symm h)
    rw [← ho, ← hs] at hpos
    linarith

/-- On the positive diagram, `s` is over at `y₂` iff `det(e_out, s) < 0`. -/
theorem over₂_eq_s_iff : D.overStrand T.y₂ = T.s ↔ det (D.Γ.dir T.eOut) (D.Γ.dir T.s) < 0 := by
  have hpos := T.pos₂
  unfold Diagram.IsPositive at hpos
  constructor
  · intro h
    have hu : T.eOut = D.underStrand T.y₂ :=
      D.eq_under_of_mem_of_ne T.y₂ T.eOut_mem (by rw [h]; exact T.eOut_ne_s)
    rw [h, ← hu, det_swap] at hpos
    linarith
  · intro hlt
    by_contra h
    have hs : T.s = D.underStrand T.y₂ := D.eq_under_of_mem_of_ne T.y₂ T.s_mem₂ (Ne.symm h)
    have ho : T.eOut = D.overStrand T.y₂ :=
      D.eq_over_of_mem_of_ne T.y₂ T.eOut_mem (by rw [← hs]; exact T.eOut_ne_s)
    rw [← ho, ← hs] at hpos
    linarith

/-- On the positive diagram exactly one of the two crossings has `s` over (the printed sign table). -/
theorem over₁_iff_not_over₂ : D.overStrand T.y₁ = T.s ↔ D.overStrand T.y₂ ≠ T.s := by
  rw [T.over₁_eq_s_iff, ne_eq, T.over₂_eq_s_iff]
  have h := T.det_mul_det_neg
  have hA := T.det_in_ne_zero
  have hB := T.det_out_ne_zero
  constructor
  · intro h1 h2
    nlinarith
  · intro h2
    have h2' : 0 < det (D.Γ.dir T.eOut) (D.Γ.dir T.s) := lt_of_le_of_ne (not_lt.mp h2) (Ne.symm hB)
    by_contra h1
    have h1' : 0 < det (D.Γ.dir T.eIn) (D.Γ.dir T.s) := lt_of_le_of_ne (not_lt.mp h1) (Ne.symm hA)
    nlinarith

/-- the under strand at `y₁` is `s` iff the over strand is not -/
theorem under₁_eq_s_iff : D.underStrand T.y₁ = T.s ↔ D.overStrand T.y₁ ≠ T.s := by
  constructor
  · intro h h'
    exact D.under_ne_over T.y₁ (h.trans h'.symm)
  · intro h
    exact (D.eq_under_of_mem_of_ne T.y₁ T.s_mem₁ (Ne.symm h)).symm

theorem under₂_eq_s_iff : D.underStrand T.y₂ = T.s ↔ D.overStrand T.y₂ ≠ T.s := by
  constructor
  · intro h h'
    exact D.under_ne_over T.y₂ (h.trans h'.symm)
  · intro h
    exact (D.eq_under_of_mem_of_ne T.y₂ T.s_mem₂ (Ne.symm h)).symm

/-- **`same_over` after switching `y₁`** (the frozen field of `BigonData`, verbatim on `D.switch y₁`). -/
theorem same_over_switch₁ :
    ((D.switch T.y₁).overStrand T.y₁ = T.s ∧ (D.switch T.y₁).overStrand T.y₂ = T.s) ∨
      ((D.switch T.y₁).overStrand T.y₁ ≠ T.s ∧ (D.switch T.y₁).overStrand T.y₂ ≠ T.s) := by
  have h1 : (D.switch T.y₁).overStrand T.y₁ = D.underStrand T.y₁ := D.switch_overStrand_self T.y₁
  have h2 : (D.switch T.y₁).overStrand T.y₂ = D.overStrand T.y₂ :=
    D.switch_overStrand_of_ne T.y₁_ne_y₂.symm
  by_cases h : D.overStrand T.y₂ = T.s
  · exact Or.inl ⟨h1.trans (T.under₁_eq_s_iff.mpr fun h' => (T.over₁_iff_not_over₂.mp h') h),
      h2.trans h⟩
  · exact Or.inr ⟨fun h' => (T.under₁_eq_s_iff.mp (h1.symm.trans h')) (T.over₁_iff_not_over₂.mpr h),
      fun h' => h (h2.symm.trans h')⟩

/-- **`same_over` after switching `y₂`.** -/
theorem same_over_switch₂ :
    ((D.switch T.y₂).overStrand T.y₁ = T.s ∧ (D.switch T.y₂).overStrand T.y₂ = T.s) ∨
      ((D.switch T.y₂).overStrand T.y₁ ≠ T.s ∧ (D.switch T.y₂).overStrand T.y₂ ≠ T.s) := by
  have h1 : (D.switch T.y₂).overStrand T.y₁ = D.overStrand T.y₁ :=
    D.switch_overStrand_of_ne T.y₁_ne_y₂
  have h2 : (D.switch T.y₂).overStrand T.y₂ = D.underStrand T.y₂ := D.switch_overStrand_self T.y₂
  by_cases h : D.overStrand T.y₁ = T.s
  · exact Or.inl ⟨h1.trans h, h2.trans (T.under₂_eq_s_iff.mpr (T.over₁_iff_not_over₂.mp h))⟩
  · exact Or.inr ⟨fun h' => h (h1.symm.trans h'),
      fun h' => (T.under₂_eq_s_iff.mp (h2.symm.trans h'))
        (not_not.mp fun hne => h (T.over₁_iff_not_over₂.mpr hne))⟩

/-- **The site theorem, switched at `y₁`**: a `BigonData` on `D.switch y₁` with the frozen fields,
through the frozen leaf `exists_bigonData_of_triangle` (the closed contact triangle `K`). -/
theorem exists_bigon_switch₁ :
    ∃ B : BigonData (D.switch T.y₁), B.i = T.i ∧ B.y = T.y₁ ∧ B.z = T.y₂ :=
  exists_bigonData_of_triangle (D.switch T.y₁) T.i T.a T.hk T.s T.y₁ T.y₂ T.hy₁ T.hy₂
    T.same_over_switch₁ T.clear

/-- **The site theorem, switched at `y₂`.** -/
theorem exists_bigon_switch₂ :
    ∃ B : BigonData (D.switch T.y₂), B.i = T.i ∧ B.y = T.y₁ ∧ B.z = T.y₂ :=
  exists_bigonData_of_triangle (D.switch T.y₂) T.i T.a T.hk T.s T.y₁ T.y₂ T.hy₁ T.hy₂
    T.same_over_switch₂ T.clear

/-- **The site theorem for the switched crossing `y₀ ∈ {y₁, y₂}`** (row 176's `y` is the lift of the
retained unselected crossing `u'`, which is `y₁` or `y₂` according to the orientation of the corner). -/
theorem exists_bigon_switch (y₀ : D.Γ.Crossing) (h : y₀ = T.y₁ ∨ y₀ = T.y₂) :
    ∃ B : BigonData (D.switch y₀), B.i = T.i ∧ (B.y = y₀ ∨ B.z = y₀) := by
  rcases h with rfl | rfl
  · obtain ⟨B, hi, hy, -⟩ := T.exists_bigon_switch₁
    exact ⟨B, hi, Or.inl hy⟩
  · obtain ⟨B, hi, -, hz⟩ := T.exists_bigon_switch₂
    exact ⟨B, hi, Or.inr hz⟩

end s176_CornerSite

/-- **`hk` for a one-component site**: if the remote strand lies on the same component as the corner
(row 176: the carrier diagram has one component) then `k ≥ 4` — a crossing pairs NON-adjacent strands,
and on `ZMod 3` every pair of labels is adjacent. -/
theorem s176_four_le_of_crossing (D : Diagram) (i : Fin D.Γ.c) (a b : ZMod (D.Γ.comp i).k)
    (x : D.Γ.Crossing) (hx : x.val = {⟨i, a⟩, ⟨i, b⟩}) : 4 ≤ (D.Γ.comp i).k := by
  have hne : (⟨i, a⟩ : D.Γ.Strand) ≠ ⟨i, b⟩ := by
    intro h
    have h2 := D.Γ.crossing_card_two x
    rw [hx, h, Finset.insert_eq_of_mem (Finset.mem_singleton_self _), Finset.card_singleton] at h2
    exact absurd h2 (by norm_num)
  have hna := (D.Γ.crossing_pair_spec x (by rw [hx]; exact Finset.mem_insert_self _ _)
    (by rw [hx]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)) hne).1
  rw [D.Γ.adjacent_mk_iff] at hna
  have h3 := (D.Γ.comp i).hk
  by_contra hlt
  have hk3 : (D.Γ.comp i).k = 3 := by omega
  apply hna
  have key : ∀ (m : ℕ), m = 3 → ∀ c d : ZMod m, adjacent c d := by
    rintro m rfl c d
    unfold adjacent
    revert c d
    decide
  exact key _ hk3 a b

end

end RProof

namespace RProof

open SM SM.GeoCarrier SM.Carrier SM.Link

noncomputable section

variable {n : ℕ} [NeZero n]

/-! ## §B. Row 176 re-based on the weak port (F-176-1): the port data, the ledger, the row shape -/

/-- **`est_PortData` with the `port` field in the deliverable (weak) form** (PLAN_FINAL §3 F-176-1): every
other field is byte-identical to `RProof.est_PortData` (RALedgers.lean:872); `port` becomes
`est_port_weak D₊ D₀ y = ∃ D₀', ReflTransGen RII (D₊.switch y) D₀' ∧ homfly D₀' = homfly D₀`. -/
structure s176_PortDataWeak (hn : 3 ≤ n) {P P' : LabelledTuple n} (hG : CV.Generic P) (hG' : CV.Generic P')
    {S : Finset (Crossing P)} {S' : Finset (Crossing P')}
    (hS : S ∈ CV.Ind hG.crossingGeometry) (hS' : S' ∈ CV.Ind hG'.crossingGeometry)
    (q : GeoComponent hG.crossingGeometry S) (q' : GeoComponent hG'.crossingGeometry S')
    (y : (CV.carrierDiagram hn hG' hS' q').Γ.Crossing) where
  /-- (T2) the RII port relation in the weak form (the only changed field) -/
  port : est_port_weak (CV.carrierDiagram hn hG' hS' q') (CV.carrierDiagram hn hG hS q) y
  DA : Diagram
  smooth : IsOrientedSmoothing (CV.carrierDiagram hn hG' hS' q') y DA
  two : DA.componentCount = 2
  i : Fin DA.Γ.c
  j : Fin DA.Γ.c
  ij : i ≠ j
  Sf : Finset (Crossing P')
  hSf : Sf ∈ CV.Ind hG'.crossingGeometry
  Λ₁ : GeoComponent hG'.crossingGeometry Sf
  Λ₂ : GeoComponent hG'.crossingGeometry Sf
  poly₁ : homfly (DA.knotRestrict i) = CV.groupedPoly hn hG' hSf Λ₁
  poly₂ : homfly (DA.knotRestrict j) = CV.groupedPoly hn hG' hSf Λ₂
  ℓ : ℤ
  link : CV.IsLinkingNumber DA i j ℓ
  writhe : CV.groupedWrithe hG q = CV.groupedWrithe hG' Λ₁ + CV.groupedWrithe hG' Λ₂ + 2 * ℓ
  rot : (CV.carrierR hn hG hS q : ℤ) = CV.carrierR hn hG' hSf Λ₁ + CV.carrierR hn hG' hSf Λ₂ + 1
  alt₁ : CV.UniformOrOneDissentCV (geoCornerPolygon hG'.crossingGeometry Sf Λ₁)
  alt₂ : CV.UniformOrOneDissentCV (geoCornerPolygon hG'.crossingGeometry Sf Λ₂)

/-- **The non-move part of the port data** (U_R176_REPORT §5 items 2–5: the oriented smoothing `D_A`,
the exact owner map (9)/(9a), the linking number, the writhe/rotation/sign ledgers): `est_PortData`
minus `port`.  This is what row 176 still owes beyond the site and `hrec`. -/
structure s176_PortDataRest (hn : 3 ≤ n) {P P' : LabelledTuple n} (hG : CV.Generic P) (hG' : CV.Generic P')
    {S : Finset (Crossing P)} {S' : Finset (Crossing P')}
    (hS : S ∈ CV.Ind hG.crossingGeometry) (hS' : S' ∈ CV.Ind hG'.crossingGeometry)
    (q : GeoComponent hG.crossingGeometry S) (q' : GeoComponent hG'.crossingGeometry S')
    (y : (CV.carrierDiagram hn hG' hS' q').Γ.Crossing) where
  DA : Diagram
  smooth : IsOrientedSmoothing (CV.carrierDiagram hn hG' hS' q') y DA
  two : DA.componentCount = 2
  i : Fin DA.Γ.c
  j : Fin DA.Γ.c
  ij : i ≠ j
  Sf : Finset (Crossing P')
  hSf : Sf ∈ CV.Ind hG'.crossingGeometry
  Λ₁ : GeoComponent hG'.crossingGeometry Sf
  Λ₂ : GeoComponent hG'.crossingGeometry Sf
  poly₁ : homfly (DA.knotRestrict i) = CV.groupedPoly hn hG' hSf Λ₁
  poly₂ : homfly (DA.knotRestrict j) = CV.groupedPoly hn hG' hSf Λ₂
  ℓ : ℤ
  link : CV.IsLinkingNumber DA i j ℓ
  writhe : CV.groupedWrithe hG q = CV.groupedWrithe hG' Λ₁ + CV.groupedWrithe hG' Λ₂ + 2 * ℓ
  rot : (CV.carrierR hn hG hS q : ℤ) = CV.carrierR hn hG' hSf Λ₁ + CV.carrierR hn hG' hSf Λ₂ + 1
  alt₁ : CV.UniformOrOneDissentCV (geoCornerPolygon hG'.crossingGeometry Sf Λ₁)
  alt₂ : CV.UniformOrOneDissentCV (geoCornerPolygon hG'.crossingGeometry Sf Λ₂)

section S176PortData

variable (hn : 3 ≤ n) {P P' : LabelledTuple n} (hG : CV.Generic P) (hG' : CV.Generic P')
  {S : Finset (Crossing P)} {S' : Finset (Crossing P')}
  (hS : S ∈ CV.Ind hG.crossingGeometry) (hS' : S' ∈ CV.Ind hG'.crossingGeometry)
  (q : GeoComponent hG.crossingGeometry S) (q' : GeoComponent hG'.crossingGeometry S')
  (y : (CV.carrierDiagram hn hG' hS' q').Γ.Crossing)

/-- The weak port data = the weak port + the rest. -/
def s176_PortDataWeak.mk' (port : est_port_weak (CV.carrierDiagram hn hG' hS' q') (CV.carrierDiagram hn hG hS q) y)
    (R : s176_PortDataRest hn hG hG' hS hS' q q' y) : s176_PortDataWeak hn hG hG' hS hS' q q' y :=
  ⟨port, R.DA, R.smooth, R.two, R.i, R.j, R.ij, R.Sf, R.hSf, R.Λ₁, R.Λ₂, R.poly₁, R.poly₂, R.ℓ, R.link,
    R.writhe, R.rot, R.alt₁, R.alt₂⟩

/-- The literal port data gives the weak one (`D₀' := D₀`). -/
def s176_PortDataWeak.ofPortData (D : est_PortData hn hG hG' hS hS' q q' y) :
    s176_PortDataWeak hn hG hG' hS hS' q q' y :=
  ⟨⟨_, D.port, rfl⟩, D.DA, D.smooth, D.two, D.i, D.j, D.ij, D.Sf, D.hSf, D.Λ₁, D.Λ₂, D.poly₁, D.poly₂,
    D.ℓ, D.link, D.writhe, D.rot, D.alt₁, D.alt₂⟩

/-- **The weak port from the bigon site and the record identification** (the composition (a)+(b) →
`est_port_weak_of_bigon`): `Dp = carrierDiagram q₀'`, `D₀ = carrierDiagram q₀`, both one-component
(`geoPositiveLift_componentCount`, `rfl`). -/
theorem s176_port_weak_of_bigon (B : BigonData ((CV.carrierDiagram hn hG' hS' q').switch y))
    (hrec : Nonempty (RecordIso B.reducedRecord (CV.carrierDiagram hn hG hS q).record)) :
    est_port_weak (CV.carrierDiagram hn hG' hS' q') (CV.carrierDiagram hn hG hS q) y :=
  est_port_weak_of_bigon _ _ y rfl rfl B hrec

/-- The weak port from an abstract corner site on `carrierDiagram q₀'` whose switched crossing is one
of the two site crossings, plus the record identification of the reduced record for THAT bigon. -/
theorem s176_port_weak_of_cornerSite (T : s176_CornerSite (CV.carrierDiagram hn hG' hS' q'))
    (hy : y = T.y₁ ∨ y = T.y₂)
    (hrec : ∀ B : BigonData ((CV.carrierDiagram hn hG' hS' q').switch y), B.i = T.i →
      (B.y = y ∨ B.z = y) → Nonempty (RecordIso B.reducedRecord (CV.carrierDiagram hn hG hS q).record)) :
    est_port_weak (CV.carrierDiagram hn hG' hS' q') (CV.carrierDiagram hn hG hS q) y := by
  obtain ⟨B, hi, hyz⟩ := T.exists_bigon_switch y hy
  exact s176_port_weak_of_bigon hn hG hG' hS hS' q q' y B (hrec B hi hyz)

/-- **(16) `Ω_+ = Ω_0` from the WEAK port data** — `est_omega1_eq_of_port` (RALedgers.lean:915) replayed
verbatim with the ONE call `CV.fulltwist_coefficient … D.port …` replaced by
`fulltwist_coefficient_of_port_weak … D.port …` (F-176-1: 1 line changed, the rest byte-identical). -/
theorem s176_est_omega1_eq_of_port_weak (hF : CV.CarrierSlotFloor)
    (D : s176_PortDataWeak hn hG hG' hS hS' q q' y)
    (hw : CV.groupedWrithe hG' q' = CV.groupedWrithe hG q + 2)
    (hR : CV.carrierR hn hG' hS' q' = CV.carrierR hn hG hS q) :
    CV.Omega1 hn hG' hS' q' = CV.Omega1 hn hG hS q := by
  have hpos : (CV.carrierDiagram hn hG' hS' q').IsPositive y := geoPositiveLift_isPositive hn _ _ q' y
  -- (7) `d_+ = d_0 − 2`
  have hd : CV.d (CV.carrierDiagram hn hG' hS' q') rfl = CV.d (CV.carrierDiagram hn hG hS q) rfl - 2 := by
    rw [est_carrierDiagram_d, est_carrierDiagram_d]
    unfold CV.slot
    rw [hw, hR]; ring
  -- (8) lem:fulltwist, re-based on the weak port (the ONE changed call)
  have hft := fulltwist_coefficient_of_port_weak (CV.carrierDiagram hn hG' hS' q')
    (CV.carrierDiagram hn hG hS q) D.DA y hpos D.smooth D.port rfl rfl hd
  rw [est_carrierDiagram_Omega, est_carrierDiagram_Omega, est_carrierDiagram_d] at hft
  -- (11) lem:homflyrows (ii)
  have hrow := CV.homflyrows.two_component_row D.DA D.i D.j D.two D.ij D.ℓ D.link
  rw [D.poly₁, D.poly₂] at hrow
  have hcoef := est_coeffAt_of_zRow _ _ (CV.slot hn hG hS q) D.ℓ hrow
  -- the floor at the two clean outer carriers
  have hne₁ := CV.cvt_groupedPoly_ne_zero hn hG' D.hSf D.Λ₁
  have hne₂ := CV.cvt_groupedPoly_ne_zero hn hG' D.hSf D.Λ₂
  have h₁ := hF hn hG' D.hSf D.Λ₁ D.alt₁
  have h₂ := hF hn hG' D.hSf D.Λ₂ D.alt₂
  -- (15) `D = d_0 + 2 + 2ℓ`
  have hsum : CV.slot hn hG' D.hSf D.Λ₁ + CV.slot hn hG' D.hSf D.Λ₂ =
      CV.slot hn hG hS q + 2 + 2 * D.ℓ := by
    unfold CV.slot
    have := D.writhe
    have := D.rot
    omega
  -- (16)
  have hz₁ := est_coeffAt_mul_eq_zero _ _ hne₁ hne₂ _ _ (CV.slot hn hG hS q - 2 + 2 * D.ℓ) h₁ h₂ (by omega)
  have hz₂ := est_coeffAt_mul_eq_zero _ _ hne₁ hne₂ _ _ (CV.slot hn hG hS q + 2 * D.ℓ) h₁ h₂ (by omega)
  rw [hcoef, hz₁, hz₂, sub_zero] at hft
  linarith

end S176PortData

/-- **The RII port relation of row 176 in the weak form** — `RProof.est_port_relation` (RALedgers.lean:1453)
with `est_PortData` replaced by `s176_PortDataWeak`; otherwise byte-identical. -/
def s176_est_port_relation_weak : Prop :=
  ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (E : CV.Event n) (e f g : ZMod n) (δ : ℝ)
    (hL : LocalizationData E e f g δ) (hR : AV_EventRadius E δ) (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
    (t t' : E.Parameter) (ht : Punctured E δ t) (ht' : Punctured E δ t') (hop : OppositeSides E t t')
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    (hef' : IsCrossing (E.curve t) {e, f}) (heg' : IsCrossing (E.curve t) {e, g})
    (hfg' : IsCrossing (E.curve t) {f, g}) (_hcomp : CompleteLocal (geomAt E t ht.1) hef' heg' hfg')
    (Q : Finset (Crossing (E.curve t))) (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
    (hfull : FullAvail (geomAt E t ht.1) e f g Q) (j : Crossing (E.curve t))
    (hj : j.val ∈ triangleSupports e f g) (q : GeoComponent (geomAt E t ht.1) (Q ∪ {j})),
    (∃ u : Crossing (E.curve t), u.val ∈ triangleSupports e f g ∧ u ≠ j ∧
      crossingTransport hs u ∈ geoCarrierCrossings (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j}))
        (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)) →
    ∃ (u : Crossing (E.curve t)) (_ : u.val ∈ triangleSupports e f g) (_ : u ≠ j)
      (hu' : crossingTransport hs u ∈ geoCarrierCrossings (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j}))
        (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)),
      Nonempty (s176_PortDataWeak hn (genericAt E t ht.1) (genericAt E t' ht'.1) (est_S_ind ht.1 hQ hfull hj)
        (est_S'_ind hL ht ht' hop hs hQ hfull hj) q
        (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)
        (est_liftCrossing hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj) _ hu'))

/-- The literal interface implies the weak one. -/
theorem s176_est_port_relation_weak_of_strong (h : est_port_relation) : s176_est_port_relation_weak := by
  intro n _ hn E e f g δ hL hR hef heg hfg t t' ht ht' hop hs hef' heg' hfg' hcomp Q hQ hfull j hj q hex
  obtain ⟨u, hu, hju, hu', ⟨D⟩⟩ := h n hn E e f g δ hL hR hef heg hfg t t' ht ht' hop hs hef' heg' hfg'
    hcomp Q hQ hfull j hj q hex
  exact ⟨u, hu, hju, hu', ⟨s176_PortDataWeak.ofPortData _ _ _ _ _ _ _ _ D⟩⟩

section S176Ledger

variable {E : CV.Event n} {e f g : ZMod n} {δ : ℝ}

/-- `est_row_H` (RALedgers.lean:1514) replayed with the weak interface: the only change is the call
`est_omega1_eq_of_port` ↦ `s176_est_omega1_eq_of_port_weak`. -/
theorem s176_est_row_H_weak (hF : CV.CarrierSlotFloor) (hport : s176_est_port_relation_weak) (hn : 3 ≤ n)
    (hL : LocalizationData E e f g δ) (hR : AV_EventRadius E δ) (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
    {t t' : E.Parameter} (ht : Punctured E δ t) (ht' : Punctured E δ t') (hop : OppositeSides E t t')
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    {hef' : IsCrossing (E.curve t) {e, f}} {heg' : IsCrossing (E.curve t) {e, g}}
    {hfg' : IsCrossing (E.curve t) {f, g}} (hcomp : CompleteLocal (geomAt E t ht.1) hef' heg' hfg')
    {Q : Finset (Crossing (E.curve t))} (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
    (hfull : FullAvail (geomAt E t ht.1) e f g Q) {j : Crossing (E.curve t)}
    (hj : j.val ∈ triangleSupports e f g) :
    rowTerm hn (genericAt E t ht.1) (Q ∪ {j}) =
      rowTerm hn (genericAt E t' ht'.1) (transportSupport hs (Q ∪ {j})) := by
  set W := est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj
  have hS := est_S_ind ht.1 hQ hfull hj
  have hS' := est_S'_ind hL ht ht' hop hs hQ hfull hj
  refine est_rowTerm_eq_of_omega hn _ _ hS hS'
    (GT_wind_eq hn (genericAt E t ht.1) (genericAt E t' ht'.1) W) (GT_carrierEquiv W) fun q => ?_
  obtain ⟨u, v, hu, hv, hju, hjv, huv⟩ := est_others hef' heg' hfg' hj
  obtain ⟨ℓ, hℓu, hℓv⟩ := GT_shared_label hu hv huv
  have hℓj := est_shared_not_mem_third hef heg hfg hj hu hv hju hjv huv hℓu hℓv
  by_cases hq : geoOwner (geomAt E t ht.1) (Q ∪ {j}) (Sum.inr (visitOn u ℓ hℓu)) = q
  · -- the affected carrier: the port ledger (weak form)
    have hu' : crossingTransport hs u ∈ geoCarrierCrossings (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j}))
        (GT_carrierEquiv W q) :=
      (est_retained_u_iff hL hR hef heg hfg ht ht' hop hs hcomp hQ hfull hj hu hju hℓu hℓj q).mpr hq
    obtain ⟨u₁, -, -, hu₁', ⟨D⟩⟩ := hport n hn E e f g δ hL hR hef heg hfg t t' ht ht' hop hs hef' heg' hfg'
      hcomp Q hQ hfull j hj q ⟨u, hu, hju.symm, hu'⟩
    exact s176_est_omega1_eq_of_port_weak hn _ _ hS hS' q _ _ hF D
      (est_groupedWrithe_affected hL hR hef heg hfg ht ht' hop hs hcomp hQ hfull hj hu hv hju hjv huv hℓu hℓv q hq)
      (GT_carrierR_eq hn (genericAt E t ht.1) (genericAt E t' ht'.1) W hS hS' q)
  · exact est_omega1_eq_of_ne hn hL hR hef heg hfg ht ht' hop hs hcomp hQ hfull hj hu hv hju hjv huv hℓu hℓv q hq

/-- `est_row` (RALedgers.lean:1548) replayed with the weak interface (byte-identical body). -/
theorem s176_est_row_weak (hF : CV.CarrierSlotFloor) (hport : s176_est_port_relation_weak) (hn : 3 ≤ n)
    (hL : LocalizationData E e f g δ) (hR : AV_EventRadius E δ) (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
    {t t' : E.Parameter} (ht : Punctured E δ t) (ht' : Punctured E δ t') (hop : OppositeSides E t t')
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    {hef' : IsCrossing (E.curve t) {e, f}} {heg' : IsCrossing (E.curve t) {e, g}}
    {hfg' : IsCrossing (E.curve t) {f, g}} (hext : ExtremeLocal (geomAt E t ht.1) hef' heg' hfg')
    {Q : Finset (Crossing (E.curve t))} (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
    (hfull : FullAvail (geomAt E t ht.1) e f g Q) {j : Crossing (E.curve t)}
    (hj : j.val ∈ triangleSupports e f g) :
    rowTerm hn (genericAt E t ht.1) (Q ∪ {j}) =
      rowTerm hn (genericAt E t' ht'.1) (transportSupport hs (Q ∪ {j})) := by
  rcases hext with hcomp | hemp
  · exact s176_est_row_H_weak hF hport hn hL hR hef heg hfg ht ht' hop hs hcomp hQ hfull hj
  · have hs' : ∀ s, IsCrossing (E.curve t') s ↔ IsCrossing (E.curve t) s := fun s => (hs s).symm
    have hop' : OppositeSides E t' t := by
      unfold OppositeSides at hop ⊢; linarith [mul_comm t.val t'.val]
    obtain ⟨hef'', heg'', hfg''⟩ := hL.triangle_crossings t' ht'
    have hcomp' : CompleteLocal (geomAt E t' ht'.1) hef'' heg'' hfg'' :=
      (PRE_176_graphs_complementary hL t' t ht' ht hop' hef'' heg'' hfg'' hef' heg' hfg').mpr hemp
    have hQ' := GT_outsideSupports_transport hL ht ht' hop hs hQ
    have hfull' := GT_fullAvail_transport hL ht ht' hop hs hQ hfull
    have hj' : (crossingTransport hs j).val ∈ triangleSupports e f g := hj
    have h := s176_est_row_H_weak hF hport hn hL hR hef heg hfg ht' ht hop' hs' hcomp' hQ' hfull' hj'
    rw [← GT_transportSupport_S hs Q j, EXT_transportSupport_symm hs (Q ∪ {j})] at h
    exact h.symm

/-- `est_extremeTransportData` (RALedgers.lean:1576) replayed with the weak interface. -/
theorem s176_est_extremeTransportData_weak (hF : CV.CarrierSlotFloor) (hport : s176_est_port_relation_weak)
    (hn : 3 ≤ n) (hL : LocalizationData E e f g δ) (hGT : GenericTableData E e f g δ) (hR : AV_EventRadius E δ)
    (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g) : ExtremeTransportData hn E e f g δ where
  singleton_rows_present := PRE_176_singleton_rows_present E e f g δ
  graphs_complementary := PRE_176_graphs_complementary hL
  sign_branch := PRE_176_sign_branch hGT
  transport_x := fun _ _ ht ht' hop hs _ _ _ hext _ hQ hfull =>
    s176_est_row_weak hF hport hn hL hR hef heg hfg ht ht' hop hs hext hQ hfull
      ((P1.mem_triangleSupports _).mpr (Or.inl rfl))
  transport_y := fun _ _ ht ht' hop hs _ _ _ hext _ hQ hfull =>
    s176_est_row_weak hF hport hn hL hR hef heg hfg ht ht' hop hs hext hQ hfull
      ((P1.mem_triangleSupports _).mpr (Or.inr (Or.inl rfl)))
  transport_z := fun _ _ ht ht' hop hs _ _ _ hext _ hQ hfull =>
    s176_est_row_weak hF hport hn hL hR hef heg hfg ht ht' hop hs hext hQ hfull
      ((P1.mem_triangleSupports _).mpr (Or.inr (Or.inr rfl)))

end S176Ledger

/-- **The RA ledger of row 176 re-based on the weak port** — `est_ledger` (RALedgers.lean:1598) with
`est_port_relation` replaced by `s176_est_port_relation_weak`; the body is byte-identical. -/
theorem s176_est_ledger_weak (hF : CV.CarrierSlotFloor) (hport : s176_est_port_relation_weak) :
    RowShape @ExtremeTransportData := by
  intro n _ hn E e f g h3 h4e h4f h4g hE
  obtain ⟨δL, hδL, hδLr, hL⟩ := localization E e f g h3 h4e h4f h4g hE
  obtain ⟨δG, hδG, -, hGT⟩ := generic_table E e f g h3 h4e h4f h4g hE
  obtain ⟨δR, hδR, -, hR⟩ := AV_exists_eventRadius hE
  have hef : e ≠ f := AV_ne_of_remote h3.1
  have hfg : f ≠ g := AV_ne_of_remote h3.2.1
  have heg : e ≠ g := AV_ne_of_remote h3.2.2.1
  refine ⟨min δL (min δG δR), lt_min hδL (lt_min hδG hδR), (min_le_left _ _).trans hδLr, ?_⟩
  have hL' := F1.localizationData_mono (min_le_left δL (min δG δR)) hL
  have hGT' := SEL_genericTableData_mono ((min_le_right δL (min δG δR)).trans (min_le_left δG δR)) hGT
  have hR' := AV_eventRadius_mono ((min_le_right δL (min δG δR)).trans (min_le_right δG δR)) hR
  exact s176_est_extremeTransportData_weak hF hport hn hL' hGT' hR' hef heg hfg

/-- The row statement from the weak ledger (`est_extreme_transport_of` re-based). -/
theorem s176_est_extreme_transport_of_weak (hF : CV.CarrierSlotFloor) (hport : s176_est_port_relation_weak)
    (hn : 3 ≤ n) (E : CV.Event n) (e f g : ZMod n)
    (h3 : remote e f ∧ remote f g ∧ remote e g ∧ CV.rep e < CV.rep f ∧ CV.rep f < CV.rep g)
    (h4e : remote e f ∧ remote e g ∧ f ≠ g ∧ CV.rep f < CV.rep g)
    (h4f : remote f e ∧ remote f g ∧ e ≠ g ∧ CV.rep e < CV.rep g)
    (h4g : remote g e ∧ remote g f ∧ e ≠ f ∧ CV.rep e < CV.rep f)
    (hE : E.IsSimpleRIII e f g h3 h4e h4f h4g) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ E.radius ∧ ExtremeTransportData hn E e f g δ :=
  s176_est_ledger_weak hF hport n hn E e f g h3 h4e h4f h4g hE

/-- Sanity: the weak ledger recovers the accepted one from the literal interface. -/
theorem s176_est_ledger_of_strong (hF : CV.CarrierSlotFloor) (hport : est_port_relation) :
    RowShape @ExtremeTransportData :=
  s176_est_ledger_weak hF (s176_est_port_relation_weak_of_strong hport)

end

end RProof

namespace RProof

open SM SM.GeoCarrier SM.Carrier SM.Link

noncomputable section

variable {n : ℕ} [NeZero n]

/-! ## §C. The carrier-level realisation of the corner site — general lemmas on a carrier `q` of an
independent support `T` on a `CarrierGeometry` polygon `P` (the L side of row 176), with the other
side `P'` entering only through `ExactTriangleVisitOrders` (R-LOC (2)–(3) at the Gauss-word level). -/

section S176Carrier

variable (hn : 3 ≤ n) {P P' : LabelledTuple n} (hG : CarrierGeometry P)
  (hs : ∀ s, IsCrossing P s ↔ IsCrossing P' s)
  {T : Finset (Crossing P)} (hT : GeoIndependent hG.cg T) (q : GeoComponent hG.cg T)

omit [NeZero n] in
theorem s176_union_supports {x y : Crossing P} {ℓ m m' : ZMod n} (hx : x.val = {ℓ, m})
    (hy : y.val = {ℓ, m'}) : x.val ∪ y.val = {ℓ, m, m'} := by
  rw [hx, hy]
  ext z
  simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
  tauto

omit [NeZero n] in
/-- a visit on `ℓ` whose crossing contains the label `m'` and `ℓ` is THE visit of the crossing `{ℓ, m'}` -/
theorem s176_visit_eq_of_mem {y : Crossing P} {ℓ m' : ZMod n} (hy : y.val = {ℓ, m'}) (hℓm' : ℓ ≠ m')
    (w : Visit P) (hw : w.2.val = ℓ) (hm' : m' ∈ w.1.val) :
    w = visitOn y ℓ (by rw [hy]; exact Finset.mem_insert_self _ _) := by
  obtain ⟨c, ⟨i, hi⟩⟩ := w
  change i = ℓ at hw
  subst hw
  change m' ∈ c.val at hm'
  have hsub : ({i, m'} : Finset (ZMod n)) ⊆ c.val := by
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact hi
    · rw [Finset.mem_singleton.mp hz]; exact hm'
  have hval : ({i, m'} : Finset (ZMod n)) = c.val :=
    Finset.eq_of_subset_of_card_le hsub (by rw [crossing_card_two c, Finset.card_pair hℓm'])
  have hc : c = y := Subtype.ext (hval.symm.trans hy.symm)
  subst hc
  rfl

omit [NeZero n] in
/-- **No visit between two adjacent triangle visits on their shared edge** (the labelled form of
`G11_no_visit_between`, for the crossings `x = {ℓ, m}`, `y = {ℓ, m'}` and the triple `{ℓ, m, m'}`). -/
theorem s176_no_visit_between {ℓ m m' : ZMod n} (hℓm : ℓ ≠ m) (hℓm' : ℓ ≠ m') (hmm' : m ≠ m')
    (hX : ExactTriangleVisitOrders P P' ℓ m m' hs) {x y : Crossing P}
    (hx : x.val = {ℓ, m}) (hy : y.val = {ℓ, m'}) (hℓx : ℓ ∈ x.val) (hℓy : ℓ ∈ y.val)
    (w : Visit P) (hw : w.2.val = ℓ) :
    ¬ (visitParameter (visitOn x ℓ hℓx) < visitParameter w ∧
        visitParameter w < visitParameter (visitOn y ℓ hℓy)) ∧
    ¬ (visitParameter (visitOn y ℓ hℓy) < visitParameter w ∧
        visitParameter w < visitParameter (visitOn x ℓ hℓx)) := by
  set vx := visitOn x ℓ hℓx with hvx
  set vy := visitOn y ℓ hℓy with hvy
  have hunion : x.val ∪ y.val = {ℓ, m, m'} := s176_union_supports hx hy
  have hunion' : y.val ∪ x.val = {ℓ, m, m'} := by rw [Finset.union_comm]; exact hunion
  have hnA : ∀ w : Visit P, w.2.val = ℓ → w ≠ vy → x.val ∪ w.1.val ≠ {ℓ, m, m'} := by
    intro w hw hwy hu
    apply hwy
    apply s176_visit_eq_of_mem hy hℓm' w hw
    have hm' : m' ∈ x.val ∪ w.1.val := by rw [hu]; simp
    rcases Finset.mem_union.mp hm' with h | h
    · exfalso
      rw [hx, Finset.mem_insert, Finset.mem_singleton] at h
      rcases h with h | h
      · exact hℓm' h.symm
      · exact hmm' h.symm
    · exact h
  have hnB : ∀ w : Visit P, w.2.val = ℓ → w ≠ vx → y.val ∪ w.1.val ≠ {ℓ, m, m'} := by
    intro w hw hwx hu
    apply hwx
    apply s176_visit_eq_of_mem hx hℓm w hw
    have hm : m ∈ y.val ∪ w.1.val := by rw [hu]; simp
    rcases Finset.mem_union.mp hm with h | h
    · exfalso
      rw [hy, Finset.mem_insert, Finset.mem_singleton] at h
      rcases h with h | h
      · exact hℓm h.symm
      · exact hmm' h
    · exact h
  constructor
  · rintro ⟨h1, h2⟩
    have hwx : w ≠ vx := fun h => by rw [h] at h1; exact lt_irrefl _ h1
    have hwy : w ≠ vy := fun h => by rw [h] at h2; exact lt_irrefl _ h2
    have h1' := ((hX vx w hw.symm).2 (hnA w hw hwy)).mp h1
    have h2' := ((hX w vy hw).2 (by rw [Finset.union_comm]; exact hnB w hw hwx)).mp h2
    have h3 := ((hX vx vy rfl).1 hunion).mp (h1.trans h2)
    exact lt_irrefl _ ((h1'.trans h2').trans h3)
  · rintro ⟨h1, h2⟩
    have hwx : w ≠ vx := fun h => by rw [h] at h2; exact lt_irrefl _ h2
    have hwy : w ≠ vy := fun h => by rw [h] at h1; exact lt_irrefl _ h1
    have h1' := ((hX vy w hw.symm).2 (hnB w hw hwx)).mp h1
    have h2' := ((hX w vx hw).2 (by rw [Finset.union_comm]; exact hnA w hw hwy)).mp h2
    have h3 := ((hX vy vx rfl).1 hunion').mp (h1.trans h2)
    exact lt_irrefl _ ((h1'.trans h2').trans h3)

include hn in
/-- the `ρ_T`-successor of an unselected visit is the next visit on its edge when no visit lies between -/
theorem s176_succ_of_lt {x y : Crossing P} {ℓ : ZMod n} (hℓx : ℓ ∈ x.val) (hℓy : ℓ ∈ y.val)
    (hxT : x ∉ T)
    (hlt : visitParameter (visitOn x ℓ hℓx) < visitParameter (visitOn y ℓ hℓy))
    (hnb : ∀ w : Visit P, w.2.val = ℓ →
      ¬ (visitParameter (visitOn x ℓ hℓx) < visitParameter w ∧
          visitParameter w < visitParameter (visitOn y ℓ hℓy))) :
    geoSmoothingSuccessor hG.cg T (Sum.inr (visitOn x ℓ hℓx)) = Sum.inr (visitOn y ℓ hℓy) := by
  rw [geoSmoothingSuccessor_visit_of_not_mem hG.cg T _ hxT]
  exact gu1_markSuccessor_eq_of_adjacent hn hG.cg rfl hlt hnb

include hn hT in
/-- **Distinct corners of a carrier sit at distinct points** (`tail_off` + nonzero edges). -/
theorem s176_cornerPolygon_inj {i j : ZMod (geoCornerCount hG.cg T q)}
    (h : geoCornerPolygon hG.cg T q i = geoCornerPolygon hG.cg T q j) : i = j := by
  by_contra hij
  have hmem : geoCornerPolygon hG.cg T q i ∈ edgeSegment (geoCornerPolygon hG.cg T q) j :=
    ⟨0, le_rfl, zero_le_one, by rw [edgePoint_zero]; exact h⟩
  by_cases hinc : incident i j
  · rcases hinc with hj | hj
    · apply geoCornerPolygon_edge_ne_zero_of_independent hn hG.cg hT q j
      have h' : geoCornerPolygon hG.cg T q (j + 1) = geoCornerPolygon hG.cg T q j := by
        rw [hj, sub_add_cancel, ← hj]; exact h
      show geoCornerPolygon hG.cg T q (j + 1) - geoCornerPolygon hG.cg T q j = 0
      rw [h', sub_self]
    · exact hij hj.symm
  · exact geoCornerPolygon_tail_off hn hG hT q i j hinc hmem

/-- **The strands of the lift of a retained crossing** are the carrier edges of its two visits
(`G11_carrierEdge_isCrossing`, `G11_carrierEdge_crossingPoint`, injectivity of crossing points). -/
theorem s176_lift_val (w : Visit P) (hw : w.1 ∈ geoCarrierCrossings hG.cg T q) :
    ((geoCarrierCrossingEquiv hn hG hT q).symm ⟨w.1, hw⟩).val =
      {(⟨0, G11_carrierEdge hn hG hT q w hw⟩ : (geoCarrierShadow hn hG hT q).Strand),
       ⟨0, G11_carrierEdge hn hG hT q (visitTwin w) (by rw [visitTwin_crossing]; exact hw)⟩} := by
  have hc := G11_carrierEdge_isCrossing hn hG hT q w hw
  have hgen := geoCarrierShadow_generic hn hG hT q
  set x' : (geoCarrierShadow hn hG hT q).Crossing :=
    (Shadow.singleCrossingEquiv (geoCarrierPolyComp hn hG hT q)).symm (xPair hc) with hx'
  have h1 : (geoCarrierShadow hn hG hT q).crossingPoint
      ((geoCarrierCrossingEquiv hn hG hT q).symm ⟨w.1, hw⟩) = crossingPoint w.1 := by
    rw [← crossingPoint_geoCarrierCrossingEquiv, Equiv.apply_symm_apply]
  have h2 : (geoCarrierShadow hn hG hT q).crossingPoint x' = crossingPoint w.1 := by
    rw [Shadow.single_crossingPoint _ hgen, hx', Equiv.apply_symm_apply]
    exact G11_carrierEdge_crossingPoint hn hG hT q w hw hc
  have heq : (geoCarrierCrossingEquiv hn hG hT q).symm ⟨w.1, hw⟩ = x' :=
    hgen.crossingPoint_injective (h1.trans h2.symm)
  rw [heq, hx']
  show ((xPair hc).val.map (Shadow.singleStrandEquiv (geoCarrierPolyComp hn hG hT q)).symm.toEmbedding) = _
  rw [show (xPair hc).val = {G11_carrierEdge hn hG hT q w hw,
      G11_carrierEdge hn hG hT q (visitTwin w) (by rw [visitTwin_crossing]; exact hw)} from rfl,
    Finset.map_insert, Finset.map_singleton]
  rfl

include hn hT in
/-- **The next corner after a block mark**: if `ρ^r c_k` is an (unselected) block mark of the edge `k`
and its `ρ`-successor is a true corner, that corner is `c_{k+1}` (`geoCornerPolygon_block`). -/
theorem s176_next_corner {k : ZMod (geoCornerCount hG.cg T q)} {r : ℕ} {w : Visit P}
    (hρ : (geoSmoothingSuccessor hG.cg T ^ r) (geoCornerMark hG.cg T q k) = Sum.inr w)
    (hb : GeoBlockInterior hG.cg T q k r) {m : Mark P} (hm : IsTrueCorner T m)
    (hsucc : geoSmoothingSuccessor hG.cg T (Sum.inr w) = m) :
    geoCornerMark hG.cg T q (k + 1) = m := by
  have hblock := geoCornerPolygon_block hn hG.cg hT q k
  obtain ⟨mk, hmk1, hchain, hmid, -, -, -, -, -⟩ := hblock
  have hρ1 : (geoSmoothingSuccessor hG.cg T ^ (r + 1)) (geoCornerMark hG.cg T q k) = m := by
    rw [pow_succ', Equiv.Perm.mul_apply, hρ, hsucc]
  rcases lt_trichotomy (r + 1) mk with hlt | heq | hgt
  · exfalso
    obtain ⟨v, hv, hvT, -⟩ := hmid (r + 1) (by omega) hlt
    rw [hρ1] at hv
    rw [hv] at hm
    exact hvT hm
  · rw [← hchain, ← heq, hρ1]
  · exfalso
    obtain ⟨v, hv, hvT, -⟩ := hb mk hmk1 (by omega)
    rw [hchain] at hv
    have := isTrueCorner_geoCornerMark hG.cg T q (k + 1)
    rw [hv] at this
    exact hvT this

/-- **The carrier edge of the first block mark after a corner**: if `ρ c_k` is a retained visit on the
outgoing edge of `c_k`, its carrier edge is `k` (`geo_block_mark_eq`). -/
theorem s176_carrierEdge_of_succ {k : ZMod (geoCornerCount hG.cg T q)} {w : Visit P}
    (hw : w.1 ∈ geoCarrierCrossings hG.cg T q)
    (hsucc : geoSmoothingSuccessor hG.cg T (geoCornerMark hG.cg T q k) = Sum.inr w)
    (hedge : w.2.val = (geoOutSlot hG.cg T (geoCornerMark hG.cg T q k)).1) :
    G11_carrierEdge hn hG hT q w hw = k := by
  obtain ⟨r', -, hρ', hb', -, -⟩ := gu1_carrierEdge_block hn hG hT q w hw
  have hwT : w.1 ∉ T := ((mem_geoCarrierCrossings hG.cg T q w.1).mp hw).1
  have hb1 : GeoBlockInterior hG.cg T q k 1 := by
    intro i h1 hi
    have hi1 : i = 1 := by omega
    subst hi1
    exact ⟨w, by rw [pow_one]; exact hsucc, hwT, hedge⟩
  exact (geo_block_mark_eq hG.cg T q hb' hb1 (hρ'.trans (by rw [pow_one]; exact hsucc.symm))).1

/-- the owner of a retained visit is `q` -/
theorem s176_owner_of_retained {x : Crossing P} (hx : x ∈ geoCarrierCrossings hG.cg T q) (w : Visit P)
    (hw : w.1 = x) : geoOwner hG.cg T (Sum.inr w) = q :=
  ((mem_geoCarrierCrossings hG.cg T q x).mp hx).2 w hw

/-- **From the index form of clearance to the strand form of `s176_CornerSite.clear`** on the
one-component carrier shadow. -/
theorem s176_clear_of_indices (kA kB kC : ZMod (geoCornerCount hG.cg T q)) (K : Set Plane)
    (hcl : ∀ h : ZMod (geoCornerCount hG.cg T q), h ≠ kA → h ≠ kB → h ≠ kC →
      ∀ x ∈ edgeSegment (geoCornerPolygon hG.cg T q) h, x ∉ K) :
    ∀ w : (geoCarrierShadow hn hG hT q).Strand,
      w ≠ ⟨(0 : Fin 1), kA⟩ → w ≠ ⟨(0 : Fin 1), kB⟩ → w ≠ ⟨(0 : Fin 1), kC⟩ →
      Disjoint ((geoCarrierShadow hn hG hT q).seg w) K := by
  intro w hA hB hC
  rw [← Shadow.single_strand_eta _ w] at hA hB hC ⊢
  have hA' : w.2 ≠ kA := fun e => hA (congrArg (fun k : ZMod (geoCornerCount hG.cg T q) =>
    (⟨(0 : Fin 1), k⟩ : (geoCarrierShadow hn hG hT q).Strand)) e)
  have hB' : w.2 ≠ kB := fun e => hB (congrArg (fun k : ZMod (geoCornerCount hG.cg T q) =>
    (⟨(0 : Fin 1), k⟩ : (geoCarrierShadow hn hG hT q).Strand)) e)
  have hC' : w.2 ≠ kC := fun e => hC (congrArg (fun k : ZMod (geoCornerCount hG.cg T q) =>
    (⟨(0 : Fin 1), k⟩ : (geoCarrierShadow hn hG hT q).Strand)) e)
  show Disjoint (edgeSegment (geoCornerPolygon hG.cg T q) w.2) K
  exact Set.disjoint_left.mpr fun x hx hxK => hcl w.2 hA' hB' hC' x hx hxK

end S176Carrier

end

end RProof

namespace RProof

open SM SM.GeoCarrier SM.Carrier SM.Link

noncomputable section

variable {n : ℕ} [NeZero n]

section S176Corner

variable (hn : 3 ≤ n) {P P' : LabelledTuple n} (hG : CarrierGeometry P)
  (hs : ∀ s, IsCrossing P s ↔ IsCrossing P' s)
  {T : Finset (Crossing P)} (hT : GeoIndependent hG.cg T) (q : GeoComponent hG.cg T)

omit [NeZero n] in
/-- the twin of the visit of `x = {ℓ, m}` on `ℓ` is its visit on `m` -/
theorem s176_visitTwin_eq {x : Crossing P} {ℓ m : ZMod n} (_hx : x.val = {ℓ, m}) (hℓm : ℓ ≠ m)
    (hℓx : ℓ ∈ x.val) (hmx : m ∈ x.val) : visitTwin (visitOn x ℓ hℓx) = visitOn x m hmx := by
  rcases visit_eq_or_twin (visitOn x ℓ hℓx) (visitOn x m hmx) rfl with h | h
  · exfalso
    have := congrArg (fun w : Visit P => w.2.val) h
    exact hℓm (this.symm)
  · exact h.symm

omit [NeZero n] in
theorem s176_mem_left {x : Crossing P} {ℓ m : ZMod n} (hx : x.val = {ℓ, m}) : ℓ ∈ x.val := by
  rw [hx]; exact Finset.mem_insert_self _ _

omit [NeZero n] in
theorem s176_mem_right {x : Crossing P} {ℓ m : ZMod n} (hx : x.val = {ℓ, m}) : m ∈ x.val := by
  rw [hx]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)

omit [NeZero n] in
theorem s176_pair_comm' {x : Crossing P} {ℓ m : ZMod n} (hx : x.val = {ℓ, m}) : x.val = {m, ℓ} := by
  rw [hx, Finset.pair_comm]

omit [NeZero n] in
/-- two crossings with a common label and different second labels are distinct -/
theorem s176_ne_of_supports {x y : Crossing P} {ℓ m m' : ZMod n} (hx : x.val = {ℓ, m})
    (hy : y.val = {ℓ, m'}) (hℓm' : ℓ ≠ m') (hmm' : m ≠ m') : x ≠ y := by
  intro h
  have : m' ∈ x.val := by rw [h, hy]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  rw [hx, Finset.mem_insert, Finset.mem_singleton] at this
  rcases this with h1 | h1
  · exact hℓm' h1.symm
  · exact hmm' h1.symm

/-- a corner mark of `q` is owned by `q` -/
theorem s176_owner_cornerMark (k : ZMod (geoCornerCount hG.cg T q)) :
    geoOwner hG.cg T (geoCornerMark hG.cg T q k) = q :=
  (geoCornerMark_mem hG.cg T q k).1

include hn hT in
/-- **No carrier has two corners at one crossing point**: the two visits of a selected crossing `j`
cannot both be corner marks of `q` (distinct corners sit at distinct points, `s176_cornerPolygon_inj`). -/
theorem s176_no_two_corners {j : Crossing P} (hjT : j ∈ T) {a b : ZMod n} (hab : a ≠ b)
    (haj : a ∈ j.val) (hbj : b ∈ j.val)
    (h1 : geoOwner hG.cg T (Sum.inr (visitOn j a haj)) = q)
    (h2 : geoOwner hG.cg T (Sum.inr (visitOn j b hbj)) = q) : False := by
  obtain ⟨k₁, hk₁⟩ := geoCornerMark_exists_of_owner hG.cg T q _ h1 (by exact hjT)
  obtain ⟨k₂, hk₂⟩ := geoCornerMark_exists_of_owner hG.cg T q _ h2 (by exact hjT)
  have hpt : geoCornerPolygon hG.cg T q k₁ = geoCornerPolygon hG.cg T q k₂ := by
    rw [geoCornerPolygon_apply, geoCornerPolygon_apply, hk₁, hk₂,
      geoMarkPosition_evaluation_visit, geoMarkPosition_evaluation_visit]
    rfl
  have hk : k₁ = k₂ := s176_cornerPolygon_inj hn hG hT q hpt
  rw [hk, hk₂] at hk₁
  have hvis : visitOn j b hbj = visitOn j a haj := Sum.inr_injective hk₁
  exact hab (congrArg (fun w : Visit P => w.2.val) hvis).symm

/-! ### The labelled corner: `j = {a, b} ∈ T` the corner, `u = {a, c}`, `v = {b, c}` retained -/

variable {a b c : ZMod n} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
  (hX : ExactTriangleVisitOrders P P' a b c hs)
  {j u v : Crossing P} (hj : j.val = {a, b}) (hu : u.val = {a, c}) (hv : v.val = {b, c})
  (hjT : j ∈ T) (huq : u ∈ geoCarrierCrossings hG.cg T q) (hvq : v ∈ geoCarrierCrossings hG.cg T q)

include hab hac hbc hX hj hu in
/-- no visit between `u` and `j` on `a` (both orders) -/
theorem s176_nb_a (w : Visit P) (hw : w.2.val = a) :
    ¬ (visitParameter (visitOn u a (s176_mem_left hu)) < visitParameter w ∧
        visitParameter w < visitParameter (visitOn j a (s176_mem_left hj))) ∧
    ¬ (visitParameter (visitOn j a (s176_mem_left hj)) < visitParameter w ∧
        visitParameter w < visitParameter (visitOn u a (s176_mem_left hu))) :=
  s176_no_visit_between hs hac hab hbc.symm
    (gu2_exact_of_eq hs (by ext z; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto) hX)
    hu hj _ _ w hw

include hab hac hbc hX hj hv in
/-- no visit between `j` and `v` on `b` (both orders) -/
theorem s176_nb_b (w : Visit P) (hw : w.2.val = b) :
    ¬ (visitParameter (visitOn j b (s176_mem_right hj)) < visitParameter w ∧
        visitParameter w < visitParameter (visitOn v b (s176_mem_left hv))) ∧
    ¬ (visitParameter (visitOn v b (s176_mem_left hv)) < visitParameter w ∧
        visitParameter w < visitParameter (visitOn j b (s176_mem_right hj))) :=
  s176_no_visit_between hs hab.symm hbc hac
    (gu2_exact_of_eq hs (by ext z; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto) hX)
    (s176_pair_comm' hj) hv _ _ w hw

include hab hac hbc hX hu hv in
/-- no visit between `u` and `v` on `c` (both orders) -/
theorem s176_nb_c (w : Visit P) (hw : w.2.val = c) :
    ¬ (visitParameter (visitOn u c (s176_mem_right hu)) < visitParameter w ∧
        visitParameter w < visitParameter (visitOn v c (s176_mem_right hv))) ∧
    ¬ (visitParameter (visitOn v c (s176_mem_right hv)) < visitParameter w ∧
        visitParameter w < visitParameter (visitOn u c (s176_mem_right hu))) :=
  s176_no_visit_between hs hac.symm hbc.symm hab
    (gu2_exact_of_eq hs (by ext z; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto) hX)
    (s176_pair_comm' hu) (s176_pair_comm' hv) _ _ w hw

include hG in
/-- distinct crossings on one edge have distinct visit parameters -/
theorem s176_param_ne {x y : Crossing P} (hxy : x ≠ y) {ℓ : ZMod n} (hx : ℓ ∈ x.val) (hy : ℓ ∈ y.val) :
    visitParameter (visitOn x ℓ hx) ≠ visitParameter (visitOn y ℓ hy) :=
  gu2_param_ne_of_xPair_ne hG hxy hx hy

include hn hT hab hac hbc hX hj hu hv hjT huq hvq in
/-- **Cyclicity of the corner from retention**: `u` before `j` on `a` iff `j` before `v` on `b` —
otherwise both visits of `j` would be corners of `q` at one point (`s176_no_two_corners`). -/
theorem s176_cyclic :
    visitParameter (visitOn u a (s176_mem_left hu)) < visitParameter (visitOn j a (s176_mem_left hj)) ↔
      visitParameter (visitOn j b (s176_mem_right hj)) < visitParameter (visitOn v b (s176_mem_left hv)) := by
  have huT : u ∉ T := ((mem_geoCarrierCrossings hG.cg T q u).mp huq).1
  have hvT : v ∉ T := ((mem_geoCarrierCrossings hG.cg T q v).mp hvq).1
  have hju : j ≠ u := s176_ne_of_supports hj hu hac hbc
  have hjv : j ≠ v := s176_ne_of_supports (s176_pair_comm' hj) hv hbc hac
  have hqu : geoOwner hG.cg T (Sum.inr (visitOn u a (s176_mem_left hu))) = q :=
    s176_owner_of_retained hG q huq _ rfl
  have hqv : geoOwner hG.cg T (Sum.inr (visitOn v b (s176_mem_left hv))) = q :=
    s176_owner_of_retained hG q hvq _ rfl
  have htwin_a : visitTwin (visitOn j a (s176_mem_left hj)) = visitOn j b (s176_mem_right hj) :=
    s176_visitTwin_eq hj hab _ _
  have htwin_b : visitTwin (visitOn j b (s176_mem_right hj)) = visitOn j a (s176_mem_left hj) :=
    s176_visitTwin_eq (s176_pair_comm' hj) hab.symm _ _
  constructor
  · intro hlt_a
    by_contra hnot
    have hlt_b : visitParameter (visitOn v b (s176_mem_left hv)) <
        visitParameter (visitOn j b (s176_mem_right hj)) :=
      lt_of_le_of_ne (not_lt.mp hnot) (s176_param_ne hG hjv.symm _ _)
    -- `ρ (u, a) = (j, a)` and `ρ (v, b) = (j, b)`: both corners owned by `q`
    have h1 : geoSmoothingSuccessor hG.cg T (Sum.inr (visitOn u a (s176_mem_left hu))) =
        Sum.inr (visitOn j a (s176_mem_left hj)) :=
      s176_succ_of_lt hn hG _ _ huT hlt_a (fun w hw => (s176_nb_a hs hab hac hbc hX hj hu w hw).1)
    have h2 : geoSmoothingSuccessor hG.cg T (Sum.inr (visitOn v b (s176_mem_left hv))) =
        Sum.inr (visitOn j b (s176_mem_right hj)) :=
      s176_succ_of_lt hn hG _ _ hvT hlt_b (fun w hw => (s176_nb_b hs hab hac hbc hX hj hv w hw).2)
    exact s176_no_two_corners hn hG hT q hjT hab _ _
      (by rw [← h1, geoOwner_successor]; exact hqu)
      (by rw [← h2, geoOwner_successor]; exact hqv)
  · intro hlt_b
    by_contra hnot
    have hlt_a : visitParameter (visitOn j a (s176_mem_left hj)) <
        visitParameter (visitOn u a (s176_mem_left hu)) :=
      lt_of_le_of_ne (not_lt.mp hnot) (s176_param_ne hG hju _ _)
    -- `ρ (j, a) = (v, b)` and `ρ (j, b) = (u, a)`: both corners owned by `q`
    have h1 : geoSmoothingSuccessor hG.cg T (Sum.inr (visitOn j a (s176_mem_left hj))) =
        Sum.inr (visitOn v b (s176_mem_left hv)) := by
      rw [geoSmoothingSuccessor_visit_of_mem hG.cg T _ hjT, htwin_a]
      exact gu1_markSuccessor_eq_of_adjacent hn hG.cg rfl hlt_b
        (fun w hw => (s176_nb_b hs hab hac hbc hX hj hv w hw).1)
    have h2 : geoSmoothingSuccessor hG.cg T (Sum.inr (visitOn j b (s176_mem_right hj))) =
        Sum.inr (visitOn u a (s176_mem_left hu)) := by
      rw [geoSmoothingSuccessor_visit_of_mem hG.cg T _ hjT, htwin_b]
      exact gu1_markSuccessor_eq_of_adjacent hn hG.cg rfl hlt_a
        (fun w hw => (s176_nb_a hs hab hac hbc hX hj hu w hw).2)
    exact s176_no_two_corners hn hG hT q hjT hab _ _
      (by rw [← geoOwner_successor, h1]; exact hqv)
      (by rw [← geoOwner_successor, h2]; exact hqu)

include hn hab hac hbc hX hj hu hv hjT huq hvq in
/-- **The corner, case 1 (`u` before `j` on `a`)**: the corner after the carrier edge `kA` of `(u, a)` is
the visit `(j, a)`; the next edge `kA + 1` carries `(v, b)`; the two `c`-visits share one carrier edge. -/
theorem s176_corner_case1
    (hlt_a : visitParameter (visitOn u a (s176_mem_left hu)) < visitParameter (visitOn j a (s176_mem_left hj))) :
    geoCornerMark hG.cg T q (G11_carrierEdge hn hG hT q (visitOn u a (s176_mem_left hu)) huq + 1) =
        Sum.inr (visitOn j a (s176_mem_left hj)) ∧
    geoCornerPolygon hG.cg T q (G11_carrierEdge hn hG hT q (visitOn u a (s176_mem_left hu)) huq + 1) =
        crossingPoint j ∧
    G11_carrierEdge hn hG hT q (visitOn v b (s176_mem_left hv)) hvq =
        G11_carrierEdge hn hG hT q (visitOn u a (s176_mem_left hu)) huq + 1 ∧
    G11_carrierEdge hn hG hT q (visitOn v c (s176_mem_right hv)) hvq =
        G11_carrierEdge hn hG hT q (visitOn u c (s176_mem_right hu)) huq := by
  have huT : u ∉ T := ((mem_geoCarrierCrossings hG.cg T q u).mp huq).1
  have hlt_b := (s176_cyclic hn hG hs hT q hab hac hbc hX hj hu hv hjT huq hvq).mp hlt_a
  have htwin_a : visitTwin (visitOn j a (s176_mem_left hj)) = visitOn j b (s176_mem_right hj) :=
    s176_visitTwin_eq hj hab _ _
  set kA := G11_carrierEdge hn hG hT q (visitOn u a (s176_mem_left hu)) huq with hkA
  -- `ρ (u, a) = (j, a)`
  have hsucc1 : geoSmoothingSuccessor hG.cg T (Sum.inr (visitOn u a (s176_mem_left hu))) =
      Sum.inr (visitOn j a (s176_mem_left hj)) :=
    s176_succ_of_lt hn hG _ _ huT hlt_a (fun w hw => (s176_nb_a hs hab hac hbc hX hj hu w hw).1)
  -- the corner `c_{kA+1} = (j, a)`
  obtain ⟨r, -, hρ, hb, -, -⟩ := gu1_carrierEdge_block hn hG hT q (visitOn u a (s176_mem_left hu)) huq
  have hcorner : geoCornerMark hG.cg T q (kA + 1) = Sum.inr (visitOn j a (s176_mem_left hj)) :=
    s176_next_corner hn hG hT q hρ hb (by exact hjT) hsucc1
  refine ⟨hcorner, ?_, ?_, ?_⟩
  · rw [geoCornerPolygon_apply, hcorner, geoMarkPosition_evaluation_visit]
    rfl
  · -- `ρ (j, a) = (v, b)`, on the outgoing edge `b` of the corner
    have hsucc2 : geoSmoothingSuccessor hG.cg T (geoCornerMark hG.cg T q (kA + 1)) =
        Sum.inr (visitOn v b (s176_mem_left hv)) := by
      rw [hcorner, geoSmoothingSuccessor_visit_of_mem hG.cg T _ hjT, htwin_a]
      exact gu1_markSuccessor_eq_of_adjacent hn hG.cg rfl hlt_b
        (fun w hw => (s176_nb_b hs hab hac hbc hX hj hv w hw).1)
    have hedge : (visitOn v b (s176_mem_left hv)).2.val =
        (geoOutSlot hG.cg T (geoCornerMark hG.cg T q (kA + 1))).1 := by
      rw [hcorner, geoOutSlot_selected hG.cg T _ hjT, htwin_a]
      rfl
    exact s176_carrierEdge_of_succ hn hG hT q hvq hsucc2 hedge
  · exact G11_carrierEdge_eq_of_adjacent hn hG hT q hvq huq rfl
      (fun w hw => ⟨(s176_nb_c hs hab hac hbc hX hu hv w hw).2, (s176_nb_c hs hab hac hbc hX hu hv w hw).1⟩)

end S176Corner

end

end RProof

namespace RProof

open SM SM.GeoCarrier SM.Carrier SM.Link

noncomputable section

variable {n : ℕ} [NeZero n]

section S176Clear

variable (hn : 3 ≤ n) {P P' : LabelledTuple n} (hG : CarrierGeometry P)
  (hs : ∀ s, IsCrossing P s ↔ IsCrossing P' s)
  {T : Finset (Crossing P)} (hT : GeoIndependent hG.cg T) (q : GeoComponent hG.cg T)

/-- the crossing point of the lift of a retained crossing is its crossing point -/
theorem s176_liftPoint {x : Crossing P} (hx : x ∈ geoCarrierCrossings hG.cg T q) :
    (geoCarrierShadow hn hG hT q).crossingPoint ((geoCarrierCrossingEquiv hn hG hT q).symm ⟨x, hx⟩) =
      crossingPoint x := by
  rw [← crossingPoint_geoCarrierCrossingEquiv, Equiv.apply_symm_apply]

variable {a b c : ZMod n} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
  (hX : ExactTriangleVisitOrders P P' a b c hs)
  {j u v : Crossing P} (hj : j.val = {a, b}) (hu : u.val = {a, c}) (hv : v.val = {b, c})
  (hjT : j ∈ T) (huq : u ∈ geoCarrierCrossings hG.cg T q) (hvq : v ∈ geoCarrierCrossings hG.cg T q)
  (hQT : ∀ x ∈ T, x ≠ j → ∃ ℓ ∈ x.val, ℓ ≠ a ∧ ℓ ≠ b ∧ ℓ ≠ c)

omit [NeZero n] in
include hj in
theorem s176_hcab : IsCrossing P {a, b} := by rw [← hj]; exact j.2
omit [NeZero n] in
include hu in
theorem s176_hcac : IsCrossing P {a, c} := by rw [← hu]; exact u.2
omit [NeZero n] in
include hv in
theorem s176_hcbc : IsCrossing P {b, c} := by rw [← hv]; exact v.2

omit [NeZero n] in
include hj in
theorem s176_xPair_j : xPair (s176_hcab hj) = j := Subtype.ext hj.symm
omit [NeZero n] in
include hu in
theorem s176_xPair_u : xPair (s176_hcac hu) = u := Subtype.ext hu.symm
omit [NeZero n] in
include hv in
theorem s176_xPair_v : xPair (s176_hcbc hv) = v := Subtype.ext hv.symm

include hn hT hab hac hbc hX hj hu hv hjT hQT in
/-- **The only corner of the carrier inside the closed triangle is the `j`-corner** (case 1 data:
`c_{kA+1} = (j, a)`): a corner is a vertex of `P` (off the triangle, `gu2_clear`), or a `T`-visit — of `j`
(then it is `(j, a)`, or `(j, b)` and two corners would sit at one point), or of a foreign crossing whose
foreign edge misses the closed triangle (`gu2_clear_closed`). -/
theorem s176_corner_mem_K {kA : ZMod (geoCornerCount hG.cg T q)}
    (hcorner : geoCornerMark hG.cg T q (kA + 1) = Sum.inr (visitOn j a (s176_mem_left hj)))
    (i : ZMod (geoCornerCount hG.cg T q))
    (hi : geoCornerPolygon hG.cg T q i ∈
      convexHull ℝ {crossingPoint j, crossingPoint u, crossingPoint v}) : i = kA + 1 := by
  have hcl := gu2_clear hG hs hab hac hbc (s176_hcab hj) (s176_hcac hu) (s176_hcbc hv) hX
  have hclosed := gu2_clear_closed hG hs hab hac hbc (s176_hcab hj) (s176_hcac hu) (s176_hcbc hv) hX
  rw [s176_xPair_j hj, s176_xPair_u hu, s176_xPair_v hv] at hcl hclosed
  rw [geoCornerPolygon_apply] at hi
  have hcorn := isTrueCorner_geoCornerMark hG.cg T q i
  rcases hmark : geoCornerMark hG.cg T q i with vtx | w
  · rw [hmark, geoMarkPosition_evaluation_vertex] at hi
    exact (hcl.2 vtx hi).elim
  · rw [hmark, geoMarkPosition_evaluation_visit] at hi
    rw [hmark, isTrueCorner_visit] at hcorn
    by_cases hwj : w.1 = j
    · rcases visit_eq_or_twin (visitOn j a (s176_mem_left hj)) w hwj with hw | hw
      · apply geoCornerMark_injective hG.cg T q
        rw [hmark, hw, hcorner]
      · exfalso
        rw [s176_visitTwin_eq hj hab _ (s176_mem_right hj)] at hw
        have h1 : geoOwner hG.cg T (Sum.inr (visitOn j a (s176_mem_left hj))) = q := by
          rw [← hcorner]; exact s176_owner_cornerMark hG q (kA + 1)
        have h2 : geoOwner hG.cg T (Sum.inr (visitOn j b (s176_mem_right hj))) = q := by
          rw [← hw, ← hmark]; exact s176_owner_cornerMark hG q i
        exact s176_no_two_corners hn hG hT q hjT hab _ _ h1 h2
    · obtain ⟨ℓ, hℓw, hℓa, hℓb, hℓc⟩ := hQT w.1 hcorn hwj
      exact (hclosed ℓ hℓa hℓb hℓc _ (crossingPoint_mem w.1 ℓ hℓw) hi).elim

include hn hab hac hbc hX hj hu hv hjT huq hvq hQT in
/-- **Clearance of the closed contact triangle (case 1)**: every edge of the corner polygon other than
`e_in = kA`, `e_out = kA + 1` and `s = kC` misses the closed triangle `conv{pt j, pt u, pt v}`.  A carrier
edge inside `a` (resp. `b`, `c`) meeting the triangle meets it on the side `[pt j, pt u] ⊆ e_in` (resp.
`[pt j, pt v] ⊆ e_out`, `[pt u, pt v] ⊆ s`); two parallel carrier edges meeting share a corner
(`gu2_parallel_meet_vertex`), which is the `j`-corner (`s176_corner_mem_K`), and an edge through the
`j`-corner is incident to it (`geoCornerPolygon_tail_off`) — i.e. it is `e_in` or `e_out`.  Foreign carrier
edges lie inside foreign edges of `P` (`gu2_clear_closed`). -/
theorem s176_clear_case1
    (hlt_a : visitParameter (visitOn u a (s176_mem_left hu)) < visitParameter (visitOn j a (s176_mem_left hj))) :
    ∀ h : ZMod (geoCornerCount hG.cg T q),
      h ≠ G11_carrierEdge hn hG hT q (visitOn u a (s176_mem_left hu)) huq →
      h ≠ G11_carrierEdge hn hG hT q (visitOn u a (s176_mem_left hu)) huq + 1 →
      h ≠ G11_carrierEdge hn hG hT q (visitOn u c (s176_mem_right hu)) huq →
      ∀ x ∈ edgeSegment (geoCornerPolygon hG.cg T q) h,
        x ∉ convexHull ℝ {crossingPoint j, crossingPoint u, crossingPoint v} := by
  obtain ⟨hcorner, hpt, hkB, hkC⟩ := s176_corner_case1 hn hG hs hT q hab hac hbc hX hj hu hv hjT huq hvq hlt_a
  set kA := G11_carrierEdge hn hG hT q (visitOn u a (s176_mem_left hu)) huq with hkA
  set kC := G11_carrierEdge hn hG hT q (visitOn u c (s176_mem_right hu)) huq with hkC0
  intro h hhA hhB hhC x hx hxK
  have hclosed := gu2_clear_closed hG hs hab hac hbc (s176_hcab hj) (s176_hcac hu) (s176_hcbc hv) hX
  rw [s176_xPair_j hj, s176_xPair_u hu, s176_xPair_v hv] at hclosed
  have hxK' : x ∈ convexHull ℝ {crossingPoint (xPair (s176_hcab hj)), crossingPoint (xPair (s176_hcac hu)),
      crossingPoint (xPair (s176_hcbc hv))} := by
    rw [s176_xPair_j hj, s176_xPair_u hu, s176_xPair_v hv]; exact hxK
  have hx₀ := gu2_edgeSegment_sub hn hG hT q h hx
  obtain ⟨c₀, hc₀, hedge₀⟩ := geoCornerPolygon_edge_smul hn hG.cg hT q h
  -- a common point with another carrier edge is a corner, hence the `j`-corner, hence `h ∈ {kA, kA+1}`
  have hnotvertex : ∀ i, x = geoCornerPolygon hG.cg T q i → False := by
    intro i hxi
    have hi := s176_corner_mem_K hn hG hs hT q hab hac hbc hX hj hu hv hjT hQT hcorner i (hxi ▸ hxK)
    rw [hi] at hxi
    have hmem : geoCornerPolygon hG.cg T q (kA + 1) ∈ edgeSegment (geoCornerPolygon hG.cg T q) h :=
      hxi ▸ hx
    have hinc : incident (kA + 1) h := by
      by_contra hn'
      exact geoCornerPolygon_tail_off hn hG hT q (kA + 1) h hn' hmem
    rcases hinc with h1 | h1
    · exact hhA (by rw [h1, add_sub_cancel_right])
    · exact hhB h1
  have hspecA := G11_carrierEdge_spec hn hG hT q (visitOn u a (s176_mem_left hu)) huq
  have hspecB := G11_carrierEdge_spec hn hG hT q (visitOn v b (s176_mem_left hv)) hvq
  have hspecC := G11_carrierEdge_spec hn hG hT q (visitOn u c (s176_mem_right hu)) huq
  have hspecC' := G11_carrierEdge_spec hn hG hT q (visitOn v c (s176_mem_right hv)) hvq
  rw [hkB] at hspecB
  rw [hkC] at hspecC'
  set lab := (geoOutSlot hG.cg T (geoCornerMark hG.cg T q h)).1 with hlab
  by_cases hla : lab = a
  · rw [hla] at hx₀ hedge₀
    obtain ⟨t, -, -, hxt⟩ := hx₀
    have hseg := gu2_line_e_mem_segment hG (s176_hcab hj) (s176_hcac hu) (s176_hcbc hv) hxK' hxt
    rw [s176_xPair_j hj, s176_xPair_u hu] at hseg
    have hA : crossingPoint u ∈ edgeSegment (geoCornerPolygon hG.cg T q) kA := hspecA.1
    have hB : crossingPoint j ∈ edgeSegment (geoCornerPolygon hG.cg T q) kA := by
      rw [← hpt]
      exact ⟨1, zero_le_one, le_rfl, by rw [edgePoint_one]⟩
    have hxkA : x ∈ edgeSegment (geoCornerPolygon hG.cg T q) kA := gu2_edgeSegment_convex hB hA hseg
    obtain ⟨cA, -, hedgeA⟩ := hspecA.2
    obtain ⟨i, hi⟩ := gu2_parallel_meet_vertex hn hG hT q hhA hedge₀ hedgeA hx hxkA
    exact hnotvertex i hi
  by_cases hlb : lab = b
  · rw [hlb] at hx₀ hedge₀
    obtain ⟨t, -, -, hxt⟩ := hx₀
    have hseg := gu2_line_f_mem_segment hG (s176_hcab hj) (s176_hcac hu) (s176_hcbc hv) hxK' hxt
    rw [s176_xPair_j hj, s176_xPair_v hv] at hseg
    have hA : crossingPoint v ∈ edgeSegment (geoCornerPolygon hG.cg T q) (kA + 1) := hspecB.1
    have hB : crossingPoint j ∈ edgeSegment (geoCornerPolygon hG.cg T q) (kA + 1) := by
      rw [← hpt]
      exact ⟨0, le_rfl, zero_le_one, by rw [edgePoint_zero]⟩
    have hxkB : x ∈ edgeSegment (geoCornerPolygon hG.cg T q) (kA + 1) := gu2_edgeSegment_convex hB hA hseg
    obtain ⟨cB, -, hedgeB⟩ := hspecB.2
    obtain ⟨i, hi⟩ := gu2_parallel_meet_vertex hn hG hT q hhB hedge₀ hedgeB hx hxkB
    exact hnotvertex i hi
  by_cases hlc : lab = c
  · rw [hlc] at hx₀ hedge₀
    obtain ⟨t, -, -, hxt⟩ := hx₀
    have hseg := gu2_line_g_mem_segment hG (s176_hcab hj) (s176_hcac hu) (s176_hcbc hv) hxK' hxt
    rw [s176_xPair_u hu, s176_xPair_v hv] at hseg
    have hA : crossingPoint u ∈ edgeSegment (geoCornerPolygon hG.cg T q) kC := hspecC.1
    have hB : crossingPoint v ∈ edgeSegment (geoCornerPolygon hG.cg T q) kC := hspecC'.1
    have hxkC : x ∈ edgeSegment (geoCornerPolygon hG.cg T q) kC := gu2_edgeSegment_convex hA hB hseg
    obtain ⟨cC, -, hedgeC⟩ := hspecC.2
    obtain ⟨i, hi⟩ := gu2_parallel_meet_vertex hn hG hT q hhC hedge₀ hedgeC hx hxkC
    exact hnotvertex i hi
  exact hclosed lab hla hlb hlc x hx₀ hxK

include hn hab hac hbc hX hj hu hv hjT huq hvq hQT in
/-- **The carrier corner site, case 1** (`u` before `j` on `a`): `e_in = kA` carries `u`, `e_out = kA + 1`
carries `v`, `s = kC`; `y₁ = lift u`, `y₂ = lift v`. -/
theorem s176_cornerSite_case1
    (hlt_a : visitParameter (visitOn u a (s176_mem_left hu)) < visitParameter (visitOn j a (s176_mem_left hj))) :
    ∃ Tsite : s176_CornerSite (geoPositiveLift hn hG hT q),
      Tsite.i = (0 : Fin 1) ∧ Tsite.y₁ = (geoCarrierCrossingEquiv hn hG hT q).symm ⟨u, huq⟩ ∧
        Tsite.y₂ = (geoCarrierCrossingEquiv hn hG hT q).symm ⟨v, hvq⟩ := by
  obtain ⟨hcorner, hpt, hkB, hkC⟩ := s176_corner_case1 hn hG hs hT q hab hac hbc hX hj hu hv hjT huq hvq hlt_a
  have hclear := s176_clear_case1 hn hG hs hT q hab hac hbc hX hj hu hv hjT huq hvq hQT hlt_a
  set kA := G11_carrierEdge hn hG hT q (visitOn u a (s176_mem_left hu)) huq with hkA
  set kC := G11_carrierEdge hn hG hT q (visitOn u c (s176_mem_right hu)) huq with hkC0
  set liftU := (geoCarrierCrossingEquiv hn hG hT q).symm ⟨u, huq⟩ with hliftU
  set liftV := (geoCarrierCrossingEquiv hn hG hT q).symm ⟨v, hvq⟩ with hliftV
  have hyU : liftU.val = {(⟨(0 : Fin 1), kA⟩ : (geoCarrierShadow hn hG hT q).Strand), ⟨(0 : Fin 1), kC⟩} := by
    have h0 : liftU.val = {(⟨(0 : Fin 1), kA⟩ : (geoCarrierShadow hn hG hT q).Strand),
        ⟨(0 : Fin 1), G11_carrierEdge hn hG hT q (visitTwin (visitOn u a (s176_mem_left hu)))
          (by rw [visitTwin_crossing]; exact huq)⟩} :=
      s176_lift_val hn hG hT q (visitOn u a (s176_mem_left hu)) huq
    rw [gu2_carrierEdge_congr hn hG hT q (s176_visitTwin_eq hu hac _ (s176_mem_right hu)) _ huq] at h0
    exact h0
  have hyV : liftV.val = {(⟨(0 : Fin 1), kA + 1⟩ : (geoCarrierShadow hn hG hT q).Strand), ⟨(0 : Fin 1), kC⟩} := by
    have h0 : liftV.val = {(⟨(0 : Fin 1), G11_carrierEdge hn hG hT q (visitOn v b (s176_mem_left hv)) hvq⟩ :
        (geoCarrierShadow hn hG hT q).Strand),
        ⟨(0 : Fin 1), G11_carrierEdge hn hG hT q (visitTwin (visitOn v b (s176_mem_left hv)))
          (by rw [visitTwin_crossing]; exact hvq)⟩} :=
      s176_lift_val hn hG hT q (visitOn v b (s176_mem_left hv)) hvq
    rw [gu2_carrierEdge_congr hn hG hT q (s176_visitTwin_eq hv hbc _ (s176_mem_right hv)) _ hvq, hkB, hkC] at h0
    exact h0
  have hclear' : ∀ h : ZMod (geoCornerCount hG.cg T q), h ≠ kA → h ≠ kA + 1 → h ≠ kC →
      ∀ x ∈ edgeSegment (geoCornerPolygon hG.cg T q) h,
        x ∉ convexHull ℝ {crossingPoint u, crossingPoint j, crossingPoint v} := by
    intro h hA hB hC x hx
    rw [Set.insert_comm]
    exact hclear h hA hB hC x hx
  have hcl'' := s176_clear_of_indices hn hG hT q kA (kA + 1) kC _ hclear'
  refine ⟨⟨(0 : Fin 1), kA, ?_, ⟨(0 : Fin 1), kC⟩, liftU, liftV, hyU, hyV,
    geoPositiveLift_isPositive hn hG hT q _, geoPositiveLift_isPositive hn hG hT q _, ?_⟩, rfl, rfl, rfl⟩
  · exact s176_four_le_of_crossing (geoPositiveLift hn hG hT q) (0 : Fin 1) kA kC liftU hyU
  · intro w hwA hwB hwC
    have hD := hcl'' w hwA hwB hwC
    convert hD using 2
    all_goals first
      | rfl
      | (show ({(geoCarrierShadow hn hG hT q).crossingPoint liftU, geoCornerPolygon hG.cg T q (kA + 1),
            (geoCarrierShadow hn hG hT q).crossingPoint liftV} : Set Plane) = _
         rw [hliftU, hliftV, s176_liftPoint hn hG hT q huq, s176_liftPoint hn hG hT q hvq, hpt])

include hn hab hac hbc hX hj hu hv hjT huq hvq hQT in
/-- **The carrier corner site of row 176** (`j ∈ T` the corner, `u = {a, c}`, `v = {b, c}` retained,
every other `T`-crossing foreign): a `s176_CornerSite` on the positive lift whose two crossings are the
lifts of `u` and `v`, in the order fixed by the orientation of the corner (`s176_cyclic`). -/
theorem s176_cornerSite_of_carrier :
    ∃ Tsite : s176_CornerSite (geoPositiveLift hn hG hT q), Tsite.i = (0 : Fin 1) ∧
      ((Tsite.y₁ = (geoCarrierCrossingEquiv hn hG hT q).symm ⟨u, huq⟩ ∧
          Tsite.y₂ = (geoCarrierCrossingEquiv hn hG hT q).symm ⟨v, hvq⟩) ∨
        (Tsite.y₁ = (geoCarrierCrossingEquiv hn hG hT q).symm ⟨v, hvq⟩ ∧
          Tsite.y₂ = (geoCarrierCrossingEquiv hn hG hT q).symm ⟨u, huq⟩)) := by
  have hju : j ≠ u := s176_ne_of_supports hj hu hac hbc
  rcases lt_or_gt_of_ne (s176_param_ne hG hju.symm (s176_mem_left hu) (s176_mem_left hj)) with hlt | hgt
  · obtain ⟨Tsite, hi, h1, h2⟩ :=
      s176_cornerSite_case1 hn hG hs hT q hab hac hbc hX hj hu hv hjT huq hvq hQT hlt
    exact ⟨Tsite, hi, Or.inl ⟨h1, h2⟩⟩
  · -- case 2: apply case 1 to the relabelled data `(b, a, c)`, `(j, v, u)`
    have hX' : ExactTriangleVisitOrders P P' b a c hs :=
      gu2_exact_of_eq hs (by ext z; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto) hX
    have hQT' : ∀ x ∈ T, x ≠ j → ∃ ℓ ∈ x.val, ℓ ≠ b ∧ ℓ ≠ a ∧ ℓ ≠ c := by
      intro x hx hxj
      obtain ⟨ℓ, hℓ, h1, h2, h3⟩ := hQT x hx hxj
      exact ⟨ℓ, hℓ, h2, h1, h3⟩
    have hlt_b : visitParameter (visitOn v b (s176_mem_left hv)) <
        visitParameter (visitOn j b (s176_mem_right hj)) := by
      have hjv : j ≠ v := s176_ne_of_supports (s176_pair_comm' hj) hv hbc hac
      have hcyc := s176_cyclic hn hG hs hT q hab hac hbc hX hj hu hv hjT huq hvq
      have hnot : ¬ visitParameter (visitOn j b (s176_mem_right hj)) <
          visitParameter (visitOn v b (s176_mem_left hv)) := fun h => lt_asymm hgt (hcyc.mpr h)
      exact lt_of_le_of_ne (not_lt.mp hnot) (s176_param_ne hG hjv.symm _ _)
    obtain ⟨Tsite, hi, h1, h2⟩ :=
      s176_cornerSite_case1 hn hG hs hT q hab.symm hbc hac hX' (s176_pair_comm' hj) hv hu hjT hvq huq hQT' hlt_b
    exact ⟨Tsite, hi, Or.inr ⟨h1, h2⟩⟩

end S176Clear

end

end RProof

namespace RProof

open SM SM.GeoCarrier SM.Carrier SM.Link

noncomputable section

variable {n : ℕ} [NeZero n]

/-! ## §D. The event-level site of row 176 (the binders of `est_port_relation`) -/

section S176Event

variable {E : CV.Event n} {e f g : ZMod n} {δ : ℝ}

/-- a crossing outside the triangle has a label outside `{e, f, g}` -/
theorem s176_foreign_label {P : LabelledTuple n} (x : Crossing P) (hx : x.val ∉ triangleSupports e f g) :
    ∃ ℓ ∈ x.val, ℓ ∉ ({e, f, g} : Finset (ZMod n)) := by
  classical
  obtain ⟨i, hi⟩ : x.val.Nonempty := Finset.card_pos.mp (by rw [crossing_card_two]; norm_num)
  obtain ⟨j₀, hij, hx₀⟩ := crossing_support_partner x i hi
  by_contra hcon
  have hcon' : ∀ ℓ ∈ x.val, ℓ ∈ ({e, f, g} : Finset (ZMod n)) := fun ℓ hℓ =>
    by_contra fun h => hcon ⟨ℓ, hℓ, h⟩
  clear hcon
  have hcon := hcon'
  apply hx
  rw [hx₀]
  have hi' := hcon i hi
  have hj' := hcon j₀ (by rw [hx₀]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi' hj'
  exact gu2_pair_mem_triangleSupports hij hi' hj'

/-- **The labelled event-level core**: with the labels `a` (shared by `j, u`), `b` (shared by `j, v`),
`c` (shared by `u, v`) fixed, the retained unselected crossing `u'` of the affected carrier `q₀'` forces
the third crossing `v'` to be retained too (`est_retained_u_iff` both ways: the two `c`-visits are
`ρ`-adjacent on `H`), and the carrier corner site exists on `carrierDiagram q₀'` with `{y₁, y₂} =
{lift u', lift v'}`. -/
theorem s176_event_site_core (hn : 3 ≤ n) (hL : LocalizationData E e f g δ) (hR : AV_EventRadius E δ)
    (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g) {t t' : E.Parameter} (ht : Punctured E δ t)
    (ht' : Punctured E δ t') (hop : OppositeSides E t t')
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    {hef' : IsCrossing (E.curve t) {e, f}} {heg' : IsCrossing (E.curve t) {e, g}}
    {hfg' : IsCrossing (E.curve t) {f, g}} (hcomp : CompleteLocal (geomAt E t ht.1) hef' heg' hfg')
    {Q : Finset (Crossing (E.curve t))} (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
    (hfull : FullAvail (geomAt E t ht.1) e f g Q) {j : Crossing (E.curve t)}
    (hj : j.val ∈ triangleSupports e f g) (q : GeoComponent (geomAt E t ht.1) (Q ∪ {j}))
    {u : Crossing (E.curve t)} (hu : u.val ∈ triangleSupports e f g) (hju : j ≠ u)
    (hu' : crossingTransport hs u ∈ geoCarrierCrossings (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j}))
        (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q))
    {a b c : ZMod n} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (habc : ({a, b, c} : Finset (ZMod n)) = {e, f, g})
    (hjab : j.val = {a, b}) (huac : u.val = {a, c}) {v : Crossing (E.curve t)} (hvbc : v.val = {b, c})
    (hv : v.val ∈ triangleSupports e f g) (hjv : j ≠ v) (huv : u ≠ v) :
    ∃ (hv' : crossingTransport hs v ∈ geoCarrierCrossings (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j}))
        (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q))
      (Tsite : s176_CornerSite (CV.carrierDiagram hn (genericAt E t' ht'.1)
        (est_S'_ind hL ht ht' hop hs hQ hfull hj)
        (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q))),
      (Tsite.y₁ = est_liftCrossing hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj) _ hu' ∧
        Tsite.y₂ = est_liftCrossing hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj) _ hv') ∨
      (Tsite.y₁ = est_liftCrossing hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj) _ hv' ∧
        Tsite.y₂ = est_liftCrossing hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj) _ hu') := by
  set W := est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj
  have hS' := est_S'_ind hL ht ht' hop hs hQ hfull hj
  -- labels
  have hcu : c ∈ u.val := s176_mem_right huac
  have hcv : c ∈ v.val := s176_mem_right hvbc
  have hcj : c ∉ j.val := by
    rw [hjab, Finset.mem_insert, Finset.mem_singleton]
    rintro (h | h)
    · exact hac h.symm
    · exact hbc h.symm
  -- the H-side geometry: `u, v ∉ S`, the two `c`-visits are `ρ_S`-adjacent, so they have one owner
  have hQout : ∀ x ∈ Q, x.val ∉ triangleSupports e f g := fun x hxQ h =>
    Finset.disjoint_left.mp ((F1.mem_outsideSupports _ e f g Q).mp hQ).2 hxQ
      ((F1.mem_triangleCrossings e f g x).mpr h)
  have huS : u ∉ Q ∪ {j} := by
    intro h
    rcases Finset.mem_union.mp h with h | h
    · exact hQout u h hu
    · exact hju (Finset.mem_singleton.mp h).symm
  have hvS : v ∉ Q ∪ {j} := by
    intro h
    rcases Finset.mem_union.mp h with h | h
    · exact hQout v h hv
    · exact hjv (Finset.mem_singleton.mp h).symm
  have hGH : CarrierGeometry (E.curve t) := CarrierGeometry.ofDiagrammatic ((genericAt E t ht.1).diagrammatic hn)
  have hXH : ExactTriangleVisitOrders (E.curve t) (E.curve t') c a b hs :=
    gu2_exact_of_eq hs (by rw [← habc]; ext z; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto)
      (hL.gauss_words t t' ht ht' hop hs)
  have hnbH := s176_no_visit_between hs hac.symm hbc.symm hab hXH (s176_pair_comm' huac) (s176_pair_comm' hvbc) hcu hcv
  have howner_u : geoOwner (geomAt E t ht.1) (Q ∪ {j}) (Sum.inr (visitOn u c hcu)) = q :=
    (est_retained_u_iff hL hR hef heg hfg ht ht' hop hs hcomp hQ hfull hj hu hju hcu hcj q).mp hu'
  have howner_v : geoOwner (geomAt E t ht.1) (Q ∪ {j}) (Sum.inr (visitOn v c hcv)) = q := by
    rcases lt_or_gt_of_ne (s176_param_ne hGH huv hcu hcv) with hlt | hgt
    · have hsucc : geoSmoothingSuccessor (geomAt E t ht.1) (Q ∪ {j}) (Sum.inr (visitOn u c hcu)) =
          Sum.inr (visitOn v c hcv) :=
        s176_succ_of_lt hn hGH hcu hcv huS hlt (fun w hw => (hnbH w hw).1)
      rw [← hsucc, geoOwner_successor]; exact howner_u
    · have hsucc : geoSmoothingSuccessor (geomAt E t ht.1) (Q ∪ {j}) (Sum.inr (visitOn v c hcv)) =
          Sum.inr (visitOn u c hcu) :=
        s176_succ_of_lt hn hGH hcv hcu hvS hgt (fun w hw => (hnbH w hw).2)
      rw [← geoOwner_successor, hsucc]; exact howner_u
  have hv' : crossingTransport hs v ∈ geoCarrierCrossings (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j}))
      (GT_carrierEquiv W q) :=
    (est_retained_u_iff hL hR hef heg hfg ht ht' hop hs hcomp hQ hfull hj hv hjv hcv hcj q).mpr howner_v
  refine ⟨hv', ?_⟩
  -- the L side
  have hs' : ∀ s, IsCrossing (E.curve t') s ↔ IsCrossing (E.curve t) s := fun s => (hs s).symm
  have hop' : OppositeSides E t' t := by
    unfold OppositeSides at hop ⊢; linarith [mul_comm t.val t'.val]
  have hXL : ExactTriangleVisitOrders (E.curve t') (E.curve t) a b c hs' :=
    gu2_exact_of_eq hs' habc.symm (hL.gauss_words t' t ht' ht hop' hs')
  have hGL : CarrierGeometry (E.curve t') :=
    CarrierGeometry.ofDiagrammatic ((genericAt E t' ht'.1).diagrammatic hn)
  have hT : GeoIndependent (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j})) :=
    CV.geoIndependent_of_mem_Ind _ hS'
  have hjT : crossingTransport hs j ∈ transportSupport hs (Q ∪ {j}) :=
    (mem_transportSupport_iff hs _ j).mpr (Finset.mem_union_right _ (Finset.mem_singleton_self j))
  have hQT : ∀ x ∈ transportSupport hs (Q ∪ {j}), x ≠ crossingTransport hs j →
      ∃ ℓ ∈ x.val, ℓ ≠ a ∧ ℓ ≠ b ∧ ℓ ≠ c := by
    intro x hx hxj
    obtain ⟨x₀, rfl⟩ := (crossingTransport hs).surjective x
    rw [mem_transportSupport_iff] at hx
    have hx₀j : x₀ ≠ j := fun h => hxj (by rw [h])
    have hx₀Q : x₀ ∈ Q := by
      rcases Finset.mem_union.mp hx with h | h
      · exact h
      · exact absurd (Finset.mem_singleton.mp h) hx₀j
    obtain ⟨ℓ, hℓ, hℓn⟩ := s176_foreign_label x₀ (hQout x₀ hx₀Q)
    rw [← habc, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton, not_or, not_or] at hℓn
    exact ⟨ℓ, hℓ, hℓn.1, hℓn.2.1, hℓn.2.2⟩
  obtain ⟨Tsite, -, hcases⟩ := s176_cornerSite_of_carrier hn (CarrierGeometry.ofDiagrammatic
    ((genericAt E t' ht'.1).diagrammatic hn)) hs' hT (GT_carrierEquiv W q) hab hac hbc hXL
    (j := crossingTransport hs j) (u := crossingTransport hs u) (v := crossingTransport hs v)
    hjab huac hvbc hjT hu' hv' hQT
  exact ⟨Tsite, hcases⟩

/-- **The site of row 176 at the event level** — the hypotheses are exactly the binders of
`est_port_relation` together with the retained unselected crossing `u` of the `∃`-premise: a corner site
on `D₊ = carrierDiagram q₀'` one of whose crossings is the lift `y` of `u'`.  Six relabellings of
`s176_event_site_core` (`GT_tri_cases` for `j` and `u`). -/
theorem s176_site_of_event (hn : 3 ≤ n) (hL : LocalizationData E e f g δ) (hR : AV_EventRadius E δ)
    (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g) {t t' : E.Parameter} (ht : Punctured E δ t)
    (ht' : Punctured E δ t') (hop : OppositeSides E t t')
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    (hef' : IsCrossing (E.curve t) {e, f}) (heg' : IsCrossing (E.curve t) {e, g})
    (hfg' : IsCrossing (E.curve t) {f, g}) (hcomp : CompleteLocal (geomAt E t ht.1) hef' heg' hfg')
    {Q : Finset (Crossing (E.curve t))} (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
    (hfull : FullAvail (geomAt E t ht.1) e f g Q) {j : Crossing (E.curve t)}
    (hj : j.val ∈ triangleSupports e f g) (q : GeoComponent (geomAt E t ht.1) (Q ∪ {j}))
    {u : Crossing (E.curve t)} (hu : u.val ∈ triangleSupports e f g) (hju : j ≠ u)
    (hu' : crossingTransport hs u ∈ geoCarrierCrossings (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j}))
        (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)) :
    ∃ Tsite : s176_CornerSite (CV.carrierDiagram hn (genericAt E t' ht'.1)
        (est_S'_ind hL ht ht' hop hs hQ hfull hj)
        (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)),
      est_liftCrossing hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj) _ hu' = Tsite.y₁ ∨
      est_liftCrossing hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj) _ hu' = Tsite.y₂ := by
  have h1 : (xPair hef').val ∈ triangleSupports e f g := (P1.mem_triangleSupports _).mpr (Or.inl rfl)
  have h2 : (xPair heg').val ∈ triangleSupports e f g := (P1.mem_triangleSupports _).mpr (Or.inr (Or.inl rfl))
  have h3 : (xPair hfg').val ∈ triangleSupports e f g := (P1.mem_triangleSupports _).mpr (Or.inr (Or.inr rfl))
  have n12 := P1.xPair_ef_ne_eg hef' heg' hfg'
  have n13 := P1.xPair_ef_ne_fg hef' heg' hfg'
  have n23 := P1.xPair_eg_ne_fg hef' heg' hfg'
  have key : ∀ {a b c : ZMod n} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
      (habc : ({a, b, c} : Finset (ZMod n)) = {e, f, g})
      (hjab : j.val = {a, b}) (huac : u.val = {a, c}) {v : Crossing (E.curve t)} (hvbc : v.val = {b, c})
      (hv : v.val ∈ triangleSupports e f g) (hjv : j ≠ v) (huv : u ≠ v),
      ∃ Tsite : s176_CornerSite (CV.carrierDiagram hn (genericAt E t' ht'.1)
          (est_S'_ind hL ht ht' hop hs hQ hfull hj)
          (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)),
        est_liftCrossing hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj) _ hu' = Tsite.y₁ ∨
        est_liftCrossing hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj) _ hu' = Tsite.y₂ := by
    intro a b c hab hac hbc habc hjab huac v hvbc hv hjv huv
    obtain ⟨hv', Tsite, hc⟩ := s176_event_site_core hn hL hR hef heg hfg ht ht' hop hs hcomp hQ hfull hj q hu hju hu'
      hab hac hbc habc hjab huac hvbc hv hjv huv
    refine ⟨Tsite, ?_⟩
    rcases hc with ⟨h1, -⟩ | ⟨-, h2⟩
    · exact Or.inl h1.symm
    · exact Or.inr h2.symm
  have p_feg : ({f, e, g} : Finset (ZMod n)) = {e, f, g} := Finset.insert_comm f e {g}
  have p_egf : ({e, g, f} : Finset (ZMod n)) = {e, f, g} := congrArg (insert e) (Finset.pair_comm g f)
  have p_gef : ({g, e, f} : Finset (ZMod n)) = {e, f, g} :=
    (Finset.insert_comm g e {f}).trans (congrArg (insert e) (Finset.pair_comm g f))
  have p_fge : ({f, g, e} : Finset (ZMod n)) = {e, f, g} :=
    (congrArg (insert f) (Finset.pair_comm g e)).trans (Finset.insert_comm f e {g})
  have p_gfe : ({g, f, e} : Finset (ZMod n)) = {e, f, g} :=
    ((congrArg (insert g) (Finset.pair_comm f e)).trans (Finset.insert_comm g e {f})).trans
      (congrArg (insert e) (Finset.pair_comm g f))
  rcases GT_tri_cases t hef' heg' hfg' j hj with rfl | rfl | rfl <;>
    rcases GT_tri_cases t hef' heg' hfg' u hu with rfl | rfl | rfl
  · exact absurd rfl hju
  · -- j = x_ef, u = x_eg, v = x_fg: a = e, b = f, c = g
    exact key hef heg hfg rfl rfl rfl (v := xPair hfg') rfl h3 n13 n23
  · -- j = x_ef, u = x_fg, v = x_eg: a = f, b = e, c = g
    exact key hef.symm hfg heg p_feg (Finset.pair_comm e f) rfl
      (v := xPair heg') rfl h2 n12 n23.symm
  · -- j = x_eg, u = x_ef, v = x_fg: a = e, b = g, c = f
    exact key heg hef hfg.symm p_egf rfl rfl (v := xPair hfg')
      (Finset.pair_comm f g) h3 n23 n13
  · exact absurd rfl hju
  · -- j = x_eg, u = x_fg, v = x_ef: a = g, b = e, c = f
    exact key heg.symm hfg.symm hef p_gef (Finset.pair_comm e g)
      (Finset.pair_comm f g) (v := xPair hef') rfl h1 n12.symm n13.symm
  · -- j = x_fg, u = x_ef, v = x_eg: a = f, b = g, c = e
    exact key hfg hef.symm heg.symm p_fge rfl (Finset.pair_comm e f)
      (v := xPair heg') (Finset.pair_comm e g) h2 n23.symm n12
  · -- j = x_fg, u = x_eg, v = x_ef: a = g, b = f, c = e
    exact key hfg.symm heg.symm hef.symm p_gfe (Finset.pair_comm f g)
      (Finset.pair_comm e g) (v := xPair hef') (Finset.pair_comm e f) h1 n13.symm n12.symm
  · exact absurd rfl hju

end S176Event

/-! ## §E. The record identification `hrec` (stated), the composition into the weak port and into the
weak interface -/

/-- The reduced record of a bigon is the restriction to the complement of its two crossings. -/
theorem s176_reducedRecord_eq {D : Diagram} (B : BigonData D) {y₁ y₂ : D.Γ.Crossing}
    (h₁ : B.y = y₁) (h₂ : B.z = y₂) :
    B.reducedRecord = D.record.restrictCrossings
      {c | c ≠ D.record.crossingOf (D.overVisit y₁) ∧ c ≠ D.record.crossingOf (D.overVisit y₂)} := by
  subst h₁ h₂; rfl

section S176Compose

variable {E : CV.Event n} {e f g : ZMod n} {δ : ℝ}

/-- **The wall transport of the reduced record (OPEN, consumer bookkeeping ≈ 1.0k lines, PLAN_FINAL §4.3 /
§6 R5)**: for the corner site on `D₊ = carrierDiagram q₀'` switched at `y = lift u'`, the record of
`D₊.switch y` with the four occurrences of `{y₁, y₂} = {lift u', lift v'}` deleted (`Record.restrictCrossings`,
first-return successor) is isomorphic to the record of `D₀ = carrierDiagram q₀`.  Content: the retained
crossings correspond (`est_retained_affected`: `q₀'` retains the transports of `q₀`'s crossings plus `u', v'`),
their visit orders are carried (`GT_Wall.key_lt` on non-triangle visits, as in `est_groupedPoly_eq_of_ne`), the
over bits agree (positive lifts, `switch` only touches `y`, and `y` is deleted), the signs are all `+1`; the
assembly is an `RecordIso` built against `restrictCrossings` (`RecordIso.ofOcc`, MarkedProducts) — the analogue
of `EXT_homfly_wall`'s `recordIsoOfData` with the two deleted crossings.  Stated as the Prop consumed below. -/
def s176_hrec_of_site (hn : 3 ≤ n) (hL : LocalizationData E e f g δ) (hR : AV_EventRadius E δ)
    (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g) {t t' : E.Parameter} (ht : Punctured E δ t)
    (ht' : Punctured E δ t') (hop : OppositeSides E t t')
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    {Q : Finset (Crossing (E.curve t))} (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
    (hfull : FullAvail (geomAt E t ht.1) e f g Q) {j : Crossing (E.curve t)}
    (hj : j.val ∈ triangleSupports e f g) (q : GeoComponent (geomAt E t ht.1) (Q ∪ {j}))
    {u : Crossing (E.curve t)}
    (hu' : crossingTransport hs u ∈ geoCarrierCrossings (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j}))
        (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)) : Prop :=
  ∀ Tsite : s176_CornerSite (CV.carrierDiagram hn (genericAt E t' ht'.1)
      (est_S'_ind hL ht ht' hop hs hQ hfull hj)
      (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)),
    (est_liftCrossing hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj) _ hu' = Tsite.y₁ ∨
      est_liftCrossing hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj) _ hu' = Tsite.y₂) →
    Nonempty (RecordIso
      (((CV.carrierDiagram hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj)
          (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)).switch
          (est_liftCrossing hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj) _ hu')).record.restrictCrossings
        {c | c ≠ ((CV.carrierDiagram hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj)
              (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)).switch
              (est_liftCrossing hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj) _ hu')).record.crossingOf
              (((CV.carrierDiagram hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj)
                (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)).switch
                (est_liftCrossing hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj) _ hu')).overVisit Tsite.y₁) ∧
             c ≠ ((CV.carrierDiagram hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj)
              (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)).switch
              (est_liftCrossing hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj) _ hu')).record.crossingOf
              (((CV.carrierDiagram hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj)
                (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)).switch
                (est_liftCrossing hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj) _ hu')).overVisit Tsite.y₂)})
      (CV.carrierDiagram hn (genericAt E t ht.1) (est_S_ind ht.1 hQ hfull hj) q).record)

/-- **The weak port of row 176 from the site and `hrec`** — (a) `s176_site_of_event` + the frozen leaf
through `s176_CornerSite.exists_bigon_switch₁/₂` + (b) `hrec` + `est_port_weak_of_bigon`. -/
theorem s176_port_weak_of_event (hn : 3 ≤ n) (hL : LocalizationData E e f g δ) (hR : AV_EventRadius E δ)
    (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g) {t t' : E.Parameter} (ht : Punctured E δ t)
    (ht' : Punctured E δ t') (hop : OppositeSides E t t')
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    (hef' : IsCrossing (E.curve t) {e, f}) (heg' : IsCrossing (E.curve t) {e, g})
    (hfg' : IsCrossing (E.curve t) {f, g}) (hcomp : CompleteLocal (geomAt E t ht.1) hef' heg' hfg')
    {Q : Finset (Crossing (E.curve t))} (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
    (hfull : FullAvail (geomAt E t ht.1) e f g Q) {j : Crossing (E.curve t)}
    (hj : j.val ∈ triangleSupports e f g) (q : GeoComponent (geomAt E t ht.1) (Q ∪ {j}))
    {u : Crossing (E.curve t)} (hu : u.val ∈ triangleSupports e f g) (hju : j ≠ u)
    (hu' : crossingTransport hs u ∈ geoCarrierCrossings (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j}))
        (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q))
    (hrec : s176_hrec_of_site hn hL hR hef heg hfg ht ht' hop hs hQ hfull hj q hu') :
    est_port_weak
      (CV.carrierDiagram hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj)
        (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q))
      (CV.carrierDiagram hn (genericAt E t ht.1) (est_S_ind ht.1 hQ hfull hj) q)
      (est_liftCrossing hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj) _ hu') := by
  obtain ⟨Tsite, hy⟩ := s176_site_of_event hn hL hR hef heg hfg ht ht' hop hs hef' heg' hfg' hcomp hQ hfull hj q
    hu hju hu'
  unfold s176_hrec_of_site at hrec
  have hR' := hrec Tsite hy
  rcases hy with hy | hy
  · rw [hy] at hR' ⊢
    obtain ⟨B, -, hB₁, hB₂⟩ := Tsite.exists_bigon_switch₁
    refine est_port_weak_of_bigon _ _ _ rfl rfl B ?_
    rw [s176_reducedRecord_eq B hB₁ hB₂]
    exact hR'
  · rw [hy] at hR' ⊢
    obtain ⟨B, -, hB₁, hB₂⟩ := Tsite.exists_bigon_switch₂
    refine est_port_weak_of_bigon _ _ _ rfl rfl B ?_
    rw [s176_reducedRecord_eq B hB₁ hB₂]
    exact hR'

/-- **The weak interface of row 176 from the site**: given `hrec` and the non-move port data
(`s176_PortDataRest`, U_R176_REPORT §5 items 2–5) for every retained unselected crossing of every affected
carrier, `s176_est_port_relation_weak` holds — hence (`s176_est_ledger_weak`) the row in `RowShape`. -/
theorem s176_est_port_relation_weak_of
    (hrec : ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (E : CV.Event n) (e f g : ZMod n) (δ : ℝ)
      (hL : LocalizationData E e f g δ) (hR : AV_EventRadius E δ) (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
      (t t' : E.Parameter) (ht : Punctured E δ t) (ht' : Punctured E δ t') (hop : OppositeSides E t t')
      (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
      (Q : Finset (Crossing (E.curve t))) (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
      (hfull : FullAvail (geomAt E t ht.1) e f g Q) (j : Crossing (E.curve t))
      (hj : j.val ∈ triangleSupports e f g) (q : GeoComponent (geomAt E t ht.1) (Q ∪ {j}))
      (u : Crossing (E.curve t))
      (hu' : crossingTransport hs u ∈ geoCarrierCrossings (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j}))
        (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)),
      s176_hrec_of_site hn hL hR hef heg hfg ht ht' hop hs hQ hfull hj q hu')
    (hrest : ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (E : CV.Event n) (e f g : ZMod n) (δ : ℝ)
      (hL : LocalizationData E e f g δ) (hR : AV_EventRadius E δ) (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
      (t t' : E.Parameter) (ht : Punctured E δ t) (ht' : Punctured E δ t') (hop : OppositeSides E t t')
      (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
      (Q : Finset (Crossing (E.curve t))) (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
      (hfull : FullAvail (geomAt E t ht.1) e f g Q) (j : Crossing (E.curve t))
      (hj : j.val ∈ triangleSupports e f g) (q : GeoComponent (geomAt E t ht.1) (Q ∪ {j}))
      (u : Crossing (E.curve t))
      (hu' : crossingTransport hs u ∈ geoCarrierCrossings (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j}))
        (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)),
      Nonempty (s176_PortDataRest hn (genericAt E t ht.1) (genericAt E t' ht'.1) (est_S_ind ht.1 hQ hfull hj)
        (est_S'_ind hL ht ht' hop hs hQ hfull hj) q
        (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)
        (est_liftCrossing hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj) _ hu'))) :
    s176_est_port_relation_weak := by
  intro n _ hn E e f g δ hL hR hef heg hfg t t' ht ht' hop hs hef' heg' hfg' hcomp Q hQ hfull j hj q hex
  obtain ⟨u, hu, hju, hu'⟩ := hex
  obtain ⟨R⟩ := hrest n hn E e f g δ hL hR hef heg hfg t t' ht ht' hop hs Q hQ hfull j hj q u hu'
  refine ⟨u, hu, hju, hu', ⟨s176_PortDataWeak.mk' _ _ _ _ _ _ _ _ ?_ R⟩⟩
  exact s176_port_weak_of_event hn hL hR hef heg hfg ht ht' hop hs hef' heg' hfg' hcomp hQ hfull hj q hu hju.symm
    hu' (hrec n hn E e f g δ hL hR hef heg hfg t t' ht ht' hop hs Q hQ hfull j hj q u hu')

end S176Compose

end

end RProof

namespace RProof

open SM SM.GeoCarrier SM.Carrier SM.Link

noncomputable section

variable {n : ℕ} [NeZero n]

/-! ## §F. The switch drops out of `hrec`: the reduced record of `D.switch y` at a keep-set missing `y`
is the reduced record of `D` (identity on occurrences), so the record identification of row 176 is a
statement about the two UNSWITCHED positive lifts. -/

/-- two occurrences of one crossing name one record crossing -/
theorem s176_crossingOf_eq_of_fst (D : Diagram) (v w : D.Γ.Visit) (h : v.1 = w.1) :
    D.record.crossingOf v = D.record.crossingOf w := by
  rcases D.eq_or_eq_twin w v h with rfl | rfl
  · rfl
  · rw [← D.record_pair_apply, Record.crossingOf_pair]

/-- a retained occurrence is not at the deleted crossing -/
theorem s176_fst_ne_of_keep (D : Diagram) (x₀ : D.Γ.Crossing) (K : Set D.record.Crossing)
    (hK : D.record.crossingOf (D.overVisit x₀) ∉ K) (w : D.Γ.Visit) (hw : D.record.crossingOf w ∈ K) :
    w.1 ≠ x₀ := by
  intro h
  apply hK
  rw [← s176_crossingOf_eq_of_fst D w (D.overVisit x₀) h]
  exact hw

/-- **Deleting the switched crossing forgets the switch**: for a keep-set `K` not containing the crossing
of `x₀`, the restricted records of `D.switch x₀` and of `D` coincide (identity on circles and
occurrences; the first-return successor and the pairing are literally the same; bits and signs differ
only at the two deleted occurrences — `switch_overBit_of_ne`, `switch_sign_of_ne`). -/
def s176_switchRestrictIso (D : Diagram) (x₀ : D.Γ.Crossing) (K : Set D.record.Crossing)
    (hK : D.record.crossingOf (D.overVisit x₀) ∉ K) :
    RecordIso ((D.switch x₀).record.restrictCrossings K) (D.record.restrictCrossings K) where
  e := Equiv.refl _
  Φ := Equiv.refl _
  comp_eq _ := rfl
  succ_eq _ := rfl
  pair_eq _ := rfl
  bit_eq v := by
    show D.overBit v.1 = (D.switch x₀).overBit v.1
    exact (D.switch_overBit_of_ne x₀ v.1 (s176_fst_ne_of_keep D x₀ K hK v.1 v.2)).symm
  sgn_eq v := by
    show D.sign v.1.1 = (D.switch x₀).sign v.1.1
    exact (Diagram.switch_sign_of_ne D (s176_fst_ne_of_keep D x₀ K hK v.1 v.2)).symm

/-- the keep-set of a bigon on `D.switch y` read on `D` -/
theorem s176_keep_switch_eq (D : Diagram) (y y₁ y₂ : D.Γ.Crossing) :
    ({c | c ≠ (D.switch y).record.crossingOf ((D.switch y).overVisit y₁) ∧
        c ≠ (D.switch y).record.crossingOf ((D.switch y).overVisit y₂)} : Set (D.switch y).record.Crossing) =
      ({c | c ≠ D.record.crossingOf (D.overVisit y₁) ∧ c ≠ D.record.crossingOf (D.overVisit y₂)} :
        Set D.record.Crossing) := by
  ext c
  show c ≠ D.record.crossingOf ((D.switch y).overVisit y₁) ∧ c ≠ D.record.crossingOf ((D.switch y).overVisit y₂) ↔
    c ≠ D.record.crossingOf (D.overVisit y₁) ∧ c ≠ D.record.crossingOf (D.overVisit y₂)
  rw [s176_crossingOf_eq_of_fst D ((D.switch y).overVisit y₁) (D.overVisit y₁) rfl,
    s176_crossingOf_eq_of_fst D ((D.switch y).overVisit y₂) (D.overVisit y₂) rfl]

/-- **`hrec` from the unswitched identification**: if the record of `D₊` with the crossings `y₁, y₂`
deleted is `D₀`'s record, so is the record of `D₊.switch y` with them deleted, for `y ∈ {y₁, y₂}`. -/
theorem s176_hrec_of_unswitched (Dp D₀ : Diagram) (y y₁ y₂ : Dp.Γ.Crossing) (hy : y = y₁ ∨ y = y₂)
    (h : Nonempty (RecordIso (Dp.record.restrictCrossings
      {c | c ≠ Dp.record.crossingOf (Dp.overVisit y₁) ∧ c ≠ Dp.record.crossingOf (Dp.overVisit y₂)}) D₀.record)) :
    Nonempty (RecordIso ((Dp.switch y).record.restrictCrossings
      {c | c ≠ (Dp.switch y).record.crossingOf ((Dp.switch y).overVisit y₁) ∧
           c ≠ (Dp.switch y).record.crossingOf ((Dp.switch y).overVisit y₂)}) D₀.record) := by
  obtain ⟨ι⟩ := h
  rw [s176_keep_switch_eq]
  have hK : Dp.record.crossingOf (Dp.overVisit y) ∉
      ({c | c ≠ Dp.record.crossingOf (Dp.overVisit y₁) ∧ c ≠ Dp.record.crossingOf (Dp.overVisit y₂)} :
        Set Dp.record.Crossing) := by
    rcases hy with rfl | rfl
    · exact fun h => h.1 rfl
    · exact fun h => h.2 rfl
  exact ⟨(s176_switchRestrictIso Dp y _ hK).trans ι⟩

section S176Unswitched

variable {E : CV.Event n} {e f g : ZMod n} {δ : ℝ}

/-- **The record identification of row 176 in its UNSWITCHED form (OPEN, ≈ 1.0k lines, the consumer's wall
transport)**: the record of the positive lift `D₊ = carrierDiagram q₀'` with the two crossings `{y₁, y₂} =
{lift u', lift v'}` of the corner site deleted (`Record.restrictCrossings`, first-return successor) is
isomorphic to the record of `D₀ = carrierDiagram q₀`.  No switch is involved (`s176_hrec_of_unswitched`).
Ingredients: `est_retained_affected` (retained sets), `GT_Wall.key_lt` (visit orders of the non-triangle
visits, as in `est_groupedPoly_eq_of_ne`), positivity (`geoPositiveLift_isPositive`) and
`GT_det_pos_iff_of_sign` (bits), all signs `+1`; assembly against `restrictCrossings` as in
`restrictCrossings_iso_of_recordIso` / `EXT_homfly_wall`. -/
def s176_hrec_unswitched (hn : 3 ≤ n) (hL : LocalizationData E e f g δ) (hR : AV_EventRadius E δ)
    (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g) {t t' : E.Parameter} (ht : Punctured E δ t)
    (ht' : Punctured E δ t') (hop : OppositeSides E t t')
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    {Q : Finset (Crossing (E.curve t))} (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
    (hfull : FullAvail (geomAt E t ht.1) e f g Q) {j : Crossing (E.curve t)}
    (hj : j.val ∈ triangleSupports e f g) (q : GeoComponent (geomAt E t ht.1) (Q ∪ {j}))
    {u : Crossing (E.curve t)}
    (hu' : crossingTransport hs u ∈ geoCarrierCrossings (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j}))
        (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)) : Prop :=
  ∀ Tsite : s176_CornerSite (CV.carrierDiagram hn (genericAt E t' ht'.1)
      (est_S'_ind hL ht ht' hop hs hQ hfull hj)
      (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)),
    (est_liftCrossing hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj) _ hu' = Tsite.y₁ ∨
      est_liftCrossing hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj) _ hu' = Tsite.y₂) →
    Nonempty (RecordIso
      ((CV.carrierDiagram hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj)
          (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)).record.restrictCrossings
        {c | c ≠ (CV.carrierDiagram hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj)
              (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)).record.crossingOf
              ((CV.carrierDiagram hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj)
                (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)).overVisit Tsite.y₁) ∧
             c ≠ (CV.carrierDiagram hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj)
              (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)).record.crossingOf
              ((CV.carrierDiagram hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj)
                (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)).overVisit Tsite.y₂)})
      (CV.carrierDiagram hn (genericAt E t ht.1) (est_S_ind ht.1 hQ hfull hj) q).record)

/-- the switched `hrec` of §E from the unswitched one -/
theorem s176_hrec_of_site_of_unswitched (hn : 3 ≤ n) (hL : LocalizationData E e f g δ)
    (hR : AV_EventRadius E δ) (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g) {t t' : E.Parameter}
    (ht : Punctured E δ t) (ht' : Punctured E δ t') (hop : OppositeSides E t t')
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    {Q : Finset (Crossing (E.curve t))} (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
    (hfull : FullAvail (geomAt E t ht.1) e f g Q) {j : Crossing (E.curve t)}
    (hj : j.val ∈ triangleSupports e f g) (q : GeoComponent (geomAt E t ht.1) (Q ∪ {j}))
    {u : Crossing (E.curve t)}
    (hu' : crossingTransport hs u ∈ geoCarrierCrossings (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j}))
        (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q))
    (h : s176_hrec_unswitched hn hL hR hef heg hfg ht ht' hop hs hQ hfull hj q hu') :
    s176_hrec_of_site hn hL hR hef heg hfg ht ht' hop hs hQ hfull hj q hu' := by
  unfold s176_hrec_unswitched at h
  unfold s176_hrec_of_site
  intro Tsite hy
  exact s176_hrec_of_unswitched _ _ _ Tsite.y₁ Tsite.y₂ hy (h Tsite hy)

end S176Unswitched

end

end RProof

namespace RProof

open SM SM.GeoCarrier SM.Carrier SM.Link

noncomputable section

variable {n : ℕ} [NeZero n]

/-! ## §G. The wall transport of the two-crossing-deleted record, modulo the successor clause: the
occurrence bijection and the clauses `comp`, `pair`, `bit`, `sgn` of `s176_hrec_unswitched` are PROVED at
the carrier level; `succ_eq` (the first-return successor against the cyclic order across the wall) is
isolated as the single remaining hypothesis. -/

/-- record crossings of two occurrences differ iff their diagram crossings differ -/
theorem s176_crossingOf_ne_iff (D : Diagram) (v w : D.Γ.Visit) :
    D.record.crossingOf v ≠ D.record.crossingOf w ↔ v.1 ≠ w.1 := by
  constructor
  · intro h hvw
    exact h (s176_crossingOf_eq_of_fst D v w hvw)
  · intro h heq
    apply h
    have hmem : v ∈ (D.record.crossingOf w).1 :=
      (Record.crossingOf_eq_iff D.record v (D.record.crossingOf w)).mp heq
    rcases (Finset.mem_insert.mp hmem) with h1 | h1
    · rw [h1]
    · rw [Finset.mem_singleton] at h1
      rw [h1]
      rfl

section S176Wall

variable (hn : 3 ≤ n) {P P' : LabelledTuple n} (hG : CarrierGeometry P) (hG' : CarrierGeometry P')
  (hs : ∀ s, IsCrossing P s ↔ IsCrossing P' s)
  {T : Finset (Crossing P)} {T' : Finset (Crossing P')} (hT : GeoIndependent hG.cg T)
  (hT' : GeoIndependent hG'.cg T') (q : GeoComponent hG.cg T) (q' : GeoComponent hG'.cg T')
  {u' v' : Crossing P'} (hu' : u' ∈ geoCarrierCrossings hG'.cg T' q') (hv' : v' ∈ geoCarrierCrossings hG'.cg T' q')

/-- the keep-set of row 176 on the L-side lift: everything but the crossings at `u'`, `v'` -/
def s176_wallKeep : Set (geoPositiveLift hn hG' hT' q').record.Crossing :=
  {c | c ≠ (geoPositiveLift hn hG' hT' q').record.crossingOf
        ((geoPositiveLift hn hG' hT' q').overVisit ((geoCarrierCrossingEquiv hn hG' hT' q').symm ⟨u', hu'⟩)) ∧
       c ≠ (geoPositiveLift hn hG' hT' q').record.crossingOf
        ((geoPositiveLift hn hG' hT' q').overVisit ((geoCarrierCrossingEquiv hn hG' hT' q').symm ⟨v', hv'⟩))}

/-- an occurrence of the lift is at the lift of `x` iff its parent crossing is `x` -/
theorem s176_fst_eq_lift_iff (v : (geoPositiveLift hn hG' hT' q').Γ.Visit) {x : Crossing P'}
    (hx : x ∈ geoCarrierCrossings hG'.cg T' q') :
    v.1 = (geoCarrierCrossingEquiv hn hG' hT' q').symm ⟨x, hx⟩ ↔ (CV.liftVisit hn hG' hT' q' v).1 = x := by
  rw [CV.liftVisit_fst]
  show _ ↔ (geoCarrierCrossingEquiv hn hG' hT' q' v.1).1 = x
  constructor
  · intro h
    rw [h, Equiv.apply_symm_apply]
  · intro h
    apply (geoCarrierCrossingEquiv hn hG' hT' q').injective
    rw [Equiv.apply_symm_apply]
    exact Subtype.ext h

variable (hX : geoCarrierCrossings hG'.cg T' q' =
    (geoCarrierCrossings hG.cg T q).map (crossingTransport hs).toEmbedding ∪ {u', v'})
  (hu_not : u' ∉ (geoCarrierCrossings hG.cg T q).map (crossingTransport hs).toEmbedding)
  (hv_not : v' ∉ (geoCarrierCrossings hG.cg T q).map (crossingTransport hs).toEmbedding)

include hX hu_not hv_not in
/-- **the retained occurrences are the lifts of the transported crossings of `q`** -/
theorem s176_crossKeep_iff (v : (geoPositiveLift hn hG' hT' q').Γ.Visit) :
    (geoPositiveLift hn hG' hT' q').record.CrossKeep (s176_wallKeep hn hG' hT' q' hu' hv') v ↔
      (CV.liftVisit hn hG' hT' q' v).1 ∈ (geoCarrierCrossings hG.cg T q).map (crossingTransport hs).toEmbedding := by
  have hmem := CV.liftVisit_mem hn hG' hT' q' v
  rw [hX, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hmem
  show (_ ≠ _ ∧ _ ≠ _) ↔ _
  rw [s176_crossingOf_ne_iff, s176_crossingOf_ne_iff]
  have e1 := (s176_fst_eq_lift_iff hn hG' hT' q' v hu').not
  have e2 := (s176_fst_eq_lift_iff hn hG' hT' q' v hv').not
  constructor
  · rintro ⟨h1, h2⟩
    have h1' := e1.mp h1
    have h2' := e2.mp h2
    rcases hmem with h | h | h
    · exact h
    · exact absurd h h1'
    · exact absurd h h2'
  · intro h
    exact ⟨e1.mpr (fun h1 => hu_not (h1 ▸ h)), e2.mpr (fun h2 => hv_not (h2 ▸ h))⟩

/-- **The occurrence bijection across the wall**: retained occurrences of the L-side lift (not at `u', v'`)
↔ occurrences of the H-side lift, through the parent visits and `visitTransport`. -/
def s176_wallΦ :
    {v : (geoPositiveLift hn hG' hT' q').Γ.Visit //
        (geoPositiveLift hn hG' hT' q').record.CrossKeep (s176_wallKeep hn hG' hT' q' hu' hv') v} ≃
      (geoPositiveLift hn hG hT q).Γ.Visit :=
  ((CV.liftVisitEquiv hn hG' hT' q').subtypeEquiv
      (q := fun w : {w : Visit P' // w.1 ∈ geoCarrierCrossings hG'.cg T' q'} =>
        w.1.1 ∈ (geoCarrierCrossings hG.cg T q).map (crossingTransport hs).toEmbedding)
      (fun v => s176_crossKeep_iff hn hG hG' hs hT' q q' hu' hv' hX hu_not hv_not v)).trans
    ((Equiv.subtypeSubtypeEquivSubtypeInter _ _).trans
      ((Equiv.subtypeEquivRight (fun w : Visit P' =>
          ⟨fun h => h.2, fun h => ⟨by rw [hX]; exact Finset.mem_union_left _ h, h⟩⟩)).trans
        (((visitTransport hs).symm.subtypeEquiv
            (fun w : Visit P' => (Finset.mem_map_equiv (f := crossingTransport hs)))).trans
          (CV.liftVisitEquiv hn hG hT q).symm)))

/-- the parent visit of the image is the transport of the parent visit -/
theorem s176_wallΦ_liftVisit (v : {v : (geoPositiveLift hn hG' hT' q').Γ.Visit //
    (geoPositiveLift hn hG' hT' q').record.CrossKeep (s176_wallKeep hn hG' hT' q' hu' hv') v}) :
    CV.liftVisit hn hG hT q (s176_wallΦ hn hG hG' hs hT hT' q q' hu' hv' hX hu_not hv_not v) =
      (visitTransport hs).symm (CV.liftVisit hn hG' hT' q' v.1) := by
  unfold s176_wallΦ
  rw [Equiv.trans_apply, Equiv.trans_apply, Equiv.trans_apply, Equiv.trans_apply, CV.liftVisit_symm]
  rfl

/-- **The wall transport of the reduced record, modulo the successor clause.**  With the occurrence
bijection `s176_wallΦ`: `comp_eq` (one circle), `pair_eq` (`liftVisit_twin`, `visitTransport_visitTwin`),
`bit_eq` (the divide convention read on the parents, `overBit_eq_true_iff_parent`, and the sign data `hdet`),
`sgn_eq` (all `+1`) are PROVED; `succ_eq` — the first-return successor of the restricted record against the
H-side successor — is the hypothesis `hsucc`, the single remaining obligation of `hrec`. -/
theorem s176_hrec_unswitched_of_succ
    (hdet : ∀ w : Visit P, w.1 ∈ geoCarrierCrossings hG.cg T q →
      (0 < det (edge P w.2.val) (edge P (visitTwin w).2.val) ↔
        0 < det (edge P' w.2.val) (edge P' (visitTwin w).2.val)))
    (hsucc : ∀ v, s176_wallΦ hn hG hG' hs hT hT' q q' hu' hv' hX hu_not hv_not
        (((geoPositiveLift hn hG' hT' q').record.restrictCrossings (s176_wallKeep hn hG' hT' q' hu' hv')).succ v) =
      (geoPositiveLift hn hG hT q).record.succ (s176_wallΦ hn hG hG' hs hT hT' q q' hu' hv' hX hu_not hv_not v)) :
    Nonempty (RecordIso
      ((geoPositiveLift hn hG' hT' q').record.restrictCrossings (s176_wallKeep hn hG' hT' q' hu' hv'))
      (geoPositiveLift hn hG hT q).record) := by
  set Φ := s176_wallΦ hn hG hG' hs hT hT' q q' hu' hv' hX hu_not hv_not with hΦ
  have hlift : ∀ v, CV.liftVisit hn hG hT q (Φ v) = (visitTransport hs).symm (CV.liftVisit hn hG' hT' q' v.1) :=
    fun v => s176_wallΦ_liftVisit hn hG hG' hs hT hT' q q' hu' hv' hX hu_not hv_not v
  refine ⟨⟨Equiv.refl (Fin 1), Φ, ?_, hsucc, ?_, ?_, ?_⟩⟩
  · intro v
    apply Fin.ext
    have h1 := ((geoPositiveLift hn hG hT q).compOf (Φ v)).isLt
    have h2 := ((geoPositiveLift hn hG' hT' q').compOf v.1).isLt
    change _ < 1 at h1 h2
    change ((geoPositiveLift hn hG hT q).compOf (Φ v)).val = ((geoPositiveLift hn hG' hT' q').compOf v.1).val
    omega
  · intro v
    apply CV.liftVisit_injective hn hG hT q
    have h1 := hlift (((geoPositiveLift hn hG' hT' q').record.restrictCrossings
      (s176_wallKeep hn hG' hT' q' hu' hv')).pair v)
    have h2 := hlift v
    refine h1.trans ?_
    change (visitTransport hs).symm (CV.liftVisit hn hG' hT' q' ((geoPositiveLift hn hG' hT' q').twin v.1)) =
      CV.liftVisit hn hG hT q ((geoPositiveLift hn hG hT q).twin (Φ v))
    rw [CV.liftVisit_twin, CV.liftVisit_twin, h2]
    exact visitTransport_visitTwin (fun s => (hs s).symm) _
  · intro v
    change (geoPositiveLift hn hG hT q).overBit (Φ v) = (geoPositiveLift hn hG' hT' q').overBit v.1
    have h2 := hlift v
    rw [Bool.eq_iff_iff, CV.overBit_eq_true_iff_parent, CV.overBit_eq_true_iff_parent, h2]
    set w := (visitTransport hs).symm (CV.liftVisit hn hG' hT' q' v.1) with hw
    have hw' : CV.liftVisit hn hG' hT' q' v.1 = visitTransport hs w := by
      rw [hw, Equiv.apply_symm_apply]
    rw [hw', ← visitTransport_visitTwin, visitTransport_edge, visitTransport_edge]
    apply hdet
    rw [← h2]
    exact CV.liftVisit_mem hn hG hT q _
  · intro v
    change (geoPositiveLift hn hG hT q).sign (Φ v).1 = (geoPositiveLift hn hG' hT' q').sign v.1.1
    rw [geoPositiveLift_sign, geoPositiveLift_sign]

end S176Wall

end

end RProof

namespace RProof

open SM SM.GeoCarrier SM.Carrier SM.Link

noncomputable section

variable {n : ℕ} [NeZero n]

/-! ## §H. The event-level closure of the `hrec` chain: the wall data of row 176 (`est_retained_affected`,
`est_not_retained_H`, the sign radius), the record identification for the SPECIFIC deleted crossings
`{lift u', lift v'}` (`s176_hrec_wall`), its reduction to the successor clause (`s176_hrec_wall_of_succ`,
through §G), the site with the identification of its two crossings (`s176_site_of_event'`), and the weak
port from `s176_hrec_wall` (`s176_port_weak_of_event'`). -/

section S176EventWall

variable {E : CV.Event n} {e f g : ZMod n} {δ : ℝ}

/-- the retained set of `q₀'` (`est_retained_affected`, with the shared label of `u, v`) -/
theorem s176_hX_event (hL : LocalizationData E e f g δ) (hR : AV_EventRadius E δ)
    (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g) {t t' : E.Parameter} (ht : Punctured E δ t)
    (ht' : Punctured E δ t') (hop : OppositeSides E t t')
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    {hef' : IsCrossing (E.curve t) {e, f}} {heg' : IsCrossing (E.curve t) {e, g}}
    {hfg' : IsCrossing (E.curve t) {f, g}} (hcomp : CompleteLocal (geomAt E t ht.1) hef' heg' hfg')
    {Q : Finset (Crossing (E.curve t))} (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
    (hfull : FullAvail (geomAt E t ht.1) e f g Q) {j : Crossing (E.curve t)}
    (hj : j.val ∈ triangleSupports e f g) (q : GeoComponent (geomAt E t ht.1) (Q ∪ {j}))
    {u : Crossing (E.curve t)} (hu : u.val ∈ triangleSupports e f g) (hju : j ≠ u)
    (hu' : crossingTransport hs u ∈ geoCarrierCrossings (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j}))
        (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q))
    {v : Crossing (E.curve t)} (hv : v.val ∈ triangleSupports e f g) (hjv : j ≠ v) (huv : u ≠ v) :
    geoCarrierCrossings (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j}))
        (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q) =
      (geoCarrierCrossings (geomAt E t ht.1) (Q ∪ {j}) q).map (crossingTransport hs).toEmbedding ∪
        {crossingTransport hs u, crossingTransport hs v} := by
  obtain ⟨ℓ, hℓu, hℓv⟩ := GT_shared_label hu hv huv
  have hℓj := est_shared_not_mem_third hef heg hfg hj hu hv hju hjv huv hℓu hℓv
  have hq : geoOwner (geomAt E t ht.1) (Q ∪ {j}) (Sum.inr (visitOn u ℓ hℓu)) = q :=
    (est_retained_u_iff hL hR hef heg hfg ht ht' hop hs hcomp hQ hfull hj hu hju hℓu hℓj q).mp hu'
  exact est_retained_affected hL hR hef heg hfg ht ht' hop hs hcomp hQ hfull hj hu hv hju hjv huv hℓu hℓv q hq

/-- a triangle crossing is not a transported retained crossing of `q₀` (`est_not_retained_H`) -/
theorem s176_not_mem_map_event {t t' : E.Parameter} (ht : Punctured E δ t)
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    {hef' : IsCrossing (E.curve t) {e, f}} {heg' : IsCrossing (E.curve t) {e, g}}
    {hfg' : IsCrossing (E.curve t) {f, g}} (hcomp : CompleteLocal (geomAt E t ht.1) hef' heg' hfg')
    {Q : Finset (Crossing (E.curve t))} (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
    (hfull : FullAvail (geomAt E t ht.1) e f g Q) {j : Crossing (E.curve t)}
    (hj : j.val ∈ triangleSupports e f g) (q : GeoComponent (geomAt E t ht.1) (Q ∪ {j}))
    {x : Crossing (E.curve t)} (hx : x.val ∈ triangleSupports e f g) :
    crossingTransport hs x ∉
      (geoCarrierCrossings (geomAt E t ht.1) (Q ∪ {j}) q).map (crossingTransport hs).toEmbedding := by
  intro h
  rw [Finset.mem_map_equiv, Equiv.symm_apply_apply] at h
  exact est_not_retained_H ht hcomp hQ hfull hj q h hx

/-- the divide signs of the parent visits are carried across the wall (the sign radius) -/
theorem s176_hdet_event (hR : AV_EventRadius E δ) {t t' : E.Parameter} (ht : Punctured E δ t)
    (ht' : Punctured E δ t') (w : Visit (E.curve t)) :
    (0 < det (edge (E.curve t) w.2.val) (edge (E.curve t) (visitTwin w).2.val) ↔
      0 < det (edge (E.curve t') w.2.val) (edge (E.curve t') (visitTwin w).2.val)) :=
  GT_det_pos_iff_of_sign (hR.sign_eq t t' ht ht' _ _
    (by rw [← visit_crossing_val_eq_pair w]; exact w.1.property))

end S176EventWall

section S176HrecWall

variable {E : CV.Event n} {e f g : ZMod n} {δ : ℝ}

/-- **The record identification of row 176 for the two deleted crossings `lift u', lift v'` (OPEN
modulo `succ_eq`, see `s176_hrec_wall_of_succ`)**: for every third triangle crossing `v` (with `v'` retained
by `q₀'`), the record of the UNSWITCHED lift `D₊` with the crossings at `u', v'` deleted is the record of `D₀`. -/
def s176_hrec_wall (hn : 3 ≤ n) (hL : LocalizationData E e f g δ) (hR : AV_EventRadius E δ)
    (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g) {t t' : E.Parameter} (ht : Punctured E δ t)
    (ht' : Punctured E δ t') (hop : OppositeSides E t t')
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    {Q : Finset (Crossing (E.curve t))} (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
    (hfull : FullAvail (geomAt E t ht.1) e f g Q) {j : Crossing (E.curve t)}
    (hj : j.val ∈ triangleSupports e f g) (q : GeoComponent (geomAt E t ht.1) (Q ∪ {j}))
    {u : Crossing (E.curve t)}
    (hu' : crossingTransport hs u ∈ geoCarrierCrossings (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j}))
        (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)) : Prop :=
  ∀ (v : Crossing (E.curve t)) (_hv : v.val ∈ triangleSupports e f g) (_hjv : j ≠ v) (_huv : u ≠ v)
    (hv' : crossingTransport hs v ∈ geoCarrierCrossings (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j}))
        (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)),
    Nonempty (RecordIso
      ((CV.carrierDiagram hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj)
          (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)).record.restrictCrossings
        (s176_wallKeep hn (CarrierGeometry.ofDiagrammatic ((genericAt E t' ht'.1).diagrammatic hn))
          (CV.geoIndependent_of_mem_Ind _ (est_S'_ind hL ht ht' hop hs hQ hfull hj))
          (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q) hu' hv'))
      (CV.carrierDiagram hn (genericAt E t ht.1) (est_S_ind ht.1 hQ hfull hj) q).record)

/-- **`s176_hrec_wall` from the successor clause alone** (§G: the occurrence bijection and the clauses
`comp`, `pair`, `bit`, `sgn` are proved; the wall data `hX`, `hu_not`, `hv_not`, `hdet` are the accepted
row-176 facts).  `hsucc` is THE remaining obligation of row 176's move: the first-return successor of the
restricted L-side record corresponds to the H-side successor under `s176_wallΦ`. -/
theorem s176_hrec_wall_of_succ (hn : 3 ≤ n) (hL : LocalizationData E e f g δ) (hR : AV_EventRadius E δ)
    (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g) {t t' : E.Parameter} (ht : Punctured E δ t)
    (ht' : Punctured E δ t') (hop : OppositeSides E t t')
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    {hef' : IsCrossing (E.curve t) {e, f}} {heg' : IsCrossing (E.curve t) {e, g}}
    {hfg' : IsCrossing (E.curve t) {f, g}} (hcomp : CompleteLocal (geomAt E t ht.1) hef' heg' hfg')
    {Q : Finset (Crossing (E.curve t))} (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
    (hfull : FullAvail (geomAt E t ht.1) e f g Q) {j : Crossing (E.curve t)}
    (hj : j.val ∈ triangleSupports e f g) (q : GeoComponent (geomAt E t ht.1) (Q ∪ {j}))
    {u : Crossing (E.curve t)} (hu : u.val ∈ triangleSupports e f g) (hju : j ≠ u)
    (hu' : crossingTransport hs u ∈ geoCarrierCrossings (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j}))
        (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q))
    (hsucc : ∀ (v : Crossing (E.curve t)) (hv : v.val ∈ triangleSupports e f g) (hjv : j ≠ v) (huv : u ≠ v)
      (hv' : crossingTransport hs v ∈ geoCarrierCrossings (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j}))
        (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)),
      ∀ w, s176_wallΦ hn (CarrierGeometry.ofDiagrammatic ((genericAt E t ht.1).diagrammatic hn))
          (CarrierGeometry.ofDiagrammatic ((genericAt E t' ht'.1).diagrammatic hn)) hs
          (CV.geoIndependent_of_mem_Ind _ (est_S_ind ht.1 hQ hfull hj))
          (CV.geoIndependent_of_mem_Ind _ (est_S'_ind hL ht ht' hop hs hQ hfull hj)) q
          (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q) hu' hv'
          (s176_hX_event hL hR hef heg hfg ht ht' hop hs hcomp hQ hfull hj q hu hju hu' hv hjv huv)
          (s176_not_mem_map_event ht hs hcomp hQ hfull hj q hu)
          (s176_not_mem_map_event ht hs hcomp hQ hfull hj q hv)
          (((CV.carrierDiagram hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj)
            (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)).record.restrictCrossings
            (s176_wallKeep hn (CarrierGeometry.ofDiagrammatic ((genericAt E t' ht'.1).diagrammatic hn))
              (CV.geoIndependent_of_mem_Ind _ (est_S'_ind hL ht ht' hop hs hQ hfull hj))
              (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q) hu' hv')).succ w) =
        (CV.carrierDiagram hn (genericAt E t ht.1) (est_S_ind ht.1 hQ hfull hj) q).record.succ
          (s176_wallΦ hn (CarrierGeometry.ofDiagrammatic ((genericAt E t ht.1).diagrammatic hn))
            (CarrierGeometry.ofDiagrammatic ((genericAt E t' ht'.1).diagrammatic hn)) hs
            (CV.geoIndependent_of_mem_Ind _ (est_S_ind ht.1 hQ hfull hj))
            (CV.geoIndependent_of_mem_Ind _ (est_S'_ind hL ht ht' hop hs hQ hfull hj)) q
            (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q) hu' hv'
            (s176_hX_event hL hR hef heg hfg ht ht' hop hs hcomp hQ hfull hj q hu hju hu' hv hjv huv)
            (s176_not_mem_map_event ht hs hcomp hQ hfull hj q hu)
            (s176_not_mem_map_event ht hs hcomp hQ hfull hj q hv) w)) :
    s176_hrec_wall hn hL hR hef heg hfg ht ht' hop hs hQ hfull hj q hu' := by
  intro v hv hjv huv hv'
  exact s176_hrec_unswitched_of_succ hn _ _ hs _ _ q _ hu' hv'
    (s176_hX_event hL hR hef heg hfg ht ht' hop hs hcomp hQ hfull hj q hu hju hu' hv hjv huv)
    (s176_not_mem_map_event ht hs hcomp hQ hfull hj q hu)
    (s176_not_mem_map_event ht hs hcomp hQ hfull hj q hv)
    (fun w _ => s176_hdet_event hR ht ht' w)
    (hsucc v hv hjv huv hv')

/-- **The site with its two crossings identified**: `s176_site_of_event` strengthened by the third
crossing `v`, its retention `hv'`, and `{Tsite.y₁, Tsite.y₂} = {lift u', lift v'}`. -/
theorem s176_site_of_event' (hn : 3 ≤ n) (hL : LocalizationData E e f g δ) (hR : AV_EventRadius E δ)
    (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g) {t t' : E.Parameter} (ht : Punctured E δ t)
    (ht' : Punctured E δ t') (hop : OppositeSides E t t')
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    (hef' : IsCrossing (E.curve t) {e, f}) (heg' : IsCrossing (E.curve t) {e, g})
    (hfg' : IsCrossing (E.curve t) {f, g}) (hcomp : CompleteLocal (geomAt E t ht.1) hef' heg' hfg')
    {Q : Finset (Crossing (E.curve t))} (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
    (hfull : FullAvail (geomAt E t ht.1) e f g Q) {j : Crossing (E.curve t)}
    (hj : j.val ∈ triangleSupports e f g) (q : GeoComponent (geomAt E t ht.1) (Q ∪ {j}))
    {u : Crossing (E.curve t)} (hu : u.val ∈ triangleSupports e f g) (hju : j ≠ u)
    (hu' : crossingTransport hs u ∈ geoCarrierCrossings (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j}))
        (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)) :
    ∃ (v : Crossing (E.curve t)) (_hv : v.val ∈ triangleSupports e f g) (_hjv : j ≠ v) (_huv : u ≠ v)
      (hv' : crossingTransport hs v ∈ geoCarrierCrossings (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j}))
        (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q))
      (Tsite : s176_CornerSite (CV.carrierDiagram hn (genericAt E t' ht'.1)
        (est_S'_ind hL ht ht' hop hs hQ hfull hj)
        (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q))),
      (Tsite.y₁ = est_liftCrossing hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj) _ hu' ∧
        Tsite.y₂ = est_liftCrossing hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj) _ hv') ∨
      (Tsite.y₁ = est_liftCrossing hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj) _ hv' ∧
        Tsite.y₂ = est_liftCrossing hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj) _ hu') := by
  have h1 : (xPair hef').val ∈ triangleSupports e f g := (P1.mem_triangleSupports _).mpr (Or.inl rfl)
  have h2 : (xPair heg').val ∈ triangleSupports e f g := (P1.mem_triangleSupports _).mpr (Or.inr (Or.inl rfl))
  have h3 : (xPair hfg').val ∈ triangleSupports e f g := (P1.mem_triangleSupports _).mpr (Or.inr (Or.inr rfl))
  have n12 := P1.xPair_ef_ne_eg hef' heg' hfg'
  have n13 := P1.xPair_ef_ne_fg hef' heg' hfg'
  have n23 := P1.xPair_eg_ne_fg hef' heg' hfg'
  have key : ∀ {a b c : ZMod n} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
      (habc : ({a, b, c} : Finset (ZMod n)) = {e, f, g})
      (hjab : j.val = {a, b}) (huac : u.val = {a, c}) {v : Crossing (E.curve t)} (hvbc : v.val = {b, c})
      (hv : v.val ∈ triangleSupports e f g) (hjv : j ≠ v) (huv : u ≠ v),
      ∃ (v : Crossing (E.curve t)) (_hv : v.val ∈ triangleSupports e f g) (_hjv : j ≠ v) (_huv : u ≠ v)
        (hv' : crossingTransport hs v ∈ geoCarrierCrossings (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j}))
          (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q))
        (Tsite : s176_CornerSite (CV.carrierDiagram hn (genericAt E t' ht'.1)
          (est_S'_ind hL ht ht' hop hs hQ hfull hj)
          (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q))),
        (Tsite.y₁ = est_liftCrossing hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj) _ hu' ∧
          Tsite.y₂ = est_liftCrossing hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj) _ hv') ∨
        (Tsite.y₁ = est_liftCrossing hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj) _ hv' ∧
          Tsite.y₂ = est_liftCrossing hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj) _ hu') := by
    intro a b c hab hac hbc habc hjab huac v hvbc hv hjv huv
    obtain ⟨hv', Tsite, hc⟩ := s176_event_site_core hn hL hR hef heg hfg ht ht' hop hs hcomp hQ hfull hj q hu hju hu'
      hab hac hbc habc hjab huac hvbc hv hjv huv
    exact ⟨v, hv, hjv, huv, hv', Tsite, hc⟩
  have p_feg : ({f, e, g} : Finset (ZMod n)) = {e, f, g} := Finset.insert_comm f e {g}
  have p_egf : ({e, g, f} : Finset (ZMod n)) = {e, f, g} := congrArg (insert e) (Finset.pair_comm g f)
  have p_gef : ({g, e, f} : Finset (ZMod n)) = {e, f, g} :=
    (Finset.insert_comm g e {f}).trans (congrArg (insert e) (Finset.pair_comm g f))
  have p_fge : ({f, g, e} : Finset (ZMod n)) = {e, f, g} :=
    (congrArg (insert f) (Finset.pair_comm g e)).trans (Finset.insert_comm f e {g})
  have p_gfe : ({g, f, e} : Finset (ZMod n)) = {e, f, g} :=
    ((congrArg (insert g) (Finset.pair_comm f e)).trans (Finset.insert_comm g e {f})).trans
      (congrArg (insert e) (Finset.pair_comm g f))
  rcases GT_tri_cases t hef' heg' hfg' j hj with rfl | rfl | rfl <;>
    rcases GT_tri_cases t hef' heg' hfg' u hu with rfl | rfl | rfl
  · exact absurd rfl hju
  · exact key hef heg hfg rfl rfl rfl (v := xPair hfg') rfl h3 n13 n23
  · exact key hef.symm hfg heg p_feg (Finset.pair_comm e f) rfl (v := xPair heg') rfl h2 n12 n23.symm
  · exact key heg hef hfg.symm p_egf rfl rfl (v := xPair hfg') (Finset.pair_comm f g) h3 n23 n13
  · exact absurd rfl hju
  · exact key heg.symm hfg.symm hef p_gef (Finset.pair_comm e g) (Finset.pair_comm f g) (v := xPair hef') rfl h1
      n12.symm n13.symm
  · exact key hfg hef.symm heg.symm p_fge rfl (Finset.pair_comm e f) (v := xPair heg') (Finset.pair_comm e g) h2
      n23.symm n12
  · exact key hfg.symm heg.symm hef.symm p_gfe (Finset.pair_comm f g) (Finset.pair_comm e g) (v := xPair hef')
      (Finset.pair_comm e f) h1 n13.symm n12.symm
  · exact absurd rfl hju

/-- the keep-set is symmetric in the two deleted crossings -/
theorem s176_wallKeep_comm (hn : 3 ≤ n) {P' : LabelledTuple n} (hG' : CarrierGeometry P')
    {T' : Finset (Crossing P')} (hT' : GeoIndependent hG'.cg T') (q' : GeoComponent hG'.cg T')
    {u' v' : Crossing P'} (hu' : u' ∈ geoCarrierCrossings hG'.cg T' q') (hv' : v' ∈ geoCarrierCrossings hG'.cg T' q') :
    s176_wallKeep hn hG' hT' q' hu' hv' = s176_wallKeep hn hG' hT' q' hv' hu' := by
  ext c
  exact and_comm

/-- **The weak port of row 176 from the site and `s176_hrec_wall`** (item (c), with `hrec` in the
specific-crossings form): `s176_site_of_event'` + the frozen leaf + `s176_hrec_of_unswitched` +
`est_port_weak_of_bigon`. -/
theorem s176_port_weak_of_event' (hn : 3 ≤ n) (hL : LocalizationData E e f g δ) (hR : AV_EventRadius E δ)
    (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g) {t t' : E.Parameter} (ht : Punctured E δ t)
    (ht' : Punctured E δ t') (hop : OppositeSides E t t')
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    (hef' : IsCrossing (E.curve t) {e, f}) (heg' : IsCrossing (E.curve t) {e, g})
    (hfg' : IsCrossing (E.curve t) {f, g}) (hcomp : CompleteLocal (geomAt E t ht.1) hef' heg' hfg')
    {Q : Finset (Crossing (E.curve t))} (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
    (hfull : FullAvail (geomAt E t ht.1) e f g Q) {j : Crossing (E.curve t)}
    (hj : j.val ∈ triangleSupports e f g) (q : GeoComponent (geomAt E t ht.1) (Q ∪ {j}))
    {u : Crossing (E.curve t)} (hu : u.val ∈ triangleSupports e f g) (hju : j ≠ u)
    (hu' : crossingTransport hs u ∈ geoCarrierCrossings (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j}))
        (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q))
    (hrec : s176_hrec_wall hn hL hR hef heg hfg ht ht' hop hs hQ hfull hj q hu') :
    est_port_weak
      (CV.carrierDiagram hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj)
        (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q))
      (CV.carrierDiagram hn (genericAt E t ht.1) (est_S_ind ht.1 hQ hfull hj) q)
      (est_liftCrossing hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj) _ hu') := by
  obtain ⟨v, hv, hjv, huv, hv', Tsite, hc⟩ := s176_site_of_event' hn hL hR hef heg hfg ht ht' hop hs hef' heg' hfg'
    hcomp hQ hfull hj q hu hju hu'
  unfold s176_hrec_wall at hrec
  have hR' := hrec v hv hjv huv hv'
  rcases hc with ⟨hy₁, hy₂⟩ | ⟨hy₁, hy₂⟩
  · -- `y = Tsite.y₁ = lift u'`, `Tsite.y₂ = lift v'`
    rw [← hy₁]
    obtain ⟨B, -, hB₁, hB₂⟩ := Tsite.exists_bigon_switch₁
    refine est_port_weak_of_bigon _ _ _ rfl rfl B ?_
    rw [s176_reducedRecord_eq B hB₁ hB₂]
    refine s176_hrec_of_unswitched _ _ _ Tsite.y₁ Tsite.y₂ (Or.inl rfl) ?_
    rw [hy₁, hy₂]
    exact hR'
  · -- `y = Tsite.y₂ = lift u'`, `Tsite.y₁ = lift v'`
    rw [← hy₂]
    obtain ⟨B, -, hB₁, hB₂⟩ := Tsite.exists_bigon_switch₂
    refine est_port_weak_of_bigon _ _ _ rfl rfl B ?_
    rw [s176_reducedRecord_eq B hB₁ hB₂]
    refine s176_hrec_of_unswitched _ _ _ Tsite.y₁ Tsite.y₂ (Or.inr rfl) ?_
    rw [hy₁, hy₂]
    have hcomm := s176_wallKeep_comm hn (CarrierGeometry.ofDiagrammatic ((genericAt E t' ht'.1).diagrammatic hn))
      (CV.geoIndependent_of_mem_Ind _ (est_S'_ind hL ht ht' hop hs hQ hfull hj))
      (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q) hu' hv'
    rw [hcomm] at hR'
    exact hR'

/-- **The weak interface of row 176 from `s176_hrec_wall` and the non-move port data** (the specific-crossings
form of `s176_est_port_relation_weak_of`). -/
theorem s176_est_port_relation_weak_of'
    (hrec : ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (E : CV.Event n) (e f g : ZMod n) (δ : ℝ)
      (hL : LocalizationData E e f g δ) (hR : AV_EventRadius E δ) (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
      (t t' : E.Parameter) (ht : Punctured E δ t) (ht' : Punctured E δ t') (hop : OppositeSides E t t')
      (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
      (Q : Finset (Crossing (E.curve t))) (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
      (hfull : FullAvail (geomAt E t ht.1) e f g Q) (j : Crossing (E.curve t))
      (hj : j.val ∈ triangleSupports e f g) (q : GeoComponent (geomAt E t ht.1) (Q ∪ {j}))
      (u : Crossing (E.curve t))
      (hu' : crossingTransport hs u ∈ geoCarrierCrossings (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j}))
        (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)),
      s176_hrec_wall hn hL hR hef heg hfg ht ht' hop hs hQ hfull hj q hu')
    (hrest : ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (E : CV.Event n) (e f g : ZMod n) (δ : ℝ)
      (hL : LocalizationData E e f g δ) (hR : AV_EventRadius E δ) (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
      (t t' : E.Parameter) (ht : Punctured E δ t) (ht' : Punctured E δ t') (hop : OppositeSides E t t')
      (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
      (Q : Finset (Crossing (E.curve t))) (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
      (hfull : FullAvail (geomAt E t ht.1) e f g Q) (j : Crossing (E.curve t))
      (hj : j.val ∈ triangleSupports e f g) (q : GeoComponent (geomAt E t ht.1) (Q ∪ {j}))
      (u : Crossing (E.curve t))
      (hu' : crossingTransport hs u ∈ geoCarrierCrossings (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j}))
        (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)),
      Nonempty (s176_PortDataRest hn (genericAt E t ht.1) (genericAt E t' ht'.1) (est_S_ind ht.1 hQ hfull hj)
        (est_S'_ind hL ht ht' hop hs hQ hfull hj) q
        (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)
        (est_liftCrossing hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj) _ hu'))) :
    s176_est_port_relation_weak := by
  intro n _ hn E e f g δ hL hR hef heg hfg t t' ht ht' hop hs hef' heg' hfg' hcomp Q hQ hfull j hj q hex
  obtain ⟨u, hu, hju, hu'⟩ := hex
  obtain ⟨R⟩ := hrest n hn E e f g δ hL hR hef heg hfg t t' ht ht' hop hs Q hQ hfull j hj q u hu'
  refine ⟨u, hu, hju, hu', ⟨s176_PortDataWeak.mk' _ _ _ _ _ _ _ _ ?_ R⟩⟩
  exact s176_port_weak_of_event' hn hL hR hef heg hfg ht ht' hop hs hef' heg' hfg' hcomp hQ hfull hj q hu hju.symm
    hu' (hrec n hn E e f g δ hL hR hef heg hfg t t' ht ht' hop hs Q hQ hfull j hj q u hu')

end S176HrecWall

end

end RProof

/-! # R176_HSUCC — the successor clause `hsucc` of `hrec` (row 176), and the discharge of the chain

Unit HSUCC (2026-09-15).  Everything above this line is `Site_176.lean`, frozen.  This appendix proves the
single remaining clause of the record identification `hrec` of row 176 (Site_176_REPORT §3):

  `hsucc : ∀ w, Φ ((D₊.record.restrictCrossings (s176_wallKeep u' v')).succ w) = D₀.record.succ (Φ w)`

— the first-return successor of a retained occurrence of the L-side lift `D₊` (the crossings at `u', v'`
deleted) corresponds under the wall bijection `s176_wallΦ` to the H-side successor.  Proof shape (the W1
skeleton's `m6_succ`, with two deleted crossings and a wall instead of a deletion): the cyclic order of three
retained occurrences is read on the parents (`CV.visitBetween_iff_key` on both lifts) and carried across the wall
by `GT_Wall.key_lt` (every pair of retained parent visits of `q₀` is non-reversed: retained crossings of `q₀` are
not triangle crossings, `est_not_retained_H`, so `GT_not_rev_of_not_mem_left`); the first return has no retained
occurrence strictly between (`firstReturn_no_between` with `nextVisit_no_between`), the H-side successor has no
occurrence strictly between (`nextVisit_no_between`), both differ from the start (`Record.firstReturn_val_ne` with
the twin, `nextVisit_ne_self`), and `cycNext_unique` on the H-side traversal coordinate identifies them.

Then the chain: `r176h_hrec_wall_proof : s176_hrec_wall …` (via `s176_hrec_wall_of_succ`),
`r176h_est_port_weak : est_port_weak (carrierDiagram q₀') (carrierDiagram q₀) (est_liftCrossing … hu')` (via
`s176_port_weak_of_event'`), the weak interface from the non-move port data alone
(`r176h_est_port_relation_weak_of_rest`), and the weak ledger from it (`r176h_est_ledger_weak_of_rest`).
All names `r176h_`. -/

namespace RProof

open SM SM.GeoCarrier SM.Carrier SM.Link

noncomputable section

variable {n : ℕ} [NeZero n]

/-! ## §I. One-component bookkeeping of a positive lift -/

/-- all occurrences of a positive lift lie on its single component -/
theorem r176h_compOf_eq (hn : 3 ≤ n) {P : LabelledTuple n} (hG : CarrierGeometry P) {T : Finset (Crossing P)}
    (hT : GeoIndependent hG.cg T) (q : GeoComponent hG.cg T) (v w : (geoPositiveLift hn hG hT q).Γ.Visit) :
    (geoPositiveLift hn hG hT q).compOf v = (geoPositiveLift hn hG hT q).compOf w := by
  apply Fin.ext
  have h1 := ((geoPositiveLift hn hG hT q).compOf v).isLt
  have h2 := ((geoPositiveLift hn hG hT q).compOf w).isLt
  change _ < 1 at h1 h2
  omega

/-- the traversal coordinate of a positive lift is injective (one component) -/
theorem r176h_visitCoord_injective (hn : 3 ≤ n) {P : LabelledTuple n} (hG : CarrierGeometry P)
    {T : Finset (Crossing P)} (hT : GeoIndependent hG.cg T) (q : GeoComponent hG.cg T) :
    Function.Injective (geoPositiveLift hn hG hT q).visitCoord :=
  fun v w h => (geoPositiveLift hn hG hT q).visitCoord_injOn (r176h_compOf_eq hn hG hT q v w) h

/-- the record of a positive lift has one component -/
theorem r176h_record_componentCount (hn : 3 ≤ n) {P : LabelledTuple n} (hG : CarrierGeometry P)
    {T : Finset (Crossing P)} (hT : GeoIndependent hG.cg T) (q : GeoComponent hG.cg T) :
    (geoPositiveLift hn hG hT q).record.componentCount = 1 :=
  ((geoPositiveLift hn hG hT q).record_componentCount).trans (geoPositiveLift_componentCount hn hG hT q)

/-! ## §J. The successor clause at the carrier level -/

section R176HWall

variable (hn : 3 ≤ n) {P P' : LabelledTuple n} (hG : CarrierGeometry P) (hG' : CarrierGeometry P')
  (hs : ∀ s, IsCrossing P s ↔ IsCrossing P' s)
  {T : Finset (Crossing P)} {T' : Finset (Crossing P')} (hT : GeoIndependent hG.cg T)
  (hT' : GeoIndependent hG'.cg T') (q : GeoComponent hG.cg T) (q' : GeoComponent hG'.cg T')
  {u' v' : Crossing P'} (hu' : u' ∈ geoCarrierCrossings hG'.cg T' q') (hv' : v' ∈ geoCarrierCrossings hG'.cg T' q')
  (hX : geoCarrierCrossings hG'.cg T' q' =
    (geoCarrierCrossings hG.cg T q).map (crossingTransport hs).toEmbedding ∪ {u', v'})
  (hu_not : u' ∉ (geoCarrierCrossings hG.cg T q).map (crossingTransport hs).toEmbedding)
  (hv_not : v' ∉ (geoCarrierCrossings hG.cg T q).map (crossingTransport hs).toEmbedding)
  (hkey : ∀ v w : Visit P, v.1 ∈ geoCarrierCrossings hG.cg T q → w.1 ∈ geoCarrierCrossings hG.cg T q →
    (geometricVisitKey hG.cg v < geometricVisitKey hG.cg w ↔
      geometricVisitKey hG'.cg (visitTransport hs v) < geometricVisitKey hG'.cg (visitTransport hs w)))

include hkey in
/-- the key order of the parent visits of two retained occurrences is carried across the wall
(`s176_wallΦ_liftVisit` + `hkey` at the transported-back parents) -/
theorem r176h_key_lt_iff (v u : {v : (geoPositiveLift hn hG' hT' q').Γ.Visit //
    (geoPositiveLift hn hG' hT' q').record.CrossKeep (s176_wallKeep hn hG' hT' q' hu' hv') v}) :
    geometricVisitKey hG.cg (CV.liftVisit hn hG hT q (s176_wallΦ hn hG hG' hs hT hT' q q' hu' hv' hX hu_not hv_not v)) <
        geometricVisitKey hG.cg (CV.liftVisit hn hG hT q (s176_wallΦ hn hG hG' hs hT hT' q q' hu' hv' hX hu_not hv_not u)) ↔
      geometricVisitKey hG'.cg (CV.liftVisit hn hG' hT' q' v.1) <
        geometricVisitKey hG'.cg (CV.liftVisit hn hG' hT' q' u.1) := by
  have h := hkey _ _
    (CV.liftVisit_mem hn hG hT q (s176_wallΦ hn hG hG' hs hT hT' q q' hu' hv' hX hu_not hv_not v))
    (CV.liftVisit_mem hn hG hT q (s176_wallΦ hn hG hG' hs hT hT' q q' hu' hv' hX hu_not hv_not u))
  rw [s176_wallΦ_liftVisit hn hG hG' hs hT hT' q q' hu' hv' hX hu_not hv_not v,
    s176_wallΦ_liftVisit hn hG hG' hs hT hT' q q' hu' hv' hX hu_not hv_not u,
    Equiv.apply_symm_apply, Equiv.apply_symm_apply] at h
  rw [s176_wallΦ_liftVisit hn hG hG' hs hT hT' q q' hu' hv' hX hu_not hv_not v,
    s176_wallΦ_liftVisit hn hG hG' hs hT hT' q q' hu' hv' hX hu_not hv_not u]
  exact h

include hkey in
/-- the oriented cyclic order of three retained occurrences is carried across the wall
(`CV.visitBetween_iff_key` on both lifts, `r176h_key_lt_iff` on the three pairs) -/
theorem r176h_cycBetween_iff (v u x : {v : (geoPositiveLift hn hG' hT' q').Γ.Visit //
    (geoPositiveLift hn hG' hT' q').record.CrossKeep (s176_wallKeep hn hG' hT' q' hu' hv') v}) :
    cycBetween
        ((geoPositiveLift hn hG hT q).visitCoord (s176_wallΦ hn hG hG' hs hT hT' q q' hu' hv' hX hu_not hv_not v))
        ((geoPositiveLift hn hG hT q).visitCoord (s176_wallΦ hn hG hG' hs hT hT' q q' hu' hv' hX hu_not hv_not u))
        ((geoPositiveLift hn hG hT q).visitCoord (s176_wallΦ hn hG hG' hs hT hT' q q' hu' hv' hX hu_not hv_not x)) ↔
      cycBetween ((geoPositiveLift hn hG' hT' q').visitCoord v.1) ((geoPositiveLift hn hG' hT' q').visitCoord u.1)
        ((geoPositiveLift hn hG' hT' q').visitCoord x.1) := by
  show (geoPositiveLift hn hG hT q).VisitBetween (s176_wallΦ hn hG hG' hs hT hT' q q' hu' hv' hX hu_not hv_not v)
      (s176_wallΦ hn hG hG' hs hT hT' q q' hu' hv' hX hu_not hv_not u)
      (s176_wallΦ hn hG hG' hs hT hT' q q' hu' hv' hX hu_not hv_not x) ↔
    (geoPositiveLift hn hG' hT' q').VisitBetween v.1 u.1 x.1
  rw [CV.visitBetween_iff_key, CV.visitBetween_iff_key]
  unfold cycBetween
  rw [r176h_key_lt_iff hn hG hG' hs hT hT' q q' hu' hv' hX hu_not hv_not hkey v u,
    r176h_key_lt_iff hn hG hG' hs hT hT' q q' hu' hv' hX hu_not hv_not hkey u x,
    r176h_key_lt_iff hn hG hG' hs hT hT' q q' hu' hv' hX hu_not hv_not hkey x v]

include hkey in
/-- **`hsucc` in the `firstReturn` form**: the first return of the L-side successor to the retained occurrences
corresponds under `s176_wallΦ` to the H-side successor.  `cycNext_unique` on the H-side traversal coordinate: both
candidates differ from `Φ w` (`Record.firstReturn_val_ne` with the retained twin; `record_succ_eq_self_iff` with the
twin), and neither has an occurrence strictly between `Φ w` and itself (`firstReturn_no_between` carried across the
wall by `r176h_cycBetween_iff`; `record_succ_no_between`). -/
theorem r176h_succ_firstReturn (w : {v : (geoPositiveLift hn hG' hT' q').Γ.Visit //
    (geoPositiveLift hn hG' hT' q').record.CrossKeep (s176_wallKeep hn hG' hT' q' hu' hv') v}) :
    s176_wallΦ hn hG hG' hs hT hT' q q' hu' hv' hX hu_not hv_not
        (firstReturn (geoPositiveLift hn hG' hT' q').record.succ
          ((geoPositiveLift hn hG' hT' q').record.CrossKeep (s176_wallKeep hn hG' hT' q' hu' hv')) w) =
      (geoPositiveLift hn hG hT q).record.succ (s176_wallΦ hn hG hG' hs hT hT' q q' hu' hv' hX hu_not hv_not w) := by
  have h1 : (geoPositiveLift hn hG' hT' q').record.componentCount = 1 := r176h_record_componentCount hn hG' hT' q'
  obtain ⟨k, hk, hkw⟩ :=
    (geoPositiveLift hn hG' hT' q').record.crossKeep_exists_ne (s176_wallKeep hn hG' hT' q' hu' hv') w.2
  have hne : firstReturn (geoPositiveLift hn hG' hT' q').record.succ
      ((geoPositiveLift hn hG' hT' q').record.CrossKeep (s176_wallKeep hn hG' hT' q' hu' hv')) w ≠ w := by
    intro h
    exact (geoPositiveLift hn hG' hT' q').record.firstReturn_val_ne _ h1 w hk hkw (congrArg Subtype.val h)
  refine cycNext_unique (k := (geoPositiveLift hn hG hT q).visitCoord)
    (v := s176_wallΦ hn hG hG' hs hT hT' q q' hu' hv' hX hu_not hv_not w)
    (r176h_visitCoord_injective hn hG hT q)
    (fun h => hne ((s176_wallΦ hn hG hG' hs hT hT' q q' hu' hv' hX hu_not hv_not).injective h)) ?_ ?_ ?_
  · intro h
    exact (geoPositiveLift hn hG hT q).twin_ne (s176_wallΦ hn hG hG' hs hT hT' q q' hu' hv' hX hu_not hv_not w)
      (((geoPositiveLift hn hG hT q).record_succ_eq_self_iff
          (s176_wallΦ hn hG hG' hs hT hT' q q' hu' hv' hX hu_not hv_not w)).mp h
        ((geoPositiveLift hn hG hT q).twin (s176_wallΦ hn hG hG' hs hT hT' q q' hu' hv' hX hu_not hv_not w))
        (r176h_compOf_eq hn hG hT q
          ((geoPositiveLift hn hG hT q).twin (s176_wallΦ hn hG hG' hs hT hT' q q' hu' hv' hX hu_not hv_not w))
          (s176_wallΦ hn hG hG' hs hT hT' q q' hu' hv' hX hu_not hv_not w)))
  · intro u hb
    -- read `u` as the image of a retained occurrence and carry the cyclic order back to the L side
    have hb' := (r176h_cycBetween_iff hn hG hG' hs hT hT' q q' hu' hv' hX hu_not hv_not hkey w
      ((s176_wallΦ hn hG hG' hs hT hT' q q' hu' hv' hX hu_not hv_not).symm u)
      (firstReturn (geoPositiveLift hn hG' hT' q').record.succ
        ((geoPositiveLift hn hG' hT' q').record.CrossKeep (s176_wallKeep hn hG' hT' q' hu' hv')) w)).mp
      (by rwa [Equiv.apply_symm_apply])
    exact firstReturn_no_between (geoPositiveLift hn hG' hT' q').record.succ
      ((geoPositiveLift hn hG' hT' q').record.CrossKeep (s176_wallKeep hn hG' hT' q' hu' hv'))
      (geoPositiveLift hn hG' hT' q').visitCoord
      (fun a b _ he => (geoPositiveLift hn hG' hT' q').visitCoord_injOn (r176h_compOf_eq hn hG' hT' q' b a) he)
      (fun a b _ => (geoPositiveLift hn hG' hT' q').record_succ_no_between a b (r176h_compOf_eq hn hG' hT' q' b a))
      w ((s176_wallΦ hn hG hG' hs hT hT' q q' hu' hv' hX hu_not hv_not).symm u).1
      (((geoPositiveLift hn hG' hT' q').record.sameCycle_iff_comp_eq _ _).mpr
        (r176h_compOf_eq hn hG' hT' q' _ _))
      ((s176_wallΦ hn hG hG' hs hT hT' q q' hu' hv' hX hu_not hv_not).symm u).2 hb'
  · intro u
    exact (geoPositiveLift hn hG hT q).record_succ_no_between _ u (r176h_compOf_eq hn hG hT q u _)

include hkey in
/-- **`hsucc` — the successor clause of `hrec`** (Site_176_REPORT §3), in the exact shape of the hypothesis of
`s176_hrec_unswitched_of_succ`: the successor of the restricted record is the first return
(`Record.restrictCrossings_succ_val`, `rfl`). -/
theorem r176h_succ (w : {v : (geoPositiveLift hn hG' hT' q').Γ.Visit //
    (geoPositiveLift hn hG' hT' q').record.CrossKeep (s176_wallKeep hn hG' hT' q' hu' hv') v}) :
    s176_wallΦ hn hG hG' hs hT hT' q q' hu' hv' hX hu_not hv_not
        (((geoPositiveLift hn hG' hT' q').record.restrictCrossings (s176_wallKeep hn hG' hT' q' hu' hv')).succ w) =
      (geoPositiveLift hn hG hT q).record.succ (s176_wallΦ hn hG hG' hs hT hT' q q' hu' hv' hX hu_not hv_not w) := by
  have e : ((geoPositiveLift hn hG' hT' q').record.restrictCrossings (s176_wallKeep hn hG' hT' q' hu' hv')).succ w =
      firstReturn (geoPositiveLift hn hG' hT' q').record.succ
        ((geoPositiveLift hn hG' hT' q').record.CrossKeep (s176_wallKeep hn hG' hT' q' hu' hv')) w :=
    Subtype.ext ((geoPositiveLift hn hG' hT' q').record.restrictCrossings_succ_val
      (s176_wallKeep hn hG' hT' q' hu' hv') w)
  rw [e]
  exact r176h_succ_firstReturn hn hG hG' hs hT hT' q q' hu' hv' hX hu_not hv_not hkey w

include hX hu_not hv_not hkey in
/-- **`hrec` at the carrier level, closed**: the wall transport of the two-crossing-deleted record
(`s176_hrec_unswitched_of_succ` with `r176h_succ`). -/
theorem r176h_hrec_unswitched
    (hdet : ∀ w : Visit P, w.1 ∈ geoCarrierCrossings hG.cg T q →
      (0 < det (edge P w.2.val) (edge P (visitTwin w).2.val) ↔
        0 < det (edge P' w.2.val) (edge P' (visitTwin w).2.val))) :
    Nonempty (RecordIso
      ((geoPositiveLift hn hG' hT' q').record.restrictCrossings (s176_wallKeep hn hG' hT' q' hu' hv'))
      (geoPositiveLift hn hG hT q).record) :=
  s176_hrec_unswitched_of_succ hn hG hG' hs hT hT' q q' hu' hv' hX hu_not hv_not hdet
    (r176h_succ hn hG hG' hs hT hT' q q' hu' hv' hX hu_not hv_not hkey)

end R176HWall

end

end RProof

namespace RProof

open SM SM.GeoCarrier SM.Carrier SM.Link

noncomputable section

variable {n : ℕ} [NeZero n]

/-! ## §K. The event level: `hkey` from the wall data, `s176_hrec_wall` PROVED, the weak port, the weak
interface and the weak ledger from the non-move port data alone -/

section R176HEvent

variable {E : CV.Event n} {e f g : ZMod n} {δ : ℝ}

/-- the key order of the parent visits is carried across the wall for every pair whose first visit is at a
retained crossing of `q₀` (`est_wall.key_lt`; a retained crossing of `q₀` is not a triangle crossing,
`est_not_retained_H`, so the pair is not reversed, `GT_not_rev_of_not_mem_left`) -/
theorem r176h_hkey_event (hL : LocalizationData E e f g δ) (hR : AV_EventRadius E δ)
    (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g) {t t' : E.Parameter} (ht : Punctured E δ t)
    (ht' : Punctured E δ t') (hop : OppositeSides E t t')
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    {hef' : IsCrossing (E.curve t) {e, f}} {heg' : IsCrossing (E.curve t) {e, g}}
    {hfg' : IsCrossing (E.curve t) {f, g}} (hcomp : CompleteLocal (geomAt E t ht.1) hef' heg' hfg')
    {Q : Finset (Crossing (E.curve t))} (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
    (hfull : FullAvail (geomAt E t ht.1) e f g Q) {j : Crossing (E.curve t)}
    (hj : j.val ∈ triangleSupports e f g) (q : GeoComponent (geomAt E t ht.1) (Q ∪ {j}))
    (v w : Visit (E.curve t)) (hv : v.1 ∈ geoCarrierCrossings (geomAt E t ht.1) (Q ∪ {j}) q) :
    geometricVisitKey (geomAt E t ht.1) v < geometricVisitKey (geomAt E t ht.1) w ↔
      geometricVisitKey (geomAt E t' ht'.1) (visitTransport hs v) <
        geometricVisitKey (geomAt E t' ht'.1) (visitTransport hs w) :=
  (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj).key_lt v w
    (GT_not_rev_of_not_mem_left fun h =>
      est_not_retained_H ht hcomp hQ hfull hj q hv ((F1.mem_triangleCrossings e f g v.1).mp h))

/-- **`s176_hrec_wall` PROVED** (rule (1) form `r176h_<name>_proof`): the record identification of row 176 for the
deleted crossings `lift u', lift v'`, for every third triangle crossing `v` with `v'` retained — through
`s176_hrec_wall_of_succ` with the successor clause `r176h_succ` and the wall key order `r176h_hkey_event`. -/
theorem r176h_hrec_wall_proof (hn : 3 ≤ n) (hL : LocalizationData E e f g δ) (hR : AV_EventRadius E δ)
    (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g) {t t' : E.Parameter} (ht : Punctured E δ t)
    (ht' : Punctured E δ t') (hop : OppositeSides E t t')
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    {hef' : IsCrossing (E.curve t) {e, f}} {heg' : IsCrossing (E.curve t) {e, g}}
    {hfg' : IsCrossing (E.curve t) {f, g}} (hcomp : CompleteLocal (geomAt E t ht.1) hef' heg' hfg')
    {Q : Finset (Crossing (E.curve t))} (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
    (hfull : FullAvail (geomAt E t ht.1) e f g Q) {j : Crossing (E.curve t)}
    (hj : j.val ∈ triangleSupports e f g) (q : GeoComponent (geomAt E t ht.1) (Q ∪ {j}))
    {u : Crossing (E.curve t)} (hu : u.val ∈ triangleSupports e f g) (hju : j ≠ u)
    (hu' : crossingTransport hs u ∈ geoCarrierCrossings (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j}))
        (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)) :
    s176_hrec_wall hn hL hR hef heg hfg ht ht' hop hs hQ hfull hj q hu' :=
  s176_hrec_wall_of_succ hn hL hR hef heg hfg ht ht' hop hs hcomp hQ hfull hj q hu hju hu'
    (fun _v hv hjv huv hv' w => r176h_succ hn _ _ hs _ _ q _ hu' hv'
      (s176_hX_event hL hR hef heg hfg ht ht' hop hs hcomp hQ hfull hj q hu hju hu' hv hjv huv)
      (s176_not_mem_map_event ht hs hcomp hQ hfull hj q hu)
      (s176_not_mem_map_event ht hs hcomp hQ hfull hj q hv)
      (fun a b ha _ => r176h_hkey_event hL hR hef heg hfg ht ht' hop hs hcomp hQ hfull hj q a b ha) w)

/-- `s176_hrec_wall`, under the unit's own name. -/
theorem r176h_hrec_wall (hn : 3 ≤ n) (hL : LocalizationData E e f g δ) (hR : AV_EventRadius E δ)
    (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g) {t t' : E.Parameter} (ht : Punctured E δ t)
    (ht' : Punctured E δ t') (hop : OppositeSides E t t')
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    {hef' : IsCrossing (E.curve t) {e, f}} {heg' : IsCrossing (E.curve t) {e, g}}
    {hfg' : IsCrossing (E.curve t) {f, g}} (hcomp : CompleteLocal (geomAt E t ht.1) hef' heg' hfg')
    {Q : Finset (Crossing (E.curve t))} (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
    (hfull : FullAvail (geomAt E t ht.1) e f g Q) {j : Crossing (E.curve t)}
    (hj : j.val ∈ triangleSupports e f g) (q : GeoComponent (geomAt E t ht.1) (Q ∪ {j}))
    {u : Crossing (E.curve t)} (hu : u.val ∈ triangleSupports e f g) (hju : j ≠ u)
    (hu' : crossingTransport hs u ∈ geoCarrierCrossings (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j}))
        (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)) :
    s176_hrec_wall hn hL hR hef heg hfg ht ht' hop hs hQ hfull hj q hu' :=
  r176h_hrec_wall_proof hn hL hR hef heg hfg ht ht' hop hs hcomp hQ hfull hj q hu hju hu'

/-- **The weak RII port of row 176** (item (c) of the site unit, now with `hrec` DISCHARGED):
`est_port_weak (carrierDiagram q₀') (carrierDiagram q₀) (est_liftCrossing … hu')`, through the frozen leaf
`exists_bigonData_of_triangle` only (`s176_port_weak_of_event'` + `r176h_hrec_wall_proof`). -/
theorem r176h_est_port_weak (hn : 3 ≤ n) (hL : LocalizationData E e f g δ) (hR : AV_EventRadius E δ)
    (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g) {t t' : E.Parameter} (ht : Punctured E δ t)
    (ht' : Punctured E δ t') (hop : OppositeSides E t t')
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    (hef' : IsCrossing (E.curve t) {e, f}) (heg' : IsCrossing (E.curve t) {e, g})
    (hfg' : IsCrossing (E.curve t) {f, g}) (hcomp : CompleteLocal (geomAt E t ht.1) hef' heg' hfg')
    {Q : Finset (Crossing (E.curve t))} (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
    (hfull : FullAvail (geomAt E t ht.1) e f g Q) {j : Crossing (E.curve t)}
    (hj : j.val ∈ triangleSupports e f g) (q : GeoComponent (geomAt E t ht.1) (Q ∪ {j}))
    {u : Crossing (E.curve t)} (hu : u.val ∈ triangleSupports e f g) (hju : j ≠ u)
    (hu' : crossingTransport hs u ∈ geoCarrierCrossings (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j}))
        (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)) :
    est_port_weak
      (CV.carrierDiagram hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj)
        (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q))
      (CV.carrierDiagram hn (genericAt E t ht.1) (est_S_ind ht.1 hQ hfull hj) q)
      (est_liftCrossing hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj) _ hu') :=
  s176_port_weak_of_event' hn hL hR hef heg hfg ht ht' hop hs hef' heg' hfg' hcomp hQ hfull hj q hu hju hu'
    (r176h_hrec_wall_proof hn hL hR hef heg hfg ht ht' hop hs hcomp hQ hfull hj q hu hju hu')

end R176HEvent

/-- **The weak interface of row 176 from the non-move port data ALONE** — `s176_est_port_relation_weak_of'`
with its `hrec` hypothesis discharged.  (The frozen `s176_est_port_relation_weak_of'` quantifies `hrec` without
`hcomp`, `hu`, `hju`, which `s176_hrec_wall_of_succ` needs; its `intro` has them, so the port is built here
directly from `r176h_est_port_weak`.)  The `hrest` binder is byte-identical to that of
`s176_est_port_relation_weak_of'`. -/
theorem r176h_est_port_relation_weak_of_rest
    (hrest : ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (E : CV.Event n) (e f g : ZMod n) (δ : ℝ)
      (hL : LocalizationData E e f g δ) (hR : AV_EventRadius E δ) (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
      (t t' : E.Parameter) (ht : Punctured E δ t) (ht' : Punctured E δ t') (hop : OppositeSides E t t')
      (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
      (Q : Finset (Crossing (E.curve t))) (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
      (hfull : FullAvail (geomAt E t ht.1) e f g Q) (j : Crossing (E.curve t))
      (hj : j.val ∈ triangleSupports e f g) (q : GeoComponent (geomAt E t ht.1) (Q ∪ {j}))
      (u : Crossing (E.curve t))
      (hu' : crossingTransport hs u ∈ geoCarrierCrossings (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j}))
        (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)),
      Nonempty (s176_PortDataRest hn (genericAt E t ht.1) (genericAt E t' ht'.1) (est_S_ind ht.1 hQ hfull hj)
        (est_S'_ind hL ht ht' hop hs hQ hfull hj) q
        (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)
        (est_liftCrossing hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj) _ hu'))) :
    s176_est_port_relation_weak := by
  intro n _ hn E e f g δ hL hR hef heg hfg t t' ht ht' hop hs hef' heg' hfg' hcomp Q hQ hfull j hj q hex
  obtain ⟨u, hu, hju, hu'⟩ := hex
  obtain ⟨R⟩ := hrest n hn E e f g δ hL hR hef heg hfg t t' ht ht' hop hs Q hQ hfull j hj q u hu'
  refine ⟨u, hu, hju, hu', ⟨s176_PortDataWeak.mk' _ _ _ _ _ _ _ _ ?_ R⟩⟩
  exact r176h_est_port_weak hn hL hR hef heg hfg ht ht' hop hs hef' heg' hfg' hcomp hQ hfull hj q hu hju.symm hu'

/-- **The weak RA ledger of row 176 from the non-move port data alone** (`s176_est_ledger_weak` +
`r176h_est_port_relation_weak_of_rest`): what row 176 still owes is exactly `s176_PortDataRest`
(U_R176_REPORT §5 items 2–5) and the F-176-1 acceptance. -/
theorem r176h_est_ledger_weak_of_rest (hF : CV.CarrierSlotFloor)
    (hrest : ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (E : CV.Event n) (e f g : ZMod n) (δ : ℝ)
      (hL : LocalizationData E e f g δ) (hR : AV_EventRadius E δ) (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
      (t t' : E.Parameter) (ht : Punctured E δ t) (ht' : Punctured E δ t') (hop : OppositeSides E t t')
      (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
      (Q : Finset (Crossing (E.curve t))) (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
      (hfull : FullAvail (geomAt E t ht.1) e f g Q) (j : Crossing (E.curve t))
      (hj : j.val ∈ triangleSupports e f g) (q : GeoComponent (geomAt E t ht.1) (Q ∪ {j}))
      (u : Crossing (E.curve t))
      (hu' : crossingTransport hs u ∈ geoCarrierCrossings (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j}))
        (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)),
      Nonempty (s176_PortDataRest hn (genericAt E t ht.1) (genericAt E t' ht'.1) (est_S_ind ht.1 hQ hfull hj)
        (est_S'_ind hL ht ht' hop hs hQ hfull hj) q
        (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)
        (est_liftCrossing hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj) _ hu'))) :
    RowShape @ExtremeTransportData :=
  s176_est_ledger_weak hF (r176h_est_port_relation_weak_of_rest hrest)

end

end RProof


/-! # R176_SMOOTH — row 176 (R:extreme_transport), the SMOOTH unit: `s176_PortDataRest` items (T1) and (9)/(9a)

APPENDED by the R176 SMOOTH prover, 2026-09-15, to `Site_176.lean` (byte-identical above this line).
Companion report: `R176_SMOOTH_REPORT.md`.  All names carry the prefix `r176s_`; nothing above is modified.

Content (U_R176_REPORT §5 items 2–3, the (T1)/(9)/(9a) fields of `s176_PortDataRest`):
* §R1 the record core: on a one-circle record `ρ` with an occurrence `x`, the two cycles of the reconnected
  successor `s₁ = s ∘ swap x (τ x)` are the two open arcs `A = (x → τ x)` and `B = (τ x → x)`
  (`r176s_smooth_comp_eq_pair_iff`, `r176s_smooth_comp_eq_self_iff`); the first return of `s₁` to any set of
  occurrences of one arc is the first return of `s` (`r176s_firstReturn_reconnect`); hence **the restriction of
  the smoothed record to one component is `ρ` restricted to the crossings with both occurrences on that arc**
  (`r176s_smoothRestrictIso`, `r176s_smoothRestrictIso'`).
* §R2 the oriented smoothing `D_A`: `r176s_DA := smoothDiagram` (the library construction, with its record
  clause `r176s_DA_record_visit`), `IsOrientedSmoothing` (`r176s_DA_smooth`), `componentCount = 2` on a
  one-component diagram (`r176s_DA_componentCount`), the two component tags `r176s_DA_i` (the `B`-arc class of
  `v`) and `r176s_DA_j` (the `A`-arc class of `τ v`), `r176s_DA_ij`; the knot restrictions of `D_A` are the
  restrictions of the record of `D_+` to the arc crossings (`r176s_knotRestrictIso_i`, `r176s_knotRestrictIso_j`).
* §R3 the exact owner map: a diagram whose record is the lift of `q'` restricted to the chords of an inner
  carrier `Λ` has `homfly` = that of the lift of `Λ` (`r176s_homfly_of_liftBlock`, `CV.liftRestrictRecordIso`);
  with one kink through the record-level R-I black box `r176s_curl_removal`
  (`r176s_homfly_of_liftBlock_curl`); `homfly X = P_{S_f,Λ}` from a record identification
  (`r176s_homfly_eq_groupedPoly`).
* §R4 `S_full = Q' ∪ {j', u', v'}` is independent on `L` (`r176s_Sfull_ind`), its transport form (`r176s_Sfull_eq`).
* §R5 the event level: the DATA `r176s_OuterData` (the two outer carriers `Λ_A, Λ_B` of `S_full`, the occurrence
  `v₀` of `y`, the kink `r`, and the identification of the arc crossing sets with the chords of the outer
  carriers — the remaining GEOMETRIC obligation of this unit, consumed as the black box
  `r176s_outer_carriers`), the ledger black box `r176s_ledger` ((14), (13), (12): other units), the third
  triangle crossing (`r176s_third`), **the construction of `s176_PortDataRest`** (`r176s_portDataRest_of`:
  `DA, smooth, two, i, j, ij, Sf, hSf, Λ₁, Λ₂, poly₁, poly₂, ℓ, link` PROVED from the black boxes, the ledger
  fields from `r176s_ledger`), and the weak interface with the enriched `hrest` binders
  (`r176s_est_port_relation_weak_of''`). -/

namespace RProof

open SM SM.GeoCarrier SM.Carrier SM.Link Equiv

noncomputable section

/-! ## §R1. The record core: the two arcs of a self crossing and the first return along `s₁` -/

section R176S_Rec

variable (ρ : Record) (h1 : ρ.componentCount = 1) (x : ρ.M)

/-- the open arc from `x` forward to `τ x` (the word `A` of `(x A y B)`) -/
def r176s_ArcA (v : ρ.M) : Prop := ρ.ArcBetween x v (ρ.pair x)

theorem r176s_arcA_iff (v : ρ.M) :
    r176s_ArcA ρ x v ↔ 0 < ρ.steps x v ∧ ρ.steps x v < ρ.steps x (ρ.pair x) := Iff.rfl

include h1 in
theorem r176s_steps_pair_pos : 0 < ρ.steps x (ρ.pair x) :=
  (ρ.steps_pos_iff h1 x (ρ.pair x)).mpr (ρ.ne_pair x)

theorem r176s_arcA_ne_self {v : ρ.M} (hv : r176s_ArcA ρ x v) : v ≠ x := by
  intro h; subst h
  have h0 := hv.1
  rw [ρ.steps_self] at h0
  exact lt_irrefl 0 h0

theorem r176s_arcA_ne_pair {v : ρ.M} (hv : r176s_ArcA ρ x v) : v ≠ ρ.pair x := by
  intro h; subst h; exact lt_irrefl _ hv.2

theorem r176s_arcA_smoothKeep {v : ρ.M} (hv : r176s_ArcA ρ x v) : ρ.SmoothKeep x v :=
  (ρ.smoothKeep_iff x v).mpr ⟨r176s_arcA_ne_self ρ x hv, r176s_arcA_ne_pair ρ x hv⟩

include h1 in
/-- powers of the successor from `x`, identified by their position -/
theorem r176s_pow_x_eq_iff (n k : ℕ) (hk : k < Fintype.card ρ.M) :
    (ρ.succ ^ n) x = (ρ.succ ^ k) x ↔ n % Fintype.card ρ.M = k := by
  constructor
  · intro h
    have h2 := ρ.steps_pow h1 x n
    rw [h, ρ.steps_pow h1 x k, Nat.mod_eq_of_lt hk] at h2
    exact h2.symm
  · intro h
    rw [← ρ.pow_mod_card_apply h1 x n, h]

include h1 in
theorem r176s_pow_x_ne_self (n : ℕ) (h0 : n % Fintype.card ρ.M ≠ 0) : (ρ.succ ^ n) x ≠ x := by
  intro h
  apply h0
  have := (r176s_pow_x_eq_iff ρ h1 x n 0 (ρ.card_M_pos x)).mp (by simpa using h)
  exact this

include h1 in
theorem r176s_pow_x_ne_pair (n : ℕ) (hm : n % Fintype.card ρ.M ≠ ρ.steps x (ρ.pair x)) :
    (ρ.succ ^ n) x ≠ ρ.pair x := by
  intro h
  apply hm
  exact (r176s_pow_x_eq_iff ρ h1 x n _ (ρ.steps_lt_card h1 x _)).mp (by rw [h, ρ.pow_steps h1])

include h1 in
/-- the reconnected walk from `succ x` follows `succ` while it stays on the arc `A` -/
theorem r176s_reconnect_pow_succ_x (i : ℕ) (hi : i < ρ.steps x (ρ.pair x)) :
    ((ρ.reconnect x) ^ i) (ρ.succ x) = (ρ.succ ^ (i + 1)) x := by
  have hm := ρ.steps_lt_card h1 x (ρ.pair x)
  show ((ρ.succ * swap x (ρ.pair x)) ^ i) (ρ.succ x) = _
  rw [mul_swap_pow_apply_of_forall_ne ρ.succ x (ρ.pair x) (ρ.succ x) i ?_, pow_succ, Perm.mul_apply]
  intro j hj
  have hj' : (j + 1) % Fintype.card ρ.M = j + 1 := Nat.mod_eq_of_lt (by omega)
  have e : (ρ.succ ^ j) (ρ.succ x) = (ρ.succ ^ (j + 1)) x := by rw [pow_succ, Perm.mul_apply]
  rw [e]
  exact ⟨r176s_pow_x_ne_self ρ h1 x _ (by omega), r176s_pow_x_ne_pair ρ h1 x _ (by omega)⟩

include h1 in
/-- **the `s₁`-cycle of `τ x` is `(τ x, A)`**: every occurrence of the open arc `A` lies on it -/
theorem r176s_reconnect_sameCycle_pair {v : ρ.M} (hv : r176s_ArcA ρ x v) :
    (ρ.reconnect x).SameCycle (ρ.pair x) v := by
  refine ⟨ρ.steps x v, ?_⟩
  rw [zpow_natCast]
  obtain ⟨k, hk⟩ : ∃ k, ρ.steps x v = k + 1 := ⟨ρ.steps x v - 1, by have := hv.1; omega⟩
  rw [hk, pow_succ, Perm.mul_apply, Record.reconnect_apply_pair,
    r176s_reconnect_pow_succ_x ρ h1 x k (by have := hv.2; omega), ← hk, ρ.pow_steps h1]

theorem r176s_pair_arcA_iff (v : ρ.M) :
    r176s_ArcA ρ (ρ.pair x) v ↔ ρ.ArcBetween (ρ.pair x) v x := by
  unfold r176s_ArcA; rw [ρ.pair_invol]

include h1 in
/-- the `s₁`-cycle of `x` is `(x, B)` -/
theorem r176s_reconnect_sameCycle_self {v : ρ.M} (hv : ρ.ArcBetween (ρ.pair x) v x) :
    (ρ.reconnect x).SameCycle x v := by
  have h := r176s_reconnect_sameCycle_pair ρ h1 (ρ.pair x) ((r176s_pair_arcA_iff ρ x v).mpr hv)
  rw [ρ.reconnect_pair, ρ.pair_invol] at h
  exact h

include h1 in
/-- every retained occurrence lies on `A` or on `B` -/
theorem r176s_arc_dichotomy {v : ρ.M} (hv : ρ.SmoothKeep x v) :
    r176s_ArcA ρ x v ∨ ρ.ArcBetween (ρ.pair x) v x := by
  obtain ⟨h1', h2'⟩ := (ρ.smoothKeep_iff x v).mp hv
  rcases ρ.arcBetween_or_arcBetween h1 (Ne.symm h1') (ρ.ne_pair x) h2' with h | h
  · exact Or.inl h
  · exact Or.inr ((ρ.arcBetween_rotate h1 x (ρ.pair x) v).mp h)

include h1 in
theorem r176s_isSelfCrossing : ρ.IsSelfCrossing x :=
  Fintype.card_le_one_iff.mp (le_of_eq h1) _ _

include h1 in
/-- **the component of a retained occurrence of the smoothing is the class of `τ x` iff it lies on `A`** -/
theorem r176s_smooth_comp_eq_pair_iff (w : (ρ.smooth x).M) :
    (ρ.smooth x).comp w = Sum.inl (Quotient.mk _ (ρ.pair x)) ↔ r176s_ArcA ρ x w.1 := by
  rw [Record.smooth_comp]
  constructor
  · intro h
    have hsc : (ρ.reconnect x).SameCycle w.1 (ρ.pair x) := Quotient.exact (Sum.inl.inj h)
    rcases r176s_arc_dichotomy ρ h1 x w.2 with hA | hB
    · exact hA
    · exfalso
      exact ρ.not_reconnect_sameCycle_pair_of_self x (r176s_isSelfCrossing ρ h1 x)
        ((r176s_reconnect_sameCycle_self ρ h1 x hB).trans hsc)
  · intro hA
    exact congrArg Sum.inl (Quotient.sound (r176s_reconnect_sameCycle_pair ρ h1 x hA).symm)

include h1 in
theorem r176s_smooth_comp_eq_self_iff (w : (ρ.smooth x).M) :
    (ρ.smooth x).comp w = Sum.inl (Quotient.mk _ x) ↔ ρ.ArcBetween (ρ.pair x) w.1 x := by
  rw [Record.smooth_comp]
  constructor
  · intro h
    have hsc : (ρ.reconnect x).SameCycle w.1 x := Quotient.exact (Sum.inl.inj h)
    rcases r176s_arc_dichotomy ρ h1 x w.2 with hA | hB
    · exfalso
      exact ρ.not_reconnect_sameCycle_pair_of_self x (r176s_isSelfCrossing ρ h1 x)
        (hsc.symm.trans (r176s_reconnect_sameCycle_pair ρ h1 x hA).symm)
    · exact hB
  · intro hB
    exact congrArg Sum.inl (Quotient.sound (r176s_reconnect_sameCycle_self ρ h1 x hB).symm)


include h1 in
/-- the reconnected walk from a point of `A` follows `succ` while it stays on `A` -/
theorem r176s_reconnect_pow_of_arcA {u : ρ.M} (hu : r176s_ArcA ρ x u) (j : ℕ)
    (hj : ρ.steps x u + j ≤ ρ.steps x (ρ.pair x)) :
    ((ρ.reconnect x) ^ j) u = (ρ.succ ^ j) u := by
  show ((ρ.succ * swap x (ρ.pair x)) ^ j) u = _
  apply mul_swap_pow_apply_of_forall_ne
  intro j' hj'
  have hm := ρ.steps_lt_card h1 x (ρ.pair x)
  have hu' : (ρ.succ ^ j') u = (ρ.succ ^ (ρ.steps x u + j')) x := by
    rw [add_comm, pow_add, Perm.mul_apply, ρ.pow_steps h1]
  rw [hu']
  have hlt : ρ.steps x u + j' < Fintype.card ρ.M := by omega
  have hmod : (ρ.steps x u + j') % Fintype.card ρ.M = ρ.steps x u + j' := Nat.mod_eq_of_lt hlt
  obtain ⟨hu0, hum⟩ := hu
  exact ⟨r176s_pow_x_ne_self ρ h1 x _ (by rw [hmod]; omega),
    r176s_pow_x_ne_pair ρ h1 x _ (by rw [hmod]; omega)⟩

include h1 in
/-- **the first return to a set of occurrences on the arc `A` is the same along `s₁` and along `s`**:
the reconnected walk skips exactly `τ x, B, x`, which carry no point of the set. -/
theorem r176s_firstReturn_reconnect (p : ρ.M → Prop) [DecidablePred p]
    (hp : ∀ v, p v → r176s_ArcA ρ x v) (u : {v // p v}) :
    (firstReturn (ρ.reconnect x) p u).1 = (firstReturn ρ.succ p u).1 := by
  have hu := hp u.1 u.2
  have ha0 : 0 < ρ.steps x u.1 := hu.1
  have ham : ρ.steps x u.1 < ρ.steps x (ρ.pair x) := hu.2
  have hmN : ρ.steps x (ρ.pair x) < Fintype.card ρ.M := ρ.steps_lt_card h1 x _
  have hux : (ρ.succ ^ ρ.steps x u.1) x = u.1 := ρ.pow_steps h1 x u.1
  have hiter : ∀ j, (ρ.succ ^ j) u.1 = (ρ.succ ^ (ρ.steps x u.1 + j)) x := by
    intro j; rw [add_comm, pow_add, Perm.mul_apply, hux]
  have hr0 : 0 < returnTime ρ.succ p u.1 u.2 := returnTime_pos _ _ _ _
  have hrp : p ((ρ.succ ^ returnTime ρ.succ p u.1 u.2) u.1) := returnTime_spec _ _ _ _
  have hrmin : ∀ j, 0 < j → j < returnTime ρ.succ p u.1 u.2 → ¬ p ((ρ.succ ^ j) u.1) :=
    fun j hj0 hj => returnTime_min _ _ _ _ hj0 hj
  have hrN : returnTime ρ.succ p u.1 u.2 ≤ Fintype.card ρ.M := by
    by_contra h
    exact hrmin _ (ρ.card_M_pos u.1) (by omega) (by rw [ρ.pow_card_apply h1]; exact u.2)
  have hposp : ∀ j, p ((ρ.succ ^ j) u.1) →
      0 < (ρ.steps x u.1 + j) % Fintype.card ρ.M ∧
        (ρ.steps x u.1 + j) % Fintype.card ρ.M < ρ.steps x (ρ.pair x) := by
    intro j hj
    have := (r176s_arcA_iff ρ x _).mp (hp _ hj)
    rw [hiter, ρ.steps_pow h1] at this
    exact this
  rcases Nat.lt_or_ge (returnTime ρ.succ p u.1 u.2) (ρ.steps x (ρ.pair x) - ρ.steps x u.1) with hcase | hcase
  · -- (i) the first return happens before `τ x`: the two walks agree
    show (firstReturn (ρ.succ * swap x (ρ.pair x)) p u).1 = _
    apply Record.firstReturn_mul_swap_apply_of_avoid
    intro j hj
    rw [hiter]
    have hlt : ρ.steps x u.1 + j < Fintype.card ρ.M := by omega
    have hmod : (ρ.steps x u.1 + j) % Fintype.card ρ.M = ρ.steps x u.1 + j := Nat.mod_eq_of_lt hlt
    exact ⟨r176s_pow_x_ne_self ρ h1 x _ (by rw [hmod]; omega),
      r176s_pow_x_ne_pair ρ h1 x _ (by rw [hmod]; omega)⟩
  · -- (ii) the walk passes `τ x`, `B` and `x`; the first `p`-point sits at position `a + r − N` on `A`
    have hrgt : Fintype.card ρ.M - ρ.steps x u.1 < returnTime ρ.succ p u.1 u.2 := by
      by_contra hle
      have hle' : ρ.steps x u.1 + returnTime ρ.succ p u.1 u.2 ≤ Fintype.card ρ.M := by omega
      have := hposp _ hrp
      rcases lt_or_eq_of_le hle' with hlt | heq
      · rw [Nat.mod_eq_of_lt hlt] at this; omega
      · rw [heq, Nat.mod_self] at this; omega
    have hposw := hposp _ hrp
    have hmodr : (ρ.steps x u.1 + returnTime ρ.succ p u.1 u.2) % Fintype.card ρ.M =
        ρ.steps x u.1 + returnTime ρ.succ p u.1 u.2 - Fintype.card ρ.M := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    rw [hmodr] at hposw
    have hstep1 : ((ρ.reconnect x) ^ (ρ.steps x (ρ.pair x) - ρ.steps x u.1)) u.1 = ρ.pair x := by
      rw [r176s_reconnect_pow_of_arcA ρ h1 x hu _ (by omega), hiter,
        show ρ.steps x u.1 + (ρ.steps x (ρ.pair x) - ρ.steps x u.1) = ρ.steps x (ρ.pair x) by omega,
        ρ.pow_steps h1]
    have hstep2 : ∀ i, i < ρ.steps x (ρ.pair x) →
        ((ρ.reconnect x) ^ (ρ.steps x (ρ.pair x) - ρ.steps x u.1 + 1 + i)) u.1 = (ρ.succ ^ (i + 1)) x := by
      intro i hi
      rw [show ρ.steps x (ρ.pair x) - ρ.steps x u.1 + 1 + i = i + (ρ.steps x (ρ.pair x) - ρ.steps x u.1 + 1)
          by omega, pow_add, Perm.mul_apply, pow_succ', Perm.mul_apply, hstep1,
        Record.reconnect_apply_pair, r176s_reconnect_pow_succ_x ρ h1 x i hi]
    have hw : (ρ.succ ^ returnTime ρ.succ p u.1 u.2) u.1 =
        (ρ.succ ^ (ρ.steps x u.1 + returnTime ρ.succ p u.1 u.2 - Fintype.card ρ.M)) x := by
      rw [hiter, ← ρ.pow_mod_card_apply h1 x (ρ.steps x u.1 + returnTime ρ.succ p u.1 u.2), hmodr]
    have key : ((ρ.reconnect x) ^ (ρ.steps x (ρ.pair x) - ρ.steps x u.1 + 1 +
        (ρ.steps x u.1 + returnTime ρ.succ p u.1 u.2 - Fintype.card ρ.M - 1))) u.1 =
        (ρ.succ ^ returnTime ρ.succ p u.1 u.2) u.1 := by
      rw [hstep2 _ (by omega), show ρ.steps x u.1 + returnTime ρ.succ p u.1 u.2 - Fintype.card ρ.M - 1 + 1 =
        ρ.steps x u.1 + returnTime ρ.succ p u.1 u.2 - Fintype.card ρ.M by omega, hw]
    rw [firstReturn_apply ρ.succ p u, ← key]
    apply firstReturn_val_eq_of_pow (ρ.reconnect x) p u (by omega)
    · rw [key]; exact hrp
    · intro j hj0 hjn
      by_cases hj : j ≤ ρ.steps x (ρ.pair x) - ρ.steps x u.1
      · rw [r176s_reconnect_pow_of_arcA ρ h1 x hu j (by omega)]
        exact hrmin j hj0 (by omega)
      · obtain ⟨i, hi⟩ : ∃ i, j = ρ.steps x (ρ.pair x) - ρ.steps x u.1 + 1 + i :=
          ⟨j - (ρ.steps x (ρ.pair x) - ρ.steps x u.1 + 1), by omega⟩
        rw [hi, hstep2 i (by omega)]
        have e : (ρ.succ ^ (i + 1)) x = (ρ.succ ^ (Fintype.card ρ.M - ρ.steps x u.1 + i + 1)) u.1 := by
          rw [hiter, ← ρ.pow_mod_card_apply h1 x (ρ.steps x u.1 + (Fintype.card ρ.M - ρ.steps x u.1 + i + 1)),
            show ρ.steps x u.1 + (Fintype.card ρ.M - ρ.steps x u.1 + i + 1) = (i + 1) + Fintype.card ρ.M
              by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
        rw [e]
        exact hrmin _ (by omega) (by omega)

/-- the crossings both of whose occurrences lie on the arc `A` (the self crossings of the `A`-component) -/
def r176s_KA : Set ρ.Crossing := {c | ∀ v ∈ c.1, r176s_ArcA ρ x v}

theorem r176s_crossKeep_KA_iff (v : ρ.M) :
    ρ.CrossKeep (r176s_KA ρ x) v ↔ r176s_ArcA ρ x v ∧ r176s_ArcA ρ x (ρ.pair v) := by
  show (∀ w ∈ ({v, ρ.pair v} : Finset ρ.M), r176s_ArcA ρ x w) ↔ _
  simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq]

/-- the `A`-component of the smoothing, as a block -/
def r176s_smoothB : Finset (ρ.smooth x).comps := {Sum.inl (Quotient.mk _ (ρ.pair x))}

theorem r176s_mem_smoothB (c : (ρ.smooth x).comps) :
    c ∈ r176s_smoothB ρ x ↔ c = Sum.inl (Quotient.mk _ (ρ.pair x)) := Finset.mem_singleton

include h1 in
theorem r176s_restrictKeep_iff (w : (ρ.smooth x).M) :
    (ρ.smooth x).RestrictKeep (r176s_smoothB ρ x) w ↔
      r176s_ArcA ρ x w.1 ∧ r176s_ArcA ρ x (ρ.pair w.1) := by
  show ((ρ.smooth x).comp w ∈ r176s_smoothB ρ x ∧ (ρ.smooth x).comp ((ρ.smooth x).pair w) ∈ r176s_smoothB ρ x) ↔ _
  rw [r176s_mem_smoothB, r176s_mem_smoothB, r176s_smooth_comp_eq_pair_iff ρ h1 x,
    r176s_smooth_comp_eq_pair_iff ρ h1 x]
  rfl

/-- the occurrence bijection: the identity on the underlying occurrences -/
def r176s_ΦA : {w : (ρ.smooth x).M // (ρ.smooth x).RestrictKeep (r176s_smoothB ρ x) w} ≃
    {v : ρ.M // ρ.CrossKeep (r176s_KA ρ x) v} where
  toFun w := ⟨w.1.1, (r176s_crossKeep_KA_iff ρ x _).mpr ((r176s_restrictKeep_iff ρ h1 x w.1).mp w.2)⟩
  invFun v := ⟨⟨v.1, r176s_arcA_smoothKeep ρ x ((r176s_crossKeep_KA_iff ρ x _).mp v.2).1⟩,
    (r176s_restrictKeep_iff ρ h1 x _).mpr ((r176s_crossKeep_KA_iff ρ x _).mp v.2)⟩
  left_inv _ := rfl
  right_inv _ := rfl

open scoped Classical in
/-- the successor clause -/
theorem r176s_ΦA_succ (w : {w : (ρ.smooth x).M // (ρ.smooth x).RestrictKeep (r176s_smoothB ρ x) w}) :
    r176s_ΦA ρ h1 x (((ρ.smooth x).restrict (r176s_smoothB ρ x)).succ w) =
      (ρ.restrictCrossings (r176s_KA ρ x)).succ (r176s_ΦA ρ h1 x w) := by
  apply Subtype.ext
  have hq : ∀ m : (ρ.smooth x).M, (ρ.smooth x).RestrictKeep (r176s_smoothB ρ x) m ↔
      (fun v : ρ.M => r176s_ArcA ρ x v ∧ r176s_ArcA ρ x (ρ.pair v)) m.1 :=
    fun m => r176s_restrictKeep_iff ρ h1 x m
  have e1 := firstReturn_congr_pred ((ρ.smooth x).succ) _ _ hq w
  have e2 := firstReturn_firstReturn (ρ.reconnect x) (ρ.SmoothKeep x)
    (fun v : ρ.M => r176s_ArcA ρ x v ∧ r176s_ArcA ρ x (ρ.pair v)) ⟨w.1, (hq w.1).mp w.2⟩
  have hq2 : ∀ v : ρ.M, (ρ.SmoothKeep x v ∧ (r176s_ArcA ρ x v ∧ r176s_ArcA ρ x (ρ.pair v))) ↔
      ρ.CrossKeep (r176s_KA ρ x) v := by
    intro v
    rw [r176s_crossKeep_KA_iff]
    exact ⟨fun h => h.2, fun h => ⟨r176s_arcA_smoothKeep ρ x h.1, h⟩⟩
  have e3 := firstReturn_congr_pred (ρ.reconnect x) _ _ hq2
    ⟨w.1.1, ⟨r176s_arcA_smoothKeep ρ x ((hq w.1).mp w.2).1, (hq w.1).mp w.2⟩⟩
  have e4 := r176s_firstReturn_reconnect ρ h1 x (ρ.CrossKeep (r176s_KA ρ x))
    (fun v hv => ((r176s_crossKeep_KA_iff ρ x v).mp hv).1) ⟨w.1.1, (r176s_ΦA ρ h1 x w).2⟩
  show ((firstReturn (ρ.smooth x).succ ((ρ.smooth x).RestrictKeep (r176s_smoothB ρ x)) w).1).1 =
    (firstReturn ρ.succ (ρ.CrossKeep (r176s_KA ρ x)) (r176s_ΦA ρ h1 x w)).1
  exact (congrArg Subtype.val e1).trans (e2.trans (e3.trans e4))

include h1 in
theorem r176s_card_comps_one : Fintype.card ρ.comps = 1 := h1

include h1 in
/-- **the `A`-component of the smoothing is the restriction of `ρ` to the crossings of `A`** (the
"(y A)" cycle of sm-3:1093-1096, read as a one-circle record) -/
def r176s_smoothRestrictIso :
    RecordIso ((ρ.smooth x).restrict (r176s_smoothB ρ x)) (ρ.restrictCrossings (r176s_KA ρ x)) where
  e := (Fintype.equivFinOfCardEq (by
      show Fintype.card {c : (ρ.smooth x).comps // c ∈ r176s_smoothB ρ x} = 1
      rw [Fintype.card_coe]
      exact Finset.card_singleton _)).trans
    (Fintype.equivFinOfCardEq (r176s_card_comps_one ρ h1)).symm
  Φ := r176s_ΦA ρ h1 x
  comp_eq _ := Fintype.card_le_one_iff.mp (le_of_eq h1) _ _
  succ_eq := r176s_ΦA_succ ρ h1 x
  pair_eq _ := rfl
  bit_eq _ := rfl
  sgn_eq _ := rfl

/-- the `B`-component of the smoothing, as a block -/
def r176s_smoothB' : Finset (ρ.smooth x).comps := {Sum.inl (Quotient.mk _ x)}

/-- the crossings both of whose occurrences lie on the arc `B` (from `τ x` forward to `x`) -/
def r176s_KB : Set ρ.Crossing := r176s_KA ρ (ρ.pair x)

theorem r176s_crossKeep_KB_iff (v : ρ.M) :
    ρ.CrossKeep (r176s_KB ρ x) v ↔ ρ.ArcBetween (ρ.pair x) v x ∧ ρ.ArcBetween (ρ.pair x) (ρ.pair v) x := by
  unfold r176s_KB
  rw [r176s_crossKeep_KA_iff, r176s_pair_arcA_iff, r176s_pair_arcA_iff]

theorem r176s_mem_smoothB' (c : (ρ.smooth x).comps) :
    c ∈ r176s_smoothB' ρ x ↔ c = Sum.inl (Quotient.mk _ x) := Finset.mem_singleton

theorem r176s_smoothPairIso_e (c : (ρ.smooth (ρ.pair x)).comps) :
    (ρ.smoothPairIso x).e c ∈ r176s_smoothB' ρ x ↔ c ∈ r176s_smoothB ρ (ρ.pair x) := by
  rw [r176s_mem_smoothB', r176s_mem_smoothB, ρ.pair_invol]
  have he : (ρ.smoothPairIso x).e (Sum.inl (Quotient.mk _ x) : (ρ.smooth (ρ.pair x)).comps) =
      Sum.inl (Quotient.mk _ x) := rfl
  constructor
  · intro h; exact (ρ.smoothPairIso x).e.injective (h.trans he.symm)
  · intro h; rw [h]; exact he

include h1 in
/-- **the `B`-component of the smoothing is the restriction of `ρ` to the crossings of `B`** -/
def r176s_smoothRestrictIso' :
    RecordIso ((ρ.smooth x).restrict (r176s_smoothB' ρ x)) (ρ.restrictCrossings (r176s_KB ρ x)) :=
  ((ρ.smoothPairIso x).restrict _ _ (r176s_smoothPairIso_e ρ x)).symm.trans
    (r176s_smoothRestrictIso ρ h1 (ρ.pair x))

end R176S_Rec

/-! ## §R2. The oriented smoothing `D_A` of a one-component diagram and its knot restrictions -/

section R176S_Knot

variable (D : Diagram) (x : D.Γ.Crossing)

/-- the library oriented smoothing of `D` at `x`, at its canonical cut parameter -/
def r176s_DA : Diagram := Smoothing.smoothDiagram D x (Smoothing.eps D x) (Smoothing.eps_small D x)

theorem r176s_DA_smooth : IsOrientedSmoothing D x (r176s_DA D x) :=
  Smoothing.isOrientedSmoothing_smoothDiagram D x _ (Smoothing.eps_small D x)

theorem r176s_DA_record_nonempty :
    Nonempty (RecordIso (r176s_DA D x).record (D.record.smooth (D.overVisit x))) :=
  Smoothing.smoothDiagram_record D x _ (Smoothing.eps_small D x)

/-- the record identification for any occurrence `v` of `x` -/
theorem r176s_DA_record_visit (v : D.Γ.Visit) (hv : v.1 = x) :
    Nonempty (RecordIso (r176s_DA D x).record (D.record.smooth v)) := by
  obtain ⟨ι⟩ := r176s_DA_record_nonempty D x
  have h := D.visit_eq_over_or_under v
  rw [hv] at h
  rcases h with rfl | rfl
  · exact ⟨ι⟩
  · exact ⟨ι.trans (D.record.smoothPairIso (D.overVisit x)).symm⟩

/-- on a one-component diagram every occurrence is a self crossing occurrence -/
theorem r176s_isSelfCrossing_of_one (hD : D.componentCount = 1) (v : D.Γ.Visit) :
    D.record.IsSelfCrossing v := by
  show D.compOf v = D.compOf (D.twin v)
  apply Fin.ext
  have hc : D.Γ.c = 1 := hD
  have h1 := (D.compOf v).isLt
  have h2 := (D.compOf (D.twin v)).isLt
  omega

theorem r176s_record_componentCount_one (hD : D.componentCount = 1) : D.record.componentCount = 1 := by
  rw [Diagram.record_componentCount, hD]

/-- "Smoothing `q` splits `D_+` into two components" -/
theorem r176s_DA_componentCount (hD : D.componentCount = 1) : (r176s_DA D x).componentCount = 2 := by
  obtain ⟨ι⟩ := r176s_DA_record_nonempty D x
  rw [← Diagram.record_componentCount, ι.componentCount_eq,
    Record.componentCount_smooth_of_self _ _ (r176s_isSelfCrossing_of_one D hD _),
    Diagram.record_componentCount, hD]

/-- the record identification, chosen -/
def r176s_DA_iso (v : D.Γ.Visit) (hv : v.1 = x) : RecordIso (r176s_DA D x).record (D.record.smooth v) :=
  Classical.choice (r176s_DA_record_visit D x v hv)

/-- the component of the arc `B = τv → v` (the reconnect class of `v`) -/
def r176s_DA_i (v : D.Γ.Visit) (hv : v.1 = x) : Fin (r176s_DA D x).Γ.c :=
  (r176s_DA_iso D x v hv).e.symm (Sum.inl (Quotient.mk _ v))

/-- the component of the arc `A = v → τv` (the reconnect class of `τ v`) -/
def r176s_DA_j (v : D.Γ.Visit) (hv : v.1 = x) : Fin (r176s_DA D x).Γ.c :=
  (r176s_DA_iso D x v hv).e.symm (Sum.inl (Quotient.mk _ (D.record.pair v)))

theorem r176s_DA_ij (hD : D.componentCount = 1) (v : D.Γ.Visit) (hv : v.1 = x) :
    r176s_DA_i D x v hv ≠ r176s_DA_j D x v hv := by
  intro h
  have h' := (r176s_DA_iso D x v hv).e.symm.injective h
  exact D.record.smooth_comps_ne_of_self v (r176s_isSelfCrossing_of_one D hD v) h'

theorem r176s_DA_e_mem_i (v : D.Γ.Visit) (hv : v.1 = x) (c : (r176s_DA D x).record.comps) :
    (r176s_DA_iso D x v hv).e c ∈ r176s_smoothB' D.record v ↔ c ∈ ({r176s_DA_i D x v hv} : Finset _) := by
  rw [r176s_mem_smoothB', Finset.mem_singleton]
  exact (Equiv.eq_symm_apply _).symm

theorem r176s_DA_e_mem_j (v : D.Γ.Visit) (hv : v.1 = x) (c : (r176s_DA D x).record.comps) :
    (r176s_DA_iso D x v hv).e c ∈ r176s_smoothB D.record v ↔ c ∈ ({r176s_DA_j D x v hv} : Finset _) := by
  rw [r176s_mem_smoothB, Finset.mem_singleton]
  exact (Equiv.eq_symm_apply _).symm

/-- **the knot restriction of `DA` to the `A`-component is `D` restricted to the crossings of `A`** -/
def r176s_knotRestrictIso_j (hD : D.componentCount = 1) (v : D.Γ.Visit) (hv : v.1 = x) :
    RecordIso ((r176s_DA D x).knotRestrict (r176s_DA_j D x v hv)).record
      (D.record.restrictCrossings (r176s_KA D.record v)) :=
  ((r176s_DA D x).restrictRecordIso {r176s_DA_j D x v hv} (Finset.singleton_nonempty _)).trans
    (((r176s_DA_iso D x v hv).restrict _ _ (r176s_DA_e_mem_j D x v hv)).trans
      (r176s_smoothRestrictIso D.record (r176s_record_componentCount_one D hD) v))

/-- **the knot restriction of `DA` to the `B`-component is `D` restricted to the crossings of `B`** -/
def r176s_knotRestrictIso_i (hD : D.componentCount = 1) (v : D.Γ.Visit) (hv : v.1 = x) :
    RecordIso ((r176s_DA D x).knotRestrict (r176s_DA_i D x v hv)).record
      (D.record.restrictCrossings (r176s_KB D.record v)) :=
  ((r176s_DA D x).restrictRecordIso {r176s_DA_i D x v hv} (Finset.singleton_nonempty _)).trans
    (((r176s_DA_iso D x v hv).restrict _ _ (r176s_DA_e_mem_i D x v hv)).trans
      (r176s_smoothRestrictIso' D.record (r176s_record_componentCount_one D hD) v))

end R176S_Knot

/-! ## §R3. The exact owner map: `homfly` of a knot restriction from a record identification -/

section R176S_Poly

variable {n : ℕ} [NeZero n]

/-- `homfly X = P_{S_f, Λ}` for any diagram `X` record-isomorphic to the positive lift of `Λ`
(`presentations`, `P_eq_homfly`, `GT_groupedPoly_eq_homfly`). -/
theorem r176s_homfly_eq_groupedPoly (hn : 3 ≤ n) {P : LabelledTuple n} (hG : CV.Generic P)
    {Sf : Finset (Crossing P)} (hSf : Sf ∈ CV.Ind hG.crossingGeometry) (Λ : GeoComponent hG.crossingGeometry Sf)
    (X : Diagram) (h : Nonempty (RecordIso X.record (CV.carrierDiagram hn hG hSf Λ).record)) :
    homfly X = CV.groupedPoly hn hG hSf Λ := by
  rw [GT_groupedPoly_eq_homfly, ← P_eq_homfly, ← P_eq_homfly]
  exact presentations _ _ h

/-- **the exact owner map, clean component**: a diagram whose record is the record of the lift of `q`
restricted to the chords labelled by the retained crossings of an inner carrier `Λ` has the HOMFLY
polynomial of the lift of `Λ` (`CV.liftRestrictRecordIso`). -/
theorem r176s_homfly_of_liftBlock (hn : 3 ≤ n) {P : LabelledTuple n} (hG : CarrierGeometry P)
    {T T' : Finset (Crossing P)} (hT : GeoIndependent hG.cg T) (hT' : GeoIndependent hG.cg T')
    (q : GeoComponent hG.cg T) (Λ : GeoComponent hG.cg T')
    (hsub : geoCarrierCrossings hG.cg T' Λ ⊆ geoCarrierCrossings hG.cg T q)
    (X : Diagram) (K : Set (geoPositiveLift hn hG hT q).record.Crossing)
    (hK : K = CV.liftBlock hn hG hT q (geoCarrierCrossings hG.cg T' Λ))
    (hX : Nonempty (RecordIso X.record ((geoPositiveLift hn hG hT q).record.restrictCrossings K))) :
    homfly X = homfly (geoPositiveLift hn hG hT' Λ) := by
  subst hK
  obtain ⟨ι⟩ := hX
  rw [← P_eq_homfly, ← P_eq_homfly]
  exact presentations _ _ ⟨ι.trans (CV.liftRestrictRecordIso hn hG hT hT' q Λ hsub).symm⟩

/-- **Record-level R-I — BLACK BOX (stated, not proved here)**: on a one-circle record `ρ`, if the two
occurrences of a retained crossing `r ∈ K` are consecutive in the restricted record `ρ|K` (the kink), then
any actual diagram with record `ρ|K` and any actual diagram with record `ρ|(K ∖ {r})` have the same HOMFLY
polynomial (lc:single-crossing / mp:blocks: the kink is a block of value one; or an R-I move +
rp:record-polynomial). -/
def r176s_curl_removal : Prop :=
  ∀ (ρ : Record), ρ.componentCount = 1 → ∀ (K : Set ρ.Crossing) (r : ρ.Crossing), r ∈ K →
    (∃ (w : ρ.M) (hw : ρ.CrossKeep K w), ρ.crossingOf w = r ∧
      ((ρ.restrictCrossings K).succ ⟨w, hw⟩).1 = ρ.pair w) →
    ∀ (X X' : Diagram), Nonempty (RecordIso X.record (ρ.restrictCrossings K)) →
      Nonempty (RecordIso X'.record (ρ.restrictCrossings (K \ {r}))) → homfly X = homfly X'

/-- **the exact owner map, kinked component**: a diagram whose record is `ρ|K` with `K` = the chords of an
inner carrier `Λ` plus one kink `r` has the HOMFLY polynomial of the lift of `Λ` (through the black box
`r176s_curl_removal`). -/
theorem r176s_homfly_of_liftBlock_curl (hcurl : r176s_curl_removal) (hn : 3 ≤ n) {P : LabelledTuple n}
    (hG : CarrierGeometry P) {T T' : Finset (Crossing P)} (hT : GeoIndependent hG.cg T)
    (hT' : GeoIndependent hG.cg T') (q : GeoComponent hG.cg T) (Λ : GeoComponent hG.cg T')
    (hsub : geoCarrierCrossings hG.cg T' Λ ⊆ geoCarrierCrossings hG.cg T q)
    (X : Diagram) (K : Set (geoPositiveLift hn hG hT q).record.Crossing)
    (r : (geoPositiveLift hn hG hT q).record.Crossing)
    (hK : K = CV.liftBlock hn hG hT q (geoCarrierCrossings hG.cg T' Λ) ∪ {r})
    (hr : r ∉ CV.liftBlock hn hG hT q (geoCarrierCrossings hG.cg T' Λ))
    (hcurlK : ∃ (w : (geoPositiveLift hn hG hT q).record.M)
      (hw : (geoPositiveLift hn hG hT q).record.CrossKeep K w),
      (geoPositiveLift hn hG hT q).record.crossingOf w = r ∧
      (((geoPositiveLift hn hG hT q).record.restrictCrossings K).succ ⟨w, hw⟩).1 =
        (geoPositiveLift hn hG hT q).record.pair w)
    (hX : Nonempty (RecordIso X.record ((geoPositiveLift hn hG hT q).record.restrictCrossings K))) :
    homfly X = homfly (geoPositiveLift hn hG hT' Λ) := by
  have hrK : r ∈ K := by rw [hK]; exact Set.mem_union_right _ (Set.mem_singleton r)
  have hKr : K \ {r} = CV.liftBlock hn hG hT q (geoCarrierCrossings hG.cg T' Λ) := by
    rw [hK, Set.union_singleton, Set.insert_sdiff_of_mem _ (Set.mem_singleton r),
      Set.sdiff_singleton_eq_self hr]
  have h1 : (geoPositiveLift hn hG hT q).record.componentCount = 1 :=
    r176s_record_componentCount_one _ (geoPositiveLift_componentCount hn hG hT q)
  refine hcurl _ h1 K r hrK hcurlK X _ hX ⟨?_⟩
  rw [hKr]
  exact CV.liftRestrictRecordIso hn hG hT hT' q Λ hsub

end R176S_Poly

/-! ### the arcs of a lift, read on the parent visits (for the geometric identification of `r176s_OuterData`) -/

section R176S_Key

variable {n : ℕ} [NeZero n] (hn : 3 ≤ n) {P : LabelledTuple n} (hG : CarrierGeometry P)
  {T : Finset (Crossing P)} (hT : GeoIndependent hG.cg T) (q : GeoComponent hG.cg T)

/-- an occurrence of the lift lies on the arc `A = (x → τ x)` iff its parent visit lies, in the traversal
order of the parent polygon, strictly between the parent visits of `x` and of its twin (`CV.arcBetween_iff_key`,
lem:carrierword: the cyclic order of a carrier's retained visits is the parent's) -/
theorem r176s_arcA_iff_key (x v : (geoPositiveLift hn hG hT q).Γ.Visit) :
    r176s_ArcA (geoPositiveLift hn hG hT q).record x v ↔
      cycBetween (geometricVisitKey hG.cg (CV.liftVisit hn hG hT q x))
        (geometricVisitKey hG.cg (CV.liftVisit hn hG hT q v))
        (geometricVisitKey hG.cg (visitTwin (CV.liftVisit hn hG hT q x))) := by
  unfold r176s_ArcA
  rw [CV.arcBetween_iff_key]
  show cycBetween _ _ (geometricVisitKey hG.cg (CV.liftVisit hn hG hT q ((geoPositiveLift hn hG hT q).twin x))) ↔ _
  rw [CV.liftVisit_twin]

/-- the crossings of the arc `A`, read on the parent: both visits of the parent crossing lie strictly between
the parent visits of `x` and of its twin -/
theorem r176s_crossKeep_KA_iff_key (x v : (geoPositiveLift hn hG hT q).Γ.Visit) :
    (geoPositiveLift hn hG hT q).record.CrossKeep (r176s_KA (geoPositiveLift hn hG hT q).record x) v ↔
      cycBetween (geometricVisitKey hG.cg (CV.liftVisit hn hG hT q x))
          (geometricVisitKey hG.cg (CV.liftVisit hn hG hT q v))
          (geometricVisitKey hG.cg (visitTwin (CV.liftVisit hn hG hT q x))) ∧
        cycBetween (geometricVisitKey hG.cg (CV.liftVisit hn hG hT q x))
          (geometricVisitKey hG.cg (visitTwin (CV.liftVisit hn hG hT q v)))
          (geometricVisitKey hG.cg (visitTwin (CV.liftVisit hn hG hT q x))) := by
  rw [r176s_crossKeep_KA_iff, r176s_arcA_iff_key, r176s_arcA_iff_key]
  show _ ∧ cycBetween _ (geometricVisitKey hG.cg (CV.liftVisit hn hG hT q ((geoPositiveLift hn hG hT q).twin v))) _ ↔ _
  rw [CV.liftVisit_twin]

end R176S_Key

/-! ## §R4. `S_full = Q' ∪ {j', u', v'}` is independent on the empty side -/

section R176S_SfullVars

variable {n : ℕ} [NeZero n]

section R176S_Sfull

variable {E : CV.Event n} {e f g : ZMod n} {δ : ℝ}

/-- **On the empty side no two triangle crossings interlace** (`complement_on_triangle` against `K3` on
`H`): every set of triangle crossings, transported to `L`, is independent. -/
theorem r176s_triangle_ind_L (hL : LocalizationData E e f g δ) {t t' : E.Parameter} (ht : Punctured E δ t)
    (ht' : Punctured E δ t') (hop : OppositeSides E t t')
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    {hef' : IsCrossing (E.curve t) {e, f}} {heg' : IsCrossing (E.curve t) {e, g}}
    {hfg' : IsCrossing (E.curve t) {f, g}} (hcomp : CompleteLocal (geomAt E t ht.1) hef' heg' hfg')
    {J : Finset (Crossing (E.curve t))} (hJ : ∀ c ∈ J, c.val ∈ triangleSupports e f g) :
    transportSupport hs J ∈ CV.Ind (geomAt E t' ht'.1) := by
  rw [CV.mem_Ind_iff]
  intro x' hx' y' hy' hxy
  obtain ⟨x, rfl⟩ := (crossingTransport hs).surjective x'
  obtain ⟨y, rfl⟩ := (crossingTransport hs).surjective y'
  rw [mem_transportSupport_iff] at hx' hy'
  have hxy' : x ≠ y := fun h => hxy (by rw [h])
  rw [hL.complement_on_triangle t t' ht ht' hop hs x y (hJ x hx') (hJ y hy') hxy']
  intro hn'
  exact hn' (est_interlaces_of_complete ht.1 hcomp (hJ x hx') (hJ y hy') hxy')

/-- `S_full = Q' ∪ {j', u', v'}` as the transport of `Q ∪ {j, u, v}`. -/
theorem r176s_Sfull_eq {t t' : E.Parameter} (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    (Q : Finset (Crossing (E.curve t))) (j u v : Crossing (E.curve t)) :
    transportSupport hs (Q ∪ {j, u, v}) =
      transportSupport hs Q ∪ {crossingTransport hs j, crossingTransport hs u, crossingTransport hs v} := by
  rw [AV_transportSupport_union]
  congr 1
  unfold transportSupport
  rw [Finset.map_insert, Finset.map_insert, Finset.map_singleton]
  rfl

/-- **`S_full = Q' ∪ {j', u', v'}` is an independent `L`-side support** (U_R176_REPORT §5 item 3: full
availability of `Q'` and the empty local graph; the `est_S'_ind` pattern with the whole triangle selected). -/
theorem r176s_Sfull_ind (hL : LocalizationData E e f g δ) {t t' : E.Parameter} (ht : Punctured E δ t)
    (ht' : Punctured E δ t') (hop : OppositeSides E t t')
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    {hef' : IsCrossing (E.curve t) {e, f}} {heg' : IsCrossing (E.curve t) {e, g}}
    {hfg' : IsCrossing (E.curve t) {f, g}} (hcomp : CompleteLocal (geomAt E t ht.1) hef' heg' hfg')
    {Q : Finset (Crossing (E.curve t))} (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
    (hfull : FullAvail (geomAt E t ht.1) e f g Q) {j u v : Crossing (E.curve t)}
    (hj : j.val ∈ triangleSupports e f g) (hu : u.val ∈ triangleSupports e f g)
    (hv : v.val ∈ triangleSupports e f g) :
    transportSupport hs (Q ∪ {j, u, v}) ∈ CV.Ind (geomAt E t' ht'.1) := by
  have hJ : ∀ c ∈ ({j, u, v} : Finset (Crossing (E.curve t))), c.val ∈ triangleSupports e f g := by
    intro c hc
    simp only [Finset.mem_insert, Finset.mem_singleton] at hc
    rcases hc with rfl | rfl | rfl <;> assumption
  rw [AV_transportSupport_union]
  refine PRE_union_mem_Ind_of_fullAvail (GT_outsideSupports_transport hL ht ht' hop hs hQ)
    (GT_fullAvail_transport hL ht ht' hop hs hQ hfull) ?_
    (r176s_triangle_ind_L hL ht ht' hop hs hcomp hJ)
  intro c' hc'
  obtain ⟨c, rfl⟩ := (crossingTransport hs).surjective c'
  rw [mem_transportSupport_iff] at hc'
  exact (F1.mem_triangleCrossings e f g _).mpr (hJ c hc')

end R176S_Sfull

end R176S_SfullVars

/-! ## §R5. The event level: the outer carriers (black box), the ledger (black box), the port data -/

section R176S_Event

variable {n : ℕ} [NeZero n] {E : CV.Event n} {e f g : ZMod n} {δ : ℝ}

/-- the third triangle crossing, given two distinct ones -/
theorem r176s_third {t : E.Parameter} (hef' : IsCrossing (E.curve t) {e, f}) (heg' : IsCrossing (E.curve t) {e, g})
    (hfg' : IsCrossing (E.curve t) {f, g}) {j u : Crossing (E.curve t)} (hj : j.val ∈ triangleSupports e f g)
    (hu : u.val ∈ triangleSupports e f g) (hju : j ≠ u) :
    ∃ v : Crossing (E.curve t), v.val ∈ triangleSupports e f g ∧ j ≠ v ∧ u ≠ v := by
  have h1 : (xPair hef').val ∈ triangleSupports e f g := (P1.mem_triangleSupports _).mpr (Or.inl rfl)
  have h2 : (xPair heg').val ∈ triangleSupports e f g := (P1.mem_triangleSupports _).mpr (Or.inr (Or.inl rfl))
  have h3 : (xPair hfg').val ∈ triangleSupports e f g := (P1.mem_triangleSupports _).mpr (Or.inr (Or.inr rfl))
  have n12 := P1.xPair_ef_ne_eg hef' heg' hfg'
  have n13 := P1.xPair_ef_ne_fg hef' heg' hfg'
  have n23 := P1.xPair_eg_ne_fg hef' heg' hfg'
  rcases GT_tri_cases t hef' heg' hfg' j hj with rfl | rfl | rfl <;>
  rcases GT_tri_cases t hef' heg' hfg' u hu with rfl | rfl | rfl <;>
  first
  | exact absurd rfl hju
  | exact ⟨_, h3, n13, n23⟩
  | exact ⟨_, h2, n12, n23.symm⟩
  | exact ⟨_, h1, n12.symm, n13.symm⟩
  | exact ⟨_, h3, n23, n13⟩
  | exact ⟨_, h2, n23.symm, n12⟩
  | exact ⟨_, h1, n13.symm, n12.symm⟩

/-- the `CarrierGeometry` of the empty side, as the library's `carrierDiagram` reads it -/
abbrev r176s_cgL (hn : 3 ≤ n) {t' : E.Parameter} (ht' : Punctured E δ t') : CarrierGeometry (E.curve t') :=
  CarrierGeometry.ofDiagrammatic ((genericAt E t' ht'.1).diagrammatic hn)

/-- **The outer carriers of `S_full` and the arc identification (DATA; U_R176_REPORT §5 item 3, the "skeleton ↔
carrier identification" on `geoSmoothingSuccessor` of `S_full`)** — the remaining geometric obligation of the
SMOOTH unit, consumed through the black box `r176s_outer_carriers`.  With `D₊ = carrierDiagram q₀'`,
`ρ = D₊.record` and `y` the lift of the retained unselected crossing `u'`: an occurrence `v₀` of `y`, the two outer
carriers `Λ_A, Λ_B` of `S_full = Q' ∪ {j', u', v'}` (retained crossings among those of `q₀'`), such that the
crossings of `ρ` with both occurrences on the arc `A = (v₀ → τ v₀)` are exactly the chords labelled by the retained
crossings of `Λ_A` (the clean component), and those on the arc `B = (τ v₀ → v₀)` are the chords of `Λ_B` plus one
kink `r` (the lift of the third triangle crossing `v'`), whose two occurrences are consecutive in `ρ|B`
(lc:single-crossing's "just one self crossing" on the `B`-component). -/
structure r176s_OuterData (hn : 3 ≤ n) (hL : LocalizationData E e f g δ) (hR : AV_EventRadius E δ)
    (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g) {t t' : E.Parameter} (ht : Punctured E δ t)
    (ht' : Punctured E δ t') (hop : OppositeSides E t t')
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    {Q : Finset (Crossing (E.curve t))} (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
    (hfull : FullAvail (geomAt E t ht.1) e f g Q) {j : Crossing (E.curve t)}
    (hj : j.val ∈ triangleSupports e f g) (q : GeoComponent (geomAt E t ht.1) (Q ∪ {j}))
    {u : Crossing (E.curve t)}
    (hu' : crossingTransport hs u ∈ geoCarrierCrossings (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j}))
        (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q))
    (v : Crossing (E.curve t)) where
  /-- the occurrence of `y` from which the arc `A` carries the kink-free component -/
  v₀ : (CV.carrierDiagram hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj)
    (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)).Γ.Visit
  hv₀ : v₀.1 = est_liftCrossing hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj) _ hu'
  /-- the clean outer carrier (the `A`-component) -/
  ΛA : GeoComponent (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j, u, v}))
  /-- the kinked outer carrier (the `B`-component) -/
  ΛB : GeoComponent (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j, u, v}))
  subA : geoCarrierCrossings (geomAt E t' ht'.1) _ ΛA ⊆
    geoCarrierCrossings (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j}))
      (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)
  subB : geoCarrierCrossings (geomAt E t' ht'.1) _ ΛB ⊆
    geoCarrierCrossings (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j}))
      (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)
  /-- the crossings on the arc `A` are the chords of `Λ_A` -/
  KA_eq : r176s_KA (CV.carrierDiagram hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj)
      (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)).record v₀ =
    CV.liftBlock hn (r176s_cgL hn ht') (CV.geoIndependent_of_mem_Ind _ (est_S'_ind hL ht ht' hop hs hQ hfull hj))
      (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)
      (geoCarrierCrossings (geomAt E t' ht'.1) _ ΛA)
  /-- the kink -/
  r : (CV.carrierDiagram hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj)
    (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)).record.Crossing
  /-- the crossings on the arc `B` are the chords of `Λ_B` plus the kink -/
  KB_eq : r176s_KB (CV.carrierDiagram hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj)
      (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)).record v₀ =
    CV.liftBlock hn (r176s_cgL hn ht') (CV.geoIndependent_of_mem_Ind _ (est_S'_ind hL ht ht' hop hs hQ hfull hj))
      (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)
      (geoCarrierCrossings (geomAt E t' ht'.1) _ ΛB) ∪ {r}
  r_not : r ∉ CV.liftBlock hn (r176s_cgL hn ht')
    (CV.geoIndependent_of_mem_Ind _ (est_S'_ind hL ht ht' hop hs hQ hfull hj))
    (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)
    (geoCarrierCrossings (geomAt E t' ht'.1) _ ΛB)
  /-- the kink's two occurrences are consecutive in `ρ|B` -/
  r_curl : ∃ (w : (CV.carrierDiagram hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj)
      (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)).record.M)
    (hw : (CV.carrierDiagram hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj)
      (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)).record.CrossKeep
        (r176s_KB (CV.carrierDiagram hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj)
          (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)).record v₀) w),
    (CV.carrierDiagram hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj)
      (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)).record.crossingOf w = r ∧
    (((CV.carrierDiagram hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj)
      (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)).record.restrictCrossings
        (r176s_KB (CV.carrierDiagram hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj)
          (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)).record v₀)).succ
            ⟨w, hw⟩).1 =
      (CV.carrierDiagram hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj)
        (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)).record.pair w

end R176S_Event

/-- **The outer-carrier data exists — BLACK BOX (the remaining geometric obligation of the SMOOTH unit)**: in
the event binders of `est_port_relation` (`K3` side `t`, empty side `t'`, affected carrier `q` with the retained
unselected `u'`, third triangle crossing `v`).  Geometric content: the carriers of `S_full` relative to those of
`S'` — `q₀'` splits at `u', v'` into the central triangle and the two outer carriers (the `geoSmoothingSuccessor`
of `S_full` on the visits of `q₀'`), the cyclic-order data of the site (`s176_corner_case1`, the order `v' <_c u'`
forced by the empty local graph), and `CV.arcBetween_iff_key` to read the record arcs on the parent. -/
def r176s_outer_carriers : Prop :=
  ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (E : CV.Event n) (e f g : ZMod n) (δ : ℝ)
    (hL : LocalizationData E e f g δ) (hR : AV_EventRadius E δ) (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
    (t t' : E.Parameter) (ht : Punctured E δ t) (ht' : Punctured E δ t') (hop : OppositeSides E t t')
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    (hef' : IsCrossing (E.curve t) {e, f}) (heg' : IsCrossing (E.curve t) {e, g})
    (hfg' : IsCrossing (E.curve t) {f, g}) (_hcomp : CompleteLocal (geomAt E t ht.1) hef' heg' hfg')
    (Q : Finset (Crossing (E.curve t))) (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
    (hfull : FullAvail (geomAt E t ht.1) e f g Q) (j : Crossing (E.curve t))
    (hj : j.val ∈ triangleSupports e f g) (q : GeoComponent (geomAt E t ht.1) (Q ∪ {j}))
    (u : Crossing (E.curve t)) (_hu : u.val ∈ triangleSupports e f g) (_hju : j ≠ u)
    (hu' : crossingTransport hs u ∈ geoCarrierCrossings (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j}))
        (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q))
    (v : Crossing (E.curve t)) (_hv : v.val ∈ triangleSupports e f g) (_hjv : j ≠ v) (_huv : u ≠ v),
    Nonempty (r176s_OuterData hn hL hR hef heg hfg ht ht' hop hs hQ hfull hj q hu' v)

/-- **The ledgers (14), (13), (12) — BLACK BOX (U_R176_REPORT §5 items 4–5, NOT this unit)**: for the outer
carriers of `r176s_OuterData` and the linking number `ℓ` of the two components of `D_A` (`i` the `B`-class of
`v₀`, `j` the `A`-class of `τ v₀`): `w_0 = w(Λ_B) + w(Λ_A) + 2ℓ`, `R(q) = R(Λ_B) + R(Λ_A) + 1`, and the one-dissent
sign ledger for `Λ_B`, `Λ_A`. -/
def r176s_ledger : Prop :=
  ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (E : CV.Event n) (e f g : ZMod n) (δ : ℝ)
    (hL : LocalizationData E e f g δ) (hR : AV_EventRadius E δ) (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
    (t t' : E.Parameter) (ht : Punctured E δ t) (ht' : Punctured E δ t') (hop : OppositeSides E t t')
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    (hef' : IsCrossing (E.curve t) {e, f}) (heg' : IsCrossing (E.curve t) {e, g})
    (hfg' : IsCrossing (E.curve t) {f, g}) (hcomp : CompleteLocal (geomAt E t ht.1) hef' heg' hfg')
    (Q : Finset (Crossing (E.curve t))) (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
    (hfull : FullAvail (geomAt E t ht.1) e f g Q) (j : Crossing (E.curve t))
    (hj : j.val ∈ triangleSupports e f g) (q : GeoComponent (geomAt E t ht.1) (Q ∪ {j}))
    (u : Crossing (E.curve t)) (hu : u.val ∈ triangleSupports e f g) (_hju : j ≠ u)
    (hu' : crossingTransport hs u ∈ geoCarrierCrossings (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j}))
        (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q))
    (v : Crossing (E.curve t)) (hv : v.val ∈ triangleSupports e f g) (_hjv : j ≠ v) (_huv : u ≠ v)
    (O : r176s_OuterData hn hL hR hef heg hfg ht ht' hop hs hQ hfull hj q hu' v) (ℓ : ℤ),
    CV.IsLinkingNumber
      (r176s_DA (CV.carrierDiagram hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj)
        (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q))
        (est_liftCrossing hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj) _ hu'))
      (r176s_DA_i _ _ O.v₀ O.hv₀) (r176s_DA_j _ _ O.v₀ O.hv₀) ℓ →
    CV.groupedWrithe (genericAt E t ht.1) q =
        CV.groupedWrithe (genericAt E t' ht'.1) O.ΛB + CV.groupedWrithe (genericAt E t' ht'.1) O.ΛA + 2 * ℓ ∧
    (CV.carrierR hn (genericAt E t ht.1) (est_S_ind ht.1 hQ hfull hj) q : ℤ) =
        CV.carrierR hn (genericAt E t' ht'.1) (r176s_Sfull_ind hL ht ht' hop hs hcomp hQ hfull hj hu hv) O.ΛB +
        CV.carrierR hn (genericAt E t' ht'.1) (r176s_Sfull_ind hL ht ht' hop hs hcomp hQ hfull hj hu hv) O.ΛA + 1 ∧
    CV.UniformOrOneDissentCV (geoCornerPolygon (genericAt E t' ht'.1).crossingGeometry _ O.ΛB) ∧
    CV.UniformOrOneDissentCV (geoCornerPolygon (genericAt E t' ht'.1).crossingGeometry _ O.ΛA)

section R176S_Port

variable {n : ℕ} [NeZero n] {E : CV.Event n} {e f g : ZMod n} {δ : ℝ}

/-- **The non-move port data of row 176** (`s176_PortDataRest`) from the three black boxes: `DA` the library
smoothing of `D₊ = carrierDiagram q₀'` at `y` with its two components, `S_f = Q' ∪ {j', u', v'}`, `Λ₁ = Λ_B`
(kinked), `Λ₂ = Λ_A` (clean), the exact owner map (9)/(9a) through the record identifications, the linking
number by `CV.exists_linkingNumber`, and the ledgers (14), (13), (12) from `r176s_ledger`. -/
theorem r176s_portDataRest_of (hcurl : r176s_curl_removal) (hout : r176s_outer_carriers) (hled : r176s_ledger)
    (hn : 3 ≤ n) (hL : LocalizationData E e f g δ) (hR : AV_EventRadius E δ)
    (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g) {t t' : E.Parameter} (ht : Punctured E δ t)
    (ht' : Punctured E δ t') (hop : OppositeSides E t t')
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    (hef' : IsCrossing (E.curve t) {e, f}) (heg' : IsCrossing (E.curve t) {e, g})
    (hfg' : IsCrossing (E.curve t) {f, g}) (hcomp : CompleteLocal (geomAt E t ht.1) hef' heg' hfg')
    {Q : Finset (Crossing (E.curve t))} (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
    (hfull : FullAvail (geomAt E t ht.1) e f g Q) {j : Crossing (E.curve t)}
    (hj : j.val ∈ triangleSupports e f g) (q : GeoComponent (geomAt E t ht.1) (Q ∪ {j}))
    {u : Crossing (E.curve t)} (hu : u.val ∈ triangleSupports e f g) (hju : j ≠ u)
    (hu' : crossingTransport hs u ∈ geoCarrierCrossings (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j}))
        (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)) :
    Nonempty (s176_PortDataRest hn (genericAt E t ht.1) (genericAt E t' ht'.1) (est_S_ind ht.1 hQ hfull hj)
      (est_S'_ind hL ht ht' hop hs hQ hfull hj) q
      (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)
      (est_liftCrossing hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj) _ hu')) := by
  obtain ⟨v, hv, hjv, huv⟩ := r176s_third hef' heg' hfg' hj hu hju
  obtain ⟨O⟩ := hout n hn E e f g δ hL hR hef heg hfg t t' ht ht' hop hs hef' heg' hfg' hcomp Q hQ hfull j hj q
    u hu hju hu' v hv hjv huv
  have hD1 : (CV.carrierDiagram hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj)
      (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)).componentCount = 1 :=
    geoPositiveLift_componentCount hn _ _ _
  obtain ⟨ℓ, hℓ⟩ := CV.exists_linkingNumber _ _ _ (r176s_DA_ij _ _ hD1 O.v₀ O.hv₀)
  obtain ⟨hw, hrot, haltB, haltA⟩ := hled n hn E e f g δ hL hR hef heg hfg t t' ht ht' hop hs hef' heg' hfg'
    hcomp Q hQ hfull j hj q u hu hju hu' v hv hjv huv O ℓ hℓ
  refine ⟨{
    DA := r176s_DA _ _
    smooth := r176s_DA_smooth _ _
    two := r176s_DA_componentCount _ _ hD1
    i := r176s_DA_i _ _ O.v₀ O.hv₀
    j := r176s_DA_j _ _ O.v₀ O.hv₀
    ij := r176s_DA_ij _ _ hD1 O.v₀ O.hv₀
    Sf := transportSupport hs (Q ∪ {j, u, v})
    hSf := r176s_Sfull_ind hL ht ht' hop hs hcomp hQ hfull hj hu hv
    Λ₁ := O.ΛB
    Λ₂ := O.ΛA
    poly₁ := ?_
    poly₂ := ?_
    ℓ := ℓ
    link := hℓ
    writhe := hw
    rot := hrot
    alt₁ := haltB
    alt₂ := haltA }⟩
  · -- (9a) the kinked component: `Λ_B` through the record-level R-I
    rw [GT_groupedPoly_eq_homfly]
    exact r176s_homfly_of_liftBlock_curl hcurl hn (r176s_cgL hn ht')
      (CV.geoIndependent_of_mem_Ind _ (est_S'_ind hL ht ht' hop hs hQ hfull hj))
      (CV.geoIndependent_of_mem_Ind _ (r176s_Sfull_ind hL ht ht' hop hs hcomp hQ hfull hj hu hv))
      _ O.ΛB O.subB _ _ O.r O.KB_eq O.r_not O.r_curl ⟨r176s_knotRestrictIso_i _ _ hD1 O.v₀ O.hv₀⟩
  · -- (9a) the clean component: `Λ_A`
    rw [GT_groupedPoly_eq_homfly]
    exact r176s_homfly_of_liftBlock hn (r176s_cgL hn ht')
      (CV.geoIndependent_of_mem_Ind _ (est_S'_ind hL ht ht' hop hs hQ hfull hj))
      (CV.geoIndependent_of_mem_Ind _ (r176s_Sfull_ind hL ht ht' hop hs hcomp hQ hfull hj hu hv))
      _ O.ΛA O.subA _ _ O.KA_eq ⟨r176s_knotRestrictIso_j _ _ hD1 O.v₀ O.hv₀⟩

/-- **The weak interface of row 176 from the site, `hrec`, and the three black boxes** — the frozen
`s176_est_port_relation_weak_of` with its `hrest` discharged by `r176s_portDataRest_of` (whose binders carry the
`K3` data `hcomp`, `hu`, `hju` that the frozen `hrest` lacks). -/
theorem r176s_est_port_relation_weak_of'' (hcurl : r176s_curl_removal) (hout : r176s_outer_carriers)
    (hled : r176s_ledger)
    (hrec : ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (E : CV.Event n) (e f g : ZMod n) (δ : ℝ)
      (hL : LocalizationData E e f g δ) (hR : AV_EventRadius E δ) (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
      (t t' : E.Parameter) (ht : Punctured E δ t) (ht' : Punctured E δ t') (hop : OppositeSides E t t')
      (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
      (Q : Finset (Crossing (E.curve t))) (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
      (hfull : FullAvail (geomAt E t ht.1) e f g Q) (j : Crossing (E.curve t))
      (hj : j.val ∈ triangleSupports e f g) (q : GeoComponent (geomAt E t ht.1) (Q ∪ {j}))
      (u : Crossing (E.curve t))
      (hu' : crossingTransport hs u ∈ geoCarrierCrossings (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j}))
        (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)),
      s176_hrec_of_site hn hL hR hef heg hfg ht ht' hop hs hQ hfull hj q hu') :
    s176_est_port_relation_weak := by
  intro n _ hn E e f g δ hL hR hef heg hfg t t' ht ht' hop hs hef' heg' hfg' hcomp Q hQ hfull j hj q hex
  obtain ⟨u, hu, hju, hu'⟩ := hex
  obtain ⟨R⟩ := r176s_portDataRest_of hcurl hout hled hn hL hR hef heg hfg ht ht' hop hs hef' heg' hfg' hcomp
    hQ hfull hj q hu hju.symm hu'
  refine ⟨u, hu, hju, hu', ⟨s176_PortDataWeak.mk' _ _ _ _ _ _ _ _ ?_ R⟩⟩
  exact s176_port_weak_of_event hn hL hR hef heg hfg ht ht' hop hs hef' heg' hfg' hcomp hQ hfull hj q hu hju.symm
    hu' (hrec n hn E e f g δ hL hR hef heg hfg t t' ht ht' hop hs Q hQ hfull j hj q u hu')

end R176S_Port

end

end RProof


/-! # R176_LEDGER — row 176 (R:extreme_transport), the LEDGER unit: items (14), (13), (12) of
`s176_PortDataRest`

APPENDED by the LEDGER prover, 2026-09-15, to `Site_176.lean` (byte-identical above this line).
Companion report: `R176_LEDGER_REPORT.md`.  All names carry the prefix `r176l_`; nothing above is
modified.  The oriented smoothing `D_A`, its component tags and the exact owner map (`poly₁`, `poly₂`)
are the SMOOTH unit's and enter only through the black-box structure `r176l_SmoothData`.

Sections: §L0 abstract sign/rotation ledgers on labelled tuples ((12) from a one-dissent corner-sign
shape, `σ·rot ≥ 1`, the uniform triangle, the `|·|`-ledger arithmetic of (13)); §L1 `mixedSignSum` as
the number of mixed crossings when every crossing is positive; §L2 the interface — the two clean outer
children `r176l_Children`, the mask-`uv` survivors `r176l_mixedSet`, the L-side retained-set
decomposition (14), the black box `r176l_SmoothData`, and the assembly `r176l_portDataRest_of`; §L3 the
geometric realisation on the labelled corner (case 1): the two-step split of the affected carrier by
`u', v'`, the central triangle, the children, the corner marks and turns of the outer carriers, the
one-dissent shapes (12) and the rotation additivity (13); §L4 the event level. -/

namespace RProof

open SM SM.GeoCarrier SM.Carrier SM.Link

noncomputable section

variable {n : ℕ} [NeZero n]

/-! ## §L0. Abstract sign and rotation ledgers on labelled tuples -/

/-- **The corner-sign shape of a clean outer carrier** (RA (12): "exactly one `-σ` local corner and
all inherited corners have sign `σ`"): every turn of `L` is `σ` except exactly one, which is `-σ`. -/
def r176l_OneDissentShape {c : ℕ} (L : LabelledTuple c) (σ : SignType) : Prop :=
  ∃ k₀ : ZMod c, turn L k₀ = -σ ∧ ∀ k, k ≠ k₀ → turn L k = σ

theorem r176l_principalTurn_pos_of_turn {c : ℕ} [NeZero c] {L : LabelledTuple c} (hL : CV.Regular L)
    {k : ZMod c} (h : turn L k = 1) : 0 < CV.principalTurn L k := by
  rw [CV.principalTurn_eq_sm]
  exact sign_eq_one_iff.mp ((principalTurn_sign ((CV.regular_iff_sm L).mp hL) k).trans h)

theorem r176l_principalTurn_neg_of_turn {c : ℕ} [NeZero c] {L : LabelledTuple c} (hL : CV.Regular L)
    {k : ZMod c} (h : turn L k = -1) : CV.principalTurn L k < 0 := by
  rw [CV.principalTurn_eq_sm]
  exact sign_eq_neg_one_iff.mp ((principalTurn_sign ((CV.regular_iff_sm L).mp hL) k).trans h)

/-- **(12)**: a one-dissent shape with `σ ≠ 0` is uniform-or-one-dissent in CV's sense: for `σ = 1`
directly (one negative turn, all others positive), for `σ = -1` after the orientation reversal
(`principalTurn_reversal` negates every turn). -/
theorem r176l_uniformOrOneDissent_of_shape {c : ℕ} [NeZero c] {L : LabelledTuple c}
    (hL : CV.Regular L) {σ : SignType} (hσ : σ ≠ 0) (h : r176l_OneDissentShape L σ) :
    CV.UniformOrOneDissentCV L := by
  obtain ⟨k₀, hk₀, hk⟩ := h
  have hSM : Regular L := (CV.regular_iff_sm L).mp hL
  cases σ with
  | zero => exact absurd rfl hσ
  | pos =>
    left; right
    exact ⟨k₀, r176l_principalTurn_neg_of_turn hL hk₀,
      fun k hk' => r176l_principalTurn_pos_of_turn hL (hk k hk')⟩
  | neg =>
    right; right
    refine ⟨2 - k₀, ?_, ?_⟩
    · rw [CV.principalTurn_eq_sm, principalTurn_reversal hSM]
      have h1 : turn L (2 - (2 - k₀)) = 1 := by
        rw [show (2 : ZMod c) - (2 - k₀) = k₀ by ring]; exact hk₀
      have := r176l_principalTurn_pos_of_turn hL h1
      rw [CV.principalTurn_eq_sm] at this; linarith
    · intro i hi
      rw [CV.principalTurn_eq_sm, principalTurn_reversal hSM]
      have hne : 2 - i ≠ k₀ := fun h => hi (by rw [← h]; ring)
      have := r176l_principalTurn_neg_of_turn hL (hk _ hne)
      rw [CV.principalTurn_eq_sm] at this; linarith

/-- The signed rotation of a one-dissent-shaped polygon has the sign `σ` and is nonzero
(CV lem:uniformrot (ii), after a possible reversal): `σ · rot(L) ≥ 1`. -/
theorem r176l_one_le_sign_mul_rot_of_shape {c : ℕ} [NeZero c] {L : LabelledTuple c}
    (hL : CV.Regular L) {σ : SignType} (hσ : σ ≠ 0) (h : r176l_OneDissentShape L σ) :
    1 ≤ (σ : ℤ) * CV.rot L hL := by
  obtain ⟨k₀, hk₀, hk⟩ := h
  have hSM : Regular L := (CV.regular_iff_sm L).mp hL
  cases σ with
  | zero => exact absurd rfl hσ
  | pos =>
    have := CV.one_le_rot_of_one_dissent hL k₀
      (fun i hi => (r176l_principalTurn_pos_of_turn hL (hk i hi)).le)
    simpa using this
  | neg =>
    have hrev := CV.regular_reversal' hL
    have h1 : 1 ≤ CV.rot (reversal L) hrev := by
      refine CV.one_le_rot_of_one_dissent hrev (2 - k₀) fun i hi => ?_
      rw [CV.principalTurn_eq_sm, principalTurn_reversal hSM]
      have hne : 2 - i ≠ k₀ := fun h => hi (by rw [← h]; ring)
      have := r176l_principalTurn_neg_of_turn hL (hk _ hne)
      rw [CV.principalTurn_eq_sm] at this; linarith
    rw [CV.rot_reversal hL hrev] at h1
    simpa using h1

/-- The rotation of a uniform three-corner polygon is its common turn sign (CV lem:uniformrot (i),
"with equality if `L` has three corners"). -/
theorem r176l_rot_uniform_three {c : ℕ} [NeZero c] {L : LabelledTuple c} (hL : CV.Regular L)
    (h3 : c = 3) {σ : SignType} (hσ : σ ≠ 0) (h : ∀ k, turn L k = σ) : CV.rot L hL = (σ : ℤ) := by
  cases σ with
  | zero => exact absurd rfl hσ
  | pos =>
    have := CV.uniformrot.pos_three c L hL (fun i => r176l_principalTurn_pos_of_turn hL (h i)) h3
    simpa using this
  | neg =>
    have := CV.uniformrot.neg_three c L hL (fun i => r176l_principalTurn_neg_of_turn hL (h i)) h3
    simpa using this

/-- **The `|·|`-arithmetic of (13)**: three signed rotations of one sign `σ` add up in absolute value. -/
theorem r176l_abs_ledger {r r₁ r₂ : ℤ} {σ : SignType} (hσ : σ ≠ 0) (h : r = r₁ + r₂ + (σ : ℤ))
    (h₁ : 1 ≤ (σ : ℤ) * r₁) (h₂ : 1 ≤ (σ : ℤ) * r₂) : |r| = |r₁| + |r₂| + 1 := by
  cases σ with
  | zero => exact absurd rfl hσ
  | pos =>
    simp only [SignType.pos_eq_one, SignType.coe_one, one_mul] at h h₁ h₂
    rw [abs_of_pos (by omega), abs_of_pos (by omega), abs_of_pos (by omega)]
    omega
  | neg =>
    simp only [SignType.neg_eq_neg_one, SignType.coe_neg, SignType.coe_one, neg_mul, one_mul] at h h₁ h₂
    rw [abs_of_neg (by omega), abs_of_neg (by omega), abs_of_neg (by omega)]
    omega

/-! ## §L1. `2ℓ` as the number of mixed crossings when every crossing is positive -/

/-- A crossing of `D` between the components `i` and `j` ("mixed"). -/
def r176l_IsMixed (D : Diagram) (i j : Fin D.Γ.c) (x : D.Γ.Crossing) : Prop :=
  ((D.overStrand x).1 = i ∧ (D.underStrand x).1 = j) ∨
  ((D.overStrand x).1 = j ∧ (D.underStrand x).1 = i)

open scoped Classical in
/-- `2ℓ_ij` as a sum over the mixed crossings (each mixed crossing is exactly one ordered strand pair
`(s, t)` with `s` on `i`, `t` on `j`); the proof is the accepted `SM.s7h_mixedSignSum_eq`
(SM/CornerChainUnits.lean, not imported here), copied. -/
theorem r176l_mixedSignSum_eq (D : Diagram) (i j : Fin D.Γ.c) (hij : i ≠ j) :
    mixedSignSum D i j =
      ∑ x ∈ Finset.univ.filter (r176l_IsMixed D i j), (D.sign x : ℤ) := by
  unfold mixedSignSum
  rw [← Finset.sum_product' Finset.univ Finset.univ (fun s t : D.Γ.Strand =>
    if h : D.Γ.MixedPair i j s t then ((D.sign ⟨{s, t}, h.2.2⟩ : SignType) : ℤ) else 0)]
  have hmp : ∀ p : D.Γ.Strand × D.Γ.Strand,
      (if h : D.Γ.MixedPair i j p.1 p.2 then ((D.sign ⟨{p.1, p.2}, h.2.2⟩ : SignType) : ℤ) else 0) ≠ 0 →
      D.Γ.MixedPair i j p.1 p.2 := by
    intro p hne
    by_contra hm
    exact hne (dite_eq_right hm)
  refine Finset.sum_bij_ne_zero (fun p _ hne => ⟨{p.1, p.2}, (hmp p hne).2.2⟩) ?_ ?_ ?_ ?_
  · intro p _ hne
    have hm := hmp p hne
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    rcases D.eq_over_under_of_crossing_eq hm.2.2 rfl with ⟨hs, ht⟩ | ⟨hs, ht⟩
    · left; exact ⟨by rw [← hs]; exact hm.1, by rw [← ht]; exact hm.2.1⟩
    · right; exact ⟨by rw [← ht]; exact hm.2.1, by rw [← hs]; exact hm.1⟩
  · intro p₁ _ hne₁ p₂ _ hne₂ e
    have hm₁ := hmp p₁ hne₁
    have hm₂ := hmp p₂ hne₂
    have e' : ({p₁.1, p₁.2} : Finset D.Γ.Strand) = {p₂.1, p₂.2} := congrArg Subtype.val e
    have hs : p₁.1 ∈ ({p₂.1, p₂.2} : Finset D.Γ.Strand) := by
      rw [← e']; exact Finset.mem_insert_self _ _
    have ht : p₁.2 ∈ ({p₂.1, p₂.2} : Finset D.Γ.Strand) := by
      rw [← e']; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    rw [Finset.mem_insert, Finset.mem_singleton] at hs ht
    refine Prod.ext ?_ ?_
    · exact hs.resolve_right fun h => hij (by rw [← hm₁.1, h, hm₂.2.1])
    · exact ht.resolve_left fun h => hij (by rw [← hm₂.1, ← h, hm₁.2.1])
  · intro x hx _
    have hx' := (Finset.mem_filter.mp hx).2
    have hsgn : ((D.sign x : SignType) : ℤ) ≠ 0 := by
      rcases D.sign_eq_one_or_neg_one x with h | h <;> rw [h] <;> decide
    rcases hx' with ⟨ho, hu⟩ | ⟨ho, hu⟩
    · have hm : D.Γ.MixedPair i j (D.overStrand x) (D.underStrand x) :=
        ⟨ho, hu, by rw [← D.val_eq_pair x]; exact x.2⟩
      refine ⟨(D.overStrand x, D.underStrand x), Finset.mem_univ _, ?_, ?_⟩
      · rw [dite_eq_left hm]
        have e : (⟨{D.overStrand x, D.underStrand x}, hm.2.2⟩ : D.Γ.Crossing) = x :=
          Subtype.ext (D.val_eq_pair x).symm
        rw [e]; exact hsgn
      · exact Subtype.ext (D.val_eq_pair x).symm
    · have hm : D.Γ.MixedPair i j (D.underStrand x) (D.overStrand x) :=
        ⟨hu, ho, by rw [Finset.pair_comm, ← D.val_eq_pair x]; exact x.2⟩
      refine ⟨(D.underStrand x, D.overStrand x), Finset.mem_univ _, ?_, ?_⟩
      · rw [dite_eq_left hm]
        have e : (⟨{D.underStrand x, D.overStrand x}, hm.2.2⟩ : D.Γ.Crossing) = x :=
          Subtype.ext ((Finset.pair_comm _ _).trans (D.val_eq_pair x).symm)
        rw [e]; exact hsgn
      · exact Subtype.ext ((Finset.pair_comm _ _).trans (D.val_eq_pair x).symm)
  · intro p _ hne
    rw [dite_eq_left (hmp p hne)]

open scoped Classical in
/-- **"Since every mixed retained crossing is positive … exactly `2ℓ` complementary-mask crossings
occur"**: with every crossing positive, `2ℓ_ij` is the number of mixed crossings. -/
theorem r176l_mixedSignSum_eq_card (D : Diagram) (i j : Fin D.Γ.c) (hij : i ≠ j)
    (hpos : ∀ x : D.Γ.Crossing, D.sign x = 1) :
    mixedSignSum D i j = ((Finset.univ.filter (r176l_IsMixed D i j)).card : ℤ) := by
  rw [r176l_mixedSignSum_eq D i j hij, Finset.card_eq_sum_ones, Nat.cast_sum]
  exact Finset.sum_congr rfl fun x _ => by rw [hpos x]; rfl

/-! ## §L2. The interface: the two clean outer children, the mask-`uv` survivors, the black box -/

section L2Children

variable {P : LabelledTuple n} (hP : CrossingGeometry P)

/-- **The two clean outer children** `Λ₁, Λ₂` of the affected carrier `q'` of `S'` inside the full
support `Sf ⊇ S'` (RA §2: "the two successive smoothings `q, r` split that carrier into the two clean
outer carriers … and the central triangle"): both lie inside `q'`, they are distinct, and every visit
of an unselected (in `Sf`) crossing that `q'` owns is owned by one of them (the central triangle owns
only the three local corner marks). -/
structure r176l_Children (S' Sf : Finset (Crossing P)) (q' : GeoComponent hP S')
    (Λ₁ Λ₂ : GeoComponent hP Sf) : Prop where
  sub₁ : ∀ m : Mark P, geoOwner hP Sf m = Λ₁ → geoOwner hP S' m = q'
  sub₂ : ∀ m : Mark P, geoOwner hP Sf m = Λ₂ → geoOwner hP S' m = q'
  ne : Λ₁ ≠ Λ₂
  cover : ∀ w : Visit P, w.1 ∉ Sf → geoOwner hP S' (Sum.inr w) = q' →
    geoOwner hP Sf (Sum.inr w) = Λ₁ ∨ geoOwner hP Sf (Sum.inr w) = Λ₂

open scoped Classical in
/-- **The mask-`uv` survivors** (R-PAR `interlaced_pair`; RA (5) "every two-letter-mask survivor has
one visit in each of the two affected gaps"): the retained crossings of `q'`, unselected in `Sf`, whose
two visits lie on different children — exactly the mixed crossings of `D_A` (14). -/
def r176l_mixedSet (S' Sf : Finset (Crossing P)) (q' : GeoComponent hP S')
    (Λ₁ Λ₂ : GeoComponent hP Sf) : Finset (Crossing P) :=
  (geoCarrierCrossings hP S' q').filter fun x => x ∉ Sf ∧
    ∃ v w : Visit P, v.1 = x ∧ w.1 = x ∧
      geoOwner hP Sf (Sum.inr v) = Λ₁ ∧ geoOwner hP Sf (Sum.inr w) = Λ₂

open scoped Classical in
/-- The retained crossings of `q'` that are selected in `Sf` (at the 176 site: `{u', v'}`). -/
def r176l_selectedPart (S' Sf : Finset (Crossing P)) (q' : GeoComponent hP S') : Finset (Crossing P) :=
  (geoCarrierCrossings hP S' q').filter fun x => x ∈ Sf

variable {S' Sf : Finset (Crossing P)} {q' : GeoComponent hP S'} {Λ₁ Λ₂ : GeoComponent hP Sf}

/-- The retained set of a child is inside the retained set of `q'`, off `Sf`. -/
theorem r176l_retained_child_subset (hSS : S' ⊆ Sf)
    (hsub : ∀ m : Mark P, geoOwner hP Sf m = Λ₁ → geoOwner hP S' m = q') {x : Crossing P}
    (hx : x ∈ geoCarrierCrossings hP Sf Λ₁) : x ∈ geoCarrierCrossings hP S' q' ∧ x ∉ Sf := by
  rw [mem_geoCarrierCrossings] at hx ⊢
  exact ⟨⟨fun h => hx.1 (hSS h), fun v hv => hsub _ (hx.2 v hv)⟩, hx.1⟩

/-- **The L-side decomposition of the retained set of the affected carrier** (RA (14): "`D_0` contains
the two outer self-crossing sets and the `2ℓ` positive crossings which become mixed in `D_A`", plus
the two local crossings selected in `Sf`). -/
theorem r176l_retained_decomp (hSS : S' ⊆ Sf) (hC : r176l_Children hP S' Sf q' Λ₁ Λ₂) :
    geoCarrierCrossings hP S' q' =
      geoCarrierCrossings hP Sf Λ₁ ∪ geoCarrierCrossings hP Sf Λ₂ ∪
        r176l_mixedSet hP S' Sf q' Λ₁ Λ₂ ∪ r176l_selectedPart hP S' Sf q' := by
  classical
  ext x
  simp only [Finset.mem_union, r176l_mixedSet, r176l_selectedPart, Finset.mem_filter]
  constructor
  · intro hx
    by_cases hxSf : x ∈ Sf
    · exact Or.inr ⟨hx, hxSf⟩
    · have hx' := (mem_geoCarrierCrossings hP S' q' x).mp hx
      obtain ⟨i, -, -⟩ := crossing_visits_exist x
      set v₀ : Visit P := ⟨x, i⟩ with hv₀
      have hall : ∀ w : Visit P, w.1 = x → w = v₀ ∨ w = visitTwin v₀ := fun w hw =>
        visit_eq_or_twin v₀ w hw
      have ho₀ := hC.cover v₀ hxSf (hx'.2 v₀ rfl)
      have ho₁ := hC.cover (visitTwin v₀) hxSf (hx'.2 _ rfl)
      rcases ho₀ with h₀ | h₀ <;> rcases ho₁ with h₁ | h₁
      · left; left; left
        rw [mem_geoCarrierCrossings]
        refine ⟨hxSf, fun w hw => ?_⟩
        rcases hall w hw with rfl | rfl
        · exact h₀
        · exact h₁
      · left; right
        exact ⟨hx, hxSf, v₀, visitTwin v₀, rfl, rfl, h₀, h₁⟩
      · left; right
        exact ⟨hx, hxSf, visitTwin v₀, v₀, rfl, rfl, h₁, h₀⟩
      · left; left; right
        rw [mem_geoCarrierCrossings]
        refine ⟨hxSf, fun w hw => ?_⟩
        rcases hall w hw with rfl | rfl
        · exact h₀
        · exact h₁
  · rintro (((h | h) | ⟨h, -⟩) | ⟨h, -⟩)
    · exact (r176l_retained_child_subset hP hSS hC.sub₁ h).1
    · exact (r176l_retained_child_subset hP hSS hC.sub₂ h).1
    · exact h
    · exact h

/-- The four parts are pairwise disjoint, so the cardinalities add (14). -/
theorem r176l_card_retained (hSS : S' ⊆ Sf) (hC : r176l_Children hP S' Sf q' Λ₁ Λ₂) :
    (geoCarrierCrossings hP S' q').card =
      (geoCarrierCrossings hP Sf Λ₁).card + (geoCarrierCrossings hP Sf Λ₂).card +
        (r176l_mixedSet hP S' Sf q' Λ₁ Λ₂).card + (r176l_selectedPart hP S' Sf q').card := by
  classical
  have hd₁₂ : Disjoint (geoCarrierCrossings hP Sf Λ₁) (geoCarrierCrossings hP Sf Λ₂) := by
    rw [Finset.disjoint_left]
    intro x h₁ h₂
    obtain ⟨i, -, -⟩ := crossing_visits_exist x
    have e₁ := ((mem_geoCarrierCrossings hP Sf Λ₁ x).mp h₁).2 ⟨x, i⟩ rfl
    have e₂ := ((mem_geoCarrierCrossings hP Sf Λ₂ x).mp h₂).2 ⟨x, i⟩ rfl
    exact hC.ne (e₁.symm.trans e₂)
  have hdM : Disjoint (geoCarrierCrossings hP Sf Λ₁ ∪ geoCarrierCrossings hP Sf Λ₂)
      (r176l_mixedSet hP S' Sf q' Λ₁ Λ₂) := by
    rw [Finset.disjoint_left]
    intro x hx hM
    obtain ⟨-, -, v, w, hv, hw, hov, how⟩ := Finset.mem_filter.mp hM
    rcases Finset.mem_union.mp hx with h | h
    · have := ((mem_geoCarrierCrossings hP Sf Λ₁ x).mp h).2 w hw
      exact hC.ne (this.symm.trans how)
    · have := ((mem_geoCarrierCrossings hP Sf Λ₂ x).mp h).2 v hv
      exact hC.ne (hov.symm.trans this)
  have hdS : Disjoint (geoCarrierCrossings hP Sf Λ₁ ∪ geoCarrierCrossings hP Sf Λ₂ ∪
      r176l_mixedSet hP S' Sf q' Λ₁ Λ₂) (r176l_selectedPart hP S' Sf q') := by
    rw [Finset.disjoint_left]
    intro x hx hS
    have hxSf : x ∈ Sf := (Finset.mem_filter.mp hS).2
    rcases Finset.mem_union.mp hx with h | h
    · rcases Finset.mem_union.mp h with h | h
      · exact ((mem_geoCarrierCrossings hP Sf Λ₁ x).mp h).1 hxSf
      · exact ((mem_geoCarrierCrossings hP Sf Λ₂ x).mp h).1 hxSf
    · exact (Finset.mem_filter.mp h).2.1 hxSf
  rw [r176l_retained_decomp hP hSS hC, Finset.card_union_of_disjoint hdS,
    Finset.card_union_of_disjoint hdM, Finset.card_union_of_disjoint hd₁₂]

end L2Children

/-! ### The black box from the SMOOTH unit -/

/-- **The SMOOTH unit's data, as a black box** (U_R176_REPORT §5 items 2–3): the oriented smoothing
`D_A` of `D₊ = carrierDiagram q'` at `y` with two components `i ≠ j`, the exact owner map (9)/(9a)
`poly₁ poly₂` (the record isomorphisms of the two component restrictions with the lifts of the clean
outer carriers `Λ₁, Λ₂` of `S_full`, the kink removed by lc:single-crossing — SMOOTH's), and the bridge
for (14): the mixed crossings of `D_A` are the mask-`uv` survivors, all positive, so `2ℓ = mixedSignSum`
is their number (`r176l_mixedSignSum_eq_card` reduces this to a bijection between the mixed crossings of
`D_A` and `r176l_mixedSet`).  The support `Sf` and the children `Λ₁, Λ₂` are PARAMETERS: they are
defined geometrically in §L3 by this unit. -/
structure r176l_SmoothData (hn : 3 ≤ n) {P' : LabelledTuple n} (hG' : CV.Generic P')
    {S' : Finset (Crossing P')} (hS' : S' ∈ CV.Ind hG'.crossingGeometry)
    (q' : GeoComponent hG'.crossingGeometry S') (y : (CV.carrierDiagram hn hG' hS' q').Γ.Crossing)
    (Sf : Finset (Crossing P')) (hSf : Sf ∈ CV.Ind hG'.crossingGeometry)
    (Λ₁ Λ₂ : GeoComponent hG'.crossingGeometry Sf) where
  DA : Diagram
  smooth : IsOrientedSmoothing (CV.carrierDiagram hn hG' hS' q') y DA
  two : DA.componentCount = 2
  i : Fin DA.Γ.c
  j : Fin DA.Γ.c
  ij : i ≠ j
  poly₁ : homfly (DA.knotRestrict i) = CV.groupedPoly hn hG' hSf Λ₁
  poly₂ : homfly (DA.knotRestrict j) = CV.groupedPoly hn hG' hSf Λ₂
  /-- (14) bridge: `2ℓ` = the number of mask-`uv` survivors -/
  mixed : mixedSignSum DA i j = ((r176l_mixedSet hG'.crossingGeometry S' Sf q' Λ₁ Λ₂).card : ℤ)

section L2Assembly

variable (hn : 3 ≤ n) {P P' : LabelledTuple n} (hG : CV.Generic P) (hG' : CV.Generic P')
  {S : Finset (Crossing P)} {S' : Finset (Crossing P')}
  (hS : S ∈ CV.Ind hG.crossingGeometry) (hS' : S' ∈ CV.Ind hG'.crossingGeometry)
  (q : GeoComponent hG.crossingGeometry S) (q' : GeoComponent hG'.crossingGeometry S')
  (y : (CV.carrierDiagram hn hG' hS' q').Γ.Crossing)
  {Sf : Finset (Crossing P')} {hSf : Sf ∈ CV.Ind hG'.crossingGeometry}
  {Λ₁ Λ₂ : GeoComponent hG'.crossingGeometry Sf}

/-- **The linking number** `ℓ` of the two components of `D_A` (`CV.exists_linkingNumber`). -/
def r176l_ell (D : r176l_SmoothData hn hG' hS' q' y Sf hSf Λ₁ Λ₂) : ℤ :=
  Classical.choose (CV.exists_linkingNumber D.DA D.i D.j D.ij)

theorem r176l_ell_spec (D : r176l_SmoothData hn hG' hS' q' y Sf hSf Λ₁ Λ₂) :
    CV.IsLinkingNumber D.DA D.i D.j (r176l_ell hn hG' hS' q' y D) :=
  Classical.choose_spec (CV.exists_linkingNumber D.DA D.i D.j D.ij)

/-- `2ℓ` is the number of mask-`uv` survivors. -/
theorem r176l_two_mul_ell (D : r176l_SmoothData hn hG' hS' q' y Sf hSf Λ₁ Λ₂) :
    2 * r176l_ell hn hG' hS' q' y D =
      ((r176l_mixedSet hG'.crossingGeometry S' Sf q' Λ₁ Λ₂).card : ℤ) :=
  (r176l_ell_spec hn hG' hS' q' y D).trans D.mixed

/-- **The non-move port data from the black box and the three ledgers**: (14) in the form
`w₀ = w₁ + w₂ + |mixedSet|`, (13), and the two one-dissent shapes (12). -/
def r176l_portDataRest_of (D : r176l_SmoothData hn hG' hS' q' y Sf hSf Λ₁ Λ₂)
    (hw : CV.groupedWrithe hG q = CV.groupedWrithe hG' Λ₁ + CV.groupedWrithe hG' Λ₂ +
      ((r176l_mixedSet hG'.crossingGeometry S' Sf q' Λ₁ Λ₂).card : ℤ))
    (hrot : (CV.carrierR hn hG hS q : ℤ) = CV.carrierR hn hG' hSf Λ₁ + CV.carrierR hn hG' hSf Λ₂ + 1)
    (alt₁ : CV.UniformOrOneDissentCV (geoCornerPolygon hG'.crossingGeometry Sf Λ₁))
    (alt₂ : CV.UniformOrOneDissentCV (geoCornerPolygon hG'.crossingGeometry Sf Λ₂)) :
    s176_PortDataRest hn hG hG' hS hS' q q' y :=
  ⟨D.DA, D.smooth, D.two, D.i, D.j, D.ij, Sf, hSf, Λ₁, Λ₂, D.poly₁, D.poly₂,
    r176l_ell hn hG' hS' q' y D, r176l_ell_spec hn hG' hS' q' y D,
    by rw [hw, r176l_two_mul_ell hn hG' hS' q' y D], hrot, alt₁, alt₂⟩

include hn hSf in
/-- (12) for both children from their one-dissent shapes. -/
theorem r176l_alt_of_shape {σ : SignType} (hσ : σ ≠ 0)
    (h₁ : r176l_OneDissentShape (geoCornerPolygon hG'.crossingGeometry Sf Λ₁) σ)
    (h₂ : r176l_OneDissentShape (geoCornerPolygon hG'.crossingGeometry Sf Λ₂) σ) :
    CV.UniformOrOneDissentCV (geoCornerPolygon hG'.crossingGeometry Sf Λ₁) ∧
    CV.UniformOrOneDissentCV (geoCornerPolygon hG'.crossingGeometry Sf Λ₂) :=
  ⟨r176l_uniformOrOneDissent_of_shape (CV.carrierPolygon_cvRegular hn hG' hSf Λ₁) hσ h₁,
    r176l_uniformOrOneDissent_of_shape (CV.carrierPolygon_cvRegular hn hG' hSf Λ₂) hσ h₂⟩

/-- **(13) from the signed additivity and the shapes**: `R(D₊) = R(D₀)` (`GT_carrierR_eq`, consumed as
`hRR`), `rot(q') = rot(Λ₁) + rot(Λ₂) + σ` (turnlift (ii) with the opposite new turns, `hadd`), and the
one-dissent shapes give `σ·rot(Λᵢ) ≥ 1`, so the absolute values add. -/
theorem r176l_rot_ledger {σ : SignType} (hσ : σ ≠ 0)
    (hRR : CV.carrierR hn hG' hS' q' = CV.carrierR hn hG hS q)
    (hadd : CV.rot (geoCornerPolygon hG'.crossingGeometry S' q') (CV.carrierPolygon_cvRegular hn hG' hS' q') =
      CV.rot (geoCornerPolygon hG'.crossingGeometry Sf Λ₁) (CV.carrierPolygon_cvRegular hn hG' hSf Λ₁) +
      CV.rot (geoCornerPolygon hG'.crossingGeometry Sf Λ₂) (CV.carrierPolygon_cvRegular hn hG' hSf Λ₂) +
      (σ : ℤ))
    (h₁ : r176l_OneDissentShape (geoCornerPolygon hG'.crossingGeometry Sf Λ₁) σ)
    (h₂ : r176l_OneDissentShape (geoCornerPolygon hG'.crossingGeometry Sf Λ₂) σ) :
    (CV.carrierR hn hG hS q : ℤ) = CV.carrierR hn hG' hSf Λ₁ + CV.carrierR hn hG' hSf Λ₂ + 1 := by
  rw [← hRR, CV.carrierR_cast, CV.carrierR_cast, CV.carrierR_cast]
  exact r176l_abs_ledger hσ hadd
    (r176l_one_le_sign_mul_rot_of_shape (CV.carrierPolygon_cvRegular hn hG' hSf Λ₁) hσ h₁)
    (r176l_one_le_sign_mul_rot_of_shape (CV.carrierPolygon_cvRegular hn hG' hSf Λ₂) hσ h₂)

end L2Assembly

/-! ## §L3. The geometric realisation on the labelled corner (case 1)

The labelled corner of Site_176 §C: `j = {a, b} ∈ T` the selected corner, `u = {a, c}`, `v = {b, c}`
the two retained (unselected) local crossings of the carrier `q`, in the orientation of case 1
(`u` before `j` on `a`, `j` before `v` on `b`, `v` before `u` on `c`; the third order is FORCED by the
independence of `S_full`, §L3.4).  The full support is `Sf = T ∪ {u, v}`, its three children inside
`q` are the central triangle `Z = owner (j, a) = {(u, c), (j, a), (v, b)}` and the two clean outer
carriers `Λ₁ = owner (v, c)`, `Λ₂ = owner (u, a)`.

Decidability: the accepted insertion lemmas of SM/GeoCarrierCount.lean state `insert v.1 S` with the
classical instance `fun a b => Classical.propDecidable (a = b)`, while this file resolves
`DecidableEq (Crossing P)` to `RProof.instDecidableEqCrossing`; the two `insert`s are not
definitionally equal, so the supports are written with the explicit classical instance (`r176l_ins`). -/

section L3

variable (hn : 3 ≤ n) {P : LabelledTuple n} (hP : CrossingGeometry P)
  {T : Finset (Crossing P)} (hT : GeoIndependent hP T) (q : GeoComponent hP T)
  {a b c : ZMod n} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
  {j u v : Crossing P} (hj : j.val = {a, b}) (hu : u.val = {a, c}) (hv : v.val = {b, c})
  (hjT : j ∈ T) (huq : u ∈ geoCarrierCrossings hP T q) (hvq : v ∈ geoCarrierCrossings hP T q)

/-! ### L3.1 The six local visits and the full support -/

omit [NeZero n] in
/-- The classical `DecidableEq (Crossing P)` of the accepted insertion lemmas (reducible, so that
`insert` below is definitionally the library's `insert`). -/
abbrev r176l_decEq (P : LabelledTuple n) : DecidableEq (Crossing P) :=
  fun a b => Classical.propDecidable (a = b)

attribute [local instance 2000] r176l_decEq

omit [NeZero n] in
/-- `insert` with the classical instance. -/
abbrev r176l_ins (x : Crossing P) (S : Finset (Crossing P)) : Finset (Crossing P) := insert x S

omit [NeZero n] in
theorem r176l_mem_ins {x y : Crossing P} {S : Finset (Crossing P)} :
    y ∈ r176l_ins x S ↔ y = x ∨ y ∈ S := Finset.mem_insert

omit [NeZero n] in
/-- the visit of `u` on `a` -/
def r176l_ua {u : Crossing P} {a c : ZMod n} (hu : u.val = {a, c}) : Visit P := visitOn u a (s176_mem_left hu)
omit [NeZero n] in
/-- the visit of `u` on `c` -/
def r176l_uc {u : Crossing P} {a c : ZMod n} (hu : u.val = {a, c}) : Visit P := visitOn u c (s176_mem_right hu)

omit [NeZero n] in
theorem r176l_twin_ua {u : Crossing P} {a c : ZMod n} (hu : u.val = {a, c}) (hac : a ≠ c) :
    visitTwin (r176l_ua hu) = r176l_uc hu :=
  s176_visitTwin_eq hu hac _ _
omit [NeZero n] in
theorem r176l_twin_uc {u : Crossing P} {a c : ZMod n} (hu : u.val = {a, c}) (hac : a ≠ c) :
    visitTwin (r176l_uc hu) = r176l_ua hu :=
  s176_visitTwin_eq (s176_pair_comm' hu) hac.symm _ _
omit [NeZero n] in
theorem r176l_twin_vb {v : Crossing P} {b c : ZMod n} (hv : v.val = {b, c}) (hbc : b ≠ c) :
    visitTwin (visitOn v b (s176_mem_left hv)) = visitOn v c (s176_mem_right hv) :=
  s176_visitTwin_eq hv hbc _ _
omit [NeZero n] in
theorem r176l_twin_vc {v : Crossing P} {b c : ZMod n} (hv : v.val = {b, c}) (hbc : b ≠ c) :
    visitTwin (visitOn v c (s176_mem_right hv)) = visitOn v b (s176_mem_left hv) :=
  s176_visitTwin_eq (s176_pair_comm' hv) hbc.symm _ _

omit [NeZero n] in
/-- two visits of distinct crossings are distinct -/
theorem r176l_visit_ne_of_ne {x y : Crossing P} (hxy : x ≠ y) {ℓ m : ZMod n} (hx : ℓ ∈ x.val) (hy : m ∈ y.val) :
    visitOn x ℓ hx ≠ visitOn y m hy := fun h => hxy (congrArg (fun w : Visit P => w.1) h)

omit [NeZero n] in
/-- two visits of one crossing on distinct edges are distinct -/
theorem r176l_visit_ne_of_edge_ne {x : Crossing P} {ℓ m : ZMod n} (hℓm : ℓ ≠ m) (hx : ℓ ∈ x.val) (hy : m ∈ x.val) :
    visitOn x ℓ hx ≠ visitOn x m hy := fun h => hℓm (congrArg (fun w : Visit P => w.2.val) h)

/-- the first insertion `S₁ = T ∪ {u}` -/
abbrev r176l_S1 (T : Finset (Crossing P)) (u : Crossing P) : Finset (Crossing P) := r176l_ins u T

/-- The full support `S_full = T ∪ {u, v}`. -/
abbrev r176l_Sf (T : Finset (Crossing P)) (u v : Crossing P) : Finset (Crossing P) := r176l_ins v (r176l_ins u T)

omit [NeZero n] in
theorem r176l_indep_mono {S S' : Finset (Crossing P)} (hS' : GeoIndependent hP S') (h : S ⊆ S') :
    GeoIndependent hP S := fun x hx y hy hxy => hS' x (h hx) y (h hy) hxy

omit [NeZero n] in
theorem r176l_subset_S1 (T : Finset (Crossing P)) (u : Crossing P) : T ⊆ r176l_S1 T u :=
  fun _ h => r176l_mem_ins.mpr (Or.inr h)
omit [NeZero n] in
theorem r176l_S1_subset_Sf (T : Finset (Crossing P)) (u v : Crossing P) : r176l_S1 T u ⊆ r176l_Sf T u v :=
  fun _ h => r176l_mem_ins.mpr (Or.inr h)
omit [NeZero n] in
theorem r176l_subset_Sf (T : Finset (Crossing P)) (u v : Crossing P) : T ⊆ r176l_Sf T u v :=
  (r176l_subset_S1 T u).trans (r176l_S1_subset_Sf T u v)
omit [NeZero n] in
theorem r176l_u_mem_S1 (T : Finset (Crossing P)) (u : Crossing P) : u ∈ r176l_S1 T u :=
  r176l_mem_ins.mpr (Or.inl rfl)
omit [NeZero n] in
theorem r176l_u_mem_Sf (T : Finset (Crossing P)) (u v : Crossing P) : u ∈ r176l_Sf T u v :=
  r176l_S1_subset_Sf T u v (r176l_u_mem_S1 T u)
omit [NeZero n] in
theorem r176l_v_mem_Sf (T : Finset (Crossing P)) (u v : Crossing P) : v ∈ r176l_Sf T u v :=
  r176l_mem_ins.mpr (Or.inl rfl)

/-! ### L3.2 Distinctness and membership -/

include huq in
theorem r176l_u_not_mem : u ∉ T := ((mem_geoCarrierCrossings hP T q u).mp huq).1
include hvq in
theorem r176l_v_not_mem : v ∉ T := ((mem_geoCarrierCrossings hP T q v).mp hvq).1

omit [NeZero n] in
include hac hbc hj hu in
theorem r176l_j_ne_u : j ≠ u := s176_ne_of_supports hj hu hac hbc
omit [NeZero n] in
include hac hbc hj hv in
theorem r176l_j_ne_v : j ≠ v := s176_ne_of_supports (s176_pair_comm' hj) hv hbc hac
omit [NeZero n] in
include hab hbc hu hv in
theorem r176l_u_ne_v : u ≠ v := s176_ne_of_supports (s176_pair_comm' hu) (s176_pair_comm' hv) hbc.symm hab

include hab hbc hu hv hvq in
theorem r176l_v_not_mem_S1 : v ∉ r176l_S1 T u := by
  intro h
  rcases r176l_mem_ins.mp h with h | h
  · exact r176l_u_ne_v hab hbc hu hv h.symm
  · exact r176l_v_not_mem hP q hvq h

include huq in
/-- the retained visits of `u` are owned by `q` -/
theorem r176l_owner_ua : geoOwner hP T (Sum.inr (r176l_ua hu)) = q :=
  ((mem_geoCarrierCrossings hP T q u).mp huq).2 _ rfl
include huq in
theorem r176l_owner_uc : geoOwner hP T (Sum.inr (r176l_uc hu)) = q :=
  ((mem_geoCarrierCrossings hP T q u).mp huq).2 _ rfl
include hvq in
theorem r176l_owner_vb : geoOwner hP T (Sum.inr (visitOn v b (s176_mem_left hv))) = q :=
  ((mem_geoCarrierCrossings hP T q v).mp hvq).2 _ rfl
include hvq in
theorem r176l_owner_vc : geoOwner hP T (Sum.inr (visitOn v c (s176_mem_right hv))) = q :=
  ((mem_geoCarrierCrossings hP T q v).mp hvq).2 _ rfl

/-! ### L3.3 The successor facts of case 1 -/

section Case1

variable (hρa : geoMarkSuccessor hP (Sum.inr (r176l_ua hu)) = Sum.inr (visitOn j a (s176_mem_left hj)))
  (hρb : geoMarkSuccessor hP (Sum.inr (visitOn j b (s176_mem_right hj))) = Sum.inr (visitOn v b (s176_mem_left hv)))
  (hρc : geoMarkSuccessor hP (Sum.inr (visitOn v c (s176_mem_right hv))) = Sum.inr (r176l_uc hu))

include huq hρa in
/-- `ρ_T (u, a) = (j, a)` -/
theorem r176l_succT_ua :
    geoSmoothingSuccessor hP T (Sum.inr (r176l_ua hu)) = Sum.inr (visitOn j a (s176_mem_left hj)) := by
  rw [geoSmoothingSuccessor_visit_of_not_mem hP T _ (r176l_u_not_mem hP q huq)]
  exact hρa

include hab hjT hρb in
/-- `ρ_T (j, a) = (v, b)` -/
theorem r176l_succT_ja :
    geoSmoothingSuccessor hP T (Sum.inr (visitOn j a (s176_mem_left hj))) = Sum.inr (visitOn v b (s176_mem_left hv)) := by
  rw [geoSmoothingSuccessor_visit_of_mem hP T _ hjT, s176_visitTwin_eq hj hab _ _]
  exact hρb

include hvq hρc in
/-- `ρ_T (v, c) = (u, c)` -/
theorem r176l_succT_vc :
    geoSmoothingSuccessor hP T (Sum.inr (visitOn v c (s176_mem_right hv))) = Sum.inr (r176l_uc hu) := by
  rw [geoSmoothingSuccessor_visit_of_not_mem hP T _ (r176l_v_not_mem hP q hvq)]
  exact hρc

include hac hj huq hρa in
/-- `ρ_{S₁} (u, c) = (j, a)` -/
theorem r176l_succS1_uc :
    geoSmoothingSuccessor hP (r176l_S1 T u) (Sum.inr (r176l_uc hu)) = Sum.inr (visitOn j a (s176_mem_left hj)) := by
  have h := geoSmoothingSuccessor_insert_twin hP T (r176l_ua hu) (r176l_u_not_mem hP q huq)
  rw [r176l_twin_ua hu hac] at h
  exact h.trans (r176l_succT_ua hP q hj hu huq hρa)

include hab hac hbc hu hjT huq hρb in
/-- `ρ_{S₁} (j, a) = (v, b)` -/
theorem r176l_succS1_ja :
    geoSmoothingSuccessor hP (r176l_S1 T u) (Sum.inr (visitOn j a (s176_mem_left hj))) =
      Sum.inr (visitOn v b (s176_mem_left hv)) := by
  have hju : j ≠ u := r176l_j_ne_u hac hbc hj hu
  have h := geoSmoothingSuccessor_insert_other hP T (r176l_ua hu) (r176l_u_not_mem hP q huq)
    (Sum.inr (visitOn j a (s176_mem_left hj)))
    (fun e => r176l_visit_ne_of_ne hju _ _ (Sum.inr.inj e))
    (by rw [r176l_twin_ua hu hac]; exact fun e => r176l_visit_ne_of_ne hju _ _ (Sum.inr.inj e))
  exact h.trans (r176l_succT_ja hP hab hj hv hjT hρb)

include hab hac hbc huq hvq hρc in
/-- `ρ_{S₁} (v, c) = (u, c)` -/
theorem r176l_succS1_vc :
    geoSmoothingSuccessor hP (r176l_S1 T u) (Sum.inr (visitOn v c (s176_mem_right hv))) = Sum.inr (r176l_uc hu) := by
  have huv : u ≠ v := r176l_u_ne_v hab hbc hu hv
  have h := geoSmoothingSuccessor_insert_other hP T (r176l_ua hu) (r176l_u_not_mem hP q huq)
    (Sum.inr (visitOn v c (s176_mem_right hv)))
    (fun e => r176l_visit_ne_of_ne huv.symm _ _ (Sum.inr.inj e))
    (by rw [r176l_twin_ua hu hac]; exact fun e => r176l_visit_ne_of_ne huv.symm _ _ (Sum.inr.inj e))
  exact h.trans (r176l_succT_vc hP q hu hv hvq hρc)

include hab hac hbc hjT huq hvq hρa hρb hρc in
/-- **The central triangle is a `ρ_{Sf}`-3-cycle**: `(u, c) → (j, a) → (v, b) → (u, c)`. -/
theorem r176l_succSf_cycle :
    geoSmoothingSuccessor hP (r176l_Sf T u v) (Sum.inr (r176l_uc hu)) = Sum.inr (visitOn j a (s176_mem_left hj)) ∧
    geoSmoothingSuccessor hP (r176l_Sf T u v) (Sum.inr (visitOn j a (s176_mem_left hj))) =
      Sum.inr (visitOn v b (s176_mem_left hv)) ∧
    geoSmoothingSuccessor hP (r176l_Sf T u v) (Sum.inr (visitOn v b (s176_mem_left hv))) = Sum.inr (r176l_uc hu) := by
  have hjv : j ≠ v := r176l_j_ne_v hac hbc hj hv
  have huv : u ≠ v := r176l_u_ne_v hab hbc hu hv
  have hvS1 : v ∉ r176l_S1 T u := r176l_v_not_mem_S1 hP q hab hbc hu hv hvq
  refine ⟨?_, ?_, ?_⟩
  · have h := geoSmoothingSuccessor_insert_other hP (r176l_S1 T u) (visitOn v b (s176_mem_left hv)) hvS1
      (Sum.inr (r176l_uc hu)) (fun e => r176l_visit_ne_of_ne huv _ _ (Sum.inr.inj e))
      (by rw [r176l_twin_vb hv hbc]; exact fun e => r176l_visit_ne_of_ne huv _ _ (Sum.inr.inj e))
    exact h.trans (r176l_succS1_uc hP q hac hj hu huq hρa)
  · have h := geoSmoothingSuccessor_insert_other hP (r176l_S1 T u) (visitOn v b (s176_mem_left hv)) hvS1
      (Sum.inr (visitOn j a (s176_mem_left hj))) (fun e => r176l_visit_ne_of_ne hjv _ _ (Sum.inr.inj e))
      (by rw [r176l_twin_vb hv hbc]; exact fun e => r176l_visit_ne_of_ne hjv _ _ (Sum.inr.inj e))
    exact h.trans (r176l_succS1_ja hP q hab hac hbc hj hu hv hjT huq hρb)
  · have h := geoSmoothingSuccessor_insert_visit hP (r176l_S1 T u) (visitOn v b (s176_mem_left hv)) hvS1
    rw [r176l_twin_vb hv hbc] at h
    exact h.trans (r176l_succS1_vc hP q hab hac hbc hu hv huq hvq hρc)

end Case1

/-! ### L3.4 The children of the affected carrier in the full support -/

omit [NeZero n] in
/-- Membership in a 3-cycle of a permutation: the `SameCycle` class of `x` under `f` with
`f x = y`, `f y = z`, `f z = x` is `{x, y, z}`. -/
theorem r176l_sameCycle_three {α : Type*} [Fintype α] (f : Equiv.Perm α) {x y z : α}
    (hx : f x = y) (hy : f y = z) (hz : f z = x) {m : α} (h : f.SameCycle x m) :
    m = x ∨ m = y ∨ m = z := by
  obtain ⟨k, hk⟩ := h.exists_nat_pow_eq
  rw [← hk]
  clear hk h
  induction k with
  | zero => left; rfl
  | succ k ih =>
    rw [pow_succ', Equiv.Perm.mul_apply]
    rcases ih with h | h | h <;> rw [h]
    · right; left; exact hx
    · right; right; exact hy
    · left; exact hz

/-- **The two-child split** (the exact split of `geoSmoothingSuccessor_insert_child_data`, read as a
disjunction): inserting a crossing `w` whose two visits lie on one carrier of `T` sends every mark of
that carrier to the carrier of `w` or to the carrier of its twin. -/
theorem r176l_owner_insert_or (T : Finset (Crossing P)) (hI : GeoInheritsMarkOrder hP T) (w : Visit P)
    (hw : w.1 ∉ T) (hc : geoOwner hP T (Sum.inr w) = geoOwner hP T (Sum.inr (visitTwin w))) (m : Mark P)
    (hm : geoOwner hP T m = geoOwner hP T (Sum.inr w)) :
    geoOwner hP (insert w.1 T) m = geoOwner hP (insert w.1 T) (Sum.inr w) ∨
    geoOwner hP (insert w.1 T) m = geoOwner hP (insert w.1 T) (Sum.inr (visitTwin w)) := by
  obtain ⟨k, A, B, hrot, -, -, -, hleft, hright, -, -⟩ :=
    geoSmoothingSuccessor_insert_child_data hP T hI w hw hc
  have hmem : m ∈ (geoMarkList hP).rotate k := List.mem_rotate.mpr (mem_geoMarkList hP m)
  rw [hrot] at hmem
  simp only [List.mem_cons, List.mem_append] at hmem
  rcases hmem with h | h | h | h
  · left; rw [h]
  · right
    rw [hright]
    simp only [List.mem_cons, List.mem_filter, decide_eq_true_eq]
    exact Or.inr ⟨h, hm⟩
  · right; rw [h]
  · left
    rw [hleft]
    simp only [List.mem_cons, List.mem_filter, decide_eq_true_eq]
    exact Or.inr ⟨h, hm⟩

section Children

variable (hρa : geoMarkSuccessor hP (Sum.inr (r176l_ua hu)) = Sum.inr (visitOn j a (s176_mem_left hj)))
  (hρb : geoMarkSuccessor hP (Sum.inr (visitOn j b (s176_mem_right hj))) = Sum.inr (visitOn v b (s176_mem_left hv)))
  (hρc : geoMarkSuccessor hP (Sum.inr (visitOn v c (s176_mem_right hv))) = Sum.inr (r176l_uc hu))
  (hSf : GeoIndependent hP (r176l_Sf T u v))

/-- the central triangle `Z = owner_{Sf} (j, a)` -/
abbrev r176l_Z (T : Finset (Crossing P)) (u v : Crossing P) {j : Crossing P} {a b : ZMod n} (hj : j.val = {a, b}) :
    GeoComponent hP (r176l_Sf T u v) :=
  geoOwner hP (r176l_Sf T u v) (Sum.inr (visitOn j a (s176_mem_left hj)))
/-- the clean outer carrier `Λ₁ = owner_{Sf} (v, c)` -/
abbrev r176l_L1 (T : Finset (Crossing P)) (u : Crossing P) {v : Crossing P} {b c : ZMod n} (hv : v.val = {b, c}) :
    GeoComponent hP (r176l_Sf T u v) :=
  geoOwner hP (r176l_Sf T u v) (Sum.inr (visitOn v c (s176_mem_right hv)))
/-- the clean outer carrier `Λ₂ = owner_{Sf} (u, a)` -/
abbrev r176l_L2 (T : Finset (Crossing P)) (v : Crossing P) {u : Crossing P} {a c : ZMod n} (hu : u.val = {a, c}) :
    GeoComponent hP (r176l_Sf T u v) :=
  geoOwner hP (r176l_Sf T u v) (Sum.inr (r176l_ua hu))

omit [NeZero n] in
include hSf in
theorem r176l_indep_S1 : GeoIndependent hP (r176l_S1 T u) :=
  r176l_indep_mono hP hSf (r176l_S1_subset_Sf T u v)

include hab hbc hu hvq hSf in
/-- in `S₁ = T ∪ {u}` the two visits of `v` still share a carrier -/
theorem r176l_owner_S1_vb_vc :
    geoOwner hP (r176l_S1 T u) (Sum.inr (visitOn v b (s176_mem_left hv))) =
      geoOwner hP (r176l_S1 T u) (Sum.inr (visitOn v c (s176_mem_right hv))) := by
  have h := geoIndependent_remaining_pair_owners hP hSf (r176l_S1 T u) (r176l_S1_subset_Sf T u v)
    (visitOn v b (s176_mem_left hv)) (r176l_v_mem_Sf T u v) (r176l_v_not_mem_S1 hP q hab hbc hu hv hvq)
  rwa [r176l_twin_vb hv hbc] at h

include hac hSf in
/-- in `S₁` the two visits of `u` are separated -/
theorem r176l_owner_S1_ua_ne_uc :
    geoOwner hP (r176l_S1 T u) (Sum.inr (r176l_ua hu)) ≠ geoOwner hP (r176l_S1 T u) (Sum.inr (r176l_uc hu)) := by
  have h := geo_selected_visits_separated hP (r176l_indep_S1 hP hSf) (r176l_ua hu) (r176l_u_mem_S1 T u)
  rwa [r176l_twin_ua hu hac] at h

include hac huq hρa in
/-- in `S₁`, `(u, c)`, `(j, a)`, `(v, b)` share a carrier -/
theorem r176l_owner_S1_uc_ja :
    geoOwner hP (r176l_S1 T u) (Sum.inr (r176l_uc hu)) = geoOwner hP (r176l_S1 T u) (Sum.inr (visitOn j a (s176_mem_left hj))) := by
  rw [← geoOwner_successor hP (r176l_S1 T u) (Sum.inr (r176l_uc hu)), r176l_succS1_uc hP q hac hj hu huq hρa]
include hab hac hbc hu hjT huq hρb in
theorem r176l_owner_S1_ja_vb :
    geoOwner hP (r176l_S1 T u) (Sum.inr (visitOn j a (s176_mem_left hj))) =
      geoOwner hP (r176l_S1 T u) (Sum.inr (visitOn v b (s176_mem_left hv))) := by
  rw [← geoOwner_successor hP (r176l_S1 T u) (Sum.inr (visitOn j a (s176_mem_left hj))),
    r176l_succS1_ja hP q hab hac hbc hj hu hv hjT huq hρb]

include hab hac hbc hjT huq hvq hρa hρb hSf in
/-- `(u, a)` and `(v, c)` are separated in `S₁` -/
theorem r176l_owner_S1_ua_ne_vc :
    geoOwner hP (r176l_S1 T u) (Sum.inr (r176l_ua hu)) ≠
      geoOwner hP (r176l_S1 T u) (Sum.inr (visitOn v c (s176_mem_right hv))) := by
  rw [← r176l_owner_S1_vb_vc hP q hab hbc hu hv hvq hSf, ← r176l_owner_S1_ja_vb hP q hab hac hbc hj hu hv hjT huq hρb,
    ← r176l_owner_S1_uc_ja hP q hac hj hu huq hρa]
  exact r176l_owner_S1_ua_ne_uc hP hac hu hSf

include hab hac hbc hjT huq hvq hρa hρb hSf in
/-- **The carrier of `(u, a)` is unaffected by the second insertion**: a mark lies on `Λ₂` iff it lies
on the `S₁`-carrier of `(u, a)`. -/
theorem r176l_owner_Sf_L2_iff (z : Mark P) :
    geoOwner hP (r176l_Sf T u v) z = r176l_L2 hP T v hu ↔
      geoOwner hP (r176l_S1 T u) z = geoOwner hP (r176l_S1 T u) (Sum.inr (r176l_ua hu)) := by
  have hc := r176l_owner_S1_vb_vc hP q hab hbc hu hv hvq hSf
  rw [← r176l_twin_vb hv hbc] at hc
  have hne : geoOwner hP (r176l_S1 T u) (Sum.inr (r176l_ua hu)) ≠
      geoOwner hP (r176l_S1 T u) (Sum.inr (visitOn v b (s176_mem_left hv))) := by
    rw [r176l_owner_S1_vb_vc hP q hab hbc hu hv hvq hSf]
    exact r176l_owner_S1_ua_ne_vc hP q hab hac hbc hj hu hv hjT huq hvq hρa hρb hSf
  exact geoOwner_insert_iff_of_unaffected hP (r176l_S1 T u) (visitOn v b (s176_mem_left hv))
    (r176l_v_not_mem_S1 hP q hab hbc hu hv hvq) hc _ hne (Sum.inr (r176l_ua hu)) rfl z

include hab hac hbc hjT huq hvq hρa hρb hρc in
/-- the marks of the central triangle: `Z = owner (u, c) = owner (j, a) = owner (v, b)` -/
theorem r176l_Z_eq :
    geoOwner hP (r176l_Sf T u v) (Sum.inr (r176l_uc hu)) = r176l_Z hP T u v hj ∧
    geoOwner hP (r176l_Sf T u v) (Sum.inr (visitOn v b (s176_mem_left hv))) = r176l_Z hP T u v hj := by
  obtain ⟨h1, h2, -⟩ := r176l_succSf_cycle hP q hab hac hbc hj hu hv hjT huq hvq hρa hρb hρc
  constructor
  · rw [← geoOwner_successor hP (r176l_Sf T u v) (Sum.inr (r176l_uc hu)), h1]
  · rw [show r176l_Z hP T u v hj = geoOwner hP (r176l_Sf T u v) (Sum.inr (visitOn j a (s176_mem_left hj))) from rfl,
      ← geoOwner_successor hP (r176l_Sf T u v) (Sum.inr (visitOn j a (s176_mem_left hj))), h2]

include hab hac hbc hjT huq hvq hρa hρb hρc in
/-- **The central triangle owns exactly its three corner marks.** -/
theorem r176l_mem_Z (m : Mark P) (h : geoOwner hP (r176l_Sf T u v) m = r176l_Z hP T u v hj) :
    m = Sum.inr (r176l_uc hu) ∨ m = Sum.inr (visitOn j a (s176_mem_left hj)) ∨
      m = Sum.inr (visitOn v b (s176_mem_left hv)) := by
  obtain ⟨h1, h2, h3⟩ := r176l_succSf_cycle hP q hab hac hbc hj hu hv hjT huq hvq hρa hρb hρc
  have hZ := (r176l_Z_eq hP q hab hac hbc hj hu hv hjT huq hvq hρa hρb hρc).1
  have hsc : (geoSmoothingSuccessor hP (r176l_Sf T u v)).SameCycle (Sum.inr (r176l_uc hu)) m :=
    (geoOwner_eq_iff hP (r176l_Sf T u v) _ _).mp (hZ.trans h.symm)
  exact r176l_sameCycle_three _ h1 h2 h3 hsc

include hab hac hbc hjT huq hvq hρa hρb hSf in
/-- `Λ₁ ≠ Λ₂` -/
theorem r176l_L1_ne_L2 : r176l_L1 hP T u hv ≠ r176l_L2 hP T v hu := by
  intro h
  exact r176l_owner_S1_ua_ne_vc hP q hab hac hbc hj hu hv hjT huq hvq hρa hρb hSf
    ((r176l_owner_Sf_L2_iff hP q hab hac hbc hj hu hv hjT huq hvq hρa hρb hSf _).mp h).symm

include hab hac hbc hjT huq hvq hρa hρb hρc hSf in
/-- `Λ₁ ≠ Z` -/
theorem r176l_L1_ne_Z : r176l_L1 hP T u hv ≠ r176l_Z hP T u v hj := by
  intro h
  have hsep := geo_selected_visits_separated hP hSf (visitOn v b (s176_mem_left hv)) (r176l_v_mem_Sf T u v)
  rw [r176l_twin_vb hv hbc, (r176l_Z_eq hP q hab hac hbc hj hu hv hjT huq hvq hρa hρb hρc).2] at hsep
  exact hsep h.symm

include hab hac hbc hjT huq hvq hρa hρb hρc hSf in
/-- `Λ₂ ≠ Z` -/
theorem r176l_L2_ne_Z : r176l_L2 hP T v hu ≠ r176l_Z hP T u v hj := by
  intro h
  have hsep := geo_selected_visits_separated hP hSf (r176l_ua hu) (r176l_u_mem_Sf T u v)
  rw [r176l_twin_ua hu hac, (r176l_Z_eq hP q hab hac hbc hj hu hv hjT huq hvq hρa hρb hρc).1] at hsep
  exact hsep h

include hvq hSf in
theorem r176l_sub_L1 (m : Mark P) (h : geoOwner hP (r176l_Sf T u v) m = r176l_L1 hP T u hv) :
    geoOwner hP T m = q :=
  (geoOwner_eq_of_subset hP hSf (r176l_subset_Sf T u v) m _ h).trans (r176l_owner_vc hP q hv hvq)

include huq hSf in
theorem r176l_sub_L2 (m : Mark P) (h : geoOwner hP (r176l_Sf T u v) m = r176l_L2 hP T v hu) :
    geoOwner hP T m = q :=
  (geoOwner_eq_of_subset hP hSf (r176l_subset_Sf T u v) m _ h).trans (r176l_owner_ua hP q hu huq)

include hT hab hac hbc hjT huq hvq hρa hρb hρc hSf in
/-- **Every mark of `q` lies on `Λ₁`, `Λ₂` or `Z`** (the two-step split). -/
theorem r176l_owner_Sf_cases (m : Mark P) (hm : geoOwner hP T m = q) :
    geoOwner hP (r176l_Sf T u v) m = r176l_L1 hP T u hv ∨
    geoOwner hP (r176l_Sf T u v) m = r176l_L2 hP T v hu ∨
    geoOwner hP (r176l_Sf T u v) m = r176l_Z hP T u v hj := by
  have hI_T := geoInheritsMarkOrder_of_independent hP hT
  have hI_S1 := geoInheritsMarkOrder_of_independent hP (r176l_indep_S1 hP hSf)
  have hcT : geoOwner hP T (Sum.inr (r176l_ua hu)) = geoOwner hP T (Sum.inr (visitTwin (r176l_ua hu))) := by
    rw [r176l_twin_ua hu hac, r176l_owner_ua hP q hu huq, r176l_owner_uc hP q hu huq]
  have hstep1 := r176l_owner_insert_or hP T hI_T (r176l_ua hu) (r176l_u_not_mem hP q huq) hcT m
    (by rw [hm, r176l_owner_ua hP q hu huq])
  rw [r176l_twin_ua hu hac] at hstep1
  have hstep1' : geoOwner hP (r176l_S1 T u) m = geoOwner hP (r176l_S1 T u) (Sum.inr (r176l_ua hu)) ∨
      geoOwner hP (r176l_S1 T u) m = geoOwner hP (r176l_S1 T u) (Sum.inr (r176l_uc hu)) := hstep1
  rcases hstep1' with h1 | h1
  · right; left
    exact (r176l_owner_Sf_L2_iff hP q hab hac hbc hj hu hv hjT huq hvq hρa hρb hSf m).mpr h1
  · have hcS1 := r176l_owner_S1_vb_vc hP q hab hbc hu hv hvq hSf
    rw [← r176l_twin_vb hv hbc] at hcS1
    have hm1 : geoOwner hP (r176l_S1 T u) m = geoOwner hP (r176l_S1 T u) (Sum.inr (visitOn v b (s176_mem_left hv))) := by
      rw [h1, r176l_owner_S1_uc_ja hP q hac hj hu huq hρa,
        r176l_owner_S1_ja_vb hP q hab hac hbc hj hu hv hjT huq hρb]
    have hstep2 := r176l_owner_insert_or hP (r176l_S1 T u) hI_S1 (visitOn v b (s176_mem_left hv))
      (r176l_v_not_mem_S1 hP q hab hbc hu hv hvq) hcS1 m hm1
    rw [r176l_twin_vb hv hbc] at hstep2
    have hstep2' : geoOwner hP (r176l_Sf T u v) m = geoOwner hP (r176l_Sf T u v) (Sum.inr (visitOn v b (s176_mem_left hv))) ∨
        geoOwner hP (r176l_Sf T u v) m = geoOwner hP (r176l_Sf T u v) (Sum.inr (visitOn v c (s176_mem_right hv))) := hstep2
    rcases hstep2' with h2 | h2
    · right; right
      exact h2.trans (r176l_Z_eq hP q hab hac hbc hj hu hv hjT huq hvq hρa hρb hρc).2
    · left; exact h2

include hT hab hac hbc hjT huq hvq hρa hρb hρc hSf in
/-- **The children of the affected carrier** (case 1): `Λ₁ = owner (v, c)`, `Λ₂ = owner (u, a)`. -/
theorem r176l_children_case1 : r176l_Children hP T (r176l_Sf T u v) q (r176l_L1 hP T u hv) (r176l_L2 hP T v hu) where
  sub₁ m h := r176l_sub_L1 hP q hv hvq hSf m h
  sub₂ m h := r176l_sub_L2 hP q hu huq hSf m h
  ne := r176l_L1_ne_L2 hP q hab hac hbc hj hu hv hjT huq hvq hρa hρb hSf
  cover w hw hq := by
    rcases r176l_owner_Sf_cases hP hT q hab hac hbc hj hu hv hjT huq hvq hρa hρb hρc hSf (Sum.inr w) hq with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exfalso
      rcases r176l_mem_Z hP q hab hac hbc hj hu hv hjT huq hvq hρa hρb hρc _ h with e | e | e
      · exact hw (by rw [Sum.inr.inj e]; exact r176l_u_mem_Sf T u v)
      · exact hw (by rw [Sum.inr.inj e]; exact r176l_subset_Sf T u v hjT)
      · exact hw (by rw [Sum.inr.inj e]; exact r176l_v_mem_Sf T u v)

end Children


/-! ### L3.5 Corner marks, corner sets and the turn/angle at a corner mark -/

section CornerMarks

variable {S : Finset (Crossing P)}

open scoped Classical in
/-- The corner marks of a carrier `r` of `S` as a finset: the marks it owns that are true corners. -/
def r176l_cornerSet (S : Finset (Crossing P)) (r : GeoComponent hP S) : Finset (Mark P) :=
  Finset.univ.filter fun m => geoOwner hP S m = r ∧ IsTrueCorner S m

theorem r176l_mem_cornerSet {r : GeoComponent hP S} {m : Mark P} :
    m ∈ r176l_cornerSet hP S r ↔ geoOwner hP S m = r ∧ IsTrueCorner S m := by
  classical
  simp only [r176l_cornerSet, Finset.mem_filter, Finset.mem_univ, true_and]

/-- **Summing over the corner indices = summing over the corner marks** (`geoCornerMark` is a bijection
`ZMod c(r) ≃ cornerSet r`). -/
theorem r176l_sum_cornerMark (r : GeoComponent hP S) (f : Mark P → ℝ) :
    ∑ k : ZMod (geoCornerCount hP S r), f (geoCornerMark hP S r k) = ∑ m ∈ r176l_cornerSet hP S r, f m := by
  refine Finset.sum_nbij (geoCornerMark hP S r) ?_ ?_ ?_ ?_
  · intro k _
    exact (r176l_mem_cornerSet hP).mpr (geoCornerMark_mem hP S r k)
  · intro k _ k' _ h
    exact geoCornerMark_injective hP S r h
  · intro m hm
    obtain ⟨hown, hc⟩ := (r176l_mem_cornerSet hP).mp hm
    obtain ⟨k, hk⟩ := geoCornerMark_exists_of_owner hP S r m hown hc
    exact ⟨k, Finset.mem_univ _, hk⟩
  · intro k _
    rfl

/-- The number of corners is the size of the corner set. -/
theorem r176l_cornerCount_eq_card (r : GeoComponent hP S) :
    geoCornerCount hP S r = (r176l_cornerSet hP S r).card := by
  have h := r176l_sum_cornerMark hP r (fun _ => (1 : ℝ))
  simp only [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul, mul_one] at h
  exact_mod_cast h

/-- The angle at a corner mark `m` of a carrier of `S`: the principal angle from the incoming original
edge to the outgoing slot's edge. -/
def r176l_tau (S : Finset (Crossing P)) (m : Mark P) : ℝ :=
  principalAngle (edge P (geoInEdge hP m)) (edge P (geoOutSlot hP S m).1)

include hn in
/-- **The principal turn of the corner polygon at `k` is the angle at its corner mark**
(`geoCornerPolygon_edge_pred_smul`, `geoCornerPolygon_edge_smul`, scale invariance of the principal angle). -/
theorem r176l_principalTurn_eq_tau (hS : GeoIndependent hP S) (r : GeoComponent hP S)
    (k : ZMod (geoCornerCount hP S r)) :
    CV.principalTurn (geoCornerPolygon hP S r) k = r176l_tau hP S (geoCornerMark hP S r k) := by
  obtain ⟨c₁, hc₁, he₁⟩ := geoCornerPolygon_edge_pred_smul hn hP hS r k
  obtain ⟨c₂, hc₂, he₂⟩ := geoCornerPolygon_edge_smul hn hP hS r k
  show principalAngle (edge (geoCornerPolygon hP S r) (k - 1)) (edge (geoCornerPolygon hP S r) k) = _
  rw [he₁, he₂, principalAngle_smul hc₁ hc₂]
  rfl

include hn in
/-- the sum of the principal turns of a carrier's corner polygon, as a sum over its corner marks -/
theorem r176l_sum_principalTurn (hS : GeoIndependent hP S) (r : GeoComponent hP S) :
    ∑ k, CV.principalTurn (geoCornerPolygon hP S r) k = ∑ m ∈ r176l_cornerSet hP S r, r176l_tau hP S m := by
  rw [← r176l_sum_cornerMark hP r (r176l_tau hP S)]
  exact Finset.sum_congr rfl fun k _ => r176l_principalTurn_eq_tau hn hP hS r k

/-- `principalAngle (-u) (-v) = principalAngle u v` (copy of the accepted `SM.principalAngle_neg_neg`,
SM/ZeroRotationSeed.lean, not imported). -/
theorem r176l_principalAngle_neg_neg (u v : Plane) : principalAngle (-u) (-v) = principalAngle u v := by
  simp only [principalAngle, cornerRotor, planeComplex_neg, star_neg, neg_mul_neg]

omit [NeZero n] in
/-- antisymmetry of the principal angle on a regular pair -/
theorem r176l_principalAngle_swap {u v : Plane} (h : RegularPair u v) :
    principalAngle v u = -principalAngle u v := by
  rw [← r176l_principalAngle_neg_neg v u]
  exact principalAngle_reverse h

omit [NeZero n] in
/-- a transverse pair is regular -/
theorem r176l_regularPair_of_det {u v : Plane} (h : det u v ≠ 0) : RegularPair u v := by
  unfold RegularPair
  refine ⟨?_, ?_, ?_⟩
  · intro hu; apply h; rw [hu]; simp [det]
  · intro hv; apply h; rw [hv]; simp [det]
  · rintro ⟨r, -, hr⟩
    apply h
    rw [hr]
    exact det_smul_self u r

omit [NeZero n] in
theorem r176l_det_self (u : Plane) : det u u = 0 := by
  have := det_smul_self u 1
  rwa [one_smul] at this

omit [NeZero n] in
theorem r176l_det_neg_right (u w : Plane) : det u (-w) = -det u w := by
  have := det_smul_right u w (-1)
  rwa [neg_one_smul, neg_one_mul] at this

omit [NeZero n] in
theorem r176l_det_neg_left (u w : Plane) : det (-u) w = -det u w := by
  have := det_smul_left u w (-1)
  rwa [neg_one_smul, neg_one_mul] at this

omit [NeZero n] in
theorem r176l_det_sub_right (u v w : Plane) : det u (v - w) = det u v - det u w := by
  rw [sub_eq_add_neg, det_add_right, r176l_det_neg_right]
  ring

omit [NeZero n] in
theorem r176l_det_sub_left (u v w : Plane) : det (u - v) w = det u w - det v w := by
  rw [det_swap, r176l_det_sub_right, det_swap u w, det_swap v w]
  ring

/-! ### the out-slot edges at the local marks -/

theorem r176l_outSlot_visit_mem {w : Visit P} (hw : w.1 ∈ S) :
    (geoOutSlot hP S (Sum.inr w)).1 = (visitTwin w).2.val := geoOutSlot_selected hP S w hw

theorem r176l_outSlot_visit_not_mem {w : Visit P} (hw : w.1 ∉ S) :
    (geoOutSlot hP S (Sum.inr w)).1 = w.2.val := by
  rw [geoOutSlot_unselected hP S w hw]; rfl

/-- the out-slot edge of a mark whose crossing is not one of the inserted ones is unchanged by the
insertion -/
theorem r176l_outSlot_eq_of_iff {S S' : Finset (Crossing P)} (m : Mark P)
    (h : ∀ w : Visit P, m = Sum.inr w → (w.1 ∈ S' ↔ w.1 ∈ S)) :
    (geoOutSlot hP S' m).1 = (geoOutSlot hP S m).1 := by
  cases m with
  | inl i => rfl
  | inr w =>
    by_cases hw : w.1 ∈ S
    · rw [r176l_outSlot_visit_mem hP hw, r176l_outSlot_visit_mem hP ((h w rfl).mpr hw)]
    · rw [r176l_outSlot_visit_not_mem hP hw, r176l_outSlot_visit_not_mem hP (fun h' => hw ((h w rfl).mp h'))]

theorem r176l_tau_eq_of_iff {S S' : Finset (Crossing P)} (m : Mark P)
    (h : ∀ w : Visit P, m = Sum.inr w → (w.1 ∈ S' ↔ w.1 ∈ S)) : r176l_tau hP S' m = r176l_tau hP S m := by
  unfold r176l_tau
  rw [r176l_outSlot_eq_of_iff hP m h]

end CornerMarks

/-! ### L3.6 The corner signs of the local configuration (RA (3), (6), (12)) -/

section LocalSigns

variable (hlt_a : visitParameter (r176l_ua hu) < visitParameter (visitOn j a (s176_mem_left hj)))
  (hlt_b : visitParameter (visitOn j b (s176_mem_right hj)) < visitParameter (visitOn v b (s176_mem_left hv)))
  (hlt_c : visitParameter (visitOn v c (s176_mem_right hv)) < visitParameter (r176l_uc hu))

omit [NeZero n] in
include hP in
/-- the crossing point of a visit is the edge point at its parameter -/
theorem r176l_edgePoint_visit (w : Visit P) : edgePoint P w.2.val (visitParameter w) = crossingPoint w.1 :=
  geometricVisitPosition_evaluation hP w

include hP hj hu hv hlt_a hlt_b hlt_c in
/-- **The vector identity of the corner** (the three crossing points are the pairwise intersections
of the three lines, in the orders of case 1): `γ e_c = -α e_a - β e_b` with `α, β, γ > 0`. -/
theorem r176l_vector_identity :
    ∃ α β γ : ℝ, 0 < α ∧ 0 < β ∧ 0 < γ ∧ γ • edge P c = -(α • edge P a) - β • edge P b := by
  refine ⟨visitParameter (visitOn j a (s176_mem_left hj)) - visitParameter (r176l_ua hu),
    visitParameter (visitOn v b (s176_mem_left hv)) - visitParameter (visitOn j b (s176_mem_right hj)),
    visitParameter (r176l_uc hu) - visitParameter (visitOn v c (s176_mem_right hv)),
    sub_pos.mpr hlt_a, sub_pos.mpr hlt_b, sub_pos.mpr hlt_c, ?_⟩
  have e1 : edgePoint P a (visitParameter (r176l_ua hu)) = crossingPoint u :=
    r176l_edgePoint_visit hP (r176l_ua hu)
  have e2 : edgePoint P c (visitParameter (r176l_uc hu)) = crossingPoint u :=
    r176l_edgePoint_visit hP (r176l_uc hu)
  have e3 : edgePoint P a (visitParameter (visitOn j a (s176_mem_left hj))) = crossingPoint j :=
    r176l_edgePoint_visit hP (visitOn j a (s176_mem_left hj))
  have e4 : edgePoint P b (visitParameter (visitOn j b (s176_mem_right hj))) = crossingPoint j :=
    r176l_edgePoint_visit hP (visitOn j b (s176_mem_right hj))
  have e5 : edgePoint P b (visitParameter (visitOn v b (s176_mem_left hv))) = crossingPoint v :=
    r176l_edgePoint_visit hP (visitOn v b (s176_mem_left hv))
  have e6 : edgePoint P c (visitParameter (visitOn v c (s176_mem_right hv))) = crossingPoint v :=
    r176l_edgePoint_visit hP (visitOn v c (s176_mem_right hv))
  have hc : (visitParameter (r176l_uc hu) - visitParameter (visitOn v c (s176_mem_right hv))) • edge P c =
      crossingPoint u - crossingPoint v := by
    rw [← edgePoint_sub_edgePoint, e2, e6]
  have ha : (visitParameter (r176l_ua hu) - visitParameter (visitOn j a (s176_mem_left hj))) • edge P a =
      crossingPoint u - crossingPoint j := by
    rw [← edgePoint_sub_edgePoint, e1, e3]
  have hb : (visitParameter (visitOn v b (s176_mem_left hv)) - visitParameter (visitOn j b (s176_mem_right hj))) •
      edge P b = crossingPoint v - crossingPoint j := by
    rw [← edgePoint_sub_edgePoint, e5, e4]
  rw [hc, hb, ← neg_smul, neg_sub, ha]
  abel

include hP hj hu hv hlt_a hlt_b hlt_c in
/-- **The corner-sign ledger** (RA (6)/(12)): with `σ = sgn det(e_a, e_b)` the turn of the corner,
`sgn det(e_a, e_c) = sgn det(e_c, e_b) = -σ` and `sgn det(e_c, e_a) = sgn det(e_b, e_c) = σ`. -/
theorem r176l_local_signs :
    SignType.sign (det (edge P a) (edge P c)) = -SignType.sign (det (edge P a) (edge P b)) ∧
    SignType.sign (det (edge P c) (edge P b)) = -SignType.sign (det (edge P a) (edge P b)) ∧
    SignType.sign (det (edge P c) (edge P a)) = SignType.sign (det (edge P a) (edge P b)) ∧
    SignType.sign (det (edge P b) (edge P c)) = SignType.sign (det (edge P a) (edge P b)) := by
  obtain ⟨α, β, γ, hα, hβ, hγ, hvec⟩ := r176l_vector_identity hP hj hu hv hlt_a hlt_b hlt_c
  have h1 : γ * det (edge P a) (edge P c) = -β * det (edge P a) (edge P b) := by
    rw [← det_smul_right, hvec, r176l_det_sub_right, r176l_det_neg_right, det_smul_right, det_smul_right,
      r176l_det_self]
    ring
  have h2 : γ * det (edge P c) (edge P b) = -α * det (edge P a) (edge P b) := by
    rw [← det_smul_left, hvec, r176l_det_sub_left, r176l_det_neg_left, det_smul_left, det_smul_left,
      r176l_det_self]
    ring
  have hs1 : SignType.sign (det (edge P a) (edge P c)) = -SignType.sign (det (edge P a) (edge P b)) := by
    have := congrArg SignType.sign h1
    rwa [sign_mul, sign_mul, sign_pos hγ, one_mul, Left.sign_neg, sign_pos hβ, neg_one_mul] at this
  have hs2 : SignType.sign (det (edge P c) (edge P b)) = -SignType.sign (det (edge P a) (edge P b)) := by
    have := congrArg SignType.sign h2
    rwa [sign_mul, sign_mul, sign_pos hγ, one_mul, Left.sign_neg, sign_pos hα, neg_one_mul] at this
  refine ⟨hs1, hs2, ?_, ?_⟩
  · rw [det_swap, Left.sign_neg, hs1, neg_neg]
  · rw [det_swap, Left.sign_neg, hs2, neg_neg]

end LocalSigns

/-! ### L3.7 The corner sets of the three children and the one-dissent shapes (12) -/

section Shapes

variable (hρa : geoMarkSuccessor hP (Sum.inr (r176l_ua hu)) = Sum.inr (visitOn j a (s176_mem_left hj)))
  (hρb : geoMarkSuccessor hP (Sum.inr (visitOn j b (s176_mem_right hj))) = Sum.inr (visitOn v b (s176_mem_left hv)))
  (hρc : geoMarkSuccessor hP (Sum.inr (visitOn v c (s176_mem_right hv))) = Sum.inr (r176l_uc hu))
  (hSf : GeoIndependent hP (r176l_Sf T u v))
  (hlt_a : visitParameter (r176l_ua hu) < visitParameter (visitOn j a (s176_mem_left hj)))
  (hlt_b : visitParameter (visitOn j b (s176_mem_right hj)) < visitParameter (visitOn v b (s176_mem_left hv)))
  (hlt_c : visitParameter (visitOn v c (s176_mem_right hv)) < visitParameter (r176l_uc hu))
  {σ : SignType} (huni : ∀ k, turn (geoCornerPolygon hP T q) k = σ)

include hac hbc hu hv in
/-- a true corner of `Sf` is a true corner of `T` or one of the four local visits -/
theorem r176l_isTrueCorner_Sf_iff (m : Mark P) :
    IsTrueCorner (r176l_Sf T u v) m ↔ IsTrueCorner T m ∨ m = Sum.inr (r176l_ua hu) ∨ m = Sum.inr (r176l_uc hu) ∨
      m = Sum.inr (visitOn v b (s176_mem_left hv)) ∨ m = Sum.inr (visitOn v c (s176_mem_right hv)) := by
  cases m with
  | inl i => simp only [isTrueCorner_vertex, true_or]
  | inr w =>
    simp only [isTrueCorner_visit, Sum.inr.injEq]
    constructor
    · intro h
      rcases r176l_mem_ins.mp h with h | h
      · rcases visit_eq_or_twin (visitOn v b (s176_mem_left hv)) w h with rfl | rfl
        · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
        · rw [r176l_twin_vb hv hbc]; exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))
      · rcases r176l_mem_ins.mp h with h | h
        · rcases visit_eq_or_twin (r176l_ua hu) w h with rfl | rfl
          · exact Or.inr (Or.inl rfl)
          · rw [r176l_twin_ua hu hac]; exact Or.inr (Or.inr (Or.inl rfl))
        · exact Or.inl h
    · rintro (h | rfl | rfl | rfl | rfl)
      · exact r176l_subset_Sf T u v h
      · exact r176l_u_mem_Sf T u v
      · exact r176l_u_mem_Sf T u v
      · exact r176l_v_mem_Sf T u v
      · exact r176l_v_mem_Sf T u v

omit [NeZero n] in
include hab hac hbc hj hu hv in
theorem r176l_visits_ne :
    Sum.inr (r176l_uc hu) ≠ (Sum.inr (visitOn j a (s176_mem_left hj)) : Mark P) ∧
    Sum.inr (r176l_uc hu) ≠ (Sum.inr (visitOn v b (s176_mem_left hv)) : Mark P) ∧
    Sum.inr (visitOn j a (s176_mem_left hj)) ≠ (Sum.inr (visitOn v b (s176_mem_left hv)) : Mark P) := by
  refine ⟨fun e => ?_, fun e => ?_, fun e => ?_⟩
  · exact r176l_j_ne_u hac hbc hj hu (congrArg (fun w : Visit P => w.1) (Sum.inr.inj e)).symm
  · exact r176l_u_ne_v hab hbc hu hv (congrArg (fun w : Visit P => w.1) (Sum.inr.inj e))
  · exact r176l_j_ne_v hac hbc hj hv (congrArg (fun w : Visit P => w.1) (Sum.inr.inj e))

include hab hac hbc hjT huq hvq hρa hρb hρc hSf in
/-- **The corner set of `Λ₁`**: the inherited corners of `q` owned by `Λ₁`, and the new corner `(v, c)`. -/
theorem r176l_mem_cornerSet_L1 (m : Mark P) :
    m ∈ r176l_cornerSet hP (r176l_Sf T u v) (r176l_L1 hP T u hv) ↔
      (m ∈ r176l_cornerSet hP T q ∧ geoOwner hP (r176l_Sf T u v) m = r176l_L1 hP T u hv) ∨
        m = Sum.inr (visitOn v c (s176_mem_right hv)) := by
  have hZ := r176l_Z_eq hP q hab hac hbc hj hu hv hjT huq hvq hρa hρb hρc
  rw [r176l_mem_cornerSet, r176l_mem_cornerSet, r176l_isTrueCorner_Sf_iff hac hbc hu hv]
  constructor
  · rintro ⟨hown, h | rfl | rfl | rfl | rfl⟩
    · exact Or.inl ⟨⟨r176l_sub_L1 hP q hv hvq hSf m hown, h⟩, hown⟩
    · exact absurd hown.symm (r176l_L1_ne_L2 hP q hab hac hbc hj hu hv hjT huq hvq hρa hρb hSf)
    · exact absurd (hZ.1.symm.trans hown) (r176l_L1_ne_Z hP q hab hac hbc hj hu hv hjT huq hvq hρa hρb hρc hSf).symm
    · exact absurd (hZ.2.symm.trans hown) (r176l_L1_ne_Z hP q hab hac hbc hj hu hv hjT huq hvq hρa hρb hρc hSf).symm
    · exact Or.inr rfl
  · rintro (⟨⟨-, hc⟩, hown⟩ | rfl)
    · exact ⟨hown, Or.inl hc⟩
    · exact ⟨rfl, Or.inr (Or.inr (Or.inr (Or.inr rfl)))⟩

include hab hac hbc hjT huq hvq hρa hρb hρc hSf in
/-- **The corner set of `Λ₂`**: the inherited corners of `q` owned by `Λ₂`, and the new corner `(u, a)`. -/
theorem r176l_mem_cornerSet_L2 (m : Mark P) :
    m ∈ r176l_cornerSet hP (r176l_Sf T u v) (r176l_L2 hP T v hu) ↔
      (m ∈ r176l_cornerSet hP T q ∧ geoOwner hP (r176l_Sf T u v) m = r176l_L2 hP T v hu) ∨
        m = Sum.inr (r176l_ua hu) := by
  have hZ := r176l_Z_eq hP q hab hac hbc hj hu hv hjT huq hvq hρa hρb hρc
  rw [r176l_mem_cornerSet, r176l_mem_cornerSet, r176l_isTrueCorner_Sf_iff hac hbc hu hv]
  constructor
  · rintro ⟨hown, h | rfl | rfl | rfl | rfl⟩
    · exact Or.inl ⟨⟨r176l_sub_L2 hP q hu huq hSf m hown, h⟩, hown⟩
    · exact Or.inr rfl
    · exact absurd (hZ.1.symm.trans hown) (r176l_L2_ne_Z hP q hab hac hbc hj hu hv hjT huq hvq hρa hρb hρc hSf).symm
    · exact absurd (hZ.2.symm.trans hown) (r176l_L2_ne_Z hP q hab hac hbc hj hu hv hjT huq hvq hρa hρb hρc hSf).symm
    · exact absurd hown (r176l_L1_ne_L2 hP q hab hac hbc hj hu hv hjT huq hvq hρa hρb hSf)
  · rintro (⟨⟨-, hc⟩, hown⟩ | rfl)
    · exact ⟨hown, Or.inl hc⟩
    · exact ⟨rfl, Or.inr (Or.inl rfl)⟩

include hab hac hbc hjT huq hvq hρa hρb hρc in
/-- **The corner set of the central triangle** is its three marks. -/
theorem r176l_mem_cornerSet_Z (m : Mark P) :
    m ∈ r176l_cornerSet hP (r176l_Sf T u v) (r176l_Z hP T u v hj) ↔
      m = Sum.inr (r176l_uc hu) ∨ m = Sum.inr (visitOn j a (s176_mem_left hj)) ∨
        m = Sum.inr (visitOn v b (s176_mem_left hv)) := by
  have hZ := r176l_Z_eq hP q hab hac hbc hj hu hv hjT huq hvq hρa hρb hρc
  rw [r176l_mem_cornerSet]
  constructor
  · rintro ⟨hown, -⟩
    exact r176l_mem_Z hP q hab hac hbc hj hu hv hjT huq hvq hρa hρb hρc m hown
  · rintro (rfl | rfl | rfl)
    · exact ⟨hZ.1, r176l_u_mem_Sf T u v⟩
    · exact ⟨rfl, r176l_subset_Sf T u v hjT⟩
    · exact ⟨hZ.2, r176l_v_mem_Sf T u v⟩

include hab hac hbc hjT huq hvq hρa hρb hρc in
/-- the central triangle has three corners -/
theorem r176l_cornerCount_Z : geoCornerCount hP (r176l_Sf T u v) (r176l_Z hP T u v hj) = 3 := by
  classical
  rw [r176l_cornerCount_eq_card]
  have hset : r176l_cornerSet hP (r176l_Sf T u v) (r176l_Z hP T u v hj) =
      {Sum.inr (r176l_uc hu), Sum.inr (visitOn j a (s176_mem_left hj)), Sum.inr (visitOn v b (s176_mem_left hv))} := by
    ext m
    rw [r176l_mem_cornerSet_Z hP q hab hac hbc hj hu hv hjT huq hvq hρa hρb hρc]
    simp only [Finset.mem_insert, Finset.mem_singleton]
  obtain ⟨h1, h2, h3⟩ := r176l_visits_ne hab hac hbc hj hu hv
  rw [hset, Finset.card_insert_of_notMem, Finset.card_pair h3]
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
  exact ⟨h1, h2⟩

include hjT huq hρa in
/-- `(j, a)` is a corner mark of `q` -/
theorem r176l_ja_mem_cornerSet_q :
    (Sum.inr (visitOn j a (s176_mem_left hj)) : Mark P) ∈ r176l_cornerSet hP T q := by
  rw [r176l_mem_cornerSet]
  refine ⟨?_, hjT⟩
  rw [← r176l_succT_ua hP q hj hu huq hρa, geoOwner_successor]
  exact r176l_owner_ua hP q hu huq

include hT hab hac hbc hjT huq hvq hρa hρb hρc hSf in
/-- **The corner set of `q`** splits into the inherited corners of `Λ₁`, those of `Λ₂`, and `(j, a)`. -/
theorem r176l_mem_cornerSet_q (m : Mark P) :
    m ∈ r176l_cornerSet hP T q ↔
      (m ∈ r176l_cornerSet hP T q ∧ geoOwner hP (r176l_Sf T u v) m = r176l_L1 hP T u hv) ∨
      (m ∈ r176l_cornerSet hP T q ∧ geoOwner hP (r176l_Sf T u v) m = r176l_L2 hP T v hu) ∨
      m = Sum.inr (visitOn j a (s176_mem_left hj)) := by
  constructor
  · intro hm
    have hown := ((r176l_mem_cornerSet hP).mp hm).1
    rcases r176l_owner_Sf_cases hP hT q hab hac hbc hj hu hv hjT huq hvq hρa hρb hρc hSf m hown with h | h | h
    · exact Or.inl ⟨hm, h⟩
    · exact Or.inr (Or.inl ⟨hm, h⟩)
    · right; right
      rcases r176l_mem_Z hP q hab hac hbc hj hu hv hjT huq hvq hρa hρb hρc m h with rfl | rfl | rfl
      · exact absurd ((r176l_mem_cornerSet hP).mp hm).2 (r176l_u_not_mem hP q huq)
      · rfl
      · exact absurd ((r176l_mem_cornerSet hP).mp hm).2 (r176l_v_not_mem hP q hvq)
  · rintro (⟨h, -⟩ | ⟨h, -⟩ | rfl)
    · exact h
    · exact h
    · exact r176l_ja_mem_cornerSet_q hP q hj hu hjT huq hρa

/-! ### the turns at the corner marks -/

include hn hP hT q hab hj hu hjT huq hρa huni in
/-- `σ = sgn det(e_a, e_b)`: the uniform turn sign of `q` is its turn at the corner `(j, a)`. -/
theorem r176l_sigma_eq : SignType.sign (det (edge P a) (edge P b)) = σ := by
  obtain ⟨k, hk⟩ := geoCornerMark_exists_of_owner hP T q _
    ((r176l_mem_cornerSet hP).mp (r176l_ja_mem_cornerSet_q hP q hj hu hjT huq hρa)).1 hjT
  have h := geoCornerPolygon_turn_eq_sign_of_independent hn hP hT q k
  rw [huni k, hk, geoInEdge_visit hn, r176l_outSlot_visit_mem hP hjT,
    s176_visitTwin_eq hj hab (s176_mem_left hj) (s176_mem_right hj)] at h
  exact h.symm

include hn hT huni in
/-- an inherited corner of a child has the turn of `q` there -/
theorem r176l_turn_inherited {S' : Finset (Crossing P)} (hS' : GeoIndependent hP S') (r : GeoComponent hP S')
    (k : ZMod (geoCornerCount hP S' r)) (hm : geoCornerMark hP S' r k ∈ r176l_cornerSet hP T q)
    (hiff : ∀ w : Visit P, geoCornerMark hP S' r k = Sum.inr w → (w.1 ∈ S' ↔ w.1 ∈ T)) :
    turn (geoCornerPolygon hP S' r) k = σ := by
  obtain ⟨hown, hc⟩ := (r176l_mem_cornerSet hP).mp hm
  obtain ⟨k', hk'⟩ := geoCornerMark_exists_of_owner hP T q _ hown hc
  rw [geoCornerPolygon_turn_eq_sign_of_independent hn hP hS' r k, r176l_outSlot_eq_of_iff hP _ hiff, ← huni k',
    geoCornerPolygon_turn_eq_sign_of_independent hn hP hT q k', hk']

/-- the crossing of an inherited corner is in `Sf` iff in `T` -/
theorem r176l_iff_of_cornerSet_q {m : Mark P} (hm : m ∈ r176l_cornerSet hP T q) (w : Visit P) (hw : m = Sum.inr w) :
    w.1 ∈ r176l_Sf T u v ↔ w.1 ∈ T := by
  have hc := ((r176l_mem_cornerSet hP).mp hm).2
  rw [hw] at hc
  exact ⟨fun _ => hc, fun h => r176l_subset_Sf T u v h⟩

include hn hT hab hac hbc hjT huq hvq hρa hρb hρc hSf hlt_a hlt_b hlt_c huni in
/-- **(12) for `Λ₁`**: every turn is `σ` except the one at the new corner `(v, c)`, which is `-σ`. -/
theorem r176l_shape_L1 : r176l_OneDissentShape (geoCornerPolygon hP (r176l_Sf T u v) (r176l_L1 hP T u hv)) σ := by
  have hσ := r176l_sigma_eq hn hP hT q hab hj hu hjT huq hρa huni
  obtain ⟨-, hcb, -, -⟩ := r176l_local_signs hP hj hu hv hlt_a hlt_b hlt_c
  obtain ⟨k₀, hk₀⟩ := geoCornerMark_exists_of_owner hP (r176l_Sf T u v) (r176l_L1 hP T u hv)
    (Sum.inr (visitOn v c (s176_mem_right hv))) rfl (r176l_v_mem_Sf T u v)
  refine ⟨k₀, ?_, fun k hk => ?_⟩
  · rw [geoCornerPolygon_turn_eq_sign_of_independent hn hP hSf _ k₀, hk₀, geoInEdge_visit hn,
      r176l_outSlot_visit_mem hP (r176l_v_mem_Sf T u v), r176l_twin_vc hv hbc]
    show SignType.sign (det (edge P c) (edge P b)) = -σ
    rw [hcb, hσ]
  · have hmem := (r176l_mem_cornerSet hP).mpr (geoCornerMark_mem hP (r176l_Sf T u v) (r176l_L1 hP T u hv) k)
    rcases (r176l_mem_cornerSet_L1 hP q hab hac hbc hj hu hv hjT huq hvq hρa hρb hρc hSf _).mp hmem with ⟨hq, -⟩ | he
    · exact r176l_turn_inherited hn hP hT q huni hSf _ k hq (r176l_iff_of_cornerSet_q hP q hq)
    · exact absurd (geoCornerMark_injective hP _ _ (he.trans hk₀.symm)) hk

include hn hT hab hac hbc hjT huq hvq hρa hρb hρc hSf hlt_a hlt_b hlt_c huni in
/-- **(12) for `Λ₂`**: every turn is `σ` except the one at the new corner `(u, a)`, which is `-σ`. -/
theorem r176l_shape_L2 : r176l_OneDissentShape (geoCornerPolygon hP (r176l_Sf T u v) (r176l_L2 hP T v hu)) σ := by
  have hσ := r176l_sigma_eq hn hP hT q hab hj hu hjT huq hρa huni
  obtain ⟨hac', -, -, -⟩ := r176l_local_signs hP hj hu hv hlt_a hlt_b hlt_c
  obtain ⟨k₀, hk₀⟩ := geoCornerMark_exists_of_owner hP (r176l_Sf T u v) (r176l_L2 hP T v hu)
    (Sum.inr (r176l_ua hu)) rfl (r176l_u_mem_Sf T u v)
  refine ⟨k₀, ?_, fun k hk => ?_⟩
  · rw [geoCornerPolygon_turn_eq_sign_of_independent hn hP hSf _ k₀, hk₀, geoInEdge_visit hn,
      r176l_outSlot_visit_mem hP (r176l_u_mem_Sf T u v), r176l_twin_ua hu hac]
    show SignType.sign (det (edge P a) (edge P c)) = -σ
    rw [hac', hσ]
  · have hmem := (r176l_mem_cornerSet hP).mpr (geoCornerMark_mem hP (r176l_Sf T u v) (r176l_L2 hP T v hu) k)
    rcases (r176l_mem_cornerSet_L2 hP q hab hac hbc hj hu hv hjT huq hvq hρa hρb hρc hSf _).mp hmem with ⟨hq, -⟩ | he
    · exact r176l_turn_inherited hn hP hT q huni hSf _ k hq (r176l_iff_of_cornerSet_q hP q hq)
    · exact absurd (geoCornerMark_injective hP _ _ (he.trans hk₀.symm)) hk

include hn hT hab hac hbc hjT huq hvq hρa hρb hρc hSf hlt_a hlt_b hlt_c huni in
/-- **The central triangle is uniform with sign `σ`.** -/
theorem r176l_turn_Z (k : ZMod (geoCornerCount hP (r176l_Sf T u v) (r176l_Z hP T u v hj))) :
    turn (geoCornerPolygon hP (r176l_Sf T u v) (r176l_Z hP T u v hj)) k = σ := by
  have hσ := r176l_sigma_eq hn hP hT q hab hj hu hjT huq hρa huni
  obtain ⟨-, -, hca, hbc'⟩ := r176l_local_signs hP hj hu hv hlt_a hlt_b hlt_c
  have hmem := (r176l_mem_cornerSet hP).mpr (geoCornerMark_mem hP (r176l_Sf T u v) (r176l_Z hP T u v hj) k)
  rw [geoCornerPolygon_turn_eq_sign_of_independent hn hP hSf _ k]
  rcases (r176l_mem_cornerSet_Z hP q hab hac hbc hj hu hv hjT huq hvq hρa hρb hρc _).mp hmem with h | h | h
  · rw [h, geoInEdge_visit hn, r176l_outSlot_visit_mem hP (r176l_u_mem_Sf T u v), r176l_twin_uc hu hac]
    exact hca.trans hσ
  · rw [h, geoInEdge_visit hn, r176l_outSlot_visit_mem hP (r176l_subset_Sf T u v hjT),
      s176_visitTwin_eq hj hab (s176_mem_left hj) (s176_mem_right hj)]
    exact hσ
  · rw [h, geoInEdge_visit hn, r176l_outSlot_visit_mem hP (r176l_v_mem_Sf T u v), r176l_twin_vb hv hbc]
    exact hbc'.trans hσ

end Shapes

/-! ### L3.8 The rotation ledger (13): signed additivity through the corner angles -/

section RotAdd

variable (hρa : geoMarkSuccessor hP (Sum.inr (r176l_ua hu)) = Sum.inr (visitOn j a (s176_mem_left hj)))
  (hρb : geoMarkSuccessor hP (Sum.inr (visitOn j b (s176_mem_right hj))) = Sum.inr (visitOn v b (s176_mem_left hv)))
  (hρc : geoMarkSuccessor hP (Sum.inr (visitOn v c (s176_mem_right hv))) = Sum.inr (r176l_uc hu))
  (hSf : GeoIndependent hP (r176l_Sf T u v))
  (hlt_a : visitParameter (r176l_ua hu) < visitParameter (visitOn j a (s176_mem_left hj)))
  (hlt_b : visitParameter (visitOn j b (s176_mem_right hj)) < visitParameter (visitOn v b (s176_mem_left hv)))
  (hlt_c : visitParameter (visitOn v c (s176_mem_right hv)) < visitParameter (r176l_uc hu))
  {σ : SignType} (hσ : σ ≠ 0) (huni : ∀ k, turn (geoCornerPolygon hP T q) k = σ)
  (hreg : ∀ (S : Finset (Crossing P)) (r : GeoComponent hP S), GeoIndependent hP S →
    CV.Regular (geoCornerPolygon hP S r))

open scoped Classical in
/-- the inherited corners of `q` lying on a child `r` of the full support -/
def r176l_inherited (S : Finset (Crossing P)) (r : GeoComponent hP S) : Finset (Mark P) :=
  (r176l_cornerSet hP T q).filter fun m => geoOwner hP S m = r

theorem r176l_mem_inherited {S : Finset (Crossing P)} {r : GeoComponent hP S} {m : Mark P} :
    m ∈ r176l_inherited hP q S r ↔ m ∈ r176l_cornerSet hP T q ∧ geoOwner hP S m = r := by
  classical
  simp only [r176l_inherited, Finset.mem_filter]

/-- on inherited corners the angle in `Sf` is the angle in `T` -/
theorem r176l_sum_inherited_tau {r : GeoComponent hP (r176l_Sf T u v)} :
    ∑ m ∈ r176l_inherited hP q (r176l_Sf T u v) r, r176l_tau hP (r176l_Sf T u v) m =
      ∑ m ∈ r176l_inherited hP q (r176l_Sf T u v) r, r176l_tau hP T m := by
  refine Finset.sum_congr rfl fun m hm => ?_
  exact r176l_tau_eq_of_iff hP m (r176l_iff_of_cornerSet_q hP q ((r176l_mem_inherited hP q).mp hm).1)

/-! the five local angles -/

include hn hbc in
theorem r176l_tau_vc : r176l_tau hP (r176l_Sf T u v) (Sum.inr (visitOn v c (s176_mem_right hv))) =
    principalAngle (edge P c) (edge P b) := by
  unfold r176l_tau
  rw [geoInEdge_visit hn, r176l_outSlot_visit_mem hP (r176l_v_mem_Sf T u v), r176l_twin_vc hv hbc]
  rfl
include hn hbc in
theorem r176l_tau_vb : r176l_tau hP (r176l_Sf T u v) (Sum.inr (visitOn v b (s176_mem_left hv))) =
    principalAngle (edge P b) (edge P c) := by
  unfold r176l_tau
  rw [geoInEdge_visit hn, r176l_outSlot_visit_mem hP (r176l_v_mem_Sf T u v), r176l_twin_vb hv hbc]
  rfl
include hn hac in
theorem r176l_tau_ua : r176l_tau hP (r176l_Sf T u v) (Sum.inr (r176l_ua hu)) =
    principalAngle (edge P a) (edge P c) := by
  unfold r176l_tau
  rw [geoInEdge_visit hn, r176l_outSlot_visit_mem hP (r176l_u_mem_Sf T u v), r176l_twin_ua hu hac]
  rfl
include hn hac in
theorem r176l_tau_uc : r176l_tau hP (r176l_Sf T u v) (Sum.inr (r176l_uc hu)) =
    principalAngle (edge P c) (edge P a) := by
  unfold r176l_tau
  rw [geoInEdge_visit hn, r176l_outSlot_visit_mem hP (r176l_u_mem_Sf T u v), r176l_twin_uc hu hac]
  rfl
include hn hab hjT in
theorem r176l_tau_ja_Sf : r176l_tau hP (r176l_Sf T u v) (Sum.inr (visitOn j a (s176_mem_left hj))) =
    principalAngle (edge P a) (edge P b) := by
  unfold r176l_tau
  rw [geoInEdge_visit hn, r176l_outSlot_visit_mem hP (r176l_subset_Sf T u v hjT),
    s176_visitTwin_eq hj hab (s176_mem_left hj) (s176_mem_right hj)]
  rfl
include hn hab hjT in
theorem r176l_tau_ja_T : r176l_tau hP T (Sum.inr (visitOn j a (s176_mem_left hj))) =
    principalAngle (edge P a) (edge P b) := by
  unfold r176l_tau
  rw [geoInEdge_visit hn, r176l_outSlot_visit_mem hP hjT,
    s176_visitTwin_eq hj hab (s176_mem_left hj) (s176_mem_right hj)]
  rfl

include hn hab hac hbc hjT huq hvq hρa hρb hρc hSf in
/-- the angle sum of `Λ₁` -/
theorem r176l_sum_tau_L1 :
    ∑ m ∈ r176l_cornerSet hP (r176l_Sf T u v) (r176l_L1 hP T u hv), r176l_tau hP (r176l_Sf T u v) m =
      ∑ m ∈ r176l_inherited hP q (r176l_Sf T u v) (r176l_L1 hP T u hv), r176l_tau hP T m +
        principalAngle (edge P c) (edge P b) := by
  classical
  have hset : r176l_cornerSet hP (r176l_Sf T u v) (r176l_L1 hP T u hv) =
      insert (Sum.inr (visitOn v c (s176_mem_right hv)) : Mark P)
        (r176l_inherited hP q (r176l_Sf T u v) (r176l_L1 hP T u hv)) := by
    ext m
    rw [r176l_mem_cornerSet_L1 hP q hab hac hbc hj hu hv hjT huq hvq hρa hρb hρc hSf, Finset.mem_insert,
      r176l_mem_inherited]
    tauto
  have hnot : (Sum.inr (visitOn v c (s176_mem_right hv)) : Mark P) ∉
      r176l_inherited hP q (r176l_Sf T u v) (r176l_L1 hP T u hv) := by
    intro h
    exact r176l_v_not_mem hP q hvq ((r176l_mem_cornerSet hP).mp ((r176l_mem_inherited hP q).mp h).1).2
  rw [hset, Finset.sum_insert hnot, r176l_sum_inherited_tau hP q, r176l_tau_vc hn hP hbc hv, add_comm]

include hn hab hac hbc hjT huq hvq hρa hρb hρc hSf in
/-- the angle sum of `Λ₂` -/
theorem r176l_sum_tau_L2 :
    ∑ m ∈ r176l_cornerSet hP (r176l_Sf T u v) (r176l_L2 hP T v hu), r176l_tau hP (r176l_Sf T u v) m =
      ∑ m ∈ r176l_inherited hP q (r176l_Sf T u v) (r176l_L2 hP T v hu), r176l_tau hP T m +
        principalAngle (edge P a) (edge P c) := by
  classical
  have hset : r176l_cornerSet hP (r176l_Sf T u v) (r176l_L2 hP T v hu) =
      insert (Sum.inr (r176l_ua hu) : Mark P) (r176l_inherited hP q (r176l_Sf T u v) (r176l_L2 hP T v hu)) := by
    ext m
    rw [r176l_mem_cornerSet_L2 hP q hab hac hbc hj hu hv hjT huq hvq hρa hρb hρc hSf, Finset.mem_insert,
      r176l_mem_inherited]
    tauto
  have hnot : (Sum.inr (r176l_ua hu) : Mark P) ∉ r176l_inherited hP q (r176l_Sf T u v) (r176l_L2 hP T v hu) := by
    intro h
    exact r176l_u_not_mem hP q huq ((r176l_mem_cornerSet hP).mp ((r176l_mem_inherited hP q).mp h).1).2
  rw [hset, Finset.sum_insert hnot, r176l_sum_inherited_tau hP q, r176l_tau_ua hn hP hac hu, add_comm]

include hn hab hac hbc hjT huq hvq hρa hρb hρc in
/-- the angle sum of the central triangle -/
theorem r176l_sum_tau_Z :
    ∑ m ∈ r176l_cornerSet hP (r176l_Sf T u v) (r176l_Z hP T u v hj), r176l_tau hP (r176l_Sf T u v) m =
      principalAngle (edge P c) (edge P a) + principalAngle (edge P a) (edge P b) +
        principalAngle (edge P b) (edge P c) := by
  classical
  have hset : r176l_cornerSet hP (r176l_Sf T u v) (r176l_Z hP T u v hj) =
      {Sum.inr (r176l_uc hu), Sum.inr (visitOn j a (s176_mem_left hj)), Sum.inr (visitOn v b (s176_mem_left hv))} := by
    ext m
    rw [r176l_mem_cornerSet_Z hP q hab hac hbc hj hu hv hjT huq hvq hρa hρb hρc]
    simp only [Finset.mem_insert, Finset.mem_singleton]
  obtain ⟨h1, h2, h3⟩ := r176l_visits_ne hab hac hbc hj hu hv
  rw [hset, Finset.sum_insert (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨h1, h2⟩),
    Finset.sum_insert (by simp only [Finset.mem_singleton]; exact h3), Finset.sum_singleton,
    r176l_tau_uc hn hP hac hu, r176l_tau_ja_Sf hn hP hab hj hjT, r176l_tau_vb hn hP hbc hv]
  ring

include hn hT hab hac hbc hjT huq hvq hρa hρb hρc hSf in
/-- the angle sum of `q` -/
theorem r176l_sum_tau_q :
    ∑ m ∈ r176l_cornerSet hP T q, r176l_tau hP T m =
      ∑ m ∈ r176l_inherited hP q (r176l_Sf T u v) (r176l_L1 hP T u hv), r176l_tau hP T m +
      ∑ m ∈ r176l_inherited hP q (r176l_Sf T u v) (r176l_L2 hP T v hu), r176l_tau hP T m +
        principalAngle (edge P a) (edge P b) := by
  classical
  have hZ := r176l_Z_eq hP q hab hac hbc hj hu hv hjT huq hvq hρa hρb hρc
  have hset : r176l_cornerSet hP T q =
      insert (Sum.inr (visitOn j a (s176_mem_left hj)) : Mark P)
        (r176l_inherited hP q (r176l_Sf T u v) (r176l_L1 hP T u hv) ∪
          r176l_inherited hP q (r176l_Sf T u v) (r176l_L2 hP T v hu)) := by
    ext m
    rw [Finset.mem_insert, Finset.mem_union, r176l_mem_inherited, r176l_mem_inherited]
    constructor
    · intro hm
      rcases (r176l_mem_cornerSet_q hP hT q hab hac hbc hj hu hv hjT huq hvq hρa hρb hρc hSf m).mp hm with h | h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
      · exact Or.inl h
    · rintro (rfl | ⟨h, -⟩ | ⟨h, -⟩)
      · exact r176l_ja_mem_cornerSet_q hP q hj hu hjT huq hρa
      · exact h
      · exact h
  have hnot : (Sum.inr (visitOn j a (s176_mem_left hj)) : Mark P) ∉
      r176l_inherited hP q (r176l_Sf T u v) (r176l_L1 hP T u hv) ∪
        r176l_inherited hP q (r176l_Sf T u v) (r176l_L2 hP T v hu) := by
    intro h
    rcases Finset.mem_union.mp h with h | h
    · exact r176l_L1_ne_Z hP q hab hac hbc hj hu hv hjT huq hvq hρa hρb hρc hSf
        ((r176l_mem_inherited hP q).mp h).2.symm
    · exact r176l_L2_ne_Z hP q hab hac hbc hj hu hv hjT huq hvq hρa hρb hρc hSf
        ((r176l_mem_inherited hP q).mp h).2.symm
  have hdisj : Disjoint (r176l_inherited hP q (r176l_Sf T u v) (r176l_L1 hP T u hv))
      (r176l_inherited hP q (r176l_Sf T u v) (r176l_L2 hP T v hu)) := by
    rw [Finset.disjoint_left]
    intro m h1 h2
    exact r176l_L1_ne_L2 hP q hab hac hbc hj hu hv hjT huq hvq hρa hρb hSf
      (((r176l_mem_inherited hP q).mp h1).2.symm.trans ((r176l_mem_inherited hP q).mp h2).2)
  rw [hset, Finset.sum_insert hnot, Finset.sum_union hdisj, r176l_tau_ja_T hn hP hab hj hjT]
  ring

include hn hT hab hac hbc hjT huq hvq hρa hρb hρc hSf hlt_a hlt_b hlt_c hσ huni in
/-- **Signed additivity of the principal-turn sums**: the two new turns at each smoothing site are
opposite (`principalAngle` antisymmetry on the transverse pairs), every inherited turn is unchanged. -/
theorem r176l_sum_principalTurn_add :
    ∑ k, CV.principalTurn (geoCornerPolygon hP (r176l_Sf T u v) (r176l_L1 hP T u hv)) k +
    ∑ k, CV.principalTurn (geoCornerPolygon hP (r176l_Sf T u v) (r176l_L2 hP T v hu)) k +
    ∑ k, CV.principalTurn (geoCornerPolygon hP (r176l_Sf T u v) (r176l_Z hP T u v hj)) k =
    ∑ k, CV.principalTurn (geoCornerPolygon hP T q) k := by
  have hσab := r176l_sigma_eq hn hP hT q hab hj hu hjT huq hρa huni
  obtain ⟨hac', hcb, -, -⟩ := r176l_local_signs hP hj hu hv hlt_a hlt_b hlt_c
  have hne_cb : det (edge P c) (edge P b) ≠ 0 := by
    intro h0
    rw [h0, sign_zero, hσab] at hcb
    cases σ with
    | zero => exact hσ rfl
    | pos => exact absurd hcb (by decide)
    | neg => exact absurd hcb (by decide)
  have hne_ac : det (edge P a) (edge P c) ≠ 0 := by
    intro h0
    rw [h0, sign_zero, hσab] at hac'
    cases σ with
    | zero => exact hσ rfl
    | pos => exact absurd hac' (by decide)
    | neg => exact absurd hac' (by decide)
  have hswap1 : principalAngle (edge P b) (edge P c) = -principalAngle (edge P c) (edge P b) :=
    r176l_principalAngle_swap (r176l_regularPair_of_det hne_cb)
  have hswap2 : principalAngle (edge P c) (edge P a) = -principalAngle (edge P a) (edge P c) :=
    r176l_principalAngle_swap (r176l_regularPair_of_det hne_ac)
  rw [r176l_sum_principalTurn hn hP hSf, r176l_sum_principalTurn hn hP hSf, r176l_sum_principalTurn hn hP hSf,
    r176l_sum_principalTurn hn hP hT, r176l_sum_tau_L1 hn hP q hab hac hbc hj hu hv hjT huq hvq hρa hρb hρc hSf,
    r176l_sum_tau_L2 hn hP q hab hac hbc hj hu hv hjT huq hvq hρa hρb hρc hSf,
    r176l_sum_tau_Z hn hP q hab hac hbc hj hu hv hjT huq hvq hρa hρb hρc,
    r176l_sum_tau_q hn hP hT q hab hac hbc hj hu hv hjT huq hvq hρa hρb hρc hSf, hswap1, hswap2]
  ring

include hn hT hab hac hbc hjT huq hvq hρa hρb hρc hSf hlt_a hlt_b hlt_c hσ huni hreg in
/-- **(13), signed form (case 1)**: `rot(q) = rot(Λ₁) + rot(Λ₂) + σ` (turnlift (ii) on the four
polygons, the central triangle having rotation `σ`). -/
theorem r176l_rot_add_case1 :
    CV.rot (geoCornerPolygon hP T q) (hreg T q hT) =
      CV.rot (geoCornerPolygon hP (r176l_Sf T u v) (r176l_L1 hP T u hv)) (hreg _ _ hSf) +
      CV.rot (geoCornerPolygon hP (r176l_Sf T u v) (r176l_L2 hP T v hu)) (hreg _ _ hSf) + (σ : ℤ) := by
  have hZ : CV.rot (geoCornerPolygon hP (r176l_Sf T u v) (r176l_Z hP T u v hj)) (hreg _ _ hSf) = (σ : ℤ) :=
    r176l_rot_uniform_three (hreg _ _ hSf) (r176l_cornerCount_Z hP q hab hac hbc hj hu hv hjT huq hvq hρa hρb hρc) hσ
      (r176l_turn_Z hn hP hT q hab hac hbc hj hu hv hjT huq hvq hρa hρb hρc hSf hlt_a hlt_b hlt_c huni)
  have hsum := r176l_sum_principalTurn_add hn hP hT q hab hac hbc hj hu hv hjT huq hvq hρa hρb hρc hSf hlt_a hlt_b
    hlt_c hσ huni
  rw [← CV.two_pi_mul_rot _ (hreg _ _ hSf), ← CV.two_pi_mul_rot _ (hreg _ _ hSf), ← CV.two_pi_mul_rot _ (hreg _ _ hSf),
    ← CV.two_pi_mul_rot _ (hreg T q hT), hZ] at hsum
  have hpi : (2 * Real.pi) ≠ 0 := by positivity
  have h : ((CV.rot (geoCornerPolygon hP T q) (hreg T q hT) : ℤ) : ℝ) =
      ((CV.rot (geoCornerPolygon hP (r176l_Sf T u v) (r176l_L1 hP T u hv)) (hreg _ _ hSf) : ℤ) : ℝ) +
        ((CV.rot (geoCornerPolygon hP (r176l_Sf T u v) (r176l_L2 hP T v hu)) (hreg _ _ hSf) : ℤ) : ℝ) +
        (((σ : ℤ) : ℤ) : ℝ) := by
    apply mul_left_cancel₀ hpi
    linarith
  rw [← Int.cast_add, ← Int.cast_add] at h
  exact Int.cast_injective h

end RotAdd

/-! ### L3.9 The forced orientation on `c`, the selected part, and the case-1 ledger bundle -/

section Case1Bundle

omit [NeZero n] in
include hP in
/-- distinct crossings on one edge have distinct visit parameters (injectivity of the geometric visit
position) -/
theorem r176l_param_ne {x y : Crossing P} (hxy : x ≠ y) {ℓ : ZMod n} (hx : ℓ ∈ x.val) (hy : ℓ ∈ y.val) :
    visitParameter (visitOn x ℓ hx) ≠ visitParameter (visitOn y ℓ hy) := by
  intro h
  have hpos : geometricVisitPosition hP (visitOn x ℓ hx) = geometricVisitPosition hP (visitOn y ℓ hy) :=
    Prod.ext rfl (Subtype.ext h)
  exact hxy (congrArg (fun w : Visit P => w.1) (geometricVisitPosition_injective hP hpos))

variable (hρa : geoMarkSuccessor hP (Sum.inr (r176l_ua hu)) = Sum.inr (visitOn j a (s176_mem_left hj)))
  (hρb : geoMarkSuccessor hP (Sum.inr (visitOn j b (s176_mem_right hj))) = Sum.inr (visitOn v b (s176_mem_left hv)))
  (hSf : GeoIndependent hP (r176l_Sf T u v))
  (hnb_c : ∀ w : Visit P, w.2.val = c →
    ¬ (visitParameter (r176l_uc hu) < visitParameter w ∧ visitParameter w < visitParameter (visitOn v c (s176_mem_right hv))) ∧
    ¬ (visitParameter (visitOn v c (s176_mem_right hv)) < visitParameter w ∧ visitParameter w < visitParameter (r176l_uc hu)))

include hn hab hac hbc hjT huq hvq hρa hρb hSf hnb_c in
/-- **The orientation of `c` is forced by the independence of `S_full`**: with `u` before `j` on `a` and
`j` before `v` on `b`, the order `u` before `v` on `c` would make the two visits of `v` lie on the two
different `S₁`-children of `q` (against `geoIndependent_remaining_pair_owners`); hence `v` is before
`u` on `c`, and the two `c`-visits are `ρ`-adjacent in that order. -/
theorem r176l_lt_c_of_indep :
    visitParameter (visitOn v c (s176_mem_right hv)) < visitParameter (r176l_uc hu) ∧
    geoMarkSuccessor hP (Sum.inr (visitOn v c (s176_mem_right hv))) = Sum.inr (r176l_uc hu) := by
  have huv : u ≠ v := r176l_u_ne_v hab hbc hu hv
  have hne := r176l_param_ne hP huv (s176_mem_right hu) (s176_mem_right hv)
  have hlt_c : visitParameter (visitOn v c (s176_mem_right hv)) < visitParameter (r176l_uc hu) := by
    by_contra hnot
    have hlt : visitParameter (r176l_uc hu) < visitParameter (visitOn v c (s176_mem_right hv)) :=
      lt_of_le_of_ne (not_lt.mp hnot) hne
    have hρc' : geoMarkSuccessor hP (Sum.inr (r176l_uc hu)) = Sum.inr (visitOn v c (s176_mem_right hv)) :=
      gu1_markSuccessor_eq_of_adjacent hn hP rfl hlt (fun w hw => (hnb_c w hw).1)
    -- in `S₁`: `(u, a) → (v, c)` and `(u, c) → (j, a) → (v, b)`
    have h1 : geoSmoothingSuccessor hP (r176l_S1 T u) (Sum.inr (r176l_ua hu)) =
        Sum.inr (visitOn v c (s176_mem_right hv)) := by
      have h := geoSmoothingSuccessor_insert_visit hP T (r176l_ua hu) (r176l_u_not_mem hP q huq)
      rw [r176l_twin_ua hu hac, geoSmoothingSuccessor_visit_of_not_mem hP T _ (r176l_u_not_mem hP q huq), hρc'] at h
      exact h
    have h2 := r176l_succS1_uc hP q hac hj hu huq hρa
    have h3 := r176l_succS1_ja hP q hab hac hbc hj hu hv hjT huq hρb
    have hcS1 := r176l_owner_S1_vb_vc hP q hab hbc hu hv hvq hSf
    have hsep := r176l_owner_S1_ua_ne_uc hP hac hu hSf
    apply hsep
    rw [← geoOwner_successor hP (r176l_S1 T u) (Sum.inr (r176l_ua hu)), h1, ← hcS1,
      ← geoOwner_successor hP (r176l_S1 T u) (Sum.inr (r176l_uc hu)), h2,
      ← geoOwner_successor hP (r176l_S1 T u) (Sum.inr (visitOn j a (s176_mem_left hj))), h3]
  exact ⟨hlt_c, gu1_markSuccessor_eq_of_adjacent hn hP rfl hlt_c (fun w hw => (hnb_c w hw).2)⟩

include hv huq hvq in
/-- the retained crossings of `q` selected in `Sf` are exactly `u, v` -/
theorem r176l_selectedPart_eq :
    r176l_selectedPart hP T (r176l_Sf T u v) q = {u, v} := by
  classical
  ext x
  simp only [r176l_selectedPart, Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hx, hxSf⟩
    rcases hxSf with h | h | h
    · exact Or.inr h
    · exact Or.inl h
    · exact absurd h ((mem_geoCarrierCrossings hP T q x).mp hx).1
  · rintro (h | h)
    · rw [h]; exact ⟨huq, Or.inr (Or.inl rfl)⟩
    · rw [h]; exact ⟨hvq, Or.inl rfl⟩

include hab hbc hu hv huq hvq in
theorem r176l_selectedPart_card : (r176l_selectedPart hP T (r176l_Sf T u v) q).card = 2 := by
  rw [r176l_selectedPart_eq hP q hv huq hvq, Finset.card_pair (r176l_u_ne_v hab hbc hu hv)]

end Case1Bundle

/-- **The geometric ledger of the affected carrier** on a full support `Sf ⊇ S'` with its two clean
outer children `Λ₁, Λ₂` and the uniform sign `σ` (the content of (14), (13), (12) that this unit owes
beyond the smoothing black box): the children property, the retained-set count, the two one-dissent
shapes and the signed rotation additivity. -/
structure r176l_LedgerData (hP : CrossingGeometry P) (S' Sf : Finset (Crossing P)) (hS' : GeoIndependent hP S')
    (hSf : GeoIndependent hP Sf) (q' : GeoComponent hP S') (Λ₁ Λ₂ : GeoComponent hP Sf) (σ : SignType)
    (hreg : ∀ (S : Finset (Crossing P)) (r : GeoComponent hP S), GeoIndependent hP S →
      CV.Regular (geoCornerPolygon hP S r)) : Prop where
  subset : S' ⊆ Sf
  children : r176l_Children hP S' Sf q' Λ₁ Λ₂
  card : (geoCarrierCrossings hP S' q').card =
    (geoCarrierCrossings hP Sf Λ₁).card + (geoCarrierCrossings hP Sf Λ₂).card +
      (r176l_mixedSet hP S' Sf q' Λ₁ Λ₂).card + 2
  shape₁ : r176l_OneDissentShape (geoCornerPolygon hP Sf Λ₁) σ
  shape₂ : r176l_OneDissentShape (geoCornerPolygon hP Sf Λ₂) σ
  rot_add : CV.rot (geoCornerPolygon hP S' q') (hreg S' q' hS') =
    CV.rot (geoCornerPolygon hP Sf Λ₁) (hreg Sf Λ₁ hSf) + CV.rot (geoCornerPolygon hP Sf Λ₂) (hreg Sf Λ₂ hSf) + (σ : ℤ)

section Case1Ledger

variable (hρa : geoMarkSuccessor hP (Sum.inr (r176l_ua hu)) = Sum.inr (visitOn j a (s176_mem_left hj)))
  (hρb : geoMarkSuccessor hP (Sum.inr (visitOn j b (s176_mem_right hj))) = Sum.inr (visitOn v b (s176_mem_left hv)))
  (hSf : GeoIndependent hP (r176l_Sf T u v))
  (hlt_a : visitParameter (r176l_ua hu) < visitParameter (visitOn j a (s176_mem_left hj)))
  (hlt_b : visitParameter (visitOn j b (s176_mem_right hj)) < visitParameter (visitOn v b (s176_mem_left hv)))
  (hnb_c : ∀ w : Visit P, w.2.val = c →
    ¬ (visitParameter (r176l_uc hu) < visitParameter w ∧ visitParameter w < visitParameter (visitOn v c (s176_mem_right hv))) ∧
    ¬ (visitParameter (visitOn v c (s176_mem_right hv)) < visitParameter w ∧ visitParameter w < visitParameter (r176l_uc hu)))
  {σ : SignType} (hσ : σ ≠ 0) (huni : ∀ k, turn (geoCornerPolygon hP T q) k = σ)
  (hreg : ∀ (S : Finset (Crossing P)) (r : GeoComponent hP S), GeoIndependent hP S →
    CV.Regular (geoCornerPolygon hP S r))

include hn hT hab hac hbc hjT huq hvq hρa hρb hSf hlt_a hlt_b hnb_c hσ huni hreg in
/-- **The ledger of case 1**: `Sf = T ∪ {u, v}`, `Λ₁ = owner (v, c)`, `Λ₂ = owner (u, a)`. -/
theorem r176l_ledgerData_case1 :
    r176l_LedgerData hP T (r176l_Sf T u v) hT hSf q (r176l_L1 hP T u hv) (r176l_L2 hP T v hu) σ hreg := by
  obtain ⟨hlt_c, hρc⟩ := r176l_lt_c_of_indep hn hP q hab hac hbc hj hu hv hjT huq hvq hρa hρb hSf hnb_c
  have hC := r176l_children_case1 hP hT q hab hac hbc hj hu hv hjT huq hvq hρa hρb hρc hSf
  exact
    { subset := r176l_subset_Sf T u v
      children := hC
      card := by
        rw [r176l_card_retained hP (r176l_subset_Sf T u v) hC, r176l_selectedPart_card hP q hab hbc hu hv huq hvq]
      shape₁ := r176l_shape_L1 hn hP hT q hab hac hbc hj hu hv hjT huq hvq hρa hρb hρc hSf hlt_a hlt_b hlt_c huni
      shape₂ := r176l_shape_L2 hn hP hT q hab hac hbc hj hu hv hjT huq hvq hρa hρb hρc hSf hlt_a hlt_b hlt_c huni
      rot_add := r176l_rot_add_case1 hn hP hT q hab hac hbc hj hu hv hjT huq hvq hρa hρb hρc hSf hlt_a hlt_b hlt_c hσ
        huni hreg }

end Case1Ledger

end L3

/-! ## §L4. The event level -/

section L4

variable {E : CV.Event n} {e f g : ZMod n} {δ : ℝ}

/-- **`S_full = Q' ∪ {j', u', v'}` is independent on `L`** (R-LOC-2 (4) full availability, R-LOC-2
corollary: the local graph is empty on `L`): `u', v'` interlace no member of `S'` (`est_mem_U_L`) and
not each other (`complement_on_triangle` against the `K3` side). -/
theorem r176l_Sf_indep_event (hL : LocalizationData E e f g δ) {t t' : E.Parameter} (ht : Punctured E δ t)
    (ht' : Punctured E δ t') (hop : OppositeSides E t t')
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    {hef' : IsCrossing (E.curve t) {e, f}} {heg' : IsCrossing (E.curve t) {e, g}}
    {hfg' : IsCrossing (E.curve t) {f, g}} (hcomp : CompleteLocal (geomAt E t ht.1) hef' heg' hfg')
    {Q : Finset (Crossing (E.curve t))} (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
    (hfull : FullAvail (geomAt E t ht.1) e f g Q) {j u v : Crossing (E.curve t)}
    (hj : j.val ∈ triangleSupports e f g) (hu : u.val ∈ triangleSupports e f g)
    (hv : v.val ∈ triangleSupports e f g) (hju : j ≠ u) (hjv : j ≠ v) (huv : u ≠ v) :
    GeoIndependent (geomAt E t' ht'.1)
      (r176l_Sf (transportSupport hs (Q ∪ {j})) (crossingTransport hs u) (crossingTransport hs v)) := by
  have hT : GeoIndependent (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j})) :=
    CV.geoIndependent_of_mem_Ind _ (est_S'_ind hL ht ht' hop hs hQ hfull hj)
  have hU := (CV.mem_U_iff _ _ _).mp (est_mem_U_L hL ht ht' hop hs hcomp hQ hfull hj hu hju)
  have hV := (CV.mem_U_iff _ _ _).mp (est_mem_U_L hL ht ht' hop hs hcomp hQ hfull hj hv hjv)
  have huv' : ¬ GeometricInterlaces (geomAt E t' ht'.1) (crossingTransport hs u) (crossingTransport hs v) := by
    rw [hL.complement_on_triangle t t' ht ht' hop hs u v hu hv huv]
    exact fun h => h (est_interlaces_of_complete ht.1 hcomp hu hv huv)
  intro x hx y hy hxy
  rcases r176l_mem_ins.mp hx with rfl | hx <;> rcases r176l_mem_ins.mp hy with rfl | hy
  · exact absurd rfl hxy
  · rcases r176l_mem_ins.mp hy with rfl | hy
    · exact fun h => huv' (geometricInterlaces_symm _ h)
    · exact hV.2 y hy
  · rcases r176l_mem_ins.mp hx with rfl | hx
    · exact huv'
    · exact fun h => hV.2 x hx (geometricInterlaces_symm _ h)
  · rcases r176l_mem_ins.mp hx with rfl | hx <;> rcases r176l_mem_ins.mp hy with rfl | hy
    · exact absurd rfl hxy
    · exact hU.2 y hy
    · exact fun h => hU.2 x hx (geometricInterlaces_symm _ h)
    · exact hT x hx y hy hxy

/-- **Uniformity is carried across the wall**: the copy of a uniform carrier is uniform with the same
sign (corner turns are carried, `GT_turn_tcp`). -/
theorem r176l_uniform_transport (hn : 3 ≤ n) (hL : LocalizationData E e f g δ) (hR : AV_EventRadius E δ)
    (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g) {t t' : E.Parameter} (ht : Punctured E δ t)
    (ht' : Punctured E δ t') (hop : OppositeSides E t t')
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    {Q : Finset (Crossing (E.curve t))} (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
    (hfull : FullAvail (geomAt E t ht.1) e f g Q) {j : Crossing (E.curve t)}
    (hj : j.val ∈ triangleSupports e f g) (q : GeoComponent (geomAt E t ht.1) (Q ∪ {j}))
    {σ : SignType} (huni : ∀ k, turn (geoCornerPolygon (geomAt E t ht.1) (Q ∪ {j}) q) k = σ) :
    ∀ k, turn (geoCornerPolygon (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j}))
      (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)) k = σ := by
  intro k
  set W := est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj
  rw [GT_cornerPolygon_eq W q, turn_geoRecast, GT_turn_tcp W hn q]
  exact huni _

/-- **The SMOOTH unit's black box at the event level** (Prop, never mapped here): for every labelled
case-1 configuration of the affected carrier `q₀' = GT_carrierEquiv W q` on `L` — labels `a, b, c`, the
selected corner `j' = {a, b}`, the two retained local crossings `u' = {a, c}`, `v' = {b, c}`, the
orientation `u' <_a j'`, `j' <_b v'`, and the full support `Sf = S' ∪ {u', v'}` — and for the lift `y`
of either local crossing, the smoothing data `r176l_SmoothData` at `Sf` with the two clean outer carriers
`Λ₁ = owner_{Sf} (v', c)`, `Λ₂ = owner_{Sf} (u', a)` of this unit. -/
def r176l_smooth_black_box : Prop :=
  ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (E : CV.Event n) (e f g : ZMod n) (δ : ℝ)
    (hL : LocalizationData E e f g δ) (hR : AV_EventRadius E δ) (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
    (t t' : E.Parameter) (ht : Punctured E δ t) (ht' : Punctured E δ t') (hop : OppositeSides E t t')
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    (Q : Finset (Crossing (E.curve t))) (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
    (hfull : FullAvail (geomAt E t ht.1) e f g Q) (j : Crossing (E.curve t))
    (hj : j.val ∈ triangleSupports e f g) (q : GeoComponent (geomAt E t ht.1) (Q ∪ {j}))
    (a b c : ZMod n) (_hab : a ≠ b) (_hac : a ≠ c) (_hbc : b ≠ c) (u v : Crossing (E.curve t))
    (_hjab : j.val = {a, b}) (huac : u.val = {a, c}) (hvbc : v.val = {b, c})
    (hu' : crossingTransport hs u ∈ geoCarrierCrossings (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j}))
      (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q))
    (hv' : crossingTransport hs v ∈ geoCarrierCrossings (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j}))
      (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q))
    (_hlt_a : visitParameter (visitOn (crossingTransport hs u) a (s176_mem_left huac)) <
      visitParameter (visitOn (crossingTransport hs j) a (s176_mem_left _hjab)))
    (hSf : r176l_Sf (transportSupport hs (Q ∪ {j})) (crossingTransport hs u) (crossingTransport hs v) ∈
      CV.Ind (geomAt E t' ht'.1))
    (y : (CV.carrierDiagram hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj)
      (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)).Γ.Crossing)
    (_hy : y = est_liftCrossing hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj) _ hu' ∨
      y = est_liftCrossing hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj) _ hv'),
    Nonempty (r176l_SmoothData hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj)
      (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q) y
      (r176l_Sf (transportSupport hs (Q ∪ {j})) (crossingTransport hs u) (crossingTransport hs v)) hSf
      (r176l_L1 (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j})) (crossingTransport hs u) (v := crossingTransport hs v) hvbc)
      (r176l_L2 (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j})) (crossingTransport hs v) (u := crossingTransport hs u) huac))

/-- **The non-move port data at a labelled case-1 configuration** (event level): the geometric ledger
of §L3 on the `L` side, the writhe shift (7) across the wall, `R(D₊) = R(D₀)`, the SMOOTH black box. -/
theorem r176l_portDataRest_case1 (hsmooth : r176l_smooth_black_box) (hn : 3 ≤ n)
    (hL : LocalizationData E e f g δ) (hR : AV_EventRadius E δ) (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
    {t t' : E.Parameter} (ht : Punctured E δ t) (ht' : Punctured E δ t') (hop : OppositeSides E t t')
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    {hef' : IsCrossing (E.curve t) {e, f}} {heg' : IsCrossing (E.curve t) {e, g}}
    {hfg' : IsCrossing (E.curve t) {f, g}} (hcomp : CompleteLocal (geomAt E t ht.1) hef' heg' hfg')
    {Q : Finset (Crossing (E.curve t))} (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
    (hfull : FullAvail (geomAt E t ht.1) e f g Q) {j : Crossing (E.curve t)}
    (hj : j.val ∈ triangleSupports e f g) (q : GeoComponent (geomAt E t ht.1) (Q ∪ {j}))
    (hwind : CV.wind (geomAt E t ht.1) (Q ∪ {j}) ≠ 0)
    {a b c : ZMod n} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (habc : ({a, b, c} : Finset (ZMod n)) = {e, f, g}) {u v : Crossing (E.curve t)}
    (hjab : j.val = {a, b}) (huac : u.val = {a, c}) (hvbc : v.val = {b, c})
    (hu : u.val ∈ triangleSupports e f g) (hv : v.val ∈ triangleSupports e f g)
    (hju : j ≠ u) (hjv : j ≠ v) (huv : u ≠ v)
    (hu' : crossingTransport hs u ∈ geoCarrierCrossings (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j}))
      (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q))
    (hv' : crossingTransport hs v ∈ geoCarrierCrossings (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j}))
      (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q))
    (hlt_a : visitParameter (visitOn (crossingTransport hs u) a (s176_mem_left huac)) <
      visitParameter (visitOn (crossingTransport hs j) a (s176_mem_left hjab)))
    (y : (CV.carrierDiagram hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj)
      (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)).Γ.Crossing)
    (hy : y = est_liftCrossing hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj) _ hu' ∨
      y = est_liftCrossing hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj) _ hv') :
    Nonempty (s176_PortDataRest hn (genericAt E t ht.1) (genericAt E t' ht'.1) (est_S_ind ht.1 hQ hfull hj)
      (est_S'_ind hL ht ht' hop hs hQ hfull hj) q
      (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q) y) := by
  have hS := est_S_ind ht.1 hQ hfull hj
  have hS' := est_S'_ind hL ht ht' hop hs hQ hfull hj
  -- the `L` side
  have hs' : ∀ s, IsCrossing (E.curve t') s ↔ IsCrossing (E.curve t) s := fun s => (hs s).symm
  have hop' : OppositeSides E t' t := by
    unfold OppositeSides at hop ⊢; linarith [mul_comm t.val t'.val]
  have hXL : ExactTriangleVisitOrders (E.curve t') (E.curve t) a b c hs' :=
    gu2_exact_of_eq hs' habc.symm (hL.gauss_words t' t ht' ht hop' hs')
  have hGL : CarrierGeometry (E.curve t') :=
    CarrierGeometry.ofDiagrammatic ((genericAt E t' ht'.1).diagrammatic hn)
  have hT : GeoIndependent (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j})) :=
    CV.geoIndependent_of_mem_Ind _ hS'
  have hjT : crossingTransport hs j ∈ transportSupport hs (Q ∪ {j}) :=
    (mem_transportSupport_iff hs _ j).mpr (Finset.mem_union_right _ (Finset.mem_singleton_self j))
  -- the successor facts of case 1
  have hρa : geoMarkSuccessor (geomAt E t' ht'.1) (Sum.inr (r176l_ua (u := crossingTransport hs u) huac)) =
      Sum.inr (visitOn (crossingTransport hs j) a (s176_mem_left hjab)) :=
    gu1_markSuccessor_eq_of_adjacent hn _ rfl hlt_a
      (fun w hw => (s176_nb_a hs' hab hac hbc hXL (j := crossingTransport hs j) (u := crossingTransport hs u)
        hjab huac w hw).1)
  have hlt_b := (s176_cyclic hn hGL hs' hT (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q) hab hac hbc hXL (j := crossingTransport hs j)
    (u := crossingTransport hs u) (v := crossingTransport hs v) hjab huac hvbc hjT hu' hv').mp hlt_a
  have hρb : geoMarkSuccessor (geomAt E t' ht'.1) (Sum.inr (visitOn (crossingTransport hs j) b (s176_mem_right hjab))) =
      Sum.inr (visitOn (crossingTransport hs v) b (s176_mem_left hvbc)) :=
    gu1_markSuccessor_eq_of_adjacent hn _ rfl hlt_b
      (fun w hw => (s176_nb_b hs' hab hac hbc hXL (j := crossingTransport hs j) (v := crossingTransport hs v)
        hjab hvbc w hw).1)
  have hnb_c := fun (w : Visit (E.curve t')) (hw : w.2.val = c) =>
    s176_nb_c hs' hab hac hbc hXL (u := crossingTransport hs u) (v := crossingTransport hs v) huac hvbc w hw
  -- the full support
  have hSf : GeoIndependent (geomAt E t' ht'.1)
      (r176l_Sf (transportSupport hs (Q ∪ {j})) (crossingTransport hs u) (crossingTransport hs v)) :=
    r176l_Sf_indep_event hL ht ht' hop hs hcomp hQ hfull hj hu hv hju hjv huv
  have hSf' : r176l_Sf (transportSupport hs (Q ∪ {j})) (crossingTransport hs u) (crossingTransport hs v) ∈
      CV.Ind (geomAt E t' ht'.1) := (CV.mem_Ind_iff _ _).mpr hSf
  -- uniformity, carried
  obtain ⟨σ, hσ, huniH⟩ := (CV.wind_ne_zero_imp (geomAt E t ht.1) (Q ∪ {j}) hwind).2 q
  have huni := r176l_uniform_transport hn hL hR hef heg hfg ht ht' hop hs hQ hfull hj q huniH
  -- regularity
  have hreg : ∀ (S : Finset (Crossing (E.curve t'))) (r : GeoComponent (geomAt E t' ht'.1) S),
      GeoIndependent (geomAt E t' ht'.1) S → CV.Regular (geoCornerPolygon (geomAt E t' ht'.1) S r) :=
    fun S r hind => CV.carrierPolygon_cvRegular hn (genericAt E t' ht'.1) ((CV.mem_Ind_iff _ _).mpr hind) r
  -- the ledger
  have LD := r176l_ledgerData_case1 hn (geomAt E t' ht'.1) hT (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q) hab hac hbc
    (j := crossingTransport hs j) (u := crossingTransport hs u) (v := crossingTransport hs v) hjab huac hvbc hjT
    hu' hv' hρa hρb hSf hlt_a hlt_b hnb_c hσ huni hreg
  -- the smoothing black box
  obtain ⟨D⟩ := hsmooth n hn E e f g δ hL hR hef heg hfg t t' ht ht' hop hs Q hQ hfull j hj q a b c hab hac hbc u v
    hjab huac hvbc hu' hv' hlt_a hSf' y hy
  -- (14): the writhe shift (7) and the `L`-side count
  have hcu : c ∈ u.val := s176_mem_right huac
  have hcv : c ∈ v.val := s176_mem_right hvbc
  have hcj : c ∉ j.val := by
    rw [hjab, Finset.mem_insert, Finset.mem_singleton]
    rintro (h | h)
    · exact hac h.symm
    · exact hbc h.symm
  have howner_u : geoOwner (geomAt E t ht.1) (Q ∪ {j}) (Sum.inr (visitOn u c hcu)) = q :=
    (est_retained_u_iff hL hR hef heg hfg ht ht' hop hs hcomp hQ hfull hj hu hju hcu hcj q).mp hu'
  have h7 := est_groupedWrithe_affected hL hR hef heg hfg ht ht' hop hs hcomp hQ hfull hj hu hv hju hjv huv hcu hcv
    q howner_u
  have hcard := LD.card
  have hw : CV.groupedWrithe (genericAt E t ht.1) q =
      CV.groupedWrithe (genericAt E t' ht'.1)
          (r176l_L1 (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j})) (crossingTransport hs u) (v := crossingTransport hs v) hvbc) +
        CV.groupedWrithe (genericAt E t' ht'.1)
          (r176l_L2 (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j})) (crossingTransport hs v) (u := crossingTransport hs u) huac) +
        ((r176l_mixedSet (genericAt E t' ht'.1).crossingGeometry (transportSupport hs (Q ∪ {j}))
          (r176l_Sf (transportSupport hs (Q ∪ {j})) (crossingTransport hs u) (crossingTransport hs v))
          (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)
          (r176l_L1 (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j})) (crossingTransport hs u) (v := crossingTransport hs v) hvbc)
          (r176l_L2 (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j})) (crossingTransport hs v) (u := crossingTransport hs u) huac)).card : ℤ) := by
    rw [CV.groupedWrithe_eq_card_geoCarrierCrossings _ hS'] at h7
    rw [CV.groupedWrithe_eq_card_geoCarrierCrossings _ hSf', CV.groupedWrithe_eq_card_geoCarrierCrossings _ hSf']
    have hc' : ((geoCarrierCrossings (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j})) (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)).card : ℤ) =
        _ := congrArg (fun m : ℕ => (m : ℤ)) hcard
    push_cast at hc'
    linarith
  -- (13)
  have hrot := r176l_rot_ledger hn (genericAt E t ht.1) (genericAt E t' ht'.1) hS hS' q (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)
    (hSf := hSf') hσ (GT_carrierR_eq hn (genericAt E t ht.1) (genericAt E t' ht'.1) (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) hS hS' q) LD.rot_add
    LD.shape₁ LD.shape₂
  -- (12)
  have halt := r176l_alt_of_shape hn (genericAt E t' ht'.1) (hSf := hSf') hσ LD.shape₁ LD.shape₂
  exact ⟨r176l_portDataRest_of hn (genericAt E t ht.1) (genericAt E t' ht'.1) hS hS' q (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q) y D hw
    hrot halt.1 halt.2⟩

/-- **The non-move port data at a labelled configuration, either orientation**: case 1 directly, case 2
as case 1 on the relabelled data `(b, a, c), (j, v, u)` (`s176_cyclic` forces `v' <_b j'`). -/
theorem r176l_portDataRest_labelled (hsmooth : r176l_smooth_black_box) (hn : 3 ≤ n)
    (hL : LocalizationData E e f g δ) (hR : AV_EventRadius E δ) (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
    {t t' : E.Parameter} (ht : Punctured E δ t) (ht' : Punctured E δ t') (hop : OppositeSides E t t')
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    {hef' : IsCrossing (E.curve t) {e, f}} {heg' : IsCrossing (E.curve t) {e, g}}
    {hfg' : IsCrossing (E.curve t) {f, g}} (hcomp : CompleteLocal (geomAt E t ht.1) hef' heg' hfg')
    {Q : Finset (Crossing (E.curve t))} (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
    (hfull : FullAvail (geomAt E t ht.1) e f g Q) {j : Crossing (E.curve t)}
    (hj : j.val ∈ triangleSupports e f g) (q : GeoComponent (geomAt E t ht.1) (Q ∪ {j}))
    (hwind : CV.wind (geomAt E t ht.1) (Q ∪ {j}) ≠ 0)
    {u : Crossing (E.curve t)} (hu : u.val ∈ triangleSupports e f g) (hju : j ≠ u)
    (hu' : crossingTransport hs u ∈ geoCarrierCrossings (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j}))
      (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q))
    {a b c : ZMod n} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (habc : ({a, b, c} : Finset (ZMod n)) = {e, f, g})
    (hjab : j.val = {a, b}) (huac : u.val = {a, c}) {v : Crossing (E.curve t)} (hvbc : v.val = {b, c})
    (hv : v.val ∈ triangleSupports e f g) (hjv : j ≠ v) (huv : u ≠ v) :
    Nonempty (s176_PortDataRest hn (genericAt E t ht.1) (genericAt E t' ht'.1) (est_S_ind ht.1 hQ hfull hj)
      (est_S'_ind hL ht ht' hop hs hQ hfull hj) q
      (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)
      (est_liftCrossing hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj) _ hu')) := by
  obtain ⟨hv', -, -⟩ := s176_event_site_core hn hL hR hef heg hfg ht ht' hop hs hcomp hQ hfull hj q hu hju hu'
    hab hac hbc habc hjab huac hvbc hv hjv huv
  have hS' := est_S'_ind hL ht ht' hop hs hQ hfull hj
  have hs' : ∀ s, IsCrossing (E.curve t') s ↔ IsCrossing (E.curve t) s := fun s => (hs s).symm
  have hop' : OppositeSides E t' t := by
    unfold OppositeSides at hop ⊢; linarith [mul_comm t.val t'.val]
  have hXL : ExactTriangleVisitOrders (E.curve t') (E.curve t) a b c hs' :=
    gu2_exact_of_eq hs' habc.symm (hL.gauss_words t' t ht' ht hop' hs')
  have hGL : CarrierGeometry (E.curve t') :=
    CarrierGeometry.ofDiagrammatic ((genericAt E t' ht'.1).diagrammatic hn)
  have hT : GeoIndependent (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j})) :=
    CV.geoIndependent_of_mem_Ind _ hS'
  have hjT : crossingTransport hs j ∈ transportSupport hs (Q ∪ {j}) :=
    (mem_transportSupport_iff hs _ j).mpr (Finset.mem_union_right _ (Finset.mem_singleton_self j))
  have hju' : crossingTransport hs u ≠ crossingTransport hs j := (crossingTransport hs).injective.ne hju.symm
  have hjv' : crossingTransport hs v ≠ crossingTransport hs j := (crossingTransport hs).injective.ne hjv.symm
  have hcyc := s176_cyclic hn hGL hs' hT (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)
    hab hac hbc hXL (j := crossingTransport hs j) (u := crossingTransport hs u) (v := crossingTransport hs v)
    hjab huac hvbc hjT hu' hv'
  rcases lt_or_gt_of_ne (r176l_param_ne (geomAt E t' ht'.1) hju' (s176_mem_left huac) (s176_mem_left hjab)) with
    hlt | hgt
  · exact r176l_portDataRest_case1 hsmooth hn hL hR hef heg hfg ht ht' hop hs hcomp hQ hfull hj q hwind hab hac hbc
      habc hjab huac hvbc hu hv hju hjv huv hu' hv' hlt _ (Or.inl rfl)
  · -- case 2: relabel `(b, a, c), (j, v, u)`
    have hnlt : ¬ visitParameter (visitOn (crossingTransport hs j) b (s176_mem_right hjab)) <
        visitParameter (visitOn (crossingTransport hs v) b (s176_mem_left hvbc)) :=
      fun h => lt_asymm hgt (hcyc.mpr h)
    have hlt_b : visitParameter (visitOn (crossingTransport hs v) b (s176_mem_left hvbc)) <
        visitParameter (visitOn (crossingTransport hs j) b (s176_mem_right hjab)) :=
      lt_of_le_of_ne (not_lt.mp hnlt) (r176l_param_ne (geomAt E t' ht'.1) hjv' (s176_mem_left hvbc) (s176_mem_right hjab))
    have habc' : ({b, a, c} : Finset (ZMod n)) = {e, f, g} := (Finset.insert_comm b a {c}).trans habc
    exact r176l_portDataRest_case1 hsmooth hn hL hR hef heg hfg ht ht' hop hs hcomp hQ hfull hj q hwind
      (a := b) (b := a) (c := c) hab.symm hbc hac habc' (u := v) (v := u) (s176_pair_comm' hjab) hvbc huac hv hu hjv hju
      huv.symm hv' hu' hlt_b _ (Or.inr rfl)

/-- **The `hrest` obligation of `s176_est_port_relation_weak_of'` under `wind(S) ≠ 0`** (the non-move
port data of row 176, from the SMOOTH black box): six relabellings of `r176l_portDataRest_labelled`. -/
theorem r176l_portDataRest_of_uniform (hsmooth : r176l_smooth_black_box) (hn : 3 ≤ n)
    (hL : LocalizationData E e f g δ) (hR : AV_EventRadius E δ) (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
    {t t' : E.Parameter} (ht : Punctured E δ t) (ht' : Punctured E δ t') (hop : OppositeSides E t t')
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    (hef' : IsCrossing (E.curve t) {e, f}) (heg' : IsCrossing (E.curve t) {e, g})
    (hfg' : IsCrossing (E.curve t) {f, g}) (hcomp : CompleteLocal (geomAt E t ht.1) hef' heg' hfg')
    {Q : Finset (Crossing (E.curve t))} (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
    (hfull : FullAvail (geomAt E t ht.1) e f g Q) {j : Crossing (E.curve t)}
    (hj : j.val ∈ triangleSupports e f g) (q : GeoComponent (geomAt E t ht.1) (Q ∪ {j}))
    (hwind : CV.wind (geomAt E t ht.1) (Q ∪ {j}) ≠ 0)
    {u : Crossing (E.curve t)} (hu : u.val ∈ triangleSupports e f g) (hju : j ≠ u)
    (hu' : crossingTransport hs u ∈ geoCarrierCrossings (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j}))
      (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)) :
    Nonempty (s176_PortDataRest hn (genericAt E t ht.1) (genericAt E t' ht'.1) (est_S_ind ht.1 hQ hfull hj)
      (est_S'_ind hL ht ht' hop hs hQ hfull hj) q
      (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)
      (est_liftCrossing hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj) _ hu')) := by
  have h1 : (xPair hef').val ∈ triangleSupports e f g := (P1.mem_triangleSupports _).mpr (Or.inl rfl)
  have h2 : (xPair heg').val ∈ triangleSupports e f g := (P1.mem_triangleSupports _).mpr (Or.inr (Or.inl rfl))
  have h3 : (xPair hfg').val ∈ triangleSupports e f g := (P1.mem_triangleSupports _).mpr (Or.inr (Or.inr rfl))
  have n12 := P1.xPair_ef_ne_eg hef' heg' hfg'
  have n13 := P1.xPair_ef_ne_fg hef' heg' hfg'
  have n23 := P1.xPair_eg_ne_fg hef' heg' hfg'
  have key : ∀ {a b c : ZMod n} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
      (habc : ({a, b, c} : Finset (ZMod n)) = {e, f, g})
      (hjab : j.val = {a, b}) (huac : u.val = {a, c}) {v : Crossing (E.curve t)} (hvbc : v.val = {b, c})
      (hv : v.val ∈ triangleSupports e f g) (hjv : j ≠ v) (huv : u ≠ v),
      Nonempty (s176_PortDataRest hn (genericAt E t ht.1) (genericAt E t' ht'.1) (est_S_ind ht.1 hQ hfull hj)
        (est_S'_ind hL ht ht' hop hs hQ hfull hj) q
        (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)
        (est_liftCrossing hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj) _ hu')) :=
    fun {a b c} hab hac hbc habc hjab huac {v} hvbc hv hjv huv =>
      r176l_portDataRest_labelled hsmooth hn hL hR hef heg hfg ht ht' hop hs hcomp hQ hfull hj q hwind hu hju hu'
        hab hac hbc habc hjab huac (v := v) hvbc hv hjv huv
  have p_feg : ({f, e, g} : Finset (ZMod n)) = {e, f, g} := Finset.insert_comm f e {g}
  have p_egf : ({e, g, f} : Finset (ZMod n)) = {e, f, g} := congrArg (insert e) (Finset.pair_comm g f)
  have p_gef : ({g, e, f} : Finset (ZMod n)) = {e, f, g} :=
    (Finset.insert_comm g e {f}).trans (congrArg (insert e) (Finset.pair_comm g f))
  have p_fge : ({f, g, e} : Finset (ZMod n)) = {e, f, g} :=
    (congrArg (insert f) (Finset.pair_comm g e)).trans (Finset.insert_comm f e {g})
  have p_gfe : ({g, f, e} : Finset (ZMod n)) = {e, f, g} :=
    ((congrArg (insert g) (Finset.pair_comm f e)).trans (Finset.insert_comm g e {f})).trans
      (congrArg (insert e) (Finset.pair_comm g f))
  rcases GT_tri_cases t hef' heg' hfg' j hj with rfl | rfl | rfl <;>
    rcases GT_tri_cases t hef' heg' hfg' u hu with rfl | rfl | rfl
  · exact absurd rfl hju
  · exact key hef heg hfg rfl rfl rfl (v := xPair hfg') rfl h3 n13 n23
  · exact key hef.symm hfg heg p_feg (Finset.pair_comm e f) rfl (v := xPair heg') rfl h2 n12 n23.symm
  · exact key heg hef hfg.symm p_egf rfl rfl (v := xPair hfg') (Finset.pair_comm f g) h3 n23 n13
  · exact absurd rfl hju
  · exact key heg.symm hfg.symm hef p_gef (Finset.pair_comm e g) (Finset.pair_comm f g) (v := xPair hef') rfl h1
      n12.symm n13.symm
  · exact key hfg hef.symm heg.symm p_fge rfl (Finset.pair_comm e f) (v := xPair heg') (Finset.pair_comm e g) h2
      n23.symm n12
  · exact key hfg.symm heg.symm hef.symm p_gfe (Finset.pair_comm f g) (Finset.pair_comm e g) (v := xPair hef')
      (Finset.pair_comm e f) h1 n13.symm n12.symm
  · exact absurd rfl hju

end L4

/-! ## §L5. The corrected interface: the port data under `wind(S) ≠ 0`

The fields `rot` (13) and `alt₁ alt₂` (12) of `est_PortData` need the affected carrier to be UNIFORM (RA
§3: "Assume [the common singleton selector] is nonzero. Then the affected singleton carrier is uniform;
by (6), all its corners have sign `σ`"): on a mixed affected carrier the inherited corners of an outer
carrier carry both signs, so `UniformOrOneDissentCV` and `R = R₁ + R₂ + 1` can fail.  The printed proof
does not need the port data there — for `wind(S) = 0` both row terms in (2) are `0` (`wind` is carried
across the wall, `GT_wind_eq`).  So the interface Props are restated with the hypothesis
`CV.wind (geomAt E t ht.1) (Q ∪ {j}) ≠ 0`; the consumer (`est_row_H` / `s176_est_row_H_weak`) must split on
`wind(S) = 0` — a RALedgers change, reported, not made here. -/

/-- `RProof.est_port_relation` with the additional hypothesis `wind(S) ≠ 0` (otherwise byte-identical). -/
def r176l_est_port_relation_uniform : Prop :=
  ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (E : CV.Event n) (e f g : ZMod n) (δ : ℝ)
    (hL : LocalizationData E e f g δ) (hR : AV_EventRadius E δ) (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
    (t t' : E.Parameter) (ht : Punctured E δ t) (ht' : Punctured E δ t') (hop : OppositeSides E t t')
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    (hef' : IsCrossing (E.curve t) {e, f}) (heg' : IsCrossing (E.curve t) {e, g})
    (hfg' : IsCrossing (E.curve t) {f, g}) (_hcomp : CompleteLocal (geomAt E t ht.1) hef' heg' hfg')
    (Q : Finset (Crossing (E.curve t))) (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
    (hfull : FullAvail (geomAt E t ht.1) e f g Q) (j : Crossing (E.curve t))
    (hj : j.val ∈ triangleSupports e f g) (q : GeoComponent (geomAt E t ht.1) (Q ∪ {j})),
    CV.wind (geomAt E t ht.1) (Q ∪ {j}) ≠ 0 →
    (∃ u : Crossing (E.curve t), u.val ∈ triangleSupports e f g ∧ u ≠ j ∧
      crossingTransport hs u ∈ geoCarrierCrossings (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j}))
        (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)) →
    ∃ (u : Crossing (E.curve t)) (_ : u.val ∈ triangleSupports e f g) (_ : u ≠ j)
      (hu' : crossingTransport hs u ∈ geoCarrierCrossings (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j}))
        (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)),
      Nonempty (est_PortData hn (genericAt E t ht.1) (genericAt E t' ht'.1) (est_S_ind ht.1 hQ hfull hj)
        (est_S'_ind hL ht ht' hop hs hQ hfull hj) q
        (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)
        (est_liftCrossing hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj) _ hu'))

/-- `s176_est_port_relation_weak` with the additional hypothesis `wind(S) ≠ 0` (otherwise byte-identical). -/
def r176l_est_port_relation_weak_uniform : Prop :=
  ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (E : CV.Event n) (e f g : ZMod n) (δ : ℝ)
    (hL : LocalizationData E e f g δ) (hR : AV_EventRadius E δ) (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
    (t t' : E.Parameter) (ht : Punctured E δ t) (ht' : Punctured E δ t') (hop : OppositeSides E t t')
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    (hef' : IsCrossing (E.curve t) {e, f}) (heg' : IsCrossing (E.curve t) {e, g})
    (hfg' : IsCrossing (E.curve t) {f, g}) (_hcomp : CompleteLocal (geomAt E t ht.1) hef' heg' hfg')
    (Q : Finset (Crossing (E.curve t))) (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
    (hfull : FullAvail (geomAt E t ht.1) e f g Q) (j : Crossing (E.curve t))
    (hj : j.val ∈ triangleSupports e f g) (q : GeoComponent (geomAt E t ht.1) (Q ∪ {j})),
    CV.wind (geomAt E t ht.1) (Q ∪ {j}) ≠ 0 →
    (∃ u : Crossing (E.curve t), u.val ∈ triangleSupports e f g ∧ u ≠ j ∧
      crossingTransport hs u ∈ geoCarrierCrossings (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j}))
        (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)) →
    ∃ (u : Crossing (E.curve t)) (_ : u.val ∈ triangleSupports e f g) (_ : u ≠ j)
      (hu' : crossingTransport hs u ∈ geoCarrierCrossings (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j}))
        (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)),
      Nonempty (s176_PortDataWeak hn (genericAt E t ht.1) (genericAt E t' ht'.1) (est_S_ind ht.1 hQ hfull hj)
        (est_S'_ind hL ht ht' hop hs hQ hfull hj) q
        (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)
        (est_liftCrossing hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj) _ hu'))

/-- The weak port relation with the uniformity hypothesis follows from the one without. -/
theorem r176l_est_port_relation_weak_uniform_of_weak (h : s176_est_port_relation_weak) :
    r176l_est_port_relation_weak_uniform :=
  fun n _ hn E e f g δ hL hR hef heg hfg t t' ht ht' hop hs hef' heg' hfg' hcomp Q hQ hfull j hj q _ hex =>
    h n hn E e f g δ hL hR hef heg hfg t t' ht ht' hop hs hef' heg' hfg' hcomp Q hQ hfull j hj q hex

/-- **The weak interface of row 176 under `wind(S) ≠ 0`, from the site, `hrec` and the SMOOTH black
box**: `s176_est_port_relation_weak_of'` with its `hrest` discharged by `r176l_portDataRest_of_uniform`. -/
theorem r176l_est_port_relation_weak_uniform_of (hsmooth : r176l_smooth_black_box)
    (hrec : ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (E : CV.Event n) (e f g : ZMod n) (δ : ℝ)
      (hL : LocalizationData E e f g δ) (hR : AV_EventRadius E δ) (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
      (t t' : E.Parameter) (ht : Punctured E δ t) (ht' : Punctured E δ t') (hop : OppositeSides E t t')
      (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
      (Q : Finset (Crossing (E.curve t))) (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
      (hfull : FullAvail (geomAt E t ht.1) e f g Q) (j : Crossing (E.curve t))
      (hj : j.val ∈ triangleSupports e f g) (q : GeoComponent (geomAt E t ht.1) (Q ∪ {j}))
      (u : Crossing (E.curve t))
      (hu' : crossingTransport hs u ∈ geoCarrierCrossings (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j}))
        (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)),
      s176_hrec_wall hn hL hR hef heg hfg ht ht' hop hs hQ hfull hj q hu') :
    r176l_est_port_relation_weak_uniform := by
  intro n _ hn E e f g δ hL hR hef heg hfg t t' ht ht' hop hs hef' heg' hfg' hcomp Q hQ hfull j hj q hwind hex
  obtain ⟨u, hu, hju, hu'⟩ := hex
  obtain ⟨R⟩ := r176l_portDataRest_of_uniform hsmooth hn hL hR hef heg hfg ht ht' hop hs hef' heg' hfg' hcomp hQ
    hfull hj q hwind hu hju.symm hu'
  refine ⟨u, hu, hju, hu', ⟨s176_PortDataWeak.mk' _ _ _ _ _ _ _ _ ?_ R⟩⟩
  exact s176_port_weak_of_event' hn hL hR hef heg hfg ht ht' hop hs hef' heg' hfg' hcomp hQ hfull hj q hu hju.symm
    hu' (hrec n hn E e f g δ hL hR hef heg hfg t t' ht ht' hop hs Q hQ hfull j hj q u hu')

end

end RProof


/-! # R176_Assembled — the assembler's composition section (2026-09-15)

Everything above this line is `Site_176.lean` (frozen, 4143 lines) followed by the three unit appendices
`R176_HSUCC` (`r176h_`, §I–§K), `R176_SMOOTH` (`r176s_`, §R1–§R5) and `R176_LEDGER` (`r176l_`, §L0–§L5),
byte-identical to the unit files.  This section (all names `r176_`) connects them; companion report
`R176_ASSEMBLY_REPORT.md`.

* §X1 the open geometric Prop of row 176 in the LEDGER's coordinates: `r176_OuterDataL` = SMOOTH's
  `r176s_OuterData` with the two outer carriers FIXED to the LEDGER's children `Λ₁ = owner_{Sf} (v', c)`
  (`r176l_L1`, the kinked `B`-component) and `Λ₂ = owner_{Sf} (u', a)` (`r176l_L2`, the clean `A`-component)
  at `Sf = r176l_Sf S' u' v'`; the black box `r176_outer_carriers_L` carries the FULL event binders
  (`hcomp`, `habc`, `hu hv hju hjv huv`, `hSf`, `hlt_a`) a geometric prover needs.
* §X2 the (14)-bridge `r176_mixed_bridge` (`2ℓ` = the number of mask-`uv` survivors) — the one clause of the
  LEDGER's `r176l_SmoothData` that neither unit proves.
* §X3 the connector `r176_smoothData_of`: the LEDGER's `r176l_SmoothData` from SMOOTH's constructions
  (`r176s_DA`, `r176s_DA_smooth`, `r176s_DA_componentCount`, `r176s_DA_i/j/ij`, `r176s_knotRestrictIso_i/j`,
  `r176s_homfly_of_liftBlock`, `r176s_homfly_of_liftBlock_curl`) from `r176_OuterDataL`, the curl black box
  `r176s_curl_removal` and the mixed bridge.
* §X4 the LEDGER's event-level chain replayed against the connector (`r176_portDataRest_case1`, `_labelled`,
  `_of_uniform`: bodies byte-identical except the `hsmooth` call) and the weak interface under `wind(S) ≠ 0`
  with HSUCC's port (`r176_est_port_relation_weak_uniform_of_curl_outer_mixed`).
* §X5 the consumer split on `wind(S) = 0` (both row terms vanish — `rowTerm_of_mem_Ind`, `GT_wind_eq`), so the
  corrected interface `r176l_est_port_relation_weak_uniform` suffices for the RA ledger
  (`r176_est_row_H_weak_uniform` … `r176_est_ledger_weak_uniform`): the "RALedgers change" of
  R176_LEDGER_REPORT §3, made here on the draft copies.
* §X6 the row: `r176_extreme_transport_of_curl_outer_mixed : RowShape @ExtremeTransportData` from exactly the
  three open Props and the library's `CV.carrierSlotFloor`; the `hrest`-only forms with `hF` discharged; and the
  SMOOTH-route composition `r176_extreme_transport_of_curl_outer_ledger` (from `r176s_outer_carriers` and
  `r176s_ledger`). -/

namespace RProof

open SM SM.GeoCarrier SM.Carrier SM.Link

noncomputable section

variable {n : ℕ} [NeZero n]

section R176Compose

variable {E : CV.Event n} {e f g : ZMod n} {δ : ℝ}

/-! ## §X1. The outer carriers of `S_full` in the LEDGER's coordinates -/

/-- **The outer-carrier data of row 176 with the LEDGER's children** — SMOOTH's `r176s_OuterData` (§R5) with
`Λ_B := r176l_L1 = owner_{Sf} (v', c)` (the kinked `B`-component, `Λ₁` of `s176_PortDataRest`) and
`Λ_A := r176l_L2 = owner_{Sf} (u', a)` (the clean `A`-component, `Λ₂`) at the full support `Sf = r176l_Sf S' u' v'`
(the LEDGER's classical-`insert` form): an occurrence `v₀` of `y`, the kink `r`, the retained sets of the two
children inside that of `q₀'`, and the identification of the two arc crossing sets of `ρ = D₊.record` at `v₀`
with the chords of the children (`KA_eq`, `KB_eq`, `r_not`, `r_curl`).  The remaining GEOMETRIC obligation of
row 176 (R176_SMOOTH_REPORT §2.2). -/
structure r176_OuterDataL (hn : 3 ≤ n) (hL : LocalizationData E e f g δ) (hR : AV_EventRadius E δ)
    (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g) {t t' : E.Parameter} (ht : Punctured E δ t)
    (ht' : Punctured E δ t') (hop : OppositeSides E t t')
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    {Q : Finset (Crossing (E.curve t))} (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
    (hfull : FullAvail (geomAt E t ht.1) e f g Q) {j : Crossing (E.curve t)}
    (hj : j.val ∈ triangleSupports e f g) (q : GeoComponent (geomAt E t ht.1) (Q ∪ {j}))
    {a b c : ZMod n} {u v : Crossing (E.curve t)} (huac : u.val = {a, c}) (hvbc : v.val = {b, c})
    (y : (CV.carrierDiagram hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj)
      (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)).Γ.Crossing) where
  /-- the occurrence of `y` from which the arc `A` carries the clean component -/
  v₀ : (CV.carrierDiagram hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj)
      (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)).Γ.Visit
  hv₀ : v₀.1 = y
  /-- the retained set of the clean child `Λ₂ = owner_{Sf} (u', a)` lies in that of `q₀'` -/
  subA : geoCarrierCrossings (geomAt E t' ht'.1) _ (r176l_L2 (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j})) (crossingTransport hs v)
        (u := crossingTransport hs u) huac) ⊆
    geoCarrierCrossings (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j})) (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)
  /-- the retained set of the kinked child `Λ₁ = owner_{Sf} (v', c)` lies in that of `q₀'` -/
  subB : geoCarrierCrossings (geomAt E t' ht'.1) _ (r176l_L1 (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j})) (crossingTransport hs u)
        (v := crossingTransport hs v) hvbc) ⊆
    geoCarrierCrossings (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j})) (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)
  /-- the crossings on the arc `A = (v₀ → τ v₀)` are the chords of `Λ₂` -/
  KA_eq : r176s_KA (CV.carrierDiagram hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj)
      (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)).record v₀ =
    CV.liftBlock hn (r176s_cgL hn ht') (CV.geoIndependent_of_mem_Ind _ (est_S'_ind hL ht ht' hop hs hQ hfull hj))
      (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q) (geoCarrierCrossings (geomAt E t' ht'.1) _ (r176l_L2 (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j})) (crossingTransport hs v)
        (u := crossingTransport hs u) huac))
  /-- the kink (the lift of the third triangle crossing) -/
  r : (CV.carrierDiagram hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj)
      (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)).record.Crossing
  /-- the crossings on the arc `B = (τ v₀ → v₀)` are the chords of `Λ₁` plus the kink -/
  KB_eq : r176s_KB (CV.carrierDiagram hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj)
      (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)).record v₀ =
    CV.liftBlock hn (r176s_cgL hn ht') (CV.geoIndependent_of_mem_Ind _ (est_S'_ind hL ht ht' hop hs hQ hfull hj))
      (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q) (geoCarrierCrossings (geomAt E t' ht'.1) _ (r176l_L1 (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j})) (crossingTransport hs u)
        (v := crossingTransport hs v) hvbc)) ∪ {r}
  r_not : r ∉ CV.liftBlock hn (r176s_cgL hn ht') (CV.geoIndependent_of_mem_Ind _ (est_S'_ind hL ht ht' hop hs hQ hfull hj))
      (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q) (geoCarrierCrossings (geomAt E t' ht'.1) _ (r176l_L1 (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j})) (crossingTransport hs u)
        (v := crossingTransport hs v) hvbc))
  /-- the kink's two occurrences are consecutive in `ρ|B` -/
  r_curl : ∃ (w : (CV.carrierDiagram hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj)
      (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)).record.M) (hw : (CV.carrierDiagram hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj)
      (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)).record.CrossKeep (r176s_KB (CV.carrierDiagram hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj)
      (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)).record v₀) w),
    (CV.carrierDiagram hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj)
      (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)).record.crossingOf w = r ∧
    (((CV.carrierDiagram hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj)
      (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)).record.restrictCrossings (r176s_KB (CV.carrierDiagram hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj)
      (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)).record v₀)).succ ⟨w, hw⟩).1 = (CV.carrierDiagram hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj)
      (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)).record.pair w

/-- **The outer carriers exist, LEDGER's coordinates — BLACK BOX (OPEN; the remaining geometric obligation
of row 176)**: for every labelled case-1 configuration of the affected carrier `q₀'` on `L` (the binders of
`r176l_portDataRest_case1`: `K3` side `t`, empty side `t'`, labels `a b c` with `{a, b, c} = {e, f, g}`, the
selected corner `j' = {a, b}`, the two retained local crossings `u' = {a, c}`, `v' = {b, c}`, the orientation
`u' <_a j'`, `S_full` independent) and the lift `y` of either local crossing, `r176_OuterDataL` is nonempty.
Geometric content: R176_SMOOTH_REPORT §2.2 (the `geoSmoothingSuccessor` of `S_full` on the visits of `q₀'`,
`s176_corner_case1`, the forced order `v' <_c u'` = `r176l_lt_c_of_indep`, `r176s_arcA_iff_key` /
`r176s_crossKeep_KA_iff_key` to read the arcs on the parent).  Estimate ≈ 1.5–2.5k lines. -/
def r176_outer_carriers_L : Prop :=
  ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (E : CV.Event n) (e f g : ZMod n) (δ : ℝ)
    (hL : LocalizationData E e f g δ) (hR : AV_EventRadius E δ) (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
    (t t' : E.Parameter) (ht : Punctured E δ t) (ht' : Punctured E δ t') (hop : OppositeSides E t t')
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    (hef' : IsCrossing (E.curve t) {e, f}) (heg' : IsCrossing (E.curve t) {e, g})
    (hfg' : IsCrossing (E.curve t) {f, g}) (_hcomp : CompleteLocal (geomAt E t ht.1) hef' heg' hfg')
    (Q : Finset (Crossing (E.curve t))) (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
    (hfull : FullAvail (geomAt E t ht.1) e f g Q) (j : Crossing (E.curve t))
    (hj : j.val ∈ triangleSupports e f g) (q : GeoComponent (geomAt E t ht.1) (Q ∪ {j}))
    (a b c : ZMod n) (_hab : a ≠ b) (_hac : a ≠ c) (_hbc : b ≠ c)
    (_habc : ({a, b, c} : Finset (ZMod n)) = {e, f, g}) (u v : Crossing (E.curve t))
    (hjab : j.val = {a, b}) (huac : u.val = {a, c}) (hvbc : v.val = {b, c})
    (_hu : u.val ∈ triangleSupports e f g) (_hv : v.val ∈ triangleSupports e f g)
    (_hju : j ≠ u) (_hjv : j ≠ v) (_huv : u ≠ v)
    (hu' : crossingTransport hs u ∈ geoCarrierCrossings (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j}))
      (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q))
    (hv' : crossingTransport hs v ∈ geoCarrierCrossings (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j}))
      (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q))
    (_hlt_a : visitParameter (visitOn (crossingTransport hs u) a (s176_mem_left huac)) <
      visitParameter (visitOn (crossingTransport hs j) a (s176_mem_left hjab)))
    (_hSf : (r176l_Sf (transportSupport hs (Q ∪ {j})) (crossingTransport hs u) (crossingTransport hs v)) ∈ CV.Ind (geomAt E t' ht'.1))
    (y : (CV.carrierDiagram hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj)
      (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)).Γ.Crossing)
    (_hy : y = est_liftCrossing hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj) _ hu' ∨
      y = est_liftCrossing hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj) _ hv'),
    Nonempty (r176_OuterDataL hn hL hR hef heg hfg ht ht' hop hs hQ hfull hj q huac hvbc y)

/-! ## §X2. The (14)-bridge: `2ℓ` is the number of mask-`uv` survivors -/

/-- **The mixed crossings of `D_A` are the mask-`uv` survivors — BLACK BOX (OPEN)**: for the outer-carrier data
`O`, the mixed sign sum of the two components `i` (the `B`-class of `v₀`) and `j` (the `A`-class of `τ v₀`) of
`D_A = r176s_DA D₊ y` is the number of retained crossings of `q₀'` unselected in `S_full` with one visit on each
child (`r176l_mixedSet`).  Route: `r176l_mixedSignSum_eq_card` (every crossing of the positive lift is `+1`,
`geoPositiveLift_sign`; the smoothing keeps the other crossings and creates none) reduces it to a bijection of
the mixed crossings of `D_A` with `r176l_mixedSet`, through `r176s_smooth_comp_eq_pair_iff` /
`r176s_smooth_comp_eq_self_iff` (a crossing is mixed iff its two occurrences lie on different arcs) and the
parent-key reading `r176s_arcA_iff_key`.  Estimate ≈ 400–700 lines. -/
def r176_mixed_bridge : Prop :=
  ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (E : CV.Event n) (e f g : ZMod n) (δ : ℝ)
    (hL : LocalizationData E e f g δ) (hR : AV_EventRadius E δ) (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
    (t t' : E.Parameter) (ht : Punctured E δ t) (ht' : Punctured E δ t') (hop : OppositeSides E t t')
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    (hef' : IsCrossing (E.curve t) {e, f}) (heg' : IsCrossing (E.curve t) {e, g})
    (hfg' : IsCrossing (E.curve t) {f, g}) (_hcomp : CompleteLocal (geomAt E t ht.1) hef' heg' hfg')
    (Q : Finset (Crossing (E.curve t))) (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
    (hfull : FullAvail (geomAt E t ht.1) e f g Q) (j : Crossing (E.curve t))
    (hj : j.val ∈ triangleSupports e f g) (q : GeoComponent (geomAt E t ht.1) (Q ∪ {j}))
    (a b c : ZMod n) (_hab : a ≠ b) (_hac : a ≠ c) (_hbc : b ≠ c)
    (_habc : ({a, b, c} : Finset (ZMod n)) = {e, f, g}) (u v : Crossing (E.curve t))
    (hjab : j.val = {a, b}) (huac : u.val = {a, c}) (hvbc : v.val = {b, c})
    (_hu : u.val ∈ triangleSupports e f g) (_hv : v.val ∈ triangleSupports e f g)
    (_hju : j ≠ u) (_hjv : j ≠ v) (_huv : u ≠ v)
    (hu' : crossingTransport hs u ∈ geoCarrierCrossings (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j}))
      (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q))
    (hv' : crossingTransport hs v ∈ geoCarrierCrossings (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j}))
      (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q))
    (_hlt_a : visitParameter (visitOn (crossingTransport hs u) a (s176_mem_left huac)) <
      visitParameter (visitOn (crossingTransport hs j) a (s176_mem_left hjab)))
    (_hSf : (r176l_Sf (transportSupport hs (Q ∪ {j})) (crossingTransport hs u) (crossingTransport hs v)) ∈ CV.Ind (geomAt E t' ht'.1))
    (y : (CV.carrierDiagram hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj)
      (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)).Γ.Crossing)
    (_hy : y = est_liftCrossing hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj) _ hu' ∨
      y = est_liftCrossing hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj) _ hv')
    (O : r176_OuterDataL hn hL hR hef heg hfg ht ht' hop hs hQ hfull hj q huac hvbc y),
    mixedSignSum (r176s_DA (CV.carrierDiagram hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj)
      (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)) y) (r176s_DA_i (CV.carrierDiagram hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj)
      (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)) y O.v₀ O.hv₀) (r176s_DA_j (CV.carrierDiagram hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj)
      (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)) y O.v₀ O.hv₀) =
      ((r176l_mixedSet (genericAt E t' ht'.1).crossingGeometry (transportSupport hs (Q ∪ {j})) (r176l_Sf (transportSupport hs (Q ∪ {j})) (crossingTransport hs u) (crossingTransport hs v)) (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)
        (r176l_L1 (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j})) (crossingTransport hs u)
        (v := crossingTransport hs v) hvbc) (r176l_L2 (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j})) (crossingTransport hs v)
        (u := crossingTransport hs u) huac)).card : ℤ)

/-! ## §X3. The connector: the LEDGER's `r176l_SmoothData` from SMOOTH's constructions -/

/-- **The LEDGER's smoothing data from SMOOTH's constructions**: `D_A = r176s_DA D₊ y` (the library smoothing),
`IsOrientedSmoothing` (`r176s_DA_smooth`), two components (`r176s_DA_componentCount`), the tags `i` (`B`-class of
`v₀`) and `j` (`A`-class of `τ v₀`) with `i ≠ j`, the exact owner map (9)/(9a) — `poly₁` for the kinked child
`Λ₁ = r176l_L1` through the record-level R-I black box and `r176s_knotRestrictIso_i`, `poly₂` for the clean child
`Λ₂ = r176l_L2` through `r176s_knotRestrictIso_j` and `CV.liftRestrictRecordIso` — and the (14)-bridge as a
hypothesis. -/
def r176_smoothData_of (hcurl : r176s_curl_removal) (hn : 3 ≤ n) (hL : LocalizationData E e f g δ)
    (hR : AV_EventRadius E δ) (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g) {t t' : E.Parameter}
    (ht : Punctured E δ t) (ht' : Punctured E δ t') (hop : OppositeSides E t t')
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    {Q : Finset (Crossing (E.curve t))} (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
    (hfull : FullAvail (geomAt E t ht.1) e f g Q) {j : Crossing (E.curve t)}
    (hj : j.val ∈ triangleSupports e f g) (q : GeoComponent (geomAt E t ht.1) (Q ∪ {j}))
    {a b c : ZMod n} {u v : Crossing (E.curve t)} (huac : u.val = {a, c}) (hvbc : v.val = {b, c})
    (y : (CV.carrierDiagram hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj)
      (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)).Γ.Crossing)
    (O : r176_OuterDataL hn hL hR hef heg hfg ht ht' hop hs hQ hfull hj q huac hvbc y)
    (hSf : (r176l_Sf (transportSupport hs (Q ∪ {j})) (crossingTransport hs u) (crossingTransport hs v)) ∈ CV.Ind (geomAt E t' ht'.1))
    (hmixed : mixedSignSum (r176s_DA (CV.carrierDiagram hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj)
      (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)) y) (r176s_DA_i (CV.carrierDiagram hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj)
      (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)) y O.v₀ O.hv₀) (r176s_DA_j (CV.carrierDiagram hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj)
      (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)) y O.v₀ O.hv₀) =
      ((r176l_mixedSet (genericAt E t' ht'.1).crossingGeometry (transportSupport hs (Q ∪ {j})) (r176l_Sf (transportSupport hs (Q ∪ {j})) (crossingTransport hs u) (crossingTransport hs v)) (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)
        (r176l_L1 (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j})) (crossingTransport hs u)
        (v := crossingTransport hs v) hvbc) (r176l_L2 (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j})) (crossingTransport hs v)
        (u := crossingTransport hs u) huac)).card : ℤ)) :
    r176l_SmoothData hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj) (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q) y (r176l_Sf (transportSupport hs (Q ∪ {j})) (crossingTransport hs u) (crossingTransport hs v)) hSf
      (r176l_L1 (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j})) (crossingTransport hs u)
        (v := crossingTransport hs v) hvbc) (r176l_L2 (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j})) (crossingTransport hs v)
        (u := crossingTransport hs u) huac) := by
  have hD1 : (CV.carrierDiagram hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj)
      (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)).componentCount = 1 := geoPositiveLift_componentCount hn _ _ _
  refine
    { DA := r176s_DA _ y, smooth := r176s_DA_smooth _ y, two := r176s_DA_componentCount _ y hD1,
      i := r176s_DA_i _ y O.v₀ O.hv₀, j := r176s_DA_j _ y O.v₀ O.hv₀, ij := r176s_DA_ij _ y hD1 O.v₀ O.hv₀,
      poly₁ := ?_, poly₂ := ?_, mixed := hmixed }
  · -- (9a) the kinked child `Λ₁`: the record-level R-I removes the kink
    rw [GT_groupedPoly_eq_homfly]
    exact r176s_homfly_of_liftBlock_curl hcurl hn (r176s_cgL hn ht')
      (CV.geoIndependent_of_mem_Ind _ (est_S'_ind hL ht ht' hop hs hQ hfull hj))
      (CV.geoIndependent_of_mem_Ind _ hSf) _ (r176l_L1 (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j})) (crossingTransport hs u)
        (v := crossingTransport hs v) hvbc) O.subB _ _ O.r O.KB_eq O.r_not O.r_curl
      ⟨r176s_knotRestrictIso_i _ _ hD1 O.v₀ O.hv₀⟩
  · -- (9) the clean child `Λ₂`
    rw [GT_groupedPoly_eq_homfly]
    exact r176s_homfly_of_liftBlock hn (r176s_cgL hn ht')
      (CV.geoIndependent_of_mem_Ind _ (est_S'_ind hL ht ht' hop hs hQ hfull hj))
      (CV.geoIndependent_of_mem_Ind _ hSf) _ (r176l_L2 (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j})) (crossingTransport hs v)
        (u := crossingTransport hs u) huac) O.subA _ _ O.KA_eq
      ⟨r176s_knotRestrictIso_j _ _ hD1 O.v₀ O.hv₀⟩

/-! ## §X4. The LEDGER's event-level chain against the connector -/

/-- `r176l_portDataRest_case1` with the SMOOTH black box replaced by the connector `r176_smoothData_of` on the
open Props `r176_outer_carriers_L`, `r176s_curl_removal`, `r176_mixed_bridge` (body otherwise byte-identical). -/
theorem r176_portDataRest_case1 (hcurl : r176s_curl_removal) (hout : r176_outer_carriers_L)
    (hmixed : r176_mixed_bridge) (hn : 3 ≤ n)
    (hL : LocalizationData E e f g δ) (hR : AV_EventRadius E δ) (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
    {t t' : E.Parameter} (ht : Punctured E δ t) (ht' : Punctured E δ t') (hop : OppositeSides E t t')
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    {hef' : IsCrossing (E.curve t) {e, f}} {heg' : IsCrossing (E.curve t) {e, g}}
    {hfg' : IsCrossing (E.curve t) {f, g}} (hcomp : CompleteLocal (geomAt E t ht.1) hef' heg' hfg')
    {Q : Finset (Crossing (E.curve t))} (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
    (hfull : FullAvail (geomAt E t ht.1) e f g Q) {j : Crossing (E.curve t)}
    (hj : j.val ∈ triangleSupports e f g) (q : GeoComponent (geomAt E t ht.1) (Q ∪ {j}))
    (hwind : CV.wind (geomAt E t ht.1) (Q ∪ {j}) ≠ 0)
    {a b c : ZMod n} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (habc : ({a, b, c} : Finset (ZMod n)) = {e, f, g}) {u v : Crossing (E.curve t)}
    (hjab : j.val = {a, b}) (huac : u.val = {a, c}) (hvbc : v.val = {b, c})
    (hu : u.val ∈ triangleSupports e f g) (hv : v.val ∈ triangleSupports e f g)
    (hju : j ≠ u) (hjv : j ≠ v) (huv : u ≠ v)
    (hu' : crossingTransport hs u ∈ geoCarrierCrossings (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j}))
      (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q))
    (hv' : crossingTransport hs v ∈ geoCarrierCrossings (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j}))
      (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q))
    (hlt_a : visitParameter (visitOn (crossingTransport hs u) a (s176_mem_left huac)) <
      visitParameter (visitOn (crossingTransport hs j) a (s176_mem_left hjab)))
    (y : (CV.carrierDiagram hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj)
      (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)).Γ.Crossing)
    (hy : y = est_liftCrossing hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj) _ hu' ∨
      y = est_liftCrossing hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj) _ hv') :
    Nonempty (s176_PortDataRest hn (genericAt E t ht.1) (genericAt E t' ht'.1) (est_S_ind ht.1 hQ hfull hj)
      (est_S'_ind hL ht ht' hop hs hQ hfull hj) q
      (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q) y) := by
  have hS := est_S_ind ht.1 hQ hfull hj
  have hS' := est_S'_ind hL ht ht' hop hs hQ hfull hj
  -- the `L` side
  have hs' : ∀ s, IsCrossing (E.curve t') s ↔ IsCrossing (E.curve t) s := fun s => (hs s).symm
  have hop' : OppositeSides E t' t := by
    unfold OppositeSides at hop ⊢; linarith [mul_comm t.val t'.val]
  have hXL : ExactTriangleVisitOrders (E.curve t') (E.curve t) a b c hs' :=
    gu2_exact_of_eq hs' habc.symm (hL.gauss_words t' t ht' ht hop' hs')
  have hGL : CarrierGeometry (E.curve t') :=
    CarrierGeometry.ofDiagrammatic ((genericAt E t' ht'.1).diagrammatic hn)
  have hT : GeoIndependent (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j})) :=
    CV.geoIndependent_of_mem_Ind _ hS'
  have hjT : crossingTransport hs j ∈ transportSupport hs (Q ∪ {j}) :=
    (mem_transportSupport_iff hs _ j).mpr (Finset.mem_union_right _ (Finset.mem_singleton_self j))
  -- the successor facts of case 1
  have hρa : geoMarkSuccessor (geomAt E t' ht'.1) (Sum.inr (r176l_ua (u := crossingTransport hs u) huac)) =
      Sum.inr (visitOn (crossingTransport hs j) a (s176_mem_left hjab)) :=
    gu1_markSuccessor_eq_of_adjacent hn _ rfl hlt_a
      (fun w hw => (s176_nb_a hs' hab hac hbc hXL (j := crossingTransport hs j) (u := crossingTransport hs u)
        hjab huac w hw).1)
  have hlt_b := (s176_cyclic hn hGL hs' hT (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q) hab hac hbc hXL (j := crossingTransport hs j)
    (u := crossingTransport hs u) (v := crossingTransport hs v) hjab huac hvbc hjT hu' hv').mp hlt_a
  have hρb : geoMarkSuccessor (geomAt E t' ht'.1) (Sum.inr (visitOn (crossingTransport hs j) b (s176_mem_right hjab))) =
      Sum.inr (visitOn (crossingTransport hs v) b (s176_mem_left hvbc)) :=
    gu1_markSuccessor_eq_of_adjacent hn _ rfl hlt_b
      (fun w hw => (s176_nb_b hs' hab hac hbc hXL (j := crossingTransport hs j) (v := crossingTransport hs v)
        hjab hvbc w hw).1)
  have hnb_c := fun (w : Visit (E.curve t')) (hw : w.2.val = c) =>
    s176_nb_c hs' hab hac hbc hXL (u := crossingTransport hs u) (v := crossingTransport hs v) huac hvbc w hw
  -- the full support
  have hSf : GeoIndependent (geomAt E t' ht'.1)
      (r176l_Sf (transportSupport hs (Q ∪ {j})) (crossingTransport hs u) (crossingTransport hs v)) :=
    r176l_Sf_indep_event hL ht ht' hop hs hcomp hQ hfull hj hu hv hju hjv huv
  have hSf' : r176l_Sf (transportSupport hs (Q ∪ {j})) (crossingTransport hs u) (crossingTransport hs v) ∈
      CV.Ind (geomAt E t' ht'.1) := (CV.mem_Ind_iff _ _).mpr hSf
  -- uniformity, carried
  obtain ⟨σ, hσ, huniH⟩ := (CV.wind_ne_zero_imp (geomAt E t ht.1) (Q ∪ {j}) hwind).2 q
  have huni := r176l_uniform_transport hn hL hR hef heg hfg ht ht' hop hs hQ hfull hj q huniH
  -- regularity
  have hreg : ∀ (S : Finset (Crossing (E.curve t'))) (r : GeoComponent (geomAt E t' ht'.1) S),
      GeoIndependent (geomAt E t' ht'.1) S → CV.Regular (geoCornerPolygon (geomAt E t' ht'.1) S r) :=
    fun S r hind => CV.carrierPolygon_cvRegular hn (genericAt E t' ht'.1) ((CV.mem_Ind_iff _ _).mpr hind) r
  -- the ledger
  have LD := r176l_ledgerData_case1 hn (geomAt E t' ht'.1) hT (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q) hab hac hbc
    (j := crossingTransport hs j) (u := crossingTransport hs u) (v := crossingTransport hs v) hjab huac hvbc hjT
    hu' hv' hρa hρb hSf hlt_a hlt_b hnb_c hσ huni hreg
  -- the smoothing data: SMOOTH's constructions on the outer carriers, the curl removal, the mixed bridge
  obtain ⟨O⟩ := hout n hn E e f g δ hL hR hef heg hfg t t' ht ht' hop hs hef' heg' hfg' hcomp Q hQ hfull j hj q
    a b c hab hac hbc habc u v hjab huac hvbc hu hv hju hjv huv hu' hv' hlt_a hSf' y hy
  have D := r176_smoothData_of hcurl hn hL hR hef heg hfg ht ht' hop hs hQ hfull hj q huac hvbc y O hSf'
    (hmixed n hn E e f g δ hL hR hef heg hfg t t' ht ht' hop hs hef' heg' hfg' hcomp Q hQ hfull j hj q
      a b c hab hac hbc habc u v hjab huac hvbc hu hv hju hjv huv hu' hv' hlt_a hSf' y hy O)
  -- (14): the writhe shift (7) and the `L`-side count
  have hcu : c ∈ u.val := s176_mem_right huac
  have hcv : c ∈ v.val := s176_mem_right hvbc
  have hcj : c ∉ j.val := by
    rw [hjab, Finset.mem_insert, Finset.mem_singleton]
    rintro (h | h)
    · exact hac h.symm
    · exact hbc h.symm
  have howner_u : geoOwner (geomAt E t ht.1) (Q ∪ {j}) (Sum.inr (visitOn u c hcu)) = q :=
    (est_retained_u_iff hL hR hef heg hfg ht ht' hop hs hcomp hQ hfull hj hu hju hcu hcj q).mp hu'
  have h7 := est_groupedWrithe_affected hL hR hef heg hfg ht ht' hop hs hcomp hQ hfull hj hu hv hju hjv huv hcu hcv
    q howner_u
  have hcard := LD.card
  have hw : CV.groupedWrithe (genericAt E t ht.1) q =
      CV.groupedWrithe (genericAt E t' ht'.1)
          (r176l_L1 (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j})) (crossingTransport hs u) (v := crossingTransport hs v) hvbc) +
        CV.groupedWrithe (genericAt E t' ht'.1)
          (r176l_L2 (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j})) (crossingTransport hs v) (u := crossingTransport hs u) huac) +
        ((r176l_mixedSet (genericAt E t' ht'.1).crossingGeometry (transportSupport hs (Q ∪ {j}))
          (r176l_Sf (transportSupport hs (Q ∪ {j})) (crossingTransport hs u) (crossingTransport hs v))
          (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)
          (r176l_L1 (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j})) (crossingTransport hs u) (v := crossingTransport hs v) hvbc)
          (r176l_L2 (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j})) (crossingTransport hs v) (u := crossingTransport hs u) huac)).card : ℤ) := by
    rw [CV.groupedWrithe_eq_card_geoCarrierCrossings _ hS'] at h7
    rw [CV.groupedWrithe_eq_card_geoCarrierCrossings _ hSf', CV.groupedWrithe_eq_card_geoCarrierCrossings _ hSf']
    have hc' : ((geoCarrierCrossings (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j})) (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)).card : ℤ) =
        _ := congrArg (fun m : ℕ => (m : ℤ)) hcard
    push_cast at hc'
    linarith
  -- (13)
  have hrot := r176l_rot_ledger hn (genericAt E t ht.1) (genericAt E t' ht'.1) hS hS' q (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)
    (hSf := hSf') hσ (GT_carrierR_eq hn (genericAt E t ht.1) (genericAt E t' ht'.1) (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) hS hS' q) LD.rot_add
    LD.shape₁ LD.shape₂
  -- (12)
  have halt := r176l_alt_of_shape hn (genericAt E t' ht'.1) (hSf := hSf') hσ LD.shape₁ LD.shape₂
  exact ⟨r176l_portDataRest_of hn (genericAt E t ht.1) (genericAt E t' ht'.1) hS hS' q (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q) y D hw
    hrot halt.1 halt.2⟩

/-- `r176l_portDataRest_labelled` against `r176_portDataRest_case1` (body byte-identical). -/
theorem r176_portDataRest_labelled (hcurl : r176s_curl_removal) (hout : r176_outer_carriers_L)
    (hmixed : r176_mixed_bridge) (hn : 3 ≤ n)
    (hL : LocalizationData E e f g δ) (hR : AV_EventRadius E δ) (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
    {t t' : E.Parameter} (ht : Punctured E δ t) (ht' : Punctured E δ t') (hop : OppositeSides E t t')
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    {hef' : IsCrossing (E.curve t) {e, f}} {heg' : IsCrossing (E.curve t) {e, g}}
    {hfg' : IsCrossing (E.curve t) {f, g}} (hcomp : CompleteLocal (geomAt E t ht.1) hef' heg' hfg')
    {Q : Finset (Crossing (E.curve t))} (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
    (hfull : FullAvail (geomAt E t ht.1) e f g Q) {j : Crossing (E.curve t)}
    (hj : j.val ∈ triangleSupports e f g) (q : GeoComponent (geomAt E t ht.1) (Q ∪ {j}))
    (hwind : CV.wind (geomAt E t ht.1) (Q ∪ {j}) ≠ 0)
    {u : Crossing (E.curve t)} (hu : u.val ∈ triangleSupports e f g) (hju : j ≠ u)
    (hu' : crossingTransport hs u ∈ geoCarrierCrossings (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j}))
      (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q))
    {a b c : ZMod n} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (habc : ({a, b, c} : Finset (ZMod n)) = {e, f, g})
    (hjab : j.val = {a, b}) (huac : u.val = {a, c}) {v : Crossing (E.curve t)} (hvbc : v.val = {b, c})
    (hv : v.val ∈ triangleSupports e f g) (hjv : j ≠ v) (huv : u ≠ v) :
    Nonempty (s176_PortDataRest hn (genericAt E t ht.1) (genericAt E t' ht'.1) (est_S_ind ht.1 hQ hfull hj)
      (est_S'_ind hL ht ht' hop hs hQ hfull hj) q
      (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)
      (est_liftCrossing hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj) _ hu')) := by
  obtain ⟨hv', -, -⟩ := s176_event_site_core hn hL hR hef heg hfg ht ht' hop hs hcomp hQ hfull hj q hu hju hu'
    hab hac hbc habc hjab huac hvbc hv hjv huv
  have hS' := est_S'_ind hL ht ht' hop hs hQ hfull hj
  have hs' : ∀ s, IsCrossing (E.curve t') s ↔ IsCrossing (E.curve t) s := fun s => (hs s).symm
  have hop' : OppositeSides E t' t := by
    unfold OppositeSides at hop ⊢; linarith [mul_comm t.val t'.val]
  have hXL : ExactTriangleVisitOrders (E.curve t') (E.curve t) a b c hs' :=
    gu2_exact_of_eq hs' habc.symm (hL.gauss_words t' t ht' ht hop' hs')
  have hGL : CarrierGeometry (E.curve t') :=
    CarrierGeometry.ofDiagrammatic ((genericAt E t' ht'.1).diagrammatic hn)
  have hT : GeoIndependent (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j})) :=
    CV.geoIndependent_of_mem_Ind _ hS'
  have hjT : crossingTransport hs j ∈ transportSupport hs (Q ∪ {j}) :=
    (mem_transportSupport_iff hs _ j).mpr (Finset.mem_union_right _ (Finset.mem_singleton_self j))
  have hju' : crossingTransport hs u ≠ crossingTransport hs j := (crossingTransport hs).injective.ne hju.symm
  have hjv' : crossingTransport hs v ≠ crossingTransport hs j := (crossingTransport hs).injective.ne hjv.symm
  have hcyc := s176_cyclic hn hGL hs' hT (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)
    hab hac hbc hXL (j := crossingTransport hs j) (u := crossingTransport hs u) (v := crossingTransport hs v)
    hjab huac hvbc hjT hu' hv'
  rcases lt_or_gt_of_ne (r176l_param_ne (geomAt E t' ht'.1) hju' (s176_mem_left huac) (s176_mem_left hjab)) with
    hlt | hgt
  · exact r176_portDataRest_case1 hcurl hout hmixed hn hL hR hef heg hfg ht ht' hop hs hcomp hQ hfull hj q hwind hab hac hbc
      habc hjab huac hvbc hu hv hju hjv huv hu' hv' hlt _ (Or.inl rfl)
  · -- case 2: relabel `(b, a, c), (j, v, u)`
    have hnlt : ¬ visitParameter (visitOn (crossingTransport hs j) b (s176_mem_right hjab)) <
        visitParameter (visitOn (crossingTransport hs v) b (s176_mem_left hvbc)) :=
      fun h => lt_asymm hgt (hcyc.mpr h)
    have hlt_b : visitParameter (visitOn (crossingTransport hs v) b (s176_mem_left hvbc)) <
        visitParameter (visitOn (crossingTransport hs j) b (s176_mem_right hjab)) :=
      lt_of_le_of_ne (not_lt.mp hnlt) (r176l_param_ne (geomAt E t' ht'.1) hjv' (s176_mem_left hvbc) (s176_mem_right hjab))
    have habc' : ({b, a, c} : Finset (ZMod n)) = {e, f, g} := (Finset.insert_comm b a {c}).trans habc
    exact r176_portDataRest_case1 hcurl hout hmixed hn hL hR hef heg hfg ht ht' hop hs hcomp hQ hfull hj q hwind
      (a := b) (b := a) (c := c) hab.symm hbc hac habc' (u := v) (v := u) (s176_pair_comm' hjab) hvbc huac hv hu hjv hju
      huv.symm hv' hu' hlt_b _ (Or.inr rfl)

/-- **The `hrest` obligation of row 176 under `wind(S) ≠ 0` from the open Props** — `r176l_portDataRest_of_uniform`
against `r176_portDataRest_labelled` (body byte-identical). -/
theorem r176_portDataRest_of_uniform (hcurl : r176s_curl_removal) (hout : r176_outer_carriers_L)
    (hmixed : r176_mixed_bridge) (hn : 3 ≤ n)
    (hL : LocalizationData E e f g δ) (hR : AV_EventRadius E δ) (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
    {t t' : E.Parameter} (ht : Punctured E δ t) (ht' : Punctured E δ t') (hop : OppositeSides E t t')
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    (hef' : IsCrossing (E.curve t) {e, f}) (heg' : IsCrossing (E.curve t) {e, g})
    (hfg' : IsCrossing (E.curve t) {f, g}) (hcomp : CompleteLocal (geomAt E t ht.1) hef' heg' hfg')
    {Q : Finset (Crossing (E.curve t))} (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
    (hfull : FullAvail (geomAt E t ht.1) e f g Q) {j : Crossing (E.curve t)}
    (hj : j.val ∈ triangleSupports e f g) (q : GeoComponent (geomAt E t ht.1) (Q ∪ {j}))
    (hwind : CV.wind (geomAt E t ht.1) (Q ∪ {j}) ≠ 0)
    {u : Crossing (E.curve t)} (hu : u.val ∈ triangleSupports e f g) (hju : j ≠ u)
    (hu' : crossingTransport hs u ∈ geoCarrierCrossings (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j}))
      (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)) :
    Nonempty (s176_PortDataRest hn (genericAt E t ht.1) (genericAt E t' ht'.1) (est_S_ind ht.1 hQ hfull hj)
      (est_S'_ind hL ht ht' hop hs hQ hfull hj) q
      (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)
      (est_liftCrossing hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj) _ hu')) := by
  have h1 : (xPair hef').val ∈ triangleSupports e f g := (P1.mem_triangleSupports _).mpr (Or.inl rfl)
  have h2 : (xPair heg').val ∈ triangleSupports e f g := (P1.mem_triangleSupports _).mpr (Or.inr (Or.inl rfl))
  have h3 : (xPair hfg').val ∈ triangleSupports e f g := (P1.mem_triangleSupports _).mpr (Or.inr (Or.inr rfl))
  have n12 := P1.xPair_ef_ne_eg hef' heg' hfg'
  have n13 := P1.xPair_ef_ne_fg hef' heg' hfg'
  have n23 := P1.xPair_eg_ne_fg hef' heg' hfg'
  have key : ∀ {a b c : ZMod n} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
      (habc : ({a, b, c} : Finset (ZMod n)) = {e, f, g})
      (hjab : j.val = {a, b}) (huac : u.val = {a, c}) {v : Crossing (E.curve t)} (hvbc : v.val = {b, c})
      (hv : v.val ∈ triangleSupports e f g) (hjv : j ≠ v) (huv : u ≠ v),
      Nonempty (s176_PortDataRest hn (genericAt E t ht.1) (genericAt E t' ht'.1) (est_S_ind ht.1 hQ hfull hj)
        (est_S'_ind hL ht ht' hop hs hQ hfull hj) q
        (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)
        (est_liftCrossing hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj) _ hu')) :=
    fun {a b c} hab hac hbc habc hjab huac {v} hvbc hv hjv huv =>
      r176_portDataRest_labelled hcurl hout hmixed hn hL hR hef heg hfg ht ht' hop hs hcomp hQ hfull hj q hwind hu hju hu'
        hab hac hbc habc hjab huac (v := v) hvbc hv hjv huv
  have p_feg : ({f, e, g} : Finset (ZMod n)) = {e, f, g} := Finset.insert_comm f e {g}
  have p_egf : ({e, g, f} : Finset (ZMod n)) = {e, f, g} := congrArg (insert e) (Finset.pair_comm g f)
  have p_gef : ({g, e, f} : Finset (ZMod n)) = {e, f, g} :=
    (Finset.insert_comm g e {f}).trans (congrArg (insert e) (Finset.pair_comm g f))
  have p_fge : ({f, g, e} : Finset (ZMod n)) = {e, f, g} :=
    (congrArg (insert f) (Finset.pair_comm g e)).trans (Finset.insert_comm f e {g})
  have p_gfe : ({g, f, e} : Finset (ZMod n)) = {e, f, g} :=
    ((congrArg (insert g) (Finset.pair_comm f e)).trans (Finset.insert_comm g e {f})).trans
      (congrArg (insert e) (Finset.pair_comm g f))
  rcases GT_tri_cases t hef' heg' hfg' j hj with rfl | rfl | rfl <;>
    rcases GT_tri_cases t hef' heg' hfg' u hu with rfl | rfl | rfl
  · exact absurd rfl hju
  · exact key hef heg hfg rfl rfl rfl (v := xPair hfg') rfl h3 n13 n23
  · exact key hef.symm hfg heg p_feg (Finset.pair_comm e f) rfl (v := xPair heg') rfl h2 n12 n23.symm
  · exact key heg hef hfg.symm p_egf rfl rfl (v := xPair hfg') (Finset.pair_comm f g) h3 n23 n13
  · exact absurd rfl hju
  · exact key heg.symm hfg.symm hef p_gef (Finset.pair_comm e g) (Finset.pair_comm f g) (v := xPair hef') rfl h1
      n12.symm n13.symm
  · exact key hfg hef.symm heg.symm p_fge rfl (Finset.pair_comm e f) (v := xPair heg') (Finset.pair_comm e g) h2
      n23.symm n12
  · exact key hfg.symm heg.symm hef.symm p_gfe (Finset.pair_comm f g) (Finset.pair_comm e g) (v := xPair hef')
      (Finset.pair_comm e f) h1 n13.symm n12.symm
  · exact absurd rfl hju


/-- **The weak interface of row 176 under `wind(S) ≠ 0` from exactly the open Props**: the record-level R-I
`r176s_curl_removal`, the outer carriers `r176_outer_carriers_L`, the (14)-bridge `r176_mixed_bridge`; the port
is HSUCC's `r176h_est_port_weak` (`hrec` CLOSED), the non-move data the LEDGER's chain through the connector. -/
theorem r176_est_port_relation_weak_uniform_of_curl_outer_mixed (hcurl : r176s_curl_removal)
    (hout : r176_outer_carriers_L) (hmixed : r176_mixed_bridge) : r176l_est_port_relation_weak_uniform := by
  intro n _ hn E e f g δ hL hR hef heg hfg t t' ht ht' hop hs hef' heg' hfg' hcomp Q hQ hfull j hj q hwind hex
  obtain ⟨u, hu, hju, hu'⟩ := hex
  obtain ⟨R⟩ := r176_portDataRest_of_uniform hcurl hout hmixed hn hL hR hef heg hfg ht ht' hop hs hef' heg' hfg'
    hcomp hQ hfull hj q hwind hu hju.symm hu'
  refine ⟨u, hu, hju, hu', ⟨s176_PortDataWeak.mk' _ _ _ _ _ _ _ _ ?_ R⟩⟩
  exact r176h_est_port_weak hn hL hR hef heg hfg ht ht' hop hs hef' heg' hfg' hcomp hQ hfull hj q hu hju.symm hu'

/-- **The weak interface under `wind(S) ≠ 0` from the non-move port data alone, in the CORRECTED `hrest` form**
(the binders carry `hcomp`, `hu`, `hju` — R176_SMOOTH_REPORT §4 — and `wind(S) ≠ 0` — R176_LEDGER_REPORT §3). -/
theorem r176_est_port_relation_weak_uniform_of_rest
    (hrest : ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (E : CV.Event n) (e f g : ZMod n) (δ : ℝ)
      (hL : LocalizationData E e f g δ) (hR : AV_EventRadius E δ) (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
      (t t' : E.Parameter) (ht : Punctured E δ t) (ht' : Punctured E δ t') (hop : OppositeSides E t t')
      (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
      (hef' : IsCrossing (E.curve t) {e, f}) (heg' : IsCrossing (E.curve t) {e, g})
      (hfg' : IsCrossing (E.curve t) {f, g}) (_hcomp : CompleteLocal (geomAt E t ht.1) hef' heg' hfg')
      (Q : Finset (Crossing (E.curve t))) (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
      (hfull : FullAvail (geomAt E t ht.1) e f g Q) (j : Crossing (E.curve t))
      (hj : j.val ∈ triangleSupports e f g) (q : GeoComponent (geomAt E t ht.1) (Q ∪ {j})),
      CV.wind (geomAt E t ht.1) (Q ∪ {j}) ≠ 0 →
      ∀ (u : Crossing (E.curve t)) (_hu : u.val ∈ triangleSupports e f g) (_hju : j ≠ u)
        (hu' : crossingTransport hs u ∈ geoCarrierCrossings (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j}))
          (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)),
      Nonempty (s176_PortDataRest hn (genericAt E t ht.1) (genericAt E t' ht'.1) (est_S_ind ht.1 hQ hfull hj)
        (est_S'_ind hL ht ht' hop hs hQ hfull hj) q
        (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)
        (est_liftCrossing hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj) _ hu'))) :
    r176l_est_port_relation_weak_uniform := by
  intro n _ hn E e f g δ hL hR hef heg hfg t t' ht ht' hop hs hef' heg' hfg' hcomp Q hQ hfull j hj q hwind hex
  obtain ⟨u, hu, hju, hu'⟩ := hex
  obtain ⟨R⟩ := hrest n hn E e f g δ hL hR hef heg hfg t t' ht ht' hop hs hef' heg' hfg' hcomp Q hQ hfull j hj q
    hwind u hu hju.symm hu'
  refine ⟨u, hu, hju, hu', ⟨s176_PortDataWeak.mk' _ _ _ _ _ _ _ _ ?_ R⟩⟩
  exact r176h_est_port_weak hn hL hR hef heg hfg ht ht' hop hs hef' heg' hfg' hcomp hQ hfull hj q hu hju.symm hu'

/-! ## §X5. The consumer split on `wind(S) = 0`: the corrected interface suffices for the RA ledger -/

/-- `s176_est_row_H_weak` (= `est_row_H`, RALedgers.lean:1514) with the interface under `wind(S) ≠ 0`: when
`wind(S) = 0` the selector is carried across the wall (`GT_wind_eq`) and both present rows are
`wind · ∏ Ω₁ = 0` (`rowTerm_of_mem_Ind`) — the printed "If the common singleton selector is zero, the matched
selector ledger already makes both terms in (2) zero"; when `wind(S) ≠ 0` the body is that of `est_row_H`.
This is the `est_row_H` split that R176_LEDGER_REPORT §3 asks of RALedgers, made on the draft copy. -/
theorem r176_est_row_H_weak_uniform (hF : CV.CarrierSlotFloor) (hport : r176l_est_port_relation_weak_uniform)
    (hn : 3 ≤ n) (hL : LocalizationData E e f g δ) (hR : AV_EventRadius E δ) (hef : e ≠ f) (heg : e ≠ g)
    (hfg : f ≠ g) {t t' : E.Parameter} (ht : Punctured E δ t) (ht' : Punctured E δ t') (hop : OppositeSides E t t')
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    {hef' : IsCrossing (E.curve t) {e, f}} {heg' : IsCrossing (E.curve t) {e, g}}
    {hfg' : IsCrossing (E.curve t) {f, g}} (hcomp : CompleteLocal (geomAt E t ht.1) hef' heg' hfg')
    {Q : Finset (Crossing (E.curve t))} (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
    (hfull : FullAvail (geomAt E t ht.1) e f g Q) {j : Crossing (E.curve t)}
    (hj : j.val ∈ triangleSupports e f g) :
    rowTerm hn (genericAt E t ht.1) (Q ∪ {j}) =
      rowTerm hn (genericAt E t' ht'.1) (transportSupport hs (Q ∪ {j})) := by
  set W := est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj
  have hS := est_S_ind ht.1 hQ hfull hj
  have hS' := est_S'_ind hL ht ht' hop hs hQ hfull hj
  by_cases hwind : CV.wind (geomAt E t ht.1) (Q ∪ {j}) = 0
  · -- `wind(S) = 0`: the selector is carried, both row terms vanish
    have h0 : CV.wind (genericAt E t ht.1).crossingGeometry (Q ∪ {j}) = 0 := hwind
    have h0' : CV.wind (genericAt E t' ht'.1).crossingGeometry (transportSupport hs (Q ∪ {j})) = 0 := by
      rw [GT_wind_eq hn (genericAt E t ht.1) (genericAt E t' ht'.1) W]; exact h0
    rw [rowTerm_of_mem_Ind hn (genericAt E t ht.1) hS, rowTerm_of_mem_Ind hn (genericAt E t' ht'.1) hS', h0, h0',
      zero_mul, zero_mul]
  · -- `wind(S) ≠ 0`: `est_row_H` verbatim, the port relation at `hwind`
    refine est_rowTerm_eq_of_omega hn _ _ hS hS'
      (GT_wind_eq hn (genericAt E t ht.1) (genericAt E t' ht'.1) W) (GT_carrierEquiv W) fun q => ?_
    obtain ⟨u, v, hu, hv, hju, hjv, huv⟩ := est_others hef' heg' hfg' hj
    obtain ⟨ℓ, hℓu, hℓv⟩ := GT_shared_label hu hv huv
    have hℓj := est_shared_not_mem_third hef heg hfg hj hu hv hju hjv huv hℓu hℓv
    by_cases hq : geoOwner (geomAt E t ht.1) (Q ∪ {j}) (Sum.inr (visitOn u ℓ hℓu)) = q
    · -- the affected carrier: the port ledger (weak form)
      have hu' : crossingTransport hs u ∈ geoCarrierCrossings (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j}))
          (GT_carrierEquiv W q) :=
        (est_retained_u_iff hL hR hef heg hfg ht ht' hop hs hcomp hQ hfull hj hu hju hℓu hℓj q).mpr hq
      obtain ⟨u₁, -, -, hu₁', ⟨D⟩⟩ := hport n hn E e f g δ hL hR hef heg hfg t t' ht ht' hop hs hef' heg' hfg'
        hcomp Q hQ hfull j hj q hwind ⟨u, hu, hju.symm, hu'⟩
      exact s176_est_omega1_eq_of_port_weak hn _ _ hS hS' q _ _ hF D
        (est_groupedWrithe_affected hL hR hef heg hfg ht ht' hop hs hcomp hQ hfull hj hu hv hju hjv huv hℓu hℓv q hq)
        (GT_carrierR_eq hn (genericAt E t ht.1) (genericAt E t' ht'.1) W hS hS' q)
    · exact est_omega1_eq_of_ne hn hL hR hef heg hfg ht ht' hop hs hcomp hQ hfull hj hu hv hju hjv huv hℓu hℓv q hq

/-- `s176_est_row_weak` (= `est_row`) with the interface under `wind(S) ≠ 0` (byte-identical body). -/
theorem r176_est_row_weak_uniform (hF : CV.CarrierSlotFloor) (hport : r176l_est_port_relation_weak_uniform)
    (hn : 3 ≤ n) (hL : LocalizationData E e f g δ) (hR : AV_EventRadius E δ) (hef : e ≠ f) (heg : e ≠ g)
    (hfg : f ≠ g) {t t' : E.Parameter} (ht : Punctured E δ t) (ht' : Punctured E δ t') (hop : OppositeSides E t t')
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    {hef' : IsCrossing (E.curve t) {e, f}} {heg' : IsCrossing (E.curve t) {e, g}}
    {hfg' : IsCrossing (E.curve t) {f, g}} (hext : ExtremeLocal (geomAt E t ht.1) hef' heg' hfg')
    {Q : Finset (Crossing (E.curve t))} (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
    (hfull : FullAvail (geomAt E t ht.1) e f g Q) {j : Crossing (E.curve t)}
    (hj : j.val ∈ triangleSupports e f g) :
    rowTerm hn (genericAt E t ht.1) (Q ∪ {j}) =
      rowTerm hn (genericAt E t' ht'.1) (transportSupport hs (Q ∪ {j})) := by
  rcases hext with hcomp | hemp
  · exact r176_est_row_H_weak_uniform hF hport hn hL hR hef heg hfg ht ht' hop hs hcomp hQ hfull hj
  · have hs' : ∀ s, IsCrossing (E.curve t') s ↔ IsCrossing (E.curve t) s := fun s => (hs s).symm
    have hop' : OppositeSides E t' t := by
      unfold OppositeSides at hop ⊢; linarith [mul_comm t.val t'.val]
    obtain ⟨hef'', heg'', hfg''⟩ := hL.triangle_crossings t' ht'
    have hcomp' : CompleteLocal (geomAt E t' ht'.1) hef'' heg'' hfg'' :=
      (PRE_176_graphs_complementary hL t' t ht' ht hop' hef'' heg'' hfg'' hef' heg' hfg').mpr hemp
    have hQ' := GT_outsideSupports_transport hL ht ht' hop hs hQ
    have hfull' := GT_fullAvail_transport hL ht ht' hop hs hQ hfull
    have hj' : (crossingTransport hs j).val ∈ triangleSupports e f g := hj
    have h := r176_est_row_H_weak_uniform hF hport hn hL hR hef heg hfg ht' ht hop' hs' hcomp' hQ' hfull' hj'
    rw [← GT_transportSupport_S hs Q j, EXT_transportSupport_symm hs (Q ∪ {j})] at h
    exact h.symm

/-- `s176_est_extremeTransportData_weak` (= `est_extremeTransportData`) with the interface under `wind(S) ≠ 0`. -/
theorem r176_est_extremeTransportData_weak_uniform (hF : CV.CarrierSlotFloor)
    (hport : r176l_est_port_relation_weak_uniform) (hn : 3 ≤ n) (hL : LocalizationData E e f g δ)
    (hGT : GenericTableData E e f g δ) (hR : AV_EventRadius E δ) (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g) :
    ExtremeTransportData hn E e f g δ where
  singleton_rows_present := PRE_176_singleton_rows_present E e f g δ
  graphs_complementary := PRE_176_graphs_complementary hL
  sign_branch := PRE_176_sign_branch hGT
  transport_x := fun _ _ ht ht' hop hs _ _ _ hext _ hQ hfull =>
    r176_est_row_weak_uniform hF hport hn hL hR hef heg hfg ht ht' hop hs hext hQ hfull
      ((P1.mem_triangleSupports _).mpr (Or.inl rfl))
  transport_y := fun _ _ ht ht' hop hs _ _ _ hext _ hQ hfull =>
    r176_est_row_weak_uniform hF hport hn hL hR hef heg hfg ht ht' hop hs hext hQ hfull
      ((P1.mem_triangleSupports _).mpr (Or.inr (Or.inl rfl)))
  transport_z := fun _ _ ht ht' hop hs _ _ _ hext _ hQ hfull =>
    r176_est_row_weak_uniform hF hport hn hL hR hef heg hfg ht ht' hop hs hext hQ hfull
      ((P1.mem_triangleSupports _).mpr (Or.inr (Or.inr rfl)))

end R176Compose

/-- **The RA ledger of row 176 from the interface under `wind(S) ≠ 0`** — `s176_est_ledger_weak` (= `est_ledger`)
with `s176_est_port_relation_weak` replaced by `r176l_est_port_relation_weak_uniform`; byte-identical body. -/
theorem r176_est_ledger_weak_uniform (hF : CV.CarrierSlotFloor) (hport : r176l_est_port_relation_weak_uniform) :
    RowShape @ExtremeTransportData := by
  intro n _ hn E e f g h3 h4e h4f h4g hE
  obtain ⟨δL, hδL, hδLr, hL⟩ := localization E e f g h3 h4e h4f h4g hE
  obtain ⟨δG, hδG, -, hGT⟩ := generic_table E e f g h3 h4e h4f h4g hE
  obtain ⟨δR, hδR, -, hR⟩ := AV_exists_eventRadius hE
  have hef : e ≠ f := AV_ne_of_remote h3.1
  have hfg : f ≠ g := AV_ne_of_remote h3.2.1
  have heg : e ≠ g := AV_ne_of_remote h3.2.2.1
  refine ⟨min δL (min δG δR), lt_min hδL (lt_min hδG hδR), (min_le_left _ _).trans hδLr, ?_⟩
  have hL' := F1.localizationData_mono (min_le_left δL (min δG δR)) hL
  have hGT' := SEL_genericTableData_mono ((min_le_right δL (min δG δR)).trans (min_le_left δG δR)) hGT
  have hR' := AV_eventRadius_mono ((min_le_right δL (min δG δR)).trans (min_le_right δG δR)) hR
  exact r176_est_extremeTransportData_weak_uniform hF hport hn hL' hGT' hR' hef heg hfg

/-- Sanity: the unconditional weak interface still gives the ledger through the split. -/
theorem r176_est_ledger_weak_uniform_of_weak (hF : CV.CarrierSlotFloor) (hport : s176_est_port_relation_weak) :
    RowShape @ExtremeTransportData :=
  r176_est_ledger_weak_uniform hF (r176l_est_port_relation_weak_uniform_of_weak hport)

/-! ## §X6. The row -/

/-- **`R:extreme_transport` in the fixed row shape from exactly the three open Props of row 176** — the
record-level R-I `r176s_curl_removal`, the outer carriers `r176_outer_carriers_L`, the (14)-bridge
`r176_mixed_bridge` — with the floor `CV.carrierSlotFloor` (thm:carrierfloor (C), library) and the RII port
`hrec` closed by HSUCC.  Once the three Props are proved, `RProof.extreme_transport := r176_extreme_transport_of_curl_outer_mixed
<curl> <outer> <mixed>` (modulo F-176-1 and the port of the moves toolkit). -/
theorem r176_extreme_transport_of_curl_outer_mixed (hcurl : r176s_curl_removal) (hout : r176_outer_carriers_L)
    (hmixed : r176_mixed_bridge) : RowShape @ExtremeTransportData :=
  r176_est_ledger_weak_uniform CV.carrierSlotFloor
    (r176_est_port_relation_weak_uniform_of_curl_outer_mixed hcurl hout hmixed)

/-- The row from the corrected non-move port data alone (`hF` discharged by the library). -/
theorem r176_extreme_transport_of_rest_uniform
    (hrest : ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (E : CV.Event n) (e f g : ZMod n) (δ : ℝ)
      (hL : LocalizationData E e f g δ) (hR : AV_EventRadius E δ) (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
      (t t' : E.Parameter) (ht : Punctured E δ t) (ht' : Punctured E δ t') (hop : OppositeSides E t t')
      (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
      (hef' : IsCrossing (E.curve t) {e, f}) (heg' : IsCrossing (E.curve t) {e, g})
      (hfg' : IsCrossing (E.curve t) {f, g}) (_hcomp : CompleteLocal (geomAt E t ht.1) hef' heg' hfg')
      (Q : Finset (Crossing (E.curve t))) (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
      (hfull : FullAvail (geomAt E t ht.1) e f g Q) (j : Crossing (E.curve t))
      (hj : j.val ∈ triangleSupports e f g) (q : GeoComponent (geomAt E t ht.1) (Q ∪ {j})),
      CV.wind (geomAt E t ht.1) (Q ∪ {j}) ≠ 0 →
      ∀ (u : Crossing (E.curve t)) (_hu : u.val ∈ triangleSupports e f g) (_hju : j ≠ u)
        (hu' : crossingTransport hs u ∈ geoCarrierCrossings (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j}))
          (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)),
      Nonempty (s176_PortDataRest hn (genericAt E t ht.1) (genericAt E t' ht'.1) (est_S_ind ht.1 hQ hfull hj)
        (est_S'_ind hL ht ht' hop hs hQ hfull hj) q
        (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)
        (est_liftCrossing hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj) _ hu'))) :
    RowShape @ExtremeTransportData :=
  r176_est_ledger_weak_uniform CV.carrierSlotFloor (r176_est_port_relation_weak_uniform_of_rest hrest)

/-- **The SMOOTH-route composition**: the unconditional weak interface from the record-level R-I, SMOOTH's
outer carriers `r176s_outer_carriers` (arbitrary `Λ_A, Λ_B` of `S_full = Q' ∪ {j', u', v'}`) and SMOOTH's ledger
black box `r176s_ledger` ((14), (13), (12) for them) — `r176s_est_port_relation_weak_of''` with its `hrec`
discharged by HSUCC.  NOTE (R176_LEDGER_REPORT §3): `r176s_ledger` asserts (13)/(12) also when `wind(S) = 0`,
where they can fail; the route to pursue is §X4–§X6 above. -/
theorem r176_est_port_relation_weak_of_curl_outer_ledger (hcurl : r176s_curl_removal)
    (hout : r176s_outer_carriers) (hled : r176s_ledger) : s176_est_port_relation_weak := by
  intro n _ hn E e f g δ hL hR hef heg hfg t t' ht ht' hop hs hef' heg' hfg' hcomp Q hQ hfull j hj q hex
  obtain ⟨u, hu, hju, hu'⟩ := hex
  obtain ⟨R⟩ := r176s_portDataRest_of hcurl hout hled hn hL hR hef heg hfg ht ht' hop hs hef' heg' hfg' hcomp
    hQ hfull hj q hu hju.symm hu'
  refine ⟨u, hu, hju, hu', ⟨s176_PortDataWeak.mk' _ _ _ _ _ _ _ _ ?_ R⟩⟩
  exact r176h_est_port_weak hn hL hR hef heg hfg ht ht' hop hs hef' heg' hfg' hcomp hQ hfull hj q hu hju.symm hu'

/-- The row along the SMOOTH route (same caveat). -/
theorem r176_extreme_transport_of_curl_outer_ledger (hcurl : r176s_curl_removal) (hout : r176s_outer_carriers)
    (hled : r176s_ledger) : RowShape @ExtremeTransportData :=
  s176_est_ledger_weak CV.carrierSlotFloor (r176_est_port_relation_weak_of_curl_outer_ledger hcurl hout hled)


/-! # R176W2_CURL — unit CURL (appended 2026-09-15 by the CURL prover): `r176s_curl_removal` PROVED

Record-level R-I on a one-circle record `ρ` with a kink `r ∈ K` (its two occurrences consecutive in
`ρ|K`).  Route (mp:blocks, lc:single-crossing; no `RIData` witness, no geometry): the kink is an isolated
vertex of the interlacement graph of `σ = ρ|K` (§C2); every block of a realizable one-circle record is
realizable — the mp:blocks realization chain (`restrictCrossings_join_decomp`,
`isRealizable_restrictCrossings_of_gapContiguous`) run down to single blocks WITHOUT supplied leaves
(§C1), so `σ` has a `BlockSupply` by choice; `SM.blocks.product` (`product_of_blockSupply`) gives
`P X = P(C_{r̂}) · ∏_{H ≠ r̂} P(C_H)` with `P(C_{r̂}) = 1` (`single_crossing.one_crossing`, §C4); the join
forest of the other blocks (`exists_joinForest_of_realizable`, `joinForest_P`) realizes `σ|{x ≠ r̂}`,
which is `ρ|(K ∖ {r})` by the restriction-of-a-restriction isomorphism (§C3), hence `P X' = ∏_{H ≠ r̂} P(C_H)`.
The degenerate case (no crossing but `r`) is `one_crossing`/`crossing_free`.  All names carry the prefix
`r176c_`; nothing above is modified.  General form `r176c_curl_removal_general` (any `w` with `crossingOf w = r`;
conclusion `P X = P X'`), shared with rows 174/110.  Companion report: `R176W2_CURL_REPORT.md`. -/

section R176C_Curl

open Classical

/-! ## §C1. Every block of a realizable block-union is realizable -/

/-- **Block realizability**: on a one-circle record `ρ`, if the restriction to a union of blocks
`S` is realizable, every block inside `S` is realizable (the realization chain of mp:blocks,
`restrictCrossings_join_decomp` + `isRealizable_restrictCrossings_of_gapContiguous`, run down to a
single block without any supplied leaves). -/
theorem r176c_isRealizable_block_of_union (ρ : Record) (h1 : ρ.componentCount = 1) :
    ∀ (S : Set ρ.Crossing),
      (∀ H : ρ.interlacementGraph.ConnectedComponent, H.supp ⊆ S ∨ Disjoint H.supp S) →
      IsRealizable (ρ.restrictCrossings S) →
      ∀ H : ρ.interlacementGraph.ConnectedComponent, H.supp ⊆ S →
        IsRealizable (ρ.restrictCrossings H.supp) := by
  have block_sub : ∀ S : Set ρ.Crossing,
      (∀ H : ρ.interlacementGraph.ConnectedComponent, H.supp ⊆ S ∨ Disjoint H.supp S) →
      ∀ x ∈ S, (ρ.interlacementGraph.connectedComponentMk x).supp ⊆ S := by
    intro S hS x hx
    rcases hS (ρ.interlacementGraph.connectedComponentMk x) with h' | h'
    · exact h'
    · exact absurd hx (Set.disjoint_left.mp h'
        ((SimpleGraph.ConnectedComponent.mem_supp_iff _ _).mpr rfl))
  suffices key : ∀ n : ℕ, ∀ S : Set ρ.Crossing,
      (Finset.univ.filter
        (fun H : ρ.interlacementGraph.ConnectedComponent => H.supp ⊆ S)).card = n →
      (∀ H : ρ.interlacementGraph.ConnectedComponent, H.supp ⊆ S ∨ Disjoint H.supp S) →
      IsRealizable (ρ.restrictCrossings S) →
      ∀ H : ρ.interlacementGraph.ConnectedComponent, H.supp ⊆ S →
        IsRealizable (ρ.restrictCrossings H.supp) from
    fun S => key _ S rfl
  intro n
  refine Nat.strong_induction_on n (fun n ih => ?_)
  intro S hcard hS hreal H hH
  by_cases h2 : ∃ H H' : ρ.interlacementGraph.ConnectedComponent,
      H ≠ H' ∧ H.supp ⊆ S ∧ H'.supp ⊆ S
  · obtain ⟨S₁, S₂, hunion, hdisj, hne₁, hne₂, hblk₁, hblk₂, hgap₁, hgap₂, -⟩ :=
      restrictCrossings_join_decomp ρ h1 S hS h2
    have hsub₁ : S₁ ⊆ S := by rw [← hunion]; exact Set.subset_union_left
    have hsub₂ : S₂ ⊆ S := by rw [← hunion]; exact Set.subset_union_right
    have hreal₁ : IsRealizable (ρ.restrictCrossings S₁) :=
      isRealizable_restrictCrossings_of_gapContiguous ρ h1 hsub₁ hreal hgap₁
    have hreal₂ : IsRealizable (ρ.restrictCrossings S₂) :=
      isRealizable_restrictCrossings_of_gapContiguous ρ h1 hsub₂ hreal hgap₂
    have hlt : ∀ T T' : Set ρ.Crossing, T ⊆ S → T' ⊆ S → T'.Nonempty → Disjoint T T' →
        (Finset.univ.filter
          (fun H : ρ.interlacementGraph.ConnectedComponent => H.supp ⊆ T)).card < n := by
      intro T T' hT hT' hne' hd
      rw [← hcard]
      apply Finset.card_lt_card
      have hsubT : Finset.univ.filter
            (fun H : ρ.interlacementGraph.ConnectedComponent => H.supp ⊆ T) ⊆
          Finset.univ.filter
            (fun H : ρ.interlacementGraph.ConnectedComponent => H.supp ⊆ S) := by
        intro H hH
        rw [Finset.mem_filter] at hH ⊢
        exact ⟨hH.1, hH.2.trans hT⟩
      rw [Finset.ssubset_iff_of_subset hsubT]
      obtain ⟨y, hy⟩ := hne'
      refine ⟨ρ.interlacementGraph.connectedComponentMk y, ?_, ?_⟩
      · rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ _, block_sub S hS y (hT' hy)⟩
      · rw [Finset.mem_filter]
        intro hcon
        exact Set.disjoint_left.mp hd
          (hcon.2 ((SimpleGraph.ConnectedComponent.mem_supp_iff _ _).mpr rfl)) hy
    rcases hblk₁ H with hH₁ | hH₁
    · exact ih _ (hlt S₁ S₂ hsub₁ hsub₂ hne₂ hdisj) S₁ rfl hblk₁ hreal₁ H hH₁
    · have hH₂ : H.supp ⊆ S₂ := by
        intro x hx
        have hxS : x ∈ S₁ ∪ S₂ := by rw [hunion]; exact hH hx
        rcases hxS with hx₁ | hx₂
        · exact absurd hx₁ (Set.disjoint_left.mp hH₁ hx)
        · exact hx₂
      exact ih _ (hlt S₂ S₁ hsub₂ hsub₁ hne₁ hdisj.symm) S₂ rfl hblk₂ hreal₂ H hH₂
  · -- one block: `S = H.supp`
    have hSeq : S = H.supp := by
      apply Set.Subset.antisymm
      · intro y hy
        have hy' : ρ.interlacementGraph.connectedComponentMk y = H := by
          by_contra hne
          exact h2 ⟨_, H, hne, block_sub S hS y hy, hH⟩
        rw [← hy']
        exact (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).mpr rfl
      · exact hH
    rw [← hSeq]
    exact hreal

/-- **A block supply from realizability alone**: a realizable one-circle record with a nonempty
occurrence set has a `BlockSupply` (each block realized by `r176c_isRealizable_block_of_union` at
`S = univ`, through `restrictCrossings_univ_iso`). -/
theorem r176c_exists_blockSupply (ρ : Record) (h1 : ρ.componentCount = 1) (hreal : IsRealizable ρ)
    (hne : Nonempty ρ.M) :
    ∃ C : ρ.interlacementGraph.ConnectedComponent → Diagram, BlockSupply ρ C := by
  obtain ⟨ιu⟩ := Record.restrictCrossings_univ_iso ρ
  have hrealU : IsRealizable (ρ.restrictCrossings Set.univ) := hreal.of_iso ιu.symm
  have hblk : ∀ H : ρ.interlacementGraph.ConnectedComponent,
      IsRealizable (ρ.restrictCrossings H.supp) :=
    fun H => r176c_isRealizable_block_of_union ρ h1 Set.univ (fun _ => Or.inl (Set.subset_univ _))
      hrealU H (Set.subset_univ _)
  refine ⟨fun H => Classical.choose (hblk H), ?_⟩
  exact
    { actual := hreal
      one_circle := h1
      nonempty := hne
      supplied := fun H => Classical.choose_spec (hblk H) }

/-! ## §C2. The kink is an isolated vertex of the interlacement graph -/

/-- An occurrence whose successor is its partner: its crossing interlaces nothing. -/
theorem r176c_not_adj_of_succ_eq_pair (ρ : Record) (h1 : ρ.componentCount = 1) (v : ρ.M)
    (hv : ρ.succ v = ρ.pair v) (y : ρ.Crossing) : ¬ ρ.interlacementGraph.Adj (ρ.crossingOf v) y := by
  intro hadj
  have hxy : ρ.crossingOf v ≠ y := hadj.ne
  obtain ⟨w, rfl⟩ := ρ.crossingOf_surjective y
  rw [ρ.adj_iff_alternates h1 hxy (ρ.mem_crossingOf v) (ρ.mem_crossingOf w)] at hadj
  have hsteps : ρ.steps v (ρ.pair v) = 1 := by
    rw [ρ.steps_eq_iff h1]
    refine ⟨?_, by simpa using hv⟩
    exact Fintype.one_lt_card_iff.mpr ⟨v, ρ.pair v, ρ.ne_pair v⟩
  unfold Record.Alternates Xor Record.ArcBetween at hadj
  rw [hsteps] at hadj
  omega

/-- The block of such a crossing is the singleton. -/
theorem r176c_supp_eq_singleton_of_succ_eq_pair (ρ : Record) (h1 : ρ.componentCount = 1) (v : ρ.M)
    (hv : ρ.succ v = ρ.pair v) :
    (ρ.interlacementGraph.connectedComponentMk (ρ.crossingOf v)).supp = {ρ.crossingOf v} := by
  ext x
  rw [SimpleGraph.ConnectedComponent.mem_supp_iff, Set.mem_singleton_iff]
  constructor
  · intro h
    obtain ⟨p⟩ := SimpleGraph.ConnectedComponent.exact h.symm
    cases p with
    | nil => rfl
    | cons hadj _ => exact absurd hadj (r176c_not_adj_of_succ_eq_pair ρ h1 v hv _)
  · rintro rfl; rfl

/-! ## §C3. Restriction of a restriction -/

/-- On `σ = ρ|K`, the crossing of an occurrence is the kink's crossing iff its underlying
`ρ`-crossing is `r`. -/
theorem r176c_crossingOf_restrict_eq_iff (ρ : Record) (K : Set ρ.Crossing) (w : ρ.M)
    (hw : ρ.CrossKeep K w) (m : (ρ.restrictCrossings K).M) :
    (ρ.restrictCrossings K).crossingOf m = (ρ.restrictCrossings K).crossingOf (⟨w, hw⟩ : (ρ.restrictCrossings K).M) ↔
      ρ.crossingOf m.1 = ρ.crossingOf w := by
  rw [(ρ.restrictCrossings K).crossingOf_eq_iff, (ρ.restrictCrossings K).mem_val_iff
    ((ρ.restrictCrossings K).mem_crossingOf (⟨w, hw⟩ : (ρ.restrictCrossings K).M)), ρ.crossingOf_eq_iff,
    ρ.mem_val_iff (ρ.mem_crossingOf w)]
  constructor
  · rintro (rfl | rfl)
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (h | h)
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext h)

/-- The retained predicate of `{x ≠ rhat}` on `ρ|K`, read on `ρ`: the crossing lies in `K ∖ {r}`. -/
theorem r176c_crossKeep_restrict_iff (ρ : Record) (K : Set ρ.Crossing) (w : ρ.M)
    (hw : ρ.CrossKeep K w) (m : (ρ.restrictCrossings K).M) :
    (ρ.restrictCrossings K).CrossKeep {x | x ≠ (ρ.restrictCrossings K).crossingOf (⟨w, hw⟩ : (ρ.restrictCrossings K).M)} m ↔
      ρ.CrossKeep (K \ {ρ.crossingOf w}) m.1 := by
  show (ρ.restrictCrossings K).crossingOf m ∈ {x | x ≠ _} ↔ ρ.crossingOf m.1 ∈ K \ {ρ.crossingOf w}
  rw [Set.mem_ofPred_eq, Set.mem_sdiff, Set.mem_singleton_iff, ne_eq,
    r176c_crossingOf_restrict_eq_iff ρ K w hw m]
  exact ⟨fun h => ⟨m.2, h⟩, fun h => h.2⟩

/-- The occurrence bijection of the restriction-of-a-restriction isomorphism. -/
def r176c_restrictRestrictEquiv (ρ : Record) (K : Set ρ.Crossing) (w : ρ.M) (hw : ρ.CrossKeep K w) :
    ((ρ.restrictCrossings K).restrictCrossings
        {x | x ≠ (ρ.restrictCrossings K).crossingOf (⟨w, hw⟩ : (ρ.restrictCrossings K).M)}).M ≃
      (ρ.restrictCrossings (K \ {ρ.crossingOf w})).M :=
  (Equiv.subtypeEquivRight (fun m => r176c_crossKeep_restrict_iff ρ K w hw m)).trans
    (Equiv.subtypeSubtypeEquivSubtype (p := ρ.CrossKeep K)
      (q := ρ.CrossKeep (K \ {ρ.crossingOf w})) (fun {_} hx => hx.1))

theorem r176c_restrictRestrictEquiv_val (ρ : Record) (K : Set ρ.Crossing) (w : ρ.M)
    (hw : ρ.CrossKeep K w) (m) : (r176c_restrictRestrictEquiv ρ K w hw m).1 = m.1.1 := rfl

/-- **Restriction of a restriction**: `(ρ|K)|{x ≠ rhat} ≅ ρ|(K ∖ {r})` where `rhat` is the crossing of the
kink occurrence `w` in `ρ|K` (`restrictCrossings_firstReturn_val`). -/
def r176c_restrictRestrictIso (ρ : Record) (K : Set ρ.Crossing) (w : ρ.M) (hw : ρ.CrossKeep K w) :
    RecordIso ((ρ.restrictCrossings K).restrictCrossings
        {x | x ≠ (ρ.restrictCrossings K).crossingOf (⟨w, hw⟩ : (ρ.restrictCrossings K).M)})
      (ρ.restrictCrossings (K \ {ρ.crossingOf w})) where
  e := Equiv.refl _
  Φ := r176c_restrictRestrictEquiv ρ K w hw
  comp_eq _ := rfl
  succ_eq m := by
    apply Subtype.ext
    have h₁ := firstReturn_congr_pred (ρ.restrictCrossings K).succ
      ((ρ.restrictCrossings K).CrossKeep {x | x ≠ (ρ.restrictCrossings K).crossingOf (⟨w, hw⟩ : (ρ.restrictCrossings K).M)})
      (fun m => ρ.CrossKeep (K \ {ρ.crossingOf w}) m.1) (r176c_crossKeep_restrict_iff ρ K w hw) m
    have h₂ := ρ.restrictCrossings_firstReturn_val (S₁ := K \ {ρ.crossingOf w}) (S := K)
      Set.sdiff_subset ⟨m.1, (r176c_crossKeep_restrict_iff ρ K w hw m.1).mp m.2⟩
    exact (congrArg Subtype.val h₁).trans h₂
  pair_eq _ := rfl
  bit_eq _ := rfl
  sgn_eq _ := rfl

/-! ## §C4. The kink block has value one; the main theorem -/

/-- A diagram record-isomorphic to `σ|{x}` (one crossing of a one-circle record) is a one-circle
one-crossing diagram: `P = 1` (lc:single-crossing). -/
theorem r176c_P_eq_one_of_iso_single (σ : Record) (h1 : σ.componentCount = 1) (v : σ.M)
    (D : Diagram) (ι : RecordIso D.record (σ.restrictCrossings {σ.crossingOf v})) : P D = 1 := by
  have hc : D.Γ.c = 1 := by
    have := ι.componentCount_eq
    rw [Diagram.record_componentCount] at this
    exact this.trans h1
  have hcard : Fintype.card D.Γ.Crossing = 1 := by
    rw [← Diagram.record_crossingCount, ι.crossingCount_eq]
    unfold Record.crossingCount
    have h2 : Fintype.card (σ.restrictCrossings {σ.crossingOf v}).M = 2 := by
      show Fintype.card {m : σ.M // σ.CrossKeep {σ.crossingOf v} m} = 2
      rw [Fintype.card_subtype]
      have : (Finset.univ.filter (fun m => σ.CrossKeep {σ.crossingOf v} m)) = {v, σ.pair v} := by
        ext m
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
          Finset.mem_singleton]
        unfold Record.CrossKeep
        rw [Set.mem_singleton_iff, σ.crossingOf_eq_iff, σ.mem_val_iff (σ.mem_crossingOf v)]
      rw [this, Finset.card_pair (σ.ne_pair v)]
    rw [h2]
  obtain ⟨x₀, hx₀⟩ := Fintype.card_eq_one_iff.mp hcard
  exact single_crossing.one_crossing D x₀ hc hx₀

/-- **Record-level R-I (the frozen Prop `r176s_curl_removal`, PROVED)**: the kink `r` is an isolated
vertex of the interlacement graph of `σ = ρ|K`; every block of the realizable one-circle record `σ`
is realizable (`r176c_exists_blockSupply`), so mp:blocks gives `P X = P(C_{rhat}) · ∏_{H ≠ rhat} P(C_H)`
with `P(C_{rhat}) = 1` (lc:single-crossing), while the join forest of the other blocks realizes
`σ|{x ≠ rhat} ≅ ρ|(K ∖ {r}) ≅ X'.record`, whence `P X' = ∏_{H ≠ rhat} P(C_H)`. -/
theorem r176c_curl_removal_general (ρ : Record) (h1 : ρ.componentCount = 1) (K : Set ρ.Crossing)
    (w : ρ.M) (hw : ρ.CrossKeep K w)
    (hsucc : ((ρ.restrictCrossings K).succ ⟨w, hw⟩).1 = ρ.pair w)
    (X X' : Diagram) (hX : Nonempty (RecordIso X.record (ρ.restrictCrossings K)))
    (hX' : Nonempty (RecordIso X'.record (ρ.restrictCrossings (K \ {ρ.crossingOf w})))) :
    P X = P X' := by
  set σ := ρ.restrictCrossings K with hσ
  have hσ1 : σ.componentCount = 1 := h1
  let v : σ.M := ⟨w, hw⟩
  have hv : σ.succ v = σ.pair v := Subtype.ext hsucc
  set rhat := σ.crossingOf v with hrhat
  set Hr := σ.interlacementGraph.connectedComponentMk rhat with hHr
  have hsupp : Hr.supp = {rhat} := r176c_supp_eq_singleton_of_succ_eq_pair σ hσ1 v hv
  -- the supply
  obtain ⟨C, hC⟩ := r176c_exists_blockSupply σ hσ1 ⟨X, hX⟩ ⟨v⟩
  have hPX : P X = ∏ H, P (C H) := product_of_blockSupply σ C hC X hX
  have hPr : P (C Hr) = 1 := by
    obtain ⟨ι⟩ := hC.supplied Hr
    rw [hsupp] at ι
    exact r176c_P_eq_one_of_iso_single σ hσ1 v (C Hr) ι
  -- the other blocks
  set S₁ : Set σ.Crossing := {x | x ≠ rhat} with hS₁
  have hblk : ∀ H : σ.interlacementGraph.ConnectedComponent, H.supp ⊆ S₁ ∨ Disjoint H.supp S₁ := by
    intro H
    by_cases hH : H = Hr
    · right
      rw [hH, hsupp]
      exact Set.disjoint_left.mpr (fun x hx hx' => hx' (Set.mem_singleton_iff.mp hx))
    · left
      intro x hx hxr
      apply hH
      exact σ.block_eq_of_mem_supp hx (by rw [hsupp]; exact Set.mem_singleton_iff.mpr hxr)
  have hS₁iff : ∀ H : σ.interlacementGraph.ConnectedComponent, H.supp ⊆ S₁ ↔ H ≠ Hr := by
    intro H
    constructor
    · intro h hH
      have : rhat ∈ S₁ := h (by rw [hH, hsupp]; exact Set.mem_singleton _)
      exact this rfl
    · intro hH
      rcases hblk H with h | h
      · exact h
      · exfalso
        obtain ⟨x, hx⟩ := H.nonempty_supp
        have hxr : x = rhat := by
          by_contra hne
          exact Set.disjoint_left.mp h hx hne
        exact hH (σ.block_eq_of_mem_supp hx (by rw [hsupp]; exact Set.mem_singleton_iff.mpr hxr))
  have hfin : ({H | H.supp ⊆ S₁} : Set σ.interlacementGraph.ConnectedComponent).toFinset =
      Finset.univ.erase Hr := by
    ext H
    rw [Set.mem_toFinset, Finset.mem_erase, Set.mem_ofPred_eq, hS₁iff]
    exact ⟨fun h => ⟨h, Finset.mem_univ _⟩, fun h => h.1⟩
  have ι₂ := r176c_restrictRestrictIso ρ K w hw
  rw [hPX, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ Hr), hPr, one_mul]
  obtain ⟨ιX'⟩ := hX'
  by_cases hne : S₁.Nonempty
  · have hreal₁ : IsRealizable (σ.restrictCrossings S₁) := ⟨X', ⟨ιX'.trans ι₂.symm⟩⟩
    obtain ⟨J, hJ, ⟨ιJ⟩⟩ := exists_joinForest_of_realizable σ C hC S₁ hblk hne hreal₁
    rw [presentations X' J ⟨ιX'.trans (ι₂.symm.trans ιJ.symm)⟩, joinForest_P C _ J hJ]
    exact (Finset.prod_congr hfin (fun _ _ => rfl)).symm
  · -- no other crossing: both sides are `1`
    have hall : ∀ H : σ.interlacementGraph.ConnectedComponent, H = Hr := by
      intro H
      by_contra hH
      obtain ⟨x, hx⟩ := H.nonempty_supp
      exact hne ⟨x, (hS₁iff H).mpr hH hx⟩
    rw [Finset.prod_eq_one (fun H hH => absurd (hall H) (Finset.ne_of_mem_erase hH))]
    have hc : X'.Γ.c = 1 := by
      have := ιX'.componentCount_eq
      rw [Diagram.record_componentCount] at this
      exact this.trans h1
    have hempty : IsEmpty X'.Γ.Crossing := by
      rw [← Fintype.card_eq_zero_iff]
      have h2 : 2 * Fintype.card X'.Γ.Crossing = 0 := by
        rw [← X'.record_card_M, ιX'.card_M_eq, Fintype.card_eq_zero_iff]
        refine ⟨fun m => ?_⟩
        have hmK : ρ.CrossKeep K m.1 := m.2.1
        apply hne
        refine ⟨σ.crossingOf ⟨m.1, hmK⟩, ?_⟩
        show σ.crossingOf ⟨m.1, hmK⟩ ≠ rhat
        rw [Ne, hrhat, r176c_crossingOf_restrict_eq_iff ρ K w hw ⟨m.1, hmK⟩]
        exact m.2.2
      omega
    exact (single_crossing.crossing_free X' ⟨hc, hempty⟩).symm

/-- **`r176s_curl_removal` PROVED**: the frozen Prop applied to its binders. -/
theorem r176c_curl_removal_proof : r176s_curl_removal := by
  intro ρ h1 K r _hrK hcurl X X' hX hX'
  obtain ⟨w, hw, hwr, hsucc⟩ := hcurl
  subst hwr
  rw [← P_eq_homfly, ← P_eq_homfly]
  exact r176c_curl_removal_general ρ h1 K w hw hsucc X X' hX hX'

/-- The kinked exact owner map with the record-level R-I discharged
(`r176s_homfly_of_liftBlock_curl` at `hcurl := r176c_curl_removal_proof`). -/
theorem r176c_homfly_of_liftBlock_curl {n : ℕ} [NeZero n] (hn : 3 ≤ n) {P : LabelledTuple n}
    (hG : CarrierGeometry P) {T T' : Finset (Crossing P)} (hT : GeoIndependent hG.cg T)
    (hT' : GeoIndependent hG.cg T') (q : GeoComponent hG.cg T) (Λ : GeoComponent hG.cg T')
    (hsub : geoCarrierCrossings hG.cg T' Λ ⊆ geoCarrierCrossings hG.cg T q)
    (X : Diagram) (K : Set (geoPositiveLift hn hG hT q).record.Crossing)
    (r : (geoPositiveLift hn hG hT q).record.Crossing)
    (hK : K = CV.liftBlock hn hG hT q (geoCarrierCrossings hG.cg T' Λ) ∪ {r})
    (hr : r ∉ CV.liftBlock hn hG hT q (geoCarrierCrossings hG.cg T' Λ))
    (hcurlK : ∃ (w : (geoPositiveLift hn hG hT q).record.M)
      (hw : (geoPositiveLift hn hG hT q).record.CrossKeep K w),
      (geoPositiveLift hn hG hT q).record.crossingOf w = r ∧
      (((geoPositiveLift hn hG hT q).record.restrictCrossings K).succ ⟨w, hw⟩).1 =
        (geoPositiveLift hn hG hT q).record.pair w)
    (hX : Nonempty (RecordIso X.record ((geoPositiveLift hn hG hT q).record.restrictCrossings K))) :
    homfly X = homfly (geoPositiveLift hn hG hT' Λ) :=
  r176s_homfly_of_liftBlock_curl r176c_curl_removal_proof hn hG hT hT' q Λ hsub X K r hK hr hcurlK hX

/-- **The row with the curl hypothesis discharged**: `r176_extreme_transport_of_curl_outer_mixed` at
`hcurl := r176c_curl_removal_proof`; the row is now open in exactly `r176_outer_carriers_L` and
`r176_mixed_bridge`. -/
theorem r176c_extreme_transport_of_outer_mixed (hout : r176_outer_carriers_L) (hmixed : r176_mixed_bridge) :
    RowShape @ExtremeTransportData :=
  r176_extreme_transport_of_curl_outer_mixed r176c_curl_removal_proof hout hmixed

end R176C_Curl


/-! # OUTER unit (`r176o_`): the outer carriers of `S_full` (R176W2_OUTER, 2026-09-15) -/

/-! ## §O0. Arithmetic and permutation helpers -/

theorem r176o_add_mod_inj {N s i j : ℕ} (hs : s < N) (hi : i < N) (hj : j < N)
    (h : (i + s) % N = (j + s) % N) : i = j := by
  have e : ∀ x, x < N → (x + s) % N = if x + s < N then x + s else x + s - N := by
    intro x hx
    split_ifs with hlt
    · exact Nat.mod_eq_of_lt hlt
    · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
  rw [e i hi, e j hj] at h
  split_ifs at h <;> omega

theorem r176o_unrotate {N s i : ℕ} (hs : s < N) (hi : i < N) : ((i + s) % N + N - s) % N = i := by
  rcases Nat.lt_or_ge (i + s) N with h | h
  · rw [Nat.mod_eq_of_lt h, show i + s + N - s = i + N by omega, Nat.add_mod_right, Nat.mod_eq_of_lt hi]
  · rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (show i + s - N < N by omega),
      show i + s - N + N - s = i by omega, Nat.mod_eq_of_lt hi]

theorem r176o_pow_mul_add_fix {α : Type*} (f : Equiv.Perm α) {x : α} {p : ℕ} (hx : (f ^ p) x = x) (d r : ℕ) :
    (f ^ (p * d + r)) x = (f ^ r) x := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [Nat.mul_succ, show p * d + p + r = (p * d + r) + p by ring, pow_add, Equiv.Perm.mul_apply, hx, ih]

theorem r176o_pow_mod_fix {α : Type*} (f : Equiv.Perm α) {x : α} {p : ℕ} (hx : (f ^ p) x = x) (i : ℕ) :
    (f ^ i) x = (f ^ (i % p)) x := by
  conv_lhs => rw [← Nat.div_add_mod i p]
  exact r176o_pow_mul_add_fix f hx _ _

theorem r176o_sameCycle_iff_pow {α : Type*} [Finite α] (f : Equiv.Perm α) {x : α} {p : ℕ} (hp : 0 < p)
    (hx : (f ^ p) x = x) (y : α) : f.SameCycle x y ↔ ∃ i, i < p ∧ (f ^ i) x = y := by
  constructor
  · intro h
    obtain ⟨i, -, hi⟩ := h.exists_pow_eq'
    exact ⟨i % p, Nat.mod_lt _ hp, by rw [← r176o_pow_mod_fix f hx, hi]⟩
  · rintro ⟨i, -, hi⟩
    exact ⟨i, by rw [zpow_natCast]; exact hi⟩

/-- the orbit of `g` from `a` follows the orbit of `f` from `b` while the two permutations agree -/
theorem r176o_orbit_transfer {α : Type*} (f g : Equiv.Perm α) {a b : α} {k : ℕ} (h0 : g a = f b)
    (hagree : ∀ i, 0 < i → i < k → g ((f ^ i) b) = f ((f ^ i) b)) :
    ∀ i, 0 < i → i ≤ k → (g ^ i) a = (f ^ i) b := by
  intro i
  induction i with
  | zero => intro h; exact absurd h (lt_irrefl 0)
  | succ i ih =>
    intro _ hik
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · simpa using h0
    · rw [pow_succ', Equiv.Perm.mul_apply, ih hpos (by omega), pow_succ', Equiv.Perm.mul_apply]
      exact hagree i hpos (by omega)

theorem r176o_sameCycle_transfer_iff {α : Type*} [Finite α] (f g : Equiv.Perm α) {a b : α} {k : ℕ}
    (hk : 0 < k) (h0 : g a = f b) (hagree : ∀ i, 0 < i → i < k → g ((f ^ i) b) = f ((f ^ i) b))
    (hka : (f ^ k) b = a) (m : α) :
    g.SameCycle a m ↔ m = a ∨ ∃ i, 0 < i ∧ i < k ∧ (f ^ i) b = m := by
  have hfix : (g ^ k) a = a := by rw [r176o_orbit_transfer f g h0 hagree k hk le_rfl, hka]
  rw [r176o_sameCycle_iff_pow g hk hfix]
  constructor
  · rintro ⟨i, hik, rfl⟩
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · left; simp
    · right; exact ⟨i, hpos, hik, (r176o_orbit_transfer f g h0 hagree i hpos hik.le).symm⟩
  · rintro (rfl | ⟨i, hpos, hik, rfl⟩)
    · exact ⟨0, hk, by simp⟩
    · exact ⟨i, hik, r176o_orbit_transfer f g h0 hagree i hpos hik.le⟩

theorem r176o_crossing_set_ext (ρ : Record) {K K' : Set ρ.Crossing}
    (h : ∀ v, ρ.CrossKeep K v ↔ ρ.CrossKeep K' v) : K = K' := by
  ext c
  rw [← ρ.crossingOf_rep c]
  exact h c.rep

/-! ## §O1. The orbit of `ρ_T` on a carrier, indexed relative to one of its marks -/

section R176O_Orbit

variable {P : LabelledTuple n} (hP : CrossingGeometry P)
  {T : Finset (Crossing P)} (hT : GeoIndependent hP T) (q : GeoComponent hP T)

include hT in
theorem r176o_pow_length_fixes {a : Mark P} (ha : geoOwner hP T a = q) :
    (geoSmoothingSuccessor hP T ^ (geoComponentMarkList hP T q).length) a = a := by
  obtain ⟨s, hs, rfl⟩ := List.getElem_of_mem ((mem_geoComponentMarkList hP T q a).mpr ha)
  rw [CV.markList_getElem_pow hP hT q s hs, ← Equiv.Perm.mul_apply, ← pow_add, add_comm, pow_add,
    Equiv.Perm.mul_apply, CV.markList_pow_length hP hT q]

include hT in
theorem r176o_pow_mod {a : Mark P} (ha : geoOwner hP T a = q) (i : ℕ) :
    (geoSmoothingSuccessor hP T ^ i) a =
      (geoSmoothingSuccessor hP T ^ (i % (geoComponentMarkList hP T q).length)) a :=
  r176o_pow_mod_fix _ (r176o_pow_length_fixes hP hT q ha) i

include hT in
theorem r176o_exists_pow {a m : Mark P} (ha : geoOwner hP T a = q) (hm : geoOwner hP T m = q) :
    ∃ i, i < (geoComponentMarkList hP T q).length ∧ (geoSmoothingSuccessor hP T ^ i) a = m := by
  have hsc : (geoSmoothingSuccessor hP T).SameCycle a m :=
    (geoOwner_eq_iff hP T a m).mp (ha.trans hm.symm)
  obtain ⟨i, -, hi⟩ := hsc.exists_pow_eq'
  exact ⟨i % (geoComponentMarkList hP T q).length, Nat.mod_lt _ (CV.markList_length_pos hP q),
    by rw [← r176o_pow_mod hP hT q ha, hi]⟩

include hT in
theorem r176o_pow_apply_getElem {s : ℕ} (hs : s < (geoComponentMarkList hP T q).length) (x : ℕ) :
    (geoSmoothingSuccessor hP T ^ x) ((geoComponentMarkList hP T q)[s]) =
      (geoComponentMarkList hP T q)[(x + s) % (geoComponentMarkList hP T q).length]'
        (Nat.mod_lt _ (CV.markList_length_pos hP q)) := by
  rw [CV.markList_getElem_pow hP hT q s hs, ← Equiv.Perm.mul_apply, ← pow_add, CV.markList_pow hP hT q]

include hT in
theorem r176o_pow_inj {a : Mark P} (ha : geoOwner hP T a = q) {i j : ℕ}
    (hi : i < (geoComponentMarkList hP T q).length) (hj : j < (geoComponentMarkList hP T q).length)
    (h : (geoSmoothingSuccessor hP T ^ i) a = (geoSmoothingSuccessor hP T ^ j) a) : i = j := by
  obtain ⟨s, hs, rfl⟩ := List.getElem_of_mem ((mem_geoComponentMarkList hP T q a).mpr ha)
  rw [r176o_pow_apply_getElem hP hT q hs, r176o_pow_apply_getElem hP hT q hs] at h
  exact r176o_add_mod_inj hs hi hj ((geoComponentMarkList_nodup hP T q).getElem_inj_iff.mp h)

include hT in
/-- **Cyclic order on `Γ` is the orbit order of `ρ_T`** (lem:carrierword, read from any mark `a` of `q`). -/
theorem r176o_cyc_iff {a : Mark P} (ha : geoOwner hP T a = q) {i j l : ℕ}
    (hi : i < (geoComponentMarkList hP T q).length) (hj : j < (geoComponentMarkList hP T q).length)
    (hl : l < (geoComponentMarkList hP T q).length) :
    cycBetween (geoMarkKey hP ((geoSmoothingSuccessor hP T ^ i) a))
        (geoMarkKey hP ((geoSmoothingSuccessor hP T ^ j) a))
        (geoMarkKey hP ((geoSmoothingSuccessor hP T ^ l) a)) ↔
      ((i < j ∧ j < l) ∨ (j < l ∧ l < i) ∨ (l < i ∧ i < j)) := by
  have hN := CV.markList_length_pos hP q
  obtain ⟨s, hs, rfl⟩ := List.getElem_of_mem ((mem_geoComponentMarkList hP T q a).mpr ha)
  rw [r176o_pow_apply_getElem hP hT q hs, r176o_pow_apply_getElem hP hT q hs,
    r176o_pow_apply_getElem hP hT q hs]
  unfold cycBetween
  rw [CV.markList_key_lt_iff hP q (Nat.mod_lt _ hN) (Nat.mod_lt _ hN),
    CV.markList_key_lt_iff hP q (Nat.mod_lt _ hN) (Nat.mod_lt _ hN),
    CV.markList_key_lt_iff hP q (Nat.mod_lt _ hN) (Nat.mod_lt _ hN)]
  have := CV.rotate_cyc_iff (N := (geoComponentMarkList hP T q).length) (s := s)
    (i := (i + s) % (geoComponentMarkList hP T q).length) (j := (j + s) % (geoComponentMarkList hP T q).length)
    (k := (l + s) % (geoComponentMarkList hP T q).length) hs (Nat.mod_lt _ hN) (Nat.mod_lt _ hN) (Nat.mod_lt _ hN)
  rw [r176o_unrotate hs hi, r176o_unrotate hs hj, r176o_unrotate hs hl] at this
  exact this.symm

end R176O_Orbit

/-! ## §O2. The labelled corner on the orbit of `ρ_T` (OUTER unit, `r176o_`) -/

section R176O_Geom

variable (hn : 3 ≤ n) {P : LabelledTuple n} (hG : CarrierGeometry P)
  {T : Finset (Crossing P)} (hT : GeoIndependent hG.cg T) (q : GeoComponent hG.cg T)
  {a b c : ZMod n} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
  {j u v : Crossing P} (hj : j.val = {a, b}) (hu : u.val = {a, c}) (hv : v.val = {b, c})
  (hjT : j ∈ T) (huq : u ∈ geoCarrierCrossings hG.cg T q) (hvq : v ∈ geoCarrierCrossings hG.cg T q)
  (hρa : geoMarkSuccessor hG.cg (Sum.inr (r176l_ua hu)) = Sum.inr (visitOn j a (s176_mem_left hj)))
  (hρb : geoMarkSuccessor hG.cg (Sum.inr (visitOn j b (s176_mem_right hj))) = Sum.inr (visitOn v b (s176_mem_left hv)))
  (hρc : geoMarkSuccessor hG.cg (Sum.inr (visitOn v c (s176_mem_right hv))) = Sum.inr (r176l_uc hu))
  (hSf : GeoIndependent hG.cg (r176l_Sf T u v))

attribute [local instance 2000] r176l_decEq

omit [NeZero n] in
theorem r176o_cycBetween_rotate {x y z : ℝ} : cycBetween x y z ↔ cycBetween y z x := by
  unfold cycBetween; tauto

omit [NeZero n] in
include hac in
theorem r176o_uc_ne_ua : (Sum.inr (r176l_uc hu) : Mark P) ≠ Sum.inr (r176l_ua hu) := fun e =>
  r176l_visit_ne_of_edge_ne hac.symm (s176_mem_right hu) (s176_mem_left hu) (Sum.inr.inj e)

omit [NeZero n] in
include hac hbc in
theorem r176o_ja_ne_uc : (Sum.inr (visitOn j a (s176_mem_left hj)) : Mark P) ≠ Sum.inr (r176l_uc hu) := fun e =>
  r176l_visit_ne_of_ne (r176l_j_ne_u hac hbc hj hu) _ _ (Sum.inr.inj e)

omit [NeZero n] in
include hab hbc in
theorem r176o_vb_ne_uc : (Sum.inr (visitOn v b (s176_mem_left hv)) : Mark P) ≠ Sum.inr (r176l_uc hu) := fun e =>
  r176l_visit_ne_of_ne (r176l_u_ne_v hab hbc hu hv).symm _ _ (Sum.inr.inj e)

omit [NeZero n] in
include hbc in
theorem r176o_vb_ne_vc : (Sum.inr (visitOn v b (s176_mem_left hv)) : Mark P) ≠ Sum.inr (visitOn v c (s176_mem_right hv)) :=
  fun e => r176l_visit_ne_of_edge_ne hbc _ _ (Sum.inr.inj e)

include hG hT q hab hac hbc hj hu hv hjT huq hvq hρa hρb hρc hSf

theorem r176o_owner_ja : geoOwner hG.cg T (Sum.inr (visitOn j a (s176_mem_left hj))) = q := by
  rw [← r176l_succT_ua hG.cg q hj hu huq hρa, geoOwner_successor]
  exact r176l_owner_ua hG.cg q hu huq

/-- the orbit index `k` of `(u, a)` from `(u, c)` -/
theorem r176o_exists_k :
    ∃ k, 0 < k ∧ k < (geoComponentMarkList hG.cg T q).length ∧
      (geoSmoothingSuccessor hG.cg T ^ k) (Sum.inr (r176l_uc hu)) = Sum.inr (r176l_ua hu) := by
  obtain ⟨k, hk, hk'⟩ := r176o_exists_pow hG.cg hT q (r176l_owner_uc hG.cg q hu huq) (r176l_owner_ua hG.cg q hu huq)
  refine ⟨k, ?_, hk, hk'⟩
  rcases Nat.eq_zero_or_pos k with rfl | h
  · exact absurd (by simpa using hk') (r176o_uc_ne_ua hac hu)
  · exact h

theorem r176o_pow_vc :
    (geoSmoothingSuccessor hG.cg T ^ ((geoComponentMarkList hG.cg T q).length - 1)) (Sum.inr (r176l_uc hu)) =
      Sum.inr (visitOn v c (s176_mem_right hv)) := by
  have hN := CV.markList_length_pos hG.cg q
  rw [← r176l_succT_vc hG.cg q hu hv hvq hρc, ← Equiv.Perm.mul_apply, ← pow_succ, Nat.sub_add_cancel hN]
  exact r176o_pow_length_fixes hG.cg hT q (r176l_owner_vc hG.cg q hv hvq)


/-- away from the four visits of `u, v`, the smoothing successors of `S_full` and of `T` agree -/
theorem r176o_succSf_eq_succT (m : Mark P) (h1 : m ≠ Sum.inr (r176l_ua hu)) (h2 : m ≠ Sum.inr (r176l_uc hu))
    (h3 : m ≠ Sum.inr (visitOn v b (s176_mem_left hv))) (h4 : m ≠ Sum.inr (visitOn v c (s176_mem_right hv))) :
    geoSmoothingSuccessor hG.cg (r176l_Sf T u v) m = geoSmoothingSuccessor hG.cg T m := by
  rcases m with i | w
  · rfl
  · by_cases hw : w.1 ∈ T
    · rw [geoSmoothingSuccessor_visit_of_mem _ _ w (r176l_subset_Sf T u v hw),
        geoSmoothingSuccessor_visit_of_mem _ _ w hw]
    · have hw' : w.1 ∉ r176l_Sf T u v := by
        intro hmem
        rcases r176l_mem_ins.mp hmem with hv' | hmem
        · rcases visit_eq_or_twin (visitOn v b (s176_mem_left hv)) w hv' with e | e
          · exact h3 (by rw [e])
          · rw [r176l_twin_vb hv hbc] at e; exact h4 (by rw [e])
        · rcases r176l_mem_ins.mp hmem with hu' | hmem
          · rcases visit_eq_or_twin (r176l_ua hu) w hu' with e | e
            · exact h1 (by rw [e])
            · rw [r176l_twin_ua hu hac] at e; exact h2 (by rw [e])
          · exact hw hmem
      rw [geoSmoothingSuccessor_visit_of_not_mem _ _ w hw', geoSmoothingSuccessor_visit_of_not_mem _ _ w hw]

section WithK

variable {k : ℕ} (hk0 : 0 < k) (hkN : k < (geoComponentMarkList hG.cg T q).length)
  (hk : (geoSmoothingSuccessor hG.cg T ^ k) (Sum.inr (r176l_uc hu)) = Sum.inr (r176l_ua hu))

include hk0 hkN hk

theorem r176o_pow_ja :
    (geoSmoothingSuccessor hG.cg T ^ (k + 1)) (Sum.inr (r176l_uc hu)) = Sum.inr (visitOn j a (s176_mem_left hj)) := by
  rw [pow_succ', Equiv.Perm.mul_apply, hk]
  exact r176l_succT_ua hG.cg q hj hu huq hρa

theorem r176o_pow_vb :
    (geoSmoothingSuccessor hG.cg T ^ (k + 2)) (Sum.inr (r176l_uc hu)) = Sum.inr (visitOn v b (s176_mem_left hv)) := by
  rw [pow_succ', Equiv.Perm.mul_apply, r176o_pow_ja hG hT q hab hac hbc hj hu hv hjT huq hvq hρa hρb hρc hSf hk0 hkN hk]
  exact r176l_succT_ja hG.cg hab hj hv hjT hρb

/-- `(u,c), (u,a), (j,a), (v,b), (v,c)` sit at the orbit indices `0 < k < k+1 < k+2 < N-1` -/
theorem r176o_k_bounds : k + 3 < (geoComponentMarkList hG.cg T q).length := by
  have hN := CV.markList_length_pos hG.cg q
  have hown := r176l_owner_uc hG.cg q hu huq
  have hfix := r176o_pow_length_fixes hG.cg hT q hown
  have h1 : k + 1 ≠ (geoComponentMarkList hG.cg T q).length := by
    intro e
    have := r176o_pow_ja hG hT q hab hac hbc hj hu hv hjT huq hvq hρa hρb hρc hSf hk0 hkN hk
    rw [e, hfix] at this
    exact r176o_ja_ne_uc hac hbc hj hu this.symm
  have h2 : k + 2 ≠ (geoComponentMarkList hG.cg T q).length := by
    intro e
    have := r176o_pow_vb hG hT q hab hac hbc hj hu hv hjT huq hvq hρa hρb hρc hSf hk0 hkN hk
    rw [e, hfix] at this
    exact r176o_vb_ne_uc hab hbc hu hv this.symm
  have h3 : k + 2 ≠ (geoComponentMarkList hG.cg T q).length - 1 := by
    intro e
    have := r176o_pow_vb hG hT q hab hac hbc hj hu hv hjT huq hvq hρa hρb hρc hSf hk0 hkN hk
    rw [e, r176o_pow_vc hG hT q hab hac hbc hj hu hv hjT huq hvq hρa hρb hρc hSf] at this
    exact r176o_vb_ne_vc hbc hv this.symm
  omega

/-- **The clean child `Λ₂ = owner_{Sf} (u, a)` is `(u, a)` together with the open orbit arc `(u,c) → (u,a)`.** -/
theorem r176o_owner_L2_iff (m : Mark P) :
    geoOwner hG.cg (r176l_Sf T u v) m = r176l_L2 hG.cg T v hu ↔
      m = Sum.inr (r176l_ua hu) ∨ ∃ i, 0 < i ∧ i < k ∧ (geoSmoothingSuccessor hG.cg T ^ i) (Sum.inr (r176l_uc hu)) = m := by
  have hN := CV.markList_length_pos hG.cg q
  have hown := r176l_owner_uc hG.cg q hu huq
  have hb := r176o_k_bounds hG hT q hab hac hbc hj hu hv hjT huq hvq hρa hρb hρc hSf hk0 hkN hk
  rw [show r176l_L2 hG.cg T v hu = geoOwner hG.cg (r176l_Sf T u v) (Sum.inr (r176l_ua hu)) from rfl, eq_comm,
    geoOwner_eq_iff]
  refine r176o_sameCycle_transfer_iff (geoSmoothingSuccessor hG.cg T) (geoSmoothingSuccessor hG.cg (r176l_Sf T u v))
    hk0 ?_ ?_ hk m
  · rw [geoSmoothingSuccessor_visit_of_mem _ _ _ (r176l_u_mem_Sf T u v), r176l_twin_ua hu hac,
      geoSmoothingSuccessor_visit_of_not_mem _ _ _ (r176l_u_not_mem hG.cg q huq)]
  · intro i hi0 hik
    apply r176o_succSf_eq_succT hG hT q hab hac hbc hj hu hv hjT huq hvq hρa hρb hρc hSf
    · intro e
      have := r176o_pow_inj hG.cg hT q hown (by omega) hkN (e.trans hk.symm)
      omega
    · intro e
      have := r176o_pow_inj hG.cg hT q hown (by omega) hN (e.trans (by simp))
      omega
    · intro e
      have := r176o_pow_inj hG.cg hT q hown (by omega) (by omega)
        (e.trans (r176o_pow_vb hG hT q hab hac hbc hj hu hv hjT huq hvq hρa hρb hρc hSf hk0 hkN hk).symm)
      omega
    · intro e
      have := r176o_pow_inj hG.cg hT q hown (by omega) (by omega)
        (e.trans (r176o_pow_vc hG hT q hab hac hbc hj hu hv hjT huq hvq hρa hρb hρc hSf).symm)
      omega

/-- a mark of `q` lies strictly between `(u,c)` and `(u,a)` on `Γ` iff it is on the open orbit arc -/
theorem r176o_between_uc_ua_iff (m : Mark P) (hm : geoOwner hG.cg T m = q) :
    cycBetween (geoMarkKey hG.cg (Sum.inr (r176l_uc hu))) (geoMarkKey hG.cg m) (geoMarkKey hG.cg (Sum.inr (r176l_ua hu))) ↔
      ∃ i, 0 < i ∧ i < k ∧ (geoSmoothingSuccessor hG.cg T ^ i) (Sum.inr (r176l_uc hu)) = m := by
  have hN := CV.markList_length_pos hG.cg q
  have hown := r176l_owner_uc hG.cg q hu huq
  obtain ⟨i, hiN, rfl⟩ := r176o_exists_pow hG.cg hT q hown hm
  have h := r176o_cyc_iff hG.cg hT q hown (i := 0) (j := i) (l := k) hN hiN hkN
  simp only [pow_zero, Equiv.Perm.coe_one, id_eq, hk] at h
  rw [h]
  constructor
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact ⟨i, h1, h2, rfl⟩
    · omega
    · omega
  · rintro ⟨i', h1, h2, e⟩
    have := r176o_pow_inj hG.cg hT q hown (by omega) hiN e
    subst this
    exact Or.inl ⟨h1, h2⟩

/-- a mark of `q` lies strictly between `(u,a)` and `(u,c)` on `Γ` iff its orbit index exceeds `k` -/
theorem r176o_between_ua_uc_iff {i : ℕ} (hiN : i < (geoComponentMarkList hG.cg T q).length) :
    cycBetween (geoMarkKey hG.cg (Sum.inr (r176l_ua hu)))
        (geoMarkKey hG.cg ((geoSmoothingSuccessor hG.cg T ^ i) (Sum.inr (r176l_uc hu))))
        (geoMarkKey hG.cg (Sum.inr (r176l_uc hu))) ↔ k < i := by
  have hN := CV.markList_length_pos hG.cg q
  have hown := r176l_owner_uc hG.cg q hu huq
  have h := r176o_cyc_iff hG.cg hT q hown (i := k) (j := i) (l := 0) hkN hiN hN
  simp only [pow_zero, Equiv.Perm.coe_one, id_eq, hk] at h
  rw [h]
  omega

/-- **the `A`-side reading**: strictly between `(u,c)` and `(u,a)` iff on `Λ₂` and not `(u,a)` -/
theorem r176o_between_uc_ua_iff_L2 (m : Mark P) (hm : geoOwner hG.cg T m = q) :
    cycBetween (geoMarkKey hG.cg (Sum.inr (r176l_uc hu))) (geoMarkKey hG.cg m) (geoMarkKey hG.cg (Sum.inr (r176l_ua hu))) ↔
      geoOwner hG.cg (r176l_Sf T u v) m = r176l_L2 hG.cg T v hu ∧ m ≠ Sum.inr (r176l_ua hu) := by
  have hown := r176l_owner_uc hG.cg q hu huq
  rw [r176o_between_uc_ua_iff hG hT q hab hac hbc hj hu hv hjT huq hvq hρa hρb hρc hSf hk0 hkN hk m hm,
    r176o_owner_L2_iff hG hT q hab hac hbc hj hu hv hjT huq hvq hρa hρb hρc hSf hk0 hkN hk m]
  constructor
  · rintro ⟨i, h1, h2, e⟩
    refine ⟨Or.inr ⟨i, h1, h2, e⟩, fun e' => ?_⟩
    have := r176o_pow_inj hG.cg hT q hown (by omega) hkN (e.trans (e'.trans hk.symm))
    omega
  · rintro ⟨h | h, hne⟩
    · exact absurd h hne
    · exact h

/-- **the `B`-side reading**: for a mark of `q` other than `(u,a), (u,c), (j,a)`: strictly between `(u,a)`
and `(u,c)` iff on `Λ₁` or equal to `(v,b)` -/
theorem r176o_between_ua_uc_iff_L1 (m : Mark P) (hm : geoOwner hG.cg T m = q)
    (hja : m ≠ Sum.inr (visitOn j a (s176_mem_left hj))) :
    cycBetween (geoMarkKey hG.cg (Sum.inr (r176l_ua hu))) (geoMarkKey hG.cg m) (geoMarkKey hG.cg (Sum.inr (r176l_uc hu))) ↔
      geoOwner hG.cg (r176l_Sf T u v) m = r176l_L1 hG.cg T u hv ∨ m = Sum.inr (visitOn v b (s176_mem_left hv)) := by
  have hN := CV.markList_length_pos hG.cg q
  have hown := r176l_owner_uc hG.cg q hu huq
  have hb := r176o_k_bounds hG hT q hab hac hbc hj hu hv hjT huq hvq hρa hρb hρc hSf hk0 hkN hk
  have hL2 := r176o_owner_L2_iff hG hT q hab hac hbc hj hu hv hjT huq hvq hρa hρb hρc hSf hk0 hkN hk
  have hvb := r176o_pow_vb hG hT q hab hac hbc hj hu hv hjT huq hvq hρa hρb hρc hSf hk0 hkN hk
  obtain ⟨i, hiN, rfl⟩ := r176o_exists_pow hG.cg hT q hown hm
  rw [r176o_between_ua_uc_iff hG hT q hab hac hbc hj hu hv hjT huq hvq hρa hρb hρc hSf hk0 hkN hk hiN]
  have hinj : ∀ i', i' < (geoComponentMarkList hG.cg T q).length →
      (geoSmoothingSuccessor hG.cg T ^ i') (Sum.inr (r176l_uc hu)) =
        (geoSmoothingSuccessor hG.cg T ^ i) (Sum.inr (r176l_uc hu)) → i' = i :=
    fun i' hi' e => r176o_pow_inj hG.cg hT q hown hi' hiN e
  constructor
  · intro hki
    rcases r176l_owner_Sf_cases hG.cg hT q hab hac hbc hj hu hv hjT huq hvq hρa hρb hρc hSf _ hm with h | h | h
    · exact Or.inl h
    · exfalso
      rcases (hL2 _).mp h with e | ⟨i', h1, h2, e⟩
      · have := hinj k hkN (hk.trans e.symm); omega
      · have := hinj i' (by omega) e; omega
    · rcases r176l_mem_Z hG.cg q hab hac hbc hj hu hv hjT huq hvq hρa hρb hρc _ h with e | e | e
      · exfalso
        have := hinj 0 hN (by simpa using e.symm); omega
      · exact absurd e hja
      · exact Or.inr e
  · rintro (h | h)
    · by_contra hle
      have hik : i ≤ k := not_lt.mp hle
      rcases Nat.eq_zero_or_pos i with rfl | hpos
      · -- `m = (u,c)` lies on `Z`
        simp only [pow_zero, Equiv.Perm.coe_one, id_eq] at h
        exact r176l_L1_ne_Z hG.cg q hab hac hbc hj hu hv hjT huq hvq hρa hρb hρc hSf
          (h.symm.trans (r176l_Z_eq hG.cg q hab hac hbc hj hu hv hjT huq hvq hρa hρb hρc).1)
      · rcases Nat.lt_or_ge i k with hlt | hge
        · exact r176l_L1_ne_L2 hG.cg q hab hac hbc hj hu hv hjT huq hvq hρa hρb hSf
            (h.symm.trans ((hL2 _).mpr (Or.inr ⟨i, hpos, hlt, rfl⟩)))
        · have : i = k := by omega
          subst this
          rw [hk] at h
          exact r176l_L1_ne_L2 hG.cg q hab hac hbc hj hu hv hjT huq hvq hρa hρb hSf (h.symm.trans ((hL2 _).mpr (Or.inl rfl)))
    · have := hinj (k + 2) (by omega) (hvb.trans h.symm)
      omega

end WithK

end R176O_Geom

/-! ## §O3. The arcs of the lift at `y = lift u'` (occurrence `v₀ ↦ (u,c)`), read on the parent -/

section R176O_Lift

variable (hn : 3 ≤ n) {P : LabelledTuple n} (hG : CarrierGeometry P)
  {T : Finset (Crossing P)} (hT : GeoIndependent hG.cg T) (q : GeoComponent hG.cg T)
  {a b c : ZMod n} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
  {j u v : Crossing P} (hj : j.val = {a, b}) (hu : u.val = {a, c}) (hv : v.val = {b, c})
  (hjT : j ∈ T) (huq : u ∈ geoCarrierCrossings hG.cg T q) (hvq : v ∈ geoCarrierCrossings hG.cg T q)
  (hρa : geoMarkSuccessor hG.cg (Sum.inr (r176l_ua hu)) = Sum.inr (visitOn j a (s176_mem_left hj)))
  (hρb : geoMarkSuccessor hG.cg (Sum.inr (visitOn j b (s176_mem_right hj))) = Sum.inr (visitOn v b (s176_mem_left hv)))
  (hρc : geoMarkSuccessor hG.cg (Sum.inr (visitOn v c (s176_mem_right hv))) = Sum.inr (r176l_uc hu))
  (hSf : GeoIndependent hG.cg (r176l_Sf T u v))

attribute [local instance 2000] r176l_decEq

include hn hG hT q hab hac hbc hj hu hv hjT huq hvq hρa hρb hρc hSf

/-- **`K_A = liftBlock (retained Λ₂)`**: the chords with both occurrences on the arc `A = ((u,c) → (u,a))`
are the chords labelled by the retained crossings of the clean child `Λ₂ = owner_{Sf} (u, a)`. -/
theorem r176o_KA_eq (v₀ : (geoPositiveLift hn hG hT q).Γ.Visit) (hv₀ : CV.liftVisit hn hG hT q v₀ = r176l_uc hu) :
    r176s_KA (geoPositiveLift hn hG hT q).record v₀ =
      CV.liftBlock hn hG hT q (geoCarrierCrossings hG.cg (r176l_Sf T u v) (r176l_L2 hG.cg T v hu)) := by
  obtain ⟨k, hk0, hkN, hk⟩ := r176o_exists_k hG hT q hab hac hbc hj hu hv hjT huq hvq hρa hρb hρc hSf
  apply r176o_crossing_set_ext
  intro w
  rw [r176s_crossKeep_KA_iff_key hn hG hT q v₀ w, CV.crossKeep_liftBlock_iff, hv₀, r176l_twin_uc hu hac,
    mem_geoCarrierCrossings]
  set z := CV.liftVisit hn hG hT q w with hz
  have hzq : geoOwner hG.cg T (Sum.inr z) = q := CV.liftVisit_owner hn hG hT q w
  have hzq' : geoOwner hG.cg T (Sum.inr (visitTwin z)) = q := by
    rw [← CV.liftVisit_twin]; exact CV.liftVisit_owner hn hG hT q _
  have hzT : z.1 ∉ T := ((mem_geoCarrierCrossings _ _ _ _).mp (CV.liftVisit_mem hn hG hT q w)).1
  have h1 := r176o_between_uc_ua_iff_L2 hG hT q hab hac hbc hj hu hv hjT huq hvq hρa hρb hρc hSf hk0 hkN hk
    (Sum.inr z) hzq
  have h2 := r176o_between_uc_ua_iff_L2 hG hT q hab hac hbc hj hu hv hjT huq hvq hρa hρb hρc hSf hk0 hkN hk
    (Sum.inr (visitTwin z)) hzq'
  change (cycBetween (geoMarkKey hG.cg (Sum.inr (r176l_uc hu))) (geoMarkKey hG.cg (Sum.inr z))
      (geoMarkKey hG.cg (Sum.inr (r176l_ua hu))) ∧
    cycBetween (geoMarkKey hG.cg (Sum.inr (r176l_uc hu))) (geoMarkKey hG.cg (Sum.inr (visitTwin z)))
      (geoMarkKey hG.cg (Sum.inr (r176l_ua hu)))) ↔ _
  rw [h1, h2]
  constructor
  · rintro ⟨⟨hz1, hz2⟩, ⟨ht1, ht2⟩⟩
    refine ⟨?_, ?_⟩
    · intro hmem
      rcases r176l_mem_ins.mp hmem with e | hmem
      · rcases visit_eq_or_twin (visitOn v b (s176_mem_left hv)) z e with ez | ez
        · rw [ez] at hz1
          exact r176l_L2_ne_Z hG.cg q hab hac hbc hj hu hv hjT huq hvq hρa hρb hρc hSf
            (hz1.symm.trans (r176l_Z_eq hG.cg q hab hac hbc hj hu hv hjT huq hvq hρa hρb hρc).2)
        · rw [r176l_twin_vb hv hbc] at ez
          rw [ez] at hz1
          exact r176l_L1_ne_L2 hG.cg q hab hac hbc hj hu hv hjT huq hvq hρa hρb hSf hz1
      · rcases r176l_mem_ins.mp hmem with e | hmem
        · rcases visit_eq_or_twin (r176l_ua hu) z e with ez | ez
          · exact hz2 (by rw [ez])
          · rw [r176l_twin_ua hu hac] at ez
            exact ht2 (by rw [ez, r176l_twin_uc hu hac])
        · exact hzT hmem
    · intro w' hw'
      rcases visit_eq_or_twin z w' hw' with e | e
      · rw [e]; exact hz1
      · rw [e]; exact ht1
  · rintro ⟨hnot, hall⟩
    have hzu : z.1 ≠ u := fun e => hnot (by rw [e]; exact r176l_u_mem_Sf T u v)
    refine ⟨⟨hall z rfl, fun e => hzu (by rw [Sum.inr.inj e]; rfl)⟩, ⟨hall _ rfl, fun e => hzu ?_⟩⟩
    have := congrArg (fun w : Visit P => w.1) (Sum.inr.inj e)
    have h2 : z.1 = (r176l_ua hu).1 := by simpa using this
    exact h2

/-- **`K_B = liftBlock (retained Λ₁) ∪ {lift v}`**: the chords with both occurrences on the arc
`B = ((u,a) → (u,c))` are those of the kinked child `Λ₁ = owner_{Sf} (v, c)` plus the kink. -/
theorem r176o_KB_eq (v₀ : (geoPositiveLift hn hG hT q).Γ.Visit) (hv₀ : CV.liftVisit hn hG hT q v₀ = r176l_uc hu)
    (vb₀ : (geoPositiveLift hn hG hT q).Γ.Visit) (hvb₀ : CV.liftVisit hn hG hT q vb₀ = visitOn v b (s176_mem_left hv)) :
    r176s_KB (geoPositiveLift hn hG hT q).record v₀ =
      CV.liftBlock hn hG hT q (geoCarrierCrossings hG.cg (r176l_Sf T u v) (r176l_L1 hG.cg T u hv)) ∪
        {(geoPositiveLift hn hG hT q).record.crossingOf vb₀} := by
  obtain ⟨k, hk0, hkN, hk⟩ := r176o_exists_k hG hT q hab hac hbc hj hu hv hjT huq hvq hρa hρb hρc hSf
  show r176s_KA (geoPositiveLift hn hG hT q).record ((geoPositiveLift hn hG hT q).twin v₀) = _
  apply r176o_crossing_set_ext
  intro w
  rw [r176s_crossKeep_KA_iff_key hn hG hT q ((geoPositiveLift hn hG hT q).twin v₀) w, CV.liftVisit_twin, hv₀, r176l_twin_uc hu hac,
    r176l_twin_ua hu hac]
  set z := CV.liftVisit hn hG hT q w with hz
  have hzq : geoOwner hG.cg T (Sum.inr z) = q := CV.liftVisit_owner hn hG hT q w
  have hzq' : geoOwner hG.cg T (Sum.inr (visitTwin z)) = q := by
    rw [← CV.liftVisit_twin]; exact CV.liftVisit_owner hn hG hT q _
  have hzT : z.1 ∉ T := ((mem_geoCarrierCrossings _ _ _ _).mp (CV.liftVisit_mem hn hG hT q w)).1
  have e1 : (geoPositiveLift hn hG hT q).record.crossingOf w ∈
      CV.liftBlock hn hG hT q (geoCarrierCrossings hG.cg (r176l_Sf T u v) (r176l_L1 hG.cg T u hv)) ↔
      z.1 ∈ geoCarrierCrossings hG.cg (r176l_Sf T u v) (r176l_L1 hG.cg T u hv) :=
    CV.crossKeep_liftBlock_iff hn hG hT q _ w
  have e2 : w = vb₀ ↔ z = visitOn v b (s176_mem_left hv) := by
    rw [← hvb₀]; exact (CV.liftVisit_injective hn hG hT q).eq_iff.symm
  have e3 : w = (geoPositiveLift hn hG hT q).twin vb₀ ↔ z = visitOn v c (s176_mem_right hv) := by
    rw [← r176l_twin_vb hv hbc, ← hvb₀, ← CV.liftVisit_twin]
    exact (CV.liftVisit_injective hn hG hT q).eq_iff.symm
  show _ ↔ (geoPositiveLift hn hG hT q).record.crossingOf w ∈ _ ∪ _
  rw [Set.mem_union, Set.mem_singleton_iff, (geoPositiveLift hn hG hT q).record.crossingOf_eq_iff, e1, mem_geoCarrierCrossings]
  have e4 : w ∈ ({vb₀, (geoPositiveLift hn hG hT q).record.pair vb₀} : Finset (geoPositiveLift hn hG hT q).record.M) ↔
      w = vb₀ ∨ w = (geoPositiveLift hn hG hT q).twin vb₀ := by
    rw [Finset.mem_insert, Finset.mem_singleton, (geoPositiveLift hn hG hT q).record_pair_apply]
  show _ ↔ _ ∨ w ∈ ({vb₀, (geoPositiveLift hn hG hT q).record.pair vb₀} : Finset _)
  rw [e4, e2, e3]
  change (cycBetween (geoMarkKey hG.cg (Sum.inr (r176l_ua hu))) (geoMarkKey hG.cg (Sum.inr z))
      (geoMarkKey hG.cg (Sum.inr (r176l_uc hu))) ∧
    cycBetween (geoMarkKey hG.cg (Sum.inr (r176l_ua hu))) (geoMarkKey hG.cg (Sum.inr (visitTwin z)))
      (geoMarkKey hG.cg (Sum.inr (r176l_uc hu)))) ↔ _
  have hzj : Sum.inr z ≠ (Sum.inr (visitOn j a (s176_mem_left hj)) : Mark P) := fun e =>
    hzT (by rw [show z.1 = j from congrArg (fun w : Visit P => w.1) (Sum.inr.inj e)]; exact hjT)
  have hzj' : Sum.inr (visitTwin z) ≠ (Sum.inr (visitOn j a (s176_mem_left hj)) : Mark P) := fun e => by
    have := congrArg (fun w : Visit P => w.1) (Sum.inr.inj e)
    simp only [visitTwin_crossing] at this
    exact hzT (by rw [show z.1 = j from this]; exact hjT)
  by_cases hzu : z.1 = u
  · have hz' : z = r176l_ua hu ∨ z = r176l_uc hu := by
      rcases visit_eq_or_twin (r176l_ua hu) z hzu with e | e
      · exact Or.inl e
      · rw [r176l_twin_ua hu hac] at e; exact Or.inr e
    constructor
    · rintro ⟨h1, -⟩
      exfalso
      rcases hz' with e | e
      · rw [e] at h1; exact not_cycBetween_self_left _ _ h1
      · rw [e] at h1; exact not_cycBetween_self_mid _ _ h1
    · rintro (⟨hnot, -⟩ | e | e)
      · exact absurd (by rw [hzu]; exact r176l_u_mem_Sf T u v) hnot
      · exact (r176l_u_ne_v hab hbc hu hv (hzu.symm.trans (congrArg (fun w : Visit P => w.1) e))).elim
      · exact (r176l_u_ne_v hab hbc hu hv (hzu.symm.trans (congrArg (fun w : Visit P => w.1) e))).elim
  · rw [r176o_between_ua_uc_iff_L1 hG hT q hab hac hbc hj hu hv hjT huq hvq hρa hρb hρc hSf hk0 hkN hk
        (Sum.inr z) hzq hzj,
      r176o_between_ua_uc_iff_L1 hG hT q hab hac hbc hj hu hv hjT huq hvq hρa hρb hρc hSf hk0 hkN hk
        (Sum.inr (visitTwin z)) hzq' hzj']
    by_cases hzv : z.1 = v
    · have hz' : z = visitOn v b (s176_mem_left hv) ∨ z = visitOn v c (s176_mem_right hv) := by
        rcases visit_eq_or_twin (visitOn v b (s176_mem_left hv)) z hzv with e | e
        · exact Or.inl e
        · rw [r176l_twin_vb hv hbc] at e; exact Or.inr e
      constructor
      · intro _
        rcases hz' with e | e
        · exact Or.inr (Or.inl e)
        · exact Or.inr (Or.inr e)
      · intro _
        rcases hz' with e | e
        · refine ⟨Or.inr (by rw [e]), Or.inl ?_⟩
          rw [e, r176l_twin_vb hv hbc]
        · refine ⟨Or.inl (by rw [e]), Or.inr ?_⟩
          rw [e, r176l_twin_vc hv hbc]
    · have hnot : z.1 ∉ r176l_Sf T u v := by
        intro hmem
        rcases r176l_mem_ins.mp hmem with e | hmem
        · exact hzv e
        · rcases r176l_mem_ins.mp hmem with e | hmem
          · exact hzu e
          · exact hzT hmem
      have hzvb : Sum.inr z ≠ (Sum.inr (visitOn v b (s176_mem_left hv)) : Mark P) := fun e =>
        hzv (congrArg (fun w : Visit P => w.1) (Sum.inr.inj e))
      have hzvb' : Sum.inr (visitTwin z) ≠ (Sum.inr (visitOn v b (s176_mem_left hv)) : Mark P) := fun e => by
        have := congrArg (fun w : Visit P => w.1) (Sum.inr.inj e)
        simp only [visitTwin_crossing] at this
        exact hzv this
      constructor
      · rintro ⟨h1 | h1, h2 | h2⟩
        · left
          refine ⟨hnot, fun w' hw' => ?_⟩
          rcases visit_eq_or_twin z w' hw' with e | e
          · rw [e]; exact h1
          · rw [e]; exact h2
        · exact absurd h2 hzvb'
        · exact absurd h1 hzvb
        · exact absurd h1 hzvb
      · rintro (⟨-, hall⟩ | e | e)
        · exact ⟨Or.inl (hall z rfl), Or.inl (hall _ rfl)⟩
        · exact absurd (congrArg (fun w : Visit P => w.1) e) hzv
        · exact absurd (congrArg (fun w : Visit P => w.1) e) hzv

/-- the kink is not a chord of `Λ₁` -/
theorem r176o_r_not (vb₀ : (geoPositiveLift hn hG hT q).Γ.Visit) (hvb₀ : CV.liftVisit hn hG hT q vb₀ = visitOn v b (s176_mem_left hv)) :
    (geoPositiveLift hn hG hT q).record.crossingOf vb₀ ∉
      CV.liftBlock hn hG hT q (geoCarrierCrossings hG.cg (r176l_Sf T u v) (r176l_L1 hG.cg T u hv)) := by
  intro h
  have h' := (CV.crossKeep_liftBlock_iff hn hG hT q _ vb₀).mp h
  rw [hvb₀] at h'
  exact ((mem_geoCarrierCrossings _ _ _ _).mp h').1 (r176l_v_mem_Sf T u v)

/-- **the kink is a curl of `ρ|B`**: the `B`-restricted successor of the `(v,c)`-occurrence is the
`(v,b)`-occurrence (the arc `B` wraps from `(v,c)` through `(u,c), C, (u,a)` — none of them in `K_B` — to `(v,b)`). -/
theorem r176o_r_curl (v₀ : (geoPositiveLift hn hG hT q).Γ.Visit) (hv₀ : CV.liftVisit hn hG hT q v₀ = r176l_uc hu)
    (vb₀ : (geoPositiveLift hn hG hT q).Γ.Visit) (hvb₀ : CV.liftVisit hn hG hT q vb₀ = visitOn v b (s176_mem_left hv)) :
    ∃ (w : (geoPositiveLift hn hG hT q).record.M) (hw : (geoPositiveLift hn hG hT q).record.CrossKeep (r176s_KB (geoPositiveLift hn hG hT q).record v₀) w),
      (geoPositiveLift hn hG hT q).record.crossingOf w = (geoPositiveLift hn hG hT q).record.crossingOf vb₀ ∧
      (((geoPositiveLift hn hG hT q).record.restrictCrossings (r176s_KB (geoPositiveLift hn hG hT q).record v₀)).succ ⟨w, hw⟩).1 = (geoPositiveLift hn hG hT q).record.pair w := by
  obtain ⟨k, hk0, hkN, hk⟩ := r176o_exists_k hG hT q hab hac hbc hj hu hv hjT huq hvq hρa hρb hρc hSf
  have h1 : (geoPositiveLift hn hG hT q).record.componentCount = 1 :=
    CV.record_componentCount_one _ (geoPositiveLift_componentCount hn hG hT q)
  have hKB := r176o_KB_eq hn hG hT q hab hac hbc hj hu hv hjT huq hvq hρa hρb hρc hSf v₀ hv₀ vb₀ hvb₀
  have hcr : (geoPositiveLift hn hG hT q).record.crossingOf ((geoPositiveLift hn hG hT q).twin vb₀) = (geoPositiveLift hn hG hT q).record.crossingOf vb₀ := by
    rw [← (geoPositiveLift hn hG hT q).record_pair_apply]; exact (geoPositiveLift hn hG hT q).record.crossingOf_pair vb₀
  have hwc : (geoPositiveLift hn hG hT q).record.CrossKeep (r176s_KB (geoPositiveLift hn hG hT q).record v₀) ((geoPositiveLift hn hG hT q).twin vb₀) := by
    show (geoPositiveLift hn hG hT q).record.crossingOf ((geoPositiveLift hn hG hT q).twin vb₀) ∈ _
    rw [hKB, hcr]; exact Or.inr rfl
  have hwb : (geoPositiveLift hn hG hT q).record.CrossKeep (r176s_KB (geoPositiveLift hn hG hT q).record v₀) vb₀ := by
    show (geoPositiveLift hn hG hT q).record.crossingOf vb₀ ∈ _
    rw [hKB]; exact Or.inr rfl
  refine ⟨(geoPositiveLift hn hG hT q).twin vb₀, hwc, hcr, ?_⟩
  rw [(geoPositiveLift hn hG hT q).record_pair_apply, (geoPositiveLift hn hG hT q).twin_twin, (geoPositiveLift hn hG hT q).record.restrictCrossings_succ_val_eq_iff h1 _ hwc]
  refine ⟨hwb, ((geoPositiveLift hn hG hT q).twin_ne vb₀).symm, fun x hx hxne => ?_⟩
  by_contra hlt
  push Not at hlt
  have harc : (geoPositiveLift hn hG hT q).record.ArcBetween ((geoPositiveLift hn hG hT q).twin vb₀) x vb₀ :=
    ⟨((geoPositiveLift hn hG hT q).record.steps_pos_iff h1 _ _).mpr hxne.symm, hlt⟩
  rw [CV.arcBetween_iff_key, CV.liftVisit_twin, hvb₀, r176l_twin_vb hv hbc] at harc
  have hx0 : (geoPositiveLift hn hG hT q).record.CrossKeep (r176s_KA (geoPositiveLift hn hG hT q).record ((geoPositiveLift hn hG hT q).twin v₀)) x := hx
  have hx' := (r176s_crossKeep_KA_iff_key hn hG hT q ((geoPositiveLift hn hG hT q).twin v₀) x).mp hx0
  rw [CV.liftVisit_twin, hv₀, r176l_twin_uc hu hac, r176l_twin_ua hu hac] at hx'
  set z := CV.liftVisit hn hG hT q x with hz
  have hzq : geoOwner hG.cg T (Sum.inr z) = q := CV.liftVisit_owner hn hG hT q x
  have hzT : z.1 ∉ T := ((mem_geoCarrierCrossings _ _ _ _).mp (CV.liftVisit_mem hn hG hT q x)).1
  have hown := r176l_owner_uc hG.cg q hu huq
  obtain ⟨i, hiN, hi⟩ := r176o_exists_pow hG.cg hT q hown hzq
  have hb := r176o_k_bounds hG hT q hab hac hbc hj hu hv hjT huq hvq hρa hρb hρc hSf hk0 hkN hk
  have hN := CV.markList_length_pos hG.cg q
  have hgt : k < i := by
    have := r176o_between_ua_uc_iff hG hT q hab hac hbc hj hu hv hjT huq hvq hρa hρb hρc hSf hk0 hkN hk hiN
    rw [hi] at this
    exact this.mp hx'.1
  have hlt2 : i < k + 2 := by
    have := r176o_cyc_iff hG.cg hT q hown (i := (geoComponentMarkList hG.cg T q).length - 1) (j := i) (l := k + 2)
      (by omega) hiN (by omega)
    rw [r176o_pow_vc hG hT q hab hac hbc hj hu hv hjT huq hvq hρa hρb hρc hSf,
      r176o_pow_vb hG hT q hab hac hbc hj hu hv hjT huq hvq hρa hρb hρc hSf hk0 hkN hk, hi] at this
    have h' := this.mp harc
    omega
  have hik : i = k + 1 := by omega
  subst hik
  rw [r176o_pow_ja hG hT q hab hac hbc hj hu hv hjT huq hvq hρa hρb hρc hSf hk0 hkN hk] at hi
  exact hzT (by rw [show z.1 = j from congrArg (fun w : Visit P => w.1) (Sum.inr.inj hi.symm)]; exact hjT)

end R176O_Lift

/-! ## §O5. The mirrored case `y = lift v'` (occurrence `v₀ ↦ (v,b)`): the corrected second half -/

section R176O_Mirror

variable (hn : 3 ≤ n) {P : LabelledTuple n} (hG : CarrierGeometry P)
  {T : Finset (Crossing P)} (hT : GeoIndependent hG.cg T) (q : GeoComponent hG.cg T)
  {a b c : ZMod n} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
  {j u v : Crossing P} (hj : j.val = {a, b}) (hu : u.val = {a, c}) (hv : v.val = {b, c})
  (hjT : j ∈ T) (huq : u ∈ geoCarrierCrossings hG.cg T q) (hvq : v ∈ geoCarrierCrossings hG.cg T q)
  (hρa : geoMarkSuccessor hG.cg (Sum.inr (r176l_ua hu)) = Sum.inr (visitOn j a (s176_mem_left hj)))
  (hρb : geoMarkSuccessor hG.cg (Sum.inr (visitOn j b (s176_mem_right hj))) = Sum.inr (visitOn v b (s176_mem_left hv)))
  (hρc : geoMarkSuccessor hG.cg (Sum.inr (visitOn v c (s176_mem_right hv))) = Sum.inr (r176l_uc hu))
  (hSf : GeoIndependent hG.cg (r176l_Sf T u v))

attribute [local instance 2000] r176l_decEq

include hG hT q hab hac hbc hj hu hv hjT huq hvq hρa hρb hρc hSf

/-- **the mirrored `A`-side reading**: for a mark of `q` other than `(j,a)`: strictly between `(v,b)` and `(v,c)`
iff on `Λ₁` and not `(v,c)` -/
theorem r176o_between_vb_vc_iff_L1 (m : Mark P) (hm : geoOwner hG.cg T m = q)
    (hja : m ≠ Sum.inr (visitOn j a (s176_mem_left hj))) :
    cycBetween (geoMarkKey hG.cg (Sum.inr (visitOn v b (s176_mem_left hv)))) (geoMarkKey hG.cg m)
        (geoMarkKey hG.cg (Sum.inr (visitOn v c (s176_mem_right hv)))) ↔
      geoOwner hG.cg (r176l_Sf T u v) m = r176l_L1 hG.cg T u hv ∧ m ≠ Sum.inr (visitOn v c (s176_mem_right hv)) := by
  obtain ⟨k, hk0, hkN, hk⟩ := r176o_exists_k hG hT q hab hac hbc hj hu hv hjT huq hvq hρa hρb hρc hSf
  have hN := CV.markList_length_pos hG.cg q
  have hown := r176l_owner_uc hG.cg q hu huq
  have hb := r176o_k_bounds hG hT q hab hac hbc hj hu hv hjT huq hvq hρa hρb hρc hSf hk0 hkN hk
  have hvb := r176o_pow_vb hG hT q hab hac hbc hj hu hv hjT huq hvq hρa hρb hρc hSf hk0 hkN hk
  have hvc := r176o_pow_vc hG hT q hab hac hbc hj hu hv hjT huq hvq hρa hρb hρc hSf
  have hja' := r176o_pow_ja hG hT q hab hac hbc hj hu hv hjT huq hvq hρa hρb hρc hSf hk0 hkN hk
  have hL1 := r176o_between_ua_uc_iff_L1 hG hT q hab hac hbc hj hu hv hjT huq hvq hρa hρb hρc hSf hk0 hkN hk m hm hja
  obtain ⟨i, hiN, rfl⟩ := r176o_exists_pow hG.cg hT q hown hm
  rw [r176o_between_ua_uc_iff hG hT q hab hac hbc hj hu hv hjT huq hvq hρa hρb hρc hSf hk0 hkN hk hiN] at hL1
  have hinj : ∀ i', i' < (geoComponentMarkList hG.cg T q).length →
      (geoSmoothingSuccessor hG.cg T ^ i') (Sum.inr (r176l_uc hu)) =
        (geoSmoothingSuccessor hG.cg T ^ i) (Sum.inr (r176l_uc hu)) → i' = i :=
    fun i' hi' e => r176o_pow_inj hG.cg hT q hown hi' hiN e
  have hcyc := r176o_cyc_iff hG.cg hT q hown (i := k + 2) (j := i) (l := (geoComponentMarkList hG.cg T q).length - 1)
    (by omega) hiN (by omega)
  rw [hvb, hvc] at hcyc
  rw [hcyc]
  have hne_ja : i ≠ k + 1 := fun e => hja (by rw [e, hja'])
  have hne_vc : (geoSmoothingSuccessor hG.cg T ^ i) (Sum.inr (r176l_uc hu)) ≠ Sum.inr (visitOn v c (s176_mem_right hv)) ↔
      i ≠ (geoComponentMarkList hG.cg T q).length - 1 := by
    constructor
    · intro h e; exact h (by rw [e, hvc])
    · intro h e; exact h (hinj _ (by omega) (hvc.trans e.symm)).symm
  have hne_vb : (geoSmoothingSuccessor hG.cg T ^ i) (Sum.inr (r176l_uc hu)) ≠ Sum.inr (visitOn v b (s176_mem_left hv)) ↔
      i ≠ k + 2 := by
    constructor
    · intro h e; exact h (by rw [e, hvb])
    · intro h e; exact h (hinj _ (by omega) (hvb.trans e.symm)).symm
  have hZvb : geoOwner hG.cg (r176l_Sf T u v) (Sum.inr (visitOn v b (s176_mem_left hv))) ≠ r176l_L1 hG.cg T u hv := by
    rw [(r176l_Z_eq hG.cg q hab hac hbc hj hu hv hjT huq hvq hρa hρb hρc).2]
    exact (r176l_L1_ne_Z hG.cg q hab hac hbc hj hu hv hjT huq hvq hρa hρb hρc hSf).symm
  constructor
  · intro h
    have hki : k < i := by omega
    have hL1' := hL1.mp hki
    rcases hL1' with h1 | h1
    · exact ⟨h1, hne_vc.mpr (by omega)⟩
    · exfalso; exact (hne_vb.mpr (by omega)) h1
  · rintro ⟨h1, h2⟩
    have hki : k < i := hL1.mpr (Or.inl h1)
    have h3 : i ≠ k + 2 := by
      intro e; rw [e, hvb] at h1; exact hZvb h1
    have h4 := hne_vc.mp h2
    omega

/-- **the mirrored `B`-side reading**: for a mark of `q` other than `(j,a)`: strictly between `(v,c)` and `(v,b)`
iff on `Λ₂` or equal to `(u,c)` -/
theorem r176o_between_vc_vb_iff_L2 (m : Mark P) (hm : geoOwner hG.cg T m = q)
    (hja : m ≠ Sum.inr (visitOn j a (s176_mem_left hj))) :
    cycBetween (geoMarkKey hG.cg (Sum.inr (visitOn v c (s176_mem_right hv)))) (geoMarkKey hG.cg m)
        (geoMarkKey hG.cg (Sum.inr (visitOn v b (s176_mem_left hv)))) ↔
      geoOwner hG.cg (r176l_Sf T u v) m = r176l_L2 hG.cg T v hu ∨ m = Sum.inr (r176l_uc hu) := by
  obtain ⟨k, hk0, hkN, hk⟩ := r176o_exists_k hG hT q hab hac hbc hj hu hv hjT huq hvq hρa hρb hρc hSf
  have hN := CV.markList_length_pos hG.cg q
  have hown := r176l_owner_uc hG.cg q hu huq
  have hb := r176o_k_bounds hG hT q hab hac hbc hj hu hv hjT huq hvq hρa hρb hρc hSf hk0 hkN hk
  have hvb := r176o_pow_vb hG hT q hab hac hbc hj hu hv hjT huq hvq hρa hρb hρc hSf hk0 hkN hk
  have hvc := r176o_pow_vc hG hT q hab hac hbc hj hu hv hjT huq hvq hρa hρb hρc hSf
  have hja' := r176o_pow_ja hG hT q hab hac hbc hj hu hv hjT huq hvq hρa hρb hρc hSf hk0 hkN hk
  have hL2 := r176o_owner_L2_iff hG hT q hab hac hbc hj hu hv hjT huq hvq hρa hρb hρc hSf hk0 hkN hk m
  obtain ⟨i, hiN, rfl⟩ := r176o_exists_pow hG.cg hT q hown hm
  have hinj : ∀ i', i' < (geoComponentMarkList hG.cg T q).length →
      (geoSmoothingSuccessor hG.cg T ^ i') (Sum.inr (r176l_uc hu)) =
        (geoSmoothingSuccessor hG.cg T ^ i) (Sum.inr (r176l_uc hu)) → i' = i :=
    fun i' hi' e => r176o_pow_inj hG.cg hT q hown hi' hiN e
  have hcyc := r176o_cyc_iff hG.cg hT q hown (i := (geoComponentMarkList hG.cg T q).length - 1) (j := i) (l := k + 2)
    (by omega) hiN (by omega)
  rw [hvb, hvc] at hcyc
  rw [hcyc, hL2]
  have hne_ja : i ≠ k + 1 := fun e => hja (by rw [e, hja'])
  constructor
  · intro h
    have hi2 : i < k + 2 := by omega
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · right; simp
    · left
      rcases Nat.lt_or_ge i k with hlt | hge
      · exact Or.inr ⟨i, hpos, hlt, rfl⟩
      · have : i = k := by omega
        subst this
        exact Or.inl hk
  · rintro ((e | ⟨i', h1, h2, e⟩) | e)
    · have := hinj k hkN (hk.trans e.symm); omega
    · have := hinj i' (by omega) e; omega
    · have := hinj 0 hN (by simpa using e.symm); omega

/-- **mirrored `K_A`**: at `v₀ ↦ (v,b)`, the arc `A = ((v,b) → (v,c))` carries exactly the chords of `Λ₁` -/
theorem r176o_KA_eq' (v₀ : (geoPositiveLift hn hG hT q).Γ.Visit)
    (hv₀ : CV.liftVisit hn hG hT q v₀ = visitOn v b (s176_mem_left hv)) :
    r176s_KA (geoPositiveLift hn hG hT q).record v₀ =
      CV.liftBlock hn hG hT q (geoCarrierCrossings hG.cg (r176l_Sf T u v) (r176l_L1 hG.cg T u hv)) := by
  apply r176o_crossing_set_ext
  intro w
  rw [r176s_crossKeep_KA_iff_key hn hG hT q v₀ w, CV.crossKeep_liftBlock_iff, hv₀, r176l_twin_vb hv hbc,
    mem_geoCarrierCrossings]
  set z := CV.liftVisit hn hG hT q w with hz
  have hzq : geoOwner hG.cg T (Sum.inr z) = q := CV.liftVisit_owner hn hG hT q w
  have hzq' : geoOwner hG.cg T (Sum.inr (visitTwin z)) = q := by
    rw [← CV.liftVisit_twin]; exact CV.liftVisit_owner hn hG hT q _
  have hzT : z.1 ∉ T := ((mem_geoCarrierCrossings _ _ _ _).mp (CV.liftVisit_mem hn hG hT q w)).1
  have hzj : Sum.inr z ≠ (Sum.inr (visitOn j a (s176_mem_left hj)) : Mark P) := fun e =>
    hzT (by rw [show z.1 = j from congrArg (fun w : Visit P => w.1) (Sum.inr.inj e)]; exact hjT)
  have hzj' : Sum.inr (visitTwin z) ≠ (Sum.inr (visitOn j a (s176_mem_left hj)) : Mark P) := fun e => by
    have := congrArg (fun w : Visit P => w.1) (Sum.inr.inj e)
    simp only [visitTwin_crossing] at this
    exact hzT (by rw [show z.1 = j from this]; exact hjT)
  have h1 := r176o_between_vb_vc_iff_L1 hG hT q hab hac hbc hj hu hv hjT huq hvq hρa hρb hρc hSf (Sum.inr z) hzq hzj
  have h2 := r176o_between_vb_vc_iff_L1 hG hT q hab hac hbc hj hu hv hjT huq hvq hρa hρb hρc hSf
    (Sum.inr (visitTwin z)) hzq' hzj'
  change (cycBetween (geoMarkKey hG.cg (Sum.inr (visitOn v b (s176_mem_left hv)))) (geoMarkKey hG.cg (Sum.inr z))
      (geoMarkKey hG.cg (Sum.inr (visitOn v c (s176_mem_right hv)))) ∧
    cycBetween (geoMarkKey hG.cg (Sum.inr (visitOn v b (s176_mem_left hv)))) (geoMarkKey hG.cg (Sum.inr (visitTwin z)))
      (geoMarkKey hG.cg (Sum.inr (visitOn v c (s176_mem_right hv))))) ↔ _
  rw [h1, h2]
  have hZ := r176l_Z_eq hG.cg q hab hac hbc hj hu hv hjT huq hvq hρa hρb hρc
  have hL1Z := r176l_L1_ne_Z hG.cg q hab hac hbc hj hu hv hjT huq hvq hρa hρb hρc hSf
  have hL1L2 := r176l_L1_ne_L2 hG.cg q hab hac hbc hj hu hv hjT huq hvq hρa hρb hSf
  constructor
  · rintro ⟨⟨hz1, hz2⟩, ⟨ht1, ht2⟩⟩
    refine ⟨?_, ?_⟩
    · intro hmem
      rcases r176l_mem_ins.mp hmem with e | hmem
      · rcases visit_eq_or_twin (visitOn v b (s176_mem_left hv)) z e with ez | ez
        · rw [ez, hZ.2] at hz1; exact hL1Z hz1.symm
        · rw [r176l_twin_vb hv hbc] at ez; exact hz2 (by rw [ez])
      · rcases r176l_mem_ins.mp hmem with e | hmem
        · rcases visit_eq_or_twin (r176l_ua hu) z e with ez | ez
          · rw [ez] at hz1; exact hL1L2 hz1.symm
          · rw [r176l_twin_ua hu hac] at ez; rw [ez, hZ.1] at hz1; exact hL1Z hz1.symm
        · exact hzT hmem
    · intro w' hw'
      rcases visit_eq_or_twin z w' hw' with e | e
      · rw [e]; exact hz1
      · rw [e]; exact ht1
  · rintro ⟨hnot, hall⟩
    have hzv : z.1 ≠ v := fun e => hnot (by rw [e]; exact r176l_v_mem_Sf T u v)
    refine ⟨⟨hall z rfl, fun e => hzv (by rw [Sum.inr.inj e]; rfl)⟩, ⟨hall _ rfl, fun e => hzv ?_⟩⟩
    have := congrArg (fun w : Visit P => w.1) (Sum.inr.inj e)
    have h2 : z.1 = (visitOn v c (s176_mem_right hv)).1 := by simpa using this
    exact h2

/-- **mirrored `K_B`**: at `v₀ ↦ (v,b)`, the arc `B = ((v,c) → (v,b))` carries the chords of `Λ₂` plus the kink `lift u` -/
theorem r176o_KB_eq' (v₀ : (geoPositiveLift hn hG hT q).Γ.Visit)
    (hv₀ : CV.liftVisit hn hG hT q v₀ = visitOn v b (s176_mem_left hv))
    (ua₀ : (geoPositiveLift hn hG hT q).Γ.Visit) (hua₀ : CV.liftVisit hn hG hT q ua₀ = r176l_ua hu) :
    r176s_KB (geoPositiveLift hn hG hT q).record v₀ =
      CV.liftBlock hn hG hT q (geoCarrierCrossings hG.cg (r176l_Sf T u v) (r176l_L2 hG.cg T v hu)) ∪
        {(geoPositiveLift hn hG hT q).record.crossingOf ua₀} := by
  show r176s_KA (geoPositiveLift hn hG hT q).record ((geoPositiveLift hn hG hT q).twin v₀) = _
  apply r176o_crossing_set_ext
  intro w
  rw [r176s_crossKeep_KA_iff_key hn hG hT q ((geoPositiveLift hn hG hT q).twin v₀) w, CV.liftVisit_twin, hv₀,
    r176l_twin_vb hv hbc, r176l_twin_vc hv hbc]
  set z := CV.liftVisit hn hG hT q w with hz
  have hzq : geoOwner hG.cg T (Sum.inr z) = q := CV.liftVisit_owner hn hG hT q w
  have hzq' : geoOwner hG.cg T (Sum.inr (visitTwin z)) = q := by
    rw [← CV.liftVisit_twin]; exact CV.liftVisit_owner hn hG hT q _
  have hzT : z.1 ∉ T := ((mem_geoCarrierCrossings _ _ _ _).mp (CV.liftVisit_mem hn hG hT q w)).1
  have e1 : (geoPositiveLift hn hG hT q).record.crossingOf w ∈
      CV.liftBlock hn hG hT q (geoCarrierCrossings hG.cg (r176l_Sf T u v) (r176l_L2 hG.cg T v hu)) ↔
      z.1 ∈ geoCarrierCrossings hG.cg (r176l_Sf T u v) (r176l_L2 hG.cg T v hu) :=
    CV.crossKeep_liftBlock_iff hn hG hT q _ w
  have e2 : w = ua₀ ↔ z = r176l_ua hu := by
    rw [← hua₀]; exact (CV.liftVisit_injective hn hG hT q).eq_iff.symm
  have e3 : w = (geoPositiveLift hn hG hT q).twin ua₀ ↔ z = r176l_uc hu := by
    rw [← r176l_twin_ua hu hac, ← hua₀, ← CV.liftVisit_twin]
    exact (CV.liftVisit_injective hn hG hT q).eq_iff.symm
  have e4 : w ∈ ({ua₀, (geoPositiveLift hn hG hT q).record.pair ua₀} : Finset (geoPositiveLift hn hG hT q).record.M) ↔
      w = ua₀ ∨ w = (geoPositiveLift hn hG hT q).twin ua₀ := by
    rw [Finset.mem_insert, Finset.mem_singleton, (geoPositiveLift hn hG hT q).record_pair_apply]
  show _ ↔ (geoPositiveLift hn hG hT q).record.crossingOf w ∈ _ ∪ _
  rw [Set.mem_union, Set.mem_singleton_iff, (geoPositiveLift hn hG hT q).record.crossingOf_eq_iff, e1,
    mem_geoCarrierCrossings]
  show _ ↔ _ ∨ w ∈ ({ua₀, (geoPositiveLift hn hG hT q).record.pair ua₀} : Finset _)
  rw [e4, e2, e3]
  change (cycBetween (geoMarkKey hG.cg (Sum.inr (visitOn v c (s176_mem_right hv)))) (geoMarkKey hG.cg (Sum.inr z))
      (geoMarkKey hG.cg (Sum.inr (visitOn v b (s176_mem_left hv)))) ∧
    cycBetween (geoMarkKey hG.cg (Sum.inr (visitOn v c (s176_mem_right hv)))) (geoMarkKey hG.cg (Sum.inr (visitTwin z)))
      (geoMarkKey hG.cg (Sum.inr (visitOn v b (s176_mem_left hv))))) ↔ _
  have hzj : Sum.inr z ≠ (Sum.inr (visitOn j a (s176_mem_left hj)) : Mark P) := fun e =>
    hzT (by rw [show z.1 = j from congrArg (fun w : Visit P => w.1) (Sum.inr.inj e)]; exact hjT)
  have hzj' : Sum.inr (visitTwin z) ≠ (Sum.inr (visitOn j a (s176_mem_left hj)) : Mark P) := fun e => by
    have := congrArg (fun w : Visit P => w.1) (Sum.inr.inj e)
    simp only [visitTwin_crossing] at this
    exact hzT (by rw [show z.1 = j from this]; exact hjT)
  by_cases hzv : z.1 = v
  · have hz' : z = visitOn v b (s176_mem_left hv) ∨ z = visitOn v c (s176_mem_right hv) := by
      rcases visit_eq_or_twin (visitOn v b (s176_mem_left hv)) z hzv with e | e
      · exact Or.inl e
      · rw [r176l_twin_vb hv hbc] at e; exact Or.inr e
    constructor
    · rintro ⟨h1, -⟩
      exfalso
      rcases hz' with e | e
      · rw [e] at h1; exact not_cycBetween_self_mid _ _ h1
      · rw [e] at h1; exact not_cycBetween_self_left _ _ h1
    · rintro (⟨hnot, -⟩ | e | e)
      · exact absurd (by rw [hzv]; exact r176l_v_mem_Sf T u v) hnot
      · exact (r176l_u_ne_v hab hbc hu hv ((congrArg (fun w : Visit P => w.1) e).symm.trans hzv)).elim
      · exact (r176l_u_ne_v hab hbc hu hv ((congrArg (fun w : Visit P => w.1) e).symm.trans hzv)).elim
  · rw [r176o_between_vc_vb_iff_L2 hG hT q hab hac hbc hj hu hv hjT huq hvq hρa hρb hρc hSf (Sum.inr z) hzq hzj,
      r176o_between_vc_vb_iff_L2 hG hT q hab hac hbc hj hu hv hjT huq hvq hρa hρb hρc hSf
        (Sum.inr (visitTwin z)) hzq' hzj']
    by_cases hzu : z.1 = u
    · have hz' : z = r176l_ua hu ∨ z = r176l_uc hu := by
        rcases visit_eq_or_twin (r176l_ua hu) z hzu with e | e
        · exact Or.inl e
        · rw [r176l_twin_ua hu hac] at e; exact Or.inr e
      constructor
      · intro _
        rcases hz' with e | e
        · exact Or.inr (Or.inl e)
        · exact Or.inr (Or.inr e)
      · intro _
        rcases hz' with e | e
        · refine ⟨Or.inl (by rw [e]), Or.inr ?_⟩
          rw [e, r176l_twin_ua hu hac]
        · refine ⟨Or.inr (by rw [e]), Or.inl ?_⟩
          rw [e, r176l_twin_uc hu hac]
    · have hnot : z.1 ∉ r176l_Sf T u v := by
        intro hmem
        rcases r176l_mem_ins.mp hmem with e | hmem
        · exact hzv e
        · rcases r176l_mem_ins.mp hmem with e | hmem
          · exact hzu e
          · exact hzT hmem
      have hzuc : Sum.inr z ≠ (Sum.inr (r176l_uc hu) : Mark P) := fun e =>
        hzu (congrArg (fun w : Visit P => w.1) (Sum.inr.inj e))
      have hzuc' : Sum.inr (visitTwin z) ≠ (Sum.inr (r176l_uc hu) : Mark P) := fun e => by
        have := congrArg (fun w : Visit P => w.1) (Sum.inr.inj e)
        simp only [visitTwin_crossing] at this
        exact hzu this
      constructor
      · rintro ⟨h1 | h1, h2 | h2⟩
        · left
          refine ⟨hnot, fun w' hw' => ?_⟩
          rcases visit_eq_or_twin z w' hw' with e | e
          · rw [e]; exact h1
          · rw [e]; exact h2
        · exact absurd h2 hzuc'
        · exact absurd h1 hzuc
        · exact absurd h1 hzuc
      · rintro (⟨-, hall⟩ | e | e)
        · exact ⟨Or.inl (hall z rfl), Or.inl (hall _ rfl)⟩
        · exact absurd (congrArg (fun w : Visit P => w.1) e) hzu
        · exact absurd (congrArg (fun w : Visit P => w.1) e) hzu

/-- the mirrored kink is not a chord of `Λ₂` -/
theorem r176o_r_not' (ua₀ : (geoPositiveLift hn hG hT q).Γ.Visit) (hua₀ : CV.liftVisit hn hG hT q ua₀ = r176l_ua hu) :
    (geoPositiveLift hn hG hT q).record.crossingOf ua₀ ∉
      CV.liftBlock hn hG hT q (geoCarrierCrossings hG.cg (r176l_Sf T u v) (r176l_L2 hG.cg T v hu)) := by
  intro h
  have h' := (CV.crossKeep_liftBlock_iff hn hG hT q _ ua₀).mp h
  rw [hua₀] at h'
  exact ((mem_geoCarrierCrossings _ _ _ _).mp h').1 (r176l_u_mem_Sf T u v)

/-- **the mirrored kink is a curl of `ρ|B`**: the `B`-restricted successor of the `(u,a)`-occurrence is the
`(u,c)`-occurrence -/
theorem r176o_r_curl' (v₀ : (geoPositiveLift hn hG hT q).Γ.Visit)
    (hv₀ : CV.liftVisit hn hG hT q v₀ = visitOn v b (s176_mem_left hv))
    (ua₀ : (geoPositiveLift hn hG hT q).Γ.Visit) (hua₀ : CV.liftVisit hn hG hT q ua₀ = r176l_ua hu) :
    ∃ (w : (geoPositiveLift hn hG hT q).record.M)
      (hw : (geoPositiveLift hn hG hT q).record.CrossKeep (r176s_KB (geoPositiveLift hn hG hT q).record v₀) w),
      (geoPositiveLift hn hG hT q).record.crossingOf w = (geoPositiveLift hn hG hT q).record.crossingOf ua₀ ∧
      (((geoPositiveLift hn hG hT q).record.restrictCrossings (r176s_KB (geoPositiveLift hn hG hT q).record v₀)).succ
        ⟨w, hw⟩).1 = (geoPositiveLift hn hG hT q).record.pair w := by
  obtain ⟨k, hk0, hkN, hk⟩ := r176o_exists_k hG hT q hab hac hbc hj hu hv hjT huq hvq hρa hρb hρc hSf
  have h1 : (geoPositiveLift hn hG hT q).record.componentCount = 1 :=
    CV.record_componentCount_one _ (geoPositiveLift_componentCount hn hG hT q)
  have hKB := r176o_KB_eq' hn hG hT q hab hac hbc hj hu hv hjT huq hvq hρa hρb hρc hSf v₀ hv₀ ua₀ hua₀
  have hwa : (geoPositiveLift hn hG hT q).record.CrossKeep (r176s_KB (geoPositiveLift hn hG hT q).record v₀) ua₀ := by
    show (geoPositiveLift hn hG hT q).record.crossingOf ua₀ ∈ _
    rw [hKB]; exact Or.inr rfl
  have hwc : (geoPositiveLift hn hG hT q).record.CrossKeep (r176s_KB (geoPositiveLift hn hG hT q).record v₀)
      ((geoPositiveLift hn hG hT q).twin ua₀) := by
    show (geoPositiveLift hn hG hT q).record.crossingOf ((geoPositiveLift hn hG hT q).twin ua₀) ∈ _
    rw [hKB, ← (geoPositiveLift hn hG hT q).record_pair_apply, (geoPositiveLift hn hG hT q).record.crossingOf_pair]
    exact Or.inr rfl
  refine ⟨ua₀, hwa, rfl, ?_⟩
  rw [(geoPositiveLift hn hG hT q).record_pair_apply,
    (geoPositiveLift hn hG hT q).record.restrictCrossings_succ_val_eq_iff h1 _ hwa]
  refine ⟨hwc, (geoPositiveLift hn hG hT q).twin_ne ua₀, fun x hx hxne => ?_⟩
  by_contra hlt
  push Not at hlt
  have harc : (geoPositiveLift hn hG hT q).record.ArcBetween ua₀ x ((geoPositiveLift hn hG hT q).twin ua₀) :=
    ⟨((geoPositiveLift hn hG hT q).record.steps_pos_iff h1 _ _).mpr hxne.symm, hlt⟩
  rw [CV.arcBetween_iff_key, CV.liftVisit_twin, hua₀, r176l_twin_ua hu hac] at harc
  have hx0 : (geoPositiveLift hn hG hT q).record.CrossKeep
      (r176s_KA (geoPositiveLift hn hG hT q).record ((geoPositiveLift hn hG hT q).twin v₀)) x := hx
  have hx' := (r176s_crossKeep_KA_iff_key hn hG hT q ((geoPositiveLift hn hG hT q).twin v₀) x).mp hx0
  rw [CV.liftVisit_twin, hv₀, r176l_twin_vb hv hbc, r176l_twin_vc hv hbc] at hx'
  set z := CV.liftVisit hn hG hT q x with hz
  have hzq : geoOwner hG.cg T (Sum.inr z) = q := CV.liftVisit_owner hn hG hT q x
  have hzT : z.1 ∉ T := ((mem_geoCarrierCrossings _ _ _ _).mp (CV.liftVisit_mem hn hG hT q x)).1
  have hown := r176l_owner_uc hG.cg q hu huq
  obtain ⟨i, hiN, hi⟩ := r176o_exists_pow hG.cg hT q hown hzq
  have hb := r176o_k_bounds hG hT q hab hac hbc hj hu hv hjT huq hvq hρa hρb hρc hSf hk0 hkN hk
  have hN := CV.markList_length_pos hG.cg q
  have hgt : k < i := by
    have := r176o_between_ua_uc_iff hG hT q hab hac hbc hj hu hv hjT huq hvq hρa hρb hρc hSf hk0 hkN hk hiN
    rw [hi] at this
    exact this.mp harc
  have hlt2 : i < k + 2 := by
    have := r176o_cyc_iff hG.cg hT q hown (i := (geoComponentMarkList hG.cg T q).length - 1) (j := i) (l := k + 2)
      (by omega) hiN (by omega)
    rw [r176o_pow_vc hG hT q hab hac hbc hj hu hv hjT huq hvq hρa hρb hρc hSf,
      r176o_pow_vb hG hT q hab hac hbc hj hu hv hjT huq hvq hρa hρb hρc hSf hk0 hkN hk, hi] at this
    have h' := this.mp hx'.1
    omega
  have hik : i = k + 1 := by omega
  subst hik
  rw [r176o_pow_ja hG hT q hab hac hbc hj hu hv hjT huq hvq hρa hρb hρc hSf hk0 hkN hk] at hi
  exact hzT (by rw [show z.1 = j from congrArg (fun w : Visit P => w.1) (Sum.inr.inj hi.symm)]; exact hjT)

end R176O_Mirror

/-! ## §O4. The event level: `r176_outer_carriers_L` at `y = lift u'`, and the corrected form -/

section R176O_Event

variable {E : CV.Event n} {e f g : ZMod n} {δ : ℝ}

/-- **The outer carriers at `y = lift u'`** — the body of `r176_outer_carriers_L` restricted to the first
disjunct of `_hy`.  `v₀` is the occurrence of `y` over the visit `(u', c)`; then `A = ((u',c) → (u',a))` carries
the clean child `Λ₂ = owner_{Sf} (u', a)` and `B = ((u',a) → (u',c))` carries `(v',b), Λ₁, (v',c)`, the kink being
`r = lift v'` (R176_SMOOTH_REPORT §2.2, with `v₀ := u'_c`). -/
theorem r176o_outer_carriers_L_u :
  ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (E : CV.Event n) (e f g : ZMod n) (δ : ℝ)
    (hL : LocalizationData E e f g δ) (hR : AV_EventRadius E δ) (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
    (t t' : E.Parameter) (ht : Punctured E δ t) (ht' : Punctured E δ t') (hop : OppositeSides E t t')
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    (hef' : IsCrossing (E.curve t) {e, f}) (heg' : IsCrossing (E.curve t) {e, g})
    (hfg' : IsCrossing (E.curve t) {f, g}) (_hcomp : CompleteLocal (geomAt E t ht.1) hef' heg' hfg')
    (Q : Finset (Crossing (E.curve t))) (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
    (hfull : FullAvail (geomAt E t ht.1) e f g Q) (j : Crossing (E.curve t))
    (hj : j.val ∈ triangleSupports e f g) (q : GeoComponent (geomAt E t ht.1) (Q ∪ {j}))
    (a b c : ZMod n) (_hab : a ≠ b) (_hac : a ≠ c) (_hbc : b ≠ c)
    (_habc : ({a, b, c} : Finset (ZMod n)) = {e, f, g}) (u v : Crossing (E.curve t))
    (hjab : j.val = {a, b}) (huac : u.val = {a, c}) (hvbc : v.val = {b, c})
    (_hu : u.val ∈ triangleSupports e f g) (_hv : v.val ∈ triangleSupports e f g)
    (_hju : j ≠ u) (_hjv : j ≠ v) (_huv : u ≠ v)
    (hu' : crossingTransport hs u ∈ geoCarrierCrossings (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j}))
      (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q))
    (_hv' : crossingTransport hs v ∈ geoCarrierCrossings (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j}))
      (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q))
    (_hlt_a : visitParameter (visitOn (crossingTransport hs u) a (s176_mem_left huac)) <
      visitParameter (visitOn (crossingTransport hs j) a (s176_mem_left hjab)))
    (_hSf : (r176l_Sf (transportSupport hs (Q ∪ {j})) (crossingTransport hs u) (crossingTransport hs v)) ∈ CV.Ind (geomAt E t' ht'.1))
    (y : (CV.carrierDiagram hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj)
      (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)).Γ.Crossing)
    (_hy : y = est_liftCrossing hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj) _ hu'),
    Nonempty (r176_OuterDataL hn hL hR hef heg hfg ht ht' hop hs hQ hfull hj q huac hvbc y) := by
  intro n _ hn E e f g δ hL hR hef heg hfg t t' ht ht' hop hs hef' heg' hfg' hcomp Q hQ hfull j hj q a b c hab hac
    hbc habc u v hjab huac hvbc hu hv hju hjv huv hu' hv' hlt_a _hSf y hy
  have hS' := est_S'_ind hL ht ht' hop hs hQ hfull hj
  have hs' : ∀ s, IsCrossing (E.curve t') s ↔ IsCrossing (E.curve t) s := fun s => (hs s).symm
  have hop' : OppositeSides E t' t := by
    unfold OppositeSides at hop ⊢; linarith [mul_comm t.val t'.val]
  have hXL : ExactTriangleVisitOrders (E.curve t') (E.curve t) a b c hs' :=
    gu2_exact_of_eq hs' habc.symm (hL.gauss_words t' t ht' ht hop' hs')
  have hGL : CarrierGeometry (E.curve t') := r176s_cgL hn ht'
  have hT : GeoIndependent (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j})) :=
    CV.geoIndependent_of_mem_Ind _ hS'
  have hjT : crossingTransport hs j ∈ transportSupport hs (Q ∪ {j}) :=
    (mem_transportSupport_iff hs _ j).mpr (Finset.mem_union_right _ (Finset.mem_singleton_self j))
  have hρa : geoMarkSuccessor (geomAt E t' ht'.1) (Sum.inr (r176l_ua (u := crossingTransport hs u) huac)) =
      Sum.inr (visitOn (crossingTransport hs j) a (s176_mem_left hjab)) :=
    gu1_markSuccessor_eq_of_adjacent hn _ rfl hlt_a
      (fun w hw => (s176_nb_a hs' hab hac hbc hXL (j := crossingTransport hs j) (u := crossingTransport hs u)
        hjab huac w hw).1)
  have hlt_b := (s176_cyclic hn hGL hs' hT (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)
    hab hac hbc hXL (j := crossingTransport hs j)
    (u := crossingTransport hs u) (v := crossingTransport hs v) hjab huac hvbc hjT hu' hv').mp hlt_a
  have hρb : geoMarkSuccessor (geomAt E t' ht'.1) (Sum.inr (visitOn (crossingTransport hs j) b (s176_mem_right hjab))) =
      Sum.inr (visitOn (crossingTransport hs v) b (s176_mem_left hvbc)) :=
    gu1_markSuccessor_eq_of_adjacent hn _ rfl hlt_b
      (fun w hw => (s176_nb_b hs' hab hac hbc hXL (j := crossingTransport hs j) (v := crossingTransport hs v)
        hjab hvbc w hw).1)
  have hnb_c := fun (w : Visit (E.curve t')) (hw : w.2.val = c) =>
    s176_nb_c hs' hab hac hbc hXL (u := crossingTransport hs u) (v := crossingTransport hs v) huac hvbc w hw
  have hSf : GeoIndependent (geomAt E t' ht'.1)
      (r176l_Sf (transportSupport hs (Q ∪ {j})) (crossingTransport hs u) (crossingTransport hs v)) :=
    r176l_Sf_indep_event hL ht ht' hop hs hcomp hQ hfull hj hu hv hju hjv huv
  have hρc := (r176l_lt_c_of_indep hn (geomAt E t' ht'.1) (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)
    hab hac hbc hjab huac hvbc hjT hu' hv' hρa hρb hSf hnb_c).2
  obtain ⟨v₀, hv₀⟩ := CV.liftVisit_surjective hn hGL hT (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)
    (w := r176l_uc (u := crossingTransport hs u) huac) hu'
  obtain ⟨vb₀, hvb₀⟩ := CV.liftVisit_surjective hn hGL hT (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)
    (w := visitOn (crossingTransport hs v) b (s176_mem_left hvbc)) hv'
  refine ⟨⟨v₀, ?_, ?_, ?_,
    r176o_KA_eq hn hGL hT _ hab hac hbc hjab huac hvbc hjT hu' hv' hρa hρb hρc hSf v₀ hv₀,
    (geoPositiveLift hn hGL hT (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)).record.crossingOf vb₀,
    r176o_KB_eq hn hGL hT _ hab hac hbc hjab huac hvbc hjT hu' hv' hρa hρb hρc hSf v₀ hv₀ vb₀ hvb₀,
    r176o_r_not hn hGL hT _ hab hac hbc hjab huac hvbc hjT hu' hv' hρa hρb hρc hSf vb₀ hvb₀,
    r176o_r_curl hn hGL hT _ hab hac hbc hjab huac hvbc hjT hu' hv' hρa hρb hρc hSf v₀ hv₀ vb₀ hvb₀⟩⟩
  · rw [hy]
    apply (Equiv.eq_symm_apply _).mpr
    apply Subtype.ext
    show CV.parentCrossing hn hGL hT _ v₀ = crossingTransport hs u
    rw [← CV.liftVisit_fst, hv₀]
    rfl
  · intro x hx
    rw [mem_geoCarrierCrossings] at hx ⊢
    exact ⟨fun h => hx.1 (r176l_subset_Sf _ _ _ h),
      fun w hw => r176l_sub_L2 (geomAt E t' ht'.1) _ huac hu' hSf _ (hx.2 w hw)⟩
  · intro x hx
    rw [mem_geoCarrierCrossings] at hx ⊢
    exact ⟨fun h => hx.1 (r176l_subset_Sf _ _ _ h),
      fun w hw => r176l_sub_L1 (geomAt E t' ht'.1) _ hvbc hv' hSf _ (hx.2 w hw)⟩

/-- **The mirrored outer-carrier data at `y = lift v'`** (the CORRECTED shape for the second disjunct of `_hy`
in `r176_outer_carriers_L`, rule (3)): `r176_OuterDataL` with the roles of the two children exchanged —
`Λ_A := Λ₁ = owner_{Sf} (v', c)` is the CLEAN child and `Λ_B := Λ₂ = owner_{Sf} (u', a)` the KINKED one, the kink
being `r = lift u'` (with `v₀ := v'_b`: `A = ((v',b) → (v',c))` carries `Λ₁`, `B = ((v',c) → (v',b))` carries
`(u',c), Λ₂, (u',a)`).  `subA`, `subB` are unchanged (both inclusions hold). -/
structure r176o_OuterDataL' (hn : 3 ≤ n) (hL : LocalizationData E e f g δ) (hR : AV_EventRadius E δ)
    (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g) {t t' : E.Parameter} (ht : Punctured E δ t)
    (ht' : Punctured E δ t') (hop : OppositeSides E t t')
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    {Q : Finset (Crossing (E.curve t))} (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
    (hfull : FullAvail (geomAt E t ht.1) e f g Q) {j : Crossing (E.curve t)}
    (hj : j.val ∈ triangleSupports e f g) (q : GeoComponent (geomAt E t ht.1) (Q ∪ {j}))
    {a b c : ZMod n} {u v : Crossing (E.curve t)} (huac : u.val = {a, c}) (hvbc : v.val = {b, c})
    (y : (CV.carrierDiagram hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj)
      (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)).Γ.Crossing) where
  /-- the occurrence of `y` from which the arc `A` carries the clean component -/
  v₀ : (CV.carrierDiagram hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj)
      (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)).Γ.Visit
  hv₀ : v₀.1 = y
  /-- the retained set of the clean child `Λ₂ = owner_{Sf} (u', a)` lies in that of `q₀'` -/
  subA : geoCarrierCrossings (geomAt E t' ht'.1) _ (r176l_L2 (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j})) (crossingTransport hs v)
        (u := crossingTransport hs u) huac) ⊆
    geoCarrierCrossings (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j})) (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)
  /-- the retained set of the kinked child `Λ₁ = owner_{Sf} (v', c)` lies in that of `q₀'` -/
  subB : geoCarrierCrossings (geomAt E t' ht'.1) _ (r176l_L1 (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j})) (crossingTransport hs u)
        (v := crossingTransport hs v) hvbc) ⊆
    geoCarrierCrossings (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j})) (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)
  /-- the crossings on the arc `A = (v₀ → τ v₀)` are the chords of `Λ₁` (the CLEAN child at `y = lift v'`) -/
  KA_eq : r176s_KA (CV.carrierDiagram hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj)
      (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)).record v₀ =
    CV.liftBlock hn (r176s_cgL hn ht') (CV.geoIndependent_of_mem_Ind _ (est_S'_ind hL ht ht' hop hs hQ hfull hj))
      (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q) (geoCarrierCrossings (geomAt E t' ht'.1) _ (r176l_L1 (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j})) (crossingTransport hs u)
        (v := crossingTransport hs v) hvbc))
  /-- the kink (the lift of the third triangle crossing) -/
  r : (CV.carrierDiagram hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj)
      (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)).record.Crossing
  /-- the crossings on the arc `B = (τ v₀ → v₀)` are the chords of `Λ₂` plus the kink `lift u'` -/
  KB_eq : r176s_KB (CV.carrierDiagram hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj)
      (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)).record v₀ =
    CV.liftBlock hn (r176s_cgL hn ht') (CV.geoIndependent_of_mem_Ind _ (est_S'_ind hL ht ht' hop hs hQ hfull hj))
      (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q) (geoCarrierCrossings (geomAt E t' ht'.1) _ (r176l_L2 (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j})) (crossingTransport hs v)
        (u := crossingTransport hs u) huac)) ∪ {r}
  r_not : r ∉ CV.liftBlock hn (r176s_cgL hn ht') (CV.geoIndependent_of_mem_Ind _ (est_S'_ind hL ht ht' hop hs hQ hfull hj))
      (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q) (geoCarrierCrossings (geomAt E t' ht'.1) _ (r176l_L2 (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j})) (crossingTransport hs v)
        (u := crossingTransport hs u) huac))
  /-- the kink's two occurrences are consecutive in `ρ|B` -/
  r_curl : ∃ (w : (CV.carrierDiagram hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj)
      (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)).record.M) (hw : (CV.carrierDiagram hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj)
      (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)).record.CrossKeep (r176s_KB (CV.carrierDiagram hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj)
      (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)).record v₀) w),
    (CV.carrierDiagram hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj)
      (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)).record.crossingOf w = r ∧
    (((CV.carrierDiagram hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj)
      (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)).record.restrictCrossings (r176s_KB (CV.carrierDiagram hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj)
      (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)).record v₀)).succ ⟨w, hw⟩).1 = (CV.carrierDiagram hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj)
      (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)).record.pair w

/-- the second disjunct of `r176_outer_carriers_L`, in its corrected (mirrored) shape — OPEN (see the report) -/
def r176o_outer_carriers_L_v : Prop :=
  ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (E : CV.Event n) (e f g : ZMod n) (δ : ℝ)
    (hL : LocalizationData E e f g δ) (hR : AV_EventRadius E δ) (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
    (t t' : E.Parameter) (ht : Punctured E δ t) (ht' : Punctured E δ t') (hop : OppositeSides E t t')
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    (hef' : IsCrossing (E.curve t) {e, f}) (heg' : IsCrossing (E.curve t) {e, g})
    (hfg' : IsCrossing (E.curve t) {f, g}) (_hcomp : CompleteLocal (geomAt E t ht.1) hef' heg' hfg')
    (Q : Finset (Crossing (E.curve t))) (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
    (hfull : FullAvail (geomAt E t ht.1) e f g Q) (j : Crossing (E.curve t))
    (hj : j.val ∈ triangleSupports e f g) (q : GeoComponent (geomAt E t ht.1) (Q ∪ {j}))
    (a b c : ZMod n) (_hab : a ≠ b) (_hac : a ≠ c) (_hbc : b ≠ c)
    (_habc : ({a, b, c} : Finset (ZMod n)) = {e, f, g}) (u v : Crossing (E.curve t))
    (hjab : j.val = {a, b}) (huac : u.val = {a, c}) (hvbc : v.val = {b, c})
    (_hu : u.val ∈ triangleSupports e f g) (_hv : v.val ∈ triangleSupports e f g)
    (_hju : j ≠ u) (_hjv : j ≠ v) (_huv : u ≠ v)
    (_hu' : crossingTransport hs u ∈ geoCarrierCrossings (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j}))
      (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q))
    (hv' : crossingTransport hs v ∈ geoCarrierCrossings (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j}))
      (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q))
    (_hlt_a : visitParameter (visitOn (crossingTransport hs u) a (s176_mem_left huac)) <
      visitParameter (visitOn (crossingTransport hs j) a (s176_mem_left hjab)))
    (_hSf : (r176l_Sf (transportSupport hs (Q ∪ {j})) (crossingTransport hs u) (crossingTransport hs v)) ∈ CV.Ind (geomAt E t' ht'.1))
    (y : (CV.carrierDiagram hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj)
      (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)).Γ.Crossing)
    (_hy : y = est_liftCrossing hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj) _ hv'),
    Nonempty (r176o_OuterDataL' hn hL hR hef heg hfg ht ht' hop hs hQ hfull hj q huac hvbc y)

/-- **The corrected form of `r176_outer_carriers_L`**: the frozen Prop asserts `r176_OuterDataL` (Λ₁ kinked,
Λ₂ clean) for BOTH lifts, which is false at `y = lift v'` whenever a child has a retained crossing (there the
arc from `v'_c` to `v'_b` carries both occurrences of `lift u'`, a chord labelled in `S_full`, so it can never be
`liftBlock (retained Λ₂)`; with `v₀ = v'_b`, `K_A = liftBlock (retained Λ₁)`).  The correct statement splits by the lift. -/
def r176o_outer_carriers_L_corrected : Prop :=
  ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (E : CV.Event n) (e f g : ZMod n) (δ : ℝ)
    (hL : LocalizationData E e f g δ) (hR : AV_EventRadius E δ) (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
    (t t' : E.Parameter) (ht : Punctured E δ t) (ht' : Punctured E δ t') (hop : OppositeSides E t t')
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    (hef' : IsCrossing (E.curve t) {e, f}) (heg' : IsCrossing (E.curve t) {e, g})
    (hfg' : IsCrossing (E.curve t) {f, g}) (_hcomp : CompleteLocal (geomAt E t ht.1) hef' heg' hfg')
    (Q : Finset (Crossing (E.curve t))) (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
    (hfull : FullAvail (geomAt E t ht.1) e f g Q) (j : Crossing (E.curve t))
    (hj : j.val ∈ triangleSupports e f g) (q : GeoComponent (geomAt E t ht.1) (Q ∪ {j}))
    (a b c : ZMod n) (_hab : a ≠ b) (_hac : a ≠ c) (_hbc : b ≠ c)
    (_habc : ({a, b, c} : Finset (ZMod n)) = {e, f, g}) (u v : Crossing (E.curve t))
    (hjab : j.val = {a, b}) (huac : u.val = {a, c}) (hvbc : v.val = {b, c})
    (_hu : u.val ∈ triangleSupports e f g) (_hv : v.val ∈ triangleSupports e f g)
    (_hju : j ≠ u) (_hjv : j ≠ v) (_huv : u ≠ v)
    (hu' : crossingTransport hs u ∈ geoCarrierCrossings (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j}))
      (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q))
    (hv' : crossingTransport hs v ∈ geoCarrierCrossings (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j}))
      (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q))
    (_hlt_a : visitParameter (visitOn (crossingTransport hs u) a (s176_mem_left huac)) <
      visitParameter (visitOn (crossingTransport hs j) a (s176_mem_left hjab)))
    (_hSf : (r176l_Sf (transportSupport hs (Q ∪ {j})) (crossingTransport hs u) (crossingTransport hs v)) ∈ CV.Ind (geomAt E t' ht'.1))
    (y : (CV.carrierDiagram hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj)
      (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)).Γ.Crossing),
    (y = est_liftCrossing hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj) _ hu' →
      Nonempty (r176_OuterDataL hn hL hR hef heg hfg ht ht' hop hs hQ hfull hj q huac hvbc y)) ∧
    (y = est_liftCrossing hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj) _ hv' →
      Nonempty (r176o_OuterDataL' hn hL hR hef heg hfg ht ht' hop hs hQ hfull hj q huac hvbc y))

/-- the corrected Prop from the `u'`-half (proved here) and the `v'`-half (open) -/
theorem r176o_outer_carriers_L_corrected_of_v (hvhalf : r176o_outer_carriers_L_v) :
    r176o_outer_carriers_L_corrected := by
  intro n _ hn E e f g δ hL hR hef heg hfg t t' ht ht' hop hs hef' heg' hfg' hcomp Q hQ hfull j hj q a b c hab hac
    hbc habc u v hjab huac hvbc hu hv hju hjv huv hu' hv' hlt_a hSf y
  exact ⟨fun hy => r176o_outer_carriers_L_u n hn E e f g δ hL hR hef heg hfg t t' ht ht' hop hs hef' heg' hfg' hcomp
      Q hQ hfull j hj q a b c hab hac hbc habc u v hjab huac hvbc hu hv hju hjv huv hu' hv' hlt_a hSf y hy,
    fun hy => hvhalf n hn E e f g δ hL hR hef heg hfg t t' ht ht' hop hs hef' heg' hfg' hcomp
      Q hQ hfull j hj q a b c hab hac hbc habc u v hjab huac hvbc hu hv hju hjv huv hu' hv' hlt_a hSf y hy⟩

/-- **The mirrored half, PROVED**: `r176o_outer_carriers_L_v` (the corrected statement at `y = lift v'`). -/
theorem r176o_outer_carriers_L_v_proof : r176o_outer_carriers_L_v := by
  intro n _ hn E e f g δ hL hR hef heg hfg t t' ht ht' hop hs hef' heg' hfg' hcomp Q hQ hfull j hj q a b c hab hac
    hbc habc u v hjab huac hvbc hu hv hju hjv huv hu' hv' hlt_a _hSf y hy
  have hS' := est_S'_ind hL ht ht' hop hs hQ hfull hj
  have hs' : ∀ s, IsCrossing (E.curve t') s ↔ IsCrossing (E.curve t) s := fun s => (hs s).symm
  have hop' : OppositeSides E t' t := by
    unfold OppositeSides at hop ⊢; linarith [mul_comm t.val t'.val]
  have hXL : ExactTriangleVisitOrders (E.curve t') (E.curve t) a b c hs' :=
    gu2_exact_of_eq hs' habc.symm (hL.gauss_words t' t ht' ht hop' hs')
  have hGL : CarrierGeometry (E.curve t') := r176s_cgL hn ht'
  have hT : GeoIndependent (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j})) :=
    CV.geoIndependent_of_mem_Ind _ hS'
  have hjT : crossingTransport hs j ∈ transportSupport hs (Q ∪ {j}) :=
    (mem_transportSupport_iff hs _ j).mpr (Finset.mem_union_right _ (Finset.mem_singleton_self j))
  have hρa : geoMarkSuccessor (geomAt E t' ht'.1) (Sum.inr (r176l_ua (u := crossingTransport hs u) huac)) =
      Sum.inr (visitOn (crossingTransport hs j) a (s176_mem_left hjab)) :=
    gu1_markSuccessor_eq_of_adjacent hn _ rfl hlt_a
      (fun w hw => (s176_nb_a hs' hab hac hbc hXL (j := crossingTransport hs j) (u := crossingTransport hs u)
        hjab huac w hw).1)
  have hlt_b := (s176_cyclic hn hGL hs' hT (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)
    hab hac hbc hXL (j := crossingTransport hs j)
    (u := crossingTransport hs u) (v := crossingTransport hs v) hjab huac hvbc hjT hu' hv').mp hlt_a
  have hρb : geoMarkSuccessor (geomAt E t' ht'.1) (Sum.inr (visitOn (crossingTransport hs j) b (s176_mem_right hjab))) =
      Sum.inr (visitOn (crossingTransport hs v) b (s176_mem_left hvbc)) :=
    gu1_markSuccessor_eq_of_adjacent hn _ rfl hlt_b
      (fun w hw => (s176_nb_b hs' hab hac hbc hXL (j := crossingTransport hs j) (v := crossingTransport hs v)
        hjab hvbc w hw).1)
  have hnb_c := fun (w : Visit (E.curve t')) (hw : w.2.val = c) =>
    s176_nb_c hs' hab hac hbc hXL (u := crossingTransport hs u) (v := crossingTransport hs v) huac hvbc w hw
  have hSf : GeoIndependent (geomAt E t' ht'.1)
      (r176l_Sf (transportSupport hs (Q ∪ {j})) (crossingTransport hs u) (crossingTransport hs v)) :=
    r176l_Sf_indep_event hL ht ht' hop hs hcomp hQ hfull hj hu hv hju hjv huv
  have hρc := (r176l_lt_c_of_indep hn (geomAt E t' ht'.1) (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)
    hab hac hbc hjab huac hvbc hjT hu' hv' hρa hρb hSf hnb_c).2
  obtain ⟨v₀, hv₀⟩ := CV.liftVisit_surjective hn hGL hT (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)
    (w := visitOn (crossingTransport hs v) b (s176_mem_left hvbc)) hv'
  obtain ⟨ua₀, hua₀⟩ := CV.liftVisit_surjective hn hGL hT (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)
    (w := r176l_ua (u := crossingTransport hs u) huac) hu'
  refine ⟨⟨v₀, ?_, ?_, ?_,
    r176o_KA_eq' hn hGL hT _ hab hac hbc hjab huac hvbc hjT hu' hv' hρa hρb hρc hSf v₀ hv₀,
    (geoPositiveLift hn hGL hT (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)).record.crossingOf ua₀,
    r176o_KB_eq' hn hGL hT _ hab hac hbc hjab huac hvbc hjT hu' hv' hρa hρb hρc hSf v₀ hv₀ ua₀ hua₀,
    r176o_r_not' hn hGL hT _ hab hac hbc hjab huac hvbc hjT hu' hv' hρa hρb hρc hSf ua₀ hua₀,
    r176o_r_curl' hn hGL hT _ hab hac hbc hjab huac hvbc hjT hu' hv' hρa hρb hρc hSf v₀ hv₀ ua₀ hua₀⟩⟩
  · rw [hy]
    apply (Equiv.eq_symm_apply _).mpr
    apply Subtype.ext
    show CV.parentCrossing hn hGL hT _ v₀ = crossingTransport hs v
    rw [← CV.liftVisit_fst, hv₀]
    rfl
  · intro x hx
    rw [mem_geoCarrierCrossings] at hx ⊢
    exact ⟨fun h => hx.1 (r176l_subset_Sf _ _ _ h),
      fun w hw => r176l_sub_L2 (geomAt E t' ht'.1) _ huac hu' hSf _ (hx.2 w hw)⟩
  · intro x hx
    rw [mem_geoCarrierCrossings] at hx ⊢
    exact ⟨fun h => hx.1 (r176l_subset_Sf _ _ _ h),
      fun w hw => r176l_sub_L1 (geomAt E t' ht'.1) _ hvbc hv' hSf _ (hx.2 w hw)⟩

/-- **The corrected outer-carrier Prop of row 176, PROVED** (both lifts). -/
theorem r176o_outer_carriers_L_corrected_proof : r176o_outer_carriers_L_corrected :=
  r176o_outer_carriers_L_corrected_of_v r176o_outer_carriers_L_v_proof

end R176O_Event

/-! ## §O6. The mirrored connector for the composition (what `r176_portDataRest_case1` needs in the `Or.inr` case) -/

section R176O_Connector

variable {E : CV.Event n} {e f g : ZMod n} {δ : ℝ}

/-- **The (14)-bridge for the mirrored data — BLACK BOX (OPEN, MIXED unit)**: `r176_mixed_bridge` word for word with
`O : r176o_OuterDataL'` (the same `i`/`j` = `B`-class of `v₀` / `A`-class of `τ v₀`; at `y = lift v'` the `B`-class
is the kinked `Λ₂`-side and the `A`-class the clean `Λ₁`-side). -/
def r176o_mixed_bridge' : Prop :=
  ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (E : CV.Event n) (e f g : ZMod n) (δ : ℝ)
    (hL : LocalizationData E e f g δ) (hR : AV_EventRadius E δ) (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
    (t t' : E.Parameter) (ht : Punctured E δ t) (ht' : Punctured E δ t') (hop : OppositeSides E t t')
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    (hef' : IsCrossing (E.curve t) {e, f}) (heg' : IsCrossing (E.curve t) {e, g})
    (hfg' : IsCrossing (E.curve t) {f, g}) (_hcomp : CompleteLocal (geomAt E t ht.1) hef' heg' hfg')
    (Q : Finset (Crossing (E.curve t))) (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
    (hfull : FullAvail (geomAt E t ht.1) e f g Q) (j : Crossing (E.curve t))
    (hj : j.val ∈ triangleSupports e f g) (q : GeoComponent (geomAt E t ht.1) (Q ∪ {j}))
    (a b c : ZMod n) (_hab : a ≠ b) (_hac : a ≠ c) (_hbc : b ≠ c)
    (_habc : ({a, b, c} : Finset (ZMod n)) = {e, f, g}) (u v : Crossing (E.curve t))
    (hjab : j.val = {a, b}) (huac : u.val = {a, c}) (hvbc : v.val = {b, c})
    (_hu : u.val ∈ triangleSupports e f g) (_hv : v.val ∈ triangleSupports e f g)
    (_hju : j ≠ u) (_hjv : j ≠ v) (_huv : u ≠ v)
    (hu' : crossingTransport hs u ∈ geoCarrierCrossings (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j}))
      (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q))
    (hv' : crossingTransport hs v ∈ geoCarrierCrossings (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j}))
      (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q))
    (_hlt_a : visitParameter (visitOn (crossingTransport hs u) a (s176_mem_left huac)) <
      visitParameter (visitOn (crossingTransport hs j) a (s176_mem_left hjab)))
    (_hSf : (r176l_Sf (transportSupport hs (Q ∪ {j})) (crossingTransport hs u) (crossingTransport hs v)) ∈ CV.Ind (geomAt E t' ht'.1))
    (y : (CV.carrierDiagram hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj)
      (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)).Γ.Crossing)
    (_hy : y = est_liftCrossing hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj) _ hu' ∨
      y = est_liftCrossing hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj) _ hv')
    (O : r176o_OuterDataL' hn hL hR hef heg hfg ht ht' hop hs hQ hfull hj q huac hvbc y),
    mixedSignSum (r176s_DA (CV.carrierDiagram hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj)
      (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)) y) (r176s_DA_i (CV.carrierDiagram hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj)
      (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)) y O.v₀ O.hv₀) (r176s_DA_j (CV.carrierDiagram hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj)
      (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)) y O.v₀ O.hv₀) =
      ((r176l_mixedSet (genericAt E t' ht'.1).crossingGeometry (transportSupport hs (Q ∪ {j})) (r176l_Sf (transportSupport hs (Q ∪ {j})) (crossingTransport hs u) (crossingTransport hs v)) (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)
        (r176l_L1 (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j})) (crossingTransport hs u)
        (v := crossingTransport hs v) hvbc) (r176l_L2 (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j})) (crossingTransport hs v)
        (u := crossingTransport hs u) huac)).card : ℤ)

/-- **The mirrored connector**: `r176_smoothData_of` for `O : r176o_OuterDataL'` — the SmoothData of `(Λ₁, Λ₂)` with
`i := r176s_DA_j` (the `A`-class, clean `Λ₁`) and `j := r176s_DA_i` (the `B`-class, kinked `Λ₂`), `mixed` by
`mixedSignSum_comm`.  This is the only piece the composition needs besides the case split on `hy`. -/
def r176o_smoothData_of' (hcurl : r176s_curl_removal) (hn : 3 ≤ n) (hL : LocalizationData E e f g δ)
    (hR : AV_EventRadius E δ) (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g) {t t' : E.Parameter}
    (ht : Punctured E δ t) (ht' : Punctured E δ t') (hop : OppositeSides E t t')
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    {Q : Finset (Crossing (E.curve t))} (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
    (hfull : FullAvail (geomAt E t ht.1) e f g Q) {j : Crossing (E.curve t)}
    (hj : j.val ∈ triangleSupports e f g) (q : GeoComponent (geomAt E t ht.1) (Q ∪ {j}))
    {a b c : ZMod n} {u v : Crossing (E.curve t)} (huac : u.val = {a, c}) (hvbc : v.val = {b, c})
    (y : (CV.carrierDiagram hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj)
      (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)).Γ.Crossing)
    (O : r176o_OuterDataL' hn hL hR hef heg hfg ht ht' hop hs hQ hfull hj q huac hvbc y)
    (hSf : (r176l_Sf (transportSupport hs (Q ∪ {j})) (crossingTransport hs u) (crossingTransport hs v)) ∈ CV.Ind (geomAt E t' ht'.1))
    (hmixed : mixedSignSum (r176s_DA (CV.carrierDiagram hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj)
      (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)) y) (r176s_DA_i (CV.carrierDiagram hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj)
      (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)) y O.v₀ O.hv₀) (r176s_DA_j (CV.carrierDiagram hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj)
      (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)) y O.v₀ O.hv₀) =
      ((r176l_mixedSet (genericAt E t' ht'.1).crossingGeometry (transportSupport hs (Q ∪ {j})) (r176l_Sf (transportSupport hs (Q ∪ {j})) (crossingTransport hs u) (crossingTransport hs v)) (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)
        (r176l_L1 (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j})) (crossingTransport hs u)
        (v := crossingTransport hs v) hvbc) (r176l_L2 (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j})) (crossingTransport hs v)
        (u := crossingTransport hs u) huac)).card : ℤ)) :
    r176l_SmoothData hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj) (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q) y (r176l_Sf (transportSupport hs (Q ∪ {j})) (crossingTransport hs u) (crossingTransport hs v)) hSf
      (r176l_L1 (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j})) (crossingTransport hs u)
        (v := crossingTransport hs v) hvbc) (r176l_L2 (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j})) (crossingTransport hs v)
        (u := crossingTransport hs u) huac) := by
  have hD1 : (CV.carrierDiagram hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj)
      (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)).componentCount = 1 := geoPositiveLift_componentCount hn _ _ _
  refine
    { DA := r176s_DA _ y, smooth := r176s_DA_smooth _ y, two := r176s_DA_componentCount _ y hD1,
      i := r176s_DA_j _ y O.v₀ O.hv₀, j := r176s_DA_i _ y O.v₀ O.hv₀, ij := (r176s_DA_ij _ y hD1 O.v₀ O.hv₀).symm,
      poly₁ := ?_, poly₂ := ?_, mixed := (mixedSignSum_comm _ _ _).trans hmixed }
  · -- (9) the clean child `Λ₁` (mirrored)
    rw [GT_groupedPoly_eq_homfly]
    exact r176s_homfly_of_liftBlock hn (r176s_cgL hn ht')
      (CV.geoIndependent_of_mem_Ind _ (est_S'_ind hL ht ht' hop hs hQ hfull hj))
      (CV.geoIndependent_of_mem_Ind _ hSf) _ (r176l_L1 (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j})) (crossingTransport hs u)
        (v := crossingTransport hs v) hvbc) O.subB _ _ O.KA_eq
      ⟨r176s_knotRestrictIso_j _ _ hD1 O.v₀ O.hv₀⟩
  · -- (9a) the kinked child `Λ₂` (mirrored): the kink is `lift u'`: the record-level R-I removes the kink
    rw [GT_groupedPoly_eq_homfly]
    exact r176s_homfly_of_liftBlock_curl hcurl hn (r176s_cgL hn ht')
      (CV.geoIndependent_of_mem_Ind _ (est_S'_ind hL ht ht' hop hs hQ hfull hj))
      (CV.geoIndependent_of_mem_Ind _ hSf) _ (r176l_L2 (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j})) (crossingTransport hs v)
        (u := crossingTransport hs u) huac) O.subA _ _ O.r O.KB_eq O.r_not O.r_curl
      ⟨r176s_knotRestrictIso_i _ _ hD1 O.v₀ O.hv₀⟩


end R176O_Connector

/-! ## §O7. The composition replayed on the corrected outer-carrier statement (byte-identical bodies except the
`hy`-split in `_case1`): the row from `r176s_curl_removal`, `r176_mixed_bridge` and `r176o_mixed_bridge'` alone -/

section R176O_Chain

variable {E : CV.Event n} {e f g : ZMod n} {δ : ℝ}

/-- `r176_portDataRest_case1` with `hout` discharged: `r176o_outer_carriers_L_u` in the `Or.inl` case,
`r176o_outer_carriers_L_v_proof` + `r176o_smoothData_of'` in the `Or.inr` case. -/
theorem r176o_portDataRest_case1 (hcurl : r176s_curl_removal) (hmixed' : r176o_mixed_bridge')
    (hmixed : r176_mixed_bridge) (hn : 3 ≤ n)
    (hL : LocalizationData E e f g δ) (hR : AV_EventRadius E δ) (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
    {t t' : E.Parameter} (ht : Punctured E δ t) (ht' : Punctured E δ t') (hop : OppositeSides E t t')
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    {hef' : IsCrossing (E.curve t) {e, f}} {heg' : IsCrossing (E.curve t) {e, g}}
    {hfg' : IsCrossing (E.curve t) {f, g}} (hcomp : CompleteLocal (geomAt E t ht.1) hef' heg' hfg')
    {Q : Finset (Crossing (E.curve t))} (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
    (hfull : FullAvail (geomAt E t ht.1) e f g Q) {j : Crossing (E.curve t)}
    (hj : j.val ∈ triangleSupports e f g) (q : GeoComponent (geomAt E t ht.1) (Q ∪ {j}))
    (hwind : CV.wind (geomAt E t ht.1) (Q ∪ {j}) ≠ 0)
    {a b c : ZMod n} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (habc : ({a, b, c} : Finset (ZMod n)) = {e, f, g}) {u v : Crossing (E.curve t)}
    (hjab : j.val = {a, b}) (huac : u.val = {a, c}) (hvbc : v.val = {b, c})
    (hu : u.val ∈ triangleSupports e f g) (hv : v.val ∈ triangleSupports e f g)
    (hju : j ≠ u) (hjv : j ≠ v) (huv : u ≠ v)
    (hu' : crossingTransport hs u ∈ geoCarrierCrossings (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j}))
      (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q))
    (hv' : crossingTransport hs v ∈ geoCarrierCrossings (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j}))
      (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q))
    (hlt_a : visitParameter (visitOn (crossingTransport hs u) a (s176_mem_left huac)) <
      visitParameter (visitOn (crossingTransport hs j) a (s176_mem_left hjab)))
    (y : (CV.carrierDiagram hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj)
      (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)).Γ.Crossing)
    (hy : y = est_liftCrossing hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj) _ hu' ∨
      y = est_liftCrossing hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj) _ hv') :
    Nonempty (s176_PortDataRest hn (genericAt E t ht.1) (genericAt E t' ht'.1) (est_S_ind ht.1 hQ hfull hj)
      (est_S'_ind hL ht ht' hop hs hQ hfull hj) q
      (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q) y) := by
  have hS := est_S_ind ht.1 hQ hfull hj
  have hS' := est_S'_ind hL ht ht' hop hs hQ hfull hj
  -- the `L` side
  have hs' : ∀ s, IsCrossing (E.curve t') s ↔ IsCrossing (E.curve t) s := fun s => (hs s).symm
  have hop' : OppositeSides E t' t := by
    unfold OppositeSides at hop ⊢; linarith [mul_comm t.val t'.val]
  have hXL : ExactTriangleVisitOrders (E.curve t') (E.curve t) a b c hs' :=
    gu2_exact_of_eq hs' habc.symm (hL.gauss_words t' t ht' ht hop' hs')
  have hGL : CarrierGeometry (E.curve t') :=
    CarrierGeometry.ofDiagrammatic ((genericAt E t' ht'.1).diagrammatic hn)
  have hT : GeoIndependent (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j})) :=
    CV.geoIndependent_of_mem_Ind _ hS'
  have hjT : crossingTransport hs j ∈ transportSupport hs (Q ∪ {j}) :=
    (mem_transportSupport_iff hs _ j).mpr (Finset.mem_union_right _ (Finset.mem_singleton_self j))
  -- the successor facts of case 1
  have hρa : geoMarkSuccessor (geomAt E t' ht'.1) (Sum.inr (r176l_ua (u := crossingTransport hs u) huac)) =
      Sum.inr (visitOn (crossingTransport hs j) a (s176_mem_left hjab)) :=
    gu1_markSuccessor_eq_of_adjacent hn _ rfl hlt_a
      (fun w hw => (s176_nb_a hs' hab hac hbc hXL (j := crossingTransport hs j) (u := crossingTransport hs u)
        hjab huac w hw).1)
  have hlt_b := (s176_cyclic hn hGL hs' hT (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q) hab hac hbc hXL (j := crossingTransport hs j)
    (u := crossingTransport hs u) (v := crossingTransport hs v) hjab huac hvbc hjT hu' hv').mp hlt_a
  have hρb : geoMarkSuccessor (geomAt E t' ht'.1) (Sum.inr (visitOn (crossingTransport hs j) b (s176_mem_right hjab))) =
      Sum.inr (visitOn (crossingTransport hs v) b (s176_mem_left hvbc)) :=
    gu1_markSuccessor_eq_of_adjacent hn _ rfl hlt_b
      (fun w hw => (s176_nb_b hs' hab hac hbc hXL (j := crossingTransport hs j) (v := crossingTransport hs v)
        hjab hvbc w hw).1)
  have hnb_c := fun (w : Visit (E.curve t')) (hw : w.2.val = c) =>
    s176_nb_c hs' hab hac hbc hXL (u := crossingTransport hs u) (v := crossingTransport hs v) huac hvbc w hw
  -- the full support
  have hSf : GeoIndependent (geomAt E t' ht'.1)
      (r176l_Sf (transportSupport hs (Q ∪ {j})) (crossingTransport hs u) (crossingTransport hs v)) :=
    r176l_Sf_indep_event hL ht ht' hop hs hcomp hQ hfull hj hu hv hju hjv huv
  have hSf' : r176l_Sf (transportSupport hs (Q ∪ {j})) (crossingTransport hs u) (crossingTransport hs v) ∈
      CV.Ind (geomAt E t' ht'.1) := (CV.mem_Ind_iff _ _).mpr hSf
  -- uniformity, carried
  obtain ⟨σ, hσ, huniH⟩ := (CV.wind_ne_zero_imp (geomAt E t ht.1) (Q ∪ {j}) hwind).2 q
  have huni := r176l_uniform_transport hn hL hR hef heg hfg ht ht' hop hs hQ hfull hj q huniH
  -- regularity
  have hreg : ∀ (S : Finset (Crossing (E.curve t'))) (r : GeoComponent (geomAt E t' ht'.1) S),
      GeoIndependent (geomAt E t' ht'.1) S → CV.Regular (geoCornerPolygon (geomAt E t' ht'.1) S r) :=
    fun S r hind => CV.carrierPolygon_cvRegular hn (genericAt E t' ht'.1) ((CV.mem_Ind_iff _ _).mpr hind) r
  -- the ledger
  have LD := r176l_ledgerData_case1 hn (geomAt E t' ht'.1) hT (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q) hab hac hbc
    (j := crossingTransport hs j) (u := crossingTransport hs u) (v := crossingTransport hs v) hjab huac hvbc hjT
    hu' hv' hρa hρb hSf hlt_a hlt_b hnb_c hσ huni hreg
  -- the smoothing data: SMOOTH's constructions on the outer carriers, the curl removal, the mixed bridge
  have hD : Nonempty (r176l_SmoothData hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj) (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q) y (r176l_Sf (transportSupport hs (Q ∪ {j})) (crossingTransport hs u) (crossingTransport hs v)) hSf'
      (r176l_L1 (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j})) (crossingTransport hs u)
        (v := crossingTransport hs v) hvbc) (r176l_L2 (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j})) (crossingTransport hs v)
        (u := crossingTransport hs u) huac)) := by
    rcases hy with hy | hy
    · obtain ⟨O⟩ := r176o_outer_carriers_L_u n hn E e f g δ hL hR hef heg hfg t t' ht ht' hop hs hef' heg' hfg' hcomp Q hQ hfull j hj q
        a b c hab hac hbc habc u v hjab huac hvbc hu hv hju hjv huv hu' hv' hlt_a hSf' y hy
      exact ⟨r176_smoothData_of hcurl hn hL hR hef heg hfg ht ht' hop hs hQ hfull hj q huac hvbc y O hSf'
        (hmixed n hn E e f g δ hL hR hef heg hfg t t' ht ht' hop hs hef' heg' hfg' hcomp Q hQ hfull j hj q
          a b c hab hac hbc habc u v hjab huac hvbc hu hv hju hjv huv hu' hv' hlt_a hSf' y (Or.inl hy) O)⟩
    · obtain ⟨O⟩ := r176o_outer_carriers_L_v_proof n hn E e f g δ hL hR hef heg hfg t t' ht ht' hop hs hef' heg' hfg' hcomp Q hQ hfull j hj q
        a b c hab hac hbc habc u v hjab huac hvbc hu hv hju hjv huv hu' hv' hlt_a hSf' y hy
      exact ⟨r176o_smoothData_of' hcurl hn hL hR hef heg hfg ht ht' hop hs hQ hfull hj q huac hvbc y O hSf'
        (hmixed' n hn E e f g δ hL hR hef heg hfg t t' ht ht' hop hs hef' heg' hfg' hcomp Q hQ hfull j hj q
          a b c hab hac hbc habc u v hjab huac hvbc hu hv hju hjv huv hu' hv' hlt_a hSf' y (Or.inr hy) O)⟩
  obtain ⟨D⟩ := hD
  -- (14): the writhe shift (7) and the `L`-side count
  have hcu : c ∈ u.val := s176_mem_right huac
  have hcv : c ∈ v.val := s176_mem_right hvbc
  have hcj : c ∉ j.val := by
    rw [hjab, Finset.mem_insert, Finset.mem_singleton]
    rintro (h | h)
    · exact hac h.symm
    · exact hbc h.symm
  have howner_u : geoOwner (geomAt E t ht.1) (Q ∪ {j}) (Sum.inr (visitOn u c hcu)) = q :=
    (est_retained_u_iff hL hR hef heg hfg ht ht' hop hs hcomp hQ hfull hj hu hju hcu hcj q).mp hu'
  have h7 := est_groupedWrithe_affected hL hR hef heg hfg ht ht' hop hs hcomp hQ hfull hj hu hv hju hjv huv hcu hcv
    q howner_u
  have hcard := LD.card
  have hw : CV.groupedWrithe (genericAt E t ht.1) q =
      CV.groupedWrithe (genericAt E t' ht'.1)
          (r176l_L1 (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j})) (crossingTransport hs u) (v := crossingTransport hs v) hvbc) +
        CV.groupedWrithe (genericAt E t' ht'.1)
          (r176l_L2 (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j})) (crossingTransport hs v) (u := crossingTransport hs u) huac) +
        ((r176l_mixedSet (genericAt E t' ht'.1).crossingGeometry (transportSupport hs (Q ∪ {j}))
          (r176l_Sf (transportSupport hs (Q ∪ {j})) (crossingTransport hs u) (crossingTransport hs v))
          (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)
          (r176l_L1 (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j})) (crossingTransport hs u) (v := crossingTransport hs v) hvbc)
          (r176l_L2 (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j})) (crossingTransport hs v) (u := crossingTransport hs u) huac)).card : ℤ) := by
    rw [CV.groupedWrithe_eq_card_geoCarrierCrossings _ hS'] at h7
    rw [CV.groupedWrithe_eq_card_geoCarrierCrossings _ hSf', CV.groupedWrithe_eq_card_geoCarrierCrossings _ hSf']
    have hc' : ((geoCarrierCrossings (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j})) (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)).card : ℤ) =
        _ := congrArg (fun m : ℕ => (m : ℤ)) hcard
    push_cast at hc'
    linarith
  -- (13)
  have hrot := r176l_rot_ledger hn (genericAt E t ht.1) (genericAt E t' ht'.1) hS hS' q (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)
    (hSf := hSf') hσ (GT_carrierR_eq hn (genericAt E t ht.1) (genericAt E t' ht'.1) (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) hS hS' q) LD.rot_add
    LD.shape₁ LD.shape₂
  -- (12)
  have halt := r176l_alt_of_shape hn (genericAt E t' ht'.1) (hSf := hSf') hσ LD.shape₁ LD.shape₂
  exact ⟨r176l_portDataRest_of hn (genericAt E t ht.1) (genericAt E t' ht'.1) hS hS' q (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q) y D hw
    hrot halt.1 halt.2⟩

/-- `r176_portDataRest_labelled` replayed (byte-identical body). -/
theorem r176o_portDataRest_labelled (hcurl : r176s_curl_removal) (hmixed' : r176o_mixed_bridge')
    (hmixed : r176_mixed_bridge) (hn : 3 ≤ n)
    (hL : LocalizationData E e f g δ) (hR : AV_EventRadius E δ) (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
    {t t' : E.Parameter} (ht : Punctured E δ t) (ht' : Punctured E δ t') (hop : OppositeSides E t t')
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    {hef' : IsCrossing (E.curve t) {e, f}} {heg' : IsCrossing (E.curve t) {e, g}}
    {hfg' : IsCrossing (E.curve t) {f, g}} (hcomp : CompleteLocal (geomAt E t ht.1) hef' heg' hfg')
    {Q : Finset (Crossing (E.curve t))} (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
    (hfull : FullAvail (geomAt E t ht.1) e f g Q) {j : Crossing (E.curve t)}
    (hj : j.val ∈ triangleSupports e f g) (q : GeoComponent (geomAt E t ht.1) (Q ∪ {j}))
    (hwind : CV.wind (geomAt E t ht.1) (Q ∪ {j}) ≠ 0)
    {u : Crossing (E.curve t)} (hu : u.val ∈ triangleSupports e f g) (hju : j ≠ u)
    (hu' : crossingTransport hs u ∈ geoCarrierCrossings (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j}))
      (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q))
    {a b c : ZMod n} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (habc : ({a, b, c} : Finset (ZMod n)) = {e, f, g})
    (hjab : j.val = {a, b}) (huac : u.val = {a, c}) {v : Crossing (E.curve t)} (hvbc : v.val = {b, c})
    (hv : v.val ∈ triangleSupports e f g) (hjv : j ≠ v) (huv : u ≠ v) :
    Nonempty (s176_PortDataRest hn (genericAt E t ht.1) (genericAt E t' ht'.1) (est_S_ind ht.1 hQ hfull hj)
      (est_S'_ind hL ht ht' hop hs hQ hfull hj) q
      (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)
      (est_liftCrossing hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj) _ hu')) := by
  obtain ⟨hv', -, -⟩ := s176_event_site_core hn hL hR hef heg hfg ht ht' hop hs hcomp hQ hfull hj q hu hju hu'
    hab hac hbc habc hjab huac hvbc hv hjv huv
  have hS' := est_S'_ind hL ht ht' hop hs hQ hfull hj
  have hs' : ∀ s, IsCrossing (E.curve t') s ↔ IsCrossing (E.curve t) s := fun s => (hs s).symm
  have hop' : OppositeSides E t' t := by
    unfold OppositeSides at hop ⊢; linarith [mul_comm t.val t'.val]
  have hXL : ExactTriangleVisitOrders (E.curve t') (E.curve t) a b c hs' :=
    gu2_exact_of_eq hs' habc.symm (hL.gauss_words t' t ht' ht hop' hs')
  have hGL : CarrierGeometry (E.curve t') :=
    CarrierGeometry.ofDiagrammatic ((genericAt E t' ht'.1).diagrammatic hn)
  have hT : GeoIndependent (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j})) :=
    CV.geoIndependent_of_mem_Ind _ hS'
  have hjT : crossingTransport hs j ∈ transportSupport hs (Q ∪ {j}) :=
    (mem_transportSupport_iff hs _ j).mpr (Finset.mem_union_right _ (Finset.mem_singleton_self j))
  have hju' : crossingTransport hs u ≠ crossingTransport hs j := (crossingTransport hs).injective.ne hju.symm
  have hjv' : crossingTransport hs v ≠ crossingTransport hs j := (crossingTransport hs).injective.ne hjv.symm
  have hcyc := s176_cyclic hn hGL hs' hT (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)
    hab hac hbc hXL (j := crossingTransport hs j) (u := crossingTransport hs u) (v := crossingTransport hs v)
    hjab huac hvbc hjT hu' hv'
  rcases lt_or_gt_of_ne (r176l_param_ne (geomAt E t' ht'.1) hju' (s176_mem_left huac) (s176_mem_left hjab)) with
    hlt | hgt
  · exact r176o_portDataRest_case1 hcurl hmixed' hmixed hn hL hR hef heg hfg ht ht' hop hs hcomp hQ hfull hj q hwind hab hac hbc
      habc hjab huac hvbc hu hv hju hjv huv hu' hv' hlt _ (Or.inl rfl)
  · -- case 2: relabel `(b, a, c), (j, v, u)`
    have hnlt : ¬ visitParameter (visitOn (crossingTransport hs j) b (s176_mem_right hjab)) <
        visitParameter (visitOn (crossingTransport hs v) b (s176_mem_left hvbc)) :=
      fun h => lt_asymm hgt (hcyc.mpr h)
    have hlt_b : visitParameter (visitOn (crossingTransport hs v) b (s176_mem_left hvbc)) <
        visitParameter (visitOn (crossingTransport hs j) b (s176_mem_right hjab)) :=
      lt_of_le_of_ne (not_lt.mp hnlt) (r176l_param_ne (geomAt E t' ht'.1) hjv' (s176_mem_left hvbc) (s176_mem_right hjab))
    have habc' : ({b, a, c} : Finset (ZMod n)) = {e, f, g} := (Finset.insert_comm b a {c}).trans habc
    exact r176o_portDataRest_case1 hcurl hmixed' hmixed hn hL hR hef heg hfg ht ht' hop hs hcomp hQ hfull hj q hwind
      (a := b) (b := a) (c := c) hab.symm hbc hac habc' (u := v) (v := u) (s176_pair_comm' hjab) hvbc huac hv hu hjv hju
      huv.symm hv' hu' hlt_b _ (Or.inr rfl)

/-- `r176_portDataRest_of_uniform` replayed (byte-identical body). -/
theorem r176o_portDataRest_of_uniform (hcurl : r176s_curl_removal) (hmixed' : r176o_mixed_bridge')
    (hmixed : r176_mixed_bridge) (hn : 3 ≤ n)
    (hL : LocalizationData E e f g δ) (hR : AV_EventRadius E δ) (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
    {t t' : E.Parameter} (ht : Punctured E δ t) (ht' : Punctured E δ t') (hop : OppositeSides E t t')
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    (hef' : IsCrossing (E.curve t) {e, f}) (heg' : IsCrossing (E.curve t) {e, g})
    (hfg' : IsCrossing (E.curve t) {f, g}) (hcomp : CompleteLocal (geomAt E t ht.1) hef' heg' hfg')
    {Q : Finset (Crossing (E.curve t))} (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
    (hfull : FullAvail (geomAt E t ht.1) e f g Q) {j : Crossing (E.curve t)}
    (hj : j.val ∈ triangleSupports e f g) (q : GeoComponent (geomAt E t ht.1) (Q ∪ {j}))
    (hwind : CV.wind (geomAt E t ht.1) (Q ∪ {j}) ≠ 0)
    {u : Crossing (E.curve t)} (hu : u.val ∈ triangleSupports e f g) (hju : j ≠ u)
    (hu' : crossingTransport hs u ∈ geoCarrierCrossings (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j}))
      (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)) :
    Nonempty (s176_PortDataRest hn (genericAt E t ht.1) (genericAt E t' ht'.1) (est_S_ind ht.1 hQ hfull hj)
      (est_S'_ind hL ht ht' hop hs hQ hfull hj) q
      (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)
      (est_liftCrossing hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj) _ hu')) := by
  have h1 : (xPair hef').val ∈ triangleSupports e f g := (P1.mem_triangleSupports _).mpr (Or.inl rfl)
  have h2 : (xPair heg').val ∈ triangleSupports e f g := (P1.mem_triangleSupports _).mpr (Or.inr (Or.inl rfl))
  have h3 : (xPair hfg').val ∈ triangleSupports e f g := (P1.mem_triangleSupports _).mpr (Or.inr (Or.inr rfl))
  have n12 := P1.xPair_ef_ne_eg hef' heg' hfg'
  have n13 := P1.xPair_ef_ne_fg hef' heg' hfg'
  have n23 := P1.xPair_eg_ne_fg hef' heg' hfg'
  have key : ∀ {a b c : ZMod n} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
      (habc : ({a, b, c} : Finset (ZMod n)) = {e, f, g})
      (hjab : j.val = {a, b}) (huac : u.val = {a, c}) {v : Crossing (E.curve t)} (hvbc : v.val = {b, c})
      (hv : v.val ∈ triangleSupports e f g) (hjv : j ≠ v) (huv : u ≠ v),
      Nonempty (s176_PortDataRest hn (genericAt E t ht.1) (genericAt E t' ht'.1) (est_S_ind ht.1 hQ hfull hj)
        (est_S'_ind hL ht ht' hop hs hQ hfull hj) q
        (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)
        (est_liftCrossing hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj) _ hu')) :=
    fun {a b c} hab hac hbc habc hjab huac {v} hvbc hv hjv huv =>
      r176o_portDataRest_labelled hcurl hmixed' hmixed hn hL hR hef heg hfg ht ht' hop hs hcomp hQ hfull hj q hwind hu hju hu'
        hab hac hbc habc hjab huac (v := v) hvbc hv hjv huv
  have p_feg : ({f, e, g} : Finset (ZMod n)) = {e, f, g} := Finset.insert_comm f e {g}
  have p_egf : ({e, g, f} : Finset (ZMod n)) = {e, f, g} := congrArg (insert e) (Finset.pair_comm g f)
  have p_gef : ({g, e, f} : Finset (ZMod n)) = {e, f, g} :=
    (Finset.insert_comm g e {f}).trans (congrArg (insert e) (Finset.pair_comm g f))
  have p_fge : ({f, g, e} : Finset (ZMod n)) = {e, f, g} :=
    (congrArg (insert f) (Finset.pair_comm g e)).trans (Finset.insert_comm f e {g})
  have p_gfe : ({g, f, e} : Finset (ZMod n)) = {e, f, g} :=
    ((congrArg (insert g) (Finset.pair_comm f e)).trans (Finset.insert_comm g e {f})).trans
      (congrArg (insert e) (Finset.pair_comm g f))
  rcases GT_tri_cases t hef' heg' hfg' j hj with rfl | rfl | rfl <;>
    rcases GT_tri_cases t hef' heg' hfg' u hu with rfl | rfl | rfl
  · exact absurd rfl hju
  · exact key hef heg hfg rfl rfl rfl (v := xPair hfg') rfl h3 n13 n23
  · exact key hef.symm hfg heg p_feg (Finset.pair_comm e f) rfl (v := xPair heg') rfl h2 n12 n23.symm
  · exact key heg hef hfg.symm p_egf rfl rfl (v := xPair hfg') (Finset.pair_comm f g) h3 n23 n13
  · exact absurd rfl hju
  · exact key heg.symm hfg.symm hef p_gef (Finset.pair_comm e g) (Finset.pair_comm f g) (v := xPair hef') rfl h1
      n12.symm n13.symm
  · exact key hfg hef.symm heg.symm p_fge rfl (Finset.pair_comm e f) (v := xPair heg') (Finset.pair_comm e g) h2
      n23.symm n12
  · exact key hfg.symm heg.symm hef.symm p_gfe (Finset.pair_comm f g) (Finset.pair_comm e g) (v := xPair hef')
      (Finset.pair_comm e f) h1 n13.symm n12.symm
  · exact absurd rfl hju

/-- `r176_est_port_relation_weak_uniform_of_curl_outer_mixed` replayed (byte-identical body). -/
theorem r176o_est_port_relation_weak_uniform_of_curl_mixed (hcurl : r176s_curl_removal)
    (hmixed' : r176o_mixed_bridge') (hmixed : r176_mixed_bridge) : r176l_est_port_relation_weak_uniform := by
  intro n _ hn E e f g δ hL hR hef heg hfg t t' ht ht' hop hs hef' heg' hfg' hcomp Q hQ hfull j hj q hwind hex
  obtain ⟨u, hu, hju, hu'⟩ := hex
  obtain ⟨R⟩ := r176o_portDataRest_of_uniform hcurl hmixed' hmixed hn hL hR hef heg hfg ht ht' hop hs hef' heg' hfg'
    hcomp hQ hfull hj q hwind hu hju.symm hu'
  refine ⟨u, hu, hju, hu', ⟨s176_PortDataWeak.mk' _ _ _ _ _ _ _ _ ?_ R⟩⟩
  exact r176h_est_port_weak hn hL hR hef heg hfg ht ht' hop hs hef' heg' hfg' hcomp hQ hfull hj q hu hju.symm hu'

/-- **The row on the two remaining open Props** (`r176s_curl_removal`, the two (14)-bridges); no outer-carrier
hypothesis remains. -/
theorem r176o_extreme_transport_of_curl_mixed (hcurl : r176s_curl_removal) (hmixed' : r176o_mixed_bridge')
    (hmixed : r176_mixed_bridge) : RowShape @ExtremeTransportData :=
  r176_est_ledger_weak_uniform CV.carrierSlotFloor
    (r176o_est_port_relation_weak_uniform_of_curl_mixed hcurl hmixed' hmixed)

end R176O_Chain

end

end RProof


/-! # R176W2_MIXED — row 176, the MIXED unit: the (14)-bridge `r176_mixed_bridge` PROVED

APPENDED by the R176 MIXED prover, 2026-09-15, to `R176_Port_draft.lean` (byte-identical above this line).
Companion report: `R176W2_MIXED_REPORT.md`.  All names carry the prefix `r176m_`; nothing above is modified.

Route (a COUNT, not a bijection with `r176l_mixedSet` — `r176_OuterDataL` does not say which parent crossing the
kink `r` labels, so no crossing-by-crossing identification of the mixed set is available from it):
* §M1 on a one-circle record `ρ` with an occurrence `x`, the chords other than `{x, τ x}` split into `K_A`
  (both occurrences on `A`), `K_B` (both on `B`) and the rest; `K_A ∩ K_B = ∅`, `{x, τ x} ∉ K_A ∪ K_B`
  (`r176m_card_rest`: `#rest + #K_A + #K_B + 1 = #chords`).
* §M2 on `D_A = r176s_DA D x` with the record identification `ι = r176s_DA_iso`: the chord of a crossing `w` of
  `D_A` is `κ w := crossingOf (ι.Φ (overVisit w)).1` (`r176m_κ`); `κ` is a bijection of the crossings of `D_A`
  with the chords `≠ {v, τ v}` (`r176m_κ_injective`, `r176m_κ_surj`), and `w` is mixed between the two
  components `i = r176s_DA_i`, `j = r176s_DA_j` iff `κ w ∉ K_A ∪ K_B` (`r176m_isMixed_iff`, through
  `r176s_smooth_comp_eq_pair_iff` / `r176s_smooth_comp_eq_self_iff` and the two-component fact); every crossing
  of `D_A` keeps its sign (`r176m_DA_sign`), so `mixedSignSum D_A i j = #rest` (`r176m_mixedSignSum_eq`, via
  `r176l_mixedSignSum_eq_card`).
* §M3 on the positive lift: `#(liftBlock W) = #W` for `W` inside the retained set (`r176m_card_liftBlock`), the
  chords are labelled bijectively by the retained crossings (`r176m_card_record_crossing`); with `KA_eq`,
  `KB_eq`, `r_not` of the outer data: `mixedSignSum + #Λ₁ + #Λ₂ + 2 = #retained q'` (`r176m_bridge_count`).
* §M4 the event level: `r176l_children_case1` + `r176l_card_retained` + `r176l_selectedPart_card` give
  `#retained q' = #Λ₁ + #Λ₂ + #mixedSet + 2`; hence `r176m_mixed_bridge_proof : r176_mixed_bridge`. -/

namespace RProof

open SM SM.GeoCarrier SM.Carrier SM.Link

noncomputable section

/-! ## §M1. The chords of a one-circle record off a self crossing: `K_A`, `K_B` and the rest -/

section R176M_Rec

variable (ρ : Record) (h1 : ρ.componentCount = 1) (x : ρ.M)

/-- the chord of `x` is not in `K_A` -/
theorem r176m_crossingOf_not_mem_KA : ρ.crossingOf x ∉ r176s_KA ρ x := by
  intro h
  have hA : r176s_ArcA ρ x x := h x (ρ.mem_crossingOf x)
  exact r176s_arcA_ne_self ρ x hA rfl

/-- the chord of `x` is not in `K_B` -/
theorem r176m_crossingOf_not_mem_KB : ρ.crossingOf x ∉ r176s_KB ρ x := by
  intro h
  have hmem : ρ.pair x ∈ (ρ.crossingOf x).1 := Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have hA : r176s_ArcA ρ (ρ.pair x) (ρ.pair x) := h (ρ.pair x) hmem
  exact r176s_arcA_ne_self ρ (ρ.pair x) hA rfl

include h1 in
/-- `K_A` and `K_B` are disjoint (an occurrence on both arcs would put the two components of the smoothing
together) -/
theorem r176m_KA_KB_disjoint {c : ρ.Crossing} (hA : c ∈ r176s_KA ρ x) (hB : c ∈ r176s_KB ρ x) : False := by
  obtain ⟨v, hv⟩ := ρ.crossingOf_surjective c
  have hvmem : v ∈ c.1 := by rw [← hv]; exact ρ.mem_crossingOf v
  have hAv : r176s_ArcA ρ x v := hA v hvmem
  have hBv : r176s_ArcA ρ (ρ.pair x) v := hB v hvmem
  have hBv' : ρ.ArcBetween (ρ.pair x) v x := (r176s_pair_arcA_iff ρ x v).mp hBv
  have hkeep : ρ.SmoothKeep x v := r176s_arcA_smoothKeep ρ x hAv
  have e1 := (r176s_smooth_comp_eq_pair_iff ρ h1 x ⟨v, hkeep⟩).mpr hAv
  have e2 := (r176s_smooth_comp_eq_self_iff ρ h1 x ⟨v, hkeep⟩).mpr hBv'
  exact ρ.smooth_comps_ne_of_self x (r176s_isSelfCrossing ρ h1 x) (e2.symm.trans e1)

open scoped Classical in
include h1 in
/-- **the chord count**: the chords other than `{x, τ x}` are `K_A`, `K_B` and the rest -/
theorem r176m_card_rest :
    (Finset.univ.filter (fun c : ρ.Crossing =>
        c ≠ ρ.crossingOf x ∧ c ∉ r176s_KA ρ x ∧ c ∉ r176s_KB ρ x)).card +
      (Finset.univ.filter (fun c : ρ.Crossing => c ∈ r176s_KA ρ x)).card +
      (Finset.univ.filter (fun c : ρ.Crossing => c ∈ r176s_KB ρ x)).card + 1 =
      Fintype.card ρ.Crossing := by
  have key : ∀ c : ρ.Crossing,
      ((if (c ≠ ρ.crossingOf x ∧ c ∉ r176s_KA ρ x ∧ c ∉ r176s_KB ρ x) then 1 else 0) +
        (if c ∈ r176s_KA ρ x then 1 else 0) + (if c ∈ r176s_KB ρ x then 1 else 0) +
        (if c = ρ.crossingOf x then 1 else 0) : ℕ) = 1 := by
    intro c
    by_cases hc : c = ρ.crossingOf x
    · subst hc
      rw [ite_eq_right (fun h => h.1 rfl), ite_eq_right (r176m_crossingOf_not_mem_KA ρ x),
        ite_eq_right (r176m_crossingOf_not_mem_KB ρ x), ite_eq_left rfl]
    · by_cases hA : c ∈ r176s_KA ρ x
      · rw [ite_eq_right (fun h => h.2.1 hA), ite_eq_left hA,
          ite_eq_right (fun hB => r176m_KA_KB_disjoint ρ h1 x hA hB), ite_eq_right hc]
      · by_cases hB : c ∈ r176s_KB ρ x
        · rw [ite_eq_right (fun h => h.2.2 hB), ite_eq_right hA, ite_eq_left hB, ite_eq_right hc]
        · rw [ite_eq_left ⟨hc, hA, hB⟩, ite_eq_right hA, ite_eq_right hB, ite_eq_right hc]
  have h1' : (1 : ℕ) = ∑ c : ρ.Crossing, if c = ρ.crossingOf x then 1 else 0 := by
    rw [Finset.sum_ite_eq' Finset.univ (ρ.crossingOf x) (fun _ => (1 : ℕ))]
    simp
  calc (Finset.univ.filter (fun c : ρ.Crossing =>
        c ≠ ρ.crossingOf x ∧ c ∉ r176s_KA ρ x ∧ c ∉ r176s_KB ρ x)).card +
      (Finset.univ.filter (fun c : ρ.Crossing => c ∈ r176s_KA ρ x)).card +
      (Finset.univ.filter (fun c : ρ.Crossing => c ∈ r176s_KB ρ x)).card + 1
      = ∑ c : ρ.Crossing,
          ((if (c ≠ ρ.crossingOf x ∧ c ∉ r176s_KA ρ x ∧ c ∉ r176s_KB ρ x) then 1 else 0) +
            (if c ∈ r176s_KA ρ x then 1 else 0) + (if c ∈ r176s_KB ρ x then 1 else 0) +
            (if c = ρ.crossingOf x then 1 else 0)) := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
          Finset.card_filter, Finset.card_filter, Finset.card_filter, ← h1']
    _ = ∑ c : ρ.Crossing, (1 : ℕ) := Finset.sum_congr rfl (fun c _ => key c)
    _ = Fintype.card ρ.Crossing := by simp

end R176M_Rec

/-! ## §M2. The crossings of `D_A` are the chords of `D` off `{v, τ v}`; mixed iff off `K_A ∪ K_B` -/

section R176M_DA

variable (D : Diagram) (x : D.Γ.Crossing) (hD : D.componentCount = 1) (v : D.Γ.Visit) (hv : v.1 = x)

/-- the chord of `D` under a crossing of `D_A`: the chord of the lifted over occurrence -/
def r176m_κ (w : (r176s_DA D x).Γ.Crossing) : D.record.Crossing :=
  D.record.crossingOf ((r176s_DA_iso D x v hv).Φ ((r176s_DA D x).overVisit w)).1

include hD in
/-- the component of an occurrence of `D_A` is `j` iff its lift lies on the arc `A` -/
theorem r176m_comp_eq_j_iff (m : (r176s_DA D x).record.M) :
    (r176s_DA D x).record.comp m = r176s_DA_j D x v hv ↔
      r176s_ArcA D.record v ((r176s_DA_iso D x v hv).Φ m).1 := by
  rw [← r176s_smooth_comp_eq_pair_iff D.record (r176s_record_componentCount_one D hD) v,
    (r176s_DA_iso D x v hv).comp_eq]
  exact Equiv.eq_symm_apply _

include hD in
/-- the component of an occurrence of `D_A` is `i` iff its lift lies on the arc `B` -/
theorem r176m_comp_eq_i_iff (m : (r176s_DA D x).record.M) :
    (r176s_DA D x).record.comp m = r176s_DA_i D x v hv ↔
      D.record.ArcBetween (D.record.pair v) ((r176s_DA_iso D x v hv).Φ m).1 v := by
  rw [← r176s_smooth_comp_eq_self_iff D.record (r176s_record_componentCount_one D hD) v,
    (r176s_DA_iso D x v hv).comp_eq]
  exact Equiv.eq_symm_apply _

include hD in
/-- `D_A` has exactly the two components `i`, `j` -/
theorem r176m_comp_i_or_j (m : (r176s_DA D x).record.M) :
    (r176s_DA D x).record.comp m = r176s_DA_i D x v hv ∨
      (r176s_DA D x).record.comp m = r176s_DA_j D x v hv := by
  have hc : (r176s_DA D x).Γ.c = 2 := r176s_DA_componentCount D x hD
  have hij := r176s_DA_ij D x hD v hv
  have hne : (r176s_DA_i D x v hv).val ≠ (r176s_DA_j D x v hv).val := fun h => hij (Fin.ext h)
  have hk : ((r176s_DA D x).record.comp m : Fin (r176s_DA D x).Γ.c).val < (r176s_DA D x).Γ.c := Fin.isLt _
  have hi : (r176s_DA_i D x v hv).val < (r176s_DA D x).Γ.c := Fin.isLt _
  have hj : (r176s_DA_j D x v hv).val < (r176s_DA D x).Γ.c := Fin.isLt _
  have : ((r176s_DA D x).record.comp m : Fin (r176s_DA D x).Γ.c).val = (r176s_DA_i D x v hv).val ∨
      ((r176s_DA D x).record.comp m : Fin (r176s_DA D x).Γ.c).val = (r176s_DA_j D x v hv).val := by
    omega
  rcases this with h | h
  · exact Or.inl (Fin.ext h)
  · exact Or.inr (Fin.ext h)

/-- the lift of the under occurrence is the pair of the lift of the over occurrence -/
theorem r176m_Φ_underVisit (w : (r176s_DA D x).Γ.Crossing) :
    (r176s_DA_iso D x v hv).Φ ((r176s_DA D x).underVisit w) =
      (D.record.smooth v).pair ((r176s_DA_iso D x v hv).Φ ((r176s_DA D x).overVisit w)) := by
  rw [← (r176s_DA_iso D x v hv).pair_eq]
  rfl

include hD in
/-- **a crossing of `D_A` is mixed iff its chord is neither in `K_A` nor in `K_B`** -/
theorem r176m_isMixed_iff (w : (r176s_DA D x).Γ.Crossing) :
    r176l_IsMixed (r176s_DA D x) (r176s_DA_i D x v hv) (r176s_DA_j D x v hv) w ↔
      r176m_κ D x v hv w ∉ r176s_KA D.record v ∧ r176m_κ D x v hv w ∉ r176s_KB D.record v := by
  have hmu := r176m_Φ_underVisit D x v hv w
  have hKA : r176m_κ D x v hv w ∈ r176s_KA D.record v ↔
      r176s_ArcA D.record v ((r176s_DA_iso D x v hv).Φ ((r176s_DA D x).overVisit w)).1 ∧
        r176s_ArcA D.record v ((r176s_DA_iso D x v hv).Φ ((r176s_DA D x).underVisit w)).1 := by
    show D.record.CrossKeep (r176s_KA D.record v) _ ↔ _
    rw [r176s_crossKeep_KA_iff, hmu, Record.smooth_pair_val]
  have hKB : r176m_κ D x v hv w ∈ r176s_KB D.record v ↔
      D.record.ArcBetween (D.record.pair v) ((r176s_DA_iso D x v hv).Φ ((r176s_DA D x).overVisit w)).1 v ∧
        D.record.ArcBetween (D.record.pair v) ((r176s_DA_iso D x v hv).Φ ((r176s_DA D x).underVisit w)).1 v := by
    show D.record.CrossKeep (r176s_KB D.record v) _ ↔ _
    rw [r176s_crossKeep_KB_iff, hmu, Record.smooth_pair_val]
  have ho_j := r176m_comp_eq_j_iff D x hD v hv ((r176s_DA D x).overVisit w)
  have hu_j := r176m_comp_eq_j_iff D x hD v hv ((r176s_DA D x).underVisit w)
  have ho_i := r176m_comp_eq_i_iff D x hD v hv ((r176s_DA D x).overVisit w)
  have hu_i := r176m_comp_eq_i_iff D x hD v hv ((r176s_DA D x).underVisit w)
  have ho := r176m_comp_i_or_j D x hD v hv ((r176s_DA D x).overVisit w)
  have hu := r176m_comp_i_or_j D x hD v hv ((r176s_DA D x).underVisit w)
  have hij := r176s_DA_ij D x hD v hv
  rw [hKA, hKB, ← ho_j, ← hu_j, ← ho_i, ← hu_i]
  show ((r176s_DA D x).record.comp ((r176s_DA D x).overVisit w) = r176s_DA_i D x v hv ∧
        (r176s_DA D x).record.comp ((r176s_DA D x).underVisit w) = r176s_DA_j D x v hv) ∨
      ((r176s_DA D x).record.comp ((r176s_DA D x).overVisit w) = r176s_DA_j D x v hv ∧
        (r176s_DA D x).record.comp ((r176s_DA D x).underVisit w) = r176s_DA_i D x v hv) ↔ _
  constructor
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact ⟨fun h => hij (h1.symm.trans h.1), fun h => hij (h2.symm.trans h.2).symm⟩
    · exact ⟨fun h => hij (h2.symm.trans h.2), fun h => hij (h1.symm.trans h.1).symm⟩
  · rintro ⟨hA, hB⟩
    rcases ho with h1 | h1 <;> rcases hu with h2 | h2
    · exact absurd ⟨h1, h2⟩ hB
    · exact Or.inl ⟨h1, h2⟩
    · exact Or.inr ⟨h1, h2⟩
    · exact absurd ⟨h1, h2⟩ hA

/-- the chord of a crossing of `D_A` is not the chord of `v` -/
theorem r176m_κ_ne (w : (r176s_DA D x).Γ.Crossing) : r176m_κ D x v hv w ≠ D.record.crossingOf v := by
  intro h
  have hmem : ((r176s_DA_iso D x v hv).Φ ((r176s_DA D x).overVisit w)).1 ∈ (D.record.crossingOf v).1 :=
    (D.record.crossingOf_eq_iff _ _).mp h
  exact ((r176s_DA_iso D x v hv).Φ ((r176s_DA D x).overVisit w)).2 hmem

theorem r176m_κ_injective : Function.Injective (r176m_κ D x v hv) := by
  intro w w' h
  unfold r176m_κ at h
  rw [D.record.crossingOf_eq_iff] at h
  simp only [Record.crossingOf, Finset.mem_insert, Finset.mem_singleton] at h
  rcases h with h | h
  · have h' := (r176s_DA_iso D x v hv).Φ.injective (Subtype.ext h)
    exact congrArg (fun m : (r176s_DA D x).Γ.Visit => m.1) h'
  · have h2 : (r176s_DA_iso D x v hv).Φ ((r176s_DA D x).overVisit w) =
        (D.record.smooth v).pair ((r176s_DA_iso D x v hv).Φ ((r176s_DA D x).overVisit w')) :=
      Subtype.ext h
    rw [← (r176s_DA_iso D x v hv).pair_eq] at h2
    have h' := (r176s_DA_iso D x v hv).Φ.injective h2
    have h'' : (r176s_DA D x).overVisit w = (r176s_DA D x).underVisit w' := h'
    exact congrArg (fun m : (r176s_DA D x).Γ.Visit => m.1) h''

/-- every chord other than that of `v` is the chord of a crossing of `D_A` -/
theorem r176m_κ_surj (c : D.record.Crossing) (hc : c ≠ D.record.crossingOf v) :
    ∃ w, r176m_κ D x v hv w = c := by
  have hkeep : D.record.SmoothKeep v c.rep := by
    intro hmem
    exact hc (by rw [← D.record.crossingOf_rep c]; exact (D.record.crossingOf_eq_iff _ _).mpr hmem)
  obtain ⟨m, hm⟩ : ∃ m : (r176s_DA D x).Γ.Visit,
      (r176s_DA_iso D x v hv).Φ m = (⟨c.rep, hkeep⟩ : (D.record.smooth v).M) :=
    ⟨_, Equiv.apply_symm_apply _ _⟩
  refine ⟨m.1, ?_⟩
  unfold r176m_κ
  rcases (r176s_DA D x).eq_or_eq_twin m ((r176s_DA D x).overVisit m.1) rfl with h | h
  · rw [h, hm]
    exact D.record.crossingOf_rep c
  · rw [h]
    have e : (r176s_DA_iso D x v hv).Φ ((r176s_DA D x).twin m) =
        (D.record.smooth v).pair ((r176s_DA_iso D x v hv).Φ m) :=
      (r176s_DA_iso D x v hv).pair_eq m
    rw [e, hm]
    show D.record.crossingOf (D.record.pair c.rep) = c
    rw [D.record.crossingOf_pair]
    exact D.record.crossingOf_rep c

open scoped Classical in
include hD in
/-- **the mixed crossings of `D_A` are counted by the chords off `{v, τ v} ∪ K_A ∪ K_B`** -/
theorem r176m_card_mixed_eq :
    (Finset.univ.filter (r176l_IsMixed (r176s_DA D x) (r176s_DA_i D x v hv) (r176s_DA_j D x v hv))).card =
      (Finset.univ.filter (fun c : D.record.Crossing =>
        c ≠ D.record.crossingOf v ∧ c ∉ r176s_KA D.record v ∧ c ∉ r176s_KB D.record v)).card := by
  refine Finset.card_bij (fun w _ => r176m_κ D x v hv w) ?_ ?_ ?_
  · intro w hw
    rw [Finset.mem_filter] at hw ⊢
    exact ⟨Finset.mem_univ _, r176m_κ_ne D x v hv w, (r176m_isMixed_iff D x hD v hv w).mp hw.2⟩
  · intro w _ w' _ h
    exact r176m_κ_injective D x v hv h
  · intro c hc
    rw [Finset.mem_filter] at hc
    obtain ⟨w, hw⟩ := r176m_κ_surj D x v hv c hc.2.1
    refine ⟨w, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, hw⟩
    rw [r176m_isMixed_iff D x hD v hv w, hw]
    exact hc.2.2

include v hv in
/-- the smoothing keeps the signs of the other crossings -/
theorem r176m_DA_sign (hpos : ∀ c : D.Γ.Crossing, D.sign c = 1) (w : (r176s_DA D x).Γ.Crossing) :
    (r176s_DA D x).sign w = 1 := by
  have h := (r176s_DA_iso D x v hv).sgn_eq ((r176s_DA D x).overVisit w)
  rw [Record.smooth_sgn] at h
  have h' : D.sign ((r176s_DA_iso D x v hv).Φ ((r176s_DA D x).overVisit w)).1.1 = (r176s_DA D x).sign w := h
  rw [← h']
  exact hpos _

open scoped Classical in
include hD in
/-- **`2ℓ` on a positive diagram is the number of chords off `{v, τ v} ∪ K_A ∪ K_B`** -/
theorem r176m_mixedSignSum_eq (hpos : ∀ c : D.Γ.Crossing, D.sign c = 1) :
    mixedSignSum (r176s_DA D x) (r176s_DA_i D x v hv) (r176s_DA_j D x v hv) =
      ((Finset.univ.filter (fun c : D.record.Crossing =>
        c ≠ D.record.crossingOf v ∧ c ∉ r176s_KA D.record v ∧ c ∉ r176s_KB D.record v)).card : ℤ) := by
  rw [r176l_mixedSignSum_eq_card _ _ _ (r176s_DA_ij D x hD v hv) (r176m_DA_sign D x v hv hpos),
    r176m_card_mixed_eq D x hD v hv]

end R176M_DA

/-! ## §M3. On the positive lift: chords are labelled by retained crossings; the bridge count -/

section R176M_Lift

/-- (abstract) an injection `f` with `W` inside its range: `#{a | f a ∈ W} = #W` -/
theorem r176m_card_filter_of_inj {α β : Type*} [Fintype α] [DecidableEq β] (f : α → β)
    (hf : Function.Injective f) (W : Finset β) (hW : ∀ c ∈ W, ∃ a, f a = c) :
    (Finset.univ.filter (fun a => f a ∈ W)).card = W.card := by
  classical
  refine Finset.card_bij (fun a _ => f a) ?_ ?_ ?_
  · intro a ha
    exact (Finset.mem_filter.mp ha).2
  · intro a _ a' _ h
    exact hf h
  · intro c hc
    obtain ⟨a, ha⟩ := hW c hc
    exact ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [ha]; exact hc⟩, ha⟩

/-- (abstract) a bijection of `α` onto `W`: `#α = #W` -/
theorem r176m_card_of_bij {α β : Type*} [Fintype α] (f : α → β)
    (hf : Function.Injective f) (W : Finset β) (hmem : ∀ a, f a ∈ W) (hW : ∀ c ∈ W, ∃ a, f a = c) :
    Fintype.card α = W.card := by
  classical
  rw [← Finset.card_univ]
  refine Finset.card_bij (fun a _ => f a) ?_ ?_ ?_
  · intro a _
    exact hmem a
  · intro a _ a' _ h
    exact hf h
  · intro c hc
    obtain ⟨a, ha⟩ := hW c hc
    exact ⟨a, Finset.mem_univ _, ha⟩

variable {n : ℕ} [NeZero n] (hn : 3 ≤ n) {P : LabelledTuple n} (hG : CarrierGeometry P)
  {T : Finset (Crossing P)} (hT : GeoIndependent hG.cg T) (q : GeoComponent hG.cg T)

/-- membership in `liftBlock W` is the label in `W` (stated to avoid unfolding the lift in defeq checks) -/
theorem r176m_mem_liftBlock (W : Finset (Crossing P)) (p : (geoPositiveLift hn hG hT q).record.Crossing) :
    p ∈ CV.liftBlock hn hG hT q W ↔ CV.liftLabel hn hG hT q p ∈ W := by
  rw [CV.liftBlock, Set.mem_ofPred_eq]

open scoped Classical in
/-- `#(liftBlock W) = #W` for `W` inside the retained set of `q` -/
theorem r176m_card_liftBlock (W : Finset (Crossing P)) (hW : W ⊆ geoCarrierCrossings hG.cg T q) :
    (Finset.univ.filter (fun p : (geoPositiveLift hn hG hT q).record.Crossing =>
      p ∈ CV.liftBlock hn hG hT q W)).card = W.card := by
  rw [Finset.filter_congr (fun p _ => r176m_mem_liftBlock hn hG hT q W p)]
  exact r176m_card_filter_of_inj (CV.liftLabel hn hG hT q)
    (fun _ _ h => CV.liftLabel_injective hn hG hT q h) W
    (fun _ hc => CV.exists_liftLabel_eq hn hG hT q (hW hc))

/-- the chords of the lift are labelled bijectively by the retained crossings of `q` -/
theorem r176m_card_record_crossing :
    Fintype.card (geoPositiveLift hn hG hT q).record.Crossing = (geoCarrierCrossings hG.cg T q).card :=
  r176m_card_of_bij (CV.liftLabel hn hG hT q) (fun _ _ h => CV.liftLabel_injective hn hG hT q h) _
    (CV.liftLabel_mem hn hG hT q) (fun _ hc => CV.exists_liftLabel_eq hn hG hT q hc)

/-- **The bridge count on the lift**: with `K_A = liftBlock W₂`, `K_B = liftBlock W₁ ∪ {r}`, `r ∉ liftBlock W₁`
(the `KA_eq`, `KB_eq`, `r_not` fields of the outer data), `2ℓ + #W₁ + #W₂ + 2 = #retained q`. -/
theorem r176m_bridge_count (y : (geoPositiveLift hn hG hT q).Γ.Crossing)
    (v₀ : (geoPositiveLift hn hG hT q).Γ.Visit) (hv₀ : v₀.1 = y)
    (W₁ W₂ : Finset (Crossing P)) (hW₁ : W₁ ⊆ geoCarrierCrossings hG.cg T q)
    (hW₂ : W₂ ⊆ geoCarrierCrossings hG.cg T q) (r : (geoPositiveLift hn hG hT q).record.Crossing)
    (hKA : r176s_KA (geoPositiveLift hn hG hT q).record v₀ = CV.liftBlock hn hG hT q W₂)
    (hKB : r176s_KB (geoPositiveLift hn hG hT q).record v₀ = CV.liftBlock hn hG hT q W₁ ∪ {r})
    (hr : r ∉ CV.liftBlock hn hG hT q W₁) :
    mixedSignSum (r176s_DA (geoPositiveLift hn hG hT q) y) (r176s_DA_i _ y v₀ hv₀) (r176s_DA_j _ y v₀ hv₀) +
      (W₁.card : ℤ) + W₂.card + 2 = (geoCarrierCrossings hG.cg T q).card := by
  classical
  have hD : (geoPositiveLift hn hG hT q).componentCount = 1 := geoPositiveLift_componentCount hn hG hT q
  rw [r176m_mixedSignSum_eq (geoPositiveLift hn hG hT q) y hD v₀ hv₀ (geoPositiveLift_sign hn hG hT q)]
  have hrest := r176m_card_rest (geoPositiveLift hn hG hT q).record
    (r176s_record_componentCount_one _ hD) v₀
  have hA : (Finset.univ.filter (fun c : (geoPositiveLift hn hG hT q).record.Crossing =>
      c ∈ r176s_KA (geoPositiveLift hn hG hT q).record v₀)).card = W₂.card := by
    have e : (Finset.univ.filter (fun c : (geoPositiveLift hn hG hT q).record.Crossing =>
        c ∈ r176s_KA (geoPositiveLift hn hG hT q).record v₀)) =
        Finset.univ.filter (fun c : (geoPositiveLift hn hG hT q).record.Crossing =>
          c ∈ CV.liftBlock hn hG hT q W₂) := by
      ext c
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hKA]
    rw [e]
    exact r176m_card_liftBlock hn hG hT q W₂ hW₂
  have hB : (Finset.univ.filter (fun c : (geoPositiveLift hn hG hT q).record.Crossing =>
      c ∈ r176s_KB (geoPositiveLift hn hG hT q).record v₀)).card = W₁.card + 1 := by
    have e : (Finset.univ.filter (fun c : (geoPositiveLift hn hG hT q).record.Crossing =>
        c ∈ r176s_KB (geoPositiveLift hn hG hT q).record v₀)) =
        Finset.univ.filter (fun c : (geoPositiveLift hn hG hT q).record.Crossing =>
          c ∈ CV.liftBlock hn hG hT q W₁) ∪ {r} := by
      ext c
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, Finset.mem_singleton, hKB,
        Set.mem_union, Set.mem_singleton_iff]
    have hdis : Disjoint (Finset.univ.filter (fun c : (geoPositiveLift hn hG hT q).record.Crossing =>
        c ∈ CV.liftBlock hn hG hT q W₁)) {r} := by
      rw [Finset.disjoint_singleton_right, Finset.mem_filter]
      exact fun h => hr h.2
    rw [e, Finset.card_union_of_disjoint hdis, Finset.card_singleton,
      r176m_card_liftBlock hn hG hT q W₁ hW₁]
  have hN := r176m_card_record_crossing hn hG hT q
  omega

end R176M_Lift

/-! ## §M4. The event level: `r176_mixed_bridge` -/

section R176M_Event

variable {n : ℕ} [NeZero n] {E : CV.Event n} {e f g : ZMod n} {δ : ℝ}

/-- **The (14)-bridge of row 176** (`r176_mixed_bridge`, the open Prop #3 of R176_ASSEMBLY_REPORT §5): the
mixed sign sum of `D_A` between `i` and `j` is the number of mask-`uv` survivors.  Proof: `r176m_bridge_count`
on `D₊ = carrierDiagram q₀'` with the outer data's `KA_eq / KB_eq / r_not / subA / subB`, against the
LEDGER's `#retained q₀' = #Λ₁ + #Λ₂ + #mixedSet + #{u', v'}` (`r176l_children_case1`,
`r176l_card_retained`, `r176l_selectedPart_card`; the case-1 successor facts derived exactly as in
`r176l_portDataRest_case1`). -/
theorem r176m_mixed_bridge_proof : r176_mixed_bridge := by
  intro n _ hn E e f g δ hL hR hef heg hfg t t' ht ht' hop hs hef' heg' hfg' hcomp Q hQ hfull j hj q a b c
    hab hac hbc habc u v hjab huac hvbc hu hv hju hjv huv hu' hv' hlt_a hSf y hy O
  have hS' := est_S'_ind hL ht ht' hop hs hQ hfull hj
  -- the `L` side (as in `r176l_portDataRest_case1`)
  have hs' : ∀ s, IsCrossing (E.curve t') s ↔ IsCrossing (E.curve t) s := fun s => (hs s).symm
  have hop' : OppositeSides E t' t := by
    unfold OppositeSides at hop ⊢; linarith [mul_comm t.val t'.val]
  have hXL : ExactTriangleVisitOrders (E.curve t') (E.curve t) a b c hs' :=
    gu2_exact_of_eq hs' habc.symm (hL.gauss_words t' t ht' ht hop' hs')
  have hGL : CarrierGeometry (E.curve t') :=
    CarrierGeometry.ofDiagrammatic ((genericAt E t' ht'.1).diagrammatic hn)
  have hT : GeoIndependent (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j})) :=
    CV.geoIndependent_of_mem_Ind _ hS'
  have hjT : crossingTransport hs j ∈ transportSupport hs (Q ∪ {j}) :=
    (mem_transportSupport_iff hs _ j).mpr (Finset.mem_union_right _ (Finset.mem_singleton_self j))
  -- the successor facts of case 1
  have hρa : geoMarkSuccessor (geomAt E t' ht'.1) (Sum.inr (r176l_ua (u := crossingTransport hs u) huac)) =
      Sum.inr (visitOn (crossingTransport hs j) a (s176_mem_left hjab)) :=
    gu1_markSuccessor_eq_of_adjacent hn _ rfl hlt_a
      (fun w hw => (s176_nb_a hs' hab hac hbc hXL (j := crossingTransport hs j) (u := crossingTransport hs u)
        hjab huac w hw).1)
  have hlt_b := (s176_cyclic hn hGL hs' hT (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)
    hab hac hbc hXL (j := crossingTransport hs j)
    (u := crossingTransport hs u) (v := crossingTransport hs v) hjab huac hvbc hjT hu' hv').mp hlt_a
  have hρb : geoMarkSuccessor (geomAt E t' ht'.1) (Sum.inr (visitOn (crossingTransport hs j) b (s176_mem_right hjab))) =
      Sum.inr (visitOn (crossingTransport hs v) b (s176_mem_left hvbc)) :=
    gu1_markSuccessor_eq_of_adjacent hn _ rfl hlt_b
      (fun w hw => (s176_nb_b hs' hab hac hbc hXL (j := crossingTransport hs j) (v := crossingTransport hs v)
        hjab hvbc w hw).1)
  have hnb_c := fun (w : Visit (E.curve t')) (hw : w.2.val = c) =>
    s176_nb_c hs' hab hac hbc hXL (u := crossingTransport hs u) (v := crossingTransport hs v) huac hvbc w hw
  -- the full support
  have hSfI : GeoIndependent (geomAt E t' ht'.1)
      (r176l_Sf (transportSupport hs (Q ∪ {j})) (crossingTransport hs u) (crossingTransport hs v)) :=
    CV.geoIndependent_of_mem_Ind _ hSf
  -- the children and the `L`-side count
  obtain ⟨hlt_c, hρc⟩ := r176l_lt_c_of_indep hn (geomAt E t' ht'.1)
    (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q) hab hac hbc
    (j := crossingTransport hs j) (u := crossingTransport hs u) (v := crossingTransport hs v) hjab huac hvbc
    hjT hu' hv' hρa hρb hSfI hnb_c
  have hC := r176l_children_case1 (geomAt E t' ht'.1) hT
    (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q) hab hac hbc
    (j := crossingTransport hs j) (u := crossingTransport hs u) (v := crossingTransport hs v) hjab huac hvbc
    hjT hu' hv' hρa hρb hρc hSfI
  have hcard := r176l_card_retained (geomAt E t' ht'.1) (r176l_subset_Sf _ _ _) hC
  have hsel := r176l_selectedPart_card (geomAt E t' ht'.1)
    (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q) hab hbc
    (u := crossingTransport hs u) (v := crossingTransport hs v) huac hvbc hu' hv'
  -- the count on the lift
  have hcount : mixedSignSum (r176s_DA (CV.carrierDiagram hn (genericAt E t' ht'.1) hS'
      (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)) y)
      (r176s_DA_i _ y O.v₀ O.hv₀) (r176s_DA_j _ y O.v₀ O.hv₀) +
      ((geoCarrierCrossings (geomAt E t' ht'.1) _ (r176l_L1 (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j}))
        (crossingTransport hs u) (v := crossingTransport hs v) hvbc)).card : ℤ) +
      ((geoCarrierCrossings (geomAt E t' ht'.1) _ (r176l_L2 (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j}))
        (crossingTransport hs v) (u := crossingTransport hs u) huac)).card : ℤ) + 2 =
      ((geoCarrierCrossings (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j}))
        (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)).card : ℤ) :=
    r176m_bridge_count hn (r176s_cgL hn ht') (CV.geoIndependent_of_mem_Ind _ hS')
      (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q) y O.v₀ O.hv₀ _ _ O.subB O.subA
      O.r O.KA_eq O.KB_eq O.r_not
  have hcard' : ((geoCarrierCrossings (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j}))
        (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)).card : ℤ) =
      ((geoCarrierCrossings (geomAt E t' ht'.1) _ (r176l_L1 (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j}))
        (crossingTransport hs u) (v := crossingTransport hs v) hvbc)).card : ℤ) +
      ((geoCarrierCrossings (geomAt E t' ht'.1) _ (r176l_L2 (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j}))
        (crossingTransport hs v) (u := crossingTransport hs u) huac)).card : ℤ) +
      ((r176l_mixedSet (genericAt E t' ht'.1).crossingGeometry (transportSupport hs (Q ∪ {j}))
        (r176l_Sf (transportSupport hs (Q ∪ {j})) (crossingTransport hs u) (crossingTransport hs v))
        (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)
        (r176l_L1 (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j})) (crossingTransport hs u)
          (v := crossingTransport hs v) hvbc)
        (r176l_L2 (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j})) (crossingTransport hs v)
          (u := crossingTransport hs u) huac)).card : ℤ) + 2 := by
    rw [hsel] at hcard
    have h := (Nat.cast_inj (R := ℤ)).mpr hcard
    push_cast at h
    exact h
  linarith

end R176M_Event

/-! ## §M5. The row with the mixed bridge discharged -/

/-- **Row 176 from the two remaining open Props**: `r176_extreme_transport_of_curl_outer_mixed` with
`r176_mixed_bridge` discharged by `r176m_mixed_bridge_proof`; what remains open is `r176s_curl_removal`
(the record-level R-I) and `r176_outer_carriers_L` (the geometric outer-carrier identification). -/
theorem r176m_extreme_transport_of_curl_outer (hcurl : r176s_curl_removal) (hout : r176_outer_carriers_L) :
    RowShape @ExtremeTransportData :=
  r176_extreme_transport_of_curl_outer_mixed hcurl hout r176m_mixed_bridge_proof

end

end RProof


/-! # R176W2 — the assembler's section (`r176a_`, 2026-09-15): the mirrored (14)-bridge

The OUTER unit found the frozen Prop `r176_outer_carriers_L` false at `y = lift v'` (R176W2_OUTER_REPORT §2) and
replaced it by the proved split `r176o_outer_carriers_L_corrected`, whose `v'`-half carries the mirrored data
`r176o_OuterDataL'` (children exchanged: `K_A = liftBlock (retained Λ₁)`, `K_B = liftBlock (retained Λ₂) ∪ {lift u'}`).
Its replayed composition `r176o_extreme_transport_of_curl_mixed` therefore needs, besides `r176s_curl_removal`
(CURL: `r176c_curl_removal_proof`) and `r176_mixed_bridge` (MIXED: `r176m_mixed_bridge_proof`), the mirrored bridge
`r176o_mixed_bridge'`.  MIXED's count `r176m_bridge_count` is symmetric in the two children (`W₁`, `W₂` are only
counted), so the mirrored bridge is MIXED's event-level proof with `W₁ := retained Λ₂`, `W₂ := retained Λ₁`
(`hW₁ := O.subA`, `hW₂ := O.subB`) — the two `card` summands of `hcount` exchange places and `linarith` closes as before.
Nothing above is modified; the only new name is `r176a_mixed_bridge'_proof`. -/

namespace RProof

open SM SM.GeoCarrier SM.Carrier SM.Link

noncomputable section

section R176A_Assembly

/-- **The mirrored (14)-bridge** `r176o_mixed_bridge'` (the Prop left open by the OUTER unit): `r176m_mixed_bridge_proof`
with the roles of `Λ₁`/`Λ₂` exchanged in the call of `r176m_bridge_count` (`W₁ := retained Λ₂` via `O.subA`,
`W₂ := retained Λ₁` via `O.subB`, against `O.KA_eq : K_A = liftBlock (retained Λ₁)`,
`O.KB_eq : K_B = liftBlock (retained Λ₂) ∪ {r}`, `O.r_not`). -/
theorem r176a_mixed_bridge'_proof : r176o_mixed_bridge' := by
  intro n _ hn E e f g δ hL hR hef heg hfg t t' ht ht' hop hs hef' heg' hfg' hcomp Q hQ hfull j hj q a b c
    hab hac hbc habc u v hjab huac hvbc hu hv hju hjv huv hu' hv' hlt_a hSf y hy O
  have hS' := est_S'_ind hL ht ht' hop hs hQ hfull hj
  -- the `L` side (as in `r176l_portDataRest_case1`)
  have hs' : ∀ s, IsCrossing (E.curve t') s ↔ IsCrossing (E.curve t) s := fun s => (hs s).symm
  have hop' : OppositeSides E t' t := by
    unfold OppositeSides at hop ⊢; linarith [mul_comm t.val t'.val]
  have hXL : ExactTriangleVisitOrders (E.curve t') (E.curve t) a b c hs' :=
    gu2_exact_of_eq hs' habc.symm (hL.gauss_words t' t ht' ht hop' hs')
  have hGL : CarrierGeometry (E.curve t') :=
    CarrierGeometry.ofDiagrammatic ((genericAt E t' ht'.1).diagrammatic hn)
  have hT : GeoIndependent (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j})) :=
    CV.geoIndependent_of_mem_Ind _ hS'
  have hjT : crossingTransport hs j ∈ transportSupport hs (Q ∪ {j}) :=
    (mem_transportSupport_iff hs _ j).mpr (Finset.mem_union_right _ (Finset.mem_singleton_self j))
  -- the successor facts of case 1
  have hρa : geoMarkSuccessor (geomAt E t' ht'.1) (Sum.inr (r176l_ua (u := crossingTransport hs u) huac)) =
      Sum.inr (visitOn (crossingTransport hs j) a (s176_mem_left hjab)) :=
    gu1_markSuccessor_eq_of_adjacent hn _ rfl hlt_a
      (fun w hw => (s176_nb_a hs' hab hac hbc hXL (j := crossingTransport hs j) (u := crossingTransport hs u)
        hjab huac w hw).1)
  have hlt_b := (s176_cyclic hn hGL hs' hT (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)
    hab hac hbc hXL (j := crossingTransport hs j)
    (u := crossingTransport hs u) (v := crossingTransport hs v) hjab huac hvbc hjT hu' hv').mp hlt_a
  have hρb : geoMarkSuccessor (geomAt E t' ht'.1) (Sum.inr (visitOn (crossingTransport hs j) b (s176_mem_right hjab))) =
      Sum.inr (visitOn (crossingTransport hs v) b (s176_mem_left hvbc)) :=
    gu1_markSuccessor_eq_of_adjacent hn _ rfl hlt_b
      (fun w hw => (s176_nb_b hs' hab hac hbc hXL (j := crossingTransport hs j) (v := crossingTransport hs v)
        hjab hvbc w hw).1)
  have hnb_c := fun (w : Visit (E.curve t')) (hw : w.2.val = c) =>
    s176_nb_c hs' hab hac hbc hXL (u := crossingTransport hs u) (v := crossingTransport hs v) huac hvbc w hw
  -- the full support
  have hSfI : GeoIndependent (geomAt E t' ht'.1)
      (r176l_Sf (transportSupport hs (Q ∪ {j})) (crossingTransport hs u) (crossingTransport hs v)) :=
    CV.geoIndependent_of_mem_Ind _ hSf
  -- the children and the `L`-side count
  obtain ⟨hlt_c, hρc⟩ := r176l_lt_c_of_indep hn (geomAt E t' ht'.1)
    (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q) hab hac hbc
    (j := crossingTransport hs j) (u := crossingTransport hs u) (v := crossingTransport hs v) hjab huac hvbc
    hjT hu' hv' hρa hρb hSfI hnb_c
  have hC := r176l_children_case1 (geomAt E t' ht'.1) hT
    (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q) hab hac hbc
    (j := crossingTransport hs j) (u := crossingTransport hs u) (v := crossingTransport hs v) hjab huac hvbc
    hjT hu' hv' hρa hρb hρc hSfI
  have hcard := r176l_card_retained (geomAt E t' ht'.1) (r176l_subset_Sf _ _ _) hC
  have hsel := r176l_selectedPart_card (geomAt E t' ht'.1)
    (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q) hab hbc
    (u := crossingTransport hs u) (v := crossingTransport hs v) huac hvbc hu' hv'
  -- the count on the lift
  have hcount : mixedSignSum (r176s_DA (CV.carrierDiagram hn (genericAt E t' ht'.1) hS'
      (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)) y)
      (r176s_DA_i _ y O.v₀ O.hv₀) (r176s_DA_j _ y O.v₀ O.hv₀) +
      ((geoCarrierCrossings (geomAt E t' ht'.1) _ (r176l_L2 (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j}))
        (crossingTransport hs v) (u := crossingTransport hs u) huac)).card : ℤ) +
      ((geoCarrierCrossings (geomAt E t' ht'.1) _ (r176l_L1 (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j}))
        (crossingTransport hs u) (v := crossingTransport hs v) hvbc)).card : ℤ) + 2 =
      ((geoCarrierCrossings (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j}))
        (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)).card : ℤ) :=
    r176m_bridge_count hn (r176s_cgL hn ht') (CV.geoIndependent_of_mem_Ind _ hS')
      (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q) y O.v₀ O.hv₀ _ _ O.subA O.subB
      O.r O.KA_eq O.KB_eq O.r_not
  have hcard' : ((geoCarrierCrossings (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j}))
        (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)).card : ℤ) =
      ((geoCarrierCrossings (geomAt E t' ht'.1) _ (r176l_L1 (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j}))
        (crossingTransport hs u) (v := crossingTransport hs v) hvbc)).card : ℤ) +
      ((geoCarrierCrossings (geomAt E t' ht'.1) _ (r176l_L2 (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j}))
        (crossingTransport hs v) (u := crossingTransport hs u) huac)).card : ℤ) +
      ((r176l_mixedSet (genericAt E t' ht'.1).crossingGeometry (transportSupport hs (Q ∪ {j}))
        (r176l_Sf (transportSupport hs (Q ∪ {j})) (crossingTransport hs u) (crossingTransport hs v))
        (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)
        (r176l_L1 (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j})) (crossingTransport hs u)
          (v := crossingTransport hs v) hvbc)
        (r176l_L2 (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j})) (crossingTransport hs v)
          (u := crossingTransport hs u) huac)).card : ℤ) + 2 := by
    rw [hsel] at hcard
    have h := (Nat.cast_inj (R := ℤ)).mpr hcard
    push_cast at h
    exact h
  linarith

/-- **Row 176 in the row shape `RowShape @ExtremeTransportData`** (RALedgers' fixed shape of an X₁-dependent R row),
unconditional: `r176o_extreme_transport_of_curl_mixed` (OUTER's replay of `r176_extreme_transport_of_curl_outer_mixed`
on the corrected outer carriers) with its three hypotheses discharged — `r176s_curl_removal` by CURL's
`r176c_curl_removal_proof`, `r176o_mixed_bridge'` by `r176a_mixed_bridge'_proof`, `r176_mixed_bridge` by MIXED's
`r176m_mixed_bridge_proof`.  The row theorem `RProof.extreme_transport` (FIXED name, the siblings' binder form) is
this statement instantiated. -/
theorem r176a_extreme_transport_rowShape : RowShape @ExtremeTransportData :=
  r176o_extreme_transport_of_curl_mixed r176c_curl_removal_proof r176a_mixed_bridge'_proof
    r176m_mixed_bridge_proof

end R176A_Assembly

end

end RProof
